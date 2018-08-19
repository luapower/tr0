
--Unicode text shaping and rendering.
--Written by Cosmin Apreutesei. Public Domain.

if not ... then require'tr_demo'; return end

local bit = require'bit'
local ffi = require'ffi'
local utf8 = require'utf8'
local hb = require'harfbuzz'
local fb = require'fribidi'
local ub = require'libunibreak'
local ft = require'freetype'
local glue = require'glue'
local box2d = require'box2d'
local lrucache = require'lrucache'
local xxhash64 = require'xxhash'.hash64
local detect_scripts = require'tr_shape_script'
local reorder_runs = require'tr_shape_reorder'
local zone = require'jit.zone' --glue.noop

local band = bit.band
local push = table.insert
local update = glue.update
local assert = glue.assert --assert with string formatting
local count = glue.count
local clamp = glue.clamp
local snap = glue.snap
local binsearch = glue.binsearch
local memoize = glue.memoize
local growbuffer = glue.growbuffer
local reverse = glue.reverse
local bounding_box = box2d.bounding_box
local hit_box = box2d.hit
local odd = function(x) return band(x, 1) == 1 end

--iterate a list of values in run-length encoded form.
local function pass(t, i) return t[i] end
local function rle_runs(t, len, run_value)
	run_value = run_value or pass
	local i = 0
	return function()
		if i >= len then
			return nil
		end
		local i1, n, val1 = i, 1, run_value(t, i)
		while true do
			i = i + 1
			if i >= len then
				return i1, n, val1
			end
			local val = run_value(t, i)
			if val ~= val1 then
				return i1, n, val1
			end
			n = n + 1
		end
	end
end

local tr = {}
setmetatable(tr, tr)

tr.glyph_run_cache_size = 1024^2 * 10 --10MB net (arbitrary default)

tr.rasterizer_module = 'tr_raster_cairo' --who does rs:paint_glyph()

function tr:create_rasterizer()
	return require(self.rasterizer_module)()
end

function tr:__call()
	self = update({}, self)

	self.rs = self:create_rasterizer()

	self.glyph_runs = lrucache{max_size = self.glyph_run_cache_size}
	function self.glyph_runs:value_size(glyph_run)
		return glyph_run.mem_size
	end
	function self.glyph_runs:free_value(glyph_run)
		glyph_run:free()
	end

	return self
end

function tr:free()
	self.glyph_runs:free()
	self.glyph_runs = false

	self.rs:free()
	self.rs = false
end

--font management ------------------------------------------------------------

local function override_font(font)
	local inherited = font.load
	function font:load()
		inherited(self)
		assert(not self.hb_font)
		self.hb_font = assert(hb.ft_font(self.ft_face, nil))
		self.hb_font:set_ft_load_flags(self.ft_load_flags)
	end
	local inherited = font.unload
	function font:unload()
		self.hb_font:free()
		self.hb_font = false
		inherited(self)
	end
	function font:size_changed()
		self.hb_font:ft_changed()
	end
	return font
end

function tr:add_font_file(...)
	return override_font(self.rs:add_font_file(...))
end

function tr:add_mem_font(...)
	return override_font(self.rs:add_mem_font(...))
end

--shaping of a single text run into an array of glyphs -----------------------

local glyph_run = {} --glyph run methods
tr.glyph_run_class = glyph_run

function glyph_run:free()
	self.hb_buf:free()
	self.hb_buf = false
	self.info = false
	self.pos = false
	self.len = 0
	self.font:unref()
	self.font = false
end

--return glyph origin relative to the start of the run.
function glyph_run:glyph_pos(i)
	local px = self.pos[i].x_offset / 64
	local py = self.pos[i].y_offset / 64
	return px, py
end

function glyph_run:glyph_metrics(i)
	local glyph_index = self.info[i].codepoint
	return self.tr.rs:glyph_metrics(self.font, self.font_size, glyph_index)
end

local hb_glyph_size =
	ffi.sizeof'hb_glyph_info_t'
	+ ffi.sizeof'hb_glyph_position_t'

local function isnewline(c)
	return c == 10 or c == 13
end

--for harfbuzz, language must be a ISO 639 language code, but libunibreak
--only uses the 2-char language code part.
local ub_lang = memoize(function(hb_lang)
	local s = hb.language_tostring(hb_lang)
	return s and s:sub(1, 2)
end)
local ub_lang = function(hb_lang)
	return ub_lang(tonumber(hb_lang))
end

local function get_cluster(glyph_info, i)
	return glyph_info[i].cluster
end

local function count_graphemes(grapheme_breaks, start, len)
	local n = 0
	for i = start, start+len-1 do
		if grapheme_breaks[i] == 0 then
			n = n + 1
		end
	end
	return n
end

local function next_grapheme(grapheme_breaks, i, len)
	while grapheme_breaks[i] ~= 0 do
		i = i + 1
	end
	i = i + 1
	return i < len and i or nil
end

local alloc_grapheme_breaks = growbuffer'char[?]'

function tr:shape_text_run(
	str, str_len, str_offset, len,
	font, font_size, features, feat_count, rtl, script, lang
)
	font:ref()
	font:setsize(font_size)

	local hb_buf = hb.buffer()
	hb_buf:set_cluster_level(hb.C.HB_BUFFER_CLUSTER_LEVEL_MONOTONE_GRAPHEMES)

	local hb_dir = rtl and hb.C.HB_DIRECTION_RTL or hb.C.HB_DIRECTION_LTR
	hb_buf:set_direction(hb_dir)
	hb_buf:set_script(script)
	hb_buf:set_language(lang)

	hb_buf:add_codepoints(str, str_len, str_offset, len)

	zone'hb_shape_full'
	hb_buf:shape_full(font.hb_font, features, feat_count)
	zone()

	local glyph_count = hb_buf:get_length()
	local glyph_info  = hb_buf:get_glyph_infos()
	local glyph_pos   = hb_buf:get_glyph_positions()

	zone'hb_shape_metrics'
	local bx, by, bw, bh = 0, 0, 0, 0 --bounding box
	local ax, ay = 0, 0 --glyph advance
	for i = 0, glyph_count-1 do

		--glyph origin relative to the start of the run.
		local px = ax + glyph_pos[i].x_offset
		local py = ay - glyph_pos[i].y_offset

		local glyph_index = glyph_info[i].codepoint

		local m = self.rs:glyph_metrics(font, font_size, glyph_index)
		bx, by, bw, bh = bounding_box(bx, by, bw, bh,
			px / 64 + m.hlsb,
			py / 64 - m.htsb,
			m.w, m.h)

		ax = ax + glyph_pos[i].x_advance
		ay = ay - glyph_pos[i].y_advance

		--put glyph origin into x/y_offset!
		glyph_pos[i].x_offset = px
		glyph_pos[i].y_offset = py
	end
	ax = ax / 64
	ay = ay / 64
	zone()

	zone'hb_shape_cursor_pos'
	local cursor_offsets = {} --{i1, ...} in visual order
	local cursor_xs = {} --{x1, ...} in visual order
	local grapheme_breaks

	local function add_cursor(
		glyph_offset, glyph_count,
		cluster, cluster_len, cluster_x
	)
		push(cursor_offsets, cluster)
		push(cursor_xs, cluster_x)
		if cluster_len > 1 then
			--the cluster is made of multiple codepoints. check how many
			--graphemes it contains since we need to add additional cursor
			--positions at each grapheme boundary.
			if not grapheme_breaks then
				grapheme_breaks = alloc_grapheme_breaks(len)
				local lang = nil --not used in current libunibreak impl.
				ub.graphemebreaks(str + str_offset, len, lang, grapheme_breaks)
			end
			local grapheme_count =
				count_graphemes(grapheme_breaks, cluster, cluster_len)
			if grapheme_count > 1 then
				--the cluster is made of multiple graphemes which can be the
				--result of forming ligatures which the font can provide carets
				--for. if the font gives no ligature carets, we divide the
				--last glyph's x-advance evenly between graphemes.
				for i = glyph_offset, glyph_offset + glyph_count - 1 do
					local glyph_index = glyph_info[i].codepoint
					local cluster_x = glyph_pos[i].x_offset / 64
					local carets, caret_count =
						font.hb_font:get_ligature_carets(hb_dir, glyph_index)
					if caret_count > 0 then
						-- there shouldn't be more carets than are graphemes - 1.
						caret_count = math.min(caret_count, grapheme_count - 1)
						--add the ligature carets from the font.
						for i = 0, caret_count-1 do
							--create a synthetic cluster at each grapheme boundary.
							cluster = next_grapheme(grapheme_breaks, cluster, len)
							local lig_x = carets[i] / 64
							push(cursor_offsets, cluster)
							push(cursor_xs, cluster_x + lig_x)
						end
						--infer the number of graphemes in the glyph as being
						--the number of ligature carets in the glyph + 1.
						grapheme_count = grapheme_count - (caret_count + 1)
					else
						--font doesn't provide carets: add synthetic carets by
						--dividing the total x-advance of the remaining glyphs
						--evenly between remaining graphemes.
						local last_glyph_index = glyph_offset + glyph_count - 1
						local total_advance_x =
							 (glyph_pos[last_glyph_index].x_offset
							+ glyph_pos[last_glyph_index].x_advance
							- glyph_pos[i].x_offset) / 64
						local w = total_advance_x / grapheme_count
						for i = 1, grapheme_count-1 do
							--create a synthetic cluster at each grapheme boundary.
							cluster = next_grapheme(grapheme_breaks, cluster, len)
							local lig_x = i * w
							push(cursor_offsets, cluster)
							push(cursor_xs, cluster_x + lig_x)
						end
						grapheme_count = 0
					end
					if grapheme_count == 0 then
						break --all graphemes have carets
					end
				end
			end
		end
	end

	if rtl then
		local last_i, last_glyph_count, last_cluster, last_cluster_len, last_cluster_x
		local first_cluster = len
		local first_cluster_x = len > 0 and glyph_pos[0].x_offset / 64 or ax
		push(cursor_offsets, first_cluster)
		push(cursor_xs, first_cluster_x)
		last_cluster = first_cluster
		for i, glyph_count, cluster in rle_runs(
			glyph_info, glyph_count, get_cluster
		) do
			local cluster = cluster - str_offset
			local cluster_len = last_cluster - cluster
			last_cluster_x = glyph_pos[i].x_offset / 64
			if last_i then
				add_cursor(last_i, last_glyph_count, last_cluster, last_cluster_len, last_cluster_x)
			end
			last_i, last_glyph_count, last_cluster, last_cluster_len =
				i, glyph_count, cluster, cluster_len
		end
		if last_i then
			last_cluster_x = ax
			add_cursor(last_i, last_glyph_count, last_cluster, last_cluster_len, last_cluster_x)
		end
		--keep cursors in logical order, easier for navigation.
		reverse(cursor_offsets)
		reverse(cursor_xs)
	else
		local last_i, last_glyph_count, last_cluster, last_cluster_x
		for i, glyph_count, cluster in rle_runs(
			glyph_info, glyph_count, get_cluster
		) do
			local cluster = cluster - str_offset
			local cluster_x = glyph_pos[i].x_offset / 64
			if last_cluster then
				local last_cluster_len = cluster - last_cluster
				add_cursor(last_i, last_glyph_count, last_cluster, last_cluster_len, last_cluster_x)
			end
			last_i, last_glyph_count, last_cluster, last_cluster_x =
				i, glyph_count, cluster, cluster_x
		end
		if last_i then
			local last_cluster_len = len - last_cluster
			add_cursor(last_i, last_glyph_count, last_cluster, last_cluster_len, last_cluster_x)
		end
		push(cursor_offsets, len)
		push(cursor_xs, ax)
	end
	zone()

	local glyph_run = update({
		tr = self,
		--for glyph painting
		font = font,
		font_size = font_size,
		len = glyph_count,
		info = glyph_info,
		pos = glyph_pos,
		hb_buf = hb_buf, --anchored
		--for creating horizontal flow
		advance_x = ax,
		--for creating vertical flow (NYI)
		advance_y = ay,
		--for vertical alignment, line spacing and line hit-testing
		ascent = font.ascent,
		descent = font.descent,
		--for horizontal alignment and for line wrapping of horizontal text
		hlsb = bx, --left-side-bearing for horizontal flow
		htsb = by, --top-side bearing for horizontal flow (not used)
		w = bw, --bounding-box width
		h = bh, --bounding-box height (not used)
		--for lru cache
		mem_size =
			224 + hb_glyph_size * math.max(len, glyph_count) --hb_buffer_t
			+ 400 --this table
			+ (8 + 8) * (len + 1) --cursor_offsets, cursor_xs
		,
		--for cursor positioning and hit testing
		cursor_offsets = cursor_offsets,
		cursor_xs = cursor_xs,
		rtl = rtl,
	}, self.glyph_run_class)

	return glyph_run
end

function tr:glyph_run(
	str, str_len, str_offset, len,
	font, font_size, features, feat_count, rtl, script, lang
)
	--ignore trailing line breaks, if any.
	--NOTE: this can result in an empty run, which is ok, we still need
	--the linebreak flag and a cursor position even on a zero-glyph run.
	for i = str_offset+len-1, str_offset, -1 do
		if isnewline(str[i]) then
			len = len - 1
		end
	end

	font:ref()
	local text_hash = tonumber(xxhash64(str + str_offset, 4 * len, 0))
	local lang_id = tonumber(lang) or false
	local key = font.tuple(text_hash, font_size, rtl, script, lang_id)
	local glyph_run = self.glyph_runs:get(key)
	if not glyph_run then
		glyph_run = self:shape_text_run(
			str, str_len, str_offset, len,
			font, font_size, features, feat_count, rtl, script, lang
		)
		self.glyph_runs:put(key, glyph_run)
	end
	font:unref()
	return glyph_run
end

--shaping of a text tree into an array of segments ---------------------------

--convert a Lua table of {name -> value} into an array of hb_feature_t.
local function hb_feature_list(features)
	local feats_count = count(features)
	if feats_count == 0 then return nil end
	local feats = ffi.new('hb_feature_t[?]', feats_count)
	local i = 0
	for k,v in pairs(features) do
		assert(hb.feature(k, #k, feats[i]) == 1)
		feats[i].value = v
		i = i + 1
	end
	return feats, feats_count
end

--convert a tree of nested text runs into a flat list of runs with properties
--dynamically inherited from the parent nodes.
--one text run is always created, even when there's no text.
local function flatten_text_tree(parent, runs)
	for i = 1, math.max(1, #parent) do
		local run_or_text = parent[i] or ''
		local run
		if type(run_or_text) == 'string' then
			run = {text = run_or_text}
			push(runs, run)
		else
			run = run_or_text
			flatten_text_tree(run, runs)
		end
		--TODO: make features individually inheritable.
		if run.features then
			run.features, run.feat_count = hb_feature_list(run.features)
		end
		run.__index = parent
		setmetatable(run, run)
	end
	return runs
end

local alloc_str = growbuffer'uint32_t[?]'
local alloc_scripts = growbuffer'hb_script_t[?]'
local alloc_langs = growbuffer'hb_language_t[?]'
local alloc_bidi_types = growbuffer'FriBidiCharType[?]'
local alloc_bracket_types = growbuffer'FriBidiBracketType[?]'
local alloc_levels = growbuffer'FriBidiLevel[?]'
local alloc_linebreaks = growbuffer'char[?]'

local tr_free = tr.free
function tr:free()
	alloc_str, alloc_scripts, alloc_langs,
	alloc_bidi_types, alloc_bracket_types, alloc_levels,
	alloc_linebreaks, alloc_grapheme_breaks = nil
	tr_free(self)
end

function tr:shape(text_tree)

	local text_runs = flatten_text_tree(text_tree, {})

	--find (font, size) of each text run and get text length in codepoints.
	local len = 0
	for _,run in ipairs(text_runs) do

		--find (font, size) of each run.
		run.font, run.font_size = self.rs.font_db:find_font(
			run.font_name,
			run.font_weight,
			run.font_slant,
			run.font_size
		)
		assert(run.font, 'Font not found: %s', run.font_name)
		assert(run.font_size, 'Font size missing')
		run.font_size = snap(run.font_size, self.rs.font_size_resolution)

		--find length in codepoints of each run.
		run.text_size = run.text_size or #run.text
		assert(run.text_size, 'text buffer size missing')
		run.charset = run.charset or 'utf8'
		if run.charset == 'utf8' then
			run.len = utf8.decode(run.text, run.text_size, false)
		elseif run.charset == 'utf32' then
			run.len = math.floor(run.text_size / 4)
		else
			assert(false, 'invalid charset: %s', run.charset)
		end

		len = len + run.len
	end

	local segments = update({tr = self}, self.segments_class) --{seg1, ...}

	--convert and concatenate text into a single utf32 buffer.
	local str = alloc_str(len)
	local offset = 0
	for _,run in ipairs(text_runs) do
		if run.charset == 'utf8' then
			run.codepoints = ffi.new('uint32_t[?]', run.len)
			utf8.decode(run.text, run.text_size, run.codepoints, run.len)
		elseif run.charset == 'utf32' then
			run.codepoints = ffi.cast('uint32_t*', run.text)
		end
		ffi.copy(str + offset, run.codepoints, run.len * 4)
		run.offset = offset
		offset = offset + run.len
	end

	--detect the script and lang properties for each char of the entire text.
	local scripts = alloc_scripts(len)
	local langs = alloc_langs(len)
	zone'detect_script'
	detect_scripts(str, len, scripts)
	zone()

	--override scripts and langs with user-provided values.
	for _,run in ipairs(text_runs) do
		if run.script then
			local script = hb.script(run.script)
			assert(script, 'invalid script: ', run.script)
			for i = run.offset, run.offset + run.len - 1 do
				scripts[i] = script
			end
		end
		if run.lang then
			local lang = hb.language(run.lang)
			assert(lang, 'invalid lang: ', run.lang)
			for i = run.offset, run.offset + run.len - 1 do
				langs[i] = lang
			end
		end
	end

	--Run fribidi over the entire text as follows:
	--Skip mirroring since harfbuzz seems to do that.
	--Skip arabic shaping since harfbuzz does that better with font assistance.
	--Skip RTL reordering because 1) fribidi also reverses the _contents_ of
	--the RTL runs which harfbuzz also does, and 2) because bidi reordering
	--needs to be done after line breaking and so it's part of layouting.
	zone'bidi'
	local dir = (text_tree.dir or 'auto'):lower()
	local fb_dir =
		   dir == 'rtl'  and fb.C.FRIBIDI_PAR_RTL
		or dir == 'ltr'  and fb.C.FRIBIDI_PAR_LTR
		or dir == 'auto' and fb.C.FRIBIDI_PAR_ON

	local bidi_types    = alloc_bidi_types(len)
	local bracket_types = alloc_bracket_types(len)
	local levels        = alloc_levels(len)

	fb.bidi_types(str, len, bidi_types)
	fb.bracket_types(str, len, bidi_types, bracket_types)
	assert(fb.par_embedding_levels(bidi_types, bracket_types, len, fb_dir, levels))
	zone()

	--run Unicode line breaking over each run of text with same language.
	zone'linebreak'
	local linebreaks = alloc_linebreaks(len)
	for i, len, lang in rle_runs(langs, len) do
		ub.linebreaks(str + i, len, ub_lang(lang), linebreaks + i)
	end
	zone()

	--split text into segments of characters with the same properties
	--and shape those individually with harfbuzz.

	zone'segment'
	local offset = 0
	local seg_i = 0
	local text_run_index = 1
	local text_run = text_runs[1]
	local level, script, lang
	if len == 0 then
		level = dir == 'rtl' and 1 or 0
		script = text_run.script and hb.script(text_run.script) or hb.C.HB_SCRIPT_COMMON
		lang = text_run.lang and hb.language(text_run.lang)
	end
	for i = 0, len do

		--0: break required, 1: break allowed, 2: break not allowed.
		local linebreak = i > 0 and linebreaks[i-1] or 2

		local text_run1, level1, script1, lang1

		if i == len then
			goto process
		end

		--change to the next text_run if we're past the current text run.
		if i > text_run.offset + text_run.len - 1 then
			text_run_index = text_run_index + 1
			text_run1 = text_runs[text_run_index]
		else
			text_run1 = text_run
		end

		level1 = levels[i]
		script1 = scripts[i]
		lang1 = langs[i]

		if i == 0 then
			goto advance
		end

		if linebreak > 1
			and text_run1 == text_run
			and level1 == level
			and script1 == script
			and lang1 == lang
		then
			goto advance
		end

		::process::
		seg_i = seg_i + 1
		segments[seg_i] = {
			--reusable part
			glyph_run = self:glyph_run(
				str, len, offset, i - offset,
				text_run.font,
				text_run.font_size,
				text_run.features,
				text_run.feat_count,
				odd(level),
				script,
				lang
			),
			--non-reusable part
			bidi_level = level, --for bidi reordering
			linebreak = linebreak == 0, --hard break; for layouting
			line_spacing = text_run.line_spacing or 1, --for layouting
			--for cursor positioning
			text_run = text_run,
			offset = offset,
			index = seg_i,
		}
		offset = i

		::advance::
		text_run, level, script, lang = text_run1, level1, script1, lang1
	end
	zone()

	return segments
end

--layouting ------------------------------------------------------------------

local segments = {} --methods for segment list
tr.segments_class = segments

function segments:layout(x, y, w, h, halign, valign)

	halign = halign or 'left'
	valign = valign or 'top'
	assert(halign == 'left' or halign == 'right' or halign == 'center')
	assert(valign == 'top' or valign == 'bottom' or valign == 'middle')

	local lines = update({
		tr = self.tr, segments = self, segmap = {},
	}, self.tr.lines_class)

	--do line wrapping and compute line width and hlsb.
	zone'linewrap'
	local line
	local ax, dx --line x-advance for line width calculation.
	local line_i = 0
	for seg_i, seg in ipairs(self) do
		local run = seg.glyph_run
		if not line or line.advance_x + dx + run.hlsb + run.w > w then
			ax = -run.hlsb
			dx = halign == 'left' and 0 or ax
			line = {
				hlsb = run.hlsb,
				advance_x = 0,
				w = 0,
				ascent = 0, descent = 0,
				spacing_ascent = 0, spacing_descent = 0,
			}
			line_i = line_i + 1
			lines[line_i] = line
		end
		line.w = ax + run.hlsb + run.w
		line.advance_x = line.advance_x + run.advance_x
		ax = ax + run.advance_x
		push(line, seg)
		lines.segmap[seg] = line_i --for cursor positioning
		if seg.linebreak then
			line = nil
		end
	end
	zone()

	--reorder RTL segments on each line separately and concatenate the runs.
	zone'reorder'
	for _,line in ipairs(lines) do
		--link segments with a `next` field as expected by reorder_runs().
		local n = #line
		for i,seg in ipairs(line) do
			seg.next = line[i+1] or false
		end
		local seg = reorder_runs(line[1])
		local i = 0
		while seg do
			i = i + 1
			line[i] = seg
			local next_seg = seg.next
			seg.next = false
			seg = next_seg
		end
		assert(i == n)
	end
	zone()

	for i,line in ipairs(lines) do

		--compute line's aligned x position relative to the textbox.
		if halign == 'left' then
			line.x = 0
		elseif halign == 'right' then
			line.x = w - line.w - line.hlsb
		elseif halign == 'center' then
			line.x = (w - line.w) / 2 - line.hlsb
		end

		--compute line's vertical metrics.
		for _,seg in ipairs(line) do
			local run = seg.glyph_run
			line.ascent = math.max(line.ascent, run.ascent)
			line.descent = math.min(line.descent, run.descent)
			local half_line_gap =
				(run.ascent - run.descent) * (seg.line_spacing - 1) / 2
			line.spacing_ascent
				= math.max(line.spacing_ascent, run.ascent + half_line_gap)
			line.spacing_descent
				= math.min(line.spacing_descent, run.descent - half_line_gap)
		end

		--compute line's y position relative to first line's baseline.
		if i == 1 then
			line.y = 0
		else
			local last_line = lines[i-1]
			line.y = last_line.y - last_line.spacing_descent + line.spacing_ascent
		end
	end

	--compute first line's baseline based on vertical alignment.
	if valign == 'top' then
		lines.baseline = lines[1].spacing_ascent
	else
		if valign == 'bottom' then
			lines.baseline = h - (lines[#lines].y - lines[#lines].spacing_descent)
		elseif valign == 'middle' then
			local lines_h = lines[#lines].y
				+ lines[1].spacing_ascent
				- lines[#lines].spacing_descent
			lines.baseline = lines[1].spacing_ascent + (h - lines_h) / 2
		end
	end

	--store textbox's origin.
	--the textbox can be moved after layouting without requiring re-layouting.
	lines.x = x
	lines.y = y

	return lines
end

local lines = {} --methods for line list
tr.lines_class = lines

tr.default_color = '#fff'

function lines:paint(cr)
	local rs = self.tr.rs
	local default_color = self.tr.default_color
	for _,line in ipairs(self) do

		local ax = self.x + line.x
		local ay = self.y + self.baseline + line.y

		for _,seg in ipairs(line) do
			local run = seg.glyph_run
			rs:setcolor(cr, seg.text_run.color or default_color)

			for i = 0, run.len-1 do

				local glyph_index = run.info[i].codepoint
				local px, py = run:glyph_pos(i)

				local glyph, bmpx, bmpy = rs:glyph(
					run.font, run.font_size, glyph_index, ax + px, ay + py)

				rs:paint_glyph(cr, glyph, bmpx, bmpy)
			end

			ax = ax + run.advance_x
			ay = ay + run.advance_y
		end
	end
	return self
end

function tr:textbox(text_tree, cr, x, y, w, h, halign, valign)
	return self
		:shape(text_tree)
		:layout(x, y, w, h, halign, valign)
		:paint(cr)
end

--hit testing and cursor positions -------------------------------------------

local function cmp_offsets(seg, offset)
	return seg.offset <= offset
end
function segments:cursor_at_text_offset(text_offset)
	local seg_i = (binsearch(text_offset, self, cmp_offsets) or #self + 1) - 1
	local seg = self[seg_i]
	local offsets = seg.glyph_run.cursor_offsets
	local cursor_i = binsearch(text_offset - seg.offset, offsets)
	return seg, cursor_i
end

function segments:text_offset_at_cursor(seg, cursor_i)
	return seg.offset + seg.glyph_run.cursor_offsets[cursor_i]
end

--move `delta` cursor positions from a certain cursor position.
function segments:next_cursor(seg, cursor_i, delta)
	delta = math.floor(delta or 0) --prevent infinite loop
	local step = delta > 0 and 1 or -1
	while delta ~= 0 do
		local i = cursor_i + step
		if (step < 0 and i < 1) or i > #seg.glyph_run.cursor_offsets then
			local next_seg = self[seg.index + step]
			if not next_seg then
				break
			end
			seg = next_seg
			i = step > 0 and 1 or #seg.glyph_run.cursor_offsets
		end
		cursor_i = i
		delta = delta - step
	end
	return seg, cursor_i, delta
end

local function cmp_ys(line, y)
	return line.y - line.spacing_descent < y
end
function lines:hit_test_lines(x, y,
	extend_top, extend_bottom, extend_left, extend_right
)
	x = x - self.x
	y = y - (self.y + self.baseline)
	if y < -self[1].spacing_ascent then
		return extend_top and 1 or nil
	elseif y > self[#self].y - self[#self].spacing_descent then
		return extend_bottom and #self or nil
	else
		local i = binsearch(y, self, cmp_ys) or #self
		local line = self[i]
		return (extend_left or x >= line.x)
			and (extend_right or x <= line.x + line.advance_x)
			and i or nil
	end
end

function lines:hit_test_cursors(line_i, x, extend_left, extend_right)
	local line = self[line_i]
	local ax = self.x + line.x
	for seg_i, seg in ipairs(line) do
		local run = seg.glyph_run
		local x = x - ax
		if ((extend_left and seg_i == 1) or x >= 0)
			and ((extend_right and seg_i == #line) or x <= run.advance_x)
		then
			--find the cursor position closest to x.
			local xs = run.cursor_xs
			local min_d, cursor_i = 1/0
			for i = 1, #xs do
				local d = math.abs(xs[i] - x)
				if d < min_d then
					min_d, cursor_i = d, i
				end
			end
			return seg, cursor_i
		end
		ax = ax + run.advance_x
	end
end

function lines:hit_test(x, y,
	extend_top, extend_bottom, extend_left, extend_right
)
	local line_i = self:hit_test_lines(x, y,
		extend_top, extend_bottom, extend_left, extend_right
	)
	if not line_i then return nil end
	return line_i, self:hit_test_cursors(line_i, x, extend_left, extend_right)
end

function lines:text_offset_at_cursor(seg, cursor_i)
	return self.segments:text_offset_at_cursor(seg, cursor_i)
end

function lines:cursor_pos(seg, cursor_i)
	local line = self[self.segmap[seg]]
	local ax = self.x + line.x
	local ay = self.y + self.baseline + line.y
	--TODO: store segment offsets to avoid O(n) when displaying cursors?
	local target_seg = seg
	for _,seg in ipairs(line) do
		local run = seg.glyph_run
		if seg == target_seg then
			return
				ax + run.cursor_xs[cursor_i],
				ay - line.ascent,
				line.ascent - line.descent --cursor height
		end
		ax = ax + run.advance_x
		ay = ay + run.advance_y
	end
end

--cursor object --------------------------------------------------------------

local cursor = {}
setmetatable(cursor, cursor)
tr.cursor_class = cursor

function segments:cursor(text_offset)
	self = update({
		tr = self.tr,
		segments = self,
	}, self.tr.cursor_class)
	self:set_text_offset(text_offset or 0)
	return self
end

function cursor:setlines(lines)
	assert(lines.segments == self.segments)
	self.lines = lines
end

function cursor:set_text_offset(text_offset)
	self.seg, self.cursor_i = self.segments:cursor_at_text_offset(text_offset)
	self.text_offset = self.segments:text_offset_at_cursor(self.seg, self.cursor_i)
end

--text position -> layout position.
function cursor:pos()
	return self.lines:cursor_pos(self.seg, self.cursor_i)
end

--layout position -> text position.
function cursor:hit_test(x, y, ...)
	local line_i, seg, cursor_i = self.lines:hit_test(x, y, ...)
	if not cursor_i then return nil end
	return self.lines:text_offset_at_cursor(seg, cursor_i), seg, cursor_i, line_i
end

--move based on a layout position.
function cursor:move_to(x, y, ...)
	local text_offset, seg, cursor_i = self:hit_test(x, y, ...)
	if text_offset then
		self.text_offset, self.seg, self.cursor_i = text_offset, seg, cursor_i
	end
end

function cursor:next_cursor(delta)
	local text_offset, seg, cursor_i = self.text_offset, self.seg, self.cursor_i
	local step = (delta or 1) > 0 and 1 or -1
	::again::
	seg, cursor_i, delta = self.segments:next_cursor(seg, cursor_i, delta)
	if delta == 0
		and self.segments:text_offset_at_cursor(seg, cursor_i) == text_offset
		and self.lines:cursor_pos(seg, cursor_i) == self:pos()
	then
		--duplicate cursor (same text position and same screen position):
		--advance further until a different one is found.
		delta = step
		goto again
	end
	text_offset = self.segments:text_offset_at_cursor(seg, cursor_i)
	return text_offset, seg, cursor_i, delta
end

function cursor:next_line(delta)
	local text_offset, seg, cursor_i = self.text_offset, self.seg, self.cursor_i
	local x = self.x or self:pos()
	local wanted_line_i = self.lines.segmap[seg] + delta
	local line_i = clamp(wanted_line_i, 1, #self.lines)
	local delta = wanted_line_i - line_i
	local line = self.lines[line_i]
	local seg1, cursor_i1 = self.lines:hit_test_cursors(line_i, x, true, true)
	if seg1 then
		seg, cursor_i = seg1, cursor_i1
		text_offset = self.segments:text_offset_at_cursor(seg, cursor_i)
		delta = 0
	end
	return text_offset, seg, cursor_i, x, delta
end

function cursor:move(dir, delta)
	if dir == 'horiz' then
		self.text_offset, self.seg, self.cursor_i = self:next_cursor(delta)
		self.x = false
	elseif dir == 'vert' then
		self.text_offset, self.seg, self.cursor_i, self.x = self:next_line(delta)
	else
		assert(false, 'invalid direction %s', dir)
	end
end

--selection object -----------------------------------------------------------

local selection = {}
setmetatable(selection, selection)
tr.selection_class = selection

function segments:selection(text_offset1, text_offset2)
	self = update({
		tr = self.tr,
		segments = self,
		cursor1 = self:cursor(text_offset1),
		cursor2 = self:cursor(text_offset2),
	}, self.tr.selection_class)
	return self
end

function selection:interval_pos()

end

return tr
