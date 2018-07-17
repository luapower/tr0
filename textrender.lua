
--Text shaping and rendering based on harfbuzz and freetype.
--Written by Cosmin Apreutesei. Public Domain.

if not ... then require'textrender_demo'; return end

local ffi = require'ffi'
local bit = require'bit'
local hb = require'harfbuzz'
local ft = require'freetype'
local fb = require'fribidi'
local ub = require'libunibreak'
local glue = require'glue'
local tuple = require'tuple'
local lrucache = require'lrucache'
local cairo = require'cairo'

local merge = glue.merge
local object = glue.object
local snap = glue.snap
local assert = glue.assert --assert with string formatting
local count = glue.count
local attr = glue.attr
local trim =glue.trim

--font selection -------------------------------------------------------------

local font_db = object()

function font_db:__call()
	self = object(self, {})
	self.db = {} --{name -> {slant -> {weight -> font}}}
	self.namecache = {} --{name -> font}
	self.searchers = {} --{searcher1, ...}
	return self
end

function font_db:free() end --stub

font_db.weights = {
	thin       = 100,
	extralight = 200,
	light      = 300,
	semibold   = 600,
	bold       = 700,
	extrabold  = 800,
}

font_db.slants = {
	italic  = 'italic',
	oblique = 'italic',
}

local function str(s)
	s = s and trim(s):lower():gsub('[%-%s_]+', '_')
	return s ~= '' and s or nil
end

local function fontname(s)
	local s = str(s)
	return s and s
		:gsub('_regular$', '') --remove 'regular' suffix
		:gsub('_?%d+%.%d+$', '') --remove version suffix
end

--TODO: invalid weights and slants in `name' are silently ignored,
--but accepted in overrides.
function font_db:parse_font(name, weight, slant, size)
	local s1, s2, s3
	if type(name) == 'string' then
		if name:find(',', 1, true) then
			name, s1, s2, s3 = name:match'([^,]*),?([^,]*),?([^,]*),?([^,]*)'
			s1 = str(s1)
			s2 = str(s2)
			s3 = str(s3)
		end
		name = fontname(name)
	end
	local w = self.weights
	local s = self.slants
	weight = w[weight] or tonumber(weight) or weight or w[s1] or w[s2] or w[s3]
	slant = s[slant] or slant or s[s1] or s[s2] or s[s3]
	size = tonumber(size) or size or tonumber(s1) or tonumber(s2) or tonumber(s3)
	return name, weight, slant, size
end

--NOTE: multiple (name, weight, slant) can be registered with the same font.
--NOTE: `name' doesn't have to be a string, it can be any indexable value.
function font_db:add_font(font, name1, weight1, slant1)
	local name, weight, slant = self:parse_font(name1, weight1, slant1)
	attr(attr(self.db, name or false), slant or 'normal')[weight or 400] = font
end

local function closest_weight(t, wanted_weight)
	local font = t[wanted_weight] --direct lookup
	if font then
		return font
	end
	local best_diff = 1/0
	local best_font
	for weight, font in pairs(t) do
		local diff = math.abs(wanted_weight - weight)
		if diff < best_diff then
			best_diff = diff
			best_font = font
		end
	end
	return best_font
end
function font_db:font(name, weight, slant, size)
	local name_only = not (weight or slant or size)
	local font = name_only and self.namecache[name] --try to skip parsing
	if font then
		return font
	end
	local name, weight, slant, size = self:parse_font(name, weight, slant, size)
	local t = self.db[name or false]
	local t = t and t[slant or 'normal']
	local font = t and closest_weight(t, weight or 400)
	if font and name_only then
		self.namecache[name] = font
	end
	return font, size
end

function font_db:dump()
	local weight_names = glue.index(self.weights)
	weight_names[400] = 'regular'
	for name,t in glue.sortedpairs(self.db) do
		local dt = {}
		for slant,t in glue.sortedpairs(t) do
			for weight, font in glue.sortedpairs(t) do
				local weight_name = weight_names[weight]
				dt[#dt+1] = weight_name..' ('..weight..')'..' '..(slant or '')
			end
		end
		print(string.format('%-30s %s', tostring(name), table.concat(dt, ', ')))
	end
end

--text rendering -------------------------------------------------------------

local render = object()

render.glyph_cache_size = 1024^2 * 20 --20MB net (arbitrary default)
render.font_size_step = 1/8 --font size granularity (arbitrary default)
render.subpixel_step = 1/64 --subpixel resolution (1/64 is max with freetype)

function render:__call()
	local self = object(self, {})

	--speed up method access by caching methods
	local super = self.__index
	while super do
		merge(self, super)
		super = super.__index
	end

	self.freetype = ft()
	self.loaded_fonts = {} --{data -> font}
	self.font_db = font_db()

	self.glyphs = lrucache{max_size = self.glyph_cache_size}
	function self.glyphs:value_size(glyph)
		return glyph:size()
	end
	function self.glyphs:free_value(glyph)
		glyph:free()
	end

	return self
end

function render:free()
	if not self.freetype then return end

	if self.hb_buf then
		self.hb_buf:free()
		self.hb_buf = false
	end

	self.glyphs:free()

	for font in pairs(self.loaded_fonts) do
		self:unload_font(font)
	end
	self.fonts = false

	self.freetype:free()
	self.freetype = false

	self.font_db:free()
	self.font_db = false
end

--font loading ---------------------------------------------------------------

function render:add_font_file(file, ...)
	local font = {file = file, load = self.load_font_file}
	self.font_db:add_font(font, ...)
end

function render:add_mem_font(data, data_size, ...)
	local font = {data = data, data_size = data_size, load = self.load_mem_font}
	self.font_db:add_font(font, ...)
end

function render:load_font_file(font)
	local bundle = require'bundle'
	local mmap = bundle.mmap(font.file)
	assert(mmap, 'Font file not found: %s', font.file)
	font.data = mmap.data
	font.data_size = mmap.size
	font.mmap = mmap --pin it
	self:load_mem_font(font)
end

render.use_internal_font_name = true --use internal font name

function render:load_mem_font(font, ...)

	local ft_face = assert(self.freetype:memory_face(font.data, font.data_size))
	font.ft_face = ft_face
	font.hb_font = assert(hb.ft_font(ft_face, nil))
	font.size_info = {} --{size -> info_table}

	--font info
	font.ft_name = ffi.string(ft_face.family_name)
	font.ft_style = ffi.string(ft_face.style_name)
	font.ft_italic = bit.band(ft_face.style_flags, ft.C.FT_STYLE_FLAG_ITALIC) ~= 0
	font.ft_bold = bit.band(ft_face.style_flags, ft.C.FT_STYLE_FLAG_BOLD) ~= 0

	font.loaded = true
	self.loaded_fonts[font] = true

	if self.use_internal_font_name then
		--infer missing font's attributes from the font itself and register
		--another font with those attributes.
		local name, weight, slant = ...
		if not name and font.ft_name then
			name = fontname(font.ft_name)
		end
		if not slant then
			if font.ft_italic then
				slant = 'italic'
			elseif str(font.ft_style or ''):find'italic' then
				slant = 'italic'
			end
		end
		if not weight then
			if font.ft_bold then
				weight = 'bold'
			elseif font.ft_style then
				local style = str(font.ft_style)
				for weight_name, weight_num in pairs(self.font_db.weights) do
					if style:find(weight_name) then
						weight = weight_num
					end
				end
			end
		end
		self.font_db:add_font(font, name, weight, slant)
	end
end

function render:font(...)
	local font, size = self.font_db:font(...)
	assert(font, 'Font not found: %s', (...))
	if not font.loaded then
		font.load(self, font, ...)
	end
	return font, size
end

function render:unload_font(font)
	if not font.loaded then return end
	font.hb_font:free()
	font.ft_face:free()
	font.hb_font = false
	font.ft_face = false
	font.loaded = false
	self.loaded_fonts[font] = nil
end

--glyph rendering ------------------------------------------------------------

function render:_select_font_size_index(face, size)
	local best_diff = 1/0
	local index, best_size
	for i=0,face.num_fixed_sizes-1 do
		local sz = face.available_sizes[i]
		local this_size = sz.width / 64
		local diff = math.abs(size - this_size)
		if diff < best_diff then
			index = i
			best_size = this_size
		end
	end
	return index, best_size or size
end

function render:setfont(name, weight, slant, size)

	local font, size = self:font(name, weight, slant, size)
	assert(size, 'Invalid font size for: %s (%s)', name, tostring(size))
	local face = font.ft_face

	local size = snap(size, self.font_size_step)
	local info = font.size_info[size]
	if not info then
		local size_index, fixed_size = self:_select_font_size_index(face, size)
		info = font.size_info[fixed_size]
		if not info then
			info = {
				size = fixed_size,
				size_index = size_index,
				font_key = tuple(font, fixed_size),
			}
			font.size_info[fixed_size] = info
		end
		font.size_info[size] = info
	end

	self.current_font = font
	self.size = size
	self.size_info = info
end

render.ft_load_mode = bit.bor(
	0
	,ft.C.FT_LOAD_COLOR
	--,ft.C.FT_LOAD_IGNORE_TRANSFORM
	,ft.C.FT_LOAD_PEDANTIC
	--,ft.C.FT_LOAD_NO_HINTING
	--,ft.C.FT_LOAD_NO_AUTOHINT
	--ft.C.FT_LOAD_NO_SCALE
	)
render.ft_render_mode = bit.bor(
	ft.C.FT_RENDER_MODE_LIGHT --disable hinting on the x-axis
)

local empty_glyph = {}

function render:rasterize_glyph(glyph_index, x_offset)

	local font = self.current_font
	local face = font.ft_face

	local info = self.size_info
	if font.size_info ~= info then
		if info.size_index then
			face:select_size(info.size_index)
		else
			face:set_pixel_sizes(info.size)
		end
		font.size_info = info
	end
	if not info.line_h then
		info.line_h = face.size.metrics.height / 64
		info.ascender = face.size.metrics.ascender / 64
	end

	face:load_glyph(glyph_index, self.ft_load_mode)

	local glyph = face.glyph

	if glyph.format == ft.C.FT_GLYPH_FORMAT_OUTLINE then
		glyph.outline:translate(x_offset * 64, 0)
	end
	local fmt = glyph.format
	if glyph.format ~= ft.C.FT_GLYPH_FORMAT_BITMAP then
		glyph:render(self.ft_render_mode)
	end
	assert(glyph.format == ft.C.FT_GLYPH_FORMAT_BITMAP)

	--BGRA bitmaps must already have aligned pitch because we can't change that
	assert(glyph.bitmap.pixel_mode ~= ft.C.FT_PIXEL_MODE_BGRA
		or glyph.bitmap.pitch % 4 == 0)

	--bitmaps must be top-down because we can't change that
	assert(glyph.bitmap.pitch >= 0) --top-down

	local bitmap = self.freetype:bitmap()

	if glyph.bitmap.pixel_mode ~= ft.C.FT_PIXEL_MODE_GRAY
		or glyph.bitmap.pitch % 4 ~= 0
	then
		self.freetype:convert_bitmap(glyph.bitmap, bitmap, 4)
		assert(bitmap.pixel_mode == ft.C.FT_PIXEL_MODE_GRAY)
		assert(bitmap.pitch % 4 == 0)
	else
		self.freetype:copy_bitmap(glyph.bitmap, bitmap)
	end

	local ft_glyph = glyph
	local glyph = {}

	glyph.bitmap = bitmap
	glyph.bitmap_left = ft_glyph.bitmap_left
	glyph.bitmap_top = ft_glyph.bitmap_top

	local freetype = self.freetype
	function glyph:free()
		freetype:free_bitmap(self.bitmap)
	end

	function glyph:size()
		return self.bitmap.width * self.bitmap.rows
	end

	return glyph
end

function render:glyph(glyph_index, x, y)
	local pixel_x = math.floor(x)
	local x_offset = snap(x - pixel_x, self.subpixel_step)
	local key = tuple(self.font_key, glyph_index, x_offset)
	local glyph = self.glyphs:get(key)
	if not glyph then
		glyph = self:rasterize_glyph(glyph_index, x_offset)
		self.glyphs:put(key, glyph, glyph.size)
	end
	local x = pixel_x + glyph.bitmap_left
	local y = y - glyph.bitmap_top
	return glyph, x, y
end

function render:paint_glyph(glyph, x, y) end --stub

--cairo render ---------------------------------------------------------------

local cairo_render = object(render)

cairo_render.rasterize_glyph_freetype = render.rasterize_glyph

function cairo_render:rasterize_glyph(glyph_index, x_offset)

	local glyph = self:rasterize_glyph_freetype(glyph_index, x_offset)

	glyph.surface = cairo.image_surface{
		data = glyph.bitmap.buffer,
		format = glyph.bitmap.pixel_mode == ft.C.FT_PIXEL_MODE_BGRA
			and 'bgra8' or 'g8',
		w = glyph.bitmap.width,
		h = glyph.bitmap.rows,
		stride = glyph.bitmap.pitch,
	}

	local free_bitmap = glyph.free
	function glyph:free()
		free_bitmap(self)
		self.surface:free()
	end

	return glyph
end

function cairo_render:paint_glyph(glyph, x, y)
	local cr = self.cr
	if glyph.surface:format() == 'a8' then
		cr:mask(glyph.surface, x, y)
	else
		cr:source(glyph.surface, x, y)
		cr:paint(glyph.surface, x, y)
		cr:rgb(0, 0, 0) --clear source
	end
end

--unicode text shaping -------------------------------------------------------

function render:shape_text(s, len, direction, script, language, features)
	local buf = self.hb_buf
	if not buf then
		buf = hb.buffer()
		self.hb_buf = buf
	end

	buf:set_direction(direction or hb.C.HB_DIRECTION_LTR)
	buf:set_script(script or hb.C.HB_SCRIPT_UNKNOWN)
	if language then
		buf:set_language(language)
	end

	buf:add_utf8(s, len)

	local feats, feats_count = nil, 0
	if features then
		feats_count = count(features)
		feats = ffi.new('hb_feature_t[?]', feats_count)
		local i = 0
		for k,v in pairs(features) do
			assert(hb.feature(k, #k, feats[i]) == 1)
			feats[i].value = v
			i = i + 1
		end
	end

	local font = self.current_font
	buf:shape(font.hb_font, feats, feats_count)
end

function render:clear()
	self.hb_buf:clear()
end

function render:paint_text(x, y)
	local buf = self.hb_buf

	local glyph_count = buf:get_length()
	local glyph_info  = buf:get_glyph_infos()
	local glyph_pos   = buf:get_glyph_positions()

	for i=0,glyph_count-1 do

		local glyph_index = glyph_info[i].codepoint

		local px = x + glyph_pos[i].x_offset / 64
		local py = y - glyph_pos[i].y_offset / 64

		local glyph, px, py = self:glyph(glyph_index, px, py)
		self:paint_glyph(glyph, px, py)

		x = x + glyph_pos[i].x_advance / 64
		y = y - glyph_pos[i].y_advance / 64
	end
end

--module ---------------------------------------------------------------------

return {
	font_db = font_db,
	render = render,
	cairo_render = cairo_render,
}

