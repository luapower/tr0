
--Text shaping and rendering based on harfbuzz and freetype.
--Written by Cosmin Apreutesei. Public Domain.

if not ... then require'textrender_demo'; return end

local ffi = require'ffi'
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

--freetype render ------------------------------------------------------------

local render = object()

render.cache_size = 1024^2 * 20 --20MB net (arbitrary default)
render.size_step = 1/8 --font size granularity (arbitrary default)
render.x_step = 1/64   --maximum subpixel resolution with freetype's renderer

function render:__call()
	local self = object(self, {})

	--speed up method access by caching methods
	local super = self.__index
	while super do
		merge(self, super)
		super = super.__index
	end

	self.freetype = ft()
	self.fonts = {} --{name -> font_object}

	self.glyphs = lrucache{max_size = self.cache_size}
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

	for _,font in pairs(self.fonts) do
		if font.hb_font then --there are multiple references to the same font
			font.hb_font:free()
			font.ft_face:free()
			font.hb_font = false
			font.ft_face = false
		end
	end
	self.fonts = false

	self.freetype:free()
	self.freetype = false
end

function render:load_font(name, data, data_size)
	name = name:lower()
	local font = self.fonts[name]
	if not font then
		local ft_face = self.freetype:memory_face(data, data_size)
		local hb_font = hb.ft_font(ft_face, nil)
		font = {
			ft_face = ft_face,
			hb_font = hb_font,
			data = data, --pin it
			size_info = {}, --{size -> info_table}
		}
		self.fonts[name] = font
	end
end

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

function render:setfont(name, size)
	local font = self.fonts[name]
	if not font then
		font = self.fonts[name:lower()]
		if font then
			self.fonts[name] = font
		end
	end
	assert(font, 'Font not found: "%s"', name)
	local face = font.ft_face

	local size = snap(size, self.size_step)
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
	self.font = font
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

	local font = self.font
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
	local x_offset = snap(x - pixel_x, self.x_step)
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

function render:paint_text(s, len, x, y, direction, script, language, features)
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

	buf:shape(self.font.hb_font, feats, feats_count)

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

	buf:clear()
end

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

return {
	render = render,
	cairo_render = cairo_render,
}
