
local tr = require'textrender'
local nw = require'nw'
local bundle = require'bundle'
local gfonts = require'gfonts'

local tr = tr.cairo_render()

local win = nw:app():window{
	w = 1800, h = 800,
}

local mmaps = {}
local function load_font(file, name)
	local name = name or assert(file:match('([^\\/]+)%.[a-z]+$')):lower()
	local mmap = assert(bundle.mmap(file), 'Font file not found: '..file)
	tr:load_font(name, mmap.data, mmap.size)
	mmaps[mmap] = true --pin it
end

local function load_gfont(name)
	load_font(assert(gfonts.font_file(name)), name)
end

--load_gfont'Open Sans'
--load_font'media/fonts/NotoColorEmoji.ttf'
--load_font'media/fonts/NotoEmoji-Regular.ttf'
--load_font'media/fonts/EmojiSymbols-Regular.ttf'
--load_font'media/fonts/SubwayTicker.ttf'
--load_font'media/fonts/dotty.ttf'
--load_font'media/fonts/ss-emoji-microsoft.ttf'
--load_font'media/fonts/Hand Faces St.ttf'
load_font'media/fonts/FSEX300.ttf'

--tr:setfont('Open Sans', 14)
--tr:setfont('NotoEmoji-Regular', 109)
--tr:setfont('EmojiSymbols-Regular', 100)
--tr:setfont('SubwayTicker', 15)
--tr:setfont('dotty', 32)
--tr:setfont('ss-emoji-microsoft', 14)
--tr:setfont('Hand Faces St', 14)
tr:setfont('FSEX300', 14)

local ii=0
function win:repaint()
	local cr = self:bitmap():cairo()
	cr:rgb(0, 0, 0)
	cr:paint()
	cr:rgb(1, 1, 1)

	tr.cr = cr

	if false then

		local gi = string.byte('E', 1)
		local maxi = 30--64
		local maxj = 30--64
		for j=0,maxj+5 do
			cr:line_width(1)
			cr:move_to(10+j*20+ii+.5, 0)
			cr:rel_line_to(0, 1000)
			cr:stroke()
			local x0 = j/(maxj+1)
			for i=0,maxi+5 do
				local x = (i/(maxi+1)+x0)
				local y = x > x0+1 and 4 or 0
				tr:paint_glyph(gi, ii+10+x+j*20, 20+y+i*11)
			end
		end

	else

		tr:paint_text('Hello there! هذه هي بعض النصوص العربي', nil, 100, 100)

	end

	ii=ii+1/60
	self:invalidate()
end

nw:app():run()

tr:free()
