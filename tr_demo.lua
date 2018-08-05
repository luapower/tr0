
local tr = require'tr'
local nw = require'nw'
local bundle = require'bundle'
local gfonts = require'gfonts'
local time = require'time'
local box2d = require'box2d'

local tr = tr()

nw:app():maxfps(1/0)

local function fps_function()
	local count_per_sec = 2
	local frame_count, last_frame_count, last_time = 0, 0
	return function()
		last_time = last_time or time.clock()
		frame_count = frame_count + 1
		local time = time.clock()
		if time - last_time > 1 / count_per_sec then
			last_frame_count, frame_count = frame_count, 0
			last_time = time
		end
		return last_frame_count * count_per_sec
	end
end

local fps = fps_function()

local win = nw:app():window{
	x = 100, y = 60,
	w = 1800, h = 900,
	--w = 800, h = 600,
}

local function font(file, name)
	local name = name or assert(file:match('([^\\/]+)%.[a-z]+$')):lower()
	local font = tr:add_font_file(file, name)
	--print(font:internal_name())
end

local function gfont(name)
	local file = assert(gfonts.font_file(tr.rs.font_db:parse_font(name)))
	font(file, name)
end

gfont'eb garamond'
gfont'dancing script'
gfont'open sans'
gfont'open sans italic'
gfont'open sans bold italic'
gfont'open sans 300'
gfont'open sans 300 italic'
font'media/fonts/NotoColorEmoji.ttf'
--font'media/fonts/NotoEmoji-Regular.ttf'
--font'media/fonts/EmojiSymbols-Regular.ttf'
--font'media/fonts/SubwayTicker.ttf'
--font'media/fonts/dotty.ttf'
--font'media/fonts/ss-emoji-microsoft.ttf'
--font'media/fonts/Hand Faces St.ttf'
--font'media/fonts/FSEX300.ttf'
font'media/fonts/amiri-regular.ttf'

--tr.rs.font_db:dump()

local function rect(cr, r, g, b, x, y, w, h)
	cr:save()
	cr:rectangle(x, y, w, h)
	cr:line_width(1)
	cr:rgb(r, g, b)
	cr:stroke()
	cr:restore()
end

local text = require'glue'.readfile('winapi_history.md')

function win:repaint()
	self:title(string.format('%d fps', fps()))

	local cr = self:bitmap():cairo()
	--cr:rgb(1, 1, 1); cr:paint(); cr:rgb(0, 0, 0)
	cr:rgb(0, 0, 0); cr:paint(); cr:rgb(1, 1, 1)

	local t0 = time.clock()

	if false then

		local segs = tr:shape{
			('\xF0\x9F\x98\x81'):rep(2), font_name = 'NotoColorEmoji,34',
		}
		local x, y, w, h = 100, 100, 80, 80
		rect(cr, .5, .5, .5, x, y, w, h)
		tr:paint(cr, segs, x, y, w, h, 'center', 'bottom')

	elseif true then

		--local s1 = ('gmmI '):rep(1)
		--local s2 = ('fi AV (ثلاثة 1234 خمسة) '):rep(1)
		--local s3 = ('Hebrew (אדםה (adamah))'):rep(1)

		local x, y, w, h = box2d.offset(-50, 0, 0, win:client_size())
		rect(cr, .5, .5, .5, x, y, w, h)

		self.segs = self.segs or tr:shape{
			line_spacing = 1.2,
			--dir = 'rtl',
			--{'A'},
			{font_name = 'eb garamond, 200', 'Dgt DD\nDD Dg'},
			--{font_name = 'amiri,200', 'خمسة المفاتيح ABC\n'},
			--{font_name = 'eb garamond, 200', 'fa AVy ffi fl lg MM f\nDEF EF F D glm\n'},
			--{font_name = 'NotoColorEmoji,34', ('\xF0\x9F\x98\x81'):rep(3)},
		}
		self.lines = self.segs:layout(x, y, w, h, 'center', 'bottom')
		self.lines:paint(cr)

		if self.rr then
			rect(cr, 1, 1, 0, unpack(self.rr))
			rect(cr, 1, 0, 0, unpack(self.rr1))
			rect(cr, 1, 1, 1, unpack(self.rr2))
			rect(cr, 1, 0, 1, unpack(self.rr3))
		end

	end

	--local s = (time.clock() - t0)
	--print(string.format('%0.2f ms    %d fps', s * 1000, 1 / s))
	--print(string.format('word  cache size:  %d KB', tr.glyph_runs.total_size / 1024))
	--print(string.format('word  count:       %d   ', tr.glyph_runs.lru.length))
	--print(string.format('glyph cache size:  %d KB', tr.rs.glyphs.total_size / 1024))
	--print(string.format('glyph count:       %d   ', tr.rs.glyphs.lru.length))
	--self:invalidate()
end

function win:mousemove(mx, my)
	if not self.lines then return end
	local line_i, seg,
		x, y, w, h,
		x1, y1, w1, h1,
		x2, y2, w2, h2,
		x3, y3, w3, h3
			= self.lines:hit_test(mx, my)
	if seg then
		self.rr = {x, y, w, h}
		self.rr1 = {x1, y1, w1, h1}
		self.rr2 = {x2, y2, w2, h2}
		self.rr3 = {x3, y3, w3, h3}
	else
		self.rr = false
	end
	self:invalidate()
end

nw:app():run()

tr:free()
