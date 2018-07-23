
## `local tr = require'tr'`

Unicode text shaping and rendering engine using exclusively portable
technologies for pixel-perfect consistent output across platforms.

Complex text shaping based on [harfbuzz] and [fribidi]. Glyph caching
and rasterization based on [freetype].

Features:

  * subpixel positioning
  * OMG color emoticons!
  * rich text markup lanugage
  * word wrapping
  * cursor positioning information for editing
  * control over OpenType features
  * font database for font selection
  * OpenType-assisted auto-hinter enabled in freetype

Note: this is a support lib for [ui] but can be used standalone.
