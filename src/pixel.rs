//! Pixel formats types and function manipulation.
//!
//! The `Pixel` trait is used to reify a pixel type at runtime via `PixelFormat`.

/// Reify a static pixel format to runtime.
pub trait Pixel {
  /// Encoding of a single pixel. It should match the `PixelFormat` mapping.
  type Encoding;
  /// Raw encoding of a single pixel; i.e. that is, encoding of underlying values in contiguous
  /// texture memory. It should be match the `PixelFormat` mapping.
  type RawEncoding;

  fn pixel_format() -> PixelFormat;
}

/// Constraint on `Pixel` for color ones.
pub trait ColorPixel: Pixel {}

/// Constraint on `Pixel` for depth ones.
pub trait DepthPixel: Pixel {}

/// Constaint on `Pixel` for renderable ones.
pub trait RenderablePixel: Pixel {}

/// A `PixelFormat` gathers a `Type` along with a `Format`.
#[derive(Clone, Copy, Debug)]
pub struct PixelFormat {
    pub encoding: Type
  , pub format: Format
}

/// Pixel type.
#[derive(Clone, Copy, Debug)]
pub enum Type {
  Integral,
  Unsigned,
  Floating
}

/// Format of a pixel.
///
/// Whichever the constructor you choose, the carried `u8`s represents how many bytes are used to
/// represent each channel.
#[derive(Clone, Copy, Debug)]
pub enum Format {
    /// Holds a red-only channel.
  R(u8),
    /// Holds red and green channels. 
  RG(u8, u8),
  /// Holds red, green and blue channels.
  RGB(u8, u8, u8),
  /// Holds red, green, blue and alpha channels.
  RGBA(u8, u8, u8, u8),
  /// Holds a depth channel.
  Depth(u8)
}

/// Does a `PixelFormat` represent a color?
pub fn is_color_pixel(f: PixelFormat) -> bool {
  match f.format {
      Format::Depth(_) => false
    , _ => true
  }
}

/// Does a `PixelFormat` represent depth information?
pub fn is_depth_pixel(f: PixelFormat) -> bool {
  !is_color_pixel(f)
}

/// A red, green and blue 8-bit unsigned pixel format.
#[derive(Clone, Copy, Debug)]
pub struct RGB8UI;

impl Pixel for RGB8UI {
  type Encoding = (u8, u8, u8);
  type RawEncoding = u8;

  fn pixel_format() -> PixelFormat {
    PixelFormat {
        encoding: Type::Unsigned
      , format: Format::RGB(8, 8, 8)
    }
  }
}

impl ColorPixel for RGB8UI {}

/// A red, green, blue and alpha 8-bit unsigned pixel format.
#[derive(Clone, Copy, Debug)]
pub struct RGBA8UI;

impl Pixel for RGBA8UI {
  type Encoding = (u8, u8, u8, u8);
  type RawEncoding = u8;

  fn pixel_format() -> PixelFormat {
    PixelFormat {
        encoding: Type::Unsigned
      , format: Format::RGBA(8, 8, 8, 8)
    }
  }
}

impl ColorPixel for RGBA8UI {}

impl RenderablePixel for RGBA8UI {}

/// A red, green and blue 32-bit floating pixel format.
#[derive(Clone, Copy, Debug)]
pub struct RGB32F;

impl Pixel for RGB32F {
  type Encoding = (f32, f32, f32);
  type RawEncoding = f32;

  fn pixel_format() -> PixelFormat {
    PixelFormat {
        encoding: Type::Floating
      , format: Format::RGB(32, 32, 32)
    }
  }
}

impl ColorPixel for RGB32F {}

/// A red, green, blue and alpha 32-bit floating pixel format.
#[derive(Clone, Copy, Debug)]
pub struct RGBA32F;

impl Pixel for RGBA32F {
  type Encoding = (f32, f32, f32, f32);
  type RawEncoding = f32;

  fn pixel_format() -> PixelFormat {
    PixelFormat {
        encoding: Type::Floating
      , format: Format::RGBA(32, 32, 32, 32)
    }
  }
}

impl ColorPixel for RGBA32F {}

impl RenderablePixel for RGBA32F {}

/// A depth 32-bit floating pixel format.
#[derive(Clone, Copy, Debug)]
pub struct Depth32F;

impl Pixel for Depth32F {
  type Encoding = f32;
  type RawEncoding = f32;

  fn pixel_format() -> PixelFormat {
    PixelFormat {
        encoding: Type::Floating
      , format: Format::Depth(32)
    }
  }
}

impl DepthPixel for RGBA32F {}
