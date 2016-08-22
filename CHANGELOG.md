### 0.6.3

- Added `get_raw_texels` to `Texture`.

### 0.6.2

- Added `upload_part_raw` and `upload_raw` to `Texture`, enabling to upload raw texels instead of
  texels directly.
- Added `RawEncoding` to `Pixel`.

### 0.6.1

- Added documentation field in Cargo.toml.

## 0.6.0

- Removed `Default` implementation for `Framebuffer` and added a new `default()` method, taking the
  size of the `Framebuffer`.
- Added `RenderablePixel` trait bound on `Slot` implementations for `ColorPixel`.
- Added `RenderablePixel`.
- Removed the need of the **core** crate.
- Removed `UniformName`.
- We can now have textures as uniforms.
- New uniform system to accept value depending on the backend.
- Using `AsRef` instead of ATexture in `update_textures`.
- Changed the meaning of mipmaps (now it’s the number of extra mipmaps).
- Using `usize` instead of `u32` for mipmaps.
- Added `Dimensionable` and `Layerable` in the interface.

### 0.5.3

- Added `update_textures` into `HasUniform`.
- Fixed signature of `UniformUpdate::update`.
- Fixed trait bound on `UniformUpdate::{contramap, update}`.

### 0.5.2

- Added `UniformUpdate`.
- Added `Uniformable` in the public interfarce shortcut.

### 0.5.1

- Removed `run_pipeline` and added `Pipeline::run`.

## 0.5.0

- Fixed uniform interfaces in `ShadingCommand` and `RenderCommand` with existential quantification.
- Renamed `FrameCommand` into `Pipeline`.
- Several patch fixes.
- Added travis CI support.
- Added documentation for `Program`.

## 0.4.0

- Changed the whole `Program` API to make it safer. Now, it closely looks like the Haskell version
  of `luminance`. The idea is that the user cannot have `Uniform`s around anymore as they’re held by
  `Program`s. Furthermore, the *uniform interface* is introduced. Because Rust doesn’t have a
  **“rank-2 types”** mechanism as Haskell, `ProgramProxy` is introduced to emulate such a behavior.
- Added a bit of documentation for shader programs.

### 0.3.1

- Removed `rw`.

## 0.3.0

- Removed A type parameter form `Buffer`. It was unnecessary safety that was never actually used.
- Added documentation around.

### 0.2.1

- Exposed `Vertex` directly in `luminance`.

## 0.2.0

- Changed `Negative*` blending factors to `*Complement`.

## 0.1.0

- Initial revision.
