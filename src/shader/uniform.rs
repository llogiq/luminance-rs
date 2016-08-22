//! Shader uniforms and associated operations.
//!
//! Uniforms kick in several and useful ways. They’re used to customize shaders.

use std::marker::PhantomData;
use linear::*;
use pixel::{self, Pixel};
use texture::{self, Dimensionable, Layerable, HasTexture, Texture};

pub trait HasUniform: HasTexture {
  /// Uniform representation.
  type U;

  // integral
  fn update1_i32(uniform: &Self::U, x: i32);
  fn update2_i32(uniform: &Self::U, xy: [i32; 2]);
  fn update3_i32(uniform: &Self::U, xyz: [i32; 3]);
  fn update4_i32(uniform: &Self::U, xyzw: [i32; 4]);
  fn update1_slice_i32(uniform: &Self::U, x: &[i32]);
  fn update2_slice_i32(uniform: &Self::U, xy: &[[i32; 2]]);
  fn update3_slice_i32(uniform: &Self::U, xyz: &[[i32; 3]]);
  fn update4_slice_i32(uniform: &Self::U, xyzw: &[[i32; 4]]);
  // unsigned
  fn update1_u32(uniform: &Self::U, x: u32);
  fn update2_u32(uniform: &Self::U, xy: [u32; 2]);
  fn update3_u32(uniform: &Self::U, xyz: [u32; 3]);
  fn update4_u32(uniform: &Self::U, xyzw: [u32; 4]);
  fn update1_slice_u32(uniform: &Self::U, x: &[u32]);
  fn update2_slice_u32(uniform: &Self::U, xy: &[[u32; 2]]);
  fn update3_slice_u32(uniform: &Self::U, xyz: &[[u32; 3]]);
  fn update4_slice_u32(uniform: &Self::U, xyzw: &[[u32; 4]]);
  // floating
  fn update1_f32(uniform: &Self::U, x: f32);
  fn update2_f32(uniform: &Self::U, xy: [f32; 2]);
  fn update3_f32(uniform: &Self::U, xyz: [f32; 3]);
  fn update4_f32(uniform: &Self::U, xyzw: [f32; 4]);
  fn update1_slice_f32(uniform: &Self::U, x: &[f32]);
  fn update2_slice_f32(uniform: &Self::U, xy: &[[f32; 2]]);
  fn update3_slice_f32(uniform: &Self::U, xyz: &[[f32; 3]]);
  fn update4_slice_f32(uniform: &Self::U, xyzw: &[[f32; 4]]);
  fn update22_f32(uniform: &Self::U, x: M22);
  fn update33_f32(uniform: &Self::U, x: M33);
  fn update44_f32(uniform: &Self::U, x: M44);
  fn update22_slice_f32(uniform: &Self::U, x: &[M22]);
  fn update33_slice_f32(uniform: &Self::U, x: &[M33]);
  fn update44_slice_f32(uniform: &Self::U, x: &[M44]);
  // boolean
  fn update1_bool(uniform: &Self::U, x: bool);
  fn update2_bool(uniform: &Self::U, xy: [bool; 2]);
  fn update3_bool(uniform: &Self::U, xyz: [bool; 3]);
  fn update4_bool(uniform: &Self::U, xyzw: [bool; 4]);
  fn update1_slice_bool(uniform: &Self::U, x: &[bool]);
  fn update2_slice_bool(uniform: &Self::U, xy: &[[bool; 2]]);
  fn update3_slice_bool(uniform: &Self::U, xyz: &[[bool; 3]]);
  fn update4_slice_bool(uniform: &Self::U, xyzw: &[[bool; 4]]);
  // textures
  fn update_textures(uniform: &Self::U, textures: &[&Self::ATexture]);
}

/// A shader uniform. `Uniform<C, T>` doesn’t hold any value. It’s more like a mapping between the
/// host code and the shader the uniform was retrieved from.
#[derive(Debug)]
pub struct Uniform<C, T> where C: HasUniform, T: Uniformable<C> {
  pub repr: C::U,
  _t: PhantomData<T>
}

impl<C, T> Uniform<C, T> where C: HasUniform, T: Uniformable<C> {
  pub fn new(repr: C::U) -> Uniform<C, T> {
    Uniform {
      repr: repr,
      _t: PhantomData
    }
  }

  pub fn update(&self, x: T) {
    T::update(self, x);
  }
}

/// Wrapper over `Uniform`, discarding everything but update.
///
/// Among its features, this type enables you to `contramap` a function to build more interesting
/// `UniformUpdate`.
///
/// Use `From` or `Into` to build a `UniformUpdate`.
pub struct UniformUpdate<'a, T> {
  update_closure: Box<Fn(T) + 'a>
}

impl<'a, C, T> From<Uniform<C, T>> for UniformUpdate<'a, T> where C: 'a + HasUniform, T: 'a + Uniformable<C> {
  fn from(u: Uniform<C, T>) -> Self {
    UniformUpdate {
      update_closure: Box::new(move |x| {
        u.update(x);
      })
    }
  }
}

impl<'a, T> UniformUpdate<'a, T> where T: 'a {
  /// Update the underlying `Uniform`.
  pub fn update(&self, x: T) {
    (self.update_closure)(x)
  }

  /// Apply a contravariant functor.
  pub fn contramap<F, Q>(self, f: F) -> UniformUpdate<'a, Q> where F: 'a + Fn(Q) -> T {
    UniformUpdate {
      update_closure: Box::new(move |x| {
        (self.update_closure)(f(x))
      })
    }
  }
}

/// Type of a uniform.
#[derive(Clone, Copy, Debug)]
pub enum Type {
  Integral,
  Unsigned,
  Floating,
  Boolean,
  ISampler,
  USampler,
  Sampler
}

/// Dimension of the uniform.
#[derive(Clone, Copy, Debug)]
pub enum Dim {
  Dim1,
  Dim2,
  Dim3,
  Dim4,
  Dim22,
  Dim33,
  Dim44,
  Cubemap
}

/// Layering of a uniform (flat or layered/array).

/// Types that can behave as `Uniform`.
pub trait Uniformable<C>: Sized where C: HasUniform {
  /// Update the uniform with a new value.
  fn update(u: &Uniform<C, Self>, x: Self);
  /// Retrieve the `Type` of the uniform.
  fn reify_type() -> Type;
  /// Retrieve the `Dim` of the uniform.
  fn dim() -> Dim;
  /// Retrieve the number of elements (if array), 1 otherwise.
  fn size(&self) -> usize;
}

impl<C> Uniformable<C> for i32 where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update1_i32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Integral }

  fn dim() -> Dim { Dim::Dim1 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [i32; 2] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update2_i32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Integral }

  fn dim() -> Dim { Dim::Dim2 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [i32; 3] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update3_i32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Integral }

  fn dim() -> Dim { Dim::Dim3 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [i32; 4] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update4_i32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Integral }

  fn dim() -> Dim { Dim::Dim4 }

  fn size(&self) -> usize { 1 }
}

impl<'a, C> Uniformable<C> for &'a [i32] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update1_slice_i32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Integral }

  fn dim() -> Dim { Dim::Dim1 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[i32; 2]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update2_slice_i32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Integral }

  fn dim() -> Dim { Dim::Dim2 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[i32; 3]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update3_slice_i32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Integral }

  fn dim() -> Dim { Dim::Dim3 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[i32; 4]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update4_slice_i32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Integral }

  fn dim() -> Dim { Dim::Dim4 }

  fn size(&self) -> usize { self.len() }
}

impl<C> Uniformable<C> for u32 where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update1_u32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Unsigned }

  fn dim() -> Dim { Dim::Dim1 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [u32; 2] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update2_u32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Unsigned }

  fn dim() -> Dim { Dim::Dim2 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [u32; 3] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update3_u32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Unsigned }

  fn dim() -> Dim { Dim::Dim3 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [u32; 4] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update4_u32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Unsigned }

  fn dim() -> Dim { Dim::Dim4 }

  fn size(&self) -> usize { 1 }
}

impl<'a, C> Uniformable<C> for &'a [u32] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update1_slice_u32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Unsigned }

  fn dim() -> Dim { Dim::Dim1 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[u32; 2]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update2_slice_u32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Unsigned }

  fn dim() -> Dim { Dim::Dim2 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[u32; 3]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update3_slice_u32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Unsigned }

  fn dim() -> Dim { Dim::Dim3 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[u32; 4]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update4_slice_u32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Unsigned }

  fn dim() -> Dim { Dim::Dim4 }

  fn size(&self) -> usize { self.len() }
}

impl<C> Uniformable<C> for f32 where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update1_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim1 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [f32; 2] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update2_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim2 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [f32; 3] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update3_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim3 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [f32; 4] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update4_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim4 }

  fn size(&self) -> usize { 1 }
}

impl<'a, C> Uniformable<C> for &'a [f32] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update1_slice_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim1 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[f32; 2]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update2_slice_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim2 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[f32; 3]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update3_slice_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim3 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[f32; 4]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update4_slice_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim4 }

  fn size(&self) -> usize { self.len() }
}

impl<C> Uniformable<C> for M22 where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update22_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim22 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for M33 where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update33_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim33 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for M44 where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update44_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim44 }

  fn size(&self) -> usize { 1 }
}

impl<'a, C> Uniformable<C> for &'a [M22] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update22_slice_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim22 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [M33] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update33_slice_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim33 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [M44] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update44_slice_f32(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Floating }

  fn dim() -> Dim { Dim::Dim44 }

  fn size(&self) -> usize { self.len() }
}

impl<C> Uniformable<C> for bool where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update1_bool(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Boolean }

  fn dim() -> Dim { Dim::Dim1 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [bool; 2] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update2_bool(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Boolean }

  fn dim() -> Dim { Dim::Dim2 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [bool; 3] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update3_bool(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Boolean }

  fn dim() -> Dim { Dim::Dim3 }

  fn size(&self) -> usize { 1 }
}

impl<C> Uniformable<C> for [bool; 4] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update4_bool(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Boolean }

  fn dim() -> Dim { Dim::Dim4 }

  fn size(&self) -> usize { 1 }
}

impl<'a, C> Uniformable<C> for &'a [bool] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update1_slice_bool(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Boolean }

  fn dim() -> Dim { Dim::Dim1 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[bool; 2]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update2_slice_bool(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Boolean }

  fn dim() -> Dim { Dim::Dim2 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[bool; 3]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update3_slice_bool(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Boolean }

  fn dim() -> Dim { Dim::Dim3 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C> Uniformable<C> for &'a [[bool; 4]] where C: HasUniform {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update4_slice_bool(&u.repr, x)
  }

  fn reify_type() -> Type { Type::Boolean }

  fn dim() -> Dim { Dim::Dim4 }

  fn size(&self) -> usize { self.len() }
}

impl<'a, C, L, D, P> Uniformable<C> for &'a Texture<C, L, D, P>
    where C: HasUniform,
          L: Layerable,
          D: Dimensionable,
          P: Pixel {
  fn update(u: &Uniform<C, Self>, x: Self) {
    C::update_textures(&u.repr, &[&x.repr]);
  }

  fn reify_type() -> Type {
    match P::pixel_format().encoding {
      pixel::Type::Integral => Type::ISampler,
      pixel::Type::Unsigned => Type::USampler,
      pixel::Type::Floating => Type::Sampler
    }
  }

  fn dim() -> Dim {
    match D::dim() {
      texture::Dim::Dim1 => Dim::Dim1,
      texture::Dim::Dim2 => Dim::Dim2,
      texture::Dim::Dim3 => Dim::Dim3,
      texture::Dim::Cubemap => Dim::Cubemap,
    }
  }

  fn size(&self) -> usize { 1 }
}
