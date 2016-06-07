//! Embedded domain specific language for shading.
//!
//! This module exports a  platform and technology independent home-made shading language.

use std::marker::PhantomData;
use std::ops::{Add, Div, Mul, Neg, Not, Sub};

#[derive(Clone, Debug)]
pub enum Expr {
  I32(i32),
  U32(u32),
  F32(f32),
  Bool(bool),
  UnaOp(UnaOp, Box<Expr>),
  BinOp(BinOp, Box<Expr>, Box<Expr>),
  TerOp(TerOp, Box<Expr>, Box<Expr>, Box<Expr>),
  Fun(FunName, Box<[Box<Expr>]>),
  Vec2(Box<Expr>, Box<Expr>),
  Vec3(Box<Expr>, Box<Expr>, Box<Expr>),
  Vec4(Box<Expr>, Box<Expr>, Box<Expr>, Box<Expr>),
  Swizzle(Swizzle, Box<Expr>)
}

#[derive(Clone, Debug)]
pub struct E<T> {
  expr: Expr,
  _t: PhantomData<T>
}

impl<T> E<T> {
  fn new(e: Expr) -> Self {
    E {
      expr: e,
      _t: PhantomData
    }
  }
}

pub trait ReifyType {
  fn reify_type() -> Type;
}

impl ReifyType for i32 {
  fn reify_type() -> Type { Type::I32 }
}

impl ReifyType for u32 {
  fn reify_type() -> Type { Type::U32 }
}

impl ReifyType for f32 {
  fn reify_type() -> Type { Type::F32 }
}

impl ReifyType for bool {
  fn reify_type() -> Type { Type::Bool }
}

macro_rules! impl_from {
  ($t:ty, $variant:ident) => {
    impl From<$t> for E<$t> {
      fn from(a: $t) -> Self { E::new(Expr::$variant(a)) }
    }
  }
}

impl_from!(i32, I32);
impl_from!(u32, U32);
impl_from!(f32, F32);
impl_from!(bool, Bool);

macro_rules! impl_scalar {
  ($trait_name:ident, $method:ident) => {
    impl<T> $trait_name<E<T>> for E<T> where T: $trait_name {
      type Output = E<T>;
    
      fn $method(self, rhs: E<T>) -> Self::Output {
        E::new(Expr::BinOp(BinOp::$trait_name, Box::new(self.expr), Box::new(rhs.expr)))
      }
    }
  }
}

macro_rules! impl_array {
  ($trait_name:ident, $method:ident, $dim:expr) => {
    impl<T> $trait_name<E<T>> for E<[T; $dim]> {
      type Output = E<[T; $dim]>;
    
      fn $method(self, rhs: E<T>) -> Self::Output {
        E::new(Expr::BinOp(BinOp::$trait_name, Box::new(self.expr), Box::new(rhs.expr)))
      }
    }
  }
}

impl_scalar!(Add, add);
impl_scalar!(Sub, sub);
impl_scalar!(Mul, mul);
impl_scalar!(Div, div);
impl_array!(Add, add, 2);
impl_array!(Add, add, 3);
impl_array!(Add, add, 4);
impl_array!(Sub, sub, 2);
impl_array!(Sub, sub, 3);
impl_array!(Sub, sub, 4);
impl_array!(Mul, mul, 2);
impl_array!(Mul, mul, 3);
impl_array!(Mul, mul, 4);
impl_array!(Div, div, 2);
impl_array!(Div, div, 3);
impl_array!(Div, div, 4);

impl<T> Neg for E<T> {
  type Output = E<T>;

  fn neg(self) -> Self::Output {
    E::new(Expr::UnaOp(UnaOp::Neg, Box::new(self.expr)))
  }
}

macro_rules! impl_not {
  ($t:ty) => {
    impl Not for E<$t> {
      type Output = E<$t>;

      fn not(self) -> Self::Output {
        E::new(Expr::UnaOp(UnaOp::Not, Box::new(self.expr)))
      }
    }
  }
}

impl_not!(bool);
impl_not!([bool; 2]);
impl_not!([bool; 3]);
impl_not!([bool; 4]);

#[derive(Copy, Clone, Debug)]
pub struct Binding(u32);

#[derive(Clone, Debug)]
pub enum Statement {
  LetStatement(LetStatement, Option<Box<Statement>>),
  ControlStatement(ControlStatement, Option<Box<Statement>>),
  AssignStatement(AssignStatement, Option<Box<Statement>>),
  Return(Box<Expr>)
}

#[derive(Clone, Debug)]
pub enum LetStatement {
  Let(Type, Box<Expr>, Option<Box<LetStatement>>)
}

#[derive(Clone, Debug)]
pub enum ControlStatement {
  If(Box<Expr>, Box<Statement>, Option<IfRest>),
  For(LetStatement, Box<Expr>, ForIterStatement),
  While(Box<Expr>, Box<Statement>)
}

#[derive(Clone, Debug)]
pub enum IfRest {
  Else(Box<Statement>),
  ElseIf(Box<Expr>, Box<Statement>, Option<Box<IfRest>>),
}

#[derive(Clone, Debug)]
pub enum ForIterStatement {
  ForIter(Box<AssignStatement>, Option<Box<ForIterStatement>>)
}

#[derive(Clone, Debug)]
pub enum AssignStatement {
  Assign(Box<Expr>, Box<Expr>)
}

#[derive(Clone, Debug)]
pub enum UnaOp {
  Neg,
  Not,
  Swizzle(Swizzle)
}

#[derive(Clone, Debug)]
pub enum Swizzle {
  SW1(SwizzleXYZ),
  SW2(SwizzleXYZ, SwizzleXYZ),
  SW3(SwizzleXYZ, SwizzleXYZ, SwizzleXYZ),
  SW4(SwizzleXYZ, SwizzleXYZ, SwizzleXYZ, SwizzleXYZ)
}

#[derive(Clone, Debug)]
pub enum SwizzleXYZ {
  X,
  Y,
  Z,
}

#[derive(Clone, Debug)]
pub enum BinOp {
  Add,
  Sub,
  Mul,
  Div,
}

#[derive(Clone, Debug)]
pub enum TerOp {
  IfThenElse
}

#[derive(Clone, Debug)]
pub struct Fun {
  name: FunName,
  ret_type: Option<Type>,
  signature: Box<[Type]>,
  body: Option<Statement> // None if built-in // TODO
}

#[derive(Clone, Debug)]
pub enum FunName {
  Sin,
  Cos,
  Tan,
  ASin,
  ACos,
  ATan,
  SinH,
  CosH,
  TanH,
  ASinH,
  ACosH,
  ATanH,
  Pow,
  Exp,
  Log,
  Sqrt,
  ISqrt,
  Abs,
  Sign,
  Floor,
  Round,
  Ceil,
  Fract,
  UserDefined(Binding)
}

#[derive(Clone, Debug)]
pub enum Type {
  I32,
  U32,
  F32,
  Bool,
  Vec2(Box<Type>),
  Vec3(Box<Type>),
  Vec4(Box<Type>),
  Struct(Box<[Type]>)
}

// sinf
fn sin_def() -> Fun {
  Fun {
    name: FunName::Sin,
    ret_type: Some(Type::F32),
    signature: Box::new([Type::F32]),
    body: None
  }
}

/// SL grammar.
macro_rules! sl {
  // input declaration
  (let in $i:ident : $t:ty; $($r:tt)*) => {{
    sl!($($r)*)
  }};

  // out declaration
  (let out $i:ident : $t:ty;) => {{
  }};

  // uniform declaration
  (uniform $i:ident : $t:ty;) => {{
  }};

  // variable declaration
  (let $i:ident = $e:expr; $($r:tt)*) => {{
    let $i = E::from($e);
    sl!($($r)*)
  }};

  // function declaration
  (fn $i:ident ($(,)*) -> $ret_type:ty { $($st:stmt)* }) => {{
  }};

  // early return
  (return $e:expr;) => {{
  }};

  // assignment
  ($v:ident = $e:expr;) => {{
  }};

  // when
  (when ($cond:expr) { $($st:stmt)* }) => {{
  }};

  // unless
  (unless ($cond:expr) { $($st:stmt)* }) => {{
  }};

  // if else
  (if ($cond:expr) { $($st_if:stmt)* } else { $($st_else:stmt)* }) => {{
  }};

  // for loop
  (for ($i:ident : $t:ty = $e:expr ; $cond:expr ; $post_st:stmt) { $($body_st:stmt)* }) => {{
  }};

  // while loop
  (while ($cond:expr) { $($body_st:stmt)* }) => {{
  }};

  // terminal macro
  () => {{ }}
}

fn test() {
  sl!{
    let a = 3;
    let b = 1;
    let c = a * b;
  }
}
