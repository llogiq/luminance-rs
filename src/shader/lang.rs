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
  fn reify_type(&self) -> Type;
}

impl ReifyType for E<i32> {
  fn reify_type(&self) -> Type { Type::I32 }
}

impl ReifyType for E<u32> {
  fn reify_type(&self) -> Type { Type::U32 }
}

impl ReifyType for E<f32> {
  fn reify_type(&self) -> Type { Type::F32 }
}

impl ReifyType for E<bool> {
  fn reify_type(&self) -> Type { Type::Bool }
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

macro_rules! impl_inner {
  ($trait_name:ident, $method:ident) => {
    impl<T> $trait_name<E<T>> for E<T> where T: $trait_name {
      type Output = E<T>;
    
      fn $method(self, rhs: E<T>) -> Self::Output {
        E::new(Expr::BinOp(BinOp::$trait_name, Box::new(self.expr), Box::new(rhs.expr)))
      }
    }
  }
}

macro_rules! impl_outer {
  ($trait_name:ident, $method:ident, $dim:expr) => {
    impl<T> $trait_name<E<T>> for E<[T; $dim]> {
      type Output = E<[T; $dim]>;
    
      fn $method(self, rhs: E<T>) -> Self::Output {
        E::new(Expr::BinOp(BinOp::$trait_name, Box::new(self.expr), Box::new(rhs.expr)))
      }
    }
  }
}

impl_inner!(Add, add);
impl_inner!(Sub, sub);
impl_inner!(Mul, mul);
impl_inner!(Div, div);
impl_outer!(Add, add, 2);
impl_outer!(Add, add, 3);
impl_outer!(Add, add, 4);
impl_outer!(Sub, sub, 2);
impl_outer!(Sub, sub, 3);
impl_outer!(Sub, sub, 4);
impl_outer!(Mul, mul, 2);
impl_outer!(Mul, mul, 3);
impl_outer!(Mul, mul, 4);
impl_outer!(Div, div, 2);
impl_outer!(Div, div, 3);
impl_outer!(Div, div, 4);

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
  Empty,
  LetStatement(LetStatement, Option<Box<Statement>>),
  ControlStatement(ControlStatement, Option<Box<Statement>>),
  AssignStatement(AssignStatement, Option<Box<Statement>>),
}

fn map_def<T, U, F>(option: Option<T>, default: U, f: F) -> Option<U> where F: FnOnce(T) -> U {
  match option {
    None => Some(default),
    Some(x) => Some(f(x))
  }
}

impl Statement {
  pub fn new() -> Self {
    Statement::Empty
  }

  pub fn new_let<T>(t: Type, e: E<T>) -> Self {
    Statement::LetStatement(LetStatement::Let(t, Box::new(e.expr)), None)
  }

  pub fn new_if_else(cond: E<bool>, st_true: Statement, st_false: Statement) -> Self {
    Statement::ControlStatement(ControlStatement::If(Box::new(cond.expr), Box::new(st_true), Some(IfRest::Else(Box::new(st_false)))), None)
  }

  pub fn push(self, st: Self) -> Self {
    match self {
      Statement::Empty => st,
      Statement::LetStatement(let_st, next_st) => Statement::LetStatement(let_st, Self::option_push(next_st, st)),
      Statement::ControlStatement(ctrl_st, next_st) => Statement::ControlStatement(ctrl_st, Self::option_push(next_st, st)),
      Statement::AssignStatement(asg_st, next_st) => Statement::AssignStatement(asg_st, Self::option_push(next_st, st))
    }
  }

  // Push a `Statement` into an `Option<Box<Statement>>`.
  //
  // Used to implement `Statement::push`.
  fn option_push(option: Option<Box<Statement>>, st: Statement) -> Option<Box<Statement>> {
    map_def(option, Box::new(st.clone()), |next| Box::new(next.push(st)))
  }
}

#[derive(Clone, Debug)]
pub enum LetStatement {
  Let(Type, Box<Expr>)
}

#[derive(Clone, Debug)]
pub enum ControlStatement {
  If(Box<Expr>, Box<Statement>, Option<IfRest>),
  For(LetStatement, Box<Expr>, ForIterStatement, Box<Statement>),
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
#[macro_export]
macro_rules! sl_eval {
  // input declaration
  ($ast:ident let in $i:ident : $t:ty; $($r:tt)*) => {{
    sl_eval!($($r)*)
  }};

  // out declaration
  ($ast:ident let out $i:ident : $t:ty;) => {{
  }};

  // uniform declaration
  ($ast:ident uniform $i:ident : $t:ty;) => {{
  }};

  // variable declaration
  ($ast:ident let $i:ident = $e:expr; $($r:tt)*) => {{
    let $i = E::from($e);
    let ast = $ast.push(Statement::new_let($i.reify_type(), $i));
    sl_eval!(ast $($r)*)
  }};

  // function declaration
  ($ast:ident fn $i:ident ($(,)*) -> $ret_type:ty { $($st:stmt)* }) => {{
  }};

  // early return
  ($ast:ident return $e:expr;) => {{
  }};

  // assignment
  ($ast:ident $v:ident = $e:expr;) => {{
  }};

  // when
  ($ast:ident when ($cond:expr) { $($st:stmt)* }) => {{
  }};

  // unless
  ($ast:ident unless ($cond:expr) { $($st:stmt)* }) => {{
  }};

  // if else
  ($ast:ident if ($cond:expr) { $($st_true:tt)* } else { $($st_false:tt)* $($r:tt)* }) => {{
    let st_true = sl!($($st_true)*);
    let st_false = sl!($($st_false)*);
    let ast = $ast.push(Statement::new_if_else(E::from($cond), st_true, st_false));

    sl_eval!(ast $($r)*)
  }};

  // for loop
  ($ast:ident for ($i:ident : $t:ty = $e:expr ; $cond:expr ; $post_st:stmt) { $($body_st:stmt)* }) => {{
  }};

  // while loop
  ($ast:ident while ($cond:expr) { $($body_st:stmt)* }) => {{
  }};

  // terminal macro
  ($ast:ident) => {{ $ast }}
}

#[macro_export]
macro_rules! sl {
  ($($t:tt)*) => {{
    let ast: Statement = Statement::new();
    sl_eval!(ast $($t)*)
  }}
}
