//! Embedded domain specific language for shading.
//!
//! This module exports a  platform and technology independent home-made shading language.

use std::marker::PhantomData;

pub enum Expr {
  I32(i32),
  U32(u32),
  F32(f32),
  Bool(bool),
  UnaOp(UnaOp, Box<Expr>),
  BinOp(BinOp, Box<Expr>, Box<Expr>),
  TerOp(TerOp, Box<Expr>, Box<Expr>, Box<Expr>),
  Fun(FunName, Box<[Box<Expr>]>),
}

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

impl From<i32> for E<i32> {
  fn from(a: i32) -> Self { E::new(Expr::I32(a)) }
}

impl From<u32> for E<u32> {
  fn from(a: u32) -> Self { E::new(Expr::U32(a)) }
}

impl From<f32> for E<f32> {
  fn from(a: f32) -> Self { E::new(Expr::F32(a)) }
}

impl From<bool> for E<bool> {
  fn from(a: bool) -> Self { E::new(Expr::Bool(a)) }
}

fn test() {
  let a = E::from(3);
  let b = E::from(1);
}

pub struct Binding(u32);

pub enum Statement {
  LetStatement(LetStatement),
  ControlStatement(ControlStatement),
  AssignStatement(AssignStatement)
}

pub enum LetStatement {
  Let(Type, Box<Expr>, Option<Box<LetStatement>>)
}

pub enum ControlStatement {
  If(Box<Expr>, Box<Statement>, Option<IfRest>),
  For(LetStatement, Box<Expr>, ForIterStatement),
  While(Box<Expr>, Box<Statement>)
}

pub enum IfRest {
  Else(Box<Statement>),
  ElseIf(Box<Expr>, Box<Statement>, Option<Box<IfRest>>),
}

pub enum ForIterStatement {
  ForIter(Box<AssignStatement>, Option<Box<ForIterStatement>>)
}

pub enum AssignStatement {
  Assign(Box<Expr>, Box<Expr>)
}

pub enum UnaOp {
  Negate,
  Not,
}

pub enum BinOp {
  Add,
  Sub,
  Mul,
  Div,
}

pub enum TerOp {
  IfThenElse
}

pub struct Fun {
  name: FunName,
  ret_type: Option<Type>,
  signature: Box<[Type]>,
  body: Option<()> // None if built-in // TODO
}

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
  UserDefined(String)
}

pub enum Type {
  I32,
  U32,
  F32,
  Bool,
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
