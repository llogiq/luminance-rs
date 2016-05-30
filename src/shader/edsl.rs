//! Embedded domain specific language for shading.
//!
//! This module exports a  platform and technology independent home-made shading language.

enum Expr {
  I32(i32),
  U32(u32),
  F32(f32),
  Bool(bool),
  UnaOp(UnaOp, Box<Expr>),
  BinOp(BinOp, Box<Expr>, Box<Expr>),
  TerOp(TerOp, Box<Expr>, Box<Expr>, Box<Expr>),
  Fun(FunName, Vec<Box<Expr>>),
}

enum UnaOp {
  Negate,
  Not,
}

enum BinOp {
  Add,
  Sub,
  Mul,
  Div,
}

enum TerOp {
  IfThenElse
}

struct Fun {
  name: FunName,
  ret_type: Type,
  signature: Vec<Type>,
  body: Option<Box<Expr>> // None if built-in
}

enum FunName {
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

enum Type {
  I32,
  U32,
  F32,
  Bool,
  Struct(Vec<Type>)
}
