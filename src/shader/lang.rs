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
  Fun(FunName, Box<[Box<Expr>]>),
}

struct Binding(u32);

struct Statement;

enum LetStatement {
  Let(Type, Box<Expr>, Option<Box<LetStatement>>)
}

enum ControlStatement {
  If(Box<Expr>, Box<Statement>, Option<IfRest>),
  For(LetStatement, Box<Expr>, ForIterStatement),
  While(Box<Expr>, Box<Statement>)
}

enum IfRest {
  Else(Box<Statement>),
  ElseIf(Box<Expr>, Box<Statement>, Option<Box<IfRest>>),
}

enum ForIterStatement {
  ForIter(Box<AssignStatement>, Option<Box<ForIterStatement>>)
}

enum AssignStatement {
  Assign(Box<Expr>, Box<Expr>)
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
  ret_type: Option<Type>,
  signature: Box<[Type]>,
  body: Option<()> // None if built-in // TODO
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
