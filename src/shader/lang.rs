//! Embedded domain specific language for shading.
//!
//! This module exports a platform and technology independent shading language.

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
  Fun(String, Box<[Box<Expr>]>),
  Vec2(Box<Expr>, Box<Expr>),
  Vec3(Box<Expr>, Box<Expr>, Box<Expr>),
  Vec4(Box<Expr>, Box<Expr>, Box<Expr>, Box<Expr>),
  V(String)
}

#[derive(Clone, Debug)]
pub struct E<T> {
  expr: Expr,
  _t: PhantomData<T>
}

impl<T> E<T> {
  pub fn new(e: Expr) -> Self {
    E {
      expr: e,
      _t: PhantomData
    }
  }

  pub fn lt(&self, rhs: &Self) -> E<bool> {
    E::new(Expr::BinOp(BinOp::LT, Box::new(self.expr.clone()), Box::new(rhs.expr.clone())))
  }

  pub fn lte(&self, rhs: &Self) -> E<bool> {
    E::new(Expr::BinOp(BinOp::LTE, Box::new(self.expr.clone()), Box::new(rhs.expr.clone())))
  }

  pub fn gt(&self, rhs: &Self) -> E<bool> {
    E::new(Expr::BinOp(BinOp::GT, Box::new(self.expr.clone()), Box::new(rhs.expr.clone())))
  }

  pub fn gte(&self, rhs: &Self) -> E<bool> {
    E::new(Expr::BinOp(BinOp::GTE, Box::new(self.expr.clone()), Box::new(rhs.expr.clone())))
  }

  pub fn eq(&self, rhs: &Self) -> E<bool> {
    E::new(Expr::BinOp(BinOp::Eq, Box::new(self.expr.clone()), Box::new(rhs.expr.clone())))
  }

  pub fn ne(&self, rhs: &Self) -> E<bool> {
    E::new(Expr::BinOp(BinOp::NE, Box::new(self.expr.clone()), Box::new(rhs.expr.clone())))
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

macro_rules! impl_neg {
  ($t:ty) => {
    impl Neg for E<$t> {
      type Output = E<$t>;
    
      fn neg(self) -> Self::Output {
        E::new(Expr::UnaOp(UnaOp::Neg, Box::new(self.expr)))
      }
    }
  }
}

impl_neg!(i32);
impl_neg!([i32; 2]);
impl_neg!([i32; 3]);
impl_neg!([i32; 4]);
impl_neg!(u32);
impl_neg!([u32; 2]);
impl_neg!([u32; 3]);
impl_neg!([u32; 4]);
impl_neg!(f32);
impl_neg!([f32; 2]);
impl_neg!([f32; 3]);
impl_neg!([f32; 4]);

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

/// A shader stage gathers inputs, outputs, uniforms, functions and main declaration.
#[derive(Clone, Debug)]
pub struct Stage {
  pub inputs: Vec<(String, Type)>,
  pub outputs: Vec<(String, Type)>,
  pub uniforms: Vec<(String, Type)>,
  pub functions: Vec<(String, Fun)>,
  pub main: Scope
}

impl Stage {
  pub fn new() -> Self {
    Stage {
      inputs: Vec::new(),
      outputs: Vec::new(),
      uniforms: Vec::new(),
      functions: Vec::new(),
      main: Scope::Empty
    }
  }

  pub fn push_input(&mut self, id: &str, ty: Type) {
    self.inputs.push((id.into(), ty));
  }

  pub fn push_output(&mut self, id: &str, ty: Type) {
    self.outputs.push((id.into(), ty));
  }

  pub fn push_uniform(&mut self, id: &str, ty: Type) {
    self.uniforms.push((id.into(), ty));
  }

  pub fn push_fun(&mut self, id: &str, fun: Fun) {
    self.functions.push((id.into(), fun));
  }
}

#[derive(Clone, Debug)]
pub enum Scope {
  Empty,
  LetStatement(LetStatement, Option<Box<Scope>>),
  ControlStatement(ControlStatement, Option<Box<Scope>>),
  AssignStatement(AssignStatement, Option<Box<Scope>>),
  Return(Box<Expr>)
}

fn map_def<T, U, F>(option: Option<T>, default: U, f: F) -> Option<U> where F: FnOnce(T) -> U {
  match option {
    None => Some(default),
    Some(x) => Some(f(x))
  }
}

impl Scope {
  pub fn new() -> Self {
    Scope::Empty
  }

  pub fn new_let<T>(identifier: String, t: Type, e: E<T>) -> Self {
    Scope::LetStatement(LetStatement::Let(identifier, t, Box::new(e.expr)), None)
  }

  pub fn new_if(cond: E<bool>, st: Scope) -> Self {
    Scope::ControlStatement(ControlStatement::If(Box::new(cond.expr), Box::new(st), None), None)
  }

  pub fn new_if_else(cond: E<bool>, st_true: Scope, st_false: Scope) -> Self {
    Scope::ControlStatement(ControlStatement::If(Box::new(cond.expr), Box::new(st_true), Some(IfRest::Else(Box::new(st_false)))), None)
  }

  pub fn new_return<T>(e: E<T>) -> Self {
    Scope::Return(Box::new(e.expr))
  }

  pub fn new_assign<T>(i: E<T>, e: E<T>) -> Self {
    Scope::AssignStatement(AssignStatement::Assign(Box::new(i.expr), Box::new(e.expr)), None)
  }

  pub fn push(self, st: Self) -> Self {
    match self {
      Scope::Empty => st,
      Scope::LetStatement(let_st, next_st) => Scope::LetStatement(let_st, Self::option_push(next_st, st)),
      Scope::ControlStatement(ctrl_st, next_st) => Scope::ControlStatement(ctrl_st, Self::option_push(next_st, st)),
      Scope::AssignStatement(asg_st, next_st) => Scope::AssignStatement(asg_st, Self::option_push(next_st, st)),
      a@Scope::Return(..) => a // short-circuit what’s next
    }
  }

  // Push a `Scope` into an `Option<Box<Scope>>`.
  //
  // Used to implement `Scope::push`.
  fn option_push(option: Option<Box<Scope>>, st: Scope) -> Option<Box<Scope>> {
    map_def(option, Box::new(st.clone()), |next| Box::new(next.push(st)))
  }
}

#[derive(Clone, Debug)]
pub enum LetStatement {
  Let(String, Type, Box<Expr>)
}

#[derive(Clone, Debug)]
pub enum ControlStatement {
  If(Box<Expr>, Box<Scope>, Option<IfRest>),
  For(LetStatement, Box<Expr>, ForIterStatement, Box<Scope>),
  While(Box<Expr>, Box<Scope>)
}

#[derive(Clone, Debug)]
pub enum IfRest {
  Else(Box<Scope>),
  ElseIf(Box<Expr>, Box<Scope>, Option<Box<IfRest>>),
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
  Add, // +
  Sub, // -
  Mul, // *
  Div, // /
  LT, // <
  LTE, // <=
  GT, // >
  GTE, // >=
  Eq, // ==
  NE, // !=
}

#[derive(Clone, Debug)]
pub struct Fun {
  name: String,
  ret_type: Option<Type>,
  args: Vec<(String, Type)>,
  body: Option<Scope> // None if built-in // TODO
}

impl Fun {
  /// Create a new user-defined function definition.
  pub fn new(name: &str, ret_type: Option<Type>, args: Vec<(String, Type)>, body: Scope) -> Self {
    Fun {
      name: name.into(),
      ret_type: ret_type,
      args: args,
      body: Some(body)
    }
  }
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

/// Scope statements.
#[macro_export]
macro_rules! sl_scope_st {
  // // input declaration
  // ($ast:ident let in $i:ident : $t:ty; $($r:tt)*) => {{
  //   sl_scope_st!($($r)*)
  // }};

  // // out declaration
  // ($ast:ident let out $i:ident : $t:ty;) => {{
  // }};

  // // uniform declaration
  // ($ast:ident uniform $i:ident : $t:ty;) => {{
  // }};

  // variable declaration
  ($ast:ident let $id:ident : $t:ty = $e:expr; $($r:tt)*) => {{
    let id = String::from(stringify!($id));
    let e = E::from($e);
    let $id: E<$t> = E::new(Expr::V(id.clone()));

    let ast = $ast.push(Scope::new_let(id, <$t as ReifyType>::reify_type(), e.clone()));

    sl_scope_st!(ast $($r)*)
  }};

  // early return; terminal
  ($ast:ident return $e:expr;) => {{
    $ast.push(Scope::new_return(E::from($e)))
  }};

  // assignment
  ($ast:ident $v:ident = $e:expr; $($r:tt)*) => {{
    let ast = $ast.push(Scope::new_assign($v.clone(), E::from($e)));
    sl_scope_st!(ast $($r)*)
  }};

  // if else
  ($ast:ident if $cond:expr { $($st_true:tt)* } else { $($st_false:tt)* } $($r:tt)*) => {{
    let st_true = sl_scope!($($st_true)*);
    let st_false = sl_scope!($($st_false)*);
    let ast = $ast.push(Scope::new_if_else($cond.into(), st_true, st_false));

    sl_scope_st!(ast $($r)*)
  }};

  // if
  ($ast:ident if ($cond:expr) { $($st:tt)* } $($r:tt)*) => {{
    let st = sl_scope!($($st)*);
    let ast = $ast.push(Scope::new_if($cond.into(), st));

    sl_scope_st!(ast $($r)*)
  }};

  // for loop
  ($ast:ident for ($i:ident : $t:ty = $e:expr ; $cond:expr ; $post_st:stmt) { $($body_st:stmt)* }) => {{
  }};

  // while loop
  ($ast:ident while ($cond:expr) { $($body_st:stmt)* }) => {{
  }};

  // expression; terminal
  ($ast:ident $e:expr) => {{
    $ast.push(Scope::new_return(E::from($e)))
  }};

  // terminal macro
  ($ast:ident) => {{ $ast }};
}

/// Macro used to define a scope. A scope can be used as function body or control statement body.
#[macro_export]
macro_rules! sl_scope {
  ($($t:tt)*) => {{
    let ast: Scope = Scope::new();
    sl_scope_st!(ast $($t)*)
  }}
}

/// Stage statements.
#[macro_export]
macro_rules! sl_stage_st {
  // main entry of the shader
  ($stage:ident fn main() { $($body:tt)* }) => {{
    let main_scope = sl_scope!($($body)*);

    $stage.main = main_scope;
  }};

  // define a function returning nothing
  ($stage:ident fn $fun_name:ident ( $( $arg:ident : $arg_ty:ty ),* ) { $($body:tt)* } $($r:tt)*) => {{
    // insert arguments into current scope so that we can use them
    $( let $arg: E<$arg_ty> = E::new(Expr::V(stringify!($arg).into())); )*
    let fun = Fun::new(stringify!($fun_name), None, vec![ $( (stringify!($arg).into(), <$arg_ty as ReifyType>::reify_type()) ),* ], sl_scope!($($body)*));

    $stage.push_fun(stringify!($fun_name), fun);

    // insert $fun_name into what comes next so that we can use it later on
    sl_stage_st!($stage $($r)*)
  }};

  // define a function with return type
  ($stage:ident fn $fun_name:ident ( $( $arg:ident : $arg_ty:ty ),* ) -> $ret_type:ty { $($body:tt)* } $($r:tt)*) => {{
    // insert arguments into current scope so that we can use them
    $( let $arg: E<$arg_ty> = E::new(Expr::V(stringify!($arg).into())); )*
    let fun = Fun::new(stringify!($fun_name), Some(<$ret_type as ReifyType>::reify_type()), vec![ $( (stringify!($arg).into(), <$arg_ty as ReifyType>::reify_type()) ),* ], sl_scope!($($body)*));

    $stage.push_fun(stringify!($fun_name), fun);

    // insert $fun_name into what comes next so that we can use it later on
    sl_stage_st!($stage $($r)*)
  }};

  // terminal macro
  ($stage:ident) => {{ }};
}

/// Macro used to define a shader stage.
#[macro_export]
macro_rules! sl_stage {
  ($($t:tt)*) => {{
    let mut stage = Stage::new();
    sl_stage_st!(stage $($t)*);
    stage
  }}
}
