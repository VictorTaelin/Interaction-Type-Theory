use crate::main;
use crate::term::*;
use crate::inet::*;

pub fn get_body(inet: &INet, host: Port) -> Port {
  return port(addr(enter(inet,host)), 2);
}

pub fn get_func(inet: &INet, host: Port) -> Port {
  return port(addr(enter(inet,host)), 0);
}

pub fn get_argm(inet: &INet, host: Port) -> Port {
  return port(addr(enter(inet,host)), 1);
}

pub fn test() {

  let code = "

// Unit
// ----

def Unit =
  dup P0 P1 = P
  ∀P -> &P0 -> P1

def unit =
  λP λu u

// Bool
// ----

def Bool =
  dup PA P0 = P;
  dup P1 P2 = PA;
  ∀P -> &P0 -> &P1 -> P2

def true =
  λP λt λf t

def false =
  λP λt λf f

// Good
def test0 = λA λB λx
  dup A0 A1 = A
  <<x : A0> : A1>

// Bad
def test1 = λA λB λx
  <<x : A> : B>

// Good
def test2 = <true : Bool>

// Bad
def test3 = <true : Unit>

// Bad
def test4 = <unit : Bool>

def term = λA λB λf λg λx λy
  dup f0 f1 = f
  dup g0 g1 = g
  (g0 (f0 (g1 (f1 x))))

def type =

  dup A0 A1 = A
  dup A2 A3 = A0
  dup A4 A5 = A1
  dup A6 A7 = A2

  dup B0 B1 = B
  dup B2 B3 = B0
  dup B4 B5 = B1
  dup B6 B7 = B2

  ∀A -> ∀B ->
  & (&A4 -> B4) ->
  & (&B5 -> A5) -> 
  & A6 ->
  & B6 ->
  A7


// Good
def test5 =
  λT

  dup T0 T1 = T
  dup P0 P1 = P
  dup Q0 Q1 = Q

  < λp p
  : & (∀(P: T0) -> &P0 -> P1) ->
      (∀(Q: T1) -> &Q0 -> Q1)
  >

// ...
def test6 = λB λT
  dup A0 A1 = A
  < λa λx x
  : ∀(A: &B -> T) -> &(A0 λt0 λf0 t0) -> (A1 λt1 λf1 t1)
  >
  
def test7 =
  dup P0 P1 = P
  < λp λx x
  : ∀P -> &P0 -> P1
  >

def test8 =
  dup A0 A1 = A
  dup B0 B1 = B
  < λa λb λx λy x
  : ∀A -> ∀B -> &A0 -> &B0 -> A1
  >

test8

";

  //  Creates initial term
  let term = from_string(code.as_bytes());
  //println!("{}", term);

  // Creates the net from term
  let mut inet = new_inet();
  inject(&mut inet, &term, ROOT);

  println!("input:\n{}", show(&inet));

  // Normal
  normal(&mut inet, ROOT);
  //println!("itt {}", readback(&inet, ROOT));

  println!("normal:\n{}", show(&inet));
  println!("{:?} rewrites", inet.rules);
  println!("");

  //println!("λ-normal:\n{}", lambda_term_from_inet(&inet));
  //println!("");

  //println!("check:\n{}", check(&mut inet, ROOT));
  //println!("");
  
  //tests equality, using `main = λx (x A B)`
  //let a = enter(&inet, ROOT);
  //let a = enter(&inet, port(addr(a), 2));
  //let a = enter(&inet, port(addr(a), 0));
  //let a = enter(&inet, port(addr(a), 1));
  //let a = enter(&inet, a);
  //let b = enter(&inet, ROOT);
  //let b = enter(&inet, port(addr(b), 2));
  //let b = enter(&inet, port(addr(b), 1));
  //let b = enter(&inet, b);
  //println!("equal ({}) = ({}) ? {}", lambda_term_from_inet(&inet, a), lambda_term_from_inet(&inet, b), equal(&mut inet, a, b));
}

