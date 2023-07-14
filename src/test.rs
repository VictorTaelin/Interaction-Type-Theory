use crate::main;
use crate::term::*;
use crate::inet::*;
use crate::check::*;

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
  dup PA PB = P;
  dup P0 P1 = PA;
  dup P2 P3 = PB;
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

// TODO
//def test5 =
  //λT λP λQ
  //dup T0 T1 = T
  //dup P0 P1 = P
  //dup Q0 Q1 = Q
  //<(λp p) : & (∀(R: T0) -> &P0 -> P1) -> (∀(S: T1) -> &Q0 -> Q1)>

test4

";

  //  Creates initial term
  let term = from_string(code.as_bytes());
  //println!("{}", term);

  // Creates the net from term
  let mut inet = new_inet();
  inject(&mut inet, &term, ROOT);

  // Normal
  normal(&mut inet, ROOT);
  //println!("itt {}", readback(&inet, ROOT));

  println!("normal:\n{}", show(&inet, ROOT));
  println!("{:?} rewrites", inet.rules);
  println!("");

  println!("check:\n{}", check(&mut inet, ROOT));
  println!("");
}

