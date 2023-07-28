use crate::main;
use crate::syntax::*;
use crate::itt::*;

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

  // Instead of an inline string, loads the local 'example.itt' file
  // This is statically loaded to the compiled binary with a macro
  let code = include_str!("./../example.itt");

  //  Creates initial term
  let term = from_string(code.as_bytes());
  //println!("{}", term);

  // Creates the net from term
  let mut inet = new_inet();
  inject(&mut inet, &term, ROOT);

  println!("input:\n{}", show(&inet));

  // Normal
  eager(&mut inet);
  //println!("itt {}", readback(&inet, ROOT));

  println!("normal:\n{}", show(&inet));
  println!("{:?} rewrites", inet.rules);
  println!("");

  //println!("λ-normal:\n{}", lambda_term_from_inet(&inet));
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

