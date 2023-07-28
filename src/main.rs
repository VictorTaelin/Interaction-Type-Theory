#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(unreachable_code)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]
#![allow(unused_variables)]

extern crate clap;
use clap::{Arg, App};

mod itt;
mod syntax;
mod test;

use itt::*;
use syntax::*;

use std::io;
use std::io::prelude::*;
use std::fs::File;

fn main() {
  //return test::test();

  let matches = App::new("My App")
    .version("1.0")
    .author("Victor Taelin <victor.taelin@gmail.com>")
    .about("Interaction Type Theory CLI")
    .arg(Arg::with_name("file")
      .help("The input file to process")
      .required(true)
      .index(1))
    .get_matches();

  // Reads source file to a string
  let file_name = matches.value_of("file").unwrap();
  let mut file = File::open(file_name).expect("Unable to open the file");
  let mut code = String::new();
  file.read_to_string(&mut code).expect("Unable to read the file");

  // Converts source to term
  let term = from_string(code.as_bytes());

  // Converts term to inet
  let mut inet = new_inet();
  inject(&mut inet, &term, ROOT);

  println!("input:\n{}", show(&inet));

  // Normalizes
  eager(&mut inet);

  println!("normal:\n{}", show(&inet));
  println!("\x1b[90m{:?} rewrites\x1b[0m", inet.rules);

  let term = syntax::from_string(code.as_bytes());
  let (norm, rules) = syntax::normalize(&term);

  println!("{}\n", norm);
  println!("{:?} rewrites", rules);

}
