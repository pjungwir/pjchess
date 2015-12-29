extern crate pjchess;

use std::io;

fn main() {
  println!("Board:");
  let mut b = pjchess::Board::initial_setup();
  print!("{}", b.as_string());
}
