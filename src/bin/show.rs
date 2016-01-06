extern crate pjchess;

fn main() {
  println!("Board:");
  let b = pjchess::Board::initial_setup();
  print!("{}", b.as_string());
}
