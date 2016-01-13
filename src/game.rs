use board::*;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Outcome {
  Undecided,
  AgreedToDraw,
  DrawByThreefoldRepetition,
  Stalemate,
  Checkmated,
  Resigned,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Game {
  frames: Vec<Box<Board>>,
  plies: Vec<Ply>,
  outcome: Outcome,
  winner: Option<Color>,
}

impl Game {

  pub fn start_game() -> Game {
    Game {
      frames: vec![Box::new(Board::initial_setup())],
      plies: vec![],
      outcome: Outcome::Undecided,
      winner: None,
    }
  }

  pub fn make_move(&self, mv: Ply) {
    
  }

}

#[cfg(test)]
mod tests {
  use super::{Game,Outcome};
  use board::{Board};
  use std::ops::Deref;

  #[test]
  fn start_game() {
    let g = Game::start_game();
    assert_eq!(*g.frames[0].deref(), Board::initial_setup());
    assert_eq!(g.plies, vec![]);
    assert_eq!(g.outcome, Outcome::Undecided);
    assert_eq!(g.winner, None);
  }

}

