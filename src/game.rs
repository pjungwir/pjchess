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

  pub fn make_move(&mut self, mv: Ply) {
    let mut b2: Box<Board>;
    {
      let ref b = self.frames.last().expect("must have a frame").as_ref();
      b2 = Box::new(Board { .. **b });
      b.make_move(mv, &mut b2);
    }

    self.plies.push(mv);
    self.frames.push(b2);
  }

}

#[cfg(test)]
mod tests {
  use super::{Game,Outcome};
  use board::{Board,Ply,Pos,Color,Piece,Figure};
  use std::ops::Deref;

  #[test]
  fn start_game() {
    let g = Game::start_game();
    assert_eq!(*g.frames[0].deref(), Board::initial_setup());
    assert_eq!(g.plies, vec![]);
    assert_eq!(g.outcome, Outcome::Undecided);
    assert_eq!(g.winner, None);
  }

  #[test]
  fn make_move() {
    let mut g = Game::start_game();
    assert_eq!(g.frames.len(), 1);
    g.make_move(Ply{from: Pos{rank: 1, file: 4}, to: Pos{rank: 3, file: 4}, capture: false, en_passant: false, castle: false, promote: None});
    assert_eq!(g.frames.len(), 2);
    assert_eq!(g.frames[1].piece_at(Pos{rank: 1, file: 4}), None);
    assert_eq!(g.frames[1].piece_at(Pos{rank: 3, file: 4}), Some(Piece{color: Color::White, figure: Figure::Pawn}));
  }

}

