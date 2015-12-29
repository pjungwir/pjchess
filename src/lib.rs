#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct Pos {
  rank: i8,
  file: i8,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Flank {
  Kingside,
  Queenside,
}

impl Flank {
  fn direction(self) -> i8 {
    match self {
      Flank::Kingside => 1,
      Flank::Queenside => -1,
    }
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Color {
  White,
  Black,
}

impl Color {
  fn other(self) -> Color {
    match self {
      Color::Black => Color::White,
      Color::White => Color::Black
    }
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Figure {
  Pawn,
  Knight,
  Bishop,
  Rook,
  Queen,
  King,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct Piece {
  color: Color,
  figure: Figure,
}

impl Piece {
  pub fn as_str(self) -> &'static str {
    match self.color {
      Color::White => match self.figure {
        Figure::Pawn => "P",
        Figure::Knight => "N",
        Figure::Bishop => "B",
        Figure::Rook => "R",
        Figure::Queen => "Q",
        Figure::King => "K",
      },
      Color::Black => match self.figure {
        Figure::Pawn => "p",
        Figure::Knight => "n",
        Figure::Bishop => "b",
        Figure::Rook => "r",
        Figure::Queen => "q",
        Figure::King => "k",
      },
    }
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Board {
  grid: [[Option<Piece>;8];8],
  en_passant: Option<Pos>,  // set to the destination square of the piece that will capture.
  can_castle: [[bool;2];2],   // [[white kingside, white queenside], [black kingside, black queenside]]
  side_to_move: Color,
}
  
impl Board {
  pub fn initial_setup() -> Board {
    let b = Board {
      grid: [
        [Some(Piece{color: Color::White, figure: Figure::Rook}),
         Some(Piece{color: Color::White, figure: Figure::Knight}),
         Some(Piece{color: Color::White, figure: Figure::Bishop}),
         Some(Piece{color: Color::White, figure: Figure::Queen}),
         Some(Piece{color: Color::White, figure: Figure::King}),
         Some(Piece{color: Color::White, figure: Figure::Bishop}),
         Some(Piece{color: Color::White, figure: Figure::Knight}),
         Some(Piece{color: Color::White, figure: Figure::Rook})],
        [Some(Piece{color: Color::White, figure: Figure::Pawn});8],
        [None;8],
        [None;8],
        [None;8],
        [None;8],
        [Some(Piece{color: Color::Black, figure: Figure::Pawn});8],
        [Some(Piece{color: Color::Black, figure: Figure::Rook}),
         Some(Piece{color: Color::Black, figure: Figure::Knight}),
         Some(Piece{color: Color::Black, figure: Figure::Bishop}),
         Some(Piece{color: Color::Black, figure: Figure::Queen}),
         Some(Piece{color: Color::Black, figure: Figure::King}),
         Some(Piece{color: Color::Black, figure: Figure::Bishop}),
         Some(Piece{color: Color::Black, figure: Figure::Knight}),
         Some(Piece{color: Color::Black, figure: Figure::Rook})],
      ],
      en_passant: None,
      can_castle: [[true, true], [true, true]],
      side_to_move: Color::White,
    };

    b
  }

  pub fn as_string(&self) -> String {
    let mut s = String::with_capacity(64 + 8);
    for rank in self.grid.iter().rev() {
      for &tile in rank {
        s.push_str(
          match tile {
            Some(p) => p.as_str(),
            None => " ",
          }
        )
      }
      s.push_str("\n");
    }
    s
  }

}

#[cfg(test)]
mod tests {
  use super::{Board, Piece, Color, Figure, Pos};

  #[test]
  fn colors() {
    assert!(Color::White.other() == Color::Black);
    assert!(Color::Black.other() == Color::White);
  }

  #[test]
  fn initial_setup() {
    assert!(Board::initial_setup().grid == 
      [
        [Some(Piece{color: Color::White, figure: Figure::Rook}),
         Some(Piece{color: Color::White, figure: Figure::Knight}),
         Some(Piece{color: Color::White, figure: Figure::Bishop}),
         Some(Piece{color: Color::White, figure: Figure::Queen}),
         Some(Piece{color: Color::White, figure: Figure::King}),
         Some(Piece{color: Color::White, figure: Figure::Bishop}),
         Some(Piece{color: Color::White, figure: Figure::Knight}),
         Some(Piece{color: Color::White, figure: Figure::Rook})],
        [Some(Piece{color: Color::White, figure: Figure::Pawn});8],
        [None;8],
        [None;8],
        [None;8],
        [None;8],
        [Some(Piece{color: Color::Black, figure: Figure::Pawn});8],
        [Some(Piece{color: Color::Black, figure: Figure::Rook}),
         Some(Piece{color: Color::Black, figure: Figure::Knight}),
         Some(Piece{color: Color::Black, figure: Figure::Bishop}),
         Some(Piece{color: Color::Black, figure: Figure::Queen}),
         Some(Piece{color: Color::Black, figure: Figure::King}),
         Some(Piece{color: Color::Black, figure: Figure::Bishop}),
         Some(Piece{color: Color::Black, figure: Figure::Knight}),
         Some(Piece{color: Color::Black, figure: Figure::Rook})],
      ]);
  }

  #[test]
  fn board_as_string() {
    assert!(Board::initial_setup().as_string() == "rnbqkbnr\npppppppp\n        \n        \n        \n        \nPPPPPPPP\nRNBQKBNR\n");
  }

}

