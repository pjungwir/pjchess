#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Pos {
  pub rank: i8,
  pub file: i8,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Flank {
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
pub enum Color {
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

  fn forward(self) -> i8 {
    match self {
      Color::White => 1,
      Color::Black => -1,
    }
  }

  fn pawn_rank(self) -> i8 {
    match self {
      Color::White => 1,
      Color::Black => 6,
    }
  }

  fn last_rank(self) -> i8 {
    match self {
      Color::White => 7,
      Color::Black => 0,
    }
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Figure {
  Pawn,
  Knight,
  Bishop,
  Rook,
  Queen,
  King,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Piece {
  pub color: Color,
  pub figure: Figure,
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



#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct Ply {
  from: Pos,
  to: Pos,
  capture: bool,
  en_passant: bool,
  castle: bool,
  promote: Option<Figure>,
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Board {
  pub grid: [[Option<Piece>;8];8],
  pub en_passant: Option<Pos>,  // set to the destination square of the piece that will capture.
  pub can_castle: [[bool;2];2],   // [[white kingside, white queenside], [black kingside, black queenside]]
  pub side_to_move: Color,
  pub halfmove_clock: u16,
  pub fullmove_number: u16,
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
      halfmove_clock: 0,
      fullmove_number: 1,
    };

    b
  }

  fn piece_at(&self, pos: Pos) -> Option<Piece> {
    self.grid[pos.rank as usize][pos.file as usize]
  }

  fn can_castle(&self, c: Color, f: Flank) -> bool {
    self.can_castle[c as usize][f as usize]
  }

  fn legal_moves(&self, from: Pos, legal: &mut [Option<Ply>;28]) {
    self.reachable_squares(from, legal);

    // Now take out the ones that are in check.
    let mut i = 0;
    let mut j = 0;
    while let Some(mv) = legal[i] {
      let mut b = Board { .. *self };
      self.make_move(mv, &mut b);
      if b.is_in_check(self.side_to_move) {
        legal[i] = None;
      } else {
        if i != j {
          legal[j] = legal[i];
          legal[i] = None;
        }
        j += 1;
      }
      i += 1;
    }
  }

  fn reachable_squares(&self, from: Pos, reachable: &mut [Option<Ply>;28]) {
    for i in 0..(reachable.len()) {
      reachable[i] = None;
    }
    if let Some(p) = self.piece_at(from) {
      if p.color != self.side_to_move { return };

      match p.figure {
        Figure::Pawn   => self.reachable_squares_pawn(from, reachable),
        Figure::Rook   => self.reachable_squares_rook(from, reachable),
        Figure::Knight => self.reachable_squares_knight(from, reachable),
        Figure::Bishop => self.reachable_squares_bishop(from, reachable),
        Figure::Queen  => self.reachable_squares_queen(from, reachable),
        Figure::King   => self.reachable_squares_king(from, reachable),
      }
    }
  }

  fn reachable_squares_pawn(&self, from: Pos, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    let mut to;
    let mut mv;

    // forward one:

    to = Pos{rank: from.rank + self.side_to_move.forward(), file: from.file};
    if self.piece_at(to) == None {
      mv = Ply { from: from, to: to, capture: false, en_passant: false, castle: false, promote: None };
      if mv.to.rank == self.side_to_move.last_rank() { mv.promote = Some(Figure::Queen); }
      reachable[reached] = Some(mv);
      reached += 1;

      // forward two:

      if from.rank == self.side_to_move.pawn_rank() {
        to = Pos{rank: from.rank + 2 * self.side_to_move.forward(), file: from.file};
        if self.piece_at(to) == None {
          mv = Ply { from: from, to: to, capture: false, en_passant: false, castle: false, promote: None };
          reachable[reached] = Some(mv);
          reached += 1;
        }
      }
    }

    // capture left:

    if from.file > 0 {
      to = Pos{rank: from.rank + self.side_to_move.forward(), file: from.file - 1};
      if let Some(p) = self.piece_at(to) {
        if p.color != self.side_to_move {
          mv = Ply { from: from, to: to, capture: true, en_passant: false, castle: false, promote: None };
          if mv.to.rank == self.side_to_move.last_rank() { mv.promote = Some(Figure::Queen); }
          reachable[reached] = Some(mv);
          reached += 1;
        }
      } else {
        if let Some(pos) = self.en_passant {
          if pos == to {
            mv = Ply { from: from, to: to, capture: true, en_passant: true, castle: false, promote: None };
            if mv.to.rank == self.side_to_move.last_rank() { mv.promote = Some(Figure::Queen); }
            reachable[reached] = Some(mv);
            reached += 1;
          }
        }
      }
    }

    // capture right:

    if from.file < 7 {
      to = Pos{rank: from.rank + self.side_to_move.forward(), file: from.file + 1};
      if let Some(p) = self.piece_at(to) {
        if p.color != self.side_to_move {
          mv = Ply { from: from, to: to, capture: true, en_passant: false, castle: false, promote: None };
          if mv.to.rank == self.side_to_move.last_rank() { mv.promote = Some(Figure::Queen); }
          reachable[reached] = Some(mv);
          // reached += 1;
        }
      } else {
        if let Some(pos) = self.en_passant {
          if pos == to {
            mv = Ply { from: from, to: to, capture: true, en_passant: true, castle: false, promote: None };
            if mv.to.rank == self.side_to_move.last_rank() { mv.promote = Some(Figure::Queen); }
            reachable[reached] = Some(mv);
            // reached += 1;
          }
        }
      }
    }

  }

  fn reachable_squares_rook(&self, from: Pos, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from, -1,  0, 8, reachable, reached);
    reached += self.reachable_squares_direction(from,  1,  0, 8, reachable, reached);
    reached += self.reachable_squares_direction(from,  0, -1, 8, reachable, reached);
    self.reachable_squares_direction(from,  0,  1, 8, reachable, reached);
  }

  fn reachable_squares_knight(&self, from: Pos, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from,  2,  1, 1, reachable, reached);
    reached += self.reachable_squares_direction(from,  1,  2, 1, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  2, 1, reachable, reached);
    reached += self.reachable_squares_direction(from, -2,  1, 1, reachable, reached);
    reached += self.reachable_squares_direction(from, -2, -1, 1, reachable, reached);
    reached += self.reachable_squares_direction(from, -1, -2, 1, reachable, reached);
    reached += self.reachable_squares_direction(from,  1, -2, 1, reachable, reached);
    self.reachable_squares_direction(from,  2, -1, 1, reachable, reached);
  }

  fn reachable_squares_bishop(&self, from: Pos, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from, -1, -1, 8, reachable, reached);
    reached += self.reachable_squares_direction(from,  1, -1, 8, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  1, 8, reachable, reached);
    self.reachable_squares_direction(from,  1,  1, 8, reachable, reached);
  }

  fn reachable_squares_queen(&self, from: Pos, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from, -1,  0, 8, reachable, reached);
    reached += self.reachable_squares_direction(from,  1,  0, 8, reachable, reached);
    reached += self.reachable_squares_direction(from,  0, -1, 8, reachable, reached);
    reached += self.reachable_squares_direction(from,  0,  1, 8, reachable, reached);
    reached += self.reachable_squares_direction(from, -1, -1, 8, reachable, reached);
    reached += self.reachable_squares_direction(from,  1, -1, 8, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  1, 8, reachable, reached);
    self.reachable_squares_direction(from,  1,  1, 8, reachable, reached);
  }

  fn reachable_squares_king(&self, from: Pos, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from, -1,  0, 1, reachable, reached);
    reached += self.reachable_squares_direction(from,  1,  0, 1, reachable, reached);
    reached += self.reachable_squares_direction(from,  0, -1, 1, reachable, reached);
    reached += self.reachable_squares_direction(from,  0,  1, 1, reachable, reached);
    reached += self.reachable_squares_direction(from, -1, -1, 1, reachable, reached);
    reached += self.reachable_squares_direction(from,  1, -1, 1, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  1, 1, reachable, reached);
    reached += self.reachable_squares_direction(from,  1,  1, 1, reachable, reached);
    if !self.is_in_check(self.side_to_move) {
      if self.can_castle(self.side_to_move, Flank::Kingside)
          && self.piece_at(Pos{rank: from.rank, file: 5}) == None
          && self.piece_at(Pos{rank: from.rank, file: 6}) == None {
        let mv = Ply{from: from, to: Pos{rank: from.rank, file: 6}, capture: false, en_passant: false, castle: true, promote: None};
        if !self.castling_through_check(mv) {
          reachable[reached] = Some(mv);
          // reached += 1;
        }
      }
      if self.can_castle(self.side_to_move, Flank::Queenside)
          && self.piece_at(Pos{rank: from.rank, file: 1}) == None
          && self.piece_at(Pos{rank: from.rank, file: 2}) == None
          && self.piece_at(Pos{rank: from.rank, file: 3}) == None {
        let mv = Ply{from: from, to: Pos{rank: from.rank, file: 2}, capture: false, en_passant: false, castle: true, promote: None};
        if !self.castling_through_check(mv) {
          reachable[reached] = Some(mv);
          // reached += 1;
        }
      }
    }
  }

  fn reachable_squares_direction(&self, from: Pos, drank: i8, dfile: i8, max_dist: i8, reachable: &mut [Option<Ply>;28], reached: usize) -> usize {
    // look at all the squares on the board based on geometry,
    // until blocked or off the board
    // if blocked: can we capture it?
    // are we in check?: construct a new board and see

    let mut d = 1;
    let mut r = 0;

    while d <= max_dist {
      let to = Pos { rank: from.rank + drank * d, file: from.file + dfile * d };
      if to.rank < 0 || to.rank > 7 || to.file < 0 || to.rank > 7 { break }

      if let Some(p) = self.piece_at(to) {
        if p.color == self.side_to_move { break }
        let mv = Ply{from: from, to: to, capture: true, en_passant: false, castle: false, promote: None};
        reachable[reached + r] = Some(mv);
        r += 1;
        break;
      } else {
        let mv = Ply{from: from, to: to, capture: false, en_passant: false, castle: false, promote: None};
        reachable[reached + r] = Some(mv);
        r += 1;
      }

      d += 1;
    }

    r
  }

  fn castling_through_check(&self, mv: Ply) -> bool {
    let mut b = Board { .. *self };
    let dir = if mv.to.file == 2 { 1 } else { -1 };
    let mv2 = Ply {
      to: Pos { rank: mv.to.rank, file: mv.to.file + dir },
      .. mv
    };
    self.make_move(mv2, &mut b);
    b.is_in_check(self.side_to_move)
  }

  fn make_move(&self, mv: Ply, b: &mut Board) {
    b.clone_from(&self);
    let p = self.grid[mv.from.rank as usize][mv.from.file as usize].expect("must move something");
    b.grid[mv.from.rank as usize][mv.from.file as usize] = None;

    if let Some(promotion) = mv.promote {
      b.grid[mv.to.rank as usize][mv.to.file as usize] = Some(Piece{color: p.color, figure: promotion});
    } else {
      b.grid[mv.to.rank as usize][mv.to.file as usize] = Some(p);
    }

    if mv.en_passant {
      b.grid[(mv.to.rank - self.side_to_move.forward()) as usize][mv.to.file as usize] = None;
    }

    if mv.castle {
      if mv.to.file == 2 {
        b.grid[mv.to.rank as usize][3] = b.grid[mv.to.rank as usize][0];
        b.grid[mv.to.rank as usize][0] = None;
      } else {
        b.grid[mv.to.rank as usize][5] = b.grid[mv.to.rank as usize][7];
        b.grid[mv.to.rank as usize][7] = None;
      }
    }

    b.side_to_move = self.side_to_move.other();

    b.en_passant = None;
    if p.figure == Figure::King {
      b.can_castle[self.side_to_move as usize][Flank::Kingside as usize] = false;
      b.can_castle[self.side_to_move as usize][Flank::Queenside as usize] = false;
    } else if p.figure == Figure::Rook {
      if mv.from.file == 0 { b.can_castle[self.side_to_move as usize][Flank::Queenside as usize] = false; }
      else if mv.from.file == 7 { b.can_castle[self.side_to_move as usize][Flank::Kingside as usize] = false; }
    } else if p.figure == Figure::Pawn {
      if (mv.from.rank - mv.to.rank).abs() == 2 {
        b.en_passant = Some(Pos{rank: mv.from.rank + b.side_to_move.forward(), file: mv.from.file});
      }
    }
  }

  fn find_king(&self, c: Color) -> Option<Pos> {
    for rank in 0..7 {
      for file in 0..7 {
        let pos = Pos{rank: rank, file: file};
        if let Some(p) = self.piece_at(pos) {
          if p.color == c && p.figure == Figure::King {
            return Some(pos);
          }
        }
      }
    }
    return None;
  }

  fn is_in_check(&self, c: Color) -> bool {
    let k = self.find_king(c).expect("no king found");
    for rank in 0..7 {
      for file in 0..7 {
        let pos = Pos{rank: rank, file: file};
        let sq = self.piece_at(pos);
        if let Some(p) = sq {
          if p.color != c {
            let mut reachable = [None;28];
            self.reachable_squares(pos, &mut reachable);
            let mut i = 0;
            while let Some(r) = reachable[i] {
              if r.to == k { return true; }
              i += 1;
            }
          }
        }
      }
    }
    false
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

  #[test]
  fn initial_legal_pawn_a2() {
    let b = Board::initial_setup();
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 1, file: 0}, &mut legal);
    println!("{:#?}", legal);
    assert!(legal[0].map(|mv| mv.to) == Some(Pos{rank: 2, file: 0}));
    assert!(legal[1].map(|mv| mv.to) == Some(Pos{rank: 3, file: 0}));
    assert!(legal[2] == None);
  }

  #[test]
  fn initial_legal_pawn_a7() {
    let b = Board::initial_setup();
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 6, file: 0}, &mut legal);
    assert!(legal[0] == None);
  }

  #[test]
  fn initial_legal_rook_a1() {
    let b = Board::initial_setup();
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 0}, &mut legal);
    assert!(legal[0] == None);
  }

  #[test]
  fn initial_legal_knight_b1() {
    let b = Board::initial_setup();
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 1}, &mut legal);
    println!("{:#?}", legal);
    assert!(legal[0].map(|mv| mv.to) == Some(Pos{rank: 2, file: 2}));
    assert!(legal[1].map(|mv| mv.to) == Some(Pos{rank: 2, file: 0}));
    assert!(legal[2] == None);
  }

  // TODO: test for is_in_check
  // TODO: test queen with 28 moves
  // TODO: test for castling allowed, not allowed
  // TODO: test for e.p. allowed, not allowed, result of taking
  // TODO: test for promotion
  // TODO: parse FEN

}

