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
pub struct Ply {
  pub from: Pos,
  pub to: Pos,
  pub capture: bool,
  pub en_passant: bool,
  pub castle: bool,
  pub promote: Option<Figure>,
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

  pub fn piece_at(&self, pos: Pos) -> Option<Piece> {
    self.grid[pos.rank as usize][pos.file as usize]
  }

  fn can_still_castle(&self, c: Color, f: Flank) -> bool {
    self.can_castle[c as usize][f as usize]
  }

  fn is_legal_move(&self, mv: Ply) -> bool {
    let mut legal = [None;28];
    self.legal_moves(mv.from, &mut legal);
    let mut i = 0;
    while let Some(ok) = legal[i] {
      if ok == mv { return true; }
      i += 1
    }
    return false;
  }

  /// Finds all possible legal moves for a given piece.
  pub fn legal_moves(&self, from: Pos, legal: &mut [Option<Ply>;28]) {

    // First find the squares this piece can reach regardless of check.
    self.reachable_squares(from, self.side_to_move, legal);

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

  /// Finds all possible moves for a given piece,
  /// *without* considering whether it would put you in check.
  /// This is so is_in_check can use this same method.
  fn reachable_squares(&self, from: Pos, moving_color: Color, reachable: &mut [Option<Ply>;28]) {
    // Look at all the squares on the board based on geometry,
    // until blocked or off the board.
    // If blocked: can we capture it?

    // TODO: Is this initialization necessary?:
    for i in 0..(reachable.len()) {
      reachable[i] = None;
    }
    if let Some(p) = self.piece_at(from) {
      if p.color != moving_color { return };

      match p.figure {
        Figure::Pawn   => self.reachable_squares_pawn(from, reachable),
        Figure::Rook   => self.reachable_squares_rook(from, moving_color, reachable),
        Figure::Knight => self.reachable_squares_knight(from, moving_color, reachable),
        Figure::Bishop => self.reachable_squares_bishop(from, moving_color, reachable),
        Figure::Queen  => self.reachable_squares_queen(from, moving_color, reachable),
        Figure::King   => self.reachable_squares_king(from, moving_color, reachable),
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

  fn reachable_squares_rook(&self, from: Pos, moving_color: Color, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from,  1,  0, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  0,  1, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  0, 8, moving_color, reachable, reached);
               self.reachable_squares_direction(from,  0, -1, 8, moving_color, reachable, reached);
  }

  fn reachable_squares_knight(&self, from: Pos, moving_color: Color, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from,  2,  1, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  1,  2, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  2, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -2,  1, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -2, -1, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1, -2, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  1, -2, 1, moving_color, reachable, reached);
    self.reachable_squares_direction(from,  2, -1, 1, moving_color, reachable, reached);
  }

  fn reachable_squares_bishop(&self, from: Pos, moving_color: Color, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from,  1,  1, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  1, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1, -1, 8, moving_color, reachable, reached);
               self.reachable_squares_direction(from,  1, -1, 8, moving_color, reachable, reached);
  }

  fn reachable_squares_queen(&self, from: Pos, moving_color: Color, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from,  1,  0, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  1,  1, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  0,  1, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  1, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  0, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1, -1, 8, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  0, -1, 8, moving_color, reachable, reached);
               self.reachable_squares_direction(from,  1, -1, 8, moving_color, reachable, reached);
  }

  fn reachable_squares_king(&self, from: Pos, moving_color: Color, reachable: &mut [Option<Ply>;28]) {
    let mut reached = 0;
    reached += self.reachable_squares_direction(from,  1,  0, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  1,  1, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  0,  1, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  1, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1,  0, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from, -1, -1, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  0, -1, 1, moving_color, reachable, reached);
    reached += self.reachable_squares_direction(from,  1, -1, 1, moving_color, reachable, reached);
    // Only look at castling if it's actually your turn.
    // Otherwise is_in_check comes back here and we recurse forever.
    if moving_color == self.side_to_move && !self.is_in_check(self.side_to_move) {
      if self.can_still_castle(self.side_to_move, Flank::Kingside)
          && self.piece_at(Pos{rank: from.rank, file: 5}) == None
          && self.piece_at(Pos{rank: from.rank, file: 6}) == None {
        let mv = Ply{from: from, to: Pos{rank: from.rank, file: 6}, capture: false, en_passant: false, castle: true, promote: None};
        if !self.castling_through_check(mv) {
          reachable[reached] = Some(mv);
          reached += 1;
        }
      }
      if self.can_still_castle(self.side_to_move, Flank::Queenside)
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

  fn reachable_squares_direction(&self, from: Pos, drank: i8, dfile: i8, max_dist: i8, moving_color: Color, reachable: &mut [Option<Ply>;28], reached: usize) -> usize {
    let mut d = 1;
    let mut r = 0;

    while d <= max_dist {
      let to = Pos { rank: from.rank + drank * d, file: from.file + dfile * d };
      if to.rank < 0 || to.rank > 7 || to.file < 0 || to.file > 7 { break }

      if let Some(p) = self.piece_at(to) {
        if p.color == moving_color { break }
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
      castle: false,
      .. mv
    };
    self.make_move(mv2, &mut b);
    b.is_in_check(self.side_to_move)
  }

  pub fn try_make_move(&self, mv: Ply) -> Result<Box<Board>, ()> {
    let mut b: Box<Board> = Box::new(Board { .. *self });
    if self.is_legal_move(mv) {
      self.make_move(mv, &mut b);
      Ok(b)
    } else {
      Err(())
    }
  }

  pub fn make_move(&self, mv: Ply, b: &mut Board) {
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
        b.en_passant = Some(Pos{rank: mv.from.rank - b.side_to_move.forward(), file: mv.from.file});
      }
    }
  }

  fn find_king(&self, c: Color) -> Option<Pos> {
    for rank in 0..8 {
      for file in 0..8 {
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
    for rank in 0..8 {
      for file in 0..8 {
        let pos = Pos{rank: rank, file: file};
        let sq = self.piece_at(pos);
        if let Some(p) = sq {
          if p.color != c {
            let mut reachable = [None;28];
            self.reachable_squares(pos, p.color, &mut reachable);
            let mut i = 0;
            while let Some(r) = reachable[i] {
              if r.to == k && r.capture{ return true; }
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
  use super::{Board, Piece, Color, Figure, Pos, Flank, Ply};
  use fen::fen;
  use nom::IResult::Done;

  #[test]
  fn colors() {
    assert_eq!(Color::White.other(), Color::Black);
    assert_eq!(Color::Black.other(), Color::White);
  }

  #[test]
  fn initial_setup() {
    assert_eq!(Board::initial_setup().grid, 
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
    assert_eq!(Board::initial_setup().as_string(), "rnbqkbnr\npppppppp\n        \n        \n        \n        \nPPPPPPPP\nRNBQKBNR\n");
  }

  #[test]
  fn test_find_king() {
    let mut b;
    b = board_from_fen(&b"1k6/8/8/8/8/8/8/K7 w - - 0 1"[..]);
    assert_eq!(b.find_king(Color::White), Some(Pos{rank: 0, file: 0}));
    assert_eq!(b.find_king(Color::Black), Some(Pos{rank: 7, file: 1}));
    b = board_from_fen(&b"8/8/8/8/8/8/8/K7 w - - 0 1"[..]);
    assert_eq!(b.find_king(Color::White), Some(Pos{rank: 0, file: 0}));
    assert_eq!(b.find_king(Color::Black), None);
  }

  #[test]
  fn test_is_in_check() {
    let mut b;
    
    b = board_from_fen(&b"1k6/8/8/8/8/8/8/K7 w - - 0 1"[..]);
    assert!(!b.is_in_check(Color::Black));

    b = board_from_fen(&b"1kQ5/8/8/8/8/8/8/K7 w - - 0 1"[..]);
    assert!(b.is_in_check(Color::Black));

    b = board_from_fen(&b"1k6/P7/8/8/8/8/8/K7 w - - 0 1"[..]);
    assert!(b.is_in_check(Color::Black));

    b = board_from_fen(&b"1k6/1P6/8/8/8/8/8/K7 w - - 0 1"[..]);
    assert!(!b.is_in_check(Color::Black));

    b = board_from_fen(&b"1k6/8/8/8/8/4r3/PPPP1PPP/R3K2R w KQ - 0 1"[..]);
    println!("{}", b.as_string());
    assert!(b.is_in_check(Color::White));
  }

  #[test]
  fn initial_legal_pawn_a2() {
    let b = Board::initial_setup();
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 1, file: 0}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 2, file: 0}));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 3, file: 0}));
    assert_eq!(legal[2], None);
  }

  #[test]
  fn initial_legal_pawn_a7() {
    let b = Board::initial_setup();
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 6, file: 0}, &mut legal);
    assert_eq!(legal[0], None);
  }

  #[test]
  fn initial_legal_rook_a1() {
    let b = Board::initial_setup();
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 0}, &mut legal);
    assert_eq!(legal[0], None);
  }

  #[test]
  fn initial_legal_knight_b1() {
    let b = Board::initial_setup();
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 1}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 2, file: 2}));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 2, file: 0}));
    assert_eq!(legal[2], None);
  }

  #[test]
  fn legal_rook_moves() {
    let b = board_from_fen(&b"1k6/8/8/8/8/4r3/PPPP1PPP/R2KQ2R b KQ - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 2, file: 4}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[ 0].map(|mv| mv.to), Some(Pos{rank: 3, file: 4}));
    assert_eq!(legal[ 1].map(|mv| mv.to), Some(Pos{rank: 4, file: 4}));
    assert_eq!(legal[ 2].map(|mv| mv.to), Some(Pos{rank: 5, file: 4}));
    assert_eq!(legal[ 3].map(|mv| mv.to), Some(Pos{rank: 6, file: 4}));
    assert_eq!(legal[ 4].map(|mv| mv.to), Some(Pos{rank: 7, file: 4}));
    assert_eq!(legal[ 5].map(|mv| mv.to), Some(Pos{rank: 2, file: 5}));
    assert_eq!(legal[ 6].map(|mv| mv.to), Some(Pos{rank: 2, file: 6}));
    assert_eq!(legal[ 7].map(|mv| mv.to), Some(Pos{rank: 2, file: 7}));
    assert_eq!(legal[ 8].map(|mv| mv.to), Some(Pos{rank: 1, file: 4}));
    assert_eq!(legal[ 9].map(|mv| mv.to), Some(Pos{rank: 0, file: 4}));
    assert_eq!(legal[10].map(|mv| mv.to), Some(Pos{rank: 2, file: 3}));
    assert_eq!(legal[11].map(|mv| mv.to), Some(Pos{rank: 2, file: 2}));
    assert_eq!(legal[12].map(|mv| mv.to), Some(Pos{rank: 2, file: 1}));
    assert_eq!(legal[13].map(|mv| mv.to), Some(Pos{rank: 2, file: 0}));
    assert_eq!(legal[14].map(|mv| mv.to), None);
  }

  // workaround https://github.com/Geal/nom/issues/148
  fn board_from_fen(str: &[u8]) -> Board {
    match fen(str) {
      Done(_, o) => return o,
      _ => panic!("uh oh"),
    }
  }

  #[test]
  fn legal_queen_e4() {
    let b = board_from_fen(&b"1k6/8/8/8/4Q3/8/8/K7 w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 3, file: 4}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[ 0].map(|mv| mv.to), Some(Pos{rank: 4, file: 4}));
    assert_eq!(legal[ 1].map(|mv| mv.to), Some(Pos{rank: 5, file: 4}));
    assert_eq!(legal[ 2].map(|mv| mv.to), Some(Pos{rank: 6, file: 4}));
    assert_eq!(legal[ 3].map(|mv| mv.to), Some(Pos{rank: 7, file: 4}));

    assert_eq!(legal[ 4].map(|mv| mv.to), Some(Pos{rank: 4, file: 5}));
    assert_eq!(legal[ 5].map(|mv| mv.to), Some(Pos{rank: 5, file: 6}));
    assert_eq!(legal[ 6].map(|mv| mv.to), Some(Pos{rank: 6, file: 7}));

    assert_eq!(legal[ 7].map(|mv| mv.to), Some(Pos{rank: 3, file: 5}));
    assert_eq!(legal[ 8].map(|mv| mv.to), Some(Pos{rank: 3, file: 6}));
    assert_eq!(legal[ 9].map(|mv| mv.to), Some(Pos{rank: 3, file: 7}));

    assert_eq!(legal[10].map(|mv| mv.to), Some(Pos{rank: 2, file: 5}));
    assert_eq!(legal[11].map(|mv| mv.to), Some(Pos{rank: 1, file: 6}));
    assert_eq!(legal[12].map(|mv| mv.to), Some(Pos{rank: 0, file: 7}));

    assert_eq!(legal[13].map(|mv| mv.to), Some(Pos{rank: 2, file: 4}));
    assert_eq!(legal[14].map(|mv| mv.to), Some(Pos{rank: 1, file: 4}));
    assert_eq!(legal[15].map(|mv| mv.to), Some(Pos{rank: 0, file: 4}));

    assert_eq!(legal[16].map(|mv| mv.to), Some(Pos{rank: 2, file: 3}));
    assert_eq!(legal[17].map(|mv| mv.to), Some(Pos{rank: 1, file: 2}));
    assert_eq!(legal[18].map(|mv| mv.to), Some(Pos{rank: 0, file: 1}));

    assert_eq!(legal[19].map(|mv| mv.to), Some(Pos{rank: 3, file: 3}));
    assert_eq!(legal[20].map(|mv| mv.to), Some(Pos{rank: 3, file: 2}));
    assert_eq!(legal[21].map(|mv| mv.to), Some(Pos{rank: 3, file: 1}));
    assert_eq!(legal[22].map(|mv| mv.to), Some(Pos{rank: 3, file: 0}));

    assert_eq!(legal[23].map(|mv| mv.to), Some(Pos{rank: 4, file: 3}));
    assert_eq!(legal[24].map(|mv| mv.to), Some(Pos{rank: 5, file: 2}));
    assert_eq!(legal[25].map(|mv| mv.to), Some(Pos{rank: 6, file: 1}));
    assert_eq!(legal[26].map(|mv| mv.to), Some(Pos{rank: 7, file: 0}));

    assert_eq!(legal[27].map(|mv| mv.to), None);
  }

  #[test]
  fn legal_to_castle() {
    let mut b;
    let mut legal;

    // white
    b = board_from_fen(&b"r3k2r/pppppppp/8/8/8/8/PPPPPPPP/R3K2R w KQkq - 0 1"[..]);
    legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 4}, &mut legal);
    println!("{:?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 0, file: 5}));
    assert_eq!(legal[0].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 0, file: 3}));
    assert_eq!(legal[1].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[2].map(|mv| mv.to), Some(Pos{rank: 0, file: 6}));
    assert_eq!(legal[2].map(|mv| mv.castle), Some(true));
    assert_eq!(legal[3].map(|mv| mv.to), Some(Pos{rank: 0, file: 2}));
    assert_eq!(legal[3].map(|mv| mv.castle), Some(true));
    assert_eq!(legal[4], None);

    // black
    b = board_from_fen(&b"r3k2r/pppppppp/8/8/8/8/PPPPPPPP/R3K2R b KQkq - 0 1"[..]);
    legal = [None;28];
    b.legal_moves(Pos{rank: 7, file: 4}, &mut legal);
    println!("{:?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 7, file: 5}));
    assert_eq!(legal[0].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 7, file: 3}));
    assert_eq!(legal[1].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[2].map(|mv| mv.to), Some(Pos{rank: 7, file: 6}));
    assert_eq!(legal[2].map(|mv| mv.castle), Some(true));
    assert_eq!(legal[3].map(|mv| mv.to), Some(Pos{rank: 7, file: 2}));
    assert_eq!(legal[3].map(|mv| mv.castle), Some(true));
    assert_eq!(legal[4], None);
  }

  #[test]
  fn illegal_to_castle() {
    let mut b;
    let mut legal;
    
    // Can't castle when something has moved:

    b = board_from_fen(&b"1k6/8/8/8/8/8/PPPPPPPP/R3K2R w - - 0 1"[..]);
    legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 4}, &mut legal);
    println!("{:?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 0, file: 5}));
    assert_eq!(legal[0].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 0, file: 3}));
    assert_eq!(legal[1].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[2], None);

    // Can't castle when a piece is in the way:

    b = board_from_fen(&b"1k6/8/8/8/8/8/PPPPPPPP/RN2K1NR w KQ - 0 1"[..]);
    legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 4}, &mut legal);
    println!("{:?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 0, file: 5}));
    assert_eq!(legal[0].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 0, file: 3}));
    assert_eq!(legal[1].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[2], None);

    // Can't castle out of check:

    b = board_from_fen(&b"1k6/8/8/8/8/4r3/PPPP1PPP/R3K2R w KQ - 0 1"[..]);
    legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 4}, &mut legal);
    println!("{:?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 0, file: 5}));
    assert_eq!(legal[0].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 0, file: 3}));
    assert_eq!(legal[1].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[2], None);

    // Can't castle through check:

    b = board_from_fen(&b"1k6/8/8/8/8/3r1r2/PPP3PP/R3K2R w KQ - 0 1"[..]);
    legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 4}, &mut legal);
    println!("{:?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 1, file: 4}));
    assert_eq!(legal[0].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[1], None);

    // Can't castle into check:

    b = board_from_fen(&b"1k6/8/8/8/8/2r3r1/PP1PPP1P/R3K2R w KQ - 0 1"[..]);
    legal = [None;28];
    b.legal_moves(Pos{rank: 0, file: 4}, &mut legal);
    println!("{:?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 0, file: 5}));
    assert_eq!(legal[0].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 0, file: 3}));
    assert_eq!(legal[1].map(|mv| mv.castle), Some(false));
    assert_eq!(legal[2], None);
  }

  #[test]
  fn moving_a_rook_ends_castling() {
    let b = board_from_fen(&b"1k6/8/8/8/8/8/PPPPPPPP/R3K2R w KQ - 0 1"[..]);
    assert!(b.can_still_castle(Color::White, Flank::Kingside));
    assert!(b.can_still_castle(Color::White, Flank::Queenside));
    let mv = Ply{from: Pos{rank: 0, file: 0}, to: Pos{rank: 0, file: 1}, capture: false, en_passant: false, castle: false, promote: None};
    let mut b2 = Board { .. b };
    b.make_move(mv, &mut b2);
    println!("board:\n{}", b2.as_string());
    assert!(b2.can_still_castle(Color::White, Flank::Kingside));
    assert!(!b2.can_still_castle(Color::White, Flank::Queenside));
  }

  #[test]
  fn moving_a_king_ends_castling() {
    let b = board_from_fen(&b"1k6/8/8/8/8/8/PPPPPPPP/R3K2R w KQ - 0 1"[..]);
    assert!(b.can_still_castle(Color::White, Flank::Kingside));
    assert!(b.can_still_castle(Color::White, Flank::Queenside));
    let mv = Ply{from: Pos{rank: 0, file: 4}, to: Pos{rank: 0, file: 3}, capture: false, en_passant: false, castle: false, promote: None};
    let mut b2 = Board { .. b };
    b.make_move(mv, &mut b2);
    println!("board:\n{}", b2.as_string());
    assert!(!b2.can_still_castle(Color::White, Flank::Kingside));
    assert!(!b2.can_still_castle(Color::White, Flank::Queenside));
  }

  #[test]
  fn cant_move_into_check() {
    let b = board_from_fen(&b"k6K/q7/8/8/8/8/8/8 w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 7, file: 7}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 7, file: 6}));
    assert_eq!(legal[1], None);
  }

  #[test]
  fn cant_move_a_pinned_piece() {
    let b = board_from_fen(&b"kq4BK/8/8/8/8/8/8/8 w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 7, file: 6}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0], None);
  }

  #[test]
  fn cant_move_an_incidental_piece_when_in_check() {
    let b = board_from_fen(&b"kq5K/8/8/8/8/8/7P/8 w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 1, file: 7}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0], None);
  }

  #[test]
  fn can_run_to_escape_check() {
    let b = board_from_fen(&b"kq5K/5PP1/8/8/8/8/8/8 w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 7, file: 7}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 6, file: 7}));
    assert_eq!(legal[1], None);
  }

  #[test]
  fn can_capture_to_escape_check() {
    let b = board_from_fen(&b"kq5K/B7/8/8/8/8/8/8 w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 6, file: 0}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 7, file: 1}));
    assert_eq!(legal[1], None);
  }

  #[test]
  fn can_block_to_escape_check() {
    let b = board_from_fen(&b"kq5K/7B/8/8/8/8/8/8 w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 6, file: 7}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 7, file: 6}));
    assert_eq!(legal[1], None);
  }

  #[test]
  fn cant_capture_to_escape_double_check() {
    let b = board_from_fen(&b"kq5K/B4n2/8/8/8/8/8/8 w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 6, file: 0}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0], None);
  }

  #[test]
  fn king_cant_move_next_to_a_king() {
    let b = board_from_fen(&b"k1K5/8/8/8/8/8/8/8 w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 7, file: 2}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 7, file: 3}));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 6, file: 3}));
    assert_eq!(legal[2].map(|mv| mv.to), Some(Pos{rank: 6, file: 2}));
    assert_eq!(legal[3], None);
  }

  #[test]
  fn pawn_second_move() {
    let b = board_from_fen(&b"k7/8/8/8/8/7P/8/7K w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 2, file: 7}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 3, file: 7}));
    assert_eq!(legal[1], None);
  }

  #[test]
  fn pawn_can_capture_opponents() {
    let b = board_from_fen(&b"k7/8/8/8/5n1n/6P1/8/7K w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 2, file: 6}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 3, file: 6}));
    assert_eq!(legal[0].map(|mv| mv.capture), Some(false));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 3, file: 5}));
    assert_eq!(legal[1].map(|mv| mv.capture), Some(true));
    assert_eq!(legal[2].map(|mv| mv.to), Some(Pos{rank: 3, file: 7}));
    assert_eq!(legal[2].map(|mv| mv.capture), Some(true));
    assert_eq!(legal[3], None);
  }

  #[test]
  fn pawn_cant_capture_friends() {
    let b = board_from_fen(&b"k7/8/8/8/5N1N/6P1/8/7K w - - 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 2, file: 6}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 3, file: 6}));
    assert_eq!(legal[0].map(|mv| mv.capture), Some(false));
    assert_eq!(legal[1], None);
  }

  #[test]
  fn pawn_can_capture_en_passant() {
    let b = board_from_fen(&b"k7/8/8/pPp5/8/8/8/7K w - a6 0 1"[..]);
    let mut legal = [None;28];
    b.legal_moves(Pos{rank: 4, file: 1}, &mut legal);
    println!("{:#?}", legal);
    assert_eq!(legal[0].map(|mv| mv.to), Some(Pos{rank: 5, file: 1}));
    assert_eq!(legal[0].map(|mv| mv.capture), Some(false));
    assert_eq!(legal[1].map(|mv| mv.to), Some(Pos{rank: 5, file: 0}));
    assert_eq!(legal[1].map(|mv| mv.capture), Some(true));
    assert_eq!(legal[1].map(|mv| mv.en_passant), Some(true));
    assert_eq!(legal[2], None);
  }

  #[test]
  fn pawn_jump_sets_en_passant() {
    let b = board_from_fen(&b"k7/p7/8/8/8/8/8/7K b - - 0 1"[..]);
    assert_eq!(b.en_passant, None);
    let mv = Ply{from: Pos{rank: 6, file: 0}, to: Pos{rank: 4, file: 0}, capture: false, en_passant: false, castle: false, promote: None};
    let mut b2 = Board { .. b };
    b.make_move(mv, &mut b2);
    println!("board:\n{}", b2.as_string());
    assert_eq!(b2.en_passant, Some(Pos{rank: 5, file: 0}));
  }

  #[test]
  fn en_passant_capture_removes_pawn() {
    let b = board_from_fen(&b"k7/8/8/pPp5/8/8/8/7K w - a6 0 1"[..]);
    let mv = Ply{from: Pos{rank: 4, file: 1}, to: Pos{rank: 5, file: 0}, capture: true, en_passant: true, castle: false, promote: None};
    let mut b2 = Board { .. b };
    b.make_move(mv, &mut b2);
    assert_eq!(b2.piece_at(Pos{rank: 4, file: 0}), None);
    assert_eq!(b2.piece_at(Pos{rank: 5, file: 0}), Some(Piece{color: Color::White, figure: Figure::Pawn}));
    assert_eq!(b2.en_passant, None);
  }

  #[test]
  fn en_passant_gets_cleared() {
    let b = board_from_fen(&b"k7/8/8/pPp5/8/8/8/7K w - a6 0 1"[..]);
    let mv = Ply{from: Pos{rank: 4, file: 1}, to: Pos{rank: 5, file: 1}, capture: false, en_passant: false, castle: false, promote: None};
    let mut b2 = Board { .. b };
    b.make_move(mv, &mut b2);
    assert_eq!(b2.piece_at(Pos{rank: 4, file: 0}), Some(Piece{color: Color::Black, figure: Figure::Pawn}));
    assert_eq!(b2.piece_at(Pos{rank: 5, file: 1}), Some(Piece{color: Color::White, figure: Figure::Pawn}));
    assert_eq!(b2.en_passant, None);
  }

  #[test]
  fn pawn_promotes_to_queen_moving_forward() {
    let b = board_from_fen(&b"k7/7P/8/8/8/8/8/7K w - - 0 1"[..]);
    let mv = Ply{from: Pos{rank: 6, file: 7}, to: Pos{rank: 7, file: 7}, capture: false, en_passant: false, castle: false, promote: Some(Figure::Queen)};
    let mut b2 = Board { .. b };
    b.make_move(mv, &mut b2);
    assert_eq!(b2.piece_at(Pos{rank: 6, file: 7}), None);
    assert_eq!(b2.piece_at(Pos{rank: 7, file: 7}), Some(Piece{color: Color::White, figure: Figure::Queen}));
  }

  #[test]
  fn pawn_promotes_to_knight_moving_forward() {
    let b = board_from_fen(&b"k7/7P/8/8/8/8/8/7K w - - 0 1"[..]);
    let mv = Ply{from: Pos{rank: 6, file: 7}, to: Pos{rank: 7, file: 7}, capture: false, en_passant: false, castle: false, promote: Some(Figure::Knight)};
    let mut b2 = Board { .. b };
    b.make_move(mv, &mut b2);
    assert_eq!(b2.piece_at(Pos{rank: 6, file: 7}), None);
    assert_eq!(b2.piece_at(Pos{rank: 7, file: 7}), Some(Piece{color: Color::White, figure: Figure::Knight}));
  }

  #[test]
  fn pawn_promotes_capturing() {
    let b = board_from_fen(&b"k5n1/7P/8/8/8/8/8/7K w - - 0 1"[..]);
    let mv = Ply{from: Pos{rank: 6, file: 7}, to: Pos{rank: 7, file: 6}, capture: true, en_passant: false, castle: false, promote: Some(Figure::Queen)};
    let mut b2 = Board { .. b };
    b.make_move(mv, &mut b2);
    assert_eq!(b2.piece_at(Pos{rank: 6, file: 7}), None);
    assert_eq!(b2.piece_at(Pos{rank: 7, file: 6}), Some(Piece{color: Color::White, figure: Figure::Queen}));
  }

}

