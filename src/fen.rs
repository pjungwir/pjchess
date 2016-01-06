use board::*;
use nom::{digit,is_digit,eof};
use nom::Err;

use std::str;
use std::str::FromStr;

named!(fen <&[u8], Board>,
  chain!(
    grid:            grid            ~
                     tag!(" ")       ~
    whose_turn:      whose_turn      ~
                     tag!(" ")       ~
    castling:        castling        ~
                     tag!(" ")       ~
    en_passant:      pos             ~
                     tag!(" ")       ~
    halfmove_clock:  halfmove_clock  ~
                     tag!(" ")       ~
    fullmove_number: fullmove_number ~
                     eof,
    || {
      Board {
        grid: grid,
        en_passant: en_passant,
        can_castle: castling,
        side_to_move: whose_turn,
        halfmove_clock: halfmove_clock,
        fullmove_number: fullmove_number,
      }
    }
  )
);

named!(grid <&[u8], [[Option<Piece>;8];8]>,
  chain!(
    row0: grid_row  ~
          tag!("/") ~
    row1: grid_row  ~
          tag!("/") ~
    row2: grid_row  ~
          tag!("/") ~
    row3: grid_row  ~
          tag!("/") ~
    row4: grid_row  ~
          tag!("/") ~
    row5: grid_row  ~
          tag!("/") ~
    row6: grid_row  ~
          tag!("/") ~
    row7: grid_row,
    || {
      [row7, row6, row5, row4, row3, row2, row1, row0]
    }
  )
);


named!(grid_row <&[u8], [Option<Piece>;8]>,
  map_res!(
    is_a!("12345678kqrbnpKQRBNP"),
    |str: &[u8]| -> Result<[Option<Piece>;8], ()> {
      let mut ret = [None;8];
      let mut i: usize = 0;
      for c in str {
        if is_digit(*c) {
          i += FromStr::from_str(str::from_utf8(&[*c]).unwrap()).unwrap();
        } else {
          match *c as char {
            'K' => ret[i] = Some(Piece{color: Color::White, figure: Figure::King}),
            'Q' => ret[i] = Some(Piece{color: Color::White, figure: Figure::Queen}),
            'R' => ret[i] = Some(Piece{color: Color::White, figure: Figure::Rook}),
            'B' => ret[i] = Some(Piece{color: Color::White, figure: Figure::Bishop}),
            'N' => ret[i] = Some(Piece{color: Color::White, figure: Figure::Knight}),
            'P' => ret[i] = Some(Piece{color: Color::White, figure: Figure::Pawn}),
            'k' => ret[i] = Some(Piece{color: Color::Black, figure: Figure::King}),
            'q' => ret[i] = Some(Piece{color: Color::Black, figure: Figure::Queen}),
            'r' => ret[i] = Some(Piece{color: Color::Black, figure: Figure::Rook}),
            'b' => ret[i] = Some(Piece{color: Color::Black, figure: Figure::Bishop}),
            'n' => ret[i] = Some(Piece{color: Color::Black, figure: Figure::Knight}),
            'p' => ret[i] = Some(Piece{color: Color::Black, figure: Figure::Pawn}),
            _ => return Err(()),
          }
          i += 1
        }
      }
      if i != 8 { return Err(()); }
      Ok(ret)
    }
  )
);


named!(halfmove_clock <&[u8], u16>,
  map_res!(
    map_res!(
      digit,
      str::from_utf8
    ),
    FromStr::from_str
  )
);
 
named!(fullmove_number <&[u8], u16>,
  map_res!(
    map_res!(
      digit,
      str::from_utf8
    ),
    FromStr::from_str
  )
);

named!(whose_turn <&[u8], Color>,
  map_res!(
    take!(1),
    |ch: &[u8]| -> Result<Color, ()> {
       match ch[0] as char {
        'w' => Ok(Color::White),
        'b' => Ok(Color::Black),
        _ => Err(()),
      }
    }
  )
);


named!(castling <&[u8], [[bool;2];2]>,
  alt!(
    tag!("-") => {|_| [[false, false], [false, false]]} |
    map_res!(
      is_a!("kqKQ"),
      |str: &[u8]| -> Result<[[bool;2];2], ()> {
        let mut ret = [[false, false], [false, false]];
        for c in str {
          match *c as char {
            'K' => ret[Color::White as usize][Flank::Kingside as usize] = true,
            'Q' => ret[Color::White as usize][Flank::Queenside as usize] = true,
            'k' => ret[Color::Black as usize][Flank::Kingside as usize] = true,
            'q' => ret[Color::Black as usize][Flank::Queenside as usize] = true,
            _ => return Err(()),
          }
        }
        Ok(ret)
      }
    )
  )
);


named!(file <&[u8], i8>,
  map_res!(
    take!(1),
    |ch: &[u8]| -> Result<i8, ()> {
       match ch[0] as char {
        'a' => Ok(0),
        'b' => Ok(1),
        'c' => Ok(2),
        'd' => Ok(3),
        'e' => Ok(4),
        'f' => Ok(5),
        'g' => Ok(6),
        'h' => Ok(7),
        _ => Err(()),
      }
    }
  )
);

named!(rank <&[u8], i8>,
  map_res!(
    take!(1),
    |ch: &[u8]| -> Result<i8, ()> {
      match ch[0] as char {
        '1' => Ok(0),
        '2' => Ok(1),
        '3' => Ok(2),
        '4' => Ok(3),
        '5' => Ok(4),
        '6' => Ok(5),
        '7' => Ok(6),
        '8' => Ok(7),
        _ => Err(()),
      }
    }
  )
);

named!(pos <&[u8], Option<Pos> >,
  alt!(
    tag!("-") => {|_| None} |
    chain!(
      file: file ~
      rank: rank
      ,
      || {
        Some(Pos{rank: rank, file: file})
      }
    )
  )
);

#[cfg(test)]
mod test {
  use board::{Pos,Color,Figure,Piece,Board};
  use super::{file,rank,pos,halfmove_clock,fullmove_number,whose_turn,castling,grid_row,grid,fen};
  use nom::ErrorKind;
  use nom::Err::Position;
  use nom::Needed::Size;
  use nom::IResult::*;


  #[test]
  fn file_test() {
    assert_eq!(file(&b"a"[..]), Done(&b""[..], 0));
    assert_eq!(file(&b"b"[..]), Done(&b""[..], 1));
    assert_eq!(file(&b"h"[..]), Done(&b""[..], 7));
    assert_eq!(file(&b"j"[..]), Error(Position(ErrorKind::MapRes, &b"j"[..])));
    assert_eq!(file(&b""[..]), Incomplete(Size(1)));
  }

  #[test]
  fn rank_test() {
    assert_eq!(rank(&b"1"[..]), Done(&b""[..], 0));
    assert_eq!(rank(&b"2"[..]), Done(&b""[..], 1));
    assert_eq!(rank(&b"8"[..]), Done(&b""[..], 7));
    assert_eq!(rank(&b"9"[..]), Error(Position(ErrorKind::MapRes, &b"9"[..])));
    assert_eq!(rank(&b"0"[..]), Error(Position(ErrorKind::MapRes, &b"0"[..])));
    assert_eq!(rank(&b"j"[..]), Error(Position(ErrorKind::MapRes, &b"j"[..])));
    assert_eq!(rank(&b""[..]), Incomplete(Size(1)));
  }

  #[test]
  fn pos_test() {
    assert_eq!(pos(&b"a1"[..]), Done(&b""[..], Some(Pos{rank: 0, file: 0})));
    assert_eq!(pos(&b"h8"[..]), Done(&b""[..], Some(Pos{rank: 7, file: 7})));
    assert_eq!(pos(&b"a9"[..]), Error(Position(ErrorKind::Alt, &b"a9"[..])));
    assert_eq!(pos(&b"-"[..]), Done(&b""[..], None));
  }

  #[test]
  fn halfmove_clock_test() {
    assert_eq!(halfmove_clock(&b"0"[..]), Done(&b""[..], 0));
    assert_eq!(halfmove_clock(&b"1"[..]), Done(&b""[..], 1));
    assert_eq!(halfmove_clock(&b"33"[..]), Done(&b""[..], 33));
    assert_eq!(halfmove_clock(&b""[..]), Error(Position(ErrorKind::Digit, &b""[..])));
    assert_eq!(halfmove_clock(&b"a"[..]), Error(Position(ErrorKind::Digit, &b"a"[..])));
    assert_eq!(halfmove_clock(&b"-1"[..]), Error(Position(ErrorKind::Digit, &b"-1"[..])));
  }

  #[test]
  fn fullmove_number_test() {
    assert_eq!(fullmove_number(&b"0"[..]), Done(&b""[..], 0));
    assert_eq!(fullmove_number(&b"1"[..]), Done(&b""[..], 1));
    assert_eq!(fullmove_number(&b"33"[..]), Done(&b""[..], 33));
    assert_eq!(fullmove_number(&b""[..]), Error(Position(ErrorKind::Digit, &b""[..])));
    assert_eq!(fullmove_number(&b"a"[..]), Error(Position(ErrorKind::Digit, &b"a"[..])));
    assert_eq!(fullmove_number(&b"-1"[..]), Error(Position(ErrorKind::Digit, &b"-1"[..])));
  }

  #[test]
  fn whose_turn_test() {
    assert_eq!(whose_turn(&b"w"[..]), Done(&b""[..], Color::White));
    assert_eq!(whose_turn(&b"b"[..]), Done(&b""[..], Color::Black));
    assert_eq!(whose_turn(&b""[..]), Incomplete(Size(1)));
    assert_eq!(whose_turn(&b"c"[..]), Error(Position(ErrorKind::MapRes, &b"c"[..])));
  }

  #[test]
  fn castling_test() {
    assert_eq!(castling(&b"-"[..]), Done(&b""[..], [[false, false], [false, false]]));
    assert_eq!(castling(&b"kqKQ"[..]), Done(&b""[..], [[true, true], [true, true]]));
    assert_eq!(castling(&b"KQkq"[..]), Done(&b""[..], [[true, true], [true, true]]));
    assert_eq!(castling(&b"k"[..]), Done(&b""[..], [[false, false], [true, false]]));
    assert_eq!(castling(&b"kQ"[..]), Done(&b""[..], [[false, true], [true, false]]));
    assert_eq!(castling(&b""[..]), Incomplete(Size(1)));
    assert_eq!(castling(&b"F"[..]), Error(Position(ErrorKind::Alt, &b"F"[..])));
  }

  #[test]
  fn grid_row_test() {
    // too short:
    assert_eq!(grid_row(&b"p"[..]), Error(Position(ErrorKind::MapRes, &b"p"[..])));
    assert_eq!(grid_row(&b"ppppppp"[..]), Error(Position(ErrorKind::MapRes, &b"ppppppp"[..])));

    // too long:
    assert_eq!(grid_row(&b"88"[..]), Error(Position(ErrorKind::MapRes, &b"88"[..])));
    assert_eq!(grid_row(&b"81"[..]), Error(Position(ErrorKind::MapRes, &b"81"[..])));
    assert_eq!(grid_row(&b"7p1"[..]), Error(Position(ErrorKind::MapRes, &b"7p1"[..])));

    // just right:
    assert_eq!(grid_row(&b"pppppppp"[..]), Done(&b""[..], [Some(Piece{color: Color::Black, figure: Figure::Pawn});8]));
    assert_eq!(grid_row(&b"8"[..]), Done(&b""[..], [None;8]));
    assert_eq!(grid_row(&b"1R5k"[..]), Done(&b""[..], [None, Some(Piece{color: Color::White, figure: Figure::Rook}), None, None, None, None, None, Some(Piece{color: Color::Black, figure: Figure::King})]));
    assert_eq!(grid_row(&b"R6k"[..]), Done(&b""[..], [Some(Piece{color: Color::White, figure: Figure::Rook}), None, None, None, None, None, None, Some(Piece{color: Color::Black, figure: Figure::King})]));
    assert_eq!(grid_row(&b"R5k1"[..]), Done(&b""[..], [Some(Piece{color: Color::White, figure: Figure::Rook}), None, None, None, None, None, Some(Piece{color: Color::Black, figure: Figure::King}), None]));
  }

  #[test]
  fn grid_test() {
    assert_eq!(grid(&b"8/8/8/8/8/8/8/8"[..]), Done(&b""[..], [[None;8];8]));
    assert_eq!(grid(&b"rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR"[..]), Done(&b""[..], [
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
      ]));

    assert_eq!(grid(&b"rnbqkbnr/pppppppp"[..]), Incomplete(Size(18)));
  }

  #[test]
  fn fen_test() {
    assert_eq!(fen(&b"rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"[..]), Done(&b""[..], Board {
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
    }));
  }

}
