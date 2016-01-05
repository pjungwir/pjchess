#[macro_use]

use board::*;
use nom::{IResult,digit,is_digit};
use nom::Err;
use nom::IResult::*;

use std::str;
use std::str::FromStr;

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

/*
named!(fen<&[u8], &Board>,
  chain!(
                     tag!(" ") ~
    en_passant:      pos ~
                     tag!(" ") ~
    halfmove_clock:  digit ~
                     tag!(" ") ~
    fullmove_number: digit ~ 
                     eof ~
    ,
    || {
    }
  )
);
*/

#[cfg(test)]
mod test {
  use board::{Pos,Color,Flank};
  use super::{file,rank,pos,halfmove_clock,fullmove_number,whose_turn,castling};
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
    assert_eq!(halfmove_clock(&b""[..]), Error(Position(ErrorKind::MapRes, &b""[..])));
    assert_eq!(halfmove_clock(&b"a"[..]), Error(Position(ErrorKind::Digit, &b"a"[..])));
    assert_eq!(halfmove_clock(&b"-1"[..]), Error(Position(ErrorKind::Digit, &b"-1"[..])));
  }

  #[test]
  fn fullmove_number_test() {
    assert_eq!(fullmove_number(&b"0"[..]), Done(&b""[..], 0));
    assert_eq!(fullmove_number(&b"1"[..]), Done(&b""[..], 1));
    assert_eq!(fullmove_number(&b"33"[..]), Done(&b""[..], 33));
    assert_eq!(fullmove_number(&b""[..]), Error(Position(ErrorKind::MapRes, &b""[..])));
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

}
