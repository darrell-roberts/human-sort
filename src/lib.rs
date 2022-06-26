use std::{
  cmp::Ordering,
  iter::{from_fn, zip},
};

/// Represents a User input item that has "Human sort" behavior.
#[derive(Debug, PartialEq, Eq, Default)]
struct Item<'a>(&'a str);

/// Item is comprised of contiguous sequences of digits or non-digits.
#[derive(Debug, PartialEq, Eq)]
enum ItemPart<'a> {
  Digits(&'a str, usize),
  NonDigits(&'a str),
}

impl<'a> ItemPart<'a> {
  /// Get the inner string slice length
  fn len(&self) -> usize {
    match self {
      Self::Digits(s, _) => s.len(),
      Self::NonDigits(s) => s.len(),
    }
  }

  /// Is the inner string slice empty
  fn is_empty(&self) -> bool {
    match self {
      Self::Digits(s, _) => s.is_empty(),
      Self::NonDigits(s) => s.is_empty(),
    }
  }
}

impl<'a> PartialOrd for ItemPart<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<'a> Ord for ItemPart<'a> {
  /// Perform number to number and string to string comparisons. Promote
  /// digits over strings when comparing.
  fn cmp(&self, other: &Self) -> Ordering {
    match (self, other) {
      (Self::Digits(_, n1), Self::Digits(_, n2)) => n1.cmp(n2),
      (Self::NonDigits(s1), Self::NonDigits(s2)) => s1.cmp(s2),
      (Self::Digits(_, _), Self::NonDigits(_)) => Ordering::Less,
      (Self::NonDigits(_), Self::Digits(_, _)) => Ordering::Greater,
    }
  }
}

/// Parse the first ItemPart segment from given string slice.
fn parse_item_part(item_str: &str) -> ItemPart {
  let digits = item_str.chars().take_while(|c| c.is_digit(10)).count();
  let non_digits = item_str.chars().take_while(|c| !c.is_digit(10)).count();

  if digits > 0 {
    let digit_str = &item_str[0..digits];
    ItemPart::Digits(digit_str, digit_str.parse().unwrap_or_default())
  } else {
    ItemPart::NonDigits(&item_str[0..non_digits])
  }
}

/// Create an iteration of ItemPart from a given string slice.
fn parse_item_parts<'a>(
  item_str: &'a str,
) -> impl Iterator<Item = ItemPart> + 'a {
  let mut remaining = item_str;

  from_fn(move || {
    let part = parse_item_part(remaining);
    remaining = &remaining[part.len()..];
    if part.is_empty() {
      None
    } else {
      Some(part)
    }
  })
}

impl<'a> PartialOrd for Item<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<'a> Ord for Item<'a> {
  fn cmp(&self, other: &Self) -> Ordering {
    match (self.0.is_empty(), other.0.is_empty()) {
      (true, true) => Ordering::Equal,
      (true, false) => Ordering::Less,
      (false, true) => Ordering::Greater,
      (false, false) => {
        zip(parse_item_parts(self.0), parse_item_parts(other.0))
          .fold(Ordering::Equal, |accum: Ordering, (a, b)| {
            accum.then(a.cmp(&b))
          })
      }
    }
  }
}

#[cfg(test)]
mod test {
  use crate::{parse_item_parts, Item, ItemPart};

  #[test]
  fn test_parse() {
    let test = "1234hello812the";
    let result = parse_item_parts(test).collect::<Vec<_>>();
    dbg!(&result);
    assert_eq!(
      result,
      [
        ItemPart::Digits("1234", 1234),
        ItemPart::NonDigits("hello"),
        ItemPart::Digits("812", 812),
        ItemPart::NonDigits("the"),
      ]
    )
  }

  #[test]
  fn test_ordering() {
    let str1 = "12345hello";
    let str2 = "234hello";

    // Default string ordering
    assert!(str2 > str1);

    // Human ordering
    assert!(Item(str1) > Item(str2));
  }

  #[test]
  fn test_equality() {
    let str1 = Item("1234hello");
    let str2 = Item("1234hello");

    assert_eq!(str1, str2)
  }

  #[test]
  fn test_human_sort() {
    let mut items = [
      Item("5 task abc"),
      Item("72 bbb"),
      Item("7 blah"),
      Item("1 task 2"),
      Item("4 ha"),
      Item("112abc"),
      Item("11abc"),
      Item("test12"),
      Item("test123"),
      Item("1babc"),
      Item("01 task 3"),
      Item("1 task 1"),
      Item("1b"),
      Item(""),
      Item("1b abc"),
      Item("1czz"),
    ];

    items.sort();

    dbg!(&items);
    assert_eq!(
      items,
      [
        Item(""),
        Item("1 task 1"),
        Item("1 task 2"),
        Item("01 task 3"),
        Item("1b"),
        Item("1b abc"),
        Item("1babc"),
        Item("1czz"),
        Item("4 ha"),
        Item("5 task abc"),
        Item("7 blah"),
        Item("11abc"),
        Item("72 bbb"),
        Item("112abc"),
        Item("test12"),
        Item("test123")
      ]
    )
  }
}
