use core::str;
use core::ops::Range;

#[derive(Clone)]
pub struct Utf8Sections<'a> {
    slice: &'a [u8],
    start: usize,
    end: usize,
}

impl<'a> Utf8Sections<'a> {
    pub fn new(slice: &'a [u8]) -> Self {
        Utf8Sections {
            slice: slice,
            start: 0,
            end: slice.len(),
        }
    }

    // Same as str::is_char_boundary
    fn looks_like_char_start(&self, index: usize) -> bool {
        if index == self.slice.len() { return true; }
        match self.slice.get(index) {
            None => false,
            Some(&b) => b < 128 || b > 192,
        }
    }

    fn is_char(&self, start: usize, end: usize) -> bool {
        match str::from_utf8(&self.slice[start..end]) {
            Ok(s) => s.chars().next().unwrap().len_utf8() == end - start,
            Err(..) => false,
        }
    }

    fn make_string_from(&self, index: usize) -> &'a str {
        match str::from_utf8(&self.slice[index..]) {
            Ok(s) => s,
            Err(e) => unsafe {
                str::from_utf8_unchecked(&self.slice[index..index + e.valid_up_to()])
            }
        }
    }
}

impl<'a> Iterator for Utf8Sections<'a> {
    type Item = (usize, &'a str);

    fn next(&mut self) -> Option<(usize, &'a str)> {
        loop {
            if self.start > self.end { return None; }
            // Empty string at the end
            if self.start == self.slice.len() {
                self.start += 1;
                return Some((self.slice.len(), ""));
            }

            let str_start = self.start;
            let string = self.make_string_from(str_start);
            self.start += string.len() + 1;
            if !string.is_empty() {
                return Some((str_start, string));
            }
            // Empty string at the beginning
            if str_start == 0 { return Some((0, "")); }
        }
    }
}

impl<'a> DoubleEndedIterator for Utf8Sections<'a> {
    fn next_back(&mut self) -> Option<(usize, &'a str)> {
        // Search backwards until we find a character
        loop {
            if self.end < self.start { return None; }

            if self.looks_like_char_start(self.end) {
                match str::from_utf8(&self.slice[self.end..]) {
                    Ok(..) => break,
                    Err(e) => {
                        if e.valid_up_to() > 0 { break; }
                    }
                }
            }

            // Empty string at the beginning
            if self.end == 0 {
                self.start = 1;
                return Some((0, ""));
            }
            self.end -= 1;
        }

        // Search backwards until we find a non-character
        let mut char_end;
        'found: loop {
            char_end = self.end;
            loop {
                self.end = match self.end.checked_sub(1) {
                    Some(x) => x,
                    None => break 'found,
                };
                if self.looks_like_char_start(self.end) {
                    if self.is_char(self.end, char_end) {
                        break;
                    } else {
                        break 'found;
                    }
                }
                // No characters are more than four bytes.
                if char_end - self.end >= 4 { break 'found; }
            }
        }
        self.end = char_end.checked_sub(1).unwrap_or_else(|| { self.start = 1; 0 });
        return Some((char_end, self.make_string_from(char_end)));
    }
}


#[derive(Clone, PartialEq, Eq)]
pub enum Section<'a> {
    Unicode(&'a str),
    NonUnicode(&'a [u8]),
}

#[derive(Clone)]
pub struct SplitUnicode<'a> {
    slice: &'a [u8],
    sections: Utf8Sections<'a>,
    next_section: (Option<(usize, &'a str)>, Option<(usize, &'a str)>),
    remaining: Range<usize>,
}

impl<'a> SplitUnicode<'a> {
    pub fn new(slice: &'a [u8]) -> Self {
        SplitUnicode {
            slice: slice,
            sections: Utf8Sections::new(slice),
            next_section: (None, None),
            remaining: 0..slice.len(),
        }
    }
}

impl<'a> Iterator for SplitUnicode<'a> {
    type Item = Section<'a>;

    fn next(&mut self) -> Option<Section<'a>> {
        use self::Section::*;

        if self.remaining.start == self.remaining.end { return None; }
        if let Some((start, section)) = self.next_section.0.take() {
            // We have a stored Unicode section.  Return it.
            self.remaining.start = start + section.len();
            if section.is_empty() {
                // Utf8Sections can return empty sections at the ends.
                // Just skip them.
                self.next()
            } else {
                Some(Unicode(section))
            }
        } else {
            if let Some((start, section)) = self.sections.next() {
                // We got a new Unicode section.  Return the
                // non-Unicode part before it and store it for later.
                self.next_section.0 = Some((start, section));
                if self.remaining.start == start {
                    // There is no non-Unicode section here.
                    // Presumably we are at the beginning of the
                    // string, before the first section.  Return that
                    // one instead.
                    self.next()
                } else {
                    let result = &self.slice[self.remaining.start..start];
                    self.remaining.start = start;
                    Some(NonUnicode(result))
                }
            } else {
                // Almost done.  We've seen all the Unicode sections.
                if let Some((start, section)) = self.next_section.1 {
                    // The other direction still has a section.
                    if self.remaining.start == start {
                        // Take it and return it.
                        self.next_section.1 == None;
                        self.remaining.start = start + section.len();
                        Some(Unicode(section))
                    } else {
                        // Return the non-Unicode section before it.
                        let result = &self.slice[self.remaining.start..start];
                        self.remaining.start = start;
                        Some(NonUnicode(result))
                    }
                } else {
                    // There are no more Unicode sections, but we
                    // can't be done because we didn't return at the
                    // beginning of the function.  Return the last
                    // non-Unicode section.
                    let result = &self.slice[self.remaining.clone()];
                    self.remaining.start = self.remaining.end;
                    Some(NonUnicode(result))
                }
            }
        }
    }
}

impl<'a> DoubleEndedIterator for SplitUnicode<'a> {
    fn next_back(&mut self) -> Option<Section<'a>> {
        use self::Section::*;

        if self.remaining.start == self.remaining.end { return None; }
        if let Some((start, section)) = self.next_section.1.take() {
            // We have a stored Unicode section.  Return it.
            self.remaining.end = start;
            if section.is_empty() {
                // Utf8Sections can return empty sections at the ends.
                // Just skip them.
                self.next_back()
            } else {
                Some(Unicode(section))
            }
        } else {
            if let Some((start, section)) = self.sections.next_back() {
                // We got a new Unicode section.  Return the
                // non-Unicode part after it and store it for later.
                self.next_section.1 = Some((start, section));
                let end = start + section.len();
                if self.remaining.end == end {
                    // There is no non-Unicode section here.
                    // Presumably we are at the end of the string,
                    // after the last section.  Return that one
                    // instead.
                    self.next_back()
                } else {
                    let result = &self.slice[end..self.remaining.end];
                    self.remaining.end = end;
                    Some(NonUnicode(result))
                }
            } else {
                // Almost done.  We've seen all the Unicode sections.
                if let Some((start, section)) = self.next_section.0 {
                    // The other direction still has a section.
                    let end = start + section.len();
                    if self.remaining.end == end {
                        // Take it and return it.
                        self.next_section.0 == None;
                        self.remaining.end = start;
                        Some(Unicode(section))
                    } else {
                        // Return the non-Unicode section after it.
                        let result = &self.slice[end..self.remaining.end];
                        self.remaining.end = end;
                        Some(NonUnicode(result))
                    }
                } else {
                    // There are no more Unicode sections, but we
                    // can't be done because we didn't return at the
                    // beginning of the function.  Return the last
                    // non-Unicode section.
                    let result = &self.slice[self.remaining.clone()];
                    self.remaining.end = self.remaining.start;
                    Some(NonUnicode(result))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::prelude::v1::*;
    use super::*;

    #[test]
    fn forward_single() {
        assert_eq!(Utf8Sections::new("aé 💩".as_bytes()).collect::<Vec<_>>(),
                   [(0, "aé 💩")]);
    }

    #[test]
    fn backward_single() {
        assert_eq!(Utf8Sections::new("aé 💩".as_bytes()).rev().collect::<Vec<_>>(),
                   [(0, "aé 💩")]);
    }

    #[test]
    fn forward_empty() {
        assert_eq!(Utf8Sections::new(b"").collect::<Vec<_>>(),
                   [(0, "")]);
    }

    #[test]
    fn backward_empty() {
        assert_eq!(Utf8Sections::new(b"").rev().collect::<Vec<_>>(),
                   [(0, "")]);
    }

    #[test]
    fn forward_multiple() {
        assert_eq!(Utf8Sections::new(&[0xF0, 0x9F, 0x98, 0xBA,
                                       0xFF,
                                       0xCE, 0x93])
                   .collect::<Vec<_>>(),
                   [(0, "😺"), (5, "Γ")]);
        assert_eq!(Utf8Sections::new(&[0xF0, 0x9F, 0x98, 0xBA,
                                       0xFF, 0xFF,
                                       0xCE, 0x93])
                   .collect::<Vec<_>>(),
                   [(0, "😺"), (6, "Γ")]);
    }

    #[test]
    fn backward_multiple() {
        assert_eq!(Utf8Sections::new(&[0xF0, 0x9F, 0x98, 0xBA,
                                       0xFF,
                                       0xCE, 0x93])
                   .rev().collect::<Vec<_>>(),
                   [(5, "Γ"), (0, "😺")]);
        assert_eq!(Utf8Sections::new(&[0xF0, 0x9F, 0x98, 0xBA,
                                       0xFF, 0xFF,
                                       0xCE, 0x93])
                   .rev().collect::<Vec<_>>(),
                   [(6, "Γ"), (0, "😺")]);
    }

    #[test]
    fn forward_multiple_empty() {
        assert_eq!(Utf8Sections::new(&[0xFF]).collect::<Vec<_>>(),
                   [(0, ""), (1, "")]);
        assert_eq!(Utf8Sections::new(&[0xFF, 0xFF]).collect::<Vec<_>>(),
                   [(0, ""), (2, "")]);
    }

    #[test]
    fn backward_multiple_empty() {
        assert_eq!(Utf8Sections::new(&[0xFF]).rev().collect::<Vec<_>>(),
                   [(1, ""), (0, "")]);
        assert_eq!(Utf8Sections::new(&[0xFF, 0xFF]).rev().collect::<Vec<_>>(),
                   [(2, ""), (0, "")]);
    }

    #[test]
    fn forward_invalid_char() {
        assert_eq!(Utf8Sections::new(&[0xF0, 0x9F, 0x98, 0xBA,
                                       0xF0, 0x9F, 0x98,
                                       0xCE, 0x93])
                   .collect::<Vec<_>>(),
                   [(0, "😺"), (7, "Γ")]);
    }

    #[test]
    fn backward_invalid_char() {
        assert_eq!(Utf8Sections::new(&[0xF0, 0x9F, 0x98, 0xBA,
                                       0xF0, 0x9F, 0x98,
                                       0xCE, 0x93])
                   .rev().collect::<Vec<_>>(),
                   [(7, "Γ"), (0, "😺")]);
    }

    #[test]
    fn bidirectional_empties() {
        let buf = [0xFF];
        let mut sections = Utf8Sections::new(&buf);
        assert_eq!(sections.next(), Some((0, "")));
        assert_eq!(sections.next_back(), Some((1, "")));
        assert_eq!(sections.next_back(), None);

        let buf = [0xFF, 0xFF];
        let mut sections = Utf8Sections::new(&buf);
        assert_eq!(sections.next(), Some((0, "")));
        assert_eq!(sections.next_back(), Some((2, "")));
        assert_eq!(sections.next_back(), None);

        let buf = [0xFF, 0xFF, 0xFF];
        let mut sections = Utf8Sections::new(&buf);
        assert_eq!(sections.next(), Some((0, "")));
        assert_eq!(sections.next_back(), Some((3, "")));
        assert_eq!(sections.next_back(), None);

        let buf = [0xFF];
        let mut sections = Utf8Sections::new(&buf);
        assert_eq!(sections.next_back(), Some((1, "")));
        assert_eq!(sections.next(), Some((0, "")));
        assert_eq!(sections.next(), None);

        let buf = [0xFF, 0xFF];
        let mut sections = Utf8Sections::new(&buf);
        assert_eq!(sections.next_back(), Some((2, "")));
        assert_eq!(sections.next(), Some((0, "")));
        assert_eq!(sections.next(), None);

        let buf = [0xFF, 0xFF, 0xFF];
        let mut sections = Utf8Sections::new(&buf);
        assert_eq!(sections.next_back(), Some((3, "")));
        assert_eq!(sections.next(), Some((0, "")));
        assert_eq!(sections.next(), None);
    }

    #[test]
    fn bidirectional_nonempties() {
        let buf = [0xF0, 0x9F, 0x98, 0xBA,
                   0x20,
                   0xFF,
                   0xCE, 0x93,
                   0x23];
        let mut sections = Utf8Sections::new(&buf);
        assert_eq!(sections.next(), Some((0, "😺 ")));
        assert_eq!(sections.next_back(), Some((6, "Γ#")));
        assert_eq!(sections.next_back(), None);

        let mut sections = Utf8Sections::new(&buf);
        assert_eq!(sections.next_back(), Some((6, "Γ#")));
        assert_eq!(sections.next(), Some((0, "😺 ")));
        assert_eq!(sections.next(), None);
    }
}
