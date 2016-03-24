// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Implementation of [the WTF-8 encoding](https://simonsapin.github.io/wtf-8/).
//!
//! This library uses Rust’s type system to maintain
//! [well-formedness](https://simonsapin.github.io/wtf-8/#well-formed),
//! like the `String` and `&str` types do for UTF-8.
//!
//! Since [WTF-8 must not be used
//! for interchange](https://simonsapin.github.io/wtf-8/#intended-audience),
//! this library deliberately does not provide access to the underlying bytes
//! of WTF-8 strings,
//! nor can it decode WTF-8 from arbitrary bytes.
//! WTF-8 strings can be obtained from UTF-8, UTF-16, or code points.

// this module is imported from @SimonSapin's repo and has tons of dead code on
// unix (it's mostly used on windows), so don't worry about dead code here.
#![allow(dead_code)]

use split_bytes;
use utf8_sections::{self, Utf8Sections};

use core::str::next_code_point;

use str::next_code_point_reverse;
use slice_searcher::SliceSearcher;

use std::ascii::*;
use std::borrow::{Borrow, Cow, ToOwned};
use std::char;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter::{self, FromIterator};
use std::mem;
use std::ops;
use std::slice;
use std::str;
use core::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher};
use std::string::String;
//use std::sys_common::AsInner;
use std::vec::Vec;

const UTF8_REPLACEMENT_CHARACTER: &'static [u8] = b"\xEF\xBF\xBD";

// UTF-8 ranges and tags for encoding characters
const TAG_CONT: u8    = 0b1000_0000;
const TAG_TWO_B: u8   = 0b1100_0000;
const TAG_THREE_B: u8 = 0b1110_0000;
const TAG_FOUR_B: u8  = 0b1111_0000;
const MAX_ONE_B: u32   =     0x80;
const MAX_TWO_B: u32   =    0x800;
const MAX_THREE_B: u32 =  0x10000;

#[inline]
fn encode_utf8_raw(code: u32, dst: &mut [u8]) -> Option<usize> {
    // Marked #[inline] to allow llvm optimizing it away
    if code < MAX_ONE_B && !dst.is_empty() {
        dst[0] = code as u8;
        Some(1)
    } else if code < MAX_TWO_B && dst.len() >= 2 {
        dst[0] = (code >> 6 & 0x1F) as u8 | TAG_TWO_B;
        dst[1] = (code & 0x3F) as u8 | TAG_CONT;
        Some(2)
    } else if code < MAX_THREE_B && dst.len() >= 3  {
        dst[0] = (code >> 12 & 0x0F) as u8 | TAG_THREE_B;
        dst[1] = (code >>  6 & 0x3F) as u8 | TAG_CONT;
        dst[2] = (code & 0x3F) as u8 | TAG_CONT;
        Some(3)
    } else if dst.len() >= 4 {
        dst[0] = (code >> 18 & 0x07) as u8 | TAG_FOUR_B;
        dst[1] = (code >> 12 & 0x3F) as u8 | TAG_CONT;
        dst[2] = (code >>  6 & 0x3F) as u8 | TAG_CONT;
        dst[3] = (code & 0x3F) as u8 | TAG_CONT;
        Some(4)
    } else {
        None
    }
}

#[inline]
fn encode_utf16_raw(mut ch: u32, dst: &mut [u16]) -> Option<usize> {
    // Marked #[inline] to allow llvm optimizing it away
    if (ch & 0xFFFF) == ch && !dst.is_empty() {
        // The BMP falls through (assuming non-surrogate, as it should)
        dst[0] = ch as u16;
        Some(1)
    } else if dst.len() >= 2 {
        // Supplementary planes break into surrogates.
        ch -= 0x1_0000;
        dst[0] = 0xD800 | ((ch >> 10) as u16);
        dst[1] = 0xDC00 | ((ch as u16) & 0x3FF);
        Some(2)
    } else {
        None
    }
}

/// A Unicode code point: from U+0000 to U+10FFFF.
///
/// Compare with the `char` type,
/// which represents a Unicode scalar value:
/// a code point that is not a surrogate (U+D800 to U+DFFF).
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Copy)]
pub struct CodePoint {
    value: u32
}

/// Format the code point as `U+` followed by four to six hexadecimal digits.
/// Example: `U+1F4A9`
impl fmt::Debug for CodePoint {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(formatter, "U+{:04X}", self.value)
    }
}

impl CodePoint {
    /// Unsafely creates a new `CodePoint` without checking the value.
    ///
    /// Only use when `value` is known to be less than or equal to 0x10FFFF.
    #[inline]
    pub unsafe fn from_u32_unchecked(value: u32) -> CodePoint {
        CodePoint { value: value }
    }

    /// Creates a new `CodePoint` if the value is a valid code point.
    ///
    /// Returns `None` if `value` is above 0x10FFFF.
    #[inline]
    pub fn from_u32(value: u32) -> Option<CodePoint> {
        match value {
            0 ... 0x10FFFF => Some(CodePoint { value: value }),
            _ => None
        }
    }

    /// Creates a new `CodePoint` from a `char`.
    ///
    /// Since all Unicode scalar values are code points, this always succeeds.
    #[inline]
    pub fn from_char(value: char) -> CodePoint {
        CodePoint { value: value as u32 }
    }

    /// Returns the numeric value of the code point.
    #[inline]
    pub fn to_u32(&self) -> u32 {
        self.value
    }

    /// Optionally returns a Unicode scalar value for the code point.
    ///
    /// Returns `None` if the code point is a surrogate (from U+D800 to U+DFFF).
    #[inline]
    pub fn to_char(&self) -> Option<char> {
        match self.value {
            0xD800 ... 0xDFFF => None,
            _ => Some(unsafe { char::from_u32_unchecked(self.value) })
        }
    }

    /// Returns a Unicode scalar value for the code point.
    ///
    /// Returns `'\u{FFFD}'` (the replacement character “�”)
    /// if the code point is a surrogate (from U+D800 to U+DFFF).
    #[inline]
    pub fn to_char_lossy(&self) -> char {
        self.to_char().unwrap_or('\u{FFFD}')
    }

    /// Returns the code point at the start of the bytes returned by
    /// the iterator.
    pub fn from_iterator(mut iter: &mut slice::Iter<u8>) -> Option<CodePoint> {
        next_code_point(iter).map(|c| CodePoint { value: c })
    }

    /// Returns the code point at the end of the bytes returned by the
    /// iterator.
    pub fn from_iterator_reverse(mut iter: &mut slice::Iter<u8>) -> Option<CodePoint> {
        next_code_point_reverse(iter).map(|c| CodePoint { value: c })
    }

    /// Returns the surrogate decomposition of the code point.
    pub fn to_surrogates(&self) -> Option<(u16, u16)> {
        let mut buf = [0; 2];
        match encode_utf16_raw(self.value, &mut buf) {
            Some(2) => Some((buf[0], buf[1])),
            _ => None
        }
    }
}

/// An owned, growable string of well-formed WTF-8 data.
///
/// Similar to `String`, but can additionally contain surrogate code points
/// if they’re not in a surrogate pair.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone)]
pub struct Wtf8Buf {
    bytes: Vec<u8>
}

impl ops::Deref for Wtf8Buf {
    type Target = Wtf8;

    fn deref(&self) -> &Wtf8 {
        self.as_slice()
    }
}

impl Borrow<Wtf8> for Wtf8Buf {
    fn borrow(&self) -> &Wtf8 { &self[..] }
}

impl AsRef<Wtf8> for Wtf8Buf {
    fn as_ref(&self) -> &Wtf8 { &self[..] }
}

impl AsRef<Wtf8> for Wtf8 {
    fn as_ref(&self) -> &Wtf8 { self }
}

impl AsRef<Wtf8> for str {
    fn as_ref(&self) -> &Wtf8 { Wtf8::from_str(self) }
}

impl ToOwned for Wtf8 {
    type Owned = Wtf8Buf;
    fn to_owned(&self) -> Wtf8Buf { Wtf8Buf { bytes: self.bytes.to_owned() } }
}

/// Format the string with double quotes,
/// and surrogates as `\u` followed by four hexadecimal digits.
/// Example: `"a\u{D800}"` for a string with code points [U+0061, U+D800]
impl fmt::Debug for Wtf8Buf {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::Debug::fmt(&**self, formatter)
    }
}

impl Wtf8Buf {
    /// Creates an new, empty WTF-8 string.
    #[inline]
    pub fn new() -> Wtf8Buf {
        Wtf8Buf { bytes: Vec::new() }
    }

    /// Creates an new, empty WTF-8 string with pre-allocated capacity for `n` bytes.
    #[inline]
    pub fn with_capacity(n: usize) -> Wtf8Buf {
        Wtf8Buf { bytes: Vec::with_capacity(n) }
    }

    /// Creates a WTF-8 string from a UTF-8 `String`.
    ///
    /// This takes ownership of the `String` and does not copy.
    ///
    /// Since WTF-8 is a superset of UTF-8, this always succeeds.
    #[inline]
    pub fn from_string(string: String) -> Wtf8Buf {
        Wtf8Buf { bytes: string.into_bytes() }
    }

    /// Creates a WTF-8 string from a UTF-8 `&str` slice.
    ///
    /// This copies the content of the slice.
    ///
    /// Since WTF-8 is a superset of UTF-8, this always succeeds.
    #[inline]
    pub fn from_str(str: &str) -> Wtf8Buf {
        Wtf8Buf { bytes: <[_]>::to_vec(str.as_bytes()) }
    }

    /// Creates a WTF-8 string from a potentially ill-formed UTF-16 slice of 16-bit code units.
    ///
    /// This is lossless: calling `.encode_wide()` on the resulting string
    /// will always return the original code units.
    pub fn from_wide(v: &[u16]) -> Wtf8Buf {
        let mut string = Wtf8Buf::with_capacity(v.len());
        for item in char::decode_utf16(v.iter().cloned()) {
            match item {
                Ok(ch) => string.push_char(ch),
                Err(surrogate) => {
                    // Surrogates are known to be in the code point range.
                    let code_point = unsafe { CodePoint::from_u32_unchecked(surrogate as u32) };
                    // Skip the WTF-8 concatenation check,
                    // surrogate pairs are already decoded by decode_utf16
                    string.push_code_point_unchecked(code_point)
                }
            }
        }
        string
    }

    /// Copied from String::push
    /// This does **not** include the WTF-8 concatenation check.
    fn push_code_point_unchecked(&mut self, code_point: CodePoint) {
        let cur_len = self.len();
        // This may use up to 4 bytes.
        self.reserve(4);

        unsafe {
            // Attempt to not use an intermediate buffer by just pushing bytes
            // directly onto this string.
            let slice = slice::from_raw_parts_mut(
                self.bytes.as_mut_ptr().offset(cur_len as isize), 4
            );
            let used = encode_utf8_raw(code_point.value, slice).unwrap();
            self.bytes.set_len(cur_len + used);
        }
    }

    #[inline]
    pub fn as_slice(&self) -> &Wtf8 {
        unsafe { Wtf8::from_bytes_unchecked(&self.bytes) }
    }

    /// Reserves capacity for at least `additional` more bytes to be inserted
    /// in the given `Wtf8Buf`.
    /// The collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.bytes.reserve(additional)
    }

    /// Reserves the minimum capacity for exactly `additional` more bytes to be
    /// inserted in the given `OsString`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore capacity can not be relied upon to be precisely
    /// minimal. Prefer reserve if future insertions are expected.
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.bytes.reserve_exact(additional)
    }

    /// Returns the number of bytes that this string buffer can hold without reallocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.bytes.capacity()
    }

    /// Append a UTF-8 slice at the end of the string.
    #[inline]
    pub fn push_str(&mut self, other: &str) {
        self.bytes.extend_from_slice(other.as_bytes())
    }

    /// Append a WTF-8 slice at the end of the string.
    ///
    /// This replaces newly paired surrogates at the boundary
    /// with a supplementary code point,
    /// like concatenating ill-formed UTF-16 strings effectively would.
    #[inline]
    pub fn push_wtf8(&mut self, other: &Wtf8) {
        match ((&*self).final_lead_surrogate(), other.initial_trail_surrogate()) {
            // Replace newly paired surrogates by a supplementary code point.
            (Some(lead), Some(trail)) => {
                let len_without_lead_surrogate = self.len() - 3;
                self.bytes.truncate(len_without_lead_surrogate);
                let other_without_trail_surrogate = &other.bytes[3..];
                // 4 bytes for the supplementary code point
                self.bytes.reserve(4 + other_without_trail_surrogate.len());
                self.push_char(decode_surrogate_pair(lead, trail));
                self.bytes.extend_from_slice(other_without_trail_surrogate);
            }
            _ => self.bytes.extend_from_slice(&other.bytes)
        }
    }

    /// Append a Unicode scalar value at the end of the string.
    #[inline]
    pub fn push_char(&mut self, c: char) {
        self.push_code_point_unchecked(CodePoint::from_char(c))
    }

    /// Append a code point at the end of the string.
    ///
    /// This replaces newly paired surrogates at the boundary
    /// with a supplementary code point,
    /// like concatenating ill-formed UTF-16 strings effectively would.
    #[inline]
    pub fn push(&mut self, code_point: CodePoint) {
        if let trail @ 0xDC00...0xDFFF = code_point.to_u32() {
            if let Some(lead) = (&*self).final_lead_surrogate() {
                let len_without_lead_surrogate = self.len() - 3;
                self.bytes.truncate(len_without_lead_surrogate);
                self.push_char(decode_surrogate_pair(lead, trail as u16));
                return
            }
        }

        // No newly paired surrogates at the boundary.
        self.push_code_point_unchecked(code_point)
    }

    /// Shortens a string to the specified length.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` > current length,
    /// or if `new_len` is not a code point boundary.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        assert!(is_code_point_boundary(self, new_len));
        self.bytes.truncate(new_len)
    }

    /// Empties the string.
    #[inline]
    pub fn clear(&mut self) {
        self.bytes.clear()
    }

    /// Consumes the WTF-8 string and tries to convert it to UTF-8.
    ///
    /// This does not copy the data.
    ///
    /// If the contents are not well-formed UTF-8
    /// (that is, if the string contains surrogates),
    /// the original WTF-8 string is returned instead.
    pub fn into_string(self) -> Result<String, Wtf8Buf> {
        match self.next_surrogate(0) {
            None => Ok(unsafe { String::from_utf8_unchecked(self.bytes) }),
            Some(_) => Err(self),
        }
    }

    /// Consumes the WTF-8 string and converts it lossily to UTF-8.
    ///
    /// This does not copy the data (but may overwrite parts of it in place).
    ///
    /// Surrogates are replaced with `"\u{FFFD}"` (the replacement character “�”)
    pub fn into_string_lossy(mut self) -> String {
        let mut pos = 0;
        loop {
            match self.next_surrogate(pos) {
                Some((surrogate_pos, _)) => {
                    pos = surrogate_pos + 3;
                    self.bytes[surrogate_pos .. pos]
                        .copy_from_slice(UTF8_REPLACEMENT_CHARACTER);
                },
                None => return unsafe { String::from_utf8_unchecked(self.bytes) }
            }
        }
    }
}

/// Create a new WTF-8 string from an iterator of code points.
///
/// This replaces surrogate code point pairs with supplementary code points,
/// like concatenating ill-formed UTF-16 strings effectively would.
impl FromIterator<CodePoint> for Wtf8Buf {
    fn from_iter<T: IntoIterator<Item=CodePoint>>(iter: T) -> Wtf8Buf {
        let mut string = Wtf8Buf::new();
        string.extend(iter);
        string
    }
}

/// Append code points from an iterator to the string.
///
/// This replaces surrogate code point pairs with supplementary code points,
/// like concatenating ill-formed UTF-16 strings effectively would.
impl Extend<CodePoint> for Wtf8Buf {
    fn extend<T: IntoIterator<Item=CodePoint>>(&mut self, iterable: T) {
        let iterator = iterable.into_iter();
        let (low, _high) = iterator.size_hint();
        // Lower bound of one byte per code point (ASCII only)
        self.bytes.reserve(low);
        for code_point in iterator {
            self.push(code_point);
        }
    }
}

/// A borrowed slice of well-formed WTF-8 data.
///
/// Similar to `&str`, but can additionally contain surrogate code points
/// if they’re not in a surrogate pair.
#[derive(Eq, Ord, PartialEq, PartialOrd)]
pub struct Wtf8 {
    bytes: [u8]
}

// impl AsInner<[u8]> for Wtf8 {
//     fn as_inner(&self) -> &[u8] { &self.bytes }
// }

/// Format the slice with double quotes,
/// and surrogates as `\u` followed by four hexadecimal digits.
/// Example: `"a\u{D800}"` for a slice with code points [U+0061, U+D800]
impl fmt::Debug for Wtf8 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        fn write_str_escaped(f: &mut fmt::Formatter, s: &str) -> fmt::Result {
            use std::fmt::Write;
            for c in s.chars().flat_map(|c| c.escape_default()) {
                try!(f.write_char(c))
            }
            Ok(())
        }

        try!(formatter.write_str("\""));
        let mut pos = 0;
        loop {
            match self.next_surrogate(pos) {
                None => break,
                Some((surrogate_pos, surrogate)) => {
                    try!(write_str_escaped(
                        formatter,
                        unsafe { str::from_utf8_unchecked(
                            &self.bytes[pos .. surrogate_pos]
                        )},
                    ));
                    try!(write!(formatter, "\\u{{{:X}}}", surrogate));
                    pos = surrogate_pos + 3;
                }
            }
        }
        try!(write_str_escaped(
            formatter,
            unsafe { str::from_utf8_unchecked(&self.bytes[pos..]) },
        ));
        formatter.write_str("\"")
    }
}

impl Wtf8 {
    /// Creates a WTF-8 slice from a UTF-8 `&str` slice.
    ///
    /// Since WTF-8 is a superset of UTF-8, this always succeeds.
    #[inline]
    pub fn from_str(value: &str) -> &Wtf8 {
        unsafe { Wtf8::from_bytes_unchecked(value.as_bytes()) }
    }

    /// Creates a WTF-8 slice from a WTF-8 byte slice.
    ///
    /// Since the byte slice is not checked for valid WTF-8, this functions is
    /// marked unsafe.
    #[inline]
    unsafe fn from_bytes_unchecked(value: &[u8]) -> &Wtf8 {
        mem::transmute(value)
    }

    /// Returns the length, in WTF-8 bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns true if the string contains no bytes.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Returns the code point at `position` if it is in the ASCII range,
    /// or `b'\xFF' otherwise.
    ///
    /// # Panics
    ///
    /// Panics if `position` is beyond the end of the string.
    #[inline]
    pub fn ascii_byte_at(&self, position: usize) -> u8 {
        match self.bytes[position] {
            ascii_byte @ 0x00 ... 0x7F => ascii_byte,
            _ => 0xFF
        }
    }

    /// Returns an iterator for the string’s code points.
    #[inline]
    pub fn code_points(&self) -> Wtf8CodePoints {
        Wtf8CodePoints { bytes: self.bytes.iter() }
    }

    /// Tries to convert the string to UTF-8 and return a `&str` slice.
    ///
    /// Returns `None` if the string contains surrogates.
    ///
    /// This does not copy the data.
    #[inline]
    pub fn as_str(&self) -> Option<&str> {
        // Well-formed WTF-8 is also well-formed UTF-8
        // if and only if it contains no surrogate.
        match self.next_surrogate(0) {
            None => Some(unsafe { str::from_utf8_unchecked(&self.bytes) }),
            Some(_) => None,
        }
    }

    /// Lossily converts the string to UTF-8.
    /// Returns a UTF-8 `&str` slice if the contents are well-formed in UTF-8.
    ///
    /// Surrogates are replaced with `"\u{FFFD}"` (the replacement character “�”).
    ///
    /// This only copies the data if necessary (if it contains any surrogate).
    pub fn to_string_lossy(&self) -> Cow<str> {
        let surrogate_pos = match self.next_surrogate(0) {
            None => return Cow::Borrowed(unsafe { str::from_utf8_unchecked(&self.bytes) }),
            Some((pos, _)) => pos,
        };
        let wtf8_bytes = &self.bytes;
        let mut utf8_bytes = Vec::with_capacity(self.len());
        utf8_bytes.extend_from_slice(&wtf8_bytes[..surrogate_pos]);
        utf8_bytes.extend_from_slice(UTF8_REPLACEMENT_CHARACTER);
        let mut pos = surrogate_pos + 3;
        loop {
            match self.next_surrogate(pos) {
                Some((surrogate_pos, _)) => {
                    utf8_bytes.extend_from_slice(&wtf8_bytes[pos .. surrogate_pos]);
                    utf8_bytes.extend_from_slice(UTF8_REPLACEMENT_CHARACTER);
                    pos = surrogate_pos + 3;
                },
                None => {
                    utf8_bytes.extend_from_slice(&wtf8_bytes[pos..]);
                    return Cow::Owned(unsafe { String::from_utf8_unchecked(utf8_bytes) })
                }
            }
        }
    }

    /// Converts the WTF-8 string to potentially ill-formed UTF-16
    /// and return an iterator of 16-bit code units.
    ///
    /// This is lossless:
    /// calling `Wtf8Buf::from_ill_formed_utf16` on the resulting code units
    /// would always return the original WTF-8 string.
    #[inline]
    pub fn encode_wide(&self) -> EncodeWide {
        EncodeWide { code_points: self.code_points(), extra: 0 }
    }

    /// Returns the first ill-formed UTF-16 digit in the string.
    fn first_wide(&self) -> Option<u16> {
        let first_code_point =
            match CodePoint::from_iterator(&mut self.bytes.iter()) {
                Some(cp) => cp,
                None => return None
            };

        match first_code_point.to_surrogates() {
            Some((s, _)) => Some(s),
            None => { Some(first_code_point.to_u32() as u16) }
        }
    }

    /// Returns the last ill-formed UTF-16 digit in the string.
    fn last_wide(&self) -> Option<u16> {
        let last_code_point =
            match CodePoint::from_iterator_reverse(&mut self.bytes.iter()) {
                Some(cp) => cp,
                None => return None
            };

        match last_code_point.to_surrogates() {
            Some((_, s)) => Some(s),
            None => { Some(last_code_point.to_u32() as u16) }
        }
    }

    /// Returns an iterator over the Unicode and non-Unicode sections
    /// of the string.  Sections will always be nonempty and types
    /// will always alternate.
    pub fn split_unicode<'a>(&'a self) -> SplitUnicode<'a> {
        SplitUnicode(utf8_sections::SplitUnicode::new(&self.bytes))
    }

    /// Returns true if the ill-formed UTF-16 data corresponding to
    /// `needle` is contained in the data corresponding to `self`.
    pub fn contains_wtf8(&self, needle: &Wtf8) -> bool {
        // Try the easy case first
        if SliceSearcher::new(&self.bytes, &needle.bytes, true).next().is_some() {
            return true;
        }

        // Split the needle into an optional trail surrogate, other
        // stuff, and an optional lead surrogate
        let start = needle.initial_trail_surrogate();
        let end = needle.final_lead_surrogate();
        if start.is_none() && end.is_none() { return false; }
        let middle = {
            let start_offset = if start.is_some() { 3 } else { 0 };
            let end_offset = if end.is_some() { 3 } else { 0 };
            &needle[start_offset..needle.len() - end_offset]
        };

        if middle.is_empty() {
            // We have no fixed bytes to match on.  We can't do
            // anything but an exhaustive search.
            match (start, end) {
                (Some(start), Some(end)) => {
                    let mut code_units = self.encode_wide().peekable();
                    while code_units.any(|c| c == start) {
                        if code_units.peek() == Some(&end) {
                            return true;
                        }
                    }
                    return false;
                }
                (Some(code_unit), None) | (None, Some(code_unit)) => {
                    return self.encode_wide().any(|c| c == code_unit);
                }
                (None, None) => unreachable!()
            }
        }

        let searcher = SliceSearcher::new(&self.bytes, &middle.bytes, true);
        for middle_start in searcher {
            let middle_end = middle_start + middle.len();
            if (start.is_none() || self[..middle_start].last_wide() == start) &&
               (end.is_none() || self[middle_end..].first_wide() == end) {
                return true;
            }
        }
        return false;
    }

    /// Returns true if the ill-formed UTF-16 data corresponding to
    /// `needle` is a prefix of the data corresponding to `self`.
    pub fn starts_with_wtf8(&self, needle: &Wtf8) -> bool {
        // Try the easy case first
        if self.bytes.starts_with(&needle.bytes) { return true; }

        // Now we have to check if we're matching half a character at
        // the end
        let surrogate = match needle.final_lead_surrogate() {
            Some(surrogate) => surrogate,
            None => return false
        };

        // Surrogates are always 3 bytes
        let start_len = needle.len() - 3;
        if !self.bytes.starts_with(&needle.bytes[..start_len]) { return false; }

        self[start_len..].first_wide() == Some(surrogate)
    }

    /// Returns true if the ill-formed UTF-16 data corresponding to
    /// `needle` is a suffix of the data corresponding to `self`.
    pub fn ends_with_wtf8(&self, needle: &Wtf8) -> bool {
        // Try the easy case first
        if self.bytes.ends_with(&needle.bytes) { return true; }

        // Now we have to check if we're matching half a character at
        // the begining
        let surrogate = match needle.initial_trail_surrogate() {
            Some(surrogate) => surrogate,
            None => return false
        };

        // Surrogates are always 3 bytes
        if !self.bytes.ends_with(&needle.bytes[3..]) { return false; }

        let rest_len = self.len() - (needle.len() - 3);
        self[..rest_len].last_wide() == Some(surrogate)
    }

    pub fn utf8_sections<'a>(&'a self) -> Utf8Sections<'a> {
        Utf8Sections::new(&self.bytes)
    }

    /// An iterator over substrings of `self` separated by characters
    /// matched by a pattern.  See `str::split` for details.
    ///
    /// Note that patterns can only match UTF-8 sections.
    pub fn split<'a, P>(&'a self, pat: P) -> Split<'a, P>
    where P: Pattern<'a> + Clone {
        Split { inner: split_bytes::Split::new(&self.bytes, pat) }
    }

    /// An iterator over substrings of `self` separated by characters
    /// matched by a pattern, in reverse order.  See `str::rsplit` for
    /// details.
    ///
    /// Note that patterns can only match UTF-8 sections.
    pub fn rsplit<'a, P>(&'a self, pat: P) -> RSplit<'a, P>
    where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
        RSplit { inner: split_bytes::RSplit::new(&self.bytes, pat) }
    }

    /// Equivalent to `split`, except the trailing substring is
    /// skipped if empty.  See `str::split_terminator` for details.
    ///
    /// Note that patterns can only match UTF-8 sections.
    pub fn split_terminator<'a, P>(&'a self, pat: P) -> SplitTerminator<'a, P>
    where P: Pattern<'a> + Clone {
        SplitTerminator { inner: split_bytes::SplitTerminator::new(&self.bytes, pat) }
    }

    /// Equivalent to `rsplit`, except the trailing substring is
    /// skipped if empty.  See `str::rsplit_terminator` for details.
    ///
    /// Note that patterns can only match UTF-8 sections.
    pub fn rsplit_terminator<'a, P>(&'a self, pat: P) -> RSplitTerminator<'a, P>
    where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
        RSplitTerminator { inner: split_bytes::RSplitTerminator::new(&self.bytes, pat) }
    }

    /// An iterator over substrings of `self` separated by characters
    /// matched by a pattern, restricted to returning at most `count`
    /// items.  See `str::splitn` for details.
    ///
    /// Note that patterns can only match UTF-8 sections.
    pub fn splitn<'a, P>(&'a self, count: usize, pat: P) -> SplitN<'a, P>
    where P: Pattern<'a> + Clone {
        SplitN { inner: split_bytes::SplitN::new(&self.bytes, count, pat) }
    }

    /// An iterator over substrings of `self` separated by characters
    /// matched by a pattern, in reverse order, restricted to returning
    /// at most `count` items.  See `str::rsplitn` for details.
    ///
    /// Note that patterns can only match UTF-8 sections.
    pub fn rsplitn<'a, P>(&'a self, count: usize, pat: P) -> RSplitN<'a, P>
    where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
        RSplitN { inner: split_bytes::RSplitN::new(&self.bytes, count, pat) }
    }

    /// An iterator over matches of a pattern in `self`.  See
    /// `str::matches` for details.
    ///
    /// Note that patterns can only match UTF-8 sections.
    pub fn matches<'a, P>(&'a self, pat: P) -> Matches<'a, P>
    where P: Pattern<'a> + Clone {
        Matches { inner: split_bytes::Matches::new(&self.bytes, pat) }
    }

    /// An iterator over matches of a pattern in `self`, in reverse
    /// order.  See `str::rmatches` for details.
    ///
    /// Note that patterns can only match UTF-8 sections.
    pub fn rmatches<'a, P>(&'a self, pat: P) -> RMatches<'a, P>
    where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
        RMatches { inner: split_bytes::RMatches::new(&self.bytes, pat) }
    }

    /// Returns a `&Wtf8` with leading and trailing matches of `pat`
    /// repeatedly removed.
    pub fn trim_matches<'a, P>(&'a self, pat: P) -> &'a Wtf8
    where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
        unsafe {
            Self::from_bytes_unchecked(split_bytes::trim_matches(&self.bytes, pat))
        }
    }

    /// Returns a `&Wtf8` with leading matches of `pat` repeatedly
    /// removed.
    pub fn trim_left_matches<'a, P>(&'a self, pat: P) -> &'a Wtf8
    where P: Pattern<'a> {
        unsafe {
            Self::from_bytes_unchecked(split_bytes::trim_left_matches(&self.bytes, pat))
        }
    }

    /// Returns a `&Wtf8` with trailing matches of `pat` repeatedly
    /// removed.
    pub fn trim_right_matches<'a, P>(&'a self, pat: P) -> &'a Wtf8
    where P: Pattern<'a>, P::Searcher: ReverseSearcher<'a> {
        unsafe {
            Self::from_bytes_unchecked(split_bytes::trim_right_matches(&self.bytes, pat))
        }
    }

    /// Replaces all occurrences of one string with another.
    // TODO: Benchmark this against just round-tripping through UTF-16
    // once I have a decent byte substring searcher.
    pub fn replace<T: AsRef<Wtf8>, U: AsRef<Wtf8>>(&self, from: T, to: U) -> Wtf8Buf {
        let from = from.as_ref();
        let to = to.as_ref();

        // Convert a 16-bit code unit to a CodePoint
        fn cu_to_cp(cu: u16) -> CodePoint {
            unsafe { CodePoint::from_u32_unchecked(cu as u32) }
        }
        // WTF-8 width of a code unit
        fn cu_width(cu: u16) -> usize {
            match char::decode_utf16(iter::once(cu)).next().unwrap() {
                Ok(c) => c.len_utf8(),
                Err(_) => 3, // Surrogates are always three bytes
            }
        }

        // Match only surrogates that could be part of non-BMP characters
        fn match_surrogates(source: &Wtf8,
                            surrogates: (Option<u16>, Option<u16>),
                            to: &Wtf8) -> Wtf8Buf {
            let code_units = source.encode_wide();
            match surrogates {
                (None, None) => {
                    // OK, from was just an empty string.
                    let mut result = Wtf8Buf::new();
                    result.push_wtf8(to);
                    for cu in code_units {
                        result.push(cu_to_cp(cu));
                        result.push_wtf8(to);
                    }
                    return result;
                }
                (Some(from_cu), None) | (None, Some(from_cu)) => {
                    // One code unit
                    let mut result = Wtf8Buf::new();
                    for cu in code_units {
                        if cu == from_cu {
                            result.push_wtf8(to);
                        } else {
                            result.push(cu_to_cp(cu));
                        }
                    }
                    return result;
                }
                (Some(trail), Some(lead)) => {
                    let mut code_units = code_units.peekable();
                    let mut result = Wtf8Buf::new();
                    while let Some(cu) = code_units.next() {
                        if cu == trail && code_units.peek() == Some(&lead) {
                            result.push_wtf8(to);
                            code_units.next();
                        } else {
                            result.push(cu_to_cp(cu));
                        }
                    }
                    return result;
                }
            }
        }

        // Match a fixed string that must occur exactly in the WTF-8
        // representation, and possibly some surrogates on the ends
        fn match_fixed(mut source: &Wtf8,
                       middle: &Wtf8, (start, end): (Option<u16>, Option<u16>),
                       to: &Wtf8) -> Wtf8Buf {
            // Search for the fixed middle string, and check if the
            // ends agree for each match.

            // Ways surrogates can match (or not)
            #[derive(PartialEq)]
            enum MatchType {
                None, // doesn't match
                Empty, // matches because it's an empty string
                Cp, // matches a code point in the WTF-8 string
                // matches a surrogate obtained by splitting a char
                // (contains the paired surrogate)
                Split(u16),
                // matches a surrogate obtained by splitting a char on
                // the previous match
                Leftover,
            }

            let mut result = Wtf8Buf::new();
            // Any extra trail surrogate at the beginning of our
            // source resulting from splitting a non-BMP character.
            let mut extra_surrogate = None;
            'next_match: loop {
                let mut search = SliceSearcher::new(&source.bytes, &middle.bytes, true);
                while let Some(index) = search.next() {
                    let start_match = match start {
                        None => MatchType::Empty,
                        Some(start) => {
                            if index == 0 {
                                if Some(start) == extra_surrogate {
                                    MatchType::Leftover
                                } else {
                                    MatchType::None
                                }
                            } else {
                                // The last code point before our match
                                let last_cp =
                                    CodePoint::from_iterator_reverse(
                                        &mut (&source.bytes[..index]).iter())
                                    .unwrap();
                                if cu_to_cp(start) == last_cp {
                                    MatchType::Cp
                                } else {
                                    match last_cp.to_surrogates() {
                                        Some((lead, trail)) if trail == start
                                            => MatchType::Split(lead),
                                        _ => MatchType::None,
                                    }
                                }
                            }
                        }
                    };
                    if start_match == MatchType::None { continue; }

                    let end_match = match end {
                        None => MatchType::Empty,
                        Some(end) => match CodePoint::from_iterator(
                            &mut (&source.bytes[index + middle.len()..]).iter()) {
                            None => MatchType::None,
                            Some(next_cp) => {
                                if cu_to_cp(end) == next_cp {
                                    MatchType::Cp
                                } else {
                                    match next_cp.to_surrogates() {
                                        Some((lead, trail)) if lead == end
                                            => MatchType::Split(trail),
                                        _ => MatchType::None,
                                    }
                                }
                            }
                        }
                    };
                    if end_match == MatchType::None { continue; }

                    // We have an actual match!

                    // Add any leading non-matching stuff
                    if start_match != MatchType::Leftover {
                        if let Some(surrogate) = extra_surrogate {
                            result.push(cu_to_cp(surrogate));
                        }
                        match start_match {
                            MatchType::Empty => {
                                result.push_wtf8(&source[..index]);
                            }
                            MatchType::Cp => {
                                let width = cu_width(start.unwrap());
                                result.push_wtf8(&source[..index - width]);
                            }
                            MatchType::Split(lead) => {
                                // Non-BMP characters are always four bytes
                                result.push_wtf8(&source[..index - 4]);
                                result.push(cu_to_cp(lead));
                            }
                            MatchType::Leftover | MatchType::None => unreachable!()
                        }
                    }

                    // Add the replacement
                    result.push_wtf8(to);

                    // Start over with a new source
                    match end_match {
                        MatchType::Empty => {
                            source = &source[index + middle.len()..];
                            extra_surrogate = None;
                        }
                        MatchType::Cp => {
                            let width = cu_width(end.unwrap());
                            source = &source[index + middle.len() + width..];
                            extra_surrogate = None;
                        }
                        MatchType::Split(trail) => {
                            // Non-BMP characters are always four bytes
                            source = &source[index + middle.len() + 4..];
                            extra_surrogate = Some(trail);
                        }
                        MatchType::Leftover | MatchType::None => unreachable!()
                    }
                    continue 'next_match;
                }

                // No more matches
                break;
            }

            // Add any extra stuff at the end
            if let Some(surrogate) = extra_surrogate {
                result.push(cu_to_cp(surrogate));
            }
            result.push_wtf8(source);
            result
        }

        // Split from into an optional trail surrogate, other
        // stuff, and an optional lead surrogate
        let start = from.initial_trail_surrogate();
        let end = from.final_lead_surrogate();
        let middle = {
            // Surrogates are always three bytes
            let start_offset = if start.is_some() { 3 } else { 0 };
            let end_offset = if end.is_some() { 3 } else { 0 };
            &from[start_offset..from.len() - end_offset]
        };

        if middle.is_empty() {
            match_surrogates(self, (start, end), to)
        } else {
            match_fixed(self, middle, (start, end), to)
        }
    }

    #[inline]
    fn next_surrogate(&self, mut pos: usize) -> Option<(usize, u16)> {
        let mut iter = self.bytes[pos..].iter();
        loop {
            let b = match iter.next() {
                None => return None,
                Some(&b) => b,
            };
            if b < 0x80 {
                pos += 1;
            } else if b < 0xE0 {
                iter.next();
                pos += 2;
            } else if b == 0xED {
                match (iter.next(), iter.next()) {
                    (Some(&b2), Some(&b3)) if b2 >= 0xA0 => {
                        return Some((pos, decode_surrogate(b2, b3)))
                    }
                    _ => pos += 3
                }
            } else if b < 0xF0 {
                iter.next();
                iter.next();
                pos += 3;
            } else {
                iter.next();
                iter.next();
                iter.next();
                pos += 4;
            }
        }
    }

    #[inline]
    fn final_lead_surrogate(&self) -> Option<u16> {
        let len = self.len();
        if len < 3 {
            return None
        }
        match &self.bytes[(len - 3)..] {
            [0xED, b2 @ 0xA0...0xAF, b3] => Some(decode_surrogate(b2, b3)),
            _ => None
        }
    }

    #[inline]
    fn initial_trail_surrogate(&self) -> Option<u16> {
        let len = self.len();
        if len < 3 {
            return None
        }
        match &self.bytes[..3] {
            [0xED, b2 @ 0xB0...0xBF, b3] => Some(decode_surrogate(b2, b3)),
            _ => None
        }
    }
}


/// Return a slice of the given string for the byte range [`begin`..`end`).
///
/// # Panics
///
/// Panics when `begin` and `end` do not point to code point boundaries,
/// or point beyond the end of the string.
impl ops::Index<ops::Range<usize>> for Wtf8 {
    type Output = Wtf8;

    #[inline]
    fn index(&self, range: ops::Range<usize>) -> &Wtf8 {
        // is_code_point_boundary checks that the index is in [0, .len()]
        if range.start <= range.end &&
           is_code_point_boundary(self, range.start) &&
           is_code_point_boundary(self, range.end) {
            unsafe { slice_unchecked(self, range.start, range.end) }
        } else {
            slice_error_fail(self, range.start, range.end)
        }
    }
}

/// Return a slice of the given string from byte `begin` to its end.
///
/// # Panics
///
/// Panics when `begin` is not at a code point boundary,
/// or is beyond the end of the string.
impl ops::Index<ops::RangeFrom<usize>> for Wtf8 {
    type Output = Wtf8;

    #[inline]
    fn index(&self, range: ops::RangeFrom<usize>) -> &Wtf8 {
        // is_code_point_boundary checks that the index is in [0, .len()]
        if is_code_point_boundary(self, range.start) {
            unsafe { slice_unchecked(self, range.start, self.len()) }
        } else {
            slice_error_fail(self, range.start, self.len())
        }
    }
}

/// Return a slice of the given string from its beginning to byte `end`.
///
/// # Panics
///
/// Panics when `end` is not at a code point boundary,
/// or is beyond the end of the string.
impl ops::Index<ops::RangeTo<usize>> for Wtf8 {
    type Output = Wtf8;

    #[inline]
    fn index(&self, range: ops::RangeTo<usize>) -> &Wtf8 {
        // is_code_point_boundary checks that the index is in [0, .len()]
        if is_code_point_boundary(self, range.end) {
            unsafe { slice_unchecked(self, 0, range.end) }
        } else {
            slice_error_fail(self, 0, range.end)
        }
    }
}

impl ops::Index<ops::RangeFull> for Wtf8 {
    type Output = Wtf8;

    #[inline]
    fn index(&self, _range: ops::RangeFull) -> &Wtf8 {
        self
    }
}

#[inline]
fn decode_surrogate(second_byte: u8, third_byte: u8) -> u16 {
    // The first byte is assumed to be 0xED
    0xD800 | (second_byte as u16 & 0x3F) << 6 | third_byte as u16 & 0x3F
}

#[inline]
fn decode_surrogate_pair(lead: u16, trail: u16) -> char {
    let code_point = 0x10000 + ((((lead - 0xD800) as u32) << 10) | (trail - 0xDC00) as u32);
    unsafe { char::from_u32_unchecked(code_point) }
}

/// Copied from core::str::StrPrelude::is_char_boundary
#[inline]
pub fn is_code_point_boundary(slice: &Wtf8, index: usize) -> bool {
    if index == slice.len() { return true; }
    match slice.bytes.get(index) {
        None => false,
        Some(&b) => b < 128 || b >= 192,
    }
}

/// Copied from core::str::raw::slice_unchecked
#[inline]
pub unsafe fn slice_unchecked(s: &Wtf8, begin: usize, end: usize) -> &Wtf8 {
    // memory layout of an &[u8] and &Wtf8 are the same
    Wtf8::from_bytes_unchecked(slice::from_raw_parts(
        s.bytes.as_ptr().offset(begin as isize),
        end - begin
    ))
}

/// Copied from core::str::raw::slice_error_fail
#[inline(never)]
pub fn slice_error_fail(s: &Wtf8, begin: usize, end: usize) -> ! {
    assert!(begin <= end);
    panic!("index {} and/or {} in `{:?}` do not lie on character boundary",
          begin, end, s);
}

/// Iterator for the code points of a WTF-8 string.
///
/// Created with the method `.code_points()`.
#[derive(Clone)]
pub struct Wtf8CodePoints<'a> {
    bytes: slice::Iter<'a, u8>
}

impl<'a> Iterator for Wtf8CodePoints<'a> {
    type Item = CodePoint;

    #[inline]
    fn next(&mut self) -> Option<CodePoint> {
        CodePoint::from_iterator(&mut self.bytes)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (len, _) = self.bytes.size_hint();
        (len.saturating_add(3) / 4, Some(len))
    }
}

#[derive(Clone)]
pub struct EncodeWide<'a> {
    code_points: Wtf8CodePoints<'a>,
    extra: u16
}

// Copied from libunicode/u_str.rs
impl<'a> Iterator for EncodeWide<'a> {
    type Item = u16;

    #[inline]
    fn next(&mut self) -> Option<u16> {
        if self.extra != 0 {
            let tmp = self.extra;
            self.extra = 0;
            return Some(tmp);
        }

        let mut buf = [0; 2];
        self.code_points.next().map(|code_point| {
            let n = encode_utf16_raw(code_point.value, &mut buf)
                .unwrap_or(0);
            if n == 2 { self.extra = buf[1]; }
            buf[0]
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (low, high) = self.code_points.size_hint();
        // every code point gets either one u16 or two u16,
        // so this iterator is between 1 or 2 times as
        // long as the underlying iterator.
        (low, high.and_then(|n| n.checked_mul(2)))
    }
}

impl Hash for CodePoint {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl Hash for Wtf8Buf {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write(&self.bytes);
        0xfeu8.hash(state)
    }
}

impl Hash for Wtf8 {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write(&self.bytes);
        0xfeu8.hash(state)
    }
}

impl AsciiExt for Wtf8 {
    type Owned = Wtf8Buf;

    fn is_ascii(&self) -> bool {
        self.bytes.is_ascii()
    }
    fn to_ascii_uppercase(&self) -> Wtf8Buf {
        Wtf8Buf { bytes: self.bytes.to_ascii_uppercase() }
    }
    fn to_ascii_lowercase(&self) -> Wtf8Buf {
        Wtf8Buf { bytes: self.bytes.to_ascii_lowercase() }
    }
    fn eq_ignore_ascii_case(&self, other: &Wtf8) -> bool {
        self.bytes.eq_ignore_ascii_case(&other.bytes)
    }

    fn make_ascii_uppercase(&mut self) { self.bytes.make_ascii_uppercase() }
    fn make_ascii_lowercase(&mut self) { self.bytes.make_ascii_lowercase() }
}


macro_rules! make_iterator {
    ($name:ident requires $bound:ident yielding $map:expr => $ret:ty) => {
        pub struct $name<'a, P> where P: Pattern<'a> {
            inner: split_bytes::$name<'a, P>,
        }

        impl<'a, P> Clone for $name<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: Clone {
            fn clone(&self) -> Self { $name { inner: self.inner.clone() } }
        }

        impl<'a, P> Iterator for $name<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: $bound<'a> {
            type Item = $ret;

            fn next(&mut self) -> Option<$ret> {
                self.inner.next().map($map)
            }
        }
    };
    ($name:ident requires $bound:ident is double ended yielding $map:expr => $ret:ty) => {
        make_iterator!{$name requires $bound yielding $map => $ret}

        impl<'a, P> DoubleEndedIterator for $name<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
            fn next_back(&mut self) -> Option<$ret> {
                self.inner.next_back().map($map)
            }
        }
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Section<'a> {
    Unicode(&'a str),
    NonUnicode(&'a Wtf8),
}

impl<'a> From<utf8_sections::Section<'a>> for Section<'a> {
    fn from<'b>(x: utf8_sections::Section<'a>) -> Section<'a> {
        match x {
            utf8_sections::Section::Unicode(s) => Section::Unicode(s),
            utf8_sections::Section::NonUnicode(s) =>
                unsafe { Section::NonUnicode(Wtf8::from_bytes_unchecked(s)) },
        }
    }
}

#[derive(Clone)]
pub struct SplitUnicode<'a>(utf8_sections::SplitUnicode<'a>);

impl<'a> Iterator for SplitUnicode<'a> {
    type Item = Section<'a>;
    fn next(&mut self) -> Option<Section<'a>> {
        self.0.next().map(|x| x.into())
    }
}

impl<'a> DoubleEndedIterator for SplitUnicode<'a> {
    fn next_back(&mut self) -> Option<Section<'a>> {
        self.0.next_back().map(|x| x.into())
    }
}


make_iterator!{Split requires Searcher is double ended
               yielding |s| unsafe { Wtf8::from_bytes_unchecked(s) } => &'a Wtf8}
make_iterator!{RSplit requires ReverseSearcher is double ended
               yielding |s| unsafe { Wtf8::from_bytes_unchecked(s) } => &'a Wtf8}
make_iterator!{SplitTerminator requires Searcher is double ended
               yielding |s| unsafe { Wtf8::from_bytes_unchecked(s) } => &'a Wtf8}
make_iterator!{RSplitTerminator requires ReverseSearcher is double ended
               yielding |s| unsafe { Wtf8::from_bytes_unchecked(s) } => &'a Wtf8}
make_iterator!{SplitN requires Searcher
               yielding |s| unsafe { Wtf8::from_bytes_unchecked(s) } => &'a Wtf8}
make_iterator!{RSplitN requires ReverseSearcher
               yielding |s| unsafe { Wtf8::from_bytes_unchecked(s) } => &'a Wtf8}
make_iterator!{Matches requires Searcher is double ended yielding |x| x => &'a str}
make_iterator!{RMatches requires ReverseSearcher is double ended yielding |x| x => &'a str}


#[cfg(test)]
mod tests {
    use std::prelude::v1::*;
    use std::borrow::Cow;
    use super::*;

    #[test]
    fn code_point_from_u32() {
        assert!(CodePoint::from_u32(0).is_some());
        assert!(CodePoint::from_u32(0xD800).is_some());
        assert!(CodePoint::from_u32(0x10FFFF).is_some());
        assert!(CodePoint::from_u32(0x110000).is_none());
    }

    #[test]
    fn code_point_to_u32() {
        fn c(value: u32) -> CodePoint { CodePoint::from_u32(value).unwrap() }
        assert_eq!(c(0).to_u32(), 0);
        assert_eq!(c(0xD800).to_u32(), 0xD800);
        assert_eq!(c(0x10FFFF).to_u32(), 0x10FFFF);
    }

    #[test]
    fn code_point_from_char() {
        assert_eq!(CodePoint::from_char('a').to_u32(), 0x61);
        assert_eq!(CodePoint::from_char('💩').to_u32(), 0x1F4A9);
    }

    #[test]
    fn code_point_to_string() {
        assert_eq!(format!("{:?}", CodePoint::from_char('a')), "U+0061");
        assert_eq!(format!("{:?}", CodePoint::from_char('💩')), "U+1F4A9");
    }

    #[test]
    fn code_point_to_char() {
        fn c(value: u32) -> CodePoint { CodePoint::from_u32(value).unwrap() }
        assert_eq!(c(0x61).to_char(), Some('a'));
        assert_eq!(c(0x1F4A9).to_char(), Some('💩'));
        assert_eq!(c(0xD800).to_char(), None);
    }

    #[test]
    fn code_point_to_char_lossy() {
        fn c(value: u32) -> CodePoint { CodePoint::from_u32(value).unwrap() }
        assert_eq!(c(0x61).to_char_lossy(), 'a');
        assert_eq!(c(0x1F4A9).to_char_lossy(), '💩');
        assert_eq!(c(0xD800).to_char_lossy(), '\u{FFFD}');
    }

    #[test]
    fn code_point_from_iterator() {
        fn c(value: u32) -> CodePoint { CodePoint::from_u32(value).unwrap() }
        assert_eq!(CodePoint::from_iterator(&mut [].iter()), None);
        assert_eq!(CodePoint::from_iterator(&mut [0x20, 0x40].iter()),
                   Some(c(0x20)));
        assert_eq!(CodePoint::from_iterator(&mut [0xC2, 0xA2, 0x40].iter()),
                   Some(c(0xA2)));
        assert_eq!(CodePoint::from_iterator(&mut [0xED, 0xA0, 0xBD, 0x40].iter()),
                   Some(c(0xD83D)));
        assert_eq!(CodePoint::from_iterator(&mut [0xF0, 0x9F, 0x98, 0xBA].iter()),
                   Some(c(0x1F63A)));
    }

    #[test]
    fn code_point_from_iterator_reverse() {
        fn c(value: u32) -> CodePoint { CodePoint::from_u32(value).unwrap() }
        assert_eq!(CodePoint::from_iterator_reverse(&mut [].iter()), None);
        assert_eq!(CodePoint::from_iterator_reverse(&mut [0x40, 0x20].iter()),
                   Some(c(0x20)));
        assert_eq!(CodePoint::from_iterator_reverse(&mut [0x40, 0xC2, 0xA2].iter()),
                   Some(c(0xA2)));
        assert_eq!(CodePoint::from_iterator_reverse(&mut [0x40, 0xED, 0xA0, 0xBD].iter()),
                   Some(c(0xD83D)));
        assert_eq!(CodePoint::from_iterator_reverse(&mut [0xF0, 0x9F, 0x98, 0xBA].iter()),
                   Some(c(0x1F63A)));
    }

    #[test]
    fn code_point_to_surrogates() {
        fn c(value: u32) -> CodePoint { CodePoint::from_u32(value).unwrap() }
        assert_eq!(c(0x20).to_surrogates(), None);
        assert_eq!(c(0xD83D).to_surrogates(), None);
        assert_eq!(c(0x1F63A).to_surrogates(), Some((0xD83D, 0xDE3A)));
    }

    #[test]
    fn wtf8buf_new() {
        assert_eq!(Wtf8Buf::new().bytes, b"");
    }

    #[test]
    fn wtf8buf_from_str() {
        assert_eq!(Wtf8Buf::from_str("").bytes, b"");
        assert_eq!(Wtf8Buf::from_str("aé 💩").bytes,
                   b"a\xC3\xA9 \xF0\x9F\x92\xA9");
    }

    #[test]
    fn wtf8buf_from_string() {
        assert_eq!(Wtf8Buf::from_string(String::from("")).bytes, b"");
        assert_eq!(Wtf8Buf::from_string(String::from("aé 💩")).bytes,
                   b"a\xC3\xA9 \xF0\x9F\x92\xA9");
    }

    #[test]
    fn wtf8buf_from_wide() {
        assert_eq!(Wtf8Buf::from_wide(&[]).bytes, b"");
        assert_eq!(Wtf8Buf::from_wide(
                      &[0x61, 0xE9, 0x20, 0xD83D, 0xD83D, 0xDCA9]).bytes,
                   b"a\xC3\xA9 \xED\xA0\xBD\xF0\x9F\x92\xA9");
    }

    #[test]
    fn wtf8buf_push_str() {
        let mut string = Wtf8Buf::new();
        assert_eq!(string.bytes, b"");
        string.push_str("aé 💩");
        assert_eq!(string.bytes, b"a\xC3\xA9 \xF0\x9F\x92\xA9");
    }

    #[test]
    fn wtf8buf_push_char() {
        let mut string = Wtf8Buf::from_str("aé ");
        assert_eq!(string.bytes, b"a\xC3\xA9 ");
        string.push_char('💩');
        assert_eq!(string.bytes, b"a\xC3\xA9 \xF0\x9F\x92\xA9");
    }

    #[test]
    fn wtf8buf_push() {
        let mut string = Wtf8Buf::from_str("aé ");
        assert_eq!(string.bytes, b"a\xC3\xA9 ");
        string.push(CodePoint::from_char('💩'));
        assert_eq!(string.bytes, b"a\xC3\xA9 \xF0\x9F\x92\xA9");

        fn c(value: u32) -> CodePoint { CodePoint::from_u32(value).unwrap() }

        let mut string = Wtf8Buf::new();
        string.push(c(0xD83D));  // lead
        string.push(c(0xDCA9));  // trail
        assert_eq!(string.bytes, b"\xF0\x9F\x92\xA9");  // Magic!

        let mut string = Wtf8Buf::new();
        string.push(c(0xD83D));  // lead
        string.push(c(0x20));  // not surrogate
        string.push(c(0xDCA9));  // trail
        assert_eq!(string.bytes, b"\xED\xA0\xBD \xED\xB2\xA9");

        let mut string = Wtf8Buf::new();
        string.push(c(0xD800));  // lead
        string.push(c(0xDBFF));  // lead
        assert_eq!(string.bytes, b"\xED\xA0\x80\xED\xAF\xBF");

        let mut string = Wtf8Buf::new();
        string.push(c(0xD800));  // lead
        string.push(c(0xE000));  // not surrogate
        assert_eq!(string.bytes, b"\xED\xA0\x80\xEE\x80\x80");

        let mut string = Wtf8Buf::new();
        string.push(c(0xD7FF));  // not surrogate
        string.push(c(0xDC00));  // trail
        assert_eq!(string.bytes, b"\xED\x9F\xBF\xED\xB0\x80");

        let mut string = Wtf8Buf::new();
        string.push(c(0x61));  // not surrogate, < 3 bytes
        string.push(c(0xDC00));  // trail
        assert_eq!(string.bytes, b"\x61\xED\xB0\x80");

        let mut string = Wtf8Buf::new();
        string.push(c(0xDC00));  // trail
        assert_eq!(string.bytes, b"\xED\xB0\x80");
    }

    #[test]
    fn wtf8buf_push_wtf8() {
        let mut string = Wtf8Buf::from_str("aé");
        assert_eq!(string.bytes, b"a\xC3\xA9");
        string.push_wtf8(Wtf8::from_str(" 💩"));
        assert_eq!(string.bytes, b"a\xC3\xA9 \xF0\x9F\x92\xA9");

        fn w(v: &[u8]) -> &Wtf8 { unsafe { Wtf8::from_bytes_unchecked(v) } }

        let mut string = Wtf8Buf::new();
        string.push_wtf8(w(b"\xED\xA0\xBD"));  // lead
        string.push_wtf8(w(b"\xED\xB2\xA9"));  // trail
        assert_eq!(string.bytes, b"\xF0\x9F\x92\xA9");  // Magic!

        let mut string = Wtf8Buf::new();
        string.push_wtf8(w(b"\xED\xA0\xBD"));  // lead
        string.push_wtf8(w(b" "));  // not surrogate
        string.push_wtf8(w(b"\xED\xB2\xA9"));  // trail
        assert_eq!(string.bytes, b"\xED\xA0\xBD \xED\xB2\xA9");

        let mut string = Wtf8Buf::new();
        string.push_wtf8(w(b"\xED\xA0\x80"));  // lead
        string.push_wtf8(w(b"\xED\xAF\xBF"));  // lead
        assert_eq!(string.bytes, b"\xED\xA0\x80\xED\xAF\xBF");

        let mut string = Wtf8Buf::new();
        string.push_wtf8(w(b"\xED\xA0\x80"));  // lead
        string.push_wtf8(w(b"\xEE\x80\x80"));  // not surrogate
        assert_eq!(string.bytes, b"\xED\xA0\x80\xEE\x80\x80");

        let mut string = Wtf8Buf::new();
        string.push_wtf8(w(b"\xED\x9F\xBF"));  // not surrogate
        string.push_wtf8(w(b"\xED\xB0\x80"));  // trail
        assert_eq!(string.bytes, b"\xED\x9F\xBF\xED\xB0\x80");

        let mut string = Wtf8Buf::new();
        string.push_wtf8(w(b"a"));  // not surrogate, < 3 bytes
        string.push_wtf8(w(b"\xED\xB0\x80"));  // trail
        assert_eq!(string.bytes, b"\x61\xED\xB0\x80");

        let mut string = Wtf8Buf::new();
        string.push_wtf8(w(b"\xED\xB0\x80"));  // trail
        assert_eq!(string.bytes, b"\xED\xB0\x80");
    }

    #[test]
    fn wtf8buf_truncate() {
        let mut string = Wtf8Buf::from_str("aé");
        string.truncate(1);
        assert_eq!(string.bytes, b"a");
    }

    #[test]
    #[should_panic]
    fn wtf8buf_truncate_fail_code_point_boundary() {
        let mut string = Wtf8Buf::from_str("aé");
        string.truncate(2);
    }

    #[test]
    #[should_panic]
    fn wtf8buf_truncate_fail_longer() {
        let mut string = Wtf8Buf::from_str("aé");
        string.truncate(4);
    }

    #[test]
    fn wtf8buf_clear() {
        let mut string = Wtf8Buf::from_str("aé");
        string.clear();
        assert!(string.is_empty());
    }

    #[test]
    fn wtf8buf_into_string() {
        let mut string = Wtf8Buf::from_str("aé 💩");
        assert_eq!(string.clone().into_string(), Ok(String::from("aé 💩")));
        string.push(CodePoint::from_u32(0xD800).unwrap());
        assert_eq!(string.clone().into_string(), Err(string));
    }

    #[test]
    fn wtf8buf_into_string_lossy() {
        let mut string = Wtf8Buf::from_str("aé 💩");
        assert_eq!(string.clone().into_string_lossy(), String::from("aé 💩"));
        string.push(CodePoint::from_u32(0xD800).unwrap());
        assert_eq!(string.clone().into_string_lossy(), String::from("aé 💩�"));
    }

    #[test]
    fn wtf8buf_from_iterator() {
        fn f(values: &[u32]) -> Wtf8Buf {
            values.iter().map(|&c| CodePoint::from_u32(c).unwrap()).collect::<Wtf8Buf>()
        };
        assert_eq!(f(&[0x61, 0xE9, 0x20, 0x1F4A9]).bytes, b"a\xC3\xA9 \xF0\x9F\x92\xA9");

        assert_eq!(f(&[0xD83D, 0xDCA9]).bytes, b"\xF0\x9F\x92\xA9");  // Magic!
        assert_eq!(f(&[0xD83D, 0x20, 0xDCA9]).bytes, b"\xED\xA0\xBD \xED\xB2\xA9");
        assert_eq!(f(&[0xD800, 0xDBFF]).bytes, b"\xED\xA0\x80\xED\xAF\xBF");
        assert_eq!(f(&[0xD800, 0xE000]).bytes, b"\xED\xA0\x80\xEE\x80\x80");
        assert_eq!(f(&[0xD7FF, 0xDC00]).bytes, b"\xED\x9F\xBF\xED\xB0\x80");
        assert_eq!(f(&[0x61, 0xDC00]).bytes, b"\x61\xED\xB0\x80");
        assert_eq!(f(&[0xDC00]).bytes, b"\xED\xB0\x80");
    }

    #[test]
    fn wtf8buf_extend() {
        fn e(initial: &[u32], extended: &[u32]) -> Wtf8Buf {
            fn c(value: &u32) -> CodePoint { CodePoint::from_u32(*value).unwrap() }
            let mut string = initial.iter().map(c).collect::<Wtf8Buf>();
            string.extend(extended.iter().map(c));
            string
        };

        assert_eq!(e(&[0x61, 0xE9], &[0x20, 0x1F4A9]).bytes,
                   b"a\xC3\xA9 \xF0\x9F\x92\xA9");

        assert_eq!(e(&[0xD83D], &[0xDCA9]).bytes, b"\xF0\x9F\x92\xA9");  // Magic!
        assert_eq!(e(&[0xD83D, 0x20], &[0xDCA9]).bytes, b"\xED\xA0\xBD \xED\xB2\xA9");
        assert_eq!(e(&[0xD800], &[0xDBFF]).bytes, b"\xED\xA0\x80\xED\xAF\xBF");
        assert_eq!(e(&[0xD800], &[0xE000]).bytes, b"\xED\xA0\x80\xEE\x80\x80");
        assert_eq!(e(&[0xD7FF], &[0xDC00]).bytes, b"\xED\x9F\xBF\xED\xB0\x80");
        assert_eq!(e(&[0x61], &[0xDC00]).bytes, b"\x61\xED\xB0\x80");
        assert_eq!(e(&[], &[0xDC00]).bytes, b"\xED\xB0\x80");
    }

    #[test]
    fn wtf8buf_show() {
        let mut string = Wtf8Buf::from_str("a\té 💩\r");
        string.push(CodePoint::from_u32(0xD800).unwrap());
        assert_eq!(format!("{:?}", string), r#""a\t\u{e9} \u{1f4a9}\r\u{D800}""#);
    }

    #[test]
    fn wtf8buf_as_slice() {
        assert_eq!(Wtf8Buf::from_str("aé").as_slice(), Wtf8::from_str("aé"));
    }

    #[test]
    fn wtf8buf_show_str() {
        let text = "a\té 💩\r";
        let string = Wtf8Buf::from_str(text);
        assert_eq!(format!("{:?}", text), format!("{:?}", string));
    }

    #[test]
    fn wtf8_from_str() {
        assert_eq!(&Wtf8::from_str("").bytes, b"");
        assert_eq!(&Wtf8::from_str("aé 💩").bytes, b"a\xC3\xA9 \xF0\x9F\x92\xA9");
    }

    #[test]
    fn wtf8_len() {
        assert_eq!(Wtf8::from_str("").len(), 0);
        assert_eq!(Wtf8::from_str("aé 💩").len(), 8);
    }

    #[test]
    fn wtf8_is_empty() {
        assert!(Wtf8::from_str("").is_empty());
        assert!(!Wtf8::from_str("💩").is_empty());
    }

    #[test]
    fn wtf8_slice() {
        assert_eq!(&Wtf8::from_str("aé 💩")[1.. 4].bytes, b"\xC3\xA9 ");
    }

    #[test]
    #[should_panic]
    fn wtf8_slice_not_code_point_boundary() {
        &Wtf8::from_str("aé 💩")[2.. 4];
    }

    #[test]
    fn wtf8_slice_from() {
        assert_eq!(&Wtf8::from_str("aé 💩")[1..].bytes, b"\xC3\xA9 \xF0\x9F\x92\xA9");
    }

    #[test]
    #[should_panic]
    fn wtf8_slice_from_not_code_point_boundary() {
        &Wtf8::from_str("aé 💩")[2..];
    }

    #[test]
    fn wtf8_slice_to() {
        assert_eq!(&Wtf8::from_str("aé 💩")[..4].bytes, b"a\xC3\xA9 ");
    }

    #[test]
    #[should_panic]
    fn wtf8_slice_to_not_code_point_boundary() {
        &Wtf8::from_str("aé 💩")[5..];
    }

    #[test]
    fn wtf8_ascii_byte_at() {
        let slice = Wtf8::from_str("aé 💩");
        assert_eq!(slice.ascii_byte_at(0), b'a');
        assert_eq!(slice.ascii_byte_at(1), b'\xFF');
        assert_eq!(slice.ascii_byte_at(2), b'\xFF');
        assert_eq!(slice.ascii_byte_at(3), b' ');
        assert_eq!(slice.ascii_byte_at(4), b'\xFF');
    }

    #[test]
    fn wtf8_code_points() {
        fn c(value: u32) -> CodePoint { CodePoint::from_u32(value).unwrap() }
        fn cp(string: &Wtf8Buf) -> Vec<Option<char>> {
            string.code_points().map(|c| c.to_char()).collect::<Vec<_>>()
        }
        let mut string = Wtf8Buf::from_str("é ");
        assert_eq!(cp(&string), [Some('é'), Some(' ')]);
        string.push(c(0xD83D));
        assert_eq!(cp(&string), [Some('é'), Some(' '), None]);
        string.push(c(0xDCA9));
        assert_eq!(cp(&string), [Some('é'), Some(' '), Some('💩')]);
    }

    #[test]
    fn wtf8_as_str() {
        assert_eq!(Wtf8::from_str("").as_str(), Some(""));
        assert_eq!(Wtf8::from_str("aé 💩").as_str(), Some("aé 💩"));
        let mut string = Wtf8Buf::new();
        string.push(CodePoint::from_u32(0xD800).unwrap());
        assert_eq!(string.as_str(), None);
    }

    #[test]
    fn wtf8_to_string_lossy() {
        assert_eq!(Wtf8::from_str("").to_string_lossy(), Cow::Borrowed(""));
        assert_eq!(Wtf8::from_str("aé 💩").to_string_lossy(), Cow::Borrowed("aé 💩"));
        let mut string = Wtf8Buf::from_str("aé 💩");
        string.push(CodePoint::from_u32(0xD800).unwrap());
        let expected: Cow<str> = Cow::Owned(String::from("aé 💩�"));
        assert_eq!(string.to_string_lossy(), expected);
    }

    #[test]
    fn wtf8_encode_wide() {
        let mut string = Wtf8Buf::from_str("aé ");
        string.push(CodePoint::from_u32(0xD83D).unwrap());
        string.push_char('💩');
        assert_eq!(string.encode_wide().collect::<Vec<_>>(),
                   vec![0x61, 0xE9, 0x20, 0xD83D, 0xD83D, 0xDCA9]);
    }

    fn from_cp(cp: u16) -> Wtf8Buf {
        let mut x = Wtf8Buf::new();
        x.push(CodePoint::from_u32(cp as u32).unwrap());
        x
    }

    #[test]
    fn wtf8_split_unicode() {
        use super::Section::*;
        assert!(Wtf8::from_str("").split_unicode().next().is_none());
        assert!(Wtf8::from_str("").split_unicode().next_back().is_none());
        assert_eq!(Wtf8::from_str("ab").split_unicode().collect::<Vec<_>>(),
                   [Unicode("ab")]);
        assert_eq!(Wtf8::from_str("ab").split_unicode().rev().collect::<Vec<_>>(),
                   [Unicode("ab")]);
        let non_unicode = from_cp(0xD800);
        assert_eq!(non_unicode.split_unicode().collect::<Vec<_>>(),
                   [NonUnicode(&non_unicode[..])]);
        assert_eq!(non_unicode.split_unicode().rev().collect::<Vec<_>>(),
                   [NonUnicode(&non_unicode[..])]);

        let mut string = non_unicode.clone();
        string.push_str("Γ");
        assert_eq!(string.split_unicode().collect::<Vec<_>>(),
                   [NonUnicode(&non_unicode[..]), Unicode("Γ")]);
        assert_eq!(string.split_unicode().rev().collect::<Vec<_>>(),
                   [Unicode("Γ"), NonUnicode(&non_unicode[..])]);
        let mut split = string.split_unicode();
        assert_eq!(split.next(), Some(NonUnicode(&non_unicode[..])));
        assert_eq!(split.next_back(), Some(Unicode("Γ")));
        assert_eq!(split.next(), None);
        let mut split = string.split_unicode();
        assert_eq!(split.next_back(), Some(Unicode("Γ")));
        assert_eq!(split.next(), Some(NonUnicode(&non_unicode[..])));
        assert_eq!(split.next_back(), None);
    }

    #[test]
    fn wtf8_contains_wtf8() {
        assert!(Wtf8::from_str("").contains_wtf8(Wtf8::from_str("")));
        assert!(Wtf8::from_str("aé 💩").contains_wtf8(Wtf8::from_str("")));
        assert!(Wtf8::from_str("aé 💩").contains_wtf8(Wtf8::from_str("aé 💩")));
        assert!(!Wtf8::from_str("").contains_wtf8(Wtf8::from_str("aé 💩")));
        assert!(Wtf8::from_str("aé 💩").contains_wtf8(Wtf8::from_str("aé")));
        assert!(Wtf8::from_str("aé 💩").contains_wtf8(Wtf8::from_str("é ")));
        assert!(Wtf8::from_str("aé 💩").contains_wtf8(Wtf8::from_str(" 💩")));

        // Non UTF-8 cases
        fn check(haystack: &[u16], needle: &[u16]) -> bool {
            Wtf8Buf::from_wide(haystack).contains_wtf8(&Wtf8Buf::from_wide(needle)[..])
        }

        // No surrogates in needle
        assert!( check(&[        0xD83D, 0xDE3A        ], &[0xD83D, 0xDE3A]));
        assert!( check(&[0x0020, 0xD83D, 0xDE3A        ], &[0xD83D, 0xDE3A]));
        assert!( check(&[0xD83D, 0xD83D, 0xDE3A        ], &[0xD83D, 0xDE3A]));
        assert!( check(&[0xD83E, 0xD83D, 0xDE3A        ], &[0xD83D, 0xDE3A]));
        assert!( check(&[0xDE3A, 0xD83D, 0xDE3A        ], &[0xD83D, 0xDE3A]));
        assert!( check(&[0xDE3B, 0xD83D, 0xDE3A        ], &[0xD83D, 0xDE3A]));
        assert!( check(&[        0xD83D, 0xDE3A, 0x0020], &[0xD83D, 0xDE3A]));
        assert!( check(&[        0xD83D, 0xDE3A, 0xD83D], &[0xD83D, 0xDE3A]));
        assert!( check(&[        0xD83D, 0xDE3A, 0xD83E], &[0xD83D, 0xDE3A]));
        assert!( check(&[        0xD83D, 0xDE3A, 0xDE3A], &[0xD83D, 0xDE3A]));
        assert!( check(&[        0xD83D, 0xDE3A, 0xDE3B], &[0xD83D, 0xDE3A]));
        assert!(!check(&[        0xD83E, 0xDE3A        ], &[0xD83D, 0xDE3A]));
        assert!(!check(&[        0xD83D, 0xDE3B        ], &[0xD83D, 0xDE3A]));
        assert!(!check(&[        0xD83E, 0xDE3B        ], &[0xD83D, 0xDE3A]));
        assert!(!check(&[        0xD83D                ], &[0xD83D, 0xDE3A]));
        assert!(!check(&[                0xDE3A        ], &[0xD83D, 0xDE3A]));
        assert!(!check(&[                              ], &[0xD83D, 0xDE3A]));

        // needle is just a lead surrogate
        assert!( check(&[        0xD83D        ], &[0xD83D]));
        assert!( check(&[0x0020, 0xD83D        ], &[0xD83D]));
        assert!( check(&[0xD83E, 0xD83D        ], &[0xD83D]));
        assert!( check(&[0xDE3A, 0xD83D        ], &[0xD83D]));
        assert!( check(&[        0xD83D, 0x0020], &[0xD83D]));
        assert!( check(&[        0xD83D, 0xD83E], &[0xD83D]));
        assert!( check(&[        0xD83D, 0xDE3A], &[0xD83D]));
        assert!(!check(&[        0xD83E        ], &[0xD83D]));
        assert!(!check(&[        0xDE3A        ], &[0xD83D]));
        assert!(!check(&[        0xD83E, 0xDE3A], &[0xD83D]));
        assert!(!check(&[                      ], &[0xD83D]));

        // needle is just a trail surrogate
        assert!( check(&[        0xDE3A        ], &[0xDE3A]));
        assert!( check(&[0x0020, 0xDE3A        ], &[0xDE3A]));
        assert!( check(&[0xD83D, 0xDE3A        ], &[0xDE3A]));
        assert!( check(&[0xDE3B, 0xDE3A        ], &[0xDE3A]));
        assert!( check(&[        0xDE3A, 0x0020], &[0xDE3A]));
        assert!( check(&[        0xDE3A, 0xD83D], &[0xDE3A]));
        assert!( check(&[        0xDE3A, 0xDE3B], &[0xDE3A]));
        assert!(!check(&[        0xDE3B        ], &[0xDE3A]));
        assert!(!check(&[        0xD83D        ], &[0xDE3A]));
        assert!(!check(&[0xD83D, 0xDE3B        ], &[0xDE3A]));
        assert!(!check(&[                      ], &[0xDE3A]));

        // needle is a trail and lead surrogate
        assert!( check(&[        0xDE3A, 0xD83D        ], &[0xDE3A, 0xD83D]));
        assert!( check(&[0x0020, 0xDE3A, 0xD83D        ], &[0xDE3A, 0xD83D]));
        assert!( check(&[0xD83D, 0xDE3A, 0xD83D        ], &[0xDE3A, 0xD83D]));
        assert!( check(&[0xD83E, 0xDE3A, 0xD83D        ], &[0xDE3A, 0xD83D]));
        assert!( check(&[0xDE3A, 0xDE3A, 0xD83D        ], &[0xDE3A, 0xD83D]));
        assert!( check(&[0xDE3B, 0xDE3A, 0xD83D        ], &[0xDE3A, 0xD83D]));
        assert!( check(&[        0xDE3A, 0xD83D, 0x0020], &[0xDE3A, 0xD83D]));
        assert!( check(&[        0xDE3A, 0xD83D, 0xD83D], &[0xDE3A, 0xD83D]));
        assert!( check(&[        0xDE3A, 0xD83D, 0xD83E], &[0xDE3A, 0xD83D]));
        assert!( check(&[        0xDE3A, 0xD83D, 0xDE3A], &[0xDE3A, 0xD83D]));
        assert!( check(&[        0xDE3A, 0xD83D, 0xDE3B], &[0xDE3A, 0xD83D]));
        assert!( check(&[0xD83D, 0xDE3A, 0xD83D, 0xDE3A], &[0xDE3A, 0xD83D]));

        assert!(!check(&[        0xDE3A, 0xD83E        ], &[0xDE3A, 0xD83D]));
        assert!(!check(&[0xD83D, 0xDE3A, 0xD83E        ], &[0xDE3A, 0xD83D]));
        assert!(!check(&[        0xDE3A, 0xD83E, 0xDE3A], &[0xDE3A, 0xD83D]));
        assert!(!check(&[0xD83D, 0xDE3A, 0xD83E, 0xDE3A], &[0xDE3A, 0xD83D]));

        assert!(!check(&[        0xDE3B, 0xD83D        ], &[0xDE3A, 0xD83D]));
        assert!(!check(&[0xD83D, 0xDE3B, 0xD83D        ], &[0xDE3A, 0xD83D]));
        assert!(!check(&[        0xDE3B, 0xD83D, 0xDE3A], &[0xDE3A, 0xD83D]));
        assert!(!check(&[0xD83D, 0xDE3B, 0xD83D, 0xDE3A], &[0xDE3A, 0xD83D]));

        assert!(!check(&[        0xDE3A                ], &[0xDE3A, 0xD83D]));
        assert!(!check(&[                0xD83D        ], &[0xDE3A, 0xD83D]));
        assert!(!check(&[                              ], &[0xDE3A, 0xD83D]));

        // needle is a trail surrogate and other stuff
        assert!( check(&[        0xDE3A, 0x0020        ], &[0xDE3A, 0x0020]));
        assert!( check(&[0x0020, 0xDE3A, 0x0020        ], &[0xDE3A, 0x0020]));
        assert!( check(&[0xD83D, 0xDE3A, 0x0020        ], &[0xDE3A, 0x0020]));
        assert!( check(&[0xDE3A, 0xDE3A, 0x0020        ], &[0xDE3A, 0x0020]));
        assert!( check(&[        0xDE3A, 0x0020, 0x0020], &[0xDE3A, 0x0020]));
        assert!( check(&[        0xDE3A, 0x0020, 0xD83D], &[0xDE3A, 0x0020]));
        assert!( check(&[        0xDE3A, 0x0020, 0xDE3A], &[0xDE3A, 0x0020]));
        assert!( check(&[0xD83D, 0xDE3A, 0x0020, 0x0020], &[0xDE3A, 0x0020]));
        assert!(!check(&[0xD83D, 0xDE3A, 0x0021        ], &[0xDE3A, 0x0020]));
        assert!(!check(&[0xD83D, 0xDE3B, 0x0020        ], &[0xDE3A, 0x0020]));
        assert!(!check(&[        0xDE3A                ], &[0xDE3A, 0x0020]));
        assert!(!check(&[                0x0020        ], &[0xDE3A, 0x0020]));
        assert!(!check(&[                              ], &[0xDE3A, 0x0020]));

        assert!( check(&[        0xDE3A, 0xDE3A        ], &[0xDE3A, 0xDE3A]));
        assert!( check(&[0x0020, 0xDE3A, 0xDE3A        ], &[0xDE3A, 0xDE3A]));
        assert!( check(&[0xD83D, 0xDE3A, 0xDE3A        ], &[0xDE3A, 0xDE3A]));
        assert!( check(&[0xDE3B, 0xDE3A, 0xDE3A        ], &[0xDE3A, 0xDE3A]));
        assert!( check(&[        0xDE3A, 0xDE3A, 0x0020], &[0xDE3A, 0xDE3A]));
        assert!( check(&[        0xDE3A, 0xDE3A, 0xD83D], &[0xDE3A, 0xDE3A]));
        assert!( check(&[        0xDE3A, 0xDE3A, 0xDE3B], &[0xDE3A, 0xDE3A]));
        assert!( check(&[0xD83D, 0xDE3A, 0xDE3A, 0xDE3B], &[0xDE3A, 0xDE3A]));
        assert!(!check(&[0xD83D, 0xDE3A, 0xDE3B        ], &[0xDE3A, 0xDE3A]));
        assert!(!check(&[0xD83D, 0xDE3B, 0xDE3A        ], &[0xDE3A, 0xDE3A]));
        assert!(!check(&[        0xDE3A                ], &[0xDE3A, 0xDE3A]));
        assert!(!check(&[                              ], &[0xDE3A, 0xDE3A]));

        // needle is a other stuff and a lead surrogate
        assert!( check(&[        0x0020, 0xD83D        ], &[0x0020, 0xD83D]));
        assert!( check(&[0x0020, 0x0020, 0xD83D        ], &[0x0020, 0xD83D]));
        assert!( check(&[0xD83D, 0x0020, 0xD83D        ], &[0x0020, 0xD83D]));
        assert!( check(&[0xDE3A, 0x0020, 0xD83D        ], &[0x0020, 0xD83D]));
        assert!( check(&[        0x0020, 0xD83D, 0x0020], &[0x0020, 0xD83D]));
        assert!( check(&[        0x0020, 0xD83D, 0xD83D], &[0x0020, 0xD83D]));
        assert!( check(&[        0x0020, 0xD83D, 0xDE3A], &[0x0020, 0xD83D]));
        assert!( check(&[0x0020, 0x0020, 0xD83D, 0x0020], &[0x0020, 0xD83D]));
        assert!(!check(&[        0x0020, 0xD83E, 0xDE3A], &[0x0020, 0xD83D]));
        assert!(!check(&[        0x0021, 0xD83D, 0xDE3A], &[0x0020, 0xD83D]));
        assert!(!check(&[        0x0020                ], &[0x0020, 0xD83D]));
        assert!(!check(&[                0xD83D        ], &[0x0020, 0xD83D]));
        assert!(!check(&[                              ], &[0x0020, 0xD83D]));

        assert!( check(&[        0xD83D, 0xD83D        ], &[0xD83D, 0xD83D]));
        assert!( check(&[0x0020, 0xD83D, 0xD83D        ], &[0xD83D, 0xD83D]));
        assert!( check(&[0xD83E, 0xD83D, 0xD83D        ], &[0xD83D, 0xD83D]));
        assert!( check(&[0xDE3A, 0xD83D, 0xD83D        ], &[0xD83D, 0xD83D]));
        assert!( check(&[        0xD83D, 0xD83D, 0x0020], &[0xD83D, 0xD83D]));
        assert!( check(&[        0xD83D, 0xD83D, 0xD83E], &[0xD83D, 0xD83D]));
        assert!( check(&[        0xD83D, 0xD83D, 0xDE3A], &[0xD83D, 0xD83D]));
        assert!( check(&[0xD83E, 0xD83D, 0xD83D, 0xDE3A], &[0xD83D, 0xD83D]));
        assert!(!check(&[        0xD83D, 0xD83E, 0xDE3A], &[0xD83D, 0xD83D]));
        assert!(!check(&[        0xD83E, 0xD83D, 0xDE3A], &[0xD83D, 0xD83D]));
        assert!(!check(&[        0xD83D                ], &[0xD83D, 0xD83D]));
        assert!(!check(&[                              ], &[0xD83D, 0xD83D]));

        // needle is a trail surrogate, other stuff, and a lead surrogate
        assert!( check(&[        0xDE3A, 0x0020, 0xD83D        ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!( check(&[0x0020, 0xDE3A, 0x0020, 0xD83D        ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!( check(&[0xD83D, 0xDE3A, 0x0020, 0xD83D        ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!( check(&[0xDE3A, 0xDE3A, 0x0020, 0xD83D        ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!( check(&[        0xDE3A, 0x0020, 0xD83D, 0x0020], &[0xDE3A, 0x0020, 0xD83D]));
        assert!( check(&[        0xDE3A, 0x0020, 0xD83D, 0xD83D], &[0xDE3A, 0x0020, 0xD83D]));
        assert!( check(&[        0xDE3A, 0x0020, 0xD83D, 0xDE3A], &[0xDE3A, 0x0020, 0xD83D]));
        assert!( check(&[0xD83D, 0xDE3A, 0x0020, 0xD83D, 0xDE3A], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[0xD83D, 0xDE3B, 0x0020, 0xD83D, 0xDE3A], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[0xD83D, 0xDE3A, 0x0021, 0xD83D, 0xDE3A], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[0xD83D, 0xDE3A, 0x0020, 0xD83E, 0xDE3A], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[        0xDE3A, 0x0020                ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[        0xDE3A,         0xD83D        ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[        0xDE3A,                       ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[                0x0020, 0xD83D        ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[                0x0020                ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[                        0xD83D        ], &[0xDE3A, 0x0020, 0xD83D]));
        assert!(!check(&[                                      ], &[0xDE3A, 0x0020, 0xD83D]));

        // Non-surrogate part matches two overlapping times
        assert!(check(&[0xD83D, 0xDE3A, 0xD83D, 0xDE3A, 0xD83D, 0xDE3A],
                      &[        0xDE3A, 0xD83D, 0xDE3A, 0xD83D, 0xDE3A]));
        assert!(check(&[0xD83D, 0xDE3A, 0xD83D, 0xDE3A, 0xD83D, 0xDE3A],
                      &[0xD83D, 0xDE3A, 0xD83D, 0xDE3A, 0xD83D        ]));
    }

    #[test]
    fn wtf8_starts_with_wtf8() {
        assert!(Wtf8::from_str("aé 💩").starts_with_wtf8(Wtf8::from_str("aé")));
        assert!(Wtf8::from_str("aé 💩").starts_with_wtf8(Wtf8::from_str("aé 💩")));
        assert!(Wtf8::from_str("aé 💩").starts_with_wtf8(Wtf8::from_str("")));
        assert!(!Wtf8::from_str("aé 💩").starts_with_wtf8(Wtf8::from_str("é")));
        assert!(Wtf8::from_str("").starts_with_wtf8(Wtf8::from_str("")));
        assert!(!Wtf8::from_str("").starts_with_wtf8(Wtf8::from_str("a")));

        fn check_surrogates(prefix: &Wtf8) {
            let mut lead = prefix.to_owned();
            lead.push_wtf8(&from_cp(0xD83D)[..]);
            let mut other_lead = prefix.to_owned();
            other_lead.push_wtf8(&from_cp(0xD83E)[..]);
            let trail = from_cp(0xDE3A);
            let mut full = lead.clone();
            full.push_wtf8(&trail);
            assert_eq!(full, { let mut x = prefix.to_owned(); x.push_str("😺"); x });

            assert!(full.starts_with_wtf8(&full));
            assert!(lead.starts_with_wtf8(&lead));
            assert!(trail.starts_with_wtf8(&trail));
            assert!(lead.starts_with_wtf8(prefix));
            assert!(full.starts_with_wtf8(&lead));
            assert!(!full.starts_with_wtf8(&trail));
            assert!(!full.starts_with_wtf8(&other_lead));
            assert!(!lead.starts_with_wtf8(&full));
        }

        check_surrogates(Wtf8::from_str(""));
        check_surrogates(Wtf8::from_str("a"));
        check_surrogates(&from_cp(0xD83D)[..]);
    }

    #[test]
    fn wtf8_ends_with_wtf8() {
        assert!(Wtf8::from_str("aé 💩").ends_with_wtf8(Wtf8::from_str(" 💩")));
        assert!(Wtf8::from_str("aé 💩").ends_with_wtf8(Wtf8::from_str("aé 💩")));
        assert!(Wtf8::from_str("aé 💩").ends_with_wtf8(Wtf8::from_str("")));
        assert!(!Wtf8::from_str("aé 💩").ends_with_wtf8(Wtf8::from_str("é")));
        assert!(Wtf8::from_str("").ends_with_wtf8(Wtf8::from_str("")));
        assert!(!Wtf8::from_str("").ends_with_wtf8(Wtf8::from_str("a")));

        fn check_surrogates(suffix: &Wtf8) {
            let lead = from_cp(0xD83D);
            let mut trail = from_cp(0xDE3A);
            trail.push_wtf8(suffix);
            let mut other_trail = from_cp(0xDE3B);
            other_trail.push_wtf8(suffix);
            let mut full = lead.clone();
            full.push_wtf8(&trail);
            assert_eq!(full, { let mut x = Wtf8Buf::from_str("😺"); x.push_wtf8(suffix); x });

            assert!(full.ends_with_wtf8(&full));
            assert!(lead.ends_with_wtf8(&lead));
            assert!(trail.ends_with_wtf8(&trail));
            assert!(trail.ends_with_wtf8(suffix));
            assert!(full.ends_with_wtf8(&trail));
            assert!(!full.ends_with_wtf8(&lead));
            assert!(!full.ends_with_wtf8(&other_trail));
            assert!(!trail.ends_with_wtf8(&full));
        }

        check_surrogates(Wtf8::from_str(""));
        check_surrogates(Wtf8::from_str("a"));
        check_surrogates(&from_cp(0xDE3A)[..]);
    }

    #[test]
    fn wtf8_split() {
        assert_eq!(Wtf8::from_str("").split('a').collect::<Vec<_>>(),
                   [Wtf8::from_str("")]);

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = Wtf8Buf::from_str("aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓaΓaé 💩aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓ");
        assert_eq!(string.split("aΓ").collect::<Vec<_>>(),
                   [Wtf8::from_str(""), &non_utf8[..], Wtf8::from_str(""),
                    Wtf8::from_str("aé 💩"), &non_utf8[..], Wtf8::from_str("")]);

        assert_eq!(Wtf8::from_str("aaa").split("aa").collect::<Vec<_>>(),
                   [Wtf8::from_str(""), Wtf8::from_str("a")]);
    }

    #[test]
    fn wtf8_rsplit() {
        assert_eq!(Wtf8::from_str("").rsplit('a').collect::<Vec<_>>(),
                   [Wtf8::from_str("")]);

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = Wtf8Buf::from_str("aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓaΓaé 💩aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓ");
        assert_eq!(string.rsplit("aΓ").collect::<Vec<_>>(),
                   [Wtf8::from_str(""), &non_utf8[..], Wtf8::from_str("aé 💩"),
                    Wtf8::from_str(""), &non_utf8[..], Wtf8::from_str("")]);

        assert_eq!(Wtf8::from_str("aaa").rsplit("aa").collect::<Vec<_>>(),
                   [Wtf8::from_str(""), Wtf8::from_str("a")]);
    }

    #[test]
    fn wtf8_split_terminator() {
        assert!(Wtf8::from_str("").split_terminator('a').next().is_none());
        assert!(Wtf8::from_str("").split_terminator('a').next_back().is_none());
        assert_eq!(Wtf8::from_str("a").split_terminator('a').collect::<Vec<_>>(),
                   [Wtf8::from_str("")]);
        assert_eq!(Wtf8::from_str("a").split_terminator('a').rev().collect::<Vec<_>>(),
                   [Wtf8::from_str("")]);

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = Wtf8Buf::from_str("aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("Γ");
        assert_eq!(string.split_terminator("Γ").collect::<Vec<_>>(),
                   [Wtf8::from_str("a"), &non_utf8[..]]);
        string.push_str("aé 💩");
        assert_eq!(string.split_terminator("Γ").collect::<Vec<_>>(),
                   [Wtf8::from_str("a"), &non_utf8[..], Wtf8::from_str("aé 💩")]);

        let string = Wtf8::from_str("xΓΓx");
        let mut split = string.split_terminator('Γ');
        assert_eq!(split.next(), Some(Wtf8::from_str("x")));
        assert_eq!(split.next_back(), Some(Wtf8::from_str("x")));
        assert_eq!(split.clone().next(), Some(Wtf8::from_str("")));
        assert_eq!(split.next_back(), Some(Wtf8::from_str("")));
    }

    #[test]
    fn wtf8_rsplit_terminator() {
        assert!(Wtf8::from_str("").rsplit_terminator('a').next().is_none());
        assert!(Wtf8::from_str("").rsplit_terminator('a').next_back().is_none());
        assert_eq!(Wtf8::from_str("a").rsplit_terminator('a').collect::<Vec<_>>(),
                   [Wtf8::from_str("")]);
        assert_eq!(Wtf8::from_str("a").rsplit_terminator('a').rev().collect::<Vec<_>>(),
                   [Wtf8::from_str("")]);

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = Wtf8Buf::from_str("aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("Γ");
        assert_eq!(string.rsplit_terminator("Γ").collect::<Vec<_>>(),
                   [&non_utf8[..], Wtf8::from_str("a")]);
        string.push_str("aé 💩");
        assert_eq!(string.rsplit_terminator("Γ").collect::<Vec<_>>(),
                   [Wtf8::from_str("aé 💩"), &non_utf8[..], Wtf8::from_str("a")]);

        let string = Wtf8::from_str("xΓΓx");
        let mut split = string.rsplit_terminator('Γ');
        assert_eq!(split.next(), Some(Wtf8::from_str("x")));
        assert_eq!(split.next_back(), Some(Wtf8::from_str("x")));
        assert_eq!(split.clone().next(), Some(Wtf8::from_str("")));
        assert_eq!(split.next_back(), Some(Wtf8::from_str("")));
    }

    #[test]
    fn wtf8_splitn() {
        assert_eq!(Wtf8::from_str("").splitn(2, 'a').collect::<Vec<_>>(),
                   [Wtf8::from_str("")]);
        assert!(Wtf8::from_str("a").splitn(0, 'a').next().is_none());
        assert_eq!(Wtf8::from_str("a").splitn(1, 'a').collect::<Vec<_>>(),
                   [Wtf8::from_str("a")]);

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = Wtf8Buf::from_str("aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓaΓaé 💩aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓ");
        let mut end = non_utf8.clone();
        end.push_str("aΓ");
        assert_eq!(string.splitn(5, "aΓ").collect::<Vec<_>>(),
                   [Wtf8::from_str(""), &non_utf8[..], Wtf8::from_str(""),
                    Wtf8::from_str("aé 💩"), &end[..]]);
    }

    #[test]
    fn wtf8_rsplitn() {
        assert_eq!(Wtf8::from_str("").rsplitn(2, 'a').collect::<Vec<_>>(),
                   [Wtf8::from_str("")]);
        assert!(Wtf8::from_str("a").rsplitn(0, 'a').next().is_none());
        assert_eq!(Wtf8::from_str("a").rsplitn(1, 'a').collect::<Vec<_>>(),
                   [Wtf8::from_str("a")]);

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = Wtf8Buf::from_str("aΓ");
        string.push_wtf8(&non_utf8);
        let beginning = string.clone();
        string.push_str("aΓaΓaé 💩aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓ");
        assert_eq!(string.rsplitn(5, "aΓ").collect::<Vec<_>>(),
                   [Wtf8::from_str(""), &non_utf8[..], Wtf8::from_str("aé 💩"),
                    Wtf8::from_str(""), &beginning[..]]);
    }

    #[test]
    fn wtf8_matches() {
        assert!(Wtf8::from_str("").matches('a').next().is_none());

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = Wtf8Buf::from_str("aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓaΓaé 💩aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓ");
        assert_eq!(string.matches("aΓ").collect::<Vec<_>>(), ["aΓ"; 5]);
        assert_eq!(string.matches(&['é', '💩'] as &[_]).collect::<Vec<_>>(), ["é", "💩"]);
    }

    #[test]
    fn wtf8_rmatches() {
        assert!(Wtf8::from_str("").rmatches('a').next().is_none());

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = Wtf8Buf::from_str("aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓaΓaé 💩aΓ");
        string.push_wtf8(&non_utf8);
        string.push_str("aΓ");
        assert_eq!(string.rmatches("aΓ").collect::<Vec<_>>(), ["aΓ"; 5]);
        assert_eq!(string.rmatches(&['é', '💩'] as &[_]).collect::<Vec<_>>(), ["💩", "é"]);
    }

    #[test]
    fn wtf8_matches_replacement() {
        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let replacement = non_utf8.to_string_lossy().into_owned();
        assert!(non_utf8.matches(&replacement).next().is_none());
    }

    #[test]
    fn wtf8_trim_matches() {
        assert_eq!(Wtf8::from_str("").trim_matches('a'), Wtf8::from_str(""));
        assert_eq!(Wtf8::from_str("b").trim_matches('a'), Wtf8::from_str("b"));
        assert_eq!(Wtf8::from_str("a").trim_matches('a'), Wtf8::from_str(""));
        assert_eq!(Wtf8::from_str("ab").trim_matches('a'), Wtf8::from_str("b"));
        assert_eq!(Wtf8::from_str("ba").trim_matches('a'), Wtf8::from_str("b"));
        assert_eq!(Wtf8::from_str("aba").trim_matches('a'), Wtf8::from_str("b"));
        assert_eq!(Wtf8::from_str("bab").trim_matches('a'), Wtf8::from_str("bab"));

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = non_utf8.clone();
        string.push_str("x");
        assert_eq!(string.trim_matches('x'), &non_utf8[..]);
        let mut string = Wtf8Buf::from_str("x");
        string.push_wtf8(&non_utf8);
        assert_eq!(string.trim_matches('x'), &non_utf8[..]);
    }

    #[test]
    fn wtf8_trim_left_matches() {
        assert_eq!(Wtf8::from_str("").trim_left_matches('a'), Wtf8::from_str(""));
        assert_eq!(Wtf8::from_str("b").trim_left_matches('a'), Wtf8::from_str("b"));
        assert_eq!(Wtf8::from_str("a").trim_left_matches('a'), Wtf8::from_str(""));
        assert_eq!(Wtf8::from_str("ab").trim_left_matches('a'), Wtf8::from_str("b"));
        assert_eq!(Wtf8::from_str("ba").trim_left_matches('a'), Wtf8::from_str("ba"));

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = non_utf8.clone();
        string.push_str("x");
        assert_eq!(string.trim_left_matches('x'), &string[..]);
        let mut string = Wtf8Buf::from_str("x");
        string.push_wtf8(&non_utf8);
        assert_eq!(string.trim_left_matches('x'), &non_utf8[..]);
    }

    #[test]
    fn wtf8_trim_right_matches() {
        assert_eq!(Wtf8::from_str("").trim_right_matches('a'), Wtf8::from_str(""));
        assert_eq!(Wtf8::from_str("b").trim_right_matches('a'), Wtf8::from_str("b"));
        assert_eq!(Wtf8::from_str("a").trim_right_matches('a'), Wtf8::from_str(""));
        assert_eq!(Wtf8::from_str("ab").trim_right_matches('a'), Wtf8::from_str("ab"));
        assert_eq!(Wtf8::from_str("ba").trim_right_matches('a'), Wtf8::from_str("b"));

        let mut non_utf8 = Wtf8Buf::new();
        non_utf8.push(CodePoint::from_u32(0xD800).unwrap());
        let mut string = non_utf8.clone();
        string.push_str("x");
        assert_eq!(string.trim_right_matches('x'), &non_utf8[..]);
        let mut string = Wtf8Buf::from_str("x");
        string.push_wtf8(&non_utf8);
        assert_eq!(string.trim_right_matches('x'), &string[..]);
    }

    #[test]
    fn wtf8_replace_smoke() {
        assert_eq!(&Wtf8::from_str("").replace("a", "b")[..], Wtf8::from_str(""));
        assert_eq!(&Wtf8::from_str("a").replace("a", "b")[..], Wtf8::from_str("b"));
        assert_eq!(&Wtf8::from_str("").replace("", "b")[..], Wtf8::from_str("b"));
        assert_eq!(&Wtf8::from_str("a").replace("a", "")[..], Wtf8::from_str(""));
        assert_eq!(&Wtf8::from_str("").replace("", "aé 💩")[..], Wtf8::from_str("aé 💩"));
        assert_eq!(&Wtf8::from_str("b").replace("b", "aé 💩")[..], Wtf8::from_str("aé 💩"));
        assert_eq!(&Wtf8::from_str("aaa").replace("a", "b")[..], Wtf8::from_str("bbb"));
        assert_eq!(&Wtf8::from_str("abb").replace("ab", "a")[..], Wtf8::from_str("ab"));
    }

    #[test]
    fn wtf8_replace_empty() {
        // Matching the empty string
        fn fw<T: AsRef<[u16]>>(wide: T) -> Wtf8Buf { Wtf8Buf::from_wide(wide.as_ref()) }
        // BMP
        assert_eq!(fw([0x0020, 0x0393]).replace("", fw([0x0394])),
                   fw([0x0394, 0x0020, 0x0394, 0x0393, 0x0394]));
        // Unpaired surrogates
        assert_eq!(fw([0xDE3A, 0xD83D]).replace("", fw([0x0394])),
                   fw([0x0394, 0xDE3A, 0x0394, 0xD83D, 0x0394]));
        // Paired surrogates
        assert_eq!(fw([0xD83D, 0xDE3A]).replace("", fw([0x0394])),
                   fw([0x0394, 0xD83D, 0x0394, 0xDE3A, 0x0394]));
    }

    #[test]
    fn wtf8_replace_simple() {
        // Simple case where the `from` string can't match partial characters
        fn fw<T: AsRef<[u16]>>(wide: T) -> Wtf8Buf { Wtf8Buf::from_wide(wide.as_ref()) }
        // Exact match
        assert_eq!(fw([0xD83D, 0xDE3A]).replace(fw([0xD83D, 0xDE3A]), fw([0x0394])),
                   fw([0x0394]));
        // Non-match
        assert_eq!(fw([0xD83D, 0xDE3B]).replace(fw([0xD83D, 0xDE3A]), fw([0x0394])),
                   fw([0xD83D, 0xDE3B]));
        // Not at the start or end
        assert_eq!(fw([0x0020, 0xD83D, 0xDE3A, 0x0021])
                   .replace(fw([0xD83D, 0xDE3A]), fw([0x0394])),
                   fw([0x0020, 0x0394, 0x0021]));
        // Not at the start or end with surrogates
        assert_eq!(fw([0xD83D, 0xD83D, 0xDE3A, 0xDE3A])
                   .replace(fw([0xD83D, 0xDE3A]), fw([0x0394])),
                   fw([0xD83D, 0x0394, 0xDE3A]));
        // Non-unicode
        assert_eq!(fw([0xD83D, 0x0020, 0xDE3A])
                   .replace(fw([0xD83D, 0x0020, 0xDE3A]), fw([0x0394])),
                   fw([0x0394]));

    }

    #[test]
    fn wtf8_replace_surrogate() {
        // Replace a single surrogate
        fn fw<T: AsRef<[u16]>>(wide: T) -> Wtf8Buf { Wtf8Buf::from_wide(wide.as_ref()) }
        // Basic
        assert_eq!(fw([0xD83D]).replace(fw([0xD83D]), fw([0x0393])),
                   fw([0x0393]));
        assert_eq!(fw([0xDE3A]).replace(fw([0xDE3A]), fw([0x0393])),
                   fw([0x0393]));
        // Unpaired in the middle
        assert_eq!(fw([0x0020, 0xD83D, 0x0021]).replace(fw([0xD83D]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0x0021]));
        assert_eq!(fw([0x0020, 0xDE3A, 0x0021]).replace(fw([0xDE3A]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0x0021]));
        // Paired at the end
        assert_eq!(fw([0xD83D, 0xDE3A]).replace(fw([0xD83D]), fw([0x0393])),
                   fw([0x0393, 0xDE3A]));
        assert_eq!(fw([0xD83D, 0xDE3A]).replace(fw([0xDE3A]), fw([0x0393])),
                   fw([0xD83D, 0x0393]));
        // Paired in the middle
        assert_eq!(fw([0x0020, 0xD83D, 0xDE3A, 0x0021])
                   .replace(fw([0xD83D]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0xDE3A, 0x0021]));
        assert_eq!(fw([0x0020, 0xD83D, 0xDE3A, 0x0021])
                   .replace(fw([0xDE3A]), fw([0x0393])),
                   fw([0x0020, 0xD83D, 0x0393, 0x0021]));
    }

    #[test]
    fn wtf8_replace_two_surrogates() {
        // Replace two unpaired surrogates
        fn fw<T: AsRef<[u16]>>(wide: T) -> Wtf8Buf { Wtf8Buf::from_wide(wide.as_ref()) }
        // Basic
        assert_eq!(fw([0xDE3A, 0xD83D])
                   .replace(fw([0xDE3A, 0xD83D]), fw([0x0393])),
                   fw([0x0393]));
        // Unpaired in the middle
        assert_eq!(fw([0x0020, 0xDE3A, 0xD83D, 0x0021])
                   .replace(fw([0xDE3A, 0xD83D]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0x0021]));
        // Paired in the middle
        assert_eq!(fw([0xD83D, 0xDE3A, 0xD83D, 0xDE3A])
                   .replace(fw([0xDE3A, 0xD83D]), fw([0x0393])),
                   fw([0xD83D, 0x0393, 0xDE3A]));
        // Two matches splitting a char
        assert_eq!(fw([0xDE3A, 0xD83D, 0xDE3A, 0xD83D])
                   .replace(fw([0xDE3A, 0xD83D]), fw([0x0393])),
                   fw([0x0393, 0x0393]));
        // Test that creating a new char from parts works
        assert_eq!(fw([0xD83D, 0xDE3A, 0xD83D, 0xDE3A])
                   .replace(fw([0xDE3A, 0xD83D]), fw([])),
                   fw([0xD83D, 0xDE3A]));
        assert_eq!(fw([0xD83D, 0xDE3A, 0xD83D, 0xDE3A])
                   .replace(fw([0xDE3A, 0xD83D]), fw([0xDE3B, 0xD83E])),
                   fw([0xD83D, 0xDE3B, 0xD83E, 0xDE3A]));
    }

    #[test]
    fn wtf8_replace_start_surrogate() {
        // Replace something starting with an unpaired surrogate
        fn fw<T: AsRef<[u16]>>(wide: T) -> Wtf8Buf { Wtf8Buf::from_wide(wide.as_ref()) }
        // Wrong surrogate (no match)
        assert_eq!(fw([0xDE3B, 0x0020])
                   .replace(fw([0xDE3A, 0x0020]), fw([0x0393])),
                   fw([0x0DE3B, 0x0020]));
        // Wrong remainder (no match)
        assert_eq!(fw([0xDE3A, 0x0021])
                   .replace(fw([0xDE3A, 0x0020]), fw([0x0393])),
                   fw([0x0DE3A, 0x0021]));
        // Entire string
        assert_eq!(fw([0xDE3A, 0x0020])
                   .replace(fw([0xDE3A, 0x0020]), fw([0x0393])),
                   fw([0x0393]));
        // Middle of string
        assert_eq!(fw([0x0040, 0xDE3A, 0x0020, 0x0041])
                   .replace(fw([0xDE3A, 0x0020]), fw([0x0393])),
                   fw([0x0040, 0x0393, 0x0041]));
        // Middle of string with extra matches of non-surrogate part
        assert_eq!(fw([0x0020, 0xDE3A, 0x0020, 0x0020])
                   .replace(fw([0xDE3A, 0x0020]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0x0020]));
        // Paired
        assert_eq!(fw([0x0040, 0xD83D, 0xDE3A, 0x0020, 0x0041])
                   .replace(fw([0xDE3A, 0x0020]), fw([0x0393])),
                   fw([0x0040, 0xD83D, 0x0393, 0x0041]));
        // Match twice, separated
        assert_eq!(fw([0x0040, 0xDE3A, 0x0020, 0x0041, 0xDE3A, 0x0020, 0x0042])
                   .replace(fw([0xDE3A, 0x0020]), fw([0x0393])),
                   fw([0x0040, 0x0393, 0x0041, 0x0393, 0x0042]));
        // Match twice, adjacent
        assert_eq!(fw([0x0040, 0xDE3A, 0x0020, 0xDE3A, 0x0020, 0x0042])
                   .replace(fw([0xDE3A, 0x0020]), fw([0x0393])),
                   fw([0x0040, 0x0393, 0x0393, 0x0042]));
    }

    #[test]
    fn wtf8_replace_end_surrogate() {
        // Replace something ending with an unpaired surrogate
        fn fw<T: AsRef<[u16]>>(wide: T) -> Wtf8Buf { Wtf8Buf::from_wide(wide.as_ref()) }
        // Wrong surrogate (no match)
        assert_eq!(fw([0x0020, 0xD83E])
                   .replace(fw([0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0020, 0xD83E]));
        // Wrong remainder (no match)
        assert_eq!(fw([0x0021, 0xD83D])
                   .replace(fw([0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0021, 0xD83D]));
        // Entire string
        assert_eq!(fw([0x0020, 0xD83D])
                   .replace(fw([0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0393]));
        // Middle of string
        assert_eq!(fw([0x0040, 0x0020, 0xD83D, 0x0041])
                   .replace(fw([0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0040, 0x0393, 0x0041]));
        // Middle of string with extra matches of non-surrogate part
        assert_eq!(fw([0x0020, 0x0020, 0xD83D, 0x0020])
                   .replace(fw([0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0x0020]));
        // Paired
        assert_eq!(fw([0x0040, 0x0020, 0xD83D, 0xDE3A, 0x0041])
                   .replace(fw([0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0040, 0x0393, 0xDE3A, 0x0041]));
        // Match twice, separated
        assert_eq!(fw([0x0040, 0x0020, 0xD83D, 0x0041, 0x0020, 0xD83D, 0x0042])
                   .replace(fw([0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0040, 0x0393, 0x0041, 0x0393, 0x0042]));
        // Match twice, adjacent
        assert_eq!(fw([0x0040, 0x0020, 0xD83D, 0x0020, 0xD83D, 0x0042])
                   .replace(fw([0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0040, 0x0393, 0x0393, 0x0042]));
    }

    #[test]
    fn wtf8_replace_wtf8_and_two_surrogates() {
        // Replace something strting and ending with unpaired
        // surrogates, with other stuff between them
        fn fw<T: AsRef<[u16]>>(wide: T) -> Wtf8Buf { Wtf8Buf::from_wide(wide.as_ref()) }
        // Wrong start surrogate (no match)
        assert_eq!(fw([0xDE3B, 0x0020, 0xD83D])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xDE3B, 0x0020, 0xD83D]));
        // Wrong middle (no match)
        assert_eq!(fw([0xDE3A, 0x0021, 0xD83D])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xDE3A, 0x0021, 0xD83D]));
        // Wrong end surrogate (no match)
        assert_eq!(fw([0xDE3A, 0x0020, 0xD83E])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xDE3A, 0x0020, 0xD83E]));
        // Entire match
        assert_eq!(fw([0xDE3A, 0x0020, 0xD83D])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0393]));
        // Entire match, non-Unicode middle
        assert_eq!(fw([0xDE3A, 0xDE3A, 0xD83D])
                   .replace(fw([0xDE3A, 0xDE3A, 0xD83D]), fw([0x0393])),
                   fw([0x0393]));
        // Wrong paired start surrogate (no match)
        assert_eq!(fw([0xD83E, 0xDE3B, 0x0020, 0xD83D, 0xDE3B])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xD83E, 0xDE3B, 0x0020, 0xD83D, 0xDE3B]));
        // Wrong paired end surrogate (no match)
        assert_eq!(fw([0xD83E, 0xDE3A, 0x0020, 0xD83E, 0xDE3B])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xD83E, 0xDE3A, 0x0020, 0xD83E, 0xDE3B]));
        // Middle without pairings
        assert_eq!(fw([0x0020, 0xDE3A, 0x0020, 0xD83D, 0x0021])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0x0021]));
        // Middle with start paring
        assert_eq!(fw([0xD83E, 0xDE3A, 0x0020, 0xD83D, 0x0020])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xD83E, 0x0393, 0x0020]));
        // Middle with end pairing
        assert_eq!(fw([0x0020, 0xDE3A, 0x0020, 0xD83D, 0xDE3B])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0xDE3B]));
        // Middle with two parings
        assert_eq!(fw([0xD83E, 0xDE3A, 0x0020, 0xD83D, 0xDE3B])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xD83E, 0x0393, 0xDE3B]));
        // Middle with two pairings equal to the opposite ends
        assert_eq!(fw([0xD83D, 0xDE3A, 0x0020, 0xD83D, 0xDE3A])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xD83D, 0x0393, 0xDE3A]));
        // Match twice, non-adjacent, unpaired
        assert_eq!(fw([0x0020,
                       0xDE3A, 0x0020, 0xD83D,
                       0x0021,
                       0xDE3A, 0x0020, 0xD83D,
                       0x0022])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0x0021, 0x0393, 0x022]));
        // Match twice, non-adjacent, paired
        assert_eq!(fw([0xD83E,
                       0xDE3A, 0x0020, 0xD83D,
                       0xDE3B, 0x0021, 0xD83E,
                       0xDE3A, 0x0020, 0xD83D,
                       0xDE3B])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xD83E, 0x0393, 0xDE3B, 0x0021, 0xD83E, 0x0393, 0xDE3B]));
        // Match twice, adjacent, unpaired
        assert_eq!(fw([0x0020,
                       0xDE3A, 0x0020, 0xD83D,
                       0xDE3A, 0x0020, 0xD83D,
                       0x0022])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0x0020, 0x0393, 0x0393, 0x022]));
        // Match twice, adjacent, paired
        assert_eq!(fw([0xD83E,
                       0xDE3A, 0x0020, 0xD83D,
                       0xDE3A, 0x0020, 0xD83D,
                       0xDE3B])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xD83E, 0x0393, 0x0393, 0xDE3B]));
        // Match twice, nearly-adjacent, first paired in center
        assert_eq!(fw([0xD83E,
                       0xDE3A, 0x0020, 0xD83D,
                       0xDE3B,
                       0xDE3A, 0x0020, 0xD83D,
                       0xDE3B])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xD83E, 0x0393, 0xDE3B, 0x0393, 0xDE3B]));
        // Match twice, nearly-adjacent, second paired in center
        assert_eq!(fw([0xD83E,
                       0xDE3A, 0x0020, 0xD83D,
                       0xD83E,
                       0xDE3A, 0x0020, 0xD83D,
                       0xDE3B])
                   .replace(fw([0xDE3A, 0x0020, 0xD83D]), fw([0x0393])),
                   fw([0xD83E, 0x0393, 0xD83E, 0x0393, 0xDE3B]));
        // Overlapping middle with previous partial match
        assert_eq!(fw([0xD83D, 0xDE3A,
                       0xD83D, 0xDE3A,
                       0xD83D, 0xDE3A,
                       0xD83D, 0xDE3A])
                   .replace(fw([0xDE3A, 0xD83D, 0xDE3A, 0xD83D, 0xDE3A, 0xD83D]),
                            fw([0x0393])),
                   fw([0xD83D, 0x0393, 0xDE3A]));
    }
}
