// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// The underlying OsString/OsStr implementation on Unix systems: just
/// a `Vec<u8>`/`[u8]`.

use std::borrow::Cow;
use std::fmt::{self, Debug};
use std::vec::Vec;
use std::str;
use std::string::String;
use std::mem;

#[derive(Clone, Hash)]
pub struct Buf {
    pub inner: Vec<u8>
}

pub struct Slice {
    pub inner: [u8]
}

pub struct Split<'a> {
    slice: &'a Slice,
    boundary: u8,
    position: usize,
}

impl Debug for Slice {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.to_string_lossy().fmt(formatter)
    }
}

impl Debug for Buf {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.as_slice().fmt(formatter)
    }
}

impl Buf {
    pub fn from_string(s: String) -> Buf {
        Buf { inner: s.into_bytes() }
    }

    pub fn as_slice(&self) -> &Slice {
        unsafe { mem::transmute(&*self.inner) }
    }

    pub fn into_string(self) -> Result<String, Buf> {
        String::from_utf8(self.inner).map_err(|p| Buf { inner: p.into_bytes() } )
    }

    pub fn into_string_lossy(self) -> String {
        self.into_string().unwrap_or_else(|buf| buf.as_slice().to_string_lossy().into_owned())
    }

    pub fn push_slice(&mut self, s: &Slice) {
        self.inner.push_all(&s.inner)
    }

    pub fn clear(&mut self) {
        self.inner.clear()
    }
}

impl Slice {
    fn from_u8_slice(s: &[u8]) -> &Slice {
        unsafe { mem::transmute(s) }
    }

    pub fn from_str(s: &str) -> &Slice {
        Slice::from_u8_slice(s.as_bytes())
    }

    pub fn to_str(&self) -> Option<&str> {
        str::from_utf8(&self.inner).ok()
    }

    pub fn to_string_lossy(&self) -> Cow<str> {
        String::from_utf8_lossy(&self.inner)
    }

    pub fn to_owned(&self) -> Buf {
        Buf { inner: self.inner.to_vec() }
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn starts_with_str(&self, prefix: &str) -> bool {
        self.inner.starts_with(prefix.as_bytes())
    }

    pub fn remove_prefix_str(&self, prefix: &str) -> Option<&Slice> {
        if self.inner.starts_with(prefix.as_bytes()) {
            Some(Self::from_u8_slice(&self.inner[prefix.len()..]))
        } else {
            None
        }
    }

    pub fn slice_shift_char(&self) -> Option<(char, &Slice)> {
        let utf8_prefix = match str::from_utf8(&self.inner) {
            Ok(s) => s,
            Err(e) => str::from_utf8(&self.inner[0..e.valid_up_to()]).unwrap()
        };
        utf8_prefix.chars().next()
            .map(|first|
                 (first, Self::from_u8_slice(&self.inner[first.len_utf8()..])))
    }

    pub fn split_off_str(&self, boundary: char) -> Option<(&str, &Slice)> {
        let utf8_prefix = match str::from_utf8(&self.inner) {
            Ok(s) => s,
            Err(e) => str::from_utf8(&self.inner[0..e.valid_up_to()]).unwrap()
        };
        utf8_prefix.find(boundary)
            .map(|b| (&utf8_prefix[0..b],
                      Self::from_u8_slice(&self.inner[b + boundary.len_utf8()..])))
    }

    pub fn split_ascii<'a>(&'a self, boundary: u8) -> Split<'a> {
        Split {
            slice: self,
            boundary: boundary,
            position: 0,
        }
    }
}

impl<'a> Iterator for Split<'a> {
    type Item = &'a Slice;

    fn next(&mut self) -> Option<&'a Slice> {
        // Using slice::split would make more sense here, but the
        // iterator returned by that is unnamable, so it can't be
        // stored directly in a struct.
        let start = self.position;
        if start > self.slice.inner.len() { return None; }

        let length = self.slice.inner[start..].iter().position(|&b| b == self.boundary);
        match length {
            Some(length) => {
                self.position += length + 1;
                Some(Slice::from_u8_slice(&self.slice.inner[start..start + length]))
            },
            None => {
                self.position = self.slice.inner.len() + 1;
                Some(Slice::from_u8_slice(&self.slice.inner[start..]))
            }
        }
    }
}

pub mod os_str {
    use super::{Buf, Slice, Split as ImplSplit};

    macro_rules! is_windows { () => { false } }
    macro_rules! if_unix_windows { (unix $u:block windows $w:block) => { $u } }

    include!("../os_str_def.rs");
}
pub use self::os_str::{OsStr, OsString};

pub mod os_str_ext;
pub use self::os_str_ext::{OsStrExt, OsStringExt};
