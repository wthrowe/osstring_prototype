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
}

pub mod os_str {
    use super::{Buf, Slice};

    macro_rules! is_windows { () => { false } }
    macro_rules! if_unix_windows { (unix $u:block windows $w:block) => { $u } }

    include!("../os_str_def.rs");
}
pub use self::os_str::{OsStr, OsString};

pub mod os_str_ext;
pub use self::os_str_ext::{OsStrExt, OsStringExt};
