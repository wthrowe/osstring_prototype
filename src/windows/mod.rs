// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// The underlying OsString/OsStr implementation on Windows is a
/// wrapper around the "WTF-8" encoding; see the `wtf8` module for more.

use std::borrow::Cow;
use std::fmt::{self, Debug};
use wtf8::{self, Wtf8, Wtf8Buf};
use std::string::String;
use std::result::Result;
use std::option::Option;
use std::mem;

#[derive(Clone, Hash)]
pub struct Buf {
    pub inner: Wtf8Buf
}

impl Debug for Buf {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.as_slice().fmt(formatter)
    }
}

pub struct Slice {
    pub inner: Wtf8
}

pub struct Split<'a> {
    inner: wtf8::Split<'a>
}

impl Debug for Slice {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.inner.fmt(formatter)
    }
}

impl Buf {
    pub fn from_string(s: String) -> Buf {
        Buf { inner: Wtf8Buf::from_string(s) }
    }

    pub fn as_slice(&self) -> &Slice {
        unsafe { mem::transmute(self.inner.as_slice()) }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Buf { inner: Wtf8Buf::with_capacity(capacity) }
    }

    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    pub fn into_string(self) -> Result<String, Buf> {
        self.inner.into_string().map_err(|buf| Buf { inner: buf })
    }

    pub fn into_string_lossy(self) -> String {
        self.inner.into_string_lossy()
    }

    pub fn push_slice(&mut self, s: &Slice) {
        self.inner.push_wtf8(&s.inner)
    }

    pub fn clear(&mut self) {
        self.inner.clear()
    }
}

impl Slice {
    pub fn from_str(s: &str) -> &Slice {
        Self::from_wtf8(Wtf8::from_str(s))
    }

    fn from_wtf8(s: &Wtf8) -> &Slice {
        unsafe { mem::transmute(s) }
    }

    pub fn to_str(&self) -> Option<&str> {
        self.inner.as_str()
    }

    pub fn to_string_lossy(&self) -> Cow<str> {
        self.inner.to_string_lossy()
    }

    pub fn to_owned(&self) -> Buf {
        let mut buf = Wtf8Buf::with_capacity(self.inner.len());
        buf.push_wtf8(&self.inner);
        Buf { inner: buf }
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn starts_with_str(&self, prefix: &str) -> bool {
        self.inner.starts_with_str(prefix)
    }

    pub fn remove_prefix_str(&self, prefix: &str) -> Option<&Slice> {
        self.inner.remove_prefix_str(prefix).map(|s| Self::from_wtf8(s))
    }

    pub fn slice_shift_char(&self) -> Option<(char, &Slice)> {
        self.inner.slice_shift_char().map(|(a, b)| (a, Self::from_wtf8(b)))
    }

    pub fn split_off_str(&self, boundary: char) -> Option<(&str, &Slice)> {
        self.inner.split_off_str(boundary).map(|(a, b)| (a, Self::from_wtf8(b)))
    }

    pub fn split_ascii<'a>(&'a self, boundary: u8) -> Split<'a> {
        Split {
            inner: self.inner.split_ascii(boundary)
        }
    }
}

impl<'a> Iterator for Split<'a> {
    type Item = &'a Slice;

    fn next(&mut self) -> Option<&'a Slice> {
        self.inner.next().map(Slice::from_wtf8)
    }
}

pub mod os_str {
    use super::{Buf, Slice, Split as ImplSplit};

    macro_rules! is_windows { () => { true } }
    macro_rules! if_unix_windows { (unix $u:block windows $w:block) => { $w } }

    include!("../os_str_def.rs");
}
pub use self::os_str::{OsStr, OsString};

pub mod os_str_ext;
pub use self::os_str_ext::{OsStrExt, OsStringExt};
