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

use utf8_sections::Utf8Sections;

use std::borrow::Cow;
use std::fmt::{self, Debug};
use wtf8::{self, Wtf8, Wtf8Buf};
use core::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher};
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

    pub fn contains_os(&self, needle: &Slice) -> bool {
        self.inner.contains_wtf8(&needle.inner)
    }

    pub fn starts_with_os(&self, needle: &Slice) -> bool {
        self.inner.starts_with_wtf8(&needle.inner)
    }

    pub fn ends_with_os(&self, needle: &Slice) -> bool {
        self.inner.ends_with_wtf8(&needle.inner)
    }

    pub fn replace(&self, from: &Slice, to: &Slice) -> Buf {
        Buf { inner: self.inner.replace(&from.inner, &to.inner) }
    }

    pub fn utf8_sections<'a>(&'a self) -> Utf8Sections<'a> {
        self.inner.utf8_sections()
    }

    pub fn split<'a, P>(&'a self, pat: P) -> Split<'a, P> where P: Pattern<'a> {
        Split { inner: self.inner.split(pat) }
    }

    pub fn rsplit<'a, P>(&'a self, pat: P) -> RSplit<'a, P> where P: Pattern<'a> {
        RSplit { inner: self.inner.rsplit(pat) }
    }

    pub fn split_terminator<'a, P>(&'a self, pat: P) -> SplitTerminator<'a, P>
    where P: Pattern<'a> {
        SplitTerminator { inner: self.inner.split_terminator(pat) }
    }

    pub fn rsplit_terminator<'a, P>(&'a self, pat: P) -> RSplitTerminator<'a, P>
    where P: Pattern<'a> {
        RSplitTerminator { inner: self.inner.rsplit_terminator(pat) }
    }

    pub fn splitn<'a, P>(&'a self, count: usize, pat: P) -> SplitN<'a, P> where P: Pattern<'a> {
        SplitN { inner: self.inner.splitn(count, pat) }
    }

    pub fn rsplitn<'a, P>(&'a self, count: usize, pat: P) -> RSplitN<'a, P> where P: Pattern<'a> {
        RSplitN { inner: self.inner.rsplitn(count, pat) }
    }

    pub fn matches<'a, P>(&'a self, pat: P) -> Matches<'a, P> where P: Pattern<'a> {
        Matches { inner: self.inner.matches(pat) }
    }

    pub fn rmatches<'a, P>(&'a self, pat: P) -> RMatches<'a, P> where P: Pattern<'a> {
        RMatches { inner: self.inner.rmatches(pat) }
    }

    pub fn trim_matches<'a, P>(&'a self, pat: P) -> &'a Slice
    where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
        Self::from_wtf8(self.inner.trim_matches(pat))
    }

    pub fn trim_left_matches<'a, P>(&'a self, pat: P) -> &'a Slice
    where P: Pattern<'a> {
        Self::from_wtf8(self.inner.trim_left_matches(pat))
    }

    pub fn trim_right_matches<'a, P>(&'a self, pat: P) -> &'a Slice
    where P: Pattern<'a>, P::Searcher: ReverseSearcher<'a> {
        Self::from_wtf8(self.inner.trim_right_matches(pat))
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
}

macro_rules! make_iterator {
    ($name:ident requires $bound:ident yielding $map:expr => $ret:ty) => {
        pub struct $name<'a, P> where P: Pattern<'a> {
            inner: wtf8::$name<'a, P>,
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

make_iterator!{Split requires Searcher is double ended
               yielding Slice::from_wtf8 => &'a Slice}
make_iterator!{RSplit requires ReverseSearcher is double ended
               yielding Slice::from_wtf8 => &'a Slice}
make_iterator!{SplitTerminator requires Searcher is double ended
               yielding Slice::from_wtf8 => &'a Slice}
make_iterator!{RSplitTerminator requires ReverseSearcher is double ended
               yielding Slice::from_wtf8 => &'a Slice}
make_iterator!{SplitN requires Searcher yielding Slice::from_wtf8 => &'a Slice}
make_iterator!{RSplitN requires ReverseSearcher yielding Slice::from_wtf8 => &'a Slice}
make_iterator!{Matches requires Searcher is double ended yielding |x| x => &'a str}
make_iterator!{RMatches requires ReverseSearcher is double ended yielding |x| x => &'a str}

pub mod os_str {
    use super::{Buf, Slice};
    mod inner { pub use super::super::*; }

    macro_rules! is_windows { () => { true } }
    macro_rules! if_unix_windows { (unix $u:block windows $w:block) => { $w } }

    include!("../os_str_def.rs");
}
pub use self::os_str::{OsStr, OsString};

pub mod os_str_ext;
pub use self::os_str_ext::{OsStrExt, OsStringExt};
