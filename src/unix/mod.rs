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

use slice_searcher::SliceSearcher;
use split_bytes;
use utf8_sections::{self, Utf8Sections};

use std::borrow::Cow;
use std::fmt::{self, Debug};
use std::vec::Vec;
use std::str;
use core::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher};
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

    pub fn with_capacity(capacity: usize) -> Self {
        Buf { inner: Vec::with_capacity(capacity) }
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
        String::from_utf8(self.inner).map_err(|p| Buf { inner: p.into_bytes() } )
    }

    pub fn into_string_lossy(self) -> String {
        self.into_string().unwrap_or_else(|buf| buf.as_slice().to_string_lossy().into_owned())
    }

    pub fn push_slice(&mut self, s: &Slice) {
        self.inner.extend_from_slice(&s.inner)
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

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn split_unicode<'a>(&'a self) -> SplitUnicode<'a> {
        SplitUnicode(utf8_sections::SplitUnicode::new(&self.inner))
    }

    pub fn contains_os(&self, needle: &Slice) -> bool {
        SliceSearcher::new(&self.inner, &needle.inner, true).next().is_some()
    }

    pub fn starts_with_os(&self, needle: &Slice) -> bool {
        self.inner.starts_with(&needle.inner)
    }

    pub fn ends_with_os(&self, needle: &Slice) -> bool {
        self.inner.ends_with(&needle.inner)
    }

    pub fn replace(&self, from: &Slice, to: &Slice) -> Buf {
        let mut result = Vec::new();
        let mut position = 0;
        for offset in SliceSearcher::new(&self.inner, &from.inner, false) {
            result.extend_from_slice(&self.inner[position..offset]);
            result.extend_from_slice(&to.inner);
            position = offset + from.len();
        }
        result.extend_from_slice(&self.inner[position..]);
        Buf { inner: result }
    }

    pub fn utf8_sections<'a>(&'a self) -> Utf8Sections<'a> {
        Utf8Sections::new(&self.inner)
    }

    pub fn split<'a, P>(&'a self, pat: P) -> Split<'a, P>
    where P: Pattern<'a> + Clone {
        Split { inner: split_bytes::Split::new(&self.inner, pat) }
    }

    pub fn rsplit<'a, P>(&'a self, pat: P) -> RSplit<'a, P>
    where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
        RSplit { inner: split_bytes::RSplit::new(&self.inner, pat) }
    }

    pub fn split_terminator<'a, P>(&'a self, pat: P) -> SplitTerminator<'a, P>
    where P: Pattern<'a> + Clone {
        SplitTerminator { inner: split_bytes::SplitTerminator::new(&self.inner, pat) }
    }

    pub fn rsplit_terminator<'a, P>(&'a self, pat: P) -> RSplitTerminator<'a, P>
    where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
        RSplitTerminator { inner: split_bytes::RSplitTerminator::new(&self.inner, pat) }
    }

    pub fn splitn<'a, P>(&'a self, count: usize, pat: P) -> SplitN<'a, P>
    where P: Pattern<'a> + Clone {
        SplitN { inner: split_bytes::SplitN::new(&self.inner, count, pat) }
    }

    pub fn rsplitn<'a, P>(&'a self, count: usize, pat: P) -> RSplitN<'a, P>
    where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
        RSplitN { inner: split_bytes::RSplitN::new(&self.inner, count, pat) }
    }

    pub fn matches<'a, P>(&'a self, pat: P) -> Matches<'a, P>
    where P: Pattern<'a> + Clone {
        Matches { inner: split_bytes::Matches::new(&self.inner, pat) }
    }

    pub fn rmatches<'a, P>(&'a self, pat: P) -> RMatches<'a, P>
    where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
        RMatches { inner: split_bytes::RMatches::new(&self.inner, pat) }
    }

    pub fn trim_matches<'a, P>(&'a self, pat: P) -> &'a Slice
    where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
        Self::from_u8_slice(split_bytes::trim_matches(&self.inner, pat))
    }

    pub fn trim_left_matches<'a, P>(&'a self, pat: P) -> &'a Slice
    where P: Pattern<'a> {
        Self::from_u8_slice(split_bytes::trim_left_matches(&self.inner, pat))
    }

    pub fn trim_right_matches<'a, P>(&'a self, pat: P) -> &'a Slice
    where P: Pattern<'a>, P::Searcher: ReverseSearcher<'a> {
        Self::from_u8_slice(split_bytes::trim_right_matches(&self.inner, pat))
    }
}


#[derive(Clone)]
pub enum Section<'a> {
    Unicode(&'a str),
    NonUnicode(&'a Slice),
}

impl<'a> From<utf8_sections::Section<'a>> for Section<'a> {
    fn from(x: utf8_sections::Section<'a>) -> Section<'a> {
        match x {
            utf8_sections::Section::Unicode(s) => Section::Unicode(s),
            utf8_sections::Section::NonUnicode(s) =>
                Section::NonUnicode(Slice::from_u8_slice(s)),
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

make_iterator!{Split requires Searcher is double ended
               yielding Slice::from_u8_slice => &'a Slice}
make_iterator!{RSplit requires ReverseSearcher is double ended
               yielding Slice::from_u8_slice => &'a Slice}
make_iterator!{SplitTerminator requires Searcher is double ended
               yielding Slice::from_u8_slice => &'a Slice}
make_iterator!{RSplitTerminator requires ReverseSearcher is double ended
               yielding Slice::from_u8_slice => &'a Slice}
make_iterator!{SplitN requires Searcher yielding Slice::from_u8_slice => &'a Slice}
make_iterator!{RSplitN requires ReverseSearcher yielding Slice::from_u8_slice => &'a Slice}
make_iterator!{Matches requires Searcher is double ended yielding |x| x => &'a str}
make_iterator!{RMatches requires ReverseSearcher is double ended yielding |x| x => &'a str}

pub mod os_str {
    use super::{Buf, Slice};
    mod inner { pub use super::super::*; }

    macro_rules! is_windows { () => { false } }
    macro_rules! if_unix_windows { (unix $u:block windows $w:block) => { $u } }

    include!("../os_str_def.rs");
}
pub use self::os_str::{OsStr, OsString};

pub mod os_str_ext;
pub use self::os_str_ext::{OsStrExt, OsStringExt};
