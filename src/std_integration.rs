use std::prelude::v1::*;
use std::borrow::Borrow;
use std::ffi;
use std::mem;
use std::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher};

use os_str;
use slice_concat_ext::LocalSliceConcatExt;

macro_rules! make_conversions {
    ($a:ty : $b:ty) => {
        impl<'a> From<$a> for $b {
            fn from(x: $a) -> $b {
                unsafe { mem::transmute(x) }
            }
        }

        impl<'a> From<$b> for $a {
            fn from(x: $b) -> $a {
                unsafe { mem::transmute(x) }
            }
        }
    }
}

make_conversions!{os_str::OsString : ffi::OsString}
make_conversions!{&'a os_str::OsString : &'a ffi::OsString}
make_conversions!{&'a mut os_str::OsString : &'a mut ffi::OsString}
make_conversions!{&'a os_str::OsStr : &'a ffi::OsStr}
make_conversions!{&'a mut os_str::OsStr : &'a mut ffi::OsStr}

pub trait OsStringPrototyping {
    fn with_capacity(capacity: usize) -> Self;
    fn capacity(&self) -> usize;
    fn into_string_lossy(self) -> String;
    fn clear(&mut self);
}

impl OsStringPrototyping for ffi::OsString {
    fn with_capacity(capacity: usize) -> Self {
        os_str::OsString::with_capacity(capacity).into()
    }
    fn capacity(&self) -> usize {
        <&os_str::OsString>::from(self).capacity()
    }
    fn into_string_lossy(self) -> String {
        <os_str::OsString>::from(self).into_string_lossy()
    }
    fn clear(&mut self) {
        <&mut os_str::OsString>::from(self).clear()
    }
}

pub trait OsStrPrototyping {
    fn is_empty(&self) -> bool;
    fn len(&self) -> usize;
    fn split_unicode<'a>(&'a self) -> SplitUnicode<'a>;
    fn split_whitespace<'a>(&'a self) -> SplitWhitespace<'a>;
    fn lines<'a>(&'a self) -> Lines<'a>;
    fn contains_os<S: AsRef<ffi::OsStr>>(&self, needle: S) -> bool;
    fn starts_with_os<S: AsRef<ffi::OsStr>>(&self, needle: S) -> bool;
    fn ends_with_os<S: AsRef<ffi::OsStr>>(&self, needle: S) -> bool;
    fn replace<T: AsRef<ffi::OsStr>, U: AsRef<ffi::OsStr>>(&self, from: T, to: U) -> ffi::OsString;
    fn contains<'a, P>(&'a self, pat: P) -> bool where P: Pattern<'a> + Clone;
    fn starts_with<'a, P>(&'a self, pat: P) -> bool where P: Pattern<'a>;
    fn ends_with<'a, P>(&'a self, pat: P) -> bool
        where P: Pattern<'a>, P::Searcher: ReverseSearcher<'a>;
    fn split<'a, P>(&'a self, pat: P) -> Split<'a, P> where P: Pattern<'a>;
    fn rsplit<'a, P>(&'a self, pat: P) -> RSplit<'a, P> where P: Pattern<'a>;
    fn split_terminator<'a, P>(&'a self, pat: P) -> SplitTerminator<'a, P> where P: Pattern<'a>;
    fn rsplit_terminator<'a, P>(&'a self, pat: P) -> RSplitTerminator<'a, P> where P: Pattern<'a>;
    fn splitn<'a, P>(&'a self, count: usize, pat: P) -> SplitN<'a, P> where P: Pattern<'a>;
    fn rsplitn<'a, P>(&'a self, count: usize, pat: P) -> RSplitN<'a, P> where P: Pattern<'a>;
    fn matches<'a, P>(&'a self, pat: P) -> Matches<'a, P> where P: Pattern<'a>;
    fn rmatches<'a, P>(&'a self, pat: P) -> RMatches<'a, P> where P: Pattern<'a>;
    fn trim(&self) -> &Self;
    fn trim_left(&self) -> &Self;
    fn trim_right(&self) -> &Self;
    fn trim_matches<'a, P>(&'a self, pat: P) -> &'a Self
    where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a>;
    fn trim_left_matches<'a, P>(&'a self, pat: P) -> &Self where P: Pattern<'a>;
    fn trim_right_matches<'a, P>(&'a self, pat: P) -> &Self
    where P: Pattern<'a>, P::Searcher: ReverseSearcher<'a>;
}

impl OsStrPrototyping for ffi::OsStr {
    fn is_empty(&self) -> bool {
        <&os_str::OsStr>::from(self).is_empty()
    }
    fn len(&self) -> usize {
        <&os_str::OsStr>::from(self).len()
    }
    fn split_unicode<'a>(&'a self) -> SplitUnicode<'a> {
        <&os_str::OsStr>::from(self).split_unicode().into()
    }
    fn split_whitespace<'a>(&'a self) -> SplitWhitespace<'a> {
        <&os_str::OsStr>::from(self).split_whitespace().into()
    }
    fn lines<'a>(&'a self) -> Lines<'a> {
        <&os_str::OsStr>::from(self).lines().into()
    }
    fn contains_os<S: AsRef<ffi::OsStr>>(&self, needle: S) -> bool {
        <&os_str::OsStr>::from(self).contains_os(<&os_str::OsStr>::from(needle.as_ref()))
    }
    fn starts_with_os<S: AsRef<ffi::OsStr>>(&self, needle: S) -> bool {
        <&os_str::OsStr>::from(self).starts_with_os(<&os_str::OsStr>::from(needle.as_ref()))
    }
    fn ends_with_os<S: AsRef<ffi::OsStr>>(&self, needle: S) -> bool {
        <&os_str::OsStr>::from(self).ends_with_os(<&os_str::OsStr>::from(needle.as_ref()))
    }
    fn replace<T: AsRef<ffi::OsStr>, U: AsRef<ffi::OsStr>>(&self, from: T, to: U) -> ffi::OsString {
        let from: &os_str::OsStr = from.as_ref().into();
        let to: &os_str::OsStr = to.as_ref().into();
        <&os_str::OsStr>::from(self).replace(from, to).into()
    }
    fn contains<'a, P>(&'a self, pat: P) -> bool where P: Pattern<'a> + Clone {
        <&os_str::OsStr>::from(self).contains(pat)
    }
    fn starts_with<'a, P>(&'a self, pat: P) -> bool where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).starts_with(pat)
    }
    fn ends_with<'a, P>(&'a self, pat: P) -> bool
        where P: Pattern<'a>, P::Searcher: ReverseSearcher<'a> {
        <&os_str::OsStr>::from(self).ends_with(pat)
    }
    fn split<'a, P>(&'a self, pat: P) -> Split<'a, P> where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).split(pat).into()
    }
    fn rsplit<'a, P>(&'a self, pat: P) -> RSplit<'a, P> where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).rsplit(pat).into()
    }
    fn split_terminator<'a, P>(&'a self, pat: P) -> SplitTerminator<'a, P> where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).split_terminator(pat).into()
    }
    fn rsplit_terminator<'a, P>(&'a self, pat: P) -> RSplitTerminator<'a, P> where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).rsplit_terminator(pat).into()
    }
    fn splitn<'a, P>(&'a self, count: usize, pat: P) -> SplitN<'a, P> where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).splitn(count, pat).into()
    }
    fn rsplitn<'a, P>(&'a self, count: usize, pat: P) -> RSplitN<'a, P> where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).rsplitn(count, pat).into()
    }
    fn matches<'a, P>(&'a self, pat: P) -> Matches<'a, P> where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).matches(pat).into()
    }
    fn rmatches<'a, P>(&'a self, pat: P) -> RMatches<'a, P> where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).rmatches(pat).into()
    }
    fn trim(&self) -> &Self {
        <&os_str::OsStr>::from(self).trim().into()
    }
    fn trim_left(&self) -> &Self {
        <&os_str::OsStr>::from(self).trim_left().into()
    }
    fn trim_right(&self) -> &Self {
        <&os_str::OsStr>::from(self).trim_right().into()
    }
    fn trim_matches<'a, P>(&'a self, pat: P) -> &'a Self
    where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
        <&os_str::OsStr>::from(self).trim_matches(pat).into()
    }
    fn trim_left_matches<'a, P>(&'a self, pat: P) -> &Self where P: Pattern<'a> {
        <&os_str::OsStr>::from(self).trim_left_matches(pat).into()
    }
    fn trim_right_matches<'a, P>(&'a self, pat: P) -> &Self
    where P: Pattern<'a>, P::Searcher: ReverseSearcher<'a> {
        <&os_str::OsStr>::from(self).trim_right_matches(pat).into()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OsStrSection<'a> {
    Unicode(&'a str),
    NonUnicode(&'a ffi::OsStr),
}

impl<'a> From<os_str::OsStrSection<'a>> for OsStrSection<'a> {
    fn from(x: os_str::OsStrSection<'a>) -> OsStrSection<'a> {
        match x {
            os_str::OsStrSection::Unicode(s) => OsStrSection::Unicode(s),
            os_str::OsStrSection::NonUnicode(s) => OsStrSection::NonUnicode(s.into()),
        }
    }
}

#[derive(Clone)]
pub struct SplitUnicode<'a>(os_str::SplitUnicode<'a>);

impl<'a> From<os_str::SplitUnicode<'a>> for SplitUnicode<'a> {
    fn from(x: os_str::SplitUnicode<'a>) -> SplitUnicode<'a> {
        SplitUnicode(x)
    }
}

impl<'a> Iterator for SplitUnicode<'a> {
    type Item = OsStrSection<'a>;

    fn next(&mut self) -> Option<OsStrSection<'a>> {
        self.0.next().map(|x| x.into())
    }
}

impl<'a> DoubleEndedIterator for SplitUnicode<'a> {
    fn next_back(&mut self) -> Option<OsStrSection<'a>> {
        self.0.next_back().map(|x| x.into())
    }
}


macro_rules! forward_iterator_simple {
    ($name:ident) => {
        #[derive(Clone)]
        pub struct $name<'a> {
            inner: os_str::$name<'a>
        }

        impl<'a> From<os_str::$name<'a>> for $name<'a> {
            fn from(x: os_str::$name<'a>) -> $name<'a> {
                $name { inner: x }
            }
        }

        impl<'a> Iterator for $name<'a> {
            type Item = &'a ffi::OsStr;

            fn next(&mut self) -> Option<&'a ffi::OsStr> {
                self.inner.next().map(|x| x.into())
            }
        }

        impl<'a> DoubleEndedIterator for $name<'a> {
            fn next_back(&mut self) -> Option<&'a ffi::OsStr> {
                self.inner.next_back().map(|x| x.into())
            }
        }
    }
}
macro_rules! forward_iterator {
    ($forward:ident and $reverse:ident) => {
        pub struct $forward<'a, P> where P: Pattern<'a> {
            inner: os_str::$forward<'a, P>
        }

        impl<'a, P> Clone for $forward<'a, P> where P: Pattern<'a> + Clone, P::Searcher: Clone {
            fn clone(&self) -> Self { $forward { inner: self.inner.clone() } }
        }

        impl<'a, P> From<os_str::$forward<'a, P>> for $forward<'a, P> where P: Pattern<'a> {
            fn from(x: os_str::$forward<'a, P>) -> $forward<'a, P> {
                $forward { inner: x }
            }
        }

        impl<'a, P> Iterator for $forward<'a, P> where P: Pattern<'a> + Clone {
            type Item = &'a ffi::OsStr;

            fn next(&mut self) -> Option<&'a ffi::OsStr> {
                self.inner.next().map(|x| x.into())
            }
        }

        pub struct $reverse<'a, P> where P: Pattern<'a> {
            inner: os_str::$reverse<'a, P>
        }

        impl<'a, P> Clone for $reverse<'a, P> where P: Pattern<'a> + Clone, P::Searcher: Clone {
            fn clone(&self) -> Self { $reverse { inner: self.inner.clone() } }
        }

        impl<'a, P> From<os_str::$reverse<'a, P>> for $reverse<'a, P> where P: Pattern<'a> {
            fn from(x: os_str::$reverse<'a, P>) -> $reverse<'a, P> {
                $reverse { inner: x }
            }
        }

        impl<'a, P> Iterator for $reverse<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
            type Item = &'a ffi::OsStr;

            fn next(&mut self) -> Option<&'a ffi::OsStr> {
                self.inner.next().map(|x| x.into())
            }
        }
    }
}
macro_rules! forward_double_ended {
    ($forward:ident and $reverse:ident) => {
        forward_iterator!{$forward and $reverse}

        impl<'a, P> DoubleEndedIterator for $forward<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
            fn next_back(&mut self) -> Option<&'a ffi::OsStr> {
                self.inner.next_back().map(|x| x.into())
            }
        }

        impl<'a, P> DoubleEndedIterator for $reverse<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
            fn next_back(&mut self) -> Option<&'a ffi::OsStr> {
                self.inner.next_back().map(|x| x.into())
            }
        }
    }
}

forward_iterator_simple!{SplitWhitespace}
forward_iterator_simple!{Lines}
forward_double_ended!{Split and RSplit}
forward_double_ended!{SplitTerminator and RSplitTerminator}
forward_iterator!{SplitN and RSplitN}
pub use os_str::{Matches, RMatches};


impl<S: Borrow<ffi::OsStr>> LocalSliceConcatExt<ffi::OsStr> for [S] {
    type Output = ffi::OsString;

    fn concat(&self) -> Self::Output {
        self.iter().map(|s| <&os_str::OsStr>::from(s.borrow())).collect::<Vec<_>>().concat().into()
    }
    fn join(&self, sep: &ffi::OsStr) -> Self::Output {
        self.iter().map(|s| <&os_str::OsStr>::from(s.borrow())).collect::<Vec<_>>().join(<&os_str::OsStr>::from(sep.borrow())).into()
    }
    fn connect(&self, sep: &ffi::OsStr) -> Self::Output {
        self.join(sep)
    }
}


#[cfg(test)]
mod tests {
    use std::prelude::v1::*;
    use prelude::*;
    use std::ffi::{OsStr, OsString};

    #[test]
    fn osstring() {
        assert!(OsString::with_capacity(10).capacity() >= 10);
        let string = OsString::from("hello");
        assert_eq!(string.into_string_lossy(), "hello");
        let mut string = OsString::from("hello");
        string.clear();
        assert_eq!(string, OsString::from(""));
    }

    #[test]
    fn osstr() {
        let string = OsString::from("hello");
        assert!(!string.is_empty());
        assert_eq!(string.len(), 5);
        assert_eq!(string.split_unicode().next(), Some(OsStrSection::Unicode("hello")));
        assert_eq!(OsStr::new("\nHello  World").split_whitespace().collect::<Vec<_>>(),
                   [OsStr::new("Hello"), OsStr::new("World")]);
        assert_eq!(OsStr::new("\nHello\n  World").lines().collect::<Vec<_>>(),
                   [OsStr::new(""), OsStr::new("Hello"), OsStr::new("  World")]);
        assert!(string.contains_os(OsStr::new("ll")));
        assert!(string.starts_with_os(OsStr::new("he")));
        assert!(string.ends_with_os(OsStr::new("lo")));
        assert_eq!(string.replace(OsStr::new("e"), OsStr::new("a")), OsString::from("hallo"));
        assert!(string.contains("ll"));
        assert!(string.starts_with("he"));
        assert!(string.ends_with("lo"));
        assert_eq!(string.split('l').collect::<Vec<_>>(),
                   [OsStr::new("he"), OsStr::new(""), OsStr::new("o")]);
        assert_eq!(string.rsplit('l').collect::<Vec<_>>(),
                   [OsStr::new("o"), OsStr::new(""), OsStr::new("he")]);
        assert_eq!(string.split_terminator('o').collect::<Vec<_>>(),
                   [OsStr::new("hell")]);
        assert_eq!(string.rsplit_terminator('o').collect::<Vec<_>>(),
                   [OsStr::new("hell")]);
        assert_eq!(string.splitn(2, 'l').collect::<Vec<_>>(),
                   [OsStr::new("he"), OsStr::new("lo")]);
        assert_eq!(string.rsplitn(2, 'l').collect::<Vec<_>>(),
                   [OsStr::new("o"), OsStr::new("hel")]);
        assert_eq!(string.matches('l').collect::<Vec<_>>(), ["l"; 2]);
        assert_eq!(string.rmatches('l').collect::<Vec<_>>(), ["l"; 2]);
        assert_eq!(OsStr::new(" \nHello World ").trim(), OsStr::new("Hello World"));
        assert_eq!(OsStr::new(" \nHello World ").trim_left(), OsStr::new("Hello World "));
        assert_eq!(OsStr::new(" \nHello World ").trim_right(), OsStr::new(" \nHello World"));
        assert_eq!(OsStr::new("aabcaa").trim_matches('a'), OsStr::new("bc"));
        assert_eq!(OsStr::new("aabcaa").trim_left_matches('a'), OsStr::new("bcaa"));
        assert_eq!(OsStr::new("aabcaa").trim_right_matches('a'), OsStr::new("aabc"));
    }

    #[test]
    fn slice_concat_ext() {
        assert_eq!([OsStr::new("Hello"), OsStr::new("world")].concat(),
                   OsString::from("Helloworld"));
        assert_eq!([OsStr::new("Hello"), OsStr::new("world")].join(OsStr::new(" ")),
                   OsString::from("Hello world"));
    }
}
