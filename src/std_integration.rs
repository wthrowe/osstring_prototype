use std::prelude::v1::*;
use std::borrow::Borrow;
use std::ffi;
use std::mem;
use std::str::pattern::{Pattern, ReverseSearcher};

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
    fn contains_os<S: AsRef<ffi::OsStr>>(&self, needle: S) -> bool;
    fn starts_with_os<S: AsRef<ffi::OsStr>>(&self, needle: S) -> bool;
    fn ends_with_os<S: AsRef<ffi::OsStr>>(&self, needle: S) -> bool;
    fn contains<'a, P>(&'a self, pat: P) -> bool where P: Pattern<'a> + Clone;
    fn starts_with<'a, P>(&'a self, pat: P) -> bool where P: Pattern<'a>;
    fn ends_with<'a, P>(&'a self, pat: P) -> bool
        where P: Pattern<'a>, P::Searcher: ReverseSearcher<'a>;
    fn starts_with_str(&self, prefix: &str) -> bool;
    fn remove_prefix_str(&self, prefix: &str) -> Option<&Self>;
    fn slice_shift_char(&self) -> Option<(char, &Self)>;
    fn split_off_str(&self, boundary: char) -> Option<(&str, &Self)>;
    fn split<'a>(&'a self, boundary: char) -> Split<'a>;
}

impl OsStrPrototyping for ffi::OsStr {
    fn is_empty(&self) -> bool {
        <&os_str::OsStr>::from(self).is_empty()
    }
    fn len(&self) -> usize {
        <&os_str::OsStr>::from(self).len()
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
    fn starts_with_str(&self, prefix: &str) -> bool {
        <&os_str::OsStr>::from(self).starts_with_str(prefix)
    }
    fn remove_prefix_str(&self, prefix: &str) -> Option<&Self> {
        <&os_str::OsStr>::from(self).remove_prefix_str(prefix).map(|x| x.into())
    }
    fn slice_shift_char(&self) -> Option<(char, &Self)> {
        <&os_str::OsStr>::from(self).slice_shift_char().map(|(a, b)| (a, b.into()))
    }
    fn split_off_str(&self, boundary: char) -> Option<(&str, &Self)> {
        <&os_str::OsStr>::from(self).split_off_str(boundary).map(|(a, b)| (a, b.into()))
    }
    fn split<'a>(&'a self, boundary: char) -> Split<'a> {
        <&'a os_str::OsStr>::from(self).split(boundary).into()
    }
}

pub struct Split<'a> {
    inner: os_str::Split<'a>
}

impl<'a> From<os_str::Split<'a>> for Split<'a> {
    fn from(x: os_str::Split<'a>) -> Split<'a> {
        Split { inner: x }
    }
}

impl<'a> Iterator for Split<'a> {
    type Item = &'a ffi::OsStr;

    fn next(&mut self) -> Option<&'a ffi::OsStr> {
        self.inner.next().map(|x| x.into())
    }
}

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
        assert!(string.contains_os(OsStr::new("ll")));
        assert!(string.starts_with_os(OsStr::new("he")));
        assert!(string.ends_with_os(OsStr::new("lo")));
        assert!(string.contains("ll"));
        assert!(string.starts_with("he"));
        assert!(string.ends_with("lo"));
        assert!(string.starts_with_str("he"));
        assert_eq!(string.remove_prefix_str("he"), Some(OsStr::new("llo")));
        assert_eq!(string.slice_shift_char(), Some(('h', OsStr::new("ello"))));
        assert_eq!(string.split_off_str('l'), Some(("he", OsStr::new("lo"))));
        assert_eq!(string.split('l').collect::<Vec<&OsStr>>(),
                   [OsStr::new("he"), OsStr::new(""), OsStr::new("o")]);
    }

    #[test]
    fn slice_concat_ext() {
        assert_eq!([OsStr::new("Hello"), OsStr::new("world")].concat(),
                   OsString::from("Helloworld"));
        assert_eq!([OsStr::new("Hello"), OsStr::new("world")].join(OsStr::new(" ")),
                   OsString::from("Hello world"));
    }
}
