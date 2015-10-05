use std::prelude::v1::*;
use std::ffi;
use std::mem;

use os_str;

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
    fn into_string_lossy(self) -> String;
    fn clear(&mut self);
}

impl OsStringPrototyping for ffi::OsString {
    fn into_string_lossy(self) -> String {
        <os_str::OsString>::from(self).into_string_lossy()
    }
    fn clear(&mut self) {
        <&mut os_str::OsString>::from(self).clear()
    }
}

pub trait OsStrPrototyping {
    fn is_empty(&self) -> bool;
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

#[cfg(test)]
mod tests {
    use std::prelude::v1::*;
    use std::ffi::{OsStr, OsString};
    use super::{OsStrPrototyping, OsStringPrototyping};

    #[test]
    fn osstring() {
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
        assert!(string.starts_with_str("he"));
        assert_eq!(string.remove_prefix_str("he"), Some(OsStr::new("llo")));
        assert_eq!(string.slice_shift_char(), Some(('h', OsStr::new("ello"))));
        assert_eq!(string.split_off_str('l'), Some(("he", OsStr::new("lo"))));
        assert_eq!(string.split('l').collect::<Vec<&OsStr>>(),
                   [OsStr::new("he"), OsStr::new(""), OsStr::new("o")]);
    }
}
