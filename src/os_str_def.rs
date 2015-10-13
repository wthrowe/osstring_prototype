// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


// This file isn't compiled normally, but is included into the two
// OS-specific os_str modules.


// Inner comments aren't valid in an include.
// //! A type that can represent all platform-native strings, but is cheaply
// //! interconvertable with Rust strings.
// //!
// //! The need for this type arises from the fact that:
// //!
// //! * On Unix systems, strings are often arbitrary sequences of non-zero
// //!   bytes, in many cases interpreted as UTF-8.
// //!
// //! * On Windows, strings are often arbitrary sequences of non-zero 16-bit
// //!   values, interpreted as UTF-16 when it is valid to do so.
// //!
// //! * In Rust, strings are always valid UTF-8, but may contain zeros.
// //!
// //! The types in this module bridge this gap by simultaneously representing Rust
// //! and platform-native string values, and in particular allowing a Rust string
// //! to be converted into an "OS" string with no cost.
// //!
// //! **Note**: At the moment, these types are extremely bare-bones, usable only
// //! for conversion to/from various other string types. Eventually these types
// //! will offer a full-fledged string API.

use core::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher};

use std::borrow::{Borrow, Cow, ToOwned};
use std::ffi::CString;
use std::fmt::{self, Debug};
use std::mem;
use slice_concat_ext::LocalSliceConcatExt;
use std::string::String;
use std::ops;
use std::cmp;
use std::hash::{Hash, Hasher};
use std::vec::Vec;

// #[cfg(unix)]
// use unix::{Buf, Slice, Split as ImplSplit, RSplit as ImplRSplit};
// #[cfg(windows)]
// use windows::{Buf, Slice, Split as ImplSplit, RSplit as ImplRSplit};
use sys_common::{AsInner, IntoInner, FromInner};

/// Owned, mutable OS strings.
#[derive(Clone)]
pub struct OsString {
    inner: Buf
}

/// Slices into OS strings.
pub struct OsStr {
    inner: Slice
}

impl OsString {
    /// Constructs a new empty `OsString`.
    pub fn new() -> OsString {
        OsString { inner: Buf::from_string(String::new()) }
    }

    /// Constructs an `OsString` from a byte sequence.
    ///
    /// # Platform behavior
    ///
    /// On Unix systems, any byte sequence can be successfully
    /// converted into an `OsString`.
    ///
    /// On Windows system, only UTF-8 byte sequences will successfully
    /// convert; non UTF-8 data will produce `None`.
    pub fn from_bytes<B>(bytes: B) -> Option<OsString> where B: Into<Vec<u8>> {
        Self::_from_bytes(bytes.into())
    }

    fn _from_bytes(vec: Vec<u8>) -> Option<OsString> {
        if_unix_windows! {
            unix {
                use unix::OsStringExt;
                Some(OsString::from_vec(vec))
            }
            windows {
                String::from_utf8(vec).ok().map(OsString::from)
            }
        }
    }

    /// Creates a new `OsString` with the given capacity. The string will be able
    /// to hold exactly `capacity` bytes without reallocating. If `capacity` is 0,
    /// the string will not allocate.
    ///
    /// See main `OsString` documentation information about encoding.
    pub fn with_capacity(capacity: usize) -> Self {
        OsString { inner: Buf::with_capacity(capacity) }
    }

    /// Returns the number of bytes this `OsString` can hold without reallocating.
    ///
    /// See `OsString` introduction for information about encoding.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Reserves capacity for at least `additional` more bytes to be inserted in the
    /// given `OsString`. The collection may reserve more space to avoid frequent
    /// reallocations.
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Reserves the minimum capacity for exactly `additional` more bytes to be
    /// inserted in the given `OsString`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore capacity can not be relied upon to be precisely
    /// minimal. Prefer reserve if future insertions are expected.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    /// Converts to an `OsStr` slice.
    pub fn as_os_str(&self) -> &OsStr {
        self
    }

    /// Converts the `OsString` into a `String` if it contains valid Unicode data.
    ///
    /// On failure, ownership of the original `OsString` is returned.
    pub fn into_string(self) -> Result<String, OsString> {
        self.inner.into_string().map_err(|buf| OsString { inner: buf} )
    }

    /// Converts an `OsString` into a `String`, avoiding a copy if possible.
    ///
    /// Any non-Unicode sequences are replaced with U+FFFD REPLACEMENT CHARACTER.
    pub fn into_string_lossy(self) -> String {
        self.inner.into_string_lossy()
    }

    /// Extends the string with the given `&OsStr` slice.
    pub fn push<T: AsRef<OsStr>>(&mut self, s: T) {
        self.inner.push_slice(&s.as_ref().inner)
    }

    /// Truncates `self` to zero length.
    pub fn clear(&mut self) {
        self.inner.clear()
    }
}

impl From<String> for OsString {
    fn from(s: String) -> OsString {
        OsString { inner: Buf::from_string(s) }
    }
}

impl<'a, T: ?Sized + AsRef<OsStr>> From<&'a T> for OsString {
    fn from(s: &'a T) -> OsString {
        s.as_ref().to_os_string()
    }
}

impl ops::Index<ops::RangeFull> for OsString {
    type Output = OsStr;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &OsStr {
        OsStr::from_inner(self.inner.as_slice())
    }
}

impl ops::Deref for OsString {
    type Target = OsStr;

    #[inline]
    fn deref(&self) -> &OsStr {
        &self[..]
    }
}

impl Debug for OsString {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::Debug::fmt(&**self, formatter)
    }
}

impl PartialEq for OsString {
    fn eq(&self, other: &OsString) -> bool {
        &**self == &**other
    }
}

impl PartialEq<str> for OsString {
    fn eq(&self, other: &str) -> bool {
        &**self == other
    }
}

impl PartialEq<OsString> for str {
    fn eq(&self, other: &OsString) -> bool {
        &**other == self
    }
}

impl Eq for OsString {}

impl PartialOrd for OsString {
    #[inline]
    fn partial_cmp(&self, other: &OsString) -> Option<cmp::Ordering> {
        (&**self).partial_cmp(&**other)
    }
    #[inline]
    fn lt(&self, other: &OsString) -> bool { &**self < &**other }
    #[inline]
    fn le(&self, other: &OsString) -> bool { &**self <= &**other }
    #[inline]
    fn gt(&self, other: &OsString) -> bool { &**self > &**other }
    #[inline]
    fn ge(&self, other: &OsString) -> bool { &**self >= &**other }
}

impl PartialOrd<str> for OsString {
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<cmp::Ordering> {
        (&**self).partial_cmp(other)
    }
}

impl Ord for OsString {
    #[inline]
    fn cmp(&self, other: &OsString) -> cmp::Ordering {
        (&**self).cmp(&**other)
    }
}

impl Hash for OsString {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&**self).hash(state)
    }
}

impl OsStr {
    /// Coerces into an `OsStr` slice.
    pub fn new<S: AsRef<OsStr> + ?Sized>(s: &S) -> &OsStr {
        s.as_ref()
    }

    fn from_inner(inner: &Slice) -> &OsStr {
        unsafe { mem::transmute(inner) }
    }

    /// Checks whether `self` is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the number of bytes in this string.
    ///
    /// See `OsStr` introduction for information about encoding.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Yields a `&str` slice if the `OsStr` is valid unicode.
    ///
    /// This conversion may entail doing a check for UTF-8 validity.
    pub fn to_str(&self) -> Option<&str> {
        self.inner.to_str()
    }

    /// Converts an `OsStr` to a `Cow<str>`.
    ///
    /// Any non-Unicode sequences are replaced with U+FFFD REPLACEMENT CHARACTER.
    pub fn to_string_lossy(&self) -> Cow<str> {
        self.inner.to_string_lossy()
    }

    /// Copies the slice into an owned `OsString`.
    pub fn to_os_string(&self) -> OsString {
        OsString { inner: self.inner.to_owned() }
    }

    /// Yields this `OsStr` as a byte slice.
    ///
    /// # Platform behavior
    ///
    /// On Unix systems, this is a no-op.
    ///
    /// On Windows systems, this returns `None` unless the `OsStr` is
    /// valid unicode, in which case it produces UTF-8-encoded
    /// data. This may entail checking validity.
    pub fn to_bytes(&self) -> Option<&[u8]> {
        if is_windows!() {
            self.to_str().map(|s| s.as_bytes())
        } else {
            Some(self.bytes())
        }
    }

    /// Creates a `CString` containing this `OsStr` data.
    ///
    /// Fails if the `OsStr` contains interior nulls.
    ///
    /// This is a convenience for creating a `CString` from
    /// `self.to_bytes()`, and inherits the platform behavior of the
    /// `to_bytes` method.
    pub fn to_cstring(&self) -> Option<CString> {
        self.to_bytes().and_then(|b| CString::new(b).ok())
    }

    /// Gets the underlying byte representation.
    ///
    /// Note: it is *crucial* that this API is private, to avoid
    /// revealing the internal, platform-specific encodings.
    fn bytes(&self) -> &[u8] {
        unsafe { mem::transmute(&self.inner) }
    }

    /// Returns true if `needle` is a substring of `self`.
    pub fn contains_os<S: AsRef<OsStr>>(&self, needle: S) -> bool {
        self.inner.contains_os(&needle.as_ref().inner)
    }

    /// Returns true if `needle` is a prefix of `self`.
    pub fn starts_with_os<S: AsRef<OsStr>>(&self, needle: S) -> bool {
        self.inner.starts_with_os(&needle.as_ref().inner)
    }

    /// Returns true if `needle` is a suffix of `self`.
    pub fn ends_with_os<S: AsRef<OsStr>>(&self, needle: S) -> bool {
        self.inner.ends_with_os(&needle.as_ref().inner)
    }

    /// Returns true if `self` matches `pat`.
    ///
    /// Note that patterns can only match UTF-8 sections of the `OsStr`.
    pub fn contains<'a, P>(&'a self, pat: P) -> bool where P: Pattern<'a> + Clone {
        self.inner.utf8_sections().any(|s| s.1.contains(pat.clone()))
    }

    /// Returns true if the beginning of `self` matches `pat`.
    ///
    /// Note that patterns can only match UTF-8 sections of the `OsStr`.
    pub fn starts_with<'a, P>(&'a self, pat: P) -> bool where P: Pattern<'a> {
        self.inner.utf8_sections().next().unwrap().1.starts_with(pat)
    }

    /// Returns true if the end of `self` matches `pat`.
    ///
    /// Note that patterns can only match UTF-8 sections of the `OsStr`.
    pub fn ends_with<'a, P>(&'a self, pat: P) -> bool
            where P: Pattern<'a>, P::Searcher: ReverseSearcher<'a> {
        self.inner.utf8_sections().next_back().unwrap().1.ends_with(pat)
    }

    /// An iterator over substrings of `self` separated by characters
    /// matched by a pattern.  See `str::split` for details.
    ///
    /// Note that patterns can only match UTF-8 sections of the `OsStr`.
    pub fn split<'a, P>(&'a self, pat: P) -> Split<'a, P> where P: Pattern<'a> {
        Split { inner: self.inner.split(pat) }
    }

    /// An iterator over substrings of `self` separated by characters
    /// matched by a pattern, in reverse order.  See `str::rsplit` for
    /// deatils.
    ///
    /// Note that patterns can only match UTF-8 sections of the `OsStr`.
    pub fn rsplit<'a, P>(&'a self, pat: P) -> RSplit<'a, P> where P: Pattern<'a> {
        RSplit { inner: self.inner.rsplit(pat) }
    }

    /// Returns true if the string starts with a valid UTF-8 sequence
    /// equal to the given `&str`.
    pub fn starts_with_str(&self, prefix: &str) -> bool {
        self.inner.starts_with_str(prefix)
    }

    /// If the string starts with the given `&str`, returns the rest
    /// of the string.  Otherwise returns `None`.
    pub fn remove_prefix_str(&self, prefix: &str) -> Option<&OsStr> {
        self.inner.remove_prefix_str(prefix).map(|s| Self::from_inner(s))
    }

    /// Retrieves the first character from the `OsStr` and returns it
    /// and the remainder of the `OsStr`.  Returns `None` if the
    /// `OsStr` does not start with a character (either because it it
    /// empty or because it starts with non-UTF-8 data).
    pub fn slice_shift_char(&self) -> Option<(char, &OsStr)> {
        self.inner.slice_shift_char().map(|(a, b)| (a, Self::from_inner(b)))
    }

    /// If the `OsStr` starts with a UTF-8 section followed by
    /// `boundary`, returns the sections before and after the boundary
    /// character.  Otherwise returns `None`.
    pub fn split_off_str(&self, boundary: char) -> Option<(&str, &OsStr)> {
        self.inner.split_off_str(boundary).map(|(a, b)| (a, Self::from_inner(b)))
    }
}

impl PartialEq for OsStr {
    fn eq(&self, other: &OsStr) -> bool {
        self.bytes().eq(other.bytes())
    }
}

impl PartialEq<str> for OsStr {
    fn eq(&self, other: &str) -> bool {
        *self == *OsStr::new(other)
    }
}

impl PartialEq<OsStr> for str {
    fn eq(&self, other: &OsStr) -> bool {
        *other == *OsStr::new(self)
    }
}

impl Eq for OsStr {}

impl PartialOrd for OsStr {
    #[inline]
    fn partial_cmp(&self, other: &OsStr) -> Option<cmp::Ordering> {
        self.bytes().partial_cmp(other.bytes())
    }
    #[inline]
    fn lt(&self, other: &OsStr) -> bool { self.bytes().lt(other.bytes()) }
    #[inline]
    fn le(&self, other: &OsStr) -> bool { self.bytes().le(other.bytes()) }
    #[inline]
    fn gt(&self, other: &OsStr) -> bool { self.bytes().gt(other.bytes()) }
    #[inline]
    fn ge(&self, other: &OsStr) -> bool { self.bytes().ge(other.bytes()) }
}

impl PartialOrd<str> for OsStr {
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<cmp::Ordering> {
        self.partial_cmp(OsStr::new(other))
    }
}

// FIXME (#19470): cannot provide PartialOrd<OsStr> for str until we
// have more flexible coherence rules.

impl Ord for OsStr {
    #[inline]
    fn cmp(&self, other: &OsStr) -> cmp::Ordering { self.bytes().cmp(other.bytes()) }
}

impl Hash for OsStr {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes().hash(state)
    }
}

impl Debug for OsStr {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.inner.fmt(formatter)
    }
}

impl Borrow<OsStr> for OsString {
    fn borrow(&self) -> &OsStr { &self[..] }
}

impl ToOwned for OsStr {
    type Owned = OsString;
    fn to_owned(&self) -> OsString { self.to_os_string() }
}

impl AsRef<OsStr> for OsStr {
    fn as_ref(&self) -> &OsStr {
        self
    }
}

impl AsRef<OsStr> for OsString {
    fn as_ref(&self) -> &OsStr {
        self
    }
}

impl AsRef<OsStr> for str {
    fn as_ref(&self) -> &OsStr {
        OsStr::from_inner(Slice::from_str(self))
    }
}

impl AsRef<OsStr> for String {
    fn as_ref(&self) -> &OsStr {
        (&**self).as_ref()
    }
}

impl FromInner<Buf> for OsString {
    fn from_inner(buf: Buf) -> OsString {
        OsString { inner: buf }
    }
}

impl IntoInner<Buf> for OsString {
    fn into_inner(self) -> Buf {
        self.inner
    }
}

impl AsInner<Slice> for OsStr {
    fn as_inner(&self) -> &Slice {
        &self.inner
    }
}

/// Iterator over parts of an OS string.
pub struct Split<'a, P> where P: Pattern<'a> {
    inner: ImplSplit<'a, P>
}

impl<'a, P> Clone for Split<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self { Split { inner: self.inner.clone() } }
}

impl<'a, P> Iterator for Split<'a, P>
where P: Pattern<'a> + Clone {
    type Item = &'a OsStr;

    fn next(&mut self) -> Option<&'a OsStr> {
        self.inner.next().map(|s| OsStr::from_inner(s))
    }
}

impl<'a, P> DoubleEndedIterator for Split<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
    fn next_back(&mut self) -> Option<&'a OsStr> {
        self.inner.next_back().map(|s| OsStr::from_inner(s))
    }
}

/// Reverse iterator over parts of an OS string.
pub struct RSplit<'a, P> where P: Pattern<'a> {
    inner: ImplRSplit<'a, P>
}

impl<'a, P> Clone for RSplit<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self { RSplit { inner: self.inner.clone() } }
}

impl<'a, P> Iterator for RSplit<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
    type Item = &'a OsStr;

    fn next(&mut self) -> Option<&'a OsStr> {
        self.inner.next().map(|s| OsStr::from_inner(s))
    }
}

impl<'a, P> DoubleEndedIterator for RSplit<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
    fn next_back(&mut self) -> Option<&'a OsStr> {
        self.inner.next_back().map(|s| OsStr::from_inner(s))
    }
}


impl<S: Borrow<OsStr>> LocalSliceConcatExt<OsStr> for [S] {
    type Output = OsString;

    fn concat(&self) -> OsString {
        if self.is_empty() {
            return OsString::new();
        }

        let len = self.iter().map(|s| s.borrow().len()).sum();
        let mut result = OsString::with_capacity(len);

        for s in self {
            result.push(s.borrow())
        }

        result
    }

    fn join(&self, sep: &OsStr) -> OsString {
        if self.is_empty() {
            return OsString::new();
        }

        // concat is faster
        if sep.is_empty() {
            return self.concat();
        }

        // this is wrong without the guarantee that `self` is non-empty
        // On Windows this may be a slight overestimate, but that's OK.
        let len = sep.len() * (self.len() - 1)
            + self.iter().map(|s| s.borrow().len()).sum::<usize>();
        let mut result = OsString::with_capacity(len);
        let mut first = true;

        for s in self {
            if first {
                first = false;
            } else {
                result.push(sep);
            }
            result.push(s.borrow());
        }
        result
    }

    fn connect(&self, sep: &OsStr) -> OsString {
        self.join(sep)
    }
}


#[cfg(test)]
mod tests {
    use std::prelude::v1::*;
    use std::borrow::Cow;
    use std::mem;
    use super::*;
    use slice_concat_ext::LocalSliceConcatExt;

    fn utf8_str() -> &'static str { "aé 💩" }
    fn utf8_osstring() -> OsString {
        OsString::from(utf8_str())
    }

    fn non_utf8_osstring() -> OsString {
        if_unix_windows! {
            unix {
                use unix::OsStringExt;
                let string = OsString::from_vec(vec![0xFF]);
                assert!(string.to_str().is_none());
                string
            }
            windows {
                use windows::OsStringExt;
                let string = OsString::from_wide(&[0xD800]);
                assert!(string.to_str().is_none());
                string
            }
        }
    }

    fn split_char() -> (OsString, OsString) {
        if_unix_windows! {
            unix {
                use unix::OsStringExt;
                (OsString::from_vec(vec![0xC2]), OsString::from_vec(vec![0xA2]))
            }
            windows {
                use windows::OsStringExt;
                (OsString::from_wide(&[0xD83D]), OsString::from_wide(&[0xDE3A]))
            }
        }
    }


    #[test]
    fn osstring_eq_smoke() {
        assert_eq!(OsString::new(), OsString::new());
        let string = OsString::from("abc");
        assert_eq!(utf8_osstring(), utf8_osstring());
        assert!(OsString::new() != utf8_osstring());
        assert!(utf8_osstring() != string);
        assert_eq!(non_utf8_osstring(), non_utf8_osstring());
    }

    #[test]
    fn osstring_from_bytes() {
        assert_eq!(OsString::from_bytes(utf8_str().as_bytes()),
                   Some(OsString::from(utf8_str())));
    }

    #[test]
    fn osstring_capacity() {
        assert!(OsString::with_capacity(10).capacity() >= 10);
        assert!(OsString::from("Hello").capacity() >= 5);
    }

    #[test]
    fn osstring_reserve() {
        let mut string = OsString::from("Hello");
        let len = string.len();
        let cap = string.capacity();
        assert!(cap >= len);
        string.reserve_exact(cap - len);
        assert_eq!(string.capacity(), cap);
        string.reserve_exact(cap - len + 1);
        assert!(string.capacity() > cap);
        let cap = string.capacity();
        string.reserve(cap - len + 1);
        assert!(string.capacity() > cap);
    }

    #[test]
    fn osstring_into_string() {
        assert_eq!(utf8_osstring().into_string(), Ok(utf8_str().to_string()));
        assert_eq!(non_utf8_osstring().into_string(), Err(non_utf8_osstring()));
    }

    #[test]
    fn osstring_into_string_lossy() {
        assert_eq!(utf8_osstring().into_string_lossy(), utf8_str());
        assert_eq!(non_utf8_osstring().into_string_lossy(), String::from_utf8_lossy(b"\xFF"));
    }

    #[test]
    fn osstring_push() {
        let mut string = OsString::new();
        string.push("foo");
        string.push("x");
        string.push(utf8_osstring());
        assert_eq!(string, OsString::from(["foox", utf8_str()].concat()));
        string.push(non_utf8_osstring());
        assert!(string.into_string().is_err());
    }

    #[test]
    fn osstring_clear() {
        let mut string = non_utf8_osstring();
        string.clear();
        assert_eq!(&string, "");
    }

    #[test]
    fn osstr_is_empty() {
        assert!(OsString::new().is_empty());
        assert!(!utf8_osstring().is_empty());
        assert!(!non_utf8_osstring().is_empty());
    }

    #[test]
    fn osstr_len() {
        assert_eq!(OsStr::new("").len(), 0);
        assert_eq!(utf8_osstring().len(), utf8_str().len());
        assert!(non_utf8_osstring().len() > 0);
    }

    #[test]
    fn osstr_to_str() {
        assert_eq!(utf8_osstring().to_str(), Some(utf8_str()));
        assert_eq!(non_utf8_osstring().to_str(), None);
    }

    #[test]
    fn osstr_to_string_lossy() {
        assert_eq!(utf8_osstring().to_string_lossy(),
                   Cow::Borrowed(utf8_str()));
        assert_eq!(non_utf8_osstring().to_string_lossy(),
                   String::from_utf8_lossy(b"\xFF"));
    }

    #[test]
    fn osstr_to_bytes() {
        assert_eq!(utf8_osstring().to_bytes(), Some(utf8_str().as_bytes()));
        if_unix_windows! {
            unix {
                assert_eq!(non_utf8_osstring().to_bytes(), Some(&b"\xFF"[..]));
            }
            windows {
                assert_eq!(non_utf8_osstring().to_bytes(), None);
            }
        }
    }

    #[test]
    fn osstr_contains_os() {
        assert!(OsStr::new("").contains_os(""));
        assert!(OsStr::new("aé 💩").contains_os(""));
        assert!(OsStr::new("aé 💩").contains_os("aé"));
        assert!(OsStr::new("aé 💩").contains_os("é "));
        assert!(OsStr::new("aé 💩").contains_os(" 💩"));
        assert!(OsStr::new("aé 💩").contains_os("aé 💩"));
        assert!(!OsStr::new("aé 💩").contains_os("b"));
        assert!(!OsStr::new("").contains_os("a"));

        let (start, end) = split_char();
        let mut full = start.to_owned();
        full.push(&end);
        assert!(start.to_str().is_none() && end.to_str().is_none() && full.to_str().is_some());
        assert!(!OsStr::new("").contains_os(&start));
        assert!(!OsStr::new("").contains_os(&end));

        assert!(start.contains_os(""));
        assert!(start.contains_os(&start));
        assert!(!start.contains_os(&end));
        assert!(!start.contains_os(&full));
        assert!(end.contains_os(""));
        assert!(!end.contains_os(&start));
        assert!(end.contains_os(&end));
        assert!(!end.contains_os(&full));
        assert!(full.contains_os(""));
        assert!(full.contains_os(&start));
        assert!(full.contains_os(&end));
        assert!(full.contains_os(&full));
    }

    #[test]
    fn osstr_starts_with_os() {
        assert!(OsStr::new("").starts_with_os(""));
        assert!(OsStr::new("aé 💩").starts_with_os(""));
        assert!(OsStr::new("aé 💩").starts_with_os("aé"));
        assert!(!OsStr::new("aé 💩").starts_with_os(" 💩"));
        assert!(OsStr::new("aé 💩").starts_with_os("aé 💩"));
        assert!(!OsStr::new("").starts_with_os("a"));

        let (start, end) = split_char();
        let mut full = start.to_owned();
        full.push(&end);
        assert!(start.to_str().is_none() && end.to_str().is_none() && full.to_str().is_some());
        assert!(!OsStr::new("").starts_with_os(&start));
        assert!(!OsStr::new("").starts_with_os(&end));

        assert!(start.starts_with_os(""));
        assert!(start.starts_with_os(&start));
        assert!(!start.starts_with_os(&end));
        assert!(!start.starts_with_os(&full));
        assert!(end.starts_with_os(""));
        assert!(!end.starts_with_os(&start));
        assert!(end.starts_with_os(&end));
        assert!(!end.starts_with_os(&full));
        assert!(full.starts_with_os(""));
        assert!(full.starts_with_os(&start));
        assert!(!full.starts_with_os(&end));
        assert!(full.starts_with_os(&full));
    }

    #[test]
    fn osstr_ends_with_os() {
        assert!(OsStr::new("").ends_with_os(""));
        assert!(OsStr::new("aé 💩").ends_with_os(""));
        assert!(!OsStr::new("aé 💩").ends_with_os("aé"));
        assert!(OsStr::new("aé 💩").ends_with_os(" 💩"));
        assert!(OsStr::new("aé 💩").ends_with_os("aé 💩"));
        assert!(!OsStr::new("").ends_with_os("a"));

        let (start, end) = split_char();
        let mut full = start.to_owned();
        full.push(&end);
        assert!(start.to_str().is_none() && end.to_str().is_none() && full.to_str().is_some());
        assert!(!OsStr::new("").ends_with_os(&start));
        assert!(!OsStr::new("").ends_with_os(&end));

        assert!(start.ends_with_os(""));
        assert!(start.ends_with_os(&start));
        assert!(!start.ends_with_os(&end));
        assert!(!start.ends_with_os(&full));
        assert!(end.ends_with_os(""));
        assert!(!end.ends_with_os(&start));
        assert!(end.ends_with_os(&end));
        assert!(!end.ends_with_os(&full));
        assert!(full.ends_with_os(""));
        assert!(!full.ends_with_os(&start));
        assert!(full.ends_with_os(&end));
        assert!(full.ends_with_os(&full));
    }

    #[test]
    fn osstr_contains() {
        assert!(OsStr::new("").contains(""));
        assert!(!OsStr::new("").contains('a'));

        let mut string = OsString::from("aé 💩");
        string.push(non_utf8_osstring());
        string.push("Zyzzl");
        assert!(string.contains('💩'));
        assert!(string.contains("yzz"));
        assert!(!string.contains("💩Z"));
        assert!(!string.contains(&non_utf8_osstring().into_string_lossy()[..]));
    }

    #[test]
    fn osstr_starts_with() {
        assert!(OsStr::new("").starts_with(""));
        assert!(!OsStr::new("").starts_with('a'));

        let mut string = OsString::from("aé 💩");
        string.push(non_utf8_osstring());
        string.push("Zyzzl");
        assert!(string.starts_with("aé 💩"));
        assert!(string.starts_with('a'));
        assert!(!string.starts_with('Z'));

        let mut string = non_utf8_osstring();
        string.push("X");
        assert!(string.starts_with(""));
        assert!(!string.starts_with('X'));
    }

    #[test]
    fn osstr_ends_with() {
        assert!(OsStr::new("").ends_with(""));
        assert!(!OsStr::new("").ends_with('a'));

        let mut string = OsString::from("aé 💩");
        string.push(non_utf8_osstring());
        string.push("Zyzzl");
        assert!(string.ends_with("Zyzzl"));
        assert!(string.ends_with('l'));
        assert!(!string.ends_with('z'));

        let mut string = OsString::from("X");
        string.push(non_utf8_osstring());
        assert!(string.ends_with(""));
        assert!(!string.ends_with('X'));
    }

    #[test]
    fn osstr_split() {
        assert_eq!(OsStr::new("").split('a').collect::<Vec<_>>(), [OsStr::new("")]);

        let part1 = non_utf8_osstring();
        let mut part2 = non_utf8_osstring();
        part2.push("aé 💩");
        let part3 = OsString::from("aé 💩");
        let mut string = part1.clone();
        string.push("aΓ");
        string.push(&part2);
        string.push("aΓ");
        string.push(&part3);
        string.push("aΓ");
        assert_eq!(string.split("aΓ").collect::<Vec<_>>(),
                   [&part1[..], &part2[..], &part3[..], OsStr::new("")]);

        assert_eq!(OsStr::new("aaa").split("aa").collect::<Vec<_>>(),
                   [OsStr::new(""), OsStr::new("a")]);
    }

    #[test]
    fn osstr_split_double_ended() {
        assert_eq!(OsStr::new("").split('a').rev().collect::<Vec<_>>(), [OsStr::new("")]);

        let part1 = non_utf8_osstring();
        let mut part2 = non_utf8_osstring();
        part2.push("aé 💩");
        let part3 = OsString::from("aé 💩");
        let mut string = part1.clone();
        string.push("Γ");
        string.push(&part2);
        string.push("Γ");
        string.push(&part3);
        string.push("Γ");
        let mut split = string.split('Γ');
        assert_eq!(split.next_back(), Some(OsStr::new("")));
        assert_eq!(split.next(), Some(&part1[..]));
        assert_eq!(split.next_back(), Some(&part3[..]));
        assert_eq!(split.next(), Some(&part2[..]));
        assert_eq!(split.next_back(), None);
        let mut split = string.split('Γ');
        assert_eq!(split.next(), Some(&part1[..]));
        assert_eq!(split.next_back(), Some(OsStr::new("")));
        assert_eq!(split.next(), Some(&part2[..]));
        assert_eq!(split.next_back(), Some(&part3[..]));
        assert_eq!(split.next(), None);
    }

    #[test]
    fn osstr_rsplit() {
        assert_eq!(OsStr::new("").rsplit('a').collect::<Vec<_>>(), [OsStr::new("")]);

        let part1 = non_utf8_osstring();
        let mut part2 = non_utf8_osstring();
        part2.push("aé 💩");
        let part3 = OsString::from("aé 💩");
        let mut string = part1.clone();
        string.push("aΓ");
        string.push(&part2);
        string.push("aΓ");
        string.push(&part3);
        string.push("aΓ");
        assert_eq!(string.rsplit("aΓ").collect::<Vec<_>>(),
                   [OsStr::new(""), &part3[..], &part2[..], &part1[..]]);

        assert_eq!(OsStr::new("aaa").split("aa").collect::<Vec<_>>(),
                   [OsStr::new(""), OsStr::new("a")]);
    }

    #[test]
    fn osstr_rsplit_double_ended() {
        assert_eq!(OsStr::new("").rsplit('a').rev().collect::<Vec<_>>(), [OsStr::new("")]);

        let part1 = non_utf8_osstring();
        let mut part2 = non_utf8_osstring();
        part2.push("aé 💩");
        let part3 = OsString::from("aé 💩");
        let mut string = part1.clone();
        string.push("Γ");
        string.push(&part2);
        string.push("Γ");
        string.push(&part3);
        string.push("Γ");
        let mut rsplit = string.rsplit('Γ');
        assert_eq!(rsplit.next_back(), Some(&part1[..]));
        assert_eq!(rsplit.next(), Some(OsStr::new("")));
        assert_eq!(rsplit.next_back(), Some(&part2[..]));
        assert_eq!(rsplit.next(), Some(&part3[..]));
        assert_eq!(rsplit.next_back(), None);
        let mut rsplit = string.rsplit('Γ');
        assert_eq!(rsplit.next(), Some(OsStr::new("")));
        assert_eq!(rsplit.next_back(), Some(&part1[..]));
        assert_eq!(rsplit.next(), Some(&part3[..]));
        assert_eq!(rsplit.next_back(), Some(&part2[..]));
        assert_eq!(rsplit.next(), None);
    }

    #[test]
    fn osstr_starts_with_str() {
        assert!(OsStr::new("").starts_with_str(""));
        assert!(!OsStr::new("").starts_with_str("a"));
        assert!(OsStr::new("abc").starts_with_str("ab"));
        assert!(utf8_osstring().starts_with_str(utf8_str()));
        assert!(non_utf8_osstring().starts_with_str(""));
        assert!(!non_utf8_osstring().starts_with_str("a"));
    }

    #[test]
    fn osstr_remove_prefix_str() {
        assert_eq!(OsStr::new("").remove_prefix_str(""), Some(OsStr::new("")));
        assert_eq!(OsStr::new("").remove_prefix_str("a"), None);
        assert_eq!(OsStr::new("abc").remove_prefix_str(""), Some(OsStr::new("abc")));
        assert_eq!(OsStr::new("abc").remove_prefix_str("ab"), Some(OsStr::new("c")));
        assert_eq!(OsStr::new("abc").remove_prefix_str("b"), None);
        assert_eq!(non_utf8_osstring().remove_prefix_str(""), Some(&non_utf8_osstring()[..]));
        assert_eq!(non_utf8_osstring().remove_prefix_str("a"), None);
        let mut string = OsString::from("X");
        string.push(non_utf8_osstring());
        assert_eq!(string.remove_prefix_str("X"), Some(&non_utf8_osstring()[..]));
    }

    #[test]
    fn osstr_slice_shift_char() {
        assert!(OsStr::new("").slice_shift_char().is_none());

        let mut string = OsString::from("aé 💩");
        string.push(non_utf8_osstring());
        let chars: Vec<char> = (0..).scan(&string[..], |s, _| {
            if let Some((c, rest)) = s.slice_shift_char() {
                mem::replace(s, rest);
                Some(c)
            } else {
                None
            }
        }).collect();
        assert_eq!(chars, ['a', 'é', ' ', '💩']);
    }

    #[test]
    fn osstr_split_off_str() {
        assert_eq!(OsStr::new("").split_off_str('a'), None);

        let mut string = OsString::from("aé 💩");
        string.push(non_utf8_osstring());
        assert_eq!(string.split_off_str('💩'), Some(("aé ", &non_utf8_osstring()[..])));
        string.push("x");
        assert_eq!(string.split_off_str('x'), None);
    }

    #[test]
    fn osstring_compare_str() {
        assert_eq!(&utf8_osstring(), utf8_str());
        assert!(non_utf8_osstring() != *"");
    }

    #[test]
    fn osstring_concat() {
        let mut string = non_utf8_osstring();
        string.push(utf8_osstring());
        string.push(non_utf8_osstring());
        assert_eq!([non_utf8_osstring(), utf8_osstring(), non_utf8_osstring()].concat(),
                   string);
    }

    #[test]
    fn osstring_join() {
        let mut string = non_utf8_osstring();
        string.push(utf8_osstring());
        string.push("xyz");
        string.push(utf8_osstring());
        string.push(non_utf8_osstring());
        assert_eq!([&non_utf8_osstring()[..], OsStr::new("xyz"), &non_utf8_osstring()[..]]
                   .join(&utf8_osstring()[..]),
                   string);
    }

}
