use core::iter::FlatMap;
use core::str::pattern::{DoubleEndedSearcher, Pattern};
use std::str;

use utf8_sections::Utf8Sections;

pub struct Split<'a, P> where P: Pattern<'a> {
    slice: &'a [u8],
    matches: FlatMap<Utf8Sections<'a>, SplitInner<'a, P>, SplitInnerFactory<P>>,
    slice_start: usize,
    back_start: usize,
}

impl<'a, P> Clone for Split<'a, P> where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self {
        Split {
            slice: self.slice.clone(),
            matches: self.matches.clone(),
            slice_start: self.slice_start.clone(),
            back_start: self.back_start.clone(),
        }
    }
}

impl<'a, P> Split<'a, P> where P: Pattern<'a> + Clone {
    pub fn new(slice: &'a [u8], pat: P) -> Self {
        Split {
            slice: slice,
            matches: Utf8Sections::new(slice).flat_map(SplitInnerFactory(pat)),
            slice_start: 0,
            back_start: slice.len(),
        }
    }
}

impl<'a, P> Iterator for Split<'a, P> where P: Pattern<'a> + Clone {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        if self.slice_start > self.back_start { return None; }
        if let Some((start, end)) = self.matches.next() {
            let result = &self.slice[self.slice_start..start];
            self.slice_start = end;
            return Some(result);
        } else {
            let result = &self.slice[self.slice_start..self.back_start];
            self.slice_start = self.back_start + 1;
            return Some(result);
        }
    }
}

impl<'a, P> DoubleEndedIterator for Split<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
    fn next_back(&mut self) -> Option<&'a [u8]> {
        if self.slice_start > self.back_start { return None; }
        if let Some((start, end)) = self.matches.next_back() {
            let result = &self.slice[end..self.back_start];
            self.back_start = start;
            return Some(result);
        } else {
            let result = &self.slice[self.slice_start..self.back_start];
            self.slice_start = self.back_start + 1;
            return Some(result);
        }
    }
}

#[derive(Clone)]
struct SplitInnerFactory<P>(P);

impl<'a, P> FnOnce<((usize, &'a str),)> for SplitInnerFactory<P> where P: Pattern<'a> + Clone {
    type Output = SplitInner<'a, P>;

    extern "rust-call"
    fn call_once(mut self, args: ((usize, &'a str),)) -> SplitInner<'a, P> {
        self.call_mut(args)
    }
}

impl<'a, P> FnMut<((usize, &'a str),)> for SplitInnerFactory<P> where P: Pattern<'a> + Clone {
    extern "rust-call"
    fn call_mut(&mut self, ((start, section),): ((usize, &'a str),)) -> SplitInner<'a, P> {
        SplitInner {
            matches: section.match_indices(self.0.clone()),
            section_start: start,
        }
    }
}

struct SplitInner<'a, P> where P: Pattern<'a> {
    matches: str::MatchIndices<'a, P>,
    section_start: usize,
}

impl<'a, P> Clone for SplitInner<'a, P> where P: Pattern<'a>, P::Searcher: Clone {
    fn clone(&self) -> Self {
        SplitInner {
            matches: self.matches.clone(),
            section_start: self.section_start.clone(),
        }
    }
}

impl<'a, P> Iterator for SplitInner<'a, P> where P: Pattern<'a> {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<(usize, usize)> {
        self.matches.next().map(
            |(offset, divider)| {
                let begin = self.section_start + offset;
                let end = begin + divider.len();
                (begin, end)
            })
    }
}

impl<'a, P> DoubleEndedIterator for SplitInner<'a, P>
        where P: Pattern<'a>, P::Searcher: DoubleEndedSearcher<'a> {
    fn next_back(&mut self) -> Option<(usize, usize)> {
        self.matches.next_back().map(
            |(offset, divider)| {
                let begin = self.section_start + offset;
                let end = begin + divider.len();
                (begin, end)
            })
    }
}
