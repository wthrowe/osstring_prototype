use core::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher};

use utf8_sections::Utf8Sections;

pub struct Split<'a, P>(SplitImpl<'a, P>) where P: Pattern<'a>;

impl<'a, P> Clone for Split<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self { Split(self.0.clone()) }
}

impl<'a, P> Split<'a, P> where P: Pattern<'a> {
    pub fn new(slice: &'a [u8], pat: P) -> Self {
        Split(SplitImpl::new(slice, pat))
    }
}

impl<'a, P> Iterator for Split<'a, P> where P: Pattern<'a> + Clone {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        self.0.next()
    }
}

impl<'a, P> DoubleEndedIterator for Split<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
    fn next_back(&mut self) -> Option<&'a [u8]> {
        self.0.next_back()
    }
}

pub struct RSplit<'a, P>(SplitImpl<'a, P>) where P: Pattern<'a>;

impl<'a, P> Clone for RSplit<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self { RSplit(self.0.clone()) }
}

impl<'a, P> RSplit<'a, P> where P: Pattern<'a> {
    pub fn new(slice: &'a [u8], pat: P) -> Self {
        RSplit(SplitImpl::new(slice, pat))
    }
}

impl<'a, P> Iterator for RSplit<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        self.0.next_back()
    }
}

impl<'a, P> DoubleEndedIterator for RSplit<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
    fn next_back(&mut self) -> Option<&'a [u8]> {
        self.0.next()
    }
}


struct MatchImpl<'a, P> where P: Pattern<'a> {
    sections: Utf8Sections<'a>,
    pat: P,
    front_searcher: Option<P::Searcher>,
    back_searcher: Option<P::Searcher>,
    front_section_start: usize,
    back_section_start: usize,
}

impl<'a, P> Clone for MatchImpl<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self {
        MatchImpl {
            sections: self.sections.clone(),
            pat: self.pat.clone(),
            front_searcher: self.front_searcher.clone(),
            back_searcher: self.back_searcher.clone(),
            front_section_start: self.front_section_start.clone(),
            back_section_start: self.back_section_start.clone(),
        }
    }
}

impl<'a, P> MatchImpl<'a, P> where P: Pattern<'a> {
    pub fn new(slice: &'a [u8], pat: P) -> Self {
        MatchImpl {
            pat: pat,
            sections: Utf8Sections::new(slice),
            front_searcher: None,
            back_searcher: None,
            front_section_start: 0,
            back_section_start: slice.len(),
        }
    }

    fn next(&mut self) -> Option<(usize, usize)> where P: Clone {
        loop {
            if self.front_section_start == self.back_section_start {
                // Last section.  Both directions use the same iterator.
                let searcher = self.front_searcher.as_mut().or(self.back_searcher.as_mut());
                let offset = self.front_section_start;
                return searcher.and_then(|m| m.next_match())
                    .map(|(start, end)| (offset + start, offset + end));
            }
            if self.front_searcher.is_none() {
                if let Some((start, section)) = self.sections.next() {
                    // New segment
                    self.front_searcher = Some(self.pat.clone().into_searcher(section));
                    self.front_section_start = start;
                } else {
                    // Starting the last segment.  Go back to the top.
                    self.front_section_start = self.back_section_start;
                    continue;
                }
            }

            if let Some((start, end)) = self.front_searcher.as_mut().unwrap().next_match() {
                return Some((self.front_section_start + start,
                             self.front_section_start + end));
            }

            // Finished this segment
            self.front_searcher = None;
        }
    }

    fn next_back(&mut self) -> Option<(usize, usize)>
    where P: Clone, P::Searcher: ReverseSearcher<'a> {
        loop {
            if self.front_section_start == self.back_section_start {
                // Last section.  Both directions use the same iterator.
                let searcher = self.front_searcher.as_mut().or(self.back_searcher.as_mut());
                let offset = self.back_section_start;
                return searcher.and_then(|m| m.next_match_back())
                    .map(|(start, end)| (offset + start, offset + end));
            }
            if self.back_searcher.is_none() {
                if let Some((start, section)) = self.sections.next_back() {
                    // New segment
                    self.back_searcher = Some(self.pat.clone().into_searcher(section));
                    self.back_section_start = start;
                } else {
                    // Starting the last segment.  Go back to the top.
                    self.back_section_start = self.front_section_start;
                    continue;
                }
            }

            if let Some((start, end)) = self.back_searcher.as_mut().unwrap().next_match_back() {
                return Some((self.back_section_start + start,
                             self.back_section_start + end));
            }

            // Finished this segment
            self.back_searcher = None;
        }
    }
}

struct SplitImpl<'a, P> where P: Pattern<'a> {
    slice: &'a [u8],
    matches: MatchImpl<'a, P>,
    remainder: (usize, usize),
}

impl<'a, P> Clone for SplitImpl<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self {
        SplitImpl {
            slice: self.slice.clone(),
            matches: self.matches.clone(),
            remainder: self.remainder.clone(),
        }
    }
}

impl<'a, P> SplitImpl<'a, P> where P: Pattern<'a> {
    pub fn new(slice: &'a [u8], pat: P) -> Self {
        SplitImpl {
            slice: slice,
            matches: MatchImpl::new(slice, pat),
            remainder: (0, slice.len()),
        }
    }

    fn next(&mut self) -> Option<&'a [u8]> where P: Clone {
        if self.remainder.1 < self.remainder.0 { return None; }
        if let Some((start, end)) = self.matches.next() {
            let result = &self.slice[self.remainder.0..start];
            self.remainder.0 = end;
            Some(result)
        } else {
            // We've exhausted all the matches, but we still
            // have the section between the last matches from
            // either side to return.
            let result = &self.slice[self.remainder.0..self.remainder.1];
            self.remainder.0 = self.remainder.1 + 1;
            Some(result)
        }
    }

    fn next_back(&mut self) -> Option<&'a [u8]>
    where P: Clone, P::Searcher: ReverseSearcher<'a> {
        if self.remainder.1 < self.remainder.0 { return None; }
        if let Some((start, end)) = self.matches.next_back() {
            let result = &self.slice[end..self.remainder.1];
            self.remainder.1 = start;
            Some(result)
        } else {
            // We've exhausted all the matches, but we still
            // have the section between the last matches from
            // either side to return.
            let result = &self.slice[self.remainder.0..self.remainder.1];
            self.remainder.0 = self.remainder.1 + 1;
            Some(result)
        }
    }
}
