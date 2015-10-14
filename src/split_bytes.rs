use core::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher};

use utf8_sections::Utf8Sections;

// make_iterator!{F and R wrap I yielding func => type}
//    defines forward and reverse versions of struct with Clone and Iterator
// make_iterator!{F and R wrap I with all impls yielding func => type}
//    additionally adds new(slice: &'a [u8], pat: P) and DoubleEndedIterator
macro_rules! make_iterator {
    ($forward:ident and $reverse:ident wrap $inner:ident yielding $map:expr => $ret:ty) => {
        pub struct $forward<'a, P>($inner<'a, P>) where P: Pattern<'a>;

        impl<'a, P> Clone for $forward<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: Clone {
            fn clone(&self) -> Self { $forward(self.0.clone()) }
        }

        impl<'a, P> Iterator for $forward<'a, P> where P: Pattern<'a> + Clone {
            type Item = $ret;

            fn next(&mut self) -> Option<$ret> {
                self.0.next().map($map)
            }
        }

        pub struct $reverse<'a, P>($inner<'a, P>) where P: Pattern<'a>;

        impl<'a, P> Clone for $reverse<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: Clone {
            fn clone(&self) -> Self { $reverse(self.0.clone()) }
        }

        impl<'a, P> Iterator for $reverse<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: ReverseSearcher<'a> {
            type Item = $ret;

            fn next(&mut self) -> Option<$ret> {
                self.0.next_back().map($map)
            }
        }
    };
    ($forward:ident and $reverse:ident wrap $inner:ident yielding $map:expr => $ret:ty;
     implement $($implement:ident)*) => {
        make_iterator!{$forward and $reverse wrap $inner yielding $map => $ret}

        $(implement!{$implement for $forward and $reverse wrap $inner yielding $map => $ret})*
    };
}
macro_rules! implement {
    (new for $forward:ident and $reverse:ident wrap $inner:ident yielding $map:expr => $ret:ty) => {
        impl<'a, P> $forward<'a, P> where P: Pattern<'a> {
            pub fn new(slice: &'a [u8], pat: P) -> Self {
                $forward($inner::new(slice, pat))
            }
        }

        impl<'a, P> $reverse<'a, P> where P: Pattern<'a> {
            pub fn new(slice: &'a [u8], pat: P) -> Self {
                $reverse($inner::new(slice, pat))
            }
        }
    };
    (DoubleEndedIterator for $forward:ident and $reverse:ident wrap $inner:ident yielding $map:expr => $ret:ty) => {
        impl<'a, P> DoubleEndedIterator for $forward<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
            fn next_back(&mut self) -> Option<$ret> {
                self.0.next_back().map($map)
            }
        }

        impl<'a, P> DoubleEndedIterator for $reverse<'a, P>
        where P: Pattern<'a> + Clone, P::Searcher: DoubleEndedSearcher<'a> {
            fn next_back(&mut self) -> Option<$ret> {
                self.0.next().map($map)
            }
        }
    };
}

make_iterator!{Matches and RMatches wrap MatchImpl yielding |x| x.1 => &'a str;
               implement new DoubleEndedIterator}
make_iterator!{Split and RSplit wrap SplitImpl yielding |x| x => &'a [u8];
               implement new DoubleEndedIterator}
make_iterator!{SplitN and RSplitN wrap SplitNImpl yielding |x| x => &'a [u8]}
make_iterator!{SplitTerminator and RSplitTerminator wrap SplitImpl
               yielding |x| x => &'a [u8];
               implement DoubleEndedIterator}

impl<'a, P> SplitN<'a, P> where P: Pattern<'a> {
    pub fn new(slice: &'a [u8], count: usize, pat: P) -> Self {
        SplitN(SplitNImpl::new(slice, count, pat))
    }
}

impl<'a, P> RSplitN<'a, P> where P: Pattern<'a> {
    pub fn new(slice: &'a [u8], count: usize, pat: P) -> Self {
        RSplitN(SplitNImpl::new(slice, count, pat))
    }
}

impl<'a, P> SplitTerminator<'a, P> where P: Pattern<'a> {
    pub fn new(slice: &'a [u8], pat: P) -> Self {
        SplitTerminator(SplitImpl::skipping_terminator(slice, pat, true))
    }
}

impl<'a, P> RSplitTerminator<'a, P> where P: Pattern<'a> {
    pub fn new(slice: &'a [u8], pat: P) -> Self {
        RSplitTerminator(SplitImpl::skipping_terminator(slice, pat, true))
    }
}



struct MatchImpl<'a, P> where P: Pattern<'a> {
    sections: Utf8Sections<'a>,
    pat: P,
    front_searcher: Option<P::Searcher>,
    back_searcher: Option<P::Searcher>,
    front_section: (usize, &'a str),
    back_section: (usize, &'a str),
}

impl<'a, P> Clone for MatchImpl<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self {
        MatchImpl {
            sections: self.sections.clone(),
            pat: self.pat.clone(),
            front_searcher: self.front_searcher.clone(),
            back_searcher: self.back_searcher.clone(),
            front_section: self.front_section.clone(),
            back_section: self.back_section.clone(),
        }
    }
}

impl<'a, P> MatchImpl<'a, P> where P: Pattern<'a> {
    fn new(slice: &'a [u8], pat: P) -> Self {
        MatchImpl {
            pat: pat,
            sections: Utf8Sections::new(slice),
            front_searcher: None,
            back_searcher: None,
            front_section: (0, ""),
            back_section: (slice.len(), ""),
        }
    }

    fn next(&mut self) -> Option<(usize, &'a str)> where P: Clone {
        loop {
            if self.front_section.0 == self.back_section.0 {
                // Last section.  Both directions use the same iterator.
                let (searcher, section) =
                    match (self.front_searcher.as_mut(), self.back_searcher.as_mut()) {
                        (Some(front), None) => (front, self.front_section),
                        (None, Some(back)) => (back, self.back_section),
                        (None, None) => return None,
                        (Some(_), Some(_)) => unreachable!(),
                    };
                return searcher.next_match()
                    .map(|(start, end)| (section.0 + start, &section.1[start..end]));
            }
            if self.front_searcher.is_none() {
                if let Some(section) = self.sections.next() {
                    self.front_section = section;
                    // New segment
                    self.front_searcher =
                        Some(self.pat.clone().into_searcher(self.front_section.1));
                } else {
                    // Starting the last segment.  Go back to the top.
                    self.front_section = self.back_section;
                    continue;
                }
            }

            if let Some((start, end)) = self.front_searcher.as_mut().unwrap().next_match() {
                let section = self.front_section;
                return Some((section.0 + start, &section.1[start..end]));
            }

            // Finished this segment
            self.front_searcher = None;
        }
    }

    fn next_back(&mut self) -> Option<(usize, &'a str)>
    where P: Clone, P::Searcher: ReverseSearcher<'a> {
        loop {
            if self.front_section.0 == self.back_section.0 {
                // Last section.  Both directions use the same iterator.
                let (searcher, section) =
                    match (self.front_searcher.as_mut(), self.back_searcher.as_mut()) {
                        (Some(front), None) => (front, self.front_section),
                        (None, Some(back)) => (back, self.back_section),
                        (None, None) => return None,
                        (Some(_), Some(_)) => unreachable!(),
                    };
                return searcher.next_match_back()
                    .map(|(start, end)| (section.0 + start, &section.1[start..end]));
            }
            if self.back_searcher.is_none() {
                if let Some(section) = self.sections.next_back() {
                    // New segment
                    self.back_section = section;
                    self.back_searcher =
                        Some(self.pat.clone().into_searcher(self.back_section.1));
                } else {
                    // Starting the last segment.  Go back to the top.
                    self.back_section = self.front_section;
                    continue;
                }
            }

            if let Some((start, end)) = self.back_searcher.as_mut().unwrap().next_match_back() {
                let section = self.back_section;
                return Some((section.0 + start, &section.1[start..end]));
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
    skip_terminator: bool,
}

impl<'a, P> Clone for SplitImpl<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self {
        SplitImpl {
            slice: self.slice.clone(),
            matches: self.matches.clone(),
            remainder: self.remainder.clone(),
            skip_terminator: self.skip_terminator.clone(),
        }
    }
}

impl<'a, P> SplitImpl<'a, P> where P: Pattern<'a> {
    fn new(slice: &'a [u8], pat: P) -> Self {
        Self::skipping_terminator(slice, pat, false)
    }

    fn skipping_terminator(slice: &'a [u8], pat: P, skip_terminator: bool) -> Self {
        SplitImpl {
            slice: slice,
            matches: MatchImpl::new(slice, pat),
            remainder: (0, slice.len()),
            skip_terminator: skip_terminator,
        }
    }

    fn next(&mut self) -> Option<&'a [u8]> where P: Clone {
        if self.remainder.1 < self.remainder.0 { return None; }
        if let Some((start, mat)) = self.matches.next() {
            let result = &self.slice[self.remainder.0..start];
            self.remainder.0 = start + mat.len();
            Some(result)
        } else {
            // We've exhausted all the matches, but we still
            // have the section between the last matches from
            // either side to return.
            let result = &self.slice[self.remainder.0..self.remainder.1];
            // Skip the last entry if we've been asked to and it
            // starts at the end of the slice.
            let result = if self.skip_terminator && self.remainder.0 == self.slice.len() {
                None
            } else {
                Some(result)
            };
            self.remainder.0 = self.remainder.1 + 1;
            return result;
        }
    }

    fn next_back(&mut self) -> Option<&'a [u8]>
    where P: Clone, P::Searcher: ReverseSearcher<'a> {
        if self.remainder.1 < self.remainder.0 { return None; }
        if let Some((start, mat)) = self.matches.next_back() {
            let result = &self.slice[start + mat.len()..self.remainder.1];
            self.remainder.1 = start;
            // Skip the value if we've been asked to and it starts at
            // the end of the slice.
            if self.skip_terminator && start + mat.len() == self.slice.len() {
                self.next_back()
            } else {
                Some(result)
            }
        } else {
            // We've exhausted all the matches, but we still
            // have the section between the last matches from
            // either side to return.
            let result = &self.slice[self.remainder.0..self.remainder.1];
            // Skip the last entry if we've been asked to and it
            // starts at the end of the slice.
            let result = if self.skip_terminator && self.remainder.0 == self.slice.len() {
                None
            } else {
                Some(result)
            };
            self.remainder.0 = self.remainder.1 + 1;
            return result;
        }
    }

    fn rest(&self) -> Option<&'a [u8]> {
        if self.remainder.1 < self.remainder.0 { return None; }
        Some(&self.slice[self.remainder.0..self.remainder.1])
    }
}


struct SplitNImpl<'a, P> where P: Pattern<'a> {
    split: SplitImpl<'a, P>,
    count: usize,
}

impl<'a, P> Clone for SplitNImpl<'a, P>
where P: Pattern<'a> + Clone, P::Searcher: Clone {
    fn clone(&self) -> Self {
        SplitNImpl {
            split: self.split.clone(),
            count: self.count.clone(),
        }
    }
}

impl<'a, P> SplitNImpl<'a, P> where P: Pattern<'a> {
    fn new(slice: &'a [u8], count: usize, pat: P) -> Self {
        SplitNImpl {
            split: SplitImpl::new(slice, pat),
            count: count,
        }
    }

    fn next(&mut self) -> Option<&'a [u8]> where P: Clone {
        match self.count {
            0 => None,
            1 => { self.count = 0; self.split.rest() },
            _ => { self.count -= 1; self.split.next() },
        }
    }

    fn next_back(&mut self) -> Option<&'a [u8]>
    where P: Clone, P::Searcher: ReverseSearcher<'a> {
        match self.count {
            0 => None,
            1 => { self.count = 0; self.split.rest() },
            _ => { self.count -= 1; self.split.next_back() },
        }
    }
}
