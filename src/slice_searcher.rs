// FIXME: Use a better algorithm for this.  core::str::pattern has
// some interesting stuff.

pub struct SliceSearcher<'a, 'b> {
    haystack: &'a [u8],
    needle: &'b [u8],
    position: usize,
    overlapping: bool,
}

impl<'a, 'b> SliceSearcher<'a, 'b> {
    pub fn new(haystack: &'a [u8], needle: &'b [u8], overlapping: bool) -> SliceSearcher<'a, 'b> {
        SliceSearcher {
            haystack: haystack,
            needle: needle,
            position: 0,
            overlapping: overlapping,
        }
    }
}

impl<'a, 'b> Iterator for SliceSearcher<'a, 'b> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        while self.position + self.needle.len() <= self.haystack.len() {
            let check = self.position;
            self.position += 1;
            if &self.haystack[check..check + self.needle.len()] == self.needle {
                if !self.overlapping {
                    self.position = check + self.needle.len();
                }
                return Some(check);
            }
        }
        None
    }
}
