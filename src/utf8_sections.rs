use core::str;

pub struct Utf8Sections<'a> {
    slice: &'a [u8],
    position: usize,
}

impl<'a> Utf8Sections<'a> {
    pub fn new(slice: &'a [u8]) -> Self {
        Utf8Sections { slice: slice, position: 0 }
    }
}

impl<'a> Iterator for Utf8Sections<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        if self.position > self.slice.len() { return None; }
        loop {
            if self.position == self.slice.len() {
                self.position += 1;
                return Some("");
            }

            match str::from_utf8(&self.slice[self.position..]) {
                Ok(s) => {
                    self.position = self.slice.len() + 1;
                    return Some(s);
                }
                Err(e) => {
                    let start = self.position;
                    if e.valid_up_to() == 0 {
                        self.position += 1;
                        if start == 0 { return Some(""); }
                    } else {
                        let end = start + e.valid_up_to();
                        self.position = end + 1;
                        unsafe {
                            return Some(str::from_utf8_unchecked(&self.slice[start..end]))
                        }
                    }
                }
            }
        }
    }
}
