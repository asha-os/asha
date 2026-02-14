#[cfg(not(target_os = "asha"))]
pub struct Args {
    args: std::vec::IntoIter<String>,
}

#[cfg(not(target_os = "asha"))]
impl Args {
    pub fn get() -> Option<Self> {
        Some(Args {
            args: std::env::args().collect::<Vec<_>>().into_iter(),
        })
    }

    pub fn len(&self) -> usize {
        self.args.len()
    }

    pub fn is_empty(&self) -> bool {
        self.args.len() == 0
    }
}

#[cfg(not(target_os = "asha"))]
impl Iterator for Args {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.args.next()
    }
}

#[cfg(target_os = "asha")]
pub struct Args;

#[cfg(target_os = "asha")]
impl Args {
    pub fn get() -> Option<Self> {
        None
    }

    pub fn len(&self) -> usize {
        0
    }

    pub fn is_empty(&self) -> bool {
        true
    }
}

#[cfg(target_os = "asha")]
impl Iterator for Args {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}
