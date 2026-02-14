use core::fmt::{self, Write};

#[cfg(not(target_os = "asha"))]
use std::io::Write as IoWrite;

struct Stdout;

impl Write for Stdout {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        #[cfg(not(target_os = "asha"))]
        std::io::stdout().write_all(s.as_bytes()).map_err(|_| fmt::Error)?;

        #[cfg(target_os = "asha")]
        {
            let _ = s;
        }

        Ok(())
    }
}

pub fn print(args: fmt::Arguments) {
    let _ = Stdout.write_fmt(args);
}
