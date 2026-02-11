#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct ColorCode(pub(crate) u8);

impl ColorCode {
    pub fn new(foreground: Color, background: Color) -> ColorCode {
        ColorCode((background as u8) << 4 | (foreground as u8))
    }

    pub fn flip(&self) -> ColorCode {
        let fg = self.0 & 0x0F;
        let bg = (self.0 & 0xF0) >> 4;
        ColorCode((fg << 4) | bg)
    }

    pub fn foreground(&self) -> Color {
        Color::from_u8(self.0 & 0x0F)
    }

    pub fn background(&self) -> Color {
        Color::from_u8((self.0 & 0xF0) >> 4)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Color {
    Black = 0,
    Blue = 1,
    Green = 2,
    Cyan = 3,
    Red = 4,
    Magenta = 5,
    Brown = 6,
    LightGray = 7,
    DarkGray = 8,
    LightBlue = 9,
    LightGreen = 10,
    LightCyan = 11,
    LightRed = 12,
    Pink = 13,
    Yellow = 14,
    White = 15,
}

impl Color {
    pub fn from_u8(color: u8) -> Color {
        match color {
            0 => Color::Black,
            1 => Color::Blue,
            2 => Color::Green,
            3 => Color::Cyan,
            4 => Color::Red,
            5 => Color::Magenta,
            6 => Color::Brown,
            7 => Color::LightGray,
            8 => Color::DarkGray,
            9 => Color::LightBlue,
            10 => Color::LightGreen,
            11 => Color::LightCyan,
            12 => Color::LightRed,
            13 => Color::Pink,
            14 => Color::Yellow,
            15 => Color::White,
            _ => Color::White,
        }
    }
}
