use super::{color::ColorCode, font::FONT8X8_BASIC_FLATTENED};
use crate::{FramebufferInfo, tty::color::Color};

pub struct TextWriter {
    buffer: &'static mut [u8],
    info: FramebufferInfo,
    font: &'static [u8],
}

impl TextWriter {
    pub fn new_framebuffer_writer(buffer: &'static mut [u8], info: FramebufferInfo) -> TextWriter {
        let mut writer = TextWriter {
            buffer,
            info,
            font: FONT8X8_BASIC_FLATTENED.as_slice(),
        };
        writer.clear_screen();
        writer
    }

    fn write_pixel(&mut self, x: usize, y: usize, color: (u8, u8, u8)) {
        let bpp = self.info.bytes_per_pixel();
        if x >= self.info.width() || y >= self.info.height() {
            return;
        }

        let pixel_offset = y * (self.info.stride() * bpp) + x * bpp;

        if pixel_offset + bpp > self.buffer.len() {
            return;
        }

        match self.info.pixel_format {
            0 => {
                self.buffer[pixel_offset] = color.0;
                self.buffer[pixel_offset + 1] = color.1;
                self.buffer[pixel_offset + 2] = color.2;
            }
            1 => {
                self.buffer[pixel_offset] = color.2;
                self.buffer[pixel_offset + 1] = color.1;
                self.buffer[pixel_offset + 2] = color.0;
            }
            2 => {
                let gray = (color.0 as f32 * 0.299
                    + color.1 as f32 * 0.587
                    + color.2 as f32 * 0.114) as u8;
                self.buffer[pixel_offset] = gray;
            }
            _ => unreachable!("Unsupported pixel format"),
        }
    }

    pub fn scroll_up(&mut self) {
        let bytes_per_line = self.info.stride() * self.info.bytes_per_pixel();
        let line_count = 8;

        let source_start = line_count * bytes_per_line;
        let copy_size = (self.info.height() - line_count) * bytes_per_line;

        if source_start + copy_size <= self.buffer.len() {
            self.buffer
                .copy_within(source_start..source_start + copy_size, 0);
        }

        let clear_start = (self.info.height() - line_count) * bytes_per_line;
        if clear_start < self.buffer.len() {
            let clear_end = core::cmp::min(
                clear_start + (line_count * bytes_per_line),
                self.buffer.len(),
            );
            self.buffer[clear_start..clear_end].fill(0);
        }
    }

    pub fn clear_screen(&mut self) {
        let bytes_per_line = self.info.stride() * self.info.bytes_per_pixel();
        let total_size = self.info.height() * bytes_per_line;

        let clear_size = core::cmp::min(total_size, self.buffer.len());
        self.buffer[0..clear_size].fill(0);
    }

    fn color_to_rgb(&self, color: Color) -> (u8, u8, u8) {
        match color {
            Color::Black => (0, 0, 0),
            Color::Blue => (0, 0, 255),
            Color::Green => (0, 255, 0),
            Color::Cyan => (0, 255, 255),
            Color::Red => (255, 0, 0),
            Color::Magenta => (255, 0, 255),
            Color::Brown => (165, 42, 42),
            Color::LightGray => (211, 211, 211),
            Color::DarkGray => (169, 169, 169),
            Color::LightBlue => (173, 216, 230),
            Color::LightGreen => (144, 238, 144),
            Color::LightCyan => (224, 255, 255),
            Color::LightRed => (255, 182, 193),
            Color::Pink => (255, 192, 203),
            Color::Yellow => (255, 255, 0),
            Color::White => (255, 255, 255),
        }
    }

    pub fn set_byte_at(&mut self, byte: u8, col: usize, row: usize, color_code: ColorCode) {
        self.set_byte(byte, col * 8, row * 8, color_code);
    }

    fn set_byte(&mut self, byte: u8, col: usize, row: usize, color_code: ColorCode) {
        let char_idx = byte as usize * 8;
        let font_char = &self.font[char_idx..char_idx + 8];
        let fg = self.color_to_rgb(color_code.foreground());
        let bg = self.color_to_rgb(color_code.background());

        for (y, &row_data) in font_char.iter().enumerate() {
            for x in 0..8 {
                if (row_data >> x) & 1 == 1 {
                    self.write_pixel(col + x, row + y, fg);
                } else {
                    self.write_pixel(col + x, row + y, bg);
                }
            }
        }
    }

    fn clear_byte(&mut self, col: usize, row: usize) {
        for y in 0..8 {
            for x in 0..8 {
                self.write_pixel(col + x, row + y, (0, 0, 0));
            }
        }
    }

    pub fn clear_byte_at(&mut self, col: usize, row: usize) {
        self.clear_byte(col * 8, row * 8);
    }

    pub fn clear_from_col(&mut self, col: usize, row: usize) {
        for c in col..self.info.width() / 8 {
            self.clear_byte(c * 8, row * 8);
        }
    }

    pub fn clear_until_col(&mut self, col: usize, row: usize) {
        for c in 0..col {
            self.clear_byte(c * 8, row * 8);
        }
    }

    pub fn clear_last_line(&mut self) {
        let bbp = self.info.bytes_per_pixel();
        let start = (self.info.height() - 8) * self.info.stride() * bbp;
        let end = self.info.height() * self.info.stride() * bbp;

        if end <= self.buffer.len() {
            self.buffer[start..end].fill(0);
        }
    }
}
