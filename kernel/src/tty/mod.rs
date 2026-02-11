use alloc::{string::String, vec::Vec};

use crate::tty::{
    color::{Color, ColorCode},
    keyboard::{Key, KeyEvent, KeyboardState},
};

pub mod color;
mod font;
pub mod keyboard;
pub mod writer;

pub struct Tty {
    writer: writer::TextWriter,
    keyboard_state: KeyboardState,
    caps_lock_active: bool,
    cursor: (usize, usize),
    shell_prompt: Option<String>,
    current_prompt: Vec<u8>,
    color_code: ColorCode,
}

impl Tty {
    pub fn new(writer: writer::TextWriter, color_code: ColorCode) -> Self {
        Self {
            writer,
            shell_prompt: None,
            keyboard_state: KeyboardState::new(),
            caps_lock_active: false,
            cursor: (0, 0),
            current_prompt: alloc::vec![],
            color_code,
        }
    }

    pub fn set_shell_prompt(&mut self, prompt: String, prompt_color_code: ColorCode) {
        for (i, byte) in prompt.bytes().enumerate() {
            self.writer
                .set_byte_at(byte, i, self.cursor.1, prompt_color_code);
        }
        self.shell_prompt = Some(prompt);
    }

    pub fn handle_input(&mut self, input: u8) -> Option<Vec<u8>> {
        let key_event = KeyEvent::from_scancode(input);
        self.keyboard_state.update(input);
        match key_event {
            KeyEvent::Pressed(Key::CapsLock) => {
                self.caps_lock_active = !self.caps_lock_active;
                None
            }
            KeyEvent::Pressed(u) => {
                let action = self.interpret_key(u);
                self.perform_action(action)
            }
            KeyEvent::Released(_) => None,
        }
    }

    pub fn perform_action(&mut self, action: KeyAction) -> Option<Vec<u8>> {
        match action {
            KeyAction::Type(c) => {
                let (col, row) = self.cursor;
                if col < self.current_prompt.len() {
                    self.clear_from_col(col, row);
                    self.current_prompt.insert(col, c as u8);
                    let following_chars: Vec<_> = self
                        .current_prompt
                        .iter()
                        .enumerate()
                        .skip(col)
                        .map(|(i, &byte)| (i, byte))
                        .collect();
                    for (i, byte) in following_chars {
                        self.set_byte_at(byte, i, row, self.color_code);
                    }
                } else {
                    self.current_prompt.push(c as u8);
                    self.set_byte_at(c as u8, col, row, self.color_code);
                }
                self.set_cursor(col + 1, row);
            }
            KeyAction::Backspace => {
                let (col, row) = self.cursor;
                if col == 0 {
                    return None;
                }
                if col < self.current_prompt.len() {
                    self.clear_from_col(col - 1, row);
                    let following_chars: Vec<_> = self
                        .current_prompt
                        .iter()
                        .enumerate()
                        .skip(col)
                        .map(|(i, &byte)| (i, byte))
                        .collect();
                    for (i, byte) in following_chars {
                        self.set_byte_at(byte, i - 1, row, self.color_code);
                    }
                } else {
                    self.clear_byte_at(col - 1, row);
                }
                self.current_prompt.remove(col - 1);
                self.set_cursor(col - 1, row);
            }
            KeyAction::ArrowLeft => {
                self.set_cursor(self.cursor.0.saturating_sub(1), self.cursor.1);
            }
            KeyAction::ArrowRight => {
                self.set_cursor(self.cursor.0.saturating_add(1), self.cursor.1);
            }
            KeyAction::Enter => {
                self.clear_from_col(0, self.cursor.1);
                let current_prompt = core::mem::take(&mut self.current_prompt);
                self.set_cursor(0, self.cursor.1);
                return Some(current_prompt);
            }
            _ => {}
        }
        None
    }

    fn set_cursor(&mut self, col: usize, row: usize) {
        if col > self.current_prompt.len() {
            return;
        }
        let (current_col, current_row) = self.cursor;
        if let Some(current_char) = self.current_prompt.get(current_col).cloned() {
            self.set_byte_at(current_char, current_col, current_row, self.color_code);
        } else {
            self.clear_byte_at(current_col, current_row);
        }
        let next_char = self.current_prompt.get(col).cloned().unwrap_or(b' ') as char;
        self.cursor = (col, row);
        self.set_byte_at(
            next_char as u8,
            col,
            row,
            ColorCode::new(Color::Black, Color::White),
        );
    }

    fn set_byte_at(&mut self, byte: u8, col: usize, row: usize, color_code: ColorCode) {
        let offset = self.get_offset_col();
        self.writer.set_byte_at(byte, col + offset, row, color_code);
    }

    fn clear_byte_at(&mut self, col: usize, row: usize) {
        let offset = self.get_offset_col();
        self.writer.clear_byte_at(col + offset, row);
    }

    fn clear_from_col(&mut self, col: usize, row: usize) {
        let offset = self.get_offset_col();
        for c in col + offset..offset + self.current_prompt.len() {
            self.writer.clear_byte_at(c, row);
        }
    }

    fn get_offset_col(&self) -> usize {
        self.shell_prompt.as_ref().map_or(0, |p| p.len())
    }

    fn interpret_key(&self, key: Key) -> KeyAction {
        match key {
            Key::Backspace => KeyAction::Backspace,
            Key::Enter => KeyAction::Enter,
            Key::Tab => KeyAction::Tab,
            Key::Up => KeyAction::ArrowUp,
            Key::Down => KeyAction::ArrowDown,
            Key::Left => KeyAction::ArrowLeft,
            Key::Right => KeyAction::ArrowRight,
            c => match c.to_ascii(self.is_uppercase()) {
                Some(c) => KeyAction::Type(c as char), // todo review
                None => KeyAction::Ignore,
            },
        }
    }

    fn is_uppercase(&self) -> bool {
        let state = &self.keyboard_state;
        state.is_pressed(Key::LeftShift)
            || state.is_pressed(Key::RightShift)
            || self.caps_lock_active
    }
}

#[derive(Debug)]
pub enum KeyAction {
    Type(char),
    Backspace,
    Enter,
    Tab,
    ArrowUp,
    ArrowDown,
    ArrowLeft,
    ArrowRight,
    Ignore,
}
