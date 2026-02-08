use alloc::vec::Vec;

use crate::{
    println,
    tty::{color::{Color, ColorCode}, keyboard::{Key, KeyEvent, KeyboardState}},
};

pub mod color;
mod font;
pub mod keyboard;
pub mod writer;

pub struct Tty {
    pub writer: writer::TextWriter,
    pub command_handler: Option<fn(&str)>,
    keyboard_state: KeyboardState,
    caps_lock_active: bool,
    cursor: (usize, usize),
    current_prompt: Vec<u8>,
    color_code: ColorCode
}

impl Tty {
    pub fn new(writer: writer::TextWriter, command_handler: Option<fn(&str)>) -> Self {
        Self {
            writer,
            command_handler,
            keyboard_state: KeyboardState::new(),
            caps_lock_active: false,
            cursor: (0, 0),
            current_prompt: alloc::vec![],
            color_code: ColorCode::new(Color::White, Color::Black),
        }
    }

    pub fn handle_input(&mut self, input: u8) {
        let key_event = KeyEvent::from_scancode(input);
        self.keyboard_state.update(input);
        println!("Key event: {:?}", key_event);
        match key_event {
            KeyEvent::Pressed(Key::CapsLock) => {
                self.caps_lock_active = !self.caps_lock_active;
            }
            KeyEvent::Pressed(u) => {
                println!("Cursor before: {:?}", self.cursor);
                let action = self.interpret_key(u);
                self.perform_action(action);
            }
            KeyEvent::Released(_) => {}
        }
    }

    pub fn perform_action(&mut self, action: KeyAction) {
        match action {
            KeyAction::Type(c) => {
                let (col, row) = self.cursor;
                if col < self.current_prompt.len() {
                    self.writer.clear_from_col(col, row);
                    self.current_prompt.insert(col, c as u8);
                    let following_chars = self.current_prompt
                        .iter()
                        .enumerate()
                        .skip(col);
                    for (i, &byte) in following_chars {
                        self.writer.set_byte_at(byte, i, row, self.color_code);
                    }
                } else {
                    self.current_prompt.push(c as u8);
                    self.writer.set_byte_at(c as u8, col, row, self.color_code);
                }
                self.set_cursor(col + 1, row);
            }
            KeyAction::Backspace => {
                let (col, row) = self.cursor;
                if col == 0 {
                    return;
                }
                if col < self.current_prompt.len() {
                    self.writer.clear_from_col(col - 1, row);
                    let following_chars = self.current_prompt
                        .iter()
                        .enumerate()
                        .skip(col);
                    for (i, &byte) in following_chars {
                        self.writer.set_byte_at(byte, i - 1, row, self.color_code);
                    }
                } else {
                    self.writer.clear_byte_at(col - 1, row);
                }
                self.current_prompt.remove(col - 1);
                self.set_cursor(col - 1, row);
            }
            KeyAction::ArrowLeft => {
                self.set_cursor(self.cursor.0.saturating_sub(1), self.cursor.1);
            },
            KeyAction::ArrowRight => {
                self.set_cursor(self.cursor.0.saturating_add(1), self.cursor.1);
            }
            _ => {}
        }
    }

    pub fn set_command_handler(&mut self, handler: Option<fn(&str)>) {
        self.command_handler = handler;
    }
    
    fn set_cursor(&mut self, col: usize, row: usize) {
        if col > self.current_prompt.len() || row > 0 { 
            return;
        }
        let (current_col, current_row) = self.cursor;
        if let Some(current_char) = self.current_prompt.get(current_col).cloned() {
            self.writer.set_byte_at(current_char, current_col, current_row, self.color_code);
        } else {
            self.writer.clear_byte_at(current_col, current_row);
        }
        let next_char = self.current_prompt.get(col).cloned().unwrap_or(b' ') as char;
        self.cursor = (col, row);
        self.writer.set_byte_at(next_char as u8, col, row, ColorCode::new(Color::Black, Color::White));
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

