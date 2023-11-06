//! This crate implements a brainfuck interpreter.

use std::sync::{Arc, Mutex};

/// Error type.
#[derive(Debug)]
pub enum Error {
    /// Out-of-bounds offset.
    Oob(usize),

    /// Out-of-bounds range.
    OobRange(usize, usize),

    /// Arithmetic overflow.
    Overflow,

    /// Invalid instruction.
    InvalidInst(u8),

    /// Invalid loop state.
    InvalidLoopState,
}

/// Brainfuck instruction.
enum Instruction {
    /// Increment data pointer (`>`).
    IncPtr,

    /// Decrement data pointer (`<`).
    DecPtr,

    /// Increment data byte (`+`).
    IncData,

    /// Decrement data byte (`-`).
    DecData,

    /// Write byte to output stream (`.`).
    Output,

    /// Read byte from input stream (`,`).
    Input,

    /// Start loop (`[`).
    StartLoop,

    /// End loop (`]`).
    EndLoop,

    /// No operation (` `, `\t`, `\n`).
    Nop,
}

impl TryFrom<u8> for Instruction {
    type Error = Error;

    fn try_from(value: u8) -> Result<Instruction, Error> {
        match value {
            b'>' => Ok(Instruction::IncPtr),
            b'<' => Ok(Instruction::DecPtr),
            b'+' => Ok(Instruction::IncData),
            b'-' => Ok(Instruction::DecData),
            b'.' => Ok(Instruction::Output),
            b',' => Ok(Instruction::Input),
            b'[' => Ok(Instruction::StartLoop),
            b']' => Ok(Instruction::EndLoop),
            b' ' | b'\t' | b'\n' => Ok(Instruction::Nop),
            _ => Err(Error::InvalidInst(value)),
        }
    }
}

/// Loop position.
enum LoopAt {
    /// Start of the loop.
    Start,

    /// End of the loop.
    End,
}

/// The `OutputStream` trait allows for writing bytes to an output stream.
pub trait OutputStream {
    /// Writes a byte to the output stream.
    fn write_byte(&self, b: u8) -> Result<(), Error>;
}

/// The `InputStream` trait allows for reading bytes from an input stream.
pub trait InputStream {
    /// Reads a byte from the input stream.
    fn read_byte(&self) -> Result<u8, Error>;
}

/// No operation I/O stream.
pub struct NopStream;

impl OutputStream for NopStream {
    fn write_byte(&self, _b: u8) -> Result<(), Error> {
        Ok(())
    }
}

impl InputStream for NopStream {
    fn read_byte(&self) -> Result<u8, Error> {
        Ok(0)
    }
}

/// Brainfuck interpreter.
pub struct Interpreter<'a, O: OutputStream = NopStream, I: InputStream = NopStream> {
    /// Program counter.
    pc: usize,

    /// Data pointer.
    ptr: usize,

    /// Memory buffer.
    mem: Arc<Mutex<Vec<u8>>>,

    /// Output stream handler.
    output_stream: &'a O,

    /// Input stream handler.
    input_stream: &'a I,
}

impl<'a> Interpreter<'a> {
    /// Returns a new brainfuck interpreter. The program counter is initialized to `pc` and the data
    /// pointer is initialized to `ptr`.
    pub fn new(mem: Arc<Mutex<Vec<u8>>>, pc: usize, ptr: usize) -> Interpreter<'a> {
        Interpreter {
            pc,
            ptr,
            mem,
            output_stream: &NopStream,
            input_stream: &NopStream,
        }
    }
}

impl<'a, O: OutputStream> Interpreter<'a, O, NopStream> {
    /// Like [`Interpreter::new`] but allows to specify an output stream.
    pub fn with_output_stream(
        mem: Arc<Mutex<Vec<u8>>>,
        pc: usize,
        ptr: usize,
        output_stream: &'a O,
    ) -> Interpreter<'a, O, NopStream> {
        Self::with_streams(mem, pc, ptr, output_stream, &NopStream)
    }
}

impl<'a, I: InputStream> Interpreter<'a, NopStream, I> {
    /// Like [`Interpreter::new`] but allows to specify an input stream.
    pub fn with_input_stream(
        mem: Arc<Mutex<Vec<u8>>>,
        pc: usize,
        ptr: usize,
        input_stream: &'a I,
    ) -> Interpreter<'a, NopStream, I> {
        Self::with_streams(mem, pc, ptr, &NopStream, input_stream)
    }
}

impl<'a, O: OutputStream, I: InputStream> Interpreter<'a, O, I> {
    /// Like [`Interpreter::new`] but allows to specify the I/O streams.
    pub fn with_streams(
        mem: Arc<Mutex<Vec<u8>>>,
        pc: usize,
        ptr: usize,
        output_stream: &'a O,
        input_stream: &'a I,
    ) -> Interpreter<'a, O, I> {
        Interpreter {
            pc,
            ptr,
            mem,
            output_stream,
            input_stream,
        }
    }

    /// Run code at program counter until error.
    pub fn run(&mut self) -> Result<(), Error> {
        loop {
            self.run_inst()?;
        }
    }

    /// Run a single instruction at program counter.
    pub fn run_inst(&mut self) -> Result<(), Error> {
        let mut off = 1;

        match self.read_byte(self.pc)?.try_into()? {
            Instruction::IncPtr => self.ptr = self.ptr.wrapping_add(1),
            Instruction::DecPtr => self.ptr = self.ptr.wrapping_sub(1),
            Instruction::IncData => {
                let b = self.read_byte(self.ptr)?;
                self.write_byte(self.ptr, b.wrapping_add(1))?
            }
            Instruction::DecData => {
                let b = self.read_byte(self.ptr)?;
                self.write_byte(self.ptr, b.wrapping_sub(1))?
            }
            Instruction::Output => {
                let b = self.read_byte(self.ptr)?;
                self.output_stream.write_byte(b)?
            }
            Instruction::Input => {
                let b = self.input_stream.read_byte()?;
                self.write_byte(self.ptr, b)?;
            }
            Instruction::StartLoop => off = self.jump_offset(LoopAt::Start)?,
            Instruction::EndLoop => off = self.jump_offset(LoopAt::End)?,
            Instruction::Nop => {}
        }

        self.pc = self.pc.wrapping_add_signed(off);
        Ok(())
    }

    /// Returns the offset to the next instruction depending on the current state.
    fn jump_offset(&self, at: LoopAt) -> Result<isize, Error> {
        let b = self.read_byte(self.ptr)?;
        let (jump, step, delta) = match at {
            LoopAt::Start => (b == 0, 1, 0),
            LoopAt::End => (b != 0, -1, 2),
        };

        if !jump {
            return Ok(1);
        }

        let mut ctr: usize = 0;
        let mut off: isize = 0;
        loop {
            let pc = self.pc.wrapping_add_signed(off);
            match self.read_byte(pc)?.try_into()? {
                Instruction::StartLoop => {
                    ctr = ctr
                        .checked_add_signed(step)
                        .ok_or(Error::InvalidLoopState)?
                }
                Instruction::EndLoop => {
                    ctr = ctr
                        .checked_add_signed(-step)
                        .ok_or(Error::InvalidLoopState)?
                }
                _ => {}
            }
            off = off.checked_add(step).ok_or(Error::Overflow)?;

            if ctr == 0 {
                break;
            }
        }

        off.checked_add(delta).ok_or(Error::Overflow)
    }

    /// Reads the byte at `off`.
    ///
    /// # Panics
    ///
    /// Panics if the memory lock cannot be acquired.
    fn read_byte(&self, off: usize) -> Result<u8, Error> {
        let mem = self.mem.lock().expect("acquire lock");
        let b = mem.get(off).ok_or(Error::Oob(off))?;
        Ok(*b)
    }

    /// Writes `b` at `off`.
    ///
    /// # Panics
    ///
    /// Panics if the memory lock cannot be acquired.
    fn write_byte(&mut self, off: usize, b: u8) -> Result<(), Error> {
        let mut mem = self.mem.lock().expect("acquire lock");
        *mem.get_mut(off).ok_or(Error::Oob(off))? = b;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;

    struct TestStream {
        buf: RefCell<Vec<u8>>,
    }

    impl TestStream {
        fn new() -> TestStream {
            TestStream {
                buf: RefCell::new(Vec::new()),
            }
        }

        fn buf(&self) -> Vec<u8> {
            return self.buf.borrow().clone();
        }
    }

    impl OutputStream for TestStream {
        fn write_byte(&self, b: u8) -> Result<(), Error> {
            self.buf.borrow_mut().push(b);
            Ok(())
        }
    }

    impl InputStream for TestStream {
        fn read_byte(&self) -> Result<u8, Error> {
            Ok(0xaa)
        }
    }

    fn new_mem<D: AsRef<[u8]>>(data: D, size: usize) -> Arc<Mutex<Vec<u8>>> {
        let data = data.as_ref();
        let mut mem = vec![0; size];
        mem.get_mut(..data.len())
            .expect("get mut slice range")
            .copy_from_slice(data);
        Arc::new(Mutex::new(mem))
    }

    #[test]
    fn run_inst() {
        let mem = new_mem("+-+++", 16);
        let mut bf = Interpreter::new(Arc::clone(&mem), 0, 8);
        for _ in 0..5 {
            bf.run_inst().expect("run instruction");
        }
        assert_eq!(
            mem.lock().expect("acquire lock").get(8).expect("read byte"),
            &3
        );
    }

    #[test]
    fn inc_data_ptr() {
        let mem = new_mem(">", 16);
        let mut bf = Interpreter::new(mem, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(bf.ptr, 9);
    }

    #[test]
    fn dec_data_ptr() {
        let mem = new_mem("<", 16);
        let mut bf = Interpreter::new(mem, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(bf.ptr, 7);
    }

    #[test]
    fn inc_data() {
        let mem = new_mem("+", 16);
        let mut bf = Interpreter::new(Arc::clone(&mem), 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(
            mem.lock().expect("acquire lock").get(8).expect("read byte"),
            &1
        );
    }

    #[test]
    fn dec_data() {
        let mem = new_mem("-", 16);
        let mut bf = Interpreter::new(Arc::clone(&mem), 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(
            mem.lock().expect("acquire lock").get(8).expect("read byte"),
            &0xff
        );
    }

    #[test]
    fn output_stream() {
        let mem = new_mem("+++.", 16);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_output_stream(mem, 0, 8, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(stream.buf(), &[3])
    }

    #[test]
    fn input_stream() {
        let mem = new_mem(",", 16);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_input_stream(Arc::clone(&mem), 0, 8, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(
            mem.lock().expect("acquire lock").get(8).expect("read byte"),
            &0xaa
        );
    }

    #[test]
    fn simple_loop() {
        let mem = new_mem("++++[->+<]", 32);
        let mut bf = Interpreter::new(Arc::clone(&mem), 0, 16);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(
            mem.lock()
                .expect("acquire lock")
                .get(16..=17)
                .expect("read range"),
            &[0, 4]
        );
    }

    #[test]
    fn unopened_loop() {
        let mem = new_mem("+]", 16);
        let mut bf = Interpreter::new(mem, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::Oob(_))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn unclosed_loop() {
        let mem = new_mem("[", 16);
        let mut bf = Interpreter::new(mem, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn missing_open_loop() {
        let mem = new_mem("[]+]", 16);
        let mut bf = Interpreter::new(mem, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::Oob(_))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn missing_close_loop() {
        let mem = new_mem("[[]", 16);
        let mut bf = Interpreter::new(mem, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn hello_world() {
        let code = r#"
            ++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>
            ---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++.
        "#;
        let mem = new_mem(code, 1024);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_output_stream(mem, 0, 512, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(stream.buf(), b"Hello World!\n");
    }

    #[test]
    fn invalid_inst() {
        let mem = new_mem("++X", 16);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_output_stream(mem, 0, 8, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(b'X'))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn invalid_loop_inst() {
        let mem = new_mem("[X]", 16);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_output_stream(mem, 0, 8, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(b'X'))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn nop_stream() {
        let mem = new_mem("+,.", 16);
        let stream = NopStream;
        let mut bf = Interpreter::with_streams(Arc::clone(&mem), 0, 8, &stream, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(
            mem.lock().expect("acquire lock").get(8).expect("read byte"),
            &0
        );
    }
}
