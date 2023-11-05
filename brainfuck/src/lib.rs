//! This crate implements a brainfuck emulator.

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

/// Memory management unit.
pub struct Mmu {
    /// Backing memory buffer.
    mem: Vec<u8>,
}

impl Mmu {
    /// Returns an MMU backed by a memory buffer of `size` bytes initialized to zeroes.
    pub fn new(size: usize) -> Mmu {
        Mmu {
            mem: vec![0u8; size],
        }
    }

    /// Writes the provided `data` at `off`.
    pub fn write<D: AsRef<[u8]>>(&mut self, off: usize, data: D) -> Result<(), Error> {
        let data = data.as_ref();
        let end = off.checked_add(data.len()).ok_or(Error::Overflow)?;
        self.mem
            .get_mut(off..end)
            .ok_or(Error::OobRange(off, end))?
            .copy_from_slice(data);
        Ok(())
    }

    /// Reads the byte at `off`.
    pub fn read_byte(&self, off: usize) -> Result<u8, Error> {
        let b = self.mem.get(off).ok_or(Error::Oob(off))?;
        Ok(*b)
    }

    /// Writes `b` at `off`.
    pub fn write_byte(&mut self, off: usize, b: u8) -> Result<(), Error> {
        *self.mem.get_mut(off).ok_or(Error::Oob(off))? = b;
        Ok(())
    }
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

/// Brainfuck emulator.
pub struct Emu<'a> {
    /// Program counter.
    pc: usize,

    /// Data pointer.
    ptr: usize,

    /// Memory management unit.
    mmu: Mmu,

    /// Output stream handler.
    output_stream: Option<&'a dyn OutputStream>,

    /// Input stream handler.
    input_stream: Option<&'a dyn InputStream>,
}

impl<'a> Emu<'a> {
    /// Returns a new brainfuck emulator. The program counter is initialized to `pc` and the data
    /// pointer is initialized to `ptr`.
    pub fn new(mmu: Mmu, pc: usize, ptr: usize) -> Emu<'a> {
        Emu {
            pc,
            ptr,
            mmu,
            output_stream: None,
            input_stream: None,
        }
    }

    /// Set output stream handler.
    pub fn output_stream<O: OutputStream>(mut self, stream: &'a O) -> Emu {
        self.output_stream = Some(stream);
        self
    }

    /// Set input stream handler.
    pub fn input_stream<I: InputStream>(mut self, stream: &'a I) -> Emu {
        self.input_stream = Some(stream);
        self
    }

    /// Run code at program counter until error.
    pub fn run(&mut self) -> Result<(), Error> {
        loop {
            self.run_inst()?;
        }
    }

    /// Run a single instruction at program counter.
    fn run_inst(&mut self) -> Result<(), Error> {
        let mut off = 1;

        match self.mmu.read_byte(self.pc)?.try_into()? {
            Instruction::IncPtr => self.ptr = self.ptr.wrapping_add(1),
            Instruction::DecPtr => self.ptr = self.ptr.wrapping_sub(1),
            Instruction::IncData => {
                let b = self.mmu.read_byte(self.ptr)?;
                self.mmu.write_byte(self.ptr, b.wrapping_add(1))?
            }
            Instruction::DecData => {
                let b = self.mmu.read_byte(self.ptr)?;
                self.mmu.write_byte(self.ptr, b.wrapping_sub(1))?
            }
            Instruction::Output => {
                if let Some(stream) = self.output_stream {
                    let b = self.mmu.read_byte(self.ptr)?;
                    stream.write_byte(b)?
                }
            }
            Instruction::Input => {
                if let Some(stream) = self.input_stream {
                    let b = stream.read_byte()?;
                    self.mmu.write_byte(self.ptr, b)?;
                }
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
        let b = self.mmu.read_byte(self.ptr)?;
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
            match self.mmu.read_byte(pc)?.try_into()? {
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

    #[test]
    fn inc_data_ptr() {
        let code = ">";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let mut emu = Emu::new(mmu, 0, 8);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(emu.ptr, 9);
    }

    #[test]
    fn dec_data_ptr() {
        let code = "<";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let mut emu = Emu::new(mmu, 0, 8);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(emu.ptr, 7);
    }

    #[test]
    fn inc_data() {
        let code = "+";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let mut emu = Emu::new(mmu, 0, 8);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(emu.mmu.read_byte(8).unwrap(), 1);
    }

    #[test]
    fn dec_data() {
        let code = "-";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let mut emu = Emu::new(mmu, 0, 8);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(emu.mmu.read_byte(8).unwrap(), 0xff);
    }

    #[test]
    fn output_stream() {
        let code = "+++.";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let stream = TestStream::new();
        let mut emu = Emu::new(mmu, 0, 8).output_stream(&stream);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(stream.buf(), &[3])
    }

    #[test]
    fn input_stream() {
        let code = ",";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let stream = TestStream::new();
        let mut emu = Emu::new(mmu, 0, 8).input_stream(&stream);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(emu.mmu.read_byte(8).unwrap(), 0xaa);
    }

    #[test]
    fn simple_loop() {
        let code = "++++[->+<]";
        let mut mmu = Mmu::new(32);
        mmu.write(0, &code).unwrap();
        let mut emu = Emu::new(mmu, 0, 16);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(emu.mmu.read_byte(16).unwrap(), 0);
        assert_eq!(emu.mmu.read_byte(17).unwrap(), 4);
    }

    #[test]
    fn unopened_loop() {
        let code = "+]";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let mut emu = Emu::new(mmu, 0, 8);
        let res = emu.run();
        if !matches!(res, Err(Error::Oob(_))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn unclosed_loop() {
        let code = "[";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let mut emu = Emu::new(mmu, 0, 8);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn missing_open_loop() {
        let code = "[]+]";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let mut emu = Emu::new(mmu, 0, 8);
        let res = emu.run();
        if !matches!(res, Err(Error::Oob(_))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn missing_close_loop() {
        let code = "[[]";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let mut emu = Emu::new(mmu, 0, 8);
        let res = emu.run();
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
        let mut mmu = Mmu::new(1024);
        mmu.write(0, &code).unwrap();
        let stream = TestStream::new();
        let mut emu = Emu::new(mmu, 0, 512).output_stream(&stream);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(stream.buf(), b"Hello World!\n");
    }

    #[test]
    fn invalid_inst() {
        let code = "++X";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let stream = TestStream::new();
        let mut emu = Emu::new(mmu, 0, 8).output_stream(&stream);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(b'X'))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn invalid_loop_inst() {
        let code = "[X]";
        let mut mmu = Mmu::new(16);
        mmu.write(0, &code).unwrap();
        let stream = TestStream::new();
        let mut emu = Emu::new(mmu, 0, 8).output_stream(&stream);
        let res = emu.run();
        if !matches!(res, Err(Error::InvalidInst(b'X'))) {
            panic!("unexpected result: {res:?}");
        }
    }
}
