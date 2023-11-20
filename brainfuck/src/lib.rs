//! This crate implements a brainfuck interpreter.

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

/// The `Mmu` trait represents a generic memory management unit.
pub trait Mmu {
    /// Reads byte at `off`.
    fn read_byte(&self, off: usize) -> Result<u8, Error>;

    /// Writes byte `b` at `off`.
    fn write_byte(&mut self, off: usize, b: u8) -> Result<(), Error>;
}

/// Simple memory management unit.
pub struct SimpleMmu {
    mem: Vec<u8>,
}

impl SimpleMmu {
    /// Returns a [`SimpleMmu`] backed by a buffer of `size` bytes initialized to zero.
    pub fn new(size: usize) -> SimpleMmu {
        SimpleMmu {
            mem: vec![0u8; size],
        }
    }

    /// Writes `data` into the memory starting at `off`.
    pub fn write(&mut self, off: usize, data: impl AsRef<[u8]>) -> Result<(), Error> {
        let data = data.as_ref();
        let end = off.checked_add(data.len()).ok_or(Error::Overflow)?;
        self.mem
            .get_mut(off..end)
            .ok_or(Error::OobRange(off, end))?
            .copy_from_slice(data);
        Ok(())
    }
}

impl Mmu for SimpleMmu {
    /// Reads byte at `off`.
    fn read_byte(&self, off: usize) -> Result<u8, Error> {
        let b = *self.mem.get(off).ok_or(Error::Oob(off))?;
        Ok(b)
    }

    /// Writes byte `b` at `off`.
    fn write_byte(&mut self, off: usize, b: u8) -> Result<(), Error> {
        *self.mem.get_mut(off).ok_or(Error::Oob(off))? = b;
        Ok(())
    }
}

/// Brainfuck interpreter.
pub struct Interpreter<M: Mmu, O: OutputStream = NopStream, I: InputStream = NopStream> {
    /// Memory management unit.
    mmu: M,

    /// Program counter.
    pc: usize,

    /// Data pointer.
    ptr: usize,

    /// Output stream handler.
    output_stream: O,

    /// Input stream handler.
    input_stream: I,
}

impl<M: Mmu> Interpreter<M> {
    /// Returns a new brainfuck interpreter. The program counter is initialized to `pc` and the data
    /// pointer is initialized to `ptr`.
    pub fn new(mmu: M, pc: usize, ptr: usize) -> Interpreter<M> {
        Interpreter {
            mmu,
            pc,
            ptr,
            output_stream: NopStream,
            input_stream: NopStream,
        }
    }
}

impl<M: Mmu, O: OutputStream> Interpreter<M, O, NopStream> {
    /// Like [`Interpreter::new`] but allows to specify an output stream.
    pub fn with_output_stream(
        mmu: M,
        pc: usize,
        ptr: usize,
        output_stream: O,
    ) -> Interpreter<M, O, NopStream> {
        Self::with_streams(mmu, pc, ptr, output_stream, NopStream)
    }
}

impl<M: Mmu, I: InputStream> Interpreter<M, NopStream, I> {
    /// Like [`Interpreter::new`] but allows to specify an input stream.
    pub fn with_input_stream(
        mmu: M,
        pc: usize,
        ptr: usize,
        input_stream: I,
    ) -> Interpreter<M, NopStream, I> {
        Self::with_streams(mmu, pc, ptr, NopStream, input_stream)
    }
}

impl<M: Mmu, O: OutputStream, I: InputStream> Interpreter<M, O, I> {
    /// Like [`Interpreter::new`] but allows to specify the I/O streams.
    pub fn with_streams(
        mmu: M,
        pc: usize,
        ptr: usize,
        output_stream: O,
        input_stream: I,
    ) -> Interpreter<M, O, I> {
        Interpreter {
            mmu,
            pc,
            ptr,
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
                let b = self.mmu.read_byte(self.ptr)?;
                self.output_stream.write_byte(b)?
            }
            Instruction::Input => {
                let b = self.input_stream.read_byte()?;
                self.mmu.write_byte(self.ptr, b)?;
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
    use std::rc::Rc;

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

    impl OutputStream for &TestStream {
        fn write_byte(&self, b: u8) -> Result<(), Error> {
            self.buf.borrow_mut().push(b);
            Ok(())
        }
    }

    impl InputStream for &TestStream {
        fn read_byte(&self) -> Result<u8, Error> {
            Ok(0xaa)
        }
    }

    impl Mmu for Rc<RefCell<SimpleMmu>> {
        fn read_byte(&self, off: usize) -> Result<u8, Error> {
            self.borrow().read_byte(off)
        }

        fn write_byte(&mut self, off: usize, b: u8) -> Result<(), Error> {
            self.borrow_mut().write_byte(off, b)
        }
    }

    fn new_test_mmu(data: impl AsRef<[u8]>, size: usize) -> Rc<RefCell<SimpleMmu>> {
        let mut mmu = SimpleMmu::new(size);
        mmu.write(0, data).expect("mmu write");
        Rc::new(RefCell::new(mmu))
    }

    #[test]
    fn run_inst() {
        let mmu = new_test_mmu("+-+++", 16);
        let mut bf = Interpreter::new(Rc::clone(&mmu), 0, 8);
        for _ in 0..5 {
            bf.run_inst().expect("run instruction");
        }
        assert_eq!(mmu.read_byte(8).expect("read byte"), 3);
    }

    #[test]
    fn inc_data_ptr() {
        let mmu = new_test_mmu(">", 16);
        let mut bf = Interpreter::new(mmu, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(bf.ptr, 9);
    }

    #[test]
    fn dec_data_ptr() {
        let mmu = new_test_mmu("<", 16);
        let mut bf = Interpreter::new(mmu, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(bf.ptr, 7);
    }

    #[test]
    fn inc_data() {
        let mmu = new_test_mmu("+", 16);
        let mut bf = Interpreter::new(Rc::clone(&mmu), 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(mmu.read_byte(8).expect("read byte"), 1);
    }

    #[test]
    fn dec_data() {
        let mmu = new_test_mmu("-", 16);
        let mut bf = Interpreter::new(Rc::clone(&mmu), 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(mmu.read_byte(8).expect("read byte"), 0xff);
    }

    #[test]
    fn output_stream() {
        let mmu = new_test_mmu("+++.", 16);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_output_stream(mmu, 0, 8, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(stream.buf(), &[3])
    }

    #[test]
    fn input_stream() {
        let mmu = new_test_mmu(",", 16);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_input_stream(Rc::clone(&mmu), 0, 8, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(mmu.read_byte(8).expect("read byte"), 0xaa);
    }

    #[test]
    fn input_output_streams() {
        let mmu = new_test_mmu(",.", 16);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_streams(mmu, 0, 8, &stream, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(stream.buf(), &[0xaa])
    }

    #[test]
    fn simple_loop() {
        let mmu = new_test_mmu("++++[->+<]", 32);
        let mut bf = Interpreter::new(Rc::clone(&mmu), 0, 16);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(mmu.read_byte(16).expect("read byte"), 0);
        assert_eq!(mmu.read_byte(17).expect("read byte"), 4);
    }

    #[test]
    fn unopened_loop() {
        let mmu = new_test_mmu("+]", 16);
        let mut bf = Interpreter::new(mmu, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::Oob(_))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn unclosed_loop() {
        let mmu = new_test_mmu("[", 16);
        let mut bf = Interpreter::new(mmu, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn missing_open_loop() {
        let mmu = new_test_mmu("[]+]", 16);
        let mut bf = Interpreter::new(mmu, 0, 8);
        let res = bf.run();
        if !matches!(res, Err(Error::Oob(_))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn missing_close_loop() {
        let mmu = new_test_mmu("[[]", 16);
        let mut bf = Interpreter::new(mmu, 0, 8);
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
        let mmu = new_test_mmu(code, 1024);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_output_stream(mmu, 0, 512, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(stream.buf(), b"Hello World!\n");
    }

    #[test]
    fn invalid_inst() {
        let mmu = new_test_mmu("++X", 16);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_output_stream(mmu, 0, 8, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(b'X'))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn invalid_loop_inst() {
        let mmu = new_test_mmu("[X]", 16);
        let stream = TestStream::new();
        let mut bf = Interpreter::with_output_stream(mmu, 0, 8, &stream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(b'X'))) {
            panic!("unexpected result: {res:?}");
        }
    }

    #[test]
    fn nop_stream() {
        let mmu = new_test_mmu("+,.", 16);
        let mut bf = Interpreter::with_streams(Rc::clone(&mmu), 0, 8, NopStream, NopStream);
        let res = bf.run();
        if !matches!(res, Err(Error::InvalidInst(0))) {
            panic!("unexpected result: {res:?}");
        }
        assert_eq!(mmu.read_byte(8).expect("read byte"), 0);
    }

    #[test]
    fn shared_memory() {
        let mut mem = vec![0; 64];
        mem[0] = b'+';
        mem[32] = b'-';

        let mmu = new_test_mmu(&mem, mem.len());

        let mut a = Interpreter::new(Rc::clone(&mmu), 0, 16);
        let mut b = Interpreter::new(Rc::clone(&mmu), 32, 48);

        a.run_inst().expect("a failed to run inst");
        b.run_inst().expect("b failed to run inst");

        assert_eq!(mmu.read_byte(16).expect("read byte"), 1);
        assert_eq!(mmu.read_byte(48).expect("read byte"), 0xff);
    }
}
