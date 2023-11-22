//! This crate implements the brainfucke.rs game dynamics.

use std::cell::RefCell;
use std::rc::Rc;

use brainfuck::{Interpreter, Mmu, SimpleMmu};

/// The default maximum number of cycles.
pub const DEFAULT_NUM_CYCLES: u64 = 8192;

/// Arena error.
#[derive(Debug)]
pub enum Error {
    /// Brainfuck error.
    Brainfuck(brainfuck::Error),

    /// The program is too big.
    InvalidSize,
}

impl From<brainfuck::Error> for Error {
    fn from(err: brainfuck::Error) -> Error {
        Error::Brainfuck(err)
    }
}

/// Memory operation.
pub enum MemOp {
    /// Read access. It provides the memory offset being read and the returned byte.
    Read(usize, u8),

    /// Write access. It provides the memory offset being written and the stored byte.
    Write(usize, u8),
}

/// Memory management unit that wraps [`SimpleMmu`] to add logging capabilities.
struct ArenaMmu {
    /// Wrapped mmu.
    mmu: Rc<RefCell<SimpleMmu>>,

    /// Memory operations.
    ops: Rc<RefCell<Vec<MemOp>>>,
}

impl ArenaMmu {
    /// Returns a new [`ArenaMmu`].
    fn new(size: usize) -> ArenaMmu {
        ArenaMmu {
            mmu: Rc::new(RefCell::new(SimpleMmu::new(size))),
            ops: Rc::new(RefCell::new(Vec::new())),
        }
    }

    /// Writes `data` into the memory starting at `off`.
    fn write(&self, off: usize, data: impl AsRef<[u8]>) -> Result<(), Error> {
        Ok(self.mmu.borrow_mut().write(off, data)?)
    }

    /// Pops a memory operation from the log.
    fn pop_mem_operation(&self) -> Option<MemOp> {
        self.ops.borrow_mut().pop()
    }
}

impl Clone for ArenaMmu {
    /// Returns a new reference to the MMU.
    fn clone(&self) -> ArenaMmu {
        ArenaMmu {
            mmu: Rc::clone(&self.mmu),
            ops: Rc::clone(&self.ops),
        }
    }
}

impl Mmu for ArenaMmu {
    /// Reads a byte from memory and logs the operation.
    fn read_byte(&self, off: usize) -> Result<u8, brainfuck::Error> {
        let b = self.mmu.borrow().read_byte(off)?;
        self.ops.borrow_mut().push(MemOp::Read(off, b));
        Ok(b)
    }

    /// Writes a byte into memory and logs the operation.
    fn write_byte(&mut self, off: usize, b: u8) -> Result<(), brainfuck::Error> {
        self.ops.borrow_mut().push(MemOp::Write(off, b));
        self.mmu.borrow_mut().write_byte(off, b)
    }
}

/// The state of a warrior.
enum WarriorState {
    /// The warrior is still alive.
    Alive,

    /// The warrior is dead. They lost on the specified tick due to the specified error.
    Dead(brainfuck::Error, u64),
}

/// Represents a battle program.
struct Warrior {
    /// Warrior index.
    idx: usize,

    /// The brainfuck interpreter handling the warrior code.
    bf: Interpreter<ArenaMmu>,

    /// The state of the warrior.
    state: WarriorState,
}

impl Warrior {
    /// Returns a new [`Warrior`]. `idx` is used as an index to calculate the location where the
    /// provided `program` must be copied into the `mmu` memory. If the program size is bigger than
    /// `rsv` bytes it returns error.
    fn new(
        idx: usize,
        mmu: ArenaMmu,
        program: impl AsRef<[u8]>,
        rsv: usize,
    ) -> Result<Warrior, Error> {
        let prog = program.as_ref();
        if prog.len() > rsv {
            return Err(Error::InvalidSize);
        }

        let pc = idx * rsv;
        let ptr = pc + prog.len();
        mmu.write(pc, prog)?;
        let bf = Interpreter::new(mmu.clone(), pc, ptr);

        Ok(Warrior {
            state: WarriorState::Alive,
            idx,
            bf,
        })
    }

    /// Sets the warrior state to dead.
    fn kill(&mut self, err: brainfuck::Error, ntick: u64) {
        self.state = WarriorState::Dead(err, ntick);
    }

    /// Returns wether the warrior is still alive.
    fn is_alive(&self) -> bool {
        matches!(self.state, WarriorState::Alive)
    }
}

/// State of the battle after a tick.
#[derive(Debug)]
pub enum BattleState {
    /// The warrior with the specified index is the winner.
    Winner(usize),

    /// All the warriors died on the same cycle.
    Tie,

    /// The battle timed out.
    Timeout,

    /// The battle is still ongoing.
    Ongoing,
}

/// The arena where the programs fight each other.
pub struct Arena {
    /// Number of cycles before the fight is considered tied.
    cycles: u64,

    /// Current tick number.
    curtick: u64,

    /// Battle programs.
    warriors: Vec<Warrior>,

    /// Shared memory.
    mmu: ArenaMmu,
}

impl Arena {
    /// Returns a new [`Arena`].
    pub fn new(
        size: usize,
        programs: impl IntoIterator<Item = impl AsRef<[u8]>>,
    ) -> Result<Arena, Error> {
        let programs = programs
            .into_iter()
            .map(|prog| prog.as_ref().to_owned())
            .collect::<Vec<Vec<u8>>>();

        let rsv = size / programs.len();
        let mmu = ArenaMmu::new(size);

        let warriors = programs
            .iter()
            .enumerate()
            .map(|(i, prog)| Warrior::new(i, mmu.clone(), prog, rsv))
            .collect::<Result<Vec<Warrior>, Error>>()?;

        Ok(Arena {
            cycles: DEFAULT_NUM_CYCLES,
            curtick: 0,
            warriors,
            mmu,
        })
    }

    /// Sets the number of cycles before the fight is considered tied.
    pub fn cycles(&mut self, cycles: u64) -> &mut Arena {
        self.cycles = cycles;
        self
    }

    /// Pops a memory operation from the log.
    pub fn pop_mem_operation(&self) -> Option<MemOp> {
        self.mmu.pop_mem_operation()
    }

    /// Runs one tick.
    pub fn tick(&mut self) -> BattleState {
        let alive = self
            .warriors
            .iter()
            .filter(|warrior| warrior.is_alive())
            .map(|warrior| warrior.idx)
            .collect::<Vec<usize>>();

        match alive.len() {
            0 => return BattleState::Tie,
            1 => return BattleState::Winner(alive[0]),
            _ => {}
        }

        if self.curtick > self.cycles {
            return BattleState::Timeout;
        }

        for warrior in &mut self.warriors {
            if !warrior.is_alive() {
                continue;
            }
            match warrior.bf.run_inst() {
                Ok(_) => {}
                Err(err) => warrior.kill(err, self.curtick),
            }
        }
        self.curtick += 1;

        BattleState::Ongoing
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tie() {
        let w1 = "";
        let w2 = "";

        let mut arena = Arena::new(8192, &[w1, w2]).expect("new arena");
        loop {
            match arena.tick() {
                BattleState::Tie => break,
                BattleState::Ongoing => {}
                other => panic!("unexpected state: {:?}", other),
            }
        }
    }

    #[test]
    fn timeout() {
        let w1 = "+[]";
        let w2 = "+[]";

        let mut arena = Arena::new(8192, &[w1, w2]).expect("new arena");
        loop {
            match arena.tick() {
                BattleState::Timeout => break,
                BattleState::Ongoing => {}
                other => panic!("unexpected state: {:?}", other),
            }
        }
    }

    #[test]
    fn winner() {
        let w1 = "+[>+]";
        let w2 = "+[]";

        let mut arena = Arena::new(8192, &[w1, w2]).expect("new arena");
        let arena = arena.cycles(16_000);
        loop {
            match arena.tick() {
                BattleState::Winner(0) => break,
                BattleState::Ongoing => {}
                other => panic!("unexpected state: {:?}", other),
            }
        }
    }
}
