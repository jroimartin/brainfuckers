//! This crate implements the battle dynamics.

use std::cell::RefCell;
use std::rc::Rc;

use brainfuck::{Interpreter, Mmu, ReadMode, SimpleMmu};

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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemOp {
    /// Memory access type.
    pub typ: AccessType,

    /// Accessed memory offset.
    pub off: usize,

    /// Warrior ID.
    pub warrior_id: Option<WarriorId>,
}

impl MemOp {
    /// Returns a new [`MemOp`].
    fn new(typ: AccessType, off: usize, warrior_id: Option<WarriorId>) -> MemOp {
        MemOp {
            typ,
            off,
            warrior_id,
        }
    }
}

/// Memory access type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccessType {
    /// Read data.
    Read,

    /// Write data.
    Write,

    /// Read instruction.
    Exec,
}

/// Memory management unit that wraps [`SimpleMmu`] to add logging capabilities.
struct ArenaMmu {
    /// Warrior ID.
    warrior_id: Option<WarriorId>,

    /// Wrapped mmu.
    mmu: Rc<RefCell<SimpleMmu>>,

    /// Memory operations.
    ops: Rc<RefCell<Vec<MemOp>>>,
}

impl ArenaMmu {
    /// Returns a new [`ArenaMmu`].
    fn new(size: usize) -> ArenaMmu {
        ArenaMmu {
            warrior_id: None,
            mmu: Rc::new(RefCell::new(SimpleMmu::new(size))),
            ops: Rc::new(RefCell::new(Vec::new())),
        }
    }

    /// Writes `data` into the memory starting at `off`.
    fn write(&self, off: usize, data: impl AsRef<[u8]>) -> Result<(), Error> {
        Ok(self.mmu.borrow_mut().write(off, data)?)
    }

    /// Returns the executed memory operations.
    fn ops(&self) -> Vec<MemOp> {
        self.ops.borrow().to_vec()
    }

    /// Returns a new reference to the MMU. This reference is linked to the provided warrior.
    fn clone(&self, warrior_id: WarriorId) -> ArenaMmu {
        ArenaMmu {
            warrior_id: Some(warrior_id),
            mmu: Rc::clone(&self.mmu),
            ops: Rc::clone(&self.ops),
        }
    }
}

impl Mmu for ArenaMmu {
    /// Reads a byte from memory and logs the operation.
    fn read_byte(&self, off: usize, mode: ReadMode) -> Result<u8, brainfuck::Error> {
        let mut ops = self.ops.borrow_mut();
        match mode {
            ReadMode::Inst => ops.push(MemOp::new(AccessType::Exec, off, self.warrior_id)),
            ReadMode::Data => ops.push(MemOp::new(AccessType::Read, off, self.warrior_id)),
            _ => {}
        };
        self.mmu.borrow().read_byte(off, mode)
    }

    /// Writes a byte into memory and logs the operation.
    fn write_byte(&mut self, off: usize, b: u8) -> Result<(), brainfuck::Error> {
        self.ops
            .borrow_mut()
            .push(MemOp::new(AccessType::Write, off, self.warrior_id));
        self.mmu.borrow_mut().write_byte(off, b)
    }
}

/// Warrior ID.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WarriorId(pub usize);

/// The state of a warrior.
enum WarriorState {
    /// The warrior is still alive.
    Alive,

    /// The warrior is dead. They lost on the specified tick due to the specified error.
    Dead(brainfuck::Error, u64),
}

/// Represents a battle program.
struct Warrior {
    /// Warrior ID.
    id: WarriorId,

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
        id: WarriorId,
        mmu: ArenaMmu,
        program: impl AsRef<[u8]>,
        rsv: usize,
    ) -> Result<Warrior, Error> {
        let prog = program.as_ref();
        if prog.len() > rsv {
            return Err(Error::InvalidSize);
        }

        let pc = id.0 * rsv;
        let ptr = pc + prog.len();
        mmu.write(pc, prog)?;
        let bf = Interpreter::new(mmu.clone(id), pc, ptr);

        Ok(Warrior {
            state: WarriorState::Alive,
            id,
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
#[derive(Debug, PartialEq, Eq)]
pub enum BattleState {
    /// The specified warrior won.
    Winner(WarriorId),

    /// The specified warriors were the last ones alive and died on the same cycle.
    Tie(Vec<WarriorId>),

    /// The battle timed out. The specified warriors remained alive.
    Timeout(Vec<WarriorId>),

    /// The battle is still ongoing.
    Ongoing,

    /// The battle is over.
    Over,
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

    /// The battle is over.
    is_over: bool,
}

impl Arena {
    /// Returns a new [`Arena`].
    pub fn new(
        size: usize,
        cycles: u64,
        programs: impl IntoIterator<Item = impl AsRef<[u8]>>,
    ) -> Result<Arena, Error> {
        let programs = programs
            .into_iter()
            .map(|prog| prog.as_ref().to_vec())
            .collect::<Vec<Vec<u8>>>();

        let rsv = size / programs.len();
        let mmu = ArenaMmu::new(size);

        let warriors = programs
            .iter()
            .enumerate()
            .map(|(i, prog)| Warrior::new(WarriorId(i), mmu.clone(WarriorId(i)), prog, rsv))
            .collect::<Result<Vec<Warrior>, Error>>()?;

        Ok(Arena {
            curtick: 0,
            is_over: false,
            cycles,
            warriors,
            mmu,
        })
    }

    /// Returns the executed memory operations.
    pub fn memops(&self) -> Vec<MemOp> {
        self.mmu.ops()
    }

    /// Runs one tick.
    pub fn tick(&mut self) -> BattleState {
        if self.is_over {
            return BattleState::Over;
        }

        if self.curtick > self.cycles {
            let survivors = self
                .warriors
                .iter()
                .filter(|warrior| warrior.is_alive())
                .map(|warrior| warrior.id)
                .collect::<Vec<WarriorId>>();
            self.is_over = true;
            return BattleState::Timeout(survivors);
        }

        let mut deaths = Vec::new();
        let mut survivors = Vec::new();
        for warrior in &mut self.warriors {
            if !warrior.is_alive() {
                continue;
            }
            match warrior.bf.run_inst() {
                Ok(_) => survivors.push(warrior.id),
                Err(err) => {
                    warrior.kill(err, self.curtick);
                    deaths.push(warrior.id);
                }
            }
        }

        match survivors.len() {
            0 => {
                self.is_over = true;
                BattleState::Tie(deaths)
            }
            1 => {
                self.is_over = true;
                BattleState::Winner(survivors[0])
            }
            _ => {
                self.curtick += 1;
                BattleState::Ongoing
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tie() {
        let w0 = "";
        let w1 = "";

        let mut arena = Arena::new(8192, 1, &[w0, w1]).expect("new arena");
        loop {
            match arena.tick() {
                BattleState::Tie(warriors) => {
                    assert_eq!(warriors, &[WarriorId(0), WarriorId(1)]);
                    break;
                }
                BattleState::Ongoing => {}
                other => panic!("unexpected state: {:?}", other),
            }
        }
    }

    #[test]
    fn timeout() {
        let w0 = "+[]";
        let w1 = "+[]";

        let mut arena = Arena::new(8192, 100, &[w0, w1]).expect("new arena");
        loop {
            match arena.tick() {
                BattleState::Timeout(_) => break,
                BattleState::Ongoing => {}
                other => panic!("unexpected state: {:?}", other),
            }
        }
    }

    #[test]
    fn winner() {
        let w0 = "+[>+]";
        let w1 = "+[]";

        let mut arena = Arena::new(8192, 16_000, &[w0, w1]).expect("new arena");
        loop {
            match arena.tick() {
                BattleState::Winner(WarriorId(0)) => break,
                BattleState::Ongoing => {}
                other => panic!("unexpected state: {:?}", other),
            }
        }
    }

    #[test]
    fn over() {
        let w0 = "";
        let w1 = "";

        let mut arena = Arena::new(8192, 1, &[w0, w1]).expect("new arena");
        arena.tick();
        assert_eq!(arena.tick(), BattleState::Over);
        assert_eq!(arena.tick(), BattleState::Over);
    }

    #[test]
    fn memops() {
        let w0 = "+";
        let w1 = ">";

        let mut arena = Arena::new(8192, 100, &[w0, w1]).expect("new arena");
        arena.tick();
        let expected = vec![
            MemOp {
                typ: AccessType::Exec,
                off: 0,
                warrior_id: Some(WarriorId(0)),
            },
            MemOp {
                typ: AccessType::Read,
                off: 1,
                warrior_id: Some(WarriorId(0)),
            },
            MemOp {
                typ: AccessType::Write,
                off: 1,
                warrior_id: Some(WarriorId(0)),
            },
            MemOp {
                typ: AccessType::Exec,
                off: 4096,
                warrior_id: Some(WarriorId(1)),
            },
        ];
        assert_eq!(arena.memops(), expected);
    }
}
