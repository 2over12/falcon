//! Loading executable binaries into Falcon.
//!
//! ```
//! # use falcon::error::*;
//! use falcon::loader::Elf;
//! use falcon::loader::Loader;
//! use std::path::Path;
//!
//! # fn example () -> Result<()> {
//! // Load an elf for analysis
//! let elf = Elf::from_file(Path::new("test_binaries/simple-0/simple-0"))?;
//! // Lift a program from the elf
//! let program = elf.program()?;
//! for function in program.functions() {
//!     println!("0x{:08x}: {}", function.address(), function.name());
//! }
//! # Ok(())
//! # }
//! ```

use architecture::Architecture;
use error::*;
use executor::eval;
use il;
use memory;
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::fmt;

mod elf;
mod json;
mod pe;
mod symbol;

pub use self::elf::*;
pub use self::json::*;
pub use self::pe::*;
pub use self::symbol::Symbol;

/// A declared entry point for a function.
#[derive(Clone, Debug, PartialEq)]
pub struct FunctionEntry {
    address: u64,
    name: Option<String>,
}

impl FunctionEntry {
    /// Create a new `FunctionEntry`.
    ///
    /// If no name is provided: `sup_{:X}` will be used to name the function.
    pub fn new(address: u64, name: Option<String>) -> FunctionEntry {
        FunctionEntry {
            address: address,
            name: name,
        }
    }

    /// Get the address for this `FunctionEntry`.
    pub fn address(&self) -> u64 {
        self.address
    }

    /// Get the name for this `FunctionEntry`.
    pub fn name(&self) -> Option<&str> {
        self.name.as_ref().map(|s| s.as_str())
    }
}

impl fmt::Display for FunctionEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.name {
            Some(ref name) => write!(f, "FunctionEntry({} -> 0x{:X})", name, self.address),
            None => write!(f, "FunctionEntry(0x{:X})", self.address),
        }
    }
}

/// Generic trait for all loaders
pub trait Loader: fmt::Debug + Send + Sync {
    /// Get a model of the memory contained in the binary
    fn memory(&self) -> Result<memory::backing::Memory>;

    /// Get addresses for known function entries
    fn function_entries(&self) -> Result<Vec<FunctionEntry>>;

    /// The address program execution should begin at
    fn program_entry(&self) -> u64;

    /// Get the architecture of the binary
    fn architecture(&self) -> &Architecture;

    /// Lift just one function from the executable
    fn function(&self, address: u64) -> Result<il::Function> {
        let translator = self.architecture().translator();
        let memory = self.memory()?;
        Ok(translator.translate_function(&memory, address)?)
    }

    /// Cast loader to `Any`
    fn as_any(&self) -> &Any;

    /// Get the symbols for this loader
    fn symbols(&self) -> Vec<Symbol>;

    /// Get the symbols as a hashmap by address
    fn symbols_map(&self) -> HashMap<u64, Symbol> {
        self.symbols()
            .into_iter()
            .map(|symbol| (symbol.address(), symbol))
            .collect()
    }

    /// Lift executable into an il::Program
    fn program(&self) -> Result<il::Program> {
        // Get out architecture-specific translator
        let translator = self.architecture().translator();

        // Create a mapping of the file memory
        let memory = self.memory()?;

        let mut program = il::Program::new();

        for function_entry in self.function_entries()? {
            let address = function_entry.address();
            // Ensure this memory is marked executable
            if memory
                .permissions(address)
                .map_or(false, |p| p.contains(memory::MemoryPermissions::EXECUTE))
            {
                let mut function = match translator.translate_function(&memory, address) {
                    Ok(function) => function,
                    Err(e) => match e {
                        Error(ErrorKind::CapstoneError, _) => {
                            eprintln!("Capstone failure, 0x{:x}", address);
                            continue;
                        }
                        _ => return Err(e),
                    },
                };
                function.set_name(function_entry.name().map(|n| n.to_string()));
                program.add_function(function);
            }
        }

        Ok(program)
    }

    /// Lift executable into an `il::Program`, while recursively resolving branch
    /// targets into functions.
    fn program_recursive(&self) -> Result<il::Program> {
        fn call_targets(function: &il::Function) -> Result<Vec<u64>> {
            let call_targets =
                function
                    .blocks()
                    .iter()
                    .fold(Vec::new(), |mut call_targets, block| {
                        block.instructions().iter().for_each(|instruction| {
                            match *instruction.operation() {
                                il::Operation::Branch { ref target } => {
                                    eval(target).ok().map(|constant| {
                                        call_targets.push(constant.value_u64().unwrap())
                                    });
                                }
                                _ => {}
                            }
                        });
                        call_targets
                    });
            Ok(call_targets)
        }

        let mut program = self.program()?;

        let mut processed = HashSet::new();

        loop {
            let function_addresses = program
                .functions()
                .into_iter()
                .map(|function| function.address())
                .collect::<Vec<u64>>();

            let addresses = {
                let functions = program
                    .functions()
                    .into_iter()
                    .filter(|function| !processed.contains(&function.address()))
                    .collect::<Vec<&il::Function>>();

                functions.iter().for_each(|function| {
                    processed.insert(function.address());
                });

                let addresses = functions
                    .into_iter()
                    .fold(HashSet::new(), |mut targets, function| {
                        call_targets(function)
                            .unwrap()
                            .into_iter()
                            .for_each(|target| {
                                targets.insert(target);
                            });
                        targets
                    })
                    .into_iter()
                    .filter(|address| !function_addresses.contains(address))
                    .collect::<Vec<u64>>();

                if addresses.is_empty() {
                    break;
                }

                addresses
            };

            for address in addresses {
                let function = match self.function(address) {
                    Ok(function) => function,
                    Err(e) => match e {
                        Error(ErrorKind::CapstoneError, _) => {
                            eprintln!("Capstone failure, 0x{:x}", address);
                            continue;
                        }
                        _ => return Err(e),
                    },
                };
                program.add_function(function);
            }
        }

        Ok(program)
    }
}
