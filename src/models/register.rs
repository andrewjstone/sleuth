use ::*;

/// A single register that handles Put and Get operations
#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Register {
    val: usize
}

impl Register {
    pub fn new() -> Register {
        Register {
            val: 0
        }
    }

    pub fn put(&self, val: usize) -> Register {
        Register {
            val: val
        }
    }
}

impl Model for Register {
    type Call = Call;
    type Return = Option<usize>;

    fn apply(&self, call: &Call, rv: &Option<usize>) -> (bool, Self) {
        match *call {
            Call::Put(val) => (true, self.put(val)),
            Call::Get => (*rv == Some(self.val), self.clone())
        }
    }
}


/// An operation on a Register
#[derive(Debug)]
pub enum Call {
    Put(usize),
    Get
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    // This history consists of two concurrent increments, followed by a get with the correct value
    fn linearizable_events() -> Vec<Event<Register>> {
        vec![
            Event {
                client_id: 1,
                time: Instant::now(),
                op: Op::Call(Call::Put(1))
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Call(Call::Put(2))
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Return(None)
            },
            Event {
                client_id: 1,
                time: Instant::now(),
                op: Op::Return(None)
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Call(Call::Get)
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Return(Some(2))
            }
        ]
    }

    // This history consists of two concurrent increments, followed by a get with the incorrect value
    fn non_linearizable_events() -> Vec<Event<Register>> {
        vec![
            Event {
                client_id: 1,
                time: Instant::now(),
                op: Op::Call(Call::Put(1))
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Call(Call::Put(2))
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Return(None)
            },
            Event {
                client_id: 1,
                time: Instant::now(),
                op: Op::Return(None)
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Call(Call::Get)
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Return(Some(0))
            }
        ]
    }

    #[test]
    fn counter_is_linearizable() {
        let history = events_to_history(linearizable_events());
        let model = Register::new();
        let mut checker = Checker::new(model, history);
        if let Err(e) = checker.check() {
            panic!("Failed to linearize: {:?}", e)
        }
    }

    #[test]
    fn counter_not_linearizable() {
        let history = events_to_history(non_linearizable_events());
        let model = Register::new();
        let mut checker = Checker::new(model, history);
        match checker.check() {
            Ok(()) => panic!("non-linearizable history incorrectly checked as linearizable"),
            Err(e) => println!("Failed to linearize: {:?}", e)
        }
    }
}
