extern crate bit_set;

use std::collections::HashSet;
use std::hash::Hash;
use std::time::Instant;
use bit_set::BitSet;

/// The specification of a sequential data type
///
/// Concurrent histories are checked against a model to verify linearizability
pub trait Model {
    /// A Call contains an operation on a sequential type (the implementor of this model) and its
    /// arguments. It is typically an enum unless the model only has one operation.
    type Call;

    /// The return value of an operation on the sequential data type
    type ReturnValue;

    /// The current state of the model
    type State: Hash + Eq;

    /// Apply an operation to the model
    fn apply(op: Self::Call) -> Self::ReturnValue;
}

/// The type representing either an operation call or return. A return can also be represented as a
/// Timeout, which means that there never was a return. In this case, it is considered concurrent
/// with all operations issued after its call.
enum Op<M: Model> {
    Call(M::Call),
    Return(M::ReturnValue),
    Timeout
}

/// A call or return of an operation for a given client
///
/// Only one operation per client can be outstanding at a time. This type is used during the
/// recording phase of a test run. Before analysis all ops are totally ordered and converted to
/// entries.
struct Event<M: Model> {
    client_id: usize,
    time: Instant,
    op: Op<M>
}

/// An entry in a History
struct Entry<M: Model> {
    id: usize,
    event: Event<M>,

    /// The index to the return operation if this is a call
    matched: Option<usize>,

    /// Whether the entry has been provisionally linearized or 'lifted' into the `calls` stack.
    removed: bool
}

/// The actual linearizability checker itself
struct Checker<M> where M: Model {
    linearized: BitSet,
    model: M,
    cache: HashSet<(BitSet, M::State)>,
    history: Vec<Entry<M>>
}

impl<M> Checker<M> where M: Model {
    /// Create a new checker
    pub fn new(m: M) -> Checker<M> {
        Checker {
            linearized: BitSet::new(),
            model: m,
            cache: HashSet::new(),
            history: Vec::new()
        }
    }

    /// Remove the call and its matching return from `history`
    fn lift(&mut self, entry: &mut Entry<M>) {
        entry.removed = true;
        if let Some(index) = entry.matched {
            self.history[index].removed = true;
        }
    }

    /// Add a call and its matching return back into history as it is not linearizable
    fn unlift(&mut self, entry: &mut Entry<M>) {
        entry.removed = false;
        if let Some(index) = entry.matched {
            self.history[index].removed = false;
        }
    }
}
