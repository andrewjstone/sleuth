extern crate bit_set;

use std::collections::HashSet;
use std::hash::Hash;
use std::time::Instant;
use bit_set::BitSet;

/// The specification of a sequential data type
///
/// Concurrent histories are checked against a model to verify linearizability
///
/// The internal state of all models must be a persistent data structure.
pub trait Model {
    /// A Call contains an operation on a sequential type (the implementor of this model) and its
    /// arguments. It is typically an enum unless the model only has one operation.
    type Call;

    /// The return value of an operation on the sequential data type
    type ReturnValue: Eq;

    /// The current state of the model
    type State: Hash + Eq + Clone;

    /// Apply an operation to the model
    ///
    /// Return the value and the new state of the model after application
    fn apply(&self, op: &Self::Call) -> (Self::ReturnValue, Self::State);

    /// Return a copy of the current model state
    fn state(&self) -> Self::State;

    /// Replace the existing state with the passed in value
    fn set_state(&mut self, Self::State);
}

/// The type representing either an operation call or return. A return can also be represented as a
/// Timeout, which means that there never was a return. In this case, it is considered concurrent
/// with all operations issued after its call.
pub enum Op<M: Model> {
    Call(M::Call),
    Return(M::ReturnValue),
    Timeout
}

/// A call or return of an operation for a given client
///
/// Only one operation per client can be outstanding at a time. This type is used during the
/// recording phase of a test run. Before analysis all ops are totally ordered and converted to
/// entries.
pub struct Event<M: Model> {
    client_id: usize,
    time: Instant,
    op: Op<M>
}

/// An entry in a History
pub struct Entry<M: Model> {
    id: usize,
    event: Event<M>,

    /// The index to the return operation if this is a call
    matched: Option<usize>,

    /// Whether the entry has been provisionally linearized or 'lifted' into the `calls` stack.
    removed: bool
}

/// The relevant parts of the history when it is not linearizable.
///
/// This is used to aid in debugging
pub struct FailureCtx {
}

/// The actual linearizability checker itself
pub struct Checker<M> where M: Model {
    linearized: BitSet,
    model: M,
    cache: HashSet<(BitSet, M::State)>,

    /// The stack of provisionally linearized calls
    calls: Vec<(usize, M::State)>,

    history: Vec<Entry<M>>,

    /// The beginning of the history, where all prior entries are linearizable
    head: usize,

    /// The position of the current entry
    current: usize
}

impl<M> Checker<M> where M: Model {
    /// Create a new checker
    pub fn new(model: M, history: Vec<Entry<M>>) -> Checker<M> {
        Checker {
            linearized: BitSet::with_capacity(history.len() / 2),
            model: model,
            cache: HashSet::new(),
            calls: Vec::with_capacity(history.len() / 2),
            history: history,
            head: 0,
            current: 0
        }
    }

    /// Determine if the history is linearizable with respect to the sequential model
    ///
    /// Returns None if the check succeeds, otherwise returns a FailureCtx
    pub fn check(&mut self) -> Option<FailureCtx> {
        let len = self.history.len();
        let current = self.current;
        let mut entry = unsafe { &mut *self.get_entry(current) };
        while self.head + 1 < len {
            match entry.matched {
                Some(return_index) => {
                    let (is_linearizable, new_state) = self.apply(entry, return_index);
                    if is_linearizable {
                        let mut linearized = self.linearized.clone();
                        let _ = linearized.insert(entry.id);
                        let not_yet_cached = self.cache.insert((linearized, new_state.clone()));
                        if not_yet_cached {
                            // provisionally linearize
                            self.calls.push((self.current, self.model.state()));
                            self.model.set_state(new_state);
                            self.linearized.insert(entry.id);
                            self.lift(entry);
                            self.head += 1;
                            let head = self.head;
                            entry = unsafe { &mut *self.get_entry(head) };
                        } else {
                            // move onto the next entry
                            self.current += 1;
                            let current = self.current;
                            entry = unsafe { &mut *self.get_entry(current) };
                        }
                    }
                }
                None => {
                    match self.calls.pop() {
                        Some((index, new_state)) => {
                            // revert to prior state
                            self.model.set_state(new_state);
                            entry = unsafe { &mut *self.get_entry(index) };
                            self.linearized.remove(entry.id);
                            self.unlift(entry);
                            self.current = index + 1;
                            entry = unsafe { &mut *self.get_entry(index + 1) };
                        }
                        None => {
                            return Some(FailureCtx{});
                        }
                    }
                }
            }
        }
        None
    }

    fn apply(&self, entry: &Entry<M>, return_index: usize) -> (bool, M::State) {
        let rv = self.get_return_value(return_index);
        if let Op::Call(ref call) = entry.event.op {
            let (model_rv, new_model_state) = self.model.apply(&call);
            return (*rv == model_rv, new_model_state);
        }
        unreachable!()
    }

    fn get_return_value(&self, return_index: usize) -> &M::ReturnValue {
        let return_entry = unsafe { self.history.get_unchecked(return_index) } ;
        if let Op::Return(ref val) = return_entry.event.op {
            return val;
        }
        unreachable!()
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

    /// Return a mutable pointer to an element of the history Vec
    ///
    /// `unsafe` is required because we often need two references into the vec: one for the call
    /// entry, and one for the return entry.
    ///
    /// Note that the only part of the entry that we ever mutate is the `removed` field.
    /// Also, note that we must never hold two references to the same entry, and we never remove or
    /// add entries to the history.
    fn get_entry(&mut self, index: usize) -> *mut Entry<M> {
        unsafe {
            self.history.get_unchecked_mut(index) as *mut Entry<M>
        }
    }
}
