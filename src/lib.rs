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

    /// The index of the entry prior to this in the history, None if this is the first entry.
    prev: Option<usize>,

    /// The index of the entry after this one in the history. None if this is the last entry.
    next: Option<usize>
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
    pub fn check(&mut self) -> Result<(), FailureCtx> {
        let len = self.history.len();
        let mut head = self.head;
        let mut entry = self.get_entry(head);
        while head + 1 < len {
            match unsafe { (*entry).matched } {
                Some(return_index) => {
                    entry = self.handle_call(entry, return_index);
                    head = self.head;
                }
                None => {
                    entry = self.handle_return()?;
                }
            }
        }
        Ok(())
    }

    /// Process a call entry in the history
    fn handle_call(&mut self, entry: *mut Entry<M>, return_index: usize) -> *mut Entry<M> {
        let entry = unsafe { &mut *entry };
        let (is_linearizable, new_state) = self.apply(entry, return_index);
        if is_linearizable && self.update_cache(entry, new_state.clone()) {
            return self.provisionally_linearize(entry, new_state);
        }
        // Since we only allow complete histories (every call has a return), it is safe to
        // call unwrap, as there must at least be a return after this entry.
        let next = entry.next.unwrap();
        // Move onto the next entry
        self.current = next;
        self.get_entry(next)
    }


    /// Treat the current entry as linearizable in our history
    ///
    /// At this point the call entry has been shown to be linearizable, and also was not checked
    /// prior since it was not in the cache. Put the entry in the calls stack, remove it from the
    /// history, update the model state and head pointer, and return the next entry to be tested.
    fn provisionally_linearize(&mut self, entry: &mut Entry<M>, new_state: M::State) -> *mut Entry<M> {
            self.calls.push((self.current, self.model.state()));
            self.model.set_state(new_state);
            self.linearized.insert(entry.id);
            self.lift(entry);
            let head = self.head;
            self.current = head;
            self.get_entry(head)
    }

    /// If the call is linearizable, update the cache.
    /// Return true if the cache was updated, false otherwise
    fn update_cache(&mut self, entry: &Entry<M>, new_state: M::State) -> bool {
        let mut linearized = self.linearized.clone();
        let _ = linearized.insert(entry.id);
        self.cache.insert((linearized, new_state))
    }

    /// Process a return entry in the history
    fn handle_return(&mut self) -> Result<*mut Entry<M>, FailureCtx> {
        match self.calls.pop() {
            Some((index, new_state)) => {
                // Revert to prior state
                self.model.set_state(new_state);
                let entry = unsafe { &mut *self.get_entry(index) };
                self.linearized.remove(entry.id);
                self.unlift(entry, index);
                // We took a call off the stack, so there must be at least a return after it.
                let next = entry.next.unwrap();
                self.current = next;
                return Ok(self.get_entry(next));

            }
            None => {
                return Err(FailureCtx{});
            }
        }
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
    ///
    /// Since this is a call, we can always unwrap calls to `next`.
    fn lift(&mut self, entry: &mut Entry<M>) {
        let next = entry.next.unwrap();
        match entry.prev {
            Some(prev_index) => {
                self.history[prev_index].next = Some(next);
                self.history[next].prev = Some(prev_index);
            }
            None => {
                // This entry is the current head.
                // Make the next entry the Head entry
                self.history[next].prev = None;
                self.head = next;
            }
        }
        let match_index = entry.matched.unwrap();
        let match_prev = self.history[match_index].prev;
        let match_next = self.history[match_index].next;
        self.history[match_prev.unwrap()].next = match_next;
        if let Some(next) = match_next {
            self.history[next].prev = match_prev;
        }
    }

    /// Add a call and return back into history as it is not linearizable in the current order.
    ///
    /// Since this is a call, we can always unwrap calls to `next`.
    fn unlift(&mut self, entry: &mut Entry<M>, entry_index: usize) {
        let match_index = entry.matched.unwrap();
        let match_prev = self.history[match_index].prev;
        let match_next = self.history[match_index].next;
        self.history[match_prev.unwrap()].next = Some(match_index);
        if let Some(next) = match_next {
            self.history[next].prev = Some(match_index);
        }
        let next = entry.next.unwrap();
        match entry.prev {
            Some(prev_index) => {
                self.history[prev_index].next = Some(entry_index);
            }
            None => {
                self.head = entry_index;
            }
        }
        self.history[next].prev = Some(entry_index);
    }

    /// Return a mutable pointer to an element of the history Vec
    ///
    /// A raw pointer is required because we often need two references into the vec: one for the
    /// call entry, and one for the return entry.
    ///
    /// Note that the only part of the entry that we ever mutate is the `removed` field.
    /// Also, note that we never hold two references to the same entry, and we never remove or add
    /// entries to the history, therfore it can not be moved to invalidate our pointers.
    fn get_entry(&mut self, index: usize) -> *mut Entry<M> {
        unsafe {
            self.history.get_unchecked_mut(index) as *mut Entry<M>
        }
    }
}
