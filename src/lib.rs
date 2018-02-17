extern crate bit_set;

use std::collections::{HashSet, HashMap};
use std::fmt::Debug;
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
    type Call: Debug;

    /// The return value of an operation on the sequential data type
    type ReturnValue: Eq + Debug;

    /// The current state of the model
    type State: Hash + Eq + Clone + Debug;

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
#[derive(Debug)]
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
#[derive(Debug)]
pub struct Event<M: Model> {
    client_id: usize,
    time: Instant,
    op: Op<M>
}

/// An entry in a History
#[derive(Debug)]
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

/// Take an ordered list of events and convert them to a history
fn events_to_history<M>(events: Vec<Event<M>>) -> Vec<Entry<M>> where M: Model {
    /// Map of client calls to (entry id, entry index) pairs. There is only one outstanding call per
    /// client at at a time, so the size of this map is bounded by the number of clients.
    let mut ids = HashMap::<usize, (usize, usize)>::new();
    /// The current number of calls iterated over
    let mut count = 0;
    let size = events.len();
    let mut history = Vec::with_capacity(events.len());
    for (i, event) in events.into_iter().enumerate() {
        match event.op {
            Op::Call(_) => {
                ids.insert(event.client_id, (count, i));
                let prev = if i == 0 { None } else { Some(i - 1) };
                history.push(Entry {
                    id: count,
                    event: event,
                    matched: None, // Fill this in when the return entry is found
                    prev: prev,
                    next: Some(i + 1)
                });
                count += 1;
            }
            Op::Return(_) | Op::Timeout => {
                let &(entry_id, call_index) = ids.get(&event.client_id).unwrap();
                let next = if i+1 == size { None } else { Some(i + 1) };
                history.push(Entry {
                    id: entry_id,
                    event: event,
                    matched: None,
                    prev: Some(i - 1),
                    next: next
                });
                history[call_index].matched = Some(i)
            }
        }
    }
    return history;
}

/// The relevant parts of the history when it is not linearizable.
///
/// This is used to aid in debugging
#[derive(Debug)]
pub struct FailureCtx {
    last_non_linearizable_call_index: usize
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
    current: usize,

    /// The last non-linearizable call
    last_non_linearizable_call_index: usize
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
            current: 0,
            last_non_linearizable_call_index: 0
        }
    }

    /// Determine if the history is linearizable with respect to the sequential model
    ///
    /// Returns None if the check succeeds, otherwise returns a FailureCtx
    pub fn check(&mut self) -> Result<(), FailureCtx> {
        let mut head = self.head;
        let mut entry = self.get_entry(head);
        let mut head_entry = entry;
        while unsafe { (*head_entry).next.is_some() } {
            match unsafe { (*entry).matched } {
                Some(return_index) => {
                    entry = self.handle_call(entry, return_index);
                    head = self.head;
                }
                None => {
                    entry = self.handle_return()?;
                }
            }
            head_entry = self.get_entry(head);
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
        let next_entry = self.get_entry(next);
        if !is_linearizable {
            self.last_non_linearizable_call_index = unsafe {(*next_entry).prev.unwrap()};
        }
        next_entry
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
            println!("provisionally linearize: head = {}", head);
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
                return Err(FailureCtx{last_non_linearizable_call_index: self.last_non_linearizable_call_index});
            }
        }
    }

    fn apply(&self, entry: &Entry<M>, return_index: usize) -> (bool, M::State) {
        let rv = self.get_return_value(return_index);
        if let Op::Call(ref call) = entry.event.op {
            let (model_rv, new_model_state) = self.model.apply(&call);
            println!("Call = {:?}, return_index = {:?}", call, return_index);
            println!("rv, model_rv) = {:?}, {:?}", *rv, model_rv);
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
        if let Some(prev) = match_prev {
            self.history[prev].next = match_next;
        }
        if let Some(next) = match_next {
            self.history[next].prev = match_prev;
            if match_prev.is_none() {
                self.head = next;
            }
        }
    }

    /// Add a call and return back into history as it is not linearizable in the current order.
    ///
    /// Since this is a call, we can always unwrap calls to `next`.
    fn unlift(&mut self, entry: &mut Entry<M>, entry_index: usize) {
        let match_index = entry.matched.unwrap();
        let match_prev = self.history[match_index].prev;
        let match_next = self.history[match_index].next;
        if let Some(prev) = match_prev {
            self.history[prev].next = Some(match_index)
        }
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

#[cfg(test)]
mod tests {

    use super::*;
    use std::time::Instant;

    /// An operation on a counter
    ///
    /// We can increment it, which doesn't return a value, or get the current value.
    #[derive(Debug)]
    enum CounterOp {
        Inc,
        Get
    }


    /// A sequential specification for an increment-only counter
    #[derive(Debug)]
    struct Counter {
        value: usize
    }

    impl Counter {
        fn new() -> Counter {
            Counter {
                value: 0
            }
        }
    }

    impl Model for Counter {
        type Call = CounterOp;

        /// Return `None` for Inc, `Some(usize)` for Get
        type ReturnValue = Option<usize>;

        type State = usize;

        fn apply(&self, op: &CounterOp) -> (Option<usize>, usize) {
            match *op {
                CounterOp::Inc => (None, self.value + 1),
                CounterOp::Get => (Some(self.value), self.value)
            }
        }

        fn state(&self) -> usize {
            self.value
        }

        fn set_state(&mut self, state: usize) {
            self.value = state;
        }
    }

    // This history consists of two concurrent increments, followed by a get with the correct value
    fn linearizable_events() -> Vec<Event<Counter>> {
        vec![
            Event {
                client_id: 1,
                time: Instant::now(),
                op: Op::Call(CounterOp::Inc)
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Call(CounterOp::Inc)
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
                op: Op::Call(CounterOp::Get)
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Return(Some(2))
            }
        ]
    }

    // This history consists of two concurrent increments, followed by a get with the incorrect value
    fn non_linearizable_events() -> Vec<Event<Counter>> {
        vec![
            Event {
                client_id: 1,
                time: Instant::now(),
                op: Op::Call(CounterOp::Inc)
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Call(CounterOp::Inc)
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
                op: Op::Call(CounterOp::Get)
            },
            Event {
                client_id: 2,
                time: Instant::now(),
                op: Op::Return(Some(1))
            }
        ]
    }

    #[test]
    fn counter_is_linearizable() {
        let history = events_to_history(linearizable_events());
        let model = Counter::new();
        let mut checker = Checker::new(model, history);
        if let Err(e) = checker.check() {
            panic!("Failed to linearize: {:?}", e)
        }
    }

    #[test]
    fn counter_not_linearizable() {
        let history = events_to_history(non_linearizable_events());
        let model = Counter::new();
        let mut checker = Checker::new(model, history);
        match checker.check() {
            Ok(()) => panic!("non-linearizable history incorrectly checked as linearizable"),
            Err(e) => println!("Failed to linearize: {:?}", e)
        }
    }

}

