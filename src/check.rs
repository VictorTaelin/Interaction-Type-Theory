use std::collections::HashMap;

pub use crate::inet::*;

use std::collections::BTreeMap;
use std::collections::VecDeque;

// It is that simple
pub fn check(inet: &mut INet, prev: Port) -> bool {
  let next = enter(inet, prev);
  if next == ROOT {
    return true;
  } else if slot(next) == 0 {
    if kind(inet, addr(next)) == ANN {
      //println!(">> check... {} {}", prev, next);
      if !equal(inet, prev, next) {
        return false;
      }
    }
    let e1 = check(inet, port(addr(next), 1));
    let e2 = check(inet, port(addr(next), 2));
    return e1 && e2;
  } else {
    return check(inet, port(addr(next), 0));
  }
}

pub struct Cursor<'a> {
  root: Port,
  prev: Port,
  path: &'a mut BTreeMap<u32, VecDeque<u8>>,
  logs: &'a mut Vec<String>,
}

impl<'a> Cursor<'a> {
  fn next(&mut self, inet: &mut INet, slot: u8) -> Cursor {
    Cursor {
      root: self.root,
      prev: port(addr(enter(inet, self.prev)), slot as u32),
      path: self.path,
      logs: self.logs,
    }
  }

  fn push_back(&mut self, kind: u32, slot: u8) {
    self.path.entry(kind).or_default().push_back(slot);
  }

  fn push_front(&mut self, kind: u32, slot: u8) {
    self.path.entry(kind).or_default().push_front(slot);
  }

  fn pop_back(&mut self, kind: u32) -> Option<u8> {
    let opt = self.path.get_mut(&kind).and_then(|vec| vec.pop_back());
    self.cleanup(kind);
    opt
  }

  fn pop_front(&mut self, kind: u32) -> Option<u8> {
    let opt = self.path.get_mut(&kind).and_then(|vec| vec.pop_front());
    self.cleanup(kind);
    opt
  }

  fn cleanup(&mut self, kind: u32) {
    if self.path.get(&kind).map_or(false, |vec| vec.is_empty()) {
      self.path.remove(&kind);
    }
  }
}

// Checks if two interaction nets ports are equal.
pub fn equal(inet: &mut INet, a: Port, b: Port) -> bool {
  let mut a_path = BTreeMap::new();
  let mut b_path = BTreeMap::new();
  let mut a_logs = vec![];
  let mut b_logs = vec![];
  let mut a_cursor = Cursor { root: a, prev: a, path: &mut a_path, logs: &mut a_logs, };
  let mut b_cursor = Cursor { root: b, prev: b, path: &mut b_path, logs: &mut b_logs, };
  compare(inet, &mut a_cursor, &mut b_cursor, true)
}

// Compares two cursors by moving them forward until root is reached
pub fn compare(inet: &mut INet, a: &mut Cursor, b: &mut Cursor, flip: bool) -> bool {
  //println!("Equal: (Node: {}, Slot: {}) ~ (Node {}, Slot {})\n  Paths: {:?} | {:?}\n  Logs : {:?} | {:?}", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev), a.path, b.path, a.logs, b.logs);
  
  let a_next = enter(inet, a.prev);
  let a_slot = slot(a_next);
  let a_kind = kind(inet, addr(a_next));

  // If on root, stop
  if a_next == a.root || a_next == ROOT || a_kind == ERA {
    if flip {
      return compare(inet, b, a, false);
    } else {
      //println!("== {:?}\n   {:?}\n   {}", a.path, b.path, a.path.get(&ANN) != b.path.get(&ANN) || a.path.get(&CON) == b.path.get(&CON));
      if a.path.get(&ANN).map_or(false, |v| v.len() == 1) && b.path.get(&ANN).map_or(false, |v| v.len() == 1) {
        return a.path.get(&CON) == b.path.get(&CON);
      } else {
        return true;
      }
    }

  // If entering main port...
  } else if a_slot == 0 {

    // If deque isn't empty, pop_back a slot and move to it
    if let Some(slot) = a.pop_back(a_kind) {
      a.logs.push(format!("V{}", slot));
      let an = &mut a.next(inet, slot);
      let eq = compare(inet, an, b, flip);
      a.logs.pop();
      a.push_back(a_kind, slot);
      return eq;

    // If deque is empty, move to slots [1,2] and push_front to the *other* deque
    } else {
      //println!("enter main (split)");
      for slot in [2,1] {
        a.logs.push(format!("W{}", slot));
        b.push_front(a_kind, slot);
        let an = &mut a.next(inet, slot);
        let eq = compare(inet, an, b, flip);
        a.logs.pop();
        b.pop_front(a_kind);
        if !eq {
          return false;
        }
      }
      return true;
    }

  // If entering an aux port, push_back that slot to the deque, and move to the main port
  } else {
    a.logs.push(format!("^{}", a_slot));
    a.push_back(a_kind, slot(enter(inet, a.prev)) as u8);
    let an = &mut a.next(inet, 0);
    let eq = compare(inet, an, b, flip);
    a.pop_back(a_kind);
    a.logs.pop();
    return eq;
  }
}
