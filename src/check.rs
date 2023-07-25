use std::collections::HashMap;

pub use crate::inet::*;

use std::collections::BTreeMap;
use std::collections::VecDeque;

pub struct Cursor<'a> {
  root: Port,
  prev: Port,
  path: &'a mut BTreeMap<u32, VecDeque<u8>>,
  logs: &'a mut Vec<String>,
}

impl<'a> Cursor<'a> {
  fn copy(&mut self) -> Cursor {
    Cursor {
      root: self.root,
      prev: self.prev,
      path: self.path,
      logs: self.logs,
    }
  }

  fn flip(&mut self, inet: &INet) -> Cursor {
    Cursor {
      root: self.root,
      prev: enter(inet, self.prev),
      path: self.path,
      logs: self.logs,
    }
  }

  fn step(&mut self, inet: &INet, slot: u8) -> Cursor {
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

  fn length(&self, kind: &u32) -> usize {
    self.path.get(kind).map_or(0, |vec| vec.len())
  }
}

// For every ANN node, check if its main port is symmetric
pub fn check(inet: &mut INet, prev: Port) -> bool {
  let next = enter(inet, prev);
  if next == ROOT {
    return true;
  } else if slot(next) == 0 {
    if kind(inet, addr(next)) == ANN {
      println!(">> check {}:{}", addr(prev), slot(prev));
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

  // If on root, check
  if a_next == a.root || a_next == ROOT {
    if flip {
      return compare(inet, b, a, false);
    } else {
      if a.length(&ANN) == 1 && b.length(&ANN) == 1 {
        println!("compat {}:{} {}:{}\n  path : {:?} | {:?}\n  logs : {:?} | {:?}", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev), a.path, b.path, a.logs, b.logs);
        let an = &mut a.flip(inet);
        let bn = &mut b.flip(inet);
        return compatible(inet, an, bn);
      } else {
        return true;
      }
    }

  // If entering an erasure node, go back
  } else if a_kind == ERA {
    let an = &mut a.flip(inet);
    let eq = compare(inet, an, b, flip);
    return eq;

  // If entering main port...
  } else if a_slot == 0 {

    // If deque isn't empty, pop_back a slot and move to it
    if let Some(slot) = a.pop_back(a_kind) {
      a.logs.push(format!("W{}", slot));
      let an = &mut a.step(inet, slot);
      let eq = compare(inet, an, b, flip);
      a.logs.pop();
      a.push_back(a_kind, slot);
      return eq;

    // If deque is empty, move to slots [1,2] and push_front to the *other* deque
    } else {
      //println!("enter main (split)");
      for slot in [2,1] {
        a.logs.push(format!("V{}", slot));
        b.push_front(a_kind, slot);
        let an = &mut a.step(inet, slot);
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
    let an = &mut a.step(inet, 0);
    let eq = compare(inet, an, b, flip);
    a.pop_back(a_kind);
    a.logs.pop();
    return eq;
  }
}

// Verifies if two paths are λ-equivalent
fn compatible(inet: &mut INet, a: &mut Cursor, b: &mut Cursor) -> bool {

  // Travels down to the bottom of this leap
  fn down(inet: &mut INet, a: &mut Cursor) {
    println!("down {}:{}", addr(a.prev), slot(a.prev));
    let mut a_prev = a.prev;
    loop {
      let next = enter(inet, a_prev);
      let kind = kind(inet, addr(next));
      let slot = slot(next);
      if kind != ERA && slot == 0 {
        let ds = a.pop_back(kind).unwrap();
        a_prev = port(addr(next), ds as u32);
      } else {
        break;
      }
    }
    a.root = a.root;
    a.prev = enter(inet, a_prev);
  }

  // Travels back up, checking for λ-equivalence
  fn up(inet: &mut INet, a: &mut Cursor, b: &mut Cursor, bruijn: bool) -> bool {
    let a_next = enter(inet, a.prev);
    let b_next = enter(inet, b.prev);
    let a_kind = kind(inet, addr(a_next));
    let b_kind = kind(inet, addr(b_next));
    let a_slot = slot(a_next);
    let b_slot = slot(b_next);
    if a_next == ROOT && b_next == ROOT {
      println!("up {}:{} {}:{} halt", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev));
      return true;
    } else if a_kind == ANN || a_kind == DUP {
      println!("up {}:{} {}:{} a up", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev));
      return up(inet, &mut a.step(inet, 0), b, bruijn);
    } else if b_kind == ANN || b_kind == DUP {
      println!("up {}:{} {}:{} b up", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev));
      return up(inet, a, &mut b.step(inet, 0), bruijn);
    } else if a_kind == CON && b_kind == CON {
      // Bruijn increment
      if bruijn {
        return up(inet, &mut a.step(inet, 0), &mut b.step(inet, 0), true);
      } else {
        // Variable
        if a_slot == 1 && b_slot == 1 {
          println!("up {}:{} {}:{} con 1", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev));
          return up(inet, &mut a.step(inet, 0), &mut b.step(inet, 0), true);
        // Application
        } else if a_slot == 2 && b_slot == 2 {
          // Checks argument
          if !equal(inet, port(addr(a_next), 1), port(addr(b_next), 1)) {
            return false;
          } else {
            return up(inet, &mut a.step(inet, 0), &mut b.step(inet, 0), bruijn);
          }
        }
      }
    }
    return false;
  }

  let a = &mut a.copy();
  down(inet, a);

  let b = &mut b.copy();
  down(inet, b);
  
  return up(inet, a, b, false);
}
