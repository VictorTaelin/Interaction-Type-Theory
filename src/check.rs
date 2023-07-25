use std::collections::HashMap;

pub use crate::inet::*;

use std::collections::BTreeMap;
use std::collections::VecDeque;

pub struct Cursor<'a> {
  init: Port,
  prev: Port,
  path: &'a mut BTreeMap<u32, VecDeque<u8>>,
  //logs: &'a mut Vec<String>,
}

impl<'a> Cursor<'a> {
  fn jump(&mut self, prev: Port) -> Cursor {
    Cursor {
      init: self.init,
      prev: prev,
      path: self.path,
      //logs: self.logs,
    }
  }

  fn copy(&mut self) -> Cursor {
    return self.jump(self.prev);
  }

  fn flip(&mut self, inet: &INet) -> Cursor {
    return self.jump(enter(inet, self.prev));
  }

  fn step(&mut self, inet: &INet, slot: u8) -> Cursor {
    return self.jump(port(addr(enter(inet, self.prev)), slot as u32));
  }

  fn push_back(&mut self, kind: u32, slot: u8) {
    self.path.entry(kind).or_default().push_back(slot);
  }

  fn push_front(&mut self, kind: u32, slot: u8) {
    self.path.entry(kind).or_default().push_front(slot);
  }

  fn pop_back(&mut self, kind: u32) -> Option<u8> {
    let opt = self.path.get_mut(&kind).and_then(|vec| vec.pop_back());
    self.clear(kind);
    opt
  }

  fn pop_front(&mut self, kind: u32) -> Option<u8> {
    let opt = self.path.get_mut(&kind).and_then(|vec| vec.pop_front());
    self.clear(kind);
    opt
  }

  fn clear(&mut self, kind: u32) {
    if self.path.get(&kind).map_or(false, |vec| vec.is_empty()) {
      self.path.remove(&kind);
    }
  }

  fn length(&self, kind: &u32) -> usize {
    self.path.get(kind).map_or(0, |vec| vec.len())
  }

  fn access(&mut self, inet: &mut INet) -> Cursor {
    let mut prev = self.prev;
    loop {
      let next = enter(inet, prev);
      let kind = kind(inet, addr(next));
      let slot = slot(next);
      if slot == 0 {
        if let Some(ds) = self.pop_back(kind) {
          prev = port(addr(next), ds as u32);
          continue;
        }
      //} else {
        //self.push_back(kind, slot as u8);
        //prev = port(addr(next), 0);
      }
      break;
    }
    return self.jump(enter(inet, prev));
  }

}

// A net is coherent when all ANN nodes are symmetric.
pub fn check(inet: &mut INet, prev: Port) -> bool {
  let next = enter(inet, prev);
  if next == ROOT {
    return true;
  } else if slot(next) == 0 {
    if kind(inet, addr(next)) == ANN {
      println!("checking ann {}", addr(next));
      if equal(inet, prev, next) {
        //decay(inet, addr(prev), addr(next));
        return true;
      } else {
        return false;
      }
    } else {
      let e1 = check(inet, port(addr(next), 1));
      let e2 = check(inet, port(addr(next), 2));
      return e1 && e2;
    }
  } else {
    return check(inet, port(addr(next), 0));
  }
}

// Checks if two interaction net ports are equal.
pub fn equal(inet: &mut INet, a: Port, b: Port) -> bool {
  let mut a_cursor = Cursor {
    init: a,
    prev: a,
    path: &mut BTreeMap::new(),
    //logs: &mut vec![],
  };
  let mut b_cursor = Cursor {
    init: b,
    prev: b,
    path: &mut BTreeMap::new(),
    //logs: &mut vec![],
  };
  return leaps(inet, &mut a_cursor, &mut b_cursor, true);
}

// Finds and compares all paired leaps.
pub fn leaps(inet: &mut INet, a: &mut Cursor, b: &mut Cursor, flip: bool) -> bool {
  println!("- leap {}:{} {}:{} | {:?} {:?}", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev), a.path, b.path);
  //println!("leaps: {}:{} ~ {}:{}\n  path: {:?} | {:?}\n  logs: {:?} | {:?}", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev), a.path, b.path, a.logs, b.logs);
  let a_next = enter(inet, a.prev);
  let a_slot = slot(a_next);
  let a_kind = kind(inet, addr(a_next));

  // If on root, check
  if a_next == a.init || a_next == ROOT || a_kind == ERA {
    if flip {
      return leaps(inet, b, a, false);
    } else if a.length(&ANN) == b.length(&ANN) {
      let a = &mut a.flip(inet);
      let a = &mut a.access(inet);
      let a = &mut a.flip(inet);
      let b = &mut b.flip(inet);
      let b = &mut b.access(inet);
      let b = &mut b.flip(inet);
      println!("equiv  : {}:{} ~ {}:{}\n  path : {:?} | {:?}", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev), a.path, b.path);
      let e = equiv(inet, a, b, false);
      println!("... {}", e);
      return e;
    } else {
      return true;
    }

  // If entering main port...
  } else if a_slot == 0 {

    // If deque isn't empty, pop_back a slot and move to it
    if let Some(slot) = a.pop_back(a_kind) {
      //a.logs.push(format!("W{}", slot));
      let an = &mut a.step(inet, slot);
      let eq = leaps(inet, an, b, flip);
      //a.logs.pop();
      a.push_back(a_kind, slot);
      return eq;

    // If deque is empty, move to slots [1,2] and push_front to the *other* deque
    } else {
      for slot in [2,1] {
        //a.logs.push(format!("V{}", slot));
        b.push_front(a_kind, slot);
        let an = &mut a.step(inet, slot);
        let eq = leaps(inet, an, b, flip);
        //a.logs.pop();
        b.pop_front(a_kind);
        if !eq { return false; }
      }
      return true;
    }

  // If entering an aux port, push_back that slot to the deque, and move to the main port
  } else {
    //a.logs.push(format!("^{}", a_slot));
    a.push_back(a_kind, slot(enter(inet, a.prev)) as u8);
    let an = &mut a.step(inet, 0);
    let eq = leaps(inet, an, b, flip);
    a.pop_back(a_kind);
    //a.logs.pop();
    return eq;
  }

}

// Verifies if two paths are λ-equiv
fn equiv(inet: &mut INet, a: &mut Cursor, b: &mut Cursor, binder: bool) -> bool {

  println!("~ equiv {}:{} {}:{}", addr(a.prev), slot(a.prev), addr(b.prev), slot(b.prev));

  let a_next = enter(inet, a.prev);
  let b_next = enter(inet, b.prev);
  let a_kind = kind(inet, addr(a_next));
  let b_kind = kind(inet, addr(b_next));
  let a_slot = slot(a_next);
  let b_slot = slot(b_next);

  // When 'a' and 'b' reach root, halt
  if a_next == ROOT && b_next == ROOT {
    return true;

  // When 'a' and 'b' are ERAs, halt
  } else if a_kind == ERA && b_kind == ERA {
    return true;

  // When 'a' is ANN or DUP, go up
  } else if a_kind == ANN || a_kind == DUP {
    return equiv(inet, &mut a.step(inet, 0), b, binder);

  // When 'b' is ANN or DUP, go up
  } else if b_kind == ANN || b_kind == DUP {
    return equiv(inet, a, &mut b.step(inet, 0), binder);

  // When 'a' and 'b' are CON, compare
  } else if a_kind == CON && b_kind == CON {

    // Binder
    if binder {
      return equiv(inet, &mut a.step(inet, 0), &mut b.step(inet, 0), true);

    // Variable
    } else if a_slot == 1 && b_slot == 1 {
      return equiv(inet, &mut a.step(inet, 0), &mut b.step(inet, 0), true);

    // Application
    } else if a_slot == 2 && b_slot == 2 {
      println!("checking arguments... {}:{} {}:{}", addr(a_next), 1, addr(b_next), 1);
      if !equal(inet, port(addr(a_next), 1), port(addr(b_next), 1)) {
        return false;
      } else {
        return equiv(inet, &mut a.step(inet, 0), &mut b.step(inet, 0), binder);
      }
    }
  }

  return false;
}
