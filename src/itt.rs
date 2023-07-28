use std::collections::BTreeMap;
use std::collections::VecDeque;

type Path = BTreeMap<u32, VecDeque<u8>>;
type Logs = Vec<String>;

#[derive(Clone, Debug)]
pub struct INet {
  pub nodes: Vec<u32>,
  pub reuse: Vec<u32>,
  pub rules: u32,
}

// Node types are consts because those are used in a Vec<u32>.
pub const TAG : u32 = 28;
pub const NIL : u32 = 0;
pub const ORB : u32 = 1;
pub const ERA : u32 = 2;
pub const CON : u32 = 3;
pub const ANN : u32 = 4;
pub const FIX : u32 = 5;
pub const DUP : u32 = 6;

// ROOT is port 1 on address 0.
pub const ROOT : u32 = 1;

// A port is just a u32 combining address (30 bits) and slot (2 bits).
pub type Port = u32;

// Create a new net with a root node.
pub fn new_inet() -> INet {
  let mut inet = INet { nodes: vec![], reuse: vec![], rules: 0 };
  let root = new_node(&mut inet, 0);
  link(&mut inet, port(root, 0), port(root, 2));
  link(&mut inet, port(root, 1), port(root, 1));
  return inet;
}

// Allocates a new node, reclaiming a freed space if possible.
pub fn new_node(inet: &mut INet, kind: u32) -> u32 {
  let node : u32 = match inet.reuse.pop() {
    Some(index) => index,
    None => {
      let len = inet.nodes.len();
      inet.nodes.resize(len + 4, 0);
      (len as u32) / 4
    }
  };
  inet.nodes[port(node, 0) as usize] = port(node, 0);
  inet.nodes[port(node, 1) as usize] = port(node, 1);
  inet.nodes[port(node, 2) as usize] = port(node, 2);
  inet.nodes[port(node, 3) as usize] = kind;
  return node;
}

pub fn erase(inet: &mut INet, node: u32) {
  inet.reuse.push(node);
  inet.nodes[port(node, 0) as usize] = 0;
  inet.nodes[port(node, 1) as usize] = 0;
  inet.nodes[port(node, 2) as usize] = 0;
  inet.nodes[port(node, 3) as usize] = NIL;
}

// Builds a port (an address / slot pair).
pub fn port(node: u32, slot: u32) -> Port {
  (node << 2) | slot
}

// Returns the address of a port (TODO: rename).
pub fn addr(port: Port) -> u32 {
  port >> 2
}

// Returns the slot of a port.
pub fn slot(port: Port) -> u32 {
  port & 3
}

// Enters a port, returning the port on the other side.
pub fn enter(inet: &INet, port: Port) -> Port {
  inet.nodes[port as usize]
}

// Enters a slot on the node pointed by this port.
pub fn get(inet: &INet, p: Port, s: u32) -> Port {
  enter(inet, port(addr(p), s))
}

// Gets the kind of the node.
pub fn kind(inet: &INet, node: u32) -> u32 {
  inet.nodes[port(node, 3) as usize]
}

// Links two ports.
pub fn link(inet: &mut INet, ptr_a: u32, ptr_b: u32) {
  inet.nodes[ptr_a as usize] = ptr_b;
  inet.nodes[ptr_b as usize] = ptr_a;
}

// Annihilation interaction.
// ---|\     /|---    ---, ,---
//    | |---| |    =>     X
// ---|/     \|---    ---' '---
fn annihilate(inet: &mut INet, x: u32, y: u32) {
  if kind(inet, x) == ORB && kind(inet, y) == ORB {
    if !equal(inet, port(x,1), port(y,1)) {
      println!("incoherent");
      std::process::exit(0);
    }
    //println!("----------------------");
    //println!("{}", show(inet));
    //println!(">> COLLAPSE {} {} {}", x, y, equal(inet, port(x,1), port(y,1)));
    //println!("----------------------");
  }
  let p0 = enter(inet, port(x, 1));
  let p1 = enter(inet, port(y, 1));
  link(inet, p0, p1);
  let p0 = enter(inet, port(x, 2));
  let p1 = enter(inet, port(y, 2));
  link(inet, p0, p1);
  erase(inet, x);
  erase(inet, y);
}

// Commute interaction.
//                        /|-------|\
//                    ---|#|       | |---
// ---|\     /|---        \|--, ,--|/
//    | |---|#|    =>          X
// ---|/     \|---        /|--' '--|\
//                    ---|#|       | |---
//                        \|-------|/
fn commute(inet: &mut INet, x: u32, y: u32) {
  let t = kind(inet, x);
  let a = new_node(inet, t);
  let t = kind(inet, y);
  let b = new_node(inet, t);
  let t = enter(inet, port(x, 1));
  link(inet, port(b, 0), t);
  let t = enter(inet, port(x, 2));
  link(inet, port(y, 0), t);
  let t = enter(inet, port(y, 1));
  link(inet, port(a, 0), t);
  let t = enter(inet, port(y, 2));
  link(inet, port(x, 0), t);
  link(inet, port(a, 1), port(b, 1));
  link(inet, port(a, 2), port(y, 1));
  link(inet, port(x, 1), port(b, 2));
  link(inet, port(x, 2), port(y, 2));
}

// Reduces a wire to weak normal form.
pub fn reduce(inet: &mut INet, root: Port) {
  let mut path = vec![];
  let mut prev = root;
  loop {
    let next = enter(inet, prev);
    //println!("------------------------------- {}:{} -> {}:{}", addr(prev), slot(prev), addr(next), slot(next));
    //println!("{}", show(inet));
    //limit(500);

    // If next is ROOT, stop.
    if next == ROOT {
      return;
    }
    // If next is a main port...
    if slot(next) == 0 {

      // If prev is a main port, reduce the active pair.
      if slot(prev) == 0 {
        inet.rules += 1;
        rewrite(inet, prev, next);
        prev = path.pop().unwrap();
        continue;
      // Otherwise, return the axiom.
      } else {
        return;
      }
    }
    // If next is an aux port, pass through.
    path.push(prev);
    prev = port(addr(next), 0);
  }
}

// Reduces the net to normal form.
pub fn normal(inet: &mut INet, root: Port) {
  let mut warp = vec![root];
  let mut tick = 0;
  while let Some(prev) = warp.pop() {
    reduce(inet, prev);
    let next = enter(inet, prev);
    let addr = addr(next);
    let kind = kind(inet, addr);
    if slot(next) == 0 {
      warp.push(port(addr, 1));
      warp.push(port(addr, 2));
    }
  }
}

// Eager reduction
// FIXME: wrote this quickly to test the checker, obviously very inefficient
pub fn eager(inet: &mut INet) {
  let mut rules = 0;
  loop {
    let init_rules = rules;
    for index in 0 .. (inet.nodes.len() / 4) as u32 {
      let kind = kind(inet, index);
      if kind != NIL {
        let prev = port(index, 0);
        let next = enter(inet, prev);
        if slot(next) == 0 {
          rules += 1;
          rewrite(inet, prev, next);
          break;
        }
      }
    }
    if rules == init_rules {
      break;
    }
  }
}

// Rewrites an active pair.
pub fn rewrite(inet: &mut INet, x: Port, y: Port) {
  //println!(">> rewrite {}:{} {}:{}", addr(x), slot(x), addr(y), slot(y));
  if kind(inet, addr(x)) == kind(inet, addr(y)) {
    annihilate(inet, addr(x), addr(y));
  } else {
    commute(inet, addr(x), addr(y));
  }
}

// Compares two ports for equivalence.
pub fn equal(inet: &mut INet, a: Port, b: Port) -> bool {
  let mut aP = &mut BTreeMap::new();
  let mut bP = &mut BTreeMap::new();
  let mut aL = &mut Vec::new();
  let mut bL = &mut Vec::new();
  return compare(inet, 0, true, a, a, aP, aL, b, b, bP, bL);
}

// Comparison algorithm.
// Aliases: R = root, P = path, L = logs, S = slot, K = kind
pub fn compare(inet: &mut INet, step: u32, flip: bool,
  a0: Port, aR: Port, aP: &mut Path, aL: &mut Logs,
  b0: Port, bR: Port, bP: &mut Path, bL: &mut Logs,
) -> bool {
  // FIXME: still can't handle loops, so we just halt deep recs for now
  let halt = 64;
  let step = step + 1;

  let a1 = enter(inet, a0);
  let aS = slot(a1);
  let aK = kind(inet, addr(a1));

  //println!("- leap {} {} | {}:{}->{}:{} {}:{} | aR={}:{} | {:?} {:?}", step, flip, addr(a0), slot(a0), addr(a1), slot(a1), addr(b0), slot(b0), addr(aR), slot(aR), aP, bP);
  //limit(50);

  // If on root...
  if step > halt || a1 == aR || a1 == ROOT {
    // If didn't move 'b' yet, flip and recurse...
    if flip {
      return compare(inet, 0, false, b0, bR, bP, bL, a0, aR, aP, aL);
    // Otherwise, compare this leap...
    } else {
      let av = aP.get(&CON).map_or(0, |vec| vec.len());
      let bv = bP.get(&CON).map_or(0, |vec| vec.len());
      return av == bv;
    }
  }

  // If entering main port...
  if aS == 0 {
    // If deque isn't empty, pop_back a slot and move to it
    if let Some(slot) = aP.get_mut(&aK).and_then(|vec| vec.pop_back()) {
      aL.push(format!("down({}:{})", addr(a1), slot));
      let a0 = port(addr(enter(inet, a0)), slot as u32);
      let eq = compare(inet, step, flip, a0, aR, aP, aL, b0, bR, bP, bL);
      aL.pop();
      aP.entry(aK).or_default().push_back(slot);
      return eq;

    // If deque is empty, move to slots [1,2] and push_front to the *other* deque
    } else {
      for slot in [2, 1] {
        aL.push(format!("choose({}:{})", addr(a1), slot));
        bP.entry(aK).or_default().push_front(slot);
        let a0 = port(addr(enter(inet, a0)), slot as u32);
        let eq = compare(inet, step, flip, a0, aR, aP, aL, b0, bR, bP, bL);
        aL.pop();
        bP.get_mut(&aK).and_then(|vec| vec.pop_front());
        if !eq { return false; }
      }
      return true;
    }
  }

  // If entering an aux port, push_back that slot to the deque, and move to the main port
  if aS > 0 {
    aL.push(format!("up({})", aS));
    aP.entry(aK).or_default().push_back(slot(enter(inet, a0)) as u8);
    let a0 = port(addr(enter(inet, a0)), 0);
    let eq = compare(inet, step, flip, a0, aR, aP, aL, b0, bR, bP, bL);
    aP.get_mut(&aK).and_then(|vec| vec.pop_back());
    aL.pop();
    return eq;
  }

  unreachable!();
}

// Debugger
// --------

pub fn show_tree(inet: &INet, prev: Port, names: &mut BTreeMap<u32,String>) -> String {
  let next = enter(inet, prev);
  let kind = kind(inet, addr(next));
  //println!("tree {}:{} -> {}:{} | {}", addr(prev), slot(prev), addr(next), slot(next), kind);
  if next == ROOT {
    return "@".to_string();
  }
  //if kind == ORB && slot(next) == 0 {
    //return format!("\x1b[2m{}\x1b[0m${}", addr(next), show_tree(inet, port(addr(next), 1), names));
  //}
  if slot(next) == 0 {
    //if kind == ERA {
      //return format!("*");
    //} else {
      let a = show_tree(inet, port(addr(next), 1), names);
      let b = show_tree(inet, port(addr(next), 2), names);
      let p = match kind {
        ERA => ('«', '»'),
        CON => ('(', ')'),
        ANN => ('[', ']'),
        ORB => ('<', '>'),
        _   => ('{', '}'),
      };
      return format!("\x1b[2m{}\x1b[0m\x1b[1m{}\x1b[0m{} {}\x1b[1m{}\x1b[0m", addr(next), p.0, a, b, p.1);
    //}
  }
  if let Some(name) = names.get(&prev) {
    return name.to_string();
  } else {
    let name = crate::syntax::index_to_name(names.len() as u32 + 1);
    let name = String::from_utf8_lossy(&name).to_string();
    //let name = format!("{}#{}:{}", name, addr(next), slot(next));
    names.insert(next, name.clone());
    return format!("{}", name);
  }
}

pub fn show(inet: &INet) -> String {
  let mut names = &mut BTreeMap::new();
  let mut lines = String::new();
  for index in 1 .. (inet.nodes.len() / 4) as u32 {
    let prev = port(index, 0);
    let next = enter(inet, prev);
    let kind = kind(inet, addr(next));
    if next != 0 {
      if next == ROOT {
        lines.push_str(&format!("^─{}\n", show_tree(inet, next, names)));
      //} else if kind == ERA {
        //lines.push_str(&format!("*─{}\n", show_tree(inet, next, names)));
      } else if addr(prev) < addr(next) && slot(prev) == 0 && slot(next) == 0 {
        lines.push_str(&format!("┌─{}\n", show_tree(inet, prev, names)));
        lines.push_str(&format!("└─{}\n", show_tree(inet, next, names)));
      }
    }
  }
  return lines;
}

pub fn limit(lim: i32) {
  static mut COUNTER: i32 = 0;
  unsafe {
    COUNTER += 1;
    if COUNTER >= lim {
      std::process::exit(0);
    }
  }
}
