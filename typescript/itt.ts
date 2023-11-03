export type Tag  = number | "ERA" | "ROOT";
export type Ptr  = {targ: Node, slot: 0 | 1 | 2};
export type Path = {[key: number]: string};
export type Node = {$: Tag, 0: Ptr, 1: Ptr, 2: Ptr};

export let REWRITES = 0;

export const CON = 0;
export const DUP = 1;

export function ptr(targ: Node, slot: 0 | 1 | 2): Ptr {
  return {slot, targ};
}

export function ctr($: Tag): Node {
  return {$, 0: null, 1: null, 2: null} as unknown as Node;
}

export function link(a: Ptr, b: Ptr) {
  a.targ[a.slot] = b;
  b.targ[b.slot] = a;
}

export function enter(a: Ptr): Ptr {
  return a.targ[a.slot];
}

export function rewrite(a: Node, b: Node) {
  ++REWRITES;
  if (a.$ !== "ERA" && b.$ !== "ERA" && a.$ === b.$) {
    link(a[1], b[1]);
    link(a[2], b[2]);
  } else if (a.$ !== "ERA" && b.$ !== "ERA" && a.$ !== b.$) {
    let A1 = ctr(b.$);
    let A2 = ctr(b.$);
    let B1 = ctr(a.$);
    let B2 = ctr(a.$);
    link(ptr(A1,1), ptr(B1,1));
    link(ptr(A1,2), ptr(B2,1));
    link(ptr(A2,1), ptr(B1,2));
    link(ptr(A2,2), ptr(B2,2));
    link(ptr(A1,0), a[1]);
    link(ptr(A2,0), a[2]);
    link(ptr(B1,0), b[1]);
    link(ptr(B2,0), b[2]);
  } else if (a.$ === "ERA" && b.$ !== "ERA") {
    let B1 = ctr("ERA");
    let B2 = ctr("ERA");
    link(ptr(B1,0), b[1]);
    link(ptr(B2,0), b[2]);
  } else if (a.$ !== "ERA" && b.$ === "ERA") {
    let A1 = ctr("ERA");
    let A2 = ctr("ERA");
    link(ptr(A1,0), a[1]);
    link(ptr(A2,0), a[2]);
  }
}

export function reduce(root: Ptr): Ptr {
  var path = [];
  var prev = root;
  while (true) {
    var next = enter(prev);
    if (next.targ.$ == "ROOT") {
      break;
    }
    if (next.slot == 0) {
      if (prev.targ.$ != "ROOT" && prev.slot == 0) {
        rewrite(prev.targ, next.targ);
        prev = path.pop() as Ptr;
        continue;
      } else {
        break;
      }
    } else {
      path.push(prev);
      prev = ptr(next.targ, 0);
    }
  }
  return root;
}

export function normal(root: Ptr): Ptr {
  var stack = [root];
  while (stack.length > 0) {
    var prev = reduce(stack.pop() as Ptr);
    var next = enter(prev);
    if (next.slot === 0 && next.targ.$ !== "ERA") {
      stack.push(ptr(next.targ, 1));
      stack.push(ptr(next.targ, 2));
    }
  }
  return root;
}

export function pop(dir: ">" | "<", path: Path, kind: number): 1 | 2 | null {
  if (path[kind] && path[kind].length > 0) {
    var elem = dir === ">" ? path[kind].slice(0,1) : path[kind].slice(-1);
    var rest = dir === ">" ? path[kind].slice(1)   : path[kind].slice(0,-1);
    path[kind] = rest;
    return Number(elem) as 1 | 2;
  }
  return null;
}

export function push(dir: ">" | "<", path: Path, kind: number, slot: 1 | 2) {
  var elem = String(slot);
  var rest = path[kind] || "";
  path[kind] = dir === ">" ? elem+rest : rest+elem;
}

export function equal(a: Ptr, b: Ptr): boolean {
  return compare(true, a, a, {}, b, b, {});
}

export function compare(sym: boolean, a0: Ptr, aR: Ptr, aP: Path, b0: Ptr, bR: Ptr, bP: Path): boolean {
  var a1 = enter(a0);
  var aS = a1.slot;
  var aK = a1.targ.$;

  if (a1 === aR || aK === "ERA" || aK === "ROOT") {
    if (sym) {
      return compare(false, b0, bR, bP, a0, aR, aP);
    } else {
      var av = aP[CON].length || 0;
      var bv = bP[CON].length || 0;
      return av === bv;
    }
  }

  if (a1.slot === 0) {
    var got_slot = pop("<", aP, aK);
    if (got_slot !== null) {
      var a0 = ptr(enter(a0).targ, got_slot);
      var eq = compare(sym, a0, aR, aP, b0, bR, bP);
      push("<", aP, aK, got_slot);
      return eq;
    } else {
      for (var slot of [2, 1]) {
        push(">", bP, aK, slot as 1 | 2);
        var a0 = ptr(enter(a0).targ, slot as 1 | 2);
        var eq = compare(sym, a0, aR, aP, b0, bR, bP);
        pop(">", bP, aK);
        if (!eq) { return false; }
      }
      return true;
    }
  }

  if (aS > 0) {
    push("<", aP, aK, enter(a0).slot as 1 | 2);
    var a0 = ptr(enter(a0).targ, 0);
    var eq = compare(sym, a0, aR, aP, b0, bR, bP);
    pop("<", aP, aK);
    return eq;
  }

  return false;

}

export function index_to_name(index: number): string {
  let name = "";
  index += 1;
  while (index > 0) {
    name += String.fromCharCode(97 + (index - 1) % 26);
    index = Math.floor((index - 1) / 26);
  }
  return name;
}

export function parse(input: string): Ptr {
  const lines = input.trim().split("\n");
  const links: { [key: string]: Ptr } = {};
  var root_node = ctr("ROOT");
  var root_ptr  = ptr(root_node, 0);
  lines.forEach(line => {
    var got = line.trim().split(" ");
    var neo = ctr(parseInt(got[0]));
    for (var n = 0; n < 3; ++n) {
      var i = n as 0 | 1 | 2;
      var p = got[1 + i];
      if (p === "@") {
        link(ptr(neo, i), root_ptr);
      } else if (p === "*") {
        link(ptr(neo, i), ptr(ctr("ERA"), 0));
      } else {
        if (links[p]) {
          link(ptr(neo, i), links[p]);
        } else {
          links[p] = ptr(neo, i);
        }
      }
    };
  });
  return root_ptr;
}

export function show(root_ptr: Ptr): string {
  var next = 0;
  var text = "";
  function visit(node: any) {
    if (!node._s) {
      node._s = true;
      for (var i = 0; i < 3; ++i) {
        if (node[i] && !node["_"+i]) {
          var targ = node[i].targ;
          var slot = node[i].slot;
          if (targ.$ === "ERA") {
            node["_"+i] = "*";
          } else {
            var pnam = node.$ === "ROOT" ? "@" : index_to_name(next++);
            node["_"+i] = targ["_"+slot] = pnam;
            visit(targ);
          }
        }
      }
      if (node.$ !== "ROOT") {
        text = `${node.$ !== "ERA" ? node.$ : "*"} ${node._0||""} ${node._1||""} ${node._2||""}\n` + text;
      }
      delete node._s;
      delete node._0;
      delete node._1;
      delete node._2;
    }
  }
  visit(root_ptr.targ);
  return text.trim();
}
