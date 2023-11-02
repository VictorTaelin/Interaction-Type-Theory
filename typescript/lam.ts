import * as itt from "./itt";

export type Term =
  | { $: "Lam", nam: string, bod: Term }
  | { $: "App", fun: Term, arg: Term }
  | { $: "Var", nam: string };

export function is_name_char(c: number): boolean {
  return false
    || (c >= "A".charCodeAt(0) && c <= "Z".charCodeAt(0))
    || (c >= "a".charCodeAt(0) && c <= "z".charCodeAt(0))
    || (c >= "0".charCodeAt(0) && c <= "9".charCodeAt(0))
    || (c == "_".charCodeAt(0))
    || (c == ".".charCodeAt(0));
}

export function parse_name(code: string): [string, string] {
  let i = 0;
  while (i < code.length && is_name_char(code.charCodeAt(i))) {
    i += 1;
  }
  return [code.slice(i), code.slice(0, i)];
}

export function skip_whitespace(code: string): string {
  let i = 0;
  while (i < code.length && (code[i] === " " || code[i] === "\n")) {
    i += 1;
  }
  return code.slice(i);
}

export function parse_text(code: string, text: string): [string, string] {
  code = skip_whitespace(code);
  if (code.startsWith(text)) {
    return [code.slice(text.length), text];
  } else {
    throw new Error(`Expected '${text}', found '${code}'`);
  }
}

export function parse_term(code: string): [string, Term] {
  code = skip_whitespace(code);
  switch (code[0]) {
    // Comment: `// many words here ... <newline>`
    case "/": {
      return parse_term(code.slice(code.indexOf("\n")));
    }
    // Untyped Abstraction: `λvar body`
    case "λ": {
      var [code, nam] = parse_name(code.slice(1));
      var [code, bod] = parse_term(code);
      return [code, { $: "Lam", nam, bod }];
    }
    // Let binding: `let var = value in body`
    case "l": {
      code = parse_text(code.slice(1), "et")[0];
      code = skip_whitespace(code);
      var [code, nam] = parse_name(code);
      code = parse_text(code, "=")[0];
      var [code, val] = parse_term(code);
      //code = parse_text(code, ";")[0];
      var [code, bod] = parse_term(code);
      return [code, { $: "App", fun: { $: "Lam", nam, bod }, arg: val }];
    }
    // Application: `(func argm1 argm2 ... argmN)`
    case "(": {
      var [code, fun] = parse_term(code.slice(1));
      code = skip_whitespace(code);
      while (code[0] !== ")") {
        var [code, arg] = parse_term(code);
        code = skip_whitespace(code);
        fun = { $: "App", fun, arg };
      }
      code = parse_text(code, ")")[0];
      return [code, fun];
    }
    // Variable: `<alphanumeric_name>`
    default: {
      var [code, nam] = parse_name(code);
      return [code, { $: "Var", nam }];
    }
  }
  throw "unreachable";
}

export function parse(code: string): Term {
  return parse_term(code)[1];
}

export function show(term: Term): string {
  switch (term.$) {
    case "Lam":
      return `λ${term.nam} ${show(term.bod)}`;
    case "App":
      return `(${show(term.fun)} ${show(term.arg)})`;
    case "Var":
      return term.nam;
    default:
      throw "unreachable";
  }
}

export function to_net(term: Term, root_ptr: itt.Ptr = itt.ROOT_PTR): itt.Ptr {

  // Converts calculus term to interaction net
  function term_to_net(term: Term, up: itt.Ptr, lams: {[key: string]: itt.Ptr}, vars: Array<[string, itt.Ptr]>): itt.Ptr {
    switch (term.$) {
      case "Lam": {
        var lam = itt.ctr(itt.CON);
        lams[term.nam] = itt.ptr(lam, 1);
        itt.link(itt.ptr(lam, 1), itt.ptr(itt.ctr(null), 0));
        var bod = term_to_net(term.bod, itt.ptr(lam, 2), lams, vars);
        itt.link(itt.ptr(lam, 2), bod);
        return itt.ptr(lam, 0);
      }
      case "App": {
        var app = itt.ctr(itt.CON);
        var fun = term_to_net(term.fun, itt.ptr(app, 0), lams, vars);
        itt.link(itt.ptr(app, 0), fun);
        var arg = term_to_net(term.arg, itt.ptr(app, 1), lams, vars);
        itt.link(itt.ptr(app, 1), arg);
        return itt.ptr(app, 2);
      }
      case "Var": {
        vars.push([term.nam, up]);
        return up;
      }
      default: {
        throw "unreachable";
      }
    }
  }

  // Initialize scope variables.
  var vars: Array<[string, itt.Ptr]> = [];
  var lams: {[key: string]: itt.Ptr} = {};
  var dups: number = 0;

  // Encode the main term.
  var main = term_to_net(term, root_ptr, lams, vars);

  // Links bound variables.
  for (var i = 0; i < vars.length; i++) {
    var [nam, vari] = vars[i];
    if (lams[nam]) {
      var bind = lams[nam];
      var used = itt.enter(bind);
      if (used.targ.$ === null) {
        itt.link(bind, vari);
      } else {
        var dup = itt.ctr(itt.DUP + (dups++));
        itt.link(itt.ptr(dup, 0), bind);
        itt.link(itt.ptr(dup, 1), used);
        itt.link(itt.ptr(dup, 2), vari);
      }
    } else {
      throw new Error(`Unbound variable: ${nam}.`);
    }
  }

  itt.link(root_ptr, main);

  return root_ptr;
}

export function from_net(init: itt.Ptr): Term {
  var count = 0;
  function go(prev: itt.Ptr, exit: (1 | 2)[], depth: number): Term {
    const next = itt.enter(prev);
    if (next.targ.$ === null) {
      throw "TODO";
    } else if (next.targ.$ === itt.CON) {
      switch (next.slot) {
        case 0: {
          (next.targ as any)._depth = depth;
          const nam = itt.index_to_name(depth);
          const bod = go(itt.ptr(next.targ, 2), exit, depth + 1);
          delete (next.targ as any)._depth;
          return { $: "Lam", nam, bod };
        }
        case 1: {
          var index = (next.targ as any)._depth;
          if (index >= 0) {
            const nam = itt.index_to_name(index);
            return { $: "Var", nam };
          } else {
            return { $: "Var", nam: "?" };
          }
        }
        case 2: {
          const fun = go(itt.ptr(next.targ, 0), exit, depth);
          const arg = go(itt.ptr(next.targ, 1), exit, depth);
          return { $: "App", fun, arg };
        }
      }
    } else if (next.targ.$ >= itt.DUP) {
      if (next.slot > 0) {
        exit.push(next.slot as 1 | 2);
        const term = go(itt.ptr(next.targ, 0), exit, depth);
        exit.pop();
        return term;
      } else {
        const last = exit.pop() as 1 | 2;
        const term = go(itt.ptr(next.targ, last), exit, depth);
        exit.push(last);
        return term;
      }
    }

    throw "unreachable";
  }
  return go(init, [], 0);
}
