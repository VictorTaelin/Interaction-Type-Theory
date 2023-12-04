// This is an example implementation of the Calculus of Constructions, using first
// class Anns that compute, inspired by Interaction Type Theory. This allows us to
// completely get rid of contexts, and the checker function becomes minimal, as
// it just needs to collapse chained ANNs into equalities. The code below is an
// initial demo of such idea (very new, not tested).

type List<A> =
  | { tag: "Cons"; head: A; tail: List<A> }
  | { tag: "Nil"; };

function Cons<A>(head: A, tail: List<A>): List<A> {
  return { tag: "Cons", head, tail };
}

function Nil<A>(): List<A> {
  return { tag: "Nil" };
}

function fold<A,P>(list: List<A>, cons: (head: A, tail: P) => P, nil: P): P {
  switch (list.tag) {
    case "Cons": return cons(list.head, fold(list.tail, cons, nil));
    case "Nil" : return nil;
  }
}
type Term =
  | { tag: "Var"; val: number }
  | { tag: "Def"; val: Term; bod: (x: Term) => Term } // def <x> = <term>; <term>
  | { tag: "Lam"; inp: Term; bod: (x: Term) => Term } // λ(x: A) f
  | { tag: "App"; fun: Term; arg: Term }              // (<term> <term>)
  | { tag: "Sup"; lab: string; fst: Term; snd: Term } // [<term> | <term>]#L
  | { tag: "Fst"; lab: string; sup: Term }            // fst#L <term>
  | { tag: "Snd"; lab: string; sup: Term }            // snd#L <term>
  | { tag: "Any" }                                    // *
  | { tag: "Ann"; val: Term; typ: Term }              // {<term> : <term>}
  | { tag: "Ref"; nam: string }                       // @term
  | { tag: "Hol", ctx: List<Term> }                   // ?
  | { tag: "Err", msg: string }                       // ⊥

// Constructors
const Var = (val: number): Term                       => ({ tag: "Var", val });
const Def = (val: Term, bod: (x: Term) => Term): Term => ({ tag: "Def", val, bod });
const Lam = (inp: Term, bod: (x: Term) => Term): Term => ({ tag: "Lam", inp, bod });
const App = (fun: Term, arg: Term): Term              => ({ tag: "App", fun, arg });
const Sup = (lab: string, fst: Term, snd: Term): Term => ({ tag: "Sup", lab, fst, snd });
const Fst = (lab: string, sup: Term): Term            => ({ tag: "Fst", lab, sup });
const Snd = (lab: string, sup: Term): Term            => ({ tag: "Snd", lab, sup });
const Any = (): Term                                  => ({ tag: "Any" });
const Ann = (val: Term, typ: Term): Term              => ({ tag: "Ann", val, typ });
const Ref = (nam: string): Term                       => ({ tag: "Ref", nam });
const Hol = (ctx: List<Term>): Term                   => ({ tag: "Hol", ctx });
const Err = (msg: string): Term                       => ({ tag: "Err", msg });

// A book of definitions
type Book = {[key: string]: Term};

// Checker
// -------

// Global mutable book.
let BOOK : Book = {};
let SIZE : number = 0;

// Reduces to weak normal form.
function reduce(term: Term): Term {
  switch (term.tag) {
    case "Var": return Var(term.val);
    case "Def": return reduce(term.bod(term.val));
    case "Lam": return Lam(term.inp, term.bod);
    case "App": return reduce_app(reduce(term.fun), term.arg);
    case "Sup": return Sup(term.lab, term.fst, term.snd);
    case "Fst": return reduce_fst(term.lab, reduce(term.sup));
    case "Snd": return reduce_snd(term.lab, reduce(term.sup));
    case "Any": return Any();
    case "Ann": return reduce_ann(term.val, reduce(term.typ));
    case "Ref": return BOOK[term.nam] || Ref(term.nam);
    case "Hol": return Hol(term.ctx);
    case "Err": return Err(term.msg);
  }
}

function reduce_ann(val: Term, typ: Term): Term {
  // {t :: λ(x: A) -> B}
  // -------------------------- ann-lam
  // λ(x: A). {(t {x::A}) :: B}
  if (typ.tag === "Lam") {
    return Lam(typ.inp, x => Ann(App(val, Ann(x, typ.inp)), typ.bod(x)));
  }
  // {t :: [A B]#L}
  // ------------------------------- ann-sup
  // [{fst#L t :: A} {snd#L t :: B}]
  if (typ.tag === "Sup") {
    return Sup(typ.lab, Ann(Fst(typ.lab, val), typ.fst), Ann(Snd(typ.lab, val), typ.snd));
  }
  if (typ.tag === "Any") {
    return reduce(val);
  }
  return Ann(val, typ);
}

function reduce_app(fun: Term, arg: Term): Term {
  // TODO...
  if (fun.tag === "Hol") {
    return Hol(Cons(arg, fun.ctx));
  }
  // ((λ(x: T) body) arg)
  // -------------------- app-lam
  // body[x <- {arg : T}]
  if (fun.tag === "Lam") {
    return reduce(fun.bod(Ann(arg, fun.inp)));
  }
  // ([a b]#L arg)
  // ------------------- app-sup
  // [(a arg) (b arg)]#L
  if (fun.tag === "Sup") {
    return Sup(fun.lab, App(fun.fst, arg), App(fun.snd, arg));
  }
  // ({x : T} arg)
  // ------------- app-ann
  // ⊥
  if (fun.tag === "Ann") {
    return Err("non-fun-app");
  }
  return App(fun, arg);
}

function reduce_fst(lab: string, sup: Term): Term {
  // fst#L λ(x: A) B
  // ----------------------------- fst-lam
  // λ(x: A) fst#L B[x <- [x | *]]
  if (sup.tag === "Lam") {
    return Lam(sup.inp, x => Fst(lab, sup.bod(Sup(lab, x, Any()))));
  }
  // fst#L [a | b]#M
  // --------------- fst-sup
  // if L==M:
  //   a
  // else:
  //   [fst#L a | fst#L b]#M
  if (sup.tag === "Sup") {
    if (lab == sup.lab) {
      return reduce(sup.fst);
    } else {
      return Sup(sup.lab, Fst(lab, sup.fst), Fst(lab, sup.snd));
    }
  }
  // fst#L {x: T}
  // ------------- fst-ann
  // {fst#L x : T}
  if (sup.tag === "Ann") {
    return Ann(Fst(lab, sup.val), sup.typ);
  }
  return Fst(lab, sup);
}

function reduce_snd(lab: string, sup: Term): Term {
  // snd#L λ(x: A) B
  // ----------------------------- snd-lam
  // λ(x: A) snd#L B[x <- [* | x]]
  if (sup.tag === "Lam") {
    return Lam(sup.inp, x => Snd(lab, sup.bod(Sup(lab, Any(), x))));
  }
  // snd#L [a | b]#M
  // --------------- snd-sup
  // if L==M:
  //   a
  // else:
  //   [snd#L a | snd#L b]#M
  if (sup.tag === "Sup") {
    if (lab == sup.lab) {
      return reduce(sup.snd);
    } else {
      return Sup(sup.lab, Snd(lab, sup.snd), Snd(lab, sup.snd));
    }
  }
  // snd#L {x: T}
  // ------------- snd-ann
  // {snd#L x : T}
  if (sup.tag === "Ann") {
    return Ann(Snd(lab, sup.val), sup.typ);
  }
  return Snd(lab, sup);
}

// Evaluates a term to normal form.
function normal(term: Term, dep: number = 0): Term {
  var term = reduce(term);
  switch (term.tag) {
    case "Var": return Var(term.val);
    case "Def": throw "unreachable";
    case "Lam": return Lam(normal(term.inp, dep), x => normal(term.bod(Ann(Var(dep), term.inp)), dep+1));
    case "App": return App(normal(term.fun, dep), normal(term.arg, dep));
    case "Sup": return Sup(term.lab, normal(term.fst, dep), normal(term.snd, dep));
    case "Fst": return Fst(term.lab, normal(term.sup, dep));
    case "Snd": return Snd(term.lab, normal(term.sup, dep));
    case "Any": return Any();
    //case "Ann": return Ann(normal(term.val, dep), normal(term.typ, dep));
    case "Ann": return check(normal(term.val, dep), normal(term.typ, dep), dep);
    case "Ref": return Ref(term.nam);
    case "Hol": return Hol(fold(term.ctx, (x, xs) => Cons(normal(x, dep), xs), Nil()));
    case "Err": return Err(term.msg);
  }
}

function check(val: Term, typ: Term, dep: number): Term {
  console.log("check", show_term(val,dep), "::", show_term(typ,dep));
  switch (val.tag) {
    // {{x : A} : B}
    // -------------
    // {x : A == B}
    case "Ann": {
      console.log("equal", show_term(val.typ,dep), "==", show_term(typ,dep));
      if (!equal(val.typ, typ, dep)) {
        let exp = show_term(typ, dep);
        let det = show_term(val.typ, dep);
        let msg = exp + "!=" + det;
        return Err(msg);
      }
      return check(val.val, val.typ, dep);
    }
    // {[x y]#L : A}
    // ---------------
    // [{x:A} {y:A}]#L
    case "Sup": {
      return Sup(val.lab, check(val.fst, typ, dep), check(val.snd, typ, dep));
    }
    // {λ(x:A)B : T}
    // -------------
    // ⊥
    case "Lam": {
      return Err("non-fun-lam");
    }
    default: {
      return Ann(val, typ);
      //return normal(val, dep);
    }
  }
}

// Checks if two terms are definitionaly equal.
function equal(a: Term, b: Term, dep: number): boolean {
  var a = reduce(a);
  var b = reduce(b);
  if (a.tag === "Var" && b.tag === "Var") {
    return a.val === b.val;
  }
  if (a.tag === "Lam" && b.tag === "Lam") {
    return equal(a.bod(Var(dep)), b.bod(Var(dep)), dep+1);
  }
  if (a.tag === "App" && b.tag === "App") {
    let fun_eq = equal(a.fun, b.fun, dep);
    let arg_eq = equal(a.arg, b.arg, dep);
    return fun_eq && arg_eq;
  }
  if (a.tag === "Sup" && b.tag === "Sup") {
    if (a.lab === b.lab) {
      let fst_eq = equal(a.fst, b.fst, dep);
      let snd_eq = equal(a.snd, b.snd, dep);
      return fst_eq && snd_eq;
    } else {
      throw "TODO";
    }
  }
  if (a.tag === "Fst" && b.tag === "Fst") {
    if (a.lab === b.lab) {
      return equal(a.sup, b.sup, dep);
    } else {
      throw "TODO";
    }
  }
  if (a.tag === "Snd" && b.tag === "Snd") {
    if (a.lab === b.lab) {
      return equal(a.sup, b.sup, dep);
    } else {
      throw "TODO";
    }
  }
  if (a.tag === "Any" && b.tag === "Any") {
    return true;
  }
  if (a.tag === "Ann") {
    return equal(a.val, b, dep);
  }
  if (b.tag === "Ann") {
    return equal(a, b.val, dep);
  }
  return false;
}

// Syntax
// ------

function show_term(term: Term, dep: number = 0): string {
  switch (term.tag) {
    case "Var": return num_to_str(term.val);
    case "Def": return "def " + num_to_str(dep) + " = " + show_term(term.val, dep) + ";\n" + show_term(term.bod(Var(dep)), dep + 1);
    case "Lam": return "λ(" + num_to_str(dep) + ":" + show_term(term.inp, dep) + ")" + show_term(term.bod(Var(dep)), dep + 1);
    case "App": return "(" + show_term(term.fun, dep) + " " + show_term(term.arg, dep) + ")";
    case "Sup": return "[" + show_term(term.fst, dep) + " | " + show_term(term.snd, dep) + "]#" + term.lab;
    case "Fst": return "fst#" + term.lab + " " + show_term(term.sup, dep);
    case "Snd": return "snd#" + term.lab + " " + show_term(term.sup, dep);
    case "Any": return "*";
    case "Ann": return "{" + show_term(term.val, dep) + ":" + show_term(term.typ, dep) + "}";
    case "Ref": return "@" + term.nam;
    case "Hol": return "?[" + fold(term.ctx, (x,xs) => show_term(x,dep) + " | " + xs, "*") + "]";
    case "Err": return "⊥{"+term.msg+"}";
  }
}

function num_to_str(num: number): string {
  let txt = '';
  num += 1;
  while (num > 0) {
    txt += String.fromCharCode(((num-1) % 26) + 'a'.charCodeAt(0));
    num  = Math.floor((num-1) / 26);
  }
  return txt.split('').reverse().join('');
}

function find<A>(list: List<[string, Term]>, nam: string): Term {
  switch (list.tag) {
    case "Cons": return list.head[0] === nam ? list.head[1] : find(list.tail, nam);
    case "Nil" : return Ref(nam);
  }
}

function skip(code: string): string {
  return /[\n ]/.test(code[0]) ? skip(code.slice(1)) : code;
}

function is_name_char(c: string): boolean {
  return /[a-zA-Z0-9_]/.test(c);
}

function parse_name(code: string): [string, string] {
  code = skip(code);
  var name = "";
  while (is_name_char(code[0]||"")) {
    name = name + code[0];
    code = code.slice(1);
  }
  return [code, name];
}

function parse_text(code: string, text: string): [string, null] {
  code = skip(code);
  if (text === "") {
    return [code, null];
  } else if (code[0] === text[0]) {
    return parse_text(code.slice(1), text.slice(1));
  } else {
    throw new Error("parse error");
  }
}

function parse_term(code: string): [string, (ctx: List<[string, Term]>) => Term] {
  code = skip(code);
  // LAM: `λ(x: T) f`
  if (code[0] === "λ" && code[1] === "(") {
    var [code, nam] = parse_name(code.slice(2));
    var [code, _  ] = parse_text(code, ":");
    var [code, typ] = parse_term(code);
    var [code, __ ] = parse_text(code, ")");
    var [code, bod] = parse_term(code);
    return [code, ctx => Lam(typ(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // APP: `(f x y z ...)`
  if (code[0] === "(") {
    var [code, fun] = parse_term(code.slice(1));
    var args: ((ctx: List<[string, Term]>) => Term)[] = [];
    while (code[0] !== ")") {
      var [code, arg] = parse_term(code);
      args.push(arg);
    }
    var [code, _] = parse_text(code, ")");
    return [code, ctx => args.reduce((f, x) => App(f, x(ctx)), fun(ctx))];
  }
  // SUP: `[a | b]#L`
  if (code[0] === "[") {
    var [code, fst] = parse_term(code.slice(1));
    var [code, _  ] = parse_text(code, "|");
    var [code, snd] = parse_term(code);
    var [code, _  ] = parse_text(code, "]");
    var [code, _  ] = parse_text(code, "#");
    var [code, lab] = parse_name(code);
    return [code, ctx => Sup(lab, fst(ctx), snd(ctx))];
  }
  // FST: `fst#L T`
  if (code.slice(0, 4) === "fst#") {
    var [code, lab] = parse_name(code.slice(4));
    var [code, sup] = parse_term(code);
    return [code, ctx => Fst(lab, sup(ctx))];
  }
  // SND: `snd#L T`
  if (code.slice(0, 4) === "snd#") {
    var [code, lab] = parse_name(code.slice(4));
    var [code, sup] = parse_term(code);
    return [code, ctx => Snd(lab, sup(ctx))];
  }
  // DEF: `def x = f; g`
  if (code.slice(0, 4) === "def ") {
    var [code, nam] = parse_name(code.slice(3));
    var [code, _  ] = parse_text(code, "=");
    var [code, val] = parse_term(code);
    var [code, bod] = parse_term(code);
    return [code, ctx => Def(val(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // ANY: `*`
  if (code[0] === "*") {
    return [code.slice(1), ctx => Any()];
  }
  // ANN: `{x : T}`
  if (code[0] === "{") {
    var [code, val] = parse_term(code.slice(1));
    var [code, _  ] = parse_text(code, ":");
    var [code, typ] = parse_term(code);
    var [code, __ ] = parse_text(code, "}");
    return [code, ctx => Ann(val(ctx), typ(ctx))];
  }
  // REF: `@name`
  if (code[0] === "@") {
    var [code, nam] = parse_name(code.slice(1));
    return [code, ctx => Ref(nam)];
  }
  // HOL: `?`
  if (code[0] === "?") {
    var code = code.slice(1);
    return [code, ctx => Hol(Nil())];
  }
  // VAR: `name`
  var [code, nam] = parse_name(code);
  if (nam.length > 0) {
    return [code, ctx => find(ctx, nam)];
  }
  throw new Error("parse error");
}

function do_parse_term(code: string): Term {
  return parse_term(code)[1](Nil());
}

function parse_book(code: string) {
  while (code.length > 0) {
    code = skip(code);
    if (code[0] === "@") {
      var code        = code.slice(1);
      var [code, nam] = parse_name(code);
      var [code, _  ] = parse_text(code, "=");
      var [code, val] = parse_term(code);
      BOOK[nam] = val(Nil());
      SIZE += 1;
    } else {
      break;
    }
  }
}

function do_parse_book(code: string) {
  parse_book(code);
}

// Tests
// -----

var code = `
@test  = λ(A: *) λ(B: *) λ(aa: λ(x: A) A) λ(ab: λ(x: A) B) λ(ba: λ(x: B) A) λ(bb: λ(x: B) B) λ(a: A) λ(b: B) (ba (aa a))
@Empty = λ(P: *) P
@Unit  = λ(P: *) λ(x: P) P
@unit  = λ(P: *) λ(x: P) x
@Equal = λ(T: *) λ(a: T) λ(b: T) λ(P: λ(b: T) *) λ(r: (P a)) (P b)
@refl  = λ(T: *) λ(x: T) λ(P: λ(b: T) *) λ(r: (P x)) r
@Bool  = λ(P: *) λ(t: P) λ(f: P) P
@true  = λ(P: *) λ(t: P) λ(f: P) t
@false = λ(P: *) λ(t: P) λ(f: P) f
@bid   = {λ(x: *) x : λ(x: Bool) Bool}
@not   = λ(b: Bool) (b Bool false true)
@Nat   = λ(P: *) λ(s: λ(x: P) P) λ(z: P) P
@succ  = λ(n: Nat) λ(P: *) λ(s: λ(x: P) P) λ(z: P) (s (n P s z))
@zero  = λ(P: *) λ(s: λ(x: P) P) λ(z: P) z
@Pair  = λ(A: *) λ(B: *) λ(P: *) λ(p: λ(a: A) λ(b: B) P) P
@pair  = λ(A: *) λ(B: *) λ(a: A) λ(b: B) λ(P: *) λ(p: λ(a: A) λ(b: B) P) (p a b)
@List  = λ(P: *) λ(c: λ(x: Nat) λ(xs: P) P) λ(n: P) P
@cons  = λ(x: Nat) λ(xs: List) λ(P: *) λ(c: λ(x: Nat) λ(xs: P) P) λ(n: P) (c x (xs P c n))
@nil   = λ(P: *) λ(c: λ(x: Nat) λ(xs: P) P) λ(n: P) n
@main  = {[true | false]#A : Bool}
`;


do_parse_book(code);

for (var name in BOOK) {
  console.log(name, "=", show_term(BOOK[name]));
}

console.log("[TERM]\n" + show_term(BOOK.main));
console.log("-----");
console.log("[NORM]\n" + show_term(normal(BOOK.main)));
console.log("-----");
