// This is an example implementation of the Calculus of Constructions, using first
// class Anns that compute, inspired by Interaction Type Theory. This allows us to
// completely get rid of contexts, and the checker function becomes minimal, as
// it just needs to collapse chained ANNs into equalities. The code below is an
// initial demo of such idea (very new, not tested).

var TOTAL = 0;

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
  | { tag: "Lam"; inp: Term; bod: (x: Term) => Term } // λ(<x>: <term>) <term>
  | { tag: "App"; fun: Term; arg: Term }              // (<term> <term>)
  | { tag: "Sup"; lab: string; fst: Term; snd: Term } // [<term> | <term>]#L
  | { tag: "Fst"; lab: string; sup: Term }            // fst#L <term>
  | { tag: "Snd"; lab: string; sup: Term }            // snd#L <term>
  | { tag: "Any" }                                    // *
  | { tag: "Slf"; bod: (x: Term) => Term }            // $<x> <term>
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
const Slf = (bod: (x: Term) => Term): Term            => ({ tag: "Slf", bod });
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

// Expands a reference.
function deref(term: Term): Term {
  if (term.tag === "Ref" && BOOK[term.nam]) {
    return reduce(BOOK[term.nam]);
  } else {
    return term;
  }
}

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
    case "Slf": return Slf(term.bod);
    case "Ann": return reduce_ann(term.val, reduce(term.typ));
    case "Ref": return Ref(term.nam);
    case "Hol": return Hol(term.ctx);
    case "Err": return Err(term.msg);
  }
}

// Annotations
function reduce_ann(val: Term, typ: Term): Term {
  var typ = deref(typ);
  // {t :: λ(x: A) -> B}
  // -------------------------- ann-lam
  // λ(x: A). {(t x) :: B}
  if (typ.tag === "Lam") {
    return Lam(typ.inp, x => Ann(App(val, x), typ.bod(x)));
  }
  // {t :: [A B]#L}
  // ------------------------------- ann-sup
  // [{fst#L t :: A} {snd#L t :: B}]
  if (typ.tag === "Sup") {
    return Sup(typ.lab, Ann(Fst(typ.lab, val), typ.fst), Ann(Snd(typ.lab, val), typ.snd));
  }
  // {t :: $x.T}
  // -----------
  // T[x <- t]
  if (typ.tag === "Slf") {
    return reduce(typ.bod(val));
  }
  // {t : *}
  // -------
  // t
  if (typ.tag === "Any") {
    return reduce(val);
  }
  return Ann(val, typ);
}

// Applications
function reduce_app(fun: Term, arg: Term): Term {
  var fun = deref(fun);
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
  // ...
  if (fun.tag === "Any") {
    throw "TODO";
  }
  // ([a b]#L arg)
  // ------------------- app-sup
  // [(a arg) (b arg)]#L
  if (fun.tag === "Sup") {
    return Sup(fun.lab, App(fun.fst, arg), App(fun.snd, arg));
  }
  // ($x.T t)
  // -------- app-slf
  // ???
  if (fun.tag === "Slf") {
    throw "TODO:APP-SLF";
  }
  // ({x : T} arg)
  // ------------- app-ann
  // ⊥
  if (fun.tag === "Ann") {
    return Err("non-fun-app");
  }
  return App(fun, arg);
}

// First-Projections
function reduce_fst(lab: string, sup: Term): Term {
  var sup = deref(sup);
  // fst#L λ(x: A) B
  // ----------------------------- fst-lam
  // λ(x: A) fst#L B[x <- [x | *]]
  if (sup.tag === "Lam") {
    return Lam(sup.inp, x => Fst(lab, sup.bod(Sup(lab, x, Any()))));
  }
  // fst#L [a | b]#M
  // -------------------------------------------- fst-sup
  // if L==M { a } else { [fst#L a | fst#L b]#M }
  if (sup.tag === "Sup") {
    if (lab == sup.lab) {
      return reduce(sup.fst);
    } else {
      return Sup(sup.lab, Fst(lab, sup.fst), Fst(lab, sup.snd));
    }
  }
  // ...
  if (sup.tag === "Any") {
    throw "TODO";
  }
  // fst#L $x.T
  // -------------------------- fst-val
  // $x.(fst#L B[x <- [x | *]])
  if (sup.tag === "Slf") {
    return Slf(x => Fst(lab, sup.bod(Sup(lab, x, Any()))));
  }
  // fst#L {x: T}
  // ------------- fst-ann
  // {fst#L x : T}
  if (sup.tag === "Ann") {
    return Ann(Fst(lab, sup.val), sup.typ);
  }
  return Fst(lab, sup);
}

// Second-Projections
function reduce_snd(lab: string, sup: Term): Term {
  var sup = deref(sup);
  // snd#L λ(x: A) B
  // ----------------------------- snd-lam
  // λ(x: A) snd#L B[x <- [* | x]]
  if (sup.tag === "Lam") {
    return Lam(sup.inp, x => Snd(lab, sup.bod(Sup(lab, Any(), x))));
  }
  // snd#L [a | b]#M
  // -------------------------------------------- snd-sup
  // if L==M { a } else { [snd#L a | snd#L b]#M }
  if (sup.tag === "Sup") {
    if (lab == sup.lab) {
      return reduce(sup.snd);
    } else {
      return Sup(sup.lab, Snd(lab, sup.snd), Snd(lab, sup.snd));
    }
  }
  // ...
  if (sup.tag === "Any") {
    throw "TODO";
  }
  // snd#L $x.T
  // -------------------------- snd-val
  // $x.(snd#L B[x <- [x | *]])
  if (sup.tag === "Slf") {
    return Slf(x => Snd(lab, sup.bod(Sup(lab, Any(), x))));
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
function normal(term: Term, seen: {[key: string]: boolean} = {}, dep: number = 0): Term {
  if (dep > 10) {
    return term;
  }
  console.log("normal", show_term(term, dep), JSON.stringify(seen), dep);
  var term = reduce(term);
  switch (term.tag) {
    case "Var": return Var(term.val);
    case "Def": throw "unreachable";
    case "Lam": return Lam(normal(term.inp, seen, dep), x => normal(term.bod(Ann(Var(dep), term.inp)), seen, dep+1));
    case "App": return App(normal(term.fun, seen, dep), normal(term.arg, seen, dep));
    case "Sup": return Sup(term.lab, normal(term.fst, seen, dep), normal(term.snd, seen, dep));
    case "Fst": return Fst(term.lab, normal(term.sup, seen, dep));
    case "Snd": return Snd(term.lab, normal(term.sup, seen, dep));
    case "Any": return Any();
    case "Slf": return Slf(x => normal(term.bod(x), seen, dep+1));
    case "Ann": return ANN(normal(term.val, seen, dep), normal(term.typ, seen, dep), dep);
    //case "Ann": return Ann(normal(term.val, dep), normal(term.typ, dep));
    //case "Ref": return BOOK[term.nam] ? normal(BOOK[term.nam]) : Ref(term.nam);
    case "Ref": return seen[term.nam] ? Ref(term.nam) : BOOK[term.nam] ? (seen[term.nam] = true, normal(BOOK[term.nam], seen, dep)) : Ref(term.nam);
    //case "Ref": return Ref(term.nam);
    case "Hol": return Hol(fold(term.ctx, (x, xs) => Cons(normal(x, seen, dep), xs), Nil()));
    case "Err": return Err(term.msg);
  }
}

function ANN(val: Term, typ: Term, dep: number): Term {
  TOTAL += 1;
  switch (val.tag) {
    // {{x : A} : B}
    // -------------
    // {x : A == B}
    case "Ann": {
      if (!equal(val.typ, typ, dep)) {
        let exp = show_term(typ, dep);
        let det = show_term(val.typ, dep);
        let msg = exp + "!=" + det;
        return Err(msg);
      } else {
        return Ann(val.val, val.typ);
      }
    }
    // {[x y]#L : A}
    // ---------------
    // [{x:A} {y:A}]#L
    case "Sup": {
      return Sup(val.lab, Ann(val.fst, typ), Ann(val.snd, typ));
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
  if (a.tag === "Slf" && b.tag === "Slf") {
    return equal(a.bod(Var(dep)), b.bod(Var(dep)), dep + 1);
  }
  if (a.tag === "Ref" && b.tag === "Ref") {
    if (a.nam === b.nam) {
      return true;
    } else {
      throw "TODO";
    }
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
    case "Lam": return (term.inp.tag === "Any" ? "λ"+num_to_str(dep)+"." : "λ("+num_to_str(dep)+":"+show_term(term.inp, dep)+")") + show_term(term.bod(Var(dep)), dep + 1);
    case "App": return "(" + show_term(term.fun, dep) + " " + show_term(term.arg, dep) + ")";
    case "Sup": return "[" + show_term(term.fst, dep) + " | " + show_term(term.snd, dep) + "]#" + term.lab;
    case "Fst": return "fst#" + term.lab + " " + show_term(term.sup, dep);
    case "Snd": return "snd#" + term.lab + " " + show_term(term.sup, dep);
    case "Any": return "*";
    case "Slf": return "$" + num_to_str(dep) + "." + show_term(term.bod(Var(dep)), dep+1);
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
  while (true) {
    // Comment
    if (code.slice(0, 2) === "//") {
      while (code.length != 0 && code[0] != "\n") {
        code = code.slice(1);
      }
      code = code.slice(1);
      continue;
    }
    // Spaces
    if (code[0] === "\n" || code[0] === " ") {
      code = code.slice(1);
      continue;
    }
    break;
  }
  return code;
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
  if (code[0] === "λ") {
    if (code[1] === "(") {
      var [code, nam] = parse_name(code.slice(2));
      var [code, _  ] = parse_text(code, ":");
      var [code, typ] = parse_term(code);
      var [code, __ ] = parse_text(code, ")");
      var [code, bod] = parse_term(code);
      return [code, ctx => Lam(typ(ctx), x => bod(Cons([nam,x], ctx)))];
    } else {
      var [code, nam] = parse_name(code.slice(1));
      var [code, _  ] = parse_text(code, ".");
      var [code, bod] = parse_term(code);
      return [code, ctx => Lam(Any(), x => bod(Cons([nam,x], ctx)))];
    }
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
  // VAl: `$x T`
  if (code[0] === "$") {
    var [code, nam] = parse_name(code.slice(1));
    var [code, _  ] = parse_text(code, ".");
    var [code, bod] = parse_term(code);
    return [code, ctx => Slf(x => bod(Cons([nam, x], ctx)))];
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
//@test  = λ(A:*) λ(B:*) λ(aa:λ(x:A) A) λ(ab:λ(x:A) B) λ(ba:λ(x:B) A) λ(bb:λ(x:B) B) λ(a:A) λ(b:B) (bb (aa a))
//@Empty = λ(P:*) P
//@Unit  = λ(P:*) λ(x:P) P
//@unit  = λ(P:*) λ(x:P) x
//@Equal = λ(T:*) λ(a:T) λ(b:T) λ(P:λ(b:T) *) λ(r:(P a)) (P b)
//@refl  = λ(T:*) λ(x:T) λ(P:λ(b:T) *) λ(r:(P x)) r
//@Bool  = λ(P:*) λ(t:P) λ(f:P) P
//@true  = λ(P:*) λ(t:P) λ(f:P) t
//@false = λ(P:*) λ(t:P) λ(f:P) f
//@bid   = {λ(x:*) x :λ(x:Bool) Bool}
//@not   = λ(b:Bool) (b Bool false true)
//@CNat  = λ(P:*) λ(s:λ(x:P) P) λ(z:P) P
//@csucc = λ(n:CNat) λ(P:*) λ(s:λ(x:P) P) λ(z:P) (s n)
//@czero = λ(P:*) λ(s:λ(x:P) P) λ(z:P) z
//@Pair  = λ(A:*) λ(B:*) λ(P:*) λ(p:λ(a:A) λ(b:B) P) P
//@pair  = λ(A:*) λ(B:*) λ(a:A) λ(b:B) λ(P:*) λ(p:λ(a:A) λ(b:B) P) (p a b)
//@List  = λ(P:*) λ(c:λ(x:Nat) λ(xs:P) P) λ(n:P) P
//@cons  = λ(x:Nat) λ(xs:List) λ(P:*) λ(c:λ(x:Nat) λ(xs:P) P) λ(n:P) (c x (xs P c n))
//@nil   = λ(P:*) λ(c:λ(x:Nat) λ(xs:P) P) λ(n:P) n
//@Nat    = λ(P:*) λ(s:λ(x:Nat) P) λ(z:P) P
//@succ   = λ(n:Nat) λ(P:*) λ(s:λ(x:Nat)P) λ(z:P) (s n)
//@zero   = λ(P:*) λ(s:λ(x:Nat)P) λ(z:P) z
//@double = λ(n:Nat) (n Nat λ(p:Nat)(succ (succ (double p))) zero)
//@main0 = {[true | false]#A :Bool}
//@foo    = λs(s @foo)

//@main  = test
//@main  = (not false)


// {t :: λ(x: A) -> B}
// --------------------- ann-lam
// λ(x: A). {(t x) :: B}

//@Self  = λ(S:*) $x.{x :(S x)}

//@true  = λP λt λf t
//@false = λP λt λf f
//@Bool  = $self {self: λ(P: λ(x: *) *) λ(t: (P true)) λ(f: (P false)) (P self)}

//@Foo   = $self {self: λ(P: λ(x: Foo) *) *}
//@Foo   = $self λ(P: λ(x: Foo) *) (self {P: λ(x: Foo) *})
//@Foo   = $self λ(P: λ(x: Foo) *) (self λ(x: Foo) {(P x): *})
//@Foo   = $self λ(P: λ(x: Foo) *) (self λ(x: Foo) {(P {x: Foo}): *})

//@main = $self {self: λ(P: λ(x: Foo) *) *}

//@main = $self {self: λ(P: λ(x: *) *) λ(t: (P true)) λ(f: (P false)) (P self)}
//@main = $self {self: λ(P: *) λ(t: λ(P: λ(x:


//@main = λ(T: *) λ(a: T) λ(b: T) λ(P: λ(x:T) *) λ(x: (P a)) λ(y: (P b)) {x : (P a)}

@Equal = λ(a: *) λ(b: *) λ(P: λ(x: *) *) λ(x: (P a)) (P b)
@refl  = λ(a: *) λ(P: λ(x: *) *) λ(x: (P a)) x

@Bool  = $self. {self: λ(P: *) λ(t: λ(e: (Equal self true)) P) λ(f: λ(e: (Equal self false)) P) P}
@true  = λP.λt.λf.(t (refl false))
@false = λP.λt.λf.(f (refl false))

@main = {true : Bool}




`;


//$a
//λ(b:λ(b:@Foo)*)(a λ(c:@Foo)(b
//λ(d:λ(d:@Foo)*)(c λ(e:@Foo)(d
//λ(f:λ(f:@Foo)*)(e λ(g:@Foo)(f
//λ(h:λ(h:@Foo)*)(g λ(i:@Foo)(h
//λ(j:λ(j:@Foo)*)(i λ(k:@Foo)(j
//λ(l:λ(l:@Foo)*)(k λ(m:@Foo)(l
//λ(n:λ(n:@Foo)*)(m λ(o:@Foo)(n λ(p:λ(p:@Foo)*)(o λ(q:@Foo)(p λ(r:λ(r:@Foo)*)(q λ(s:@Foo)(r λ(t:λ(t:@Foo)*)(s λ(u:@Foo){(t {u:@Foo}):*})))))))))))))))))))

do_parse_book(code);

for (var name in BOOK) {
  console.log(name, "=", show_term(BOOK[name]));
}

console.log("[TERM]\n" + show_term(BOOK.main));
console.log("-----");
console.log("[NORM]\n" + show_term(normal(BOOK.main)));
console.log("-----");
console.log(TOTAL);
