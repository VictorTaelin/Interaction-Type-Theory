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
  | { tag: "Set" }                                    // *
  | { tag: "Def"; val: Term; bod: (x: Term) => Term } // def <x> = <term>; <term>
  | { tag: "All"; inp: Term; bod: (x: Term) => Term } // ∀(<x>: <term>) <term>
  | { tag: "Lam"; bod: (x: Term) => Term }            // λx <term>
  | { tag: "App"; fun: Term; arg: Term }              // (<term> <term>)
  | { tag: "Sup"; lab: string; fst: Term; snd: Term } // [<term> | <term>]#L
  | { tag: "Fst"; lab: string; sup: Term }            // fst#L <term>
  | { tag: "Snd"; lab: string; sup: Term }            // snd#L <term>
  | { tag: "Slf"; bod: (x: Term) => Term }            // $<x> <term>
  | { tag: "Ann"; val: Term; typ: Term }              // {<term> : <term>}
  | { tag: "Ref"; nam: string }                       // @term
  | { tag: "Hol", ctx: List<Term> }                   // ?
  | { tag: "Err", msg: string }                       // ⊥

// Constructors
const Var = (val: number): Term                       => ({ tag: "Var", val });
const Set = (): Term                                  => ({ tag: "Set" });
const Def = (val: Term, bod: (x: Term) => Term): Term => ({ tag: "Def", val, bod });
const Lam = (bod: (x: Term) => Term): Term            => ({ tag: "Lam", bod });
const All = (inp: Term, bod: (x: Term) => Term): Term => ({ tag: "All", inp, bod });
const App = (fun: Term, arg: Term): Term              => ({ tag: "App", fun, arg });
const Sup = (lab: string, fst: Term, snd: Term): Term => ({ tag: "Sup", lab, fst, snd });
const Fst = (lab: string, sup: Term): Term            => ({ tag: "Fst", lab, sup });
const Snd = (lab: string, sup: Term): Term            => ({ tag: "Snd", lab, sup });
const Slf = (bod: (x: Term) => Term): Term            => ({ tag: "Slf", bod });
const Ann = (val: Term, typ: Term): Term              => ({ tag: "Ann", val, typ });
const Ref = (nam: string): Term                       => ({ tag: "Ref", nam });
const Hol = (ctx: List<Term>): Term                   => ({ tag: "Hol", ctx });
const Err = (msg: string): Term                       => ({ tag: "Err", msg });

// A book of definitions
type Book = {[key: string]: {typ: Term, val: Term}};

// Checker
// -------

// Expands a reference.
function deref(book: Book, term: Term): Term {
  if (term.tag === "Ref" && book[term.nam]) {
    return reduce(book, book[term.nam].val);
  } else {
    return term;
  }
}

// Reduces to weak normal form.
function reduce(book: Book, term: Term): Term {
  switch (term.tag) {
    case "Var": return Var(term.val);
    case "Set": return Set();
    case "Def": return reduce(book, term.bod(term.val));
    case "All": return All(term.inp, term.bod);
    case "Lam": return Lam(term.bod);
    case "App": return reduce_app(book, reduce(book, term.fun), term.arg);
    case "Sup": return Sup(term.lab, term.fst, term.snd);
    case "Fst": return reduce_fst(book, term.lab, reduce(book, term.sup));
    case "Snd": return reduce_snd(book, term.lab, reduce(book, term.sup));
    case "Slf": return Slf(term.bod);
    case "Ann": return reduce_ann(book, term.val, reduce(book, term.typ));
    case "Ref": return Ref(term.nam);
    case "Hol": return Hol(term.ctx);
    case "Err": return Err(term.msg);
  }
}

// Annotations
function reduce_ann(book: Book, val: Term, typ: Term): Term {
  var typ = deref(book, typ);
  // {t :: ∀(x: A) -> B}
  // -------------------------- ann-lam
  // λx. {(t {x :: A}) :: B}
  if (typ.tag === "All") {
    return Lam(x => Ann(App(val, Ann(x, typ.inp)), typ.bod(x)));
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
    return reduce(book, typ.bod(val));
  }
  return Ann(val, typ);
}

// Applications
function reduce_app(book: Book, fun: Term, arg: Term): Term {
  var fun = deref(book, fun);
  // TODO...
  if (fun.tag === "Hol") {
    return Hol(Cons(arg, fun.ctx));
  }
  // ((λx body) arg)
  // -------------------- app-lam
  // body[x <- arg]
  if (fun.tag === "Lam") {
    return reduce(book, fun.bod(arg));
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
    throw "ERROR: NonFunApp";
    //return Err("non-fun-app");
  }
  return App(fun, arg);
}

// First-Projections
function reduce_fst(book: Book, lab: string, sup: Term): Term {
  var sup = deref(book, sup);
  // fst#L λx B
  // ----------------------- fst-lam
  // λx fst#L B[x <- [x | *]]
  if (sup.tag === "Lam") {
    return Lam(x => Fst(lab, sup.bod(Sup(lab, x, Set()))));
  }
  // fst#L [a | b]#M
  // -------------------------------------------- fst-sup
  // if L==M { a } else { [fst#L a | fst#L b]#M }
  if (sup.tag === "Sup") {
    if (lab == sup.lab) {
      return reduce(book, sup.fst);
    } else {
      return Sup(sup.lab, Fst(lab, sup.fst), Fst(lab, sup.snd));
    }
  }
  // fst#L $x.T
  // -------------------------- fst-val
  // $x.(fst#L B[x <- [x | *]])
  if (sup.tag === "Slf") {
    return Slf(x => Fst(lab, sup.bod(Sup(lab, x, Set()))));
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
function reduce_snd(book: Book, lab: string, sup: Term): Term {
  var sup = deref(book, sup);
  // snd#L λ(x: A) B
  // ------------------------ snd-lam
  // λx snd#L B[x <- [* | x]]
  if (sup.tag === "Lam") {
    return Lam(x => Snd(lab, sup.bod(Sup(lab, Set(), x))));
  }
  // snd#L [a | b]#M
  // -------------------------------------------- snd-sup
  // if L==M { a } else { [snd#L a | snd#L b]#M }
  if (sup.tag === "Sup") {
    if (lab == sup.lab) {
      return reduce(book, sup.snd);
    } else {
      return Sup(sup.lab, Snd(lab, sup.snd), Snd(lab, sup.snd));
    }
  }
  // snd#L $x.T
  // -------------------------- snd-val
  // $x.(snd#L B[x <- [x | *]])
  if (sup.tag === "Slf") {
    return Slf(x => Snd(lab, sup.bod(Sup(lab, Set(), x))));
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
function normal(book: Book, term: Term, dep: number = 0): Term {
  var term = reduce(book, term);
  switch (term.tag) {
    case "Var": return Var(term.val);
    case "Set": return Set();
    case "Def": throw "unreachable";
    case "All": return All(normal(book, term.inp, dep), x => normal(book, term.bod(Ann(x, term.inp)), dep+1));
    case "Lam": return Lam(x => normal(book, term.bod(x), dep+1));
    case "App": return App(normal(book, term.fun, dep), normal(book, term.arg, dep));
    case "Sup": return Sup(term.lab, normal(book, term.fst, dep), normal(book, term.snd, dep));
    case "Fst": return Fst(term.lab, normal(book, term.sup, dep));
    case "Snd": return Snd(term.lab, normal(book, term.sup, dep));
    case "Slf": return Slf(x => normal(book, term.bod(x), dep+1));
    case "Ann": return ANN(book, normal(book, term.val, dep), normal(book, term.typ, dep), dep);
    case "Ref": return book[term.nam] ? normal(book, book[term.nam].val, dep) : Ref(term.nam);
    case "Hol": return Hol(fold(term.ctx, (x, xs) => Cons(normal(book, x, dep), xs), Nil()));
    case "Err": return Err(term.msg);
  }
}


function ANN(book: Book, val: Term, typ: Term, dep: number): Term {
  switch (val.tag) {
    // {{x : A} : B}
    // -------------
    // {x : A == B}
    case "Ann": {
      if (!equal(book, val.typ, typ, dep)) {
        let exp = show_term(typ, dep);
        let det = show_term(val.typ, dep);
        let msg = "- expected: " + exp + "\n- detected: " + det;
        throw ("TypeMismatch\n"+msg);
        return Err(exp+"!="+det);
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
    // {λx(B) : T}
    // -----------
    // ⊥
    case "Lam": {
      throw "ERROR: NonFunLam";
    }
    default: {
      return Ann(val, typ);
    }
  }
}

// Checks if two terms are definitionaly equal.
function equal(book: Book, a: Term, b: Term, dep: number): boolean {
  //console.log("EQ");
  //console.log("-" + show_term(a, dep));
  //console.log("-" + show_term(b, dep));
  //var a = reduce(a);
  //var b = reduce(b);
  if (a.tag === "Var" && b.tag === "Var") {
    return a.val === b.val;
  }
  if (a.tag === "Set" && b.tag === "Set") {
    return true;
  }
  if (a.tag === "Lam" && b.tag === "Lam") {
    return equal(book, a.bod(Var(dep)), b.bod(Var(dep)), dep+1);
  }
  if (a.tag === "App" && b.tag === "App") {
    let fun_eq = equal(book, a.fun, b.fun, dep);
    let arg_eq = equal(book, a.arg, b.arg, dep);
    return fun_eq && arg_eq;
  }
  if (a.tag === "Sup" && b.tag === "Sup") {
    if (a.lab === b.lab) {
      let fst_eq = equal(book, a.fst, b.fst, dep);
      let snd_eq = equal(book, a.snd, b.snd, dep);
      return fst_eq && snd_eq;
    } else {
      throw "TODO";
    }
  }
  if (a.tag === "Fst" && b.tag === "Fst") {
    if (a.lab === b.lab) {
      return equal(book, a.sup, b.sup, dep);
    } else {
      throw "TODO";
    }
  }
  if (a.tag === "Snd" && b.tag === "Snd") {
    if (a.lab === b.lab) {
      return equal(book, a.sup, b.sup, dep);
    } else {
      throw "TODO";
    }
  }
  if (a.tag === "Slf" && b.tag === "Slf") {
    return equal(book, a.bod(Var(dep)), b.bod(Var(dep)), dep + 1);
  }
  if (a.tag === "Ref" && b.tag === "Ref" && a.nam == b.nam) {
    return true;
  }
  if (a.tag === "Ref" && book[a.nam]) {
    return equal(book, normal(book, book[a.nam].val, dep), b, dep);
  }
  if (b.tag === "Ref" && book[b.nam]) {
    return equal(book, a, normal(book, book[b.nam].val, dep), dep);
  }
  if (a.tag === "Ann") {
    return equal(book, a.val, b, dep);
  }
  if (b.tag === "Ann") {
    return equal(book, a, b.val, dep);
  }
  if (a.tag === "Lam") {
    return equal(book, a, Lam(x => App(b, x)), dep);
  }
  if (b.tag === "Lam") {
    return equal(book, Lam(x => App(a, x)), b, dep);
  }
  return false;
}

function check(book: Book) {
  for (var name in book) {
    try {
      show_term(normal(book, Ann(book[name].val, book[name].typ)));
      console.log("\x1b[32m✔ " + name + "\x1b[0m");
    } catch (e) {
      console.log("\x1b[31m✘ " + name + "\x1b[0m");
      console.log(e);
    }
  }
}

// Syntax
// ------

function show_term(term: Term, dep: number = 0): string {
  switch (term.tag) {
    case "Var": return num_to_str(term.val);
    case "Set": return "*";
    case "Def": return "def " + num_to_str(dep) + " = " + show_term(term.val, dep) + ";\n" + show_term(term.bod(Var(dep)), dep + 1);
    case "All": return "∀(" +num_to_str(dep) + ":"+show_term(term.inp, dep)+")" + show_term(term.bod(Var(dep)), dep + 1);
    case "Lam": return "λ" +num_to_str(dep) + " " + show_term(term.bod(Var(dep)), dep + 1);
    case "App": return "(" + show_term(term.fun, dep) + " " + show_term(term.arg, dep) + ")";
    case "Sup": return "[" + show_term(term.fst, dep) + " | " + show_term(term.snd, dep) + "]#" + term.lab;
    case "Fst": return "fst#" + term.lab + " " + show_term(term.sup, dep);
    case "Snd": return "snd#" + term.lab + " " + show_term(term.sup, dep);
    case "Slf": return "$" + num_to_str(dep) + " " + show_term(term.bod(Var(dep)), dep+1);
    case "Ann": return "{" + show_term(term.val, dep) + ":" + show_term(term.typ, dep) + "}";
    case "Ref": return "@" + term.nam;
    case "Hol": return "?[" + fold(term.ctx, (x,xs) => show_term(x,dep) + " | " + xs, "*") + "]";
    case "Err": return "⊥{"+term.msg+"}";
  }
}

function show_book(book: Book): string {
  var text = "";
  for (var name in book) {
    text += name + " : " + show_term(book[name].typ) + " = " + show_term(book[name].val) + "\n";
  }
  return text;
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
      do { code = code.slice(1); } while (code.length != 0 && code[0] != "\n");
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
  // ALL: `∀(x: T) f`
  if (code[0] === "∀") {
    var [code, nam] = parse_name(code.slice(2));
    var [code, _  ] = parse_text(code, ":");
    var [code, typ] = parse_term(code);
    var [code, __ ] = parse_text(code, ")");
    var [code, bod] = parse_term(code);
    return [code, ctx => All(typ(ctx), x => bod(Cons([nam,x], ctx)))];
  }
  // LAM: `λx f`
  if (code[0] === "λ" || code[0] === "∀") {
    var [code, nam] = parse_name(code.slice(1));
    var [code, bod] = parse_term(code);
    return [code, ctx => Lam(x => bod(Cons([nam,x], ctx)))];
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
  // SET: `*`
  if (code[0] === "*") {
    return [code.slice(1), ctx => Set()];
  }
  // SLF: `$x T`
  if (code[0] === "$") {
    var [code, nam] = parse_name(code.slice(1));
    //var [code, _  ] = parse_text(code, " ");
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

function parse_book(code: string): Book {
  var book : Book = {};
  while (code.length > 0) {
    code = skip(code);
    if (code[0] === "@") {
      var code        = code.slice(1);
      var [code, nam] = parse_name(code);
      var [code, _  ] = parse_text(code, ":");
      var [code, typ] = parse_term(code);
      var [code, _  ] = parse_text(code, "=");
      var [code, val] = parse_term(code);
      book[nam] = {typ: typ(Nil()), val: val(Nil())};
    } else {
      break;
    }
  }
  return book;
}

function do_parse_book(code: string): Book {
  return parse_book(code);
}

// Tests
// -----

var code = `
// Any

@Any : $x x = $x x

// Self Type

@Self : Any = λF $self { self: (F self) }

// Heterogeneous Equality

@Equal : ∀(a: *) ∀(b: *) * =
  λa λb ∀(P: ∀(x: Any) *) ∀(x: (P a)) (P b)

@refl : ∀(a: Any) (Equal a a) =
  λa λP λx x

// Boolean

@Bool : * =
  (Self λself
    ∀(P: *) 
    ∀(t: ∀(e: (Equal true  self)) P)
    ∀(f: ∀(e: (Equal false self)) P)
    P)

@true : Bool =
  λP λt λf (t (refl *))

@false : Bool =
  λP λt λf (f (refl *))

// Boolean Induction

@bool_match : ∀(b: Bool) ∀(P: ∀(x:Bool) *) ∀(t: (P true)) ∀(f: (P false)) (P b) =
  λb λP λt λf (b (P b) λe(e P t) λe(e P f))

// Boolean Negation

@not : ∀(b: Bool) Bool =
  λb (bool_match b λb(Bool) false true)

// Double Negation Theorem

@theorem
  : ∀(b: Bool) (Equal (not (not b)) b)
  = λb (bool_match b λb(Equal (not (not b)) b) (refl *) (refl *))




//@Nat : * =
  //(Self λself
    //∀(P: *) 
    //∀(z: ∀(e: (Equal zero self)) P)
    //∀(s: ∀(n: Nat) ∀(e: (Equal (succ n) self)) P)
    //P)

//@zero : Nat =
  //λP λz λs (z (refl *))

//@succ : ∀(n: Nat) Nat =
  //λn λP λz λs (s n (refl *))

////@nat_match : ∀(n: Nat) ∀(P: ∀(x:Nat) *) ∀(z: (P zero)) ∀(s: ∀(n:Nat) (P (succ n))) (P n) =
  ////λn λP λz λs (n (P n) λe(e P z) λp λe(e P (s p)))


//@main : ∀(P: *) ∀(t: P) P = λx (x ∀(P:*)∀(t:P)P λPλt(t))



`;

check(do_parse_book(code));

