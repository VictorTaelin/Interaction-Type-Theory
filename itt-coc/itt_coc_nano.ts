// Lists
type List<A> =
  | { tag: "Cons"; head: A; tail: List<A> }
  | { tag: "Nil"; };
const Cons = <A>(head: A, tail: List<A>): List<A> => ({ tag: "Cons", head, tail });
const Nil  = <A>(): List<A>                       => ({ tag: "Nil" });

// Terms
type Term =
  | { tag: "Var"; val: number }
  | { tag: "All"; inp: Term; bod: (x: Term) => Term } // ∀(<x>: <term>) <term>
  | { tag: "Lam"; bod: (x: Term) => Term }            // λx <term>
  | { tag: "App"; fun: Term; arg: Term }              // (<term> <term>)
  | { tag: "Slf"; bod: (x: Term) => Term }            // $<x> <term>
  | { tag: "Ann"; val: Term; typ: Term }              // {<term> : <term>}
  | { tag: "Ref"; nam: string }                       // @term
const Var = (val: number): Term                       => ({ tag: "Var", val });
const Lam = (bod: (x: Term) => Term): Term            => ({ tag: "Lam", bod });
const All = (inp: Term, bod: (x: Term) => Term): Term => ({ tag: "All", inp, bod });
const App = (fun: Term, arg: Term): Term              => ({ tag: "App", fun, arg });
const Slf = (bod: (x: Term) => Term): Term            => ({ tag: "Slf", bod });
const Ann = (val: Term, typ: Term): Term              => ({ tag: "Ann", val, typ });
const Ref = (nam: string): Term                       => ({ tag: "Ref", nam });

// A book of definitions
type Book = {[key: string]: {typ: Term, val: Term}};

// Checker
// -------

// Expands a reference
function deref(book: Book, term: Term): Term {
  if (term.tag === "Ref" && book[term.nam]) {
    return reduce(book, book[term.nam].val);
  } else {
    return term;
  }
}

// Reduces to weak normal form
function reduce(book: Book, term: Term): Term {
  switch (term.tag) {
    case "Var": return Var(term.val);
    case "Lam": return Lam(term.bod);
    case "All": return All(term.inp, term.bod);
    case "App": return reduce_app(book, reduce(book, term.fun), term.arg);
    case "Slf": return Slf(term.bod);
    case "Ann": return reduce_ann(book, term.val, reduce(book, term.typ));
    case "Ref": return Ref(term.nam);
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
  // {t :: $x.T}
  // ----------- ann-slf
  // T[x <- t]
  if (typ.tag === "Slf") {
    return reduce(book, typ.bod(val));
  }
  return Ann(val, typ);
}

// Applications
function reduce_app(book: Book, fun: Term, arg: Term): Term {
  var fun = deref(book, fun);
  // ((λx body) arg)
  // -------------------- app-lam
  // body[x <- arg]
  if (fun.tag === "Lam") {
    return reduce(book, fun.bod(arg));
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
  }
  return App(fun, arg);
}

// Evaluates a term to normal form.
function normal(book: Book, term: Term, dep: number = 0): Term {
  var term = reduce(book, term);
  switch (term.tag) {
    case "Var": return Var(term.val);
    case "All": return All(term.inp, x => normal(book, term.bod(Ann(x, term.inp)), dep+1));
    case "Lam": return Lam(x => normal(book, term.bod(x), dep+1));
    case "All": return All(normal(book, term.inp, dep), x => normal(book, term.bod(Ann(x, term.inp)), dep+1));
    case "App": return App(normal(book, term.fun, dep), normal(book, term.arg, dep));
    case "Slf": return Slf(x => normal(book, term.bod(x), dep+1));
    case "Ann": return ANN(book, normal(book, term.val, dep), normal(book, term.typ, dep), dep);
    case "Ref": return book[term.nam] ? normal(book, book[term.nam].val, dep) : Ref(term.nam);
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
      } else {
        return Ann(val.val, val.typ);
      }
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
  if (a.tag === "Var" && b.tag === "Var") {
    return a.val === b.val;
  }
  if (a.tag === "Lam" && b.tag === "Lam") {
    return equal(book, a.bod(Var(dep)), b.bod(Var(dep)), dep+1);
  }
  if (a.tag === "App" && b.tag === "App") {
    return equal(book, a.fun, b.fun, dep) && equal(book, a.arg, b.arg, dep);
  }
  if (a.tag === "Slf" && b.tag === "Slf") {
    return equal(book, a.bod(Var(dep)), b.bod(Var(dep)), dep + 1);
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
    case "Lam": return "λ"+num_to_str(dep)+" " + show_term(term.bod(Var(dep)), dep + 1);
    case "All": return "∀("+num_to_str(dep)+":"+show_term(term.inp, dep)+")" + show_term(term.bod(Var(dep)), dep + 1);
    case "App": return "(" + show_term(term.fun, dep) + " " + show_term(term.arg, dep) + ")";
    case "Slf": return "$" + num_to_str(dep) + " " + show_term(term.bod(Var(dep)), dep+1);
    case "Ann": return "{" + show_term(term.val, dep) + ":" + show_term(term.typ, dep) + "}";
    case "Ref": return "@" + term.nam;
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
    if (code.slice(0, 2) === "//") {
      do { code = code.slice(1); } while (code.length != 0 && code[0] != "\n");
      continue;
    }
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
    throw "parse error";
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
  // ANY: `*`
  if (code[0] === "*") {
    return [code.slice(1), ctx => ({ tag: "Slf", bod: x => x })];
  }
  // VAl: `$x T`
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
  // VAR: `name`
  var [code, nam] = parse_name(code);
  if (nam.length > 0) {
    return [code, ctx => find(ctx, nam)];
  }
  throw "parse error";
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
// Self Types

@Self : * = λF $self { self: (F self) }

// Equality

@Equal : * =
  λa λb ∀(P: ∀(x:*) *) ∀(x: (P a)) (P b)

@refl : ∀(a: *) (Equal a a) =
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

@match : ∀(b: Bool) ∀(P: ∀(x:Bool) *) ∀(t: (P true)) ∀(f: (P false)) (P b) =
  λb λP λt λf (b (P b) λe(e P t) λe(e P f))

// Boolean Negation

@not : ∀(b: Bool) Bool =
  λb (match b λb(Bool) false true)

// Double Negation Theorem

@theorem
  : ∀(b: Bool) (Equal (not (not b)) b)
  = λb (match b λb(Equal (not (not b)) b) (refl *) (refl *))
`;

check(do_parse_book(code));
