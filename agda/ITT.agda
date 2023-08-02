-- Formalization of ITT in Agda
-- ----------------------------

-- Core Dependencies
-- -----------------

data Unit : Set where
  unit : Unit

data Bool : Set where
  true  : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Maybe (a : Set) : Set where
  none : Maybe a
  some : a -> Maybe a

data Pair (a b : Set) : Set where
  pair : a -> b -> Pair a b

data List (a : Set) : Set where
  nil : List a
  _,_ : a -> List a -> List a
infixr 20 _,_

if : ∀ {a : Set} -> Bool -> a -> a -> a
if true  t f = t
if false t f = f

may : ∀ {a b : Set} -> Maybe b -> (b -> a) -> a -> a
may (some x) s n = s x
may none     s n = n

eq : Nat -> Nat -> Bool
eq zero      zero    = true
eq (succ a)  zero    = false
eq  zero    (succ b) = false
eq (succ a) (succ b) = eq a b

max : Nat -> Nat -> Nat
max zero     b       = b
max a        zero    = a
max (succ a) (succ b) = succ (max a b)

len : ∀ {a} -> List a -> Nat
len nil      = 0
len (x , xs) = succ (len xs)

foldr : ∀ {a b : Set} -> (a -> b -> b) -> b -> List a -> b
foldr f z nil      = z
foldr f z (x , xs) = f x (foldr f z xs)

-- Interaction Combinators
-- -----------------------

-- A variable is just an ID

Var : Set
Var = Nat

-- A node can be either air, an erasure, a constructor or a duplicator
data Node : Set where
  air : Node
  era : Var -> Node
  con : Var -> Var -> Var -> Node
  dup : Var -> Var -> Var -> Node

-- A graph is just a list of nodes
Graph : Set
Graph = List Node

-- Gets the node at index 'i'
get : Nat -> Graph -> Node
get zero     (node , graph) = node
get (succ p) (node , graph) = get p graph
get index    graph          = air

-- Sets the node at index 'i'
set : Nat -> Node -> Graph -> Graph
set i        val nil            = nil
set zero     val (node , graph) = val , graph
set (succ p) val (node , graph) = node , set p val graph

-- Renames a variable 'x', from 'a' to 'b'
rename : Var -> Var -> Var -> Var
rename a b x = if (eq a x) b x

-- Globally renames 'a' by 'b' on the graph
subst : Var -> Var -> Graph -> Graph
subst a b nil                    = nil
subst a b (air          , graph) = air , subst a b graph
subst a b (era a0       , graph) = era (rename a b a0) , subst a b graph
subst a b (con a0 a1 a2 , graph) = con (rename a b a0) (rename a b a1) (rename a b a2) , subst a b graph
subst a b (dup a0 a1 a2 , graph) = dup (rename a b a0) (rename a b a1) (rename a b a2) , subst a b graph

-- Generates a fresh, unused variable
fresh : Graph -> Var
fresh nil                    = zero
fresh (air          , graph) = fresh graph
fresh (era a0       , graph) = max (succ a0) (fresh graph)
fresh (con a0 a1 a2 , graph) = max (succ a0) (max (succ a1) (max (succ a2) (fresh graph)))
fresh (dup a0 a1 a2 , graph) = max (succ a0) (max (succ a1) (max (succ a2) (fresh graph)))

-- (x a1 a2)
-- (x b1 b1)
-- --------- annihilation rule
-- a1 <- b1
-- a2 <- b2
anni-rule : Nat -> Nat -> Nat -> Nat -> Graph -> Graph
anni-rule a1 a2 b1 b2 graph =
  -- Substitutes [a1 <- b1]
  let graph = subst a1 b1 graph in
  let a2    = rename a1 b1 a2 in
  let b2    = rename a1 b1 b2 in
  -- Substitutes [a2 <- b2]
  let graph = subst a2 b2 graph in
  -- Returns result
  graph

-- (x a1 a2)
-- {x b1 b2}
-- ---------- commutation rule
-- {a1 x0 x1}
-- {a2 x2 x3}
-- (b1 x2 x0)
-- (b2 x3 x1)
comm-rule : Nat -> Nat -> Nat -> Nat -> Graph -> Graph
comm-rule a1 a2 b1 b2 graph =
  -- Generates 4 fresh vars, x0, x1, x2, x3
  let x0 = fresh graph in
  let x1 = succ x0 in 
  let x2 = succ x1 in 
  let x3 = succ x2 in 
  -- Creates the 4 commuted nodes
  let A1 = dup a1 x0 x1 in
  let A2 = dup a2 x2 x3 in
  let B1 = con b1 x2 x0 in
  let B2 = con b2 x3 x1 in
  -- Returns result
  (A1 , A2 , B1 , B2 , graph)

-- Performs an interaction on indices 'i', 'j'
interact : Nat -> Nat -> Graph -> Graph
interact i j graph with (get i graph) | (get j graph)
... | (con a0 a1 a2) | (con b0 b1 b2) = anni-rule a1 a2 b1 b2 (set i air (set j air graph))
... | (con a0 a1 a2) | (dup b0 b1 b2) = comm-rule a1 a2 b1 b2 (set i air (set j air graph))
... | (dup a0 a1 a2) | (con b0 b1 b2) = comm-rule b1 b2 a1 a2 (set i air (set j air graph))
... | (dup a0 a1 a2) | (dup b0 b1 b2) = anni-rule b1 b2 a1 a2 (set i air (set j air graph))
... | a              | b              = graph

-- Finds the active pairs of a graph
active-pairs : Graph -> List (Pair Nat Nat)
active-pairs graph = go zero (λ x -> none) graph where
  go : Nat -> (Var -> Maybe Nat) -> Graph -> List (Pair Nat Nat) 
  ln : Nat -> (Var -> Maybe Nat) -> Graph -> Var -> List (Pair Nat Nat) 
  go i j-of nil                    = nil
  go i j-of (air          , graph) = go (succ i) j-of graph
  go i j-of (era a0       , graph) = ln i j-of graph a0
  go i j-of (con a0 a1 a2 , graph) = ln i j-of graph a0
  go i j-of (dup a0 a1 a2 , graph) = ln i j-of graph a0
  ln i j-of graph a0 with j-of a0
  ... | none   = go (succ i) (λ b0 -> if (eq a0 b0) (some i) (j-of b0)) graph
  ... | some j = pair j i , go (succ i) j-of graph

-- Performs a parallel reduction of all active pairs
reduce : Graph -> Graph
reduce graph = foldr (λ{ (pair i j) -> interact i j }) graph (active-pairs graph)

main : _
main =
  let g = nil in
  let g = con 0 1 1 , g in
  let g = con 2 4 4 , g in
  let g = con 0 2 3 , g in
  let g = con 3 5 5 , g in
  reduce g
