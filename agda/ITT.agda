-- Formalization of ITT in Agda
-- ============================

open import Base

-- Interaction Combinators
-- =======================

-- A variable is just an ID

Var : Set
Var = Nat

-- There are 3 node symbols: ERA, CON and DUP
data Symbol : Set where
  ERA : Symbol
  CON : Symbol
  DUP : Symbol

-- A node can be an eraser, a constructor, or a duplicator
--   ERA   #      CON      #      DUP     
-- ======= # ============= # =============
--         #       /|-- a2 #       /|-- a2
-- a0 --[] # a0 --| |      # a0 --|||
--         #       \|-- a1 #       \|-- a1
data Node : Set where
  era : Var -> Node
  con : Var -> Var -> Var -> Node
  dup : Var -> Var -> Var -> Node

-- A graph is just a list of nodes
Graph : Set
Graph = List (Maybe Node)

-- An active pair is two indices connected by their main ports
IndexPair : Set
IndexPair = Pair Nat Nat

-- Gets a node's symbol
symbol : Node -> Symbol
symbol (era a0)       = ERA
symbol (con a0 a1 a2) = CON
symbol (dup a0 a1 a2) = DUP

-- Counts nodes
size : Graph -> Nat
size nil            = zero
size (none # graph) = size graph
size (node # graph) = succ (size graph)

-- Gets the node at index 'i'
get : Nat -> Graph -> Maybe Node
get zero     (node # graph) = node
get (succ p) (node # graph) = get p graph
get index    graph          = none

-- Sets the node at index 'i'
set : Nat -> Maybe Node -> Graph -> Graph
set i        val nil            = nil
set zero     val (node # graph) = val # graph
set (succ p) val (node # graph) = node # set p val graph

-- Renames a variable 'x', from 'a' to 'b'
rename : Var -> Var -> Var -> Var
rename a b x = if (eq a x) b x

-- Globally renames 'a' by 'b' on the graph
subst : Var -> Var -> Graph -> Graph
subst a b nil                           = nil
subst a b (none                # graph) = none # subst a b graph
subst a b (some (era a0)       # graph) = some (era (rename a b a0)) # subst a b graph
subst a b (some (con a0 a1 a2) # graph) = some (con (rename a b a0) (rename a b a1) (rename a b a2)) # subst a b graph
subst a b (some (dup a0 a1 a2) # graph) = some (dup (rename a b a0) (rename a b a1) (rename a b a2)) # subst a b graph

-- Generates a fresh, unused variable
fresh : Graph -> Var
fresh nil                           = zero
fresh (none                # graph) = fresh graph
fresh (some (era a0)       # graph) = max (succ a0) (fresh graph)
fresh (some (con a0 a1 a2) # graph) = max (succ a0) (max (succ a1) (max (succ a2) (fresh graph)))
fresh (some (dup a0 a1 a2) # graph) = max (succ a0) (max (succ a1) (max (succ a2) (fresh graph)))

-- Gets the main port of a node
get-main : Node -> Var
get-main (era a0)       = a0
get-main (con a0 a1 a2) = a0
get-main (dup a0 a1 a2) = a0

-- a1 ---|\      #
--       | |--[] #
-- a2 ---|/      # (x a1 a2) -x
-- ============= # ============ Erasure
-- a1 --------[] # -a1 -a2
-- a2 --------[] # 
eras-rule : Nat -> Nat -> Graph -> Graph
eras-rule a1 a2 graph =
  -- Creates the 2 eraser nodes
  let E1 = some (era a1) in
  let E2 = some (era a2) in
  -- Returns result
  (E1 # E2 # graph)

-- a1 ---|\     /|--- b2 #
--       | |---| |       #
-- a2 ---|/     \|--- b1 # (x a1 a2) (x b1 b2)
-- ===================== # ===================== Annihilation
-- a1 ------, ,------ b2 # [a1 <- b1] [a2 <- b2]
--           X           #
-- a2 ------' '------ b1 #
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

--   a1 ---|\     /|--- b2   #
--         | |---|||         #
--   a2 ---|/     \|--- b1   # (x a1 a2) {x b1 b2}
-- ========================= # ===================== Commutation
--        /|-------|\        # {a1 x0 x1} (b2 x3 x1)
-- a1 ---|||       | |--- b2 # {a2 x2 x3} (b1 x2 x0)
--        \|--, ,--|/        #
--             X             #
--        /|--' '--|\        #
-- a2 ---|||       | |--- b1 #
--        \|-------|/        #
comm-rule : Nat -> Nat -> Nat -> Nat -> Graph -> Graph
comm-rule a1 a2 b1 b2 graph =
  -- Generates 4 fresh vars, x0, x1, x2, x3
  let x0 = fresh graph in
  let x1 = succ x0 in 
  let x2 = succ x1 in 
  let x3 = succ x2 in 
  -- Creates the 4 commuted nodes
  let A1 = some (dup a1 x0 x1) in
  let A2 = some (dup a2 x2 x3) in
  let B1 = some (con b1 x2 x0) in
  let B2 = some (con b2 x3 x1) in
  -- Returns result
  (A1 # A2 # B1 # B2 # graph)

-- Performs an interaction on indices 'i', 'j'
interact : IndexPair -> Graph -> Graph
interact (pair i j) g with get i g | get j g | set i none (set j none g)
... | some (era a0)       | some (era b0)       | g = g
... | some (era a0)       | some (con b0 b1 b2) | g = eras-rule b1 b2       g
... | some (era a0)       | some (dup b0 b1 b2) | g = eras-rule b1 b2       g
... | some (con a0 a1 a2) | some (era b0)       | g = eras-rule a1 a2       g
... | some (con a0 a1 a2) | some (con b0 b1 b2) | g = anni-rule a1 a2 b1 b2 g
... | some (con a0 a1 a2) | some (dup b0 b1 b2) | g = comm-rule a1 a2 b1 b2 g
... | some (dup a0 a1 a2) | some (era b0)       | g = eras-rule a1 a2       g
... | some (dup a0 a1 a2) | some (con b0 b1 b2) | g = comm-rule b1 b2 a1 a2 g
... | some (dup a0 a1 a2) | some (dup b0 b1 b2) | g = anni-rule b1 b2 a1 a2 g
... | a                   | b                   | g = a # b # g

-- Finds the active pairs of a graph
active-pairs : Graph -> List IndexPair
active-pairs graph = find zero empty graph where

  -- Maps variables to indices where they occur
  Map : Set
  Map = Var -> Maybe Nat

  -- Empty map
  empty : Map
  empty = λ x -> none

  -- Extends a map with a (idx,var) pair
  ext : Nat -> Var -> Map -> Map
  ext idx var map = λ x -> if (eq x var) (some idx) (map x)

  -- Registers an active pair, when found
  reg : Maybe Nat -> Nat -> List IndexPair -> List IndexPair
  reg none     j xs = xs
  reg (some i) j xs = pair i j # xs

  -- Finds and collects all active pairs
  find : Nat -> Map -> Graph -> List IndexPair
  find i map nil                 = nil
  find i map (none      # graph) = find (succ i) map graph
  find i map (some node # graph) =
    let a0 = get-main node in
    let xs = find (succ i) (ext i a0 map) graph
    in reg (map a0) i xs

-- Performs a parallel reduction of all active pairs
reduce : Graph -> Graph
reduce graph = foldr interact graph (active-pairs graph)

-- ~
-- ~
-- ~

-- Theorems and Proofs
-- ===================

-- An active pair has identical main ports
IsActive : IndexPair -> Graph -> Set
IsActive (pair i j) g with get i g | get j g
... | none   | y      = Empty
... | x      | none   = Empty
... | some x | some y = Pair (i != j) (get-main x == get-main y)

-- A normalized graph has no active pairs
IsNormal : Graph -> Set
IsNormal graph = (npair : IndexPair) -> Not (IsActive npair graph)

-- Reduction relation
data _=>_ : Graph -> Graph -> Set where
  nham : ∀ {npair graph} -> IsActive npair graph -> graph => interact npair graph

-- Reflexive transitive closure
data _==>_ : Graph -> Graph -> Set where
  base : ∀ g -> g ==> g
  step : ∀ {g0 g1 g2} -> g0 => g1 -> g1 => g2 -> g0 ==> g2

-- A graph is linear when all symbols are CON
IsLinear : Graph -> Set
IsLinear graph = ∀ i -> Unwrap (get i graph) (λ x -> symbol x == CON)

-- Substitution doesn't affect the size
size-subst : ∀ a b g -> size (subst a b g) == size g
size-subst a b nil                       = refl
size-subst a b (none                # g) = size-subst a b g
size-subst a b (some (era a0)       # g) = apl succ (size-subst a b g)
size-subst a b (some (con a0 a1 a2) # g) = apl succ (size-subst a b g)
size-subst a b (some (dup a0 a1 a2) # g) = apl succ (size-subst a b g)

-- Setting a 'some' to 'none' reduces size by 1
set-some-to-none-size : ∀ i g -> S _ (λ x -> get i g == some x) -> succ (size (set i none g)) == size g
set-some-to-none-size zero     (some x # g) p = refl
set-some-to-none-size (succ i) (some x # g) p = apl succ (set-some-to-none-size i g p)
set-some-to-none-size (succ i) (none   # g) p = set-some-to-none-size i g p

-- Getting after setting (a different index) returns the same result
get-after-set : ∀ i x j y g -> i != j -> get i g == x -> get i (set j y g) == x
get-after-set zero     x zero     y nil      e0 e1 = e1
get-after-set zero     x zero     y (nd # g) e0 e1 = absurd (e0 refl)
get-after-set zero     x (succ j) y nil      e0 e1 = e1
get-after-set zero     x (succ j) y (nd # g) e0 e1 = e1
get-after-set (succ i) x zero     y nil      e0 e1 = e1
get-after-set (succ i) x zero     y (nd # g) e0 e1 = e1
get-after-set (succ i) x (succ j) y nil      e0 e1 = e1
get-after-set (succ i) x (succ j) y (nd # g) e0 e1 = get-after-set i x j y g (λ k -> e0 (apl succ k)) e1

-- Reducing a linear graph decreases its size by 2
linear-decreases : ∀ {g0 g1} -> IsLinear g0 -> g0 => g1 -> size g0 == succ (succ (size g1))
linear-decreases {g0} {g1} lin red = ?

-- linear-decreases li (nham {pair i j} {g0} x) with get i g0 in got-i | get j g0 in got-j | li i | li j | x
-- ... | some (con a0 a1 a2) | some (con b0 b1 b2) | li-i | li-j | pair x0 x1
  -- rewrite size-subst (if (eq a1 a2) b1 a2) (if (eq a1 b2) b1 b2) (subst a1 b1 (set i none (set j none g0)))
  -- rewrite size-subst a1 b1 (set i none (set j none g0))
  -- rewrite set-some-to-none-size i (set j none g0) (con a0 a1 a2 , get-after-set i (some (con a0 a1 a2)) j none g0 x0 got-i)
  -- rewrite set-some-to-none-size j g0 (con b0 b1 b2 , got-j)
  -- = refl
