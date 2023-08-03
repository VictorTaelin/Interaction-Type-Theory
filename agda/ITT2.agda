open import Base

data Symbol : Set where
  ERA : Symbol
  CON : Symbol
  DUP : Symbol

data Slot : Set where
  S0 : Slot
  S1 : Slot
  S2 : Slot

record Port (len : Nat) : Set where
  constructor port
  field addr : Fin len
        slot : Slot

record Wiring (len : Nat) : Set where
  constructor wiring
  field enter : Port len -> Port len
        invol : ∀ x -> enter (enter x) == x
        nofix : ∀ x -> enter x != x

record Graph (len : Nat) : Set where
  constructor graph
  field types : Fin len -> Symbol
        wires : Wiring len

-- TODO:
-- Converts a list of nats to a graph. Example:
-- build-graph [(0,1,1),(0,2,2)] == example
build-graph : (nodes : List (Pair Nat Nat)) -> Maybe (Graph (len nodes))
build-graph = ?

-- Example graph:
-- (a b b)
-- (a c c)
example : Graph 2
example = graph types wires where

  types : Fin 2 -> Symbol
  types fz      = CON
  types (fs fz) = CON

  wires : Wiring 2
  wires = wiring enter invol nofix where

    enter : (x : Port 2) → Port 2
    enter (port fz      S0) = port (fs fz) S0
    enter (port fz      S1) = port fz S2
    enter (port fz      S2) = port fz S1
    enter (port (fs fz) S0) = port fz S0
    enter (port (fs fz) S1) = port (fs fz) S2
    enter (port (fs fz) S2) = port (fs fz) S1

    invol : (x : Port 2) -> enter (enter x) == x
    invol (port fz      S0) = refl
    invol (port fz      S1) = refl
    invol (port fz      S2) = refl
    invol (port (fs fz) S0) = refl
    invol (port (fs fz) S1) = refl
    invol (port (fs fz) S2) = refl

    nofix : (x : Port 2) -> enter x == x -> Empty
    nofix (port fz      S0) ()
    nofix (port fz      S1) ()
    nofix (port fz      S2) ()
    nofix (port (fs fz) S0) ()
    nofix (port (fs fz) S1) ()
