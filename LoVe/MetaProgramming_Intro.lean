
import Lean


/-
We can introduce notation using a macro which transforms
our syntax to Lean's syntax (or syntax we previously defined).
Here we introduce the ↦ notation for functions.-/


macro x:ident ":" t:term " ↦ " y:term : term => do
  `(fun $x : $t => $y)

#eval (x : Nat ↦ x + 2) 2 -- 4

macro x:ident " ↦ " y:term : term => do
  `(fun $x  => $y)

#eval (x ↦  x + 2) 2 -- 4
