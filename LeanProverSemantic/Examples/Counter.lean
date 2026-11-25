import LeanProverSemantic.Tiers

/-!
Counter with bound 3. Reachable states 0..3.
The invariant `c ≤ 3` is the faithful statement.
-/

namespace LeanProverSemantic.Examples.Counter

def counter : Model Nat := ⟨[0, 1, 2, 3]⟩

def inv (c : Nat) : Bool := decide (c ≤ 3)

/-- Mutant: lower bound raised to 1. State 0 refutes it. -/
def mutLower (c : Nat) : Bool := decide (1 ≤ c ∧ c ≤ 3)

/-- Mutant: the tautology. No state refutes it. -/
def tautology (_ : Nat) : Bool := true

example : nonVacuous inv counter = true := by decide
example : gold inv counter = true := by decide
example : diamond inv [mutLower] counter = true := by decide
example : diamond inv [tautology] counter = false := by decide

end LeanProverSemantic.Examples.Counter
