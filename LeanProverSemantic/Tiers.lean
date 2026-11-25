/-!
Validation tiers for formal statements over finite models.

Mirrors the four-tier hierarchy of the TLA+ synthesis paper
(bronze, silver, gold, diamond). A model is an explicit list of states
(the reachable set). Invariants are `S → Bool`.

- bronze:  the statement compiles (checked by `lake build`)
- silver:  non-vacuous: some state satisfies the invariant
- gold:    the invariant holds on every state
- diamond: gold, and every mutant of the invariant is refuted by some state
-/

namespace LeanProverSemantic

structure Model (S : Type) where
  states : List S

def nonVacuous {S : Type} (inv : S → Bool) (m : Model S) : Bool :=
  m.states.any inv

def gold {S : Type} (inv : S → Bool) (m : Model S) : Bool :=
  m.states.all inv

/-- Each mutant must be refuted by some state, as TLC would find a counterexample. -/
def diamond {S : Type} (inv : S → Bool) (mutants : List (S → Bool)) (m : Model S) : Bool :=
  gold inv m && mutants.all (fun μ => m.states.any (fun s => !μ s))

end LeanProverSemantic
