import LeanProverSemantic.Statement

/-!
Each case mirrors a defect class from the Lean benchmark audits
(ProofNet#, miniF2F-v2, "Faults in Our Formal Benchmarking").
`#guard_msgs` locks the expected grades.
-/

namespace LeanProverSemantic.Examples.Statements

/-- info: ∀ (a b : Nat), a ≤ 3 → b ≤ 3 → a + b ≤ 6
bronze   PASS  elaborates
silver   skip  statement only, no proof
grid     a ∈ 0..6, b ∈ 0..6 (49 points)
gold     PASS  holds; 16/49 points satisfy the hypotheses
diamond  PASS  4/4 mutants refuted -/
#guard_msgs in -- Faithful and tight.
#validate ∀ a b : Nat, a ≤ 3 → b ≤ 3 → a + b ≤ 6

/-- info: ∀ (n : Nat), n < 0 → n = 5
bronze   PASS  elaborates
silver   skip  statement only, no proof
grid     n ∈ 0..6 (7 points)
gold     FAIL  hypotheses unsatisfiable on the grid (vacuous) -/
#guard_msgs in -- Vacuous: no natural number is below 0.
#validate ∀ n : Nat, n < 0 → n = 5

/-- info: ∀ (n : Nat), n ≤ 3 → n ≤ 100
bronze   PASS  elaborates
silver   skip  statement only, no proof
grid     n ∈ 0..6 (7 points)
gold     PASS  holds; 4/7 points satisfy the hypotheses
diamond  FAIL  0/3 refuted; survivors: drop hypothesis 1, ≤ → <, 100 → 99 -/
#guard_msgs in -- Slack: true, but far from its hypothesis.
#validate ∀ n : Nat, n ≤ 3 → n ≤ 100

/-- info: ∀ (a b : Nat), a - b + b = a
bronze   PASS  elaborates
silver   skip  statement only, no proof
grid     a ∈ 0..6, b ∈ 0..6 (49 points)
gold     FAIL  counterexample a=0 b=1 -/
#guard_msgs in -- ℕ default: the informal statement is over ℤ.
#validate ∀ a b : Nat, a - b + b = a

/-- info: ∀ (a b : Int), a - b + b = a
bronze   PASS  elaborates
silver   skip  statement only, no proof
grid     a ∈ -6..6, b ∈ -6..6 (169 points)
gold     PASS  holds; 169/169 points satisfy the hypotheses
diamond  skip  no mutants generated -/
#guard_msgs in
#validate ∀ a b : Int, a - b + b = a

/-- info: ∀ (x : Nat), x * x = 4 → x = 2 ∨ x = 3
bronze   PASS  elaborates
silver   skip  statement only, no proof
grid     x ∈ 0..6 (7 points)
gold     PASS  holds; 1/7 points satisfy the hypotheses
diamond  FAIL  4/7 refuted; survivors: drop right disjunct, 3 → 4, 3 → 2 -/
#guard_msgs in -- Spurious disjunct.
#validate ∀ x : Nat, x * x = 4 → x = 2 ∨ x = 3

theorem sum_le (a b : Nat) (ha : a ≤ 3) (hb : b ≤ 3) : a + b ≤ 6 := by omega

/-- info: ∀ (a b : Nat), a ≤ 3 → b ≤ 3 → a + b ≤ 6
bronze   PASS  elaborates
silver   PASS  axioms [propext, Quot.sound]
grid     a ∈ 0..6, b ∈ 0..6 (49 points)
gold     PASS  holds; 16/49 points satisfy the hypotheses
diamond  PASS  4/4 mutants refuted -/
#guard_msgs in
#validate sum_le

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem sum_le_sorry (a b : Nat) (ha : a ≤ 3) (hb : b ≤ 3) : a + b ≤ 6 := by sorry

/-- info: ∀ (a b : Nat), a ≤ 3 → b ≤ 3 → a + b ≤ 6
bronze   PASS  elaborates
silver   FAIL  nonstandard axioms [sorryAx]
grid     a ∈ 0..6, b ∈ 0..6 (49 points)
gold     PASS  holds; 16/49 points satisfy the hypotheses
diamond  PASS  4/4 mutants refuted -/
#guard_msgs in
#validate sum_le_sorry

end LeanProverSemantic.Examples.Statements
