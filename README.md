# Lean Prover Semantic

A proof that compiles shows the formal statement is true. It does not show the
statement says what the informal problem says. This repo grades statements on
that second question, porting the bronze / silver / gold / diamond hierarchy
from TLA+ spec synthesis to Lean 4.

## `#validate`

```lean
import LeanProverSemantic

#validate ∀ x : Nat, x * x = 4 → x = 2 ∨ x = 3
```

```
grid     x ∈ 0..6 (7 points)
gold     PASS  holds; 1/7 points satisfy the hypotheses
diamond  FAIL  4/7 refuted; survivors: drop right disjunct, 3 → 4, 3 → 2
```

| Tier | Check |
|---|---|
| bronze | statement elaborates |
| silver | proof uses only `propext`, `Classical.choice`, `Quot.sound` (theorems only) |
| gold | hypotheses satisfiable and statement holds on a finite grid |
| diamond | gold, and every mutant is refuted on the grid |

Mutants drop a hypothesis, drop a disjunct, turn `≤` into `<`, or shift a
numeric literal. A surviving mutant marks a part of the statement nothing
depends on: slack, vacuity, or a misformalization.

`#validate` takes a statement or a theorem name. Variables range over `Nat`
(0..6) or `Int` (-6..6), at most three; hypotheses and conclusion must be
decidable.

## Defect classes covered

`LeanProverSemantic/Examples/Statements.lean`, locked with `#guard_msgs`:

| Statement | Defect | Caught by |
|---|---|---|
| `a ≤ 3 → b ≤ 3 → a + b ≤ 6` | none | passes diamond |
| `n < 0 → n = 5` | vacuous hypothesis | gold |
| `n ≤ 3 → n ≤ 100` | slack conclusion | diamond |
| `a - b + b = a` over `Nat` | ℕ default for a ℤ statement | gold, counterexample `a=0 b=1` |
| `x * x = 4 → x = 2 ∨ x = 3` | spurious disjunct | diamond |
| theorem proved `by sorry` | unproved | silver |

`Examples/Counter.lean` keeps the original TLA-style tiers over explicit state
lists.

## Build

```bash
lake build
```

## Limits

- The grid is a test, not a proof: a statement can pass gold and fail at 7.
- Surviving mutants include equivalent ones; a survivor is a flag for review.
- No Mathlib types yet (reals, finsets, polynomials), so most competition
  statements are out of reach.

## Sources

- Levent Alpöge, Riemann Hypothesis note: https://alpo.ge/remark.pdf. The
  formalization's `anyGeometry : GeoP := fun _ _ _ => True` (`OverIx.lean:19`)
  is the internal-definition case these tiers do not yet cover.
- Jenny Lorraine Nielsen, critique of the Alpöge Lean code:
  https://philarchive.org/rec/NIEIOT-2
- Ospanov et al., miniF2F-Lean Revisited: https://arxiv.org/abs/2511.03108
- Ammanamanchi et al., Faults in Our Formal Benchmarking: https://arxiv.org/abs/2606.29493
- Poiroux et al., ProofNet#: https://arxiv.org/abs/2406.07222
