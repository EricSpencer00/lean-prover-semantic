# Lean Prover Semantic

Validation tiers for formal statements, ported from the TLA+ synthesis paper's
bronze / silver / gold / diamond hierarchy to Lean 4.

A proof that compiles shows the formal statement is true. It does not show the
statement says what the informal problem says. The diamond tier closes part of
that gap: a statement must be sensitive to mutations of its invariant, so
tautologies and vacuous statements fail.

## Tiers

| Tier | Check |
|---|---|
| bronze | compiles (`lake build`) |
| silver | non-vacuous: some state satisfies the invariant |
| gold | invariant holds on every state |
| diamond | gold, and every mutant is refuted by some state |

Models are explicit state lists. The check is only as strong as the enumeration.

## Build

```bash
lake build
```

## Sources

- Levent Alpöge, Riemann Hypothesis note: https://alpo.ge/remark.pdf
- Jenny Lorraine Nielsen, critique of the Alpöge Lean code: https://philarchive.org/rec/NIEIOT-2
  (not yet read in full; the argument summarized here is from secondary coverage)

## Status

Finite-model tiers only. Not yet connected to Lean statements over Mathlib
types, and no mutant generator yet.
