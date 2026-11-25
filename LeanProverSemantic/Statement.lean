import Lean

/-!
`#validate` grades a Lean statement, before or after it is proved.

- bronze:  the statement elaborates
- silver:  the proof uses only standard axioms (theorems only)
- gold:    the hypotheses are satisfiable and the statement holds on a finite grid
- diamond: gold, and every mutant of the statement is refuted on the grid

Variables range over `Nat` (0..6) or `Int` (-6..6). Hypotheses and the
conclusion must be decidable. Mutants drop a hypothesis, drop a disjunct,
turn `≤` into `<`, or shift a numeric literal. A surviving mutant means the
statement does not depend on that part of itself: slack, vacuity, or a
misformalization.
-/

open Lean Meta Elab Term Command

namespace LeanProverSemantic.Statement

def gridMax : Nat := 6
def maxVars : Nat := 3
def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

inductive Kind where
  | nat
  | int

def Kind.domain : Kind → List Int
  | .nat => (List.range (gridMax + 1)).map Int.ofNat
  | .int => (List.range (2 * gridMax + 1)).map fun (i : Nat) => (i : Int) - gridMax

def Kind.toExpr : Kind → Int → Expr
  | .nat, v => mkRawNatLit v.toNat
  | .int, .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .int, .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

def grid : List (List Int) → List (List Int)
  | [] => [[]]
  | d :: ds => (grid ds).flatMap fun rest => d.map (· :: rest)

def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 0).isConstOf ``Nat then
      match e.getArg! 1 with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- `decide p` with its instance, synthesized once over free variables. -/
def decideOpen (p : Expr) : MetaM (Option Expr) := do
  try
    let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
    return some (mkApp2 (mkConst ``Decidable.decide) p inst)
  catch _ => return none

def evalBool (e : Expr) : MetaM (Option Bool) := do
  let r ← withTransparency .all <| whnf e
  if r.isConstOf ``Bool.true then return some true
  if r.isConstOf ``Bool.false then return some false
  return none

def andE (p q : Expr) : Expr := mkApp2 (mkConst ``And) p q
def orE (p q : Expr) : Expr := mkApp2 (mkConst ``Or) p q

/-- Replace Nat literal argument `i` of relation `e` by `n + delta`. -/
def shiftLit (e : Expr) (i : Nat) (delta : Int) : Array (String × Expr) := Id.run do
  let args := e.getAppArgs
  unless (args[0]!).isConstOf ``Nat do return #[]
  let some n := natLit? args[i]! | return #[]
  let m := (n : Int) + delta
  if m < 0 then return #[]
  return #[(s!"{n} → {m}", mkAppN e.getAppFn (args.modify i fun _ => mkNatLit m.toNat))]

partial def mutants (e : Expr) : MetaM (Array (String × Expr)) := do
  let args := e.getAppArgs
  if e.isAppOfArity ``And 2 then
    let p := args[0]!
    let q := args[1]!
    let ps ← mutants p
    let qs ← mutants q
    return ps.map (fun (d, p') => (d, andE p' q)) ++ qs.map (fun (d, q') => (d, andE p q'))
  else if e.isAppOfArity ``Or 2 then
    let p := args[0]!
    let q := args[1]!
    let ps ← mutants p
    let qs ← mutants q
    return #[("drop right disjunct", p), ("drop left disjunct", q)]
      ++ ps.map (fun (d, p') => (d, orE p' q)) ++ qs.map (fun (d, q') => (d, orE p q'))
  else if e.isAppOfArity ``LE.le 4 then
    let mut out := #[]
    try
      out := out.push ("≤ → <", ← mkAppM ``LT.lt #[args[2]!, args[3]!])
    catch _ => pure ()
    return out ++ shiftLit e 3 (-1) ++ shiftLit e 2 1
  else if e.isAppOfArity ``LT.lt 4 then
    return shiftLit e 3 (-1) ++ shiftLit e 2 1
  else if e.isAppOfArity ``Eq 3 then
    return shiftLit e 2 1 ++ shiftLit e 2 (-1) ++ shiftLit e 1 1 ++ shiftLit e 1 (-1)
  else
    return #[]

def fmtPoint (names : Array Name) (pt : List Int) : String :=
  " ".intercalate ((names.toList.zip pt).map fun (n, v) => s!"{n}={v}")

def grade (xs : Array Expr) (concl : Expr) : MetaM (Array MessageData) := do
  let mut vars := #[]
  let mut kinds := #[]
  let mut hyps := #[]
  for x in xs do
    let ty ← inferType x
    if ty.isConstOf ``Nat then
      vars := vars.push x
      kinds := kinds.push Kind.nat
    else if ty.isConstOf ``Int then
      vars := vars.push x
      kinds := kinds.push Kind.int
    else if ← isProp ty then
      hyps := hyps.push ty
    else
      return #[m!"gold     skip  unsupported binder type {ty}"]
  if vars.size > maxVars then
    return #[m!"gold     skip  more than {maxVars} variables"]
  let names ← vars.mapM fun v => v.fvarId!.getUserName
  let some conclD ← decideOpen concl
    | return #[m!"gold     skip  conclusion is not decidable"]
  let mut hypDs := #[]
  for h in hyps do
    let some d ← decideOpen h
      | return #[m!"gold     skip  hypothesis {h} is not decidable"]
    hypDs := hypDs.push d
  let vars' := vars
  let kinds' := kinds
  let eval : List Int → Expr → MetaM Bool := fun pt d => do
    let vals := (kinds'.toList.zip pt).toArray.map fun (k, v) => k.toExpr v
    match ← evalBool (d.replaceFVars vars' vals) with
    | some b => pure b
    | none => throwError "could not evaluate at {fmtPoint names pt}"
  let pts := grid (kinds.toList.map Kind.domain)
  let mut table := #[]
  for pt in pts do
    let hv ← hypDs.mapM (eval pt)
    let cv ← eval pt conclD
    table := table.push (pt, hv, cv)
  let dom := ", ".intercalate ((names.toList.zip kinds.toList).map fun (n, k) =>
    match k with
    | .nat => s!"{n} ∈ 0..{gridMax}"
    | .int => s!"{n} ∈ -{gridMax}..{gridMax}")
  let mut out := #[m!"grid     {dom} ({pts.length} points)"]
  let sat := table.filter fun (_, hv, _) => hv.all id
  if sat.isEmpty then
    return out.push m!"gold     FAIL  hypotheses unsatisfiable on the grid (vacuous)"
  if let some (pt, _, _) := sat.find? fun (_, _, cv) => !cv then
    return out.push m!"gold     FAIL  counterexample {fmtPoint names pt}"
  out := out.push m!"gold     PASS  holds; {sat.size}/{pts.length} points satisfy the hypotheses"
  let mut survivors : Array String := #[]
  let mut total := 0
  for i in [0:hyps.size] do
    total := total + 1
    let refuted := table.any fun (_, hv, cv) =>
      !cv && (List.range hv.size).all fun j => j == i || hv[j]!
    unless refuted do survivors := survivors.push s!"drop hypothesis {i + 1}"
  for (desc, m) in ← mutants concl do
    total := total + 1
    match ← decideOpen m with
    | none => survivors := survivors.push s!"{desc} (undecidable)"
    | some md =>
      let mut refuted := false
      for (pt, _, _) in sat do
        if !(← eval pt md) then
          refuted := true
          break
      unless refuted do survivors := survivors.push desc
  if total == 0 then
    return out.push m!"diamond  skip  no mutants generated"
  if survivors.isEmpty then
    return out.push m!"diamond  PASS  {total}/{total} mutants refuted"
  return out.push
    m!"diamond  FAIL  {total - survivors.size}/{total} refuted; survivors: {", ".intercalate survivors.toList}"

def validate (stmt : Expr) (thm? : Option Name) : MetaM MessageData := do
  let mut out : Array MessageData := #[m!"{stmt}", m!"bronze   PASS  elaborates"]
  match thm? with
  | none => out := out.push m!"silver   skip  statement only, no proof"
  | some n =>
    let axs ← collectAxioms n
    let bad := axs.filter (· ∉ stdAxioms)
    out := out.push <| if bad.isEmpty then m!"silver   PASS  axioms {axs.toList}"
      else m!"silver   FAIL  nonstandard axioms {bad.toList}"
  let rest ← try forallTelescope stmt grade
    catch e => pure #[m!"gold     skip  {e.toMessageData}"]
  return MessageData.joinSep (out ++ rest).toList "\n"

syntax (name := validateCmd) "#validate " term : command

@[command_elab validateCmd] def elabValidate : CommandElab := fun stx => liftTermElabM do
  let t := stx[1]
  let mut thm? : Option Name := none
  if t.isIdent then
    try
      let n ← realizeGlobalConstNoOverloadWithInfo t
      if let .thmInfo _ ← getConstInfo n then thm? := some n
    catch _ => pure ()
  let stmt ← match thm? with
    | some n => pure (← getConstInfo n).type
    | none => do
      let e ← elabTerm t (some (mkSort Level.zero))
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  logInfo (← validate stmt thm?)

end LeanProverSemantic.Statement
