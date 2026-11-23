/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Lean
import Batteries.Tactic.Lint

/-!
# Proof integrity: `#check_integrity`

Every declaration of this library — in `AxQM` and in `ToMathlib` — is fully proved and
rests on Lean's standard axioms alone. Concretely, for each such declaration:

* it is not itself an `axiom`, so the library adds nothing to the trusted base; and
* its transitive dependencies reach no axiom other than `propext`, `Classical.choice` and
  `Quot.sound`. This excludes `sorryAx` (an unfinished proof, however it was written) and
  `Lean.ofReduceBool` / `Lean.trustCompiler` (`native_decide`, which trusts the compiler).

The check reads the elaborated environment, not the sources, so it holds for modules whose
`.olean`s were reused from a cache and cannot be evaded by how a `sorry` is spelled.

Run it over the whole library with

```
import AxQM
import ToMathlib
#check_integrity
```

The same check is registered as the env-linter `checkProofIntegrity`, for `#lint` and
`lake exe runLinter`.
-/

open Lean Elab Command

namespace AxQM.Meta

/-- The axioms a declaration of this library may depend on. -/
def standardAxioms : NameSet :=
  .ofList [``propext, ``Classical.choice, ``Quot.sound]

/-- The module roots whose declarations are checked. -/
def checkedRoots : List Name := [`AxQM, `ToMathlib]

/-- Whether `n` belongs to this library: declared in a module under `checkedRoots`, or in the file
being elaborated (so the check can be exercised on a scratch file). Private and auxiliary
declarations count: a `sorry` in an unused private lemma is still an unfinished proof. -/
def isChecked (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => checkedRoots.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => true

/-- The non-standard axioms each constant depends on, memoized across constants, so that one pass
over the library visits every dependency once. -/
partial def nonstandardAxioms (env : Environment) (n : Name) :
    StateM (NameMap NameSet) NameSet := do
  if let some s := (← get).find? n then return s
  -- mark as in progress; a dependency cycle only arises through `opaque`/recursive auxiliaries,
  -- and contributes nothing new
  modify (·.insert n {})
  let result ← match env.find? n with
    | none => pure {}
    | some (.axiomInfo _) => pure (if standardAxioms.contains n then {} else NameSet.empty.insert n)
    | some ci =>
      let extra : Array Name := match ci with
        | .inductInfo iv => iv.ctors.toArray
        | .ctorInfo cv => #[cv.induct]
        | _ => #[]
      let deps := ci.type.getUsedConstants ++
        ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[] ++ extra
      deps.foldlM (init := {}) fun acc d => return acc.append (← nonstandardAxioms env d)
  modify (·.insert n result)
  return result

/-- The library declarations that violate proof integrity, each with the reason. -/
def integrityViolations (env : Environment) : Array (Name × MessageData) := Id.run do
  let mut memo : NameMap NameSet := {}
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    if !isChecked env n then continue
    if let .axiomInfo _ := ci then
      out := out.push (n, m!"is a new `axiom`")
      continue
    let (axs, memo') := (nonstandardAxioms env n).run memo
    memo := memo'
    unless axs.isEmpty do
      out := out.push (n, m!"depends on {axs.toList}")
  return out

/-- `#check_integrity`: fail if any declaration of this library is an `axiom` or depends on an
axiom other than `propext`, `Classical.choice` and `Quot.sound`. -/
elab "#check_integrity" : command => do
  let env ← getEnv
  let bad := integrityViolations env
  let count : Nat := env.constants.fold (init := 0) fun k n _ ↦
    if isChecked env n then k + 1 else k
  if bad.isEmpty then
    logInfo m!"proof integrity passed: {count} declarations, none an `axiom`, none depending on \
      an axiom beyond `propext`, `Classical.choice`, `Quot.sound`."
  else
    let lines := bad.toList.take 50 |>.map fun (n, why) ↦ m!"  {n} {why}"
    throwError m!"proof integrity FAILED for {bad.size} declaration(s):\n\
      {MessageData.joinSep lines "\n"}"

/-- **Proof-integrity linter**: a declaration of this library may not be an `axiom`, nor depend on
an axiom other than `propext`, `Classical.choice` and `Quot.sound`. -/
@[env_linter] meta def checkProofIntegrity : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "no declaration is an axiom or depends on a non-standard axiom"
  errorsFound := "proof integrity: declarations that are axioms or depend on non-standard axioms"
  test declName := do
    let env ← getEnv
    unless isChecked env declName do return none
    match env.find? declName with
    | some (.axiomInfo _) => return some m!"is a new `axiom`"
    | _ =>
      let axs ← collectAxioms declName
      let bad := axs.filter (!standardAxioms.contains ·)
      if bad.isEmpty then return none else return some m!"depends on {bad.toList}"

end AxQM.Meta
