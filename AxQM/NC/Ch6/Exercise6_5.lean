/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.AugmentedSearchOracle

/-!
# Nielsen & Chuang, Exercise 6.5 (the augmented oracle `O'` from one call to `O`)

*(N&C p. 255.)*

Show the augmented oracle O' can be built from one call to O and elementary gates using extra qubit.

**The setting (N&C §6.1.4, p. 255).** When *more than half* the items of a search space are
solutions the Grover iteration count perversely *grows* with the number of solutions `M`. One fix
**doubles** the search space by adjoining a single extra qubit `|q⟩` (from `N` to `2N` items) and
replaces the oracle `O` by an **augmented oracle** `O'` that marks an item `(x, q)` *only if* `x` is
a solution *and* the extra bit is `q = 0`. Then fewer than half of the `2N` items are solutions, so
the plain search algorithm applies. Exercise 6.5 asks to exhibit `O'` from **one** call to `O` plus
elementary gates.

**The construction (phase kickback).** The original bit-flip oracle acts on the index `|x⟩` and a
response qubit `|r⟩` by `O|x⟩|r⟩ = |x⟩|r ⊕ f(x)⟩` (`f(x) = 1` iff `x` is a solution); on the
augmented register it leaves the extra qubit `q` untouched. Supplying `r` as a fresh work qubit in
`|0⟩`, the circuit `X_r · CNOT_{q→r} · H_r · O · H_r · CNOT_{q→r} · X_r` prepares `r` as `|−⟩`
exactly on the `q = 0` branch, so the **single** oracle call `O` kicks the phase `(−1)^{f(x)}`
precisely when `q = 0` and nothing when `q = 1`, and returns the work qubit to `|0⟩` — the mark
"solution ∧ `q = 0`" defining `O'`. The surrounding gates are elementary and independent of `x` and
`f`, so the whole `O'` uses just **one** application of `O`.

## The formalisation

The formalisation has three parts:

* **`AxQM/Concrete/AugmentedOracleConstruction.lean`** — complex matrices: the two-qubit response
  block `augResponseCircuit` and the key diagonal identity `augResponseCircuit_eq_diagonal` (phase
  kickback at the matrix level, for a single item's flag).
* **`AxQM/Postulates/API/AugmentedOracleBlock.lean`** — the physical counterpart of the block:
  `augmentedOracleBlock c : Evolution (qubit ⊗ qubit)` for a *single item* with a fixed solution
  flag `c`, and `augmentedOracleBlock_hasEigenstate`, the mark on `|q⟩|0⟩`.
* **`AxQM/Postulates/API/AugmentedSearchOracle.lean`** — the **full-register assembly**
  over the entire search index, the content that makes "**one** application of `O`" honest:
  * `IsSearchBitFlipOracle f O` — the abstract one-call oracle `O|x⟩|a⟩|b⟩ = |x⟩|a⟩|b ⊕ f(x)⟩` over
    the general index `qudit N` (the `qudit N`-generalisation of `IsDeutschOracle`);
  * `augmentedSearchOracle O` — the seven-factor circuit built from **one** `O` and the elementary
    gates `X_r`, `CNOT_{q→r}`, `H_r`;
  * `hadamardConj_oracle_op` — the abstract-oracle collapse `H_r · O · H_r = Z^{f(x)}` (the one-call
    analogue of the block's `hadamardConj_targetXPow`, `H X^c H = Z^c`);
  * `augmentedSearchOracle_hasEigenstate` — the mark, for **every** item `x` of the search space.

## The formalisation (this file)

`augmentedSearchOracle_marks_solution_and_zero` is the statement for the exercise, in terms of
`Evolution.HasEigenstate`, `augmentedSearchOracle`, `qudit` / `qubit` / `quditBasis` /
`qubitBasis` / `PureState.tmul`: for **any** one-call bit-flip oracle `O` for `f`, the augmented
circuit `augmentedSearchOracle O`, on the response work qubit supplied in `|0⟩`, fixes `|x⟩|q⟩|0⟩`
with eigenvalue `−1` exactly when the item is a solution (`f(x) = 1`) **and** the extra bit is
`q = 0`, and `+1` otherwise — the augmented-oracle mark `O'`, using one call to `O`. It
discharges by applying the full-register assembly `augmentedSearchOracle_hasEigenstate`.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 6.5 — the augmented oracle `O'` from one call to `O`.** For **any**
one-call bit-flip oracle `O` for `f : Fin N → Fin 2` on the augmented register
`qudit N ⊗ (qubit ⊗ qubit)` (search index `|x⟩`, extra qubit `|q⟩`, response `|r⟩`), the augmented
circuit `augmentedSearchOracle O` — built from **one** application of `O` and the elementary gates
`X_r`, `CNOT_{q→r}`, `H_r` on the extra qubit `|q⟩` — implements the augmented oracle `O'`: on the
response work qubit supplied in `|0⟩`, `|x⟩|q⟩|0⟩` is an eigenstate whose eigenvalue is `−1` exactly
when the item is a solution (`f(x) = 1`) **and** the extra bit is `q = 0`, and `+1` otherwise. That
is `O'` marks `(x, q)` iff `x` is a solution and `q = 0`, for every item `x` of the search space,
with the work qubit returned to `|0⟩`.

It discharges by applying the full-register assembly `augmentedSearchOracle_hasEigenstate`
(`AxQM/Postulates/API/AugmentedSearchOracle.lean`), whose proof reduces the one oracle call to the
diagonal phase `Z^{f(x)}` (`hadamardConj_oracle_op`) and tracks `|x⟩|q⟩|0⟩` through the flanking
elementary gates. -/
theorem augmentedSearchOracle_marks_solution_and_zero {N : ℕ} {f : Fin N → Fin 2}
    {O : Evolution ((qudit N).compose (qubit.compose qubit))} (h : IsSearchBitFlipOracle f O)
    (x : Fin N) (q : Fin 2) :
    (augmentedSearchOracle O).HasEigenstate (if f x = 1 ∧ q = 0 then -1 else 1)
      ((quditBasis x).tmul ((qubitBasis q).tmul (qubitBasis 0))) :=
  augmentedSearchOracle_hasEigenstate h x q

end AxQM
