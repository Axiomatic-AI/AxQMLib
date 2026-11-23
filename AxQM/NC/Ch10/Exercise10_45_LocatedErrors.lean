/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerCodeDistance

/-!
# Nielsen & Chuang, Exercise 10.45 (Correcting located errors)

[n,k,d] stabilizer code can correct located errors on d-1 known-position qubits.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 10.45 (p. 467).

## The formalisation

Because we are told *precisely which* `d − 1` qubits `L` are affected, the relevant candidate errors
are all Pauli operators `E ∈ Gₙ` supported on `L` (acting as the identity off `L`). For two
`L`-supported errors `Eⱼ, Eₖ`, the product `Eⱼ⁻¹ Eₖ` is again supported on `L`, so it has weight at
most `|L| = d − 1 < d`. An operator of weight below the distance `d` cannot be a nontrivial logical
operator: if it lies in `N(S)` it is a phase multiple `iˢ·s'` of a stabilizer element (`P Eⱼ† Eₖ P =
iˢ·P`), otherwise it anticommutes with a stabilizer generator (`P Eⱼ† Eₖ P = 0`). Either way
`P Eⱼ† Eₖ P` is a scalar multiple of `P`, so the **Knill–Laflamme conditions** (Theorem 10.1) hold
with a Hermitian coefficient matrix and `{Eⱼ}` is a **correctable set of errors** for `C(S)`.

The phase multiples matter: `X₁ · (Y₁ Z₂) = i·Z₁Z₂` with `Z₁Z₂ ∈ S` shows the located-error
products genuinely enter `N(S) − S`, so Theorem 10.8's (`AxQM/NC/Ch10/Theorem10_8.lean`) restricted
`∉ N(S) − S` condition does not
apply — the general KL conditions with a *complex*-Hermitian `α` are needed. Since these Pauli
errors span all operators on the `L` qubits, the discretization of errors (Theorem 10.2) upgrades
this to correcting an arbitrary noise operation confined to `L` — the effect N&C asks us to correct.

## The declarations

All in `AxQM/Concrete/StabilizerCodeDistance.lean`, namespace `AxQM.Concrete`:

* `PauliGroup.weight` — the **weight** of a Pauli-group element (the number of non-identity tensor
  factors, `|supp p.idx|`; N&C §10.5.5).
* `pauliStringSupport_pauliMulIndex_subset` — the support of a Pauli-string product lies in the
  union of the supports (`σ_I σ_I = σ_I`).
* `weight_inv_mul_le_of_support_subset` — the product of two errors each supported on `L` is again
  supported on `L`, so `weight (p⁻¹ q) ≤ |L|`.
* `stabilizerCodeDistance` — the **distance** of a stabilizer code `C(S)`, the minimum weight over
  the nontrivial logical operators (elements of `N(S)` that are not a phase multiple `iˢ·s'` of any
  stabilizer element — N&C's `N(S) − S` read modulo the global phase, `N(S) \ ⟨iI, S⟩`; in `ℕ∞`).
  An `[n, k, d]` code has `stabilizerCodeDistance S = d`.
* `stabilizerCodeDistance_le_weight` — every nontrivial logical operator has weight at least the
  distance; `one_le_stabilizerCodeDistance` — the distance is always `≥ 1` (weight-`0` phase
  elements like `-I` are excluded, so the hypotheses below are genuinely satisfiable).
* `codeProjector_conj_toMat_phaseStab` / `exists_codeProjector_conj_smul_of_weight_lt` — conjugation
  of `P` by a phase multiple of a stabilizer element gives `iˢ·P`; below the distance,
  `P (toMat p) P` is always *some* scalar multiple of `P`.
* `stabilizerTraceKLCoeff` / `stabilizerTraceKLCoeff_isHermitian`,
  `codeProjector_satisfiesKL_of_weight_lt` / `codeProjector_satisfiesKLConditions_of_weight_lt` —
  the trace-defined Hermitian KL coefficient matrix and the Knill–Laflamme conditions for a family
  whose pairwise products have weight below the distance.
* `codeProjector_isCorrectableErrorSet_of_weight_lt` — the core: a Pauli error family with
  `weight (Eⱼ⁻¹ Eₖ) < distance` for all `j, k` is correctable (also N&C's "distance `≥ 2t + 1`
  corrects `t` errors").
* `locatedPauliErrors_isCorrectableErrorSet` — **Exercise 10.45**: for a stabilizer `S` (`-I ∉ S`)
  and a known affected set `L` with `|L| < stabilizerCodeDistance S`, the family of all
  `L`-supported Pauli errors is a correctable set of errors for `C(S)` (a trace-preserving recovery
  corrects them).
* `locatedPauliErrors_isCorrectableErrorSet_of_dist_ge` — the literal `[n, k, d]` reading: distance
  at least `d` and fewer than `d` affected qubits (`|L| < d`, i.e. at most `d − 1`) suffice.
-/
