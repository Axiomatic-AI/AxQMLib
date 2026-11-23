/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerErrorCorrection

/-!
# Nielsen & Chuang, Theorem 10.8 (Error-correction conditions for stabilizer codes)

Stabilizer QEC conditions: {Ej} with Ej-dag Ek not in N(S)-S for all j,k is a correctable error set
for C(S).
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 10.8 (p. 466).

Theorem 10.8 is, in N&C's words, "essentially just a translation of the quantum error-correction
conditions (Theorem 10.1) into the terms of stabilizer codes". Its proof shows that the projector
`P` onto the code space `C(S)` and the Pauli errors `{Eⱼ}` satisfy the **Knill–Laflamme conditions**
`P Eⱼ† Eₖ P = αⱼₖ P` (eq. (10.16)) with a Hermitian coefficient matrix `α`: for `Eⱼ† Eₖ ∈ S` the
projector absorbs it (`P Eⱼ† Eₖ P = P`); for `Eⱼ† Eₖ ∈ Gₙ − N(S)` it anticommutes with some element
of `S`, killing the sandwiched product (`P Eⱼ† Eₖ P = 0`); the excluded case is exactly
`Eⱼ† Eₖ ∈ N(S) − S`. Since `C(S)` is a genuine code (the stabilizer hypothesis `-I ∉ S` forces
`P ≠ 0`), Theorem 10.1's sufficiency (`corrects_of_satisfiesKLConditions`) then produces a
trace-preserving recovery correcting `{Eⱼ}`, so `{Eⱼ}` is a correctable error set.

## The formalisation

The stabilizer, its code projector, and the projector algebra, in
`AxQM/Concrete/StabilizerCodeProjector.lean`:

* `AxQM.Concrete.codeProjector` — the group-average projector
  `P_S = |S|⁻¹ ∑_{s∈S} toMat(s)` onto the code space `C(S)`, with
  `codeProjector_isHermitian`, `codeProjector_mul_self` (self-adjoint idempotent),
  `toMat_mul_codeProjector` / `codeProjector_mul_toMat` (absorption by `S`), and
  `codeProjector_mulVec_self_iff` (its range is exactly `C(S) = V_S`).

The error-correction conditions themselves, in
`AxQM/Concrete/StabilizerErrorCorrection.lean`:

* `AxQM.Concrete.stabilizerKLCoeff` / `stabilizerKLCoeff_isHermitian` — the Hermitian
  coefficient matrix `αⱼₖ = 1_S(Eⱼ⁻¹ Eₖ)` (N&C's `α` in eq. (10.16)).
* `AxQM.Concrete.codeProjector_satisfiesKL` — for Pauli errors `E : ι → Gₙ` with
  `Eⱼ⁻¹ Eₖ ∉ N(S) \ S`, the code projector satisfies the **Knill–Laflamme conditions**
  `P (toMat Eⱼ)ᴴ (toMat Eₖ) P = αⱼₖ • P` (eq. (10.16)); and `codeProjector_satisfiesKLConditions`
  restates this in the exact predicate `ContinuousLinearMap.SatisfiesKLConditions` of Theorem 10.1
  (via `toEuclideanCLM`). These hold for any finite stabilizer subgroup.
* `AxQM.Concrete.codeProjector_ne_zero` — for a genuine stabilizer (`-I ∉ S`) the code
  projector is nonzero (`tr P = |S|⁻¹ · 2ⁿ ≠ 0`); this is the remaining `P ≠ 0` hypothesis of
  Theorem 10.1, and where the stabilizer condition `-I ∉ S` enters.
* `AxQM.Concrete.codeProjector_isCorrectableErrorSet` — **Theorem 10.8**: for `-I ∉ S` and
  `Eⱼ⁻¹ Eₖ ∉ N(S) \ S`, there is a trace-preserving recovery `R` (`∑ₒ Rₒ† Rₒ = 1`) correcting
  `{Eⱼ}` on `C(S)`, i.e. `{Eⱼ}` is a **correctable set of errors** — obtained by feeding the KL
  conditions, Hermitian `α`, and `P ≠ 0` into Theorem 10.1's sufficiency
  (`ContinuousLinearMap.corrects_of_satisfiesKLConditions`).
-/
