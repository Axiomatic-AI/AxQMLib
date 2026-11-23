/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.FiveQubitCode

/-!
# Nielsen & Chuang, Exercise 10.49 — the five-qubit code corrects an arbitrary single-qubit error

Use Theorem 10.8 to verify the five qubit code protects against an arbitrary single-qubit error.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.5.6 (p. 469).

## What the exercise asks, and how it is verified

The **five-qubit code** `[[5,1,3]]` (N&C §10.5.6, Fig 10.12) is the smallest code protecting a
single logical qubit against an arbitrary single-qubit error. Its stabilizer `S = ⟨g₁, g₂, g₃, g₄⟩`
has the four Figure-10.12 generators `g₁ = XZZXI`, `g₂ = IXZZX`, `g₃ = XIXZZ`, `g₄ = ZXIXZ` (cyclic
right-shift of the one before). Following N&C, the verification applies **Theorem 10.8**
(`AxQM/NC/Ch10/Theorem10_8.lean`; error-correction conditions for stabilizer codes,
`Concrete.codeProjector_isCorrectableErrorSet`):
the error set `{Eⱼ} = {I} ∪ {Xᵢ, Yᵢ, Zᵢ}` is a *correctable set of errors* provided
`Eⱼ† Eₖ ∉ N(S) − S` for all `j, k`. For `j = k` the product is `I ∈ S`; for `j ≠ k` it is a weight
`≤ 2` Pauli that anticommutes with one of the four generators — so it lies outside `N(S)` (the
five-qubit code has distance `3`: no nonidentity weight `≤ 2` Pauli commutes with the whole
stabilizer). Since `-I ∉ S`, Theorem 10.8 then produces a trace-preserving recovery operation
correcting the whole single-qubit error set — the code "protects against an arbitrary single qubit
error" (an arbitrary single-qubit operation is corrected by the discretization Theorem 10.2 once its
Pauli-basis errors are).

## The declarations

The item-specific declarations are all in `AxQM/Concrete/FiveQubitCode.lean`; it uses two general
Pauli-group facts: `PauliGroup.mul_ne_mul_of_odd_anticommCount` (odd symplectic pairing ⟹ group
elements don't commute) in `AxQM/Concrete/PauliGroup.lean`, beside `toMat_anticomm_of_ne_mul_comm`;
and `notMem_normalizer_of_mem_of_ne_comm` (anticommuting with an element of `S` puts you outside
`N(S) = Z(S)`) in `AxQM/Concrete/PauliSubgroupNormalizer.lean`, beside the `N(S) = Z(S)` lemma it
wraps.

* `AxQM.Concrete.fiveQubitGen` / `fiveQubitGenIdx` — the four Figure-10.12 generators as
  elements of `G₅` (resp. their Pauli-string index vectors), and `fiveQubitStab := ⟨g₁,…,g₄⟩` the
  stabilizer subgroup.
* `AxQM.Concrete.fiveQubitGen_commute` — the generators pairwise commute (Exercise 10.33
  symplectic criterion); `fiveQubitGen_checkRow_linearIndependent` — their check rows are
  `ZMod 2`-linearly independent (Proposition 10.3: the generators are independent).
* `AxQM.Concrete.negOne_notMem_fiveQubitStab` — **`-I ∉ S`**, so `S` is a genuine
  stabilizer. Since `-I` is a Pauli commutator (killed by every abelian quotient), this goes through
  the faithful representation. Proposition 10.5 (`stabilizedSubspace_finrank`) gives
  `dim V_S = 2 ≠ 0` (a nonzero code space), and the generic criterion
  `Concrete.negOne_notMem_closure_of_ne_bot` (in `Concrete/StabilizerErrorCorrection.lean`, beside
  its reverse companion `codeProjector_ne_zero`) concludes: a nonzero common `+1`-eigenvector `v`
  gives a subgroup `{p | toMat p ·ᵥ v = v} ⊇ S`, while `toMat (-I) ·ᵥ v = -v ≠ v`.
* `AxQM.Concrete.fiveQubitError` — the error set `{I} ∪ {single-qubit Paulis}`, and
  `fiveQubitError_notMem_normalizer_diff` — its Theorem-10.8 hypothesis `Eⱼ⁻¹ Eₖ ∉ N(S) \ S`, via
  the two helpers above (`j = k` gives `1 ∈ S`; `j ≠ k` gives a weight-`≤ 2` product
  anticommuting with a generator, hence outside `N(S)`).
* `AxQM.Concrete.fiveQubitCode_isCorrectableErrorSet` — **Exercise 10.49**: feeding
  `-I ∉ S` and the error condition into Theorem 10.8 yields a trace-preserving recovery `R`
  (`∑ₒ Rₒ† Rₒ = 1`) correcting the single-qubit error set on the code space `C(S)`.
-/
