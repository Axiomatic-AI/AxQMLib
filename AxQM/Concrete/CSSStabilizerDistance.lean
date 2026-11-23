/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CSSStabilizerNormalizer

/-!
# Concrete: the distance and `t`-qubit correction of the CSS code `CSS(C₁, C₂)`

This file completes the error-correction
half of **Nielsen & Chuang, Exercise 10.51** — *the check matrix (10.106) is the stabilizer of the
CSS code `CSS(C₁, C₂)`, and Theorem 10.8 gives `t`-qubit correction* (p. 470). The earlier files
build the stabilizer group `cssStabilizer C₁ C₂` (from the check-matrix rows), its element normal
form `X^v Z^u`, its genuineness `-I ∉ S`, and the normalizer geometry
(`checkRow_mem_of_mem_normalizer`: a logical operator has `X`-part in `C₁` and `Z`-part in `C₂⊥`).
This file turns that geometry into the **code distance** and then feeds it, through Theorem 10.8's
weight-based correctability core, into the exercise's conclusion.

## The distance bound (`min_minDist_le_stabilizerCodeDistance_cssStabilizer`)

N&C's assumption is that the classical codes `C₁` and `C₂⊥` both correct `t` errors — i.e. each has
minimum distance `≥ 2t + 1`. We show the CSS **quantum** code inherits this:
`stabilizerCodeDistance (cssStabilizer C₁ C₂) ≥ min(d(C₁), d(C₂⊥))`.

Let `p` be a *nontrivial* logical operator: `p ∈ N(S)` and `p` is not a phase multiple of any
stabilizer element (`∀ s' ∈ S, p.idx ≠ s'.idx`). By the normalizer geometry its `X`-part
`a = (checkRow p.idx).₁` lies in `C₁` and its `Z`-part `b = (checkRow p.idx).₂` in `C₂⊥`. The key
step is that `p` cannot have **both** `a ∈ C₂` and `b ∈ C₁⊥`: if it did, `X^a Z^b ∈ S`
(`mem_cssStabilizer_iff`) and its check row is exactly `(a, b) = checkRow p.idx`
(`checkRow_xPauli_mul_zPauli`), so `p.idx = (X^a Z^b).idx` by the faithfulness of the check row
(`checkRow_injective`) — contradicting nontriviality. Hence `a ∉ C₂` (so `a` is a nonzero codeword
of `C₁`, weight `≥ d(C₁)`) or `b ∉ C₁⊥` (so `b` is a nonzero codeword of `C₂⊥`, weight `≥ d(C₂⊥)`);
the weight bridge `hammingNorm_checkRow_..._le_weight` lifts either bound to `weight p`. This is the
CSS reading of the general fact that a stabilizer code's distance is the minimum weight of a
nontrivial logical operator: here that minimum is a classical minimum-distance computation.

## `t`-qubit correction (`cssStabilizer_isCorrectableErrorSet_of_correctsErrors`)

With `d(C₁), d(C₂⊥) ≥ 2t + 1` the distance bound gives
`stabilizerCodeDistance (cssStabilizer C₁ C₂) ≥ 2t + 1`. Theorem 10.8's weight-based core
(`codeProjector_isCorrectableErrorSet_of_weight_lt`) then makes the **whole family of Pauli errors
of weight `≤ t`** a correctable set: for two such errors `Eⱼ, Eₖ`, the product `Eⱼ⁻¹ Eₖ` has weight
`≤ weight Eⱼ + weight Eₖ ≤ 2t < 2t + 1 ≤ distance` (`weight_inv_mul_le`), so the correctability
hypothesis holds. This is exactly N&C's "arbitrary errors on up to `t` qubits may be corrected by
this code" (the Pauli basis of weight `≤ t` errors; discretization upgrades it to arbitrary
`t`-qubit noise).

The remaining
part of Exercise 10.51 (that the code *space* is exactly `CSS(C₁, C₂)`, of dimension `2^{k₁-k₂}`)
is not treated here.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The check row of a CSS normal-form element -/

/-- **The check row of `X^a Z^b` is `(a, b)`.** The product string `X^a ⊙ Z^b` has, at each qubit,
`x`-bit `aₖ` and `z`-bit `bₖ`, so its check row is `(a, b)`: additivity of the check row
(`checkRow_pauliMulIndex`) over `checkRow (X^a) = (a, 0)` and `checkRow (Z^b) = (0, b)`. This is
what identifies a stabilizer element `X^a Z^b ∈ S` with its `(a, b)` data, the bridge used (via
`checkRow_injective`) to detect when a normalizer element is a phase multiple of a stabilizer
element. -/
theorem checkRow_xPauli_mul_zPauli (a b : Fin n → ZMod 2) :
    checkRow (xPauli a * zPauli b).idx = (a, b) := by
  rw [PauliGroup.mul_idx, xPauli_idx, zPauli_idx, checkRow_pauliMulIndex, checkRow_xString,
    checkRow_zString]
  simp

/-! ### The CSS code distance bound -/

/-- **The CSS quantum code distance is at least `min(d(C₁), d(C₂⊥))`** (Nielsen & Chuang,
Exercise 10.51). For classical binary codes `C₂ ≤ C₁`,
`min C₁.minDist C₂.dual.minDist ≤ stabilizerCodeDistance (cssStabilizer C₁ C₂)`.

A nontrivial logical operator `p` (`p ∈ N(S)`, not a phase multiple of any stabilizer element) has,
by the normalizer geometry, `X`-part `(checkRow p.idx).₁ ∈ C₁` and `Z`-part `(checkRow p.idx).₂ ∈
C₂⊥`. It cannot have both `X`-part in `C₂` and `Z`-part in `C₁⊥`: then `X^{x} Z^{z} ∈ S` has the
same check row as `p` (`checkRow_xPauli_mul_zPauli`), forcing `p.idx = (X^{x} Z^{z}).idx`
(`checkRow_injective`) against nontriviality. So one of the two parts is a **nonzero** codeword of
`C₁` (resp. `C₂⊥`), with Hamming weight at least that code's minimum distance
(`LinearCode.minDist_le_hammingNorm`), which the weight bridge
(`hammingNorm_checkRow_..._le_weight`) bounds by `weight p`. -/
theorem min_minDist_le_stabilizerCodeDistance_cssStabilizer
    {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁) :
    min C₁.minDist C₂.dual.minDist ≤ stabilizerCodeDistance (cssStabilizer C₁ C₂) := by
  rw [stabilizerCodeDistance, le_iInf₂_iff]
  rintro p ⟨hpN, hpid⟩
  obtain ⟨ha, hb⟩ := checkRow_mem_of_mem_normalizer hsub hpN
  have hnt : (checkRow p.idx).1 ∉ C₂ ∨ (checkRow p.idx).2 ∉ C₁.dual := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨ha2, hb1⟩ := hcon
    refine hpid (xPauli (checkRow p.idx).1 * zPauli (checkRow p.idx).2)
      ((mem_cssStabilizer_iff hsub).mpr ⟨_, ha2, _, hb1, rfl⟩) ?_
    exact checkRow_injective (by rw [checkRow_xPauli_mul_zPauli])
  rcases hnt with ha2 | hb1
  · have ha0 : (checkRow p.idx).1 ≠ 0 := fun h => ha2 (by rw [h]; exact C₂.zero_mem)
    exact (min_le_left _ _).trans ((LinearCode.minDist_le_hammingNorm ha ha0).trans
      (by exact_mod_cast hammingNorm_checkRow_fst_le_weight p))
  · have hb0 : (checkRow p.idx).2 ≠ 0 := fun h => hb1 (by rw [h]; exact C₁.dual.zero_mem)
    exact (min_le_right _ _).trans ((LinearCode.minDist_le_hammingNorm hb hb0).trans
      (by exact_mod_cast hammingNorm_checkRow_snd_le_weight p))

/-- **CSS(C₁, C₂) has distance at least `2t + 1` when `C₁` and `C₂⊥` both correct `t` errors**
(Nielsen & Chuang, Exercise 10.51). This packages the distance bound in the form Theorem 10.8's
correction needs: since `C₁.CorrectsErrors t` and `C₂.dual.CorrectsErrors t` both mean
`2t + 1 ≤ minDist`, their minimum — and hence the quantum code distance — is at least `2t + 1`. -/
theorem stabilizerCodeDistance_cssStabilizer_ge_of_correctsErrors
    {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁) {t : ℕ}
    (h1 : C₁.CorrectsErrors t) (h2 : C₂.dual.CorrectsErrors t) :
    (↑(2 * t + 1) : ℕ∞) ≤ stabilizerCodeDistance (cssStabilizer C₁ C₂) :=
  (le_min h1 h2).trans (min_minDist_le_stabilizerCodeDistance_cssStabilizer hsub)

/-! ### `t`-qubit correction (Nielsen & Chuang, Theorem 10.8) -/

/-- The CSS stabilizer is finite (a subgroup of the finite Pauli group `Gₙ`), as Theorem 10.8's code
projector and correction require. -/
noncomputable instance {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} :
    Fintype ↥(cssStabilizer C₁ C₂) := Fintype.ofFinite _

/-- **CSS(C₁, C₂) corrects arbitrary errors on up to `t` qubits** (Nielsen & Chuang,
Exercise 10.51). For classical binary codes `C₂ ≤ C₁` with `C₁` and `C₂⊥` both correcting `t`
errors, the family of **all Pauli errors of weight `≤ t`** is a correctable set of errors for the
CSS code `C(cssStabilizer C₁ C₂)`: there is a trace-preserving recovery `R` (`∑ₒ Rₒ† Rₒ = 1`) that
corrects every such error.

This is the second half of the exercise, via Theorem 10.8. The distance bound
(`stabilizerCodeDistance_cssStabilizer_ge_of_correctsErrors`) gives
`stabilizerCodeDistance S ≥ 2t + 1`, and any two weight-`≤ t` errors `Eⱼ, Eₖ` have
`weight (Eⱼ⁻¹ Eₖ) ≤ weight Eⱼ + weight Eₖ ≤ 2t < 2t + 1 ≤ distance` (`weight_inv_mul_le`), so the
weight-based correctability core `codeProjector_isCorrectableErrorSet_of_weight_lt` applies.
(By discretization of errors this Pauli basis suffices for an arbitrary noise operation supported on
any `t` qubits.) -/
theorem cssStabilizer_isCorrectableErrorSet_of_correctsErrors
    {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁) {t : ℕ}
    (h1 : C₁.CorrectsErrors t) (h2 : C₂.dual.CorrectsErrors t) :
    ∃ (κ : Type) (_ : Fintype κ)
      (R : κ → EuclideanSpace ℂ (Fin n → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin n → Fin 2)),
      (∑ o, (ContinuousLinearMap.adjoint (R o)).comp (R o) = 1) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2)
          (codeProjector (cssStabilizer C₁ C₂))).Corrects
        (fun i : {p : PauliGroup n // p.weight ≤ t} =>
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (i.val).toMat) R := by
  refine codeProjector_isCorrectableErrorSet_of_weight_lt (negOne_notMem_cssStabilizer hsub)
    (Subtype.val : {p : PauliGroup n // p.weight ≤ t} → PauliGroup n) ?_
  intro i j
  have hle : ((i.val)⁻¹ * j.val).weight ≤ 2 * t := by
    refine (weight_inv_mul_le _ _).trans ?_
    rw [two_mul]; exact Nat.add_le_add i.2 j.2
  calc (((i.val)⁻¹ * j.val).weight : ℕ∞)
      ≤ ((2 * t : ℕ) : ℕ∞) := by exact_mod_cast hle
    _ < (↑(2 * t + 1) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self (2 * t)
    _ ≤ stabilizerCodeDistance (cssStabilizer C₁ C₂) :=
        stabilizerCodeDistance_cssStabilizer_ge_of_correctsErrors hsub h1 h2

end AxQM.Concrete
