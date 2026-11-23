/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BlochState
import AxQM.Postulates.API.PauliEigen
import AxQM.Postulates.API.EntropySpectral
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# AxQM.Postulates.API — the von Neumann entropy of a qubit Bloch state

The von Neumann entropy of a single-qubit **Bloch state** `ρ = ½(I + r⃗·σ⃗)` is the binary
Shannon entropy of its two eigenvalues `(1 ± ‖r⃗‖)/2` (Nielsen & Chuang §11.3, eqs.
(11.39)–(11.40)):

`S(blochState r) = H((1 + ‖r⃗‖)/2, (1 − ‖r⃗‖)/2)`,   where `‖r⃗‖ = √(r₀² + r₁² + r₂²)`.

This is the reusable engine behind the "example calculations of entropy" of Exercise 11.11
(three explicit `2 × 2` density matrices) and the comparison Exercise 11.12; both present states
that are qubit Bloch states.

## Main result

* `AxQM.blochState_vonNeumannEntropy` — for a Bloch vector `r` in the closed unit ball
  with `0 < ‖r⃗‖²`, `S(blochState r) = H((1 ± ‖r⃗‖)/2)`.

## Design notes

* **Why `0 < ‖r⃗‖²`.** For the zero Bloch vector `blochState 0 = I/2` is the maximally mixed
  state, whose entropy is `log 2 = log d` and is already given by
  `State.vonNeumannEntropy_maximallyMixed`; the formula `H((1 ± 0)/2) = H(½, ½) = log 2` agrees
  there, but the eigenbasis below degenerates (both eigenvalues coincide, so no canonical
  `±`-split), so we restrict to `‖r⃗‖ > 0`.
* **The eigenbasis, without surds.** Instead of writing out explicit (surd-laden) eigenvectors, we
  reuse the Pauli-eigenprojector infrastructure of `AxQM/Postulates/API/PauliEigen.lean`. Writing
  `n̂ = ‖r⃗‖⁻¹ r⃗` for the unit direction, `pauliObservable n̂ = n̂·σ` is a self-adjoint involution
  (`(n̂·σ)² = 1`, `pauliObservable_op_mul_self`), so its `±1` eigenprojectors are nonzero and
  supply unit eigenstates `ψ₊, ψ₋` (`pauliObservable_proj{Plus,Minus}_ne_zero` +
  `Observable.exists_hasEigenstate_{one,neg_one}…`). Self-adjointness with distinct eigenvalues
  makes them orthogonal, hence an orthonormal basis (`basisOfOrthonormalOfCardEqFinrank`,
  `finrank qubit.space = 2`). Since `(blochState r).op = ½(1 + r⃗·σ)` and `r⃗·σ = ‖r⃗‖ • (n̂·σ)`,
  the same `ψ₊, ψ₋` diagonalize the density operator with eigenvalues `(1 ± ‖r⃗‖)/2`, and
  `State.vonNeumannEntropy_eq_entropy_of_isEigenbasis` reads off the Shannon entropy.
* The statement involves only `blochState`, `State.vonNeumannEntropy` and `Real.entropy`, and is
  applied directly in the exercises of `AxQM/NC/`.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

open ContinuousLinearMap Matrix

/-- **The von Neumann entropy of a qubit Bloch state** `ρ = ½(I + r⃗·σ⃗)` is the binary Shannon
entropy of its eigenvalues `(1 ± ‖r⃗‖)/2` (Nielsen & Chuang §11.3, eq. (11.40)):
`S(blochState r) = H((1 + ‖r⃗‖)/2, (1 − ‖r⃗‖)/2)`, where `‖r⃗‖ = √(r₀² + r₁² + r₂²)`.

Requires `0 < ‖r⃗‖²` (the strictly mixed / pure sphere-and-interior case); the zero Bloch vector
is the maximally mixed state handled by `State.vonNeumannEntropy_maximallyMixed`. -/
theorem blochState_vonNeumannEntropy (r : Fin 3 → ℝ)
    (hle : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1)
    (hpos : 0 < r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2) :
    (blochState r hle).vonNeumannEntropy =
      Real.entropy ![(1 + Real.sqrt (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)) / 2,
                     (1 - Real.sqrt (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)) / 2] := by
  set Sq := r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 with hSq
  set ρ := Real.sqrt Sq with hρdef
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr hpos
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hρsq : ρ ^ 2 = Sq := Real.sq_sqrt hpos.le
  -- The unit Bloch direction `n̂ = ρ⁻¹ r⃗`.
  set n := (ρ⁻¹ : ℝ) • r with hn
  have hrn : r = (ρ : ℝ) • n := by
    rw [hn, smul_smul, mul_inv_cancel₀ hρne, one_smul]
  have hnunit : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    have hexp : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = ρ⁻¹ ^ 2 * Sq := by
      simp only [hn, Pi.smul_apply, smul_eq_mul, mul_pow, hSq]; ring
    rw [hexp, ← hρsq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hρne)]
  -- `A = n̂·σ` is a self-adjoint involution.
  set A := pauliObservable n with hA
  have hinv : A.op * A.op = 1 := by rw [hA]; exact pauliObservable_op_mul_self hnunit
  -- The `±1` eigenstates of `A`.
  obtain ⟨ψp, hψp⟩ :=
    A.exists_hasEigenstate_one_of_projPlus_ne_zero hinv (pauliObservable_projPlus_ne_zero n)
  obtain ⟨ψm, hψm⟩ :=
    A.exists_hasEigenstate_neg_one_of_projMinus_ne_zero hinv (pauliObservable_projMinus_ne_zero n)
  have hAp : A.op ψp.vec = ψp.vec := by
    have h : A.op ψp.vec = ((1 : ℝ) : ℂ) • ψp.vec := hψp
    simpa using h
  have hAm : A.op ψm.vec = -ψm.vec := by
    have h : A.op ψm.vec = ((-1 : ℝ) : ℂ) • ψm.vec := hψm
    simpa using h
  -- `ψ₊ ⟂ ψ₋` (distinct eigenvalues of a self-adjoint operator).
  have horth : inner ℂ ψp.vec ψm.vec = 0 := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp A.selfAdjoint
    have h1 : inner ℂ (A.op ψp.vec) ψm.vec = inner ℂ ψp.vec (A.op ψm.vec) := hsym ψp.vec ψm.vec
    rw [hAp, hAm, inner_neg_right] at h1
    linear_combination h1 / 2
  -- The orthonormal eigenbasis `![ψ₊, ψ₋]`.
  have hmp : inner ℂ ψm.vec ψp.vec = 0 := inner_eq_zero_symm.mpr horth
  have hon : Orthonormal ℂ ![ψp.vec, ψm.vec] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [horth, hmp, ψp.normalized, ψm.normalized]
  have hcard : Fintype.card (Fin 2) = Module.finrank ℂ qubit.space := by
    rw [finrank_qubit_space, Fintype.card_fin]
  set b : OrthonormalBasis (Fin 2) ℂ qubit.space :=
    (basisOfOrthonormalOfCardEqFinrank hon hcard).toOrthonormalBasis
      (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hon) with hbdef
  have hb : ∀ i, b i = ![ψp.vec, ψm.vec] i := by
    intro i
    rw [hbdef, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  -- `(blochState r).op = ½(1 + r⃗·σ)` and `r⃗·σ = ρ (n̂·σ)`, so `ψ±` are its eigenvectors.
  have hbop : (blochState r hle).op = (2⁻¹ : ℂ) • (1 + (pauliObservable r).op) := by
    rw [blochState_op, Concrete.blochMatrix, map_smul, map_add, map_one]; rfl
  have hpd : Concrete.pauliDot r = (ρ : ℂ) • Concrete.pauliDot n := by
    conv_lhs => rw [hrn]
    rw [Concrete.pauliDot_smul]
  have hscale : (pauliObservable r).op = (ρ : ℂ) • A.op := by
    rw [hA, pauliObservable_op, hpd, map_smul]; rfl
  have hev0 : (blochState r hle).op ψp.vec = (((1 + ρ) / 2 : ℝ) : ℂ) • ψp.vec := by
    rw [hbop, hscale]
    simp only [_root_.smul_apply, _root_.add_apply,
      one_apply_eq_self, hAp]
    push_cast
    module
  have hev1 : (blochState r hle).op ψm.vec = (((1 - ρ) / 2 : ℝ) : ℂ) • ψm.vec := by
    rw [hbop, hscale]
    simp only [_root_.smul_apply, _root_.add_apply,
      one_apply_eq_self, hAm]
    push_cast
    module
  -- Read off the Shannon entropy from the eigenbasis.
  refine State.vonNeumannEntropy_eq_entropy_of_isEigenbasis (blochState r hle) b
    (μ := ![(1 + ρ) / 2, (1 - ρ) / 2]) ?_
  intro i
  simp only [hb]
  fin_cases i
  · simpa using hev0
  · simpa using hev1

end AxQM
