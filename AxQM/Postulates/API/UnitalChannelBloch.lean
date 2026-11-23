/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RandomUnitaryChannel
import AxQM.Postulates.API.BlochState
import AxQM.Concrete.BlochChannelMatrix
import AxQM.Concrete.BlochChannelCP
import ToMathlib.Analysis.InnerProductSpace.OperatorSumTheorem
import ToMathlib.Analysis.InnerProductSpace.OperatorSumMatrix

/-!
# The Bloch matrix of a unital qubit channel

The qubit converse of Nielsen & Chuang, Problem 8.3: a **unital qubit channel** acts on the Bloch
ball by a real-linear map `r ↦ M r`. This is the first step of the converse "every unital qubit
channel is random-unitary": it produces the real `3 × 3` **Bloch matrix** `M`, whose
singular-value / polar decomposition is used in the rest of the argument.

* `AxQM.exists_channelBlochMatrix_op` — for a channel `f` (`IsChannel`) that is unital
  (`IsUnital`, i.e. `f (I/2) = I/2`), there is a real `3 × 3` matrix `M` with
  `(f (blochState r)).op = ½(I + (M r)·σ)`: the density operator of the image Bloch state has Bloch
  vector `M r`.
* `AxQM.exists_channelBlochMatrix` — the state-level form: `f (blochState r) = blochState
  (M r)`, the Bloch vector transforming linearly `r ↦ M r` (the affine map has no translation
  because `f` is unital). The image Bloch vector `M r` again lies in the closed unit ball, forced by
  positivity of the output density operator.

## Proof route

`IsChannel f` bundles a completely-positive, trace-preserving superoperator `Φ` with `(f ρ).op =
Φ ρ.op`. Complete positivity + trace preservation give the quantum-operation axioms, so the
operator-sum representation theorem (N&C Theorem 8.1,
`ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum`) yields a Kraus family `Φ =
krausSumₗ E`. Transporting the operators `Eₖ` to matrices `Aₖ = toEuclideanCLM⁻¹ Eₖ` across the
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM` turns `Φ` into the matrix operator sum
`B ↦ ∑ₖ Aₖ B Aₖ†`. Unitality forces `∑ₖ Aₖ Aₖ† = I` (the identity term is fixed) and trace
preservation forces each Pauli image `∑ₖ Aₖ σⱼ Aₖ†` traceless; the concrete matrix identity
`Concrete.sum_conj_blochMatrix` then reads off the Bloch matrix `M = Concrete.krausBlochMatrix A`.

The statement of Problem 8.3 is in `AxQM/NC/Ch8/Problem8_3.lean`.
-/

open scoped InnerProductSpace Matrix

noncomputable section

namespace AxQM

/-- **The Bloch matrix of a unital qubit channel, with the complete-positivity criterion (operator
form).** A quantum channel `f` (`IsChannel`, a CPTP map) that is **unital** (`IsUnital`,
`f (I/2) = I/2`) acts on the Bloch state `blochState r = ½(I + r·σ)` by a real-linear transformation
of the Bloch vector — there is a real `3 × 3` matrix `M` with
`(f (blochState r)).op = Matrix.toEuclideanCLM (½(I + (M r)·σ))` — and, moreover, the four
**inverse-Pauli-transfer weights of `M`'s diagonal are nonnegative**:
`0 ≤ Concrete.pauliTwirlInvProb (fun j ↦ M j j) m`.

This packages the two ingredients of the qubit converse of Nielsen & Chuang, Problem 8.3 that both
flow from the *same* operator-sum (Kraus) family: the Bloch-affine-map representation (via the
concrete matrix identity `Concrete.sum_conj_blochMatrix`), and the **complete-positivity /
Fujiwara–Algoet criterion** (`Concrete.pauliTwirlInvProb_krausBlochMatrix_diag_nonneg`, the
Choi-free sum-of-squares matrix core). Both are read off `M = Concrete.krausBlochMatrix A`
for the *one* family `A = toEuclideanCLM⁻¹ ∘ E` obtained from the operator-sum representation
theorem (N&C Theorem 8.1); unitality forces `∑ₖ Aₖ Aₖ† = I` (removing the affine translation,
`M · 0 = 0`) and trace preservation forces each Pauli image `∑ₖ Aₖ σⱼ Aₖ†` traceless — exactly the
two hypotheses the matrix core consumes. The nonnegativity is what the diagonal case of the converse
(`isRandomUnitary_of_blochState_eq_diagonalScaling`) needs: after diagonalising `M` it certifies
that the singular-value diagonal is a genuine Pauli-transfer vector. -/
theorem exists_channelBlochMatrix_diag_nonneg {f : State qubit → State qubit}
    (hCh : IsChannel f) (hU : IsUnital f) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1),
        (f (blochState r h)).op
          = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix (M *ᵥ r)))
      ∧ ∀ m : Fin 4, 0 ≤ Concrete.pauliTwirlInvProb (fun j => M j j) m := by
  obtain ⟨Φ, hCP, hTP, hres⟩ := hCh
  -- The channel satisfies the quantum-operation axioms (CP + trace-non-increasing).
  have hSOA : ContinuousLinearMap.SatisfiesOperationAxioms Φ :=
    ⟨hCP, fun ρ _ => le_of_eq (congrArg RCLike.re (hTP ρ))⟩
  -- ... hence has a Kraus representation `Φ = krausSumₗ E` (N&C Theorem 8.1).
  obtain ⟨ι, hFin, E, hE, -⟩ :=
    (ContinuousLinearMap.satisfiesOperationAxioms_iff_isOperatorSum Φ).1 hSOA
  let := hFin
  -- Transport the Kraus operators to matrices across `toEuclideanCLM`.
  set A : ι → Matrix (Fin 2) (Fin 2) ℂ :=
    fun k => (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).symm (E k) with hA
  have hEA : ∀ k, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (A k) = E k := by
    intro k; rw [hA]; exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).apply_symm_apply (E k)
  -- `Φ (toEuclideanCLM B) = toEuclideanCLM (∑ₖ Aₖ B Aₖ†)`: the reusable matrix↔operator Kraus
  -- bridge `ContinuousLinearMap.krausSumₗ_toEuclideanCLM`, at the family `Eₖ = toEuclideanCLM Aₖ`.
  have key : ∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      Φ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) B)
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (∑ k, A k * B * (A k)ᴴ) := fun B => by
    rw [hE, show E = fun k => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (A k)
        from funext fun k => (hEA k).symm]
    exact ContinuousLinearMap.krausSumₗ_toEuclideanCLM A B
  -- Unitality: `f (I/2) = I/2` forces `Φ 1 = 1`, hence `∑ₖ Aₖ Aₖ† = I`.
  have hd : ((Module.finrank ℂ qubit.space : ℂ))⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero, Nat.cast_eq_zero]
    exact Module.finrank_pos.ne'
  have hU2 : f (maximallyMixedState qubit) = maximallyMixedState qubit := hU
  have hone : Φ (1 : qubit.space →L[ℂ] qubit.space) = 1 := by
    have hmm : Φ ((maximallyMixedState qubit).op) = (maximallyMixedState qubit).op := by
      rw [← hres, hU2]
    rw [maximallyMixedState_op qubit, map_smul] at hmm
    exact smul_right_injective _ hd hmm
  have hU' : ∑ k, A k * (A k)ᴴ = 1 := by
    have hk := key 1
    rw [map_one] at hk
    simp only [mul_one] at hk
    -- `hk : Φ 1 = toEuclideanCLM (∑ₖ Aₖ Aₖ†)`; `hone : Φ 1 = 1` (defeq `1`, bridged by `Eq.trans`).
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (∑ k, A k * (A k)ᴴ) = 1 :=
      hk.symm.trans hone
    exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective (h1.trans (map_one _).symm)
  -- Trace preservation: each Pauli image `∑ₖ Aₖ σⱼ Aₖ†` is traceless. `Eq.trans` bridges the
  -- `qubit.space`-vs-`EuclideanSpace` trace (defeq) between `hTP` and `trace_toEuclideanCLM`.
  have htl : ∀ j, (∑ k, A k * Concrete.pauliDot (Pi.single j 1) * (A k)ᴴ).trace = 0 := by
    intro j
    have e := hTP (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot (Pi.single j 1)))
    rw [key] at e
    have step : (∑ k, A k * Concrete.pauliDot (Pi.single j 1) * (A k)ᴴ).trace
        = (Concrete.pauliDot (Pi.single j 1)).trace :=
      (Matrix.trace_toEuclideanCLM _).symm.trans (e.trans (Matrix.trace_toEuclideanCLM _))
    rw [step, Concrete.pauliDot_trace]
  refine ⟨Concrete.krausBlochMatrix A, fun r h => ?_, fun m => ?_⟩
  · rw [hres, blochState_op, key, Concrete.sum_conj_blochMatrix A hU' htl]
  · exact Concrete.pauliTwirlInvProb_krausBlochMatrix_diag_nonneg A hU' htl m

/-- **The Bloch matrix of a unital qubit channel (operator form).** A quantum channel `f`
(`IsChannel`, a CPTP map) that is **unital** (`IsUnital`, `f (I/2) = I/2`) acts on the Bloch state
`blochState r = ½(I + r·σ)` by a real-linear transformation of the Bloch vector: there is a real
`3 × 3` matrix `M` with `(f (blochState r)).op = Matrix.toEuclideanCLM (½(I + (M r)·σ))`, i.e. the
image density operator is the Bloch matrix of `M r`.

This is the **Bloch-affine-map representation of a unital qubit channel** — the entry point of the
qubit converse of Nielsen & Chuang, Problem 8.3. `M` is obtained from an operator-sum (Kraus)
representation of `f` (N&C Theorem 8.1) via the concrete matrix identity
`Concrete.sum_conj_blochMatrix`. Unitality removes the affine translation (`M · 0 = 0`), so a
*unital* channel is purely linear on the Bloch ball. The projection of
`exists_channelBlochMatrix_diag_nonneg` that keeps only this Bloch-map half. -/
theorem exists_channelBlochMatrix_op {f : State qubit → State qubit}
    (hCh : IsChannel f) (hU : IsUnital f) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℝ, ∀ (r : Fin 3 → ℝ)
      (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1),
      (f (blochState r h)).op
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix (M *ᵥ r)) :=
  (exists_channelBlochMatrix_diag_nonneg hCh hU).imp fun _ h => h.1

/-- **The Bloch matrix of a unital qubit channel (state form).** A unital quantum channel `f` sends
the Bloch state `blochState r` to the Bloch state `blochState (M r)`: the Bloch vector transforms
by the real-linear map `r ↦ M r` (Nielsen & Chuang, Problem 8.3, dim-2 direction). The image Bloch
vector `M r` again lies in the closed unit ball — forced by positivity of the output density
operator `f (blochState r)`. This is the affine-map representation with *no* translation (unital
⟹ the ball centre `r = 0` is fixed). -/
theorem exists_channelBlochMatrix {f : State qubit → State qubit}
    (hCh : IsChannel f) (hU : IsUnital f) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℝ, ∀ (r : Fin 3 → ℝ)
      (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1),
      ∃ h' : (M *ᵥ r) 0 ^ 2 + (M *ᵥ r) 1 ^ 2 + (M *ᵥ r) 2 ^ 2 ≤ 1,
        f (blochState r h) = blochState (M *ᵥ r) h' := by
  obtain ⟨M, hop⟩ := exists_channelBlochMatrix_op hCh hU
  refine ⟨M, fun r h => ?_⟩
  have hpos : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
      (Concrete.blochMatrix (M *ᵥ r))).IsPositive := by
    rw [← hop r h]; exact (f (blochState r h)).isDensity.isPositive
  have hball := (Concrete.blochMatrix_posSemidef_iff _).1
    ((Matrix.isPositive_toEuclideanCLM_iff _).1 hpos)
  refine ⟨hball, ?_⟩
  apply State.ext
  rw [hop r h, blochState_op]

/-- **Complete-positivity criterion for a diagonally-acting unital qubit channel (Problem 8.3).**
If a unital quantum channel `f` acts on Bloch states by a *diagonal* contraction of the Bloch
vector — `(f (blochState r)).op = ½(I + (d ⊙ r)·σ)` with `d ⊙ r = (d₀ r₀, d₁ r₁, d₂ r₂)` — then the
coefficient triple `d` satisfies the Fujiwara–Algoet inequalities
`0 ≤ Concrete.pauliTwirlInvProb d`.
This is the physics form of the complete-positivity criterion of the qubit converse of Nielsen &
Chuang, Problem 8.3: complete positivity of `f` forces its diagonal Bloch action to be a genuine
Pauli-transfer vector — hence realisable as a Pauli (random-unitary) channel.

The remaining step of the converse feeds this the singular-value diagonal `d` of a unital channel's
Bloch matrix (`M = O₁ · diagonal d · O₂`): conjugating the channel by the rotations `O₁, O₂` yields
a unital channel with diagonal Bloch action `d`, and this lemma then certifies
`pauliTwirlInvProb d ≥ 0`, the hypothesis of `isRandomUnitary_of_blochState_eq_diagonalScaling`.

Obtained from `exists_channelBlochMatrix_diag_nonneg`: the channel's own Bloch matrix `M` equals
`Matrix.diagonal d` because it agrees with `d ⊙ ·` on the Bloch basis vectors
(`Concrete.blochMatrix_injective` through the injective `Matrix.toEuclideanCLM`), so `M j j = d j`
and the packaged nonnegativity `0 ≤ pauliTwirlInvProb (fun j ↦ M j j)` is exactly the claim. -/
theorem pauliTwirlInvProb_nonneg_of_channel_blochDiagonal {f : State qubit → State qubit}
    (hCh : IsChannel f) (hU : IsUnital f) (d : Fin 3 → ℝ)
    (hf : ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1),
        (f (blochState r h)).op
          = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
              (Concrete.blochMatrix ![d 0 * r 0, d 1 * r 1, d 2 * r 2]))
    (m : Fin 4) :
    0 ≤ Concrete.pauliTwirlInvProb d m := by
  obtain ⟨M, hM, hnn⟩ := exists_channelBlochMatrix_diag_nonneg hCh hU
  -- The channel's Bloch matrix `M` acts as the diagonal contraction on the whole ball.
  have hMr : ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1),
      M *ᵥ r = ![d 0 * r 0, d 1 * r 1, d 2 * r 2] := fun r h =>
    Concrete.blochMatrix_injective
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective ((hM r h).symm.trans (hf r h)))
  -- Read off `M j j = d j` from the Bloch basis vectors `e₀, e₁, e₂`.
  have hMd : (fun j => M j j) = d := by
    funext j
    fin_cases j
    · have e := congrFun (hMr ![1, 0, 0] (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])) 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using e
    · have e := congrFun (hMr ![0, 1, 0] (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])) 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using e
    · have e := congrFun (hMr ![0, 0, 1] (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])) 2
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using e
  rw [← hMd]; exact hnn m

end AxQM
