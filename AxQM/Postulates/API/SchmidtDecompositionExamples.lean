/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtDecomposition
import AxQM.Postulates.API.BellState
import AxQM.Postulates.API.RelativePhase

/-!
# AxQM — explicit Schmidt decompositions of concrete two-qubit states (N&C Ex 2.79)

Nielsen & Chuang, Exercise 2.79 asks to **find** the Schmidt decompositions of three specific
two-qubit states. "Finding" a Schmidt decomposition means *exhibiting* it: the concrete Schmidt
coefficients `λᵢ` and orthonormal Schmidt bases `{|iᴬ⟩}`, `{|iᴮ⟩}` with
`|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`.

"Here is a valid Schmidt decomposition" is a single, reusable claim through the predicate
`PureState.IsSchmidtDecomposition ψ l a b` (defined beside the decomposition theorem in
`AxQM/Postulates/API/SchmidtDecomposition.lean`), whose fields are exactly the conclusion of
`PureState.exists_schmidt_decomposition` (N&C Theorem 2.7): the coefficients `l` are strictly
positive, the Schmidt bases `a`, `b` are orthonormal families, `∑ᵢ lᵢ² = 1`, and
`ψ.vec = ∑ᵢ (lᵢ : ℂ) • aᵢ ⊗ₜ bᵢ`. Theorem 2.7 then reads
`∃ n l a b, ψ.IsSchmidtDecomposition l a b` (`PureState.exists_isSchmidtDecomposition`).

This file covers the two states whose decomposition is *clean* (rational/computational-basis):

* **State 1** — the Bell state `(|00⟩ + |11⟩)/√2` (`bellPhiPlus`). It is already in Schmidt form
  in the computational basis: `bellPhiPlus_isSchmidtDecomposition` exhibits the two-term
  decomposition with coefficients `λ₀ = λ₁ = 1/√2` and Schmidt bases `|0⟩, |1⟩`.
* **State 2** — `(|00⟩ + |01⟩ + |10⟩ + |11⟩)/2`. This is *secretly a product state*
  `|+⟩ ⊗ |+⟩` (`plusPlusState`); recognising that is the content of the exercise for this state.
  `plusPlusState_vec_eq` proves the given sum-of-kets equals `|+⟩ ⊗ |+⟩`, and
  `plusPlusState_isSchmidtDecomposition` exhibits its trivial *single-term* Schmidt decomposition
  (coefficient `1`, Schmidt basis `|+⟩`), i.e. Schmidt number 1 (no entanglement).

The third state `(|00⟩ + |01⟩ + |10⟩)/√3` — genuinely entangled, with irrational
(golden-ratio) Schmidt coefficients `√((3 ± √5)/6)` — is handled separately.

The Schmidt *numbers* `bellPhiPlus.schmidtNumber = 2` and `plusPlusState.schmidtNumber = 1` are in
`AxQM/NC/Ch2/Exercise2_79.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### State 1 — the Bell state `(|00⟩ + |11⟩)/√2` -/

/-- **Nielsen & Chuang, Exercise 2.79 (state 1).** The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`
(`bellPhiPlus`) is already in Schmidt form in the *computational* basis: its Schmidt
decomposition has two terms, with equal coefficients `λ₀ = λ₁ = 1/√2` and Schmidt bases
`|0⟩, |1⟩` on both qubits — `|Φ⁺⟩ = (1/√2)|0⟩|0⟩ + (1/√2)|1⟩|1⟩`. The coefficients are positive
and orthonormal-basis; `∑ᵢ (1/√2)² = 1`; the identity is `bellPhiPlus.vec = (√2)⁻¹ • bellVec`
expanded over `Fin 2`. (Being a two-term decomposition with the computational basis, it exhibits
the maximal entanglement of `|Φ⁺⟩`: Schmidt number 2.) -/
theorem bellPhiPlus_isSchmidtDecomposition :
    bellPhiPlus.IsSchmidtDecomposition (fun _ : Fin 2 => (Real.sqrt 2)⁻¹)
      (fun i => (qubitBasis i).vec) (fun i => (qubitBasis i).vec) := by
  refine ⟨fun _ => by positivity, qubitBasis_vec_orthonormal, qubitBasis_vec_orthonormal, ?_, ?_⟩
  · simp only [Fin.sum_univ_two, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  · rw [bellPhiPlus_vec, bellVec, Fin.sum_univ_two, Complex.ofReal_inv]
    exact smul_add _ _ _

/-! ### State 2 — the product state `(|00⟩ + |01⟩ + |10⟩ + |11⟩)/2 = |+⟩ ⊗ |+⟩` -/

/-- **The two-qubit state `(|00⟩ + |01⟩ + |10⟩ + |11⟩)/2` of Exercise 2.79 (state 2).** Defined as
the product `|+⟩ ⊗ |+⟩` (`qubitPlus.tmul qubitPlus`); `plusPlusState_vec_eq` proves this equals
the sum-of-kets form the exercise gives. Recognising it as a product is precisely what "finding
its Schmidt decomposition" amounts to: a product state is unentangled, so the decomposition is the
single term `1 · |+⟩|+⟩`. -/
def plusPlusState : PureState (qubit ⊗ qubit) := qubitPlus.tmul qubitPlus

/-- **Nielsen & Chuang, Exercise 2.79 (state 2, recognition).** The state
`(|00⟩ + |01⟩ + |10⟩ + |11⟩)/2` is the product state `|+⟩ ⊗ |+⟩`: expanding
`|+⟩ = (1/√2)(|0⟩ + |1⟩)` bilinearly gives `|+⟩ ⊗ |+⟩ = (1/2)(|00⟩ + |01⟩ + |10⟩ + |11⟩)`, since
`(1/√2)(1/√2) = 1/2`. This identification is the substance of the exercise for this state — it
reveals the state is unentangled. -/
theorem plusPlusState_vec_eq :
    plusPlusState.vec = (2 : ℂ)⁻¹ •
      ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec + (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec
        + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec
        + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec) := by
  -- Prove the bilinear expansion in the *raw* tensor space `qubit.space ⊗[ℂ] qubit.space`, where
  -- the `TensorProduct.*_tmul` rewrites fire (they do not match the `(qubit ⊗ qubit).space` head);
  -- then discharge the composite-head goal by definitional equality.
  have key : (Concrete.invSqrt2 • ((qubitBasis 0).vec + (qubitBasis 1).vec)) ⊗ₜ[ℂ]
        (Concrete.invSqrt2 • ((qubitBasis 0).vec + (qubitBasis 1).vec))
      = (2 : ℂ)⁻¹ • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec
          + (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec
          + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec
          + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec) := by
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
      Concrete.invSqrt2_mul_self]
    congr 1
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel
  rw [plusPlusState, PureState.tmul_vec, qubitPlus_vec_eq_smul_add]
  exact key

/-- **Nielsen & Chuang, Exercise 2.79 (state 2).** The product state
`(|00⟩ + |01⟩ + |10⟩ + |11⟩)/2 = |+⟩ ⊗ |+⟩` (`plusPlusState`) has the trivial *single-term*
Schmidt decomposition: coefficient `λ₀ = 1` and Schmidt basis `|+⟩` on both qubits,
`|+⟩ ⊗ |+⟩ = 1 · |+⟩|+⟩`. The single Schmidt coefficient (Schmidt number 1) is the hallmark of a
product state — no entanglement. Orthonormality over `Fin 1` is just the normalisation
`⟨+|+⟩ = 1`; the identity is `PureState.tmul_vec` followed by `1 • x = x`. -/
theorem plusPlusState_isSchmidtDecomposition :
    plusPlusState.IsSchmidtDecomposition (fun _ : Fin 1 => (1 : ℝ))
      (fun _ => qubitPlus.vec) (fun _ => qubitPlus.vec) := by
  have ho : Orthonormal ℂ (fun _ : Fin 1 => qubitPlus.vec) :=
    orthonormal_iff_ite.mpr fun i j => by
      rw [ite_eq_left (Subsingleton.elim i j)]; exact inner_qubitPlus_self
  refine ⟨fun _ => one_pos, ho, ho, ?_, ?_⟩
  · simp
  · rw [plusPlusState, PureState.tmul_vec, Fin.sum_univ_one]
    simp
    rfl

end AxQM
