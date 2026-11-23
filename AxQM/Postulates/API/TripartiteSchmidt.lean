/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellState
import AxQM.Concrete.BellVector

/-!
# AxQM — no single-Schmidt-basis decomposition for tripartite states (N&C Exercise 2.77)

Nielsen & Chuang, Exercise 2.77 (p. 110): *there exist* pure states `|ψ⟩` of a three-component
system `ABC` which **cannot** be written in the "single Schmidt basis" (triorthogonal) form

  `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩|iᴄ⟩`,

with `λᵢ` real and `{|iᴬ⟩}`, `{|iᴮ⟩}`, `{|iᴄ⟩}` orthonormal bases of the three systems. In other
words, the bipartite Schmidt decomposition (Theorem 2.7) has **no** direct tripartite analogue.

## The example and the argument

We exhibit the concrete counterexample `|0⟩ ⊗ |Φ⁺⟩` on `qubit ⊗ (qubit ⊗ qubit)` — the first
qubit in the computational-basis state `|0⟩`, the last two in the maximally entangled Bell state
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. Suppose it *did* have a triorthogonal decomposition
`∑ᵢ λᵢ (aᵢ ⊗ bᵢ ⊗ cᵢ)`. Contract the `A`-factor against `aₖ`: because `{aᵢ}` is orthonormal, the
partial inner product (`TensorProduct.contractFst`, in `ToMathlib`) collapses the sum to
`⟨aₖ|0⟩ • |Φ⁺⟩ = λₖ • (bₖ ⊗ cₖ)`. Some
`λₖ ≠ 0` (else `|ψ⟩ = 0`, impossible for a unit vector), and then `bₖ ⊗ cₖ ≠ 0`, forcing
`⟨aₖ|0⟩ ≠ 0`; dividing shows `|Φ⁺⟩` equals the *simple tensor* `((…) • bₖ) ⊗ cₖ`. But the Bell
vector is not a simple tensor (`Concrete.bellVector_ne_tmul`, Exercise 2.68) — contradiction.

The refutation uses only that `{aᵢ}` is orthonormal and that `bₖ`, `cₖ` are nonzero unit vectors,
so it in fact rules out any decomposition into orthonormal *families* — strictly stronger than N&C's
"orthonormal bases" form (bases are families; ruling out the wider class subsumes the exercise).

## The statement and the partial inner product

The sum `∑ᵢ λᵢ (aᵢ ⊗ bᵢ ⊗ cᵢ)` is a sum of state vectors (`.vec`, in `⊗ₜ`, `.space`, with
`Orthonormal` families), since pure states are not a vector space. The statement of Exercise 2.77
is in `AxQM/NC/Ch2/Exercise2_77.lean`.

The device that isolates one term of the decomposition — the partial inner product
`x ⊗ w ↦ ⟨v|x⟩ • w` on the first tensor factor (`TensorProduct.contractFst` / `contractFst_tmul`) —
is general inner-product/tensor mathematics, in
`ToMathlib/Analysis/InnerProductSpace/TensorProduct.lean` (next to `rankOne_tmul_self`).

## Main results

* `PureState.HasTriorthogonalDecomposition` — the tripartite "single Schmidt basis" form.
* `zeroTensorBell` — the counterexample `|0⟩ ⊗ |Φ⁺⟩`.
* `zeroTensorBell_not_hasTriorthogonalDecomposition` — it has no such
  decomposition.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **A "single Schmidt basis" (triorthogonal) decomposition** of a tripartite pure state:
`|ψ⟩ = ∑ᵢ λᵢ (aᵢ ⊗ bᵢ ⊗ cᵢ)` for real `λᵢ` and orthonormal families `{aᵢ}` (in `A`), `{bᵢ}` (in
`B`), `{cᵢ}` (in `C`). This is the tripartite analogue of the Schmidt form of Theorem 2.7; N&C
Exercise 2.77 asks to show it does not always exist. (Stated with orthonormal *families*, which
subsumes N&C's orthonormal *bases*.) -/
def PureState.HasTriorthogonalDecomposition (ψ : PureState (A ⊗ (B ⊗ C))) : Prop :=
  ∃ (n : ℕ) (l : Fin n → ℝ) (a : Fin n → A.space) (b : Fin n → B.space) (c : Fin n → C.space),
    Orthonormal ℂ a ∧ Orthonormal ℂ b ∧ Orthonormal ℂ c ∧
    ψ.vec = ∑ i, (l i : ℂ) • (a i ⊗ₜ[ℂ] (b i ⊗ₜ[ℂ] c i))

/-- **The counterexample `|0⟩ ⊗ |Φ⁺⟩`** (N&C Exercise 2.77): the first qubit in the
computational-basis state `|0⟩`, the last two maximally entangled in the Bell state `|Φ⁺⟩`. A pure
state of `qubit ⊗ (qubit ⊗ qubit)` with no triorthogonal decomposition. -/
def zeroTensorBell : PureState (qubit ⊗ (qubit ⊗ qubit)) := qubitBasis 0 ⊗ bellPhiPlus

/-- **Nielsen & Chuang, Exercise 2.77.** The tripartite state `|0⟩ ⊗ |Φ⁺⟩` has no "single Schmidt
basis" decomposition `∑ᵢ λᵢ (aᵢ ⊗ bᵢ ⊗ cᵢ)` — the Schmidt decomposition (Theorem 2.7) has no
tripartite analogue. Contracting the `A`-factor against `aₖ` collapses any such decomposition to
`⟨aₖ|0⟩ • |Φ⁺⟩ = λₖ • (bₖ ⊗ cₖ)`; a nonzero term makes `|Φ⁺⟩` a simple tensor, contradicting that
the Bell vector is entangled (`Concrete.bellVector_ne_tmul`). -/
theorem zeroTensorBell_not_hasTriorthogonalDecomposition :
    ¬ zeroTensorBell.HasTriorthogonalDecomposition := by
  rintro ⟨n, l, a, b, c, ha, hb, hc, hdecomp⟩
  -- `qubit.space` is defeq `EuclideanSpace ℂ (Fin 2)`, but instance search does not unfold the
  -- `QSystem.space` projection, so supply the scalar-commutativity instance the tensor-scalar
  -- lemmas need over the qubit space.
  have : SMulCommClass ℂ ℂ qubit.space :=
    inferInstanceAs (SMulCommClass ℂ ℂ (EuclideanSpace ℂ (Fin 2)))
  -- some coefficient is nonzero, else `|ψ⟩ = 0` contradicts normalization.
  have hne : ∃ k, l k ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hzero : zeroTensorBell.vec = 0 := by
      rw [hdecomp]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [h i, Complex.ofReal_zero]
      exact zero_smul ℂ _
    have hnorm := zeroTensorBell.normalized
    rw [hzero, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  obtain ⟨k, hk⟩ := hne
  -- contract the `A`-factor against `aₖ`.
  have hL : TensorProduct.contractFst (a k) zeroTensorBell.vec
      = (inner ℂ (a k) (qubitBasis 0).vec : ℂ) • bellPhiPlus.vec := by
    simp only [zeroTensorBell, PureState.tmul_vec, TensorProduct.contractFst_tmul]
  have hR : TensorProduct.contractFst (a k) zeroTensorBell.vec = (l k : ℂ) • (b k ⊗ₜ[ℂ] c k) := by
    rw [hdecomp]
    -- `zeroTensorBell.vec` is defeq to the raw sum; `show` unifies the tensor head so `map_sum`
    -- (which needs the linear map's domain to match the summand type) fires.
    change TensorProduct.contractFst (a k) (∑ i, (l i : ℂ) • (a i ⊗ₜ[ℂ] (b i ⊗ₜ[ℂ] c i)))
        = (l k : ℂ) • (b k ⊗ₜ[ℂ] c k)
    simp only [map_sum, map_smul, TensorProduct.contractFst_tmul]
    rw [Finset.sum_eq_single k]
    · rw [orthonormal_iff_ite.mp ha k k, ite_eq_left rfl, one_smul]
    · intro i _ hik
      rw [orthonormal_iff_ite.mp ha k i, ite_eq_right (fun e => hik e.symm), zero_smul, smul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hcontract : (inner ℂ (a k) (qubitBasis 0).vec : ℂ) • bellPhiPlus.vec
      = (l k : ℂ) • (b k ⊗ₜ[ℂ] c k) := hL.symm.trans hR
  -- `bₖ`, `cₖ` are unit vectors, so `bₖ ⊗ cₖ ≠ 0`.
  have hbk : ‖b k‖ = 1 := hb.norm_eq_one k
  have hck : ‖c k‖ = 1 := hc.norm_eq_one k
  have hwk : (b k ⊗ₜ[ℂ] c k) ≠ 0 := by
    intro h0
    have hz : ‖(b k ⊗ₜ[ℂ] c k)‖ = 0 := by rw [h0, norm_zero]
    rw [TensorProduct.norm_tmul, hbk, hck, mul_one] at hz
    exact one_ne_zero hz
  have hlk : (l k : ℂ) ≠ 0 := by exact_mod_cast hk
  -- hence the contracted scalar `⟨aₖ|0⟩` is nonzero.
  have hμne : (inner ℂ (a k) (qubitBasis 0).vec : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hcontract
    exact (smul_ne_zero hlk hwk) hcontract.symm
  -- solve for `|Φ⁺⟩` (as the raw Bell vector) being a simple tensor, contradicting entanglement.
  have hbell : Concrete.bellVector
      = ((inner ℂ (a k) (qubitBasis 0).vec : ℂ)⁻¹ • (l k : ℂ) • b k) ⊗ₜ[ℂ] c k := by
    have hc2 : (inner ℂ (a k) (qubitBasis 0).vec : ℂ) • Concrete.bellVector
        = (l k : ℂ) • (b k ⊗ₜ[ℂ] c k) := hcontract
    have hcancel : Concrete.bellVector
        = (inner ℂ (a k) (qubitBasis 0).vec : ℂ)⁻¹
            • ((inner ℂ (a k) (qubitBasis 0).vec : ℂ) • Concrete.bellVector) := by
      rw [smul_smul, inv_mul_cancel₀ hμne, one_smul]
    rw [hcancel, hc2, TensorProduct.smul_tmul']
    exact TensorProduct.smul_tmul'
      ((inner ℂ (a k) (qubitBasis 0).vec : ℂ))⁻¹ ((l k : ℂ) • b k) (c k)
  exact Concrete.bellVector_ne_tmul _ _ hbell

end AxQM
