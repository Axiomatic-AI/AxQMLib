/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import Mathlib.Analysis.CStarAlgebra.Projection
import ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# AxQM — projective measurements (N&C §2.2.5 / Exercise 2.62)

A **projective (von Neumann) measurement** is the special case of the general measurement
postulate (Postulate 3, `Measurement`) in which the measurement
operators are *orthogonal projectors*. Nielsen–Chuang §2.2.5 describes it by projectors `Pₘ`
with

  `Pₘ Pₘ' = δₘₘ' Pₘ`   and   `∑ₘ Pₘ = I`.

This file adds the vocabulary a projective measurement needs:

* `Measurement.IsProjective` — the predicate carving out the projective measurements among all
  measurements: every operator `Mᵢ` is a star projection (self-adjoint idempotent — an
  orthogonal projector), and distinct operators are orthogonal (`Mᵢ Mⱼ = 0` for `i ≠ j`). This
  is exactly the off-diagonal/diagonal split of N&C's `Pₘ Pₘ' = δₘₘ' Pₘ`.
* `Measurement.IsSelfPOVM` — the hypothesis of N&C Exercise 2.62: the measurement operators
  coincide with their POVM effects, `Mᵢ = Eᵢ = Mᵢ† Mᵢ` (N&C: "all the POVM elements are the
  same as the measurement operators themselves").

Two structural facts complete the correspondence with N&C's definition:

* `Measurement.sum_op_eq_one_of_isStarProjection` / `Measurement.IsProjective.sum_op_eq_one` —
  the resolution of the identity `∑ᵢ Mᵢ = 1` (N&C's `∑ₘ Pₘ = I`). It is *automatic* for a
  measurement whose operators are projectors: the structural completeness `∑ᵢ Mᵢ† Mᵢ = 1`
  collapses to `∑ᵢ Mᵢ = 1` because `Mᵢ† Mᵢ = Mᵢ` for a projector.
* `Measurement.mul_op_eq_zero_of_isStarProjection` — mutual orthogonality is likewise automatic:
  projectors that resolve the identity are pairwise orthogonal. The short proof is C*-algebraic:
  `Mᵢ ≤ 1 - Mⱼ` (the other projectors are positive and `∑ = 1`), and for star projections
  `p ≤ q ↔ p q = p` (`IsStarProjection.le_iff_mul_eq_left`), giving `Mᵢ(1 - Mⱼ) = Mᵢ`, i.e.
  `Mᵢ Mⱼ = 0`. This uses the C*-algebra / Loewner-order structure of `S →L[ℂ] S`.

Exercise 2.62 — `IsSelfPOVM → IsProjective`, stated with these predicates — is in
`AxQM/NC/Ch2/Exercise2_62.lean`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- A measurement is **projective** (von Neumann) when every operator `Mᵢ` is a star projection
(`IsStarProjection` — a self-adjoint idempotent, an orthogonal projector). This is the single
minimal condition carving out the projective measurements among all general measurements
(Postulate 3): the remaining defining data of N&C §2.2.5 is then automatic and supplied as
derived theorems, on equal footing —

* `IsProjective.orthogonal` : `Mᵢ Mⱼ = 0` for `i ≠ j` (the off-diagonal of `Pₘ Pₘ' = δₘₘ' Pₘ`;
  the `m = m'` diagonal is the idempotence already inside `IsStarProjection`);
* `IsProjective.sum_op_eq_one` : `∑ᵢ Mᵢ = 1` (N&C's `∑ₘ Pₘ = I`).

Both hold for *any* `Measurement` whose operators are projectors — orthogonality from the
`m.complete` completeness relation, and the resolution of the identity likewise — so neither is a
bundled hypothesis; they are theorems, and together with the definition they are exactly N&C's
`Pₘ Pₘ' = δₘₘ' Pₘ`, `∑ₘ Pₘ = I`. -/
def IsProjective (m : Measurement ι S) : Prop := ∀ i, IsStarProjection (m.op i)

/-- The measurement operators **coincide with their POVM effects**: `Mᵢ = Eᵢ = Mᵢ† Mᵢ` for every
outcome (N&C Exercise 2.62 hypothesis). Equivalently the induced POVM `toPOVM` has the operators
themselves as its elements. -/
def IsSelfPOVM (m : Measurement ι S) : Prop := ∀ i, m.op i = m.toPOVM.elements i

/-- **Resolution of the identity from projectors.** If every operator of a measurement is a star
projection, they sum to the identity, `∑ᵢ Mᵢ = 1` (N&C's `∑ₘ Pₘ = I`). This is automatic: the
structural completeness relation `∑ᵢ Mᵢ† Mᵢ = 1` collapses because `Mᵢ† Mᵢ = Mᵢ` for a projector
(self-adjoint `Mᵢ† = Mᵢ`, idempotent `Mᵢ Mᵢ = Mᵢ`). -/
theorem sum_op_eq_one_of_isStarProjection {m : Measurement ι S}
    (hsp : ∀ i, IsStarProjection (m.op i)) : ∑ i, m.op i = 1 := by
  have key : ∀ i, (adjoint (m.op i)).comp (m.op i) = m.op i := fun i => by
    rw [← ContinuousLinearMap.star_eq_adjoint, (hsp i).isSelfAdjoint.star_eq,
      ← ContinuousLinearMap.mul_def]
    exact (hsp i).isIdempotentElem
  calc ∑ i, m.op i = ∑ i, (adjoint (m.op i)).comp (m.op i) :=
        Finset.sum_congr rfl fun i _ => (key i).symm
    _ = 1 := m.complete

/-- **Projectors resolving the identity are mutually orthogonal.** If every operator of a
measurement is a star projection, distinct operators are orthogonal, `Mᵢ Mⱼ = 0` for `i ≠ j`.
Proof (C*-algebraic, in the C*-algebra `S →L[ℂ] S` with the Loewner order): from
`sum_op_eq_one_of_isStarProjection`, `∑ₖ Mₖ = 1`, so `Mᵢ ≤ ∑_{k ≠ j} Mₖ = 1 - Mⱼ` since the
projectors are positive; and for star projections `p ≤ q ↔ p q = p`
(`IsStarProjection.le_iff_mul_eq_left`), giving `Mᵢ(1 - Mⱼ) = Mᵢ`, i.e. `Mᵢ Mⱼ = 0`. -/
theorem mul_op_eq_zero_of_isStarProjection {m : Measurement ι S}
    (hsp : ∀ i, IsStarProjection (m.op i)) {i j : ι} (hij : i ≠ j) :
    m.op i * m.op j = 0 := by
  classical
  have hsum : ∑ k, m.op k = 1 := sum_op_eq_one_of_isStarProjection hsp
  have hle : m.op i ≤ 1 - m.op j := by
    have h1 : m.op i ≤ ∑ k ∈ Finset.univ.erase j, m.op k :=
      Finset.single_le_sum (fun k _ => (hsp k).nonneg)
        (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
    rwa [Finset.sum_erase_eq_sub (Finset.mem_univ j), hsum] at h1
  have hmul := ((hsp i).le_iff_mul_eq_left (hsp j).one_sub).mp hle
  rw [mul_sub, mul_one] at hmul
  exact sub_eq_self.mp hmul

/-- **Orthogonality of a projective measurement:** distinct operators annihilate, `Mᵢ Mⱼ = 0` for
`i ≠ j` — the off-diagonal of N&C's `Pₘ Pₘ' = δₘₘ' Pₘ` (the diagonal `m = m'` is the idempotence
inside `IsProjective`). Automatic from the projectors resolving the identity
(`mul_op_eq_zero_of_isStarProjection`). -/
theorem IsProjective.orthogonal {m : Measurement ι S} (h : m.IsProjective) {i j : ι}
    (hij : i ≠ j) : m.op i * m.op j = 0 :=
  mul_op_eq_zero_of_isStarProjection h hij

/-- **Resolution of the identity for a projective measurement:** `∑ᵢ Mᵢ = 1` (N&C's `∑ₘ Pₘ = I`),
the second defining property of a projective measurement alongside `Pₘ Pₘ' = δₘₘ' Pₘ`. Automatic
(`sum_op_eq_one_of_isStarProjection`), symmetric with `IsProjective.orthogonal`. -/
theorem IsProjective.sum_op_eq_one {m : Measurement ι S} (h : m.IsProjective) :
    ∑ i, m.op i = 1 :=
  sum_op_eq_one_of_isStarProjection h

/-- **A basis measurement is projective (von Neumann).** The measurement `ofOrthonormalBasis b`
has each operator `Mᵢ = |bᵢ⟩⟨bᵢ|` (`ofOrthonormalBasis_op`) equal to the rank-one projector onto
the unit basis vector `bᵢ`, hence a star projection
(`InnerProductSpace.isStarProjection_rankOne_self`, using `‖bᵢ‖ = 1`). So it is projective in the
sense of N&C §2.2.5: by the derived theorems its operators are pairwise orthogonal
(`IsProjective.orthogonal`) and resolve the identity (`IsProjective.sum_op_eq_one`). General
reusable infrastructure — the genuine-basis case of `isProjective_ofOrthonormalBasisFiber`, which
coarse-grains outcomes through a map `ι → M` (needing `Fintype`/`DecidableEq` on `M`). -/
theorem isProjective_ofOrthonormalBasis (b : OrthonormalBasis ι ℂ S.space) :
    (Measurement.ofOrthonormalBasis b).IsProjective := fun i => by
  rw [Measurement.ofOrthonormalBasis_op]
  exact InnerProductSpace.isStarProjection_rankOne_self (b.orthonormal.1 i)

/-- **Born rule for a projective measurement in an orthonormal basis, on a pure state.** The
probability of outcome `i` when measuring the pure state `ψ` in the basis `b` is the squared
magnitude of the amplitude `⟨bᵢ, ψ⟩`, i.e. `|amplitude|²` — N&C's `p(m) = |⟨m|ψ⟩|²` for a
computational-basis measurement. Immediate from the induced rank-one POVM: `bornProb` unfolds to
`re⟨bᵢ, |ψ⟩⟨ψ| bᵢ⟩ = re(⟨ψ, bᵢ⟩⟨bᵢ, ψ⟩) = ‖⟨bᵢ, ψ⟩‖²`. General reusable infrastructure. -/
theorem bornProb_ofOrthonormalBasis_toState (b : OrthonormalBasis ι ℂ S.space) (ψ : PureState S)
    (i : ι) :
    (Measurement.ofOrthonormalBasis b).bornProb ψ.toState i = ‖(inner ℂ (b i) ψ.vec : ℂ)‖ ^ 2 := by
  rw [Measurement.bornProb, Measurement.toPOVM_ofOrthonormalBasis, POVM.toPMF_ofOrthonormalBasis,
    PureState.toState_op, InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm,
    RCLike.conj_mul]
  exact_mod_cast rfl

/-- **Born rule for a projective measurement in an orthonormal basis, on a general state.** The
probability of outcome `i` when measuring the state `ρ` in the basis `b` is the diagonal density
matrix element `re⟨bᵢ, ρ bᵢ⟩`. Immediate from the induced rank-one POVM. The general-state
counterpart of `bornProb_ofOrthonormalBasis_toState`; general reusable infrastructure. -/
theorem bornProb_ofOrthonormalBasis (b : OrthonormalBasis ι ℂ S.space) (ρ : State S) (i : ι) :
    (Measurement.ofOrthonormalBasis b).bornProb ρ i = (⟪b i, ρ.op (b i)⟫_ℂ).re := by
  rw [Measurement.bornProb, Measurement.toPOVM_ofOrthonormalBasis, POVM.toPMF_ofOrthonormalBasis]
  rfl

end Measurement

end AxQM
