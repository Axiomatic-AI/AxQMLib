/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.LinearMap

/-!
# AxQM.Postulates.API — shared facts on pure states

Shared facts on pure states, concerning the state vector `PureState.vec` (or the induced density
operator `PureState.toState`):

* `PureState.normalize v hv` — the pure state `‖v‖⁻¹ • v` of a nonzero vector `v : S`. Every
  construction that presents a pure state as "the normalization of some explicit (unnormalized)
  vector" — an eigenvector, a projected vector, a post-measurement direction — routes its `‖·‖ = 1`
  obligation through this one lemma instead of re-proving it.
* `PureState.toState_eq_of_vec_eq_smul` — a **global phase is invisible to the density operator**:
  vectors differing by a unit-modulus scalar induce the same `PureState.toState`.
* `PureState.inner_self` — a pure state's vector is a unit vector: `⟨ψ, ψ⟩ = 1`. The shared form of
  the normalization fact whenever an inner product `⟪ψ.vec, ψ.vec⟫` appears in a computation.
* `PureState.overlap` — the **overlap** (transition amplitude) `⟨ψ|φ⟩` of two pure states, used in
  place of the raw `inner` of state vectors (e.g. in Uhlmann's theorem, N&C Thm 9.4).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

namespace PureState

variable {S : QSystem}

/-- **A pure state's vector has unit self-inner-product: `⟨ψ, ψ⟩ = 1`.** The complex-valued
companion of `PureState.normalized` (`‖ψ.vec‖ = 1`). Cite this single shared lemma whenever
`⟪ψ.vec, ψ.vec⟫_ℂ` appears, rather than re-deriving it from `inner_self_eq_norm_sq_to_K`.
It is not `@[simp]`: `simp` already rewrites `⟪ψ.vec, ψ.vec⟫` to `↑‖ψ.vec‖ ^ 2`. -/
theorem inner_self (ψ : PureState S) : inner ℂ ψ.vec ψ.vec = (1 : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, ψ.normalized]; norm_num

/-- **A pure state's underlying vector is nonzero:** its norm is `1`, so it cannot be the zero
vector. The foundational nonzero witness cited whenever a state vector must be shown nonzero — e.g.
to feed `PureState.normalize`, or to conclude from `μ • ψ.vec = ν • ψ.vec` that `μ = ν`. -/
theorem vec_ne_zero (ψ : PureState S) : ψ.vec ≠ 0 := by
  intro h
  have hn := ψ.normalized
  rw [h, norm_zero] at hn
  norm_num at hn

/-- The **overlap** (transition amplitude) `⟨ψ|φ⟩` of two pure states of the same system,
`⟪ψ.vec, φ.vec⟫`. It is used in place of the raw `inner` of state vectors — e.g. in Uhlmann's
theorem (N&C Thm 9.4), where the fidelity is the greatest overlap magnitude `‖ψ.overlap φ‖`
achievable over purifications. Following Mathlib's `inner ℂ` convention it is conjugate-linear in
the bra `ψ` and linear in the ket `φ`; its magnitude `‖ψ.overlap φ‖` is the physical transition
probability amplitude. -/
def overlap (ψ φ : PureState S) : ℂ := inner ℂ ψ.vec φ.vec

/-- Unfolding lemma for `PureState.overlap`: `ψ.overlap φ = ⟪ψ.vec, φ.vec⟫`. Kept out of the default
`simp` set (like `inner_self`) so `overlap` survives in statements that use it; cite it explicitly
when the raw inner product is needed. -/
theorem overlap_def (ψ φ : PureState S) : ψ.overlap φ = inner ℂ ψ.vec φ.vec := rfl

/-- **A pure state has unit overlap with itself: `⟨ψ|ψ⟩ = 1`.** The `overlap`-level companion of
`PureState.inner_self`; cite it whenever the diagonal transition amplitude `ψ.overlap ψ` appears
(e.g. the ancilla `⟨u|u⟩ = 1` normalization in N&C Proposition 12.18). Kept out of `simp` (like
`overlap_def`) so `overlap` is not eagerly unfolded. -/
theorem overlap_self (ψ : PureState S) : ψ.overlap ψ = 1 := by
  rw [overlap_def]; exact ψ.inner_self

/-- **Two pure states with overlap `1` are equal.** If the transition amplitude `⟨ψ|φ⟩` equals `1`
then `ψ = φ`: the rigidity (equality) case of the Cauchy–Schwarz bound `‖⟨ψ|φ⟩‖ ≤ 1` for unit
vectors — a unit overlap forces the two unit vectors to coincide *exactly*, leaving not even a
global phase free. The shared lever for "unit overlap pins the state down", e.g. an undisturbed
probe whose ancilla is left unchanged (N&C Proposition 12.18). The direct equality-case lemma
`inner_eq_one_iff_of_norm_eq_one` (`‖x‖ = ‖y‖ = 1 → (⟨x, y⟩ = 1 ↔ x = y)`) applies through the
definitional unfolding of `overlap`. -/
theorem eq_of_overlap_eq_one {ψ φ : PureState S} (h : ψ.overlap φ = 1) : ψ = φ :=
  PureState.ext ((inner_eq_one_iff_of_norm_eq_one ψ.normalized φ.normalized).mp h)

/-- The **normalized pure state** `‖v‖⁻¹ • v` built from a nonzero vector `v : S`. The single shared
constructor for "the pure state in the direction of `v`"; its `‖·‖ = 1` proof is the one place the
`norm_smul` / `inv_mul_cancel₀` normalization argument is discharged. -/
def normalize (v : S) (hv : v ≠ 0) : PureState S where
  vec := ((‖v‖ : ℝ) : ℂ)⁻¹ • v
  normalized := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

@[simp]
theorem normalize_vec (v : S) (hv : v ≠ 0) :
    (normalize v hv).vec = ((‖v‖ : ℝ) : ℂ)⁻¹ • v := rfl

/-- **A global phase is invisible to the density operator.** If `ψ.vec = c • φ.vec` for a
unit-modulus scalar `c` (`‖c‖ = 1`), then the density operators coincide, `|ψ⟩⟨ψ| = |φ⟩⟨φ|`, hence
`ψ.toState = φ.toState`: a global phase never affects the state.  (`|ψ⟩⟨ψ|` scales by
`c · conj c = ‖c‖² = 1`, `InnerProductSpace.rankOne_smul_smul_self`.) -/
theorem toState_eq_of_vec_eq_smul {ψ φ : PureState S} {c : ℂ} (hc : ‖c‖ = 1)
    (h : ψ.vec = c • φ.vec) : ψ.toState = φ.toState := by
  refine State.ext ?_
  rw [toState_op, toState_op, h, InnerProductSpace.rankOne_smul_smul_self,
    show c * (starRingEnd ℂ) c = 1 by rw [RCLike.mul_conj, hc]; norm_num, one_smul]

end PureState

end AxQM
