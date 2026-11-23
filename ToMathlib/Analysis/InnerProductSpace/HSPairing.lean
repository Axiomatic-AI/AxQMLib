/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Adjoint
public import ToMathlib.Analysis.InnerProductSpace.Trace
public import ToMathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Hilbert–Schmidt pairing of linear maps

For two linear maps `T, U : E →ₗ[𝕜] F` between finite-dimensional inner product spaces over
`𝕜` (where `𝕜` is `ℝ` or `ℂ`), the **Hilbert–Schmidt pairing** is

`hsPairing T U := trace (U† ∘ T)`

where `U†` is the (finite-dimensional) adjoint of `U`. This is the bilinear (sesquilinear)
form underlying the Hilbert–Schmidt inner product on operators.

The existing `HilbertSchmidt.hsInner` provides the same pairing on the bundled
`HilbertSchmidt 𝕜 E` type of endomorphisms; this file gives the unbundled function form for
general `E →ₗ[𝕜] F` so that the variational characterization of the trace norm
(`traceNorm T = ⨆_{‖W‖_op ≤ 1} re (hsPairing T W)`) can be stated cleanly at the LM/CLM
level without committing to the bundled type.

## Main definitions

- `LinearMap.hsPairing` — the function `(T, U) ↦ trace (U† ∘ T)`.
- `ContinuousLinearMap.hsPairing` — the CLM sibling.

## Main results

- `hsPairing_add_left` / `_right`, `hsPairing_sub_left` / `_right`,
  `hsPairing_neg_left` / `_right`, `hsPairing_smul_left` / `_right`,
  `hsPairing_zero_left` / `_right`: bilinearity (sesquilinear in the right slot).
- `hsPairing_conj`: conjugate symmetry `star (hsPairing T U) = hsPairing U T`.
- `hsPairing_self_star_eq_self`: the self-pairing `hsPairing T T` is fixed by `star`
  (equivalently, real-valued).
- `hsPairing_comp_left` / `_right`: the "move-adjoint" identities for compositions.
- `re_hsPairing_self_eq_sum_norm_sq`: the basis-sum form of the HS-norm squared,
  `re (hsPairing T T) = ∑ ‖T (b i)‖²`.
- `re_hsPairing_self_eq_re_trace_comp_self_of_isSymmetric` (LM) /
  `re_hsPairing_self_eq_re_trace_sq_of_isSelfAdjoint` (CLM): for a symmetric/self-adjoint
  endomorphism, the HS self-pairing reduces to the trace of `T ∘ₗ T` (resp. `T * T`).
- `norm_hsPairing_sq_le`: the Cauchy–Schwarz inequality
  `‖hsPairing T U‖² ≤ re (hsPairing T T) · re (hsPairing U U)`.
- `re_hsPairing_self_comp_le`: HS-norm sub-multiplicativity,
  `re (hsPairing (S ∘ T) (S ∘ T)) ≤ ‖S‖_op² · re (hsPairing T T)`.

## Implementation notes

The pairing uses `LinearMap.adjoint` (the finite-dim-specific RCLike-clean definition); no
`[CompleteSpace _]` premises propagate. The CLM sibling defers to the LM version via
`toLinearMap`, mirroring the pattern in `TraceNorm.lean`.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The **Hilbert–Schmidt pairing** of two linear maps: `trace (U† ∘ T)`. -/
noncomputable def hsPairing (T U : E →ₗ[𝕜] F) : 𝕜 :=
  LinearMap.trace 𝕜 E (U.adjoint ∘ₗ T)

theorem hsPairing_eq (T U : E →ₗ[𝕜] F) :
    T.hsPairing U = LinearMap.trace 𝕜 E (U.adjoint ∘ₗ T) := rfl

@[simp]
theorem hsPairing_zero_left (U : E →ₗ[𝕜] F) : hsPairing (0 : E →ₗ[𝕜] F) U = 0 := by
  simp [hsPairing_eq]

@[simp]
theorem hsPairing_zero_right (T : E →ₗ[𝕜] F) : T.hsPairing 0 = 0 := by
  simp [hsPairing_eq]

theorem hsPairing_add_left (T T' U : E →ₗ[𝕜] F) :
    (T + T').hsPairing U = T.hsPairing U + T'.hsPairing U := by
  simp [hsPairing_eq, LinearMap.comp_add, map_add]

theorem hsPairing_sub_left (T T' U : E →ₗ[𝕜] F) :
    (T - T').hsPairing U = T.hsPairing U - T'.hsPairing U := by
  simp [hsPairing_eq, LinearMap.comp_sub, map_sub]

theorem hsPairing_neg_left (T U : E →ₗ[𝕜] F) :
    (-T).hsPairing U = - T.hsPairing U := by
  simp [hsPairing_eq, LinearMap.comp_neg, map_neg]

theorem hsPairing_add_right (T U U' : E →ₗ[𝕜] F) :
    T.hsPairing (U + U') = T.hsPairing U + T.hsPairing U' := by
  simp [hsPairing_eq, map_add, LinearMap.add_comp]

theorem hsPairing_sub_right (T U U' : E →ₗ[𝕜] F) :
    T.hsPairing (U - U') = T.hsPairing U - T.hsPairing U' := by
  simp [hsPairing_eq, map_sub, LinearMap.sub_comp]

theorem hsPairing_neg_right (T U : E →ₗ[𝕜] F) :
    T.hsPairing (-U) = - T.hsPairing U := by
  simp [hsPairing_eq, map_neg, LinearMap.neg_comp]

theorem hsPairing_sum_left {ι : Type*} (s : Finset ι) (T : ι → E →ₗ[𝕜] F)
    (U : E →ₗ[𝕜] F) :
    (∑ i ∈ s, T i).hsPairing U = ∑ i ∈ s, (T i).hsPairing U := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, hsPairing_add_left, ih, Finset.sum_insert hi]

theorem hsPairing_sum_right {ι : Type*} (T : E →ₗ[𝕜] F) (s : Finset ι)
    (U : ι → E →ₗ[𝕜] F) :
    T.hsPairing (∑ i ∈ s, U i) = ∑ i ∈ s, T.hsPairing (U i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, hsPairing_add_right, ih, Finset.sum_insert hi]

theorem hsPairing_smul_left (c : 𝕜) (T U : E →ₗ[𝕜] F) :
    (c • T).hsPairing U = c * T.hsPairing U := by
  simp [hsPairing_eq, LinearMap.comp_smul, map_smul]

theorem hsPairing_smul_right (c : 𝕜) (T U : E →ₗ[𝕜] F) :
    T.hsPairing (c • U) = star c * T.hsPairing U := by
  rw [hsPairing_eq, hsPairing_eq, LinearMap.adjoint.map_smulₛₗ, LinearMap.smul_comp, map_smul,
    smul_eq_mul, RCLike.star_def]

/-- **Conjugate symmetry** of the HS pairing: `star (hsPairing T U) = hsPairing U T`. The
proof uses `trace_adjoint` to move the star inside the trace, then `adjoint_comp` +
`adjoint_adjoint` to expand. -/
theorem hsPairing_conj (T U : E →ₗ[𝕜] F) :
    star (T.hsPairing U) = U.hsPairing T := by
  rw [hsPairing_eq, hsPairing_eq, LinearMap.trace_adjoint, adjoint_comp, adjoint_adjoint]

/-- The HS self-pairing `hsPairing T T` is fixed by `star` (equivalently, real-valued). -/
theorem hsPairing_self_star_eq_self (T : E →ₗ[𝕜] F) :
    star (T.hsPairing T) = T.hsPairing T :=
  hsPairing_conj T T

section MoveAdjoint
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- **Move-adjoint identity, left form**: for `T : E →ₗ[𝕜] F`, `S : F →ₗ[𝕜] G`,
`W : E →ₗ[𝕜] G`, we have `hsPairing (S ∘ₗ T) W = hsPairing T (S.adjoint ∘ₗ W)`. The factor
`S` can be moved from the first slot to the (adjoint of the) second slot. Proof: unfold
`hsPairing`, expand `adjoint (S.adjoint ∘ₗ W)` via `adjoint_comp` + `adjoint_adjoint`, then
collect by `comp_assoc`. -/
theorem hsPairing_comp_left (T : E →ₗ[𝕜] F) (S : F →ₗ[𝕜] G) (W : E →ₗ[𝕜] G) :
    (S ∘ₗ T).hsPairing W = T.hsPairing (S.adjoint ∘ₗ W) := by
  rw [hsPairing_eq, hsPairing_eq, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    LinearMap.comp_assoc]

/-- **Move-adjoint identity, right form**: for `T : E →ₗ[𝕜] F`, `S : F →ₗ[𝕜] G`,
`W : E →ₗ[𝕜] G`, we have `hsPairing (S ∘ₗ T) W = hsPairing S (W ∘ₗ T.adjoint)`. The factor
`T` can be moved from the first slot to the (adjoint of the) second slot. Proof: unfold,
expand `adjoint`, then apply `trace_comp_comm'` to swap the trace from `End E` to `End F`. -/
theorem hsPairing_comp_right (T : E →ₗ[𝕜] F) (S : F →ₗ[𝕜] G) (W : E →ₗ[𝕜] G) :
    (S ∘ₗ T).hsPairing W = S.hsPairing (W ∘ₗ T.adjoint) := by
  rw [hsPairing_eq, hsPairing_eq, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  exact LinearMap.trace_comp_comm' T (LinearMap.adjoint W ∘ₗ S)

end MoveAdjoint

/-- The real part of the HS self-pairing `hsPairing T T` is the HS-norm squared: it equals
`∑ ‖T (b i)‖²` over any orthonormal basis. (The expression is basis-independent because
the trace is.) -/
theorem re_hsPairing_self_eq_sum_norm_sq {ι : Type*} [Fintype ι]
    (T : E →ₗ[𝕜] F) (b : OrthonormalBasis ι 𝕜 E) :
    RCLike.re (T.hsPairing T) = ∑ i, ‖T (b i)‖ ^ 2 := by
  rw [hsPairing_eq, LinearMap.trace_eq_sum_inner _ b, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]

/-- For a symmetric endomorphism `T`, the HS self-pairing reduces to the trace of `T ∘ₗ T`:
`re (hsPairing T T) = re (trace (T ∘ₗ T))`. The adjoint in the HS pairing collapses via
`IsSymmetric.adjoint_eq`. -/
theorem re_hsPairing_self_eq_re_trace_comp_self_of_isSymmetric
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    RCLike.re (T.hsPairing T) = RCLike.re (LinearMap.trace 𝕜 E (T ∘ₗ T)) := by
  rw [hsPairing_eq, hT.adjoint_eq]

/-- **HS-norm sub-multiplicativity** in the operator-norm sense: composing on the left by
`S` scales the HS norm of `T` by at most `‖S‖_op`. Stated in terms of the (real-valued,
non-negative) `re hsPairing _ _` form:
`re (hsPairing (S ∘ T) (S ∘ T)) ≤ ‖S‖_op² · re (hsPairing T T)`. -/
theorem re_hsPairing_self_comp_le {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    (S : F →ₗ[𝕜] G) (T : E →ₗ[𝕜] F) :
    RCLike.re ((S ∘ₗ T).hsPairing (S ∘ₗ T)) ≤
      ‖S.toContinuousLinearMap‖ ^ 2 * RCLike.re (T.hsPairing T) := by
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E) :=
    ⟨stdOrthonormalBasis 𝕜 E⟩
  rw [re_hsPairing_self_eq_sum_norm_sq _ b, re_hsPairing_self_eq_sum_norm_sq _ b,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [LinearMap.comp_apply]
  calc ‖S (T (b i))‖ ^ 2
      ≤ (‖S.toContinuousLinearMap‖ * ‖T (b i)‖) ^ 2 := by
        gcongr
        exact S.toContinuousLinearMap.le_opNorm _
    _ = ‖S.toContinuousLinearMap‖ ^ 2 * ‖T (b i)‖ ^ 2 := by ring

/-- **Cauchy–Schwarz inequality for the HS pairing.** The HS pairing satisfies the usual
inner-product Cauchy–Schwarz bound: `‖hsPairing T U‖² ≤ re (hsPairing T T) · re (hsPairing U U)`.
The right-hand side is the product of the (real-valued, non-negative) HS-norm squares
(`re_hsPairing_self_eq_sum_norm_sq`). Proof: expand the pairings on a basis, bound
`‖hsPairing T U‖` by `∑ ‖U (b i)‖ * ‖T (b i)‖` via the triangle inequality and per-term
`norm_inner_le_norm`, then apply the finset Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq`. -/
theorem norm_hsPairing_sq_le (T U : E →ₗ[𝕜] F) :
    ‖T.hsPairing U‖ ^ 2 ≤ RCLike.re (T.hsPairing T) * RCLike.re (U.hsPairing U) := by
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E) :=
    ⟨stdOrthonormalBasis 𝕜 E⟩
  have hTU_norm : ‖T.hsPairing U‖ ≤ ∑ i, ‖U (b i)‖ * ‖T (b i)‖ := by
    rw [hsPairing_eq, LinearMap.trace_eq_sum_inner _ b]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    exact norm_inner_le_norm _ _
  rw [re_hsPairing_self_eq_sum_norm_sq T b, re_hsPairing_self_eq_sum_norm_sq U b]
  calc ‖T.hsPairing U‖ ^ 2
      ≤ (∑ i, ‖U (b i)‖ * ‖T (b i)‖) ^ 2 := by gcongr
    _ ≤ (∑ i, ‖U (b i)‖ ^ 2) * (∑ i, ‖T (b i)‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, ‖T (b i)‖ ^ 2) * (∑ i, ‖U (b i)‖ ^ 2) := mul_comm _ _

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The HS pairing of two continuous linear maps, defined as the HS pairing of their
underlying linear maps. -/
noncomputable def hsPairing (T U : E →L[𝕜] F) : 𝕜 :=
  T.toLinearMap.hsPairing U.toLinearMap

@[simp]
theorem hsPairing_toLinearMap (T U : E →L[𝕜] F) :
    T.toLinearMap.hsPairing U.toLinearMap = T.hsPairing U := rfl

/-- CLM-level unfold of the HS pairing as a trace, sibling of `LinearMap.hsPairing_eq`. -/
theorem hsPairing_eq [CompleteSpace E] [CompleteSpace F] (T U : E →L[𝕜] F) :
    T.hsPairing U = LinearMap.trace 𝕜 E ((U.adjoint ∘L T : E →L[𝕜] E) : E →ₗ[𝕜] E) := rfl

@[simp]
theorem hsPairing_zero_left (U : E →L[𝕜] F) : hsPairing (0 : E →L[𝕜] F) U = 0 :=
  LinearMap.hsPairing_zero_left _

@[simp]
theorem hsPairing_zero_right (T : E →L[𝕜] F) : T.hsPairing 0 = 0 :=
  LinearMap.hsPairing_zero_right _

theorem hsPairing_add_left (T T' U : E →L[𝕜] F) :
    (T + T').hsPairing U = T.hsPairing U + T'.hsPairing U :=
  LinearMap.hsPairing_add_left _ _ _

theorem hsPairing_sub_left (T T' U : E →L[𝕜] F) :
    (T - T').hsPairing U = T.hsPairing U - T'.hsPairing U :=
  LinearMap.hsPairing_sub_left _ _ _

theorem hsPairing_neg_left (T U : E →L[𝕜] F) :
    (-T).hsPairing U = - T.hsPairing U :=
  LinearMap.hsPairing_neg_left _ _

theorem hsPairing_add_right (T U U' : E →L[𝕜] F) :
    T.hsPairing (U + U') = T.hsPairing U + T.hsPairing U' :=
  LinearMap.hsPairing_add_right _ _ _

theorem hsPairing_sub_right (T U U' : E →L[𝕜] F) :
    T.hsPairing (U - U') = T.hsPairing U - T.hsPairing U' :=
  LinearMap.hsPairing_sub_right _ _ _

theorem hsPairing_neg_right (T U : E →L[𝕜] F) :
    T.hsPairing (-U) = - T.hsPairing U :=
  LinearMap.hsPairing_neg_right _ _

theorem hsPairing_sum_left {ι : Type*} (s : Finset ι) (T : ι → E →L[𝕜] F)
    (U : E →L[𝕜] F) :
    (∑ i ∈ s, T i).hsPairing U = ∑ i ∈ s, (T i).hsPairing U := by
  simp only [← hsPairing_toLinearMap, ContinuousLinearMap.toLinearMap_sum,
    LinearMap.hsPairing_sum_left]

theorem hsPairing_sum_right {ι : Type*} (T : E →L[𝕜] F) (s : Finset ι)
    (U : ι → E →L[𝕜] F) :
    T.hsPairing (∑ i ∈ s, U i) = ∑ i ∈ s, T.hsPairing (U i) := by
  simp only [← hsPairing_toLinearMap, ContinuousLinearMap.toLinearMap_sum,
    LinearMap.hsPairing_sum_right]

theorem hsPairing_smul_left (c : 𝕜) (T U : E →L[𝕜] F) :
    (c • T).hsPairing U = c * T.hsPairing U :=
  LinearMap.hsPairing_smul_left _ _ _

theorem hsPairing_smul_right (c : 𝕜) (T U : E →L[𝕜] F) :
    T.hsPairing (c • U) = star c * T.hsPairing U :=
  LinearMap.hsPairing_smul_right _ _ _

theorem hsPairing_conj (T U : E →L[𝕜] F) :
    star (T.hsPairing U) = U.hsPairing T :=
  LinearMap.hsPairing_conj _ _

theorem hsPairing_self_star_eq_self (T : E →L[𝕜] F) :
    star (T.hsPairing T) = T.hsPairing T :=
  LinearMap.hsPairing_self_star_eq_self _

section MoveAdjoint
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- CLM sibling of `LinearMap.hsPairing_comp_left`. -/
theorem hsPairing_comp_left [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (T : E →L[𝕜] F) (S : F →L[𝕜] G) (W : E →L[𝕜] G) :
    (S ∘L T).hsPairing W = T.hsPairing (S.adjoint ∘L W) := by
  have hS : (S.adjoint : G →L[𝕜] F).toLinearMap = LinearMap.adjoint S.toLinearMap :=
    (ContinuousLinearMap.adjoint_toLinearMap S).symm
  simpa [← hsPairing_toLinearMap, coe_comp, hS]
    using LinearMap.hsPairing_comp_left T.toLinearMap S.toLinearMap W.toLinearMap

/-- CLM sibling of `LinearMap.hsPairing_comp_right`. -/
theorem hsPairing_comp_right [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (T : E →L[𝕜] F) (S : F →L[𝕜] G) (W : E →L[𝕜] G) :
    (S ∘L T).hsPairing W = S.hsPairing (W ∘L T.adjoint) := by
  have hT : (T.adjoint : F →L[𝕜] E).toLinearMap = LinearMap.adjoint T.toLinearMap :=
    (ContinuousLinearMap.adjoint_toLinearMap T).symm
  simpa [← hsPairing_toLinearMap, coe_comp, hT]
    using LinearMap.hsPairing_comp_right T.toLinearMap S.toLinearMap W.toLinearMap

end MoveAdjoint

/-- **Cauchy–Schwarz inequality for the HS pairing**, CLM sibling of
`LinearMap.norm_hsPairing_sq_le`. -/
theorem norm_hsPairing_sq_le (T U : E →L[𝕜] F) :
    ‖T.hsPairing U‖ ^ 2 ≤ RCLike.re (T.hsPairing T) * RCLike.re (U.hsPairing U) := by
  simpa using LinearMap.norm_hsPairing_sq_le T.toLinearMap U.toLinearMap

/-- The real part of the HS self-pairing `re ‖T‖²_HS` is nonnegative: it is a sum of squared
norms over an orthonormal basis (`LinearMap.re_hsPairing_self_eq_sum_norm_sq`). This is the
nonnegativity companion of `norm_hsPairing_sq_le`. -/
theorem re_hsPairing_self_nonneg (T : E →L[𝕜] F) : 0 ≤ RCLike.re (T.hsPairing T) := by
  rw [← hsPairing_toLinearMap,
    LinearMap.re_hsPairing_self_eq_sum_norm_sq _ (stdOrthonormalBasis 𝕜 E)]
  positivity

/-- **HS-norm sub-multiplicativity** in the operator-norm sense, CLM sibling of
`LinearMap.re_hsPairing_self_comp_le`. -/
theorem re_hsPairing_self_comp_le {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    RCLike.re ((S ∘L T).hsPairing (S ∘L T)) ≤ ‖S‖ ^ 2 * RCLike.re (T.hsPairing T) := by
  have h := LinearMap.re_hsPairing_self_comp_le S.toLinearMap T.toLinearMap
  rwa [ContinuousLinearMap.toLinearMap_toContinuousLinearMap,
      ← ContinuousLinearMap.toLinearMap_comp,
    hsPairing_toLinearMap, hsPairing_toLinearMap] at h

/-- CLM sibling of `LinearMap.re_hsPairing_self_eq_re_trace_comp_self_of_isSymmetric`: for a
self-adjoint operator `T`, `re (hsPairing T T) = re (trace (T * T))`. The CLM multiplication
`T * T : E →L[𝕜] E` coerces to `T.toLinearMap ∘ₗ T.toLinearMap`. -/
theorem re_hsPairing_self_eq_re_trace_sq_of_isSelfAdjoint [CompleteSpace E]
    {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    RCLike.re (T.hsPairing T) =
      RCLike.re (LinearMap.trace 𝕜 E ((T * T : E →L[𝕜] E) : E →ₗ[𝕜] E)) := by
  rw [← hsPairing_toLinearMap]
  exact (LinearMap.re_hsPairing_self_eq_re_trace_comp_self_of_isSymmetric hT.isSymmetric).trans
    rfl

end ContinuousLinearMap
