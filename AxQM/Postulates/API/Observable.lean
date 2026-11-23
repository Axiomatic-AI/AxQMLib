/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Observable
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# AxQM.Postulates.API — bipartite observables and expectation bounds

Observables of a composite system.

* `Observable.tmul` (`A ⊗ B`) — the **tensor product of two observables**: the observable
  of `S ⊗ T` acting as `A` on the first factor and `B` on the second. It completes the
  `⊗` overload alongside `PureState.tmul` / `State.tmul` / `Evolution.tmul`,
  and grounds Nielsen–Chuang Exercise 2.30 (the tensor of Hermitian operators is Hermitian).
* `PureState.re_inner_apply_le_of_le_smul_one` — the **operator-order → expectation bridge**,
  raw-operator form: if `M ≤ c • 1` in the operator (Loewner) order, then `Re ⟪ψ, M ψ⟫ ≤ c` in
  every normalized pure state. The general statement (a raw operator, not a bundled
  `Observable`), so an operator bound on a *sum* of observables descends without repackaging.
  This is the mechanism by which a C*-algebraic operator bound (e.g. Tsirelson's
  `tsirelson_inequality`) descends to a bound on measured expectation values.
* `PureState.expectation_le_of_op_le_smul_one` — the `Observable`-bundled corollary: if
  `A.op ≤ c • 1` then `⟪A⟫_ψ ≤ c`, i.e. the raw lemma at `M := A.op`.

-/

open scoped InnerProductSpace TensorProduct ComplexOrder

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Tensor product of observables** `A ⊗ B`: the observable of the composite system
`S ⊗ T` that measures `A` on the first factor and `B` on the second. It is self-adjoint
because the tensor product of self-adjoint operators is self-adjoint
(`IsSelfAdjoint.tensorMapL`). This is the observable analogue of `State.tmul` /
`Evolution.tmul`, and grounds Nielsen–Chuang Exercise 2.30 (the tensor of Hermitian
operators is Hermitian). -/
def Observable.tmul (A : Observable S) (B : Observable T) : Observable (S ⊗ T) where
  op := TensorProduct.mapL A.op B.op
  selfAdjoint := IsSelfAdjoint.tensorMapL A.selfAdjoint B.selfAdjoint

@[inherit_doc] scoped infixr:70 " ⊗ " => Observable.tmul

@[simp]
theorem Observable.tmul_op (A : Observable S) (B : Observable T) :
    (A ⊗ B).op = TensorProduct.mapL A.op B.op := rfl

/-- **Action of a tensor observable on a pure tensor:** `(A ⊗ B)(a ⊗ b) = A a ⊗ B b`. Definitional
(`Observable.tmul_op` + `TensorProduct.mapL_tmul`), the observable analogue of
`Evolution.tmul_op_tmul`. -/
theorem Observable.tmul_op_tmul (A : Observable S) (B : Observable T) (a : S.space) (b : T.space) :
    (A ⊗ B).op (a ⊗ₜ[ℂ] b) = A.op a ⊗ₜ[ℂ] B.op b :=
  TensorProduct.mapL_tmul A.op B.op a b

/-- **The tensor of two involutive observables is involutive:** if `A.op² = I` and `B.op² = I` then
`(A ⊗ B).op² = I`. Since `(A ⊗ B).op = mapL A.op B.op` and `mapL` is multiplicative
(`TensorProduct.mapL_mul`), `(A ⊗ B).op² = mapL (A.op²) (B.op²) = mapL 1 1 = 1`. A reusable bridge:
a product `±1` observable built by tensoring sign observables is again a `±1` observable (used for
the Shor-code syndrome observables and the first-qubit `X ⊗ I` / `Z ⊗ I` measurements of the
EPR-collapse item). -/
theorem Observable.tmul_op_mul_self {A : Observable S} {B : Observable T}
    (hA : A.op * A.op = 1) (hB : B.op * B.op = 1) :
    (A ⊗ B).op * (A ⊗ B).op = 1 := by
  change TensorProduct.mapL A.op B.op * TensorProduct.mapL A.op B.op = 1
  rw [← TensorProduct.mapL_mul A.op A.op B.op B.op, hA, hB, TensorProduct.mapL_one]

/-- **The identity observable** `I` on a system `S`: the identity operator, self-adjoint. Its
expectation in any state is `1`; it is the trivial effect used to embed a single-factor observable
into a composite as `E ⊗ I` (e.g. Nielsen–Chuang Exercise 2.70). A derived observable, sibling of
`Observable.tmul`. -/
def Observable.id (S : QSystem) : Observable S where
  op := 1
  selfAdjoint := IsSelfAdjoint.one _

@[simp] theorem Observable.id_op (S : QSystem) : (Observable.id S).op = 1 := rfl

/-- **Raw-operator form of the operator-order → expectation bridge.** If a raw operator `M` is
bounded above by `c • 1` in the operator (Loewner) order on `S →L[ℂ] S` — with the real scalar
`c` acting through the `ℝ`-action on the operator algebra — then `Re ⟪ψ, M ψ⟫ ≤ c` for every
normalized pure state `ψ`.

The difference `(c : ℂ) • 1 - M` is a positive operator (`nonneg_iff_isPositive`), so
`0 ≤ ⟪ψ, ((c : ℂ) • 1 - M) ψ⟫`; taking real parts and using `‖ψ‖ = 1` gives the bound. This is
the general operator statement: it takes a *raw* operator rather than a bundled `Observable`, so
an operator bound on a **sum** of observables (e.g. the CHSH operator, or the `√2³ • 1` output of
Tsirelson's inequality) descends to a bound on the sum of expectation values without first
repackaging that sum as a single `Observable`. The `Observable`-bundled bridge
`PureState.expectation_le_of_op_le_smul_one` is the corollary at `M := A.op`. -/
theorem PureState.re_inner_apply_le_of_le_smul_one (ψ : PureState S) {M : S →L[ℂ] S} {c : ℝ}
    (h : M ≤ c • (1 : S →L[ℂ] S)) : (inner ℂ ψ.vec (M ψ.vec)).re ≤ c := by
  rw [← Complex.coe_smul] at h
  have hpos : ((c : ℂ) • (1 : S →L[ℂ] S) - M).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mp (sub_nonneg.mpr h)
  have key : 0 ≤ inner ℂ ψ.vec (((c : ℂ) • (1 : S →L[ℂ] S) - M) ψ.vec) :=
    hpos.inner_nonneg_right ψ.vec
  have hnorm : inner ℂ ψ.vec ψ.vec = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ψ.normalized]; norm_num
  rw [sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_right, inner_smul_right, hnorm, mul_one] at key
  -- key : (0 : ℂ) ≤ ↑c - ⟪ψ.vec, M ψ.vec⟫  (ComplexOrder)
  have hre := (Complex.le_def.mp key).1
  simp only [Complex.zero_re, Complex.sub_re, Complex.ofReal_re] at hre
  -- hre : 0 ≤ c - (⟪ψ.vec, M ψ.vec⟫).re
  linarith

/-- **Operator-order → expectation bridge.** If an observable `A` is bounded above by
`c • 1` in the operator (Loewner) order — `A.op ≤ c • 1` in the `StarOrderedRing` order on
`S →L[ℂ] S` — then its expectation value in any pure state `ψ` is at most `c`. This lets an
operator inequality proved in the C*-algebra `S →L[ℂ] S` (such as Tsirelson's bound) be read off
as a bound on the measured expectation value.

The `Observable`-bundled corollary of `PureState.re_inner_apply_le_of_le_smul_one` at `M := A.op`
(after unfolding `expectation` to `Re ⟪ψ, A.op ψ⟫`). The scalar is written `(c : ℂ) • 1` (rather
than `c • 1` over `ℝ`) so the operator lives in the ambient complex algebra without extra
real-scalar-tower bookkeeping; `Complex.coe_smul` bridges it to the general
lemma's `ℝ`-smul hypothesis. -/
theorem PureState.expectation_le_of_op_le_smul_one (ψ : PureState S) (A : Observable S)
    {c : ℝ} (h : A.op ≤ (c : ℂ) • (1 : S →L[ℂ] S)) :
    ψ.expectation A ≤ c := by
  rw [Complex.coe_smul] at h
  rw [PureState.expectation]
  exact ψ.re_inner_apply_le_of_le_smul_one h

end AxQM
