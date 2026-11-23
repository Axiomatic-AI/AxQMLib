/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qubit
import AxQM.Concrete.PauliEigenvectors
import AxQM.Concrete.PlusStateTensorPower
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# AxQM.Postulates.API — the `|±⟩` states and relative-phase equivalence in a basis

The `|±⟩` states and relative-phase equivalence for **Nielsen & Chuang, Exercise 2.65**
(§2.2.7, *Phase*, p. 93). The exercise asks to express `|+⟩ = (|0⟩ + |1⟩)/√2` and
`|-⟩ = (|0⟩ - |1⟩)/√2` in a basis in which they are *not* the same up to a relative phase shift.

## Relative phase, following N&C §2.2.7

Two complex amplitudes `a` and `b` **differ by a relative phase** if `a = exp(iθ) b` for some
real `θ`. Two *states* differ by a relative phase *in a basis* if each amplitude of one, in that
basis, is `exp(iθ)` times the corresponding amplitude of the other — crucially, the phase `θ`
**may vary from amplitude to amplitude** (this is what distinguishes a *relative* phase from a
*global* one, and makes it a basis-dependent notion). We model a "basis" physically as a family of
pure states `e : ι → PureState S` (intended to be an orthonormal basis), and the amplitude of a
state `ψ` in direction `e i` as the inner product `⟪(e i).vec, ψ.vec⟫`.

* `PureState.RelativePhaseEquiv e ψ φ` — the predicate that `ψ` and `φ` differ by a relative phase
  in the frame `e`: `∀ i, ∃ θ : ℝ, ⟪(e i).vec, ψ.vec⟫ = exp(iθ) • ⟪(e i).vec, φ.vec⟫`.
* `PureState.RelativePhaseEquiv.norm_inner_eq` — its physical fingerprint: relative-phase-equivalent
  states have **identical amplitude magnitudes** in every direction of the frame
  (`|exp(iθ)| = 1`). This is the lever that certifies a basis where the equivalence *fails*.

## The `|±⟩` states

* `qubitPlus`, `qubitMinus : PureState qubit` — the `X`-eigenstates `|±⟩ = (|0⟩ ± |1⟩)/√2`, built
  on the concrete unit vectors `Concrete.xPlus`/`Concrete.xMinus`.
* Amplitude lemmas: `inner_qubitBasis_qubitPlus`/`_qubitMinus` give the computational-basis
  amplitudes (`⟨i|±⟩ = (xPlus/xMinus) i`), and `inner_qubitPlus_self`/`inner_qubitPlus_qubitMinus`
  record that `{|+⟩, |-⟩}` is an **orthonormal** pair (`⟨+|+⟩ = 1`, `⟨+|-⟩ = 0`) — hence a genuine
  basis of the qubit, the basis used as N&C's answer.

## Design notes

* **Basis as a family of pure states.** Representing the basis as `ι → PureState S` (rather than a
  Mathlib `OrthonormalBasis` of the underlying space `↑S`) lets the statements in
  `AxQM/NC/Ch2/Exercise2_65.lean` mention only `PureState` and this predicate. It is also the more
  physical reading of "a basis of states". The two theorems of Exercise 2.65, stated with
  `RelativePhaseEquiv`, are in `AxQM/NC/Ch2/Exercise2_65.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-! ### Relative-phase equivalence in a frame -/

/-- Two pure states `ψ`, `φ` of a system `S` **differ by a relative phase in the frame `e`** (a
family of pure states, intended to be an orthonormal basis) if each amplitude of `ψ` equals
`exp(iθ)` times the corresponding amplitude of `φ`, for some real phase `θ` that may depend on the
index. This is Nielsen & Chuang's basis-dependent notion of relative phase (§2.2.7): the amplitude
of a state in direction `e i` is the inner product `⟪(e i).vec, ·.vec⟫`, and the phase `θ` is
allowed to vary from index to index. -/
def PureState.RelativePhaseEquiv {S : QSystem} {ι : Type*} (e : ι → PureState S)
    (ψ φ : PureState S) : Prop :=
  ∀ i, ∃ θ : ℝ, ⟪(e i).vec, ψ.vec⟫_ℂ = Complex.exp ((θ : ℂ) * Complex.I) • ⟪(e i).vec, φ.vec⟫_ℂ

/-- **Relative-phase-equivalent states have equal amplitude magnitudes.** If `ψ` and `φ` differ by
a relative phase in the frame `e`, then in every direction `e i` the magnitudes of their amplitudes
coincide, `‖⟪(e i).vec, ψ.vec⟫‖ = ‖⟪(e i).vec, φ.vec⟫‖`, because the relating factor `exp(iθ)` is a
unit complex number. This is the physical fingerprint of relative phase, and the lever used to
exhibit a basis in which two states are *not* relative-phase equivalent. -/
theorem PureState.RelativePhaseEquiv.norm_inner_eq {S : QSystem} {ι : Type*}
    {e : ι → PureState S} {ψ φ : PureState S} (h : PureState.RelativePhaseEquiv e ψ φ) (i : ι) :
    ‖⟪(e i).vec, ψ.vec⟫_ℂ‖ = ‖⟪(e i).vec, φ.vec⟫_ℂ‖ := by
  obtain ⟨θ, hθ⟩ := h i
  rw [hθ, smul_eq_mul, norm_mul, Complex.norm_exp]
  simp

/-- **A single phase factor on the vectors gives relative-phase equivalence in every frame.** If
`ψ.vec = e^{iθ} φ.vec` (the two pure states differ by one *global* phase), then
`RelativePhaseEquiv e ψ φ` holds for *any* family `e`: each amplitude `⟪(e i).vec, ψ.vec⟫` is
`e^{iθ}` times `⟪(e i).vec, φ.vec⟫`, with the same `θ` for every index. The bridge used to lift a
global-phase identity on state vectors to a `RelativePhaseEquiv` statement. -/
theorem PureState.relativePhaseEquiv_of_vec_eq_smul {S : QSystem} {ι : Type*}
    (e : ι → PureState S) {ψ φ : PureState S} (θ : ℝ)
    (h : ψ.vec = Complex.exp ((θ : ℂ) * Complex.I) • φ.vec) :
    PureState.RelativePhaseEquiv e ψ φ :=
  fun i => ⟨θ, by rw [h, inner_smul_right, smul_eq_mul]⟩

/-! ### The `|±⟩` states -/

/-- The **`X`-eigenstate `|+⟩ = (|0⟩ + |1⟩)/√2`** as a pure state of the qubit, built on the
concrete unit vector `Concrete.xPlus = (1/√2, 1/√2)`. -/
def qubitPlus : PureState qubit where
  vec := WithLp.toLp 2 Concrete.xPlus
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.xPlus : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.xPlus_apply, Fin.sum_univ_two, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

/-- The **`X`-eigenstate `|-⟩ = (|0⟩ - |1⟩)/√2`** as a pure state of the qubit, built on the
concrete unit vector `Concrete.xMinus = (1/√2, -1/√2)`. -/
def qubitMinus : PureState qubit where
  vec := WithLp.toLp 2 Concrete.xMinus
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.xMinus : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.xMinus, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, norm_neg, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

@[simp] theorem qubitPlus_vec : qubitPlus.vec = WithLp.toLp 2 Concrete.xPlus := rfl

@[simp] theorem qubitMinus_vec : qubitMinus.vec = WithLp.toLp 2 Concrete.xMinus := rfl

/-! ### The `|±i⟩` states -/

/-- The **`Y`-eigenstate `|+i⟩ = (|0⟩ + i|1⟩)/√2`** as a pure state of the qubit, built on the
concrete unit vector `Concrete.yPlus = (1/√2, i/√2)`. The `Y`-analogue of `qubitPlus`; no canonical
`|±i⟩` pure state existed in the library before. -/
def qubitPlusI : PureState qubit where
  vec := WithLp.toLp 2 Concrete.yPlus
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.yPlus : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.yPlus, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        norm_mul, Complex.norm_I, mul_one, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

/-- The **`Y`-eigenstate `|-i⟩ = (|0⟩ - i|1⟩)/√2`** as a pure state of the qubit, built on the
concrete unit vector `Concrete.yMinus = (1/√2, -i/√2)`. The `Y`-analogue of `qubitMinus`. -/
def qubitMinusI : PureState qubit where
  vec := WithLp.toLp 2 Concrete.yMinus
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.yMinus : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.yMinus, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        norm_neg, norm_mul, Complex.norm_I, mul_one, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

@[simp] theorem qubitPlusI_vec : qubitPlusI.vec = WithLp.toLp 2 Concrete.yPlus := rfl

@[simp] theorem qubitMinusI_vec : qubitMinusI.vec = WithLp.toLp 2 Concrete.yMinus := rfl

/-- The `|+⟩` state expanded in the computational basis: `|+⟩ = (1/√2)(|0⟩ + |1⟩)`, i.e.
`qubitPlus.vec = invSqrt2 • (|0⟩ + |1⟩)`. Lifts the concrete `Concrete.xPlus_eq_smul_add`
(`xPlus = invSqrt2 • (ket 0 + ket 1)`) to the vector of the `PureState`, `WithLp.toLp` carrying
`ket i` to `EuclideanSpace.single i 1 = (qubitBasis i).vec` definitionally. -/
theorem qubitPlus_vec_eq_smul_add :
    qubitPlus.vec = Concrete.invSqrt2 • ((qubitBasis 0).vec + (qubitBasis 1).vec) := by
  rw [qubitPlus_vec, Concrete.xPlus_eq_smul_add]
  rfl

/-- The `|-⟩` state expanded in the computational basis: `|-⟩ = (1/√2)(|0⟩ - |1⟩)`, i.e.
`qubitMinus.vec = invSqrt2 • (|0⟩ - |1⟩)`. Lifts the concrete `Concrete.xMinus_eq_smul_sub`
(`xMinus = invSqrt2 • (ket 0 - ket 1)`) to the vector of the `PureState`, the sign-flipped
companion of `qubitPlus_vec_eq_smul_add`. -/
theorem qubitMinus_vec_eq_smul_sub :
    qubitMinus.vec = Concrete.invSqrt2 • ((qubitBasis 0).vec - (qubitBasis 1).vec) := by
  rw [qubitMinus_vec, Concrete.xMinus_eq_smul_sub]
  rfl

/-- `|-⟩` written with an explicit `(-1)`-scaled `|1⟩` branch:
`|-⟩ = (1/√2)(|0⟩ + (-1)|1⟩)`. The additive companion of `qubitMinus_vec_eq_smul_sub`, giving
`|-⟩` the same uniform `(1/√2)(|0⟩ + s|1⟩)` shape (`s = -1`) as `qubitPlus_vec_eq_smul_add` gives
`|+⟩` (`s = +1`). -/
theorem qubitMinus_vec_eq_smul_add :
    qubitMinus.vec = Concrete.invSqrt2 • ((qubitBasis 0).vec + (-1 : ℂ) • (qubitBasis 1).vec) := by
  rw [qubitMinus_vec_eq_smul_sub, sub_eq_add_neg, ← neg_one_smul ℂ]

/-! ### Amplitudes of `|±⟩` -/

/-- The computational-basis amplitude of `|+⟩`: `⟨i|+⟩ = (xPlus) i = 1/√2` for each `i`. -/
theorem inner_qubitBasis_qubitPlus (i : Fin 2) :
    ⟪(qubitBasis i).vec, qubitPlus.vec⟫_ℂ = Concrete.xPlus i := by
  change ⟪(EuclideanSpace.single i 1 : EuclideanSpace ℂ (Fin 2)),
    WithLp.toLp 2 Concrete.xPlus⟫_ℂ = Concrete.xPlus i
  rw [EuclideanSpace.inner_single_left]
  simp

/-- The computational-basis amplitude of `|-⟩`: `⟨i|-⟩ = (xMinus) i`, which is `1/√2` at `i = 0`
and `-1/√2` at `i = 1` (the sign flip N&C highlights). -/
theorem inner_qubitBasis_qubitMinus (i : Fin 2) :
    ⟪(qubitBasis i).vec, qubitMinus.vec⟫_ℂ = Concrete.xMinus i := by
  change ⟪(EuclideanSpace.single i 1 : EuclideanSpace ℂ (Fin 2)),
    WithLp.toLp 2 Concrete.xMinus⟫_ℂ = Concrete.xMinus i
  rw [EuclideanSpace.inner_single_left]
  simp

/-- `⟨+|+⟩ = 1`: the amplitude of `|+⟩` on itself is `1`. Together with `inner_qubitPlus_qubitMinus`
this certifies that `{|+⟩, |-⟩}` is an orthonormal pair, hence a basis of the qubit. -/
theorem inner_qubitPlus_self : ⟪qubitPlus.vec, qubitPlus.vec⟫_ℂ = 1 := by
  change ⟪(WithLp.toLp 2 Concrete.xPlus : EuclideanSpace ℂ (Fin 2)),
    WithLp.toLp 2 Concrete.xPlus⟫_ℂ = 1
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simpa using Concrete.xPlus_dotProduct_self

/-- `⟨+|-⟩ = 0`: `|+⟩` and `|-⟩` are orthogonal — the amplitude of `|-⟩` on `|+⟩` vanishes. -/
theorem inner_qubitPlus_qubitMinus : ⟪qubitPlus.vec, qubitMinus.vec⟫_ℂ = 0 := by
  change ⟪(WithLp.toLp 2 Concrete.xPlus : EuclideanSpace ℂ (Fin 2)),
    WithLp.toLp 2 Concrete.xMinus⟫_ℂ = 0
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simpa using Concrete.xPlus_dotProduct_xMinus

end AxQM
