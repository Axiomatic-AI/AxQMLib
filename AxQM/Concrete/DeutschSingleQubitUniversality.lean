/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.EulerDecompositionOrthogonal
import AxQM.Concrete.AxisAngleGateValues
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Monoid

/-!
# Concrete: single-qubit universality from a dense `x`-axis and the phase gate `S` (N&C Ex 4.44)

Every statement is about `2 × 2` matrices — the rotations `rotX`/`rotY`, the phase gate `sMatrix`,
and the unitary group.

## Mathematical content (the single-qubit half of Nielsen & Chuang, Exercise 4.44)

Exercise 4.44 asks to show the three-qubit Deutsch gate `G = C²(iR_x(πα))` is universal whenever `α`
is irrational. Iterating `G` on the doubly-controlled subspace runs the orbit `(iR_x(πα))^k`, whose
`x`-rotation content is *dense* precisely when `α` is irrational (`rotX_mem_closure_cyclic_iRx`,
lifted to the physics gate in `Postulates/API/DeutschGateReachable.lean`). The `x`-rotations are a
single abelian axis, so they alone cannot give every single-qubit gate. The **second axis** comes
from the phase gate `S = diag(1, i)`: conjugating an `x`-rotation by `S` turns it into the
corresponding `y`-rotation (`sMatrix_mul_rotX_mul_conjTranspose`, `S R_x(β) S† = R_y(β)`). With a
dense `x`-axis *and* a dense `y`-axis — two *perpendicular* dense axes — every single-qubit unitary
becomes approximable, up to a global phase, exactly as in Exercise 4.43's `z`/`x` argument.

This file assembles that step, parameterised over an arbitrary submonoid `M` of gates (the
reachability facts — that `G` supplies a dense `x`-axis and the phase gate `S` — are the physics
input, discharged for the actual Deutsch-reachable submonoid separately):

* `sMatrix_mul_rotX_mul_conjTranspose` — **the second-axis mechanism**: `S R_x(β) S† = R_y(β)`.
* `exists_phase_smul_mem_closure_of_forall_rotX_rotY` — **single-qubit universality core**: if the
  closure of a gate submonoid `M` contains *every* `x`-rotation and *every* `y`-rotation, then for
  every single-qubit unitary `U` some global phase `e^{iα}` makes `e^{iα} U` a limit of members of
  `M`. Proved from the perpendicular-axis Euler decomposition
  `U = e^{iα} R_x(β) R_y(γ) R_x(δ)` (`exists_smul_rotAxis_triple_of_perp`, N&C Ex 4.11 corrected)
  and closure of a submonoid's topological closure under products.
* `exists_phase_smul_mem_closure_of_forall_rotX_sMatrix` — **the Deutsch specialisation**: a dense
  `x`-axis together with the phase gate `S` (and its adjoint `S†`) in the closure suffice — the
  `y`-rotations are recovered from `S R_x S† = R_y`. This is the single-qubit content of the Deutsch
  gate's universality: from `G` one obtains a dense set of `x`-rotations and the phase gate `S`.

The whole argument mirrors `Concrete/SingleQubitRotationUniversality.lean` (Exercise 4.43), with the
`z`-axis replaced by the `y`-axis supplied by `S`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The phase gate `S` conjugates an `x`-rotation into the corresponding `y`-rotation:**
`S · R_x(β) · S† = R_y(β)`, where `S = diag(1, i)` (`sMatrix`). This is the mechanism that supplies
the *second* rotation axis in the Deutsch gate's universality argument (Nielsen & Chuang,
Exercise 4.44): the `x`-rotations form one abelian axis, and conjugating them by `S` rotates that
axis to the perpendicular `y`-axis. Proved by the explicit `2 × 2` matrix computation
`diag(1,i) · R_x(β) · diag(1,-i) = R_y(β)`, using `i² = -1`. -/
theorem sMatrix_mul_rotX_mul_conjTranspose (β : ℝ) :
    sMatrix * rotX β * sMatrix.conjTranspose = rotY β := by
  have hSc : sMatrix.conjTranspose = !![1, 0; 0, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sMatrix, Matrix.conjTranspose_apply]
  rw [rotX_eq, rotY_eq, hSc, sMatrix, Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num [Complex.I_mul_I]
  refine ⟨?_, ?_, ?_⟩ <;> ring_nf <;> simp [Complex.I_sq]

/-- **The topological closure of a gate submonoid is closed under multiplication.** A convenience
wrapper around `Submonoid.top_closure_mul_self_subset` (the closure of a submonoid is a submonoid),
specialised to `2 × 2` matrices. -/
theorem mul_mem_closure_submonoid {M : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)}
    {a b : Matrix (Fin 2) (Fin 2) ℂ}
    (ha : a ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)))
    (hb : b ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ))) :
    a * b ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Submonoid.top_closure_mul_self_subset M (Set.mul_mem_mul ha hb)

/-- **Single-qubit universality up to a global phase, from two perpendicular dense axes** (the
single-qubit content of Nielsen & Chuang, Exercise 4.44). Let `M` be a submonoid of single-qubit
gates whose topological closure contains *every* `x`-rotation `R_x(β)` and *every* `y`-rotation
`R_y(γ)`. Then for every single-qubit unitary `U` some global phase `e^{iα}` makes `e^{iα} U` a
limit of members of `M`.

The `x̂` and `ŷ` axes are orthonormal, so the corrected generalized Euler decomposition
(`exists_smul_rotAxis_triple_of_perp`) writes `U = e^{iα₀} R_x(β) R_y(γ) R_x(δ)`; each factor lies
in the closure, whose closure-of-a-submonoid structure is closed under products
(`mul_mem_closure_submonoid`), so the phase-stripped `e^{-iα₀} U = R_x(β) R_y(γ) R_x(δ)` lies in the
closure, taking `α = -α₀`. -/
theorem exists_phase_smul_mem_closure_of_forall_rotX_rotY
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℂ))
    (hX : ∀ β : ℝ, rotX β ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)))
    (hY : ∀ γ : ℝ, rotY γ ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)))
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • U
      ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hm : (![0, 1, 0] : Fin 3 → ℝ) 0 ^ 2 + (![0, 1, 0] : Fin 3 → ℝ) 1 ^ 2
      + (![0, 1, 0] : Fin 3 → ℝ) 2 ^ 2 = 1 := by
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  have hn : (![1, 0, 0] : Fin 3 → ℝ) 0 ^ 2 + (![1, 0, 0] : Fin 3 → ℝ) 1 ^ 2
      + (![1, 0, 0] : Fin 3 → ℝ) 2 ^ 2 = 1 := by
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  have hperp : (![0, 1, 0] : Fin 3 → ℝ) 0 * (![1, 0, 0] : Fin 3 → ℝ) 0
      + (![0, 1, 0] : Fin 3 → ℝ) 1 * (![1, 0, 0] : Fin 3 → ℝ) 1
      + (![0, 1, 0] : Fin 3 → ℝ) 2 * (![1, 0, 0] : Fin 3 → ℝ) 2 = 0 := by
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  obtain ⟨a, β, γ, δ, hUeq⟩ := exists_smul_rotAxis_triple_of_perp hm hn hperp U hU
  refine ⟨-a, ?_⟩
  have hW : rotX β * rotY γ * rotX δ ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    mul_mem_closure_submonoid (mul_mem_closure_submonoid (hX β) (hY γ)) (hX δ)
  rw [hUeq, smul_smul, ← Complex.exp_add,
    show ((-a : ℝ) : ℂ) * Complex.I + (a : ℂ) * Complex.I = 0 by push_cast; ring,
    Complex.exp_zero, one_smul]
  exact hW

/-- **Single-qubit universality of the Deutsch gate set, up to a global phase** (Nielsen & Chuang,
Exercise 4.44, single-qubit content). Let `M` be a submonoid of single-qubit gates whose closure
contains *every* `x`-rotation `R_x(β)` together with the phase gate `S = diag(1, i)` (`sMatrix`)
and its adjoint `S†`. Then for every single-qubit unitary `U` some global phase `e^{iα}` makes
`e^{iα} U` a limit of members of `M`.

The `y`-rotations are not assumed: each `R_y(γ) = S R_x(γ) S†`
(`sMatrix_mul_rotX_mul_conjTranspose`) lies in the closure by `mul_mem_closure_submonoid`, so the
two-axis core `exists_phase_smul_mem_closure_of_forall_rotX_rotY` applies. This packages the exact
single-qubit gate set the Deutsch gate `G = C²(iR_x(πα))` reaches: a dense family of `x`-rotations
(from iterating `G`, `rotX_mem_closure_cyclic_iRx`) and the phase gate `S` (from the controlled
structure of `G`). -/
theorem exists_phase_smul_mem_closure_of_forall_rotX_sMatrix
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℂ))
    (hX : ∀ β : ℝ, rotX β ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)))
    (hS : sMatrix ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)))
    (hS' : sMatrix.conjTranspose ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)))
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • U
      ∈ closure (M : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine exists_phase_smul_mem_closure_of_forall_rotX_rotY M hX (fun γ => ?_) U hU
  rw [← sMatrix_mul_rotX_mul_conjTranspose]
  exact mul_mem_closure_submonoid (mul_mem_closure_submonoid hS (hX γ)) hS'

end AxQM.Concrete
