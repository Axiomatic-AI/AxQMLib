/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellBasis

/-!
# AxQM.Postulates.API — one-sided expectations on the Bell states

The **local (one-sided) expectation** `⟪E ⊗ I⟫` of an observable
`E` on the first qubit, in each of the four Bell states `bellState x y`
(`AxQM/Postulates/API/BellBasis.lean`). This is the operator-level core of Nielsen & Chuang
**Exercise 2.70** (whose statement is in `AxQM/NC/Ch2/Exercise2_70.lean`).

The identity observable `E ⊗ I` uses `Observable.id` (`AxQM/Postulates/API/Observable.lean`).

* `bellState_expectation_tmul_id` — for **any** observable `E` on the first qubit and any Bell
  state `|β_xy⟩`, the expectation `⟪E ⊗ I⟫_{β_xy}` equals `½(⟪0|E|0⟫ + ⟪1|E|1⟫)`, *independently*
  of the classical bits `x, y`. Since `⟪0|E|0⟫ + ⟪1|E|1⟫ = Tr E` (the sum of `E`'s diagonal
  matrix elements in the computational basis), this common value is `½ Tr E = Tr(E · I/2)` — the
  trace of `E` against the maximally mixed reduced state `I/2`, which is why the value is
  Bell-state-independent.

## Why the value is `½ Tr E`

Every Bell state `|β_xy⟩ = (|0,y⟩ + (-1)ˣ|1,ȳ⟩)/√2` has first-qubit labels `{0, 1}` on its two
summands and *orthogonal* second-qubit labels `{y, ȳ}` (`ȳ = y+1`), so in `⟪ψ,(E⊗I)ψ⟫` the two
off-diagonal terms vanish (second-qubit orthogonality) and the two diagonal terms give
`½(⟪0|E|0⟫ + ⟪1|E|1⟫)` regardless of `x, y` — the reduced state on the first qubit is `I/2` for
every Bell state.

The explicit-diagonal form `½(⟪0|E|0⟫ + ⟪1|E|1⟫)` is `½ Tr E`; it is used in place of
`½ LinearMap.trace …` to stay clear of the `qubit.space` / `EuclideanSpace` orthonormal-basis
defeq friction that `trace_eq_sum_inner` incurs.

## Proof design

Mirroring `bellBasisVec_inner` and Exercise 2.66's expectation computation: the normalising
`(√2)⁻¹` and the sign `(-1)ˣ` are pulled out through the *composite* `(E ⊗ I).op` (whose domain is
`(qubit ⊗ qubit).space`, matching the composite scalar action — `TensorProduct.mapL`'s raw domain
does not), and only then is `(E ⊗ I).op` rewritten to `TensorProduct.mapL E.op 1` so the
computational two-qubit inner products reduce via `qubitBasis_tmul_mapL_id_inner`. A four-way
`fin_cases x, y` discharges the sign and second-qubit-orthogonality bookkeeping.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- Matrix element of `E ⊗ I` between computational two-qubit vectors:
`⟨ab|(E ⊗ I)|cd⟩ = ⟨a|E|c⟩ · δ_{bd}`. The `I` on the second factor forces the second-qubit labels
to agree; the first factor contributes the single-qubit matrix element `⟨a|E|c⟩`. From
`TensorProduct.mapL_tmul` and single-qubit orthonormality (`qubitBasis_inner_qubitBasis`); the
`change` restates the composite inner product at the definitionally equal raw tensor inner so
`TensorProduct.inner_tmul` applies. -/
theorem qubitBasis_tmul_mapL_id_inner (E : Observable qubit) (a b c d : Fin 2) :
    inner ℂ ((qubitBasis a ⊗ qubitBasis b).vec)
      (TensorProduct.mapL E.op 1 ((qubitBasis c ⊗ qubitBasis d).vec))
      = inner ℂ (qubitBasis a).vec (E.op (qubitBasis c).vec) * (if b = d then (1 : ℂ) else 0) := by
  rw [PureState.tmul_vec, PureState.tmul_vec, TensorProduct.mapL_tmul,
    one_apply_eq_self]
  change inner ℂ ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      ((E.op (qubitBasis c).vec) ⊗ₜ[ℂ] (qubitBasis d).vec) = _
  rw [TensorProduct.inner_tmul ℂ, qubitBasis_inner_qubitBasis]

/-- The **one-sided matrix element of `E ⊗ I` on a Bell vector**:
`⟨β_xy|(E ⊗ I)|β_xy⟩ = ½(⟪0|E|0⟫ + ⟪1|E|1⟫) = ½ Tr E`, independently of `x, y`. The heart of
Exercise 2.70. -/
theorem bellBasisVec_inner_tmul_id (E : Observable qubit) (x y : Fin 2) :
    inner ℂ (bellBasisVec x y) ((E ⊗ Observable.id qubit).op (bellBasisVec x y))
      = 2⁻¹ * (inner ℂ (qubitBasis 0).vec (E.op (qubitBasis 0).vec)
        + inner ℂ (qubitBasis 1).vec (E.op (qubitBasis 1).vec)) := by
  simp only [bellBasisVec]
  rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    conj_sqrtTwoInv_mul_self, ContinuousLinearMap.map_add]
  simp only [ContinuousLinearMap.map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right]
  simp only [Observable.tmul_op, Observable.id_op]
  erw [qubitBasis_tmul_mapL_id_inner E 0 y 0 y, qubitBasis_tmul_mapL_id_inner E 0 y 1 (y + 1),
    qubitBasis_tmul_mapL_id_inner E 1 (y + 1) 0 y,
    qubitBasis_tmul_mapL_id_inner E 1 (y + 1) 1 (y + 1)]
  fin_cases x <;> fin_cases y <;> simp

/-- **Exercise 2.70, core computation.** For any observable `E` on the first qubit, the
expectation of `E ⊗ I` in the Bell state `|β_xy⟩` is `½(⟪0|E|0⟫ + ⟪1|E|1⟫) = ½ Tr E`, the *same*
value for every `x, y`. -/
theorem bellState_expectation_tmul_id (E : Observable qubit) (x y : Fin 2) :
    (bellState x y).expectation (E ⊗ Observable.id qubit)
      = (2⁻¹ * (inner ℂ (qubitBasis 0).vec (E.op (qubitBasis 0).vec)
        + inner ℂ (qubitBasis 1).vec (E.op (qubitBasis 1).vec))).re := by
  simp only [PureState.expectation, bellState_vec]
  exact congrArg Complex.re (bellBasisVec_inner_tmul_id E x y)

end AxQM
