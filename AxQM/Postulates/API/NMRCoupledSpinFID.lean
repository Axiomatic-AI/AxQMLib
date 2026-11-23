/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.InvolutionPropagatorConjugation
import AxQM.Postulates.API.Observable
import AxQM.Postulates.API.Qubit

/-!
# AxQM.Postulates.API — the J-coupled NMR readout operator (Nielsen & Chuang §7.7)

The **transverse magnetization readout operator** of a two-spin, `J`-coupled NMR system and its
**Heisenberg evolution** — the algebraic core of the free-induction-decay computation of
Nielsen & Chuang Exercise 7.37.

The coupling Hamiltonian is `H = J Z₁Z₂` (`couplingZZHamiltonian`), whose operator `J • (Z ⊗ Z)`
is a scalar multiple of the **involution** `G = Z ⊗ Z` (`G² = 1`). The pickup coil reads out the
spin-1 transverse magnetization through the *non-Hermitian* operator `i X₁ + Y₁`
(`nmrTransverseReadout`, the `k = 1` case of the readout `i Xₖ + Yₖ` of N&C eq. 7.143). Since it
**anticommutes** with `G`, the reusable involution-Heisenberg lemma
`Observable.propagator_conj_op_anticomm` (this directory's `InvolutionPropagatorConjugation`)
gives the Heisenberg-evolved readout in closed form:

* `nmrReadout_heisenberg` —
  `U(t)† (i X₁ + Y₁) U(t) = (i X₁ + Y₁) · (cos(2Jt) • 1 − (sin(2Jt) i) • Z₂)`,

the raising-type operator `i X₁ + Y₁` picking up the neighbour phase `e^{-2iJ Z₂ t}` at **twice**
the coupling frequency. (Since `i X₁ + Y₁` absorbs its own `Z₁` — `(i X + Y) Z = i X + Y` — the
coupling generator `G = Z₁Z₂` collapses to the neighbour operator `Z₂`.) Expanded, this reads
`cos(2Jt) (i X₁ + Y₁) + sin(2Jt) (X₁ − i Y₁) Z₂`: the `J`-coupled precession that turns the
spin-1 magnetization into a spectral **doublet** at `±2J`.

## Design

* **Proof.** No matrix trigonometry: `Observable.propagator_conj_op_anticomm` supplies the
  `cos(2ct)A − i sin(2ct)(A·G)` normal form for the whole readout `A = i X₁ + Y₁` at once (it
  anticommutes with `G`), and the single operator identity `(i X₁ + Y₁) · G = (i X₁ + Y₁) · Z₂`
  collapses the `G`-part to the neighbour operator `Z₂`. The single-qubit Pauli input is only the
  shared `AxQM/Postulates/API/Qubit.lean` lemmas — the anticommutators `{X, Z} = {Y, Z} = 0` and the
  raising identity `i (X Z) + Y Z = i X + Y` (both lifted to operators through the `⋆`-algebra map
  `Matrix.toEuclideanCLM`) — assembled here into the composite (`TensorProduct.mapL`) statements.
-/

open scoped ComplexOrder

noncomputable section

namespace AxQM

/-! ### The J-coupling Hamiltonian and its involution generator

The single-qubit Pauli operator facts this file builds on — `Z² = 1`
(`pauliZObservable_op_mul_self`), the anticommutators `{X, Z} = {Y, Z} = 0`
(`pauliXObservable_op_anticomm_pauliZObservable_op` / `…Y…`), and the raising-operator absorption
`i (X Z) + Y Z = i X + Y` (`pauliRaising_op_mul_pauliZObservable_op`) — are the generic shared
lemmas of `AxQM/Postulates/API/Qubit.lean`. -/

variable (J : ℝ)

/-- The **two-spin `J`-coupling Hamiltonian** `H = J Z₁Z₂` of Nielsen & Chuang §7.7, as an
`Observable` on the two-qubit system whose operator is `J • (Z ⊗ Z)` — a real scalar multiple of
the `Z ⊗ Z` observable, the NMR Ising/`ZZ` coupling between two spins with coupling constant `J`. -/
def couplingZZHamiltonian : Observable (qubit.compose qubit) where
  op := (J : ℂ) • (pauliZObservable.tmul pauliZObservable).op
  selfAdjoint :=
    ((Complex.im_eq_zero_iff_isSelfAdjoint _).mp rfl).smul
      (pauliZObservable.tmul pauliZObservable).selfAdjoint

@[simp]
theorem couplingZZHamiltonian_op :
    (couplingZZHamiltonian J).op = (J : ℂ) • (pauliZObservable.tmul pauliZObservable).op :=
  rfl

/-- The generator `G = Z ⊗ Z` of the `J`-coupling Hamiltonian is an **involution**: `G² = 1`,
because `Z² = 1` on each factor. -/
theorem pauliZZ_op_mul_self :
    (pauliZObservable.tmul pauliZObservable).op * (pauliZObservable.tmul pauliZObservable).op
      = 1 := by
  -- Prove the identity in the raw tensor operator ring (where the `mapL` lemmas apply directly),
  -- then transport it to the goal by defeq (`(A ⊗ B).op ≡ mapL A.op B.op`).
  have H : TensorProduct.mapL pauliZObservable.op pauliZObservable.op
        * TensorProduct.mapL pauliZObservable.op pauliZObservable.op = 1 := by
    rw [← TensorProduct.mapL_mul, pauliZObservable_op_mul_self, TensorProduct.mapL_one]
  exact H

/-! ### The transverse magnetization readout and its Heisenberg evolution -/

/-- The **spin-1 transverse magnetization readout** operator `i X₁ + Y₁` (`X₁ = X ⊗ 1`,
`Y₁ = Y ⊗ 1`) — the `k = 1` case of the non-Hermitian pickup operator `i Xₖ + Yₖ` of the
free-induction-decay signal `V(t)` (Nielsen & Chuang eq. 7.143). -/
def nmrTransverseReadout : (qubit.compose qubit).space →L[ℂ] (qubit.compose qubit).space :=
  Complex.I • (pauliXObservable.tmul (Observable.id qubit)).op
    + (pauliYObservable.tmul (Observable.id qubit)).op

/-- The readout operator `i X₁ + Y₁` **anticommutes** with the coupling generator `G = Z ⊗ Z`
(both `X₁` and `Y₁` anticommute with `G`, `1` on the second factor commuting with `Z`). -/
theorem nmrTransverseReadout_anticomm_pauliZZ :
    nmrTransverseReadout * (pauliZObservable.tmul pauliZObservable).op
      = -((pauliZObservable.tmul pauliZObservable).op * nmrTransverseReadout) := by
  -- Per-factor anticommutation, in the raw tensor operator ring.
  have hX : TensorProduct.mapL pauliXObservable.op 1
        * TensorProduct.mapL pauliZObservable.op pauliZObservable.op
      = -(TensorProduct.mapL pauliZObservable.op pauliZObservable.op
          * TensorProduct.mapL pauliXObservable.op 1) := by
    rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, one_mul, mul_one,
      ← TensorProduct.mapL_neg_left, pauliXObservable_op_anticomm_pauliZObservable_op]
  have hY : TensorProduct.mapL pauliYObservable.op 1
        * TensorProduct.mapL pauliZObservable.op pauliZObservable.op
      = -(TensorProduct.mapL pauliZObservable.op pauliZObservable.op
          * TensorProduct.mapL pauliYObservable.op 1) := by
    rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, one_mul, mul_one,
      ← TensorProduct.mapL_neg_left, pauliYObservable_op_anticomm_pauliZObservable_op]
  -- Assemble `i X₁ + Y₁` in the raw ring, then transport to the goal by defeq.
  have H : (Complex.I • TensorProduct.mapL pauliXObservable.op 1
          + TensorProduct.mapL pauliYObservable.op 1)
        * TensorProduct.mapL pauliZObservable.op pauliZObservable.op
      = -(TensorProduct.mapL pauliZObservable.op pauliZObservable.op
        * (Complex.I • TensorProduct.mapL pauliXObservable.op 1
          + TensorProduct.mapL pauliYObservable.op 1)) := by
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hX, hY, smul_neg, ← neg_add]
  exact H

/-- **The readout absorbs the coupling into the neighbour: `(i X₁ + Y₁) G = (i X₁ + Y₁) Z₂`.**
Right-multiplying the raising-type readout by the coupling generator `G = Z₁Z₂` reduces to right
multiplication by the neighbour operator `Z₂ = 1 ⊗ Z`, because `i X + Y` absorbs its own `Z₁`
(`pauliRaising_op_mul_pauliZObservable_op`). -/
theorem nmrTransverseReadout_mul_pauliZZ :
    nmrTransverseReadout * (pauliZObservable.tmul pauliZObservable).op
      = nmrTransverseReadout * ((Observable.id qubit).tmul pauliZObservable).op := by
  -- Both sides reduce to `((i X + Y) L) ⊗ Z` in the raw tensor ring: with `L = Z` (the coupling)
  -- and `L = 1` (the neighbour), and `(i X + Y) Z = i X + Y`, they coincide.
  have H : (Complex.I • TensorProduct.mapL pauliXObservable.op 1
          + TensorProduct.mapL pauliYObservable.op 1)
        * TensorProduct.mapL pauliZObservable.op pauliZObservable.op
      = (Complex.I • TensorProduct.mapL pauliXObservable.op 1
          + TensorProduct.mapL pauliYObservable.op 1)
        * TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) pauliZObservable.op := by
    simp only [add_mul, smul_mul_assoc, ← TensorProduct.mapL_mul, one_mul, mul_one,
      ← TensorProduct.mapL_smul_left, ← TensorProduct.mapL_add_left,
      pauliRaising_op_mul_pauliZObservable_op]
  exact H

/-- **Heisenberg evolution of the transverse magnetization readout (N&C Ex 7.37, `H = J Z₁Z₂`).**
Under the `J`-coupling propagator `U(t) = exp(-i J Z₁Z₂ t)`, the readout operator `i X₁ + Y₁`
evolves in the Heisenberg picture to

`U(t)† (i X₁ + Y₁) U(t) = (i X₁ + Y₁) · (cos(2Jt) • 1 − (sin(2Jt) i) • Z₂)`,

i.e. the raising-type readout precesses at **twice** the coupling frequency, `i X₁ + Y₁`
acquiring the neighbour phase `cos(2Jt) − i sin(2Jt) Z₂ = e^{-2iJ Z₂ t}`. Proof: `i X₁ + Y₁`
anticommutes with the involution `G = Z ⊗ Z`, so `Observable.propagator_conj_op_anticomm` gives
`cos(2Jt)(i X₁+Y₁) − (sin(2Jt) i)((i X₁+Y₁) G)`, and `(i X₁+Y₁) G = (i X₁+Y₁) Z₂`
(`nmrTransverseReadout_mul_pauliZZ`) collapses the coupling to the neighbour `Z₂`. -/
theorem nmrReadout_heisenberg (t : ℝ) :
    ContinuousLinearMap.adjoint ((couplingZZHamiltonian J).propagator 1 0 t).op
        * nmrTransverseReadout * ((couplingZZHamiltonian J).propagator 1 0 t).op
      = nmrTransverseReadout
        * ((Real.cos (2 * J * t) : ℂ)
            • (1 : (qubit.compose qubit).space →L[ℂ] (qubit.compose qubit).space)
          - ((Real.sin (2 * J * t) : ℂ) * Complex.I)
            • ((Observable.id qubit).tmul pauliZObservable).op) := by
  have hconj := (couplingZZHamiltonian J).propagator_conj_op_anticomm
    (couplingZZHamiltonian_op J) pauliZZ_op_mul_self
    (pauliZObservable.tmul pauliZObservable).selfAdjoint
    nmrTransverseReadout_anticomm_pauliZZ t
  rw [hconj, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, nmrTransverseReadout_mul_pauliZZ]

end AxQM
