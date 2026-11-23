/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CNOTDensityMatrix
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.HadamardGate

/-!
# AxQM.Postulates.API — CNOT in the `X` (`|±⟩`) basis

Helpers for Nielsen & Chuang **Exercise 4.20** (CNOT basis transformations):
the operator-level action of `cnotGate` on tensor products of computational- and `X`-eigenbasis
vectors, plus the identification of the Hadamard gate's action on the computational basis with
the `|±⟩` states. The statements of Exercise 4.20 (the `±`-basis truth table and the
reversed-CNOT circuit identity) are proved from them in `AxQM/NC/Ch4/Exercise4_20.lean`.

* `cnotGate_op_qubitBasisVec_tmul` — the operator form of the CNOT truth table on the two-qubit
  computational basis: `CNOT (|i⟩ ⊗ |j⟩) = |i⟩ ⊗ |j ⊕ i⟩`, at the vector level (the raw-`⊗ₜ`
  restatement of `cnotGate_op_qubitBasis_tmul` of `Postulates/API/CNOTDensityMatrix.lean`). This is
  the workhorse for computing the CNOT action on `X`-eigenbasis superpositions by linearity.
* `hadamardGate_evolvePure_qubitBasis_zero` / `_one` — `H|0⟩ = |+⟩`, `H|1⟩ = |-⟩`: the Hadamard
  gate carries the computational basis to the `X`-eigenbasis.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **CNOT truth table at the operator level, raw-`⊗ₜ` phrasing:** `CNOT(|i⟩ ⊗ |j⟩) = |i⟩ ⊗ |j ⊕ i⟩`
with the tensor written on the underlying vectors `(qubitBasis i).vec ⊗ₜ (qubitBasis j).vec` (rather
than the product-state vector `(qubitBasis i ⊗ qubitBasis j).vec` of
`cnotGate_op_qubitBasis_tmul` in `Postulates/API/CNOTDensityMatrix.lean`, from which it is a
one-step restatement). This is the shape the bilinear expansion of an `X`-eigenvector produces, so
it is the
form the `±`-basis cores below rewrite with; the workhorse for the CNOT action on superpositions. -/
theorem cnotGate_op_qubitBasisVec_tmul (i j : Fin 2) :
    cnotGate.op ((qubitBasis i).vec ⊗ₜ[ℂ] (qubitBasis j).vec)
      = (qubitBasis i).vec ⊗ₜ[ℂ] (qubitBasis (j + i)).vec := by
  simpa only [PureState.tmul_vec] using cnotGate_op_qubitBasis_tmul i j

/-- Additivity of `cnotGate.op` on the raw two-qubit tensor space, as an `rw`/`simp`-shaped lemma
(stated with the arguments at the raw tensor head `qubit.space ⊗[ℂ] qubit.space` so it matches the
tensor expansions of `X`-eigenbasis vectors, where the generic `map_add` fails to unify the head
against `cnotGate.op`'s composite domain). -/
theorem cnotGate_op_add (x y : qubit.space ⊗[ℂ] qubit.space) :
    cnotGate.op ((x + y : qubit.space ⊗[ℂ] qubit.space)) = cnotGate.op x + cnotGate.op y :=
  ContinuousLinearMap.map_add _ _ _

/-- Homogeneity of `cnotGate.op` on the raw two-qubit tensor space, the `smul` companion of
`cnotGate_op_add` (see its note on the head-unification issue). -/
theorem cnotGate_op_smul (c : ℂ) (x : qubit.space ⊗[ℂ] qubit.space) :
    cnotGate.op ((c • x : qubit.space ⊗[ℂ] qubit.space)) = c • cnotGate.op x :=
  ContinuousLinearMap.map_smul _ _ _

/-! ### The `±`-basis action of CNOT, on state vectors

The vector-level cores of Nielsen & Chuang eqs. (4.24)–(4.27): `cnotGate.op` on the underlying
vectors of `|±⟩ ⊗ |±⟩`. Each is proved by expanding both `X`-eigenvectors in the computational
basis (`qubitPlus_vec_eq_smul_add`/`qubitMinus_vec_eq_smul_add`), applying the CNOT truth table
`cnotGate_op_qubitBasisVec_tmul` term by term through the raw-head linearity lemmas
`cnotGate_op_add`/`cnotGate_op_smul`, and recombining. The theorems of
`AxQM/NC/Ch4/Exercise4_20.lean` stating (4.24)–(4.27) use them through `PureState.ext`. -/

/-- Vector-level form of N&C eq. (4.24): `CNOT(|+⟩ ⊗ |+⟩) = |+⟩ ⊗ |+⟩` at the vector level. -/
theorem cnotGate_op_qubitPlus_qubitPlus_vec :
    cnotGate.op (qubitPlus.vec ⊗ₜ[ℂ] qubitPlus.vec) = qubitPlus.vec ⊗ₜ[ℂ] qubitPlus.vec := by
  simp only [qubitPlus_vec_eq_smul_add, smul_add, TensorProduct.add_tmul, TensorProduct.tmul_add,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  simp only [cnotGate_op_add, cnotGate_op_smul, cnotGate_op_qubitBasisVec_tmul, Fin.reduceAdd]
  have hgen :
      (Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec +
          (Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec) :
          qubit.space ⊗[ℂ] qubit.space) =
        Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
          (Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
                1).vec) := by
    module
  exact hgen

/-- Vector-level form of N&C eq. (4.25): `CNOT(|-⟩ ⊗ |+⟩) = |-⟩ ⊗ |+⟩` at the vector level. -/
theorem cnotGate_op_qubitMinus_qubitPlus_vec :
    cnotGate.op (qubitMinus.vec ⊗ₜ[ℂ] qubitPlus.vec) = qubitMinus.vec ⊗ₜ[ℂ] qubitPlus.vec := by
  simp only [qubitPlus_vec_eq_smul_add, qubitMinus_vec_eq_smul_add, smul_add,
    TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul]
  simp only [cnotGate_op_add, cnotGate_op_smul, cnotGate_op_qubitBasisVec_tmul, Fin.reduceAdd]
  have hgen :
      (Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (-1 : ℂ) • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
                1).vec +
          (Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (-1 : ℂ) • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
                0).vec) :
          qubit.space ⊗[ℂ] qubit.space) =
        Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (-1 : ℂ) • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
                0).vec +
          (Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (-1 : ℂ) • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
                1).vec) := by
    module
  exact hgen

/-- Vector-level form of N&C eq. (4.26): `CNOT(|+⟩ ⊗ |-⟩) = |-⟩ ⊗ |-⟩` at the vector level. -/
theorem cnotGate_op_qubitPlus_qubitMinus_vec :
    cnotGate.op (qubitPlus.vec ⊗ₜ[ℂ] qubitMinus.vec) = qubitMinus.vec ⊗ₜ[ℂ] qubitMinus.vec := by
  simp only [qubitPlus_vec_eq_smul_add, qubitMinus_vec_eq_smul_add, smul_add,
    TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul]
  simp only [cnotGate_op_add, cnotGate_op_smul, cnotGate_op_qubitBasisVec_tmul, Fin.reduceAdd]
  have hgen :
      (Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec +
          (Concrete.invSqrt2 • (-1 : ℂ) • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis
              1).vec +
            Concrete.invSqrt2 • (-1 : ℂ) • Concrete.invSqrt2 • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
                0).vec) :
          qubit.space ⊗[ℂ] qubit.space) =
        Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (-1 : ℂ) • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
                0).vec +
          (Concrete.invSqrt2 • (-1 : ℂ) • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis
              1).vec +
            Concrete.invSqrt2 • (-1 : ℂ) • Concrete.invSqrt2 • (-1 : ℂ) • (qubitBasis
                1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec) := by
    module
  exact hgen

/-- Vector-level form of N&C eq. (4.27): `CNOT(|-⟩ ⊗ |-⟩) = |+⟩ ⊗ |-⟩` at the vector level. -/
theorem cnotGate_op_qubitMinus_qubitMinus_vec :
    cnotGate.op (qubitMinus.vec ⊗ₜ[ℂ] qubitMinus.vec) = qubitPlus.vec ⊗ₜ[ℂ] qubitMinus.vec := by
  simp only [qubitPlus_vec_eq_smul_add, qubitMinus_vec_eq_smul_add, smul_add,
    TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul]
  simp only [cnotGate_op_add, cnotGate_op_smul, cnotGate_op_qubitBasisVec_tmul, Fin.reduceAdd]
  have hgen :
      (Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (-1 : ℂ) • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
                1).vec +
          (Concrete.invSqrt2 • (-1 : ℂ) • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis
              1).vec +
            Concrete.invSqrt2 • (-1 : ℂ) • Concrete.invSqrt2 • (-1 : ℂ) • (qubitBasis
                1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec) :
          qubit.space ⊗[ℂ] qubit.space) =
        Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
            Concrete.invSqrt2 • Concrete.invSqrt2 • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec +
          (Concrete.invSqrt2 • (-1 : ℂ) • Concrete.invSqrt2 • (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis
              1).vec +
            Concrete.invSqrt2 • (-1 : ℂ) • Concrete.invSqrt2 • (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis
                1).vec) := by
    module
  exact hgen

/-- **`H|0⟩ = |+⟩`:** the Hadamard gate carries `|0⟩` to the `X`-eigenstate `|+⟩ = (|0⟩+|1⟩)/√2`. -/
theorem hadamardGate_evolvePure_qubitBasis_zero :
    hadamardGate.evolvePure (qubitBasis 0) = qubitPlus := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, hadamardGate_op, qubitBasis_vec, qubitPlus_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC)
        (EuclideanSpace.single 0 1)).ofLp
      = (WithLp.toLp 2 Concrete.xPlus : EuclideanSpace ℂ (Fin 2)).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.hadamardC, Concrete.xPlus, Concrete.invSqrt2, Matrix.mulVec, dotProduct,
        EuclideanSpace.single]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **`H|1⟩ = |-⟩`:** the Hadamard gate carries `|1⟩` to the `X`-eigenstate `|-⟩ = (|0⟩-|1⟩)/√2`. -/
theorem hadamardGate_evolvePure_qubitBasis_one :
    hadamardGate.evolvePure (qubitBasis 1) = qubitMinus := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, hadamardGate_op, qubitBasis_vec, qubitMinus_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC)
        (EuclideanSpace.single 1 1)).ofLp
      = (WithLp.toLp 2 Concrete.xMinus : EuclideanSpace ℂ (Fin 2)).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.hadamardC, Concrete.xMinus, Concrete.invSqrt2, Matrix.mulVec, dotProduct,
        EuclideanSpace.single]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

end AxQM
