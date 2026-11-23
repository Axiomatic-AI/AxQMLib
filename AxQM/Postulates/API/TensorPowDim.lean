/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.PiTensor
import AxQM.Postulates.API.Qubit
import ToMathlib.LinearAlgebra.PiTensorProduct.Finrank

/-!
# AxQM.Postulates.API — dimension of a tensor-power system

The Hilbert-space dimension of the `n`-fold tensor power `S ^⊗ₛ n` of a quantum system `S` is
`(dim S) ^ n`, since its state space is the `n`-ary tensor power `⨂[ℂ] (_ : Fin n), S.space`
(`QSystem.tensorPow_space`) and the finite rank of a tensor product is the product of the ranks
(`Module.finrank_piTensorProduct`).

This is the dimension arithmetic behind the `n`-qubit register: `dim (qubitⁿ) = 2ⁿ`.

## Main results

* `AxQM.QSystem.finrank_tensorPow_space` — `dim (Sⁿ) = (dim S) ^ n`.
* `AxQM.QSystem.dim_tensorPow` — the `QSystem.dim` form of the same.
* `AxQM.finrank_qubit_tensorPow_space` — `dim (qubitⁿ) = 2 ^ n`.
-/

namespace AxQM

open scoped TensorProduct

/-- **Dimension of a tensor-power system**: the Hilbert-space dimension of `S ^⊗ₛ n` is
`(dim S) ^ n`. The state space of `S ^⊗ₛ n` is `⨂[ℂ] (_ : Fin n), S.space`
(`QSystem.tensorPow_space`), whose finite rank is `∏ (_ : Fin n), finrank ℂ S.space =
(finrank ℂ S.space) ^ n` (`Module.finrank_piTensorProduct`). -/
theorem QSystem.finrank_tensorPow_space (S : QSystem) (n : ℕ) :
    Module.finrank ℂ (S.tensorPow n).space = Module.finrank ℂ S.space ^ n := by
  have h : Module.finrank ℂ (S.tensorPow n).space = ∏ _i : Fin n, Module.finrank ℂ S.space :=
    Module.finrank_piTensorProduct (M := fun _ : Fin n => S.space)
  rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Dimension of a tensor-power system** (`QSystem.dim` companion of
`QSystem.finrank_tensorPow_space`): the dimension of the `n`-fold tensor power `S ^⊗ₛ n` is
`(dim S) ^ n`. Restates `finrank_tensorPow_space` through `QSystem.dim`. -/
theorem QSystem.dim_tensorPow (S : QSystem) (n : ℕ) : (S.tensorPow n).dim = S.dim ^ n := by
  simp only [QSystem.dim]; exact QSystem.finrank_tensorPow_space S n

/-- **Dimension of the `n`-qubit register**: `dim (qubit ^⊗ₛ n) = 2 ^ n`, since each qubit factor
has dimension `2` (`finrank_qubit_space`). This is the `2ⁿ` bound behind Nielsen & Chuang's
Exercise 12.3 (`n` qubits carry at most `n` bits of classical information). -/
theorem finrank_qubit_tensorPow_space (n : ℕ) :
    Module.finrank ℂ (qubit.tensorPow n).space = 2 ^ n := by
  rw [QSystem.finrank_tensorPow_space, finrank_qubit_space]

end AxQM
