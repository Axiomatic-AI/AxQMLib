/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.LinearCode
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Parity-check matrices and elementary row operations

An `[n, k]` linear code may be specified by a **parity-check matrix** `H`: an `(n - k) × n` matrix,
the code being the set of words `x` with `H *ᵥ x = 0`, i.e. the *kernel* of `x ↦ H *ᵥ x` (Nielsen &
Chuang, *Quantum Computation and Quantum Information*, §10.4.1, eq. (10.57)). This file records the
parity-check description as a `LinearCode` and proves the row-operation invariance of N&C
Exercise 10.16.

## Main definitions

* `LinearCode.ofParityCheck H`: the code cut out by the parity-check matrix `H`, namely
  `LinearMap.ker H.mulVecLin`.

## Main results

* `LinearCode.mem_ofParityCheck_iff`: `x` is a codeword of `ofParityCheck H` iff `H *ᵥ x = 0`.
* `LinearCode.ofParityCheck_updateRow_add`: **adding one row of the parity-check matrix to another
  leaves the code unchanged** (N&C Exercise 10.16). Replacing row `b` by `H b + H a` (for `a ≠ b`)
  gives a parity-check matrix for the very same code.
* `LinearCode.ofParityCheck_updateRow_add_smul`: the same for adding *any* scalar multiple
  `c • H a` of row `a` to row `b` — the general elementary row operation, of which N&C's
  coefficient-`1` statement is the special case, and which over `ZMod 2` is the only nontrivial one.

## Implementation notes

The code is defined over an arbitrary field `K` and an arbitrary (finite) coordinate index type `ι`;
the binary codes of N&C are `K = ZMod 2`, `ι = Fin n`. The row-operation proof is entirely
elementary: adding row `a` to row `b` changes coordinate `b` of `H *ᵥ x` from `(H *ᵥ x) b` to
`(H *ᵥ x) b + c * (H *ᵥ x) a`, and — because `a ≠ b` — a word annihilated by one matrix is
annihilated by the other. No invertibility machinery is needed; the operation is its own witness in
each direction.

The **standard form** `[A | I_{n-k}]` that N&C obtains from these operations (by Gaussian
elimination and coordinate permutation) is developed in the sibling file
`ToMathlib/InformationTheory/Coding/ParityCheckStandardForm.lean`
(`LinearCode.exists_isUnit_submatrix_eq_one_of_mulVecLin_surjective`), which rests on the elementary
row-operation invariance supplied here.
-/

open Matrix

@[expose] public section

namespace LinearCode

variable {K m ι : Type*} [Field K] [Fintype ι]

/-- The linear code specified by a **parity-check matrix** `H`: the words `x` annihilated by `H`,
i.e. the kernel of the linear map `x ↦ H *ᵥ x` (Nielsen & Chuang, §10.4.1, eq. (10.57)). An
`[n, k]` code is cut out by an `(n - k) × n` matrix. -/
noncomputable def ofParityCheck (H : Matrix m ι K) : LinearCode K ι :=
  LinearMap.ker H.mulVecLin

/-- A word `x` is a codeword of the parity-check code `ofParityCheck H` exactly when
`H *ᵥ x = 0`. -/
theorem mem_ofParityCheck_iff {H : Matrix m ι K} {x : ι → K} :
    x ∈ ofParityCheck H ↔ H *ᵥ x = 0 := by
  rw [ofParityCheck, LinearMap.mem_ker, mulVecLin_apply]

variable [DecidableEq m]

/-- **Adding a scalar multiple of one row of the parity-check matrix to another leaves the code
unchanged.** For `a ≠ b`, replacing row `b` of `H` by `H b + c • H a` yields a parity-check matrix
for the same code. This is the general elementary row operation; N&C Exercise 10.16 is the case
`c = 1` (`ofParityCheck_updateRow_add`). -/
theorem ofParityCheck_updateRow_add_smul (H : Matrix m ι K) {a b : m} (hab : a ≠ b) (c : K) :
    ofParityCheck (H.updateRow b (H b + c • H a)) = ofParityCheck H := by
  ext x
  rw [mem_ofParityCheck_iff, mem_ofParityCheck_iff, updateRow_mulVec]
  have hv : (H b + c • H a) ⬝ᵥ x = (H *ᵥ x) b + c * (H *ᵥ x) a := by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]; rfl
  rw [hv, funext_iff, funext_iff]
  simp only [Pi.zero_apply]
  rw [Function.forall_update_iff (H *ᵥ x) (fun _ y => y = 0)]
  constructor
  · rintro ⟨hb, hne⟩ i
    rcases eq_or_ne i b with rfl | hi
    · rwa [hne a hab, mul_zero, add_zero] at hb
    · exact hne i hi
  · refine fun h => ⟨?_, fun i _ => h i⟩
    rw [h a, h b, mul_zero, add_zero]

/-- **Adding one row of the parity-check matrix to another leaves the code unchanged**
(Nielsen & Chuang, Exercise 10.16). For `a ≠ b`, replacing row `b` of `H` by `H b + H a` yields a
parity-check matrix for the same code. -/
theorem ofParityCheck_updateRow_add (H : Matrix m ι K) {a b : m} (hab : a ≠ b) :
    ofParityCheck (H.updateRow b (H b + H a)) = ofParityCheck H := by
  simpa using ofParityCheck_updateRow_add_smul H hab 1

end LinearCode
