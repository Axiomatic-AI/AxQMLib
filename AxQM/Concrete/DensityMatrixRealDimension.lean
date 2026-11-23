/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import ToMathlib.Analysis.InnerProductSpace.SelfAdjointFinrank
import ToMathlib.Analysis.Matrix.HilbertSchmidt
import ToMathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Concrete: real-parameter count of an `n`-qubit density matrix (N&C Ex 4.46)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.46 (p. 205):

An n-qubit density matrix is described by 4ⁿ − 1 independent real parameters.

This is a **linear-algebra parameter count**. The statement of Exercise 4.46 is in
`AxQM/NC/Ch4/Exercise4_46.lean`.

## The argument

A density matrix on the `d`-dimensional space `ℂ^d` (`d = 2ⁿ` for `n` qubits) is a `d × d`
**Hermitian** matrix that is additionally positive semidefinite and has unit trace. Counting
the *real* degrees of freedom:

* The real vector space of Hermitian `d × d` complex matrices,
  `selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ)`, has real dimension `d²`
  (`finrank_selfAdjoint_matrix`) — the matrix special case of the general lemma
  `finrank_real_selfAdjoint`, that the self-adjoint elements of a finite-dimensional complex
  star module have real dimension equal to its complex dimension.
* Unit trace is **one** real linear constraint: the trace of a Hermitian matrix is real, giving
  a surjective real-linear functional `realTraceOnSelfAdjoint` onto `ℝ`. Its kernel — the
  *traceless* Hermitian matrices, i.e. the "generalized Bloch vector" space
  `tracelessSelfAdjoint` — therefore has real dimension `d² − 1`
  (`finrank_tracelessSelfAdjoint_matrix`, via rank–nullity). Positive semidefiniteness is an
  open (inequality) condition and does not lower the count; a density matrix is `ρ = I/d + T`
  with `T` a free traceless Hermitian matrix.

Specialising to `d = 2ⁿ` gives `d² = 4ⁿ` and the exercise's `4ⁿ − 1`
(`finrank_tracelessSelfAdjoint_matrix_two_pow`).
-/

namespace AxQM.Concrete

noncomputable section

/-- **The real dimension of the Hermitian `d × d` matrices is `d²`.**

The matrix special case of `finrank_real_selfAdjoint` — the real dimension of the self-adjoint
elements of a finite-dimensional complex star module equals its complex dimension — applied to
`A = Matrix (Fin d) (Fin d) ℂ`, whose complex dimension is `d²` (`Matrix.finrank_eq_card_sq`). For
`n` qubits (`d = 2ⁿ`) this is the `4ⁿ` real parameters of a general Hermitian matrix; the unit-trace
constraint removes one (see `finrank_tracelessSelfAdjoint_matrix`). -/
theorem finrank_selfAdjoint_matrix (d : ℕ) :
    Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ)) = d ^ 2 := by
  -- `selfAdjoint.submodule ℝ A` and `selfAdjoint A` share a defeq carrier, so the general lemma
  -- closes it once the complex dimension `finrank ℂ (Matrix (Fin d) (Fin d) ℂ) = d²` is rewritten
  have h := finrank_real_selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  rw [Matrix.finrank_eq_card_sq, Fintype.card_fin] at h
  exact h

/-- The (real) trace as a real-linear functional on the Hermitian matrices, `s ↦ Re (tr s)`.
Since a Hermitian matrix has real trace this records the full trace, and unit trace is the single
linear constraint `realTraceOnSelfAdjoint = 1` cutting density matrices out of the Hermitian
matrices. -/
def realTraceOnSelfAdjoint (d : ℕ) :
    selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ :=
  Complex.reLm ∘ₗ (Matrix.traceLinearMap (Fin d) ℝ ℂ) ∘ₗ
    (selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ)).subtype

/-- The **traceless Hermitian** `d × d` matrices: the kernel of the real trace functional on the
Hermitian matrices. This is the "generalized Bloch vector" space — a density matrix is
`ρ = I/d + T` for a unique `T` in this space, so it parametrizes the density matrices. -/
def tracelessSelfAdjoint (d : ℕ) :
    Submodule ℝ (selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ)) :=
  LinearMap.ker (realTraceOnSelfAdjoint d)

/-- The real trace functional on the Hermitian matrices is surjective (for `d ≠ 0`): the identity
is Hermitian with trace `d ≠ 0`, and scaling it hits every real value. -/
theorem realTraceOnSelfAdjoint_surjective (d : ℕ) [NeZero d] :
    Function.Surjective (realTraceOnSelfAdjoint d) := by
  have hone : (1 : Matrix (Fin d) (Fin d) ℂ) ∈
      selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ) :=
    selfAdjoint.mem_iff.mpr (star_one _)
  have hval : realTraceOnSelfAdjoint d ⟨1, hone⟩ = (d : ℝ) := by
    simp [realTraceOnSelfAdjoint, Matrix.trace_one, Fintype.card_fin]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  intro t
  exact ⟨(t / (d : ℝ)) • ⟨1, hone⟩, by rw [map_smul, hval, smul_eq_mul, div_mul_cancel₀ t hd]⟩

/-- **The real dimension of the traceless Hermitian `d × d` matrices is `d² − 1`** (for `d ≠ 0`).
By rank–nullity applied to the surjective real trace functional on the `d²`-dimensional Hermitian
matrices: one real constraint removes one dimension. -/
theorem finrank_tracelessSelfAdjoint_matrix (d : ℕ) [NeZero d] :
    Module.finrank ℝ (tracelessSelfAdjoint d) = d ^ 2 - 1 := by
  have : Module.Finite ℝ (Matrix (Fin d) (Fin d) ℂ) :=
    Module.Finite.trans ℂ (Matrix (Fin d) (Fin d) ℂ)
  have hrn := (realTraceOnSelfAdjoint d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (realTraceOnSelfAdjoint_surjective d), finrank_top,
    Module.finrank_self, finrank_selfAdjoint_matrix] at hrn
  rw [tracelessSelfAdjoint]
  omega

/-- `(2ⁿ)² = 4ⁿ`. -/
theorem two_pow_sq (n : ℕ) : (2 ^ n) ^ 2 = 4 ^ n := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- **`n`-qubit specialization: the Hermitian `2ⁿ × 2ⁿ` matrices have real dimension `4ⁿ`.** -/
theorem finrank_selfAdjoint_matrix_two_pow (n : ℕ) :
    Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) = 4 ^ n := by
  rw [finrank_selfAdjoint_matrix, two_pow_sq]

/-- **Nielsen & Chuang, Exercise 4.46.** Describing an `n`-qubit density matrix requires `4ⁿ − 1`
independent real numbers: the traceless Hermitian `2ⁿ × 2ⁿ` matrices — the parameter space of
`n`-qubit density matrices — have real dimension `4ⁿ − 1`. -/
theorem finrank_tracelessSelfAdjoint_matrix_two_pow (n : ℕ) :
    Module.finrank ℝ (tracelessSelfAdjoint (2 ^ n)) = 4 ^ n - 1 := by
  rw [finrank_tracelessSelfAdjoint_matrix, two_pow_sq]

end

end AxQM.Concrete
