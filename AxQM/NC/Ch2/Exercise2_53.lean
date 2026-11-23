/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardEigen

/-!
# Nielsen & Chuang, Exercise 2.53 (eigenvalues and eigenvectors of the Hadamard gate)

What are the eigenvalues and eigenvectors of H?

The Hadamard gate `H = (1/√2)!![1,1;1,-1]` (§2.2.2, eq. 2.85) is both unitary (Exercise 2.51) and
**Hermitian**, hence a legitimate `Observable qubit` (`hadamardObservable`), whose
real spectrum is a set of measurement values. Since `H² = I` (Exercise 2.52), its eigenvalues are
`±1`, with normalized eigenvectors

* `|h₊⟩ ∝ (1, √2 − 1)` for eigenvalue `+1`,
* `|h₋⟩ ∝ (√2 − 1, −1)` for eigenvalue `−1`

(equivalently `cos(π/8)|0⟩ + sin(π/8)|1⟩` and `sin(π/8)|0⟩ − cos(π/8)|1⟩`: `H` is the reflection
about the line at angle `π/8`). The eigenvalues are *exactly* `±1` — nothing else is an eigenvalue,
since `H² = I` (Exercise 2.52) forces `μ² = 1` — so this exhausts the answer to *"what **are** the
eigenvalues of `H`?"*; the two eigenvectors are moreover orthogonal.

The statement concerns `H` as an observable, its eigenstates as `PureState`s, and the eigenvalue
equations, expressed with `Observable.HasEigenstate` and `PureState.expectation`:

* `hadamardObservable_hasEigenstate_one` / `_neg_one` — `|h₊⟩`, `|h₋⟩` are eigenstates with
  eigenvalues `+1`, `−1` (exhibiting eigenvectors for each eigenvalue);
* `hadamardObservable_eigenvalue_eq_one_or_neg_one` — **exhaustiveness:** *every* eigenvalue of `H`
  is `+1` or `−1`, so together with the two witnesses the eigenvalues are exactly `{+1, −1}`;
* `hadamardEigenstatePlus_expectation` / `hadamardEigenstateMinus_expectation` — `⟪H⟫ = ±1` in each
  eigenstate, i.e. measuring `H` in an eigenstate yields the eigenvalue with certainty (the physical
  meaning of the eigenvalue as a measurement outcome).

The observable `hadamardObservable` (with
`hadamardObservable_op_eq_hadamardGate`: it is the same operator as the Exercise 2.51 gate), the
explicit eigenvectors, the operator-level eigenvalue equations `hadamardObservable_apply_eigenvec*`,
and the orthogonality `hadamardEigenstate_orthogonal` (an inner product of state vectors) are in
`AxQM/Postulates/API/HadamardEigen.lean`, together with the predicate `Observable.HasEigenstate`
and its helpers.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.53 (`+1`).** `|h₊⟩ ∝ (1, √2 − 1)` is an eigenstate of the
Hadamard observable with eigenvalue `+1`: `H |h₊⟩ = |h₊⟩`. -/
theorem hadamardObservable_hasEigenstate_one :
    hadamardObservable.HasEigenstate 1 hadamardEigenstatePlus :=
  hadamardObservable.hasEigenstate_of_smul hadamardEigenstatePlus_vec
    hadamardObservable_apply_eigenvecPlus

/-- **Nielsen & Chuang, Exercise 2.53 (`−1`).** `|h₋⟩ ∝ (√2 − 1, −1)` is an eigenstate of the
Hadamard observable with eigenvalue `−1`: `H |h₋⟩ = −|h₋⟩`. -/
theorem hadamardObservable_hasEigenstate_neg_one :
    hadamardObservable.HasEigenstate (-1) hadamardEigenstateMinus := by
  refine hadamardObservable.hasEigenstate_of_smul hadamardEigenstateMinus_vec ?_
  rw [hadamardObservable_apply_eigenvecMinus]; norm_num

/-- **Nielsen & Chuang, Exercise 2.53 (exhaustiveness).** The eigenvalues of the Hadamard
observable are *exactly* `±1`: every real `μ` for which some pure state is a `μ`-eigenstate
satisfies `μ = 1` or `μ = −1`. Together with `hadamardObservable_hasEigenstate_one` / `_neg_one`
(which exhibit eigenstates for `+1` and `−1`), this says the spectrum is precisely `{+1, −1}` — the
full answer to "what *are* the eigenvalues of `H`?". Proved from `H² = I` (`μ² = 1`), reusing the
involution content of Exercise 2.52. -/
theorem hadamardObservable_eigenvalue_eq_one_or_neg_one (μ : ℝ) (ψ : PureState qubit)
    (h : hadamardObservable.HasEigenstate μ ψ) : μ = 1 ∨ μ = -1 :=
  Observable.eigenvalue_eq_of_op_mul_self hadamardObservable_op_mul_self h

/-- The expectation value of the Hadamard observable in its `+1`-eigenstate is `+1`: measuring `H`
in `|h₊⟩` yields `+1` with certainty. -/
theorem hadamardEigenstatePlus_expectation :
    hadamardEigenstatePlus.expectation hadamardObservable = 1 :=
  PureState.expectation_of_hasEigenstate hadamardObservable_hasEigenstate_one

/-- The expectation value of the Hadamard observable in its `−1`-eigenstate is `−1`: measuring `H`
in `|h₋⟩` yields `−1` with certainty. -/
theorem hadamardEigenstateMinus_expectation :
    hadamardEigenstateMinus.expectation hadamardObservable = -1 :=
  PureState.expectation_of_hasEigenstate hadamardObservable_hasEigenstate_neg_one

end AxQM
