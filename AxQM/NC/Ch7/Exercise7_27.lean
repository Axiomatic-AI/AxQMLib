/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ThreeSpinAngularMomentum

/-!
# Nielsen & Chuang, Exercise 7.27 (Three spin angular momenta states)

Three-spin angular momenta: show the listed states are the j=1/2 and j=3/2 total-momentum
eigenstates.

(N&C p. 314.) The eight listed states are the total-angular-momentum eigenbasis of the three-qubit
space `(ℂ²)⊗³`: a `j = 3/2` symmetric quartet and two `j = 1/2` mixed-symmetry doublets.

The content is pure linear algebra over
`Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ` and column vectors
`Fin 2 × Fin 2 × Fin 2 → ℂ`.

## The formalisation

In `AxQM/Concrete/ThreeSpinAngularMomentum.lean` (namespace
`AxQM.Concrete.ThreeSpin`):

* `emb1`/`emb2`/`emb3`, `jx`, `jy`, `jz`, `jsq` — the single-qubit embeddings and the total-momentum
  operators `(X₁+X₂+X₃)/2`, …, `J² = jx²+jy²+jz²`.
* `symP32`, `symP12`, `symM12`, `symM32` — the `j = 3/2` symmetric quartet (7.101), (7.100), (7.99),
  (7.98); `mixAP12`, `mixAM12` and `mixBP12`, `mixBM12` — the two `j = 1/2` doublets
  (7.102)–(7.105).
* `jz_*` (eight) — each state is a `jz`-eigenstate, with its **actual** eigenvalue.
* `jsq_*` (eight) — each state is a `J²`-eigenstate with eigenvalue `j(j+1)` (`15/4` for the
  `j = 3/2` quartet, `3/4` for the `j = 1/2` doublets), matching N&C exactly.
* `toEuclid`, `stateVec` — the eight states reinterpreted as Hilbert-space vectors in
  `EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)` (the same data under the `ℓ²`/`PiLp 2` structure),
  packaged as a family indexed by `Fin 8`.
* `stateVec_orthonormal` — the eight states are **orthonormal** (`⟨j,mⱼ|j',mⱼ'⟩ = δ`).
* `stateBasis` — hence they **form a basis** of the `2³ = 8`-dimensional space, which is the
  exercise's headline claim ("the states (7.98)–(7.105) form a basis for the space").

The `jz`-labels of the four `j = 3/2` kets as **printed** in (7.98)–(7.101) disagree in sign with
the operator `jz = (Z₁+Z₂+Z₃)/2` the exercise itself writes (the printed list mixes the `|0⟩ = up`
and `|1⟩ = up` spin conventions); the module docstring of that file documents this and proves
the true eigenvalues.
-/
