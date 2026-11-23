/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HyperfineCoupledBasis

/-!
# Nielsen & Chuang, Exercise 7.28 (Hyperfine states)

*(N&C p. 315.)*

Hyperfine states: show spin-3/2 i_x,i_y,i_z satisfy SU(2) rules; build 8×8 f_z,F² and diagonalize
for |F,m_F⟩.

The whole exercise is pure linear algebra over `ℂ⁴` (nuclear spin `3/2`)
and `ℂ⁴ ⊗ ℂ² ≅ ℂ⁸` (the coupled system): explicit complex matrices (the `4 × 4` operators
`i_x, i_y, i_z`; the `8 × 8` operators `f_x, f_y, f_z, F²`), explicit column vectors (the eight
coupled states `|F, m_F⟩`), and the commutator / eigenvalue / orthonormality identities relating
them. Compare `AxQM/NC/Ch7/Exercise7_26.lean` (the two spin-½ analogue).

## The formalisation

The exercise is formalised in three files (namespace `AxQM.Concrete`), each
using the previous one.

### Part 1 — the spin-`3/2` operators and their `SU(2)` relations

`AxQM/Concrete/Spin32AngularMomentum.lean`:

* `sqrt3`, `sqrt3_mul_self`, `sqrt3_sq`, `sqrt3_star` — the amplitude `√3 : ℂ` and its identities.
* `spin32Ix`, `spin32Iy`, `spin32Iz` — the three operators `i_x, i_y, i_z` as `4 × 4` matrices,
  transcribed verbatim from (7.106)–(7.108) (basis ordered by increasing `m_I = −3/2,…,3/2`, so
  `i_z = ½·diag(−3,−1,1,3)`).
* `spin32_comm_ix_iy`, `spin32_comm_iy_iz`, `spin32_comm_iz_ix` — **part 1**: the three cyclic
  `SU(2)` commutation relations `[i_a, i_b] = i·i_c` (`[i_x,i_y] = i·i_z`, etc.).

### Part 2 (first half) — the `8 × 8` coupled operators

`AxQM/Concrete/HyperfineAngularMomentum.lean`:

* `flattenFin8` — the `Fin 4 × Fin 2 ≃ Fin 8` re-indexing of a nuclear ⊗ electron tensor product
  to a flat `8 × 8` matrix (`(a, b) ↦ 2·a + b`).
* `hyperfineFx`, `hyperfineFy`, `hyperfineFz` — the operators `f_a = i_a ⊗ I + I ⊗ σ_a/2`, and
  `hyperfineFSq = f_x² + f_y² + f_z²`, built by Kronecker product.
* `hyperfineFz_eq`, `hyperfineFx_eq`, `hyperfineFy_eq`, `hyperfineFSq_eq` — **the `8 × 8` matrices
  the exercise asks us to write out**. In particular `f_z = diag(−1,−2,0,−1,1,0,2,1)` and `F²` is
  block-diagonal, with the `2 × 2` blocks `!![3,√3;√3,5]`, `!![4,2;2,4]`, `!![5,√3;√3,3]` on the
  `m_F = −1, 0, +1` subspaces.

### Part 2 (second half) — the coupled `|F, m_F⟩` basis and the diagonalization

`AxQM/Concrete/HyperfineCoupledBasis.lean`:

* `hyperfineCoupledF2p2`, `hyperfineCoupledF2p1`, `hyperfineCoupledF2z`, `hyperfineCoupledF2n1`,
  `hyperfineCoupledF2n2` (the `F = 2` quintet) and `hyperfineCoupledF1p1`, `hyperfineCoupledF1z`,
  `hyperfineCoupledF1n1` (the `F = 1` triplet) — the eight coupled states `|F, m_F⟩` (from the
  Clebsch–Gordan coefficients for `3/2 ⊗ 1/2`) as vectors `Fin 8 → ℂ`.
* `hyperfineFz_mulVec_*` (eight theorems) — `f_z |F, m_F⟩ = m_F • |F, m_F⟩`.
* `hyperfineFSq_mulVec_*` (eight theorems) — `F² |F, m_F⟩ = F(F+1) • |F, m_F⟩`, eigenvalue `6`
  for `F = 2` and `2` for `F = 1`.
* `hyperfineCoupledBasis` and `hyperfineCoupledBasis_conjTranspose_mul_self` — the change-of-basis
  matrix `U` (columns the eight states) is unitary, `Uᴴ U = I`, so they form an orthonormal
  basis. Together with the eigenvalue equations, `Uᴴ f_z U = diag(−2,−1,0,1,2,−1,0,1)` and
  `Uᴴ F² U = diag(6,6,6,6,6,2,2,2)` — **the simultaneous diagonalization of `f_z` and `F²`** that
  part 2 asks for.

### Note on the `m_F` sign / basis-ordering conventions

The flat basis is ordered `(m_I, m_S) ↦ 2·a + b` with `a` increasing `m_I = a − 3/2` and, under
the standard Pauli `Z = diag(1,−1)` (so `Z/2 = diag(+½,−½)`), `b = 0 ↦ m_S = +½`,
`b = 1 ↦ m_S = −½`; hence `f_z = diag(−1,−2,0,−1,1,0,2,1)` carries `m_F = m_I + m_S` on each
product state. All eigenvalues are computed against this convention; see the `Concrete` module
docstrings for the full basis-ordering discussion.
-/
