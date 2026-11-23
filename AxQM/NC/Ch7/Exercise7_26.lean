/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoQubitAngularMomentum

/-!
# Nielsen & Chuang, Exercise 7.26 (coupled angular-momentum basis of two spin-½ particles)

*(N&C p. 314.)*

Verify properties of |j,m_j⟩ by writing the 4×4 matrices J² and j_z in that basis.

For two spin-½ particles the total angular-momentum operators are `j_x = (X₁ + X₂)/2`,
`j_y = (Y₁ + Y₂)/2`, `j_z = (Z₁ + Z₂)/2` and `J² = j_x² + j_y² + j_z²` (N&C, unnumbered
equation before (7.97), and (7.97)), where `A₁ = A ⊗ I`, `A₂ = I ⊗ A`. The coupled basis
(N&C (7.93)–(7.96)) is the spin singlet `|0,0⟩_J = (|01⟩ − |10⟩)/√2` (`j = 0`) together with
the triplet `|00⟩`, `(|01⟩ + |10⟩)/√2`, `|11⟩` (`j = 1`). The "properties to verify" (stated
in the text preceding the exercise) are that these are simultaneous eigenstates of `J²` with
eigenvalue `j(j+1)` and of `j_z` with eigenvalue `m_j`; the exercise's suggested method is to
write out the `4 × 4` matrices `J²` and `j_z`, which are diagonal in this basis.

The exercise's content is pure linear algebra over `ℂ⁴ = ℂ² ⊗ ℂ²`: four
explicit `4 × 4` complex matrices (`j_x, j_y, j_z, J²`), four explicit column vectors (the
coupled states), and the eigenvalue/orthonormality equations relating them. Compare
`AxQM/NC/Ch6/Exercise6_8.lean`.

## The formalisation

`AxQM/Concrete/TwoQubitAngularMomentum.lean` (namespace `AxQM.Concrete`):

* `totalJx`, `totalJy`, `totalJz`, `totalJSq` — the four operators as `4 × 4` matrices built
  from the Pauli matrices by Kronecker product, with explicit matrix forms `totalJx_eq`,
  `totalJy_eq`, `totalJz_eq`, `totalJSq_eq`. In particular `totalJz = diag(1, 0, 0, −1)` and
  `totalJSq = !![2,0,0,0; 0,1,1,0; 0,1,1,0; 0,0,0,2]` — **the two matrices the exercise asks
  us to write out**.
* `coupledSinglet`, `coupledTripletPlus`, `coupledTripletZero`, `coupledTripletMinus` — the
  four coupled-basis vectors (N&C (7.93)–(7.96)).
* `totalJz_mulVec_*` and `totalJSq_mulVec_*` (eight theorems) — **the properties to verify**:
  each coupled state is an eigenvector of `J²` with eigenvalue `j(j+1)` (`0` for the singlet,
  `2` for the triplet) and simultaneously of `j_z` with its `j_z`-eigenvalue. Column by column
  these say exactly that `J²` and `j_z` are **diagonal in the coupled basis**, with diagonal
  entries `(0, 2, 2, 2)` and `(0, 1, 0, −1)`.
* `coupledBasis` and `coupledBasis_conjTranspose_mul_self` — the change-of-basis matrix `U`
  (columns the four states, in N&C's order) is unitary, `Uᴴ U = I`: the four states form an
  orthonormal basis, so "writing the matrices in that basis" is well defined.

### Note on the `j_z` sign convention

With N&C's standard Pauli `Z = diag(1, −1)`, `j_z = (Z₁ + Z₂)/2` gives `|00⟩` eigenvalue `+1`
and `|11⟩` eigenvalue `−1` — the opposite sign to the `m_j` labels `|1,∓1⟩_J` of (7.94),
(7.96). This is a spin-orientation convention (which extremal state is `m_j = +1`); the states
are named by their actual `j_z`-eigenvalue (`…Plus`/`…Minus`). The convention-independent
physical content — simultaneous eigenstates, `J²`-eigenvalue `j(j+1) ∈ {0, 2}`, `|j_z|`
eigenvalue `|m_j| ∈ {0, 1}` — is verified exactly. See the `Concrete` module docstring.
-/
