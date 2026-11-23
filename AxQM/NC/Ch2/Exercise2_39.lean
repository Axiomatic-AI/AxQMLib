/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Matrix.HilbertSchmidt

/-!
# Nielsen & Chuang, Exercise 2.39 (The Hilbert–Schmidt inner product on operators)

Show (A,B)=tr(A^dagger B) is an inner product (Hilbert-Schmidt); dim L_V = d^2; orthonormal basis of
Hermitian matrices.

## The declarations — parts (1), (2) and (3)

The formalisation is in `ToMathlib/Analysis/Matrix/HilbertSchmidt.lean`, for a finite index type
`n` and an `RCLike` field `𝕜` (of which `ℂ` is an instance), with `L_V := Matrix n n 𝕜` and
`d := Fintype.card n`:

* `Matrix.hsInner A B : 𝕜 := (Aᴴ * B).trace` — the Hilbert–Schmidt inner product `(A, B) = tr(A† B)`
  (eq. (2.65)) as a bare function.
* `Matrix.hsInnerCore : InnerProductSpace.Core 𝕜 (Matrix n n 𝕜)` — **part (1)**. Its fields *are*
  the inner-product axioms for `hsInner`: conjugate symmetry `conj (B, A) = (A, B)`, nonnegativity
  `0 ≤ re (A, A)`, definiteness `(A, A) = 0 → A = 0`, additivity `(A + B, C) = (A, C) + (B, C)`, and
  conjugate linearity in the first slot `(r • A, B) = conj r · (A, B)`. Bundling them as an
  `InnerProductSpace.Core` is exactly "showing `(·, ·)` is an inner product function".
* `Matrix.finrank_eq_card_sq : Module.finrank 𝕜 (Matrix n n 𝕜) = (Fintype.card n) ^ 2` — **part
  (2)** (`dim L_V = d²`).

For **part (3)**, over `ℂ` with `n` linearly ordered (and nonempty), the same file constructs the
**generalised Gell–Mann family** — `d²` Hermitian matrices indexed by `n × n`:

* `Matrix.gellMann p` — the family: the diagonal units `Eⱼⱼ`, the symmetric `(Eⱼₖ + Eₖⱼ)/√2` and the
  antisymmetric `i(Eₖⱼ − Eⱼₖ)/√2` (`j < k`).
* `Matrix.gellMann_isHermitian` — each member is Hermitian.
* `Matrix.gellMann_orthonormal : hsInner (gellMann p) (gellMann q) = if p = q then 1 else 0` — the
  family is orthonormal under the Hilbert–Schmidt inner product.
* `Matrix.hermitianOrthonormalBasis : Module.Basis (n × n) ℂ (Matrix n n ℂ)` — bundled as an actual
  basis (via `basisOfLinearIndependentOfCardEqFinrank`, using orthonormality ⇒ linear independence
  and `finrank_eq_card_sq` for the cardinality `#(n × n) = d²`), with
  `Matrix.hermitianOrthonormalBasis_isHermitian` / `Matrix.hermitianOrthonormalBasis_orthonormal`
  recording that its members are Hermitian and orthonormal.

## N&C ↦ Mathlib dictionary and fidelity

* **The operator space** `L_V` is `Matrix n n 𝕜` (operators on `V ≅ 𝕜ⁿ` in a fixed basis), a
  `𝕜`-vector space with the usual `+`, `•`, `0`.
* **The trace inner product** `(A, B) = tr(A† B)` is `Matrix.hsInner A B = (Aᴴ * B).trace`, with `†`
  the conjugate transpose `ᴴ`. Mathlib's convention makes an inner product conjugate-linear in its
  *first* argument, which matches N&C exactly — the adjoint sits on the first slot `A`.
* **Positive definiteness**, the substantive axiom, reduces to `Aᴴ * A` being positive semidefinite
  (`Matrix.posSemidef_conjTranspose_mul_self`), so `0 ≤ re (tr(Aᴴ A))`
  (`Matrix.PosSemidef.trace_nonneg` via `RCLike.nonneg_iff`), with `tr(Aᴴ A) = 0` forcing `A = 0`
  (`Matrix.trace_conjTranspose_mul_self_eq_zero_iff`); i.e. `(A, A) = ∑ᵢⱼ ‖Aᵢⱼ‖²`.
* **The dimension count** is the diagonal, `𝕜`-valued case of `Module.finrank_matrix`
  (`finrank R (Matrix m n M) = card m · card n · finrank R M`): with `card m = card n = d` and
  `finrank 𝕜 𝕜 = 1`, this is `d · d · 1 = d²`.
* **Part (3), and generality.** The orthonormal Hermitian basis is `ℂ`-specific: its antisymmetric
  generators `i(Eₖⱼ − Eⱼₖ)/√2` need `Complex.I`, and over `ℝ` the Hermitian (= symmetric) matrices
  do not span `L_V`. Naming the basis uses a `LinearOrder` on `n` (to split the `j < k` / `j > k` /
  `j = k` cases; canonical for `n = Fin d`) and `Nonempty n`; both are nondegeneracy scaffolds, not
  a weakening — such a basis exists for every finite-dimensional `L_V`. Parts (1) and (2) are stated
  over any `RCLike 𝕜` and any finite `n` (with `ℂ` the intended instance), a faithful
  generalisation of N&C's finite-dimensional complex Hilbert space.
-/
