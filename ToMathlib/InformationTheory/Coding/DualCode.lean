/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.LinearCode
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Rank
public import ToMathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The dual of a classical linear code

The **dual code** `C⊥` of a linear code `C ⊆ Kⁿ` is the set of all words orthogonal to every
codeword under the standard dot product `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` (Nielsen & Chuang, *Quantum Computation
and Quantum Information*, §10.4.1, p. 449). The dual construction is the classical ingredient of the
Calderbank–Shor–Steane (CSS) quantum codes, whose Gilbert–Varshamov bound is N&C Problem 10.2: the
CSS code `CSS(C₁, C₂)` requires a nested pair `C₂ ⊆ C₁` with both `C₁` and `C₂⊥` of large minimum
distance, and its dimension is governed by `dim C₁ - dim C₂` — quantities that only make sense once
the dual is available.

## Main definitions

* `stdBilin K ι`: the standard dot-product bilinear form `⟨x, y⟩ = x ⬝ᵥ y` on `ι → K` (used to take
  the dual; a reusable object independent of any particular code).
* `LinearCode.dual C`: the dual code `C⊥`, the orthogonal complement of `C` with respect to
  `stdBilin`.
* `LinearCode.IsSelfOrthogonal C`: `C` is **weakly self-dual** (self-orthogonal), `C ⊆ C⊥`
  (N&C §10.4.1, p. 449).
* `LinearCode.IsDualContaining C`: `C` **contains its dual**, `C⊥ ⊆ C` — the condition on `C₁`
  under which `CSS(C₁, C₁⊥)` is a genuine quantum code.
* `LinearCode.IsSelfDual C`: `C` is **strictly self-dual**, `C = C⊥`.

## Main results

* `LinearCode.mem_dual_iff`: `y ∈ C⊥` iff `x ⬝ᵥ y = 0` for every codeword `x ∈ C`.
* `LinearCode.finrank_dual`: `dim C⊥ = n - dim C`, where `n = #ι` is the block length. An `[n, k]`
  code thus has an `[n, n - k]` dual (N&C §10.4.1).
* `LinearCode.dual_dual`: the dual is an involution, `(C⊥)⊥ = C`.
* `LinearCode.dual_le_dual`: the dual is order-reversing, so `C₂ ⊆ C₁ ↔ C₁⊥ ⊆ C₂⊥` — exactly the
  duality behind the CSS nesting constraint.
* `LinearCode.dual_ker_mulVecLin`: the dual of a kernel code is its row space,
  `(ker M.mulVecLin)⊥ = range (vecMulLinear M)`, for any matrix `M` over a field — the identity that
  lets a CSS/stabilizer construction identify `C₂⊥` with the generator/row space of its parity
  matrix.

## Implementation notes

`stdBilin K ι` is the identity-matrix form `Matrix.toBilin' 1` (so `stdBilin K ι x y = x ⬝ᵥ y`); it
is symmetric and nondegenerate (`det 1 = 1 ≠ 0`). Those two facts are exactly the hypotheses of
Mathlib's `LinearMap.BilinForm.finrank_orthogonal`, `orthogonal_orthogonal`, and `orthogonal_le`,
which then deliver the dimension formula, the double-dual involution, and order-reversal directly,
with no bespoke reimplementation. `stdBilin` names no code and lives outside the `LinearCode`
namespace.

The coefficients range over an arbitrary field `K`; the binary CSS applications specialise to
`K = ZMod 2`.
-/

open Matrix

@[expose] public section

/-- The standard **dot-product bilinear form** `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` on the word space `ι → K`, given
by `Matrix.toBilin'` of the identity matrix. It is the (code-independent) form with respect to which
the dual of a linear code is taken. -/
noncomputable def stdBilin (K ι : Type*) [Field K] [Fintype ι] [DecidableEq ι] :
    LinearMap.BilinForm K (ι → K) :=
  Matrix.toBilin' (1 : Matrix ι ι K)

@[simp] theorem stdBilin_apply {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] (x y : ι → K) :
    (stdBilin K ι x) y = x ⬝ᵥ y := by
  rw [stdBilin, Matrix.toBilin'_apply', Matrix.one_mulVec]

/-- The standard dot-product form is symmetric: `⟨x, y⟩ = ⟨y, x⟩`. -/
theorem stdBilin_isSymm {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    (stdBilin K ι).IsSymm :=
  ⟨fun x y => by simp only [stdBilin_apply]; exact dotProduct_comm x y⟩

/-- The standard dot-product form is nondegenerate: its Gram matrix is the identity, of determinant
`1 ≠ 0`. -/
theorem stdBilin_nondegenerate {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    (stdBilin K ι).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' 1 (by
    rw [Matrix.det_one]; exact one_ne_zero)

namespace LinearCode

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The **dual code** `C⊥` of a linear code `C`: the set of words orthogonal to every codeword under
the standard dot product (Nielsen & Chuang, §10.4.1, p. 449). -/
noncomputable def dual (C : LinearCode K ι) : LinearCode K ι :=
  (stdBilin K ι).orthogonal C

/-- A word lies in the dual code `C⊥` exactly when it is orthogonal to every codeword. -/
theorem mem_dual_iff {C : LinearCode K ι} {y : ι → K} :
    y ∈ dual C ↔ ∀ x ∈ C, x ⬝ᵥ y = 0 := by
  simp only [dual, LinearMap.BilinForm.mem_orthogonal_iff, stdBilin_apply]

/-- The dual is **order-reversing**: a larger code has a smaller dual. Combined with `dual_dual`,
this gives `C₂ ⊆ C₁ ↔ C₁⊥ ⊆ C₂⊥`, the duality underlying the CSS nesting constraint. -/
theorem dual_le_dual {C₁ C₂ : LinearCode K ι} (h : C₁ ≤ C₂) : dual C₂ ≤ dual C₁ :=
  LinearMap.BilinForm.orthogonal_le (B := stdBilin K ι) h

/-- **Dimension of the dual code**: `dim C⊥ = n - dim C`, where `n = #ι` is the block length. An
`[n, k]` code has an `[n, n - k]` dual (Nielsen & Chuang, §10.4.1). Follows from the nondegeneracy
of the dot-product form. -/
theorem finrank_dual (C : LinearCode K ι) :
    Module.finrank K (dual C) = Fintype.card ι - Module.finrank K C := by
  rw [dual, LinearMap.BilinForm.finrank_orthogonal stdBilin_nondegenerate, Module.finrank_pi]

/-- **The dual is an involution**: `(C⊥)⊥ = C`. Follows from the nondegeneracy and symmetry of the
dot-product form. -/
@[simp] theorem dual_dual (C : LinearCode K ι) : dual (dual C) = C :=
  LinearMap.BilinForm.orthogonal_orthogonal stdBilin_nondegenerate stdBilin_isSymm.isRefl C

/-- A linear code is **weakly self-dual** (self-orthogonal) when it is contained in its dual,
`C ⊆ C⊥` (Nielsen & Chuang, §10.4.1, p. 449). -/
def IsSelfOrthogonal (C : LinearCode K ι) : Prop := C ≤ dual C

/-- A linear code is **dual-containing** when it contains its dual, `C⊥ ⊆ C`. This is the condition
on `C₁` making `CSS(C₁, C₁⊥)` a genuine quantum code (its `C₂ = C₁⊥ ⊆ C₁`). -/
def IsDualContaining (C : LinearCode K ι) : Prop := dual C ≤ C

/-- A linear code is **strictly self-dual** when it equals its dual, `C = C⊥`. -/
def IsSelfDual (C : LinearCode K ι) : Prop := dual C = C

/-- Weak self-duality unfolded: every two codewords are orthogonal under the dot product. -/
theorem isSelfOrthogonal_iff {C : LinearCode K ι} :
    IsSelfOrthogonal C ↔ ∀ x ∈ C, ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  rw [IsSelfOrthogonal, IsConcreteLE.le_iff]
  refine ⟨fun h x hx y hy => ?_, fun h z hz => (mem_dual_iff).2 fun x hx => ?_⟩
  · exact (mem_dual_iff.1 (h hy)) x hx
  · exact h x hx z hz

/-- A code is self-orthogonal iff its dual is dual-containing — the two forms of the CSS constraint,
related by the double-dual involution `(C⊥)⊥ = C`. -/
theorem isDualContaining_dual {C : LinearCode K ι} :
    IsDualContaining (dual C) ↔ IsSelfOrthogonal C := by
  rw [IsDualContaining, IsSelfOrthogonal, dual_dual]

/-- **The dual of a kernel code is its row space**: `(ker M)⊥ = range (Mᵀ)`, i.e. the orthogonal
complement of the column-null space `ker (M *ᵥ ·)` is the row space `range (· ᵥ* M)`. This holds for
*any* matrix over a field — no rank or injectivity hypothesis — so it cleanly identifies the dual
`C₂⊥` of a code presented as `ker M.mulVecLin` with the generator/row space `range (vecMulLinear M)`
that the CSS and stabilizer constructions build on. The proof is a dimension count: the row space is
always contained in the dual (orthogonality of rows to the null space), and both have dimension
`rank M` (`finrank_dual` + rank–nullity, using `Matrix.rank_transpose` for `dim (row space) =
dim (column space)`). -/
theorem dual_ker_mulVecLin {m : Type*} [Fintype m] (M : Matrix m ι K) :
    dual (LinearMap.ker M.mulVecLin) = LinearMap.range (Matrix.vecMulLinear M) := by
  have hle : LinearMap.range (Matrix.vecMulLinear M) ≤ dual (LinearMap.ker M.mulVecLin) := by
    rintro _ ⟨z, rfl⟩
    rw [mem_dual_iff]
    intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
    rw [Matrix.vecMulLinear_apply, dotProduct_comm, ← Matrix.dotProduct_mulVec, hx, dotProduct_zero]
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  -- both dimensions equal `rank M`: the row space is `Mᵀ`'s column space (`mulVecLin_transpose`),
  -- whose rank equals `rank M` (`rank_transpose`); the dual's dimension is `card ι - dim (ker)`.
  have hrank_vec : Module.finrank K ↥(LinearMap.range (Matrix.vecMulLinear M))
      = Module.finrank K ↥(LinearMap.range M.mulVecLin) := by
    rw [← Matrix.mulVecLin_transpose, Matrix.finrank_range_mulVecLin,
      Matrix.finrank_range_mulVecLin]
    exact Matrix.rank_transpose M
  rw [finrank_dual, hrank_vec]
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_pi] at hrn
  omega

end LinearCode

end
