/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-!
# Concrete: compressing a matrix to an invariant coordinate subspace (matrix level)

## Extracting the data-register action of an ancilla circuit

The register realisation of Nielsen & Chuang's universality arguments places a gate on the wires of
a large register (data wires together with ancilla wires held in a fixed state) and reads off its
action on the *data* register. When the ancilla wires start in `|1⟩` and the gate leaves that
ancilla state invariant, the data action is exactly the restriction of the full `d × d` matrix to
the coordinate subspace spanned by the basis states with the ancillas set to `1`, where
`ι : α ↪ β` picks out those data basis indices among the full basis indices.

That restriction is the **submatrix** `M.submatrix ι ι`. The point of this file is that this
compression is a `monoid` homomorphism — not on all matrices (a submatrix along a non-surjective
index map is not multiplicative in general; `Matrix.submatrix_mul` needs a *bijective* middle index)
but on the submonoid of matrices that leave the subspace `range ι` invariant, where the cross terms
routed through indices outside `range ι` vanish. This is the generic algebraic core that the
register-layout bridge (identifying a compressed ancilla placement with a data-register gate)
consumes.

## The construction and results

Fix finite index types `α β` and an injection `ι : α → β` (the data basis indices among the full
basis indices).

* `PreservesRange ι N` — the matrix `N` leaves the coordinate subspace `range ι` invariant on the
  right: every column `N · (ι s)` is supported on `range ι` (`N r (ι s) = 0` for `r ∉ range ι`),
  i.e. `N` maps each range basis vector back into the range subspace.
* `compressionInvariant ι` — the `Submonoid` of range-preserving matrices (the identity preserves
  the range; a product of range-preserving matrices does, because every mixed term vanishes).
* `compress ι M := M.submatrix ι ι` — the compression to the subspace, with `compress_apply`,
  `compress_one` (`ι` injective), and the key `compress_mul`: for any `M` and any *range-preserving*
  `N`, `compress (M * N) = compress M * compress N` (the full sum over `β` collapses to the sum over
  `range ι`, the off-range terms killed by `N`'s invariance).
* `compressHom ι` — `compress` packaged as a `MonoidHom` from `compressionInvariant ι`; and
  `continuous_compress`, its continuity (a submatrix is continuous in the matrix entries).
-/

namespace AxQM.Concrete

open Matrix

variable {α β : Type*}

/-- **`N` preserves the coordinate subspace `range ι` on the right.** Every column of `N` indexed by
a range basis element `ι s` is supported on `range ι`: `N r (ι s) = 0` whenever `r ∉ range ι`.
Equivalently, `N` maps each basis vector `e_{ι s}` of the subspace back into the subspace — the
invariance that makes the compression `M ↦ M.submatrix ι ι` multiplicative. -/
def PreservesRange (ι : α → β) (N : Matrix β β ℂ) : Prop :=
  ∀ (s : α) (r : β), r ∉ Set.range ι → N r (ι s) = 0

/-- **The range-preserving matrices form a submonoid.** The identity preserves `range ι` (its column
`ι s` is the basis vector `e_{ι s}`, supported on `range ι`); and a product `M * N` of
range-preserving matrices preserves `range ι`, because in each entry `(M * N) r (ι s)` every term
`M r t * N t (ι s)` vanishes — the `t ∈ range ι` terms through `M`'s invariance (`M r (ι u) = 0`),
the `t ∉ range ι` terms through `N`'s (`N t (ι s) = 0`). -/
def compressionInvariant [Fintype β] [DecidableEq β] (ι : α → β) :
    Submonoid (Matrix β β ℂ) where
  carrier := {N | PreservesRange ι N}
  one_mem' := fun s r hr => by
    rw [Matrix.one_apply, ite_eq_right (fun h => hr ⟨s, h.symm⟩)]
  mul_mem' := fun {M N} hM hN s r hr => by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t ∈ Set.range ι
    · obtain ⟨u, rfl⟩ := ht
      rw [hM u r hr, zero_mul]
    · rw [hN s t ht, mul_zero]

/-- **A diagonal matrix preserves every coordinate subspace.** Each column `(diagonal d) · (ι s)`
is supported at the single index `ι s ∈ range ι`, so the off-range entries vanish
(`Matrix.diagonal_apply_ne`). In particular a diagonal matrix lies in `compressionInvariant ι`, so
`compressHom` applies to it and its products — the fact a diagonal (e.g. global-phase) register
placement is compressible. -/
theorem preservesRange_diagonal [DecidableEq β] (ι : α → β) (d : β → ℂ) :
    PreservesRange ι (Matrix.diagonal d) := fun s _r hr =>
  Matrix.diagonal_apply_ne d fun h => hr ⟨s, h.symm⟩

/-- **The compression of `M` to the coordinate subspace `range ι`** — the submatrix
`M.submatrix ι ι`, keeping only the rows and columns indexed by `range ι`. When `ι` picks out the
data basis indices of a register whose ancillas are held `|1⟩`, `compress ι M` is the action of `M`
on the data register. -/
def compress (ι : α → β) (M : Matrix β β ℂ) : Matrix α α ℂ :=
  M.submatrix ι ι

/-- Entry unfolding: `compress ι M x y = M (ι x) (ι y)`. Marked `@[simp]` (mirroring
`Matrix.submatrix_apply`) so that `simp` sees through the opaque `def compress` in consumers. -/
@[simp] theorem compress_apply (ι : α → β) (M : Matrix β β ℂ) (x y : α) :
    compress ι M x y = M (ι x) (ι y) := rfl

/-- **The compression of a diagonal matrix is diagonal.** For an injective index embedding `ι`,
`compress ι (diagonal d) = diagonal (d ∘ ι)`: the submatrix of a diagonal along an injective map is
again diagonal (`Matrix.submatrix_diagonal`), keeping the diagonal entries at the chosen indices. -/
theorem compress_diagonal [DecidableEq α] [DecidableEq β] {ι : α → β}
    (hι : Function.Injective ι) (d : β → ℂ) :
    compress ι (Matrix.diagonal d) = Matrix.diagonal (d ∘ ι) :=
  Matrix.submatrix_diagonal d ι hι

/-- **The compression of the identity is the identity** (for `ι` injective): `1 (ι x) (ι y)` is
`1` when `ι x = ι y`, i.e. (by injectivity) when `x = y`, matching `(1 : Matrix α α ℂ) x y`. -/
theorem compress_one [DecidableEq α] [DecidableEq β] {ι : α → β} (hι : Function.Injective ι) :
    compress ι (1 : Matrix β β ℂ) = 1 := by
  ext x y
  rw [compress_apply]
  simp only [Matrix.one_apply, hι.eq_iff]

/-- **The compression is multiplicative on a range-preserving right factor.** For any `M` and any
range-preserving `N` (`PreservesRange ι N`), `compress ι (M * N) = compress ι M * compress ι N`.
The full sum `∑ t : β, M (ι x) t * N t (ι z)` collapses to the sum `∑ y : α, M (ι x) (ι y) *
N (ι y) (ι z)` over `range ι`: the terms with `t ∉ range ι` vanish because `N t (ι z) = 0`, and the
surviving `range ι` terms reindex through `ι` (injective). -/
theorem compress_mul [Fintype α] [Fintype β] {ι : α → β} (hι : Function.Injective ι)
    (M : Matrix β β ℂ) {N : Matrix β β ℂ} (hN : PreservesRange ι N) :
    compress ι (M * N) = compress ι M * compress ι N := by
  classical
  ext x z
  rw [compress_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp_rw [compress_apply]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm.trans (Finset.sum_image hι.injOn)
  intro t _ ht
  have hrange : t ∉ Set.range ι := by
    rintro ⟨u, rfl⟩
    exact ht (Finset.mem_image_of_mem ι (Finset.mem_univ u))
  rw [hN z t hrange, mul_zero]

/-- **The compression as a monoid homomorphism** from the range-preserving submonoid
`compressionInvariant ι` to `Matrix α α ℂ`. `compress` sends the identity to the identity
(`compress_one`) and respects products of range-preserving matrices (`compress_mul`), so on the
whole submonoid it is a `MonoidHom` — in particular its image is a submonoid, the fact the density
transfer of the register-layout bridge consumes. -/
def compressHom [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {ι : α → β}
    (hι : Function.Injective ι) : compressionInvariant ι →* Matrix α α ℂ where
  toFun N := compress ι (N : Matrix β β ℂ)
  map_one' := compress_one hι
  map_mul' M N := compress_mul hι (M : Matrix β β ℂ) N.2

/-- **`compressHom` applies as `compress`.** The `_apply` simp lemma of the bundled hom, so
consumers (the register-layout bridge, the density transfer) rewrite `compressHom hι N` to
`compress ι ↑N` rather than reaching past the `MonoidHom` coercion by hand. -/
@[simp] theorem compressHom_apply [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {ι : α → β} (hι : Function.Injective ι) (N : compressionInvariant ι) :
    compressHom hι N = compress ι (N : Matrix β β ℂ) := rfl

/-- **The compression is continuous** in the matrix entries: a submatrix selects entries of the
input matrix, and each entry map is continuous (`Continuous.matrix_submatrix`). Consumers transport
a closure/limit of full-register matrices to their compressed data-register actions through this. -/
theorem continuous_compress (ι : α → β) :
    Continuous fun M : Matrix β β ℂ => compress ι M := by
  unfold compress
  exact continuous_id.matrix_submatrix ι ι

end AxQM.Concrete
