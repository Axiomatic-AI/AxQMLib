/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliEigenvectors

/-!
# Concrete: tensor powers of the plus state (Nielsen & Chuang, Exercise 2.26)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.26 (p. 74)
asks: for `|ψ⟩ = (|0⟩ + |1⟩)/√2`, write out `|ψ⟩^⊗2` and `|ψ⟩^⊗3` explicitly, **both**
in terms of tensor products like `|0⟩|1⟩` and **using the Kronecker product**.

The state `|ψ⟩` is exactly the `X`-eigenvector `|+⟩` (`xPlus` from
`Concrete.PauliEigenvectors`); `xPlus_eq_smul_add` records this identification
`|+⟩ = (|0⟩ + |1⟩)/√2`. This is pure linear algebra over `ℂ²`.

## The Kronecker product of vectors

`vecKron u v` is the Kronecker (tensor) product of two finite complex column vectors,
indexed by the product index type: `(u ⊗ v) (i, j) = uᵢ · vⱼ`. Viewing `u, v` as
column vectors, this is their Kronecker product, with the row index of the result the
pair `(i, j)` — the row-major ordering that `finProdFinEquiv` flattens to `n·i + j`,
so `vecKron` *is* N&C's Kronecker product up to that reindexing. A basis ket `|i⟩|j⟩`
of the tensor-product space is `vecKron (ket i) (ket j)`, which is the standard basis
vector supported at `(i, j)`; that identification is what makes the two requested
representations — a sum of basis kets, and an explicit (uniform) column vector — the
same object.

## Contents

* `vecKron`, `vecKron_apply` — the vector Kronecker product and its entrywise value.
* `xPlus_eq_smul_add` — `|+⟩` equals `(|0⟩ + |1⟩)/√2` (the exercise's `|ψ⟩`). The
  component formula `xPlus_apply` (`|+⟩ᵢ = 1/√2`) lives with `xPlus` in
  `Concrete.PauliEigenvectors` and is used here via the import.
* `vecKron_xPlus_xPlus` — the Kronecker-product form of `|ψ⟩^⊗2`: the explicit
  4-component column vector with every entry `1/2`, i.e. `½(1, 1, 1, 1)ᵀ`.
* `vecKron_xPlus_xPlus_eq_sum` — the tensor-product form of `|ψ⟩^⊗2`:
  `½(|00⟩ + |01⟩ + |10⟩ + |11⟩)`.
* `vecKron_xPlus_vecKron_xPlus_xPlus` — the Kronecker-product form of `|ψ⟩^⊗3`: the
  explicit 8-component column vector with every entry `1/(2√2) = (1/√2)/2`.
* `vecKron_xPlus_vecKron_xPlus_xPlus_eq_sum` — the tensor-product form of `|ψ⟩^⊗3`:
  `1/(2√2) · (|000⟩ + |001⟩ + ⋯ + |111⟩)`, all eight computational-basis kets.

## Design notes

* `|ψ⟩^⊗3` is right-nested, `|ψ⟩ ⊗ (|ψ⟩ ⊗ |ψ⟩)`, so it is indexed by
  `Fin 2 × Fin 2 × Fin 2 = Fin 2 × (Fin 2 × Fin 2)`; Kronecker association is a mere
  reindexing, so the grouping is immaterial to the "written-out" content.
* The two forms are stated as separate named theorems (not a monolithic conjunction),
  one per representation the exercise requests. The uniform-vector forms use the shared
  arithmetic fact `invSqrt2_mul_self : (1/√2)·(1/√2) = 1/2`; the sum-of-kets forms hold
  because at each index exactly one of the enumerated basis kets is supported.
-/

namespace AxQM.Concrete

open Matrix

/-- The Kronecker (tensor) product of two finite complex column vectors, indexed by the
product index type: `(u ⊗ v) (i, j) = uᵢ · vⱼ`. This is the Kronecker product of `u`
and `v` viewed as column vectors, with the row index of the result the pair `(i, j)`
(row-major order flattens `(i, j)` to `n·i + j` via `finProdFinEquiv`). The tensor-product
basis ket `|i⟩|j⟩` is `vecKron (ket i) (ket j)`. -/
def vecKron {m n : Type*} (u : m → ℂ) (v : n → ℂ) : m × n → ℂ := fun p => u p.1 * v p.2

/-- The `(i, j)` entry of the Kronecker product `u ⊗ v` is `uᵢ · vⱼ`. -/
@[simp] theorem vecKron_apply {m n : Type*} (u : m → ℂ) (v : n → ℂ) (i : m) (j : n) :
    vecKron u v (i, j) = u i * v j := rfl

/-- The plus state written in N&C's Exercise 2.26 form `|ψ⟩ = (|0⟩ + |1⟩)/√2`, i.e.
`|+⟩ = (1/√2) · (|0⟩ + |1⟩)`. -/
theorem xPlus_eq_smul_add : xPlus = invSqrt2 • (ket 0 + ket 1) := by
  funext i
  fin_cases i <;>
    simp [xPlus, ket]

/-- The minus state in the analogous form `|-⟩ = (|0⟩ - |1⟩)/√2`, i.e.
`|-⟩ = (1/√2) · (|0⟩ - |1⟩)`. The sign-flipped companion of `xPlus_eq_smul_add`. -/
theorem xMinus_eq_smul_sub : xMinus = invSqrt2 • (ket 0 - ket 1) := by
  funext i
  fin_cases i <;>
    simp [xMinus, ket]

/-! ### `|ψ⟩^⊗2` -/

/-- **`|ψ⟩^⊗2` via the Kronecker product.** For `|ψ⟩ = (|0⟩ + |1⟩)/√2`, the Kronecker
product `|ψ⟩ ⊗ |ψ⟩` is the explicit 4-component column vector with every entry `1/2`:
`|ψ⟩^⊗2 = ½(1, 1, 1, 1)ᵀ`. -/
theorem vecKron_xPlus_xPlus : vecKron xPlus xPlus = fun _ => (1 / 2 : ℂ) := by
  funext p
  simp only [vecKron, xPlus_apply, invSqrt2_mul_self]
  norm_num

/-- **`|ψ⟩^⊗2` in terms of tensor products.** For `|ψ⟩ = (|0⟩ + |1⟩)/√2`,
`|ψ⟩^⊗2 = ½(|00⟩ + |01⟩ + |10⟩ + |11⟩)`, where `|ij⟩ = vecKron (ket i) (ket j)`. -/
theorem vecKron_xPlus_xPlus_eq_sum :
    vecKron xPlus xPlus =
      (1 / 2 : ℂ) • (vecKron (ket 0) (ket 0) + vecKron (ket 0) (ket 1) +
        vecKron (ket 1) (ket 0) + vecKron (ket 1) (ket 1)) := by
  funext p
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;>
    simp [vecKron, ket, Pi.add_apply, Pi.smul_apply, invSqrt2_mul_self]

/-! ### `|ψ⟩^⊗3` -/

/-- **`|ψ⟩^⊗3` via the Kronecker product.** For `|ψ⟩ = (|0⟩ + |1⟩)/√2`, the Kronecker
product `|ψ⟩ ⊗ (|ψ⟩ ⊗ |ψ⟩)` is the explicit 8-component column vector with every entry
`1/(2√2) = (1/√2)/2`. -/
theorem vecKron_xPlus_vecKron_xPlus_xPlus :
    vecKron xPlus (vecKron xPlus xPlus) = fun _ => invSqrt2 / 2 := by
  funext p
  obtain ⟨i, j, k⟩ := p
  simp only [vecKron, xPlus_apply, invSqrt2_mul_self]
  ring

/-- **`|ψ⟩^⊗3` in terms of tensor products.** For `|ψ⟩ = (|0⟩ + |1⟩)/√2`,
`|ψ⟩^⊗3 = 1/(2√2) · (|000⟩ + |001⟩ + |010⟩ + |011⟩ + |100⟩ + |101⟩ + |110⟩ + |111⟩)`,
the equal superposition of all eight computational-basis kets
`|ijk⟩ = vecKron (ket i) (vecKron (ket j) (ket k))`. -/
theorem vecKron_xPlus_vecKron_xPlus_xPlus_eq_sum :
    vecKron xPlus (vecKron xPlus xPlus) =
      (invSqrt2 / 2) • (vecKron (ket 0) (vecKron (ket 0) (ket 0)) +
        vecKron (ket 0) (vecKron (ket 0) (ket 1)) +
        vecKron (ket 0) (vecKron (ket 1) (ket 0)) +
        vecKron (ket 0) (vecKron (ket 1) (ket 1)) +
        vecKron (ket 1) (vecKron (ket 0) (ket 0)) +
        vecKron (ket 1) (vecKron (ket 0) (ket 1)) +
        vecKron (ket 1) (vecKron (ket 1) (ket 0)) +
        vecKron (ket 1) (vecKron (ket 1) (ket 1))) := by
  funext p
  obtain ⟨i, j, k⟩ := p
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [vecKron, ket, Pi.add_apply, Pi.smul_apply, invSqrt2_mul_self] <;>
    ring

end AxQM.Concrete
