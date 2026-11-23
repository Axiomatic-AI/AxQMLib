/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringDiagonalize
import AxQM.Concrete.PauliStringCliffordConjugation
import AxQM.Concrete.SingleQubitWire

/-!
# Concrete: a tensor product of per-qubit gates is the ordered product of single-wire gates

This file proves the **flat-register
factorisation** of an `n`-fold tensor product `⨂ₖ Aₖ` into the ordered matrix product of its
single-wire embeddings — the elementary identity behind every *wire-by-wire* circuit decomposition
(each `Aₖ` is a separate one-qubit gate on wire `k`).

## Why this is needed (Nielsen & Chuang, Problem 4.3(3))

The `O(n)`-gate circuit implementing `exp(-i h_g g Δ)` opens with a **layer** `B = ⨂ₖ B_{gₖ}` of
single-qubit basis-change gates (`Concrete/PauliStringDiagonalize.lean`). To count that layer's
gates through the elementary-gate accountant `CircuitBudget` — which folds a *product* of
single-wire `Evolution`s one gate at a time — the tensor product `B` must first be exhibited as
such a product: `B = ∏ₜ Bₜ` with `Bₜ` acting only on wire `t`. This file supplies that identity; the
`Evolution`/`CircuitBudget` promotion of `B` is a separate physics-level step.

## What is proved

* `kronFamily_eq_prod_kronWireGate` — on the bit-string indexing `Fin n → Fin 2`, the tensor product
  is the ordered product of its one-wire embeddings:
  `kronFamily A = ∏_{j < n} kronWireGate j (A j)` (a `List.prod` over `List.finRange n`). The
  factors act on disjoint wires and commute, but the statement fixes the wire order for later use.
* `singleQubitOnWire_eq_submatrix_kronWireGate` — under any register encoding
  `enc : (Fin n → Fin 2) ≃ Fin d`, the wire gate `singleQubitOnWire enc j g` is the reindexing
  of the bit-string one-wire embedding `kronWireGate j g`.
* `kronFamilyStd_eq_prod_singleQubitOnWire` — combining the two, on the flat register `Fin (2ⁿ)`:
  `kronFamilyStd A = ∏_{t < n} singleQubitOnWire finFunctionFinEquiv t (A t)`.
* `kronFamilyStd_pauliDiagGate_eq_prod_singleQubitOnWire` — the Problem 4.3(3) instance: the
  basis-change `B = ⨂ₖ B_{gₖ}` (`kronFamilyStd (pauliDiagGate ∘ g)`) is the ordered product of the
  per-wire diagonalising gates `singleQubitOnWire finFunctionFinEquiv t (pauliDiagGate (g t))`.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- **A tensor product is the ordered product of its one-wire embeddings.** On the bit-string
register `Fin n → Fin 2`, `⨂ₖ Aₖ = ∏_{j<n} (I ⊗ ⋯ ⊗ A_j ⊗ ⋯ ⊗ I)`:
`kronFamily A = ∏_{j < n} kronWireGate j (A j)` (as a `List.prod` over `List.finRange n`). The
one-wire factors act on disjoint wires, so they commute and the order is immaterial; the statement
records a fixed order for the wire-by-wire circuit assembly. Proof: `kronFamily` is the monoid
homomorphism `(Fin n → M₂(ℂ)) →* M₂ₙ(ℂ)` sending pointwise products to matrix products
(`kronFamily_mul`, `kronFamily_one`); it carries the product `∏_j (1 update j ↦ A j)` of one-hot
families — which is `A` pointwise, each coordinate a list of `1`s with a single `A k`
(`List.prod_map_eq_pow_single`) — onto `∏_j kronWireGate j (A j)`. -/
theorem kronFamily_eq_prod_kronWireGate (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    kronFamily A = ((List.finRange n).map (fun j => kronWireGate j (A j))).prod := by
  -- `kronFamily` as a monoid homomorphism from the pointwise-product monoid of qubit gates.
  let φ : (Fin n → Matrix (Fin 2) (Fin 2) ℂ) →* Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
    { toFun := kronFamily
      map_one' := by simpa [Pi.one_def] using (kronFamily_one (n := n))
      map_mul' := fun A B => (kronFamily_mul A B).symm }
  -- The one-hot families multiply to `A` (pointwise: one non-identity factor per coordinate).
  have hprod : ((List.finRange n).map
      (fun j => Function.update (1 : Fin n → Matrix (Fin 2) (Fin 2) ℂ) j (A j))).prod = A := by
    funext k
    have h := map_list_prod (Pi.evalMonoidHom (fun _ : Fin n => Matrix (Fin 2) (Fin 2) ℂ) k)
      ((List.finRange n).map
        (fun j => Function.update (1 : Fin n → Matrix (Fin 2) (Fin 2) ℂ) j (A j)))
    simp only [List.map_map] at h
    rw [Pi.evalMonoidHom] at h
    simp only [MonoidHom.coe_mk, OneHom.coe_mk] at h
    rw [h, List.prod_map_eq_pow_single (a := k)]
    · simp [Function.update_self]
    · intro j hjk _
      simp [Function.update_of_ne (Ne.symm hjk)]
  calc kronFamily A = φ A := rfl
    _ = φ (((List.finRange n).map
        (fun j => Function.update (1 : Fin n → Matrix (Fin 2) (Fin 2) ℂ) j (A j))).prod) := by
          rw [hprod]
    _ = ((List.finRange n).map (fun j => kronWireGate j (A j))).prod := by
          rw [map_list_prod, List.map_map]; rfl

/-- **The wire gate is the reindexed one-wire embedding.** Under any register encoding
`enc : (Fin n → Fin 2) ≃ Fin d`, the single-qubit gate on wire `j` is the bit-string one-wire
embedding `kronWireGate j g` reindexed along `enc`:
`singleQubitOnWire enc j g = (kronWireGate j g).submatrix enc.symm enc.symm`. Proof: entrywise, the
`kronFamily` entry `∏ₖ (1 update j ↦ g)ₖ` splits off the `k = j` factor `g (x j) (x' j)`; the
remaining `k ≠ j` factors are the identity entries `[xₖ = x'ₖ]`, whose product
(`Finset.prod_boole`) is `[∀ k ≠ j, xₖ = x'ₖ]` — exactly the `singleQubitOnWire` conditional. -/
theorem singleQubitOnWire_eq_submatrix_kronWireGate {d : ℕ} (enc : (Fin n → Fin 2) ≃ Fin d)
    (j : Fin n) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    singleQubitOnWire enc j g = (kronWireGate j g).submatrix enc.symm enc.symm := by
  ext i i'
  simp only [singleQubitOnWire_apply, submatrix_apply, kronWireGate, kronFamily_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  have hentry : ∀ k ∈ Finset.univ.erase j,
      Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) j g k
        (enc.symm i k) (enc.symm i' k)
      = (if enc.symm i k = enc.symm i' k then (1 : ℂ) else 0) := by
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk), Matrix.one_apply]
  rw [Finset.prod_congr rfl hentry, Finset.prod_boole]
  have hcond : (∀ k ∈ Finset.univ.erase j, enc.symm i k = enc.symm i' k)
      ↔ (∀ k, k ≠ j → enc.symm i k = enc.symm i' k) := by
    simp [Finset.mem_erase]
  by_cases h : ∀ k, k ≠ j → enc.symm i k = enc.symm i' k
  · rw [ite_eq_left h, ite_eq_left (hcond.mpr h), mul_one]
  · rw [ite_eq_right h, ite_eq_right (mt hcond.mp h), mul_zero]

/-- **The flat-register tensor factorisation.** On the computational-basis register `Fin (2ⁿ)`,
`⨂ₖ Aₖ = ∏_{t<n} (single-qubit gate `A t` on wire `t`)`:
`kronFamilyStd A = ∏_{t < n} singleQubitOnWire finFunctionFinEquiv t (A t)`. This is the reindexing
of `kronFamily_eq_prod_kronWireGate` to `Fin (2ⁿ)`, pushing the `finFunctionFinEquiv`-reindexing
(a monoid homomorphism on matrices, `Matrix.submatrix_mul_equiv`/`submatrix_one_equiv`) through the
product and rewriting each factor with `singleQubitOnWire_eq_submatrix_kronWireGate`. -/
theorem kronFamilyStd_eq_prod_singleQubitOnWire (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    kronFamilyStd A
      = ((List.finRange n).map (fun t => singleQubitOnWire finFunctionFinEquiv t (A t))).prod := by
  -- The `finFunctionFinEquiv`-reindexing as a monoid homomorphism on `Fin (2ⁿ)`-matrices.
  let ψ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ →* Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    { toFun := fun M => M.submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm
      map_one' := Matrix.submatrix_one_equiv finFunctionFinEquiv.symm
      map_mul' := fun M N => (Matrix.submatrix_mul_equiv M N _ finFunctionFinEquiv.symm _).symm }
  have hstd : kronFamilyStd A = ψ (kronFamily A) := rfl
  rw [hstd, kronFamily_eq_prod_kronWireGate, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
  exact (singleQubitOnWire_eq_submatrix_kronWireGate finFunctionFinEquiv j (A j)).symm

/-- **Problem 4.3(3): the basis-change layer `B` factors into single-wire gates.** The single-qubit
basis change `B = ⨂ₖ B_{gₖ}` diagonalising the Pauli string `g`
(`kronFamilyStd (pauliDiagGate ∘ g)`, `Concrete/PauliStringDiagonalize.lean`) is the ordered matrix
product of the per-wire diagonalising
gates `B_{gₜ}` on wire `t`:
`kronFamilyStd (fun k => pauliDiagGate (g k))
  = ∏_{t < n} singleQubitOnWire finFunctionFinEquiv t (pauliDiagGate (g t))`. The instance of
`kronFamilyStd_eq_prod_singleQubitOnWire` at `A = pauliDiagGate ∘ g`; it exhibits the layer `B` as
literally `n` one-qubit gates, one per wire, the shape the elementary-gate budget of Problem 4.3(3)
folds over. -/
theorem kronFamilyStd_pauliDiagGate_eq_prod_singleQubitOnWire (g : Fin n → Fin 4) :
    kronFamilyStd (fun k => pauliDiagGate (g k))
      = ((List.finRange n).map
          (fun t => singleQubitOnWire finFunctionFinEquiv t (pauliDiagGate (g t)))).prod :=
  kronFamilyStd_eq_prod_singleQubitOnWire (fun k => pauliDiagGate (g k))

end AxQM.Concrete
