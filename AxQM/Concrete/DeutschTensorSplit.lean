/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.KroneckerReindex
import AxQM.Concrete.DeutschRegisterBridge

/-!
# Concrete: the leading-three-wires gate factors as `C²(g) ⊗ₖ 1` (matrix level, N&C Ex 4.44)

Every statement is about matrices — the multiply-controlled single-qubit wire gate
`mcCtrlSingleQubit`, the doubly-controlled `Fin 8` gate `ccontrolledMatFin8`, and the packed
Kronecker product `kroneckerFin` — together with the encoding equivalences.

## The register tensor-split of a base-register placement

The Deutsch-gate universality reduction (Nielsen & Chuang, Exercise 4.44) places
the gate `G = C²(iR_x(πα))` on three wires of a larger register and reads the result as `G` acting
on those three wires while the rest are untouched — a Kronecker product `C²(iR_x(πα)) ⊗ₖ 1`. The
base-register bridge (`Concrete/DeutschRegisterBridge.lean`) already identifies the
doubly-controlled `Fin 8` matrix with the base three-wire placement,
`ccontrolledMatFin8 g = mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 g`. This file supplies the
**register tensor-split**: relative to a register whose wires split as *three leading wires* plus a
block of `n` further wires, the placement of `g`'s doubly-controlled gate on the leading three wires
factors as that `Fin 8` gate tensored with the identity on the rest.

Concretely, fix a wire-splitting equivalence `e : Fin M ≃ Fin 3 ⊕ Fin n` (the leading three wires
are `e.symm (inl 0/1/2)`, the rest `e.symm (inr ·)`) and a `rest`-register encoding
`restEnc : (Fin n → Fin 2) ≃ Fin r`. The combined encoding `regTensorEnc e restEnc` packs the
leading three bits into `Fin 8` (via the canonical three-wire encoding `finThreeRegEnc`) and the
remaining bits into `Fin r` (via `restEnc`), then packs the pair `Fin 8 × Fin r` into the flat index
`Fin (8 · r)` along `finProdFinEquiv`. Against this encoding,

  `mcCtrlSingleQubit (regTensorEnc e restEnc) {e.symm (inl 0), e.symm (inl 1)} (e.symm (inl 2)) g
    = kroneckerFin (ccontrolledMatFin8 g) 1`.

Feeding this into the `quditGate`-of-Kronecker bridge (`Postulates/API/QuditKroneckerGate.lean`,
`quditGate_kroneckerFin_eq_congr_tmul`) reads the promoted placement as the physical Deutsch gate
tensored with the identity — the shape from which `deutschGate α` is named on register wires. The
general placement on *arbitrary* distinct wires reduces to this leading-three-wires case by the wire
relabelling of `Concrete/WireGateRelabel.lean`.

## The construction and results

* `regTensorEnc e restEnc : (Fin M → Fin 2) ≃ Fin (8 · r)` — the split encoding: leading three
  wires via `finThreeRegEnc`, remaining `n` wires via `restEnc`, packed with `finProdFinEquiv`.
* `regTensorEnc_symm_apply` — the decoding read wire by wire: bit `K` of the string decoded from
  the packed index `finProdFinEquiv (i₁, i₂)` is `finThreeRegEnc.symm i₁` on a leading wire
  `e K = inl a` and `restEnc.symm i₂` on a rest wire `e K = inr b`.
* `mcCtrlSingleQubit_regTensorEnc_eq_kroneckerFin` — the tensor-split identity, proved entrywise on
  packed indices via `wireGate_apply` and `kroneckerFin_apply`: the leading fibre/control conditions
  read off the `Fin 8` factor and the rest wires force the second factor's indices to agree
  (`= δ`, the identity block).
-/

namespace AxQM.Concrete

open Matrix

variable {M n r : ℕ}

/-- **The register tensor-split encoding.** For a wire-splitting equivalence
`e : Fin M ≃ Fin 3 ⊕ Fin n` and a `rest`-register encoding `restEnc : (Fin n → Fin 2) ≃ Fin r`,
`regTensorEnc e restEnc : (Fin M → Fin 2) ≃ Fin (8 · r)` reads a bit-string by packing its leading
three wires (`e ⁻¹ (inl ·)`) into `Fin 8` via the canonical three-wire encoding `finThreeRegEnc` and
its remaining wires (`e ⁻¹ (inr ·)`) into `Fin r` via `restEnc`, then packing the pair
`Fin 8 × Fin r` into the flat index `Fin (8 · r)` along `finProdFinEquiv`. This is the encoding
against which the leading-three-wires doubly-controlled gate factors as `C²(g) ⊗ₖ 1`. -/
def regTensorEnc (e : Fin M ≃ Fin 3 ⊕ Fin n) (restEnc : (Fin n → Fin 2) ≃ Fin r) :
    (Fin M → Fin 2) ≃ Fin (8 * r) :=
  (Equiv.arrowCongr e (Equiv.refl (Fin 2))).trans
    ((Equiv.sumArrowEquivProdArrow (Fin 3) (Fin n) (Fin 2)).trans
      ((Equiv.prodCongr finThreeRegEnc restEnc).trans finProdFinEquiv))

/-- **Wire-by-wire decoding of the tensor-split encoding.** The bit-string decoded from the packed
index `finProdFinEquiv (i₁, i₂)` reads its leading wires (`e K = inl a`) off the `Fin 8` factor
`finThreeRegEnc.symm i₁` and its rest wires (`e K = inr b`) off the `Fin r` factor
`restEnc.symm i₂`:

  `(regTensorEnc e restEnc).symm (finProdFinEquiv (i₁, i₂)) K
    = Sum.elim (finThreeRegEnc.symm i₁) (restEnc.symm i₂) (e K)`. -/
theorem regTensorEnc_symm_apply (e : Fin M ≃ Fin 3 ⊕ Fin n) (restEnc : (Fin n → Fin 2) ≃ Fin r)
    (i₁ : Fin 8) (i₂ : Fin r) (K : Fin M) :
    (regTensorEnc e restEnc).symm (finProdFinEquiv (i₁, i₂)) K
      = Sum.elim (finThreeRegEnc.symm i₁) (restEnc.symm i₂) (e K) := by
  simp only [regTensorEnc, Equiv.symm_trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map]
  rfl

/-- **The leading-three-wires placement factors as `C²(g) ⊗ₖ 1`** (Nielsen & Chuang, Exercise 4.44,
matrix level). Relative to the register tensor-split encoding `regTensorEnc e restEnc`, the
two-control single-qubit wire gate placing `g` on the leading target wire `e.symm (inl 2)` with
controls the leading wires `e.symm (inl 0)`, `e.symm (inl 1)` equals the doubly-controlled `Fin 8`
gate `C²(g)` tensored with the identity on the remaining register:

  `mcCtrlSingleQubit (regTensorEnc e restEnc) {e.symm (inl 0), e.symm (inl 1)} (e.symm (inl 2)) g
    = kroneckerFin (ccontrolledMatFin8 g) 1`.

Both sides are read entrywise on the packed indices `finProdFinEquiv (i₁, i₂)`,
`finProdFinEquiv (i₁', i₂')`. On the right, `kroneckerFin_apply` splits the entry into the `Fin 8`
factor `ccontrolledMatFin8 g i₁ i₁'` — itself the base placement
`mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 g i₁ i₁'` (`ccontrolledMatFin8_eq_mcCtrlSingleQubit`) —
and the identity factor `δ_{i₂ i₂'}`. On the left, `wireGate_apply` reads the fibre and control
conditions off the decoded string (`regTensorEnc_symm_apply`): the leading wires reproduce the
three-wire gate's conditions and the rest wires agree exactly when `i₂ = i₂'`, matching the
identity factor. -/
theorem mcCtrlSingleQubit_regTensorEnc_eq_kroneckerFin (e : Fin M ≃ Fin 3 ⊕ Fin n)
    (restEnc : (Fin n → Fin 2) ≃ Fin r) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    mcCtrlSingleQubit (regTensorEnc e restEnc) {e.symm (Sum.inl 0), e.symm (Sum.inl 1)}
        (e.symm (Sum.inl 2)) g
      = kroneckerFin (ccontrolledMatFin8 g) 1 := by
  ext I I'
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨i₁', i₂'⟩, rfl⟩ := finProdFinEquiv.surjective I'
  rw [kroneckerFin_apply, ccontrolledMatFin8_eq_mcCtrlSingleQubit, mcCtrlSingleQubit,
    mcCtrlSingleQubit, wireGate_apply, wireGate_apply, Matrix.one_apply]
  -- Abbreviations for the two factor decodings.
  set x := finThreeRegEnc.symm i₁ with hx
  set x' := finThreeRegEnc.symm i₁' with hx'
  -- Distinctness of the three leading wires.
  have h02 : e.symm (Sum.inl (0 : Fin 3)) ≠ e.symm (Sum.inl 2) := by
    intro h; exact absurd (Sum.inl_injective (e.symm.injective h)) (by decide)
  have h12 : e.symm (Sum.inl (1 : Fin 3)) ≠ e.symm (Sum.inl 2) := by
    intro h; exact absurd (Sum.inl_injective (e.symm.injective h)) (by decide)
  -- Target-bit reads: the decoded leading target bit is `x 2` / `x' 2`.
  have htgt : (regTensorEnc e restEnc).symm (finProdFinEquiv (i₁, i₂))
      (e.symm (Sum.inl 2)) = x 2 := by
    rw [regTensorEnc_symm_apply, Equiv.apply_symm_apply, Sum.elim_inl]
  have htgt' : (regTensorEnc e restEnc).symm (finProdFinEquiv (i₁', i₂'))
      (e.symm (Sum.inl 2)) = x' 2 := by
    rw [regTensorEnc_symm_apply, Equiv.apply_symm_apply, Sum.elim_inl]
  -- The leading fibre condition: agreement off the target wire, restricted to the `Fin 8` factor,
  -- and additionally forcing the second factor `i₂ = i₂'`.
  have hfib : (∀ K, K ≠ e.symm (Sum.inl 2) →
        (regTensorEnc e restEnc).symm (finProdFinEquiv (i₁, i₂)) K
          = (regTensorEnc e restEnc).symm (finProdFinEquiv (i₁', i₂')) K)
      ↔ ((∀ k : Fin 3, k ≠ 2 → x k = x' k) ∧ i₂ = i₂') := by
    constructor
    · intro h
      refine ⟨fun k hk => ?_, ?_⟩
      · have hne : e.symm (Sum.inl k) ≠ e.symm (Sum.inl 2) :=
          fun he => hk (Sum.inl_injective (e.symm.injective he))
        have := h (e.symm (Sum.inl k)) hne
        rwa [regTensorEnc_symm_apply, regTensorEnc_symm_apply, Equiv.apply_symm_apply,
          Sum.elim_inl, Sum.elim_inl] at this
      · apply restEnc.symm.injective
        funext b
        have hne : e.symm (Sum.inr b) ≠ e.symm (Sum.inl 2) :=
          fun he => Sum.inr_ne_inl (e.symm.injective he)
        have := h (e.symm (Sum.inr b)) hne
        rwa [regTensorEnc_symm_apply, regTensorEnc_symm_apply, Equiv.apply_symm_apply,
          Sum.elim_inr, Sum.elim_inr] at this
    · rintro ⟨hlead, hrest⟩ K hK
      rw [regTensorEnc_symm_apply, regTensorEnc_symm_apply]
      rcases heK : e K with a | b
      · rw [Sum.elim_inl, Sum.elim_inl]
        rcases eq_or_ne a 2 with rfl | ha
        · exact absurd (by rw [← heK, Equiv.symm_apply_apply]) hK
        · exact hlead a ha
      · rw [Sum.elim_inr, Sum.elim_inr, hrest]
  -- The leading control condition (both the big and the base form) reduces to `x 0 = 1 ∧ x 1 = 1`.
  have hctrlBig : (∀ K ∈ ({e.symm (Sum.inl 0), e.symm (Sum.inl 1)} : Finset (Fin M)),
        Function.update ((regTensorEnc e restEnc).symm (finProdFinEquiv (i₁, i₂)))
          (e.symm (Sum.inl 2)) 0 K = 1)
      ↔ (x 0 = 1 ∧ x 1 = 1) := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := h (e.symm (Sum.inl 0)) (by simp)
        rwa [Function.update_of_ne h02, regTensorEnc_symm_apply, Equiv.apply_symm_apply,
          Sum.elim_inl] at this
      · have := h (e.symm (Sum.inl 1)) (by simp)
        rwa [Function.update_of_ne h12, regTensorEnc_symm_apply, Equiv.apply_symm_apply,
          Sum.elim_inl] at this
    · rintro ⟨h0, h1⟩ K hK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hK
      rcases hK with rfl | rfl
      · rw [Function.update_of_ne h02, regTensorEnc_symm_apply, Equiv.apply_symm_apply,
          Sum.elim_inl]; exact h0
      · rw [Function.update_of_ne h12, regTensorEnc_symm_apply, Equiv.apply_symm_apply,
          Sum.elim_inl]; exact h1
  have hctrlBase : (∀ k ∈ ({0, 1} : Finset (Fin 3)), Function.update x 2 0 k = 1)
      ↔ (x 0 = 1 ∧ x 1 = 1) := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := h 0 (by decide); rwa [Function.update_of_ne (by decide)] at this
      · have := h 1 (by decide); rwa [Function.update_of_ne (by decide)] at this
    · rintro ⟨h0, h1⟩ k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · rwa [Function.update_of_ne (by decide)]
      · rwa [Function.update_of_ne (by decide)]
  -- Assemble: rewrite target reads, then split on the leading fibre condition.
  rw [htgt, htgt']
  simp only [hfib, hctrlBig, hctrlBase]
  by_cases hf : (∀ k : Fin 3, k ≠ 2 → x k = x' k) ∧ i₂ = i₂'
  · obtain ⟨hlead, rfl⟩ := hf
    rw [ite_eq_left ⟨hlead, rfl⟩, ite_eq_left hlead, ite_eq_left rfl, mul_one]
  · rw [ite_eq_right hf]
    by_cases hlead : ∀ k : Fin 3, k ≠ 2 → x k = x' k
    · -- leading fibre holds, so `i₂ ≠ i₂'`; the identity factor kills the product
      have hne : i₂ ≠ i₂' := fun h => hf ⟨hlead, h⟩
      rw [ite_eq_right hne, mul_zero]
    · rw [ite_eq_right hlead, zero_mul]

end AxQM.Concrete
