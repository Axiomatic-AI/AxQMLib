/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorCodeProjector

/-!
# AxQM.Postulates.API — the Shor-code stabilizer generators of Figure 10.11

Infrastructure for the **stabilizer** of the nine-qubit Shor code (Nielsen &
Chuang §10.5.6, Figure 10.11): the six bit-flip (Z-type) generators, together with the two
phase-flip (X-type) generators already built in `ShorPhaseSyndrome.lean`, and the fact that every
one of them *fixes* both logical codewords `|0_L⟩`, `|1_L⟩` (eq. (10.13)). This is the reusable
theory behind Exercise 10.47 (`AxQM/NC/Ch10/Exercise10_47.lean`).

On the nine-qubit register `shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`, whose qubits are
grouped into three blocks `(q₁q₂q₃)(q₄q₅q₆)(q₇q₈q₉)`, the eight stabilizer generators of Figure
10.11 are the **within-block** bit-flip syndrome operators and the **between-block** phase-flip
syndrome operators:

| Fig 10.11 | operator       | this development                    |
| --------- | -------------- | ---------------------------------- |
| `g₁`      | `Z₁Z₂`         | `shorZ12` = `Z₁Z₂` on block 1      |
| `g₂`      | `Z₂Z₃`         | `shorZ23` = `Z₂Z₃` on block 1      |
| `g₃`      | `Z₄Z₅`         | `shorZ45` = `Z₁Z₂` on block 2      |
| `g₄`      | `Z₅Z₆`         | `shorZ56` = `Z₂Z₃` on block 2      |
| `g₅`      | `Z₇Z₈`         | `shorZ78` = `Z₁Z₂` on block 3      |
| `g₆`      | `Z₈Z₉`         | `shorZ89` = `Z₂Z₃` on block 3      |
| `g₇`      | `X₁X₂X₃X₄X₅X₆` | `shorPhaseSyndromeX123456`         |
| `g₈`      | `X₄X₅X₆X₇X₈X₉` | `shorPhaseSyndromeX456789`         |

## The two physical mechanisms

* **Z-type (within a block).** A codeword's block is the cat state
  `catBlockState σ = (|000⟩ + (−1)^σ|111⟩)/√2`, on which both `|000⟩` and `|111⟩` carry *matching*
  bits at any pair of positions — so `Z₁Z₂` and `Z₂Z₃` act by the trivial parity sign `(−1)^0 = +1`.
  Hence every block-Z syndrome operator fixes its cat block
  (`zzIObservable_hasEigenstate_one_catBlockState`, `izzObservable_hasEigenstate_one_catBlockState`)
  and, tensored with identities on the other two blocks, fixes the whole codeword.
* **X-type (between two blocks).** `X⊗X⊗X` reads a block's `±` sign `(−1)^σ`, so `X₁X₂X₃X₄X₅X₆`
  acts on `|s_L⟩ = shorCatProduct s s s` by `(−1)^{s+s} = +1`: the two spanned blocks have *equal*
  signs in a codeword (`shorPhaseSyndromeX123456_op_shorCatProduct_vec`). Likewise `X₄X₅X₆X₇X₈X₉`.

## General helpers introduced here

The composition of block eigenstates into codeword eigenstates rests on two gate-agnostic lemmas,
proved here and reusable throughout (cf. the general `Observable.tmul_op_mul_self` introduced beside
the syndrome observables):

* `Observable.HasEigenstate.tmul` — a tensor of eigenstates is an eigenstate of the tensor
  observable, with the product eigenvalue.
* `Observable.hasEigenstate_one_id` — the identity observable fixes every state (eigenvalue `1`).

Every stabilization statement is of the form `Observable.HasEigenstate 1`, and the generators are
observables on `shorReg`. These are the statements used in Exercise 10.47
(`AxQM/NC/Ch10/Exercise10_47.lean`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-! ### General eigenstate-composition helpers -/

/-- **A tensor of eigenstates is an eigenstate of the tensor observable.** If `A ψ = μ ψ` and
`B φ = ν φ` then `(A ⊗ B)(ψ ⊗ φ) = (μν)(ψ ⊗ φ)`: `A ⊗ B` acts factorwise
(`Observable.tmul_op_tmul`), each factor contributes its eigenvalue, and the two scalars combine
(`TensorProduct.smul_tmul_smul`). A gate-agnostic bridge for building joint eigenstates on
composite systems out of per-factor eigenstates. -/
theorem Observable.HasEigenstate.tmul {A : Observable S} {B : Observable T}
    {μ ν : ℝ} {ψ : PureState S} {φ : PureState T}
    (hA : A.HasEigenstate μ ψ) (hB : B.HasEigenstate ν φ) :
    (A ⊗ B).HasEigenstate (μ * ν) (ψ ⊗ φ) := by
  rw [Observable.HasEigenstate, PureState.tmul_vec, Observable.tmul_op_tmul, hA, hB,
    TensorProduct.smul_tmul_smul]
  norm_cast

/-- **The identity observable fixes every state:** `id ψ = ψ`, i.e. every pure state is an
eigenstate of `Observable.id S` with eigenvalue `1`. The eigenstate-side companion of
`Observable.id_op`, used to leave the untouched blocks of the Shor register alone when a
single-block generator is tensored across the whole register. -/
theorem Observable.hasEigenstate_one_id (ψ : PureState S) :
    (Observable.id S).HasEigenstate 1 ψ := by
  rw [Observable.HasEigenstate, Observable.id_op, one_apply_eq_self,
    Complex.ofReal_one, one_smul]

/-! ### The block bit-flip syndrome operators fix a cat block -/

/-- **`Z₁Z₂` fixes a cat block:** `catBlockState σ = (|000⟩ + (−1)^σ|111⟩)/√2` is a `+1`
eigenstate of `zzIObservable`. Both supporting kets `|000⟩`, `|111⟩` have matching first-two bits,
so `Z₁Z₂` acts by `(−1)^0·(−1)^0 = +1` on `|000⟩` and `(−1)^1·(−1)^1 = +1` on `|111⟩`
(`zzI_op_ket`), leaving the cat vector unchanged; transported to the normalised state via
`Observable.hasEigenstate_of_smul`. -/
theorem zzIObservable_hasEigenstate_one_catBlockState (σ : Fin 2) :
    zzIObservable.HasEigenstate 1 (catBlockState σ) :=
  Observable.hasEigenstate_of_smul
    (PureState.normalize_vec (catBlockVec σ) (catBlockVec_ne_zero σ))
    (by simp only [catBlockVec, map_add, map_smul, zzI_op_ket]; norm_num)

/-- **`Z₂Z₃` fixes a cat block:** `catBlockState σ` is a `+1` eigenstate of `izzObservable`, for
the same parity reason as `Z₁Z₂` — the last-two bits of `|000⟩` and `|111⟩` also match, giving
trivial sign `+1` (`izz_op_ket`). -/
theorem izzObservable_hasEigenstate_one_catBlockState (σ : Fin 2) :
    izzObservable.HasEigenstate 1 (catBlockState σ) :=
  Observable.hasEigenstate_of_smul
    (PureState.normalize_vec (catBlockVec σ) (catBlockVec_ne_zero σ))
    (by simp only [catBlockVec, map_add, map_smul, izz_op_ket]; norm_num)

/-! ### The six bit-flip (Z-type) generators of Figure 10.11

Each is a block bit-flip syndrome operator (`Z₁Z₂ = zzIObservable`, `Z₂Z₃ = izzObservable`) placed
on one of the three blocks of `shorReg`, with the identity on the other two blocks. -/

/-- **`g₁ = Z₁Z₂`** of Figure 10.11: `Z₁Z₂` on block 1, identity on blocks 2, 3. -/
def shorZ12 : Observable shorReg :=
  zzIObservable ⊗ (Observable.id bitFlipReg ⊗ Observable.id bitFlipReg)

/-- **`g₂ = Z₂Z₃`** of Figure 10.11: `Z₂Z₃` on block 1, identity on blocks 2, 3. -/
def shorZ23 : Observable shorReg :=
  izzObservable ⊗ (Observable.id bitFlipReg ⊗ Observable.id bitFlipReg)

/-- **`g₃ = Z₄Z₅`** of Figure 10.11: identity on block 1, `Z₁Z₂` on block 2, identity on block 3. -/
def shorZ45 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (zzIObservable ⊗ Observable.id bitFlipReg)

/-- **`g₄ = Z₅Z₆`** of Figure 10.11: identity on block 1, `Z₂Z₃` on block 2, identity on block 3. -/
def shorZ56 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (izzObservable ⊗ Observable.id bitFlipReg)

/-- **`g₅ = Z₇Z₈`** of Figure 10.11: identity on blocks 1, 2, `Z₁Z₂` on block 3. -/
def shorZ78 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (Observable.id bitFlipReg ⊗ zzIObservable)

/-- **`g₆ = Z₈Z₉`** of Figure 10.11: identity on blocks 1, 2, `Z₂Z₃` on block 3. -/
def shorZ89 : Observable shorReg :=
  Observable.id bitFlipReg ⊗ (Observable.id bitFlipReg ⊗ izzObservable)

/-! ### Every generator fixes both codewords -/

/-- **`Z₁Z₂` stabilizes both codewords.** `shorZ12` fixes
`|s_L⟩ = catBlockState s ⊗ (catBlockState s ⊗ catBlockState s)`: `Z₁Z₂` fixes block 1's cat state
and the identities fix blocks 2, 3, so the product eigenvalue is `1·(1·1) = 1`. -/
theorem shorZ12_hasEigenstate_one_shorCodeword (s : Fin 2) :
    shorZ12.HasEigenstate 1 (shorCodeword s) := by
  have h := (zzIObservable_hasEigenstate_one_catBlockState s).tmul
    ((Observable.hasEigenstate_one_id (catBlockState s)).tmul
      (Observable.hasEigenstate_one_id (catBlockState s)))
  simpa [shorZ12, shorCodeword, shorCatProduct] using h

/-- **`Z₂Z₃` stabilizes both codewords.** Same mechanism as `shorZ12`, `Z₂Z₃` fixing block 1. -/
theorem shorZ23_hasEigenstate_one_shorCodeword (s : Fin 2) :
    shorZ23.HasEigenstate 1 (shorCodeword s) := by
  have h := (izzObservable_hasEigenstate_one_catBlockState s).tmul
    ((Observable.hasEigenstate_one_id (catBlockState s)).tmul
      (Observable.hasEigenstate_one_id (catBlockState s)))
  simpa [shorZ23, shorCodeword, shorCatProduct] using h

/-- **`Z₄Z₅` stabilizes both codewords.** `Z₁Z₂` fixes block 2, identities fix blocks 1, 3. -/
theorem shorZ45_hasEigenstate_one_shorCodeword (s : Fin 2) :
    shorZ45.HasEigenstate 1 (shorCodeword s) := by
  have h := (Observable.hasEigenstate_one_id (catBlockState s)).tmul
    ((zzIObservable_hasEigenstate_one_catBlockState s).tmul
      (Observable.hasEigenstate_one_id (catBlockState s)))
  simpa [shorZ45, shorCodeword, shorCatProduct] using h

/-- **`Z₅Z₆` stabilizes both codewords.** `Z₂Z₃` fixes block 2, identities fix blocks 1, 3. -/
theorem shorZ56_hasEigenstate_one_shorCodeword (s : Fin 2) :
    shorZ56.HasEigenstate 1 (shorCodeword s) := by
  have h := (Observable.hasEigenstate_one_id (catBlockState s)).tmul
    ((izzObservable_hasEigenstate_one_catBlockState s).tmul
      (Observable.hasEigenstate_one_id (catBlockState s)))
  simpa [shorZ56, shorCodeword, shorCatProduct] using h

/-- **`Z₇Z₈` stabilizes both codewords.** `Z₁Z₂` fixes block 3, identities fix blocks 1, 2. -/
theorem shorZ78_hasEigenstate_one_shorCodeword (s : Fin 2) :
    shorZ78.HasEigenstate 1 (shorCodeword s) := by
  have h := (Observable.hasEigenstate_one_id (catBlockState s)).tmul
    ((Observable.hasEigenstate_one_id (catBlockState s)).tmul
      (zzIObservable_hasEigenstate_one_catBlockState s))
  simpa [shorZ78, shorCodeword, shorCatProduct] using h

/-- **`Z₈Z₉` stabilizes both codewords.** `Z₂Z₃` fixes block 3, identities fix blocks 1, 2. -/
theorem shorZ89_hasEigenstate_one_shorCodeword (s : Fin 2) :
    shorZ89.HasEigenstate 1 (shorCodeword s) := by
  have h := (Observable.hasEigenstate_one_id (catBlockState s)).tmul
    ((Observable.hasEigenstate_one_id (catBlockState s)).tmul
      (izzObservable_hasEigenstate_one_catBlockState s))
  simpa [shorZ89, shorCodeword, shorCatProduct] using h

/-- **`X₁X₂X₃X₄X₅X₆` stabilizes both codewords.** On `|s_L⟩ = shorCatProduct s s s` the operator
acts by `(−1)^{s+s}` (`shorPhaseSyndromeX123456_op_shorCatProduct_vec`) — blocks 1 and 2 share the
sign `s`, so the exponent `s + s` is even and the eigenvalue is `+1`. -/
theorem shorPhaseSyndromeX123456_hasEigenstate_one_shorCodeword (s : Fin 2) :
    shorPhaseSyndromeX123456.HasEigenstate 1 (shorCodeword s) := by
  rw [Observable.HasEigenstate, shorCodeword, shorPhaseSyndromeX123456_op_shorCatProduct_vec,
    Even.neg_one_pow ⟨(s : ℕ), rfl⟩]
  simp

/-- **`X₄X₅X₆X₇X₈X₉` stabilizes both codewords.** On `|s_L⟩` the operator acts by `(−1)^{s+s}`
(`shorPhaseSyndromeX456789_op_shorCatProduct_vec`) — blocks 2 and 3 also share the sign `s`, so the
eigenvalue is `+1`. -/
theorem shorPhaseSyndromeX456789_hasEigenstate_one_shorCodeword (s : Fin 2) :
    shorPhaseSyndromeX456789.HasEigenstate 1 (shorCodeword s) := by
  rw [Observable.HasEigenstate, shorCodeword, shorPhaseSyndromeX456789_op_shorCatProduct_vec,
    Even.neg_one_pow ⟨(s : ℕ), rfl⟩]
  simp

end AxQM
