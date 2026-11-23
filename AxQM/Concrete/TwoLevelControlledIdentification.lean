/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.TwoLevelGrayWalk

/-!
# Concrete: a two-level unitary supported on a bit-adjacent pair *is* a controlled single-qubit gate

(Nielsen & Chuang §4.5.2, the first-stage → controlled-`Ũ` junction, p. 191–193.)

The §4.5.2 realisation of a two-level unitary as a circuit of single-qubit and `CNOT` gates has two
stages. The **first stage** (`swapConj_swapChain_grayCode_support`) walks a Gray code to relocate
the two active basis states of a two-level unitary onto a pair `{enc e, enc t}` differing in exactly
one bit; the **second stage** applies a controlled single-qubit gate. This file supplies the
*junction* between them: a two-level unitary whose support is a bit-adjacent pair is, verbatim, one
of the controlled single-qubit gates `ctrlSingleQubit` of `Concrete/ControlledSingleQubit.lean`.

`ctrlSingleQubit_eq_twoLevelEmbed` already runs the *forward* direction — a controlled
single-qubit gate is a two-level embedding. The converse needed here is structural, in two layers.

## The general two-level converse (reusable, no bit-strings)

For any `d × d` matrix `W` agreeing with the identity off a coordinate pair `{p, q}` (`p ≠ q`):

* `AxQM.Concrete.twoLevelBlock W p q` — the `2 × 2` block `!![W p p, W p q; W q p, W q q]`.
* `AxQM.Concrete.eq_twoLevelEmbed_of_support` —
  **`W = twoLevelEmbed p q (twoLevelBlock W p q)`**: a matrix supported on `{p, q}` is the two-level
  embedding of its own block. This is the structural converse of `isTwoLevelUnitary_twoLevelEmbed`.
* `AxQM.Concrete.twoLevelEmbed_injective` — `twoLevelEmbed p q` is injective on the block
  (`p ≠ q`), read off the four block entries.
* `AxQM.Concrete.twoLevelBlock_mem_unitaryGroup` — **the block of a two-level *unitary* is
  unitary**: from `Wᴴ W = 1`, the `*`-homomorphism laws give `twoLevelEmbed p q (GᴴG) =
  twoLevelEmbed p q 1`, so injectivity forces `Gᴴ G = 1`.

## The controlled single-qubit identification

* `AxQM.Concrete.eq_ctrlSingleQubit_of_support` — **a two-level unitary supported on a
  bit-adjacent encoded pair `{enc a, enc b}` (`differsInOneBit a b`) equals
  `ctrlSingleQubit enc j c Ũ`** for the differing bit `j`, control pattern `c = a`, and a `2 × 2`
  *unitary* block `Ũ`. The two active states `{c[j↦0], c[j↦1]}` are exactly `{a, b}` (in some
  order — `update_zero_one_eq_pair`), so the general converse applies at the pair
  `(enc c[j↦0], enc c[j↦1])` and `ctrlSingleQubit_eq_twoLevelEmbed` closes it.
* `AxQM.Concrete.swapConj_swapChain_grayCode_eq_ctrlSingleQubit` — **the junction,
  assembled**: conjugating a two-level unitary supported on `{enc s, enc t}` (`s ≠ t`) by the
  Gray-code swap chain yields, verbatim, a controlled single-qubit gate `ctrlSingleQubit enc j c Ũ`
  with `Ũ` unitary. This hands the §4.5.2 first stage's output straight to the controlled-`Ũ`
  object.

## Use

This is used in the §4.5.2 development of Exercise 4.43's `n`-qubit lift; the statement of
Exercise 4.43 is in `AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- The `2 × 2` principal block of a `d × d` matrix `W` at the coordinate pair `{p, q}`
(`p ↦ 0`, `q ↦ 1`). For a matrix supported on `{p, q}` it is the block `twoLevelEmbed` re-embeds
(`eq_twoLevelEmbed_of_support`). -/
def twoLevelBlock (W : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![W p p, W p q; W q p, W q q]

/-- Off the `{p, q} × {p, q}` block, `twoLevelEmbed p q G` agrees with the identity — the "acts
non-trivially on at most two components" clause, extracted as a reusable entry lemma. -/
theorem twoLevelEmbed_eq_one_of_off (G : Matrix (Fin 2) (Fin 2) ℂ) {p q i j : Fin d}
    (hij : (i ≠ p ∧ i ≠ q) ∨ (j ≠ p ∧ j ≠ q)) :
    twoLevelEmbed p q G i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  rw [twoLevelEmbed_apply, Matrix.one_apply]
  rcases hij with ⟨hip, hiq⟩ | ⟨hjp, hjq⟩ <;> split_ifs <;> simp_all

/-- **A matrix supported on a coordinate pair is the two-level embedding of its own block.** If `W`
agrees with the identity on every entry off the `{p, q} × {p, q}` block (`p ≠ q`), then
`W = twoLevelEmbed p q (twoLevelBlock W p q)`. This is the structural converse of
`isTwoLevelUnitary_twoLevelEmbed`. -/
theorem eq_twoLevelEmbed_of_support {W : Matrix (Fin d) (Fin d) ℂ} {p q : Fin d} (hpq : p ≠ q)
    (hsupp : ∀ i j : Fin d, (i ≠ p ∧ i ≠ q) ∨ (j ≠ p ∧ j ≠ q) →
      W i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) :
    W = twoLevelEmbed p q (twoLevelBlock W p q) := by
  ext i j
  by_cases hoff : (i ≠ p ∧ i ≠ q) ∨ (j ≠ p ∧ j ≠ q)
  · rw [hsupp i j hoff, twoLevelEmbed_eq_one_of_off (twoLevelBlock W p q) hoff]
  · simp only [not_or, not_and_or, not_not] at hoff
    obtain ⟨hi, hj⟩ := hoff
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [twoLevelEmbed_apply, twoLevelBlock, hpq.symm]

/-- **`twoLevelEmbed p q` is injective on the `2 × 2` block** (`p ≠ q`): two embeddings agree iff
the blocks do, read off the four block entries `(p,p), (p,q), (q,p), (q,q)`. -/
theorem twoLevelEmbed_injective {p q : Fin d} (hpq : p ≠ q) {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (h : twoLevelEmbed p q A = twoLevelEmbed p q B) : A = B := by
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [twoLevelEmbed_apply, hpq] using congrFun (congrFun h p) p
  · simpa [twoLevelEmbed_apply, hpq, hpq.symm] using congrFun (congrFun h p) q
  · simpa [twoLevelEmbed_apply, hpq, hpq.symm] using congrFun (congrFun h q) p
  · simpa [twoLevelEmbed_apply, hpq, hpq.symm] using congrFun (congrFun h q) q

/-- **The block of a two-level unitary is a `2 × 2` unitary.** If `W` is unitary and supported on
`{p, q}` (`p ≠ q`), then `twoLevelBlock W p q ∈ U(2)`: unfolding `Wᴴ W = 1` through the
`*`-homomorphism laws of `twoLevelEmbed` gives `twoLevelEmbed p q (GᴴG) = twoLevelEmbed p q 1`, and
injectivity forces `Gᴴ G = 1`. -/
theorem twoLevelBlock_mem_unitaryGroup {W : Matrix (Fin d) (Fin d) ℂ} {p q : Fin d} (hpq : p ≠ q)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsupp : ∀ i j : Fin d, (i ≠ p ∧ i ≠ q) ∨ (j ≠ p ∧ j ≠ q) →
      W i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) :
    twoLevelBlock W p q ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  set G := twoLevelBlock W p q with hG
  have hWe : W = twoLevelEmbed p q G := eq_twoLevelEmbed_of_support hpq hsupp
  rw [Matrix.mem_unitaryGroup_iff'] at hW ⊢
  rw [Matrix.star_eq_conjTranspose] at hW ⊢
  rw [hWe, twoLevelEmbed_conjTranspose, twoLevelEmbed_mul hpq, ← twoLevelEmbed_one hpq] at hW
  exact twoLevelEmbed_injective hpq hW

variable {m : ℕ}

/-- The two states `a[j↦0]` and `a[j↦1]` obtained by pinning bit `j` of `a` to `0`/`1` are exactly
`{a, b}` (in one of the two orders) whenever `a` and `b` differ precisely at bit `j`. -/
theorem update_zero_one_eq_pair {a b : Fin m → Fin 2} {j : Fin m} (hj : a j ≠ b j)
    (hoff : ∀ k, k ≠ j → a k = b k) :
    (Function.update a j 0 = a ∧ Function.update a j 1 = b) ∨
      (Function.update a j 0 = b ∧ Function.update a j 1 = a) := by
  have hb : Function.update a j (b j) = b := by
    funext k
    rcases eq_or_ne k j with rfl | hk
    · rw [Function.update_self]
    · rw [Function.update_of_ne hk]; exact hoff k hk
  rcases (by omega : a j = 0 ∨ a j = 1) with h0 | h1
  · refine Or.inl ⟨?_, ?_⟩
    · rw [← h0]; exact Function.update_eq_self j a
    · rw [← (by omega : b j = 1)]; exact hb
  · refine Or.inr ⟨?_, ?_⟩
    · rw [← (by omega : b j = 0)]; exact hb
    · rw [← h1]; exact Function.update_eq_self j a

/-- **A two-level unitary supported on a bit-adjacent pair is a controlled single-qubit gate.** Fix
an encoding `enc : (Fin m → Fin 2) ≃ Fin d`. If `W` is unitary and acts non-trivially only on the
two basis states `{enc a, enc b}` for bit-strings differing in exactly one bit
(`differsInOneBit a b`), then `W = ctrlSingleQubit enc j c Ũ` for the differing bit `j`, control
pattern `c = a`, and a `2 × 2` *unitary* `Ũ` — the §4.5.2 controlled-`Ũ` gate. -/
theorem eq_ctrlSingleQubit_of_support (enc : (Fin m → Fin 2) ≃ Fin d) {a b : Fin m → Fin 2}
    (hab : differsInOneBit a b) {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsupp : ∀ i j : Fin d, (i ≠ enc a ∧ i ≠ enc b) ∨ (j ≠ enc a ∧ j ≠ enc b) →
      W i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) :
    ∃ (j : Fin m) (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ),
      Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ W = ctrlSingleQubit enc j c Ũ := by
  obtain ⟨j, hj, hoff⟩ := hab
  set p := enc (Function.update a j 0) with hp
  set q := enc (Function.update a j 1) with hq
  have hpq : p ≠ q := enc.injective.ne (update_zero_ne_update_one a)
  -- `{p, q} = {enc a, enc b}` as a set, so the support hypothesis transfers to the pair `(p, q)`.
  have hset : ∀ x : Fin d, (x ≠ p ∧ x ≠ q) ↔ (x ≠ enc a ∧ x ≠ enc b) := by
    intro x
    rcases update_zero_one_eq_pair hj hoff with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simp only [hp, hq, h0, h1]
    · simp only [hp, hq, h0, h1]; tauto
  have hsupp' : ∀ i j' : Fin d, (i ≠ p ∧ i ≠ q) ∨ (j' ≠ p ∧ j' ≠ q) →
      W i j' = (1 : Matrix (Fin d) (Fin d) ℂ) i j' := by
    rintro i j' (h | h)
    · exact hsupp i j' (Or.inl ((hset i).mp h))
    · exact hsupp i j' (Or.inr ((hset j').mp h))
  refine ⟨j, a, twoLevelBlock W p q, twoLevelBlock_mem_unitaryGroup hpq hW hsupp', ?_⟩
  rw [ctrlSingleQubit_eq_twoLevelEmbed]
  exact eq_twoLevelEmbed_of_support hpq hsupp'

/-- **The §4.5.2 first-stage → controlled-`Ũ` junction, assembled.** Conjugating a two-level unitary
`U` supported on `{enc s, enc t}` (`s ≠ t`) by the Gray-code swap chain
`swapChain ((grayCode s t).dropLast.map enc)` yields, verbatim, a controlled single-qubit gate
`ctrlSingleQubit enc j c Ũ` with `Ũ` a `2 × 2` unitary. Chains the first-stage relocation
(`swapConj_swapChain_grayCode_support`, which lands the support on a bit-adjacent pair) into the
controlled-gate identification (`eq_ctrlSingleQubit_of_support`). -/
theorem swapConj_swapChain_grayCode_eq_ctrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d)
    {s t : Fin m → Fin 2} (hst : s ≠ t) {U : Matrix (Fin d) (Fin d) ℂ}
    (hunit : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsupp : ∀ i j : Fin d, (i ≠ enc s ∧ i ≠ enc t) ∨ (j ≠ enc s ∧ j ≠ enc t) →
      U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) :
    ∃ (j : Fin m) (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ),
      Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        swapConj (swapChain ((grayCode s t).dropLast.map enc)) U = ctrlSingleQubit enc j c Ũ := by
  obtain ⟨e, hdiff, hu, hsupp'⟩ := swapConj_swapChain_grayCode_support enc hst hunit hsupp
  exact eq_ctrlSingleQubit_of_support enc hdiff hu hsupp'

end AxQM.Concrete
