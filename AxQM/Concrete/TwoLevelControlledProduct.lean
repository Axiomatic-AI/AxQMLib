/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelControlledDecomposition

/-!
# Concrete: a two-level unitary as an explicit product of controlled single-qubit gates (N&C §4.5.2)

(Nielsen & Chuang §4.5.2, p. 191–193.)

`Concrete/TwoLevelControlledDecomposition.lean` established the §4.5.2 decomposition of a two-level
unitary `U` (supported on two computational basis states `|s⟩`, `|t⟩`) in *swap-conjugation* form,
`U = swapConj (reversed Gray chain) (ctrlSingleQubit …)`, and that each Gray-code swap is itself a
controlled single-qubit gate. This file flattens that conjugation into a **single explicit product
(`List.prod`) of controlled single-qubit gates** — the concrete "circuit as a list of gates" form
that the `n`-qubit lift of Exercise 4.43 consumes.

## The pieces

* `AxQM.Concrete.IsCtrlSingleQubit` — the predicate "`g` is a controlled single-qubit gate
  for the encoding `enc`": `g = ctrlSingleQubit enc j c Ũ` for some target bit `j`, control pattern
  `c`, and `2 × 2` *unitary* `Ũ`. Both stages of the §4.5.2 circuit — the Gray-code swaps
  (controlled-`NOT`s) and the final controlled-`Ũ` — are of this family.
* `AxQM.Concrete.isCtrlSingleQubit_swap` — a bit-adjacent basis transposition is one
  (repackages `swap_eq_ctrlSingleQubit`: the `2 × 2` block is the swap `!![0,1;1,0] = X`, unitary).
* `AxQM.Concrete.rel_of_mem_swapChain` — **the combinatorial bridge**: if the path is a
  chain for a relation `R` (`List.IsChain R path`), every transposition `(p, q)` of `swapChain path`
  has `R p q` (it is a consecutive pair of the path). Applied with `R = differsInOneBit` through the
  encoding, this makes *every* swap of the Gray-code chain bit-adjacent, hence a controlled-`NOT`.
* `AxQM.Concrete.swapConj_eq_prod` — **the algebra**: conjugation by a transposition
  list is an explicit product, `swapConj L V = (L.map swap ++ V :: L.reverse.map swap).prod`.
* `AxQM.Concrete.twoLevelUnitary_isProd_ctrlSingleQubit` — **the headline**: a two-level
  unitary supported on `{enc s, enc t}` (`s ≠ t`) equals `gates.prod` for an explicit list `gates`
  *every* member of which is a controlled single-qubit gate. It flattens
  `twoLevelUnitary_eq_swapConj_ctrlSingleQubit` via `swapConj_eq_prod`, then classifies each factor:
  the middle factor is the controlled-`Ũ`, and each swap factor is a Gray-chain transposition, shown
  bit-adjacent by `rel_of_mem_swapChain` fed the Gray chain `grayCode_isChain`. This is the §4.5.2
  conclusion "a two-level unitary is a product of controlled single-qubit gates" in gate-list form.

## Use

This is used in the §4.5.2 development of Exercise 4.43's `n`-qubit lift; the statement of
Exercise 4.43 is in `AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

/-- A `d × d` matrix `g` is a **controlled single-qubit gate** for the encoding
`enc : (Fin m → Fin 2) ≃ Fin d` when `g = ctrlSingleQubit enc j c Ũ` for some target bit `j`,
control pattern `c`, and `2 × 2` *unitary* block `Ũ`. This is the gate family both stages of the
§4.5.2 circuit belong to: the Gray-code swaps (controlled-`NOT`s) and the final controlled-`Ũ`. -/
def IsCtrlSingleQubit {m d : ℕ} (enc : (Fin m → Fin 2) ≃ Fin d)
    (g : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (j : Fin m) (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ),
    Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ g = ctrlSingleQubit enc j c Ũ

/-- **A bit-adjacent basis transposition is a controlled single-qubit gate** (a controlled-`NOT`).
Repackages `swap_eq_ctrlSingleQubit`: for `differsInOneBit a b`, `Matrix.swap ℂ (enc a) (enc b)` is
`ctrlSingleQubit enc j c (Matrix.swap ℂ 0 1)`, whose `2 × 2` block `!![0,1;1,0] = X` is unitary
(`swapTwo_mem_unitaryGroup`). -/
theorem isCtrlSingleQubit_swap {m d : ℕ} (enc : (Fin m → Fin 2) ≃ Fin d)
    {a b : Fin m → Fin 2} (hab : differsInOneBit a b) :
    IsCtrlSingleQubit enc (Matrix.swap ℂ (enc a) (enc b)) := by
  obtain ⟨j, c, hjc⟩ := swap_eq_ctrlSingleQubit enc hab
  exact ⟨j, c, Matrix.swap ℂ (0 : Fin 2) 1, swapTwo_mem_unitaryGroup, hjc⟩

/-- **Every transposition of a swap chain relates its two coordinates under any relation the path is
a chain for.** If `List.IsChain R l` then each pair `(p, q) ∈ swapChain l` satisfies `R p q` — it is
a consecutive pair of the path. With `R = differsInOneBit` (through the encoding) this makes every
Gray-code swap bit-adjacent, hence a controlled-`NOT`. Proved by the `swapChain` recursion: the
outer swap `(a, b)` of `swapChain (a :: b :: l)` is related by the chain's head step `R a b`, the
rest by the inductive hypothesis on `b :: l`. -/
theorem rel_of_mem_swapChain {d : ℕ} {R : Fin d → Fin d → Prop} :
    ∀ {l : List (Fin d)}, List.IsChain R l → ∀ pq ∈ swapChain l, R pq.1 pq.2 := by
  intro l
  induction l using swapChain.induct with
  | case1 => intro _ pq hpq; simp at hpq
  | case2 a => intro _ pq hpq; simp at hpq
  | case3 a b l ih =>
    intro hch pq hpq
    rw [swapChain_cons_cons, List.mem_append, List.mem_singleton] at hpq
    rcases (List.isChain_cons_iff R a (b :: l)).mp hch with h | ⟨b', l', hab, hbl, heq⟩
    · simp at h
    · obtain ⟨rfl, rfl⟩ : b = b' ∧ l = l' := by simpa using heq
      rcases hpq with hpq | rfl
      · exact ih hbl pq hpq
      · exact hab

/-- **Conjugation by a list of basis transpositions is an explicit product of swap matrices around
the conjugand.** `swapConj L V` equals the product of the swap matrices of `L`, then `V`, then the
swap matrices of `L.reverse`:
`swapConj L V = (L.map (swap ·.1 ·.2) ++ V :: L.reverse.map (swap ·.1 ·.2)).prod`. Proved by
induction on `L`; the cons step reassociates `s * (P·V·Q) * s = (s·P)·(V·(Q·s))` (`noncomm_ring`),
matching the head swap `s` peeled off the front and the back of the reversed tail. -/
theorem swapConj_eq_prod {d : ℕ} (L : List (Fin d × Fin d)) (V : Matrix (Fin d) (Fin d) ℂ) :
    swapConj L V
      = ((L.map fun pq => Matrix.swap ℂ pq.1 pq.2)
          ++ V :: (L.reverse.map fun pq => Matrix.swap ℂ pq.1 pq.2)).prod := by
  induction L with
  | nil => simp
  | cons pq L ih =>
    rw [swapConj_cons, ih]
    simp only [List.map_cons, List.reverse_cons, List.map_append, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    noncomm_ring

/-- **The §4.5.2 decomposition of a two-level unitary as an explicit product of controlled
single-qubit gates.** A two-level unitary `U` supported on `{enc s, enc t}` (`s ≠ t` two distinct
`m`-bit strings, `enc : (Fin m → Fin 2) ≃ Fin d`) *equals* `gates.prod` for an explicit list `gates`
**every** member of which is a controlled single-qubit gate (`IsCtrlSingleQubit enc`).

Flattens `twoLevelUnitary_eq_swapConj_ctrlSingleQubit` (`U` as the swap-conjugate of a
controlled-`Ũ` by the reversed Gray chain) via `swapConj_eq_prod`, then classifies each factor of
the resulting product: the single middle factor is the controlled-`Ũ` itself, and every swap is a
transposition of the Gray-code swap chain — shown bit-adjacent (hence a controlled-`NOT`,
`isCtrlSingleQubit_swap`) by feeding `grayCode_isChain` to `rel_of_mem_swapChain`. This is the
§4.5.2 conclusion "a two-level unitary is built entirely from controlled single-qubit gates",
delivered as a concrete gate list — the structural input to Exercise 4.43's `n`-qubit lift. -/
theorem twoLevelUnitary_isProd_ctrlSingleQubit {m d : ℕ} (enc : (Fin m → Fin 2) ≃ Fin d)
    {s t : Fin m → Fin 2} (hst : s ≠ t) {U : Matrix (Fin d) (Fin d) ℂ}
    (hunit : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsupp : ∀ i j : Fin d, (i ≠ enc s ∧ i ≠ enc t) ∨ (j ≠ enc s ∧ j ≠ enc t) →
      U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g ∈ gates, IsCtrlSingleQubit enc g) ∧ U = gates.prod := by
  obtain ⟨j, c, Ũ, hŨ, hUeq⟩ :=
    twoLevelUnitary_eq_swapConj_ctrlSingleQubit enc hst hunit hsupp
  set gpath := (grayCode s t).dropLast.map enc with hgpath
  set chainRev := (swapChain gpath).reverse with hchainRev
  refine ⟨(chainRev.map fun pq => Matrix.swap ℂ pq.1 pq.2)
            ++ ctrlSingleQubit enc j c Ũ :: chainRev.reverse.map fun pq => Matrix.swap ℂ pq.1 pq.2,
          ?_, ?_⟩
  · -- Every gate in the list is a controlled single-qubit gate.
    -- Consecutive coordinates of the encoded Gray path differ in exactly one bit.
    have hchain : List.IsChain (fun p q => differsInOneBit (enc.symm p) (enc.symm q)) gpath := by
      rw [hgpath]
      refine List.isChain_map_of_isChain enc ?_ ((grayCode_isChain s t).dropLast)
      intro a b hab
      simpa only [Equiv.symm_apply_apply] using hab
    -- Hence every transposition of the Gray swap chain is a controlled-`NOT`.
    have hswap : ∀ pq ∈ swapChain gpath, IsCtrlSingleQubit enc (Matrix.swap ℂ pq.1 pq.2) := by
      intro pq hpq
      have hrel := rel_of_mem_swapChain hchain pq hpq
      have := isCtrlSingleQubit_swap enc hrel
      rwa [enc.apply_symm_apply, enc.apply_symm_apply] at this
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · rw [List.mem_map] at hg
      obtain ⟨pq, hpq, rfl⟩ := hg
      rw [hchainRev, List.mem_reverse] at hpq
      exact hswap pq hpq
    · rw [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨j, c, Ũ, hŨ, rfl⟩
      · rw [List.mem_map] at hg
        obtain ⟨pq, hpq, rfl⟩ := hg
        rw [List.mem_reverse, hchainRev, List.mem_reverse] at hpq
        exact hswap pq hpq
  · -- The product equals `U`.
    rw [hUeq, swapConj_eq_prod]

end AxQM.Concrete
