/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelSwap

/-!
# Concrete: folding the basis-transposition conjugation along a list (N&C §4.5.2)

Nielsen & Chuang §4.5.2 (p. 191–193) realises a two-level unitary `U` on `n` qubits — one acting
non-trivially only on the computational basis states `|s⟩` and `|t⟩` — by *walking a Gray code* from
`s` to `t`: a **sequence** of basis-state swaps shuffles `|s⟩` next to `|t⟩`, a single controlled
single-qubit gate acts, and the swaps are undone. `IsTwoLevelUnitary.swap_conj` (in
`Concrete/TwoLevelSwap.lean`) is the matrix engine of *one* such swap step — conjugation by one
basis transposition `Matrix.swap ℂ p q` relocates the two active basis states from `{a, b}` to
`{swap p q a, swap p q b}`. This file iterates that step along a whole list of transpositions, which
is the form the Gray-code walk consumes.

* `swapConj L U` — conjugate `U` by the list `L` of transpositions, head **outermost**:
  `swapConj [] U = U` and
  `swapConj ((p,q) :: L) U = Matrix.swap ℂ p q * swapConj L U * Matrix.swap ℂ p q`.
* `swapPerm L` — the composite permutation `Equiv.swap p₁ q₁ * ⋯ * Equiv.swap pₖ qₖ` of the index
  set that `L` effects; the two active basis states of `swapConj L U` are the images under it of
  those of `U`.
* `swapConj_unitary_support` — **the headline**: if `U` is unitary with support `{a, b}` then
  `swapConj L U` is unitary with support `{swapPerm L a, swapPerm L b}` (the support is carried
  along by the composite permutation, tracked *explicitly* — not merely "some pair" — so a consumer
  can compute where `s` and `t` land).
* `isTwoLevelUnitary_swapConj` — the packaged corollary: `swapConj L U` is a two-level unitary
  whenever `U` is (support existentially quantified again).
* `swapConj_append` / `swapPerm_append` — the walk composes: conjugating by `L₁ ++ L₂` is
  conjugating by `L₂` and then by `L₁`, and the composite permutation is
  `swapPerm L₁ * swapPerm L₂`. This is the algebra the "undo the swaps" half of the walk uses.

## Use

This is the shared list-level swap lemma of the §4.5.2 two-level → single-qubit + `CNOT`
reduction used by Exercise 4.43's `n`-qubit lift; the statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **Conjugation of a matrix by a list of basis transpositions**, applied one at a time with the
list head **outermost**: `swapConj [] U = U` and
`swapConj ((p,q) :: L) U = Matrix.swap ℂ p q * swapConj L U * Matrix.swap ℂ p q`. Iterating N&C's
one-step swap conjugation (`IsTwoLevelUnitary.swap_conj`) along the Gray-code walk of §4.5.2. -/
noncomputable def swapConj :
    List (Fin d × Fin d) → Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ
  | [], U => U
  | pq :: L, U => Matrix.swap ℂ pq.1 pq.2 * swapConj L U * Matrix.swap ℂ pq.1 pq.2

@[simp] theorem swapConj_nil (U : Matrix (Fin d) (Fin d) ℂ) : swapConj [] U = U := rfl

@[simp] theorem swapConj_cons (pq : Fin d × Fin d) (L : List (Fin d × Fin d))
    (U : Matrix (Fin d) (Fin d) ℂ) :
    swapConj (pq :: L) U
      = Matrix.swap ℂ pq.1 pq.2 * swapConj L U * Matrix.swap ℂ pq.1 pq.2 := rfl

/-- **The composite permutation of the index set effected by a list of basis transpositions**:
`swapPerm [] = 1` and `swapPerm ((p,q) :: L) = Equiv.swap p q * swapPerm L`. If `U` acts
non-trivially only on the basis states `{a, b}`, then `swapConj L U` acts non-trivially only on
`{swapPerm L a, swapPerm L b}` (see `swapConj_unitary_support`). -/
def swapPerm : List (Fin d × Fin d) → Equiv.Perm (Fin d)
  | [] => 1
  | pq :: L => Equiv.swap pq.1 pq.2 * swapPerm L

@[simp] theorem swapPerm_nil : swapPerm ([] : List (Fin d × Fin d)) = 1 := rfl

@[simp] theorem swapPerm_cons (pq : Fin d × Fin d) (L : List (Fin d × Fin d)) :
    swapPerm (pq :: L) = Equiv.swap pq.1 pq.2 * swapPerm L := rfl

/-- **Conjugating by `L₁ ++ L₂` is conjugating by `L₂`, then by `L₁`.** The `++` splits the walk
into two stages; used with `swapConj_cons` to compose a Gray-code walk with the reversed walk that
undoes it. -/
theorem swapConj_append (L₁ L₂ : List (Fin d × Fin d)) (U : Matrix (Fin d) (Fin d) ℂ) :
    swapConj (L₁ ++ L₂) U = swapConj L₁ (swapConj L₂ U) := by
  induction L₁ with
  | nil => rfl
  | cons pq L ih => rw [List.cons_append, swapConj_cons, swapConj_cons, ih]

/-- **The composite permutation of `L₁ ++ L₂` is `swapPerm L₁ * swapPerm L₂`.** The list-of-swaps ↦
permutation map is a monoid homomorphism from `(List _, ++)` to `Equiv.Perm _`. -/
theorem swapPerm_append (L₁ L₂ : List (Fin d × Fin d)) :
    swapPerm (L₁ ++ L₂) = swapPerm L₁ * swapPerm L₂ := by
  induction L₁ with
  | nil => rw [List.nil_append, swapPerm_nil, one_mul]
  | cons pq L ih => rw [List.cons_append, swapPerm_cons, swapPerm_cons, ih, mul_assoc]

/-- **Folding the basis-transposition conjugation along a list relocates the support explicitly.**
If `U` is unitary and acts non-trivially only on the two computational basis states `{a, b}` (its
entries outside the `{a,b} × {a,b}` block agree with the identity), then `swapConj L U` is unitary
and acts non-trivially only on `{swapPerm L a, swapPerm L b}` — the images of `a` and `b` under the
composite permutation `swapPerm L`. Tracking the support *pair by name* (rather than existentially,
as in `IsTwoLevelUnitary`) is what lets the §4.5.2 Gray-code walk conclude that the two active basis
states end up differing in exactly one bit. Proved by induction on `L`, each step applying the
single-transposition `swap_conj_support` to the inductive hypothesis's explicit support pair. -/
theorem swapConj_unitary_support (L : List (Fin d × Fin d)) {U : Matrix (Fin d) (Fin d) ℂ}
    {a b : Fin d} (hunit : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsupp : ∀ i j : Fin d, (i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b) →
      U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) :
    swapConj L U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      ∀ i j : Fin d,
        (i ≠ swapPerm L a ∧ i ≠ swapPerm L b) ∨ (j ≠ swapPerm L a ∧ j ≠ swapPerm L b) →
          swapConj L U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  induction L with
  | nil => exact ⟨hunit, by simpa using hsupp⟩
  | cons pq L ih =>
    -- One list step is exactly the single-transposition `swap_conj_support`, applied to the
    -- inductive hypothesis's *explicit* support pair `{swapPerm L a, swapPerm L b}`.
    -- `swapConj (pq :: L) U` is defeq to `swap * swapConj L U * swap`, so `swap_conj_support`
    -- discharges both goals directly (no `swapConj_cons` unfold needed).
    obtain ⟨hu, hs⟩ := ih
    obtain ⟨hu', hs'⟩ := swap_conj_support hu hs pq.1 pq.2
    refine ⟨hu', fun i j h => hs' i j ?_⟩
    simpa only [swapPerm_cons, Equiv.Perm.mul_apply] using h

/-- **Conjugating a two-level unitary by a list of basis transpositions yields a two-level
unitary.** The packaged corollary of `swapConj_unitary_support`: `swapConj L U` is a two-level
unitary whenever `U` is (here the relocated support `{swapPerm L a, swapPerm L b}` is repackaged
into the existential of `IsTwoLevelUnitary`). This is the §4.5.2 statement "the Gray-code swaps
carry a two-level unitary to a two-level unitary" at the matrix level. -/
theorem isTwoLevelUnitary_swapConj (L : List (Fin d × Fin d)) {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : IsTwoLevelUnitary U) : IsTwoLevelUnitary (swapConj L U) := by
  obtain ⟨hunit, a, b, hab⟩ := hU
  obtain ⟨hu, hs⟩ := swapConj_unitary_support L hunit hab
  exact ⟨hu, swapPerm L a, swapPerm L b, hs⟩

end AxQM.Concrete
