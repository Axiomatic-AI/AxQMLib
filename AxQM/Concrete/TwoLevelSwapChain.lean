/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelSwapList

/-!
# Concrete: the swap chain of a basis-state path (N&C §4.5.2, eqs. 4.54–4.57)

Nielsen & Chuang §4.5.2 (p. 191–193) realises a two-level unitary `U` on `n` qubits — one acting
non-trivially only on the computational basis states `|s⟩` and `|t⟩` — by *walking a Gray code*
`g₁ = s, g₂, …, g_m = t`. The first stage performs a sequence of `m − 2` basis-state swaps,
`|g₁⟩ ↔ |g₂⟩`, `|g₂⟩ ↔ |g₃⟩`, …, `|g_{m-2}⟩ ↔ |g_{m-1}⟩`, whose net effect (N&C eqs. 4.54–4.57) is

```
|g₁⟩ → |g_{m-1}⟩,   |g₂⟩ → |g₁⟩,   |g₃⟩ → |g₂⟩,   …,   |g_{m-1}⟩ → |g_{m-2}⟩,
```

**all other computational basis states left unchanged** — in particular `|g_m⟩ = |t⟩` is fixed. The
two active basis states of `U` are thereby moved from `{g₁, g_m} = {s, t}` to `{g_{m-1}, g_m}`,
which differ in exactly one bit (adjacent Gray-code words); there the two-level unitary is a
*controlled*
single-qubit gate, ready for the controlled-`Ũ` step. The swaps are then undone.

This file provides the **combinatorial engine of that first stage**, at the raw-matrix / index-
permutation level — the transposition list read off a path of basis indices, and the two facts that
pin down its permutation action on the endpoints:

* `swapChain path` — the list of transpositions `[(g_{m-2}, g_{m-1}), …, (g₂, g₃), (g₁, g₂)]` read
  off a path `path = [g₁, …, g_{m-1}]` of basis indices, ordered so that (via `swapPerm`, head
  outermost) the swap `|g₁⟩ ↔ |g₂⟩` is applied *first* and `|g_{m-2}⟩ ↔ |g_{m-1}⟩` *last*.
* `swapPerm_swapChain_eq` — the permutation carries the path's **head to its last element**
  (`swapPerm (swapChain path) s = e` when `path.head? = some s`, `path.getLast? = some e`): this is
  N&C eq. 4.54, `|g₁⟩ → |g_{m-1}⟩`.
* `swapPerm_swapChain_apply_of_not_mem` — it **fixes every index off the path**
  (`swapPerm (swapChain path) w = w` for `w ∉ path`): the "all other states unchanged" clause, whose
  consequence for `w = g_m = t` is that `|t⟩` is fixed.
* `swapConj_swapChain_support` — **the headline**: conjugating a unitary `U` with two-level support
  `{s, w}` (here `s = g₁` is the path head, `w = g_m = t` lies off the path) by `swapChain path`
  yields a unitary with support `{e, w}` where `e = g_{m-1}` is the path's last element — the
  §4.5.2 relocation of the active pair to two adjacent basis states, at the matrix level.

## Use

This reuses the existing `swapConj` / `swapPerm` lemmas. It is the shared first-stage lemma of the
§4.5.2 two-level → single-qubit + `CNOT` reduction used by Exercise 4.43's `n`-qubit lift; the
statement of Exercise 4.43 is in `AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **The swap chain read off a path of basis indices** (N&C §4.5.2, first stage): the list of
consecutive-pair transpositions `[(g_{m-2}, g_{m-1}), …, (g₁, g₂)]` of `path = [g₁, …, g_{m-1}]`,
ordered with the *first* swap `(g₁, g₂)` **last** so that, read through `swapPerm` (head outermost)
/ `swapConj`, the swap `|g₁⟩ ↔ |g₂⟩` is applied first and `|g_{m-2}⟩ ↔ |g_{m-1}⟩` last. Defined by
the structural recursion `swapChain (a :: b :: l) = swapChain (b :: l) ++ [(a, b)]` so its action
on the endpoints unfolds cleanly (`swapPerm_swapChain_eq`). -/
def swapChain : List (Fin d) → List (Fin d × Fin d)
  | [] => []
  | [_] => []
  | a :: b :: l => swapChain (b :: l) ++ [(a, b)]

@[simp] theorem swapChain_nil : swapChain ([] : List (Fin d)) = [] := rfl

@[simp] theorem swapChain_singleton (a : Fin d) : swapChain [a] = [] := rfl

theorem swapChain_cons_cons (a b : Fin d) (l : List (Fin d)) :
    swapChain (a :: b :: l) = swapChain (b :: l) ++ [(a, b)] := rfl

/-- **The composite permutation of a swap chain peels the first transposition on the right.**
`swapPerm (swapChain (a :: b :: l)) = swapPerm (swapChain (b :: l)) * Equiv.swap a b`: the swap
`(a, b)` sits innermost (applied first). Follows from `swapPerm_append`. -/
theorem swapPerm_swapChain_cons_cons (a b : Fin d) (l : List (Fin d)) :
    swapPerm (swapChain (a :: b :: l)) = swapPerm (swapChain (b :: l)) * Equiv.swap a b := by
  rw [swapChain_cons_cons, swapPerm_append, swapPerm_cons, swapPerm_nil, mul_one]

/-- **A swap chain fixes every index off its path** — N&C's "all other computational basis states
are left unchanged" (the clause that keeps `|t⟩ = |g_m⟩` fixed, since `t` lies off the path
`[g₁, …, g_{m-1}]`). Proved by structural induction: the outer swap `(a, b)` fixes
`w ∉ a :: b :: l`, and the inductive hypothesis fixes it under the shorter chain. -/
theorem swapPerm_swapChain_apply_of_not_mem :
    ∀ {l : List (Fin d)} {w : Fin d}, w ∉ l → swapPerm (swapChain l) w = w := by
  intro l
  induction l using swapChain.induct with
  | case1 => intro w _; simp
  | case2 a => intro w _; simp
  | case3 a b l ih =>
    intro w hw
    rw [List.mem_cons, not_or, List.mem_cons, not_or] at hw
    obtain ⟨hwa, hwb, hwl⟩ := hw
    rw [swapPerm_swapChain_cons_cons, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hwa hwb, ih (by simp [hwb, hwl])]

/-- **A swap chain carries the path's head to its last element** — N&C eq. 4.54, `|g₁⟩ → |g_{m-1}⟩`.
For a nonempty path `path` with `path.head? = some s` and `path.getLast? = some e`,
`swapPerm (swapChain path) s = e`. Proved by structural induction on the `a :: b :: l` recursion:
the outer swap sends `a` to `b = (b :: l).head`, and the inductive hypothesis carries that head to
the common last element. (No `Nodup` needed — only the head is tracked.) -/
theorem swapPerm_swapChain_eq :
    ∀ {l : List (Fin d)} {s e : Fin d}, l.head? = some s → l.getLast? = some e →
      swapPerm (swapChain l) s = e := by
  intro l
  induction l using swapChain.induct with
  | case1 => intro s e hs _; simp at hs
  | case2 a =>
    intro s e hs he
    rw [List.head?_cons, Option.some_inj] at hs
    rw [List.getLast?_singleton, Option.some_inj] at he
    subst hs he
    simp
  | case3 a b l ih =>
    intro s e hs he
    rw [List.head?_cons, Option.some_inj] at hs
    subst hs
    rw [List.getLast?_cons_cons] at he
    rw [swapPerm_swapChain_cons_cons, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact ih (List.head?_cons) he

/-- **The swap chain relocates a two-level unitary's support from `{s, w}` to `{e, w}`** — the
matrix-level statement of N&C's §4.5.2 first stage. If `U` is unitary and acts non-trivially only on
the two computational basis states `{s, w}`, where `s` is the head of `path` and `w` lies off the
path, then conjugating `U` by the swap chain of `path` (`swapConj (swapChain path) U`) is unitary
and acts non-trivially only on `{e, w}`, where `e` is the last element of `path`. Instantiating
`path` at a
Gray code `[g₁, …, g_{m-1}]` (`s = g₁`, `e = g_{m-1}`, `w = g_m = t`) moves the active pair to
`{g_{m-1}, g_m}`, two basis states differing in a single bit — the point where the two-level unitary
is a controlled single-qubit gate. Combines `swapConj_unitary_support` (support tracked by the
composite permutation) with the two endpoint facts above. -/
theorem swapConj_swapChain_support {path : List (Fin d)} {s e w : Fin d}
    (hs : path.head? = some s) (he : path.getLast? = some e) (hw : w ∉ path)
    {U : Matrix (Fin d) (Fin d) ℂ} (hunit : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsupp : ∀ i j : Fin d, (i ≠ s ∧ i ≠ w) ∨ (j ≠ s ∧ j ≠ w) →
      U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) :
    swapConj (swapChain path) U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      ∀ i j : Fin d, (i ≠ e ∧ i ≠ w) ∨ (j ≠ e ∧ j ≠ w) →
        swapConj (swapChain path) U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  obtain ⟨hu, hs'⟩ := swapConj_unitary_support (swapChain path) hunit hsupp
  rw [swapPerm_swapChain_eq hs he, swapPerm_swapChain_apply_of_not_mem hw] at hs'
  exact ⟨hu, hs'⟩

end AxQM.Concrete
