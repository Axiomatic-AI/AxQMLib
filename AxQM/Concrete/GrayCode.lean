/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic

/-!
# Concrete: a Gray code connecting two bit-strings (N&C §4.5.2)

Nielsen & Chuang §4.5.2 (p. 191) reduces an arbitrary two-level unitary on `n` qubits — one acting
non-trivially only on the two computational basis states `|s⟩` and `|t⟩` — to single-qubit and
`CNOT` gates using a **Gray code** connecting `s` and `t`: a sequence of bit-strings starting at `s`
and ending at `t` in which *adjacent members differ in exactly one bit*. Each one-bit step is then a
controlled bit-flip (a multiply-controlled `NOT`, conditional on the other wires), so the code
prescribes the swap circuit that shuffles `|s⟩` adjacent to `|t⟩`, after which a single
controlled-`Ũ` acts and the swaps are undone.

This file provides that purely combinatorial ingredient, independently of the circuit realisation.
For two bit-strings `s t : Fin m → Fin 2` it builds `grayCode s t`, the path that
flips, one at a time, exactly the coordinates on which `s` and `t` disagree.

## The construction

`grayPath t s L` walks from `s`, rewriting the coordinates listed in `L` to their `t`-values one at
a time (`List.scanl`-style, but by explicit recursion so the induction unfolds cleanly):

```
  grayPath t s []       = [s]
  grayPath t s (i :: L) = s :: grayPath t (Function.update s i (t i)) L.
```

The two facts that make it a Gray code, when `L` is duplicate-free and lists coordinates on which
`s` and `t` genuinely differ:

* `grayPath_isChain_differsInOneBit` — consecutive entries differ in exactly one coordinate
  (`differsInOneBit`), namely the one flipped at that step. `L.Nodup` and `s i ≠ t i` are needed: a
  coordinate is still at its `s`-value when its step happens (so the value really changes there),
  and only that coordinate is touched.
* `grayPath_getLast?` — the last entry equals `t` on the coordinates in `L` and `s` elsewhere.

`grayCode s t := grayPath t s (differing coordinates)` then starts at `s` (`grayCode_head?`), ends
at `t` (`grayCode_getLast?`), has consecutive entries differing in one bit (`grayCode_isChain`), and
length `≤ m + 1` (`grayCode_length_le`, since `s` and `t` differ in at most `m` of `m` coordinates —
N&C's "`m ≤ n + 1`"). It is moreover a **simple** path — duplicate-free (`grayCode_nodup`, via the
invariant `grayPath_apply_eq_of_not_mem` feeding `grayPath_nodup`) — so its endpoint `t` occurs
only as the last entry: `t ∉ (grayCode s t).dropLast` (`grayCode_getLast_not_mem_dropLast`). That
"`t` off the initial segment" fact is precisely the hypothesis the §4.5.2 swap chain consumes to
keep `|t⟩` fixed while it relocates the active pair `{s, t}` onto two adjacent Gray-code words.

## Use

Everything here is decidable `Fin 2` / `Finset` / `List` combinatorics on bit-strings
`Fin m → Fin 2`. It is the shared foundation of the §4.5.2 two-level → single-qubit + `CNOT`
reduction used by Exercise 4.43's `n`-qubit lift. The statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

variable {m : ℕ}

/-- Two bit-strings `a`, `b : Fin m → Fin 2` **differ in exactly one bit**: there is a single
coordinate `i` at which they disagree, and they agree everywhere else. This is the adjacency
relation of a Gray code; the distinguished coordinate `i` is where the corresponding controlled
bit-flip acts. -/
def differsInOneBit (a b : Fin m → Fin 2) : Prop :=
  ∃ i : Fin m, a i ≠ b i ∧ ∀ j : Fin m, j ≠ i → a j = b j

/-- The Gray-code path from `s`, flipping each coordinate listed in `L` to its `t`-value in turn.
Built by explicit recursion so its induction unfolds definitionally. See the module docstring. -/
def grayPath (t : Fin m → Fin 2) : (Fin m → Fin 2) → List (Fin m) → List (Fin m → Fin 2)
  | s, [] => [s]
  | s, i :: L => s :: grayPath t (Function.update s i (t i)) L

@[simp] theorem grayPath_nil (t s : Fin m → Fin 2) : grayPath t s [] = [s] := rfl

theorem grayPath_cons (t s : Fin m → Fin 2) (i : Fin m) (L : List (Fin m)) :
    grayPath t s (i :: L) = s :: grayPath t (Function.update s i (t i)) L := rfl

/-- A Gray-code path is never empty (it always begins with its start point). -/
theorem grayPath_ne_nil (t s : Fin m → Fin 2) (L : List (Fin m)) : grayPath t s L ≠ [] := by
  cases L with
  | nil => simp
  | cons i L => simp [grayPath_cons]

/-- A Gray-code path begins at its start point `s`. -/
@[simp] theorem grayPath_head? (t s : Fin m → Fin 2) (L : List (Fin m)) :
    (grayPath t s L).head? = some s := by
  cases L with
  | nil => rfl
  | cons i L => rfl

/-- A Gray-code path over `L` has `L.length + 1` entries. -/
@[simp] theorem grayPath_length (t s : Fin m → Fin 2) (L : List (Fin m)) :
    (grayPath t s L).length = L.length + 1 := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih => simp [grayPath_cons, ih]

/-- The final entry of a Gray-code path equals `t` on the flipped coordinates `L` and `s`
elsewhere. Stated via `getLast?` to avoid a nonemptiness side condition. -/
theorem grayPath_getLast? (t : Fin m → Fin 2) :
    ∀ (s : Fin m → Fin 2) (L : List (Fin m)),
      (grayPath t s L).getLast? = some (fun x => if x ∈ L then t x else s x) := by
  intro s L
  induction L generalizing s with
  | nil => simp
  | cons i L ih =>
      rw [grayPath_cons, List.getLast?_cons_of_ne_nil (grayPath_ne_nil _ _ _), ih]
      congr 1
      funext x
      by_cases hxi : x = i <;> by_cases hxL : x ∈ L <;>
        simp [List.mem_cons, hxi, hxL]

/-- **Adjacent Gray-code words differ in exactly one bit.** When `L` is duplicate-free and lists
coordinates on which `s` and `t` disagree, consecutive entries of `grayPath t s L` differ in exactly
one coordinate — the one flipped at that step. -/
theorem grayPath_isChain_differsInOneBit (t : Fin m → Fin 2) :
    ∀ (s : Fin m → Fin 2) (L : List (Fin m)), L.Nodup → (∀ i ∈ L, s i ≠ t i) →
      List.IsChain differsInOneBit (grayPath t s L) := by
  intro s L
  induction L generalizing s with
  | nil => intro _ _; exact List.isChain_singleton s
  | cons i L ih =>
      intro hnd hdiff
      have hiL : i ∉ L := (List.nodup_cons.mp hnd).1
      rw [grayPath_cons, List.isChain_cons]
      refine ⟨?_, ?_⟩
      · -- the first step `s → Function.update s i (t i)` differs exactly at `i`
        intro y hy
        rw [grayPath_head?, Option.mem_some_iff] at hy
        subst hy
        refine ⟨i, ?_, ?_⟩
        · simpa using hdiff i (by simp)
        · intro j hj
          rw [Function.update_apply, ite_eq_right hj]
      · -- the remaining steps, by the induction hypothesis on the updated start point
        apply ih
        · exact (List.nodup_cons.mp hnd).2
        · intro k hk
          have hki : k ≠ i := fun h => hiL (h ▸ hk)
          rw [Function.update_apply, ite_eq_right hki]
          exact hdiff k (by simp [hk])

/-- **Every entry of a Gray-code path agrees with the start point off the flipped coordinates.** For
`x ∈ grayPath t s L` and a coordinate `j ∉ L`, `x j = s j` — only the coordinates listed in `L` are
ever touched. The key invariant behind `grayPath_nodup`: a coordinate not yet (or never) flipped
still holds its `s`-value. -/
theorem grayPath_apply_eq_of_not_mem (t : Fin m → Fin 2) :
    ∀ {s : Fin m → Fin 2} {L : List (Fin m)} {x : Fin m → Fin 2}, x ∈ grayPath t s L →
      ∀ {j : Fin m}, j ∉ L → x j = s j := by
  intro s L
  induction L generalizing s with
  | nil => intro x hx j _; rw [grayPath_nil, List.mem_singleton] at hx; rw [hx]
  | cons i L ih =>
      intro x hx j hj
      rw [grayPath_cons, List.mem_cons] at hx
      rw [List.mem_cons, not_or] at hj
      obtain ⟨hji, hjL⟩ := hj
      rcases hx with h | h
      · rw [h]
      · rw [ih h hjL, Function.update_apply, ite_eq_right hji]

/-- **A Gray-code path has no repeated entries** when `L` is duplicate-free and lists coordinates on
which `s` and `t` genuinely differ. Two entries differ on the coordinates flipped between them, a
nonempty set (each listed coordinate really changes value, by `s i ≠ t i`), so no entry recurs.
Proved by induction: the head `s` differs from every tail entry at the just-flipped coordinate `i`
(which the tail leaves at its `t`-value, via `grayPath_apply_eq_of_not_mem` since `i ∉ L`), and the
tail is duplicate-free by the inductive hypothesis. -/
theorem grayPath_nodup (t : Fin m → Fin 2) :
    ∀ {s : Fin m → Fin 2} {L : List (Fin m)}, L.Nodup → (∀ i ∈ L, s i ≠ t i) →
      (grayPath t s L).Nodup := by
  intro s L
  induction L generalizing s with
  | nil => intro _ _; rw [grayPath_nil]; exact List.nodup_singleton s
  | cons i L ih =>
      intro hnd hdiff
      have hiL : i ∉ L := (List.nodup_cons.mp hnd).1
      rw [grayPath_cons, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · -- the head `s` is not among the tail entries: they all hold `t i` at coordinate `i`,
        -- while `s i ≠ t i`
        intro hs
        have hval : s i = (Function.update s i (t i)) i :=
          grayPath_apply_eq_of_not_mem t hs (j := i) hiL
        rw [Function.update_apply, ite_eq_left rfl] at hval
        exact hdiff i (by simp) hval
      · -- the tail is duplicate-free by the induction hypothesis on the updated start point
        apply ih
        · exact (List.nodup_cons.mp hnd).2
        · intro k hk
          have hki : k ≠ i := fun h => hiL (h ▸ hk)
          rw [Function.update_apply, ite_eq_right hki]
          exact hdiff k (by simp [hk])

/-- The Gray code connecting two bit-strings `s`, `t : Fin m → Fin 2`: the path flipping, one bit at
a time, exactly the coordinates on which they differ. It starts at `s`, ends at `t`, and has
consecutive entries differing in exactly one bit. -/
noncomputable def grayCode (s t : Fin m → Fin 2) : List (Fin m → Fin 2) :=
  grayPath t s (Finset.univ.filter (fun i => s i ≠ t i)).toList

/-- The Gray code begins at `s`. -/
@[simp] theorem grayCode_head? (s t : Fin m → Fin 2) : (grayCode s t).head? = some s :=
  grayPath_head? t s _

/-- The Gray code is nonempty. -/
theorem grayCode_ne_nil (s t : Fin m → Fin 2) : grayCode s t ≠ [] :=
  grayPath_ne_nil _ _ _

/-- The Gray code has at most `m + 1` entries: `s` and `t` differ in at most `m` of `m`
coordinates (N&C's "`m ≤ n + 1`"). -/
theorem grayCode_length_le (s t : Fin m → Fin 2) : (grayCode s t).length ≤ m + 1 := by
  have hlen : (grayCode s t).length
      = (Finset.univ.filter (fun i => s i ≠ t i)).toList.length + 1 := grayPath_length t s _
  rw [hlen, Finset.length_toList]
  have h : (Finset.univ.filter (fun i => s i ≠ t i)).card ≤ m := by
    calc (Finset.univ.filter (fun i => s i ≠ t i)).card
        ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
      _ = m := by simp
  omega

/-- **The Gray code ends at `t`.** -/
theorem grayCode_getLast? (s t : Fin m → Fin 2) : (grayCode s t).getLast? = some t := by
  unfold grayCode
  rw [grayPath_getLast?]
  congr 1
  funext x
  split_ifs with h
  · rfl
  · rw [Finset.mem_toList, Finset.mem_filter] at h
    simp only [Finset.mem_univ, true_and, not_not] at h
    exact h

/-- **Adjacent Gray-code words differ in exactly one bit** — the defining Gray-code property, at the
level of `grayCode s t`. -/
theorem grayCode_isChain (s t : Fin m → Fin 2) :
    List.IsChain differsInOneBit (grayCode s t) := by
  apply grayPath_isChain_differsInOneBit
  · exact Finset.nodup_toList _
  · intro i hi
    rw [Finset.mem_toList, Finset.mem_filter] at hi
    exact hi.2

/-- **The Gray code has no repeated entries.** The path visits each intermediate bit-string once, so
it is a *simple* path from `s` to `t`. Instance of `grayPath_nodup` (the filtered coordinate list is
duplicate-free and, by construction, lists exactly the coordinates on which `s` and `t` differ). -/
theorem grayCode_nodup (s t : Fin m → Fin 2) : (grayCode s t).Nodup := by
  apply grayPath_nodup
  · exact Finset.nodup_toList _
  · intro i hi
    rw [Finset.mem_toList, Finset.mem_filter] at hi
    exact hi.2

/-- **`t` lies off the Gray code's initial segment `(grayCode s t).dropLast`** — its only occurrence
in the (duplicate-free) code is the final entry, which `dropLast` removes. This is the "`t` off the
path `[g₁, …, g_{m-1}]`" hypothesis that the §4.5.2 swap chain (`swapConj_swapChain_support`)
consumes to keep `|t⟩` fixed while the active pair is relocated. Follows from `grayCode_nodup` and
`grayCode_getLast?` via `l = l.dropLast ++ [l.getLast]`. -/
theorem grayCode_getLast_not_mem_dropLast (s t : Fin m → Fin 2) :
    t ∉ (grayCode s t).dropLast := by
  have hne : grayCode s t ≠ [] := grayCode_ne_nil s t
  have hlast : (grayCode s t).getLast hne = t := by
    have h := grayCode_getLast? s t
    rw [List.getLast?_eq_some_getLast hne] at h
    exact Option.some_inj.mp h
  have hnd : (grayCode s t).Nodup := grayCode_nodup s t
  have hsplit : (grayCode s t).dropLast ++ [(grayCode s t).getLast hne] = grayCode s t :=
    List.dropLast_append_getLast hne
  have hnd' : ((grayCode s t).dropLast ++ [(grayCode s t).getLast hne]).Nodup := by
    rw [hsplit]; exact hnd
  have hpair := (List.nodup_append.mp hnd').2.2
  have hnotmem : (grayCode s t).getLast hne ∉ (grayCode s t).dropLast := fun hmem =>
    hpair _ hmem _ (List.mem_singleton_self _) rfl
  rwa [hlast] at hnotmem

/-!
## The swap-chain path `(grayCode s t).dropLast`

N&C §4.5.2 relocates the active pair of a two-level unitary by conjugating with the swap chain read
off the Gray-code path with its **final** entry `t = g_m` dropped, `(grayCode s t).dropLast =
[g₁, …, g_{m-1}]`. The three facts `swapConj_swapChain_support` consumes about that path are: its
head is `s` (`grayCode_dropLast_head?`), its last entry is bit-adjacent to `t`
(`grayCode_dropLast_getLast?_differsInOneBit` — so the relocated pair `{g_{m-1}, t}` is a
single-bit-differing pair, i.e. a controlled single-qubit gate), and `t` lies off it
(`grayCode_getLast_not_mem_dropLast`, above). All three need `s ≠ t` (else `grayCode s t = [s]` and
the path is empty — no relocation is required, the unitary already acts on a single basis state).
-/

/-- For distinct `s ≠ t` the swap-chain path `(grayCode s t).dropLast` is nonempty: the Gray code
has at least two entries (it starts at `s ≠ t` and ends at `t`), so dropping its last entry leaves
a nonempty list. -/
theorem grayCode_dropLast_ne_nil (s t : Fin m → Fin 2) (hst : s ≠ t) :
    (grayCode s t).dropLast ≠ [] := by
  intro h
  have hsplit : (grayCode s t).dropLast ++ [t] = grayCode s t :=
    List.dropLast_append_getLast? _ (Option.mem_def.mpr (grayCode_getLast? s t))
  rw [h, List.nil_append] at hsplit
  have hhd := grayCode_head? s t
  rw [← hsplit, List.head?_cons, Option.some_inj] at hhd
  exact hst hhd.symm

/-- **The swap-chain path `(grayCode s t).dropLast` begins at `s`** — the `path.head? = some s`
hypothesis of `swapConj_swapChain_support`, with `s = g₁` the Gray code's start (N&C §4.5.2).
Dropping the last entry `t` of the Gray code leaves a nonempty path (`s ≠ t`) still headed by
`s`. -/
theorem grayCode_dropLast_head? (s t : Fin m → Fin 2) (hst : s ≠ t) :
    (grayCode s t).dropLast.head? = some s := by
  have hsplit : (grayCode s t).dropLast ++ [t] = grayCode s t :=
    List.dropLast_append_getLast? _ (Option.mem_def.mpr (grayCode_getLast? s t))
  have hhd := grayCode_head? s t
  rw [← hsplit, List.head?_append_of_ne_nil _ (grayCode_dropLast_ne_nil s t hst)] at hhd
  exact hhd

/-- **The last entry of the swap-chain path `(grayCode s t).dropLast` is bit-adjacent to `t`.** That
entry is the penultimate Gray-code word `g_{m-1}`, and `g_{m-1}`, `t = g_m` are consecutive
Gray-code words (`grayCode_isChain`), hence `differsInOneBit`. This is what makes the relocated pair
`{g_{m-1}, t}` produced by `swapConj_swapChain_support` a pair of basis states differing in exactly
one bit — the point where the two-level unitary is a *controlled single-qubit gate* (N&C §4.5.2). -/
theorem grayCode_dropLast_getLast?_differsInOneBit (s t : Fin m → Fin 2) (hst : s ≠ t) :
    ∃ e, (grayCode s t).dropLast.getLast? = some e ∧ differsInOneBit e t := by
  have hne := grayCode_dropLast_ne_nil s t hst
  have hsplit : (grayCode s t).dropLast ++ [t] = grayCode s t :=
    List.dropLast_append_getLast? _ (Option.mem_def.mpr (grayCode_getLast? s t))
  refine ⟨(grayCode s t).dropLast.getLast hne, List.getLast?_eq_some_getLast hne, ?_⟩
  have hchain : List.IsChain differsInOneBit (grayCode s t) := grayCode_isChain s t
  rw [← hsplit] at hchain
  obtain ⟨-, -, hcross⟩ := List.isChain_append.1 hchain
  exact hcross _ (Option.mem_def.mpr (List.getLast?_eq_some_getLast hne)) t (Option.mem_def.mpr rfl)

end AxQM.Concrete
