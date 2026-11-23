/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNot
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic

/-!
# Concrete: the recursive `O(n²)` no-work-qubit `Cⁿ(X)` circuit (N&C Exercise 4.29)

Building on `AxQM/Concrete/MultiControlledNot.lean`, this file assembles the
**recursive halving construction** that Nielsen & Chuang, Exercise 4.29 (p. 184), asks for: a
circuit of `Toffoli`, `CNOT` and single-qubit (`NOT`) gates that implements the `n`-controlled
`NOT` `Cⁿ(X)`, using each gate at most twice-controlled and using no *clean* work qubit — the only
scratch is a **dirty borrowed wire** drawn from the register, restored after use.

A *gate* is a pair `(S, t) : Finset (Fin m) × Fin m` denoting `mcNot S t`; a *circuit* is a
`List` of gates, denoted (`mcNotDenote`) by composing the gates' actions. The construction
(`exists_mcNotCircuit`) is: to build `mcNot S t` with `|S| ≥ 3` controls, split the controls into
two near-equal halves `A ⊔ B` (`|A| = ⌈|S|/2⌉`, `|B| = ⌊|S|/2⌋`), pick a borrowed wire `a` outside
the gate's support, and apply the dirty-borrow reduction `mcNot_union_borrow`:
`mcNot (A ∪ B) t = mcNot (insert a B) t ∘ mcNot A a ∘ mcNot (insert a B) t ∘ mcNot A a`,
recursing on the two smaller gates `mcNot (insert a B) t` (with `⌊|S|/2⌋ + 1` controls) and
`mcNot A a` (with `⌈|S|/2⌉` controls). The recursion bottoms out at `|S| ≤ 2` — a single `Toffoli`,
`CNOT`, or `NOT`.

The **borrowed wire is always available in the recursive calls** because after the first split each
sub-gate touches only a proper part of the register, leaving the other half (and the target) free
to borrow; the sole hypothesis is that the *top* call has at least one wire outside its support
(`(insert t S).card < m`), and this invariant is preserved downward. The gate count is bounded by
the explicit recurrence `mcNotGateBound |S|` satisfying `T(k) = 2 T(⌈k/2⌉) + 2 T(⌊k/2⌋+1)`, which
is `Θ(k²)`; the asymptotic `O(n²)` reading of this bound (an `Asymptotics.IsBigO`), and the
tight-register bootstrap that manufactures the first borrowed wire on exactly `n + 1` qubits
(Barenco's `n ≥ 4` step), are separate developments built on this one.

Everything here is `Fin 2`/`Finset` combinatorics; each gate is realised as a genuine `Evolution`,
and the circuit as `mcCtrl n pauliXGate`, elsewhere.
-/

namespace AxQM.Concrete

variable {m : ℕ}

/-- A single reversible gate of a multiply-controlled-`NOT` circuit: the control set together with
the target wire, denoting the classical gate `mcNot S t`. With `|S| ≤ 2` this is a `Toffoli`
(`|S| = 2`), `CNOT` (`|S| = 1`), or `NOT` (`|S| = 0`). -/
abbrev McNotGate (m : ℕ) : Type := Finset (Fin m) × Fin m

/-- **Denotation of a gate circuit**: the reversible map on bit-strings obtained by applying each
gate's `mcNot` action in turn, the head gate acting last (leftmost in the composition). -/
def mcNotDenote (gs : List (McNotGate m)) (x : Fin m → Fin 2) : Fin m → Fin 2 :=
  gs.foldr (fun g y => mcNot g.1 g.2 y) x

@[simp] theorem mcNotDenote_nil (x : Fin m → Fin 2) : mcNotDenote [] x = x := rfl

@[simp] theorem mcNotDenote_cons (g : McNotGate m) (gs : List (McNotGate m)) (x : Fin m → Fin 2) :
    mcNotDenote (g :: gs) x = mcNot g.1 g.2 (mcNotDenote gs x) := rfl

/-- Concatenating circuits composes their denotations (the second list acts first). -/
@[simp] theorem mcNotDenote_append (gs hs : List (McNotGate m)) (x : Fin m → Fin 2) :
    mcNotDenote (gs ++ hs) x = mcNotDenote gs (mcNotDenote hs x) :=
  List.foldr_append

/-- **A reversed gate circuit inverts the original.** For a valid circuit `gs` (every gate's target
not among its controls, so each gate `mcNot g.1 g.2` is an involution, `mcNot_involutive`), running
the reversed circuit `gs.reverse` and then `gs` returns every bit-string unchanged:
`mcNotDenote gs (mcNotDenote gs.reverse x) = x`. Equivalently `gs.reverse` denotes the inverse
permutation of `gs`. Proved by induction on `gs`, folding `List.reverse_cons` through
`mcNotDenote_append`/`mcNotDenote_cons` and closing each layer with the per-gate involutivity. -/
theorem mcNotDenote_mcNotDenote_reverse :
    ∀ (gs : List (McNotGate m)), (∀ g ∈ gs, g.2 ∉ g.1) →
      ∀ (x : Fin m → Fin 2), mcNotDenote gs (mcNotDenote gs.reverse x) = x
  | [], _, x => by simp
  | g :: gs, hgs, x => by
      rw [List.reverse_cons, mcNotDenote_cons, mcNotDenote_append, mcNotDenote_cons,
        mcNotDenote_nil,
        mcNotDenote_mcNotDenote_reverse gs
          (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (mcNot g.1 g.2 x)]
      exact mcNot_involutive g.1 (hgs g (by simp)) x

/-- **The gate-count bound of the halving construction**: an explicit `ℕ → ℕ` recurrence with
`T(k) = 1` for `k ≤ 2` (one base gate) and `T(k) = 2 T(⌈k/2⌉) + 2 T(⌊k/2⌋+1)` for `k ≥ 3` (two
copies each of the two sub-gates produced by `mcNot_union_borrow`). This is `Θ(k²)`; the `O(n²)`
statement of the exercise is `mcNotGateBound n = O[atTop] n²`. -/
def mcNotGateBound : ℕ → ℕ
  | k =>
    if 3 ≤ k then
      2 * mcNotGateBound ((k + 1) / 2) + 2 * mcNotGateBound (k / 2 + 1)
    else 1
decreasing_by
  · omega
  · omega

/-- Unfolding of `mcNotGateBound` at the base cases `k ≤ 2`. -/
theorem mcNotGateBound_of_le {k : ℕ} (hk : k ≤ 2) : mcNotGateBound k = 1 := by
  rw [mcNotGateBound]; exact ite_eq_right (by omega)

/-- Unfolding of `mcNotGateBound` at the recursive cases `k ≥ 3`. -/
theorem mcNotGateBound_of_ge {k : ℕ} (hk : 3 ≤ k) :
    mcNotGateBound k = 2 * mcNotGateBound ((k + 1) / 2) + 2 * mcNotGateBound (k / 2 + 1) := by
  rw [mcNotGateBound]; exact ite_eq_left hk

/-- **The recursive `O(n²)` `Cⁿ(X)` circuit (N&C Exercise 4.29).** For any control set `S` and
target `t ∉ S` on a register `Fin m` that has at least one wire outside the gate's support
(`(insert t S).card < m` — the borrowed wire needed to start the recursion), there is a circuit of
gates each with at most two controls (a `Toffoli`/`CNOT`/`NOT`, target never a control) whose
denotation is exactly `mcNot S t = C^{|S|}(X)`, and whose length is bounded by `mcNotGateBound |S|`
(a `Θ(|S|²)` recurrence). The construction uses the dirty borrowed-wire reduction
`mcNot_union_borrow` recursively, halving the control set; no clean work qubit is introduced. -/
theorem exists_mcNotCircuit (S : Finset (Fin m)) (t : Fin m)
    (hst : t ∉ S) (hspare : (insert t S).card < m) :
    ∃ gs : List (McNotGate m),
      (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
      mcNotDenote gs = mcNot S t ∧
      gs.length ≤ mcNotGateBound S.card := by
  suffices H : ∀ n : ℕ, ∀ (S : Finset (Fin m)) (t : Fin m),
      S.card = n → t ∉ S → (insert t S).card < m →
      ∃ gs : List (McNotGate m),
        (∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) ∧
        mcNotDenote gs = mcNot S t ∧ gs.length ≤ mcNotGateBound S.card by
    exact H S.card S t rfl hst hspare
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro S t hcard hst hspare
    by_cases hn : n ≤ 2
    · -- Base case: a single ≤2-control gate.
      refine ⟨[(S, t)], ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg
        exact ⟨by simpa [hcard] using hn, hst⟩
      · funext x; simp [mcNotDenote]
      · simp only [List.length_singleton]
        rw [mcNotGateBound_of_le (hcard ▸ hn)]
    · -- Recursive case: `n ≥ 3`. Split `S = A ⊔ B` and borrow a wire `a`.
      have hn3 : 3 ≤ n := by omega
      -- A borrowed wire `a` outside the gate's support.
      have hcompl : (insert t S)ᶜ.Nonempty := by
        rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]; omega
      obtain ⟨a, ha⟩ := hcompl
      rw [Finset.mem_compl, Finset.mem_insert, not_or] at ha
      obtain ⟨hat, haS⟩ := ha
      -- The first half `A ⊆ S` of size `⌈n/2⌉`, and `B = S \ A` of size `⌊n/2⌋`.
      obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq (n := (n + 1) / 2) (s := S)
        (by rw [hcard]; omega)
      set B := S \ A with hB
      have hAB : A ∪ B = S := Finset.union_sdiff_of_subset hAS
      have hBcard : B.card = n / 2 := by
        rw [hB, Finset.card_sdiff_of_subset hAS, hcard, hAcard]; omega
      have haA : a ∉ A := fun h => haS (hAS h)
      have haB : a ∉ B := fun h => haS (Finset.sdiff_subset h)
      have htA : t ∉ A := fun h => hst (hAS h)
      have htB : t ∉ B := fun h => hst (Finset.sdiff_subset h)
      have htaB : t ∉ insert a B := by
        rw [Finset.mem_insert, not_or]; exact ⟨fun h => hat h.symm, htB⟩
      -- Cardinalities of the two sub-gates' control sets.
      have hS1card : (insert a B).card = n / 2 + 1 := by
        rw [Finset.card_insert_of_notMem haB, hBcard]
      have htSn : (insert t S).card = n + 1 := by rw [Finset.card_insert_of_notMem hst, hcard]
      -- Spare-wire invariant is preserved for both sub-gates (their supports are smaller).
      have hspare1 : (insert t (insert a B)).card < m := by
        rw [Finset.card_insert_of_notMem htaB, hS1card]; omega
      have hspare2 : (insert a A).card < m := by
        rw [Finset.card_insert_of_notMem haA, hAcard]; omega
      -- Recurse on the two sub-gates.
      obtain ⟨gs₁, hgate₁, hden₁, hlen₁⟩ :=
        IH (n / 2 + 1) (by omega) (insert a B) t hS1card htaB hspare1
      obtain ⟨gs₂, hgate₂, hden₂, hlen₂⟩ :=
        IH ((n + 1) / 2) (by omega) A a hAcard haA hspare2
      -- Assemble: two copies each, matching `mcNot_union_borrow`.
      refine ⟨gs₁ ++ gs₂ ++ gs₁ ++ gs₂, ?_, ?_, ?_⟩
      · simp only [List.forall_mem_append]
        exact ⟨⟨⟨hgate₁, hgate₂⟩, hgate₁⟩, hgate₂⟩
      · funext x
        have e := congrFun (mcNot_union_borrow A B haA haB hat htA htB) x
        simp only [Function.comp_apply] at e
        simp only [mcNotDenote_append, hden₁, hden₂]
        rw [← hAB, e]
      · simp only [List.length_append]
        have hb := mcNotGateBound_of_ge hn3
        rw [hS1card] at hlen₁
        rw [hAcard] at hlen₂
        rw [hcard]
        omega

/-! ### Prepending an idle head wire to a gate circuit

Placing a whole `≤ 2`-control gate circuit `gs` on the *tail* wires `1, …, m` of an `(m+1)`-wire
register — the head wire `0` left untouched — is, at the classical bit-string level, shifting every
gate's control set and target up by `Fin.succ`. This section supplies that reindexing and its
passthrough law, the combinatorial core of the register-level "add an idle head wire" closure of the
`Evolution` gate-count budget (`Core/CircuitBudgetOnRight`). -/

/-- **Prepend an idle head wire to a gate.** Shift a gate's control set and target up by `Fin.succ`,
so it acts on wires `1, …, m` of the `(m+1)`-wire register and leaves the new head wire `0`
untouched: `(S, t) ↦ (Fin.succ '' S, t.succ)`. -/
def mcNotConsWire (g : McNotGate m) : McNotGate (m + 1) :=
  (g.1.map ⟨Fin.succ, Fin.succ_injective m⟩, g.2.succ)

/-- Prepending an idle head wire preserves a gate's control count (`Fin.succ` is injective). -/
theorem mcNotConsWire_card (g : McNotGate m) : (mcNotConsWire g).1.card = g.1.card := by
  simp [mcNotConsWire]

/-- Prepending an idle head wire preserves "the target is not a control": if `t ∉ S` then
`t.succ ∉ Fin.succ '' S`. -/
theorem mcNotConsWire_target_not_mem {g : McNotGate m} (h : g.2 ∉ g.1) :
    (mcNotConsWire g).2 ∉ (mcNotConsWire g).1 := by
  simp only [mcNotConsWire, Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
  intro a ha hcontra
  exact h (Fin.succ_injective m hcontra ▸ ha)

/-- The control bit of a shifted gate on `Fin.cons b x` reads the same controls as the original gate
on `x`: the new head wire `0` is not in the shifted control set, so `b` is ignored. -/
theorem ctrlBit_map_succ_cons (S : Finset (Fin m)) (b : Fin 2) (x : Fin m → Fin 2) :
    ctrlBit (S.map ⟨Fin.succ, Fin.succ_injective m⟩) (Fin.cons b x) = ctrlBit S x := by
  unfold ctrlBit
  have hiff : (∀ i ∈ S.map ⟨Fin.succ, Fin.succ_injective m⟩,
      (Fin.cons b x : Fin (m + 1) → Fin 2) i = 1) ↔ (∀ a ∈ S, x a = 1) := by
    constructor
    · intro h a ha
      have h2 := h a.succ (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
      rwa [Fin.cons_succ] at h2
    · intro h i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
      rw [Function.Embedding.coeFn_mk, Fin.cons_succ]
      exact h a ha
  exact if_congr hiff rfl rfl

/-- **Per-gate passthrough.** A gate shifted up by `Fin.succ`, acting on `Fin.cons b x`, leaves the
head wire `b` untouched and acts as the original gate on the tail `x`:
`mcNot (Fin.succ '' S) t.succ (Fin.cons b x) = Fin.cons b (mcNot S t x)`. -/
theorem mcNot_map_succ_cons (S : Finset (Fin m)) (t : Fin m) (b : Fin 2) (x : Fin m → Fin 2) :
    mcNot (S.map ⟨Fin.succ, Fin.succ_injective m⟩) t.succ (Fin.cons b x)
      = Fin.cons b (mcNot S t x) := by
  unfold mcNot
  rw [ctrlBit_map_succ_cons, Fin.cons_succ, Fin.cons_update]

/-- **Circuit passthrough.** The whole shifted circuit `gs.map mcNotConsWire`, acting on
`Fin.cons b x`, passes the head wire `b` through and denotes as the original circuit `gs` on the
tail `x`: `mcNotDenote (gs.map mcNotConsWire) (Fin.cons b x) = Fin.cons b (mcNotDenote gs x)`. By
induction on `gs` from the per-gate passthrough `mcNot_map_succ_cons`. -/
theorem mcNotDenote_map_mcNotConsWire (gs : List (McNotGate m)) (b : Fin 2) (x : Fin m → Fin 2) :
    mcNotDenote (gs.map mcNotConsWire) (Fin.cons b x) = Fin.cons b (mcNotDenote gs x) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      rw [List.map_cons, mcNotDenote_cons, ih, mcNotDenote_cons]
      exact mcNot_map_succ_cons g.1 g.2 b (mcNotDenote gs x)

end AxQM.Concrete
