/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNotDirtyCascade

/-!
# Concrete: the genuine dirty-ancilla `Cᵏ(X)` from a double borrowed-wire AND cascade

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for an `O(n²)` no-work-qubit circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing the `n`-controlled `NOT` `Cⁿ(X)`. The linear-cascade
sub-project reaches the `O(n²)` count — which the `Θ(k²)` halving recursion
`exists_mcNotCircuit` misses (it sums to `Θ(n³)` over `barencoNCircuit`'s `O(n)` blocks) —
by bottoming each internal `Cᵏ(X)` block in a **linear**
`O(k)` number of `Toffoli`s, using the register's idle wires as **dirty** borrowed ancillas
(Barenco *Elementary gates*, Lemma 7.2/7.3).

`AxQM/Concrete/MultiControlledNotDirtyCascade.lean` builds the **borrowed-wire AND
cascade** `borrowedAndCascade as cs tgt`: it flips the target by the exact control AND
`ctrlBit cs.toFinset x`, **independently of the dirty borrowed wires**
(`borrowedAndCascade_apply_tgt`), in a linear number of `≤ 2`-control gates — but it *corrupts* the
borrowed wires (each is flipped by a partial AND), so it is **not** itself a `Cᵏ(X)`. It is however
an involution (`borrowedAndCascade_involutive`).

This file assembles the genuine dirty `Cᵏ(X)` from it. Write

* `C := borrowedAndCascade (a :: as) (c :: cs) tgt` — the full cascade: flips `tgt` by
  `⋀ (c :: cs)`, corrupts the ancillas `a :: as`;
* `R := borrowedAndCascade as cs a` — the *sub*-cascade one layer down (target the head ancilla
  `a`).

The key structural fact (`borrowedAndCascade_agree_off_tgt`) is that `C` and `R` **act identically
on every wire except `tgt`** — because `C = T · R · T` sandwiches `R` between two copies of the
single `Toffoli` `T = ({a, c}, tgt)`, and `T` touches only `tgt`, which lies outside `R`'s support.
Hence

`borrowedMcNot (a :: as) (c :: cs) tgt := C ++ R`

is a genuine `Cᵏ(X)`: applied as `x ↦ C (R x)`, on the target it flips by `⋀ (c :: cs)` (the two
target-flips of `R` are killed since `R` fixes `tgt`, and `C` supplies the one correct flip), and on
every other wire `C` acts as `R`, so the net effect is `R (R x) = x` — every borrowed wire is
**restored** (`mcNotDenote_borrowedMcNot`). Its gates are all `Toffoli`/`CNOT`/`NOT`
(`borrowedMcNot_gate_mem`) and its length is linear, `≤ 4 |as| + 1` (`borrowedMcNot_length_le`) —
the `O(k)` per-block count the `O(n²)` assembly needs, requiring `|cs| - 2` **arbitrary** (dirty)
borrowed wires and **no** clean work qubit.

Everything here is `Fin 2`/`Finset`/`List` combinatorics. Compare the other `MultiControlledNot*`
files.
-/

namespace AxQM.Concrete

variable {m : ℕ}

/-! ### Two reusable frame lemmas for `mcNot` circuits -/

/-- **`ctrlBit` depends only on the control wires.** Two bit-strings agreeing on every wire of the
control set `S` have the same control bit. -/
theorem ctrlBit_congr {S : Finset (Fin m)} {x y : Fin m → Fin 2} (h : ∀ i ∈ S, y i = x i) :
    ctrlBit S y = ctrlBit S x := by
  simp only [ctrlBit, forall_mem_eq_one_congr h]

/-- **Per-gate frame lemma.** Updating a wire `w` that is neither a control (`w ∉ S`) nor the target
(`w ≠ t`) of a gate commutes with the gate: `mcNot S t (x[w ↦ v]) = (mcNot S t x)[w ↦ v]`. The gate
neither reads nor writes `w`, so the update passes straight through. -/
theorem mcNot_update_comm (S : Finset (Fin m)) (t : Fin m) {w : Fin m} (hwS : w ∉ S) (hwt : w ≠ t)
    (x : Fin m → Fin 2) (v : Fin 2) :
    mcNot S t (Function.update x w v) = Function.update (mcNot S t x) w v := by
  unfold mcNot
  rw [ctrlBit_update_of_notMem S hwS, Function.update_of_ne (Ne.symm hwt),
    Function.update_comm hwt]

/-- **Circuit frame lemma.** If a wire `w` is outside the support of every gate of a circuit `gs`
(never a control, `w ∉ g.1`, and never a target, `w ≠ g.2`), then updating `w` commutes with running
the whole circuit: `mcNotDenote gs (x[w ↦ v]) = (mcNotDenote gs x)[w ↦ v]`. Proved by structural
recursion over the gate list, iterating `mcNot_update_comm`. -/
theorem mcNotDenote_update_comm {w : Fin m} :
    ∀ (gs : List (McNotGate m)), (∀ g ∈ gs, w ∉ g.1 ∧ w ≠ g.2) →
      ∀ (x : Fin m → Fin 2) (v : Fin 2),
        mcNotDenote gs (Function.update x w v) = Function.update (mcNotDenote gs x) w v
  | [], _, _, _ => rfl
  | g :: gs, h, x, v => by
      rw [mcNotDenote_cons, mcNotDenote_cons,
        mcNotDenote_update_comm gs (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) x v,
        mcNot_update_comm _ _ (h g List.mem_cons_self).1 (h g List.mem_cons_self).2]

/-! ### The target lies outside the sub-cascade's support -/

/-- **The borrowed-wire AND cascade has no external wire as a control or target.** Any wire `w`
distinct from every control (`w ∉ cs`), every ancilla (`w ∉ as`), and the target (`w ≠ t`) occurs
neither as a control nor as a target of any gate of `borrowedAndCascade as cs t`. Used to feed
`mcNotDenote_update_comm`: the outer register wire `tgt` of the enclosing cascade lies outside the
sub-cascade's support. -/
theorem borrowedAndCascade_notMem_support :
    ∀ (as cs : List (Fin m)) (t : Fin m) {w : Fin m}, w ∉ cs → w ∉ as → w ≠ t →
      ∀ g ∈ borrowedAndCascade as cs t, w ∉ g.1 ∧ w ≠ g.2
  | [], cs, t, w => by
      intro hwc _ hwt g hg
      rw [borrowedAndCascade_nil, List.mem_singleton] at hg
      subst hg
      exact ⟨by rwa [List.mem_toFinset], hwt⟩
  | a :: as, cs, t, w => by
      intro hwc hwa hwt g hg
      obtain _ | ⟨c, cs⟩ := cs
      · rw [borrowedAndCascade_cons_nil, List.mem_singleton] at hg
        subst hg
        exact ⟨by simp, hwt⟩
      · have hwa' : w ∉ as := fun h => hwa (List.mem_cons_of_mem _ h)
        have hwa_ne : w ≠ a := fun h => hwa (h ▸ List.mem_cons_self)
        have hwc' : w ∉ cs := fun h => hwc (List.mem_cons_of_mem _ h)
        have hwc_ne : w ≠ c := fun h => hwc (h ▸ List.mem_cons_self)
        have hpeel : w ∉ ({a, c} : Finset (Fin m)) ∧ w ≠ t := by
          refine ⟨?_, hwt⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hwa_ne, hwc_ne⟩
        rw [borrowedAndCascade_cons] at hg
        rcases List.mem_cons.mp hg with hg | hg
        · subst hg; exact hpeel
        rcases List.mem_append.mp hg with hg | hg
        · exact borrowedAndCascade_notMem_support as cs a hwc' hwa' hwa_ne g hg
        · rw [List.mem_singleton] at hg; subst hg; exact hpeel

/-- **The full cascade and its sub-cascade agree off the target.** For any wire `w ≠ tgt`,
`borrowedAndCascade (a :: as) (c :: cs) tgt` acts on `w` exactly as its one-layer-down sub-cascade
`borrowedAndCascade as cs a` (target the head ancilla `a`). Reason: the full cascade is `T · R · T`
with `R = borrowedAndCascade as cs a` and `T = ({a, c}, tgt)` a single `Toffoli` touching only
`tgt`;
since `tgt` lies outside `R`'s support, `R`'s obliviousness to `tgt` (`mcNotDenote_update_comm` +
`borrowedAndCascade_notMem_support`) and the two `T`s leave `R`'s action on every other wire
unchanged. This is what lets the double cascade restore the borrowed wires. -/
theorem borrowedAndCascade_agree_off_tgt {a : Fin m} {as : List (Fin m)} (c : Fin m)
    {cs : List (Fin m)} {tgt : Fin m} (htcs : tgt ∉ cs) (htas : tgt ∉ as) (hta : tgt ≠ a)
    (x : Fin m → Fin 2) {w : Fin m} (hwt : w ≠ tgt) :
    mcNotDenote (borrowedAndCascade (a :: as) (c :: cs) tgt) x w
      = mcNotDenote (borrowedAndCascade as cs a) x w := by
  rw [borrowedAndCascade_cons, mcNotDenote_cons, mcNot_apply_of_ne _ _ _ hwt, mcNotDenote_append]
  simp only [mcNotDenote_cons, mcNotDenote_nil]
  rw [mcNot, mcNotDenote_update_comm (borrowedAndCascade as cs a)
      (borrowedAndCascade_notMem_support as cs a htcs htas hta) x _,
    Function.update_of_ne hwt]

/-! ### The genuine dirty `Cᵏ(X)` circuit -/

/-- **The dirty-ancilla `Cᵏ(X)` circuit** (Barenco *Elementary gates*, Lemma 7.2/7.3). Given
borrowed ancilla wires `as`, controls `cs`, and target `tgt`, `borrowedMcNot as cs tgt` runs the
borrowed-wire AND cascade `borrowedAndCascade (a :: as) (c :: cs) tgt` (which flips `tgt` by the
exact control AND
but corrupts the ancillas) followed by the one-layer-down sub-cascade `borrowedAndCascade as cs a`
(which un-corrupts the ancillas without touching `tgt`, since it is an involution and the two agree
off `tgt`). It bottoms out (ancillas exhausted, `|cs| ≤ 2`) at a single `≤ 2`-control gate. With
`|cs| - 2` **arbitrary** (dirty) borrowed ancillas it is a genuine `C^{|cs|}(X)` restoring every
wire (`mcNotDenote_borrowedMcNot`), in a **linear** `O(|cs|)` number of `Toffoli`/`CNOT`/`NOT` gates
and no clean work qubit. -/
def borrowedMcNot : List (Fin m) → List (Fin m) → Fin m → List (McNotGate m)
  | a :: as, c :: cs, tgt =>
      borrowedAndCascade (a :: as) (c :: cs) tgt ++ borrowedAndCascade as cs a
  | _, cs, tgt => [(cs.toFinset, tgt)]

/-- Base unfolding of `borrowedMcNot` when the ancillas run out (`|cs| ≤ 2`: a single base gate). -/
theorem borrowedMcNot_nil (cs : List (Fin m)) (tgt : Fin m) :
    borrowedMcNot [] cs tgt = [(cs.toFinset, tgt)] := rfl

/-- Base unfolding of `borrowedMcNot` when the controls run out (unreached under the invariant
`|cs| = |as| + 2`). -/
theorem borrowedMcNot_cons_nil (a : Fin m) (as : List (Fin m)) (tgt : Fin m) :
    borrowedMcNot (a :: as) [] tgt = [(([] : List (Fin m)).toFinset, tgt)] := rfl

/-- Recursive unfolding of `borrowedMcNot` (≥ 1 ancilla, ≥ 1 control): the full cascade followed by
its one-layer-down sub-cascade. -/
theorem borrowedMcNot_cons (a : Fin m) (as : List (Fin m)) (c : Fin m) (cs : List (Fin m))
    (tgt : Fin m) :
    borrowedMcNot (a :: as) (c :: cs) tgt
      = borrowedAndCascade (a :: as) (c :: cs) tgt ++ borrowedAndCascade as cs a := rfl

/-- **The dirty `Cᵏ(X)` is linear.** `borrowedMcNot as cs tgt` has at most `4 |as| + 1` gates —
twice the borrowed-wire cascade's `≤ 2|as| + 1` plus its one-layer sub-cascade, `O(|as|) = O(|cs|)`
(the linear per-block count the `O(n²)` assembly needs). -/
theorem borrowedMcNot_length_le (as cs : List (Fin m)) (tgt : Fin m) :
    (borrowedMcNot as cs tgt).length ≤ 4 * as.length + 1 := by
  obtain _ | ⟨a, as⟩ := as
  · rw [borrowedMcNot_nil]; simp
  · obtain _ | ⟨c, cs⟩ := cs
    · rw [borrowedMcNot_cons_nil]; simp only [List.length_cons, List.length_nil]; omega
    · rw [borrowedMcNot_cons, List.length_append]
      have h1 := borrowedAndCascade_length_le (a :: as) (c :: cs) tgt
      have h2 := borrowedAndCascade_length_le as cs a
      simp only [List.length_cons] at h1 ⊢
      omega

/-- **Every gate of the dirty `Cᵏ(X)` is a `Toffoli`/`CNOT`/`NOT`** (`≤ 2` controls, target not a
control), under the matching invariant `|cs| = |as| + 2` with all wires distinct — inherited from
the two borrowed-wire cascades it concatenates. -/
theorem borrowedMcNot_gate_mem (as cs : List (Fin m)) (tgt : Fin m)
    (hlen : cs.length = as.length + 2) (hcs : cs.Nodup) (has : as.Nodup) (hdisj : cs.Disjoint as)
    (htcs : tgt ∉ cs) (htas : tgt ∉ as) :
    ∀ g ∈ borrowedMcNot as cs tgt, g.1.card ≤ 2 ∧ g.2 ∉ g.1 := by
  obtain _ | ⟨a, as⟩ := as
  · rw [borrowedMcNot_nil]
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    refine ⟨?_, ?_⟩
    · calc cs.toFinset.card ≤ cs.length := List.toFinset_card_le cs
        _ = 2 := by simp only [List.length_nil] at hlen; omega
    · simpa [List.mem_toFinset] using htcs
  · obtain _ | ⟨c, cs⟩ := cs
    · simp only [List.length_nil, List.length_cons] at hlen; omega
    · rw [borrowedMcNot_cons]
      obtain ⟨hlen', hcs', has', hdisj', hacs', haas'⟩ :=
        borrowedAndCascade_step_hyps hlen hcs has hdisj
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact borrowedAndCascade_gate_mem (a :: as) (c :: cs) tgt hlen hcs has hdisj htcs htas g hg
      · exact borrowedAndCascade_gate_mem as cs a hlen' hcs' has' hdisj' hacs' haas' g hg

/-- **N&C Exercise 4.29 / Barenco Lemma 7.2/7.3 — the double borrowed-wire cascade is a genuine
dirty `Cᵏ(X)`.** With `|cs|` controls, `|cs| - 2` **arbitrary** (dirty) borrowed ancillas `as`, and
every
wire distinct, `borrowedMcNot as cs tgt` acts on the bit-string `x` exactly as the multiply-
controlled `NOT` `mcNot cs.toFinset tgt` — flipping only the target by the true control AND
`ctrlBit cs.toFinset x` and **restoring every borrowed wire**, with no dependence on the ancillas'
initial values.

Applied as `x ↦ C (R x)` with `C = borrowedAndCascade (a :: as) (c :: cs) tgt` and
`R = borrowedAndCascade as cs a`:

* on the target `tgt`, `C` supplies the one correct flip `⋀ (c :: cs)`
  (`borrowedAndCascade_apply_tgt`) while `R` fixes `tgt` and every control
  (`borrowedAndCascade_apply_of_ne`, `ctrlBit_congr`);
* on every other wire `C` acts as `R` (`borrowedAndCascade_agree_off_tgt`), so the net effect is
  `R (R x) = x` (`borrowedAndCascade_involutive`) — the corruption cancels. -/
theorem mcNotDenote_borrowedMcNot (as cs : List (Fin m)) (tgt : Fin m)
    (hlen : cs.length = as.length + 2) (hcs : cs.Nodup) (has : as.Nodup) (hdisj : cs.Disjoint as)
    (htcs : tgt ∉ cs) (htas : tgt ∉ as) (x : Fin m → Fin 2) :
    mcNotDenote (borrowedMcNot as cs tgt) x = mcNot cs.toFinset tgt x := by
  obtain _ | ⟨a, as⟩ := as
  · rw [borrowedMcNot_nil]
    simp [mcNotDenote_cons, mcNotDenote_nil]
  · obtain _ | ⟨c, cs⟩ := cs
    · simp only [List.length_nil, List.length_cons] at hlen; omega
    · rw [borrowedMcNot_cons, mcNotDenote_append]
      -- Distinctness facts for the sub-cascade `R = borrowedAndCascade as cs a`.
      have hta : tgt ≠ a := fun h => htas (h ▸ List.mem_cons_self)
      have htas' : tgt ∉ as := fun h => htas (List.mem_cons_of_mem _ h)
      have htcs' : tgt ∉ cs := fun h => htcs (List.mem_cons_of_mem _ h)
      have hca : c ≠ a := by rintro rfl; exact hdisj List.mem_cons_self List.mem_cons_self
      have hcas : c ∉ as := fun h => hdisj List.mem_cons_self (List.mem_cons_of_mem _ h)
      obtain ⟨hlen', hcs', has', hdisj', hacs', haas'⟩ :=
        borrowedAndCascade_step_hyps hlen hcs has hdisj
      funext w
      by_cases hwt : w = tgt
      · subst hwt
        rw [borrowedAndCascade_apply_tgt (a :: as) (c :: cs) w hlen hcs has hdisj htcs htas
            (mcNotDenote (borrowedAndCascade as cs a) x),
          borrowedAndCascade_apply_of_ne as cs a x hta htas', mcNot_apply_self]
        congr 1
        refine ctrlBit_congr fun i hi => ?_
        rw [List.mem_toFinset] at hi
        rcases List.mem_cons.mp hi with rfl | hics
        · exact borrowedAndCascade_apply_of_ne as cs a x hca hcas
        · exact borrowedAndCascade_apply_of_ne as cs a x (fun h => hacs' (h ▸ hics)) (hdisj' hics)
      · rw [borrowedAndCascade_agree_off_tgt c htcs' htas' hta
            (mcNotDenote (borrowedAndCascade as cs a) x) hwt,
          borrowedAndCascade_involutive as cs a hlen' hcs' has' hdisj' hacs' haas' x,
          mcNot_apply_of_ne _ _ _ hwt]

end AxQM.Concrete
