/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNotCircuit

/-!
# Concrete: the borrowed-wire AND cascade for `Cⁿ(X)` (Barenco's dirty-ancilla conditioning)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for an `O(n²)` no-work-qubit circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing the `n`-controlled `NOT` `Cⁿ(X)`. The linear-cascade
sub-project reaches the `O(n²)` count (which the `Θ(k²)` halving recursion
`exists_mcNotCircuit` misses — it sums to `Θ(n³)` over `barencoNCircuit`'s `O(n)` blocks)
by bottoming each internal `Cᵏ(X)` block in a **linear** `O(k)`
number of `Toffoli`s (Barenco *Elementary gates*, Lemma 7.2/7.3). The file
`Concrete/MultiControlledNotLinearCircuit.lean` gave the **clean-ancilla** staircase (Figure 4.10);
this file supplies the **dirty-ancilla** building block, whose borrowed wires may start in an
*arbitrary* state (the wires borrowed from `barencoNCircuit`'s idle register are not clean).

## The borrowed-wire AND cascade

`borrowedAndCascade as cs tgt` (`as` the borrowed ancilla wires, `cs` the controls, `tgt` the
target) fuses the first control `c` **together with the first borrowed wire `a`** into `tgt`
(a `Toffoli` `({a, c}, tgt)`), recurses to flip `a` by the AND of the remaining controls `cs`, and
repeats the **same** `Toffoli` — a palindrome sandwich `T · (flip a by ⋀cs) · T`. It bottoms out
(ancillas exhausted) at a single `≤ 2`-control gate `(cs.toFinset, tgt)` fusing the last two
controls into `tgt`.

Its decisive property (`borrowedAndCascade_apply_tgt`) is that it flips the target by the **exact**
control AND `ctrlBit cs.toFinset x`, **independently of the borrowed wires' dirty values**: the two
copies of the `Toffoli` `({a, c}, tgt)` flip `tgt` before and after `a` is transformed by
`⋀ cs`, and in `Fin 2` the dirty part of `a` cancels between them (`x a` cancels: `x a · c + (x a ⊕
⋀cs) · c = ⋀cs · c`). This is exactly Barenco's group-commutator cancellation of a borrowed dirty
wire, here iterated down a linear cascade rather than the halving `mcNot_union_borrow`.

The cascade is **not** itself a `Cᵏ(X)`: it flips `tgt` correctly but **corrupts** the borrowed
wires (each `aᵢ` is flipped by a partial AND). It *is* an involution
(`borrowedAndCascade_involutive`, since every wire is flipped by a control-AND independent of that
wire's own value). The genuine dirty
`Cᵏ(X)` — this cascade run **twice** with a leading `Toffoli`, so the borrowed-wire corruption
cancels and every wire is restored — is built from the involution and target-action proved here
in `AxQM/Concrete/MultiControlledNotBorrowedMcNot.lean`.

Everything here is `Fin 2`/`Finset`/`List` combinatorics. Compare `MultiControlledNot` and
`MultiControlledNotCircuit`.
-/

namespace AxQM.Concrete

variable {m : ℕ}

/-! ### Two `ctrlBit` reformulations -/

/-- The control bit is set exactly when every control wire is set. -/
theorem ctrlBit_eq_one {S : Finset (Fin m)} {x : Fin m → Fin 2} :
    ctrlBit S x = 1 ↔ ∀ i ∈ S, x i = 1 := by
  rw [ctrlBit]
  split
  · exact iff_of_true rfl ‹_›
  · exact iff_of_false (by decide) ‹_›

/-- `ctrlBit` of a two-element control set `{a, c}` in boolean-`if` form. -/
theorem ctrlBit_pair (a c : Fin m) (x : Fin m → Fin 2) :
    ctrlBit ({a, c} : Finset (Fin m)) x = if x a = 1 ∧ x c = 1 then 1 else 0 := by
  rw [ctrlBit_insert]; simp only [Finset.mem_singleton, forall_eq]

/-- `ctrlBit` of a `List`-`cons` control set factors through the head control and the tail's
`ctrlBit`: `⋀ (c :: cs) = (x c = 1) ∧ (⋀ cs = 1)`. -/
theorem ctrlBit_cons_toFinset (c : Fin m) (cs : List (Fin m)) (x : Fin m → Fin 2) :
    ctrlBit (c :: cs).toFinset x = if x c = 1 ∧ ctrlBit cs.toFinset x = 1 then 1 else 0 := by
  rw [List.toFinset_cons, ctrlBit_insert]
  simp only [ctrlBit_eq_one]

/-! ### The borrowed-wire AND cascade -/

/-- **The borrowed-wire AND cascade** (Barenco's dirty-ancilla conditioning cascade). Given borrowed
ancilla wires `as`, controls `cs`, and target `tgt`, it fuses the first control `c` with the first
borrowed wire `a` into `tgt` (a `Toffoli` `({a, c}, tgt)`), recurses to flip `a` by the AND of the
remaining controls `cs`, and repeats the same `Toffoli`; it bottoms out (ancillas exhausted) at a
single `≤ 2`-control gate fusing the remaining controls into `tgt`. See the file docstring for its
dirty-robust target action. -/
def borrowedAndCascade : List (Fin m) → List (Fin m) → Fin m → List (McNotGate m)
  | a :: as, c :: cs, tgt => ({a, c}, tgt) :: (borrowedAndCascade as cs a ++ [({a, c}, tgt)])
  | _, cs, tgt => [(cs.toFinset, tgt)]

/-- Base unfolding of `borrowedAndCascade` when the ancillas run out. -/
theorem borrowedAndCascade_nil (cs : List (Fin m)) (tgt : Fin m) :
    borrowedAndCascade [] cs tgt = [(cs.toFinset, tgt)] := rfl

/-- Recursive unfolding of `borrowedAndCascade` (≥ 1 ancilla, ≥ 1 control). -/
theorem borrowedAndCascade_cons (a : Fin m) (as : List (Fin m)) (c : Fin m) (cs : List (Fin m))
    (tgt : Fin m) :
    borrowedAndCascade (a :: as) (c :: cs) tgt
      = ({a, c}, tgt) :: (borrowedAndCascade as cs a ++ [({a, c}, tgt)]) := rfl

/-- Base unfolding of `borrowedAndCascade` when the controls run out (unreached under the length
invariant `|cs| = |as| + 2`). -/
theorem borrowedAndCascade_cons_nil (a : Fin m) (as : List (Fin m)) (tgt : Fin m) :
    borrowedAndCascade (a :: as) [] tgt = [(([] : List (Fin m)).toFinset, tgt)] := rfl

/-- **The cascade is linear.** `borrowedAndCascade as cs tgt` has at most `2 |as| + 1` gates — under
the matching invariant `|cs| = |as| + 2`, exactly `2|cs| - 3`, the linear `O(k)` `Toffoli` count of
Barenco's cascade (contrast the halving `exists_mcNotCircuit`'s `Θ(k²)`). -/
theorem borrowedAndCascade_length_le :
    ∀ (as cs : List (Fin m)) (tgt : Fin m),
      (borrowedAndCascade as cs tgt).length ≤ 2 * as.length + 1
  | [], cs, tgt => by rw [borrowedAndCascade_nil]; simp
  | a :: as, cs, tgt => by
      obtain _ | ⟨c, cs⟩ := cs
      · rw [borrowedAndCascade_cons_nil]; simp only [List.length_singleton]; omega
      · rw [borrowedAndCascade_cons]
        have ih := borrowedAndCascade_length_le as cs a
        simp only [List.length_cons, List.length_append, List.length_nil] at ih ⊢
        omega

/-- **The cascade fixes every non-target, non-ancilla wire.** Every gate's target is `tgt` or one of
the borrowed wires `as`, so a wire `w` outside them passes through unchanged — in particular the
controls and the ambient register are untouched. -/
theorem borrowedAndCascade_apply_of_ne :
    ∀ (as cs : List (Fin m)) (tgt : Fin m) (x : Fin m → Fin 2) {w : Fin m},
      w ≠ tgt → w ∉ as → mcNotDenote (borrowedAndCascade as cs tgt) x w = x w
  | [], cs, tgt, x, w => by
      intro hwt _
      rw [borrowedAndCascade_nil]
      simp only [mcNotDenote_cons, mcNotDenote_nil]
      exact mcNot_apply_of_ne _ _ _ hwt
  | a :: as, cs, tgt, x, w => by
      intro hwt hwas
      obtain _ | ⟨c, cs⟩ := cs
      · rw [borrowedAndCascade_cons_nil]
        simp only [mcNotDenote_cons, mcNotDenote_nil]
        exact mcNot_apply_of_ne _ _ _ hwt
      · have hwa : w ≠ a := fun h => hwas (h ▸ List.mem_cons_self)
        have hwas' : w ∉ as := fun h => hwas (List.mem_cons_of_mem _ h)
        rw [borrowedAndCascade_cons, mcNotDenote_cons, mcNot_apply_of_ne _ _ _ hwt,
          mcNotDenote_append, borrowedAndCascade_apply_of_ne as cs a _ hwa hwas']
        simp only [mcNotDenote_cons, mcNotDenote_nil]
        exact mcNot_apply_of_ne _ _ _ hwt

/-- **The induction-step distinctness bundle for `borrowedAndCascade`.** In the recursive layer —
controls `c :: cs`, ancillas `a :: as` — the recursive call runs on controls `cs`, ancillas `as`,
and target the peeled ancilla `a`. This packages the six invariants that call needs: the matching
length `|cs| = |as| + 2`, both `Nodup`s, disjointness, and the new target `a`'s absence from the
sub-controls and sub-ancillas. -/
theorem borrowedAndCascade_step_hyps {a : Fin m} {as : List (Fin m)} {c : Fin m}
    {cs : List (Fin m)}
    (hlen : (c :: cs).length = (a :: as).length + 2)
    (hcs : (c :: cs).Nodup) (has : (a :: as).Nodup)
    (hdisj : (c :: cs).Disjoint (a :: as)) :
    cs.length = as.length + 2 ∧ cs.Nodup ∧ as.Nodup ∧ cs.Disjoint as ∧ a ∉ cs ∧ a ∉ as := by
  refine ⟨?_, (List.nodup_cons.mp hcs).2, (List.nodup_cons.mp has).2, ?_, ?_,
    (List.nodup_cons.mp has).1⟩
  · simp only [List.length_cons] at hlen ⊢; omega
  · exact fun w hw hwas => hdisj (List.mem_cons_of_mem _ hw) (List.mem_cons_of_mem _ hwas)
  · exact fun h => hdisj (List.mem_cons_of_mem _ h) List.mem_cons_self

/-- **Every cascade gate is a `Toffoli`/`CNOT`/`NOT`** (`≤ 2` controls, target not a control), under
the matching invariant `|cs| = |as| + 2` with all wires distinct. -/
theorem borrowedAndCascade_gate_mem :
    ∀ (as cs : List (Fin m)) (tgt : Fin m), cs.length = as.length + 2 →
      cs.Nodup → as.Nodup → cs.Disjoint as → tgt ∉ cs → tgt ∉ as →
      ∀ g ∈ borrowedAndCascade as cs tgt, g.1.card ≤ 2 ∧ g.2 ∉ g.1
  | [], cs, tgt => by
      intro hlen _ _ _ htcs _ g hg
      rw [borrowedAndCascade_nil] at hg
      simp only [List.mem_singleton] at hg
      obtain rfl := hg
      refine ⟨?_, ?_⟩
      · calc cs.toFinset.card ≤ cs.length := List.toFinset_card_le cs
          _ = 2 := by simp only [List.length_nil] at hlen; omega
      · simpa using htcs
  | a :: as, cs, tgt => by
      intro hlen hcs has hdisj htcs htas
      obtain _ | ⟨c, cs⟩ := cs
      · simp only [List.length_nil, List.length_cons] at hlen; omega
      · rw [borrowedAndCascade_cons]
        have htc : tgt ≠ c := fun h => htcs (h ▸ List.mem_cons_self)
        have hta : tgt ≠ a := fun h => htas (h ▸ List.mem_cons_self)
        have hpeel : (({a, c} : Finset (Fin m))).card ≤ 2 ∧ tgt ∉ ({a, c} : Finset (Fin m)) := by
          refine ⟨Finset.card_insert_le _ _ |>.trans (by simp), ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hta, htc⟩
        obtain ⟨hlen', hcs', has', hdisj', hacs', haas'⟩ :=
          borrowedAndCascade_step_hyps hlen hcs has hdisj
        have ih := borrowedAndCascade_gate_mem as cs a hlen' hcs' has' hdisj' hacs' haas'
        intro g hg
        rcases List.mem_cons.mp hg with hg | hg
        · rw [hg]; exact hpeel
        rcases List.mem_append.mp hg with hg | hg
        · exact ih g hg
        · rw [List.mem_singleton.mp hg]; exact hpeel

/-- **N&C Exercise 4.29 / Barenco Lemma 7.2 — the cascade flips the target by the exact control AND,
independently of the dirty borrowed wires.** With `|cs|` controls, `|cs| - 2` **arbitrary** (dirty)
borrowed ancillas `as`, and every wire distinct, `borrowedAndCascade as cs tgt` acts on the target
`tgt` exactly as `mcNot cs.toFinset tgt` — it adds the true control bit `ctrlBit cs.toFinset x`,
with **no** dependence on the ancillas' initial values.

Proved by structural induction on `as`. In the recursive layer the two copies of the `Toffoli`
`({a, c}, tgt)` sandwich the sub-cascade that flips `a` by `⋀ cs`; the target is flipped by
`x a · x c` first and by `(x a ⊕ ⋀cs) · x c` second, and in `Fin 2` the dirty `x a` cancels, leaving
`⋀cs · x c = ⋀(c :: cs)` — Barenco's borrowed-wire group-commutator cancellation. -/
theorem borrowedAndCascade_apply_tgt :
    ∀ (as cs : List (Fin m)) (tgt : Fin m),
      cs.length = as.length + 2 → cs.Nodup → as.Nodup → cs.Disjoint as →
      tgt ∉ cs → tgt ∉ as → ∀ x : Fin m → Fin 2,
      mcNotDenote (borrowedAndCascade as cs tgt) x tgt = x tgt + ctrlBit cs.toFinset x
  | [], cs, tgt => by
      intro _ _ _ _ _ _ x
      rw [borrowedAndCascade_nil]
      simp only [mcNotDenote_cons, mcNotDenote_nil, mcNot_apply_self]
  | a :: as, cs, tgt => by
      intro hlen hcs has hdisj htcs htas x
      obtain _ | ⟨c, cs⟩ := cs
      · simp only [List.length_nil, List.length_cons] at hlen; omega
      · -- A decidable `Fin 2` identity: the dirty `x a` cancels between the two target flips.
        have master : ∀ w α p g : Fin 2,
            (w + (if α = 1 ∧ p = 1 then (1 : Fin 2) else 0))
              + (if (α + g) = 1 ∧ p = 1 then (1 : Fin 2) else 0)
              = w + (if p = 1 ∧ g = 1 then (1 : Fin 2) else 0) := by decide
        rw [borrowedAndCascade_cons]
        -- Distinctness facts.
        have htc : tgt ≠ c := fun h => htcs (h ▸ List.mem_cons_self)
        have htcs' : tgt ∉ cs := fun h => htcs (List.mem_cons_of_mem _ h)
        have hta : tgt ≠ a := fun h => htas (h ▸ List.mem_cons_self)
        have htas' : tgt ∉ as := fun h => htas (List.mem_cons_of_mem _ h)
        have hca : c ≠ a := by rintro rfl; exact hdisj List.mem_cons_self List.mem_cons_self
        have hcas : c ∉ as := fun h =>
          hdisj List.mem_cons_self (List.mem_cons_of_mem _ h)
        obtain ⟨hlen', hcs', has', hdisj', hacs', haas'⟩ :=
          borrowedAndCascade_step_hyps hlen hcs has hdisj
        -- Unfold to the sub-cascade acting on the state after the tail `Toffoli`.
        rw [mcNotDenote_cons, mcNotDenote_append]
        simp only [mcNotDenote_cons, mcNotDenote_nil]
        set x' := mcNot ({a, c} : Finset (Fin m)) tgt x with hx'
        set y := mcNotDenote (borrowedAndCascade as cs a) x' with hy
        -- The head `Toffoli` reads `y a`, `y c`; and `y tgt` after the sandwich.
        have hx'cs : ctrlBit cs.toFinset x' = ctrlBit cs.toFinset x := by
          rw [hx', mcNot]
          exact ctrlBit_update_of_notMem cs.toFinset (by rwa [List.mem_toFinset]) x _
        have hya : y a = x a + ctrlBit cs.toFinset x := by
          rw [hy, borrowedAndCascade_apply_tgt as cs a hlen' hcs' has' hdisj' hacs' haas' x',
            hx', mcNot_apply_of_ne _ _ _ (Ne.symm hta), ← hx', hx'cs]
        have hyc : y c = x c := by
          rw [hy, borrowedAndCascade_apply_of_ne as cs a x' hca hcas, hx',
            mcNot_apply_of_ne _ _ _ (Ne.symm htc)]
        have hytgt : y tgt = x tgt + ctrlBit ({a, c} : Finset (Fin m)) x := by
          rw [hy, borrowedAndCascade_apply_of_ne as cs a x' hta htas', hx', mcNot_apply_self]
        rw [mcNot_apply_self, hytgt, ctrlBit_pair a c y, hya, hyc, ctrlBit_pair a c x,
          ctrlBit_cons_toFinset]
        exact master (x tgt) (x a) (x c) (ctrlBit cs.toFinset x)

/-- **The cascade is an involution.** Applying `borrowedAndCascade as cs tgt` twice restores the
bit-string: every wire is flipped by a control AND independent of that wire's own value, so the
flips cancel. Proved by induction — the two outer `Toffoli`s and the sub-cascade each cancel with
their copy. This is what the follow-on dirty `Cᵏ(X)` assembly consumes to restore the borrowed wires
(running the cascade twice). -/
theorem borrowedAndCascade_involutive :
    ∀ (as cs : List (Fin m)) (tgt : Fin m),
      cs.length = as.length + 2 → cs.Nodup → as.Nodup → cs.Disjoint as →
      tgt ∉ cs → tgt ∉ as → ∀ x : Fin m → Fin 2,
      mcNotDenote (borrowedAndCascade as cs tgt) (mcNotDenote (borrowedAndCascade as cs tgt) x) = x
  | [], cs, tgt => by
      intro _ _ _ _ htcs _ x
      rw [borrowedAndCascade_nil]
      simp only [mcNotDenote_cons, mcNotDenote_nil]
      exact mcNot_involutive cs.toFinset (by rwa [List.mem_toFinset]) x
  | a :: as, cs, tgt => by
      intro hlen hcs has hdisj htcs htas x
      obtain _ | ⟨c, cs⟩ := cs
      · simp only [List.length_nil, List.length_cons] at hlen; omega
      · rw [borrowedAndCascade_cons]
        have htc : tgt ≠ c := fun h => htcs (h ▸ List.mem_cons_self)
        have hta : tgt ≠ a := fun h => htas (h ▸ List.mem_cons_self)
        have htac : tgt ∉ ({a, c} : Finset (Fin m)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hta, htc⟩
        obtain ⟨hlen', hcs', has', hdisj', hacs', haas'⟩ :=
          borrowedAndCascade_step_hyps hlen hcs has hdisj
        have ih := borrowedAndCascade_involutive as cs a hlen' hcs' has' hdisj' hacs' haas'
        simp only [mcNotDenote_cons, mcNotDenote_append, mcNotDenote_nil]
        rw [mcNot_involutive ({a, c} : Finset (Fin m)) htac
            (mcNotDenote (borrowedAndCascade as cs a) (mcNot ({a, c} : Finset (Fin m)) tgt x)),
          ih (mcNot ({a, c} : Finset (Fin m)) tgt x),
          mcNot_involutive ({a, c} : Finset (Fin m)) htac x]

end AxQM.Concrete
