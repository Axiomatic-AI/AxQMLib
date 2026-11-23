/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNotCircuit

/-!
# Concrete: the clean-ancilla linear staircase for `Cⁿ(X)` (N&C Figure 4.10)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for an `O(n²)` no-work-qubit circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing the `n`-controlled `NOT` `Cⁿ(X)`. The file
`Concrete/MultiControlledNotCircuit.lean` builds *a* circuit — the **halving** dirty-borrow
recursion `exists_mcNotCircuit` — but its gate count is the balanced-doubling recurrence
`mcNotGateBound`, which is `Θ(k²)` **per block**. Substituted into the `n+1`-wire `barencoNCircuit`
(`O(n)` blocks `Cᵏ(X)`, `k ≤ n`), that sums to `Θ(n³)`, missing the exercise's `O(n²)`.
Barenco's genuine `O(n²)` needs each block bottomed in a
**linear** `O(k)` number of `Toffoli`s — the *conditioning cascade* of Barenco *Elementary gates*,
Lemma 7.2 — using the idle wires of the register as borrowed ancillas.

This file lays the foundation of that linear cascade: the **clean-ancilla staircase** — Nielsen &
Chuang's own Figure 4.10 construction, read as a reversible bit-string circuit. Given `k` control
wires `cs`, a target `t`, and `k - 2` **clean** (initialised to `0`) borrowed ancilla wires `as`,
the staircase

* peels the first two controls `c₀, c₁` into the first ancilla `a` with a `Toffoli` (`a ← c₀ ∧ c₁`,
  clean so exact), recurses treating `a` as the new leading control on `k - 1` controls, and
  **uncomputes** `a` with a second identical `Toffoli` restoring it to `0`;
* bottoms out at two controls — a single `Toffoli` `(cs.toFinset, t)`.

Unfolded, its `Toffoli` count is `2(k - 2) + 1 = 2k - 3` — **linear** (`andStaircase_length_le`) —
and every gate has `≤ 2` controls (`andStaircase_gate_mem`). On a clean-ancilla input it computes
exactly `mcNot cs.toFinset t = C^k(X)` (`mcNotDenote_andStaircase`).

The `k - 2` ancillas start (and end) at `0`, i.e. this is Figure 4.10's work-qubit staircase. It is
therefore **not yet** the no-work-qubit answer: the exercise forbids clean work qubits, so the
ancillas must be **dirty** wires borrowed from the register in an arbitrary state and restored
(Barenco Lemma 7.2's group-commutator wrapper: run the compute/uncompute sweep twice to cancel the
dirty initial values). That dirty wrapper — and the wire-budget bookkeeping placing it inside
`barencoNCircuit`'s blocks — are in `AxQM/Concrete/MultiControlledNotDirtyCascade.lean` and
`AxQM/Concrete/MultiControlledNotBorrowedMcNot.lean`; this file is the clean core they build on.

Everything here is `Fin 2`/`Finset`/`List` combinatorics. Compare `MultiControlledNot` and
`MultiControlledNotCircuit`.
-/

namespace AxQM.Concrete

variable {m : ℕ}

/-! ### The one-step clean-ancilla reduction -/

/-- **One clean-ancilla staircase step.** Let `a` be a borrowed wire in the clean state `x a = 0`,
disjoint from the two peeled controls `c₀, c₁`, the target `t`, and the remaining control set `S`
(`a ∉ S`), with `c₀, c₁ ≠ t`. Then fusing `c₀, c₁` into `a`, applying the `(1 + |S|)`-controlled
`NOT` with `a` as leading control, and unfusing `a` implements the `(2 + |S|)`-controlled `NOT`:

`mcNot {c₀, c₁} a (mcNot (insert a S) t (mcNot {c₀, c₁} a x)) = mcNot (insert c₀ (insert c₁ S)) t x`

on the clean input `x` (composition reads right to left). The borrowed wire `a` is set to `c₀ ∧ c₁`
by the first fuse, so the middle gate flips `t` iff `c₀ ∧ c₁ ∧ (⋀ S)` — every original control — and
the final fuse restores `a` to `0`. Unlike the dirty `mcNot_union_borrow` (four sub-gates, two
target-flips), the clean version uses **three** sub-gates — one target-flip. -/
theorem mcNot_clean_borrow_step {c₀ c₁ a t : Fin m} (S : Finset (Fin m)) (x : Fin m → Fin 2)
    (hxa : x a = 0) (hac₀ : a ≠ c₀) (hac₁ : a ≠ c₁) (hat : a ≠ t)
    (hc₀t : c₀ ≠ t) (hc₁t : c₁ ≠ t) (haS : a ∉ S) :
    mcNot {c₀, c₁} a (mcNot (insert a S) t (mcNot {c₀, c₁} a x))
      = mcNot (insert c₀ (insert c₁ S)) t x := by
  have htpair : t ∉ ({c₀, c₁} : Finset (Fin m)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hc₀t h.symm, fun h => hc₁t h.symm⟩
  have hapair : a ∉ ({c₀, c₁} : Finset (Fin m)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hac₀, hac₁⟩
  have hadd : ∀ c : Fin 2, c + c = 0 := by decide
  have hzero : ∀ c : Fin 2, (0 : Fin 2) + c = c := by decide
  set y := mcNot {c₀, c₁} a x with hy
  set z := mcNot (insert a S) t y with hz
  -- The pair control bit `γ = c₀ ∧ c₁`, and its boolean reading.
  have hγeq : ctrlBit {c₀, c₁} x = 1 ↔ (x c₀ = 1 ∧ x c₁ = 1) := by
    rw [ctrlBit_insert]
    simp only [Finset.mem_singleton, forall_eq]
    by_cases h : x c₀ = 1 ∧ x c₁ = 1 <;> simp [h]
  have hyc : ctrlBit {c₀, c₁} y = ctrlBit {c₀, c₁} x := by
    rw [hy]; exact ctrlBit_update_of_notMem _ hapair x _
  have hzc : ctrlBit {c₀, c₁} z = ctrlBit {c₀, c₁} x := by
    rw [hz, mcNot, ctrlBit_update_of_notMem _ htpair, hyc]
  have hya : y a = ctrlBit {c₀, c₁} x := by rw [hy, mcNot_apply_self, hxa]; exact hzero _
  -- The middle gate reads `a` (= γ) and `S` (agrees with `x`).
  have hctrl : ctrlBit (insert a S) y
      = if ctrlBit {c₀, c₁} x = 1 ∧ ∀ i ∈ S, x i = 1 then (1 : Fin 2) else 0 := by
    rw [ctrlBit_insert, hya]
    refine if_congr (and_congr_right fun _ => ?_) rfl rfl
    exact forall_mem_eq_one_congr fun i hi => mcNot_apply_of_ne _ _ _ (by rintro rfl; exact haS hi)
  have hzt : z t
      = x t + if ctrlBit {c₀, c₁} x = 1 ∧ ∀ i ∈ S, x i = 1 then (1 : Fin 2) else 0 := by
    rw [hz, mcNot_apply_self, hctrl, hy, mcNot_apply_of_ne _ _ _ (Ne.symm hat)]
  -- The full control bit of the reduced gate, in the same boolean form.
  have hbig : ctrlBit (insert c₀ (insert c₁ S)) x
      = if ctrlBit {c₀, c₁} x = 1 ∧ ∀ i ∈ S, x i = 1 then (1 : Fin 2) else 0 := by
    rw [ctrlBit]
    refine if_congr ?_ rfl rfl
    rw [Finset.forall_mem_insert, Finset.forall_mem_insert, hγeq]
    tauto
  funext j
  by_cases hjt : j = t
  · -- Target wire: one flip iff every original control is set.
    subst hjt
    rw [mcNot_apply_of_ne _ _ _ (Ne.symm hat), hzt, mcNot_apply_self, hbig]
  · by_cases hja : j = a
    · -- Borrowed wire restored to `x a = 0`.
      subst hja
      have hR : mcNot (insert c₀ (insert c₁ S)) t x j = 0 := by
        rw [mcNot_apply_of_ne _ _ _ hat, hxa]
      have hL : mcNot {c₀, c₁} j z j = ctrlBit {c₀, c₁} x + ctrlBit {c₀, c₁} x := by
        rw [mcNot_apply_self, hzc, hz, mcNot_apply_of_ne _ _ _ hat, hya]
      rw [hL, hR, hadd]
    · -- Any other wire: passes through unchanged.
      have hR : mcNot (insert c₀ (insert c₁ S)) t x j = x j := mcNot_apply_of_ne _ _ _ hjt
      have hL : mcNot {c₀, c₁} a z j = x j := by
        rw [mcNot_apply_of_ne _ _ _ hja, hz, mcNot_apply_of_ne _ _ _ hjt, hy,
          mcNot_apply_of_ne _ _ _ hja]
      rw [hL, hR]

/-! ### The staircase circuit -/

/-- **The clean-ancilla staircase circuit for `Cⁿ(X)` (N&C Figure 4.10).** Given control wires `as`
of borrowed ancillas, control wires `cs`, and target `t`, `andStaircase as cs t` peels the first two
controls of `cs` into the first ancilla of `as` (a `Toffoli`), recurses with that ancilla as the new
leading control, and unfuses it — bottoming out (when `< 3` controls remain, or the ancillas run
out) at a single `≤ 2`-control gate `(cs.toFinset, t)`. With `as` of length `|cs| - 2` all clean
(`= 0`), it computes `mcNot cs.toFinset t` (`mcNotDenote_andStaircase`) in `2|cs| - 3` gates. -/
def andStaircase : List (Fin m) → List (Fin m) → Fin m → List (McNotGate m)
  | a :: as, c₀ :: c₁ :: _c₂ :: cs, t =>
      ({c₀, c₁}, a) :: (andStaircase as (a :: _c₂ :: cs) t ++ [({c₀, c₁}, a)])
  | _, cs, t => [(cs.toFinset, t)]

/-- Base unfolding of `andStaircase` when the ancillas run out. -/
theorem andStaircase_nil (cs : List (Fin m)) (t : Fin m) :
    andStaircase [] cs t = [(cs.toFinset, t)] := rfl

/-- Recursive unfolding of `andStaircase` (≥ 3 controls, ≥ 1 ancilla). -/
theorem andStaircase_cons (a : Fin m) (as : List (Fin m)) (c₀ c₁ c₂ : Fin m) (cs : List (Fin m))
    (t : Fin m) :
    andStaircase (a :: as) (c₀ :: c₁ :: c₂ :: cs) t
      = ({c₀, c₁}, a) :: (andStaircase as (a :: c₂ :: cs) t ++ [({c₀, c₁}, a)]) := rfl

/-- Base unfolding of `andStaircase` when `< 3` controls remain. -/
theorem andStaircase_cons_short (a : Fin m) (as : List (Fin m)) (cs : List (Fin m)) (t : Fin m)
    (h : cs.length ≤ 2) : andStaircase (a :: as) cs t = [(cs.toFinset, t)] := by
  obtain _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ := cs
  · rfl
  · rfl
  · rfl
  · simp only [List.length_cons] at h; omega

/-- **The staircase is linear.** `andStaircase as cs t` has at most `2 |as| + 1` gates — under the
matching invariant `|cs| = |as| + 2` this is `2|cs| - 3`, the linear `O(k)` `Toffoli` count of
Figure 4.10 (contrast the halving `exists_mcNotCircuit`'s `Θ(k²)`). -/
theorem andStaircase_length_le :
    ∀ (as cs : List (Fin m)) (t : Fin m), (andStaircase as cs t).length ≤ 2 * as.length + 1
  | [], cs, t => by rw [andStaircase_nil]; simp
  | a :: as, cs, t => by
      obtain _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ := cs
      · rw [andStaircase_cons_short _ _ _ _ (by simp)]
        simp only [List.length_cons, List.length_nil]; omega
      · rw [andStaircase_cons_short _ _ _ _ (by simp)]
        simp only [List.length_cons, List.length_nil]; omega
      · rw [andStaircase_cons_short _ _ _ _ (by simp)]
        simp only [List.length_cons, List.length_nil]; omega
      · rw [andStaircase_cons]
        have ih := andStaircase_length_le as (a :: c₂ :: cs) t
        simp only [List.length_cons, List.length_append, List.length_nil] at ih ⊢
        omega

/-- **The induction-step distinctness bundle for `andStaircase`.** In the recursive layer of a
staircase — controls `c₀ :: c₁ :: c₂ :: cs`, ancillas `a :: as` — the recursive call runs on
controls `a :: c₂ :: cs` (the peeled ancilla `a` promoted to leading control) and ancillas `as`.
This packages, derived once from the layer's hypotheses, the six invariants that recursive call
needs: the matching length `|cs'| = |as'| + 2`, both `Nodup`s, disjointness, and the target's
absence from both lists. Reused by `andStaircase_gate_mem` and `mcNotDenote_andStaircase` (and by
the dirty-ancilla cascades). -/
theorem andStaircase_step_hyps {a : Fin m} {as : List (Fin m)} {c₀ c₁ c₂ : Fin m}
    {cs : List (Fin m)} {t : Fin m}
    (hlen : (c₀ :: c₁ :: c₂ :: cs).length = (a :: as).length + 2)
    (hcs : (c₀ :: c₁ :: c₂ :: cs).Nodup) (has : (a :: as).Nodup)
    (hdisj : (c₀ :: c₁ :: c₂ :: cs).Disjoint (a :: as))
    (htcs : t ∉ (c₀ :: c₁ :: c₂ :: cs)) (htas : t ∉ (a :: as)) :
    (a :: c₂ :: cs).length = as.length + 2 ∧ (a :: c₂ :: cs).Nodup ∧ as.Nodup ∧
      (a :: c₂ :: cs).Disjoint as ∧ t ∉ (a :: c₂ :: cs) ∧ t ∉ as := by
  have hmem_a : a ∈ a :: as := List.mem_cons_self
  have ha_notin : a ∉ (c₂ :: cs) := fun h =>
    hdisj (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) hmem_a
  have hcs_tail : (c₂ :: cs).Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hcs).2).2
  refine ⟨?_, List.nodup_cons.mpr ⟨ha_notin, hcs_tail⟩, (List.nodup_cons.mp has).2, ?_, ?_,
    fun h => htas (List.mem_cons_of_mem _ h)⟩
  · simp only [List.length_cons] at hlen ⊢; omega
  · intro w hw hwas
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact (List.nodup_cons.mp has).1 hwas
    · exact hdisj (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw'))
        (List.mem_cons_of_mem _ hwas)
  · simp only [List.mem_cons, not_or]
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl; exact htas hmem_a
    · rintro rfl
      exact htcs (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · intro h
      exact htcs (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))

/-- **Every staircase gate is a `Toffoli`/`CNOT`/`NOT`** (`≤ 2` controls, target not a control),
under the matching invariant `|cs| = |as| + 2` with all wires distinct. -/
theorem andStaircase_gate_mem :
    ∀ (as cs : List (Fin m)) (t : Fin m), cs.length = as.length + 2 →
      cs.Nodup → as.Nodup → cs.Disjoint as → t ∉ cs → t ∉ as →
      ∀ g ∈ andStaircase as cs t, g.1.card ≤ 2 ∧ g.2 ∉ g.1
  | [], cs, t => by
      intro hlen _ _ _ htcs _ g hg
      rw [andStaircase_nil] at hg
      simp only [List.mem_singleton] at hg
      obtain rfl := hg
      refine ⟨?_, ?_⟩
      · calc cs.toFinset.card ≤ cs.length := List.toFinset_card_le cs
          _ = 2 := by simp only [List.length_nil] at hlen; omega
      · simpa using htcs
  | a :: as, cs, t => by
      intro hlen hcs has hdisj htcs htas
      obtain _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ := cs
      · simp only [List.length_nil, List.length_cons] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · -- Recursive layer: the two peel gates plus the recursive gates.
        rw [andStaircase_cons]
        -- Membership facts derived from the distinctness hypotheses.
        have hmem_a : a ∈ a :: as := List.mem_cons_self
        have hac₀ : a ≠ c₀ := fun h => hdisj (List.mem_cons_self) (h ▸ hmem_a)
        have hac₁ : a ≠ c₁ := fun h =>
          hdisj (List.mem_cons_of_mem _ (List.mem_cons_self)) (h ▸ hmem_a)
        have hpeel : (({c₀, c₁} : Finset (Fin m))).card ≤ 2 ∧ a ∉ ({c₀, c₁} : Finset (Fin m)) := by
          refine ⟨Finset.card_insert_le _ _ |>.trans (by simp), ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hac₀, hac₁⟩
        -- Hypotheses for the recursive call on controls `a :: c₂ :: cs`, ancillas `as`.
        obtain ⟨hlen', hcs', has', hdisj', htcs', htas'⟩ :=
          andStaircase_step_hyps hlen hcs has hdisj htcs htas
        have ih := andStaircase_gate_mem as (a :: c₂ :: cs) t hlen' hcs' has' hdisj' htcs' htas'
        intro g hg
        rcases List.mem_cons.mp hg with hg | hg
        · rw [hg]; exact hpeel
        rcases List.mem_append.mp hg with hg | hg
        · exact ih g hg
        · rw [List.mem_singleton.mp hg]; exact hpeel

/-- **N&C Exercise 4.29 / Figure 4.10 — the clean-ancilla staircase computes `Cⁿ(X)`.** With `|cs|`
controls, `|cs| - 2` clean (all `0`) borrowed ancillas `as`, and every wire distinct, the staircase
`andStaircase as cs t` acts on the bit-string `x` exactly as the multiply-controlled `NOT`
`mcNot cs.toFinset t` — the classical `C^{|cs|}(X)` with controls `cs` and target `t`.

Proved by structural induction on the ancilla list `as`, iterating `mcNot_clean_borrow_step`: each
layer fuses two controls into a clean ancilla (still clean, the fuse touches only that ancilla),
recurses on one fewer control, and unfuses. -/
theorem mcNotDenote_andStaircase :
    ∀ (as cs : List (Fin m)) (t : Fin m), cs.length = as.length + 2 →
      cs.Nodup → as.Nodup → cs.Disjoint as → t ∉ cs → t ∉ as →
      ∀ x : Fin m → Fin 2, (∀ a ∈ as, x a = 0) →
      mcNotDenote (andStaircase as cs t) x = mcNot cs.toFinset t x
  | [], cs, t => by
      intro hlen _ _ _ _ _ x _
      rw [andStaircase_nil]
      simp [mcNotDenote]
  | a :: as, cs, t => by
      intro hlen hcs has hdisj htcs htas x hclean
      obtain _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ := cs
      · simp only [List.length_nil, List.length_cons] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · rw [andStaircase_cons]
        -- Distinctness / membership facts.
        have hmem_a : a ∈ a :: as := List.mem_cons_self
        have hac₀ : a ≠ c₀ := fun h => hdisj (List.mem_cons_self) (h ▸ hmem_a)
        have hac₁ : a ≠ c₁ := fun h =>
          hdisj (List.mem_cons_of_mem _ (List.mem_cons_self)) (h ▸ hmem_a)
        have hat : a ≠ t := fun h => htas (h ▸ hmem_a)
        have hc₀t : c₀ ≠ t := fun h => htcs (h ▸ List.mem_cons_self)
        have hc₁t : c₁ ≠ t := fun h => htcs (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self))
        have ha_notin : a ∉ (c₂ :: cs) := fun h =>
          hdisj (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) hmem_a
        have haS : a ∉ (c₂ :: cs).toFinset := by
          rw [List.mem_toFinset]; exact ha_notin
        -- Recursive hypotheses (shared induction-step bundle).
        obtain ⟨hlen', hcs', has', hdisj', htcs', htas'⟩ :=
          andStaircase_step_hyps hlen hcs has hdisj htcs htas
        have hxa : x a = 0 := hclean a hmem_a
        -- The cleaned input after the first fuse: `x` with `a ↦ c₀ ∧ c₁`; still clean on `as`.
        have hclean' : ∀ w ∈ as, mcNot ({c₀, c₁} : Finset (Fin m)) a x w = 0 := by
          intro w hw
          have hwa : w ≠ a := fun h => (List.nodup_cons.mp has).1 (h ▸ hw)
          rw [mcNot_apply_of_ne _ _ _ hwa]
          exact hclean w (List.mem_cons_of_mem _ hw)
        have ih := mcNotDenote_andStaircase as (a :: c₂ :: cs) t hlen' hcs' has' hdisj' htcs' htas'
          (mcNot ({c₀, c₁} : Finset (Fin m)) a x) hclean'
        -- Register-cast identities for the two control sets.
        have hS : (a :: c₂ :: cs).toFinset = insert a (c₂ :: cs).toFinset := List.toFinset_cons
        have hCS : (c₀ :: c₁ :: c₂ :: cs).toFinset
            = insert c₀ (insert c₁ (c₂ :: cs).toFinset) := by
          rw [List.toFinset_cons, List.toFinset_cons]
        -- Assemble: [peel] ++ rec ++ [peel]; then apply the one-step reduction.
        simp only [mcNotDenote_cons, mcNotDenote_append, mcNotDenote_nil]
        rw [ih, hS, mcNot_clean_borrow_step (c₂ :: cs).toFinset x hxa hac₀ hac₁ hat hc₀t hc₁t haS,
          hCS]

end AxQM.Concrete
