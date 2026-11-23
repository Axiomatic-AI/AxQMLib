/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Concrete: the multiply-controlled NOT as a reversible bit-string permutation (N&C §4.3)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a circuit of `O(n²)` Toffoli, `CNOT` and
single-qubit gates that implements a `Cⁿ(X)` gate — the `n`-controlled `NOT` — **using no work
qubits** (the whole register is the `n` controls and the one target, `n + 1` qubits).

Every gate in such a circuit (`X`, `CNOT`, Toffoli, and any multiply-controlled `NOT`) is a
*permutation of the computational basis*, so the entire construction — its correctness **and** its
gate count — is a statement about reversible classical circuits on bit-strings, decidable
`Fin 2`/`Finset` combinatorics. This file sets up that classical model: bit-strings `Fin m → Fin 2`
and the **multiply-controlled `NOT`** `mcNot S t`, which flips wire `t` exactly when every control
wire in the finite set `S` is set. It is an involution, hence a permutation (`mcNotPerm`).

The mathematical heart of the `O(n²)` no-work-qubit construction is the **dirty borrowed-wire
reduction** `mcNot_union_borrow`: for disjoint control sets `A`, `B`, a target `t`, and *any* wire
`a` outside the gate's support, splitting the controls as `A ∪ B` and using `a` as a **borrowed**
work wire,
`mcNot (A ∪ B) t = mcNot (insert a B) t ∘ mcNot A a ∘ mcNot (insert a B) t ∘ mcNot A a`,
and — crucially — `a` starts in an *arbitrary* ("dirty") state yet is restored, so no clean work
qubit is needed. The middle wire `a` is toggled by the two `mcNot A a` iff every control in `A` is
set; the two `mcNot (insert a B) t` flip `t` iff every control in `B` **and** `a` are set, and the
even number of `a`-toggles between them makes the net effect flip `t` iff every control in
`A ∪ B` is set (a group-commutator / parity cancellation). Iterating this reduction with
`|A|, |B| ≈ n/2` bottoms out in Toffoli/`CNOT` gates and yields the `O(n²)` gate count of the
exercise (the recursion `T(n) = 2T(⌈n/2⌉) + 2T(⌊n/2⌋+1)` is `Θ(n²)`).

This is pure combinatorics. Each `mcNot` gate is realised as a genuine `Evolution` (a
Toffoli/`CNOT`/single-qubit gate placed on the register), and the whole circuit as
`mcCtrl n pauliXGate`, in `AxQM/NC/Ch4/Exercise4_29.lean`.
-/

namespace AxQM.Concrete

variable {m : ℕ}

/-- A `Fin 2` bit added to itself cancels: `b + c + c = b` (the target wire, flipped by the same
control bit an even number of times, is restored). -/
theorem add_add_self_right (b c : Fin 2) : b + c + c = b := by revert b c; decide

/-- Bit-strings agreeing on every wire of `B` satisfy the "all controls set" predicate together. -/
theorem forall_mem_eq_one_congr {B : Finset (Fin m)} {x y : Fin m → Fin 2}
    (h : ∀ i ∈ B, x i = y i) : (∀ i ∈ B, x i = 1) ↔ (∀ i ∈ B, y i = 1) :=
  ⟨fun H i hi => h i hi ▸ H i hi, fun H i hi => (h i hi).symm ▸ H i hi⟩

/-- **The control bit of a multiply-controlled `NOT`**: `1` when every control wire in the finite
set `S` is set to `1` in the bit-string `x`, and `0` otherwise. This is the amount by which the
target wire is flipped. -/
def ctrlBit (S : Finset (Fin m)) (x : Fin m → Fin 2) : Fin 2 :=
  if ∀ i ∈ S, x i = 1 then 1 else 0

/-- **The classical multiply-controlled `NOT`** `mcNot S t`: the reversible map on bit-strings
`Fin m → Fin 2` that adds the control bit `ctrlBit S x` (XOR, since we are in `Fin 2`) to wire `t`,
leaving every other wire unchanged. For `|S| = 0, 1, 2` this is the `NOT`, `CNOT`, Toffoli gate
respectively; in general it is the classical `C^{|S|}(X)` gate with controls `S` and target `t`. -/
def mcNot (S : Finset (Fin m)) (t : Fin m) (x : Fin m → Fin 2) : Fin m → Fin 2 :=
  Function.update x t (x t + ctrlBit S x)

/-! ### Pointwise behaviour -/

/-- The value of `mcNot S t x` on the target wire `t` is `x t` flipped by the control bit. -/
@[simp] theorem mcNot_apply_self (S : Finset (Fin m)) (t : Fin m) (x : Fin m → Fin 2) :
    mcNot S t x t = x t + ctrlBit S x := by
  simp [mcNot]

/-- The value of `mcNot S t x` on any wire other than the target `t` is unchanged. -/
theorem mcNot_apply_of_ne (S : Finset (Fin m)) (t : Fin m) (x : Fin m → Fin 2) {j : Fin m}
    (h : j ≠ t) : mcNot S t x j = x j := by
  simp only [mcNot, Function.update_of_ne h]

/-- When no control condition is met (`ctrlBit S x = 0`), `mcNot S t` fixes the bit-string. -/
theorem mcNot_of_ctrlBit_eq_zero (S : Finset (Fin m)) (t : Fin m) (x : Fin m → Fin 2)
    (h : ctrlBit S x = 0) : mcNot S t x = x := by
  rw [mcNot, h]; simp

/-- `ctrlBit S` only reads the wires in `S`, so updating a wire outside `S` leaves it unchanged. -/
theorem ctrlBit_update_of_notMem (S : Finset (Fin m)) {j : Fin m} (hj : j ∉ S)
    (x : Fin m → Fin 2) (v : Fin 2) :
    ctrlBit S (Function.update x j v) = ctrlBit S x := by
  simp only [ctrlBit, forall_mem_eq_one_congr
    fun i hi => Function.update_of_ne (fun (h : i = j) => hj (h ▸ hi)) v x]

/-- `ctrlBit` of an `insert`: every control in `insert a B` is set iff `a` is set and every control
in `B` is set. -/
theorem ctrlBit_insert (a : Fin m) (B : Finset (Fin m)) (x : Fin m → Fin 2) :
    ctrlBit (insert a B) x = if x a = 1 ∧ ∀ i ∈ B, x i = 1 then 1 else 0 := by
  simp only [ctrlBit, Finset.forall_mem_insert]

/-- `ctrlBit` of a `union`: every control in `A ∪ B` is set iff every control in `A` is set and
every control in `B` is set. -/
theorem ctrlBit_union (A B : Finset (Fin m)) (x : Fin m → Fin 2) :
    ctrlBit (A ∪ B) x = if (∀ i ∈ A, x i = 1) ∧ ∀ i ∈ B, x i = 1 then 1 else 0 := by
  simp only [ctrlBit, Finset.forall_mem_union]

/-- `ctrlBit` under a `Finset.image`: the control bit of the relabelled control set `S.image f`
read on `x` equals the control bit of `S` read on the pulled-back bit-string `x ∘ f`. (Used to
transport a placed multiply-controlled gate's control condition back through the wire relabelling.)
No injectivity of `f` is needed: `∀ y ∈ S.image f, x y = 1 ↔ ∀ i ∈ S, x (f i) = 1`. -/
theorem ctrlBit_image {n : ℕ} (S : Finset (Fin m)) (f : Fin m → Fin n) (x : Fin n → Fin 2) :
    ctrlBit (S.image f) x = ctrlBit S (fun i => x (f i)) := by
  simp only [ctrlBit, Finset.forall_mem_image]

/-- The multiply-controlled `NOT` control bit of a **single** control wire `a` is just that wire's
value: `ctrlBit {a} c = c a` (the `CNOT` control bit). -/
theorem ctrlBit_singleton (a : Fin m) (c : Fin m → Fin 2) : ctrlBit {a} c = c a := by
  unfold ctrlBit
  simp only [Finset.mem_singleton, forall_eq]
  generalize c a = b
  revert b
  decide

/-! ### Reversibility -/

/-- **`mcNot S t` is an involution** when the target `t` is not one of the controls: applying it
twice restores the bit-string, because the target is flipped by the same control bit twice
(`c + c = 0` in `Fin 2`) and the flip does not affect the control wires. -/
theorem mcNot_involutive (S : Finset (Fin m)) {t : Fin m} (ht : t ∉ S) :
    Function.Involutive (mcNot S t) := by
  intro x
  have hc : ctrlBit S (mcNot S t x) = ctrlBit S x :=
    ctrlBit_update_of_notMem S ht x _
  funext j
  by_cases hj : j = t
  · subst hj
    rw [mcNot_apply_self, hc, mcNot_apply_self]
    exact add_add_self_right _ _
  · rw [mcNot_apply_of_ne _ _ _ hj, mcNot_apply_of_ne _ _ _ hj]

/-- **The multiply-controlled `NOT` as a permutation** of the computational basis (when the target
is not a control): the reversible-gate incarnation, ready to be realised as a unitary. -/
def mcNotPerm (S : Finset (Fin m)) {t : Fin m} (ht : t ∉ S) : Equiv.Perm (Fin m → Fin 2) :=
  (mcNot_involutive S ht).toPerm _

@[simp] theorem mcNotPerm_apply (S : Finset (Fin m)) {t : Fin m} (ht : t ∉ S) (x : Fin m → Fin 2) :
    mcNotPerm S ht x = mcNot S t x := rfl

/-! ### Naturality under wire relabelling -/

/-- **`mcNot` is natural under a bijective relabelling of the wires.** Relabelling the wires by an
equivalence `σ : Fin m ≃ Fin p` — sending the control set `S` to `S.map σ.toEmbedding` and the
target `t` to `σ t` — turns the gate `mcNot S t` into `mcNot (S.map σ.toEmbedding) (σ t)`, read on
the relabelled bit-string: `mcNot (S.map σ.toEmbedding) (σ t) x j = mcNot S t (x ∘ σ) (σ.symm j)`.
The control condition transports because `ctrlBit` of a `Finset.map` is `ctrlBit` of the pulled-back
bit-string (`ctrlBit_image`, no injectivity needed); the target flip transports because
`σ.symm j = t ↔ j = σ t`. This is the equivariance a **register cast** uses to place a
wire-addressed `mcNot` gate on a propositionally-resized register (`Fin (k + 1 + b) ≃ Fin m`), so
the classical truth table survives the relabelling. -/
theorem mcNot_map_equiv {p : ℕ} (σ : Fin m ≃ Fin p) (S : Finset (Fin m)) (t : Fin m)
    (x : Fin p → Fin 2) (j : Fin p) :
    mcNot (S.map σ.toEmbedding) (σ t) x j = mcNot S t (fun i => x (σ i)) (σ.symm j) := by
  have hctrl : ctrlBit (S.map σ.toEmbedding) x = ctrlBit S (fun i => x (σ i)) := by
    rw [Finset.map_eq_image, Equiv.coe_toEmbedding, ctrlBit_image]
  by_cases hj : j = σ t
  · subst hj
    rw [Equiv.symm_apply_apply, mcNot_apply_self, mcNot_apply_self, hctrl]
  · have hj' : σ.symm j ≠ t := fun h => hj ((Equiv.symm_apply_eq σ).mp h)
    rw [mcNot_apply_of_ne _ _ _ hj, mcNot_apply_of_ne _ _ _ hj', Equiv.apply_symm_apply]

/-! ### The dirty borrowed-wire reduction -/

/-- **The Barenco dirty borrowed-wire reduction (the heart of Exercise 4.29).** Split the controls
of a multiply-controlled `NOT` into two disjoint sets `A`, `B`, and let `a` be *any* wire outside
the gate's support (`a ∉ A`, `a ∉ B`, `a ≠ t`) — used as a **borrowed** work wire in an arbitrary
("dirty") state. Then
`mcNot (A ∪ B) t = mcNot (insert a B) t ∘ mcNot A a ∘ mcNot (insert a B) t ∘ mcNot A a`,
where the composition reads right to left (the rightmost `mcNot A a` acts first). The borrowed wire
`a` is toggled iff every control in `A` is set, and is **restored** by the two `mcNot A a`; the two
`mcNot (insert a B) t` flip the target `t` iff every control in `B` and `a` are set, and the even
number of `a`-toggles between them nets out to: `t` flips iff every control in `A ∪ B` is set. This
is the identity iterated (with `|A|, |B| ≈ n/2`) to reach the `O(n²)` no-work-qubit circuit. -/
theorem mcNot_union_borrow (A B : Finset (Fin m)) {a t : Fin m}
    (haA : a ∉ A) (haB : a ∉ B) (hat : a ≠ t) (htA : t ∉ A) (htB : t ∉ B) :
    mcNot (A ∪ B) t
      = mcNot (insert a B) t ∘ mcNot A a ∘ mcNot (insert a B) t ∘ mcNot A a := by
  -- A decidable `Fin 2` identity capturing the parity cancellation of the borrowed wire `a`.
  have master : ∀ w y α : Fin 2,
      w + α = w + (if y + α = 1 then (1 : Fin 2) else 0) + (if y = 1 then (1 : Fin 2) else 0) := by
    decide
  funext x
  simp only [Function.comp_apply]
  set x1 := mcNot A a x with hx1
  set x2 := mcNot (insert a B) t x1 with hx2
  set x3 := mcNot A a x2 with hx3
  -- The control bit of `A` is unaffected by the two updates (both hit wires outside `A`).
  have hAx2 : ctrlBit A x2 = ctrlBit A x := by
    rw [hx2, mcNot, ctrlBit_update_of_notMem A htA, hx1, mcNot, ctrlBit_update_of_notMem A haA]
  -- Values of the intermediate states on the relevant wires.
  have hx1a : x1 a = x a + ctrlBit A x := by rw [hx1, mcNot_apply_self]
  have hx1B : ∀ i ∈ B, x1 i = x i := by
    intro i hi; rw [hx1]; exact mcNot_apply_of_ne A a x (by rintro rfl; exact haB hi)
  have hx3a : x3 a = x a := by
    rw [hx3, mcNot_apply_self, hAx2, hx2, mcNot_apply_of_ne _ _ _ hat, hx1a]
    exact add_add_self_right _ _
  have hx3B : ∀ i ∈ B, x3 i = x i := by
    intro i hi
    have hia : i ≠ a := by rintro rfl; exact haB hi
    have hit : i ≠ t := by rintro rfl; exact htB hi
    rw [hx3, mcNot_apply_of_ne _ _ _ hia, hx2, mcNot_apply_of_ne _ _ _ hit, hx1B i hi]
  have hx3t : x3 t = x t + ctrlBit (insert a B) x1 := by
    rw [hx3, mcNot_apply_of_ne _ _ _ (Ne.symm hat), hx2, mcNot_apply_self, hx1,
      mcNot_apply_of_ne _ _ _ (Ne.symm hat)]
  funext j
  by_cases hjt : j = t
  · -- Target wire: the parity cancellation.
    subst hjt
    rw [mcNot_apply_self, ctrlBit_union, mcNot_apply_self, hx3t]
    have hB3 := forall_mem_eq_one_congr hx3B
    have hB1 := forall_mem_eq_one_congr hx1B
    rw [ctrlBit_insert, ctrlBit_insert, hx3a, hx1a]
    simp only [hB3, hB1]
    by_cases hPB : ∀ i ∈ B, x i = 1
    · simp only [and_iff_left hPB]
      exact master (x j) (x a) (ctrlBit A x)
    · rw [ite_eq_right fun h => hPB h.2, ite_eq_right fun h => hPB h.2,
          ite_eq_right fun h => hPB h.2]
      have h0 : ∀ w : Fin 2, w + 0 = w + 0 + 0 := by decide
      exact h0 (x j)
  · -- Non-target wire: passes through unchanged (borrowed wire `a` restored).
    rw [mcNot_apply_of_ne _ _ _ hjt, mcNot_apply_of_ne _ _ _ hjt]
    by_cases hja : j = a
    · subst hja; rw [hx3a]
    · rw [hx3, mcNot_apply_of_ne _ _ _ hja, hx2, mcNot_apply_of_ne _ _ _ hjt,
        hx1, mcNot_apply_of_ne _ _ _ hja]

end AxQM.Concrete
