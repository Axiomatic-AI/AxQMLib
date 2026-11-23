/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNotCircuit
import Mathlib.Data.Fin.Tuple.Basic
import ToMathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Defs

/-!
# Concrete: the CNOT circuit that computes a parity-check syndrome (N&C Exercise 10.26)

Nielsen & Chuang, Exercise 10.26 (p. 451): *Suppose `H` is a parity check matrix. Explain how to
compute the transformation `|x⟩|0⟩ → |x⟩|Hx⟩` using a circuit composed entirely of controlled-NOTs.*

This file supplies the **classical, bit-string** half of that exercise. A parity-check matrix
`H : Fin k → Fin n → Fin 2` (the entry function of a `k × n` parity-check matrix over `Fin 2`; `k`
parity checks, `n` code bits) is realised by a circuit of
CNOTs on an `n + k`-wire register: the first `n` wires hold the data `x`, the last `k` are the
syndrome ancillas (initialised to `0`). For every matrix entry `H i j = 1` the circuit contains a
CNOT with **control** the data wire `Fin.castAdd k j` and **target** the syndrome wire
`Fin.natAdd n i`. Because every control is a data wire and every target a syndrome wire — two
disjoint blocks — the CNOTs never disturb the data and each syndrome wire `i` accumulates
`∑ⱼ H i j · xⱼ = (H *ᵥ x) i` (XOR, over `Fin 2`). Hence the whole circuit's bit-string denotation
`Concrete.mcNotDenote` sends `Fin.append x 0` to `Fin.append x (H *ᵥ x)`.

The quantum realisation — a genuine closed-system `Evolution` on `qubit ^⊗ₛ (n + k)` acting on the
computational basis exactly by this denotation — is obtained in the physics file
`NC/Ch10/Exercise10_26.lean` by feeding `parityCnotCircuit` to `exists_mcNotCircuitEvolution`.

## What is formalised

* `parityCnotCols`, `parityCnotRow`, `parityCnotCircuit` — the CNOT gate list of a parity-check
  matrix (one gate per `1`-entry, control = data wire, target = syndrome wire).
* `parityCnotCircuit_target_notMem_controls` — every gate has its target off its (singleton)
  control set, the side condition `exists_mcNotCircuitEvolution` consumes.
* `mcNotDenote_parityCnotCircuit_append` — the **main** classical statement: the circuit's
  denotation maps `Fin.append x 0` to `Fin.append x (H *ᵥ x)`.

-/

namespace AxQM.Concrete

open scoped BigOperators

variable {n k M : ℕ}

/-- A data wire (`Fin.castAdd`) is never a syndrome wire (`Fin.natAdd`): the two index blocks of
`Fin (n + k)` are disjoint. -/
theorem castAdd_ne_natAdd (j : Fin n) (i : Fin k) :
    (Fin.castAdd k j : Fin (n + k)) ≠ Fin.natAdd n i := by
  refine Fin.ne_of_val_ne ?_
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  omega

/-- **A chain of CNOTs into a common target.** For control wires `cs`, all distinct from the target
`t`, the circuit `[CNOT(c → t) | c ∈ cs]` adds `∑_{c ∈ cs} y c` to wire `t` and leaves every other
wire fixed. Each control is read from the original `y` because the chain modifies only `t`. -/
theorem mcNotDenote_map_singleton (t : Fin M) (cs : List (Fin M))
    (hcs : ∀ c ∈ cs, c ≠ t) (y : Fin M → Fin 2) :
    mcNotDenote (cs.map (fun c => (({c}, t) : McNotGate M))) y
      = Function.update y t (y t + (cs.map y).sum) := by
  induction cs with
  | nil => simp [mcNotDenote_nil]
  | cons a cs IH =>
    have hat : a ≠ t := hcs a List.mem_cons_self
    rw [List.map_cons, mcNotDenote_cons, IH (fun c hc => hcs c (List.mem_cons_of_mem a hc))]
    unfold mcNot
    rw [ctrlBit_singleton]
    simp only [Function.update_self, Function.update_of_ne hat, Function.update_idem,
      List.map_cons, List.sum_cons]
    congr 1
    omega

/-- A `filterMap` guarded by an `if`, then summed, equals the plain conditional sum. Bridges the
gate-list description to a `Finset` sum. -/
private theorem list_filterMap_ite_map_sum {α γ : Type*} (l : List α)
    (p : α → Prop) [DecidablePred p] (f : α → γ) (g : γ → Fin 2) :
    ((l.filterMap fun a => if p a then some (f a) else none).map g).sum
      = (l.map fun a => if p a then g (f a) else 0).sum := by
  induction l with
  | nil => simp
  | cons a l IH => by_cases h : p a <;> simp [h, IH]

/-- The list of **control wires** for one parity-check row `r : Fin n → Fin 2` on the `n + k`-wire
register: the data wire `Fin.castAdd k j` for each column `j` with `r j = 1`. -/
def parityCnotCols (k : ℕ) (r : Fin n → Fin 2) : List (Fin (n + k)) :=
  (List.finRange n).filterMap fun j => if r j = 1 then some (Fin.castAdd k j) else none

/-- The CNOT sub-circuit for one parity-check row `r`, every gate targeting the syndrome wire `t`:
one `CNOT (castAdd k j → t)` per column `j` with `r j = 1`. -/
def parityCnotRow (k : ℕ) (r : Fin n → Fin 2) (t : Fin (n + k)) : List (McNotGate (n + k)) :=
  (parityCnotCols k r).map fun c => ({c}, t)

/-- **The CNOT circuit of a parity-check matrix `H`.** The row sub-circuits `parityCnotRow`
concatenated, row `i` targeting syndrome wire `Fin.natAdd n i`: for every entry `H i j = 1` a `CNOT`
with control the data wire `Fin.castAdd k j` and target the syndrome wire `Fin.natAdd n i`. -/
def parityCnotCircuit (H : Fin k → Fin n → Fin 2) : List (McNotGate (n + k)) :=
  (List.finRange k).flatMap fun i => parityCnotRow k (H i) (Fin.natAdd n i)

/-- Summing `y` over the control wires of row `r` gives the row's syndrome contribution
`∑ⱼ r j · y (castAdd k j)` (XOR over `Fin 2`, since `r j ∈ {0, 1}`). -/
theorem parityCnotCols_map_sum (k : ℕ) (r : Fin n → Fin 2) (y : Fin (n + k) → Fin 2) :
    ((parityCnotCols k r).map y).sum = ∑ j, r j * y (Fin.castAdd k j) := by
  have hfin : ∀ b a : Fin 2, (if b = 1 then a else 0) = b * a := by decide
  unfold parityCnotCols
  rw [list_filterMap_ite_map_sum, ← Fin.sum_univ_def]
  exact Finset.sum_congr rfl fun j _ => hfin (r j) (y (Fin.castAdd k j))

/-- **One parity-check row as a chain of CNOTs.** Applying row `r`'s CNOT sub-circuit — all
targeting a syndrome wire `t` that is off the data block — adds the row's syndrome contribution
`∑ⱼ r j · y(castAdd k j)` to wire `t` and leaves every other wire fixed. -/
theorem mcNotDenote_parityCnotRow (k : ℕ) (r : Fin n → Fin 2) (t : Fin (n + k))
    (ht : ∀ j : Fin n, (Fin.castAdd k j : Fin (n + k)) ≠ t) (y : Fin (n + k) → Fin 2) :
    mcNotDenote (parityCnotRow k r t) y
      = Function.update y t (y t + ∑ j, r j * y (Fin.castAdd k j)) := by
  rw [parityCnotRow, mcNotDenote_map_singleton t (parityCnotCols k r) ?_ y, parityCnotCols_map_sum]
  intro c hc
  unfold parityCnotCols at hc
  rw [List.mem_filterMap] at hc
  obtain ⟨j, -, hj⟩ := hc
  by_cases h : r j = 1
  · rw [ite_eq_left h, Option.some.injEq] at hj
    rw [← hj]; exact ht j
  · rw [ite_eq_right h] at hj; exact absurd hj (by simp)

/-- **Assembly over the parity-check rows.** For a list `is` of distinct rows, the concatenated CNOT
circuit maps `Fin.append x 0` to the bit-string that keeps the data `x` and sets syndrome wire `i`
to `∑ⱼ H i j · xⱼ` exactly for the rows `i ∈ is` (others stay `0`). -/
theorem mcNotDenote_parityCnotCircuit_flatMap (H : Fin k → Fin n → Fin 2)
    (x : Fin n → Fin 2) : ∀ is : List (Fin k), is.Nodup →
    mcNotDenote (is.flatMap fun i => parityCnotRow k (H i) (Fin.natAdd n i))
        (Fin.append x (fun _ => 0))
      = Fin.append x (fun i => if i ∈ is then (∑ j, H i j * x j) else 0) := by
  intro is
  induction is with
  | nil =>
    intro _
    simp only [List.flatMap_nil, mcNotDenote_nil, List.not_mem_nil, ite_false]
  | cons i₀ is IH =>
    intro hnd
    obtain ⟨hi₀, hndtl⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons, mcNotDenote_append, IH hndtl,
      mcNotDenote_parityCnotRow k (H i₀) (Fin.natAdd n i₀) fun j => castAdd_ne_natAdd j i₀]
    funext w
    induction w using Fin.addCases with
    | left j =>
      simp only [Function.update_of_ne (castAdd_ne_natAdd j i₀), Fin.append_left]
    | right i =>
      by_cases hii : i = i₀
      · subst hii
        simp only [Function.update_self, Fin.append_right, Fin.append_left, ite_eq_right hi₀,
          List.mem_cons, true_or, ite_true, zero_add]
      · have hne : (Fin.natAdd n i : Fin (n + k)) ≠ Fin.natAdd n i₀ :=
          (Fin.natAdd_injective k n).ne hii
        simp only [Function.update_of_ne hne, Fin.append_right, List.mem_cons, hii, false_or]

/-- **The parity-check syndrome CNOT circuit (classical denotation).** The bit-string denotation of
`parityCnotCircuit H` sends `Fin.append x 0` to `Fin.append x (fun i => ∑ⱼ H i j · xⱼ)`: the data
block is preserved and syndrome wire `i` holds `(Hx)ᵢ = ∑ⱼ H i j · xⱼ` (mod 2).
The classical half of N&C Ex 10.26; the quantum realisation is `NC/Ch10/Exercise10_26.lean`. -/
theorem mcNotDenote_parityCnotCircuit_append (H : Fin k → Fin n → Fin 2) (x : Fin n → Fin 2) :
    mcNotDenote (parityCnotCircuit H) (Fin.append x (fun _ => 0))
      = Fin.append x (fun i => ∑ j, H i j * x j) := by
  rw [parityCnotCircuit,
    mcNotDenote_parityCnotCircuit_flatMap H x (List.finRange k) (List.nodup_finRange k)]
  congr 1
  funext i
  rw [ite_eq_left (List.mem_finRange i)]

/-- **Membership characterization of `parityCnotCircuit`.** Its gates are exactly the CNOTs
`({Fin.castAdd k j}, Fin.natAdd n i)` — control the data wire `castAdd k j`, target the syndrome
wire `natAdd n i` — for the entries `H i j = 1`. -/
theorem mem_parityCnotCircuit {H : Fin k → Fin n → Fin 2} {g : McNotGate (n + k)}
    (hg : g ∈ parityCnotCircuit H) :
    ∃ (i : Fin k) (j : Fin n), H i j = 1 ∧ g = ({Fin.castAdd k j}, Fin.natAdd n i) := by
  unfold parityCnotCircuit at hg
  rw [List.mem_flatMap] at hg
  obtain ⟨i, -, hg⟩ := hg
  unfold parityCnotRow at hg
  rw [List.mem_map] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  unfold parityCnotCols at hc
  rw [List.mem_filterMap] at hc
  obtain ⟨j, -, hj⟩ := hc
  by_cases h : H i j = 1
  · rw [ite_eq_left h, Option.some.injEq] at hj
    exact ⟨i, j, h, by rw [← hj]⟩
  · rw [ite_eq_right h] at hj; exact absurd hj (by simp)

/-- Every CNOT in `parityCnotCircuit H` has its target off its (singleton) control set — the side
condition `exists_mcNotCircuitEvolution` consumes to realise the circuit as an `Evolution`. -/
theorem parityCnotCircuit_target_notMem_controls (H : Fin k → Fin n → Fin 2) :
    ∀ g ∈ parityCnotCircuit H, g.2 ∉ g.1 := by
  intro g hg
  obtain ⟨i, j, -, rfl⟩ := mem_parityCnotCircuit hg
  simp only [Finset.mem_singleton]
  exact (castAdd_ne_natAdd j i).symm

/-- Every gate in `parityCnotCircuit H` has a **single** control wire — so the circuit is composed
entirely of controlled-`NOT`s (each `|S| = 1`), never a `NOT` (`|S| = 0`) or `Toffoli` (`|S| = 2`).
This is the "composed entirely of controlled-NOTs" clause of N&C Exercise 10.26. -/
theorem parityCnotCircuit_card_controls (H : Fin k → Fin n → Fin 2) :
    ∀ g ∈ parityCnotCircuit H, g.1.card = 1 := by
  intro g hg
  obtain ⟨i, j, -, rfl⟩ := mem_parityCnotCircuit hg
  exact Finset.card_singleton _

end AxQM.Concrete
