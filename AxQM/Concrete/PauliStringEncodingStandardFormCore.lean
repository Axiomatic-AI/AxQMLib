/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingCnotStage

/-!
# Concrete: the CNOT + Hadamard core of the stabilizer encoding circuit (N&C, Problem 10.3)

This file continues the **synthesis** half
of Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes") — building the circuit that
carries the *trivial* check matrix `G` of Eq. (10.124) (a listing of the single-qubit generators
`Z₁, …, Zₙ`, i.e. every row `(0 | eᵢ)`) to the **standard form** of Eq. (10.125). The final circuit
is three composed layers,

  `encodingCircuit = phaseCZNetwork ws pairs`
  `++ cnotNetwork (pivots ++ dataWires) tgt ++ hadLayer pivots`;

this file assembles and evaluates the **first two** (`hadLayer ++ cnotNetwork`), depositing every
`X`-block and every *coupled* `Z`-block of (10.125), and leaves the residual top-row `Z`-blocks
`B`, `C₂` — built by the phase/`CZ` network — to the terminal assembly.

## The partition and the two-stage CNOT ordering

`StdFormData n` bundles the combinatorial data of a standard form: a partition of the `n` wires into
`pivots` (the `r` rows with an `X`-part, Hadamard'd at the front), `middle` (the `n − k − r`
pure-`Z` generator rows), and `dataWires` (the `k` encoded-`Z` rows), together with the fan targets
`tgt : Fin n → List (Fin n)`. Reading a target list as a support, `tgt` encodes the standard-form
matrices: for a pivot `p`, `tgt p ⊆ middle ∪ dataWires` is the support of row `p` of `[A₁ | A₂]`;
for a data wire `d`, `tgt d ⊆ middle` is the support of row `d` of `E`.

`encodingCnotHad D := cnotNetwork (D.pivots ++ D.dataWires) D.tgt ++ hadLayer D.pivots`. Reading the
append right-to-left (`CliffordCircuit.act_append`), the Hadamard layer acts **first**
(`Zₚ ↦ Xₚ` on the pivots, `act_hadLayer_zGenPauli`), then the CNOT network. The control list is
`pivots ++ dataWires`, so within the network — via `cnotNetwork_append` and the two-stage engine
(`checkRow_act_cnotNetwork_split_zGenPauli` / `_xGenPauli`) — the **data**-controlled
`E`-fans act innermost and the **pivot** fans act on their output. That ordering is the crux:
the data fans deposit the `E`-block on the middle rows, then
the pivot fans *read the just-deposited `E`* off the data columns, injecting the `E A₂ᵀ` cross-term
that
makes the standard-form relation `D = A₁ᵀ + E A₂ᵀ` (10.125).

## What is proved

For any `D : StdFormData n`, the row-by-row check-matrix action of `encodingCnotHad D` on the seed
rows `Zᵢ` of `G` (10.124):

* `checkRow_encodingCnotHad_pivot` — a **pivot** row `p` becomes `(eₚ + 𝟙_{tgt p} | 0)`: the top
  rows' `X`-blocks `[I A₁ A₂]` (the `I` from the pivot's own wire, `A₁ A₂` from the fan onto its
  middle/data targets), with `Z`-part still `0` (`B, C₂` are the phase/`CZ` layer's job).
* `checkRow_encodingCnotHad_data` — a **data** row `d` becomes
  `(0 | e_d + 𝟙_{p ∈ pivots, d ∈ tgt p})`:
  the encoded-`Z` rows `[A₂ᵀ 0 I]` (the `I` on the data wire itself, `A₂ᵀ` the pivots whose fan
  reaches `d`; the `0` middle block because a data wire is no middle wire's fan source).
* `checkRow_encodingCnotHad_middle` — a **middle** row `m` becomes `(0 | …)` with `Z`-part carrying
  the `I` on `m`, the `E`-block `𝟙[m ∈ tgt d]` on each data wire `d`, and the `D`-block
  `[m ∈ tgt p] + Σ_{t ∈ tgt p} [t ∈ dataWires ∧ m ∈ tgt t]` on each pivot `p` — exactly
  `A₁ᵀ + E A₂ᵀ = D`, the middle rows `[D I E]` of (10.125). This is the read-off exhibiting the
  general `E` and the coupling `D = A₁ᵀ + E A₂ᵀ`.

Since `tgt` is arbitrary (subject only to the partition/support constraints), the blocks `A₁, A₂, E`
range over all `ZMod 2` matrices of the right shape — so this reaches the *general* standard form,
not a specific code (the book's own Steane example has `E ≠ 0`).

Everything is stated for raw index / matrix data (`Concrete.CliffordCircuit`, `Fin n → Fin 4`,
`ZMod 2`). The phase/`CZ` layer (`B, C₂`), the full assembly `encodingCircuit` reaching
(10.125), and the operator-level (unitary) reading build on this.

## Design notes

* The partition data is bundled as a `structure` so the three read-offs share one hypothesis list
  and the terminal assembly can reuse it. Only the constraints the proofs consume are recorded:
  `Nodup` of the two control lists and every target list; the two support inclusions
  (`tgt p ⊆ middle ∪ dataWires`, `tgt d ⊆ middle`); and the three class-disjointnesses. From these,
  `pivots_disj_tgt` / `data_disj_tgt` supply the *internal disjointness* the two-stage split lemmas
  demand (a control is never a fan target within its own stage), while cross-stage non-disjointness
  (a pivot fan may target a data wire that is itself an `E`-fan control) is exactly the `E A₂ᵀ`
  coupling and is *not* required.
* Each read-off is `CliffordCircuit.act_append` (peel the Hadamard layer) + `act_hadLayer_zGenPauli`
  (`Zₚ ↦ Xₚ` on pivots, identity off them) + the two-stage split lemma (front `= pivots`, back
  `= dataWires`), reducing to `cnotNetworkCol pivots tgt` applied to an explicit seed row, which is
  then evaluated wire-by-wire with `sum_map_ite_eq_of_nodup` (indicator sums) and `List.sum_map_add`
  (splitting the `D`-block into `A₁ᵀ` and the `E A₂ᵀ` matrix product).
-/

namespace AxQM.Concrete

variable {n : ℕ}

/-- **The combinatorial data of a standard-form stabilizer code** (N&C (10.111)/(10.125)), as
consumed by the encoding circuit. A partition of the `n` wires into `pivots` (the `r` generator rows
carrying an `X`-part), `middle` (the `n − k − r` pure-`Z` generator rows) and `dataWires` (the `k`
encoded-`Z` rows), together with a fan-target assignment `tgt : Fin n → List (Fin n)` whose supports
*are* the standard-form matrices: `tgt p` (for a pivot `p`) is the support of row `p` of `[A₁ | A₂]`
(targets in `middle ∪ dataWires`); and `tgt d` (for a data wire `d`) is the support of row `d`
of `E`
(targets in `middle`). Only the constraints the read-offs consume are recorded. -/
structure StdFormData (n : ℕ) where
  /-- The pivot wires: the `r` generator rows with a nonzero `X`-part, Hadamard'd at the front. -/
  pivots : List (Fin n)
  /-- The middle wires: the `n − k − r` pure-`Z` generator rows. -/
  middle : List (Fin n)
  /-- The data wires: the `k` encoded-`Z` rows. -/
  dataWires : List (Fin n)
  /-- The CNOT-fan targets of each control wire (the supports of the `[A₁ | A₂]` / `E` rows). -/
  tgt : Fin n → List (Fin n)
  /-- The pivot control list has no repeats. -/
  pivots_nodup : pivots.Nodup
  /-- The data control list has no repeats. -/
  data_nodup : dataWires.Nodup
  /-- Every target list has no repeats (each `1` of a block gives one CNOT). -/
  tgt_nodup : ∀ w : Fin n, (tgt w).Nodup
  /-- A pivot's fan targets lie in the middle or data wires (the columns of `[A₁ | A₂]`). -/
  tgt_pivot_mem : ∀ p ∈ pivots, ∀ t ∈ tgt p, t ∈ middle ∨ t ∈ dataWires
  /-- A data wire's fan targets lie in the middle wires (the columns of `E`). -/
  tgt_data_mem : ∀ d ∈ dataWires, ∀ t ∈ tgt d, t ∈ middle
  /-- No pivot is a middle wire. -/
  pivot_not_middle : ∀ p ∈ pivots, p ∉ middle
  /-- No pivot is a data wire. -/
  pivot_not_data : ∀ p ∈ pivots, p ∉ dataWires
  /-- No data wire is a middle wire. -/
  data_not_middle : ∀ d ∈ dataWires, d ∉ middle

namespace StdFormData

variable (D : StdFormData n)

/-- **Internal disjointness of the pivot stage**: no pivot is a fan target of any pivot. From the
`[A₁ | A₂]`-support inclusion (`tgt_pivot_mem`, targets in `middle ∪ dataWires`) and the fact that a
pivot is neither a middle nor a data wire. This is the hypothesis the two-stage split lemmas demand
of the `front = pivots` stage. -/
theorem pivots_disj_tgt : ∀ a ∈ D.pivots, ∀ b ∈ D.pivots, a ∉ D.tgt b := by
  intro a ha b hb hmem
  rcases D.tgt_pivot_mem b hb a hmem with h | h
  · exact D.pivot_not_middle a ha h
  · exact D.pivot_not_data a ha h

/-- **Internal disjointness of the data stage**: no data wire is a fan target of any data wire. From
the `E`-support inclusion (`tgt_data_mem`, targets in `middle`) and the fact that a data wire is
not a middle wire. This is the hypothesis the two-stage split lemmas demand of the
`back = dataWires` stage. -/
theorem data_disj_tgt : ∀ a ∈ D.dataWires, ∀ b ∈ D.dataWires, a ∉ D.tgt b := by
  intro a ha b hb hmem
  exact D.data_not_middle a ha (D.tgt_data_mem b hb a hmem)

end StdFormData

/-- **The CNOT + Hadamard core of the encoding circuit** (N&C Problem 10.3): the Hadamard layer on
the pivots followed (in circuit order: acting after) by the CNOT network with control list
`pivots ++ dataWires`. Reading `act` right-to-left, the Hadamards act first (`Zₚ ↦ Xₚ`), then the
data-controlled `E`-fans, then the pivot fans. Composing the phase/`CZ` network onto the front of
this circuit gives the full stabilizer encoding circuit `encodingCircuit`. -/
def encodingCnotHad (D : StdFormData n) : CliffordCircuit n :=
  cnotNetwork (D.pivots ++ D.dataWires) D.tgt ++ hadLayer D.pivots

/-- **The CNOT+Hadamard core builds the top rows' `X`-blocks `[I A₁ A₂]`** (N&C (10.125)). For a
pivot wire `p`, `encodingCnotHad D` carries the seed row `Zₚ` of `G` (10.124) to the check row
`(eₚ + 𝟙_{tgt p} | 0)`: the Hadamard turns `Zₚ` into `Xₚ`, then the pivot fan spreads that `X` onto
every wire in `tgt p` (the `A₁, A₂` support), while the `Z`-part stays `0` (the residual blocks
`B, C₂` are deposited by the later phase/`CZ` layer). The data-fan stage fixes `Xₚ` because a pivot
is no data wire, so the two-stage split collapses to the pivot stage alone. -/
theorem checkRow_encodingCnotHad_pivot (D : StdFormData n) {p : Fin n} (hp : p ∈ D.pivots) :
    checkRow (CliffordCircuit.act (encodingCnotHad D) (zGenPauli p))
      = (fun k => (if k = p then (1 : ZMod 2) else 0) + (if k ∈ D.tgt p then 1 else 0),
         0) := by
  rw [encodingCnotHad, CliffordCircuit.act_append,
    act_hadLayer_zGenPauli D.pivots D.pivots_nodup, ite_eq_left hp,
    checkRow_act_cnotNetwork_split_xGenPauli D.pivots D.dataWires D.tgt
      D.pivots_nodup D.pivots_disj_tgt (fun c _ => D.tgt_nodup c)
      D.data_nodup D.data_disj_tgt (fun c _ => D.tgt_nodup c) p]
  have hpd : p ∉ D.dataWires := D.pivot_not_data p hp
  rw [show (fun k : Fin n => (if k = p then (1 : ZMod 2) else 0)
        + (if p ∈ D.dataWires ∧ k ∈ D.tgt p then (1 : ZMod 2) else 0))
      = (fun k : Fin n => if k = p then (1 : ZMod 2) else 0) from by
        funext k
        have hne : ¬ (p ∈ D.dataWires ∧ k ∈ D.tgt p) := fun h => hpd h.1
        rw [ite_eq_right hne, add_zero]]
  ext k
  · simp only [cnotNetworkCol]
    have hmap :
      D.pivots.map (fun c => if k ∈ D.tgt c then (if c = p then (1 : ZMod 2) else 0) else 0)
      = D.pivots.map (fun c => if c = p then (if k ∈ D.tgt p then (1 : ZMod 2) else 0) else 0) := by
      apply List.map_congr_left
      intro c _
      by_cases hc : c = p
      · subst hc; simp
      · simp [hc]
    rw [hmap, sum_map_ite_eq_of_nodup p (if k ∈ D.tgt p then (1 : ZMod 2) else 0) D.pivots
        D.pivots_nodup, ite_eq_left hp]
  · simp [cnotNetworkCol]

/-- **The CNOT+Hadamard core builds the data rows' `[A₂ᵀ 0 I]`** (N&C (10.125)). For a data wire
`d`, `encodingCnotHad D` carries the seed row `Z_d` of `G` (10.124) to the check row
`(0 | e_d + 𝟙_{p ∈ pivots, d ∈ tgt p})`: the Hadamard leaves `Z_d` alone (`d` is no pivot), the
data-fan stage leaves it alone (a data wire is no middle wire, so no `E`-fan reaches it), and each
pivot fan whose target set contains `d` (an `A₂` entry) copies a `Z` back onto its pivot column —
building the transposed block `A₂ᵀ`, with the `I` on the data wire itself and the `0` middle
block. -/
theorem checkRow_encodingCnotHad_data (D : StdFormData n) {d : Fin n} (hd : d ∈ D.dataWires) :
    checkRow (CliffordCircuit.act (encodingCnotHad D) (zGenPauli d))
      = (0, fun k => (if k = d then (1 : ZMod 2) else 0)
          + (if k ∈ D.pivots ∧ d ∈ D.tgt k then 1 else 0)) := by
  have hdp : d ∉ D.pivots := fun h => D.pivot_not_data d h hd
  rw [encodingCnotHad, CliffordCircuit.act_append,
    act_hadLayer_zGenPauli D.pivots D.pivots_nodup, ite_eq_right hdp,
    checkRow_act_cnotNetwork_split_zGenPauli D.pivots D.dataWires D.tgt
      D.pivots_nodup D.pivots_disj_tgt (fun c _ => D.tgt_nodup c)
      D.data_nodup D.data_disj_tgt (fun c _ => D.tgt_nodup c) d]
  rw [show (fun k : Fin n => (if k = d then (1 : ZMod 2) else 0)
        + (if k ∈ D.dataWires ∧ d ∈ D.tgt k then (1 : ZMod 2) else 0))
      = (fun k : Fin n => if k = d then (1 : ZMod 2) else 0) from by
        funext k
        have hne : ¬ (k ∈ D.dataWires ∧ d ∈ D.tgt k) :=
          fun h => D.data_not_middle d hd (D.tgt_data_mem k h.1 d h.2)
        rw [ite_eq_right hne, add_zero]]
  ext k
  · simp [cnotNetworkCol]
  · simp only [cnotNetworkCol]
    rw [sum_map_ite_eq_of_nodup d (1 : ZMod 2) (D.tgt k) (D.tgt_nodup k)]
    by_cases hk : k ∈ D.pivots <;> by_cases hkd : d ∈ D.tgt k <;> simp [hk, hkd]

/-- **The CNOT+Hadamard core builds the middle rows' `[D I E]` with `D = A₁ᵀ + E A₂ᵀ`** (N&C
(10.125)). For a middle wire `m`, `encodingCnotHad D` carries the seed row `Z_m` of `G` (10.124) to
the pure-`Z` check row whose `Z`-part is:

* `I`: a `1` on `m` itself;
* `E`: a `1` on each data wire `k` whose `E`-fan reaches `m` (`k ∈ dataWires ∧ m ∈ tgt k`);
* `D = A₁ᵀ + E A₂ᵀ`: on each pivot `k`, `[m ∈ tgt k] + Σ_{t ∈ tgt k} [t ∈ dataWires ∧ m ∈ tgt k]` —
  the direct `A₁ᵀ` term (pivot `k`'s fan reaches `m`) plus the `E A₂ᵀ` cross-term (pivot `k`'s fan
  reaches a data wire `t` whose own `E`-fan reaches `m`).

The cross-term is where the two-stage ordering pays off: the data-controlled `E`-fans (innermost)
deposit `E` on the data columns of `m`'s row first, and the pivot fans then read it back onto their
pivot columns (`z_c += z_t`) — exactly `E A₂ᵀ`, giving the standard-form coupling `D = A₁ᵀ + E A₂ᵀ`
and the general (non-zero) `E` of (10.125). -/
theorem checkRow_encodingCnotHad_middle (D : StdFormData n) {m : Fin n} (hm : m ∈ D.middle) :
    checkRow (CliffordCircuit.act (encodingCnotHad D) (zGenPauli m))
      = (0, fun k =>
          (if k = m then (1 : ZMod 2) else 0)
          + (if k ∈ D.dataWires ∧ m ∈ D.tgt k then 1 else 0)
          + (if k ∈ D.pivots then
               ((if m ∈ D.tgt k then (1 : ZMod 2) else 0)
                + ((D.tgt k).map
                    (fun t => if t ∈ D.dataWires ∧ m ∈ D.tgt t then (1 : ZMod 2) else 0)).sum)
             else 0)) := by
  have hmp : m ∉ D.pivots := fun h => D.pivot_not_middle m h hm
  rw [encodingCnotHad, CliffordCircuit.act_append,
    act_hadLayer_zGenPauli D.pivots D.pivots_nodup, ite_eq_right hmp,
    checkRow_act_cnotNetwork_split_zGenPauli D.pivots D.dataWires D.tgt
      D.pivots_nodup D.pivots_disj_tgt (fun c _ => D.tgt_nodup c)
      D.data_nodup D.data_disj_tgt (fun c _ => D.tgt_nodup c) m]
  ext k
  · simp [cnotNetworkCol]
  · simp only [cnotNetworkCol]
    congr 1
    by_cases hk : k ∈ D.pivots
    · rw [ite_eq_left hk, ite_eq_left hk, List.sum_map_add,
        sum_map_ite_eq_of_nodup m (1 : ZMod 2) (D.tgt k) (D.tgt_nodup k)]
    · rw [ite_eq_right hk, ite_eq_right hk]

end AxQM.Concrete
