/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingCnotNetwork

/-!
# Concrete: closed-form column action of a *disjoint* CNOT network (N&C, Problem 10.3)

It continues the **synthesis** half
of Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes"). The multi-control CNOT network
`cnotNetwork controls tgt` of `Concrete/PauliStringEncodingCnotNetwork.lean` acts on a check row by
the *right fold* of the per-control fan column operations `cnotFanCol` (`checkRow_act_cnotNetwork`).
A fold is exactly what a proof cannot read block structure off of: successive fans could, in
principle, feed each other. This file evaluates that fold to a **simultaneous closed form** under
the one structural hypothesis the encoding circuit always satisfies — that the network's *controls
are
disjoint from every one of its target lists* (`∀ a b ∈ controls, a ∉ tgt b`):

* `cnotNetworkCol` — the closed-form column operation of a disjoint network: every wire `k` in some
  `tgt c` receives the (original) control `X`-bits `x_c` fanned onto it
  (`x_k += Σ_{c : k ∈ tgt c} x_c`); every control `c` receives the sum of its (original) target
  `Z`-bits (`z_c += Σ_{t ∈ tgt c} z_t`); everything else is fixed. Because controls never appear as
  targets, a control's `X`-bit and a target's `Z`-bit are read **once, from the input row** — the
  fans do not interfere, so the fold collapses to this single simultaneous operation.
* `checkRow_act_cnotNetwork_disjoint` — the fold-free column action: `checkRow (act (cnotNetwork
  controls tgt) g) = cnotNetworkCol controls tgt (checkRow g)`, from the generic fold
  `checkRow_act_cnotNetwork` and the collapse lemma `cnotNetworkCol_foldr`.
* `checkRow_act_cnotNetwork_disjoint_zGenPauli` — the network's action on a pure-`Z` seed row `Zᵢ`
  (row of the trivial matrix `G` (10.124)): the `X`-part stays `0` and a `Z` is deposited on each
  control `c` whose target list reaches `w` (`z_c += 1` iff `w ∈ tgt c`). With **data-wire controls
  fanning onto middle wires**, this is exactly how the encoding circuit builds the `E`-block of
  (10.125) on the middle rows — refuting the apparent obstruction that "phase/`CZ` gates cannot
  build `E`": a CNOT fan *can*, precisely because its controls (the encoded/data wires) are disjoint
  from its targets (the middle wires). With **pivot controls**, the same lemma deposits the coupled
  transpose `Z`-blocks `A₁ᵀ`, `A₂ᵀ`.
* `checkRow_act_cnotNetwork_disjoint_xGenPauli` — the network's action on a pure-`X` seed row `Xᵢ`
  (a top row after the Hadamard layer): the `Z`-part stays `0` and, if `w` is a control, its
  `X`-bit spreads onto every wire in `tgt w` (`x_k += 1` for `k ∈ tgt w`). This is how the pivot
  CNOT fans build the top rows' `X`-blocks `[I A₁ A₂]`.

Carrying `G` (10.124) to the standard form (10.125) applies this
lemma twice: once for the middle-target `E`-fans (data controls) on the seed rows, and once for the
pivot fans (whose reads then pick up the just-deposited `E`, injecting the `E A₂ᵀ` cross-term into
`D` and giving the standard-form relation `D = A₁ᵀ + E A₂ᵀ`).

## Design notes

* The disjointness hypothesis is `∀ a ∈ controls, ∀ b ∈ controls, a ∉ tgt b` — no control is a
  target of any fan (including its own, so it subsumes the per-fan freshness `c ∉ tgt c` that
  `checkRow_act_cnotNetwork` demands). It is what makes the reads in `cnotFanCol` original: a
  control's `X`-bit is never fanned into (controls are not targets), and a target's `Z`-bit is never
  accumulated away (only control `Z`-bits change).
* `cnotNetworkCol_foldr` is proved by induction on `controls`; the cons step uses `c ∉ cs`
  (`Nodup`) to see the freshly-peeled control's own bits unchanged, and the disjointness to drop the
  inner fans' contributions to the peeled control's `X`-bit and to its targets' `Z`-bits.
* `sum_map_ite_eq_of_nodup` — the `Nodup` specialization of Mathlib's `List.sum_map_ite_eq` —
  is the elementary "indicator sum over a duplicate-free list" fact turning the `X`-fan /
  `Z`-transpose map-sums into single membership tests; it is the only bookkeeping the seed
  corollaries need beyond the closed form.
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### An indicator sum over a duplicate-free list -/

/-- **Indicator sum over a `Nodup` list**: `∑_{a ∈ l} (if a = w then v else 0) = v` if `w ∈ l`, else
`0`. The `Nodup` specialization of the general Mathlib lemma `List.sum_map_ite_eq`, from which
it is derived: with no duplicates `w` occurs at most once (`List.count w l ∈ {0, 1}`), so it
contributes its value `v` at most once. This is the only bookkeeping the seed corollaries need to
turn the fan map-sums into membership tests. -/
theorem sum_map_ite_eq_of_nodup (w : Fin n) (v : ZMod 2) (l : List (Fin n)) (hnd : l.Nodup) :
    (l.map (fun a => if a = w then v else 0)).sum = if w ∈ l then v else 0 := by
  rw [List.sum_map_ite_eq l (fun _ => v) (fun _ => 0) w]
  simp only [sub_zero, List.map_const', List.sum_replicate, smul_zero, add_zero]
  rcases em (w ∈ l) with h | h
  · rw [ite_eq_left h, List.count_eq_one_of_mem hnd h, one_smul]
  · rw [ite_eq_right h, List.count_eq_zero_of_not_mem h, zero_smul]

/-! ### The closed-form column operation of a disjoint CNOT network -/

/-- The **simultaneous closed-form column operation** of a CNOT network whose controls are disjoint
from all its target lists, on a check row `r = (x | z)`: fan each control's (original) `X`-bit onto
its targets (`x_k += Σ_{c : k ∈ tgt c} x_c`) and accumulate each control's (original) target
`Z`-bits back onto it (`z_c += Σ_{t ∈ tgt c} z_t`), fixing everything else. Every read is of the
**input** row `r`: valid because a control is never a target (so control `X`-bits and target
`Z`-bits are untouched by the network), which is exactly why the per-fan fold collapses to this one
operation (`cnotNetworkCol_foldr`). -/
def cnotNetworkCol (controls : List (Fin n)) (tgt : Fin n → List (Fin n))
    (r : (Fin n → ZMod 2) × (Fin n → ZMod 2)) : (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (fun k => r.1 k + (controls.map (fun c => if k ∈ tgt c then r.1 c else 0)).sum,
   fun k => r.2 k + (if k ∈ controls then ((tgt k).map (fun t => r.2 t)).sum else 0))

/-- **The disjoint CNOT network's fold collapses to the closed form** `cnotNetworkCol`. For controls
without duplicates (`controls.Nodup`) and disjoint from every target list
(`∀ a b ∈ controls, a ∉ tgt b`), the right fold of the per-control fan column operations equals the
simultaneous closed form. Proved by induction on `controls`: peeling the head control `c`, the inner
fold already reads only the original row, and disjointness makes `c`'s own `X`-bit and its targets'
`Z`-bits unchanged by `cs`'s fans (each such would need `c ∈ tgt c'` or a target `∈ cs`, both
excluded), so the head fan `cnotFanCol c (tgt c)` extends the closed form by its `c`-indexed row. -/
theorem cnotNetworkCol_foldr (tgt : Fin n → List (Fin n)) :
    ∀ (controls : List (Fin n)), controls.Nodup →
      (∀ a ∈ controls, ∀ b ∈ controls, a ∉ tgt b) →
      ∀ (r : (Fin n → ZMod 2) × (Fin n → ZMod 2)),
        controls.foldr (fun c r' => cnotFanCol c (tgt c) r') r = cnotNetworkCol controls tgt r
  | [], _, _, r => by
      ext k <;> simp [cnotNetworkCol]
  | c :: cs, hnd, hdisj, r => by
      obtain ⟨hcnotin, hndcs⟩ := List.nodup_cons.mp hnd
      have hdisjcs : ∀ a ∈ cs, ∀ b ∈ cs, a ∉ tgt b := fun a ha b hb =>
        hdisj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
      -- `c` is not a target of any inner fan, so its X-bit is read unchanged.
      have hxc : (cs.map (fun c' => if c ∈ tgt c' then r.1 c' else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨c', hc', rfl⟩ := hy
        exact ite_eq_right (hdisj c (List.mem_cons_self ..) c' (List.mem_cons_of_mem _ hc'))
      have hXc : (cnotNetworkCol cs tgt r).1 c = r.1 c := by
        simp only [cnotNetworkCol, hxc, add_zero]
      -- Each target `t ∈ tgt c` is not a control in `cs`, so its Z-bit is read unchanged.
      have hZt : ∀ t ∈ tgt c, (cnotNetworkCol cs tgt r).2 t = r.2 t := by
        intro t ht
        have htnotin : t ∉ cs := fun htc =>
          hdisj t (List.mem_cons_of_mem _ htc) c (List.mem_cons_self ..) ht
        simp only [cnotNetworkCol, ite_eq_right htnotin, add_zero]
      have hZc : (cnotNetworkCol cs tgt r).2 c = r.2 c := by
        simp only [cnotNetworkCol, ite_eq_right hcnotin, add_zero]
      rw [List.foldr_cons, cnotNetworkCol_foldr tgt cs hndcs hdisjcs r]
      ext k
      · -- X-part
        simp only [cnotFanCol]
        rw [hXc]
        simp only [cnotNetworkCol, List.map_cons, List.sum_cons]
        abel
      · -- Z-part
        simp only [cnotFanCol]
        by_cases hkc : k = c
        · subst hkc
          have hmap : (tgt k).map (fun t => (cnotNetworkCol cs tgt r).2 t)
              = (tgt k).map (fun t => r.2 t) := by
            apply List.map_congr_left; exact hZt
          rw [ite_eq_left rfl, hmap, hZc]
          simp only [cnotNetworkCol, List.mem_cons_self, ite_true]
        · rw [ite_eq_right hkc, add_zero]
          simp only [cnotNetworkCol, List.mem_cons, hkc, false_or]

/-- **The disjoint CNOT network acts on the check matrix by the closed form** `cnotNetworkCol` (N&C
Problem 10.3): for controls without duplicates and disjoint from every target list, and each target
list itself duplicate-free, conjugating any Pauli string `g` by `cnotNetwork controls tgt`
transforms its check row by the simultaneous column operation `cnotNetworkCol controls tgt`, no fan
interfering with another. Combines the generic fold `checkRow_act_cnotNetwork` with the collapse
`cnotNetworkCol_foldr`. This is the fold-free form the encoding assembly evaluates on the rows of
`G` (10.124). -/
theorem checkRow_act_cnotNetwork_disjoint (controls : List (Fin n)) (tgt : Fin n → List (Fin n))
    (hnd : controls.Nodup) (hdisj : ∀ a ∈ controls, ∀ b ∈ controls, a ∉ tgt b)
    (htnd : ∀ c ∈ controls, (tgt c).Nodup) (g : Fin n → Fin 4) :
    checkRow (CliffordCircuit.act (cnotNetwork controls tgt) g)
      = cnotNetworkCol controls tgt (checkRow g) := by
  rw [checkRow_act_cnotNetwork tgt controls
        (fun c hc => ⟨hdisj c hc c hc, htnd c hc⟩) g,
    cnotNetworkCol_foldr tgt controls hnd hdisj]

/-! ### Action on the trivial check matrix's seed rows -/

/-- **The disjoint CNOT network on a pure-`Z` seed row** `Zᵢ` (row `w` of the trivial matrix `G`
(10.124), check row `(0 | e_w)`): the `X`-part stays `0`, and the `Z`-part is `e_w` plus a `1` on
each control `k` whose fan reaches `w` (`k ∈ controls ∧ w ∈ tgt k`). With **data-wire controls
fanning onto middle wires**, this deposits the `E`-block on the middle rows of (10.125) — a CNOT fan
builds `E` even though the middle rows carry no `X`-part, because its controls are disjoint from its
targets. With **pivot controls** it deposits the coupled transpose blocks `A₁ᵀ`, `A₂ᵀ`. -/
theorem checkRow_act_cnotNetwork_disjoint_zGenPauli (controls : List (Fin n))
    (tgt : Fin n → List (Fin n)) (hnd : controls.Nodup)
    (hdisj : ∀ a ∈ controls, ∀ b ∈ controls, a ∉ tgt b)
    (htnd : ∀ c ∈ controls, (tgt c).Nodup) (w : Fin n) :
    checkRow (CliffordCircuit.act (cnotNetwork controls tgt) (zGenPauli w))
      = (0, fun k => (if k = w then (1 : ZMod 2) else 0)
          + (if k ∈ controls ∧ w ∈ tgt k then 1 else 0)) := by
  rw [checkRow_act_cnotNetwork_disjoint controls tgt hnd hdisj htnd, checkRow_zGenPauli]
  ext k
  · simp [cnotNetworkCol]
  · simp only [cnotNetworkCol, Pi.single_apply]
    by_cases hk : k ∈ controls
    · rw [ite_eq_left hk, sum_map_ite_eq_of_nodup w 1 (tgt k) (htnd k hk)]
      simp [hk]
    · rw [ite_eq_right hk]
      simp [hk]

/-- **The disjoint CNOT network on a pure-`X` seed row** `Xᵢ` (a top row after the Hadamard layer,
check row `(e_w | 0)`): the `Z`-part stays `0`, and the `X`-part is `e_w` plus a `1` on each wire
`k` that `w`'s fan reaches (`w ∈ controls ∧ k ∈ tgt w`). With **pivot controls**, spreading the
`X`-bit onto its target support is how the encoding circuit builds the top rows' `X`-blocks
`[I A₁ A₂]` of (10.125). -/
theorem checkRow_act_cnotNetwork_disjoint_xGenPauli (controls : List (Fin n))
    (tgt : Fin n → List (Fin n)) (hnd : controls.Nodup)
    (hdisj : ∀ a ∈ controls, ∀ b ∈ controls, a ∉ tgt b)
    (htnd : ∀ c ∈ controls, (tgt c).Nodup) (w : Fin n) :
    checkRow (CliffordCircuit.act (cnotNetwork controls tgt) (xGenPauli w))
      = (fun k => (if k = w then (1 : ZMod 2) else 0)
          + (if w ∈ controls ∧ k ∈ tgt w then 1 else 0), 0) := by
  rw [checkRow_act_cnotNetwork_disjoint controls tgt hnd hdisj htnd, checkRow_xGenPauli]
  ext k
  · simp only [cnotNetworkCol, Pi.single_apply]
    have hmap : controls.map (fun c => if k ∈ tgt c then (if c = w then (1 : ZMod 2) else 0) else 0)
        = controls.map (fun c => if c = w then (if k ∈ tgt w then (1 : ZMod 2) else 0) else 0) := by
      apply List.map_congr_left
      intro c _
      by_cases hcw : c = w <;> simp [hcw]
    rw [hmap, sum_map_ite_eq_of_nodup w (if k ∈ tgt w then (1 : ZMod 2) else 0) controls hnd]
    by_cases hw : w ∈ controls <;> by_cases hkw : k ∈ tgt w <;> simp [hw, hkw]
  · simp [cnotNetworkCol]

end AxQM.Concrete
