/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingCnotNetworkClosedForm

/-!
# Concrete: the two-stage CNOT engine of the encoding circuit (N&C, Problem 10.3)

This file continues the **synthesis** half of Nielsen & Chuang **Problem 10.3** ("encoding
stabilizer codes"), packaging the *composition* of two CNOT networks into the reusable engine that
the final assembly — carrying the trivial check matrix `G` (10.124) to the standard form (10.125) —
evaluates on each seed row.

## Why two stages

The full CNOT layer of the encoding circuit is **not** a disjoint network, so the single closed
form `checkRow_act_cnotNetwork_disjoint` (`Concrete/PauliStringEncodingCnotNetworkClosedForm.lean`)
does not apply to it directly: the **pivot** controls fan onto the **data** wires (their `A₂`
support), and those very data wires are *also* controls (of the `E`-fans onto the middle wires). A
control that is another fan's target breaks the disjointness hypothesis. The resolution is to write
the control list as `piv ++ dat` and read the network as a **composition** of two networks that are
each internally disjoint:

* the **data** stage `cnotNetwork dat tgt` (the `E`-fans, controls `dat`, targets in the middle
  wires) — disjoint because `dat` wires are never middle wires;
* the **pivot** stage `cnotNetwork piv tgt` (controls `piv`, targets in the middle/data wires) —
  disjoint because `piv` wires are never middle or data wires.

Because `act` reads an append right-to-left (`act (U ++ V) g = act U (act V g)`,
`CliffordCircuit.act_append`) and `cnotNetwork` distributes over `++` on its control list
(`cnotNetwork_append`), the **data** stage (the tail) acts **first** and the **pivot** stage acts on
its output. This ordering is the crux: the data stage deposits
the `E`-block on the middle rows, and the pivot stage then *reads the just-deposited `E`* off the
data columns, injecting the `E A₂ᵀ` cross-term into the middle rows' `D`-block — the standard-form
relation `D = A₁ᵀ + E A₂ᵀ` (10.125).

## What this file delivers

* `cnotNetwork_append` — the network of a concatenated control list is the concatenation of the two
  sub-networks: `cnotNetwork (front ++ back) tgt = cnotNetwork front tgt ++ cnotNetwork back tgt`.
* `checkRow_act_cnotNetwork_split_zGenPauli` — the composite action on a pure-`Z` seed row `Z_w`
  (a row of `G` (10.124)): the `back` stage deposits its transpose/`E` bits (`checkRow`
  `(0, e_w + Σ_{c ∈ back, w ∈ tgt c} e_c)`), and the `front` stage then applies its own closed-form
  column operation `cnotNetworkCol front tgt` **to that deposited row** — so the front reads pick up
  the back deposits. This is the engine building the middle rows `[D I E]` (with the `E A₂ᵀ`
  cross-term) and the data rows `[A₂ᵀ 0 I]` of (10.125).
* `checkRow_act_cnotNetwork_split_xGenPauli` — the composite action on a pure-`X` seed row `X_w`
  (a top row after the Hadamard layer): symmetrically, `cnotNetworkCol front tgt` applied to the
  `back`-spread `X`-row `(e_w + Σ_{k ∈ tgt w} e_k, 0)` (when `w ∈ back`; just `(e_w, 0)` when
  `w ∉ back`). This is the engine building the top rows' `X`-blocks `[I A₁ A₂]`.

Each is a direct composition of the single-network lemmas
(`checkRow_act_cnotNetwork_disjoint` for the outer/front stage and
`checkRow_act_cnotNetwork_disjoint_zGenPauli` /
`checkRow_act_cnotNetwork_disjoint_xGenPauli` for the inner/back seed), and requires only that the
two control lists be **internally** disjoint — `front` need not be disjoint from `back` (indeed it
is not: that non-disjointness is precisely the `E A₂ᵀ` coupling).

-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- **The CNOT network of a concatenated control list splits as an appended circuit**:
`cnotNetwork (front ++ back) tgt = cnotNetwork front tgt ++ cnotNetwork back tgt`. Immediate from
the definition `cnotNetwork controls tgt = controls.flatMap (fun c => cnotFan c (tgt c))` and the
library lemma `List.flatMap_append` (mirroring the sibling `cnotNetwork_cons`, which reads off
`List.flatMap_cons`). Combined with `CliffordCircuit.act_append`, this lets the encoding assembly
read the full CNOT layer as the pivot stage acting on the output of the (innermost) data/`E`-fan
stage. -/
theorem cnotNetwork_append (front back : List (Fin n)) (tgt : Fin n → List (Fin n)) :
    cnotNetwork (front ++ back) tgt = cnotNetwork front tgt ++ cnotNetwork back tgt := by
  simp only [cnotNetwork, List.flatMap_append]

/-- **The two-stage CNOT network on a pure-`Z` seed row** `Z_w` (a row of the trivial check matrix
`G` (10.124), check row `(0 | e_w)`). Writing the control list as `front ++ back`, the network acts
as the `front` stage composed after the `back` stage (`back` innermost). Under the sole hypothesis
that each control list is **internally disjoint** from its own target lists (so each stage is a
disjoint network — `front` and `back` need *not* be disjoint from each other), the composite check
row is the `front` stage's closed-form column operation `cnotNetworkCol front tgt` applied to the
`back` stage's deposited row `(0, fun k => [k = w] + [k ∈ back ∧ w ∈ tgt k])`.

Concretely: the `back` stage (e.g. the `E`-fans, data controls onto middle targets) deposits a `Z`
on `w` itself and on every `back` control whose fan reaches `w`; the `front` stage (the pivot fans)
then reads *that* row — so a pivot fan reaching a data column that the `back` stage marked picks up
the `E`-contribution, producing the `E A₂ᵀ` cross-term of the standard-form block
`D = A₁ᵀ + E A₂ᵀ`. Proof: `cnotNetwork_append` + `CliffordCircuit.act_append` reduce to the two
single-network lemmas `checkRow_act_cnotNetwork_disjoint` (front) and
`checkRow_act_cnotNetwork_disjoint_zGenPauli` (back). -/
theorem checkRow_act_cnotNetwork_split_zGenPauli (front back : List (Fin n))
    (tgt : Fin n → List (Fin n)) (hfnd : front.Nodup)
    (hfdisj : ∀ a ∈ front, ∀ b ∈ front, a ∉ tgt b) (hftnd : ∀ c ∈ front, (tgt c).Nodup)
    (hbnd : back.Nodup) (hbdisj : ∀ a ∈ back, ∀ b ∈ back, a ∉ tgt b)
    (hbtnd : ∀ c ∈ back, (tgt c).Nodup) (w : Fin n) :
    checkRow ((cnotNetwork (front ++ back) tgt).act (zGenPauli w))
      = cnotNetworkCol front tgt
          (0, fun k => (if k = w then (1 : ZMod 2) else 0)
            + (if k ∈ back ∧ w ∈ tgt k then 1 else 0)) := by
  rw [cnotNetwork_append, CliffordCircuit.act_append,
    checkRow_act_cnotNetwork_disjoint front tgt hfnd hfdisj hftnd,
    checkRow_act_cnotNetwork_disjoint_zGenPauli back tgt hbnd hbdisj hbtnd w]

/-- **The two-stage CNOT network on a pure-`X` seed row** `X_w` (a top row entering the CNOT layer
after the Hadamard layer, check row `(e_w | 0)`). Symmetrically to the `Z` case, the composite check
row is `cnotNetworkCol front tgt` applied to the `back` stage's spread `X`-row
`(fun k => [k = w] + [w ∈ back ∧ k ∈ tgt w], 0)`: the `back` stage spreads `w`'s `X`-bit onto
`tgt w` if `w` is a `back` control (otherwise leaves `X_w` alone), and the `front` (pivot) stage
then spreads further, building the top rows' `X`-blocks `[I A₁ A₂]` of (10.125). Proof: same
composition as the `Z` case, using `checkRow_act_cnotNetwork_disjoint_xGenPauli` for the inner
seed. -/
theorem checkRow_act_cnotNetwork_split_xGenPauli (front back : List (Fin n))
    (tgt : Fin n → List (Fin n)) (hfnd : front.Nodup)
    (hfdisj : ∀ a ∈ front, ∀ b ∈ front, a ∉ tgt b) (hftnd : ∀ c ∈ front, (tgt c).Nodup)
    (hbnd : back.Nodup) (hbdisj : ∀ a ∈ back, ∀ b ∈ back, a ∉ tgt b)
    (hbtnd : ∀ c ∈ back, (tgt c).Nodup) (w : Fin n) :
    checkRow ((cnotNetwork (front ++ back) tgt).act (xGenPauli w))
      = cnotNetworkCol front tgt
          (fun k => (if k = w then (1 : ZMod 2) else 0)
            + (if w ∈ back ∧ k ∈ tgt w then 1 else 0), 0) := by
  rw [cnotNetwork_append, CliffordCircuit.act_append,
    checkRow_act_cnotNetwork_disjoint front tgt hfnd hfdisj hftnd,
    checkRow_act_cnotNetwork_disjoint_xGenPauli back tgt hbnd hbdisj hbtnd w]

end AxQM.Concrete
