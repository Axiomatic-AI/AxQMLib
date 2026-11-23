/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CascadedMeasurement
import AxQM.Postulates.API.DeferredMeasurement

/-!
# Deferring a gate past a *cascade* of measurements (the recursive deferred-measurement step)

The deferred-measurement engine (`DeferredMeasurement.lean`, N&C §4.4 / Exercise 4.35) commutes a
gate past a **single** measurement `m`: if each operator `Mᵢ` of `m` satisfies `Mᵢ V = Wᵢ Mᵢ`, then
measuring `m` after `V` is measuring `m` first and then applying the branch gate `Wᵢ`. Nielsen &
Chuang's measured quantum Fourier transform (Problem 5.2) measures **every wire** of the output;
that terminal measurement is a *cascade* (`Measurement.cascade`, N&C Exercise 2.57) — measure head
wire, then the recursive tail — so its reduction must defer a gate past a cascade of measurements,
one measured factor at a time.

This file supplies that composition law. Let `L.cascade M` be the cascade "measure `L` (outcomes
`κ`), then `M` (outcomes `μ`)", with operators `N₍ᵢ,ᵣ₎ = Mᵣ Lᵢ`. If a gate `V` defers past the head
measurement `L` — `Lᵢ V = Wᵢ Lᵢ` (`hL`) — **and** each head-branch gate `Wᵢ` in turn defers past the
tail measurement `M` — `Mᵣ Wᵢ = W'ᵢᵣ Mᵣ` (`hM`) — then `V` defers past the whole cascade
`L.cascade M`, with branch family `W'ᵢᵣ`:

  `N₍ᵢ,ᵣ₎ V = Mᵣ Lᵢ V = Mᵣ Wᵢ Lᵢ = W'ᵢᵣ Mᵣ Lᵢ = W'ᵢᵣ N₍ᵢ,ᵣ₎`.

* `Measurement.op_comp_cascade_of_comm` — the composed commutation, the heart: threading `hL` then
  `hM` through `cascade_op` and associativity of composition.
* `Measurement.bornProb_evolve_cascade_of_comm` — the **joint outcome probabilities are unchanged**
  under the deferred gate (Postulate 3), `p((i,r) ∣ V ρ V†) = p((i,r) ∣ ρ)`.
* `Measurement.postMeasurement_evolve_cascade_of_comm` — the **joint post-measurement state defers
  the gate** (Postulate 4): the collapsed state after measuring the cascade on `V ρ V†` equals
  `W'ᵢᵣ` applied to the collapsed state after measuring `ρ`.

The last two are the instances of the single-measurement `bornProb_evolve_of_comm` /
`postMeasurement_evolve_of_comm` at the cascade measurement `L.cascade M`, gate `V` and branch
family `(i,r) ↦ W'ᵢᵣ`, whose commutation hypothesis is `op_comp_cascade_of_comm`.

## Why this is the recursive step

The terminal all-wire measurement of the measured QFT is built head-first as
`qtowerMeasurement (n+1) = cascade (controlMeasurement head) (tail measurement)` (N&C Problem 5.2).
A control wire's controlled-`Rₖ` cascade defers past the head-wire measurement `controlMeasurement`
alone (`hL`, with `Wᵢ` the classically-controlled single-wire branch gates). This law composes that
head deferral with the tail: once each branch gate defers past the tail measurement (`hM`), the
control cascade defers past the *whole* terminal measurement. Applied along the tower recursion it
is the engine of the semiclassical induction, deferring the measurement wire by wire.

## Generality

`hL` and `hM` are the exact structural conditions the two deferrals use; the conclusions hold for an
arbitrary head measurement `L`, tail measurement `M`, gate `V`, and branch families `W` / `W'`, no
dimension specialized.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {κ μ : Type*} [Fintype κ] [Fintype μ] {S : QSystem}

namespace Measurement

/-- **Deferring a gate past a cascade of two measurements** (operator form). If a gate `V` defers
past the head measurement `L` up to a head-branch family `W` — `Lᵢ V = Wᵢ Lᵢ` (`hL`) — and each
head-branch gate `Wᵢ` defers past the tail measurement `M` up to a family `W'ᵢ` —
`Mᵣ Wᵢ = W'ᵢᵣ Mᵣ` (`hM`) — then `V` defers past the cascade measurement `L.cascade M` (operators
`N₍ᵢ,ᵣ₎ = Mᵣ Lᵢ`) up to `W'ᵢᵣ`:

  `N₍ᵢ,ᵣ₎ V = Mᵣ Lᵢ V = Mᵣ Wᵢ Lᵢ = W'ᵢᵣ Mᵣ Lᵢ = W'ᵢᵣ N₍ᵢ,ᵣ₎`.

Threads `hL` (on the head factor `Lᵢ`) then `hM` (on the tail factor `Mᵣ`) through the cascade
operator `cascade_op` and associativity of `ContinuousLinearMap.comp`. This is the commutation the
cascade Born-rule and collapse readings below consume. -/
theorem op_comp_cascade_of_comm (L : Measurement κ S) (M : Measurement μ S)
    (V : Evolution S) (W : κ → Evolution S) (W' : κ → μ → Evolution S)
    (hL : ∀ i, (L.op i).comp V.op = (W i).op.comp (L.op i))
    (hM : ∀ i r, (M.op r).comp (W i).op = (W' i r).op.comp (M.op r)) (i : κ) (r : μ) :
    ((L.cascade M).op (i, r)).comp V.op = (W' i r).op.comp ((L.cascade M).op (i, r)) := by
  simp only [cascade_op]
  rw [ContinuousLinearMap.comp_assoc, hL i, ← ContinuousLinearMap.comp_assoc, hM i r,
    ContinuousLinearMap.comp_assoc]

/-- **Joint outcome probabilities are unchanged when a gate is deferred past a cascade measurement**
(Postulate 3). Under the two commutations `Lᵢ V = Wᵢ Lᵢ` (`hL`) and `Mᵣ Wᵢ = W'ᵢᵣ Mᵣ` (`hM`), the
Born probability of the joint outcome `(i, r)` of `L.cascade M` on the evolved state `V ρ V†` equals
that on `ρ`: the cascade measurement's statistics do not see the gate `V`. The instance of
`bornProb_evolve_of_comm` at the cascade measurement, gate `V` and branch family `(i,r) ↦ W'ᵢᵣ`,
whose commutation is `op_comp_cascade_of_comm`. -/
theorem bornProb_evolve_cascade_of_comm (L : Measurement κ S) (M : Measurement μ S)
    (V : Evolution S) (W : κ → Evolution S) (W' : κ → μ → Evolution S)
    (hL : ∀ i, (L.op i).comp V.op = (W i).op.comp (L.op i))
    (hM : ∀ i r, (M.op r).comp (W i).op = (W' i r).op.comp (M.op r))
    (ρ : State S) (p : κ × μ) :
    (L.cascade M).bornProb (V.evolve ρ) p = (L.cascade M).bornProb ρ p :=
  bornProb_evolve_of_comm (L.cascade M) V (fun p => W' p.1 p.2)
    (fun p => op_comp_cascade_of_comm L M V W W' hL hM p.1 p.2) ρ p

/-- **The joint post-measurement state defers the gate past a cascade measurement** (Postulate 4).
Under the two commutations `Lᵢ V = Wᵢ Lᵢ` (`hL`) and `Mᵣ Wᵢ = W'ᵢᵣ Mᵣ` (`hM`), the state after
measuring the joint outcome `(i, r)` of `L.cascade M` on the evolved input `V ρ V†` equals the
branch gate `W'ᵢᵣ` applied to the state after measuring `ρ`:

  `postMeas(V ρ V†, (i,r)) = W'ᵢᵣ · postMeas(ρ, (i,r))`.

The joint outcome is equally possible after `V` because the probabilities agree
(`bornProb_evolve_cascade_of_comm`). The instance of `postMeasurement_evolve_of_comm` at the cascade
measurement, gate `V` and branch family `(i,r) ↦ W'ᵢᵣ`, whose commutation is
`op_comp_cascade_of_comm`. -/
theorem postMeasurement_evolve_cascade_of_comm (L : Measurement κ S) (M : Measurement μ S)
    (V : Evolution S) (W : κ → Evolution S) (W' : κ → μ → Evolution S)
    (hL : ∀ i, (L.op i).comp V.op = (W i).op.comp (L.op i))
    (hM : ∀ i r, (M.op r).comp (W i).op = (W' i r).op.comp (M.op r))
    (ρ : State S) (p : κ × μ) (hp : (L.cascade M).bornProb ρ p ≠ 0) :
    (L.cascade M).postMeasurement (V.evolve ρ) p
        (by rw [bornProb_evolve_cascade_of_comm L M V W W' hL hM]; exact hp)
      = (W' p.1 p.2).evolve ((L.cascade M).postMeasurement ρ p hp) :=
  postMeasurement_evolve_of_comm (L.cascade M) V (fun p => W' p.1 p.2)
    (fun p => op_comp_cascade_of_comm L M V W W' hL hM p.1 p.2) ρ p hp

end Measurement

end AxQM
