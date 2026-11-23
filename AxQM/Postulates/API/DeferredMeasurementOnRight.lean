/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeferredMeasurement
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.API.CnotPauliPropagation

/-!
# Deferring a right-factor gate past a right-factor measurement (the `onRight` lift)

The deferred-measurement engine (`DeferredMeasurement.lean`, N&C §4.4 / Exercise 4.35) commutes a
gate `g` past a measurement `m` on a system `S` whenever `Mᵢ g = Wᵢ Mᵢ` (operator commutation).
Nielsen & Chuang's measured quantum Fourier transform (Problem 5.2) measures **every wire** of the
output via a *cascade* `L.cascade M` (`DeferredCascadeMeasurement.lean`): measure the head wire `L`,
then the recursive tail `M`. Deferring a control wire's controlled-`Rₖ` cascade past that terminal
measurement (the `bornProb_evolve_cascade_of_comm` / `postMeasurement_evolve_cascade_of_comm`
engine) needs its two premises — `hL` (the gate defers past the head measurement) and **`hM`** (each
classically-controlled branch gate in turn defers past the *tail* measurement). After the head
deferral the branch gates act on the tail register alone and leave the head wire idle: they are
`onRight`-shaped, `g.onRight qubit = 1 ⊗ g` (identity on the head wire, `g` on the tail), and the
tail measurement is `m.onRight qubit = 1 ⊗ m` (identity on the head wire, the tail measurement `m`
on the rest). This file supplies exactly that `hM`.

Let `S` be the tail register carrying the branch gate `g` and its measurement `m`, and let `T` be
the extra (head) factor left idle. If `g` defers past `m` up to a branch family `W` — `Mᵢ g = Wᵢ Mᵢ`
(`hcomm`) — then the lifted gate `g.onRight T = 1 ⊗ g` defers past the lifted measurement
`m.onRight T = 1 ⊗ m` up to `Wᵢ.onRight T = 1 ⊗ Wᵢ`. Because both liftings are `1 ⊗ (·)`
(`Measurement.onRight_op` / `Evolution.onRight_op`, both `TensorProduct.mapL 1`), the composite
commutation is the base one tensored with the identity on `T`:

  `(1 ⊗ Mᵢ)(1 ⊗ g) = 1 ⊗ (Mᵢ g) = 1 ⊗ (Wᵢ Mᵢ) = (1 ⊗ Wᵢ)(1 ⊗ Mᵢ)`   (`TensorProduct.mapL_comp`).

* `Measurement.op_comp_onRight_of_comm` — the lifted operator commutation, the heart: distributing
  the two `1 ⊗ (·)` composites over `TensorProduct.mapL_comp` and threading `hcomm` through the
  right factor. This is precisely the `hM` premise `op_comp_cascade_of_comm` consumes for a
  right-factor branch gate.
* `Measurement.bornProb_evolve_onRight_of_comm` — the lifted gate is **invisible to the statistics**
  of the lifted measurement (Postulate 3), `p(i ∣ (1⊗g) ρ (1⊗g)†) = p(i ∣ ρ)`.
* `Measurement.postMeasurement_evolve_onRight_of_comm` — the lifted **post-measurement state defers
  the lifted gate** (Postulate 4): `postMeas((1⊗g) ρ (1⊗g)†, i) = (1⊗Wᵢ) · postMeas(ρ, i)`.

The last two are the instances of the single-measurement `bornProb_evolve_of_comm` /
`postMeasurement_evolve_of_comm` at the lifted measurement `m.onRight T`, lifted gate `g.onRight T`
and lifted branch family `i ↦ (W i).onRight T`, whose commutation is `op_comp_onRight_of_comm`.

## Generality

`hcomm` (`Mᵢ g = Wᵢ Mᵢ`) is the exact structural condition the base deferral uses; the conclusions
hold for an arbitrary measurement `m`, gate `g`, branch family `W`, extra factor `T`, and state on
`T ⊗ S`, no dimension specialized.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Lifting a deferral commutation onto the right factor** (operator form). If a gate `g` defers
past a measurement `m` on `S` up to a branch family `W` — `Mᵢ g = Wᵢ Mᵢ` (`hcomm`) — then on the
composite `T ⊗ S` the right-factor gate `g.onRight T = 1 ⊗ g` defers past the right-factor
measurement `m.onRight T = 1 ⊗ m` up to the right-factor branch family `i ↦ (W i).onRight T`:

  `(1 ⊗ Mᵢ)(1 ⊗ g) = 1 ⊗ (Mᵢ g) = 1 ⊗ (Wᵢ Mᵢ) = (1 ⊗ Wᵢ)(1 ⊗ Mᵢ)`.

Both liftings are `TensorProduct.mapL 1` (`Measurement.onRight_op` / `Evolution.onRight_op`), so the
two `1 ⊗ (·)` composites collapse to `1 ⊗ (·)` of a single composite via `TensorProduct.mapL_comp`,
into which `hcomm` is threaded on the right factor. This is the `hM` premise
`op_comp_cascade_of_comm` consumes when a cascade's branch gates leave the head wire idle — the
shape the measured-QFT reduction produces after the head-wire deferral (N&C Problem 5.2). -/
theorem op_comp_onRight_of_comm (m : Measurement ι S) (g : Evolution S) (W : ι → Evolution S)
    (hcomm : ∀ i, (m.op i).comp g.op = (W i).op.comp (m.op i)) (T : QSystem) (i : ι) :
    ((m.onRight T).op i).comp (g.onRight T).op
      = ((W i).onRight T).op.comp ((m.onRight T).op i) := by
  -- The `mapL 1 (·)` liftings compose via `mapL_comp`; abstracting the operators lets keyed
  -- rewriting fire (the composite `1.comp 1` stays on the head factor `T` untouched).
  have key : ∀ (a b c d : S.space →L[ℂ] S.space), a.comp b = c.comp d →
      (TensorProduct.mapL (1 : T.space →L[ℂ] T.space) a).comp
          (TensorProduct.mapL (1 : T.space →L[ℂ] T.space) b)
        = (TensorProduct.mapL (1 : T.space →L[ℂ] T.space) c).comp
          (TensorProduct.mapL (1 : T.space →L[ℂ] T.space) d) := by
    intro a b c d h
    rw [← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp, h]
  simp only [Measurement.onRight_op, Evolution.onRight_op]
  exact key (m.op i) g.op (W i).op (m.op i) (hcomm i)

/-- **A right-factor gate is invisible to the statistics of a right-factor measurement** (Postulate
3). Under the base commutation `Mᵢ g = Wᵢ Mᵢ` (`hcomm`), the Born probability of outcome `i` of the
lifted measurement `m.onRight T` on the lifted-gate-evolved state `(1⊗g) ρ (1⊗g)†` equals that on
`ρ`: the right-factor gate does not affect the right-factor measurement statistics. The instance of
`bornProb_evolve_of_comm` at the lifted measurement, gate and branch family, whose commutation is
`op_comp_onRight_of_comm`. -/
theorem bornProb_evolve_onRight_of_comm (m : Measurement ι S) (g : Evolution S)
    (W : ι → Evolution S) (hcomm : ∀ i, (m.op i).comp g.op = (W i).op.comp (m.op i)) (T : QSystem)
    (ρ : State (T.compose S)) (i : ι) :
    (m.onRight T).bornProb ((g.onRight T).evolve ρ) i = (m.onRight T).bornProb ρ i :=
  bornProb_evolve_of_comm (m.onRight T) (g.onRight T) (fun i => (W i).onRight T)
    (fun i => op_comp_onRight_of_comm m g W hcomm T i) ρ i

/-- **The post-measurement state defers a right-factor gate past a right-factor measurement**
(Postulate 4). Under the base commutation `Mᵢ g = Wᵢ Mᵢ` (`hcomm`), the state after measuring
outcome `i` of the lifted measurement `m.onRight T` on the lifted-gate input `(1⊗g) ρ (1⊗g)†` equals
the lifted branch gate `(W i).onRight T = 1 ⊗ Wᵢ` applied to the state after measuring `ρ`:

  `postMeas((1⊗g) ρ (1⊗g)†, i) = (1 ⊗ Wᵢ) · postMeas(ρ, i)`.

The outcome is equally possible after `1⊗g` because the probabilities agree
(`bornProb_evolve_onRight_of_comm`). The instance of `postMeasurement_evolve_of_comm` at the lifted
measurement, gate and branch family (`op_comp_onRight_of_comm`). This is the collapse reading a
cascade's right-factor branch gate contributes to the measured-QFT semiclassical reduction (N&C
Problem 5.2). -/
theorem postMeasurement_evolve_onRight_of_comm (m : Measurement ι S) (g : Evolution S)
    (W : ι → Evolution S) (hcomm : ∀ i, (m.op i).comp g.op = (W i).op.comp (m.op i)) (T : QSystem)
    (ρ : State (T.compose S)) (i : ι) (hp : (m.onRight T).bornProb ρ i ≠ 0) :
    (m.onRight T).postMeasurement ((g.onRight T).evolve ρ) i
        (by rw [bornProb_evolve_onRight_of_comm m g W hcomm]; exact hp)
      = ((W i).onRight T).evolve ((m.onRight T).postMeasurement ρ i hp) :=
  postMeasurement_evolve_of_comm (m.onRight T) (g.onRight T) (fun i => (W i).onRight T)
    (fun i => op_comp_onRight_of_comm m g W hcomm T i) ρ i hp

end Measurement

end AxQM
