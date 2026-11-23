/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativePhase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Nielsen & Chuang, Exercise 2.65 (relative phase is basis-dependent)

Express (|0>±|1>)/sqrt2 in a basis where not the same up to a relative phase.

**Context (§2.2.7, *Phase*).** Two amplitudes `a`, `b` *differ by a relative phase* if
`a = exp(iθ)b` for some real `θ`; two states *differ by a relative phase in a basis* if each
amplitude of one, in that basis, is `exp(iθ)` times the corresponding amplitude of the other — and,
crucially, the phase `θ` may vary from amplitude to amplitude. In the **computational** basis
`{|0⟩, |1⟩}` the states `|+⟩ = (|0⟩+|1⟩)/√2` and `|-⟩ = (|0⟩-|1⟩)/√2` *do* differ by a relative
phase: their `|0⟩` amplitudes are identical (phase `1`) and their `|1⟩` amplitudes differ by a
factor `-1 = exp(iπ)`. This is exactly why relative phase is a *basis-dependent* notion. The
exercise asks for a basis where that fails; the natural answer is `{|+⟩, |-⟩}` itself (an
orthonormal basis of the qubit),
in which `|+⟩` and `|-⟩` become distinct basis vectors with amplitudes `(1, 0)` and `(0, 1)` — of
manifestly different magnitude, so no per-amplitude phase factor can relate them.

The statement is for pure states, using
`PureState.RelativePhaseEquiv` (N&C's relative-phase-in-a-basis relation, modelling a
"basis" as a family of pure states `Fin 2 → PureState qubit`):

* `qubitPlus_qubitMinus_relativePhaseEquiv_qubitBasis` — in the computational basis `qubitBasis`,
  `|+⟩` and `|-⟩` **do** differ by a relative phase (phase `1` on `|0⟩`, phase `π` on `|1⟩`).
* `plusMinusFrame` — the frame `⟨|+⟩, |-⟩⟩`, i.e. N&C's answer basis.
* `not_qubitPlus_qubitMinus_relativePhaseEquiv_plusMinusFrame` — in the `{|+⟩, |-⟩}` basis they are
  **not** relative-phase equivalent (the required amplitude-magnitude equality `1 = 0` fails).

The `|±⟩` states `qubitPlus`/`qubitMinus`, the relation `PureState.RelativePhaseEquiv` and its
amplitude-magnitude fingerprint `RelativePhaseEquiv.norm_inner_eq`, and the amplitude lemmas are in
`AxQM/Postulates/API/RelativePhase.lean`.
-/

open scoped InnerProductSpace

namespace AxQM

/-- **In the computational basis `{|0⟩, |1⟩}`, `|+⟩` and `|-⟩` differ by a relative phase.** For
each computational basis direction there is a phase `θ` with `⟨i|+⟩ = exp(iθ)⟨i|-⟩`: `θ = 0` on
`|0⟩` (the `|0⟩` amplitudes `1/√2` coincide) and `θ = π` on `|1⟩` (the `|1⟩` amplitudes `±1/√2`
differ by `-1 = exp(iπ)`). This is the setup of N&C Exercise 2.65 — the two states *look* phase
related in the standard basis, which is why the exercise must change basis. -/
theorem qubitPlus_qubitMinus_relativePhaseEquiv_qubitBasis :
    PureState.RelativePhaseEquiv qubitBasis qubitPlus qubitMinus := by
  intro i
  fin_cases i
  · refine ⟨0, ?_⟩
    rw [inner_qubitBasis_qubitPlus, inner_qubitBasis_qubitMinus]
    simp [Concrete.xPlus, Concrete.xMinus]
  · refine ⟨Real.pi, ?_⟩
    rw [inner_qubitBasis_qubitPlus, inner_qubitBasis_qubitMinus, Complex.exp_pi_mul_I]
    simp [Concrete.xPlus, Concrete.xMinus]

/-- The frame `⟨|+⟩, |-⟩⟩` — the orthonormal basis `{|+⟩, |-⟩}` of the qubit, as a family of pure
states. This is the basis N&C asks for: the one in which `|+⟩` and `|-⟩` are *not* relative-phase
equivalent. -/
noncomputable def plusMinusFrame : Fin 2 → PureState qubit := ![qubitPlus, qubitMinus]

/-- **Nielsen & Chuang, Exercise 2.65 (the answer).** In the basis `{|+⟩, |-⟩}`, the states `|+⟩`
and `|-⟩` are **not** the same up to a relative phase shift. If they were relative-phase equivalent
in this frame, then (by `RelativePhaseEquiv.norm_inner_eq`) their amplitude magnitudes in the `|+⟩`
direction would agree — but `|⟨+|+⟩| = 1` while `|⟨+|-⟩| = 0`, a contradiction. Physically: in its
own basis `|+⟩` has amplitudes `(1, 0)` and `|-⟩` has `(0, 1)`, whose magnitudes differ, so no
per-amplitude phase can relate them. -/
theorem not_qubitPlus_qubitMinus_relativePhaseEquiv_plusMinusFrame :
    ¬ PureState.RelativePhaseEquiv plusMinusFrame qubitPlus qubitMinus := by
  intro h
  have key := h.norm_inner_eq 0
  simp only [plusMinusFrame, Matrix.cons_val_zero, inner_qubitPlus_self,
    inner_qubitPlus_qubitMinus] at key
  simp at key

end AxQM
