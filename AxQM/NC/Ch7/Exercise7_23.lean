/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PhaseShiftPauliZ
import AxQM.NC.Ch4.Exercise4_17

/-!
# Nielsen & Chuang, Exercise 7.23 (a universal two-qubit gate from the optical Kerr gate)

Show the two-qubit gate (7.87) plus single-qubit ops realizes a controlled-NOT for any φ_a,φ_b, Δ=π.

(N&C p. 308, §7.5.4.) In the cavity-QED optical logic gate, two light modes (a *probe* and a *pump*)
interact through a single atom acting as a Kerr medium. The end effect (N&C p. 307) is that a photon
in mode `a` picks up a single-photon phase `e^{iϕ_a}`, a photon in mode `b` picks up `e^{iϕ_b}`, and
the two-photon state `|11⟩` picks up an *additional* Kerr phase `Δ`. On the two-qubit computational
basis `|00⟩, |01⟩, |10⟩, |11⟩` this is the diagonal gate (7.87)

`U = diag(1, e^{iϕ_a}, e^{iϕ_b}, e^{i(ϕ_a + ϕ_b + Δ)})`.

The exercise asks to show that, at the "hard" Kerr value `Δ = π`, this gate together with arbitrary
single-qubit operations realises a controlled-`NOT` — the missing ingredient for universal quantum
computation with single photons.

The gate (7.87), the single-qubit corrections, the Hadamards and `CNOT` are all closed-system
evolutions (Postulate 2 / `Evolution`); the exercise is a *circuit identity* between these gate
objects. The faithful statement is therefore an equality of `Evolution`s, built from gates and
gate composition (`Evolution.comp`, `Evolution.onLeft/onRight`).

## The formalisation

* `opticalKerrGate ϕ_a ϕ_b Δ` — **the gate (7.87)** as an `Evolution` on `qubit ⊗ qubit`, defined,
  exactly as N&C's physical model prescribes, as the composition of the two single-photon phase
  shifts `P(ϕ_b) ⊗ 1` and `1 ⊗ P(ϕ_a)` with the controlled Kerr phase `C(P(Δ))`. Its diagonal in
  the computational basis is `diag(1, e^{iϕ_a}, e^{iϕ_b}, e^{i(ϕ_a + ϕ_b + Δ)})`, i.e. (7.87).
* `opticalKerrGate_dressed_eq_controlledPhaseShift` — **the gate is a dressed controlled phase.**
  Undoing the single-photon phases with `P(-ϕ_b) ⊗ 1` and `1 ⊗ P(-ϕ_a)` leaves exactly the
  controlled phase `C(P(Δ))`. This certifies that `opticalKerrGate` is (7.87) up to local phases and
  is the key algebraic step: single-qubit gates strip the `ϕ_a, ϕ_b` parts, isolating the Kerr
  phase `Δ`.
* `cnotGate_eq_singleQubit_conj_opticalKerrGate` — **Exercise 7.23:** for any `ϕ_a, ϕ_b` and
  `Δ = π`,

  `CNOT = (1 ⊗ H) · [(P(-ϕ_b) ⊗ 1) · (1 ⊗ P(-ϕ_a)) · U] · (1 ⊗ H)`,

  a full equality of gate `Evolution`s. Every factor other than `U = opticalKerrGate ϕ_a ϕ_b π` is a
  single-qubit gate (`P(·)`, `H`) placed on one wire via `Evolution.onLeft/onRight` — so the
  right-hand side is `U` "augmented with arbitrary single qubit operations", and it equals `CNOT`.

## Design notes

* **Why this shape.** The claim is a genuine equality of the gate
  `Evolution`s, holding on every input as a full unitary identity — not an "up to global phase" or
  "on basis states" surrogate. The single-qubit augmentation is exhibited *explicitly* (the exact
  correction phases and Hadamards), which is stronger than the bare existential "there exist
  single-qubit gates …" the exercise literally asks for; the explicit form makes the
  single-qubit-only nature manifest (each factor is `g.onLeft`/`g.onRight` of a one-qubit `g`). The
  gate `opticalKerrGate` is defined as the composition N&C itself gives on p. 307 (single-photon
  phases + Kerr phase), and `opticalKerrGate_dressed_eq_controlledPhaseShift` certifies that this is
  the diagonal gate (7.87): stripping the single-photon phases returns the pure controlled Kerr
  phase.
* **Proof.** Two moves. (1) `opticalKerrGate_dressed_eq_controlledPhaseShift` reduces the dressed
  gate to `C(P(π))` — proved on the four computational-basis inputs (`twoQubit_evolution_ext`), the
  single-photon phases telescoping away via `P(-α) · P(α) = 1`
  (`phaseShiftGate_neg_comp_self`). (2) At `Δ = π` the controlled phase is a controlled-`Z`
  (`controlledPhaseShift_pi_eq_controlledZGate`, i.e. `e^{iπ} = -1`), and a controlled-`Z` with its
  target conjugated by Hadamards is a `CNOT` (`cnotGate_eq_hadamard_conj_controlledZGate`, N&C
  Exercise 4.17). The `Δ = π` restriction is essential: only there is the conditional phase a
  `Z`, letting the two Hadamards turn it into a bit flip; N&C notes the gate is universal for nearly
  any `Δ`, but the clean `CNOT` reduction is the `Δ = π` case.
* **Reused / shared components.** The phase-gate algebra (`P(-α) · P(α) = 1`, `P(π) = Z`,
  `C(P(π)) = CZ`) is factored into `AxQM/Postulates/API/PhaseShiftPauliZ.lean` as reusable
  lemmas; the `CZ`-to-`CNOT` identity is Exercise 4.17. This file only introduces the gate (7.87)
  and assembles these.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The two-qubit optical logic gate (7.87)** of Nielsen & Chuang §7.5.4, as an `Evolution` on
`qubit ⊗ qubit`. Following N&C's physical model (p. 307) — a probe photon acquires the phase
`e^{iϕ_a}`, a pump photon acquires `e^{iϕ_b}`, and the two-photon state acquires an additional Kerr
phase `Δ` — it is the composition of the single-photon phase shifts `P(ϕ_b) ⊗ 1` (on the left/pump
wire) and `1 ⊗ P(ϕ_a)` (on the right/probe wire) with the controlled Kerr phase `C(P(Δ))`. In the
computational basis this is the diagonal gate
`diag(1, e^{iϕ_a}, e^{iϕ_b}, e^{i(ϕ_a + ϕ_b + Δ)})`, i.e. the matrix (7.87). -/
def opticalKerrGate (φa φb Δ : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((phaseShiftGate φb).onLeft qubit).comp
    (((phaseShiftGate φa).onRight qubit).comp (controlledPhaseShift Δ))

/-- **The optical Kerr gate (7.87) is a single-photon-phase-dressed controlled phase gate.** Undoing
the two single-photon phases — applying `P(-ϕ_b) ⊗ 1` on the pump wire and `1 ⊗ P(-ϕ_a)` on the
probe wire — turns `opticalKerrGate ϕ_a ϕ_b Δ` into the bare controlled Kerr phase `C(P(Δ))`:

`(P(-ϕ_b) ⊗ 1) · (1 ⊗ P(-ϕ_a)) · opticalKerrGate ϕ_a ϕ_b Δ = C(P(Δ))`.

This both certifies that `opticalKerrGate` is the diagonal gate (7.87) (up to the local phases) and
isolates the physically essential Kerr phase `Δ`. Proved on the four computational-basis inputs
(`twoQubit_evolution_ext`), the single-photon phases telescoping via `P(-α) · P(α) = 1`. -/
theorem opticalKerrGate_dressed_eq_controlledPhaseShift (φa φb Δ : ℝ) :
    ((phaseShiftGate (-φb)).onLeft qubit).comp
        (((phaseShiftGate (-φa)).onRight qubit).comp (opticalKerrGate φa φb Δ))
      = controlledPhaseShift Δ := by
  apply twoQubit_evolution_ext
  intro q1 q2
  simp only [opticalKerrGate, controlledPhaseShift_eq, Evolution.evolvePure_comp]
  fin_cases q1 <;>
    (simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, controlledUnitary_evolvePure_ketZero,
        controlledUnitary_evolvePure_ketOne, Evolution.onLeft_evolvePure,
        Evolution.onRight_evolvePure]
     refine congrArg₂ PureState.tmul ?_ ?_ <;>
       rw [← Evolution.evolvePure_comp, phaseShiftGate_neg_comp_self, Evolution.id_evolvePure])

/-- **Nielsen & Chuang, Exercise 7.23: the optical gate (7.87) plus single-qubit operations realises
a `CNOT`.** For any single-photon phases `ϕ_a, ϕ_b` and the Kerr value `Δ = π`,

`CNOT = (1 ⊗ H) · [(P(-ϕ_b) ⊗ 1) · (1 ⊗ P(-ϕ_a)) · opticalKerrGate ϕ_a ϕ_b π] · (1 ⊗ H)`,

a full equality of gate `Evolution`s. Every factor besides `opticalKerrGate ϕ_a ϕ_b π` is a
single-qubit gate placed on one wire (`Evolution.onLeft`/`onRight`): the Hadamards `1 ⊗ H` and the
correction phases `P(-ϕ_b) ⊗ 1`, `1 ⊗ P(-ϕ_a)`. Thus the two-qubit gate (7.87), augmented with
arbitrary single-qubit operations, realises a controlled-`NOT`.

The correction phases strip the single-photon phases, leaving the controlled Kerr phase `C(P(π))`
(`opticalKerrGate_dressed_eq_controlledPhaseShift`); at `Δ = π` that is a controlled-`Z`
(`controlledPhaseShift_pi_eq_controlledZGate`), whose target conjugated by Hadamards is a `CNOT`
(`cnotGate_eq_hadamard_conj_controlledZGate`, Exercise 4.17). -/
theorem cnotGate_eq_singleQubit_conj_opticalKerrGate (φa φb : ℝ) :
    cnotGate = (hadamardGate.onRight qubit).comp
      ((((phaseShiftGate (-φb)).onLeft qubit).comp
            (((phaseShiftGate (-φa)).onRight qubit).comp (opticalKerrGate φa φb Real.pi))).comp
        (hadamardGate.onRight qubit)) := by
  rw [opticalKerrGate_dressed_eq_controlledPhaseShift, controlledPhaseShift_pi_eq_controlledZGate]
  exact cnotGate_eq_hadamard_conj_controlledZGate

end AxQM
