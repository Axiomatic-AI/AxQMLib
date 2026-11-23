/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.NmrTomographyReconstruction

/-!
# Nielsen & Chuang, Exercise 7.45 (State tomography with NMR)

State tomography with NMR: show nine experiments (given M_k rotations) suffice to reconstruct
two-spin ρ. (§7.7.4, p. 336.)

*State tomography* is the ability to measure a quantum computer's density matrix (§7.7.4). N&C
recall (eq. 7.166–7.168) that a state is reconstructed from the expectation values of the Pauli
observables, `ρ = ½(I + Σₖ rₖ σₖ)` with `rₖ = ⟨σₖ⟩ = tr(ρ σₖ)`, "Similar results hold for larger
numbers of spins"; in practice one measures the traceless *deviation density matrix* (the
non-identity Pauli expectations). The exercise's nine experiments provide, through their
pre-rotations `Mₖ` and the coupled-spin readout, exactly these expectations, so `ρ` is determined.

## What is formalised, and where

The exercise's content splits into a **reconstruction** engine (`ρ` is fixed by its Pauli
expectations) and a **readout covering** (the nine experiments' data are those expectations). Both
are stated in this file, in terms of `State.expectation`:

* `twoSpin_state_eq_of_expectation_pauliString_eq` — **the reconstruction claim**: two states of the
  four-dimensional two-qubit register `qudit (2²)` with equal expectation values `⟨P_g⟩` of every
  **non-identity** Pauli-string observable `P_g = pauliStringHamiltonian g 1` (`g : Fin 2 → Fin 4`,
  `g ≠ 0` — the `4² − 1 = 15` non-identity two-qubit Pauli strings) are equal. This is "the measured
  expectations suffice to reconstruct `ρ`" (eq. 7.166–7.168): the `15` non-identity expectations
  plus the fixed normalisation `tr ρ = 1` (N&C's traceless deviation density matrix) determine `ρ`.

* `twoSpin_state_eq_of_expectation_nineExperiments` (below) — **the nine-experiment claim**: two
  states of `qudit (2²)` that agree on `⟨P_g⟩` for every Pauli string `g` **observed by some of the
  nine experiments** are equal. The nine experiments are the settings `s : Fin 2 → Fin 3`
  (`Fintype.card (Fin 2 → Fin 3) = 9`, `Concrete.nmrTomographyExperiments_two`), i.e. the
  `{I, R_x, R_y}²` pre-rotation grid `M₀ = I, M₁ = R_{x1}, M₂ = R_{y1}, M₃ = R_{x2},
  M₄ = R_{x2}R_{x1}, …` of the exercise — spin `i` measured, by its pre-pulse, in one of three bases
  `{Z, Y, X}`. This
  family is tomographically complete (`Concrete.tomographyComplete_univ`), so its observed strings
  cover all `15` non-identity Paulis and the reconstruction applies: **the nine experiments provide
  sufficient data from which `ρ` is reconstructed** — the exercise's conclusion.

Supporting results (used here, in terms of `Matrix` and `trace`):

* `AxQM.State.eq_of_expectation_pauliString_of_tomographyComplete`
  (`AxQM/Core/NmrTomographyReconstruction.lean`) — the `n`-spin reconstruction from **any**
  tomographically complete family of settings, grounded in `State.expectation`; the nine-experiment
  headline is its
  `n = 2`, `T = univ` instance.
* `AxQM.State.eq_of_expectation_pauliStringHamiltonian_eq`
  (`AxQM/Core/PauliTomographyExpectation.lean`) — the underlying reconstruction principle for `n`
  spins.
* `AxQM.Concrete.TomographyComplete` / `SettingObserves` / `tomographyComplete_univ`
  (`AxQM/Concrete/NmrTomographyExperimentCount.lean`, from Exercise 7.46) — the combinatorial
  covering: a *setting* is a per-spin basis choice `Fin n → Fin 3`, it *observes* a Pauli string
  when each non-identity factor matches that spin's basis, and the full family of all `3ⁿ` settings
  observes every string.
* `AxQM.State.expectation_pauliStringHamiltonian` and `State.pauliMatrix`
  (`AxQM/Postulates/API/PauliTomographyExpectation.lean`) — the (7.168) bridge
  `⟨P_g⟩_ρ = Re tr(P_g ρ)`.
* `AxQM.Concrete.eq_of_trace_eq_of_trace_pauliString_eq`
  (`AxQM/Concrete/PauliTomography.lean`) — the matrix uniqueness underlying the
  reconstruction.

## Fidelity and readout model

The reconstruction is the operational core of "`ρ` can be reconstructed" and is faithful (the `15`
non-identity Pauli expectations, no weakening — a general uniqueness over all states, not a special
case). The nine-experiment covering completes the exercise's *count*: the nine `Mₖ` (the
`{I, R_x, R_y}` grid on the two spins) rotate all `15` non-identity Pauli strings into the readable
set, so their observed expectations determine `ρ`.

The readout `Vₖ(t)` is modelled at
the **observable level**: that experiment `k`, through its pre-rotation `Mₖ` and the `J`-coupled
transverse-magnetisation readout `iXₖ + Yₖ` (the `nmrTransverseReadout` / `nmrReadout_heisenberg`
infrastructure of `AxQM/Postulates/API/NMRCoupledSpinFID.lean`), delivers the expectation values of
the pre-rotated single-quantum-coherence observables it resolves is *posited* — abstracting the
time-domain spectral resolution, which the exercise itself abstracts into "`Vₖ(t)` provides data"
and is not the content it tests. The covering and the reconstruction — the exercise's actual
intellectual content — are proved rigorously here.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 7.45 — two-spin state tomography (reconstruction).** Two states
`ρ`, `σ` of the four-dimensional two-qubit register `qudit (2²)` that yield the same expectation
values `⟨P_g⟩` for every **non-identity** two-qubit Pauli-string observable
`P_g = pauliStringHamiltonian g 1` (`g : Fin 2 → Fin 4`, `g ≠ 0`) are equal: `ρ = σ`. These are the
`4² − 1 = 15` non-identity Pauli
expectations (the traceless *deviation density matrix*); together with the fixed normalisation
`tr ρ = 1` they reconstruct `ρ` — the operational content of eq. (7.166)–(7.168) for two spins. The
`n`-general form is `State.eq_of_expectation_pauliStringHamiltonian_eq`. -/
theorem twoSpin_state_eq_of_expectation_pauliString_eq {ρ σ : State (qudit (2 ^ 2))}
    (h : ∀ g : Fin 2 → Fin 4, g ≠ (fun _ => 0) →
        ρ.expectation (pauliStringHamiltonian g 1)
          = σ.expectation (pauliStringHamiltonian g 1)) :
    ρ = σ :=
  State.eq_of_expectation_pauliStringHamiltonian_eq h

/-- **Nielsen & Chuang, Exercise 7.45 — nine experiments suffice.** Two states `ρ`, `σ` of the
two-qubit register `qudit (2²)` that agree on the expectation `⟨P_g⟩` of every two-qubit
Pauli-string observable `P_g = pauliStringHamiltonian g 1` **observed by some one of the nine
experiments** are equal: `ρ = σ`.

The nine experiments are the settings `s : Fin 2 → Fin 3` (there are
`Fintype.card (Fin 2 → Fin 3) = 3² = 9`, `Concrete.nmrTomographyExperiments_two`) — the exercise's
`{I, R_x, R_y}²` pre-rotation grid `M₀ = I, M₁ = R_{x1}, M₂ = R_{y1}, M₃ = R_{x2},
M₄ = R_{x2}R_{x1}, M₅ = R_{x2}R_{y1}, …` — under which spin `i` is measured in one of three bases
`{Z, Y, X}`, and experiment `s` reads out the Pauli string `g` exactly when each non-identity
factor of `g` matches that spin's measured basis (`Concrete.SettingObserves`). Because the full
nine-setting family `univ` is tomographically complete (`Concrete.tomographyComplete_univ`), its
observed strings cover all `15` non-identity Paulis, so the reconstruction
(`twoSpin_state_eq_of_expectation_pauliString_eq`) applies: **the nine experiments provide
sufficient data from which `ρ` is reconstructed**, the exercise's conclusion. Proved as the
`n = 2`, `T = univ` instance of `State.eq_of_expectation_pauliString_of_tomographyComplete`. -/
theorem twoSpin_state_eq_of_expectation_nineExperiments {ρ σ : State (qudit (2 ^ 2))}
    (h : ∀ g : Fin 2 → Fin 4,
        (∃ s ∈ (Finset.univ : Finset (Fin 2 → Fin 3)), Concrete.SettingObserves s g) →
          ρ.expectation (pauliStringHamiltonian g 1)
            = σ.expectation (pauliStringHamiltonian g 1)) :
    ρ = σ :=
  State.eq_of_expectation_pauliString_of_tomographyComplete Concrete.tomographyComplete_univ h

end AxQM
