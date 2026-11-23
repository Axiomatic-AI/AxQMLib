/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.PauliTomographyExpectation
import AxQM.Concrete.NmrTomographyExperimentCount

/-!
# AxQM.Core — state reconstruction from a complete NMR tomography scheme (N&C §7.7.4)

The **grounded reconstruction theorem for the NMR tomography scheme** of Nielsen & Chuang Exercises
7.45–7.46: a state `ρ` on the `n`-qubit register `qudit (2ⁿ)` is uniquely determined by the Pauli
expectations `⟨P_g⟩_ρ` that a *tomographically complete* family of measurement settings observes. It
ties the combinatorial covering of the pre-rotation scheme (`Concrete.TomographyComplete`,
`Concrete.SettingObserves`, from Exercise 7.46) to the reconstruction principle
`State.eq_of_expectation_pauliStringHamiltonian_eq`.

## The physics (N&C §7.7.4, eqs. 7.143, 7.166–7.168)

Each experiment applies to each spin one of three pre-pulses `{I, R_x, R_y}` — equivalently, it
measures each spin in one of three bases `{Z, Y, X}` — so a *setting* is `s : Fin n → Fin 3`, and
the coupled-spin readout of experiment `s` delivers the expectation `⟨P_g⟩_ρ` of exactly the Pauli
strings `g` it *observes* (`SettingObserves s g`: each non-identity factor of `g` matches that
spin's measured basis, N&C eq. 7.168 read out under the pre-rotation). A family `T` of settings is
*tomographically complete* when every non-identity Pauli string is observed by some setting in `T`.
Then the observed expectations span all `4ⁿ − 1` non-identity Pauli coefficients (N&C's traceless
*deviation density matrix*), and with the fixed normalisation `tr ρ = 1` they reconstruct `ρ`.

## Statement

* `State.eq_of_expectation_pauliString_of_tomographyComplete` — if `T` is tomographically complete
  and two states `ρ, σ` agree on `⟨P_g⟩` for every Pauli string `g` observed by some setting in `T`,
  then
  `ρ = σ`. This is "a complete tomography scheme's data determine the state," grounded in
  `State.expectation`, for every `n`. Exercise 7.45 (two spins, the nine `{I, R_x, R_y}²`
  settings) is its `n = 2` instance; Exercise 7.46 (three spins) the `n = 3` instance.

## Design

* **Index-level predicates.** The statement uses `State.expectation`, the observable
  `pauliStringHamiltonian`, and the *index-level* combinatorial predicates
  `Concrete.TomographyComplete` / `Concrete.SettingObserves` (`Prop`s over the plain index types
  `Fin n → Fin 3` / `Fin n → Fin 4`).
* **Readout model.** The readout is
  modelled at the *observable* level: that experiment `s` delivers `⟨P_g⟩_ρ` for the strings it
  observes is *posited* (abstracting the time-domain `V(t)` and its resolved
  single-quantum-coherence spectrum, N&C eq. 7.143), while the covering
  (`Concrete.tomographyComplete_univ`) and the
  reconstruction are proved rigorously — the intellectual content of the exercise.
* **Proof.** Immediate from the reconstruction principle: for each non-identity Pauli string `g`,
  completeness of `T` supplies a setting in `T` observing `g`, and the hypothesis then furnishes the
  equal expectation `⟨P_g⟩_ρ = ⟨P_g⟩_σ`.
-/

namespace AxQM

variable {n : ℕ}

/-- **Reconstruction from a complete NMR tomography scheme** (Nielsen & Chuang §7.7.4, Ex
7.45–7.46). If a family `T` of measurement settings is *tomographically complete* (every
non-identity Pauli string is observed by some setting, `Concrete.TomographyComplete`) and two
states `ρ, σ` on the `n`-qubit register `qudit (2ⁿ)` agree on the expectation `⟨P_g⟩` of every
Pauli-string observable
`P_g = pauliStringHamiltonian g 1` that some setting in `T` observes, then `ρ = σ`. The observed
expectations span all `4ⁿ − 1` non-identity Pauli coefficients, so with the fixed normalisation
`tr ρ = 1` they reconstruct the state (`State.eq_of_expectation_pauliStringHamiltonian_eq`). The
readout of each experiment (which strings it delivers) is modelled at the observable level; the
covering and the reconstruction are proved. -/
theorem State.eq_of_expectation_pauliString_of_tomographyComplete
    {ρ σ : State (qudit (2 ^ n))} {T : Finset (Fin n → Fin 3)}
    (hT : Concrete.TomographyComplete T)
    (h : ∀ g : Fin n → Fin 4, (∃ s ∈ T, Concrete.SettingObserves s g) →
        ρ.expectation (pauliStringHamiltonian g 1)
          = σ.expectation (pauliStringHamiltonian g 1)) :
    ρ = σ :=
  State.eq_of_expectation_pauliStringHamiltonian_eq fun g hg => h g (hT g hg)

end AxQM
