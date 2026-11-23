/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.NmrTomographyExperimentCount

/-!
# Nielsen & Chuang, Exercise 7.46 (Tomography experiments for three spins)

*(N&C p. 337, §7.7.4.)*

How many tomography experiments are sufficient/necessary for three spins?

## The physics and the answer

This is the direct sequel to Exercise 7.45, whose answer for **two** spins is *nine*. An `n`-spin
density matrix expands in the `4ⁿ` Pauli strings `P_g = σ_{g₁} ⊗ ⋯ ⊗ σ_{gₙ}` and is reconstructed
from the coefficients `⟨P_g⟩ = tr(ρ P_g)` (N&C eqs. 7.166–7.168, generalizing the single-qubit
trace-orthogonality reconstruction to `n` spins). The tomography scheme of Exercise 7.45 applies to
each spin one of three pre-pulses `{I, R_x, R_y}` — equivalently, **measures each spin in one of
three bases** — so a measurement configuration is a *setting* `s : Fin n → Fin 3`, and a Pauli
string is read out under `s` exactly when each of its non-identity factors matches that spin's
measured basis.

> **Sufficient and necessary: `3ⁿ` experiments — for three spins, `3³ = 27`.**

* **Sufficient:** the family of all `3ⁿ` settings observes every Pauli string, so it determines
  every coefficient and hence the state.
* **Necessary:** `3ⁿ` is also necessary, and in fact the complete family is *unique* — a full-weight
  Pauli string (every factor non-identity, e.g. `X ⊗ Y ⊗ Z`) is observed by a **single** setting, so
  no setting can be dropped.

Separately, the *information* content — how many real numbers must be determined — is `4ⁿ − 1`
(Exercise 4.46); for three spins, `4³ − 1 = 63`. Each of the `27` settings reads out `2ⁿ = 8`
coefficients, so the experiments over-determine the `63` parameters. These are the two halves of the
question: `27` *experiments*, `63` *real parameters*.

## The formalisation

The answer is a combinatorial count over the tomography settings `Fin n → Fin 3` and the
Pauli-string index `Fin n → Fin 4`, tied to the Pauli-basis reconstruction of a density `Matrix`.
Compare Exercise 7.44 (logical labeling) and Exercise 4.46 (the `4ⁿ − 1` parameter count used
here).

In `AxQM/Concrete/NmrTomographyExperimentCount.lean` (namespace `AxQM.Concrete`):

* `SettingObserves s g` — setting `s : Fin n → Fin 3` observes Pauli string `g : Fin n → Fin 4`
  (each non-identity factor matches the spin's measured basis).
* `TomographyComplete T` — the setting family `T` observes every non-identity Pauli string (so its
  measurements suffice to reconstruct the state).
* `tomographyComplete_univ` — **sufficiency**: all `3ⁿ` settings are complete.
* `TomographyComplete.eq_univ` — **necessity/uniqueness**: for `0 < n`, the *only* complete family
  is `univ`; and `TomographyComplete.card_eq` — every complete family has exactly `3ⁿ` settings.
* `TomographyComplete.matrix_ext` — **genuine reconstruction**: a complete scheme's data (equal
  trace + equal observed Pauli coefficients) determine the density matrix.
* `card_settingObserves` — each experiment reads out `2ⁿ` Pauli coefficients.
* `nmrTomographyExperiments n = 3ⁿ`, with `nmrTomographyExperiments_two = 9` (Exercise 7.45) and
  `nmrTomographyExperiments_three = 27` (**the answer**); `nmrTomographyParams_three = 63` for the
  real-parameter count.

## Fidelity

The three-basis-per-spin scheme is exactly Exercise 7.45's `{I, R_x, R_y}` construction (its
two-spin count `9` is reproduced), read as a product-basis measurement. Both `sufficient` and
`necessary` are proved — `3ⁿ` settings suffice and are necessary, with the complete family pinned
uniquely — and
completeness is shown to genuinely determine the density matrix, not merely cover an index set. No
dimension is specialized and no hypothesis is added beyond `0 < n` (needed only for necessity;
`n = 0` has no spins). The answer is neither weakened nor overstated.
-/
