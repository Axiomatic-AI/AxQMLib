/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.KerrTwoPhotonPhase

/-!
# Nielsen & Chuang, Exercise 7.21 (two-photon Kerr phase shift)

Explicitly exponentiate (7.82) and show the two-photon phase φ_ab equals
arg[e^{iδt}(cosΩ't−i(δ/Ω')sinΩ't)].

(N&C p. 305.) In the microscopic model of the optical Kerr effect (N&C §7.5.3), two orthogonally
polarised single-photon modes `a`, `b` interact with one three-level atom. In the total-excitation
basis the Hamiltonian is block diagonal (7.82), `H = diag(H₀, H₁, H₂)`, with `H₀ = -δ` (7.83) on the
vacuum `|000⟩` and `H₂` (7.85) the `3 × 3` block on the two-excitation sector `|110⟩, |011⟩, |102⟩`.
With `U = exp(iHt)` (the p. 305 convention), the two-photon phase shift is
`ϕ_ab = arg⟨110|U|110⟩ − arg⟨000|U|000⟩`, and the exercise asks to exponentiate the blocks and
establish the closed form (7.86).

The content is a computation about a `3 × 3` complex `Matrix`, its `NormedSpace.exp`, and
`Complex.arg`. Compare Exercise 7.9 and Exercise 7.16.

## The formalisation

In `AxQM/Concrete/KerrTwoPhotonPhase.lean`:

* `kerrRabiFreq` — the generalised Rabi frequency `Ω' = √(δ² + gₐ² + g_b²)`.
* `kerrBlockTwo`, `kerrBlockZero` — the `H₂` (7.85) and `H₀` (7.83) blocks of (7.82).
* `kerrBlockTwo_exp_apply_zero_zero_eigensum` — the **explicit exponentiation** of `H₂`: the `(0,0)`
  entry of `exp((it)·H₂)` as its eigenvalue expansion over the spectrum `{Ω', −Ω', δ}` (orthogonal
  diagonalisation; the `δ`-eigenvector is orthogonal to `|110⟩`).
* `kerrBlockTwo_exp_apply_zero_zero` — the two-photon amplitude
  `⟨110|U|110⟩ = cos Ω't − i(δ/Ω') sin Ω't`.
* `kerrBlockZero_exp_apply_zero_zero` — the reference amplitude `⟨000|U|000⟩ = e^{-iδt}`.
* `kerrTwoPhotonPhase_ratio` — the exact amplitude ratio
  `⟨110|U|110⟩ / ⟨000|U|000⟩ = e^{iδt}(cos Ω't − i(δ/Ω') sin Ω't)`, whose argument is `ϕ_ab`.
* `kerrTwoPhotonPhase_arg` — **Exercise 7.21, eq. (7.86)**:
  `ϕ_ab = arg[e^{iδt}(cos Ω't − i(δ/Ω') sin Ω't)]`.

A physically inessential nondegeneracy hypothesis `0 < gₐ² + g_b²` (a genuine atom–field coupling
is present — N&C's Fig. 7.5 uses `gₐ = g_b = 1`) makes the spectrum simple and `Ω' > 0`.

The follow-on "use this to compute `χ₃ = ϕ_ab − ϕ_a − ϕ_b`" is the exercise's numerical discussion
(the plotted Kerr shift, Fig. 7.5): it needs the single-photon shifts `ϕ_a`, `ϕ_b` from the `4 × 4`
block `H₁` (7.84). The exercise's stated verifiable proposition is (7.86), formalised above.
-/
