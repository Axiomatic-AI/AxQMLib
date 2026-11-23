/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.NMRGroverIteration

/-!
# Nielsen & Chuang, Exercise 7.51 (simplifying the NMR Grover iteration)

*(N&C §7.7.4, p. 339–340.)*

Show the Grover iteration can be simplified by canceling adjacent single-qubit rotations to obtain
(7.172).

The two-qubit NMR Grover iteration is `G = H^{⊗2} · P · H^{⊗2} · O`, where each ingredient is a
product of single-qubit `x`/`y`-rotation pulses (`R = R(π/2)`, `R̄ = R(−π/2)`, `R² = R(π)`) and one
free-`J`-coupling period `τ = e^{−iH/2ℏJ}` (eqs. 7.170–7.171 and the surrounding text). Writing them
out and cancelling the adjacent rotations that meet at the `O`–`H^{⊗2}` and `H^{⊗2}`–`P` junctions
(each junction has an `R̄_y R_y = 1`, after which the `x`-pulses combine) collapses `G` to the four
cases of (7.172).

The exercise is an identity between products of the `2×2`/`4×4` rotation matrices — the
cancellation is pure single-qubit rotation algebra (`R̄_y R_y = 1`, `R²_x R_x = R³_x`) and the
Kronecker mixed-product rule, and it touches `τ` nowhere (it holds for *any* `τ`). That the pulse
products *are* the genuine Grover operators is the physics content of
Exercises 7.41 (`AxQM/NC/Ch7/Exercise7_41.lean`) and 7.50 (`AxQM/NC/Ch7/Exercise7_50.lean`).

## The formalisation

In `AxQM/Concrete/NMRGroverIteration.lean` (namespace `AxQM.Concrete`):

* `nmrHadamardPulse`, `nmrRotYXY s` — the per-qubit pulses `H = R²_x R̄_y` and the sandwich
  `R_y R_x(s) R̄_y` (`P` uses `s = π/2`; the oracle uses `s = −π/2` on a marked qubit, `+π/2` on an
  unmarked one), with the junction lemma `nmrHadamardPulse_mul_nmrRotYXY : H · (R_y R_x(s) R̄_y) =
  R_x(π+s) R̄_y` — the single-qubit cancellation itself.
* `nmrHadamardPair`, `nmrPhaseShiftPulse τ`, `nmrOraclePulse s₁ s₂ τ`, `nmrGroverIteration s₁ s₂ τ`
  — the two-qubit operators `H^{⊗2}`, `P`, `O_{x₀}` and their product `G = H^{⊗2} P H^{⊗2} O`,
  with `τ` a parameter and the oracle's per-qubit `x`-angles `s₁, s₂`.
* `nmrGroverIterationSimplified a₁ a₂ τ` — the literal right-hand side of (7.172).
* `nmrGroverIteration_collapse` — the heart: `G` collapses to
  `(R̄_x R̄_y)^{⊗2} τ · (R_x(π+s₁) R̄_y ⊗ R_x(π+s₂) R̄_y) τ`.
* `nmrGroverIteration_markedThree` / `markedZero` — the two cases `x₀ ∈ {3, 0}` of (7.172), as
  **exact** matrix identities `G = nmrGroverIterationSimplified …` (the residual signs cancel).
* `nmrGroverIteration_markedTwo` / `markedOne` — the two cases `x₀ ∈ {2, 1}`, as
  `G = −(nmrGroverIterationSimplified …)`: a single unmarked qubit contributes `R_x(3π/2) = −R̄_x`,
  the honest form of N&C's *"up to an irrelevant overall phase factor"* (unobservable in the channel
  `ρ ↦ G ρ G†`).

## Fidelity

The formalisation is faithful. The pulse decompositions are exactly N&C's
(the `x₀ = 3` oracle is the printed `R_y R̄_x R̄_y τ` per qubit; the other three flip the marked
qubit's `x`-pulse direction, matching Exercise 7.50). The identity reproduces (7.172) literally in
all four cases, and where the printed equation drops a global `−1` (`x₀ = 1, 2`) the sign is carried
honestly in the statement rather than hidden. Leaving `τ` an arbitrary matrix is a strict
generalisation (the cancellation never touches `τ`).
-/
