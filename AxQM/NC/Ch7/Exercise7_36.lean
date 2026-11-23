/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HighTempThermalState

/-!
# Nielsen & Chuang, Exercise 7.36 (Thermal-equilibrium NMR state)

*(N&C p. 329, §7.7.1.)*

Thermal-equilibrium NMR state: show ρ≈1−(ℏω/2k_BT)Z for n=1 and the n=2 diagonal form.

## The physics and what is proved

An NMR sample sits in **thermal equilibrium**, `ρ = e^{−βH}/Z` with `β = 1/(k_B T)` and
`Z = tr e^{−βH}` (N&C eq. 7.139). At NMR field strengths and temperatures `β` is tiny, so `e^{−βH}`
is replaced by its first-order Taylor term, giving the **high-temperature approximation**
(eq. 7.140) `ρ ≈ 2^{−n}(I − βH)` for `n` spins. Exercise 7.36 asks to evaluate it explicitly.

We formalise the `2^{−n}(I − βH)` object *exactly* as
`AxQM.highTempThermalState` (a genuine `State`, in the high-temperature/positivity regime),
and prove that for the physical Hamiltonians it equals the book's explicit forms **exactly** — the
`≈` sign in the exercise is the `e^{−βH}/Z ≈ 2^{−n}(I − βH)` truncation of eq. 7.140 (the *setup*),
not the equation the exercise itself asserts, which is the exact substitution `2^{−n}(I − βH) =`
[explicit matrix].

### `n = 1` (this file, eq. 7.141)

The single-spin Hamiltonian is `H = ℏω Z` (`nmrHamiltonianSpinOne`). Then
`2^{−1}(I − βH) = ½(I − βℏω Z)`, whose Bloch form is `½(I + r·σ)` with Bloch vector
`r = (0, 0, −βℏω)`:

* `nmrThermalState_spinOne_eq` — **Exercise 7.36, `n = 1`**: the single-spin high-temperature
  thermal state equals the Bloch state with Bloch vector `(0, 0, −βℏω)`, i.e. `½(I − βℏω Z)` — the
  matrix `1 − (ℏω/2k_BT) Z` of eq. 7.141 (with the book's `1` denoting the maximally-mixed identity
  part `½I`, since the literal matrix `1 − (ℏω/2k_BT)Z` has trace `2`, not `1`, and only its
  traceless part `Z` carries physical content). Valid whenever `(βℏω)² ≤ 1` — the single-spin
  high-temperature/positivity condition.

The equality is stated for states, in terms of `highTempThermalState` / `nmrHamiltonianSpinOne`
(`AxQM/Postulates/API/HighTempThermalState.lean`) and the Bloch state `blochState`; the computation
`½(I − βℏω Z) = toEuclideanCLM (blochMatrix (0,0,−βℏω))` is
`highTempThermalStateSpinOne_op` there.

### `n = 2` (eq. 7.142)

The two-spin Hamiltonian is `H = ℏ(ω_A Z₁ + ω_B Z₂)` (`nmrHamiltonianSpinTwo`, genuinely built from
the Pauli Kronecker products `Z⊗I`, `I⊗Z`) on the `4`-level register `qudit 4`. In the resonance
case `ω_A = 4ω_B` its Zeeman levels are `ℏω_B·(5, 3, −3, −5)`, so
`2^{−2}(I − βH) = ¼(I − βℏω_B·diag(5, 3, −3, −5))`, the diagonal density matrix of eq. 7.142:

* `nmrThermalState_spinTwo_eq` — **Exercise 7.36, `n = 2`**: the two-spin high-temperature thermal
  state equals `nmrThermalStateSpinTwo`, the diagonal state with populations
  `¼·(1 − 5βℏω_B, 1 − 3βℏω_B, 1 + 3βℏω_B, 1 + 5βℏω_B)` — the matrix
  `1 − (ℏω_B/4k_BT)·diag(5, 3, −3, −5)` of eq. 7.142 (again the book's `1` is the maximally-mixed
  identity part `¼I`; only the traceless `diag(5, 3, −3, −5)` carries physical content). Valid
  whenever `(5βℏω_B)² ≤ 1` — the two-spin high-temperature/positivity condition.

As for `n = 1`, the equality is stated for states, in terms of
`highTempThermalState` / `nmrHamiltonianSpinTwo` / `nmrThermalStateSpinTwo`; the computation
`¼(I − βℏω_B·diag) = toEuclideanCLM (diag populations)` is `highTempThermalStateSpinTwo_op` in
`AxQM/Postulates/API/HighTempThermalState.lean`.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 7.36 (`n = 1`, eq. 7.141).** The single-spin NMR high-temperature
thermal-equilibrium state `2^{−1}(I − βH)` for the Zeeman Hamiltonian `H = ℏω Z` equals the qubit
Bloch state with Bloch vector `(0, 0, −βℏω)`, i.e. `½(I − βℏω Z)` — the density operator `1 −
(ℏω/2k_BT) Z` of eq. 7.141 (`β = 1/(k_B T)`; the book's leading `1` is the maximally-mixed part
`½I`). The hypothesis `(βℏω)² ≤ 1` is the single-spin high-temperature/positivity condition (the
Bloch vector lies in the unit ball).

Proof: both states have the same density operator. Reducing through `State.ext`, the
high-temperature operator `½(I − β · ℏω Z)` equals `toEuclideanCLM (blochMatrix (0,0,−βℏω))`
(`highTempThermalStateSpinOne_op`), which is exactly `(blochState (0,0,−βℏω)).op`. -/
theorem nmrThermalState_spinOne_eq (β ℏ ω : ℝ) (hr : (β * ℏ * ω) ^ 2 ≤ 1) :
    highTempThermalState β (nmrHamiltonianSpinOne ℏ ω)
        (highTempThermalStateSpinOne_isDensity β ℏ ω hr)
      = blochState ![0, 0, -(β * ℏ * ω)] (nmrThermalStateSpinOne_bloch_ball β ℏ ω hr) := by
  apply State.ext
  rw [highTempThermalState_op, blochState_op]
  exact highTempThermalStateSpinOne_op β ℏ ω

/-- **Nielsen & Chuang, Exercise 7.36 (`n = 2`, eq. 7.142).** In the resonance case `ω_A = 4ω_B`,
the two-spin NMR high-temperature thermal-equilibrium state `2⁻²(I − βH)` for the Zeeman Hamiltonian
`H = ℏ(ω_A Z₁ + ω_B Z₂)` equals the diagonal state `nmrThermalStateSpinTwo` with populations
`¼·(1 − 5βℏω_B, 1 − 3βℏω_B, 1 + 3βℏω_B, 1 + 5βℏω_B)` — the density operator
`1 − (ℏω_B/4k_BT)·diag(5, 3, −3, −5)` of eq. 7.142 (`β = 1/(k_B T)`; the book's leading `1` is the
maximally-mixed part `¼I`). The hypothesis `(5βℏω_B)² ≤ 1` is the two-spin high-temperature /
positivity condition (the largest Zeeman population stays in `[0,1]`).

Proof: both states have the same density operator. Reducing through `State.ext`, the
high-temperature operator `¼(I − β·H)` equals `Matrix.toEuclideanCLM (diag populations)`
(`highTempThermalStateSpinTwo_op`), which is exactly `(nmrThermalStateSpinTwo β ℏ ω_B _).op`. -/
theorem nmrThermalState_spinTwo_eq (β ℏ ωB : ℝ) (h : (5 * (β * ℏ * ωB)) ^ 2 ≤ 1) :
    highTempThermalState β (nmrHamiltonianSpinTwo ℏ (4 * ωB) ωB)
        (highTempThermalStateSpinTwo_isDensity β ℏ ωB h)
      = nmrThermalStateSpinTwo β ℏ ωB h := by
  apply State.ext
  rw [highTempThermalState_op, nmrThermalStateSpinTwo_op]
  exact highTempThermalStateSpinTwo_op β ℏ ωB

end AxQM
