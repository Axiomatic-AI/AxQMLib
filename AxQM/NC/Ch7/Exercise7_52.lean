/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HeisenbergSwap
import AxQM.Concrete.SqrtSwapCNOT

/-!
# Nielsen & Chuang, Exercise 7.52 — Universality of the Heisenberg Hamiltonian

Universality of Heisenberg Hamiltonian: show swap U=exp(-iπ S1·S2), √SWAP is universal, and derive
CNOT.

Every statement is about `4×4` complex matrices and Mathlib's matrix exponential
`NormedSpace.exp`.

The coupling operator is `S⃗₁·S⃗₂ = ¼(X⊗X + Y⊗Y + Z⊗Z) = ¼ σ⃗₁·σ⃗₂` (`heisenbergDot`, built from
`Concrete.spinSpinCoupling`). The formalisation is the following collection of definitions
and theorems.

## Where the formalisation lives

`AxQM/Concrete/HeisenbergSwap.lean` — Parts 1 and 2:

* `AxQM.Concrete.twoQubitSwap` — the `4×4` SWAP gate on `Fin 2 × Fin 2`;
  `twoQubitSwap_mul_self` — `SWAP² = I`.
* `AxQM.Concrete.spinSpinCoupling_eq_two_smul_twoQubitSwap_sub_one` — the key identity
  `σ⃗₁·σ⃗₂ = 2·SWAP − I`, hence `heisenbergDot_eq : S⃗₁·S⃗₂ = ½·SWAP − ¼·I`.
* `AxQM.Concrete.heisenbergEvolution` / `heisenbergEvolution_eq` — the propagator
  `exp(−iφ S⃗₁·S⃗₂) = e^{iφ/4}(cos(φ/2)·I − i sin(φ/2)·SWAP)`.
* `AxQM.Concrete.heisenbergEvolution_pi` — **Part 1:** `exp(−iπ S⃗₁·S⃗₂) = e^{−iπ/4}·SWAP`.
* `AxQM.Concrete.sqrtSwapHeis` / `sqrtSwapHeis_eq` — **Part 2:**
  `√SWAP = exp(−i(π/2) S⃗₁·S⃗₂) = e^{iπ/8}(√2/2)(I − i·SWAP)`;
  `sqrtSwapHeis_mul_self` — `√SWAP² = exp(−iπ S⃗₁·S⃗₂)` (a genuine square root of the swap).

`AxQM/Concrete/SqrtSwapCNOT.lean` — Part 3 (**the universality of `√SWAP`**: a `CNOT`
built from `√SWAP` and single-qubit gates). With `S = sMatrix = diag(1, i)`, `S† = diag(1, −i)`,
`Z = pauliZ`, `H = hadamardC`:

* `AxQM.Concrete.twoQubitCZ` / `twoQubitCNOT` — the controlled-`Z` `diag(1,1,1,−1)` and
  controlled-`NOT` `|a,b⟩ ↦ |a, a+b⟩` gates on `Fin 2 × Fin 2`.
* `AxQM.Concrete.sqrtSwapHeis_controlledZ` — two `√SWAP`s with a central `Z` on qubit 1 and
  the phase corrections `S ⊗ S†` build controlled-`Z` up to a global phase:
  `(S ⊗ S†)·√SWAP·(Z ⊗ 1)·√SWAP = e^{−iπ/4}·CZ`.
* `AxQM.Concrete.hadamardC_conj_twoQubitCZ` — `(1 ⊗ H)·CZ·(1 ⊗ H) = CNOT` (the standard
  `CZ ↦ CNOT` Hadamard conjugation on the target).
* `AxQM.Concrete.sqrtSwapHeisCNOT` / `sqrtSwapHeisCNOT_eq` — **Part 3:** the explicit
  circuit `(1 ⊗ H)·(S ⊗ S†)·√SWAP·(Z ⊗ 1)·√SWAP·(1 ⊗ H)` equals `e^{−iπ/4}·CNOT`, so `√SWAP`
  together with single-qubit gates implements a controlled-`NOT` — the universality claim.
-/
