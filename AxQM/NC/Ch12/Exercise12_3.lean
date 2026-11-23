/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChiBound
import AxQM.Postulates.API.TensorPowDim
import AxQM.Postulates.API.Entropy
import AxQM.NC.Ch12.Problem12_1

/-!
# Nielsen & Chuang, Exercise 12.3 (`n` qubits carry no more than `n` bits)

*(N&C p. 535.)*

Use Holevo bound to show n qubits carry no more than n bits of classical info.

Alice encodes a classical message `X` into the quantum states `ρₓ` of an `n`-qubit register and
sends it to Bob, who measures with some POVM to obtain a result `Y`. The information Bob gains about
`X` is the classical mutual information `H(X : Y)`. The **Holevo bound** (Nielsen & Chuang
Theorem 12.1) states that for *any* measurement,

`H(X : Y) ≤ χ({pₓ, ρₓ}) = S(∑ₓ pₓ ρₓ) − ∑ₓ pₓ S(ρₓ)`.

Exercise 12.3 is the observation that on `n` qubits the Holevo χ quantity is itself bounded by `n`
bits, independently of the ensemble: writing `ρ = ∑ₓ pₓ ρₓ` for the average state,

`χ = S(ρ) − ∑ₓ pₓ S(ρₓ) ≤ S(ρ) ≤ log d = log 2ⁿ = n · log 2`,

using (i) non-negativity of the average component entropy `∑ₓ pₓ S(ρₓ) ≥ 0`, (ii) the maximum-
entropy bound `S(ρ) ≤ log d` (N&C Theorem 11.8) with `d = dim = 2ⁿ` the dimension of the `n`-qubit
Hilbert space. Chaining with the Holevo bound gives `H(X : Y) ≤ n · log 2`, i.e. Bob's information
about Alice's message is at most `n` bits — so `n` qubits carry no more than `n` bits of classical
information.

Entropies here are measured in **nats** (`Real.log` is the natural logarithm, matching
`State.vonNeumannEntropy`); the textbook's "`n` bits" is `n · log 2` nats, since one bit is `log 2`
nats.

## What is formalised

The item is two declarations, chained exactly as the exercise instructs — *using the Holevo bound*:

* `AxQM.State.holevoChi_qubit_tensorPow_le` — the **dimensional half** (the new inequality
  Exercise 12.3 supplies): for any ensemble `{pₓ, ρₓ}` of states on the `n`-qubit register
  `qubit ^⊗ₛ n`, `χ({pₓ, ρₓ}) ≤ n · log 2`. It is assembled from three results:
  * `State.holevoChi_le_vonNeumannEntropy_mix` (`Core/`) — `χ ≤ S(∑ₓ pₓ ρₓ)`;
  * `State.vonNeumannEntropy_le_log_finrank` (`Postulates/API/`) — `S(ρ) ≤ log d`;
  * `finrank_qubit_tensorPow_space` (`Postulates/API/`) — `d = dim (qubit ^⊗ₛ n) = 2ⁿ`, itself from
    the general `Module.finrank_piTensorProduct` (`ToMathlib/`).

* `AxQM.State.mutualInfo_qubit_tensorPow_le` — the **exercise's stated conclusion**
  `H(X : Y) ≤ n · log 2`: Bob's classical information about Alice's message is at most `n` bits. It
  is the one-line composition of the Holevo bound with the dimensional half,
  `(holevoBound_of_chi_monotone …).trans (holevoChi_qubit_tensorPow_le …)`.

The **Holevo bound** `H(X : Y) ≤ χ` — the tool the problem names — is
`AxQM.holevoBound_of_chi_monotone` (N&C Problem 12.1 / Theorem 12.1, in
`NC/Ch12/Problem12_1.lean`): for Alice's ensemble `{pₓ, ρₓ}` on any system and Bob's POVM `m` with
`r` outcomes, `H(X : Y) = Real.mutualInfo (fun (x, y) ↦ pₓ · m.bornProb ρₓ y) ≤ χ({pₓ, ρₓ})`. We
neither reprove nor inline it — we *apply* the shared theorem. Composing the two,

`H(X : Y) ≤ χ({pₓ, ρₓ}) ≤ n · log 2`,

so a measurement on the register reveals at most `n · log 2` nats = `n` bits: `n` qubits cannot
transmit more than `n` bits of classical information. Bob's POVM is presented with outcome type
`Fin r` — the form in which the Holevo bound is available, and no loss of generality, since any
finite outcome set is a `Fin r`.
-/

namespace AxQM.State

/-- **Nielsen & Chuang, Exercise 12.3.** For any finite ensemble `{pₓ, ρₓ}` of states on the
`n`-qubit register `qubit ^⊗ₛ n`, the Holevo χ quantity is at most `n · log 2` (i.e. `n` bits):

`χ({pₓ, ρₓ}) ≤ n · log 2`.

Combined with the Holevo bound `H(X : Y) ≤ χ` (N&C Theorem 12.1), this shows that a measurement on
the register reveals at most `n` bits of classical information — `n` qubits cannot transmit more
than `n` bits. The proof chains `χ ≤ S(∑ₓ pₓ ρₓ)`
(`holevoChi_le_vonNeumannEntropy_mix`), the maximum-entropy bound `S(ρ) ≤ log d`
(`vonNeumannEntropy_le_log_finrank`), and the register dimension `d = 2ⁿ`
(`finrank_qubit_tensorPow_space`), then `log 2ⁿ = n · log 2` (`Real.log_pow`). -/
theorem holevoChi_qubit_tensorPow_le {ι : Type*} [Fintype ι] {n : ℕ}
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ρ : ι → State (qubit.tensorPow n)) :
    holevoChi p hp hsum ρ ≤ (n : ℝ) * Real.log 2 :=
  calc holevoChi p hp hsum ρ
      ≤ (mix p hp hsum ρ).vonNeumannEntropy := holevoChi_le_vonNeumannEntropy_mix p hp hsum ρ
    _ ≤ Real.log (Module.finrank ℂ (qubit.tensorPow n).space) :=
        vonNeumannEntropy_le_log_finrank _
    _ = Real.log ((2 ^ n : ℕ) : ℝ) := by rw [finrank_qubit_tensorPow_space]
    _ = (n : ℝ) * Real.log 2 := by push_cast; rw [Real.log_pow]

/-- **Nielsen & Chuang, Exercise 12.3.** `n` qubits carry no more than `n` bits of classical
information. Alice encodes a classical message `X` (value `x` with probability `pₓ`) into states
`ρₓ` of an `n`-qubit register `qubit ^⊗ₛ n` and sends it to Bob, who measures with an arbitrary POVM
`m` (with `r` outcomes, `Y`). The classical mutual information Bob's outcome shares with Alice's
message is at most `n · log 2` — i.e. `n` bits:

`H(X : Y) ≤ n · log 2`,

where `H(X : Y) = Real.mutualInfo` of the joint distribution `p(x, y) = pₓ · Tr(Eᵧ ρₓ) =
pₓ · m.bornProb ρₓ y` of Alice's message and Bob's outcome.

This is the exercise's stated conclusion, obtained exactly as the exercise instructs — *using the
Holevo bound*. It chains the Holevo bound `H(X : Y) ≤ χ` (`holevoBound_of_chi_monotone`, N&C
Problem 12.1 / Theorem 12.1) with the dimensional χ bound `χ ≤ n · log 2` on the `n`-qubit register
(`holevoChi_qubit_tensorPow_le`, the reusable half proved above):

`H(X : Y) ≤ χ({pₓ, ρₓ}) ≤ n · log 2`. -/
theorem mutualInfo_qubit_tensorPow_le {ι : Type*} [Fintype ι] {n r : ℕ} [NeZero r]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ρ : ι → State (qubit.tensorPow n)) (m : Measurement (Fin r) (qubit.tensorPow n)) :
    Real.mutualInfo (fun xy : ι × Fin r => p xy.1 * m.bornProb (ρ xy.1) xy.2)
      ≤ (n : ℝ) * Real.log 2 :=
  (holevoBound_of_chi_monotone p hp hsum ρ m).trans (holevoChi_qubit_tensorPow_le p hp hsum ρ)

end AxQM.State
