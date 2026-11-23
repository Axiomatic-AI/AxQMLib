/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliTomographyExpectation

/-!
# AxQM.Core — tomographic reconstruction: a state is fixed by its Pauli expectations

The **grounded reconstruction principle** of *state tomography* (Nielsen & Chuang
§7.7.4, eqns 7.166–7.168): a quantum state `ρ` on the `n`-qubit register `qudit (2ⁿ)` is uniquely
determined by the expectation values `⟨P_g⟩_ρ` of the non-identity Pauli-string observables
`P_g = pauliStringHamiltonian g 1` (`g ≠ 0`). This is the precise content of "the state can be
reconstructed from its measured Pauli expectation values": two states with identical Pauli
measurement statistics are equal.

## Statement

* `State.eq_of_expectation_pauliStringHamiltonian_eq` — if
  `ρ.expectation (pauliStringHamiltonian g 1) = σ.expectation (pauliStringHamiltonian g 1)` for
  every **non-identity** Pauli string `g ≠ (fun _ => 0)`, then `ρ = σ`. For `n = 2` (two spins) this
  is the `4² − 1 = 15` non-identity two-qubit Pauli expectations of Exercise 7.45; the identity is
  the fixed normalisation `tr ρ = 1`, not a measurement, matching N&C's traceless *deviation density
  matrix* (the `4ⁿ − 1` real parameters).

## Design

* **Where the ingredients are.** The statement uses `State.expectation` and the observable
  `pauliStringHamiltonian`. It is proved through `State.pauliMatrix`, the (7.168) trace
  identity `State.expectation_pauliStringHamiltonian` and `State.eq_of_pauliMatrix_eq`, all in
  `AxQM/Postulates/API/PauliTomographyExpectation.lean`; the underlying matrix uniqueness is
  `eq_of_trace_eq_of_trace_pauliString_eq` in `AxQM/Concrete/PauliTomography.lean`.
* **`n`-general.** Stated for every `n`, so it serves both Exercise 7.45 (two spins) and Exercise
  7.46 (three spins) verbatim.
* **Proof.** Reduce `ρ = σ` to the matrix identity `ρ.pauliMatrix = σ.pauliMatrix`
  (`State.eq_of_pauliMatrix_eq`), then apply the Concrete deviation-uniqueness backbone: the traces
  agree (both density matrices have `tr = 1`, `State.trace_pauliMatrix`), and each non-identity
  Pauli trace pairing agrees because the bridge turns the hypothesis into
  `Re tr(P_g ρ) = Re tr(P_g σ)`, which lifts to full equality since both pairings are real
  (`Concrete.trace_pauliString_mul_im`, the pairings of Hermitian matrices).
-/

open scoped BigOperators

namespace AxQM

variable {n : ℕ}

/-- **Tomographic reconstruction of a state from its Pauli expectations** (Nielsen & Chuang §7.7.4,
eqns 7.166–7.168; the reconstruction underlying Exercise 7.45). A state `ρ` on the `n`-qubit
register `qudit (2ⁿ)` is uniquely determined by the expectations `⟨P_g⟩_ρ` of the **non-identity**
Pauli-string observables `P_g = pauliStringHamiltonian g 1`: if `ρ` and `σ` have equal such
expectations for every `g ≠ 0`, then `ρ = σ`. The identity Pauli `P_0 = I` is not needed — it pairs
to the fixed normalisation `tr ρ = 1`, N&C's traceless *deviation density matrix* — so the
`4ⁿ − 1` non-identity expectations (`15` for two spins) suffice. -/
theorem State.eq_of_expectation_pauliStringHamiltonian_eq {ρ σ : State (qudit (2 ^ n))}
    (h : ∀ g : Fin n → Fin 4, g ≠ (fun _ => 0) →
        ρ.expectation (pauliStringHamiltonian g 1)
          = σ.expectation (pauliStringHamiltonian g 1)) :
    ρ = σ := by
  refine State.eq_of_pauliMatrix_eq (Concrete.eq_of_trace_eq_of_trace_pauliString_eq ?_ ?_)
  · rw [ρ.trace_pauliMatrix, σ.trace_pauliMatrix]
  · intro g hg
    have hre : ((Concrete.pauliString g * ρ.pauliMatrix).trace).re
        = ((Concrete.pauliString g * σ.pauliMatrix).trace).re := by
      rw [← ρ.expectation_pauliStringHamiltonian, ← σ.expectation_pauliStringHamiltonian]
      exact h g hg
    have himρ := Concrete.trace_pauliString_mul_im ρ.pauliMatrix_isHermitian g
    have himσ := Concrete.trace_pauliString_mul_im σ.pauliMatrix_isHermitian g
    exact Complex.ext hre (himρ.trans himσ.symm)

end AxQM
