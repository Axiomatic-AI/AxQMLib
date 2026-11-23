/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliString

/-!
# Concrete: tomographic reconstruction of a matrix from its Pauli trace pairings

This file turns the Pauli **basis**
of `M₂ₙ(ℂ)` (`Concrete/PauliString.lean`) into the explicit **reconstruction** and
**uniqueness** statements underlying *state tomography* — Nielsen & Chuang, §7.7.4, equations
(7.166)–(7.168) and their multi-spin generalisation ("Similar results hold for larger numbers of
spins"). Everything here is stated for raw matrix data (`Matrix`, `Concrete.pauliString`, `trace`).

## The tomography backbone

For a single qubit N&C writes `ρ = ½(I + Σₖ rₖ σₖ)` (7.166) with real coordinates
`rₖ = tr(ρ σₖ)` (7.168), recoverable because of the trace orthogonality `tr(σₖ σⱼ) = 2 δₖⱼ`
(7.167). The `n`-fold generalisation, over the Pauli strings `P_g = σ_{g₀} ⊗ ⋯ ⊗ σ_{g_{n-1}}`, is:

* every coordinate is a trace pairing — `pauliBasis.repr M g = (2ⁿ)⁻¹ tr(P_g M)`
  (`pauliBasis_repr_apply`), the (7.168) formula `rₖ = tr(ρ σₖ)`;
* the **reconstruction formula** `M = (2ⁿ)⁻¹ Σ_g tr(P_g M) • P_g`
  (`eq_smul_sum_trace_pauliString`), the (7.166) expansion;
* the **uniqueness / injectivity** principle `(∀ g, tr(P_g M) = tr(P_g N)) → M = N`
  (`eq_of_trace_pauliString_eq`) — *this* is what "the measurements suffice to reconstruct `M`"
  means: a matrix is determined by its `4ⁿ` Pauli trace pairings;
* the **deviation-density-matrix** refinement `eq_of_trace_eq_of_trace_pauliString_eq`: once the
  trace is fixed (density matrices have `tr ρ = 1`), the `4ⁿ − 1` **non-identity** pairings
  already determine `M`, matching N&C's "traceless deviation" bookkeeping and the counting
  `4ⁿ − 1` of independent real parameters.

For a Hermitian `M` (a density matrix) every pairing `tr(P_g M)` is real, so the recovered
coordinates are the real `⟨σ_g⟩` of (7.168). The underlying trace-pairing facts
`trace_pauliString_mul_eq_repr` (`tr(P_g M) = repr M g · 2ⁿ`) and `trace_pauliString_mul_im` (that
pairing is real for Hermitian `M`) live upstream in `Concrete/PauliString.lean`, beside the Pauli
basis and the existence result `exists_real_pauliString_expansion` that consumes them; this file
adds the *reconstruction* / *uniqueness* statements built on top — the reusable half of state
tomography applied by N&C Exercise 7.45 (two spins) and 7.46 (three spins).
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-- **The (7.168) coordinate formula**: `pauliBasis.repr M g = (2ⁿ)⁻¹ tr(P_g M)`. The single-qubit
case `rₖ = tr(ρ σₖ)` (`n = 1`, `2ⁿ = 2`, so `rₖ = ½ tr(ρ σₖ)` in N&C's `½`-normalised form). -/
theorem pauliBasis_repr_apply (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (g : Fin n → Fin 4) :
    pauliBasis.repr M g = ((2 : ℂ) ^ n)⁻¹ * (pauliString g * M).trace := by
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  rw [trace_pauliString_mul_eq_repr]
  field_simp

/-- **The reconstruction formula (7.166), `n`-fold form**: every `2ⁿ × 2ⁿ` complex matrix is the
Pauli sum of its own trace pairings, `M = (2ⁿ)⁻¹ Σ_g tr(P_g M) • P_g`. This is the operational
content of tomography — the matrix is *rebuilt* from the numbers `tr(P_g M)`, which the
measurements provide. (No Hermitian hypothesis: it holds for every matrix, `ρ` being one case.) -/
theorem eq_smul_sum_trace_pauliString (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    M = ((2 : ℂ) ^ n)⁻¹ • ∑ g, (pauliString g * M).trace • pauliString g := by
  conv_lhs => rw [← pauliBasis.sum_repr M]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [pauliBasis_apply, pauliBasis_repr_apply, smul_smul]

/-- **Tomographic uniqueness / injectivity**: a matrix is determined by its `4ⁿ` Pauli trace
pairings — if `tr(P_g M) = tr(P_g N)` for every Pauli string `P_g`, then `M = N`. This is the
precise sense in which "the measured expectation values suffice to reconstruct the state": two
states with identical Pauli measurement statistics are equal. Both sides are rebuilt by the
reconstruction formula from data that agree termwise. -/
theorem eq_of_trace_pauliString_eq {M N : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ}
    (h : ∀ g, (pauliString g * M).trace = (pauliString g * N).trace) : M = N := by
  rw [eq_smul_sum_trace_pauliString M, eq_smul_sum_trace_pauliString N]
  simp only [h]

/-- **Deviation-density-matrix uniqueness**: once the trace is fixed, the **non-identity** Pauli
pairings already determine the matrix. If `tr M = tr N` and `tr(P_g M) = tr(P_g N)` for every
`g ≠ (0, …, 0)` (every Pauli string other than `I ⊗ ⋯ ⊗ I`), then `M = N`. Density matrices carry
`tr ρ = 1`, so this is the statement that the `4ⁿ − 1` non-identity expectation values
`⟨P_g⟩ = tr(ρ P_g)` reconstruct `ρ` — N&C's traceless "deviation density matrix" bookkeeping and
the `4ⁿ − 1` real-parameter count. -/
theorem eq_of_trace_eq_of_trace_pauliString_eq
    {M N : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (htr : M.trace = N.trace)
    (h : ∀ g, g ≠ (fun _ => 0) → (pauliString g * M).trace = (pauliString g * N).trace) :
    M = N := by
  refine eq_of_trace_pauliString_eq fun g => ?_
  by_cases hg : g = (fun _ => 0)
  · subst hg
    rw [pauliString_const_zero, Matrix.one_mul, Matrix.one_mul, htr]
  · exact h g hg

end AxQM.Concrete
