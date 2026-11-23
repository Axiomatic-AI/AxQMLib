/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliStringExpCircuit
import AxQM.Postulates.API.NMRControlledZ
import AxQM.Concrete.PauliStringLocality

/-!
# The total per-string Trotter summand `exp(-i h_g g Δ)` over all `4ⁿ` strings (N&C Problem 4.3(6))

Nielsen & Chuang, Problem 4.3(6) assembles the universal approximation `U ≈ [∏_g exp(-i h_g g Δ)]ᵏ`
as the `k`-fold power (part (5)) of one Trotter step, itself the ordered product over **all** `4ⁿ`
Pauli strings `g : Fin n → Fin 4` of the summands `exp(-i h_g g Δ)`. For that product to be a
well-defined `Evolution`-valued function of `g`, each summand — including the one for the **identity
string** `g = I^{⊗n}` — must be a single register `Evolution`. This file supplies exactly that total
function and its operator faithfulness; the `O(n)` gate count is `pauliTrotterSummand_circuitBudget`
(`AxQM/Core/PauliTrotterSummandBudget.lean`).

## What this file provides

* `pauliTrotterSummand n g coeff t` — the Trotter summand `exp(-i · coeff · t · g)` of the
  Pauli-string Hamiltonian `coeff · g`, as one `Evolution (qudit (2ⁿ))`, defined by cases on the
  **support** `Concrete.pauliStringSupport g = {k | g k ≠ 0}`:
  * **nonempty support** (a genuine Pauli rotation): the Figure-4.19 compute–rotate–uncompute
    cascade `pauliStringExpCircuit n g c ts (2 · coeff · t)`, with collector `c = min'` of the
    support and remaining support wires `ts = (support.erase c).toList` (so the string's support is
    exactly `insert c ts`);
  * **empty support** (the identity string `g = I^{⊗n}`, whose summand `exp(-i coeff t · I)` is a
    *global phase*, not a Pauli rotation — the part-(3) circuit needs a nonempty support/collector,
    so it does not cover this case): the global-phase gate `globalPhaseGate (-(coeff · t))`.

* `pauliTrotterSummand_op` — **faithfulness, for every `g`**: the summand's operator is the
  propagator of the Pauli-string Hamiltonian, `(pauliTrotterSummand n g coeff t).op =
  ((pauliStringHamiltonian g coeff).propagator 1 0 t).op`, i.e. exactly `exp(-i · coeff · t · g)`
  (N&C's `exp(-i h_g g Δ)` at `coeff = h_g`, `t = Δ`). The nonempty case is the part-(3) result
  `pauliStringExpCircuit_op_eq_propagator` (whose five support hypotheses are discharged from the
  canonical collector/support-list choice); the identity case reduces the propagator's closed form
  `pauliStringHamiltonian_propagator_op` at the all-identity string
  (`(pauliStringHamiltonian g 1).op = 1` via `Concrete.pauliStringStd_zero`) to
  `cos(coeff t)·1 − i·sin(coeff t)·1 = e^{-i coeff t}·1`, Euler's formula
  (`Complex.exp_ofReal_mul_I`) matched against `globalPhaseGate_op`.

## Design notes

* **One total function, not two.** The full Trotter step
  (`AxQM/Postulates/API/PauliTrotterStep.lean`) is the product
  `∏_g pauliTrotterSummand n g (h g) Δ` over the fixed list of all `4ⁿ` strings; its operator equals
  the part-(5) propagator product `∏_g ((pauliStringHamiltonian g (h g)).propagator 1 0 Δ).op`
  precisely because `pauliTrotterSummand_op` holds *uniformly* in `g`. The identity string sits in
  that list and must contribute a real `Evolution` with the right operator (a global phase), so the
  case split lives inside the summand rather than being a special case the product must dodge.
* **Canonical collector/support-list.** The Figure-4.19 circuit `pauliStringExpCircuit` is faithful
  only when its collector `c` and control list `ts` partition the support (`support = insert c ts`,
  `c ∉ ts`, `ts` nodup). Choosing `c = support.min'` and `ts = (support.erase c).toList` makes this
  automatic: `c ∈ support`, `ts` is exactly the rest of the support (nodup as a `Finset.toList`),
  and a qubit off `{c} ∪ ts` is off the support hence `g = 0` there.
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- **The total per-string Trotter summand** `exp(-i · coeff · t · g)` (Nielsen & Chuang,
Problem 4.3(6)), as one `Evolution (qudit (2ⁿ))`, defined for *every* Pauli string
`g : Fin n → Fin 4` by cases on its support `Concrete.pauliStringSupport g`:

* **nonempty support** — a genuine Pauli rotation: the Figure-4.19 cascade
  `pauliStringExpCircuit n g c ts (2 · coeff · t)` with collector `c` the least support wire and
  `ts` the remaining support wires, so `g`'s support is exactly `insert c ts`;
* **empty support** — the identity string `g = I^{⊗n}`, whose summand `exp(-i coeff t · I)` is the
  global phase `e^{-i coeff t} · I`: the gate `globalPhaseGate (-(coeff · t))`.

Its operator is the Trotter summand propagator (`pauliTrotterSummand_op`) and it costs `O(n)`
one- and two-qubit gates (`pauliTrotterSummand_circuitBudget`). For `coeff = h_g`, `t = Δ` this is
N&C's `exp(-i h_g g Δ)`, the factor of the Trotter product `∏_g exp(-i h_g g Δ)`. -/
def pauliTrotterSummand (n : ℕ) (g : Fin n → Fin 4) (coeff t : ℝ) :
    Evolution (qudit (2 ^ n)) :=
  if hne : (Concrete.pauliStringSupport g).Nonempty then
    pauliStringExpCircuit n g ((Concrete.pauliStringSupport g).min' hne)
      (((Concrete.pauliStringSupport g).erase
        ((Concrete.pauliStringSupport g).min' hne)).toList) (2 * coeff * t)
  else
    globalPhaseGate (-(coeff * t))

/-- **Nielsen & Chuang, Problem 4.3(6), faithfulness of the total summand.** For *every* Pauli
string `g : Fin n → Fin 4`, the operator of `pauliTrotterSummand n g coeff t` is the unit-`ℏ`
propagator of the Pauli-string Hamiltonian `coeff · g`,
`(pauliTrotterSummand n g coeff t).op = ((pauliStringHamiltonian g coeff).propagator 1 0 t).op`,
i.e. exactly the Trotter summand `exp(-i · coeff · t · g)` — N&C's `exp(-i h_g g Δ)` for
`coeff = h_g` and `t = Δ`. Uniform in `g`: the nonempty-support case is the part-(3) faithfulness
result `pauliStringExpCircuit_op_eq_propagator` (its five support hypotheses discharged from the
canonical `c = support.min'`, `ts = (support.erase c).toList`), and the identity-string case matches
`globalPhaseGate_op` against the propagator's closed form `pauliStringHamiltonian_propagator_op` at
`g = 0` (Euler's formula, `Complex.exp_ofReal_mul_I`). -/
theorem pauliTrotterSummand_op (g : Fin n → Fin 4) (coeff t : ℝ) :
    (pauliTrotterSummand n g coeff t).op
      = ((pauliStringHamiltonian g coeff).propagator 1 0 t).op := by
  unfold pauliTrotterSummand
  by_cases hne : (Concrete.pauliStringSupport g).Nonempty
  · -- Nonempty support: the Figure-4.19 circuit is faithful (part (3) result).
    rw [dite_eq_left hne]
    set S := Concrete.pauliStringSupport g with hSdef
    set c := S.min' hne with hcdef
    have hcmem : c ∈ S := S.min'_mem hne
    refine pauliStringExpCircuit_op_eq_propagator g c _ ?_ ?_ ?_ ?_ ?_ coeff t
    · rw [Finset.mem_toList]; exact Finset.notMem_erase c S
    · exact Finset.nodup_toList _
    · exact Concrete.mem_pauliStringSupport.mp hcmem
    · intro x hx
      rw [Finset.mem_toList] at hx
      exact Concrete.mem_pauliStringSupport.mp (Finset.mem_of_mem_erase hx)
    · intro k hkc hknm
      by_contra hk
      exact hknm (by
        rw [Finset.mem_toList]
        exact Finset.mem_erase.mpr ⟨hkc, Concrete.mem_pauliStringSupport.mpr hk⟩)
  · -- Empty support: the identity string, whose summand is a global phase.
    rw [dite_eq_right hne]
    have hg0 : g = 0 := by
      funext k
      exact Concrete.notMem_pauliStringSupport.mp fun hk => hne ⟨k, hk⟩
    have hop1 : (pauliStringHamiltonian g 1).op = 1 := by
      rw [pauliStringHamiltonian_op, hg0, Concrete.pauliStringStd_zero, Complex.ofReal_one,
        one_smul]
      exact map_one _
    have hscalar : Complex.exp ((↑(-(coeff * t)) : ℂ) * Complex.I)
        = (↑(Real.cos (coeff * t)) : ℂ) - (↑(Real.sin (coeff * t)) : ℂ) * Complex.I := by
      rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [globalPhaseGate_op, pauliStringHamiltonian_propagator_op, hop1, ← sub_smul, hscalar]

end AxQM
