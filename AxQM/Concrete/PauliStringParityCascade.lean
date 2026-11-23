/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerZClear
import AxQM.Concrete.PauliStringDiagonalize

/-!
# Concrete: the Figure-4.19 parity circuit — collapse `exp(s · Z^{⊗S})` to a single `Z`-rotation

This file is the **second step** of Nielsen & Chuang **Problem 4.3(3)** — "implement
`exp(-i h_g g Δ)` using `O(n)` one- and two-qubit gates" — the *parity computation* that follows
the single-qubit basis change of `Concrete/PauliStringDiagonalize.lean`.

## The construction (N&C §4.7.3, Figure 4.19)

After the local basis change diagonalises a Pauli string to an operator that is `Z` on its support
`S` and `I` elsewhere (`d(g) = pauliToZ ∘ g`), the remaining task is to implement
`exp(s · Z^{⊗S})` — a diagonal unitary applying a phase that depends on the **parity**
`⊕_{i∈S} xᵢ` of the support bits. Nielsen & Chuang's Figure 4.19 computes this parity into a single
*collector* wire `c ∈ S` with a fan of `CNOT`s, applies one single-qubit `Z`-rotation
`exp(s · Z_c)` on the collector, then uncomputes the fan:
`exp(s · Z^{⊗S}) = V† · exp(s · Z_c) · V`, where `V` is the `CNOT` fan and `V†` its uncomputation.
Only `2·(|S|−1)` `CNOT`s and one rotation are used — `O(n)` elementary gates.

## Reuse: the Gottesman `CNOT`-fan already in the library

The `CNOT` fan `V = cnotFanInto c ts` (controls `ts`, target `c`), built for the Clifford-normalizer
synthesis of Theorem 10.6, already carries the Pauli-conjugation facts we need
(`Concrete/PauliNormalizerZClear.lean`): `act_cnotFanInto_collapse` proves the fan conjugates the
all-`Z` string on `insert c ts` back to the single generator `zGenPauli c` (`Z` on the collector,
`I` on every control), and `sign_cnotFanInto_collapse` proves this acquires no `±1` phase. The
`z_c += z_t` propagation of `CNOT_{t→c}` (Figure 10.7) *is* the parity accumulation of Figure 4.19.
So this file needs only to push those facts through the exponential; the `O(n)` gate count is
`length_cnotFanInto_le`.

## What is proved

For a collector `c ∉ ts` with a duplicate-free control list `ts`, and any Pauli string `a` that is
`Z` (letter `3`) exactly on `insert c ts` and `I` elsewhere:

* `cnotFanInto_act_eq_zGenPauli` — the fan's symplectic action collapses `a` to `zGenPauli c`.
* `cnotFanInto_toMatrix_conj_pauliString_eq_zGenPauli` — the operator collapse
  `V · P_a · V† = P_{Z_c}` (no sign).
* `pauliString_exp_smul_conj_cnotFanInto` — the exponentiated **Figure-4.19 identity**
  `exp(s · P_a) = V† · exp(s · P_{Z_c}) · V` for any scalar `s` (physically `s = -i h_g Δ`): the
  exponential of the diagonalised (all-`Z`-on-support) Hamiltonian is the collector `Z`-rotation
  conjugated by the `CNOT` parity fan. Reading right-to-left, this is exactly "compute the parity
  (`V`), rotate the collector (`exp(s · Z_c)`), uncompute (`V†`)".

The string `a` is the output `pauliToZ ∘ g` of `Concrete/PauliStringDiagonalize.lean` (`Z` on the
support of `g`), so chaining the two files reduces `exp(s · g)` for an arbitrary Pauli string `g` to
a single single-qubit `Z`-rotation conjugated by an `O(n)`-gate circuit. Every statement is about
raw matrix / index data (`Concrete.CliffordCircuit`, `Concrete.pauliString`, `Concrete.zGenPauli`,
`NormedSpace.exp`).
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- **Figure-4.19 parity collapse (symplectic form).** For a collector `c ∉ ts` (`ts.Nodup`) and a
Pauli string `a` that is `Z` (`3`) on `c` and on every wire of `ts` and `I` (`0`) on every other
wire, the reverse `CNOT` fan `cnotFanInto c ts` conjugates `a` to the single `Z` generator
`zGenPauli c`. Packages the pointwise `act_cnotFanInto_collapse` (which clears the `Z` off each
control and keeps it on the collector) into the equality of Pauli strings, using the support
hypothesis `hrest` to kill the `else a k` branch off the support. -/
theorem cnotFanInto_act_eq_zGenPauli (c : Fin n) (ts : List (Fin n)) (hc : c ∉ ts)
    (hnd : ts.Nodup) (a : Fin n → Fin 4) (hac : a c = 3) (hts : ∀ t ∈ ts, a t = 3)
    (hrest : ∀ k, k ≠ c → k ∉ ts → a k = 0) :
    (cnotFanInto c ts).act a = zGenPauli c := by
  funext k
  rw [act_cnotFanInto_collapse c ts hc hnd a hac hts k]
  simp only [zGenPauli, Function.update_apply, Pi.zero_apply]
  by_cases hkc : k = c
  · simp [hkc]
  · rw [ite_eq_right hkc, ite_eq_right hkc]
    by_cases hkt : k ∈ ts
    · rw [ite_eq_left hkt]
    · rw [ite_eq_right hkt]; exact hrest k hkc hkt

/-- **Figure-4.19 parity collapse (operator form).** Under the same hypotheses, the `CNOT` fan
conjugates the operator `P_a` (`Z` on `insert c ts`) to the collector generator `P_{Z_c}` with no
sign: `V · P_a · V† = P_{Z_c}`. Immediate from `CliffordCircuit.conj_pauliString` together with the
trivial sign (`sign_cnotFanInto_collapse`) and the symplectic collapse
(`cnotFanInto_act_eq_zGenPauli`). -/
theorem cnotFanInto_toMatrix_conj_pauliString_eq_zGenPauli (c : Fin n) (ts : List (Fin n))
    (hc : c ∉ ts) (hnd : ts.Nodup) (a : Fin n → Fin 4) (hac : a c = 3) (hts : ∀ t ∈ ts, a t = 3)
    (hrest : ∀ k, k ≠ c → k ∉ ts → a k = 0) :
    (cnotFanInto c ts).toMatrix * pauliString a * (cnotFanInto c ts).toMatrixᴴ
      = pauliString (zGenPauli c) := by
  rw [CliffordCircuit.conj_pauliString, sign_cnotFanInto_collapse c ts hc hnd a hac hts,
    cnotFanInto_act_eq_zGenPauli c ts hc hnd a hac hts hrest, one_smul]

/-- **Problem 4.3(3), exponentiated form: the Figure-4.19 parity circuit for `exp(s · Z^{⊗S})`.**
For any complex scalar `s` (physically `s = -i h_g Δ`), the exponential of the diagonalised
(all-`Z`-on-support) Hamiltonian `a` is the single collector `Z`-rotation conjugated by the `CNOT`
parity fan:
`exp(s · P_a) = V† · exp(s · P_{Z_c}) · V`, `V = cnotFanInto c ts`.
Reading the right side right-to-left: apply the fan `V` (compute the parity of the support onto the
collector `c`), apply the single-qubit rotation `exp(s · Z_c)` on the collector, then apply `V†`
(uncompute the parity) — Nielsen & Chuang's Figure 4.19.

The proof mirrors `pauliStringStd_exp_smul_conj_kronFamilyStd_pauliDiagGate`: the operator collapse
`V · P_a · V† = P_{Z_c}` (`cnotFanInto_toMatrix_conj_pauliString_eq_zGenPauli`) together with the
unitarity of the Clifford circuit `V` feeds the reusable matrix-exponential lemma
`Matrix.exp_smul_conj_of_conj_eq` (which packages `Matrix.exp_units_conj` with the `s • ` scalar
and the equational conjugation hypothesis), carrying the conjugation through the exponential in one
step. The fan uses `O(n)` `CNOT`s (`length_cnotFanInto_le`). -/
theorem pauliString_exp_smul_conj_cnotFanInto (c : Fin n) (ts : List (Fin n)) (hc : c ∉ ts)
    (hnd : ts.Nodup) (a : Fin n → Fin 4) (hac : a c = 3) (hts : ∀ t ∈ ts, a t = 3)
    (hrest : ∀ k, k ≠ c → k ∉ ts → a k = 0) (s : ℂ) :
    NormedSpace.exp (s • pauliString a)
      = (cnotFanInto c ts).toMatrixᴴ
          * NormedSpace.exp (s • pauliString (zGenPauli c))
          * (cnotFanInto c ts).toMatrix := by
  have hmul_CH : (cnotFanInto c ts).toMatrix * (cnotFanInto c ts).toMatrixᴴ = 1 :=
    CliffordCircuit.mul_conjTranspose _
  exact Matrix.exp_smul_conj_of_conj_eq _ _ _ _ hmul_CH (mul_eq_one_comm.mp hmul_CH)
    (cnotFanInto_toMatrix_conj_pauliString_eq_zGenPauli c ts hc hnd a hac hts hrest) s

end AxQM.Concrete
