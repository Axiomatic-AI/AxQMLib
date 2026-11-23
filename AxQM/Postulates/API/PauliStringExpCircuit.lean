/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CnotFanEvolution
import AxQM.Postulates.API.CollectorZRotationEvolution
import AxQM.Postulates.API.PauliDiagWire
import AxQM.Postulates.API.InvolutiveObservable

/-!
# The Figure-4.19 circuit for a Trotter summand, and its faithfulness (N&C Problem 4.3(3))

Nielsen & Chuang **Problem 4.3(3)** asks to implement the Trotter summand `exp(-i h_g g Δ)` — the
unit-`ℏ` propagator `exp(-i c t · g)` of a single Pauli-string Hamiltonian `c · g` — with `O(n)`
one- and two-qubit gates. The construction is the compute–rotate–uncompute cascade of Figure
4.19 (N&C §4.7.3):

1. a layer `B = ⨂ₖ B_{gₖ}` of single-qubit basis-change gates diagonalising each Pauli factor of `g`
   to `Z` (`pauliDiagLayer`, `Postulates/API/PauliDiagWire`);
2. a fan `V` of `CNOT`s computing the support parity onto a collector wire `c`
   (`cnotFanIntoEvolution`, `Postulates/API/CnotFanEvolution`), reversed as `V†`;
3. a single-qubit `z`-rotation `exp(-i c t · Z_c)` on the collector (`rotZWireEvolution`);
4. uncomputation `V` and `B†`.

The preceding files of this sub-project built each piece as a register `Evolution` on `qudit (2ⁿ)`,
established its operator (`pauliDiagLayer_op`, `cnotFanIntoEvolution_op`,
`rotZWireEvolution_op_eq_exp_smul_zGenPauli`) and, for the `CircuitBudget`, its elementary-gate
count. This file **assembles** them and proves the assembly is *faithful*: the composite circuit's
operator is exactly the Trotter summand.

## What is formalised

* `pauliStringExpCircuit n g c ts θ` — the Figure-4.19 circuit `B · V† · R_z · V · B†` as one
  `Evolution (qudit (2ⁿ))` (the `V†`/`B†` uncomputation are the `Evolution` adjoints of the fan and
  the basis-change layer). Here `c` is the collector wire, `ts` the remaining support wires (so the
  support of `g` is `insert c ts`), and `θ` the collector-rotation angle.

* `pauliStringExpCircuit_op` — **the closed form**: for a Pauli string `g` whose support is exactly
  `insert c ts` (`g c ≠ 0`, `g t ≠ 0` on `ts`, `g k = 0` off `insert c ts`), the circuit's operator
  is the rotation `cos(θ/2) · 1 − (sin(θ/2) · i) · P_g`, where `P_g = Matrix.toEuclideanCLM
  (pauliStringStd g)` is the Pauli-string operator (an involution). The Figure-4.19 cascade really
  *is* the single-axis rotation about the Pauli string `g`, not merely some product of `O(n)` gates.

* `pauliStringExpCircuit_op_eq_propagator` — **the faithfulness headline**: taking `θ = 2 c t`, the
  circuit's operator equals the Trotter summand `((pauliStringHamiltonian g c).propagator 1 0 t).op
  = exp(-i c t · g)`. So `pauliStringExpCircuit n g c ts (2 c t)` implements `exp(-i h_g g Δ)` for
  `c = h_g`, `t = Δ` — the operator Problem 4.3(3) asks to realise. (The `O(n)` elementary-gate
  `CircuitBudget` of this same assembly is `pauliStringExpCircuit_circuitBudget`
  (`AxQM/Core/PauliStringExpCircuitBudget.lean`), folding the per-piece budgets
  `pauliDiagLayer_circuitBudget`, `cnotFanIntoEvolution_circuitBudget`,
  `rotZWireEvolution_circuitBudget` and their adjoints.)

## Proof design

The correctness composes the two matrix cores, kept entirely on the bit-string register
`Fin n → Fin 2` so the exponential never meets a `.submatrix`:

* `Concrete.pauliString_exp_smul_conj_kronFamily_pauliDiagGate` (basis change):
  `exp(s · g) = B · exp(s · d(g)) · B†`, `d(g) = pauliToZ ∘ g`;
* `Concrete.pauliString_exp_smul_conj_cnotFanInto` (Figure-4.19 parity):
  `exp(s · d(g)) = V† · exp(s · Z_c) · V`.

Composing gives the bit-string identity `B · V† · exp(s · Z_c) · V · B† = exp(s · g)`. The circuit's
operator is `Matrix.toEuclideanCLM` of exactly that five-fold product, each factor reindexed to the
flat register `Fin (2ⁿ)` by the `.submatrix finFunctionFinEquiv.symm` that the `_op` faithfulness
lemmas produce (the two adjoints `V†`/`B†` supply the conjugate transposes via
`Matrix.toEuclideanCLM_conjTranspose_eq_adjoint`); `Matrix.submatrix_mul_equiv` folds the product,
`map_mul` folds the `toEuclideanCLM`s, so the whole operator is
`toEuclideanCLM ((exp(s · g)).submatrix …)`. Finally `exp(s · g)` collapses to the rotation
`cos − i sin` because `pauliString g` is an involution
(`NormedSpace.exp_smul_mul_I_of_mul_self_eq_one`, `Concrete.pauliString_mul_self`), and that closed
form — being *linear* in `1` and `pauliString g` — reindexes and transports through `toEuclideanCLM`
without any `exp`/`submatrix` commutation. The collector-rotation scalar is `s = (−θ/2) i`, so
`θ = 2 c t` gives `s = -i c t`, matching the summand.
-/

open Matrix
open scoped InnerProductSpace
-- The `L∞` operator norm supplies the `NormedRing`/`NormedAlgebra ℂ (Matrix …)` instances that
-- `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` needs to collapse the bit-string exponential to a
-- rotation; the resulting matrix `exp` is norm-independent (this only enables the lemma).
open scoped Matrix.Norms.Operator

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The Nielsen–Chuang Figure-4.19 circuit for a Pauli-string Trotter summand.** The
compute–rotate–uncompute cascade `B · V† · R_z(θ) · V · B†` implementing `exp(-i c t · g)` (for
`θ = 2 c t`), as one `Evolution (qudit (2ⁿ))`:

* `B = pauliDiagLayer n g` — the layer of single-qubit basis-change gates diagonalising each Pauli
  factor of `g` to `Z`; `B†` its adjoint;
* `V = cnotFanIntoEvolution n c ts` — the `CNOT` fan computing the support parity onto the collector
  wire `c` (controls `ts`); `V†` its adjoint (the uncomputation);
* `R_z(θ) = rotZWireEvolution n c θ` — the single-qubit `z`-rotation on the collector.

Reading the product right-to-left (the order gates act on a state): apply `B†`, then the parity fan
`V`, then the collector rotation, then uncompute the fan `V†`, then `B`. For a Pauli string whose
support is `insert c ts`, this realises `exp(-i c t · g)` (`pauliStringExpCircuit_op_eq_propagator`)
using `O(n)` elementary gates. -/
def pauliStringExpCircuit (n : ℕ) (g : Fin n → Fin 4) (c : Fin n) (ts : List (Fin n)) (θ : ℝ) :
    Evolution (qudit (2 ^ n)) :=
  pauliDiagLayer n g
    * (cnotFanIntoEvolution n c ts).adjoint
    * rotZWireEvolution n c θ
    * cnotFanIntoEvolution n c ts
    * (pauliDiagLayer n g).adjoint

/-- **Problem 4.3(3): the Figure-4.19 circuit is a Pauli-string rotation.** For a Pauli string `g`
whose support is exactly `insert c ts` (`g c ≠ 0`, `g t ≠ 0` for `t ∈ ts`, and `g k = 0` for every
`k` off `insert c ts`; `ts` duplicate-free with `c ∉ ts`), the operator of the assembled cascade
`pauliStringExpCircuit n g c ts θ` is the single-axis rotation

`toEuclideanCLM (cos(θ/2) · 1 − (sin(θ/2) · i) · pauliStringStd g)`

about the Pauli string `g`. This is the **faithfulness** of the Figure-4.19 assembly: the composite
of the basis-change layer, the parity `CNOT` fan, the collector `z`-rotation and the two
uncomputations really computes the Pauli-string rotation, not merely some `O(n)`-gate circuit.

The proof keeps the exponential on the bit-string register: the basis-change reduction
(`pauliString_exp_smul_conj_kronFamily_pauliDiagGate`) and the parity collapse
(`pauliString_exp_smul_conj_cnotFanInto`) compose to `B · V† · exp(s · Z_c) · V · B† = exp(s · g)`
(`s = (−θ/2) i`); the circuit operator is `toEuclideanCLM` of that five-fold product reindexed to
the register (`_op` faithfulness lemmas + `Matrix.submatrix_mul_equiv` + `map_mul`, the two adjoints
supplying the conjugate transposes via `Matrix.toEuclideanCLM_conjTranspose_eq_adjoint`); and
`exp(s · g)` collapses to the rotation because `pauliString g` is an involution
(`NormedSpace.exp_smul_mul_I_of_mul_self_eq_one`). -/
theorem pauliStringExpCircuit_op {n : ℕ} (g : Fin n → Fin 4) (c : Fin n) (ts : List (Fin n))
    (hc : c ∉ ts) (hnd : ts.Nodup) (hgc : g c ≠ 0) (hgts : ∀ t ∈ ts, g t ≠ 0)
    (hrest : ∀ k, k ≠ c → k ∉ ts → g k = 0) (θ : ℝ) :
    (pauliStringExpCircuit n g c ts θ).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
          ((Real.cos (θ / 2) : ℂ) • 1
            - ((Real.sin (θ / 2) : ℂ) * Complex.I) • Concrete.pauliStringStd g) := by
  set s : ℂ := ((-(θ / 2) : ℝ) : ℂ) * Complex.I with hs
  -- The `pauliToZ ∘ g` string is `Z` exactly on `insert c ts` (the support hypotheses on `g`).
  have hac : Concrete.pauliToZ (g c) = 3 := Concrete.pauliToZ_eq_three_of_ne_zero _ hgc
  have hats : ∀ t ∈ ts, Concrete.pauliToZ (g t) = 3 := fun t ht =>
    Concrete.pauliToZ_eq_three_of_ne_zero _ (hgts t ht)
  have harest : ∀ k, k ≠ c → k ∉ ts → Concrete.pauliToZ (g k) = 0 := fun k h1 h2 =>
    Concrete.pauliToZ_eq_zero_iff.mpr (hrest k h1 h2)
  -- The bit-string identity `B · V† · exp(s·Z_c) · V · B† = exp(s · g)` (five-fold, left-assoc).
  have hMprime :
      kronFamily (fun k => pauliDiagGate (g k)) * (cnotFanInto c ts).toMatrixᴴ
          * NormedSpace.exp (s • Concrete.pauliString (Concrete.zGenPauli c))
          * (cnotFanInto c ts).toMatrix * (kronFamily (fun k => pauliDiagGate (g k)))ᴴ
      = NormedSpace.exp (s • Concrete.pauliString g) := by
    rw [Concrete.pauliString_exp_smul_conj_kronFamily_pauliDiagGate g s,
      Concrete.pauliString_exp_smul_conj_cnotFanInto c ts hc hnd (fun k => Concrete.pauliToZ (g k))
        hac hats harest s]
    simp only [mul_assoc]
  -- The five-fold Std product on `Fin (2ⁿ)` folds (via `submatrix_mul_equiv`) to the reindexed
  -- bit-string exponential.
  have hStd :
      kronFamilyStd (fun k => pauliDiagGate (g k))
          * ((cnotFanInto c ts).toMatrix.submatrix finFunctionFinEquiv.symm
              finFunctionFinEquiv.symm)ᴴ
          * (NormedSpace.exp (s • Concrete.pauliString (Concrete.zGenPauli c))).submatrix
              finFunctionFinEquiv.symm finFunctionFinEquiv.symm
          * (cnotFanInto c ts).toMatrix.submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm
          * (kronFamilyStd (fun k => pauliDiagGate (g k)))ᴴ
      = (NormedSpace.exp (s • Concrete.pauliString g)).submatrix finFunctionFinEquiv.symm
          finFunctionFinEquiv.symm := by
    simp only [kronFamilyStd, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    rw [hMprime]
  -- The circuit operator as `toEuclideanCLM` of the reindexed bit-string exponential. The two
  -- uncomputation adjoints `V†`, `B†` are the citable adjoint companions
  -- `cnotFanIntoEvolution_adjoint_op` / `pauliDiagLayer_adjoint_op` of the forward `_op` lemmas.
  have hcircop : (pauliStringExpCircuit n g c ts θ).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
          ((NormedSpace.exp (s • Concrete.pauliString g)).submatrix
            finFunctionFinEquiv.symm finFunctionFinEquiv.symm) := by
    rw [← hStd, map_mul, map_mul, map_mul, map_mul, pauliStringExpCircuit]
    simp only [Evolution.mul_def, Evolution.comp_op, cnotFanIntoEvolution_adjoint_op,
      pauliDiagLayer_adjoint_op, pauliDiagLayer_op, cnotFanIntoEvolution_op,
      rotZWireEvolution_op_eq_exp_smul_zGenPauli, ← hs, ContinuousLinearMap.mul_def]
    rfl
  rw [hcircop]
  congr 1
  -- The bit-string exponential collapses to the rotation `cos − i sin` (`pauliString g` is an
  -- involution), and reindexing the linear combination commutes with `submatrix` (`reindexAlgEquiv`
  -- is a ⋆-algebra iso, so `map_add`/`map_smul`/`map_one` distribute over the rotation).
  have hexp : NormedSpace.exp (s • Concrete.pauliString g)
      = (Real.cos (-(θ / 2)) : ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
        + ((Real.sin (-(θ / 2)) : ℂ) * Complex.I) • Concrete.pauliString g := by
    rw [hs]
    exact NormedSpace.exp_smul_mul_I_of_mul_self_eq_one (Concrete.pauliString_mul_self g) (-(θ / 2))
  rw [hexp,
    show ((Real.cos (-(θ / 2)) : ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
          + ((Real.sin (-(θ / 2)) : ℂ) * Complex.I) • Concrete.pauliString g).submatrix
          finFunctionFinEquiv.symm finFunctionFinEquiv.symm
        = Matrix.reindexAlgEquiv ℂ ℂ finFunctionFinEquiv
            ((Real.cos (-(θ / 2)) : ℂ) • 1
              + ((Real.sin (-(θ / 2)) : ℂ) * Complex.I) • Concrete.pauliString g) from rfl,
    map_add, map_smul, map_smul, map_one, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul,
    neg_smul, ← sub_eq_add_neg]
  rfl

/-- **Problem 4.3(3) faithfulness headline: the Figure-4.19 circuit implements `exp(-i h_g g Δ)`.**
For a Pauli string `g` whose support is exactly `insert c ts`, the assembled cascade
`pauliStringExpCircuit n g c ts (2 c t)` (basis change, parity `CNOT` fan, collector `z`-rotation at
angle `θ = 2 c t`, and the two uncomputations) has operator equal to the Trotter summand — the
unit-`ℏ` propagator of the Pauli-string Hamiltonian `c · g`:

`(pauliStringExpCircuit n g c ts (2 c t)).op = ((pauliStringHamiltonian g c).propagator 1 0 t).op`,

i.e. `exp(-i c t · g)`. So the circuit realises the operator `exp(-i h_g g Δ)` of Problem 4.3(3) for
`c = h_g`, `t = Δ = 1/k`. The proof puts both sides in the common closed form
`toEuclideanCLM (cos(c t) · 1 − (sin(c t) · i) · pauliStringStd g)`: the circuit side is
`pauliStringExpCircuit_op` (with `θ/2 = c t`), and the summand side is the involution rotation law
`pauliStringHamiltonian_propagator_op` transported through `toEuclideanCLM`
(`pauliStringHamiltonian_op`, `map_one`/`map_smul`/`map_sub`). The `O(n)` elementary-gate
`CircuitBudget` of the same `pauliStringExpCircuit` is `pauliStringExpCircuit_circuitBudget`. -/
theorem pauliStringExpCircuit_op_eq_propagator {n : ℕ} (g : Fin n → Fin 4) (c : Fin n)
    (ts : List (Fin n)) (hc : c ∉ ts) (hnd : ts.Nodup) (hgc : g c ≠ 0) (hgts : ∀ t ∈ ts, g t ≠ 0)
    (hrest : ∀ k, k ≠ c → k ∉ ts → g k = 0) (coeff t : ℝ) :
    (pauliStringExpCircuit n g c ts (2 * coeff * t)).op
      = ((pauliStringHamiltonian g coeff).propagator 1 0 t).op := by
  have hθ : (2 * coeff * t) / 2 = coeff * t := by ring
  rw [pauliStringExpCircuit_op g c ts hc hnd hgc hgts hrest, hθ,
    pauliStringHamiltonian_propagator_op, pauliStringHamiltonian_op g 1, Complex.ofReal_one,
    one_smul, map_sub, map_smul, map_smul, map_one]
  rfl

end

end AxQM
