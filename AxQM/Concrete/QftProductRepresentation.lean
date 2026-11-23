/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QuantumFourierTransform
import ToMathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

/-!
# Concrete: the product representation of the quantum Fourier transform (N&C eq. 5.4)

Nielsen & Chuang, §5.1, derive from the defining action (eq. 5.2)

```
        1  d-1
|j⟩ ↦ ────  Σ   e^{2πi jk/d} |k⟩            (5.2)
       √d  k=0
```

the **product representation** of the `n`-qubit quantum Fourier transform (`d = 2ⁿ`),

```
              (|0⟩ + e^{2πi 0.jₙ}|1⟩)(|0⟩ + e^{2πi 0.jₙ₋₁jₙ}|1⟩)···(|0⟩ + e^{2πi 0.j₁···jₙ}|1⟩)
|j₁…jₙ⟩ ↦  ─────────────────────────────────────────────────────────────────────────────── ,
                                              2^{n/2}
```                                                                                    (5.4)

obtained (eqs. 5.5–5.10) purely from the factorisation of the Fourier kernel over the bits of the
**output** index `k`: writing `k = ∑ₗ kₗ 2ˡ`,

```
  e^{2πi jk/2ⁿ}  =  ∏ₗ e^{2πi j kₗ 2ˡ / 2ⁿ}  =  ∏ₗ (e^{2πi j 2ˡ/2ⁿ})^{kₗ} .          (5.7)
```

N&C call this representation "so useful that you may even wish to consider this to be the definition
of the quantum Fourier transform": it is the bridge that turns the monolithic matrix `qftMatrix 2ⁿ`
into a **circuit** of one-qubit gates (Figure 5.1), and it is the object every gate-level QFT
argument reduces to.

## What is formalised

This file works with the matrix `Concrete.qftMatrix`: it establishes the kernel factorisation
(5.7) — hence the amplitude form of (5.4) — for a general number of qubits `n`,
indexing the `2ⁿ`-dimensional register by bit strings
`kbits : Fin n → Fin 2` through `finFunctionFinEquiv` (`k = ∑ₗ kₗ 2ˡ`, little-endian).

* `qftWirePhase n j l = e^{2πi · j · 2ˡ / 2ⁿ}` — the **single-qubit output phase** attached to wire
  `l` in the product representation (the `e^{2πi 0.j…}` factor of (5.4); by periodicity it depends
  only on `j mod 2^{n−l}`, i.e. the binary fraction `0.j_{…}`). `norm_qftWirePhase` records that it
  is a unit-modulus phase, `‖qftWirePhase n j l‖ = 1`.
* `qftMatrix_apply_prod` — the kernel factorisation (5.7): the `(k, j)` entry of `qftMatrix 2ⁿ`, at
  `k = finFunctionFinEquiv kbits`, factors as `(1/√2ⁿ) · ∏ₗ e^{2πi j (kₗ 2ˡ)/2ⁿ}`.
* `qftMatrix_apply_eq_prod_wirePhase` — the product representation (5.4) proper: the same entry is
  `(1/√2ⁿ) · ∏ₗ (qftWirePhase n j l)^{kₗ}`, exhibiting column `j` of the QFT as the tensor product
  `⨂ₗ (|0⟩ + qftWirePhase n j l · |1⟩)/√2` in the computational basis (the factor for wire `l` is
  `1` when `kₗ = 0` and `qftWirePhase n j l` when `kₗ = 1`).

## Why this file exists (Exercise 5.6)

The faithful `Ω(n²/p(n))` half of Exercise 5.6 (the approximate QFT: perturbing the controlled-`Rₖ`
gates to precision `Δ = 1/p(n)` costs error `Θ(n²/p(n))`) requires the **gate-level** Figure 5.1
circuit as a formal object — a decomposition `qftMatrix 2ⁿ = (Hadamards · controlled-Rₖ · swaps)`
whose `Rₖ` factors one then perturbs (the abstract chaining tightness in
`Postulates/API/ApproxErrorTight.lean` is QFT-agnostic and does not, by itself, give a faithful
lower bound). Proving that gate decomposition correct is exactly proving the circuit reproduces the
product representation (5.4); this file supplies its right-hand side — the amplitude target the
gate-by-gate computation must hit, and the product-of-phases structure the coherent
`Rₖ`-perturbation lower bound exploits. It is reusable QFT infrastructure (the general-`n`
counterpart of the two-qubit factorisation `qftFour_eq_prod`), built ahead of the gate-level circuit
that consumes it.

The matrix `qftMatrix` itself is defined in `AxQM/Concrete/QuantumFourierTransform.lean`.
-/

namespace AxQM.Concrete

open Complex

/-- The **single-qubit output phase** of the quantum Fourier transform on wire `l` (Nielsen &
Chuang eq. 5.4): `qftWirePhase n j l = e^{2πi · j · 2ˡ / 2ⁿ}`. This is the phase `e^{2πi 0.j_{…}}`
that multiplies `|1⟩` on output wire `l` in the product representation of `F|j⟩`; by the periodicity
of the exponential it depends only on `j mod 2^{n−l}` — the binary fraction `0.j_{…}` of N&C's
notation. -/
noncomputable def qftWirePhase (n : ℕ) (j : Fin (2 ^ n)) (l : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * 2 ^ (l : ℕ)) / (2 ^ n : ℕ))

/-- The single-qubit output phase is a **unit-modulus phase**: `‖qftWirePhase n j l‖ = 1`. Its
argument `2πi · j · 2ˡ/2ⁿ` is purely imaginary, so `‖e^{iθ}‖ = 1`
(`Complex.norm_exp_ofReal_mul_I`). -/
theorem norm_qftWirePhase (n : ℕ) (j : Fin (2 ^ n)) (l : Fin n) :
    ‖qftWirePhase n j l‖ = 1 := by
  rw [qftWirePhase,
    show (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * 2 ^ (l : ℕ)) / (2 ^ n : ℕ) : ℂ)
        = ((2 * Real.pi * ((j : ℕ) * 2 ^ (l : ℕ)) / (2 ^ n : ℕ) : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The Fourier-kernel factorisation over the output bits** (Nielsen & Chuang eq. 5.7). Writing
the output index `k` in binary as `k = finFunctionFinEquiv kbits = ∑ₗ kₗ 2ˡ`, the `(k, j)` entry of
`2ⁿ`-dimensional quantum Fourier transform matrix factors over the `n` wires:

`qftMatrix 2ⁿ k j = (1/√2ⁿ) · ∏ₗ e^{2πi · j · (kₗ · 2ˡ) / 2ⁿ}`.

This is the algebraic heart of the QFT's product representation (5.4): `e^{2πi jk/2ⁿ} = ∏ₗ e^{2πi j
kₗ 2ˡ/2ⁿ}` because `jk = ∑ₗ j kₗ 2ˡ` (`finFunctionFinEquiv_apply_val`), and `Complex.exp` turns the
sum in the exponent into the product (`Complex.exp_sum`). -/
theorem qftMatrix_apply_prod (n : ℕ) (j : Fin (2 ^ n)) (kbits : Fin n → Fin 2) :
    qftMatrix (2 ^ n) (finFunctionFinEquiv kbits) j
      = (Real.sqrt (2 ^ n : ℕ) : ℂ)⁻¹ *
        ∏ l : Fin n, Complex.exp (2 * Real.pi * Complex.I *
          ((j : ℕ) * ((kbits l : ℕ) * 2 ^ (l : ℕ))) / (2 ^ n : ℕ)) := by
  have hkC : (((finFunctionFinEquiv kbits : Fin (2 ^ n)) : ℕ) : ℂ)
      = ∑ i, ((kbits i : ℕ) : ℂ) * 2 ^ (i : ℕ) := by
    rw [finFunctionFinEquiv_apply_val]; push_cast; ring
  rw [qftMatrix_apply, ← Complex.exp_sum]
  congr 1
  congr 1
  rw [hkC, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]

/-- **The product representation of the quantum Fourier transform** (Nielsen & Chuang eq. 5.4). At
output index `k = finFunctionFinEquiv kbits`, the `(k, j)` entry of `qftMatrix 2ⁿ` is

`qftMatrix 2ⁿ k j = (1/√2ⁿ) · ∏ₗ (qftWirePhase n j l)^{kₗ}`,

so column `j` of the QFT is the tensor product `⨂ₗ (|0⟩ + qftWirePhase n j l · |1⟩)/√2` in the
computational basis: on wire `l` the amplitude carries the single-qubit phase `qftWirePhase n j l`
raised to the output bit `kₗ` (a factor of `1` when `kₗ = 0`, and the phase itself when `kₗ = 1`).
The bit-power form follows from the kernel factorisation `qftMatrix_apply_prod` by pulling the bit
`kₗ` out of the exponent (`Complex.exp_natCast_mul`). -/
theorem qftMatrix_apply_eq_prod_wirePhase (n : ℕ) (j : Fin (2 ^ n)) (kbits : Fin n → Fin 2) :
    qftMatrix (2 ^ n) (finFunctionFinEquiv kbits) j
      = (Real.sqrt (2 ^ n : ℕ) : ℂ)⁻¹ * ∏ l : Fin n, qftWirePhase n j l ^ (kbits l : ℕ) := by
  rw [qftMatrix_apply_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  rw [qftWirePhase, ← Complex.exp_natCast_mul]
  congr 1
  push_cast
  ring

end AxQM.Concrete
