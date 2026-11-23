/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HarmonicOscillatorAmplitudeDamping
import AxQM.Concrete.HarmonicOscillatorBeamSplitter

/-!
# Nielsen & Chuang, Exercise 8.21 (amplitude damping of a harmonic oscillator)

*(N&C p. 381.)*

Show H=χ(a†b+b†a) gives amplitude-damping operation elements E_k and that they are trace-preserving.

## The answer

The oscillator's number states `|n⟩` (`n : ℕ`, eigenstates of `a†a`) span the infinite-dimensional
Fock space. The operation element `Eₖ` (eq. 8.110) lowers the quantum number by `k`, sending `|n⟩`
to `|n-k⟩` with amplitude `√( C(n,k) (1-γ)^{n-k} γ^k )` — the amplitude for exactly `k` of the `n`
quanta to be lost. Part **(2)** is the completeness relation `Σₖ Eₖ† Eₖ = I`: each `Eₖ† Eₖ` is the
diagonal operator `Σₙ C(n,k) (1-γ)^{n-k} γ^k |n⟩⟨n|`, and summing over `k` the diagonal entry at
level `n` is the binomial identity `Σₖ C(n,k) (1-γ)^{n-k} γ^k = ((1-γ)+γ)^n = 1` — the number of
quanta lost is binomially distributed, so the total probability is one and the operation preserves
the trace.

## Scope

Part **(2)** — that the operation elements define a *trace-preserving* quantum operation — is the
substantive completeness claim, and it is proved in full
(`AxQM/Concrete/HarmonicOscillatorAmplitudeDamping.lean`). Part **(1)** — the *derivation* of
eq. 8.110 from `U = exp(-iHΔt)`, `H = χ(a†b + b†a)` — is developed in full in
`AxQM/Concrete/HarmonicOscillatorBeamSplitter.lean`. The key structural fact is that `H`
**conserves the total quantum number** `N = a†a + b†b`: it is block diagonal over the
finite-dimensional excitation-number sectors, so `U` is the direct sum of its restrictions
`Uⁿ = exp(-iθMₙ)` (`θ = χΔt`) to the `(n+1)`-dimensional sectors, and `Eₖ = ⟨k_b|U|0_b⟩` reads
off their first columns — the whole content of eq. 8.110 is captured *sector by sector*, by genuine
**finite** matrix exponentials, with no unbounded-operator / Stone's-theorem apparatus. `Mₙ`
(`fockBeamGen`) is the honest number-basis
matrix of `a†b + b†a` (tridiagonal, entries `√((j+1)(n-j))`); `Uⁿ` (`fockBeamProp`) is unitary; the
claimed first-column amplitude `√(C(n,k)) cosⁿ⁻ᵏθ (-i sinθ)ᵏ` (`fockBeamAmp`) has modulus the
eq.-8.110 amplitude (`fockBeamAmp_norm`), with `γ = 1 - cos²θ = sin²θ ∈ [0,1]`. The sector
framework, the base cases `n = 0` (vacuum) and `n = 1` (`U¹ = exp(-iθX) = cosθ·I - i sinθ·X`,
eq. 8.110 at `n = 1`), the general-`n` first column (by ODE uniqueness, `fockBeamProp_col`), and the
assembly of the `ℕ`-indexed operation element `Eₖ` (`fockBeamKraus`, reconciled with part (2)) are
all proved; part (1) is complete.

The Fock space is infinite-dimensional, so it is not an `AxQM.QSystem` (which bundles a
finite-dimensional Hilbert space, `QSystem.findim`). The formal content of the exercise is pure
mathematics about matrices, matrix exponentials and binomial coefficients (`Matrix`,
`NormedSpace.exp`, `Nat.choose`, `Real.cos`/`sin`, `Real.sqrt`). Compare Exercises 8.16 and 8.17.

## The formalisation

The formalisation is in the files below.

* `AxQM/Concrete/HarmonicOscillatorBeamSplitter.lean` — **part (1), the derivation of
  eq. 8.110 from `U = exp(-iHΔt)`, complete**, including the assembly of the `ℕ`-indexed operation
  elements `Eₖ` and their reconciliation with part (2):
  * `AxQM.Concrete.fockBeamGen` / `fockBeamGen_isHermitian` — the honest number-basis
    matrix `Mₙ` of `a†b + b†a` on the `n`-quantum sector (tridiagonal, `√((j+1)(n-j))`), Hermitian.
  * `AxQM.Concrete.fockBeamProp` / `fockBeamProp_mem_unitaryGroup` — the sector propagator
    `Uⁿ(θ) = exp(-iθMₙ)` and its unitarity.
  * `AxQM.Concrete.fockBeamAmp` / `fockBeamAmp_norm` — the complex first-column amplitude
    `√(C(n,k)) cosⁿ⁻ᵏθ (-i sinθ)ᵏ` of eq. 8.110, with modulus the real eq.-8.110 amplitude.
  * `AxQM.Concrete.fockBeamProp_zero` — the vacuum sector (`U⁰ = I`).
  * `AxQM.Concrete.fockBeamGen_one`, `fockBeamProp_one`, `fockBeamProp_one_col` — the
    single-excitation sector (`M₁ = X`, `U¹ = cosθ·I - i sinθ·X`): **eq. 8.110 for `n = 1`**.
  * `AxQM.Concrete.sqrt_choose_succ_mul` / `sqrt_choose_pred_mul` — the two `√`-form
    binomial recurrences (Pascal's rule) that drive the sector dynamics.
  * `AxQM.Concrete.fockBeamAmpVec` / `fockBeamAmp_hasDerivAt` / `fockBeamGen_mulVec_amp` /
    `fockBeamAmpVec_hasDerivAt` — the **sector Schrödinger equation** `d/dθ c(θ) = -i Mₙ c(θ)`
    solved by the eq.-8.110 amplitude vector `c(θ)` (the dynamical heart of the general-`n`
    derivation).
  * `AxQM.Concrete.fockBeamProp_eq_exp` / `fockBeamProp_apply_zero` / `fockBeamAmpVec_zero`
    / `fockBeamProp_col_hasDerivAt` / `fockBeamProp_col` — the **general-`n` first column, eq. 8.110
    for all `n`**: `⟨j| Uⁿ(θ) |0⟩ = fockBeamAmp θ n j` (`fockBeamProp_col`), obtained because both
    `Uⁿ(θ) e₀` and the amplitude vector `c(θ)` solve the linear IVP `d/dθ w = -i Mₙ w`, `w(0) = e₀`
    (ODE uniqueness, `ODE_solution_unique_univ`); its modulus is the eq.-8.110 amplitude
    (`fockBeamAmp_norm`).
  * `AxQM.Concrete.fockBeamKraus` / `fockBeamKraus_apply` / `fockBeamKraus_eq_prop_col` —
    the **assembled `ℕ`-indexed operation element `Eₖ = ⟨k_b|U|0_b⟩`** (`Matrix ℕ ℕ ℂ`) lowering
    `|n⟩ → |n-k⟩` with amplitude `fockBeamAmp θ n k`; `fockBeamKraus_eq_prop_col` certifies this
    entry is the sector first-column reading `fockBeamProp n θ ⟨k⟩ 0` (eq. 8.110 for all `n`).
  * `AxQM.Concrete.fockBeamKraus_norm` / `fockBeamGram_eq` / `fockBeamKraus_completeness` —
    the **reconciliation with part (2)**: the modulus of the derived `Eₖ` is part (2)'s
    `fockDampingKraus (sin²θ)` (`fockBeamKraus_norm`, the phase `(-i)ᵏ` dropping out), `Eₖ† Eₖ` is
    the diagonal loss operator `fockDampingGram (sin²θ)` (`fockBeamGram_eq`, the phase cancelling),
    and the derived `Eₖ` are themselves trace preserving, `Σₖ Eₖ† Eₖ = I`
    (`fockBeamKraus_completeness`).

* `AxQM/Concrete/HarmonicOscillatorAmplitudeDamping.lean` — **part (2), trace
  preservation**:
  * `AxQM.Concrete.fockDampingProb` — the loss probability `γ = 1 - cos²(χΔt)`, with
    `fockDampingProb_eq_sin_sq` (`= sin²(χΔt)`), `fockDampingProb_nonneg`, `fockDampingProb_le_one`
    (the parameter of eq. 8.110 and its `[0,1]` bounds).
  * `AxQM.Concrete.fockDampingProbCoef` — the loss weight `C(n,k) (1-γ)^{n-k} γ^k`, with
    `fockDampingProbCoef_sum` (`Σ_{k≤n} = 1`, the binomial theorem) and
    `fockDampingProbCoef_eq_zero`.
  * `AxQM.Concrete.fockDampingAmp` — the amplitude `√(…)` of eq. 8.110, with
    `fockDampingAmp_sq`.
  * `AxQM.Concrete.fockDampingKraus` — **the operation element `Eₖ` of eq. 8.110** as an
    `ℕ`-indexed matrix (the modulus form used for the completeness relation), with
    `fockDampingKraus_apply` and `fockDampingKraus_lower` (`Eₖ |n⟩ = √(…) |n-k⟩`).
  * `AxQM.Concrete.fockDampingGram` / `fockDampingGram_eq` — the diagonal product `Eₖ† Eₖ`,
    certified to be the genuine (entrywise) matrix product.
  * `AxQM.Concrete.fockDampingKraus_completeness` — **Exercise 8.21(2):** the operation
    elements define a trace-preserving quantum operation, `Σₖ Eₖ† Eₖ = I` (stated entrywise over the
    number-state index `ℕ`).

See the module docstrings of `AxQM/Concrete/HarmonicOscillatorBeamSplitter.lean` (part (1), the
sector-wise derivation of eq. 8.110 from `U = exp(-iHΔt)`) and
`AxQM/Concrete/HarmonicOscillatorAmplitudeDamping.lean` (part (2), trace preservation) for the full
argument.
-/
