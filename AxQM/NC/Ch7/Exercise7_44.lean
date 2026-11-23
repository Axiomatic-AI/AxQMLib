/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LogicalLabelingCapacity

/-!
# Nielsen & Chuang, Exercise 7.44 (Logical labeling for `n` spins)

*(N&C p. 335, §7.7.1.)*

Logical labeling for n spins: what is the largest effective pure state constructible from ρ via
logical labeling?

## The physics and the answer

The high-temperature thermal state of `n` spins is diagonal in the computational basis, with the
observable *signal population* on `|b⟩` proportional to the total magnetization
`n − 2·(Hamming weight of b)` (the eigenvalue of `Z₁ + ⋯ + Zₙ`); the isotropic background is
unobservable because NMR observables are traceless. Two basis states carry the **same** population
iff they have the same Hamming weight, and there are `C(n, w) = n.choose w` states of weight `w`.

An *effective pure state* `ρ = (1-ε)/d · I + ε·|ψ⟩⟨ψ|` of a `d`-level manifold has eigenvalue
populations of the shape **one distinguished value, strictly above `d − 1` equal values**. *Logical
labeling* applies a basis permutation (a reversible circuit) and isolates a sub-manifold; a
permutation only relabels populations, so any subset of basis states with this shape is
constructible. The excited (equal-population) part must therefore be a set of basis states of one
common Hamming weight `k`, of which there are at most `n.choose k`, maximised at the central weight
`k = ⌊n/2⌋` (as the hint indicates). Adding one distinguished ground state (e.g. `|0…0⟩`, population
`n`):

> **The largest effective pure state has dimension `n.choose (⌊n/2⌋) + 1`.**

In qubit terms this is `⌊log₂(n.choose (n/2) + 1)⌋` logical qubits; the Hilbert-space dimension need
not be a power of two (as N&C remark). For `n = 3` it is `C(3,1) + 1 = 4`, the `4 × 4`
effective-pure block `8|00⟩⟨00| − 2I` of the worked three-spin example (Exercise 7.43).

## The formalisation

The answer is a combinatorial optimisation over the thermal state's population multiset, formalised
over `Finset (Fin n)`, `ℤ`, and `Nat.choose`. Compare the labeling exercises 7.42 (temporal) and
7.43 (logical, `n = 3`).

In `AxQM/Concrete/LogicalLabelingCapacity.lean` (namespace `AxQM.Concrete`):

* `magPop` — the signal population `n − 2·|A|` of the basis state with spin-`|1⟩` set `A`;
  `magPop_eq_iff` — equal population iff equal Hamming weight (the degeneracy logical labeling
  uses).
* `IsEffectivePureManifold` — a set of basis states with the effective-pure population profile (one
  distinguished ground state strictly above `d − 1` mutually equal excited states).
* `maxEffectivePureDim n := n.choose (n / 2) + 1` — **the exercise's answer**.
* `IsEffectivePureManifold.card_le` — **optimality**: every effective-pure manifold has
  `card ≤ maxEffectivePureDim n`.
* `exists_isEffectivePureManifold` — **achievability**: for `n ≥ 1` an effective-pure manifold of
  cardinality exactly `maxEffectivePureDim n` exists (excited = the weight-`⌈n/2⌉` manifold, ground
  = `|0…0⟩`).
* `maxEffectivePureDim_one`/`_two`/`_three` — the values `2, 3, 4` for `n = 1, 2, 3`; `n = 3`
  reproduces the worked example.

## Fidelity

N&C's populations `n − 2w` are recorded exactly (their `6 − 4w` for `n = 3` is the same up to the
physically irrelevant overall scale `2`). The effective-pure profile captures the eigenvalue
structure of `(1-ε)/d·I + ε|ψ⟩⟨ψ|` for arbitrary `d`, including the non-power-of-two generality N&C
mention. Both directions are proved, pinning the maximum exactly at `n.choose (n/2) + 1` — the
answer is neither weakened (no dimension restriction, no power-of-two assumption) nor overstated.
-/
