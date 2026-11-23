/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SingleSpinRefocusing

/-!
# Nielsen & Chuang, Exercise 7.39 (Three-dimensional refocusing)

*(N&C §7.7.3, p. 332.)*

Three-dimensional refocusing: what set of pulses refocuses evolution under any single-spin H=Σ c_k
σ_k?

## Context

Refocusing (N&C §7.7.3) is the NMR technique of interleaving free evolution with `π`-pulses so that
unwanted terms of the Hamiltonian cancel. For a single generator it is exact: with
`R²ₓ₁ = e^{-iπX₁/2}` the `180°` pulse, Exercise 7.38 / eq. (7.150) gives
`R²ₓ₁ e^{-iaZ₁t} R²ₓ₁ = e^{+iaZ₁t}`, because conjugation by `X` (which anticommutes with `Z`)
reverses the sign of the `Z` generator. The present exercise asks for the analogue when the
single-spin Hamiltonian is **fully general**, `Hsys = c₀ X + c₁ Y + c₂ Z`.

**The answer.** No single pulse works: conjugation by a unitary rotates the Bloch axis of `Hsys`
but cannot invert all three coordinates at once (that improper map is not a rotation), and a single
`x̂`-pulse pair refocuses only the two components orthogonal to `x̂`, leaving the `x̂` one. The
refocusing pulse set is therefore a **sequence of `π`-pulses about two orthogonal axes** (say `x̂`
and `ŷ`), whose toggling-frame conjugations run over the whole Pauli group `{I, X, Y, Z}`. Their
equal-weight average annihilates the Hamiltonian,
`¼ (Hsys + X Hsys X + Y Hsys Y + Z Hsys Z) = 0`, so the zeroth-order average Hamiltonian vanishes
and the evolution is refocused — the standard meaning of refocusing a *non-commuting* Hamiltonian.
Two orthogonal axes suffice because `X Y = i Z`, so the `ẑ`-pulse conjugation is realised by a
`ŷ`-pulse followed by an `x̂`-pulse.

## The formalisation

The content is pure `2 × 2` complex-matrix algebra over the Pauli matrices and the
combination `pauliDot c = c·σ` (`Concrete.pauliX/Y/Z`, `Concrete.pauliDot`,
`Concrete.pauliBlochFlip`, the matrix exponential). Compare the refocusing and Pauli exercises
`AxQM/NC/Ch7/Exercise7_35.lean` and `AxQM/NC/Ch8/Exercise8_17.lean`. The single-spin Hamiltonian
uses `pauliDot` (`AxQM/Concrete/Pauli.lean`); the coefficient reflections use `pauliBlochFlip`
(`AxQM/Concrete/BlochPauliTwirl.lean`); the refocusing identity uses the Pauli-twirl sum
`pauliConjSum_eq` (`AxQM/Concrete/PauliAverage.lean`).

The statements are in `AxQM/Concrete/SingleSpinRefocusing.lean` (namespace `AxQM.Concrete`). That
every single-spin Hamiltonian `Σₖ cₖ σₖ` is traceless is `pauliDot_trace`
(`AxQM/Concrete/BlochUnitaryRotation.lean`):

* `pauliX_conj_pauliDot`, `pauliY_conj_pauliDot`, `pauliZ_conj_pauliDot` — **the refocusing
  mechanism**: conjugating `c·σ` by `X` / `Y` / `Z` (a `π`-pulse about `x̂` / `ŷ` / `ẑ`) fixes that
  axis' component and negates the other two, e.g. `X (c·σ) X = (c₀, −c₁, −c₂)·σ`.
* `pauli_conj_pauliDot` — the same uniformly over `k : Fin 4`,
  `σₖ (c·σ) σₖ = (pauliBlochFlip k c)·σ`, exhibiting the Bloch-vector map `pauliBlochFlip` as matrix
  conjugation on `pauliDot`.
* `pauliDot_add_conj_pauliX` — **why one axis is not enough** (eqs. 7.150–7.151):
  `(c·σ) + X (c·σ) X = (2 c₀) • X` (the `x̂` term survives, doubled).
* `pauliDot_conjSum_eq_zero` — **the refocusing identity** (the answer):
  `(c·σ) + X (c·σ) X + Y (c·σ) Y + Z (c·σ) Z = 0` — the full pulse group `{I, X, Y, Z}` averages any
  single-spin Hamiltonian to zero.
* `pauliZ_conj_eq_pauliX_pauliY_conj` — **two orthogonal axes suffice**:
  `Z M Z = X (Y M Y) X` (since `X Y = i Z`), and `pauliDot_conjSum_twoAxis_eq_zero` restates the
  refocusing identity using only `x̂`- and `ŷ`-pulses.
* `pauli_conj_propagator` — **the exact evolution-level statement**, generalising eq. 7.150 /
  Exercise 7.38: `σₖ · e^{-i t (c·σ)} · σₖ = e^{-i t ((pauliBlochFlip k c)·σ)}`.

See the module docstring of `AxQM/Concrete/SingleSpinRefocusing.lean` for the full discussion.
-/
