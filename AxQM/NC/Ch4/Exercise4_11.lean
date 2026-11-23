/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.EulerDecompositionCounterexample
import AxQM.Concrete.EulerDecompositionOrthogonal

/-!
# Nielsen & Chuang, Exercise 4.11 (three-rotation decomposition over two axes) — **false as stated**

For non-parallel unit vectors m,n show U=e^{i a}R_n(b)R_m(g)R_n(d).

**This exercise is false as stated.** Non-parallelism of `m̂, n̂` is *not* sufficient for the
decomposition (4.13) to exist for every unitary `U`; the correct hypothesis is that the middle axis
be **perpendicular** to the repeated outer axis, `m̂ ⊥ n̂`. This is Davenport's theorem: the
classical Euler decompositions `R_ẑ R_ŷ R_ẑ` (Theorem 4.1) and `R_ẑ R_x̂ R_ẑ` both use perpendicular
axes, and that perpendicularity is essential, not incidental.

## Why it is false

Conjugation by `R_â(θ)` rotates a Bloch/Pauli vector `v·σ` about `â` by `θ` (Exercise 4.6). For a
product `U = e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)` the global phase cancels in `U (n̂·σ) U†` and the two
outer `R_n̂` factors fix `n̂`, so `U (n̂·σ) U† = (R(n̂))·σ` with

`n̂ · R(n̂) = (m̂·n̂)² + (1 − (m̂·n̂)²) cos γ ≥ 2(m̂·n̂)² − 1`.

When `m̂` is **not** perpendicular to `n̂` this lower bound exceeds `−1`, so any unitary whose
induced rotation flips `n̂ ↦ −n̂` — e.g. the Pauli `X`, for which `X (ẑ·σ) X = −(ẑ·σ)` — cannot be
written in the form (4.13). Concretely, taking `n̂ = ẑ` and the non-parallel, non-perpendicular unit
vector
`m̂ = (3/5, 0, 4/5)`, matching the `(0,0)` entry would force `cos γ = −41/9`, which is impossible.

The statement and its refutation are pure `2 × 2` complex-matrix facts, expressed with the
rotation matrices `rotAxis`, the Pauli combinations `pauliDot`/`pauliX`/`pauliZ`, and the
Rodrigues rotation `rot3D`.

## The formalisation

The refutation is in `AxQM/Concrete/EulerDecompositionCounterexample.lean`:

* `AxQM.Concrete.pauliDot_conj_rotAxis_triple` — the **conjugation invariant**:
  `(e^{iα} • R_n̂(β) R_m̂(γ) R_n̂(δ)) · (n̂·σ) · (…)ᴴ = (rot3D n̂ β (rot3D m̂ γ n̂))·σ`, built from
  Exercise 4.6's `pauliDot_conj_rotAxis`, the phase cancellation, and `rot3D_self` (a rotation fixes
  its axis).
* `AxQM.Concrete.pauliX_ne_smul_rotAxis_mul_rotAxis_mul_rotAxis` — the **counterexample**:
  for `n̂ = ẑ`, `m̂ = (3/5, 0, 4/5)` the unitary `X` is not `e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)` for any
  `α, β, γ, δ`.
* `AxQM.Concrete.not_forall_unit_nonParallel_exists_smul_rotAxis_triple` — **Exercise 4.11
  itself, negated**: the universal statement (4.13) over all non-parallel unit pairs does not hold,
  witnessed by the counterexample above.

The **corrected** statement — the true result Exercise 4.11 intends — is in
`AxQM/Concrete/EulerDecompositionOrthogonal.lean`:

* `AxQM.Concrete.exists_smul_rotAxis_triple_of_perp` — for a *perpendicular* pair of unit
  axes `m̂ ⊥ n̂`, every single-qubit unitary `U` does factor as
  `U = e^{iα} R_n̂(β) R_m̂(γ) R_n̂(δ)`.
  This is the honest repair of the exercise: `m̂ ⊥ n̂` (not mere non-parallelism) is the correct
  hypothesis, and Theorem 4.1 (the Z–Y decomposition, `n̂ = ẑ`, `m̂ = ŷ`) is its special case. The
  proof follows N&C's own hint — "use Theorem 4.1" — by realizing the orthonormal frame
  `[m̂×n̂ | m̂ | n̂] ∈ SO(3)` as a qubit rotation `W` (Euler's theorem) with `W R_z Wᴴ = R_n̂` and
  `W R_y Wᴴ = R_m̂` (`AxQM.Concrete.rotAxis_conj_rotAxis`), then applying the Z–Y
  decomposition to `Wᴴ U W` and conjugating back.

Together these formalise both halves of the item: the exercise is false as written, and the
intended perpendicular-axes statement is true and proved.
-/
