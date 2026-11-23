/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TypicalSubspace

/-!
# N&C Theorem 12.5 — the typical subspace theorem (parts (1) and (2))

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 12.5, pp. 543–544.

For an i.i.d. quantum source `ρ : State S` with spectral decomposition `ρ = ∑ₓ λ(x) |eₓ⟩⟨eₓ|`, the
**typical subspace theorem** is the quantum translation of the classical theorem of typical
sequences (N&C Theorem 12.2). Writing `P(n, ε) = ρ.typicalSubspaceProj n ε` for the projector onto
the ε-typical subspace `T(n, ε)` (N&C Eq. 12.42) and `S(ρ) = ρ.vonNeumannEntropy` for the von
Neumann entropy, N&C states three parts, all proved here:

* **Part (1)** (`State.typicalSubspace_bornProb_ge`, N&C Eq. 12.43). Fix `ε > 0`. For any `δ > 0`,
  for all sufficiently large `n`, the probability that `ρ^⊗n` lies in the ε-typical subspace is at
  least `1 − δ`:  `tr(P(n, ε) ρ^⊗n) ≥ 1 − δ`.
* **Part (2)** (`State.typicalSubspaceDim_bounds`, N&C Eq. 12.44). Fix `ε > 0` and `δ > 0`. For all
  sufficiently large `n`, the dimension `|T(n, ε)| = tr(P(n, ε))` of the typical subspace satisfies
  `(1 − δ) 2^{n(S(ρ)−ε)} ≤ |T(n, ε)| ≤ 2^{n(S(ρ)+ε)}`.

* **Part (3)** (`State.smallSubspace_bornProb_le`, N&C Eq. 12.45). Fix a rate `R < S(ρ)`. For any
  `δ > 0`, for all sufficiently large `n`, *every* subspace `S(n)` of dimension at most `2^{nR}`
  satisfies `tr(S(n) ρ^⊗n) ≤ δ` — a small subspace cannot capture the source. `S(n)` is presented as
  any projective two-outcome measurement `M` whose `true`-projector has rank
  `M.trueSubspaceDim ≤ exp(n R)`, and the left-hand side is the Born probability
  `M.bornProb (ρ^⊗n) true` of landing in it.

## Statement shape and fidelity

Both parts are stated over N&C's full data — an arbitrary system `S`, an arbitrary state `ρ`, and
the *exact* `ε`/`δ`/`n` quantifier structure of the textbook ("fix `ε > 0`; for any `δ > 0`, for
sufficiently large `n`, …") — with no dimension fixed and no hypothesis added.

* Part (1) is stated through the Born probability `Measurement.bornProb`: `P(n, ε)` is packaged
  as the two-outcome projective measurement `ρ.typicalSubspaceMeasurement n ε` (typical / atypical),
  and the left-hand side is *literally* the Born probability of the typical outcome `true` on
  `ρ^⊗n`. This is the faithful physical reading of N&C's `tr(P(n, ε) ρ^⊗n)` — the probability of
  landing in the typical subspace — rather than a raw operator trace.
* Part (2) is stated over the dimension `ρ.typicalSubspaceDim n ε : ℕ = |T(n, ε)|`. N&C's identity
  `|T(n, ε)| = tr(P(n, ε))` is `State.trace_typicalSubspaceProj_eq_typicalSubspaceDim` (in
  `AxQM/Postulates/API/TypicalSubspace.lean`), so this cardinality *is* the trace of the
  projector.
* Part (3) quantifies over N&C's "*any* subspace `S(n)` of dimension at most `2^{nR}`". Every such
  subspace is the range of a genuine projector, faithfully modelled as the `true`-outcome projector
  of a projective two-outcome `Measurement Bool (S ^⊗ₛ n)` — its rank is
  `Measurement.trueSubspaceDim : ℕ` — and, as in Part (1), the conclusion `tr(S(n) ρ^⊗n) ≤ δ` is
  the Born probability `Measurement.bornProb` of the `true` outcome. No generality is lost (any
  projector arises this way) and none is added.

**Nats convention**: the von Neumann entropy and the
exponentials are in nats (`Real.exp`), so N&C's base-`2` bounds `(1 − δ) 2^{n(S−ε)} ≤ |T| ≤
2^{n(S+ε)}` read here as `(1 − δ) exp(n(S − ε)) ≤ |T| ≤ exp(n(S + ε))` — the same statement rescaled
by `log 2`, consistent with Theorems 12.2/12.4 in `ToMathlib/`.

## Proof route and reuse

The whole content is the reduction to the *classical* theorem of typical sequences applied to `ρ`'s
eigenvalue distribution `λ = ρ.eigenvalueDist` (a genuine probability distribution,
`eigenvalueDist_nonneg` / `eigenvalueDist_sum_eq_one`, with `H(λ) = S(ρ)`,
`vonNeumannEntropy_eq_entropy_eigenvalueDist`).
Both proofs are one application of the classical existence theorem followed by the two bridge
rewrites already established in `AxQM/Postulates/API/TypicalSubspace.lean`:

* Part (1): `typicalSubspaceMeasurement_bornProb_true` rewrites the Born probability to the
  classical typicality mass `∑_{κ ∈ T(n, ε)} ∏ᵢ λ(κᵢ)`, which `Real.exists_le_sum_typicalSeq`
  bounds below by `1 − δ`.
* Part (2): `Real.exists_card_typicalSeq_bounds` bounds `|T(n, ε)| = (typicalSeq λ n ε).card`
  (definitionally `typicalSubspaceDim`) between `(1 − δ) exp(n(H(λ) − ε))` and `exp(n(H(λ) + ε))`;
  the entropy bridge turns `H(λ)` into `S(ρ)`.
* Part (3): `State.exists_weights_bornProb_true` expands the Born probability of
  *any* projective `S(n)` on `ρ^⊗n` into the classical *weighted* mass `∑_κ w κ · ∏ᵢ λ(κᵢ)`, with
  eigenbasis-diagonal weights `w κ ∈ [0, 1]` summing to `tr S(n) = M.trueSubspaceDim`; the weighted
  small-set bound `Real.exists_sum_weighted_prod_le_of_sum_le_exp` (the fractional refinement of
  `Real.exists_sum_prod_le_of_card_le_exp`) then forces it below `δ` once `M.trueSubspaceDim ≤
  exp(n R)` and `R < H(λ) = S(ρ)`.

The machinery they reduce to (`typicalSubspaceProj`, the trace identities, the projective
measurement, `eigenvalueDist`, `trueSubspaceDim`, and the weighted-mass reduction
`exists_weights_bornProb_true`) is in `AxQM/Postulates/API/TypicalSubspace.lean`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Typical subspace theorem, part (1)** (Nielsen & Chuang, Theorem 12.5, Eq. 12.43): the source
`ρ^⊗n` lands in the ε-typical subspace with probability `≥ 1 − δ` for all sufficiently large `n`.
Fix `ε > 0`; then for any `δ > 0` there is an `N` such that for every `n ≥ N` the Born probability
of the typical outcome of the projective measurement `{P(n, ε), I − P(n, ε)}` on `ρ^⊗n` is at least
`1 − δ` — i.e. `tr(P(n, ε) ρ^⊗n) ≥ 1 − δ`.

The proof rewrites the Born probability to the classical typicality mass `∑_{κ typical} ∏ᵢ λ(κᵢ)`
(`typicalSubspaceMeasurement_bornProb_true`) and applies the classical theorem of typical sequences
(`Real.exists_le_sum_typicalSeq`) to the eigenvalue distribution `λ = ρ.eigenvalueDist`. -/
theorem State.typicalSubspace_bornProb_ge (ρ : State S) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      1 - δ ≤ (ρ.typicalSubspaceMeasurement n ε).bornProb (ρ.tensorPow n) true := by
  obtain ⟨N, hNpos, hN⟩ :=
    Real.exists_le_sum_typicalSeq ρ.eigenvalueDist_nonneg ρ.eigenvalueDist_sum_eq_one hε hδ
  refine ⟨N, hNpos, fun n hn => ?_⟩
  rw [ρ.typicalSubspaceMeasurement_bornProb_true]
  exact hN n hn

/-- **Typical subspace theorem, part (1), limit form**: the probability that `ρ^⊗n` lies in the
ε-typical subspace tends to `1` as `n → ∞`, `tr(P(n, ε) ρ^⊗n) → 1`. The `Tendsto` companion of
`State.typicalSubspace_bornProb_ge` (which provides the eventual lower bound `≥ 1 − δ`): together
with `bornProb ≤ 1` (`Measurement.bornProb_le_one`) the two-sided squeeze gives the limit. The
citable driver of ensemble/entanglement-fidelity compression-reliability arguments. -/
theorem State.typicalSubspace_bornProb_tendsto_one (ρ : State S) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun n => (ρ.typicalSubspaceMeasurement n ε).bornProb (ρ.tensorPow n) true)
      Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, -, hN⟩ := ρ.typicalSubspace_bornProb_ge hε (half_pos hδ)
  refine ⟨N, fun n hn => ?_⟩
  have h2 := (ρ.typicalSubspaceMeasurement n ε).bornProb_le_one (ρ.tensorPow n) true
  rw [Real.dist_eq, abs_of_nonpos (by linarith [hN n hn])]; linarith [hN n hn]

/-- **Typical subspace theorem, part (2)** (Nielsen & Chuang, Theorem 12.5, Eq. 12.44): the
dimension of the ε-typical subspace is `2^{n S(ρ)}` up to the exponential tolerance `ε`. Fix `ε > 0`
and `δ > 0`; then for all sufficiently large `n` the dimension `|T(n, ε)| = tr(P(n, ε))` satisfies

`(1 − δ) exp(n (S(ρ) − ε)) ≤ |T(n, ε)| ≤ exp(n (S(ρ) + ε))`

(in nats; N&C's base-`2` `(1 − δ) 2^{n(S(ρ)−ε)} ≤ |T(n, ε)| ≤ 2^{n(S(ρ)+ε)}`). The dimension is
`ρ.typicalSubspaceDim n ε`, which equals `tr(P(n, ε))` by
`trace_typicalSubspaceProj_eq_typicalSubspaceDim`.

The proof applies the classical dimension bounds (`Real.exists_card_typicalSeq_bounds`) to `λ =
ρ.eigenvalueDist` — whose typical-set cardinality is definitionally `typicalSubspaceDim` — and
rewrites the classical entropy `H(λ)` to the von Neumann entropy `S(ρ)` via the entropy bridge
`vonNeumannEntropy_eq_entropy_eigenvalueDist`. -/
theorem State.typicalSubspaceDim_bounds (ρ : State S) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      (1 - δ) * Real.exp (n * (ρ.vonNeumannEntropy - ε)) ≤ (ρ.typicalSubspaceDim n ε : ℝ) ∧
        (ρ.typicalSubspaceDim n ε : ℝ) ≤ Real.exp (n * (ρ.vonNeumannEntropy + ε)) := by
  obtain ⟨N, hNpos, hN⟩ :=
    Real.exists_card_typicalSeq_bounds ρ.eigenvalueDist_nonneg ρ.eigenvalueDist_sum_eq_one hε hδ
  refine ⟨N, hNpos, fun n hn => ?_⟩
  simp only [State.typicalSubspaceDim, ρ.vonNeumannEntropy_eq_entropy_eigenvalueDist]
  exact hN n hn

/-- **Typical subspace theorem, part (3)** (Nielsen & Chuang, Theorem 12.5, Eq. 12.45): a *small*
subspace carries negligible weight of the source. Fix a rate `R < S(ρ)`. For any `δ > 0`, for all
sufficiently large `n`, *every* subspace `S(n) ⊆ (S ^⊗ₛ n).space` of dimension at most `exp(n R)` —
presented as the `true`-outcome projector of a projective two-outcome measurement `M` with
`M.trueSubspaceDim ≤ exp(n R)` — satisfies `tr(S(n) ρ^⊗n) ≤ δ`: the probability of landing in `S(n)`
when measuring `ρ^⊗n` is at most `δ`.

(In nats; N&C's base-`2` bound reads `dim S(n) ≤ 2^{nR}`, `R < S(ρ)`.) N&C quantifies over "any
subspace of `H^⊗n` of dimension at most `2^{nR}`"; every such subspace is the range of a genuine
projector `S(n)`, faithfully captured here as the `true`-outcome projector `M.op true` of the
two-outcome von Neumann measurement `{S(n), I − S(n)}`, with its rank `M.trueSubspaceDim`
bounded by `exp(n R)` — so the conclusion is the Born probability
`M.bornProb (ρ.tensorPow n) true`, the faithful reading
of `tr(S(n) ρ^⊗n)`.

The proof expands `tr(S(n) ρ^⊗n) = ∑_κ ⟨e_κ, S(n) e_κ⟩ ∏ᵢ λ(κᵢ)` in the `ρ^⊗n` eigenbasis
(`exists_weights_bornProb_true`): the diagonal weights `w κ = ⟨e_κ, S(n) e_κ⟩ ∈ [0, 1]` sum to
`tr S(n) = dim S(n) ≤ exp(n R)`, so the classical *weighted* small-set bound
(`Real.exists_sum_weighted_prod_le_of_sum_le_exp`) applied to the eigenvalue distribution
`λ = ρ.eigenvalueDist` (with `entropy λ = S(ρ)`, `vonNeumannEntropy_eq_entropy_eigenvalueDist`)
forces the weighted mass below `δ`. -/
theorem State.smallSubspace_bornProb_le (ρ : State S) {R : ℝ} (hR : R < ρ.vonNeumannEntropy)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ M : Measurement Bool (S ^⊗ₛ n), M.IsProjective →
      (M.trueSubspaceDim : ℝ) ≤ Real.exp (n * R) →
        M.bornProb (ρ.tensorPow n) true ≤ δ := by
  have hR' : R < Real.entropy ρ.eigenvalueDist := by
    rw [← ρ.vonNeumannEntropy_eq_entropy_eigenvalueDist]; exact hR
  obtain ⟨N, hNpos, hN⟩ :=
    Real.exists_sum_weighted_prod_le_of_sum_le_exp ρ.eigenvalueDist_nonneg
      ρ.eigenvalueDist_sum_eq_one hR' hδ
  refine ⟨N, hNpos, fun n hn M hM hdim => ?_⟩
  obtain ⟨w, hw0, hw1, hwsum, hbp⟩ := ρ.exists_weights_bornProb_true n M hM
  rw [hbp]
  exact hN n hn w hw0 hw1 (by rw [hwsum]; exact hdim)

end AxQM
