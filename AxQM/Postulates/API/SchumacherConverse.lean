/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TypicalSubspace
import ToMathlib.Analysis.InnerProductSpace.SchumacherConverse
import ToMathlib.Analysis.InnerProductSpace.QuantumDataCompression

/-!
# AxQM.Postulates.API — the converse part of Schumacher's theorem (N&C Thm 12.6)

The **converse (optimality) half** of Nielsen & Chuang's quantum noiseless channel coding theorem
(Theorem 12.6): for an i.i.d. quantum source `ρ : State S`, if the (qubit) rate `R ≥ 0` is *below*
the source entropy, `R < S(ρ)` (in nats: `R * log 2 < ρ.vonNeumannEntropy`), then `ρ` is **not**
reliably compressible at rate `R` — no family of rate-`R` schemes can drive the entanglement
fidelity for `ρ^⊗n` to `1` (`¬ ContinuousLinearMap.ReliablyCompressible ρ.op R`).

## The construction (N&C Eqs. 12.54–12.58)

Two established facts are combined:

* **Fidelity bound** (`QuantumCompressionScheme.fidelity_le` in `ToMathlib`,
  N&C Eqs. 12.54–12.58): for a single block length, if *every* orthogonal projector `P` onto a
  subspace of dimension `≤ 2^numBits` carries only weight `re tr(P ρ^⊗n) ≤ δ` of the source, then
  the scheme's entanglement fidelity is `≤ δ`.
* **Small-subspace bound** (typical subspace theorem, part (3), N&C Eq. 12.45): for a rate
  `R' < S(ρ)`, for large `n`, every projective two-outcome measurement `M` whose `true`-projector
  has rank `≤ exp(n R')` has Born probability `M.bornProb (ρ^⊗n) true ≤ δ`. Here it is derived from
  `State.exists_weights_bornProb_true` (the eigenbasis-diagonal weighted-mass reduction) fed into
  the classical weighted small-set bound `Real.exists_sum_weighted_prod_le_of_sum_le_exp`, exactly
  as the direct part derives part (1). The same statement is `State.smallSubspace_bornProb_le` in
  `AxQM/NC/Ch12/Theorem12_5.lean`.

The bridge between them is `Measurement.ofStarProjection` (the general two-outcome projector
measurement, in `AxQM/Postulates/API/MeasurementModel.lean`): an arbitrary orthogonal (star)
projector `P` is packaged as the two-outcome von Neumann measurement `{P, 1 − P}`, whose
`true`-projector is `P`, whose `trueSubspaceDim` is `finrank (range P)`, and whose Born probability
is `re tr(P ρ^⊗n)`.
With the rate identified as `R' = R * log 2` (so `R' < S(ρ)` is the hypothesis and, since `R ≥ 0`,
`2^{⌊nR⌋} ≤ 2^{nR} = exp(n R')` bounds the rank), the small-subspace bound supplies exactly
`fidelity_le`'s hypothesis, forcing `F(ρ^⊗n, Dₙ∘Cₙ) ≤ δ` for every `δ` and large `n`; a family
whose fidelity also tends to `1` is impossible.

## Fidelity to N&C: the rate is non-negative

N&C's rate `R` is a number of qubits per symbol and is implicitly `R ≥ 0`; the hypothesis carries
`0 ≤ R`. This is *necessary*, not a weakening: for a pure source (`S(ρ) = 0`) the state `ρ^⊗n` is
deterministic and can be recovered perfectly from a one-dimensional compressed space, so a
*negative* rate `R` (the only way `R * log 2 < 0 = S(ρ)` can hold) makes the source reliably
compressible and the converse false. Restricting to the physical rate domain `R ≥ 0` — under which
N&C's `R < S` is `R * log 2 < S(ρ)` in nats — is the faithful statement; with it the proof is
uniform (`R' = R log 2`, no case split). The direct part needs no such hypothesis: there
`S(ρ) < R * log 2` with `S(ρ) ≥ 0` already forces `R > 0`.

## Main results

* `State.re_trace_smallSubspace_le` — the typical subspace theorem part (3) in the *operator form*
  `QuantumCompressionScheme.fidelity_le` consumes: for `R' < S(ρ)`, for large `n`, every orthogonal
  projector `P` on `(S ^⊗ₛ n).space` of rank `≤ exp(n R')` carries weight `re tr(P ρ^⊗n) ≤ δ`.
* `State.not_reliablyCompressible_of_lt_vonNeumannEntropy` — **the converse part of Theorem 12.6**:
  `0 ≤ R → R * log 2 < ρ.vonNeumannEntropy → ¬ ReliablyCompressible ρ.op R`.

The general two-outcome projector measurement `Measurement.ofStarProjection` used as the bridge
is defined beside its sibling `Measurement.ofOrthonormalBasisFiber` in
`AxQM/Postulates/API/MeasurementModel.lean`. The direct part is in
`AxQM/Postulates/API/SchumacherDirect.lean`; the iff of Theorem 12.6 is assembled from the two
halves in `AxQM/NC/Ch12/Theorem12_6.lean`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2 (Theorem 12.6; Eqs. (12.54)–(12.58)).
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The small-subspace weight bound in operator form -/

/-- **Small-subspace weight bound, operator form** (Nielsen & Chuang, Theorem 12.5, part (3), Eq.
12.45 — the hypothesis `QuantumCompressionScheme.fidelity_le` consumes). Fix a rate
`R' < S(ρ) = H(λ)`. For any `δ > 0`, for all sufficiently large `n`, *every* orthogonal projector
`P` on `(S ^⊗ₛ n).space` of rank `≤ exp(n R')` carries source weight `re tr(P ρ^⊗n) ≤ δ`.

The projector `P` is packaged as the two-outcome von Neumann measurement `{P, 1 − P}`
(`Measurement.ofStarProjection`), so `re tr(P ρ^⊗n)` is its Born probability
(`bornProb_ofStarProjection_true`), `rank P = trueSubspaceDim` is its `true`-subspace dimension, and
`State.exists_weights_bornProb_true` rewrites the Born probability as the classical *weighted* mass
`∑_κ w κ · ∏ᵢ λ(κᵢ)` with `∑_κ w κ = rank P ≤ exp(n R')`; the classical weighted small-set bound
`Real.exists_sum_weighted_prod_le_of_sum_le_exp` (applied to `λ = ρ.eigenvalueDist`, `H(λ) = S(ρ)`)
then forces it below `δ`. This is the same statement as `State.smallSubspace_bornProb_le`, derived
from the same kernel. -/
theorem State.re_trace_smallSubspace_le (ρ : State S) {R' : ℝ}
    (hR' : R' < Real.entropy ρ.eigenvalueDist) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ P : (S ^⊗ₛ n).space →L[ℂ] (S ^⊗ₛ n).space, IsStarProjection P →
      (Module.finrank ℂ (LinearMap.range (P : (S ^⊗ₛ n).space →ₗ[ℂ] (S ^⊗ₛ n).space)) : ℝ)
          ≤ Real.exp ((n : ℝ) * R') →
        RCLike.re ((LinearMap.trace ℂ (S ^⊗ₛ n).space)
            ((P.comp (ρ.tensorPow n).op : (S ^⊗ₛ n).space →L[ℂ] (S ^⊗ₛ n).space) :
              (S ^⊗ₛ n).space →ₗ[ℂ] (S ^⊗ₛ n).space)) ≤ δ := by
  obtain ⟨N, _, hN⟩ := Real.exists_sum_weighted_prod_le_of_sum_le_exp
    ρ.eigenvalueDist_nonneg ρ.eigenvalueDist_sum_eq_one hR' hδ
  refine ⟨N, fun n hn P hP hfin => ?_⟩
  rw [← Measurement.bornProb_ofStarProjection_true P hP (ρ.tensorPow n)]
  obtain ⟨w, hw0, hw1, hwsum, hbpeq⟩ := ρ.exists_weights_bornProb_true n
    (Measurement.ofStarProjection P hP) (Measurement.isProjective_ofStarProjection P hP)
  rw [hbpeq]
  refine hN n hn w hw0 hw1 ?_
  rw [hwsum]
  exact hfin

/-! ### The converse: a below-entropy rate is not reliable -/

/-- **The converse part of Schumacher's noiseless channel coding theorem** (Nielsen & Chuang,
Theorem 12.6, Eqs. 12.54–12.58). For a non-negative (qubit) rate `R` below the source entropy,
`R < S(ρ)` (in nats: `R * log 2 < ρ.vonNeumannEntropy`), the source `ρ` is **not** reliably
compressible at rate `R`: no family of rate-`R` schemes has entanglement fidelity for `ρ^⊗n` tending
to `1`.

The hypothesis `0 ≤ R` is the physical rate domain and is necessary (a pure source is reliably
compressible at every rate, including negative ones). For large `n`, the fidelity bound
`QuantumCompressionScheme.fidelity_le` reduces reliability to the small-subspace weight bound
(`State.re_trace_smallSubspace_le` at rate `R log 2 < S(ρ)`): every rank-`≤ 2^{⌊nR⌋}` projector `P`
has `re tr(P ρ^⊗n) ≤ 1/2`, because `2^{⌊nR⌋} ≤ 2^{nR} = exp(n · R log 2)` (using `R ≥ 0`). Hence
`(sch n).fidelity (ρ^⊗n) ≤ 1/2` eventually, contradicting a fidelity tending to `1`. -/
theorem State.not_reliablyCompressible_of_lt_vonNeumannEntropy (ρ : State S) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R * Real.log 2 < ρ.vonNeumannEntropy) :
    ¬ ContinuousLinearMap.ReliablyCompressible ρ.op R := by
  rintro ⟨sch, hlim⟩
  have hR' : R * Real.log 2 < Real.entropy ρ.eigenvalueDist := by
    rw [← ρ.vonNeumannEntropy_eq_entropy_eigenvalueDist]; exact hR
  obtain ⟨N, hbound⟩ := ρ.re_trace_smallSubspace_le hR' (show (0 : ℝ) < 1 / 2 by norm_num)
  -- Eventually the fidelity is `≤ 1/2`, via `fidelity_le` fed by the small-subspace bound.
  have hle : ∀ᶠ n in atTop,
      (sch n).fidelity (PiTensorProduct.mapCLM fun _ : Fin n => ρ.op) ≤ 1 / 2 := by
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    -- `fidelity_le` unifies its `(sch n).fidelity (ρ.tensorPow n).op` conclusion against the
    -- `PiTensorProduct.mapCLM`-shaped goal up to defeq (`(ρ.tensorPow n).op = mapCLM …` is `rfl`).
    refine ContinuousLinearMap.QuantumCompressionScheme.fidelity_le (sch n)
      (ρ.tensorPow n).isDensity (fun P hP hrank => ?_)
    -- The rank of `P` is `≤ exp(n · R log 2)`: `2^{⌊nR⌋} ≤ 2^{nR} = exp(n · R log 2)`.
    refine hbound n hn P hP ?_
    have hnR : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR0
    have hexp : ((2 : ℝ) ^ ⌊(n : ℝ) * R⌋₊) ≤ Real.exp ((n : ℝ) * (R * Real.log 2)) := by
      calc ((2 : ℝ) ^ ⌊(n : ℝ) * R⌋₊)
          = (2 : ℝ) ^ ((⌊(n : ℝ) * R⌋₊ : ℝ)) := by rw [Real.rpow_natCast]
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hnR)
        _ = Real.exp ((n : ℝ) * (R * Real.log 2)) := by
            rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
    exact le_trans (by exact_mod_cast hrank) hexp
  -- A reliable family has fidelity `> 1/2` eventually, contradicting `hle`.
  have h1 : ∀ᶠ n in atTop,
      (1 : ℝ) / 2 < (sch n).fidelity (PiTensorProduct.mapCLM fun _ : Fin n => ρ.op) :=
    hlim.eventually_const_lt (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := (h1.and hle).exists
  linarith

end AxQM
