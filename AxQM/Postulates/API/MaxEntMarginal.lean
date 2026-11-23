/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtNumber
import AxQM.Postulates.API.Entropy

/-!
# AxQM — maximally entangled resource marginals

`State.IsMaxEntMarginal ρ K`: the state `ρ` is the reduced state (one-party marginal) of a
**maximally entangled pure state of Schmidt rank `K`** — equivalently, `ρ` is maximally mixed on a
`K`-dimensional subspace (its `K` non-zero eigenvalues are all `1/K`). We characterise this by

`ρ.rank = K  ∧  ρ.vonNeumannEntropy = Real.log K`.

This pair *is* the characterisation: a rank-`K` state has entropy `≤ log K`
(`State.vonNeumannEntropy_le_log_finrank` on its `K`-dimensional support) with equality **iff** the
spectrum is uniform, so `rank = K` together with the maximal value `S = log K` forces the `K`
non-zero eigenvalues to be exactly `1/K` — i.e. `ρ = (1/K)·P` for a rank-`K` projection `P`, the
marginal of `K`-dimensional maximal entanglement. For `K = 2ⁿ` this is the reduced state of `n`
shared Bell pairs, with entropy `n · log 2`.

This is the *target-resource* predicate for entanglement distillation (N&C §12.5.2,
Exercise 12.23): distilling copies of `|ψ⟩` produces, with fidelity → 1, a state trace-close to some
`μ` with `μ.IsMaxEntMarginal K` — i.e. close to `K`-dimensional maximal entanglement.

Here `State.rank` is `finrank ℂ` of the range of the density operator. The predicate is used in
the statement of Exercise 12.23 (`AxQM/NC/Ch12/Exercise12_23.lean`).
-/

noncomputable section

namespace AxQM

namespace State

variable {S : QSystem}

/-- `ρ.IsMaxEntMarginal K`: `ρ` is the marginal of a maximally entangled pure state of Schmidt
rank `K`, i.e. `ρ` is maximally mixed on a `K`-dimensional subspace. Characterised by its rank being
`K` and its entropy attaining the maximal value `log K` for that rank — which forces the `K`
non-zero eigenvalues to be uniform, each `1/K`. For `K = 2ⁿ` this is the reduced state of `n` shared
Bell pairs, `S(ρ) = n · log 2`. -/
def IsMaxEntMarginal (ρ : State S) (K : ℕ) : Prop :=
  ρ.rank = K ∧ ρ.vonNeumannEntropy = Real.log K

/-- The entropy of a rank-`K` maximally entangled marginal is `log K`. -/
theorem IsMaxEntMarginal.vonNeumannEntropy_eq {ρ : State S} {K : ℕ}
    (h : ρ.IsMaxEntMarginal K) : ρ.vonNeumannEntropy = Real.log K :=
  h.2

/-- The rank of a rank-`K` maximally entangled marginal is `K`. -/
theorem IsMaxEntMarginal.rank_eq {ρ : State S} {K : ℕ}
    (h : ρ.IsMaxEntMarginal K) : ρ.rank = K :=
  h.1

end State

end AxQM
