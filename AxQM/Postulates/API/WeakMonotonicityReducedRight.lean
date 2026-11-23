/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.WeakMonotonicity
import AxQM.Postulates.API.ReducedStateReshape
import AxQM.Postulates.API.SubadditivityReformulations

/-!
# AxQM — the `reducedRight`-side marginal crux for weak monotonicity (N&C Ex 11.24)

Nielsen & Chuang **Exercise 11.24** (p. 521) derives weak monotonicity
`S(A) + S(B) ≤ S(A,C) + S(B,C)` from strong subadditivity by purifying `ρ` with a reference `R` and
applying strong subadditivity to the tripartite `R ⊗ (B ⊗ C)` marginal. The reduced-state reshaping
this needs splits into two halves along which factor is traced first:

* the **`reducedLeft` half** — the subsystem-`A` purity identity `S(A) = S(R,B,C)`
  (`PureState.vonNeumannEntropy_reducedLeft_reducedLeft_eq_pullRefReshape`,
  `Postulates/API/WeakMonotonicity`);
* the **`reducedRight` half** (this file) — the *marginal-consistency* fact that the
  `R ⊗ (B ⊗ C)` marginal `τ := (ρ.purify.congr (pullRefReshape ..)).reducedRight` has the *same*
  `B ⊗ C`-marginal as `ρ` itself, so the `S(B)` and `S(B,C)` terms produced by strong subadditivity
  on `τ` are `ρ`'s own marginals.

## What this file provides

* `State.reducedRight_reducedLeft_congr_assoc_symm` — trace out `A` then `R` (through the inverse
  associator on `(A ⊗ M) ⊗ R`) equals trace out `R` then `A`; the reverse of
  `State.reducedRight_reducedLeft_congr_assoc` (`Postulates/API/SubadditivityReformulations`),
  obtained by the associator-cancellation trick (as for
  `State.reducedLeft_reducedLeft_congr_assoc`): instantiate the forward lemma at
  `ω.congr (assoc _ _ _).symm` and cancel `(assoc).symm.trans assoc = refl` (the transport-backbone
  left-inverse law `QSystem.Iso.symm_trans_self`, `Postulates/API/ReducedStateTransport`), so no new
  proof at the level of the density operator `.op` is needed.
* `State.reducedRight_reducedRight_congr_pullRefReshape` — the **crux**: for any state `ω` on
  `(A ⊗ M) ⊗ R`, the `M`-marginal of the reference-pull marginal
  `(ω.congr (QSystem.pullRefReshape A M R)).reducedRight` equals the `M`-marginal of
  `ω.reducedLeft`.
  With `M := B ⊗ C` and `ω := ρ.purify` (so `ω.reducedLeft = ρ` by `State.purify_reducedLeft_eq`),
  this is exactly `τ.reducedRight = ρ.reducedRight`.

It reuses the one-factor reshape quartet from `Postulates/API/ReducedStateReshape` — in particular
`State.reducedRight_congr_tmul_right` (reshaping the *kept* right factor conjugates the right
marginal), which peels the reference swap `id ⊗ comm` off the `reducedRight`.

## Ingredients

The proofs use the `partialTraceLeft` naturality (through the reshaping lemmas above). The
`reducedLeft ↔ reducedRight` swap it uses is `State.reducedLeft_congr_comm`
(`Postulates/API/ReducedStateComm`); the associator trace-commutation is
`State.reducedRight_reducedLeft_congr_assoc` (`Postulates/API/SubadditivityReformulations`).

Weak monotonicity is assembled from this together with the `reducedLeft` half in
`AxQM/NC/Ch11/Exercise11_24.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A M R : QSystem}

/-- **`A`-then-`R` marginal via the inverse associator equals `R`-then-`A`.** For a state `ω` on
the left-nested composite `(A ⊗ M) ⊗ R`, re-associating to `A ⊗ (M ⊗ R)`, tracing out `A`
(`reducedRight`), then tracing out `R` (`reducedLeft`) gives the same `M`-marginal as tracing out
`R` (`reducedLeft`) then `A` (`reducedRight`):

`Tr_R (Tr_A (assoc⁻¹ ω)) = Tr_A (Tr_R ω)`.

The reverse face of `State.reducedRight_reducedLeft_congr_assoc` (which applies the
trace-commutation `LinearMap.partialTraceLeft_partialTraceRight_assoc` once), obtained by cancelling
the associator against its inverse: instantiate the forward lemma at
`ω.congr (assoc A M R).symm` and rewrite `(assoc).symm.trans assoc = refl`
(`QSystem.Iso.symm_trans_self`). -/
theorem State.reducedRight_reducedLeft_congr_assoc_symm (ω : State ((A ⊗ M) ⊗ R)) :
    ((State.congr (QSystem.assoc A M R).symm ω).reducedRight).reducedLeft =
      ω.reducedLeft.reducedRight := by
  have h := State.reducedRight_reducedLeft_congr_assoc (State.congr (QSystem.assoc A M R).symm ω)
  rw [← State.congr_trans, QSystem.Iso.symm_trans_self, State.congr_refl] at h
  exact h.symm

/-- **`M`-marginal consistency of the reference-pull marginal** (N&C Exercise 11.24). For any state
`ω` on `(A ⊗ M) ⊗ R`, the `M`-marginal of the reference-pull `R ⊗ M` marginal
`(ω.congr (QSystem.pullRefReshape A M R)).reducedRight` equals the `M`-marginal of `ω`'s `A ⊗ M`
marginal `ω.reducedLeft`:

`((pullRefReshape ω)ʳ)ʳ = (ωˡ)ʳ`.

Both trace out `A` and `R`, leaving `M`; the identity is that the order and the reference
re-bracketing do not matter. With `M := B ⊗ C` and `ω := ρ.purify` (whose left marginal is `ρ`,
`State.purify_reducedLeft_eq`) this is `τ.reducedRight = ρ.reducedRight`, so the `S(B,C)` term of
strong subadditivity applied to the reference marginal `τ` is `S(ρ.reducedRight)` and (one more
`reducedLeft`) the `S(B)` term is `S(ρ.reducedRight.reducedLeft)`. Peels the reference swap off the
`reducedRight` via `State.reducedRight_congr_tmul_right`, cancels it against
`State.reducedLeft_congr_comm`, and closes with
`State.reducedRight_reducedLeft_congr_assoc_symm`. -/
theorem State.reducedRight_reducedRight_congr_pullRefReshape (ω : State ((A ⊗ M) ⊗ R)) :
    ((State.congr (QSystem.pullRefReshape A M R) ω).reducedRight).reducedRight =
      ω.reducedLeft.reducedRight := by
  rw [QSystem.pullRefReshape, State.congr_trans, State.reducedRight_congr_tmul_right,
    ← State.reducedLeft_congr_comm]
  exact State.reducedRight_reducedLeft_congr_assoc_symm ω

end AxQM
