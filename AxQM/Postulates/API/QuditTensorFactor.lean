/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditPairPermGate
import AxQM.Postulates.API.QuditMeasurement
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.SystemIso

/-!
# AxQM.Postulates.API — factoring a qudit of composite dimension

A `d·e`-level system is a *bipartite* system: `qudit (d·e) ≃ₛ qudit d ⊗ qudit e`, identifying the
computational basis `|x·e + y⟩` of the single register with the product basis `|x⟩ ⊗ |y⟩` of the
pair. This file supplies that **system isomorphism** and its computational-basis action.

## What is formalised

* `quditProdIso d e` — the system isomorphism `qudit (d·e) ≃ₛ qudit d ⊗ qudit e`. It is the
  `OrthonormalBasis.equiv` sending the computational basis `quditOrthonormalBasis (d·e)` of
  `qudit (d·e)` to the product basis `quditPairBasis d e` of `qudit d ⊗ qudit e` along
  `finProdFinEquiv : Fin d × Fin e ≃ Fin (d·e)`; packaged as a `QSystem.Iso` (a linear isometric
  equivalence of state spaces), exactly as `quditFinCardIso` is built from `OrthonormalBasis.equiv`.
* `quditProdIso_toIsometry_quditBasis` — the **defining action** on vectors:
  `Φ |finProdFinEquiv (x, y)⟩ = |x⟩ ⊗ |y⟩`.
* `quditProdIso_congr_quditBasis` / `quditProdIso_congr_toState` — the same action transported to
  pure states and to density-operator states: `Φ · |x·e+y⟩ = |x⟩ ⊗ |y⟩` and
  `Φ · |x·e+y⟩⟨x·e+y| Φ⁻¹ = (|x⟩ ⊗ |y⟩)(⟨x| ⊗ ⟨y|)`. These are what a caller rewrites with, rather
  than re-unfolding the iso into its `OrthonormalBasis.equiv`.

## Index convention

`finProdFinEquiv (x, y)` has value `x·e + y` (`finProdFinEquiv_apply_val`), so `x : Fin d` is the
**high** (most-significant) part and `y : Fin e` the low part. Hence `quditProdIso 2 e` (using
`qubit = qudit 2` definitionally) is `qudit (2·e) ≃ₛ qubit ⊗ qudit e` peeling the leading qubit off
the front — the big-endian `|j₁⟩ ⊗ |j₂…jₙ⟩` split of N&C's `|j₁,…,jₙ⟩` register (§5.1). Iterating it
identifies `qudit (2ⁿ)` with an `n`-qubit tensor register; that recursion, and the transport of
`qftEvolution` onto it, are used in the whole-circuit measured-QFT reduction (Problem 5.2).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {d e : ℕ}

/-- **Factoring a composite-dimension qudit** `qudit (d·e) ≃ₛ qudit d ⊗ qudit e`: the system
isomorphism identifying the `d·e`-level register with the bipartite `d`-by-`e` register. Built as
the `OrthonormalBasis.equiv` sending the computational basis `quditOrthonormalBasis (d·e)` to the
product basis `quditPairBasis d e` along `finProdFinEquiv : Fin d × Fin e ≃ Fin (d·e)` — so
`|finProdFinEquiv (x, y)⟩ ↦ |x⟩ ⊗ |y⟩` (`quditProdIso_toIsometry_quditBasis`). Mirrors
`quditFinCardIso`'s `OrthonormalBasis.equiv` construction of a `QSystem.Iso`. -/
def quditProdIso (d e : ℕ) : (qudit (d * e)) ≃ₛ (qudit d ⊗ qudit e) :=
  ⟨(quditOrthonormalBasis (d * e)).equiv (quditPairBasis d e) finProdFinEquiv.symm⟩

/-- The underlying isometry of `quditProdIso` is the basis-reindexing equivalence it is defined by.
An unfolding lemma so the action lemmas can rewrite through the `QSystem.Iso` wrapper. -/
theorem quditProdIso_toIsometry (d e : ℕ) :
    (quditProdIso d e).toIsometry
      = (quditOrthonormalBasis (d * e)).equiv (quditPairBasis d e) finProdFinEquiv.symm :=
  rfl

/-- **Defining action of `quditProdIso` on a computational-basis vector.** The factorisation
isometry sends the single-register ket `|finProdFinEquiv (x, y)⟩ = |x·e + y⟩` to the product ket
`|x⟩ ⊗ |y⟩`. Proof: the ket is the basis vector `quditOrthonormalBasis (d·e)` at
`finProdFinEquiv (x, y)` (`quditOrthonormalBasis_apply`), so `OrthonormalBasis.equiv_apply_basis`
moves the isometry to `quditPairBasis d e` at `finProdFinEquiv.symm (finProdFinEquiv (x, y)) =
(x, y)`, which is `|x⟩ ⊗ |y⟩` by `quditPairBasis_apply`. -/
theorem quditProdIso_toIsometry_quditBasis (d e : ℕ) (x : Fin d) (y : Fin e) :
    (quditProdIso d e).toIsometry (quditBasis (finProdFinEquiv (x, y))).vec
      = (quditBasis x).vec ⊗ₜ[ℂ] (quditBasis y).vec := by
  rw [quditProdIso_toIsometry, ← quditOrthonormalBasis_apply, OrthonormalBasis.equiv_apply_basis,
    Equiv.symm_apply_apply, quditPairBasis_apply]

/-- **Action of `quditProdIso` on a computational-basis pure state:** transporting the ket
`|finProdFinEquiv (x, y)⟩` of `qudit (d·e)` along the factorisation gives the product pure state
`|x⟩ ⊗ |y⟩` of `qudit d ⊗ qudit e`. The `PureState` companion of
`quditProdIso_toIsometry_quditBasis`. -/
theorem quditProdIso_congr_quditBasis (d e : ℕ) (x : Fin d) (y : Fin e) :
    PureState.congr (quditProdIso d e) (quditBasis (finProdFinEquiv (x, y)))
      = (quditBasis x) ⊗ (quditBasis y) := by
  apply PureState.ext
  rw [PureState.congr_vec, PureState.tmul_vec, quditProdIso_toIsometry_quditBasis]

/-- **The symm-direction basis law for `quditProdIso`.** The companion of
`quditProdIso_congr_quditBasis`: transporting a product basis state `|x⟩ ⊗ |y⟩` back along
`(quditProdIso d e).symm` gives the computational basis vector at the packed index
`finProdFinEquiv (x, y)`. Immediate from the forward law via the `symm`-transport roundtrip
`PureState.congr_symm_congr`. -/
theorem quditProdIso_symm_congr_quditBasis (d e : ℕ) (x : Fin d) (y : Fin e) :
    PureState.congr (quditProdIso d e).symm ((quditBasis x).tmul (quditBasis y))
      = quditBasis (finProdFinEquiv (x, y)) := by
  rw [← quditProdIso_congr_quditBasis d e x y, PureState.congr_symm_congr]

/-- **Action of `quditProdIso` on a computational-basis density-operator state:** transporting the
diagonal state `|finProdFinEquiv (x, y)⟩⟨finProdFinEquiv (x, y)|` along the factorisation gives the
product state `(|x⟩ ⊗ |y⟩)(⟨x| ⊗ ⟨y|)`. The `State` companion, obtained from
`quditProdIso_congr_quditBasis` through `PureState.congr_toState`. -/
theorem quditProdIso_congr_toState (d e : ℕ) (x : Fin d) (y : Fin e) :
    State.congr (quditProdIso d e) (quditBasis (finProdFinEquiv (x, y))).toState
      = ((quditBasis x) ⊗ (quditBasis y)).toState := by
  rw [← PureState.congr_toState, quditProdIso_congr_quditBasis]

end AxQM
