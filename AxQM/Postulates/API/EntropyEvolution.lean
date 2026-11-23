/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.API.Evolution

/-!
# AxQM — invariance of the von Neumann entropy under unitary evolution

The von Neumann entropy is unchanged by unitary evolution:

`S(U ρ U†) = S(ρ)`.

This is the operator-conjugation counterpart of the transport-invariance lemma
`State.vonNeumannEntropy_congr` (entropy is unchanged along a *system* isomorphism): here the
isometry equivalence is the one packaged from the unitary `U` itself (`Evolution.toIsometryEquiv`),
so `U ρ U†` is `U.toIsometryEquiv`-conjugate to `ρ` and hence has the same eigenvalue spectrum.

It is the first ingredient of Nielsen & Chuang's proof of **Theorem 11.15(3)** (quantum operations
never increase mutual information, p. 523): that proof dilates the channel on `B` to a unitary
interaction `U` on `B ⊗ C` with a pure ancilla, and uses that this *local* unitary changes neither
the joint entropy `S(A,B,C)` nor the marginal entropy `S(B,C)`, so the mutual information `S(A:B,C)`
is preserved. Both of those invariances are instances of the lemma below (applied to the joint state
and to the `B ⊗ C`-marginal). The full Theorem 11.15(3) is
`State.vonNeumannMutualInfo_dilatedChannelOnRight_le` in `AxQM/NC/Ch11/Theorem11_15.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Unitary invariance of the von Neumann entropy**: conjugation by a unitary evolution leaves the
entropy unchanged, `S(U ρ U†) = S(ρ)`. Unitary conjugation preserves the eigenvalue spectrum, so it
preserves the Shannon entropy of that spectrum. Proved by exhibiting `U.evolve ρ = U ρ U†` as the
`U.toIsometryEquiv`-conjugate of `ρ` (the bridge `Evolution.evolve_op_conjStarAlgEquiv`) and
invoking the operator fact `ContinuousLinearMap.vonNeumannEntropy_conjStarAlgEquiv`. No faithfulness
hypothesis is needed — the entropy of any state is preserved.

The operator-conjugation counterpart of `State.vonNeumannEntropy_congr` (invariance along a system
isomorphism); a building block of Nielsen & Chuang Theorem 11.15(3). -/
@[simp] theorem State.vonNeumannEntropy_evolve (U : Evolution S) (ρ : State S) :
    (U.evolve ρ).vonNeumannEntropy = ρ.vonNeumannEntropy := by
  -- `U ρ U†` is the conjugate of `ρ` by the isometry equivalence `U.toIsometryEquiv`
  -- (`Evolution.evolve_op_conjStarAlgEquiv`), and conjugation preserves the spectrum.
  rw [State.vonNeumannEntropy_def, State.vonNeumannEntropy_def,
    Evolution.evolve_op_conjStarAlgEquiv, ContinuousLinearMap.vonNeumannEntropy_conjStarAlgEquiv]

end AxQM
