/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditTensorFactor

/-!
# AxQM.Postulates.API — reindexing a qudit across an equality of dimensions

Two qudit systems `qudit d` and `qudit e` whose dimensions are *propositionally* equal (`d = e`)
but not *definitionally* so — e.g. `qudit (2^(n+1))` and `qudit (2 * 2^n)` (`pow_succ'`), or
`qudit (2^(n+2))` and `qudit (2 * 2^(n+1))` — are distinct types, so a term of one cannot be used
where the other is expected. This file supplies the **system isomorphism** reconciling them, the
sibling of `quditFinCardIso` (which reconciles `qudit r` with `qudit (Fintype.card (Fin r))`).

## What is formalised

* `quditDimCongr h` — for `h : d = e`, the system isomorphism `qudit d ≃ₛ qudit e`, built as the
  `OrthonormalBasis.equiv` sending the computational basis `quditOrthonormalBasis d` to
  `quditOrthonormalBasis e` along `finCongr h : Fin d ≃ Fin e`; packaged as a `QSystem.Iso`, exactly
  as `quditFinCardIso` is built.
* `quditDimCongr_toIsometry` — the underlying isometry is that basis-reindexing equivalence (an
  unfolding lemma for the action proofs).
* `quditDimCongr_congr_quditBasis` — the **defining action**: the cast sends the computational-basis
  ket `|j⟩` to `|Fin.cast h j⟩` (`= |finCongr h j⟩`). This is what a caller rewrites with, rather
  than re-unfolding the iso.

Compare `quditFinCardIso`, `quditProdIso` and `quditPairBasis`. A `QSystem.Iso` is a plain
isometry of the underlying state spaces.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d e : ℕ}

/-- **Reindexing a qudit across an equality of dimensions** `qudit d ≃ₛ qudit e` for `h : d = e`:
the system isomorphism identifying the two (propositionally-equal-dimension) registers, built as the
`OrthonormalBasis.equiv` sending the computational basis `quditOrthonormalBasis d` to
`quditOrthonormalBasis e` along `finCongr h : Fin d ≃ Fin e` — so `|j⟩ ↦ |Fin.cast h j⟩`
(`quditDimCongr_congr_quditBasis`). Mirrors `quditFinCardIso`'s `OrthonormalBasis.equiv`
construction of a `QSystem.Iso`; the special case reconciling `qudit (2·2ⁿ)` with `qudit (2ⁿ⁺¹)`
that the measured-QFT register bridge (Problem 5.2) iterates. -/
def quditDimCongr (h : d = e) : (qudit d) ≃ₛ (qudit e) :=
  ⟨(quditOrthonormalBasis d).equiv (quditOrthonormalBasis e) (finCongr h)⟩

/-- The underlying isometry of `quditDimCongr` is the basis-reindexing equivalence it is defined by.
An unfolding lemma so the action lemma can rewrite through the `QSystem.Iso` wrapper. -/
theorem quditDimCongr_toIsometry (h : d = e) :
    (quditDimCongr h).toIsometry
      = (quditOrthonormalBasis d).equiv (quditOrthonormalBasis e) (finCongr h) :=
  rfl

/-- **Defining action of `quditDimCongr` on a computational-basis pure state.** The dimension cast
sends the ket `|j⟩` of `qudit d` to `|finCongr h j⟩ = |Fin.cast h j⟩` of `qudit e`. Proof:
`PureState.ext` reduces it to the action `Φ |j⟩ = |finCongr h j⟩`, which is
`OrthonormalBasis.equiv_apply_basis` for the two computational bases (after
`quditOrthonormalBasis_apply` moves between `(quditBasis _).vec` and the orthonormal basis). -/
theorem quditDimCongr_congr_quditBasis (h : d = e) (j : Fin d) :
    PureState.congr (quditDimCongr h) (quditBasis j) = quditBasis (finCongr h j) := by
  apply PureState.ext
  rw [PureState.congr_vec, quditDimCongr_toIsometry, ← quditOrthonormalBasis_apply,
    OrthonormalBasis.equiv_apply_basis, quditOrthonormalBasis_apply]

end AxQM
