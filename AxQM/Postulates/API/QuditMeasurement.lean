/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GeneralizedDepolarizingChannel
import AxQM.Postulates.API.ProjectiveMeasurement
import AxQM.Postulates.SystemIso

/-!
# AxQM.Postulates.API — the computational-basis measurement of a qudit

The **projective measurement of `qudit d` in the computational basis** `{|0⟩, …, |d−1⟩}`, the
final read-out step of the qudit quantum algorithms of Nielsen & Chuang (Chapters 5–6): measuring
the register and reading off which basis state `|i⟩` it collapsed to.

* `quditMeasurement d` — the projective `Measurement (Fin d) (qudit d)` in the standard basis,
  `Measurement.ofOrthonormalBasis` of the computational orthonormal basis `quditOrthonormalBasis d`
  (`= EuclideanSpace.basisFun`). Outcome `i` has measurement operator `|i⟩⟨i|`. The `d`-level
  generalisation of the two-outcome `groverSolutionMeasurement` of Exercise 6.4.
* `quditMeasurement_op` — the `.op`-level unfolding: `(quditMeasurement d).op x = |x⟩⟨x|`, the
  rank-one projector onto the computational-basis state `|x⟩`.
* `bornProb_quditMeasurement_toState` — the Born rule for it on a pure state `ψ`:
  `p(i) = ‖⟨i, ψ⟩‖²`, the squared amplitude of `|ψ⟩` on the basis state `|i⟩`. This is N&C's
  `p(m) = |⟨m|ψ⟩|²` for a computational-basis measurement, specialised so the amplitude is written
  against the computational-basis pure states `quditBasis i` used throughout the library.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- The **computational-basis (projective) measurement** of `qudit d`: the projective measurement in
the standard basis `{|i⟩}`, with outcome `i : Fin d` the rank-one projector `|i⟩⟨i|` — "the register
was found in the state `|i⟩`". Built from the computational orthonormal basis
`quditOrthonormalBasis` (`= EuclideanSpace.basisFun`). This is N&C's measurement of a register in
the computational basis (the read-out step of the search and other algorithms), and the `d`-level
generalisation of the two-outcome `groverSolutionMeasurement`. -/
def quditMeasurement (d : ℕ) : Measurement (Fin d) (qudit d) :=
  Measurement.ofOrthonormalBasis (quditOrthonormalBasis d)

/-- The computational orthonormal basis is the family of computational-basis pure states:
`quditOrthonormalBasis d i = |i⟩ = (quditBasis i).vec` (both are `EuclideanSpace.single i 1`). -/
theorem quditOrthonormalBasis_apply (i : Fin d) :
    quditOrthonormalBasis d i = (quditBasis i).vec := by
  rw [quditBasis_vec]; exact EuclideanSpace.basisFun_apply (Fin d) ℂ i

/-- **The reindexing isomorphism `qudit r ≃ₛ qudit (Fintype.card (Fin r))`.** For a type of `r`
outcomes, results indexed over `Fin r` (e.g. the apparatus register `qudit r` of a measurement
operation) and results indexed over a generic finite type `ι` reindexed by `Fintype.equivFin`
(e.g. `Measurement.measState`, which records the outcome in `qudit (Fintype.card ι)`) live on
distinct qudit systems, because `Fintype.card (Fin r) = r` holds only *propositionally*, not
definitionally. This is the system isomorphism reconciling them: it sends the computational ket
`|y⟩` to `|Fintype.equivFin y⟩`, built as the `OrthonormalBasis.equiv` of the two computational
bases along `Fintype.equivFin (Fin r)`. It is the `qudit (Fintype.card ι)` reindexing anticipated
by `quditBasis_equivFin_orthonormal`, and its action on states is `quditFinCardIso_congr_toState`.
Under it every system-iso-invariant quantity is preserved (`State.vonNeumannEntropy_congr`,
`State.holevoChi_congr`), so it lets the χ / entropy of a `qudit r`-marginal be identified with that
of the corresponding `measState`. -/
def quditFinCardIso (r : ℕ) : (qudit r) ≃ₛ (qudit (Fintype.card (Fin r))) :=
  ⟨(quditOrthonormalBasis r).equiv (quditOrthonormalBasis (Fintype.card (Fin r)))
    (Fintype.equivFin (Fin r))⟩

/-- **Action of `quditFinCardIso` on a computational-basis state.** Transporting the outcome ket
`|y⟩` on `qudit r` along the reindexing isomorphism gives the reindexed ket `|Fintype.equivFin y⟩`
on `qudit (Fintype.card (Fin r))`:

`State.congr (quditFinCardIso r) |y⟩⟨y| = |Fintype.equivFin y⟩⟨Fintype.equivFin y|`.

This is the companion action lemma of `quditFinCardIso`; it is what a caller rewrites with (rather
than re-unfolding the iso into its `OrthonormalBasis.equiv`), e.g. to match a `qudit r`-marginal's
diagonal Born state with `Measurement.measState`. Proof: `PureState.congr_toState` reduces it to
the vector action `quditFinCardIso |y⟩ = |Fintype.equivFin y⟩`, which is
`OrthonormalBasis.equiv_apply_basis` for the two computational bases. -/
theorem quditFinCardIso_congr_toState (r : ℕ) (y : Fin r) :
    State.congr (quditFinCardIso r) (quditBasis y).toState
      = (quditBasis (Fintype.equivFin (Fin r) y)).toState := by
  rw [← PureState.congr_toState]
  congr 1
  apply PureState.ext
  rw [PureState.congr_vec]
  change (quditOrthonormalBasis r).equiv (quditOrthonormalBasis (Fintype.card (Fin r)))
      (Fintype.equivFin (Fin r)) (quditBasis y).vec
    = (quditBasis (Fintype.equivFin (Fin r) y)).vec
  rw [← quditOrthonormalBasis_apply, OrthonormalBasis.equiv_apply_basis,
    quditOrthonormalBasis_apply]

/-- **The computational-basis measurement operator is the rank-one projector** `|x⟩⟨x|`:
`(quditMeasurement d).op x = |x⟩⟨x|` (`rankOne` of the computational-basis vector with itself). The
`.op`-level unfolding of `quditMeasurement = ofOrthonormalBasis (quditOrthonormalBasis d)` via
`Measurement.ofOrthonormalBasis_op` and `quditOrthonormalBasis_apply`. -/
theorem quditMeasurement_op (x : Fin d) :
    (quditMeasurement d).op x
      = InnerProductSpace.rankOne ℂ (quditBasis x).vec (quditBasis x).vec := by
  rw [quditMeasurement, Measurement.ofOrthonormalBasis_op, quditOrthonormalBasis_apply]

/-- **Born rule for the computational-basis measurement, on a pure state.** The probability of
outcome `i` when the pure state `ψ` is measured in the computational basis is the squared amplitude
`‖⟨i, ψ⟩‖²` on the basis state `|i⟩ = quditBasis i` — N&C's `p(m) = |⟨m|ψ⟩|²`. Immediate from the
projective Born rule `bornProb_ofOrthonormalBasis_toState` and `quditOrthonormalBasis_apply`. -/
theorem bornProb_quditMeasurement_toState (ψ : PureState (qudit d)) (i : Fin d) :
    (quditMeasurement d).bornProb ψ.toState i = ‖inner ℂ (quditBasis i).vec ψ.vec‖ ^ 2 := by
  rw [quditMeasurement, Measurement.bornProb_ofOrthonormalBasis_toState,
    quditOrthonormalBasis_apply]

/-- **The computational-basis measurement of a computational-basis state is deterministic.** The
probability of outcome `x` when the basis state `|y⟩` is measured in the computational basis is `1`
if `x = y` and `0` otherwise — the register is found in exactly the basis state it is in. Immediate
from `bornProb_quditMeasurement_toState` (`p(x) = ‖⟨x|y⟩‖²`) and orthonormality of the computational
basis (`quditBasis_inner`, `⟨x|y⟩ = δₓᵧ`). This is the `p(m) = |⟨m|ψ⟩|²` Born rule collapsing to a
Kronecker delta on a basis input; it is why measuring the computational-basis projectors on a
(corrupted) basis codeword yields a *certain* outcome. -/
theorem bornProb_quditMeasurement_quditBasis (y x : Fin d) :
    (quditMeasurement d).bornProb (quditBasis y).toState x = if x = y then 1 else 0 := by
  rw [bornProb_quditMeasurement_toState, quditBasis_inner]
  split_ifs with h <;> simp

end AxQM
