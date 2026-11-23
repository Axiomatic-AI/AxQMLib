/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliMeasurement
import AxQM.Postulates.API.PauliEigen
import AxQM.Postulates.API.EigenspaceCollapse

/-!
# AxQM.Postulates.API — measurement in the stabilizer formalism (N&C §10.5.3)

The update rules for **measuring a Pauli-group observable on a stabilizer state**,
the content of Nielsen & Chuang §10.5.3 (pp. 463–464) that the Gottesman–Knill theorem (Theorem
10.7) turns into a classical-simulation step. A Pauli-group element `g` (a product of Pauli
matrices, no `±1`/`±i` phase) is a self-adjoint **involution** `g² = I` — a `±1` observable — so
its projective measurement is the `Observable.signMeasurement` of `Postulates/API/PauliMeasurement`
(outcome `0 ↔ +1`, `1 ↔ −1`). Given a state `|ψ⟩` with stabilizer `⟨g₁, …, gₙ⟩`, N&C split the
measurement of such a `g` into two cases.

## The deterministic case: `g` (or `−g`) is in the stabilizer

If `g` commutes with all generators then either `g` or `−g` is in the stabilizer. N&C treat both
sub-outcomes; both are formalised here.

*Sub-case `g ∈ S` (`g|ψ⟩ = |ψ⟩`, `A.HasEigenstate 1 ψ`):* outcome `+1` is certain and the state is
undisturbed —

* `bornProb_signMeasurement_plus_of_hasEigenstate_one` — `p(+1) = 1`;
* `bornProb_signMeasurement_minus_of_hasEigenstate_one` — `p(−1) = 0`;
* `postMeasPlus_eq_of_hasEigenstate_one` — the collapse `P₊|ψ⟩/‖P₊|ψ⟩‖` equals `|ψ⟩`.

*Sub-case `−g ∈ S` (`g|ψ⟩ = −|ψ⟩`, `A.HasEigenstate (-1) ψ`):* the mirror, outcome `−1` certain and
undisturbed —

* `bornProb_signMeasurement_minus_of_hasEigenstate_neg_one` — `p(−1) = 1`;
* `bornProb_signMeasurement_plus_of_hasEigenstate_neg_one` — `p(+1) = 0`;
* `postMeasMinus_eq_of_hasEigenstate_neg_one` — the collapse `P₋|ψ⟩/‖P₋|ψ⟩‖` equals `|ψ⟩`.

This is N&C's "a measurement of `g` yields `+1` with probability one … does not disturb the state …
leaves the stabilizer invariant", together with "if instead `−g ∈ S` … yields `−1` with probability
one, and again does not disturb the state".

## The random case: `g` anticommutes with a stabilizer generator

If `g` anticommutes with a generator `g₁` with `g₁|ψ⟩ = |ψ⟩`, then (N&C eqs. 10.96–10.100) the two
outcomes are equiprobable:

* `expectation_eq_zero_of_anticomm_stabilizer` — the engine: `⟪g⟫_ψ = 0`, because
  `⟪ψ, gψ⟫ = ⟪ψ, g g₁ ψ⟫ = −⟪ψ, g₁ g ψ⟫ = −⟪g₁ ψ, g ψ⟫ = −⟪ψ, g ψ⟫` (using `g₁|ψ⟩ = |ψ⟩`, `g₁`
  self-adjoint and `g g₁ = −g₁ g`), so `⟪ψ, gψ⟫ = −⟪ψ, gψ⟫ = 0`;
* `bornProb_signMeasurement_plus_of_anticomm` — `p(+1) = 1/2`;
* `bornProb_signMeasurement_minus_of_anticomm` — `p(−1) = 1/2`.

After outcome `+1` (resp. `−1`) the posterior state is a `+1` (resp. `−1`) eigenstate of `g`
(`Observable.postMeasPlus_hasEigenstate` / `postMeasMinus_hasEigenstate`), i.e. it is stabilized by
`g` (resp. `−g`) — the stabilizer's leading generator is replaced by `±g`.

## Stabilizer preservation

Any other generator that commutes with `g` and stabilizes `|ψ⟩` still stabilizes the collapsed
state, so the tail `g₂, …, gₙ` of the stabilizer is carried through unchanged:

* `hasEigenstate_one_postMeasPlus_of_commute`, `hasEigenstate_one_postMeasMinus_of_commute`.

Together the new stabilizer is `⟨±g, g₂, …, gₙ⟩`, exactly N&C's post-measurement stabilizer. These
lemmas presuppose the surviving generator commutes with `g` — N&C's WLOG normalisation of the
generator set: if some `gₖ` (`k ≥ 2`) anticommutes with `g`, replace it by `g₁ gₖ`, which commutes
with `g` and generates the same group, so that only `g₁` anticommutes. That purely
generator-bookkeeping reduction is not itself formalised here.

This extends the `±1`-observable measurement family of `PauliMeasurement` /
`EigenspaceCollapse`. The statement of Theorem 10.7 (the classical-simulability statement) is in
`AxQM/NC/Ch10/Theorem10_7_GottesmanKnill.lean`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Observable

/-! ### The deterministic case: the observable already stabilizes `|ψ⟩` -/

/-- **N&C §10.5.3 (deterministic outcome).** If a `±1` observable `A` stabilizes `|ψ⟩`
(`A|ψ⟩ = |ψ⟩`, i.e. `A.HasEigenstate 1 ψ`), then measuring `A` yields `+1` with certainty:
`p(+1) = 1`. Immediate from `bornProb_signMeasurement_plus` (`p(+1) = (1 + ⟪A⟫_ψ)/2`) and
`expectation_of_hasEigenstate` (`⟪A⟫_ψ = 1`). -/
theorem bornProb_signMeasurement_plus_of_hasEigenstate_one (A : Observable S)
    (hinv : A.op * A.op = 1) (ψ : PureState S) (h : A.HasEigenstate 1 ψ) :
    (A.signMeasurement hinv).bornProb ψ.toState 0 = 1 := by
  rw [bornProb_signMeasurement_plus, PureState.expectation_of_hasEigenstate h]; norm_num

/-- **N&C §10.5.3 (deterministic outcome).** If a `±1` observable `A` stabilizes `|ψ⟩`, the outcome
`−1` is impossible: `p(−1) = 0`. From `p(+1) = 1` and `∑ᵢ p(i) = 1`. -/
theorem bornProb_signMeasurement_minus_of_hasEigenstate_one (A : Observable S)
    (hinv : A.op * A.op = 1) (ψ : PureState S) (h : A.HasEigenstate 1 ψ) :
    (A.signMeasurement hinv).bornProb ψ.toState 1 = 0 := by
  have hsum := (A.signMeasurement hinv).sum_bornProb_eq_one ψ.toState
  rw [Fin.sum_univ_two,
    bornProb_signMeasurement_plus_of_hasEigenstate_one A hinv ψ h] at hsum
  linarith

/-- **N&C §10.5.3 (state undisturbed).** If a `±1` observable `A` stabilizes `|ψ⟩`, the `+1`
collapse leaves the state unchanged: `P₊|ψ⟩/‖P₊|ψ⟩‖ = |ψ⟩`. Here `P₊|ψ⟩ = |ψ⟩`
(`projPlus_apply_eq_self`) and `‖ψ‖ = 1`, so normalization is the identity. This is N&C's "the
measurement does not disturb the state of the system, and thus leaves the stabilizer invariant". -/
theorem postMeasPlus_eq_of_hasEigenstate_one (A : Observable S) (ψ : PureState S)
    (h : A.HasEigenstate 1 ψ) (hne : A.projPlus ψ.vec ≠ 0) :
    A.postMeasPlus ψ hne = ψ := by
  have hAψ : A.op ψ.vec = ψ.vec := by simpa [Observable.HasEigenstate] using h
  apply PureState.ext
  rw [postMeasPlus_vec, A.projPlus_apply_eq_self hAψ, ψ.normalized]
  simp

/-- **N&C §10.5.3 (deterministic outcome, `−g ∈ S`).** The mirror sub-case: if a `±1` observable
`A` has `|ψ⟩` as a `−1` eigenstate (`A|ψ⟩ = −|ψ⟩`, i.e. `−A` — equivalently `−g` — stabilizes
`|ψ⟩`), then measuring `A` yields `−1` with certainty: `p(−1) = 1`. From `p(−1) = ‖P₋|ψ⟩‖²` with
`P₋|ψ⟩ = |ψ⟩` (`projMinus_apply_eq_self`) and `‖ψ‖ = 1`. This is N&C's "if instead `−g ∈ S` …
yields `−1` with probability one". -/
theorem bornProb_signMeasurement_minus_of_hasEigenstate_neg_one (A : Observable S)
    (hinv : A.op * A.op = 1) (ψ : PureState S) (h : A.HasEigenstate (-1) ψ) :
    (A.signMeasurement hinv).bornProb ψ.toState 1 = 1 := by
  have hAψ : A.op ψ.vec = -ψ.vec := by simpa [Observable.HasEigenstate] using h
  rw [bornProb_signMeasurement_minus_eq_normSq, A.projMinus_apply_eq_self hAψ, ψ.normalized]
  norm_num

/-- **N&C §10.5.3 (deterministic outcome, `−g ∈ S`).** If a `±1` observable `A` has `|ψ⟩` as a `−1`
eigenstate, the outcome `+1` is impossible: `p(+1) = 0`. From `p(+1) = (1 + ⟪A⟫_ψ)/2` and
`⟪A⟫_ψ = −1`. -/
theorem bornProb_signMeasurement_plus_of_hasEigenstate_neg_one (A : Observable S)
    (hinv : A.op * A.op = 1) (ψ : PureState S) (h : A.HasEigenstate (-1) ψ) :
    (A.signMeasurement hinv).bornProb ψ.toState 0 = 0 := by
  rw [bornProb_signMeasurement_plus, PureState.expectation_of_hasEigenstate h]; norm_num

/-- **N&C §10.5.3 (state undisturbed, `−g ∈ S`).** If `A` has `|ψ⟩` as a `−1` eigenstate, the `−1`
collapse leaves the state unchanged: `P₋|ψ⟩/‖P₋|ψ⟩‖ = |ψ⟩` — the `−1` mirror of
`postMeasPlus_eq_of_hasEigenstate_one`. Completes the deterministic case faithfully to N&C's "and
again does not disturb the state" for the `−g ∈ S` sub-case. -/
theorem postMeasMinus_eq_of_hasEigenstate_neg_one (A : Observable S) (ψ : PureState S)
    (h : A.HasEigenstate (-1) ψ) (hne : A.projMinus ψ.vec ≠ 0) :
    A.postMeasMinus ψ hne = ψ := by
  have hAψ : A.op ψ.vec = -ψ.vec := by simpa [Observable.HasEigenstate] using h
  apply PureState.ext
  rw [postMeasMinus_vec, A.projMinus_apply_eq_self hAψ, ψ.normalized]
  simp

/-! ### The random case: the observable anticommutes with a stabilizer generator -/

/-- **The engine of N&C eqs. (10.96)–(10.100) at an arbitrary eigenvalue: a vanishing
expectation.** If a self-adjoint `B` has `|ψ⟩` as a `μ`-eigenstate with `μ ≠ 0` (`B|ψ⟩ = μ|ψ⟩`)
and `A` anticommutes with `B` (`A B = −B A`), then the expectation of `A` in `|ψ⟩` vanishes:
`⟪A⟫_ψ = 0`. The proof slides `B` across `⟪ψ, Aψ⟫` two ways — using `Bψ = μψ` and `B` self-adjoint
it is `μ ⟪ψ, Aψ⟫`, while `B(Aψ) = −μ (Aψ)` (from `AB = −BA` and `Bψ = μψ`) makes it `−μ ⟪ψ, Aψ⟫`;
hence `μ ⟪ψ, Aψ⟫ = −μ ⟪ψ, Aψ⟫`, and `μ ≠ 0` forces `⟪ψ, Aψ⟫ = 0`. (Only `B` self-adjoint is used,
not `A² = I`.) The `μ = 1` case is `expectation_eq_zero_of_anticomm_stabilizer`; the general form is
needed e.g. for BB84's `−1`-eigenstate encodings (Exercise 12.26). -/
theorem expectation_eq_zero_of_anticomm_eigenstate (A B : Observable S) (ψ : PureState S)
    {μ : ℝ} (hμ : μ ≠ 0) (hB : B.HasEigenstate μ ψ)
    (hanti : A.op * B.op = -(B.op * A.op)) :
    ψ.expectation A = 0 := by
  have hBψ : B.op ψ.vec = (μ : ℂ) • ψ.vec := hB
  -- `B (A ψ) = -(μ • A ψ)` from anticommutation applied to `ψ` together with `B ψ = μ ψ`.
  have hBx : B.op (A.op ψ.vec) = -((μ : ℂ) • A.op ψ.vec) := by
    have h1 := congrArg (fun T : S.space →L[ℂ] S.space => T ψ.vec) hanti
    simp only [mul_apply_eq_comp, _root_.neg_apply] at h1
    rw [hBψ, map_smul] at h1
    rw [eq_comm, neg_eq_iff_eq_neg] at h1
    exact h1
  have hBadj : ContinuousLinearMap.adjoint B.op = B.op := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact B.selfAdjoint
  -- Slide `B` across `⟪ψ, B(Aψ)⟫` two ways.
  have e1 : inner ℂ ψ.vec (B.op (A.op ψ.vec)) = (μ : ℂ) * inner ℂ ψ.vec (A.op ψ.vec) := by
    conv_lhs => rw [← hBadj]
    rw [ContinuousLinearMap.adjoint_inner_right, hBψ, inner_smul_left, Complex.conj_ofReal]
  have e2 : inner ℂ ψ.vec (B.op (A.op ψ.vec)) = -((μ : ℂ) * inner ℂ ψ.vec (A.op ψ.vec)) := by
    rw [hBx, inner_neg_right, inner_smul_right]
  have hz2 : (μ : ℂ) * inner ℂ ψ.vec (A.op ψ.vec) = 0 := by
    have h := e1.symm.trans e2
    linear_combination h / 2
  have hz : inner ℂ ψ.vec (A.op ψ.vec) = 0 :=
    (mul_eq_zero.mp hz2).resolve_left (Complex.ofReal_ne_zero.mpr hμ)
  rw [PureState.expectation, hz]
  simp

/-- **The engine of N&C eqs. (10.96)–(10.100): a vanishing expectation.** If a self-adjoint `B`
stabilizes `|ψ⟩` (`B|ψ⟩ = |ψ⟩`, `B.HasEigenstate 1 ψ`) and `A` anticommutes with `B`
(`A B = −B A`), then the expectation of `A` in `|ψ⟩` vanishes: `⟪A⟫_ψ = 0`. The `μ = 1`
specialization of `expectation_eq_zero_of_anticomm_eigenstate` (`1 ≠ 0`). -/
theorem expectation_eq_zero_of_anticomm_stabilizer (A B : Observable S) (ψ : PureState S)
    (hB : B.HasEigenstate 1 ψ) (hanti : A.op * B.op = -(B.op * A.op)) :
    ψ.expectation A = 0 :=
  expectation_eq_zero_of_anticomm_eigenstate A B ψ one_ne_zero hB hanti

/-- **N&C eq. (10.100) at an arbitrary eigenvalue (`+1` outcome).** If `B` has `|ψ⟩` as a
`μ`-eigenstate with `μ ≠ 0` and the `±1` observable `A` anticommutes with `B`, then measuring `A`
is a fair coin: `p(+1) = 1/2`. From `p(+1) = (1 + ⟪A⟫_ψ)/2` and `⟪A⟫_ψ = 0`
(`expectation_eq_zero_of_anticomm_eigenstate`). The `μ = 1` case is
`bornProb_signMeasurement_plus_of_anticomm`; the general form serves e.g. BB84's `−1`-eigenstate
encodings (Exercise 12.26). -/
theorem bornProb_signMeasurement_plus_of_anticomm_eigenstate (A B : Observable S)
    (hinv : A.op * A.op = 1) (ψ : PureState S) {μ : ℝ} (hμ : μ ≠ 0)
    (hB : B.HasEigenstate μ ψ) (hanti : A.op * B.op = -(B.op * A.op)) :
    (A.signMeasurement hinv).bornProb ψ.toState 0 = 1 / 2 := by
  rw [bornProb_signMeasurement_plus, expectation_eq_zero_of_anticomm_eigenstate A B ψ hμ hB hanti]
  norm_num

/-- **N&C eq. (10.100) at an arbitrary eigenvalue (`−1` outcome).** Under the same hypotheses,
`p(−1) = 1/2`. From `p(+1) = 1/2` and `∑ᵢ p(i) = 1`. The `μ = 1` case is
`bornProb_signMeasurement_minus_of_anticomm`. -/
theorem bornProb_signMeasurement_minus_of_anticomm_eigenstate (A B : Observable S)
    (hinv : A.op * A.op = 1) (ψ : PureState S) {μ : ℝ} (hμ : μ ≠ 0)
    (hB : B.HasEigenstate μ ψ) (hanti : A.op * B.op = -(B.op * A.op)) :
    (A.signMeasurement hinv).bornProb ψ.toState 1 = 1 / 2 := by
  have hsum := (A.signMeasurement hinv).sum_bornProb_eq_one ψ.toState
  rw [Fin.sum_univ_two,
    bornProb_signMeasurement_plus_of_anticomm_eigenstate A B hinv ψ hμ hB hanti] at hsum
  linarith

/-- **N&C eq. (10.100) (`+1` outcome).** If `B` stabilizes `|ψ⟩` and the `±1` observable `A`
anticommutes with `B`, then measuring `A` is a fair coin: `p(+1) = 1/2`. The `μ = 1` specialization
of `bornProb_signMeasurement_plus_of_anticomm_eigenstate`. -/
theorem bornProb_signMeasurement_plus_of_anticomm (A B : Observable S)
    (hinv : A.op * A.op = 1) (ψ : PureState S) (hB : B.HasEigenstate 1 ψ)
    (hanti : A.op * B.op = -(B.op * A.op)) :
    (A.signMeasurement hinv).bornProb ψ.toState 0 = 1 / 2 :=
  bornProb_signMeasurement_plus_of_anticomm_eigenstate A B hinv ψ one_ne_zero hB hanti

/-- **N&C eq. (10.100) (`−1` outcome).** Under the same anticommutation hypothesis, `p(−1) = 1/2`.
The `μ = 1` specialization of `bornProb_signMeasurement_minus_of_anticomm_eigenstate`. -/
theorem bornProb_signMeasurement_minus_of_anticomm (A B : Observable S)
    (hinv : A.op * A.op = 1) (ψ : PureState S) (hB : B.HasEigenstate 1 ψ)
    (hanti : A.op * B.op = -(B.op * A.op)) :
    (A.signMeasurement hinv).bornProb ψ.toState 1 = 1 / 2 :=
  bornProb_signMeasurement_minus_of_anticomm_eigenstate A B hinv ψ one_ne_zero hB hanti

/-! ### Stabilizer preservation: commuting generators survive the collapse -/

/-- **N&C §10.5.3 (stabilizer preservation, `+1` outcome).** If `C` commutes with `A` and stabilizes
`|ψ⟩`, then `C` still stabilizes the `+1`-collapsed state `P₊|ψ⟩/‖P₊|ψ⟩‖`. So every generator of the
old stabilizer that commutes with the measured observable is carried through unchanged: with
`postMeasPlus_hasEigenstate` (`A` stabilizes the collapse) the new stabilizer is `⟨A, g₂, …, gₙ⟩`.
The commutativity hypothesis is N&C's WLOG generator-set normalisation (replace any anticommuting
`gₖ` by `g₁ gₖ` so only `g₁` anticommutes); see the module docstring. Proof: `C` fixes
`P₊|ψ⟩ = ½(|ψ⟩ + A|ψ⟩)` since `C|ψ⟩ = |ψ⟩` and `C A|ψ⟩ = A C|ψ⟩ = A|ψ⟩`. -/
theorem hasEigenstate_one_postMeasPlus_of_commute (A C : Observable S) (ψ : PureState S)
    (hcomm : C.op * A.op = A.op * C.op) (hC : C.HasEigenstate 1 ψ)
    (hne : A.projPlus ψ.vec ≠ 0) :
    C.HasEigenstate 1 (A.postMeasPlus ψ hne) := by
  have hCψ : C.op ψ.vec = ψ.vec := by simpa [Observable.HasEigenstate] using hC
  have hCA : C.op (A.op ψ.vec) = A.op ψ.vec := by
    rw [← mul_apply_eq_comp, hcomm, mul_apply_eq_comp, hCψ]
  have hfix : C.op (A.projPlus ψ.vec) = A.projPlus ψ.vec := by
    rw [projPlus]
    simp only [_root_.smul_apply, _root_.add_apply,
      one_apply_eq_self, map_smul, map_add, hCψ, hCA]
  exact hasEigenstate_of_smul (A.postMeasPlus_vec ψ hne) (by simpa using hfix)

/-- **N&C §10.5.3 (stabilizer preservation, `−1` outcome).** If `C` commutes with `A` and stabilizes
`|ψ⟩`, then `C` still stabilizes the `−1`-collapsed state `P₋|ψ⟩/‖P₋|ψ⟩‖`. Together with
`postMeasMinus_hasEigenstate` (`−A` stabilizes the collapse) the new stabilizer is
`⟨−A, g₂, …, gₙ⟩`. -/
theorem hasEigenstate_one_postMeasMinus_of_commute (A C : Observable S) (ψ : PureState S)
    (hcomm : C.op * A.op = A.op * C.op) (hC : C.HasEigenstate 1 ψ)
    (hne : A.projMinus ψ.vec ≠ 0) :
    C.HasEigenstate 1 (A.postMeasMinus ψ hne) := by
  have hCψ : C.op ψ.vec = ψ.vec := by simpa [Observable.HasEigenstate] using hC
  have hCA : C.op (A.op ψ.vec) = A.op ψ.vec := by
    rw [← mul_apply_eq_comp, hcomm, mul_apply_eq_comp, hCψ]
  have hfix : C.op (A.projMinus ψ.vec) = A.projMinus ψ.vec := by
    rw [projMinus]
    simp only [_root_.smul_apply, _root_.sub_apply,
      one_apply_eq_self, map_smul, map_sub, hCψ, hCA]
  exact hasEigenstate_of_smul (A.postMeasMinus_vec ψ hne) (by simpa using hfix)

end Observable

end AxQM
