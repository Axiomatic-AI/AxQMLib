/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerErrorCorrection
import AxQM.Concrete.PauliStringLocality

/-!
# Concrete: weight, distance, and correcting located errors (Nielsen & Chuang, Exercise 10.45)

This file formalises **Nielsen & Chuang,
Exercise 10.45** (*correcting located errors*, p. 467), building on the error-correction conditions
for stabilizer codes (Theorem 10.8, `AxQM/Concrete/StabilizerErrorCorrection.lean`). Everything here
is stated for the abstract Pauli group `PauliGroup n`, its subgroups, Pauli-string supports
(`pauliStringSupport`), and raw matrices / operators, exactly as Theorem 10.8 is.

## The weight and distance of a stabilizer code (N&C §10.5.5, p. 467)

N&C: *"the **weight** of an error `E ∈ Gₙ` [is] the number of terms in the tensor product which are
not equal to the identity"* (so `weight (X₁ Z₄ Y₈) = 3`), and *"the **distance** of a stabilizer
code `C(S)` is defined to be the minimum weight of an element of `N(S) − S`; ... we say that `C(S)`
is an `[n, k, d]` stabilizer code"* (distance `d`).

* `PauliGroup.weight p` — the weight `|supp p.idx|` (the overall phase `iˢ` is irrelevant).
* `stabilizerCodeDistance S : ℕ∞` — the minimum weight over the **nontrivial** logical operators.
  N&C's literal "`N(S) − S`" must be read modulo the global phase: the central element
  `-I = i²·I ∈ N(S)` has weight `0` and lies outside `S` (for a genuine stabilizer `-I ∉ S`), so the
  bare set-difference would collapse the distance to `0`. The genuine logical operators are the
  elements of `N(S)` that are **not** a phase multiple `iˢ·s'` of any stabilizer element `s' ∈ S`
  (equivalently `p.idx ≠ s'.idx` for all `s' ∈ S` — the string, ignoring phase, is not a
  stabilizer's). This excludes the whole center-coset `{±1, ±i}·S` (in particular `-I`, since
  `(-I).idx = 0 = 1.idx`), and it is the standard `N(S) \ ⟨iI, S⟩`; an `[n, k, d]` code has
  `stabilizerCodeDistance S = d > 0`.

## Exercise 10.45

[n,k,d] stabilizer code can correct located errors on d-1 known-position qubits.

**The argument.** Let `L` be the known set of affected qubit positions, `|L| = d − 1 < d`. Every
Pauli error `E ∈ Gₙ` supported on `L` (acting as identity off `L`) is a candidate error. For two
such errors `Eⱼ, Eₖ`, the product `Eⱼ⁻¹ Eₖ` is again supported on `L`
(`pauliStringSupport_pauliMulIndex_subset`), so its weight is at most `|L| = d − 1 < d`. An operator
of weight `< d` cannot be a nontrivial logical operator: if it lies in `N(S)` it must be a phase
multiple `iˢ·s'` of a stabilizer element (`exists_codeProjector_conj_smul_of_weight_lt`, via the
distance), and then `P Eⱼ† Eₖ P = iˢ·P`; if it lies outside `N(S)` it anticommutes with a stabilizer
generator and `P Eⱼ† Eₖ P = 0`. Either way `P Eⱼ† Eₖ P` is a scalar multiple of `P`, so the
**Knill–Laflamme conditions** (Theorem 10.1) hold with a Hermitian coefficient matrix (here defined
via the trace, `stabilizerTraceKLCoeff`), and `{Eⱼ}` is a **correctable set of errors** for `C(S)`.

The phase multiples matter: e.g. `X₁ · (Y₁ Z₂) = i·Z₁Z₂` with `Z₁Z₂ ∈ S`, so the located-error
products genuinely enter `N(S) − S` and Theorem 10.8's restricted `∉ N(S) − S` condition does
**not** apply — the general KL conditions with a *complex*-Hermitian `α` are needed, so this file
re-derives correctability rather than invoking `codeProjector_isCorrectableErrorSet` directly.

Because the `L`-supported Pauli group elements span *all* operators acting on the `L` qubits (tensor
identity elsewhere), the discretization of errors (Theorem 10.2, `correctsErrors_linearCombination`)
upgrades this to correcting an *arbitrary* noise operation on the `L` qubits — the effect N&C asks
us to correct.

## What is proved

* `PauliGroup.weight`, `pauliStringSupport_pauliMulIndex_subset`,
  `weight_inv_mul_le_of_support_subset` — the weight and its behaviour under products.
* `stabilizerCodeDistance` / `stabilizerCodeDistance_le_weight` — the (phase-corrected) code
  distance and the fact that every nontrivial logical operator has weight at least the distance.
* `codeProjector_conj_toMat_phaseStab` — `P (toMat p) P = iˢ • P` when `p` is a phase multiple of a
  stabilizer element; `exists_codeProjector_conj_smul_of_weight_lt` — for weight `< distance`,
  `P (toMat p) P` is *some* scalar multiple of `P`.
* `stabilizerTraceKLCoeff` / `stabilizerTraceKLCoeff_isHermitian` — the (trace-defined) Hermitian KL
  coefficient matrix; `codeProjector_satisfiesKL_of_weight_lt` /
  `codeProjector_satisfiesKLConditions_of_weight_lt` — the KL conditions for a family whose pairwise
  products have weight `< distance`.
* `codeProjector_isCorrectableErrorSet_of_weight_lt` — **the reusable core**: any Pauli error family
  with `weight (Eⱼ⁻¹ Eₖ) < distance` for all `j, k` is correctable (this is also N&C's "a code with
  distance `≥ 2t + 1` corrects `t` errors").
* `locatedPauliErrors_isCorrectableErrorSet` — **Exercise 10.45**: for a stabilizer `S` (`-I ∉ S`)
  and a known set `L` of affected positions with `|L| < stabilizerCodeDistance S`, the family of all
  `L`-supported Pauli errors is a correctable set of errors for `C(S)`.
* `locatedPauliErrors_isCorrectableErrorSet_of_dist_ge` — the `[n, k, d]` reading: distance at least
  `d` and fewer than `d` affected qubits (`|L| < d`, i.e. at most `d − 1`) suffice.
-/

open Matrix
open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The weight of a Pauli-group element -/

/-- The **weight** of a Pauli-group element `p ∈ Gₙ` (Nielsen & Chuang §10.5.5): the number of
tensor factors of `p` that are not the identity, i.e. the cardinality of the support of its
underlying Pauli string `p.idx`. The overall phase `iˢ` does not affect the weight; e.g.
`weight (X₁ Z₄ Y₈) = 3`. -/
def PauliGroup.weight (p : PauliGroup n) : ℕ := (pauliStringSupport p.idx).card

/-- **Support of a Pauli-string product.** The product index `pauliMulIndex a b` acts non-trivially
at a qubit only where `a` or `b` does — at a qubit outside both supports the factors are `σ_I σ_I =
σ_I` (`pauliMul 0 0 = 0`). Hence `supp (a ⊙ b) ⊆ supp a ∪ supp b`. -/
theorem pauliStringSupport_pauliMulIndex_subset (a b : Fin n → Fin 4) :
    pauliStringSupport (pauliMulIndex a b) ⊆ pauliStringSupport a ∪ pauliStringSupport b := by
  intro i hi
  rw [Finset.mem_union]
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨ha, hb⟩ := hcon
  rw [notMem_pauliStringSupport] at ha hb
  rw [mem_pauliStringSupport] at hi
  apply hi
  change pauliMul (a i) (b i) = 0
  rw [ha, hb]
  decide

/-- If two Pauli-group elements `p, q` are both **supported on a set `L`** (their underlying strings
act as the identity off `L`), then so is `p⁻¹ q` — inversion leaves the index unchanged
(`PauliGroup.inv_idx`) and the product support lies in the union of supports — so its weight is at
most `|L|`. This is the "product of two located errors is again located" step of Exercise 10.45. -/
theorem weight_inv_mul_le_of_support_subset {p q : PauliGroup n} {L : Finset (Fin n)}
    (hp : pauliStringSupport p.idx ⊆ L) (hq : pauliStringSupport q.idx ⊆ L) :
    (p⁻¹ * q).weight ≤ L.card := by
  refine Finset.card_le_card ?_
  rw [PauliGroup.mul_idx, PauliGroup.inv_idx]
  exact (pauliStringSupport_pauliMulIndex_subset p.idx q.idx).trans (Finset.union_subset hp hq)

/-- **The weight is subadditive under products**: `(p⁻¹ q).weight ≤ p.weight + q.weight`. The
product index acts non-trivially only where `p` or `q` does
(`pauliStringSupport_pauliMulIndex_subset`), so its support lies in the union of the two supports,
whose cardinality is at most the sum. Unlike `weight_inv_mul_le_of_support_subset`, the two factors
need not share a common support set — the bound needed for a general `t`-qubit error family, whose
members are arbitrary weight-`≤ t` Paulis rather than errors located on a fixed set. -/
theorem weight_inv_mul_le (p q : PauliGroup n) : (p⁻¹ * q).weight ≤ p.weight + q.weight := by
  change (pauliStringSupport (p⁻¹ * q).idx).card ≤ _
  rw [PauliGroup.mul_idx, PauliGroup.inv_idx]
  exact (Finset.card_le_card (pauliStringSupport_pauliMulIndex_subset p.idx q.idx)).trans
    (Finset.card_union_le _ _)

/-- **The weight is subadditive under products**: `(p q).weight ≤ p.weight + q.weight`. The product
index acts non-trivially only where `p` or `q` does (`pauliStringSupport_pauliMulIndex_subset`), so
its support lies in the union of the two supports, whose cardinality is at most the sum. Companion
to `weight_inv_mul_le`, for a plain product of two Paulis (e.g. an error `E` composed with its
correction `C`), rather than `p⁻¹ q`. -/
theorem weight_mul_le (p q : PauliGroup n) : (p * q).weight ≤ p.weight + q.weight := by
  change (pauliStringSupport (p * q).idx).card ≤ _
  rw [PauliGroup.mul_idx]
  exact (Finset.card_le_card (pauliStringSupport_pauliMulIndex_subset p.idx q.idx)).trans
    (Finset.card_union_le _ _)

/-! ### The distance of a stabilizer code -/

/-- The **distance** of a stabilizer code `C(S)` (Nielsen & Chuang §10.5.5): the minimum weight of a
nontrivial logical operator, taken in `ℕ∞ = WithTop ℕ`. A nontrivial logical operator is an element
`p ∈ N(S)` that is not a phase multiple of any stabilizer element (`∀ s' ∈ S, p.idx ≠ s'.idx`) —
N&C's `N(S) − S` read modulo the global phase, i.e. `N(S) \ ⟨iI, S⟩`. Using `ℕ∞` handles the trivial
case where there are no such operators (e.g. `k = 0`), for which the infimum over the empty set is
`⊤`. An `[n, k, d]` stabilizer code is one with `stabilizerCodeDistance S = d`. -/
noncomputable def stabilizerCodeDistance (S : Subgroup (PauliGroup n)) : ℕ∞ :=
  ⨅ p ∈ {p : PauliGroup n | p ∈ Subgroup.normalizer S ∧ ∀ s' ∈ S, p.idx ≠ s'.idx},
    (p.weight : ℕ∞)

/-- **Every nontrivial logical operator has weight at least the distance.** This is the defining
property of the minimum: for `p ∈ N(S)` that is not a phase multiple of any stabilizer element
(`∀ s' ∈ S, p.idx ≠ s'.idx`), the code distance lower-bounds its weight. -/
theorem stabilizerCodeDistance_le_weight {S : Subgroup (PauliGroup n)} {p : PauliGroup n}
    (hp : p ∈ Subgroup.normalizer S) (hpid : ∀ s' ∈ S, p.idx ≠ s'.idx) :
    stabilizerCodeDistance S ≤ (p.weight : ℕ∞) :=
  iInf₂_le p ⟨hp, hpid⟩

/-- **A below-distance normalizer element is a phase multiple of a stabilizer element.** For
`p ∈ N(S)` with `weight p < d`, `p.idx = s'.idx` for some `s' ∈ S`: otherwise `p` would be a
nontrivial logical operator of weight below the distance, contradicting
`stabilizerCodeDistance_le_weight`. This is the contrapositive of the distance's defining property,
and the shared step that turns "the operator is correctable" into "its projector conjugation is a
scalar" (see `exists_codeProjector_conj_smul_of_weight_lt`). -/
theorem exists_mem_idx_eq_of_mem_normalizer_of_weight_lt {S : Subgroup (PauliGroup n)}
    {p : PauliGroup n} (hN : p ∈ Subgroup.normalizer S)
    (hw : (p.weight : ℕ∞) < stabilizerCodeDistance S) : ∃ s' ∈ S, p.idx = s'.idx := by
  by_contra hcon
  refine absurd hw (not_lt.mpr (stabilizerCodeDistance_le_weight hN ?_))
  intro s' hs' heq
  exact hcon ⟨s', hs', heq⟩

/-- **The distance is at least `1`** for every stabilizer subgroup — a nontrivial logical operator
has nonzero weight. This is the sanity check that fixes the naïve reading of "`N(S) − S`": a
weight-`0` element `p` has `p.idx = 0 = (1 : Gₙ).idx` with `1 ∈ S`, so it is a phase multiple of the
identity stabilizer and is excluded from the distance's infimum. In particular the central `-I`
(weight `0`) no longer collapses the distance to `0`, and the hypotheses of the located-error
theorems below are genuinely satisfiable. -/
theorem one_le_stabilizerCodeDistance (S : Subgroup (PauliGroup n)) :
    1 ≤ stabilizerCodeDistance S := by
  rw [stabilizerCodeDistance, le_iInf₂_iff]
  rintro p ⟨-, hpid⟩
  have hne : p.idx ≠ 0 := fun h0 => hpid 1 S.one_mem (by rw [h0]; rfl)
  have hw : 1 ≤ p.weight := by
    rw [PauliGroup.weight, Nat.one_le_iff_ne_zero, ne_eq, Finset.card_eq_zero]
    intro hempty
    refine hne (funext fun i => ?_)
    have hi : i ∉ pauliStringSupport p.idx := by rw [hempty]; exact Finset.notMem_empty i
    rwa [notMem_pauliStringSupport] at hi
  exact_mod_cast hw

/-! ### The trace of the code projector -/

/-- **The trace of the unnormalized stabilizer sum is `2ⁿ`** (for a genuine stabilizer, `-I ∉ S`).
Expanding `tr (∑_{s∈S} toMat s)`, a summand `tr (iˢ P_a) = iˢ · [a = 0] · 2ⁿ` is nonzero only when
the string index is `0`, and the only such element of `S` is the identity `I`
(`eq_one_of_checkRowHom_eq_zero_of_negOne_notMem`, using `-I ∉ S`), contributing `tr I = 2ⁿ`. -/
theorem stabilizerSum_trace {S : Subgroup (PauliGroup n)} [Fintype S]
    (hS : PauliGroup.negOne n ∉ S) : (stabilizerSum S).trace = (2 : ℂ) ^ n := by
  rw [stabilizerSum_eq, Matrix.trace_sum, Finset.sum_eq_single_of_mem (1 : S) (Finset.mem_univ _)]
  · rw [OneMemClass.coe_one, PauliGroup.toMat_one,
      show (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) = pauliString 0 from
        pauliString_const_zero.symm, pauliString_trace, ite_eq_left rfl]
  · intro t _ hne
    rw [PauliGroup.toMat, Matrix.trace_smul, pauliString_trace, smul_eq_mul, ite_eq_right, mul_zero]
    intro h0
    exact hne (Subtype.ext ((PauliGroup.eq_one_of_checkRowHom_eq_zero_of_negOne_notMem hS t.2
      ((PauliGroup.checkRowHom_eq_zero_iff _).mpr h0)).trans (OneMemClass.coe_one S).symm))

/-- **The exact trace of the code projector.** For a genuine stabilizer (`-I ∉ S`),
`tr(codeProjector S) = |S|⁻¹ · 2ⁿ`, from `codeProjector S = |S|⁻¹ • stabilizerSum S` and
`tr(stabilizerSum S) = 2ⁿ` (`stabilizerSum_trace`). -/
theorem codeProjector_trace_eq {S : Subgroup (PauliGroup n)} [Fintype S]
    (hS : PauliGroup.negOne n ∉ S) :
    (codeProjector S).trace = (↑(Fintype.card ↥S))⁻¹ * 2 ^ n := by
  rw [codeProjector, Matrix.trace_smul, smul_eq_mul, stabilizerSum_trace hS]

/-- **The trace of the code projector is nonzero** for a genuine stabilizer (`-I ∉ S`):
`tr P = |S|⁻¹ · 2ⁿ ≠ 0`. -/
theorem codeProjector_trace_ne_zero {S : Subgroup (PauliGroup n)} [Fintype S]
    (hS : PauliGroup.negOne n ∉ S) : (codeProjector S).trace ≠ 0 := by
  rw [codeProjector_trace_eq hS]
  exact mul_ne_zero (inv_ne_zero (card_stabilizer_ne_zero S)) (pow_ne_zero n two_ne_zero)

/-- **The trace of the code projector is real** (`P` is Hermitian, so `star (tr P) = tr Pᴴ = tr P`).
Used to show the trace-defined KL coefficient matrix is Hermitian. -/
theorem star_trace_codeProjector {S : Subgroup (PauliGroup n)} [Fintype S] :
    star (codeProjector S).trace = (codeProjector S).trace := by
  rw [← Matrix.trace_conjTranspose, codeProjector_isHermitian.eq]

/-! ### The code projector conjugated by a phase multiple of a stabilizer element -/

/-- **Conjugation by a phase multiple of a stabilizer element.** If `p` has the same underlying
Pauli string as some `s' ∈ S` (`p.idx = s'.idx`), then `toMat p = iˢ • toMat s'` with
`s = p.phase − s'.phase`, and `s'` is absorbed by `P` (`codeProjector_conj_toMat_eq_self`), so
`P (toMat p) P = iˢ • P`. This is the phase-multiple case that the restricted Theorem 10.8 condition
(`∉ N(S) − S`) does not cover. -/
theorem codeProjector_conj_toMat_phaseStab {S : Subgroup (PauliGroup n)} [Fintype S]
    {p s' : PauliGroup n} (hs' : s' ∈ S) (hidx : p.idx = s'.idx) :
    codeProjector S * p.toMat * codeProjector S
      = zmod4Pow (p.phase - s'.phase) • codeProjector S := by
  have htoMat : p.toMat = zmod4Pow (p.phase - s'.phase) • s'.toMat := by
    simp only [PauliGroup.toMat, hidx, smul_smul, ← zmod4Pow_add, sub_add_cancel]
  rw [htoMat, mul_smul_comm, smul_mul_assoc, codeProjector_conj_toMat_eq_self hs']

/-- **For an operator of weight below the distance, `P (toMat p) P` is a scalar multiple of `P`.**
Either `p ∉ N(S)` — then `p` anticommutes with a stabilizer element and `P (toMat p) P = 0`
(`codeProjector_conj_toMat`) — or `p ∈ N(S)`, and since `weight p < distance`, `p` cannot be a
nontrivial logical operator, so it is a phase multiple of some `s' ∈ S`
(`stabilizerCodeDistance_le_weight`, contrapositive) and `codeProjector_conj_toMat_phaseStab`
applies. This is what lets the Knill–Laflamme coefficient be read off as a scalar. -/
theorem exists_codeProjector_conj_smul_of_weight_lt {S : Subgroup (PauliGroup n)} [Fintype S]
    {p : PauliGroup n} (hw : (p.weight : ℕ∞) < stabilizerCodeDistance S) :
    ∃ c : ℂ, codeProjector S * p.toMat * codeProjector S = c • codeProjector S := by
  by_cases hN : p ∈ Subgroup.normalizer S
  · obtain ⟨s', hs', hidx⟩ := exists_mem_idx_eq_of_mem_normalizer_of_weight_lt hN hw
    exact ⟨zmod4Pow (p.phase - s'.phase), codeProjector_conj_toMat_phaseStab hs' hidx⟩
  · refine ⟨0, ?_⟩
    have hpS : p ∉ (S : Set (PauliGroup n)) := fun h =>
      hN (Subgroup.le_normalizer (SetLike.mem_coe.mp h))
    rw [codeProjector_conj_toMat (fun h => hN h.1), Set.indicator_of_notMem hpS, zero_smul]

/-- **A below-distance normalizer element conjugates the code projector to a unit-phase multiple.**
For `p ∈ N(S)` with `weight p < distance`, `P (toMat p) P = c • P` for a scalar `c` of **unit
modulus** `‖c‖ = 1`. This sharpens `exists_codeProjector_conj_smul_of_weight_lt` (which yields
*some* scalar, possibly `0`, for a `p` outside `N(S)`): since `p ∈ N(S)` and `weight p < distance`,
`p` is a phase multiple `iˢ·s'` of a stabilizer element
(`exists_mem_idx_eq_of_mem_normalizer_of_weight_lt`), so `c = iˢ = zmod4Pow (p.phase − s'.phase)` is
a fourth root of unity
(`codeProjector_conj_toMat_phaseStab`, `zmod4Pow_norm`). The unit modulus certifies that the
sandwiched conjugation neither scales nor annihilates `P` — used, e.g., in the
entanglement-distillation recovery `stabilizerDistilledVec_error_corrected` (N&C Ex 12.34(b)). -/
theorem exists_norm_one_codeProjector_conj_toMat_of_mem_normalizer_of_weight_lt
    {S : Subgroup (PauliGroup n)} [Fintype S] {p : PauliGroup n}
    (hN : p ∈ Subgroup.normalizer S) (hw : (p.weight : ℕ∞) < stabilizerCodeDistance S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ codeProjector S * p.toMat * codeProjector S = c • codeProjector S := by
  obtain ⟨s', hs', hidx⟩ := exists_mem_idx_eq_of_mem_normalizer_of_weight_lt hN hw
  exact ⟨zmod4Pow (p.phase - s'.phase), zmod4Pow_norm _,
    codeProjector_conj_toMat_phaseStab hs' hidx⟩

/-! ### The trace-defined Knill–Laflamme coefficient matrix -/

/-- The **Knill–Laflamme coefficient matrix** for an error family `E : ι → Gₙ`, defined via the
trace: `αⱼₖ = (tr P)⁻¹ · tr (P Eⱼ† Eₖ P)`. When `P Eⱼ† Eₖ P = c • P` (as holds below the distance),
taking traces forces `c = αⱼₖ`, so this recovers the scalar; defining it by the trace makes it
manifestly Hermitian without a case split. Unlike the `0/1`-valued `stabilizerKLCoeff` of Theorem
10.8, this is genuinely `ℂ`-valued (the phase multiples contribute `iˢ`). -/
noncomputable def stabilizerTraceKLCoeff {ι : Type*} (S : Subgroup (PauliGroup n)) [Fintype S]
    (E : ι → PauliGroup n) : Matrix ι ι ℂ :=
  fun j k => (codeProjector S).trace⁻¹ *
    (codeProjector S * ((E j).toMat)ᴴ * (E k).toMat * codeProjector S).trace

/-- **The trace KL coefficient matrix is Hermitian.** `αₖⱼ = (tr P)⁻¹ · tr (P Eₖ† Eⱼ P)`, and
`(P Eₖ† Eⱼ P)ᴴ = P Eⱼ† Eₖ P` (`P` Hermitian), so `tr (P Eₖ† Eⱼ P) = star (tr (P Eⱼ† Eₖ P))`; with
`tr P` real (`star_trace_codeProjector`) this gives `αₖⱼ = star αⱼₖ`. -/
theorem stabilizerTraceKLCoeff_isHermitian {ι : Type*} (S : Subgroup (PauliGroup n)) [Fintype S]
    (E : ι → PauliGroup n) : (stabilizerTraceKLCoeff S E).IsHermitian := by
  ext j k
  rw [Matrix.conjTranspose_apply, stabilizerTraceKLCoeff, stabilizerTraceKLCoeff, star_mul',
    star_inv₀, star_trace_codeProjector, ← Matrix.trace_conjTranspose]
  refine congrArg (fun M => (codeProjector S).trace⁻¹ * Matrix.trace M) ?_
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    codeProjector_isHermitian.eq, mul_assoc]

/-! ### The Knill–Laflamme conditions and correctability below the distance -/

/-- **The Knill–Laflamme conditions for an error family whose pairwise products have weight below
the distance** (matrix level). For `E : ι → Gₙ` with `weight (Eⱼ⁻¹ Eₖ) < distance` for all `j, k`,
the
code projector satisfies `P Eⱼ† Eₖ P = αⱼₖ • P` with `α = stabilizerTraceKLCoeff S E`. Proof:
`Eⱼ† Eₖ = toMat (Eⱼ⁻¹ Eₖ)` (`toMat_inv`/`toMat_mul`), whose conjugation by `P` is *some* scalar
multiple `c • P` (`exists_codeProjector_conj_smul_of_weight_lt`); taking traces gives
`c = (tr P)⁻¹ · tr (P Eⱼ† Eₖ P) = αⱼₖ` (using `tr P ≠ 0`). -/
theorem codeProjector_satisfiesKL_of_weight_lt {ι : Type*} {S : Subgroup (PauliGroup n)} [Fintype S]
    (hS : PauliGroup.negOne n ∉ S) (E : ι → PauliGroup n)
    (hE : ∀ j k, (((E j)⁻¹ * E k).weight : ℕ∞) < stabilizerCodeDistance S) (j k : ι) :
    codeProjector S * ((E j).toMat)ᴴ * (E k).toMat * codeProjector S
      = stabilizerTraceKLCoeff S E j k • codeProjector S := by
  have hprod : ((E j).toMat)ᴴ * (E k).toMat = ((E j)⁻¹ * E k).toMat := by
    rw [PauliGroup.toMat_mul, PauliGroup.toMat_inv]
  obtain ⟨c, hc⟩ := exists_codeProjector_conj_smul_of_weight_lt (hE j k)
  have hPP : codeProjector S * ((E j).toMat)ᴴ * (E k).toMat * codeProjector S
      = c • codeProjector S := by
    rw [mul_assoc (codeProjector S) _ _, hprod, hc]
  rw [hPP]
  refine congrArg (· • _) ?_
  rw [stabilizerTraceKLCoeff, hPP, Matrix.trace_smul, smul_eq_mul,
    mul_comm c (codeProjector S).trace, ← mul_assoc,
    inv_mul_cancel₀ (codeProjector_trace_ne_zero hS), one_mul]

/-- The Knill–Laflamme conditions of `codeProjector_satisfiesKL_of_weight_lt`, transported through
the `*`-algebra isomorphism `Matrix.toEuclideanCLM` into the predicate
`ContinuousLinearMap.SatisfiesKLConditions` of Theorem 10.1 (same transport as
`codeProjector_satisfiesKLConditions`). -/
theorem codeProjector_satisfiesKLConditions_of_weight_lt {ι : Type*} {S : Subgroup (PauliGroup n)}
    [Fintype S] (hS : PauliGroup.negOne n ∉ S) (E : ι → PauliGroup n)
    (hE : ∀ j k, (((E j)⁻¹ * E k).weight : ℕ∞) < stabilizerCodeDistance S) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).SatisfiesKLConditions
      (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (E i).toMat)
      (stabilizerTraceKLCoeff S E) := by
  intro i j
  have hadj := (Matrix.toEuclideanCLM_conjTranspose_eq_adjoint (𝕜 := ℂ) (n := Fin n → Fin 2)
    (E i).toMat).symm
  rw [hadj]
  simp only [← ContinuousLinearMap.mul_def, ← map_mul, ← map_smul]
  refine congrArg _ ?_
  rw [← codeProjector_satisfiesKL_of_weight_lt hS E hE i j]
  noncomm_ring

/-- **Correctability below the distance** — the reusable core of Exercise 10.45. For a stabilizer
`S` (`-I ∉ S`) and a finite Pauli error family `E : ι → Gₙ` such that `weight (Eⱼ⁻¹ Eₖ) < distance`
for all `j, k`, the family `{Eⱼ}` is a **correctable set of errors** for `C(S)`: there is a
trace-preserving recovery `R` (`∑ₒ Rₒ† Rₒ = 1`) correcting `{Eⱼ}`. Obtained by feeding the Hermitian
`α` (`stabilizerTraceKLCoeff_isHermitian`) and the KL conditions
(`codeProjector_satisfiesKLConditions_of_weight_lt`) — together with `P` self-adjoint, idempotent,
and nonzero — into `ContinuousLinearMap.corrects_of_satisfiesKLConditions`. (This is also N&C's "a
code with distance `≥ 2t + 1` corrects arbitrary errors on any `t` qubits", via `weight ≤ 2t < d`.)
-/
theorem codeProjector_isCorrectableErrorSet_of_weight_lt {ι : Type} [Fintype ι]
    {S : Subgroup (PauliGroup n)} [Fintype S] (hS : PauliGroup.negOne n ∉ S) (E : ι → PauliGroup n)
    (hE : ∀ j k, (((E j)⁻¹ * E k).weight : ℕ∞) < stabilizerCodeDistance S) :
    ∃ (κ : Type) (_ : Fintype κ)
      (R : κ → EuclideanSpace ℂ (Fin n → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin n → Fin 2)),
      (∑ o, (ContinuousLinearMap.adjoint (R o)).comp (R o) = 1) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).Corrects
        (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (E i).toMat) R :=
  ContinuousLinearMap.corrects_of_satisfiesKLConditions
    isSelfAdjoint_toEuclideanCLM_codeProjector toEuclideanCLM_codeProjector_comp_self
    (toEuclideanCLM_codeProjector_ne_zero hS)
    (stabilizerTraceKLCoeff_isHermitian S E)
    (codeProjector_satisfiesKLConditions_of_weight_lt hS E hE)

/-! ### Exercise 10.45: correcting located errors -/

/-- **Nielsen & Chuang, Exercise 10.45** (correcting located errors). Let `S` be a stabilizer
(`-I ∉ S`) for a code `C(S)`, and let `L` be a *known* set of affected qubit positions whose size is
strictly below the code distance, `|L| < stabilizerCodeDistance S` (for an `[n, k, d]` code and the
exercise's `|L| = d − 1` this is `d − 1 < d`). Then the family of **all Pauli errors supported on
`L`** (elements of `Gₙ` acting as the identity off `L`) is a **correctable set of errors** for
`C(S)`: there is a trace-preserving recovery `R` (`∑ₒ Rₒ† Rₒ = 1`) correcting every such error.

Proof: for two `L`-supported errors `p, q`, the product `p⁻¹ q` is again supported on `L`
(`weight_inv_mul_le_of_support_subset`), so `weight (p⁻¹ q) ≤ |L| < stabilizerCodeDistance S`; hence
`codeProjector_isCorrectableErrorSet_of_weight_lt` applies. -/
theorem locatedPauliErrors_isCorrectableErrorSet
    {S : Subgroup (PauliGroup n)} [Fintype S] (hS : PauliGroup.negOne n ∉ S)
    (L : Finset (Fin n)) (hL : (L.card : ℕ∞) < stabilizerCodeDistance S) :
    ∃ (κ : Type) (_ : Fintype κ)
      (R : κ → EuclideanSpace ℂ (Fin n → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin n → Fin 2)),
      (∑ o, (ContinuousLinearMap.adjoint (R o)).comp (R o) = 1) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).Corrects
        (fun i : {p : PauliGroup n // pauliStringSupport p.idx ⊆ L} =>
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (i.val).toMat) R := by
  refine codeProjector_isCorrectableErrorSet_of_weight_lt hS
    (Subtype.val : {p : PauliGroup n // pauliStringSupport p.idx ⊆ L} → PauliGroup n) ?_
  intro i j
  exact lt_of_le_of_lt (by exact_mod_cast weight_inv_mul_le_of_support_subset i.2 j.2) hL

/-- **Exercise 10.45 for an `[n, k, d]` code.** The specialization to the textbook's parameters: a
stabilizer `S` (`-I ∉ S`) whose code has distance at least `d`
(`(d : ℕ∞) ≤ stabilizerCodeDistance S`, in particular any `[n, k, d]` code), and a known set `L` of
affected qubits with fewer than `d` of them (`|L| < d`, i.e. at most `d − 1` — the exercise's
hypothesis), admits a recovery correcting all Pauli errors located on `L`. Immediate from
`locatedPauliErrors_isCorrectableErrorSet` since `|L| < d ≤ stabilizerCodeDistance S`. -/
theorem locatedPauliErrors_isCorrectableErrorSet_of_dist_ge
    {S : Subgroup (PauliGroup n)} [Fintype S] (hS : PauliGroup.negOne n ∉ S)
    {d : ℕ} (hdist : (d : ℕ∞) ≤ stabilizerCodeDistance S)
    (L : Finset (Fin n)) (hL : L.card < d) :
    ∃ (κ : Type) (_ : Fintype κ)
      (R : κ → EuclideanSpace ℂ (Fin n → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin n → Fin 2)),
      (∑ o, (ContinuousLinearMap.adjoint (R o)).comp (R o) = 1) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).Corrects
        (fun i : {p : PauliGroup n // pauliStringSupport p.idx ⊆ L} =>
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (i.val).toMat) R :=
  locatedPauliErrors_isCorrectableErrorSet hS L
    (lt_of_lt_of_le (by exact_mod_cast hL) hdist)

end AxQM.Concrete
