/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Joint entropy, conditional entropy, and mutual information

For finite types `ι`, `κ` and a joint distribution `p : ι × κ → ℝ` (a probability mass function
of a pair of random variables `(X, Y)` when `p ≥ 0` and `∑ p = 1`), this file develops the
elementary information-theoretic quantities built on `Real.entropy`:

* the **marginals** `Real.marginalFst p x = ∑ y, p (x, y)` and
  `Real.marginalSnd p y = ∑ x, p (x, y)` (the distributions of `X` and of `Y`);
* the **conditional entropy** `Real.condEntropy p = H(X, Y) - H(Y)` (`= H(X | Y)`);
* the **mutual information** `Real.mutualInfo p = H(X) + H(Y) - H(X, Y)` (`= H(X : Y)`);
* the **product of the marginals** `Real.indepProd p (x, y) = marginalFst p x * marginalSnd p y`
  (the joint distribution `X`, `Y` would have if they were independent).

The joint entropy `H(X, Y)` itself is just `Real.entropy p` for `p : ι × κ → ℝ`.

## Main results

These are the classical (Shannon) half of Nielsen & Chuang, Theorem 11.3 ("Basic properties of
Shannon entropy"). Entropy is measured in nats (natural log), as in `Real.entropy`.

* `Real.entropy_swap`, `Real.mutualInfo_swap` — **symmetry** (part 1): `H(X, Y) = H(Y, X)` and
  `H(X : Y) = H(Y : X)`.
* `Real.mutualInfo_eq_relativeEntropy` — the key identity `H(X : Y) = D(p ‖ p_X ⊗ p_Y)`, valid for
  any `p ≥ 0`. Every subadditivity statement below is an instance of relative-entropy
  non-negativity through this identity.
* `Real.relativeEntropy_indepProd_eq` — the same identity spelled out (Nielsen–Chuang Exercise
  11.5): `D(p ‖ p_X ⊗ p_Y) = H(X) + H(Y) - H(X, Y)`.
* `Real.entropy_le_add_marginal` — **subadditivity** (part 4): `H(X, Y) ≤ H(X) + H(Y)`.
* `Real.mutualInfo_nonneg` — `H(X : Y) ≥ 0` (part 5).
* `Real.condEntropy_le_marginalFst` — **conditioning reduces entropy** at the mutual-information
  level: `H(X | Y) ≤ H(X)` (part 5).
* `Real.mutualInfo_eq_zero_iff`, `Real.entropy_add_marginal_eq_iff` — the **equality condition** for
  parts 4/5: subadditivity is saturated iff `X` and `Y` are independent (`p = p_X ⊗ p_Y`).
* `Real.entropy_marginalFst_le`, `Real.entropy_marginalSnd_le` — **the joint entropy dominates each
  marginal entropy** (part 3): `H(X) ≤ H(X, Y)` and `H(Y) ≤ H(X, Y)`.
* `Real.condEntropy_nonneg` — **non-negativity of the conditional entropy** (part 2):
  `H(X | Y) ≥ 0`, whence `Real.mutualInfo_le_marginalSnd` gives `H(X : Y) ≤ H(Y)`.
* `Real.entropy_marginalFst_eq_iff_sndDeterminedByFst`,
  `Real.mutualInfo_eq_marginalSnd_iff_sndDeterminedByFst` — the **equality condition** for parts
  2/3: `H(X) = H(X, Y)` (equivalently `H(X : Y) = H(Y)`) iff `Y` is a deterministic function of `X`
  (`Real.SndDeterminedByFst`).

`H(Y | X)` **as a relative entropy** (Nielsen & Chuang, Exercise 11.7), with `X` the conditioning
(first) variable so that `H(Y | X) = entropy p − entropy (marginalFst p)`:

* `Real.entropy_sub_entropy_marginalFst_eq_relativeEntropy` — **the expression**:
  `H(Y | X) = D(p ‖ Real.condEntropyRef p)`, where `condEntropyRef p (x, y) = p(x, y)² / p_X(x)`.
* `Real.relativeEntropy_condEntropyRef_nonneg` — **the deduction** `H(Y | X) ≥ 0`, from
  nonnegativity of the relative entropy against the sub-normalized `condEntropyRef p`.
* `Real.relativeEntropy_condEntropyRef_eq_zero_iff` — **the equality condition**: `H(Y | X) = 0` iff
  `Y` is a deterministic function of `X` (`Real.SndDeterminedByFst`).

For a tripartite distribution `p : ι × κ × μ → ℝ` of `(X, Y, Z)` (read as `ι × (κ × μ)`, with `Y`
the shared middle variable), the remaining parts are developed on the same definitions, via the
conditional-independence reconstruction `Real.condIndepProd p (x, y, z) = p_{XY}(x, y)·p_{YZ}(y, z)
/ p_Y(y)`:

* `Real.entropy_triple_add_marginal_le` — **strong subadditivity** (part 6; also N&C Exercise 11.6):
  `H(X, Y, Z) + H(Y) ≤ H(X, Y) + H(Y, Z)`.
* `Real.entropy_triple_add_marginal_eq_iff` — the **equality condition** for part 6: strong
  subadditivity is saturated iff `Z → Y → X` forms a Markov chain (`Real.IsMarkovChain`,
  equivalently `X` and `Z` conditionally independent given `Y`).
* `Real.entropy_conditioning_le` — **conditioning reduces entropy** (part 7):
  `H(X | Y, Z) ≤ H(X | Y)`.

The namespace `Real.XorMutualInfo` records a concrete counterexample to the naive subadditivity of
the mutual information (Nielsen & Chuang, Exercise 11.8): for `X, Y` independent uniform bits and
`Z = X ⊕ Y`, `Real.XorMutualInfo.mutualInfo_xorDist_not_subadditive` shows
`H(X, Y : Z) ≰ H(X : Z) + H(Y : Z)`.
-/

@[expose] public section

namespace Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Marginals -/

/-- The first marginal `p_X(x) = ∑_y p(x, y)` of a joint distribution `p : ι × κ → ℝ`. -/
noncomputable def marginalFst (p : ι × κ → ℝ) : ι → ℝ := fun x ↦ ∑ y, p (x, y)

/-- The second marginal `p_Y(y) = ∑_x p(x, y)` of a joint distribution `p : ι × κ → ℝ`. -/
noncomputable def marginalSnd (p : ι × κ → ℝ) : κ → ℝ := fun y ↦ ∑ x, p (x, y)

omit [Fintype ι] in
theorem marginalFst_apply (p : ι × κ → ℝ) (x : ι) : marginalFst p x = ∑ y, p (x, y) := rfl

omit [Fintype κ] in
theorem marginalSnd_apply (p : ι × κ → ℝ) (y : κ) : marginalSnd p y = ∑ x, p (x, y) := rfl

omit [Fintype ι] in
theorem marginalFst_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (x : ι) : 0 ≤ marginalFst p x :=
  Finset.sum_nonneg fun y _ ↦ hp (x, y)

omit [Fintype κ] in
theorem marginalSnd_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (y : κ) : 0 ≤ marginalSnd p y :=
  Finset.sum_nonneg fun x _ ↦ hp (x, y)

omit [Fintype ι] in
/-- Each cell is dominated by its first marginal: `p(x, y) ≤ p_X(x)`. -/
theorem le_marginalFst {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (x : ι) (y : κ) :
    p (x, y) ≤ marginalFst p x :=
  Finset.single_le_sum (fun i _ ↦ hp (x, i)) (Finset.mem_univ y)

omit [Fintype κ] in
/-- Each cell is dominated by its second marginal: `p(x, y) ≤ p_Y(y)`. -/
theorem le_marginalSnd {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (x : ι) (y : κ) :
    p (x, y) ≤ marginalSnd p y :=
  Finset.single_le_sum (fun i _ ↦ hp (i, y)) (Finset.mem_univ x)

/-- The first marginal has the same total mass as the joint distribution. -/
theorem sum_marginalFst (p : ι × κ → ℝ) : ∑ x, marginalFst p x = ∑ q, p q := by
  simp only [marginalFst_apply, ← Fintype.sum_prod_type]

/-- The second marginal has the same total mass as the joint distribution. -/
theorem sum_marginalSnd (p : ι × κ → ℝ) : ∑ y, marginalSnd p y = ∑ q, p q := by
  simp only [marginalSnd_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

omit [Fintype ι] in
/-- A first marginal vanishes exactly when its whole fibre does (under nonnegativity). -/
theorem marginalFst_eq_zero_iff {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (x : ι) :
    marginalFst p x = 0 ↔ ∀ y, p (x, y) = 0 := by
  rw [marginalFst_apply, Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦ hp (x, y)]
  simp

/-! ### Definitions of the derived quantities -/

/-- The conditional entropy `H(X | Y) = H(X, Y) - H(Y)` of a joint distribution. -/
noncomputable def condEntropy (p : ι × κ → ℝ) : ℝ := entropy p - entropy (marginalSnd p)

theorem condEntropy_eq (p : ι × κ → ℝ) : condEntropy p = entropy p - entropy (marginalSnd p) := rfl

/-- The mutual information `H(X : Y) = H(X) + H(Y) - H(X, Y)` of a joint distribution. -/
noncomputable def mutualInfo (p : ι × κ → ℝ) : ℝ :=
  entropy (marginalFst p) + entropy (marginalSnd p) - entropy p

theorem mutualInfo_eq (p : ι × κ → ℝ) :
    mutualInfo p = entropy (marginalFst p) + entropy (marginalSnd p) - entropy p := rfl

omit [Fintype ι] in
/-- The first marginal `p ↦ (x ↦ ∑ y, p (x, y))` is a continuous function of the joint law. -/
theorem continuous_marginalFst : Continuous (marginalFst : (ι × κ → ℝ) → (ι → ℝ)) := by
  unfold marginalFst
  exact continuous_pi fun x => continuous_finsetSum _ fun y _ => continuous_apply (x, y)

omit [Fintype κ] in
/-- The second marginal `p ↦ (y ↦ ∑ x, p (x, y))` is a continuous function of the joint law. -/
theorem continuous_marginalSnd : Continuous (marginalSnd : (ι × κ → ℝ) → (κ → ℝ)) := by
  unfold marginalSnd
  exact continuous_pi fun y => continuous_finsetSum _ fun x _ => continuous_apply (x, y)

/-- The mutual information `p ↦ H(X : Y)` is a continuous function of the joint distribution. -/
theorem continuous_mutualInfo : Continuous (mutualInfo : (ι × κ → ℝ) → ℝ) := by
  unfold mutualInfo
  exact ((continuous_entropy.comp continuous_marginalFst).add
    (continuous_entropy.comp continuous_marginalSnd)).sub continuous_entropy

/-- The product of the marginals `(p_X ⊗ p_Y)(x, y) = p_X(x) · p_Y(y)`: the joint distribution the
pair would have under independence. -/
noncomputable def indepProd (p : ι × κ → ℝ) : ι × κ → ℝ :=
  fun q ↦ marginalFst p q.1 * marginalSnd p q.2

theorem indepProd_apply (p : ι × κ → ℝ) (q : ι × κ) :
    indepProd p q = marginalFst p q.1 * marginalSnd p q.2 := rfl

theorem indepProd_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (q : ι × κ) : 0 ≤ indepProd p q :=
  mul_nonneg (marginalFst_nonneg hp q.1) (marginalSnd_nonneg hp q.2)

/-- The product of the marginals has total mass `(∑ p)²`. -/
theorem sum_indepProd (p : ι × κ → ℝ) :
    ∑ q, indepProd p q = (∑ x, marginalFst p x) * ∑ y, marginalSnd p y := by
  simp only [indepProd_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]

/-- The support of the joint distribution lies in the support of the product of its marginals. -/
theorem p_eq_zero_of_indepProd_eq_zero {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    ∀ q, indepProd p q = 0 → p q = 0 := by
  rintro ⟨x, y⟩ h
  rw [indepProd_apply, mul_eq_zero] at h
  rcases h with h1 | h2
  · exact (marginalFst_eq_zero_iff hp x).mp h1 y
  · rw [marginalSnd_apply, Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hp (i, y)] at h2
    exact h2 x (Finset.mem_univ _)

/-! ### Symmetry (N&C Theorem 11.3, part 1) -/

/-- **Symmetry of the joint entropy**: `H(X, Y) = H(Y, X)`. -/
theorem entropy_swap (p : ι × κ → ℝ) : entropy (fun q : κ × ι ↦ p (q.2, q.1)) = entropy p := by
  simp only [entropy_eq]
  exact (Equiv.prodComm κ ι).sum_comp fun r ↦ negMulLog (p r)

omit [Fintype κ] in
theorem marginalFst_swap (p : ι × κ → ℝ) :
    marginalFst (fun q : κ × ι ↦ p (q.2, q.1)) = marginalSnd p := by
  funext y; simp only [marginalFst_apply, marginalSnd_apply]

omit [Fintype ι] in
theorem marginalSnd_swap (p : ι × κ → ℝ) :
    marginalSnd (fun q : κ × ι ↦ p (q.2, q.1)) = marginalFst p := by
  funext x; simp only [marginalFst_apply, marginalSnd_apply]

/-- **Symmetry of the mutual information**: `H(X : Y) = H(Y : X)`. -/
theorem mutualInfo_swap (p : ι × κ → ℝ) :
    mutualInfo (fun q : κ × ι ↦ p (q.2, q.1)) = mutualInfo p := by
  rw [mutualInfo_eq, mutualInfo_eq, marginalFst_swap, marginalSnd_swap, entropy_swap]; ring

/-! ### Mutual information as a relative entropy -/

/-- Collapsing the joint sum `∑_{x,y} p(x, y) log p_X(x)` onto the first marginal. -/
theorem sum_p_mul_log_marginalFst (p : ι × κ → ℝ) :
    ∑ q : ι × κ, p q * Real.log (marginalFst p q.1) =
      ∑ x, marginalFst p x * Real.log (marginalFst p x) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [← Finset.sum_mul, ← marginalFst_apply]

/-- Collapsing the joint sum `∑_{x,y} p(x, y) log p_Y(y)` onto the second marginal. -/
theorem sum_p_mul_log_marginalSnd (p : ι × κ → ℝ) :
    ∑ q : ι × κ, p q * Real.log (marginalSnd p q.2) =
      ∑ y, marginalSnd p y * Real.log (marginalSnd p y) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  simp only [← Finset.sum_mul, ← marginalSnd_apply]

/-- Splitting of the cross term `∑ p log (p_X ⊗ p_Y)` into the two marginal self-cross terms,
using that on the support of `p` both marginal factors are strictly positive. -/
theorem sum_p_mul_log_indepProd {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    ∑ q, p q * Real.log (indepProd p q) =
      (∑ x, marginalFst p x * Real.log (marginalFst p x)) +
        ∑ y, marginalSnd p y * Real.log (marginalSnd p y) := by
  have hsplit : ∀ q : ι × κ, p q * Real.log (indepProd p q) =
      p q * Real.log (marginalFst p q.1) + p q * Real.log (marginalSnd p q.2) := by
    rintro ⟨x, y⟩
    rcases eq_or_lt_of_le (hp (x, y)) with h0 | h0
    · simp [← h0]
    · have hm1 : (0 : ℝ) < marginalFst p x := lt_of_lt_of_le h0 (le_marginalFst hp x y)
      have hm2 : (0 : ℝ) < marginalSnd p y := lt_of_lt_of_le h0 (le_marginalSnd hp x y)
      simp only [indepProd_apply, Real.log_mul hm1.ne' hm2.ne', mul_add]
  calc ∑ q, p q * Real.log (indepProd p q)
      = ∑ q : ι × κ, (p q * Real.log (marginalFst p q.1) + p q * Real.log (marginalSnd p q.2)) :=
        Finset.sum_congr rfl fun q _ ↦ hsplit q
    _ = (∑ q, p q * Real.log (marginalFst p q.1)) + ∑ q, p q * Real.log (marginalSnd p q.2) :=
        Finset.sum_add_distrib
    _ = _ := by rw [sum_p_mul_log_marginalFst, sum_p_mul_log_marginalSnd]

/-- **Mutual information is a relative entropy**: `H(X : Y) = D(p ‖ p_X ⊗ p_Y)`. Valid for any
nonnegative `p` (no normalization needed). This is the identity through which N&C proves
subadditivity: `H(X : Y) = H(p(x, y) ‖ p(x) p(y))`. -/
theorem mutualInfo_eq_relativeEntropy {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    mutualInfo p = relativeEntropy p (indepProd p) := by
  rw [relativeEntropy_eq_sub, mutualInfo_eq, entropy_eq_neg_sum_mul_log p,
    entropy_eq_neg_sum_mul_log (marginalFst p), entropy_eq_neg_sum_mul_log (marginalSnd p),
    sum_p_mul_log_indepProd hp]
  ring

/-- **Subadditivity via a relative-entropy identity** (Nielsen & Chuang, Exercise 11.5): the
relative entropy of the joint distribution `p` against the product of its marginals is the excess
of the summed marginal entropies over the joint entropy,
`D(p ‖ p_X ⊗ p_Y) = H(X) + H(Y) - H(X, Y)`. This is precisely the identity N&C Exercise 11.5 asks
to establish, `H(p(x, y) ‖ p(x) p(y)) = H(p(x)) + H(p(y)) - H(p(x, y))`, written out through the
definition of the mutual information (`mutualInfo_eq_relativeEntropy` reads the same equality with
the right-hand side packaged as `mutualInfo p`). Valid for any nonnegative `p` (no normalization is
needed for the identity itself). Combined with non-negativity of the relative entropy it yields
subadditivity `H(X, Y) ≤ H(X) + H(Y)` (`entropy_le_add_marginal`), with equality iff `X` and `Y`
are independent (`entropy_add_marginal_eq_iff`) — the "deduce" half of the exercise. -/
theorem relativeEntropy_indepProd_eq {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    relativeEntropy p (indepProd p)
      = entropy (marginalFst p) + entropy (marginalSnd p) - entropy p :=
  (mutualInfo_eq_relativeEntropy hp).symm.trans (mutualInfo_eq p)

/-- **Mixing identity for the mutual information.** Given weights `p : ι → ℝ` and a family of
conditional distributions `q : ι → κ → ℝ` (each `q x` a probability distribution, `∑ y, q x y = 1`),
the mutual information of the joint distribution `(x, y) ↦ p x * q x y` equals the `p`-average
of the relative entropies of the conditionals `q x` against the average distribution
`q̄ y = ∑ x', p x' * q x' y`:
`H(X : Y) = ∑ x, p x * D(q x ‖ q̄)`.
This is the classical counterpart of the Holevo χ identity for the von Neumann entropy
(`∑ᵢ pᵢ S(ρᵢ ‖ μ) = S(μ) − ∑ᵢ pᵢ S(ρᵢ)`): reading `q x = p(· | x)` as the channel output for input
`x` and `q̄ = p_Y` as the average output, it says the mutual information between input and output
is the mean relative entropy of the conditional outputs to the average output. Only nonnegativity
of `p` and `q` and normalization of each `q x` are needed. -/
theorem mutualInfo_eq_sum_mul_relativeEntropy
    (p : ι → ℝ) (q : ι → κ → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x y, 0 ≤ q x y) (hq1 : ∀ x, ∑ y, q x y = 1) :
    mutualInfo (fun xy : ι × κ ↦ p xy.1 * q xy.1 xy.2)
      = ∑ x, p x * relativeEntropy (q x) (fun y ↦ ∑ x', p x' * q x' y) := by
  set joint : ι × κ → ℝ := fun xy ↦ p xy.1 * q xy.1 xy.2 with hjoint
  set qbar : κ → ℝ := fun y ↦ ∑ x', p x' * q x' y with hqbar
  have hjoint_nonneg : ∀ z, 0 ≤ joint z := fun z ↦ mul_nonneg (hp z.1) (hq z.1 z.2)
  have hmF : marginalFst joint = p := by
    funext x; rw [marginalFst_apply]; simp only [hjoint]
    rw [← Finset.mul_sum, hq1 x, mul_one]
  have hmS : marginalSnd joint = qbar := rfl
  have hindep : indepProd joint = fun z ↦ p z.1 * qbar z.2 := by
    funext z; rw [indepProd_apply, hmF, hmS]
  rw [mutualInfo_eq_relativeEntropy hjoint_nonneg, relativeEntropy_eq, hindep,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [relativeEntropy_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  simp only [hjoint]
  rcases eq_or_lt_of_le (hp x) with hx | hx
  · simp [← hx]
  · rcases eq_or_lt_of_le (hq x y) with hxy | hxy
    · rw [← hxy]; ring
    · have hqbar_pos : 0 < qbar y :=
        lt_of_lt_of_le (mul_pos hx hxy)
          (Finset.single_le_sum (f := fun x' ↦ p x' * q x' y)
            (fun i _ ↦ mul_nonneg (hp i) (hq i y)) (Finset.mem_univ x))
      rw [Real.log_mul hx.ne' hxy.ne', Real.log_mul hx.ne' hqbar_pos.ne']
      ring

/-- **Mutual information of a conditional joint as output entropy minus average conditional
entropy.** Given weights `p : ι → ℝ` and a family of conditional distributions `q : ι → κ → ℝ`
(each `q x` a probability distribution, `∑ y, q x y = 1`), the mutual information of the joint
distribution `(x, y) ↦ p x * q x y` is the entropy of the average output distribution
`q̄ y = ∑ x, p x * q x y` minus the `p`-weighted average of the conditional-output entropies:

`H(X : Y) = H(Y) − ∑ x, p x · H(q x)`   (equivalently `H(Y) − H(Y | X)`).

This is the entropy-difference companion of `mutualInfo_eq_sum_mul_relativeEntropy` (which writes
the same mutual information as `∑ x, p x · D(q x ‖ q̄)`), obtained from the definition
`mutualInfo p = H(p_X) + H(p_Y) − H(X, Y)` by evaluating the marginals of the conditional joint
(`p_X = p` since each `q x` normalizes, `p_Y = q̄`) and the classical chain rule `entropy_prod_mul`
(`H(X, Y) = H(X) + ∑ x, p x · H(q x)`). Only normalization of each `q x` is needed. It is the
classical counterpart of the Holevo χ ↔ mutual-information identity `χ = S(μ) − ∑ᵢ pᵢ S(ρᵢ)` under
the measure-and-record channel (Nielsen & Chuang Problem 12.1). -/
theorem mutualInfo_prod_conditional (p : ι → ℝ) (q : ι → κ → ℝ) (hq : ∀ x, ∑ y, q x y = 1) :
    mutualInfo (fun xy : ι × κ ↦ p xy.1 * q xy.1 xy.2)
      = entropy (fun y ↦ ∑ x, p x * q x y) - ∑ x, p x * entropy (q x) := by
  rw [mutualInfo_eq]
  have hmF : marginalFst (fun xy : ι × κ ↦ p xy.1 * q xy.1 xy.2) = p := by
    funext x; rw [marginalFst_apply]; dsimp only; rw [← Finset.mul_sum, hq x, mul_one]
  have hmS : marginalSnd (fun xy : ι × κ ↦ p xy.1 * q xy.1 xy.2) = fun y ↦ ∑ x, p x * q x y := rfl
  rw [hmF, hmS, entropy_prod_mul hq]
  ring

/-! ### Subadditivity and mutual-information non-negativity (N&C Theorem 11.3, parts 4 & 5) -/

/-- The mass condition feeding the relative-entropy comparison of `p` with `p_X ⊗ p_Y`. -/
private theorem sum_p_eq_sum_indepProd {p : ι × κ → ℝ} (hsum : ∑ q, p q = 1) :
    ∑ q, p q = ∑ q, indepProd p q := by
  rw [sum_indepProd, sum_marginalFst, sum_marginalSnd, hsum, mul_one]

/-- **Subadditivity of the Shannon entropy** (N&C Theorem 11.3, part 4): the joint entropy of a
probability distribution is at most the sum of its marginal entropies,
`H(X, Y) ≤ H(X) + H(Y)`. -/
theorem entropy_le_add_marginal {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    entropy p ≤ entropy (marginalFst p) + entropy (marginalSnd p) := by
  have h := relativeEntropy_nonneg_of_support_subset hp (indepProd_nonneg hp)
    (p_eq_zero_of_indepProd_eq_zero hp) (sum_p_eq_sum_indepProd hsum)
  rw [← mutualInfo_eq_relativeEntropy hp, mutualInfo_eq] at h
  linarith

/-- **Non-negativity of the mutual information** (N&C Theorem 11.3, part 5): `H(X : Y) ≥ 0`. -/
theorem mutualInfo_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    0 ≤ mutualInfo p := by
  rw [mutualInfo_eq_relativeEntropy hp]
  exact relativeEntropy_nonneg_of_support_subset hp (indepProd_nonneg hp)
    (p_eq_zero_of_indepProd_eq_zero hp) (sum_p_eq_sum_indepProd hsum)

/-- **Conditioning reduces entropy** (N&C Theorem 11.3, part 5): `H(X | Y) ≤ H(X)`. -/
theorem condEntropy_le_marginalFst {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    condEntropy p ≤ entropy (marginalFst p) := by
  have h := mutualInfo_nonneg hp hsum
  rw [mutualInfo_eq] at h
  rw [condEntropy_eq]
  linarith

/-- **Equality condition for subadditivity / mutual information** (N&C Theorem 11.3, parts 4 & 5):
`H(X : Y) = 0` iff `X` and `Y` are independent, i.e. `p = p_X ⊗ p_Y`. -/
theorem mutualInfo_eq_zero_iff {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    mutualInfo p = 0 ↔ p = indepProd p := by
  rw [mutualInfo_eq_relativeEntropy hp]
  exact relativeEntropy_eq_zero_iff hp (indepProd_nonneg hp)
    (p_eq_zero_of_indepProd_eq_zero hp) (sum_p_eq_sum_indepProd hsum)

/-- Subadditivity `H(X, Y) ≤ H(X) + H(Y)` is saturated iff `X` and `Y` are independent. -/
theorem entropy_add_marginal_eq_iff {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    entropy (marginalFst p) + entropy (marginalSnd p) = entropy p ↔ p = indepProd p := by
  rw [← mutualInfo_eq_zero_iff hp hsum, mutualInfo_eq, sub_eq_zero]

/-! ### Joint entropy dominates a marginal (N&C Theorem 11.3, parts 2 & 3) -/

/-- The gap between the joint entropy and the first marginal entropy, written out as a sum:
`H(X, Y) - H(X) = ∑_{x,y} p(x, y) (log p_X(x) - log p(x, y))`. A pure algebraic identity (valid for
any `p`); it is the workhorse behind both the part-3 inequality and its equality condition, and is
reused by the strong-subadditivity development. -/
theorem entropy_sub_entropy_marginalFst_eq_sum (p : ι × κ → ℝ) :
    entropy p - entropy (marginalFst p)
      = ∑ q, p q * (Real.log (marginalFst p q.1) - Real.log (p q)) := by
  rw [entropy_eq_neg_sum_mul_log p, entropy_eq_neg_sum_mul_log (marginalFst p),
    ← sum_p_mul_log_marginalFst]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]; ring

omit [Fintype ι] in
/-- Each summand of `entropy_sub_entropy_marginalFst_eq_sum` is nonnegative: since
`p(x, y) ≤ p_X(x)` (`le_marginalFst`) the logarithmic difference is nonnegative, and the
`p(x, y) = 0` cells vanish. -/
theorem entropy_sub_entropy_marginalFst_summand_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (q : ι × κ) : 0 ≤ p q * (Real.log (marginalFst p q.1) - Real.log (p q)) := by
  rcases eq_or_lt_of_le (hp q) with h0 | h0
  · rw [← h0]; simp
  · exact mul_nonneg h0.le (sub_nonneg.mpr (Real.log_le_log h0 (le_marginalFst hp q.1 q.2)))

/-- **The joint entropy dominates the first marginal entropy** (N&C Theorem 11.3, part 3):
`H(X) ≤ H(X, Y)`. Equivalently the conditional entropy `H(Y | X) = H(X, Y) - H(X)` is nonnegative
(part 2). This is N&C's argument: the difference is a sum of nonnegative terms
(`entropy_sub_entropy_marginalFst_eq_sum` + `entropy_sub_entropy_marginalFst_summand_nonneg`). -/
theorem entropy_marginalFst_le {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    entropy (marginalFst p) ≤ entropy p := by
  rw [← sub_nonneg, entropy_sub_entropy_marginalFst_eq_sum]
  exact Finset.sum_nonneg fun q _ ↦ entropy_sub_entropy_marginalFst_summand_nonneg hp q

/-- **The joint entropy dominates the second marginal entropy** (N&C Theorem 11.3, part 3):
`H(Y) ≤ H(X, Y)`, obtained from `entropy_marginalFst_le` by symmetry. -/
theorem entropy_marginalSnd_le {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    entropy (marginalSnd p) ≤ entropy p := by
  have hp' : ∀ q : κ × ι, 0 ≤ (fun q : κ × ι ↦ p (q.2, q.1)) q := fun q ↦ hp (q.2, q.1)
  calc entropy (marginalSnd p)
      = entropy (marginalFst fun q : κ × ι ↦ p (q.2, q.1)) := by rw [marginalFst_swap]
    _ ≤ entropy (fun q : κ × ι ↦ p (q.2, q.1)) := entropy_marginalFst_le hp'
    _ = entropy p := entropy_swap p

/-- **Non-negativity of the conditional entropy** (N&C Theorem 11.3, part 2; N&C Exercise 11.7):
`H(X | Y) = H(X, Y) - H(Y) ≥ 0`. Learning `Y` cannot leave a negative amount of uncertainty about
`X`. -/
theorem condEntropy_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) : 0 ≤ condEntropy p := by
  rw [condEntropy_eq, sub_nonneg]
  exact entropy_marginalSnd_le hp

/-- **`H(X : Y) ≤ H(Y)`** (N&C Theorem 11.3, part 2): the mutual information never exceeds a
marginal entropy. Together with `mutualInfo_nonneg` this pins `0 ≤ H(X : Y) ≤ H(Y)`. -/
theorem mutualInfo_le_marginalSnd {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    mutualInfo p ≤ entropy (marginalSnd p) := by
  have := entropy_marginalFst_le hp
  rw [mutualInfo_eq]; linarith

/-- The second coordinate `Y` is a **deterministic function of the first** `X`: there is `f : ι → κ`
with `y = f x` on every cell of positive probability. This is the finite-support rendering of
Nielsen & Chuang's "`Y = f(X)`", the equality condition for parts 2 and 3 of Theorem 11.3. The name
is directional; the symmetric notion (`X` a function of `Y`) would be `FstDeterminedBySnd`. -/
def SndDeterminedByFst (p : ι × κ → ℝ) : Prop := ∃ f : ι → κ, ∀ x y, p (x, y) ≠ 0 → y = f x

/-- **Equality condition for `H(X) ≤ H(X, Y)`** (N&C Theorem 11.3, parts 2 & 3): the joint entropy
equals the first marginal entropy iff `Y` is a deterministic function of `X`. Equality forces every
term of the nonnegative sum `∑ p(x, y)(log p_X(x) - log p(x, y))` to vanish, i.e. each cell of
positive probability carries the whole fibre mass `p(x, y) = p_X(x)`; a fibre can then support only
a single `y`, which defines `f`. -/
theorem entropy_marginalFst_eq_iff_sndDeterminedByFst {p : ι × κ → ℝ} [Nonempty κ]
    (hp : ∀ q, 0 ≤ p q) :
    entropy (marginalFst p) = entropy p ↔ SndDeterminedByFst p := by
  classical
  rw [eq_comm, ← sub_eq_zero, entropy_sub_entropy_marginalFst_eq_sum,
    Finset.sum_eq_zero_iff_of_nonneg fun q _ ↦ entropy_sub_entropy_marginalFst_summand_nonneg hp q]
  constructor
  · intro hz
    -- Each cell is either empty or carries the whole fibre mass.
    have hcell : ∀ x y, p (x, y) = 0 ∨ p (x, y) = marginalFst p x := by
      intro x y
      rcases eq_or_lt_of_le (hp (x, y)) with h0 | h0
      · exact Or.inl h0.symm
      · refine Or.inr ?_
        have h : p (x, y) * (Real.log (marginalFst p x) - Real.log (p (x, y))) = 0 :=
          hz (x, y) (Finset.mem_univ _)
        have hlog : Real.log (marginalFst p x) = Real.log (p (x, y)) :=
          sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h0.ne')
        have hmpos : 0 < marginalFst p x := lt_of_lt_of_le h0 (le_marginalFst hp x y)
        exact (Real.log_injOn_pos (Set.mem_Ioi.mpr hmpos) (Set.mem_Ioi.mpr h0) hlog).symm
    -- Hence each `X`-fibre supports at most one `y`.
    have huniq : ∀ x y₁ y₂, p (x, y₁) ≠ 0 → p (x, y₂) ≠ 0 → y₁ = y₂ := by
      intro x y₁ y₂ h1 h2
      by_contra hne
      have he1 : p (x, y₁) = marginalFst p x := (hcell x y₁).resolve_left h1
      have hzero : ∑ y ∈ (Finset.univ : Finset κ).erase y₁, p (x, y) = 0 := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ y₁), ← marginalFst_apply, ← he1, sub_self]
      have hle : p (x, y₂) ≤ 0 := by
        rw [← hzero]
        exact Finset.single_le_sum (fun y _ ↦ hp (x, y))
          (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ y₂⟩)
      exact h2 (le_antisymm hle (hp (x, y₂)))
    refine ⟨fun x ↦ if h : ∃ y, p (x, y) ≠ 0 then h.choose else Classical.arbitrary κ, ?_⟩
    intro x y hxy
    have hex : ∃ y, p (x, y) ≠ 0 := ⟨y, hxy⟩
    simp only [dite_eq_left hex]
    exact huniq x y hex.choose hxy hex.choose_spec
  · rintro ⟨f, hf⟩ q -
    obtain ⟨x, y⟩ := q
    change p (x, y) * (Real.log (marginalFst p x) - Real.log (p (x, y))) = 0
    rcases eq_or_lt_of_le (hp (x, y)) with h0 | h0
    · rw [← h0]; simp
    · have hyfx : y = f x := hf x y h0.ne'
      have hmarg : marginalFst p x = p (x, y) := by
        rw [marginalFst_apply]
        refine Finset.sum_eq_single y (fun y' _ hy' ↦ ?_)
          (fun hnot ↦ absurd (Finset.mem_univ y) hnot)
        by_contra hpy'
        exact hy' ((hf x y' hpy').trans hyfx.symm)
      rw [hmarg]; ring

/-- **Equality condition for `H(X : Y) ≤ H(Y)`** (N&C Theorem 11.3, part 2): the mutual information
equals the second marginal entropy iff `Y` is a deterministic function of `X`. -/
theorem mutualInfo_eq_marginalSnd_iff_sndDeterminedByFst {p : ι × κ → ℝ} [Nonempty κ]
    (hp : ∀ q, 0 ≤ p q) :
    mutualInfo p = entropy (marginalSnd p) ↔ SndDeterminedByFst p := by
  rw [mutualInfo_eq, ← entropy_marginalFst_eq_iff_sndDeterminedByFst hp]
  constructor <;> intro h <;> linarith

/-! ### Conditional entropy as a relative entropy (N&C Exercise 11.7)

Nielsen & Chuang, Exercise 11.7 asks to express the conditional entropy `H(Y | X)` as a relative
entropy between two probability distributions, and to *deduce* `H(Y | X) ≥ 0` and its equality
condition from that expression — the conditional-entropy counterpart of Exercise 11.5, which reads
subadditivity off the mutual-information relative entropy `H(X : Y) = D(p ‖ p_X ⊗ p_Y)`.

Writing `p : ι × κ → ℝ` for the joint distribution of `(X, Y)` with `X` the *conditioning* (first)
variable and `Y` the (second) variable, the conditional entropy is
`H(Y | X) = H(X, Y) − H(X) = entropy p − entropy (marginalFst p)`. The relative-entropy expression
is `H(Y | X) = D(p ‖ q)` for the reference `q(x, y) = p(x, y)² / p_X(x) = p_X(x) · p(y | x)²`
(`condEntropyRef`): on the support of `p`, `log q = 2 log p − log p_X`, so `D(p ‖ q)` collapses to
`∑ p(x, y) (log p_X(x) − log p(x, y))`, which is exactly `entropy_sub_entropy_marginalFst_eq_sum`.

Unlike the mutual-information reference `p_X ⊗ p_Y`, this `q` is only a *sub*-probability
distribution — `∑ q ≤ ∑ p` (`sum_condEntropyRef_le`), from `∑_y p(x, y)² ≤ (∑_y p(x, y))² = p_X(x)²`
— so `H(Y | X) ≥ 0` is nonnegativity of the relative entropy against a sub-normalized reference
(`relativeEntropy_nonneg_of_sum_le`), and the equality condition `H(Y | X) = 0` iff `Y` is a
deterministic function of `X` is read off the same expression via the part-2/3 characterization
`entropy_marginalFst_eq_iff_sndDeterminedByFst`. -/

/-- The **reference distribution** realizing the conditional entropy `H(Y | X)` as a relative
entropy (Nielsen & Chuang, Exercise 11.7): `condEntropyRef p (x, y) = p(x, y)² / p_X(x)`, equal to
`p_X(x) · p(y | x)²` on the support of `p`. It is a *sub*-probability distribution
(`∑ ≤ ∑ p`, `sum_condEntropyRef_le`), and
`H(Y | X) = D(p ‖ condEntropyRef p)` (`entropy_sub_entropy_marginalFst_eq_relativeEntropy`). -/
noncomputable def condEntropyRef (p : ι × κ → ℝ) : ι × κ → ℝ :=
  fun q ↦ p q ^ 2 / marginalFst p q.1

omit [Fintype ι] in
theorem condEntropyRef_apply (p : ι × κ → ℝ) (x : ι) (y : κ) :
    condEntropyRef p (x, y) = p (x, y) ^ 2 / marginalFst p x := rfl

omit [Fintype ι] in
theorem condEntropyRef_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) (q : ι × κ) :
    0 ≤ condEntropyRef p q :=
  div_nonneg (sq_nonneg _) (marginalFst_nonneg hp q.1)

omit [Fintype ι] in
/-- The support of the joint distribution lies in the support of `condEntropyRef p`: if the
reference vanishes at `(x, y)` then so does `p` — its numerator `p(x, y)²` vanishes, or its
denominator `p_X(x)` does (and then the whole `x`-fibre of `p` vanishes). -/
theorem p_eq_zero_of_condEntropyRef_eq_zero {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    ∀ q, condEntropyRef p q = 0 → p q = 0 := by
  rintro ⟨x, y⟩ h
  rw [condEntropyRef_apply, div_eq_zero_iff] at h
  rcases h with h1 | h2
  · exact sq_eq_zero_iff.mp h1
  · exact (marginalFst_eq_zero_iff hp x).mp h2 y

/-- `condEntropyRef p` is a **sub-probability distribution**: `∑ condEntropyRef p ≤ ∑ p`. Per
`X`-fibre `∑_y p(x, y)² / p_X(x) ≤ p_X(x)`, since `∑_y p(x, y)² ≤ (∑_y p(x, y))² = p_X(x)²`
(`Finset.sum_sq_le_sq_sum_of_nonneg`); summing over `x` gives `∑_x p_X(x) = ∑ p`. -/
theorem sum_condEntropyRef_le {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    ∑ q, condEntropyRef p q ≤ ∑ q, p q := by
  rw [← sum_marginalFst p, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  have hsum_sq : ∑ y, p (x, y) ^ 2 ≤ marginalFst p x ^ 2 := by
    rw [marginalFst_apply]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun y _ ↦ hp (x, y)
  have hcref : ∑ y, condEntropyRef p (x, y) = (∑ y, p (x, y) ^ 2) / marginalFst p x := by
    simp only [condEntropyRef_apply, div_eq_mul_inv, ← Finset.sum_mul]
  rw [hcref]
  rcases eq_or_lt_of_le (marginalFst_nonneg hp x) with hx | hx
  · simp [← hx]
  · rw [div_le_iff₀ hx, ← pow_two]; exact hsum_sq

/-- **Conditional entropy as a relative entropy** (Nielsen & Chuang, Exercise 11.7): with `X` the
conditioning variable, the conditional entropy `H(Y | X) = H(X, Y) − H(X) = entropy p −
entropy (marginalFst p)` equals the classical relative entropy of the joint distribution against
`condEntropyRef p`, i.e. `H(Y | X) = D(p ‖ q)` with `q(x, y) = p(x, y)² / p_X(x)`. On the support
of `p` the reference log splits as `log q = 2 log p − log p_X`, so `D(p ‖ q)` reduces to
`∑ p(x, y)(log p_X(x) − log p(x, y))` — precisely `entropy_sub_entropy_marginalFst_eq_sum`. This is
the expression the exercise asks for, from which the two deductions below follow. -/
theorem entropy_sub_entropy_marginalFst_eq_relativeEntropy {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    entropy p - entropy (marginalFst p) = relativeEntropy p (condEntropyRef p) := by
  rw [entropy_sub_entropy_marginalFst_eq_sum, relativeEntropy_eq]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rcases eq_or_lt_of_le (hp q) with h0 | h0
  · simp [← h0, condEntropyRef]
  · have hmpos : 0 < marginalFst p q.1 := lt_of_lt_of_le h0 (le_marginalFst hp q.1 q.2)
    simp only [condEntropyRef]
    rw [Real.log_div (pow_ne_zero 2 h0.ne') hmpos.ne', Real.log_pow]
    push_cast; ring

/-- **Non-negativity of the conditional entropy, via the relative-entropy expression** (Nielsen &
Chuang, Exercise 11.7): the relative entropy of the joint distribution against `condEntropyRef p`
is nonnegative, so — through `entropy_sub_entropy_marginalFst_eq_relativeEntropy` — the conditional
entropy `H(Y | X) = entropy p − entropy (marginalFst p) ≥ 0`. This is the exercise's deduction:
`condEntropyRef p` is a sub-probability distribution (`sum_condEntropyRef_le`) whose support
contains that of `p`, so nonnegativity is the sub-normalized Gibbs inequality
(`relativeEntropy_nonneg_of_sum_le`) — the same inequality as the direct `entropy_marginalFst_le`,
reached here by the relative-entropy route. -/
theorem relativeEntropy_condEntropyRef_nonneg {p : ι × κ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    0 ≤ relativeEntropy p (condEntropyRef p) :=
  relativeEntropy_nonneg_of_sum_le hp (condEntropyRef_nonneg hp)
    (p_eq_zero_of_condEntropyRef_eq_zero hp) (sum_condEntropyRef_le hp)

/-- **Equality condition for the conditional entropy** (Nielsen & Chuang, Exercise 11.7): the
relative-entropy expression `D(p ‖ condEntropyRef p) = H(Y | X)` vanishes if and only if `Y` is a
deterministic function of `X` (`SndDeterminedByFst p`). Read off the expression
(`entropy_sub_entropy_marginalFst_eq_relativeEntropy`) through the part-2/3 characterization
`entropy_marginalFst_eq_iff_sndDeterminedByFst`; equivalently, `H(Y | X) = 0` exactly when
conditioning on `X` removes all uncertainty about `Y`. -/
theorem relativeEntropy_condEntropyRef_eq_zero_iff {p : ι × κ → ℝ} [Nonempty κ]
    (hp : ∀ q, 0 ≤ p q) :
    relativeEntropy p (condEntropyRef p) = 0 ↔ SndDeterminedByFst p := by
  rw [← entropy_sub_entropy_marginalFst_eq_relativeEntropy hp, sub_eq_zero, eq_comm,
    entropy_marginalFst_eq_iff_sndDeterminedByFst hp]

/-! ### Strong subadditivity and conditioning-reduces-entropy (N&C Theorem 11.3, parts 6 & 7)

For a tripartite distribution `p : ι × κ × μ → ℝ` of `(X, Y, Z)` — with `Y` the shared middle
variable — this section proves N&C Theorem 11.3(6), **strong subadditivity**
`H(X, Y, Z) + H(Y) ≤ H(X, Y) + H(Y, Z)`, and its rearrangement Theorem 11.3(7),
**conditioning reduces entropy** `H(X | Y, Z) ≤ H(X | Y)`.

Reading `ι × κ × μ` as `ι × (κ × μ)` lets the joint `(Y, Z)`-marginal and the entropy `H(X | Y, Z)`
reuse the two-variable `marginalSnd`/`condEntropy`; only the `(X, Y)`-marginal (`marginalFstMid`,
summing out `Z`) and the middle `Y`-marginal (`marginalMid`) are new. Following N&C's proof of
subadditivity, the inequality is non-negativity of the relative entropy of `p` against the
reconstruction `condIndepProd p (x, y, z) = p(x, y) · p(y, z) / p(y)` — the distribution `(X, Y, Z)`
would have if `X` and `Z` were conditionally independent given `Y`. -/

variable {μ : Type*} [Fintype μ]

/-- The joint `(X, Y)`-marginal `p_{XY}(x, y) = ∑_z p(x, y, z)` of a tripartite distribution,
obtained by summing out the third variable `Z`. -/
noncomputable def marginalFstMid (p : ι × κ × μ → ℝ) : ι × κ → ℝ := fun q ↦ ∑ z, p (q.1, q.2, z)

/-- The middle `Y`-marginal `p_Y(y) = ∑_{x,z} p(x, y, z)` of a tripartite distribution, defined as
the first marginal of the `(Y, Z)`-marginal `marginalSnd p` so that it inherits its two-variable
API. -/
noncomputable def marginalMid (p : ι × κ × μ → ℝ) : κ → ℝ := marginalFst (marginalSnd p)

omit [Fintype ι] [Fintype κ] in
theorem marginalFstMid_apply (p : ι × κ × μ → ℝ) (x : ι) (y : κ) :
    marginalFstMid p (x, y) = ∑ z, p (x, y, z) := rfl

omit [Fintype κ] in
theorem marginalMid_apply (p : ι × κ × μ → ℝ) (y : κ) :
    marginalMid p y = ∑ z, marginalSnd p (y, z) := rfl

omit [Fintype ι] [Fintype κ] in
theorem marginalFstMid_nonneg {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) (w : ι × κ) :
    0 ≤ marginalFstMid p w :=
  Finset.sum_nonneg fun z _ ↦ hp (w.1, w.2, z)

omit [Fintype κ] in
theorem marginalMid_nonneg {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) (y : κ) :
    0 ≤ marginalMid p y :=
  marginalFst_nonneg (fun w ↦ marginalSnd_nonneg hp w) y

omit [Fintype ι] [Fintype κ] in
/-- Each cell is dominated by its `(X, Y)`-marginal: `p(x, y, z) ≤ p_{XY}(x, y)`. -/
theorem le_marginalFstMid {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) (x : ι) (y : κ) (z : μ) :
    p (x, y, z) ≤ marginalFstMid p (x, y) :=
  Finset.single_le_sum (fun z' _ ↦ hp (x, y, z')) (Finset.mem_univ z)

omit [Fintype κ] in
/-- The `(X, Y)`-marginal summed over `X` recovers the middle marginal:
`∑_x p_{XY}(x, y) = p_Y(y)`. -/
theorem sum_marginalFstMid (p : ι × κ × μ → ℝ) (y : κ) :
    ∑ x, marginalFstMid p (x, y) = marginalMid p y := by
  rw [marginalMid_apply]
  simp only [marginalFstMid_apply, marginalSnd_apply]
  rw [Finset.sum_comm]

omit [Fintype κ] in
/-- The second marginal of the `(X, Y)`-marginal is the middle marginal:
`(p_{XY})_Y = p_Y`. This is the bridge realizing `H(X | Y) = condEntropy p_{XY}`. -/
theorem marginalSnd_marginalFstMid (p : ι × κ × μ → ℝ) :
    marginalSnd (marginalFstMid p) = marginalMid p := by
  funext y; rw [marginalSnd_apply, sum_marginalFstMid]

/-- Reordering a sum over the triple to bring the middle variable outermost:
`∑_{x,y,z} f = ∑_y ∑_x ∑_z f`. -/
theorem sum_triple_comm (f : ι × κ × μ → ℝ) : ∑ q, f q = ∑ y, ∑ x, ∑ z, f (x, y, z) := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Collapsing a sum whose summand depends only on the second coordinate:
`∑_{(x,y)} p(x, y) g(y) = ∑_y p_Y(y) g(y)`. Generalizes `sum_p_mul_log_marginalSnd`. -/
theorem sum_mul_of_snd (p : ι × κ → ℝ) (g : κ → ℝ) :
    ∑ q : ι × κ, p q * g q.2 = ∑ y, marginalSnd p y * g y := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  simp only [← Finset.sum_mul, ← marginalSnd_apply]

/-- Collapsing a tripartite sum whose summand depends only on `(X, Y)` onto the `(X, Y)`-marginal:
`∑_{x,y,z} p(x, y, z) g(x, y) = ∑_{(x,y)} p_{XY}(x, y) g(x, y)`. -/
theorem sum_mul_of_fstMid (p : ι × κ × μ → ℝ) (g : ι × κ → ℝ) :
    ∑ q : ι × κ × μ, p q * g (q.1, q.2.1) = ∑ w : ι × κ, marginalFstMid p w * g w := by
  rw [Fintype.sum_prod_type (f := fun w : ι × κ ↦ marginalFstMid p w * g w)]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  simp only [← Finset.sum_mul, ← marginalFstMid_apply]

/-- Collapsing `∑_{x,y,z} p(x, y, z) log p_Y(y)` onto the middle marginal, via `sum_mul_of_snd`
(collapse `X`) followed by the two-variable `sum_p_mul_log_marginalFst` on `marginalSnd p`
(collapse `Z`). -/
theorem sum_p_mul_log_marginalMid (p : ι × κ × μ → ℝ) :
    ∑ q, p q * Real.log (marginalMid p q.2.1) =
      ∑ y, marginalMid p y * Real.log (marginalMid p y) := by
  rw [sum_mul_of_snd p fun w : κ × μ ↦ Real.log (marginalMid p w.1)]
  exact sum_p_mul_log_marginalFst (marginalSnd p)

/-- The reconstruction `condIndepProd p (x, y, z) = p_{XY}(x, y) · p_{YZ}(y, z) / p_Y(y)`: the joint
distribution `(X, Y, Z)` would have if `X` and `Z` were conditionally independent given `Y` (the
`Z → Y → X` Markov reconstruction). Strong subadditivity is `D(p ‖ condIndepProd p) ≥ 0`. -/
noncomputable def condIndepProd (p : ι × κ × μ → ℝ) : ι × κ × μ → ℝ :=
  fun q ↦ marginalFstMid p (q.1, q.2.1) * marginalSnd p q.2 / marginalMid p q.2.1

omit [Fintype κ] in
theorem condIndepProd_nonneg {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) (q : ι × κ × μ) :
    0 ≤ condIndepProd p q :=
  div_nonneg (mul_nonneg (marginalFstMid_nonneg hp _) (marginalSnd_nonneg hp _))
    (marginalMid_nonneg hp _)

omit [Fintype κ] in
/-- The support of the joint distribution lies in the support of the reconstruction: any vanishing
factor of `condIndepProd p (x, y, z)` forces `p(x, y, z) = 0` by marginal-mass domination. -/
theorem p_eq_zero_of_condIndepProd_eq_zero {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    ∀ q, condIndepProd p q = 0 → p q = 0 := by
  rintro ⟨x, y, z⟩ h
  simp only [condIndepProd, div_eq_zero_iff, mul_eq_zero] at h
  rcases h with (h1 | h2) | h3
  · exact le_antisymm (h1 ▸ le_marginalFstMid hp x y z) (hp _)
  · exact le_antisymm (h2 ▸ le_marginalSnd hp x (y, z)) (hp _)
  · exact le_antisymm
      (h3 ▸ le_trans (le_marginalSnd hp x (y, z))
        (le_marginalFst (fun w ↦ marginalSnd_nonneg hp w) y z)) (hp _)

/-- The reconstruction is a probability distribution: `∑ condIndepProd p = 1`. Per middle-fibre
`y`, the reconstruction sums to `(∑_x p_{XY})(∑_z p_{YZ}) / p_Y = p_Y·p_Y / p_Y = p_Y` (the
`p_Y(y) = 0` fibre vanishes by `_ / 0 = 0`); summing over `y` gives `∑_y p_Y(y) = ∑ p = 1`. -/
theorem sum_condIndepProd {p : ι × κ × μ → ℝ} (hsum : ∑ q, p q = 1) :
    ∑ q, condIndepProd p q = 1 := by
  rw [sum_triple_comm]
  have key : ∀ y : κ, ∑ x, ∑ z, condIndepProd p (x, y, z) = marginalMid p y := by
    intro y
    rcases eq_or_ne (marginalMid p y) 0 with h | h
    · simp only [condIndepProd, h, div_zero, Finset.sum_const_zero]
    · have hx : ∑ x, marginalFstMid p (x, y) = marginalMid p y := sum_marginalFstMid p y
      have hz : ∑ z, marginalSnd p (y, z) = marginalMid p y := (marginalMid_apply p y).symm
      simp only [condIndepProd, div_eq_mul_inv, ← Finset.sum_mul]
      rw [← Finset.sum_mul_sum, hx, hz, mul_inv_cancel_right₀ h]
  rw [Finset.sum_congr rfl fun y _ ↦ key y]
  simp only [marginalMid]
  rw [sum_marginalFst, sum_marginalSnd]
  exact hsum

/-- The three-way log split feeding the relative-entropy identity: on the support of `p`, all three
marginal factors of `condIndepProd` are strictly positive, so
`log(p_{XY} · p_{YZ} / p_Y) = log p_{XY} + log p_{YZ} - log p_Y`; summing and collapsing each term
gives the marginal self-cross sums. -/
theorem sum_p_mul_log_condIndepProd {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    ∑ q, p q * Real.log (condIndepProd p q) =
      (∑ w : ι × κ, marginalFstMid p w * Real.log (marginalFstMid p w))
        + (∑ w : κ × μ, marginalSnd p w * Real.log (marginalSnd p w))
        - ∑ y, marginalMid p y * Real.log (marginalMid p y) := by
  have hsplit : ∀ q : ι × κ × μ, p q * Real.log (condIndepProd p q) =
      p q * Real.log (marginalFstMid p (q.1, q.2.1)) + p q * Real.log (marginalSnd p q.2)
        - p q * Real.log (marginalMid p q.2.1) := by
    rintro ⟨x, y, z⟩
    rcases eq_or_lt_of_le (hp (x, y, z)) with h0 | h0
    · simp [← h0]
    · have hxy : 0 < marginalFstMid p (x, y) := lt_of_lt_of_le h0 (le_marginalFstMid hp x y z)
      have hyz : 0 < marginalSnd p (y, z) := lt_of_lt_of_le h0 (le_marginalSnd hp x (y, z))
      have hy : 0 < marginalMid p y :=
        lt_of_lt_of_le hyz (le_marginalFst (fun w ↦ marginalSnd_nonneg hp w) y z)
      simp only [condIndepProd]
      rw [Real.log_div (mul_pos hxy hyz).ne' hy.ne', Real.log_mul hxy.ne' hyz.ne']
      ring
  calc ∑ q, p q * Real.log (condIndepProd p q)
      = ∑ q : ι × κ × μ, (p q * Real.log (marginalFstMid p (q.1, q.2.1))
            + p q * Real.log (marginalSnd p q.2) - p q * Real.log (marginalMid p q.2.1)) :=
        Finset.sum_congr rfl fun q _ ↦ hsplit q
    _ = (∑ q, p q * Real.log (marginalFstMid p (q.1, q.2.1)))
          + (∑ q, p q * Real.log (marginalSnd p q.2))
          - ∑ q, p q * Real.log (marginalMid p q.2.1) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
        rw [sum_mul_of_fstMid p fun w ↦ Real.log (marginalFstMid p w), sum_p_mul_log_marginalSnd p,
          sum_p_mul_log_marginalMid p]

/-- **The conditional mutual information as a relative entropy**:
`D(p ‖ condIndepProd p) = H(X, Y) + H(Y, Z) - H(Y) - H(X, Y, Z)`. This is the tripartite analogue
of `mutualInfo_eq_relativeEntropy`, and the identity through which strong subadditivity is an
instance of relative-entropy non-negativity. -/
theorem relativeEntropy_condIndepProd {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    relativeEntropy p (condIndepProd p)
      = entropy (marginalFstMid p) + entropy (marginalSnd p) - entropy (marginalMid p)
        - entropy p := by
  rw [relativeEntropy_eq_sub, sum_p_mul_log_condIndepProd hp, entropy_eq_neg_sum_mul_log p,
    entropy_eq_neg_sum_mul_log (marginalFstMid p), entropy_eq_neg_sum_mul_log (marginalSnd p),
    entropy_eq_neg_sum_mul_log (marginalMid p)]
  ring

/-- **Strong subadditivity of the Shannon entropy** (N&C Theorem 11.3, part 6; N&C Exercise 11.6):
for a tripartite probability distribution of `(X, Y, Z)`,
`H(X, Y, Z) + H(Y) ≤ H(X, Y) + H(Y, Z)`. Following N&C's subadditivity argument, this is
non-negativity of `D(p ‖ condIndepProd p)` (`relativeEntropy_nonneg_of_support_subset` through
`relativeEntropy_condIndepProd`): the reconstruction `condIndepProd p` is a probability distribution
(`sum_condIndepProd`) whose support contains that of `p`. -/
theorem entropy_triple_add_marginal_le {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hsum : ∑ q, p q = 1) :
    entropy p + entropy (marginalMid p) ≤ entropy (marginalFstMid p) + entropy (marginalSnd p) := by
  have hmass : ∑ q, p q = ∑ q, condIndepProd p q := by rw [hsum, sum_condIndepProd hsum]
  have h := relativeEntropy_nonneg_of_support_subset hp (condIndepProd_nonneg hp)
    (p_eq_zero_of_condIndepProd_eq_zero hp) hmass
  rw [relativeEntropy_condIndepProd hp] at h
  linarith

/-- **Conditioning reduces entropy** (N&C Theorem 11.3, part 7): `H(X | Y, Z) ≤ H(X | Y)`. Learning
`Z` in addition to `Y` cannot increase the average uncertainty about `X`. Reading `ι × κ × μ` as
`ι × (κ × μ)`, `condEntropy p = H(X, Y, Z) - H(Y, Z) = H(X | Y, Z)` and
`condEntropy (marginalFstMid p) = H(X, Y) - H(Y) = H(X | Y)`; the inequality is the rearrangement of
strong subadditivity (`entropy_triple_add_marginal_le`). -/
theorem entropy_conditioning_le {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) (hsum : ∑ q, p q = 1) :
    condEntropy p ≤ condEntropy (marginalFstMid p) := by
  rw [condEntropy_eq, condEntropy_eq, marginalSnd_marginalFstMid]
  linarith [entropy_triple_add_marginal_le hp hsum]

/-! ### Equality in strong subadditivity: the Markov-chain condition (N&C Theorem 11.3, part 6) -/

omit [Fintype κ] in
/-- Each cell of a tripartite distribution is dominated by its middle marginal:
`p(x, y, z) ≤ p_Y(y)`. -/
theorem le_marginalMid {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) (x : ι) (y : κ) (z : μ) :
    p (x, y, z) ≤ marginalMid p y :=
  le_trans (le_marginalSnd hp x (y, z)) (le_marginalFst (fun w ↦ marginalSnd_nonneg hp w) y z)

/-- `Z → Y → X` **forms a Markov chain** — equivalently, `X` and `Z` are conditionally independent
given `Y`. Written division-free as `p(x, y, z) · p_Y(y) = p_{XY}(x, y) · p_{YZ}(y, z)` for all
`x, y, z`: on the fibres with `p_Y(y) > 0` this rearranges to
`p(x, y, z) = p_{XY}(x, y)·p_{YZ}(y, z) / p_Y(y)`, i.e. `p(x, z | y) = p(x | y) p(z | y)`
(conditional independence); on the fibres with `p_Y(y) = 0` both sides vanish. The condition is
symmetric in `X` and `Z`, so it equally expresses the chain `X → Y → Z`. -/
def IsMarkovChain (p : ι × κ × μ → ℝ) : Prop :=
  ∀ x y z, p (x, y, z) * marginalMid p y = marginalFstMid p (x, y) * marginalSnd p (y, z)

omit [Fintype κ] in
/-- The Markov-chain condition is exactly agreement of `p` with its conditional-independence
reconstruction: `IsMarkovChain p ↔ p = condIndepProd p`. On the `p_Y(y) > 0` fibres it is the
cross-multiplication `p · p_Y = p_{XY} · p_{YZ} ↔ p = p_{XY}·p_{YZ}/p_Y`; on the `p_Y(y) = 0` fibres
`p`, `condIndepProd p`, and both sides of the factorization all vanish (by marginal-mass
domination). -/
theorem isMarkovChain_iff_eq_condIndepProd {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    IsMarkovChain p ↔ p = condIndepProd p := by
  constructor
  · intro h
    funext q
    obtain ⟨x, y, z⟩ := q
    rcases eq_or_ne (marginalMid p y) 0 with hy | hy
    · have hpxyz : p (x, y, z) = 0 := le_antisymm (hy ▸ le_marginalMid hp x y z) (hp _)
      simp only [condIndepProd, hy, div_zero, hpxyz]
    · simp only [condIndepProd]
      rw [eq_div_iff hy]
      exact h x y z
  · intro h x y z
    rcases eq_or_ne (marginalMid p y) 0 with hy | hy
    · have hyz : marginalSnd p (y, z) = 0 :=
        le_antisymm (hy ▸ le_marginalFst (fun w ↦ marginalSnd_nonneg hp w) y z)
          (marginalSnd_nonneg hp _)
      rw [hy, mul_zero, hyz, mul_zero]
    · have hpe := congrFun h (x, y, z)
      simp only [condIndepProd] at hpe
      rw [eq_div_iff hy] at hpe
      exact hpe

/-- **Equality in strong subadditivity** (N&C Theorem 11.3, part 6): the strong-subadditivity
inequality `entropy_triple_add_marginal_le` is saturated,
`H(X, Y, Z) + H(Y) = H(X, Y) + H(Y, Z)`, if and only if `Z → Y → X` forms a Markov chain
(`IsMarkovChain p`, i.e. `X` and `Z` conditionally independent given `Y`). This is the equality half
of relative-entropy non-negativity applied to the conditional-independence reconstruction:
`D(p ‖ condIndepProd p) = 0 ↔ p = condIndepProd p` (`relativeEntropy_eq_zero_iff` through the
identity `relativeEntropy_condIndepProd`), and `p = condIndepProd p` is precisely the Markov
condition (`isMarkovChain_iff_eq_condIndepProd`). -/
theorem entropy_triple_add_marginal_eq_iff {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hsum : ∑ q, p q = 1) :
    entropy p + entropy (marginalMid p)
        = entropy (marginalFstMid p) + entropy (marginalSnd p) ↔ IsMarkovChain p := by
  have hmass : ∑ q, p q = ∑ q, condIndepProd p q := by rw [hsum, sum_condIndepProd hsum]
  have hz := relativeEntropy_eq_zero_iff hp (condIndepProd_nonneg hp)
    (p_eq_zero_of_condIndepProd_eq_zero hp) hmass
  rw [relativeEntropy_condIndepProd hp] at hz
  rw [isMarkovChain_iff_eq_condIndepProd hp, ← hz]
  constructor <;> intro h <;> linarith

/-! ### Reversal symmetry of the Markov-chain condition (N&C Exercise 11.10) -/

/-- The joint distribution of the reversed triple `(Z, Y, X)`, obtained from the joint distribution
`p` of `(X, Y, Z)` by swapping the outer coordinates: `reverseTriple p (z, y, x) = p (x, y, z)`.
Reversing twice is the identity (`reverseTriple_reverseTriple`), so this is an involution on joint
distributions. -/
def reverseTriple (p : ι × κ × μ → ℝ) : μ × κ × ι → ℝ := fun q ↦ p (q.2.2, q.2.1, q.1)

omit [Fintype ι] [Fintype κ] [Fintype μ] in
/-- Value of the reversed distribution: `reverseTriple p (z, y, x) = p (x, y, z)`. -/
theorem reverseTriple_apply (p : ι × κ × μ → ℝ) (z : μ) (y : κ) (x : ι) :
    reverseTriple p (z, y, x) = p (x, y, z) := rfl

omit [Fintype ι] [Fintype κ] [Fintype μ] in
/-- Reversing the outer coordinates twice restores the original distribution:
`reverseTriple (reverseTriple p) = p`. -/
theorem reverseTriple_reverseTriple (p : ι × κ × μ → ℝ) :
    reverseTriple (reverseTriple p) = p := rfl

/-- Reversing the outer coordinates preserves total mass: `∑ reverseTriple p = ∑ p`, since it is a
reindexing of the sum along the outer-coordinate swap. -/
theorem sum_reverseTriple (p : ι × κ × μ → ℝ) : ∑ t, reverseTriple p t = ∑ t, p t :=
  Fintype.sum_equiv
    (Equiv.mk (fun t : μ × κ × ι => (t.2.2, t.2.1, t.1))
      (fun s : ι × κ × μ => (s.2.2, s.2.1, s.1)) (fun _ => rfl) (fun _ => rfl))
    _ _ (fun _ => rfl)

omit [Fintype κ] in
/-- The middle `Y`-marginal is invariant under reversal:
`(reverseTriple p)_Y = p_Y`. -/
theorem marginalMid_reverseTriple (p : ι × κ × μ → ℝ) :
    marginalMid (reverseTriple p) = marginalMid p := by
  funext y
  simp only [marginalMid_apply, marginalSnd_apply, reverseTriple]
  exact Finset.sum_comm

omit [Fintype κ] [Fintype μ] in
/-- The `(X, Y)`-marginal of the reversed triple is the `(Y, Z)`-marginal of the original:
`(reverseTriple p)_{ZY}(z, y) = p_{YZ}(y, z)`. -/
theorem marginalFstMid_reverseTriple (p : ι × κ × μ → ℝ) (z : μ) (y : κ) :
    marginalFstMid (reverseTriple p) (z, y) = marginalSnd p (y, z) := by
  simp only [marginalFstMid_apply, marginalSnd_apply, reverseTriple]

omit [Fintype ι] [Fintype κ] in
/-- The `(Y, Z)`-marginal of the reversed triple is the `(X, Y)`-marginal of the original:
`(reverseTriple p)_{YX}(y, x) = p_{XY}(x, y)`. -/
theorem marginalSnd_reverseTriple (p : ι × κ × μ → ℝ) (y : κ) (x : ι) :
    marginalSnd (reverseTriple p) (y, x) = marginalFstMid p (x, y) := by
  simp only [marginalSnd_apply, marginalFstMid_apply, reverseTriple]

omit [Fintype κ] in
/-- **N&C Exercise 11.10**: if `X → Y → Z` is a Markov chain, then so is `Z → Y → X`. Since
`IsMarkovChain p` is the division-free conditional independence `X ⊥ Z ∣ Y`, symmetric in `X` and
`Z`, reversing the outer variables of the joint distribution preserves it:
`IsMarkovChain p → IsMarkovChain (reverseTriple p)`. The proof rewrites each marginal of
`reverseTriple p` in terms of the corresponding marginal of `p` (`marginalMid` is invariant, while
the `(X, Y)`- and `(Y, Z)`-marginals swap) and applies the Markov condition for `p` up to
commutativity of the product. -/
theorem isMarkovChain_reverseTriple {p : ι × κ × μ → ℝ} (h : IsMarkovChain p) :
    IsMarkovChain (reverseTriple p) := by
  intro z y x
  rw [marginalMid_reverseTriple, marginalFstMid_reverseTriple, marginalSnd_reverseTriple,
    reverseTriple_apply]
  exact (h x y z).trans (mul_comm _ _)

omit [Fintype κ] in
/-- The Markov-chain condition is symmetric under reversing the outer variables: `Z → Y → X` is a
Markov chain if and only if `X → Y → Z` is. This is the two-way form of N&C Exercise 11.10,
immediate from `isMarkovChain_reverseTriple` and the involution `reverseTriple_reverseTriple`. -/
theorem isMarkovChain_reverseTriple_iff {p : ι × κ × μ → ℝ} :
    IsMarkovChain (reverseTriple p) ↔ IsMarkovChain p := by
  refine ⟨fun h ↦ ?_, isMarkovChain_reverseTriple⟩
  exact reverseTriple_reverseTriple p ▸ isMarkovChain_reverseTriple h

/-! ### Mutual information is not subadditive (Nielsen & Chuang, Exercise 11.8)

A concrete counterexample to the naive subadditivity `H(X, Y : Z) ≤ H(X : Z) + H(Y : Z)` of the
mutual information. Take `X` and `Y` to be independent uniform bits and `Z = X ⊕ Y` (addition
modulo `2`). Individually, each of `X` and `Y` is independent of `Z`, so `H(X : Z) = H(Y : Z) = 0`;
but the pair `(X, Y)` *determines* `Z`, so `H(X, Y : Z) = H(Z) = log 2 > 0`. Hence the combined
system carries strictly more information about `Z` than the parts do separately, and subadditivity
fails. All three joint distributions are read off the single joint distribution `xorDist` of the
triple `(X, Y, Z)`. -/

namespace XorMutualInfo

/-- The joint distribution of `(X, Y, Z)` for Nielsen & Chuang Exercise 11.8: `X` and `Y` are
independent uniform bits (values in `ZMod 2`) and `Z = X ⊕ Y` (addition modulo `2`). Each of the
four `(x, y)` combinations has probability `1/4` and forces `z = x + y`; the four inconsistent
triples have probability `0`. -/
noncomputable def xorDist : ZMod 2 × ZMod 2 × ZMod 2 → ℝ :=
  fun q => if q.2.2 = q.1 + q.2.1 then (1 / 4 : ℝ) else 0

/-- The joint distribution of the *pair* `(X, Y)` against `Z`, obtained from `xorDist` by regrouping
the triple as `((X, Y), Z)`. Its mutual information is `H(X, Y : Z)`. -/
noncomputable def xorDistPairZ : (ZMod 2 × ZMod 2) × ZMod 2 → ℝ :=
  fun q => xorDist (q.1.1, q.1.2, q.2)

/-- The joint distribution of `(X, Z)`, the marginal of `xorDist` obtained by summing out `Y`. Its
mutual information is `H(X : Z)`. -/
noncomputable def xorDistXZ : ZMod 2 × ZMod 2 → ℝ := fun q => ∑ y, xorDist (q.1, y, q.2)

/-- The joint distribution of `(Y, Z)`, the marginal of `xorDist` obtained by summing out `X`. Its
mutual information is `H(Y : Z)`. -/
noncomputable def xorDistYZ : ZMod 2 × ZMod 2 → ℝ := fun q => ∑ x, xorDist (x, q.1, q.2)

/-- `xorDist` is nonnegative (a genuine probability mass function, with `sum_xorDist`). -/
theorem xorDist_nonneg (q : ZMod 2 × ZMod 2 × ZMod 2) : 0 ≤ xorDist q := by
  unfold xorDist; split <;> norm_num

/-- The XOR-indicator sums to `1/4` over either summand: for fixed `a, c : ZMod 2` there is exactly
one `b` with `c = a + b` (namely `b = c - a`), so `∑ b, [c = a + b] · (1/4) = 1/4`. This is the
single cancellation fact underlying every marginal of `xorDist` (`z = x + y ↔ y = z - x`). -/
theorem sum_ite_add_eq (a c : ZMod 2) :
    (∑ b : ZMod 2, if c = a + b then (1 / 4 : ℝ) else 0) = 1 / 4 := by
  have hcond : ∀ b : ZMod 2, (c = a + b) ↔ (b = c - a) := fun b => by
    constructor <;> intro h <;> · rw [h]; ring
  simp only [hcond]
  rw [Finset.sum_ite_eq' Finset.univ (c - a) (fun _ => (1 / 4 : ℝ))]; simp

/-- `xorDist` has total mass `1`: it is a probability distribution. -/
theorem sum_xorDist : ∑ q, xorDist q = 1 := by
  simp only [xorDist, Fintype.sum_prod_type]
  have inner : ∀ x y : ZMod 2, (∑ z : ZMod 2, if z = x + y then (1 / 4 : ℝ) else 0) = 1 / 4 :=
    fun x y => by rw [Finset.sum_ite_eq' Finset.univ (x + y) (fun _ => (1 / 4 : ℝ))]; simp
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => inner x y))]
  simp [ZMod.card 2]; norm_num

/-- Entropy of the uniform distribution on `ZMod 2 × ZMod 2` (four outcomes of mass `1/4`):
`H = 2 log 2` (`= log 4`, i.e. `2` bits). -/
theorem entropy_const_quarter :
    entropy (fun _ : ZMod 2 × ZMod 2 => (1 / 4 : ℝ)) = 2 * Real.log 2 := by
  rw [show (1 / 4 : ℝ) = (Fintype.card (ZMod 2 × ZMod 2) : ℝ)⁻¹ by
        rw [Fintype.card_prod, ZMod.card]; norm_num,
    entropy_uniform, Fintype.card_prod, ZMod.card,
    show ((2 * 2 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

/-- Entropy of the uniform distribution on `ZMod 2` (two outcomes of mass `1/2`): `H = log 2`
(one bit). -/
theorem entropy_const_half : entropy (fun _ : ZMod 2 => (1 / 2 : ℝ)) = Real.log 2 := by
  rw [show (1 / 2 : ℝ) = (Fintype.card (ZMod 2) : ℝ)⁻¹ by rw [ZMod.card]; norm_num,
    entropy_uniform, ZMod.card]; norm_num

/-- Each marginal of the uniform distribution on `ZMod 2 × ZMod 2` is the uniform distribution on
`ZMod 2`. -/
theorem marginalFst_const_quarter :
    marginalFst (fun _ : ZMod 2 × ZMod 2 => (1 / 4 : ℝ)) = fun _ => (1 / 2 : ℝ) := by
  funext x
  simp only [marginalFst_apply, Finset.sum_const, Finset.card_univ, ZMod.card 2, nsmul_eq_mul]
  norm_num

/-- Each marginal of the uniform distribution on `ZMod 2 × ZMod 2` is the uniform distribution on
`ZMod 2`. -/
theorem marginalSnd_const_quarter :
    marginalSnd (fun _ : ZMod 2 × ZMod 2 => (1 / 4 : ℝ)) = fun _ => (1 / 2 : ℝ) := by
  funext x
  simp only [marginalSnd_apply, Finset.sum_const, Finset.card_univ, ZMod.card 2, nsmul_eq_mul]
  norm_num

/-- The `(X, Z)` marginal of `xorDist` is the uniform distribution: `X` and `Z = X ⊕ Y` are
independent uniform bits (for each `(x, z)` there is exactly one `y` with `z = x + y`). -/
theorem xorDistXZ_eq : xorDistXZ = fun _ => (1 / 4 : ℝ) := by
  funext q; obtain ⟨x, z⟩ := q
  simp only [xorDistXZ, xorDist]
  exact sum_ite_add_eq x z

/-- The `(Y, Z)` marginal of `xorDist` is the uniform distribution: `Y` and `Z = X ⊕ Y` are
independent uniform bits (for each `(y, z)` there is exactly one `x` with `z = x + y`). -/
theorem xorDistYZ_eq : xorDistYZ = fun _ => (1 / 4 : ℝ) := by
  funext q; obtain ⟨y, z⟩ := q
  simp only [xorDistYZ, xorDist]
  have hcomm : ∀ x : ZMod 2,
      (if z = x + y then (1 / 4 : ℝ) else 0) = if z = y + x then (1 / 4 : ℝ) else 0 :=
    fun x => by rw [add_comm x y]
  rw [Finset.sum_congr rfl (fun x _ => hcomm x)]
  exact sum_ite_add_eq y z

/-- The `(X, Y)`-marginal of `xorDistPairZ` is uniform on the four pairs (`X`, `Y` are independent
uniform bits), giving `H(X, Y) = 2 log 2`. -/
theorem marginalFst_xorDistPairZ : marginalFst xorDistPairZ = fun _ => (1 / 4 : ℝ) := by
  funext w; obtain ⟨x, y⟩ := w
  simp only [marginalFst_apply, xorDistPairZ, xorDist]
  rw [Finset.sum_ite_eq' Finset.univ (x + y) (fun _ => (1 / 4 : ℝ))]; simp

/-- The `Z`-marginal of `xorDistPairZ` is uniform on `ZMod 2`, giving `H(Z) = log 2` (for each `z`
there are exactly two pairs `(x, y)` with `z = x + y`). -/
theorem marginalSnd_xorDistPairZ : marginalSnd xorDistPairZ = fun _ => (1 / 2 : ℝ) := by
  funext z
  simp only [marginalSnd_apply, xorDistPairZ, xorDist, Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun x _ => sum_ite_add_eq x z)]
  simp [ZMod.card 2]; norm_num

/-- The joint entropy `H(X, Y, Z) = H(X, Y) = 2 log 2`, since `Z` is a deterministic function of
`(X, Y)` (only the four consistent triples carry mass). -/
theorem entropy_xorDistPairZ : entropy xorDistPairZ = 2 * Real.log 2 := by
  rw [entropy_eq, Fintype.sum_prod_type]
  have inner : ∀ w : ZMod 2 × ZMod 2,
      (∑ z : ZMod 2, Real.negMulLog (xorDistPairZ (w, z))) = Real.negMulLog (1 / 4) := fun w => by
    simp only [xorDistPairZ, xorDist, apply_ite Real.negMulLog, Real.negMulLog_zero]
    rw [Finset.sum_ite_eq' Finset.univ (w.1 + w.2) (fun _ => Real.negMulLog (1 / 4))]; simp
  rw [Finset.sum_congr rfl (fun w _ => inner w)]
  -- the remaining `∑ w, negMulLog (1/4)` is exactly `entropy (fun _ ↦ 1/4)` on the pair type
  exact entropy_const_quarter

/-- `H(X : Z) = 0`: on its own, `X` carries no information about `Z = X ⊕ Y`. -/
theorem mutualInfo_xorDistXZ : mutualInfo xorDistXZ = 0 := by
  rw [mutualInfo_eq, xorDistXZ_eq, marginalFst_const_quarter, marginalSnd_const_quarter,
    entropy_const_half, entropy_const_quarter]; ring

/-- `H(Y : Z) = 0`: on its own, `Y` carries no information about `Z = X ⊕ Y`. -/
theorem mutualInfo_xorDistYZ : mutualInfo xorDistYZ = 0 := by
  rw [mutualInfo_eq, xorDistYZ_eq, marginalFst_const_quarter, marginalSnd_const_quarter,
    entropy_const_half, entropy_const_quarter]; ring

/-- `H(X, Y : Z) = log 2` (one bit): the pair `(X, Y)` *determines* `Z = X ⊕ Y`. -/
theorem mutualInfo_xorDistPairZ : mutualInfo xorDistPairZ = Real.log 2 := by
  rw [mutualInfo_eq, marginalFst_xorDistPairZ, marginalSnd_xorDistPairZ,
    entropy_xorDistPairZ, entropy_const_quarter, entropy_const_half]; ring

/-- **Mutual information is not subadditive** (Nielsen & Chuang, Exercise 11.8, eq. (11.34)): for
`X`, `Y` independent uniform bits and `Z = X ⊕ Y`,
`H(X, Y : Z) ≰ H(X : Z) + H(Y : Z)`, because
`H(X, Y : Z) = log 2 > 0 = 0 + 0 = H(X : Z) + H(Y : Z)`. The values are base-independent (a change
of logarithm base scales every term by the same positive factor), so the failure holds equally for
the base-`2` (bit) convention of N&C. -/
theorem mutualInfo_xorDist_not_subadditive :
    ¬ mutualInfo xorDistPairZ ≤ mutualInfo xorDistXZ + mutualInfo xorDistYZ := by
  rw [mutualInfo_xorDistPairZ, mutualInfo_xorDistXZ, mutualInfo_xorDistYZ, add_zero]
  exact not_le.mpr (Real.log_pos (by norm_num))

end XorMutualInfo

end Real
