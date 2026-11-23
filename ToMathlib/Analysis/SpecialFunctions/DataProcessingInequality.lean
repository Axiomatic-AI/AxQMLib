/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# The data processing inequality (Nielsen & Chuang, Theorem 11.5)

For a tripartite distribution `p : ι × κ × μ → ℝ` of random variables `(X, Y, Z)`, this file proves
the **classical data processing inequality**: if `X → Y → Z` is a Markov chain, then
`H(X) ≥ H(X : Y) ≥ H(X : Z)`, where `H(X : Y)` is the mutual information. Intuitively, further
processing the output `Y` of a noisy channel cannot increase the information it carries about the
input `X`: once information is lost, it is gone forever.

Reading `ι × κ × μ` as `ι × (κ × μ)`, the quantities are entropies / mutual informations of
marginals of `p` (from `ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`):

* `H(X) = entropy (marginalFst p)`;
* `H(X : Y) = mutualInfo (marginalFstMid p)`, the mutual information of the `(X, Y)`-marginal;
* `H(X : Z) = mutualInfo (marginalFstLast p)`, of the `(X, Z)`-marginal `marginalFstLast` — the one
  new marginal here (summing out the middle `Y`).

## Main definitions and results

* `Real.marginalFstLast` — the `(X, Z)`-marginal `p_{XZ}(x, z) = ∑_y p(x, y, z)`.
* `Real.IsMarkovChain` — `X → Y → Z` is a Markov chain: `X` and `Z` are conditionally independent
  given `Y`, `p(x, y, z) · p_Y(y) = p_{XY}(x, y) · p_{YZ}(y, z)` (the division-free form of
  `p(z | x, y) = p(z | y)`, N&C eq. (11.36)). The condition is symmetric in `X` and `Z`, so it also
  expresses `Z → Y → X` (N&C Exercise 11.10).
* `Real.mutualInfo_marginalFstMid_le_marginalFst` — the first inequality `H(X : Y) ≤ H(X)` (needing
  no Markov hypothesis), and `Real.mutualInfo_marginalFstMid_eq_marginalFst_iff` its saturation
  condition: `H(X) = H(X : Y)` iff `X` is a deterministic function of `Y`, i.e. `X` is
  reconstructible from `Y`.
* `Real.mutualInfo_marginalFstLast_le_marginalFstMid` — the data processing inequality proper,
  `H(X : Z) ≤ H(X : Y)`, for a Markov chain.

The DPI proper follows N&C's proof. Since `H(X : W) = H(X) − H(X | W)`, it reduces to
`H(X | Y) ≤ H(X | Z)`. The Markov property gives `H(X | Y) = H(X | Y, Z)`
(`condEntropy_marginalFstMid_eq_of_isMarkovChain`, as `p` equals its conditional-independence
reconstruction `condIndepProd p`), and conditioning-reduces-entropy (`Real.entropy_conditioning_le`,
applied to `p` with `Y` and `Z` swapped so that `Y` is conditioned away) gives
`H(X | Y, Z) ≤ H(X | Z)`.

This is pure finite-probability real analysis on `p : ι × κ × μ → ℝ`; the statement of Theorem 11.5
is in `AxQM/NC/Ch11/Theorem11_5.lean`. Entropy is in nats; the
inequalities are base-invariant, so this is a faithful reformulation of N&C's base-2 statement.
-/

@[expose] public section

namespace Real

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-! ### The `(X, Z)`-marginal -/

/-- The joint `(X, Z)`-marginal `p_{XZ}(x, z) = ∑_y p(x, y, z)` of a tripartite distribution,
obtained by summing out the middle variable `Y`. -/
noncomputable def marginalFstLast (p : ι × κ × μ → ℝ) : ι × μ → ℝ := fun q ↦ ∑ y, p (q.1, y, q.2)

omit [Fintype ι] [Fintype μ] in
theorem marginalFstLast_apply (p : ι × κ × μ → ℝ) (x : ι) (z : μ) :
    marginalFstLast p (x, z) = ∑ y, p (x, y, z) := rfl

omit [Fintype ι] [Fintype μ] in
/-- The `(X, Z)`-marginal of the reversed triple is the `(X, Z)`-marginal of the original with its
outer coordinates swapped: `(reverseTriple p)_{ZX}(z, x) = p_{XZ}(x, z)`. Completes the
`reverseTriple`-marginal family (`marginalMid_reverseTriple`, `marginalFstMid_reverseTriple`,
`marginalSnd_reverseTriple`), which live in `JointEntropy` beside their marginals; `marginalFstLast`
is defined here, so this member does too. -/
theorem marginalFstLast_reverseTriple (p : ι × κ × μ → ℝ) (z : μ) (x : ι) :
    marginalFstLast (reverseTriple p) (z, x) = marginalFstLast p (x, z) := by
  simp only [marginalFstLast_apply, reverseTriple_apply]

omit [Fintype ι] in
/-- The `(X, Y)`-marginal and the full distribution share the first marginal `p_X`:
`(p_{XY})_X = p_X`. -/
theorem marginalFst_marginalFstMid (p : ι × κ × μ → ℝ) :
    marginalFst (marginalFstMid p) = marginalFst p := by
  funext x
  simp only [marginalFst_apply, marginalFstMid_apply, Fintype.sum_prod_type]

omit [Fintype ι] in
/-- The `(X, Z)`-marginal and the full distribution share the first marginal `p_X`:
`(p_{XZ})_X = p_X`. -/
theorem marginalFst_marginalFstLast (p : ι × κ × μ → ℝ) :
    marginalFst (marginalFstLast p) = marginalFst p := by
  funext x
  simp only [marginalFst_apply, marginalFstLast_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-! ### The Markov chain condition

`Real.IsMarkovChain` (`X → Y → Z` a Markov chain: `X` and `Z` conditionally independent given `Y`,
N&C eq. (11.36) / Ex. 11.10) is defined upstream in
`ToMathlib.Analysis.SpecialFunctions.JointEntropy` (imported above) and reused here. -/

omit [Fintype κ] in
/-- For a Markov chain, the joint distribution equals its conditional-independence reconstruction
`p = condIndepProd p` (`condIndepProd p (x, y, z) = p_{XY}(x, y) · p_{YZ}(y, z) / p_Y(y)`). On the
`p_Y(y) = 0` fibre both sides vanish (`p ≤ p_Y = 0`, and `_ / 0 = 0`); elsewhere it is the Markov
identity divided by `p_Y(y)`. -/
theorem eq_condIndepProd_of_isMarkovChain {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hm : IsMarkovChain p) : p = condIndepProd p := by
  funext q
  obtain ⟨x, y, z⟩ := q
  simp only [condIndepProd]
  rcases eq_or_ne (marginalMid p y) 0 with h | h
  · rw [h, div_zero]
    have hle : p (x, y, z) ≤ marginalMid p y :=
      le_trans (le_marginalSnd hp x (y, z))
        (le_marginalFst (fun w ↦ marginalSnd_nonneg hp w) y z)
    exact le_antisymm (h ▸ hle) (hp _)
  · rw [eq_div_iff h]
    exact hm x y z

/-! ### The first inequality `H(X : Y) ≤ H(X)` and its saturation -/

/-- **First inequality of the data processing inequality** (N&C Theorem 11.5): the mutual
information never exceeds the source entropy, `H(X : Y) ≤ H(X)`. This is
`H(X : Y) = H(X) − H(X | Y)` with the conditional entropy `H(X | Y) ≥ 0`; it needs no Markov
hypothesis. -/
theorem mutualInfo_marginalFstMid_le_marginalFst {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q) :
    mutualInfo (marginalFstMid p) ≤ entropy (marginalFst p) := by
  have h := condEntropy_nonneg (marginalFstMid_nonneg hp)
  rw [condEntropy_eq] at h
  rw [mutualInfo_eq, marginalFst_marginalFstMid]
  linarith

/-- **Saturation of the first inequality** (N&C Theorem 11.5, the "moreover"): `H(X) = H(X : Y)` if
and only if `X` is a deterministic function of `Y` — i.e. given `Y` one can reconstruct `X`. The
right-hand side `SndDeterminedByFst (fun w ↦ p_{XY}(w.2, w.1))` reads on the `(Y, X)`-marginal as
`∃ f, ∀ y x, p_{XY}(x, y) ≠ 0 → x = f y`. Obtained from
`mutualInfo_eq_marginalSnd_iff_sndDeterminedByFst` (N&C Theorem 11.3, part 2) applied to the
`(Y, X)`-marginal. -/
theorem mutualInfo_marginalFstMid_eq_marginalFst_iff {p : ι × κ × μ → ℝ} [Nonempty ι]
    (hp : ∀ q, 0 ≤ p q) :
    mutualInfo (marginalFstMid p) = entropy (marginalFst p) ↔
      SndDeterminedByFst (fun w : κ × ι ↦ marginalFstMid p (w.2, w.1)) := by
  have hqnn : ∀ w : κ × ι, 0 ≤ marginalFstMid p (w.2, w.1) := fun w ↦ marginalFstMid_nonneg hp _
  have key := mutualInfo_eq_marginalSnd_iff_sndDeterminedByFst
    (p := fun w : κ × ι ↦ marginalFstMid p (w.2, w.1)) hqnn
  rw [mutualInfo_swap (marginalFstMid p), marginalSnd_swap (marginalFstMid p),
    marginalFst_marginalFstMid] at key
  exact key

/-! ### The data processing inequality `H(X : Z) ≤ H(X : Y)` -/

/-- **The Markov property equates two conditional entropies**: `H(X | Y) = H(X | Y, Z)`. Learning
`Z` in addition to `Y` reveals nothing further about `X`, because for a Markov chain `p` equals its
reconstruction `condIndepProd p`, so `D(p ‖ condIndepProd p) = 0`, i.e. strong subadditivity is
saturated (`relativeEntropy_condIndepProd`). -/
theorem condEntropy_marginalFstMid_eq_of_isMarkovChain {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hm : IsMarkovChain p) : condEntropy (marginalFstMid p) = condEntropy p := by
  have hpeq : p = condIndepProd p := eq_condIndepProd_of_isMarkovChain hp hm
  have hzero : relativeEntropy p (condIndepProd p) = 0 := by
    rw [← hpeq]; exact relativeEntropy_self p
  rw [relativeEntropy_condIndepProd hp] at hzero
  rw [condEntropy_eq, condEntropy_eq, marginalSnd_marginalFstMid]
  linarith

/-- **Conditioning on `Z` reduces the conditional entropy further**: `H(X | Y, Z) ≤ H(X | Z)`.
Obtained from `entropy_conditioning_le` (`H(X | Y, Z) ≤ H(X | Y)`) applied to `p` with the roles of
`Y` and `Z` swapped, so that `Z` is the middle variable and `Y` is conditioned away. -/
theorem condEntropy_le_condEntropy_marginalFstLast {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hsum : ∑ q, p q = 1) : condEntropy p ≤ condEntropy (marginalFstLast p) := by
  have hp'_nn : ∀ q : ι × μ × κ, 0 ≤ (fun t : ι × μ × κ ↦ p (t.1, t.2.2, t.2.1)) q := fun _ ↦ hp _
  have hp'_sum : ∑ q : ι × μ × κ, (fun t : ι × μ × κ ↦ p (t.1, t.2.2, t.2.1)) q = 1 := by
    rw [← hsum]
    exact Fintype.sum_equiv ((Equiv.refl ι).prodCongr (Equiv.prodComm μ κ)) _ _ fun _ ↦ rfl
  have hcond := entropy_conditioning_le hp'_nn hp'_sum
  have he : entropy (fun t : ι × μ × κ ↦ p (t.1, t.2.2, t.2.1)) = entropy p := by
    rw [entropy_eq, entropy_eq]
    exact Fintype.sum_equiv ((Equiv.refl ι).prodCongr (Equiv.prodComm μ κ)) _ _ fun _ ↦ rfl
  have hsnd : marginalSnd (fun t : ι × μ × κ ↦ p (t.1, t.2.2, t.2.1))
      = fun w : μ × κ ↦ marginalSnd p (w.2, w.1) := by
    funext w
    simp only [marginalSnd_apply]
  have hcondp' : condEntropy (fun t : ι × μ × κ ↦ p (t.1, t.2.2, t.2.1)) = condEntropy p := by
    rw [condEntropy_eq, condEntropy_eq, he, hsnd, entropy_swap]
  have hmfm : marginalFstMid (fun t : ι × μ × κ ↦ p (t.1, t.2.2, t.2.1)) = marginalFstLast p := by
    funext w
    obtain ⟨x, z⟩ := w
    simp only [marginalFstMid_apply, marginalFstLast_apply]
  rw [hcondp', hmfm] at hcond
  exact hcond

/-- **The data processing inequality** (N&C Theorem 11.5): for a Markov chain `X → Y → Z`, the
mutual information decreases along the chain, `H(X : Z) ≤ H(X : Y)`. Since
`H(X : W) = H(X) − H(X | W)`, this is `H(X | Y) ≤ H(X | Z)`, which combines the Markov equality
`H(X | Y) = H(X | Y, Z)` (`condEntropy_marginalFstMid_eq_of_isMarkovChain`) with
conditioning-reduces-entropy `H(X | Y, Z) ≤ H(X | Z)`
(`condEntropy_le_condEntropy_marginalFstLast`). -/
theorem mutualInfo_marginalFstLast_le_marginalFstMid {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hsum : ∑ q, p q = 1) (hm : IsMarkovChain p) :
    mutualInfo (marginalFstLast p) ≤ mutualInfo (marginalFstMid p) := by
  have key : condEntropy (marginalFstMid p) ≤ condEntropy (marginalFstLast p) := by
    rw [condEntropy_marginalFstMid_eq_of_isMarkovChain hp hm]
    exact condEntropy_le_condEntropy_marginalFstLast hp hsum
  rw [condEntropy_eq, condEntropy_eq] at key
  rw [mutualInfo_eq, mutualInfo_eq, marginalFst_marginalFstMid, marginalFst_marginalFstLast]
  linarith

/-- **The data processing inequality, second form.** For a Markov chain `X → Y → Z`, the
input–output mutual information is at most the intermediate–output mutual information,
`H(X : Z) ≤ H(Y : Z)`. The symmetric partner of `mutualInfo_marginalFstLast_le_marginalFstMid`:
apply that first form to the reversed triple `Z → Y → X` (`isMarkovChain_reverseTriple`) and
identify the marginals via the swap-invariance of mutual information (`mutualInfo_swap`). -/
theorem mutualInfo_marginalFstLast_le_marginalSnd {p : ι × κ × μ → ℝ} (hp : ∀ q, 0 ≤ p q)
    (hsum : ∑ q, p q = 1) (hm : IsMarkovChain p) :
    mutualInfo (marginalFstLast p) ≤ mutualInfo (marginalSnd p) := by
  have key := mutualInfo_marginalFstLast_le_marginalFstMid (p := reverseTriple p)
    (fun t => hp _) (by rw [sum_reverseTriple]; exact hsum) (isMarkovChain_reverseTriple hm)
  have e1 : marginalFstLast (reverseTriple p)
      = fun w : μ × ι => marginalFstLast p (w.2, w.1) := by
    funext w
    obtain ⟨z, x⟩ := w
    exact marginalFstLast_reverseTriple _ z x
  have e2 : marginalFstMid (reverseTriple p)
      = fun w : μ × κ => marginalSnd p (w.2, w.1) := by
    funext w
    obtain ⟨z, y⟩ := w
    exact marginalFstMid_reverseTriple _ z y
  rwa [e1, e2, mutualInfo_swap, mutualInfo_swap] at key

end Real
