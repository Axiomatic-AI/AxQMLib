/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyConvexNonfaithful
public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Generalized relative entropy for positive operators (Nielsen & Chuang, Problem 11.2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 11.2 extends the
(Umegaki) relative entropy `S(r ‖ s) = tr(r log r) - tr(r log s)` to arbitrary positive
operators and asks for four properties. This file proves all four for strictly positive
operators on a finite-dimensional complex Euclidean space.

The relative entropy itself is `ContinuousLinearMap.quantumRelativeEntropy` from
`ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy`, whose definition
`re tr(ρ log ρ) - re tr(ρ log σ)` (with `log` the operator logarithm via the continuous functional
calculus) is exactly N&C's generalized definition (11.131).

## Main results

- `ContinuousLinearMap.quantumRelativeEntropy_smul_smul`: **scaling** (N&C 11.132),
  `S(c • r ‖ d • s) = c · S(r ‖ s) + c · tr(r) · log(c / d)`.
- `ContinuousLinearMap.quantumRelativeEntropy_subadditive_of_jointConvex`: **(11.133) via joint
  convexity** — joint convexity of the relative entropy implies its subadditivity.
- `ContinuousLinearMap.quantumRelativeEntropy_subadditive`: **subadditivity** (11.133),
  `S(r₁ + r₂ ‖ s₁ + s₂) ≤ S(r₁ ‖ s₁) + S(r₂ ‖ s₂)`, the concrete instance obtained from Lindblad
  joint convexity (`quantumRelativeEntropy_jointly_convex`).
- `ContinuousLinearMap.quantumRelativeEntropy_jointConvex_of_subadditive`: **the converse** —
  subadditivity implies joint convexity, closing the equivalence `subadditivity ↔ joint convexity`
  from parts (2) and (3).
- `ContinuousLinearMap.quantumRelativeEntropy_sum_le_sum`: **n-ary subadditivity** —
  `S(∑ᵢ rᵢ ‖ ∑ᵢ sᵢ) ≤ ∑ᵢ S(rᵢ ‖ sᵢ)` over a nonempty index `Finset`, the finite iterate of the
  binary subadditivity used by part (4).
- `ContinuousLinearMap.quantumRelativeEntropy_sum_smul_smul_le`: **the mixture bound** (N&C 11.134),
  `S(∑ᵢ pᵢ • rᵢ ‖ ∑ᵢ qᵢ • sᵢ) ≤ ∑ᵢ pᵢ · S(rᵢ ‖ sᵢ) + ∑ᵢ pᵢ · tr(rᵢ) · log(pᵢ / qᵢ)`.
- `ContinuousLinearMap.quantumRelativeEntropy_sum_smul_smul_le_relativeEntropy`: **the "pretty
  formula"** (N&C 11.135), the density-operator (`tr(rᵢ) = 1`) specialization in which the
  correction term collapses to the classical relative entropy
  `Real.relativeEntropy p q = ∑ᵢ pᵢ log(pᵢ / qᵢ)`.

N&C states the problem for *any two positive operators*, not only strictly positive ones. The
strictly-positive results above therefore carry **faithful strengthenings** on the finite branch
(the support condition `supp r ⊆ supp s`, `HasSupportLE r s`, on which the `cfc`-based `D` equals
the true relative entropy — the domain of the faithful joint convexity, N&C Theorem 11.12
`quantumRelativeEntropy_jointly_convex_of_hasSupportLE`); the strict forms are their special case
`HasSupportLE.of_isStrictlyPositive`:

- `ContinuousLinearMap.quantumRelativeEntropy_smul_smul_of_hasSupportLE`: **scaling** (11.132) for
  positive `r, s` with `r.HasSupportLE s`.
- `ContinuousLinearMap.quantumRelativeEntropy_subadditive_of_hasSupportLE`: **subadditivity**
  (11.133) for positive `r₁, r₂, s₁, s₂` with `rᵢ.HasSupportLE sᵢ`, via the faithful joint
  convexity, with `quantumRelativeEntropy_subadditive_of_jointConvex_of_hasSupportLE` its
  joint-convexity hypothesis form (part (2)).
- `ContinuousLinearMap.quantumRelativeEntropy_jointConvex_of_subadditive_of_hasSupportLE`: **the
  converse** (part (3)) — faithful subadditivity implies faithful joint convexity, closing the
  equivalence for positive operators on the finite branch.
- `ContinuousLinearMap.quantumRelativeEntropy_sum_le_sum_of_hasSupportLE`: **n-ary subadditivity**
  for positive families on the finite branch, the engine of part (4).
- `ContinuousLinearMap.quantumRelativeEntropy_sum_smul_smul_le_of_hasSupportLE`: **the mixture
  bound** (11.134) for positive `rᵢ, sᵢ` with `rᵢ.HasSupportLE sᵢ` and positive weights `pᵢ, qᵢ`.
- `ContinuousLinearMap.quantumRelativeEntropy_sum_smul_smul_le_relativeEntropy_of_hasSupportLE`:
  **the "pretty formula"** (11.135), its density-operator (`re tr(rᵢ) = 1`) specialization.

The per-term support-condition transport `ContinuousLinearMap.hasSupportLE_smul_smul`
(`rᵢ.HasSupportLE sᵢ ⟹ (pᵢ • rᵢ).HasSupportLE (qᵢ • sᵢ)`) feeds the mixture bound.

## Implementation notes

N&C states the problem for "any two positive operators". The definition `S(r ‖ s)` is finite only
under the support condition `supp r ⊆ supp s`; we take the uniformly-clean representative
`IsStrictlyPositive` (spectrum `⊆ (0, ∞)`), where the `Real.log 0 = 0` junk value never appears and
which is also the exact domain of the library joint-convexity theorem (Lindblad,
`convexOn_quantumRelativeEntropy`) that parts (2)–(4) invoke. The scaling identity (part 1) already
needs this hypothesis: the cross term `tr(r log(d • s))` picks up a `log d · tr(r · P_{ker s})`
discrepancy off the support of `s`. We work on `EuclideanSpace ℂ ι` (every finite-dimensional
complex Hilbert space is isometric to one) so as to reuse the `re_trace_*` trace-linearity helpers
and the binary `quantumRelativeEntropy_jointly_convex` directly.

For the mixture bound (part 4) N&C takes `pᵢ, qᵢ` to be probability distributions. The inequality
(11.134) in fact needs only `0 < pᵢ` and `0 < qᵢ` (each `pᵢ • rᵢ`, `qᵢ • sᵢ` strictly positive, so
that finite subadditivity and the scaling law apply term by term); the normalization
`∑ pᵢ = ∑ qᵢ = 1` is used nowhere in the bound. We therefore state the (stronger, more reusable)
positive-weight form. Normalization re-enters only for N&C's "pretty formula" (11.135): with
`tr(rᵢ) = 1` the correction term is `∑ᵢ pᵢ log(pᵢ / qᵢ)`, which is the classical relative entropy
`Real.relativeEntropy p q` — a `Fintype`-wide sum, so the (11.135) specialization is stated over
`Finset.univ`.
-/

@[expose] public section

open scoped ComplexOrder

namespace ContinuousLinearMap

variable {ι : Type*} [Fintype ι]

/-- **Operator logarithm of a positive scalar multiple.** For a strictly positive operator `W` and
`0 < c`, `log (c • W) = (log c) • 1 + log W`, where `log` is the operator real logarithm via the
continuous functional calculus. (The `Real.log 0 = 0` junk value never appears: `W`, hence `c • W`,
has spectrum in `(0, ∞)`.) The operator form of `CFC.log_smul'`, phrased for the `cfc Real.log`
occurring in `quantumRelativeEntropy`. -/
theorem cfc_log_smul {W : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hW : IsStrictlyPositive W) {c : ℝ} (hc : 0 < c) :
    cfc Real.log (c • W) =
      Real.log c • (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) + cfc Real.log W := by
  have h := CFC.log_smul' (A := EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) W hc hW
  rwa [Algebra.algebraMap_eq_smul_one] at h

/-- **Log-scaling of a trace term.** For strictly positive `W`, `0 < c`, and any operator `M`,
`re tr(log(c • W) ∘ M) = log c · re tr M + re tr(log W ∘ M)`. The single-term engine of the scaling
law: the operator identity `cfc_log_smul` splits `log(c • W)`, and the split trace is collapsed by
the operator-level `re_trace_add_smul`. -/
theorem re_trace_cfc_log_smul_comp {W M : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hW : IsStrictlyPositive W) {c : ℝ} (hc : 0 < c) :
    RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        ((cfc Real.log (c • W)).toLinearMap ∘ₗ M.toLinearMap)) =
      Real.log c * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) M.toLinearMap) +
        RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          ((cfc Real.log W).toLinearMap ∘ₗ M.toLinearMap)) := by
  have key : cfc Real.log (c • W) * M
      = Real.log c • M + (1 : ℝ) • (cfc Real.log W * M) := by
    rw [cfc_log_smul hW hc, add_mul, smul_mul_assoc, one_mul, one_smul]
  rw [← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.mul_def, key,
    re_trace_add_smul, one_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.toLinearMap_comp]

set_option linter.unusedFintypeInType false in
-- `[Fintype ι]` occurs in the statement only inside instance proofs on `EuclideanSpace ℂ ι`, so
-- it can be neither omitted nor weakened to `Finite ι` here.
/-- **Pulling a scalar out of the right factor of a trace term.**
`re tr(A ∘ (c • N)) = c · re tr(A ∘ N)`. -/
theorem re_trace_comp_smul_right (A N : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (c : ℝ) :
    RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (A.toLinearMap ∘ₗ (c • N).toLinearMap)) =
      c * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (A.toLinearMap ∘ₗ N.toLinearMap)) := by
  rw [← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.mul_def, mul_smul_comm,
    re_trace_smul, ContinuousLinearMap.mul_def, ContinuousLinearMap.toLinearMap_comp]

set_option maxHeartbeats 400000 in
-- The `ring` finish accumulates CFC `whnf` reductions on the operator-trace atoms.
/-- **Scaling of the generalized relative entropy** (N&C Problem 11.2(1), eq. (11.132)). For
strictly positive operators `r, s` and positive scalars `c, d`,
`S(c • r ‖ d • s) = c · S(r ‖ s) + c · tr(r) · log(c / d)`, where `tr(r)` is `re tr r`. Both
`log`-terms of `S(c • r ‖ d • s)` split via `re_trace_cfc_log_smul_comp`; the residual `c • r`
factors pull out by `re_trace_smul` / `re_trace_comp_smul_right`, and `log c - log d = log(c / d)`.
-/
theorem quantumRelativeEntropy_smul_smul
    {ρ σ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    quantumRelativeEntropy (c • ρ) (d • σ) =
      c * quantumRelativeEntropy ρ σ +
        c * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) ρ.toLinearMap) *
          Real.log (c / d) := by
  rw [quantumRelativeEntropy_def, quantumRelativeEntropy_def,
    re_trace_cfc_log_smul_comp hρ hc, re_trace_cfc_log_smul_comp hσ hd, re_trace_smul,
    re_trace_comp_smul_right, re_trace_comp_smul_right, Real.log_div (ne_of_gt hc) (ne_of_gt hd)]
  ring

set_option maxHeartbeats 400000 in
-- Rewriting with `quantumRelativeEntropy_smul_smul` in `h` reduces CFC operator terms via `whnf`.
/-- **Joint convexity implies subadditivity** (N&C Problem 11.2(2), the forward direction of the
`subadditivity ↔ joint convexity` equivalence, eq. (11.133)). Given the joint convexity of the
relative entropy (as the hypothesis `hJC`), for strictly positive `r₁, r₂, s₁, s₂`,
`S(r₁ + r₂ ‖ s₁ + s₂) ≤ S(r₁ ‖ s₁) + S(r₂ ‖ s₂)`. Apply `hJC` at the midpoint `t = s = ½`; the
left-hand side is `S(½ • (r₁ + r₂) ‖ ½ • (s₁ + s₂))`, which by `quantumRelativeEntropy_smul_smul`
equals `½ · S(r₁ + r₂ ‖ s₁ + s₂)` since `log(½ / ½) = log 1 = 0`. -/
theorem quantumRelativeEntropy_subadditive_of_jointConvex
    (hJC : ∀ {a₁ a₂ b₁ b₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι},
      IsStrictlyPositive a₁ → IsStrictlyPositive a₂ → IsStrictlyPositive b₁ →
        IsStrictlyPositive b₂ → ∀ {t s : ℝ}, 0 ≤ t → 0 ≤ s → t + s = 1 →
          quantumRelativeEntropy (t • a₁ + s • a₂) (t • b₁ + s • b₂) ≤
            t * quantumRelativeEntropy a₁ b₁ + s * quantumRelativeEntropy a₂ b₂)
    {r₁ r₂ s₁ s₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr₁ : IsStrictlyPositive r₁) (hr₂ : IsStrictlyPositive r₂)
    (hs₁ : IsStrictlyPositive s₁) (hs₂ : IsStrictlyPositive s₂) :
    quantumRelativeEntropy (r₁ + r₂) (s₁ + s₂) ≤
      quantumRelativeEntropy r₁ s₁ + quantumRelativeEntropy r₂ s₂ := by
  have h := hJC hr₁ hr₂ hs₁ hs₂ (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (0:ℝ) ≤ 2⁻¹)
    (by norm_num : (2:ℝ)⁻¹ + 2⁻¹ = 1)
  rw [← smul_add, ← smul_add,
    quantumRelativeEntropy_smul_smul (IsStrictlyPositive.nonneg_add hr₁.nonneg hr₂)
      (IsStrictlyPositive.nonneg_add hs₁.nonneg hs₂) (by norm_num) (by norm_num),
    div_self (by norm_num : (2:ℝ)⁻¹ ≠ 0), Real.log_one, mul_zero, add_zero] at h
  linarith

/-- **Subadditivity of the generalized relative entropy** (N&C Problem 11.2(2), eq. (11.133)). For
strictly positive `r₁, r₂, s₁, s₂`,
`S(r₁ + r₂ ‖ s₁ + s₂) ≤ S(r₁ ‖ s₁) + S(r₂ ‖ s₂)`. The concrete instance of
`quantumRelativeEntropy_subadditive_of_jointConvex` obtained by discharging the joint-convexity
hypothesis with Lindblad's theorem (`quantumRelativeEntropy_jointly_convex`). -/
theorem quantumRelativeEntropy_subadditive
    {r₁ r₂ s₁ s₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr₁ : IsStrictlyPositive r₁) (hr₂ : IsStrictlyPositive r₂)
    (hs₁ : IsStrictlyPositive s₁) (hs₂ : IsStrictlyPositive s₂) :
    quantumRelativeEntropy (r₁ + r₂) (s₁ + s₂) ≤
      quantumRelativeEntropy r₁ s₁ + quantumRelativeEntropy r₂ s₂ :=
  quantumRelativeEntropy_subadditive_of_jointConvex
    quantumRelativeEntropy_jointly_convex hr₁ hr₂ hs₁ hs₂

set_option synthInstance.maxHeartbeats 80000 in
-- The `IsStrictlyPositive.smul` applications need the `PosSMulMono ℝ (E →L[ℂ] E)` instance, whose
-- synthesis on the operator algebra exceeds the default `synthInstance` budget.
/-- **Subadditivity implies joint convexity** (N&C Problem 11.2(3), the converse direction of the
`subadditivity ↔ joint convexity` equivalence). Given the subadditivity of the relative entropy
(as the hypothesis `hSub`), for strictly positive `r₁, r₂, s₁, s₂` and convex weights `t + u = 1`,
`S(t • r₁ + u • r₂ ‖ t • s₁ + u • s₂) ≤ t · S(r₁ ‖ s₁) + u · S(r₂ ‖ s₂)`. The boundary weights
`t = 0` / `u = 0` are trivial; on the interior apply `hSub` to `t • r₁, u • r₂, t • s₁, u • s₂` and
rescale each summand via `quantumRelativeEntropy_smul_smul` (with `log(t / t) = log 1 = 0`). -/
theorem quantumRelativeEntropy_jointConvex_of_subadditive
    (hSub : ∀ {a₁ a₂ b₁ b₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι},
      IsStrictlyPositive a₁ → IsStrictlyPositive a₂ → IsStrictlyPositive b₁ →
        IsStrictlyPositive b₂ →
          quantumRelativeEntropy (a₁ + a₂) (b₁ + b₂) ≤
            quantumRelativeEntropy a₁ b₁ + quantumRelativeEntropy a₂ b₂)
    {r₁ r₂ s₁ s₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr₁ : IsStrictlyPositive r₁) (hr₂ : IsStrictlyPositive r₂)
    (hs₁ : IsStrictlyPositive s₁) (hs₂ : IsStrictlyPositive s₂)
    {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (htu : t + u = 1) :
    quantumRelativeEntropy (t • r₁ + u • r₂) (t • s₁ + u • s₂) ≤
      t * quantumRelativeEntropy r₁ s₁ + u * quantumRelativeEntropy r₂ s₂ := by
  rcases eq_or_lt_of_le ht with rfl | ht0
  · have hu1 : u = 1 := by linarith
    subst hu1; simp
  rcases eq_or_lt_of_le hu with rfl | hu0
  · have ht1 : t = 1 := by linarith
    subst ht1; simp
  have h := hSub (hr₁.smul ht0) (hr₂.smul hu0) (hs₁.smul ht0) (hs₂.smul hu0)
  rw [quantumRelativeEntropy_smul_smul hr₁ hs₁ ht0 ht0,
    quantumRelativeEntropy_smul_smul hr₂ hs₂ hu0 hu0] at h
  simp only [div_self ht0.ne', div_self hu0.ne', Real.log_one, mul_zero, add_zero] at h
  exact h

/-- **n-ary subadditivity of the generalized relative entropy.** For a nonempty index `Finset t`
and strictly positive families `r, s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι`,
`S(∑ᵢ rᵢ ‖ ∑ᵢ sᵢ) ≤ ∑ᵢ S(rᵢ ‖ sᵢ)`. The finite iterate of the binary subadditivity
`quantumRelativeEntropy_subadditive`, proved by induction on `t`
(`Finset.Nonempty.cons_induction`): the singleton case is reflexivity, and the cons step splits off
one summand with binary subadditivity — the tail sum stays strictly positive by
`IsStrictlyPositive.sum` — then finishes with the inductive hypothesis. This is the engine of the
mixture bound (part 4). -/
theorem quantumRelativeEntropy_sum_le_sum {κ : Type*} {t : Finset κ} (ht : t.Nonempty)
    {r s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr : ∀ i ∈ t, IsStrictlyPositive (r i)) (hs : ∀ i ∈ t, IsStrictlyPositive (s i)) :
    quantumRelativeEntropy (∑ i ∈ t, r i) (∑ i ∈ t, s i) ≤
      ∑ i ∈ t, quantumRelativeEntropy (r i) (s i) := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a u _ hu ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons]
    have hru : ∀ i ∈ u, IsStrictlyPositive (r i) := fun i hi => hr i (Finset.mem_cons_of_mem hi)
    have hsu : ∀ i ∈ u, IsStrictlyPositive (s i) := fun i hi => hs i (Finset.mem_cons_of_mem hi)
    calc quantumRelativeEntropy (r a + ∑ i ∈ u, r i) (s a + ∑ i ∈ u, s i)
        ≤ quantumRelativeEntropy (r a) (s a) +
            quantumRelativeEntropy (∑ i ∈ u, r i) (∑ i ∈ u, s i) :=
          quantumRelativeEntropy_subadditive (hr a (Finset.mem_cons_self a u))
            (IsStrictlyPositive.sum hu hru) (hs a (Finset.mem_cons_self a u))
            (IsStrictlyPositive.sum hu hsu)
      _ ≤ quantumRelativeEntropy (r a) (s a) + ∑ i ∈ u, quantumRelativeEntropy (r i) (s i) := by
          have := ih hru hsu; linarith

set_option synthInstance.maxHeartbeats 80000 in
-- The `IsStrictlyPositive.smul` applications need the `PosSMulMono ℝ (E →L[ℂ] E)` instance, whose
-- synthesis on the operator algebra exceeds the default `synthInstance` budget.
/-- **Mixture bound for the generalized relative entropy** (N&C Problem 11.2(4), eq. (11.134)). For
strictly positive families `r, s`, positive weights `p, q` (`0 < pᵢ`, `0 < qᵢ`) on a nonempty index
`Finset t`,
`S(∑ᵢ pᵢ • rᵢ ‖ ∑ᵢ qᵢ • sᵢ) ≤ ∑ᵢ pᵢ · S(rᵢ ‖ sᵢ) + ∑ᵢ pᵢ · tr(rᵢ) · log(pᵢ / qᵢ)`,
where `tr(rᵢ)` is `re tr(rᵢ)`. n-ary subadditivity (`quantumRelativeEntropy_sum_le_sum`) applied to
the strictly positive `pᵢ • rᵢ`, `qᵢ • sᵢ` bounds the left-hand side by `∑ᵢ S(pᵢ • rᵢ ‖ qᵢ • sᵢ)`,
and the scaling law (`quantumRelativeEntropy_smul_smul`) rewrites each summand.

N&C phrases part (4) for probability distributions `p, q`; the bound needs only their positivity
(the normalization `∑ pᵢ = ∑ qᵢ = 1` is unused), so this is the stronger positive-weight form. -/
theorem quantumRelativeEntropy_sum_smul_smul_le {κ : Type*} {t : Finset κ} (ht : t.Nonempty)
    {r s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} {p q : κ → ℝ}
    (hr : ∀ i ∈ t, IsStrictlyPositive (r i)) (hs : ∀ i ∈ t, IsStrictlyPositive (s i))
    (hp : ∀ i ∈ t, 0 < p i) (hq : ∀ i ∈ t, 0 < q i) :
    quantumRelativeEntropy (∑ i ∈ t, p i • r i) (∑ i ∈ t, q i • s i) ≤
      (∑ i ∈ t, p i * quantumRelativeEntropy (r i) (s i)) +
        ∑ i ∈ t, p i * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (r i).toLinearMap) *
          Real.log (p i / q i) := by
  refine (quantumRelativeEntropy_sum_le_sum ht (fun i hi => (hr i hi).smul (hp i hi))
    (fun i hi => (hs i hi).smul (hq i hi))).trans (le_of_eq ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    quantumRelativeEntropy_smul_smul (hr i hi) (hs i hi) (hp i hi) (hq i hi)

/-- **The "pretty formula" for the mixture bound** (N&C Problem 11.2(4), eq. (11.135)). When the
`rᵢ` are density operators (`re tr(rᵢ) = 1`), the mixture-bound correction term collapses to the
classical relative entropy (Kullback–Leibler divergence) `Real.relativeEntropy p q = ∑ᵢ pᵢ log(pᵢ /
qᵢ)` of the weight distributions:
`S(∑ᵢ pᵢ • rᵢ ‖ ∑ᵢ qᵢ • sᵢ) ≤ ∑ᵢ pᵢ · S(rᵢ ‖ sᵢ) + D(p ‖ q)`.
Stated over `Finset.univ` of a nonempty `Fintype κ`, matching the index range of
`Real.relativeEntropy`; per-term, `re tr(rᵢ) = 1` and `log(pᵢ / qᵢ) = log pᵢ - log qᵢ`
(`Real.log_div`, valid since `pᵢ, qᵢ > 0`) turn the correction into `∑ᵢ pᵢ (log pᵢ - log qᵢ)`. -/
theorem quantumRelativeEntropy_sum_smul_smul_le_relativeEntropy {κ : Type*} [Fintype κ] [Nonempty κ]
    {r s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} {p q : κ → ℝ}
    (hr : ∀ i, IsStrictlyPositive (r i)) (hs : ∀ i, IsStrictlyPositive (s i))
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (htr : ∀ i, RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (r i).toLinearMap) = 1) :
    quantumRelativeEntropy (∑ i, p i • r i) (∑ i, q i • s i) ≤
      (∑ i, p i * quantumRelativeEntropy (r i) (s i)) + Real.relativeEntropy p q := by
  refine (quantumRelativeEntropy_sum_smul_smul_le Finset.univ_nonempty
    (fun i _ => hr i) (fun i _ => hs i) (fun i _ => hp i) (fun i _ => hq i)).trans (le_of_eq ?_)
  rw [Real.relativeEntropy_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [htr i, mul_one, Real.log_div (hp i).ne' (hq i).ne']

/-! ### Faithful (support-condition) forms for arbitrary positive operators

Nielsen & Chuang Problem 11.2 is stated for *any two positive operators*, not only strictly
positive ones. The `cfc`-based `D` equals the true relative entropy precisely on the **finite
branch**, the support condition `supp r ⊆ supp s` (`HasSupportLE r s`, i.e. `ker s ≤ ker r`); this
is the domain of the faithful joint convexity
`quantumRelativeEntropy_jointly_convex_of_hasSupportLE` (N&C Theorem 11.12, N&C's literal
statement). All four parts of Problem 11.2 go through on that branch for `IsPositive` operators; the
strictly-positive statements above are the special case `HasSupportLE.of_isStrictlyPositive`. This
section develops parts (1)–(3): the scaling law, and the subadditivity ↔ joint convexity
equivalence. -/

/-- **Kernel invariance of the support condition under nonzero real scaling.** For `c ≠ 0`, scaling
the first operator by `c` leaves its kernel unchanged, so `ρ.HasSupportLE σ` upgrades to
`(c • ρ).HasSupportLE σ`. The step that turns a per-pair support condition on `ρᵢ, σᵢ` into one on
the scaled `c • ρᵢ`, as used by the scaling law and the mixture bound. -/
theorem hasSupportLE_smul_left {ρ σ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    {c : ℝ} (hc : c ≠ 0) (h : ρ.HasSupportLE σ) : (c • ρ).HasSupportLE σ := by
  have hker : (↑(c • ρ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).ker
      = (↑ρ : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).ker := by
    rw [← Complex.coe_smul c ρ]
    ext x
    simp only [LinearMap.mem_ker, ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, smul_eq_zero, Complex.ofReal_eq_zero]
    tauto
  unfold ContinuousLinearMap.HasSupportLE at h ⊢
  rwa [hker]

set_option maxHeartbeats 800000 in
-- The eigenbasis spectral computation (three `re_trace_cfc_comp_eq_sum_of_apply_eq_smul` unfoldings
-- plus the `cfc` `whnf` reductions on the operator-trace atoms) exceeds the default budget.
/-- **Log-scaling of a trace term under the support condition.** For a self-adjoint `W`, `0 < c`,
and any `M` supported inside `W` (`M.HasSupportLE W`, i.e. `ker W ≤ ker M`),
`re tr(log(c • W) ∘ M) = log c · re tr M + re tr(log W ∘ M)`. The support-condition generalisation
of `re_trace_cfc_log_smul_comp`, which needs strict positivity (the operator identity
`log(c • W) = log c • 1 + log W` fails on the kernel of `W`, where `log 0 = 0` is a junk value).
Computing all three traces in a common eigenbasis `b` of `W`
(`re_trace_cfc_comp_eq_sum_of_apply_eq_smul`, whose `ContinuousOn Real.log` premise is discharged by
`continuousOn_log_spectrum` since the finite spectrum is discrete), the identity is the termwise
`log(c μᵢ) aᵢ = (log c + log μᵢ) aᵢ` with `aᵢ = re⟨bᵢ, M bᵢ⟩`; on the kernel of `W` (`μᵢ = 0`) the
support condition forces `M bᵢ = 0`, hence `aᵢ = 0`, so the junk value never contributes. -/
theorem re_trace_cfc_log_smul_comp_of_hasSupportLE
    {W M : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hW : IsSelfAdjoint W) (hMW : M.HasSupportLE W) {c : ℝ} (hc : 0 < c) :
    RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        ((cfc Real.log (c • W)).toLinearMap ∘ₗ M.toLinearMap)) =
      Real.log c * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) M.toLinearMap) +
        RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
          ((cfc Real.log W).toLinearMap ∘ₗ M.toLinearMap)) := by
  have hn : Module.finrank ℂ (EuclideanSpace ℂ ι) = Module.finrank ℂ (EuclideanSpace ℂ ι) := rfl
  set b := hW.isSymmetric.eigenvectorBasis hn with hb
  set μ := hW.isSymmetric.eigenvalues hn with hμdef
  have hWb : ∀ i, W (b i) = (μ i : ℂ) • b i := fun i => hW.apply_eigenvectorBasis_cast hn i
  have hcW : IsSelfAdjoint (c • W) := IsSelfAdjoint.smul (IsSelfAdjoint.all c) hW
  have hcWb : ∀ i, (c • W) (b i) = ((c * μ i : ℝ) : ℂ) • b i := fun i => by
    rw [← Complex.coe_smul c W, _root_.smul_apply, hWb i, smul_smul,
      ← Complex.ofReal_mul]
  have hsum_cW := hcW.re_trace_cfc_comp_eq_sum_of_apply_eq_smul b hcWb
    hcW.continuousOn_log_spectrum M
  have hsum_W := hW.re_trace_cfc_comp_eq_sum_of_apply_eq_smul b hWb hW.continuousOn_log_spectrum M
  have htrM : RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) M.toLinearMap)
      = ∑ i, RCLike.re (inner ℂ (b i) (M (b i))) := by
    rw [LinearMap.trace_eq_sum_inner M.toLinearMap b, map_sum]
    simp only [ContinuousLinearMap.coe_coe]
  rw [hsum_cW, hsum_W, htrM, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne (μ i) 0 with hμ0 | hμ0
  · have hker : b i ∈ LinearMap.ker (W : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
      rw [LinearMap.mem_ker]
      change W (b i) = 0
      rw [hWb i, hμ0]; simp
    have hMbi : M (b i) = 0 := by
      have := hMW hker
      rwa [LinearMap.mem_ker] at this
    rw [hMbi]; simp
  · rw [Real.log_mul hc.ne' hμ0]; ring

set_option maxHeartbeats 400000 in
-- The `ring` finish accumulates CFC `whnf` reductions on the operator-trace atoms.
/-- **Scaling of the generalized relative entropy for positive operators** (N&C Problem 11.2(1), eq.
(11.132), faithful form). For positive operators `r, s` on the finite branch `r.HasSupportLE s`
(`supp r ⊆ supp s`) and positive scalars `c, d`,
`S(c • r ‖ d • s) = c · S(r ‖ s) + c · tr(r) · log(c / d)`, where `tr(r)` is `re tr r`. Both
`log`-terms split via `re_trace_cfc_log_smul_comp_of_hasSupportLE`; for the cross term, the support
condition (transported to `(c • r).HasSupportLE s` by `hasSupportLE_smul_left`) is what discards the
`log d · tr(r · P_{ker s})` discrepancy off the support of `s` that would otherwise appear. The
residual `c • r` factors pull out by `re_trace_smul` / `re_trace_comp_smul_right`, and
`log c − log d = log(c / d)`. Strengthens `quantumRelativeEntropy_smul_smul` from strict positivity
to the full positive-operator finite branch. -/
theorem quantumRelativeEntropy_smul_smul_of_hasSupportLE
    {ρ σ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive) (hρσ : ρ.HasSupportLE σ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    quantumRelativeEntropy (c • ρ) (d • σ) =
      c * quantumRelativeEntropy ρ σ +
        c * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) ρ.toLinearMap) *
          Real.log (c / d) := by
  rw [quantumRelativeEntropy_def, quantumRelativeEntropy_def,
    re_trace_cfc_log_smul_comp_of_hasSupportLE hρ.isSelfAdjoint
      (hasSupportLE_smul_left hc.ne' (le_refl _)) hc,
    re_trace_cfc_log_smul_comp_of_hasSupportLE hσ.isSelfAdjoint
      (hasSupportLE_smul_left hc.ne' hρσ) hd, re_trace_smul,
    re_trace_comp_smul_right, re_trace_comp_smul_right, Real.log_div (ne_of_gt hc) (ne_of_gt hd)]
  ring

/-- **Joint convexity implies subadditivity, faithful form** (N&C Problem 11.2(2), the forward
direction of the `subadditivity ↔ joint convexity` equivalence, eq. (11.133), for positive operators
on the finite branch). Given the faithful joint convexity of the relative entropy (as the hypothesis
`hJC`, for positive operators with the support condition), for positive `r₁, r₂, s₁, s₂` with
`r₁.HasSupportLE s₁`, `r₂.HasSupportLE s₂`,
`S(r₁ + r₂ ‖ s₁ + s₂) ≤ S(r₁ ‖ s₁) + S(r₂ ‖ s₂)`. Apply `hJC` at the midpoint `t = s = ½`; the
left-hand side is `S(½ • (r₁ + r₂) ‖ ½ • (s₁ + s₂))`, which by
`quantumRelativeEntropy_smul_smul_of_hasSupportLE` (using `(r₁ + r₂).HasSupportLE (s₁ + s₂)` from
`hasSupportLE_add`) equals `½ · S(r₁ + r₂ ‖ s₁ + s₂)` since `log(½ / ½) = log 1 = 0`. Strengthens
`quantumRelativeEntropy_subadditive_of_jointConvex` from strict positivity to the full
positive-operator finite branch. -/
theorem quantumRelativeEntropy_subadditive_of_jointConvex_of_hasSupportLE
    (hJC : ∀ {a₁ a₂ b₁ b₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι},
      a₁.IsPositive → a₂.IsPositive → b₁.IsPositive → b₂.IsPositive →
        a₁.HasSupportLE b₁ → a₂.HasSupportLE b₂ → ∀ {t s : ℝ}, 0 ≤ t → 0 ≤ s → t + s = 1 →
          quantumRelativeEntropy (t • a₁ + s • a₂) (t • b₁ + s • b₂) ≤
            t * quantumRelativeEntropy a₁ b₁ + s * quantumRelativeEntropy a₂ b₂)
    {r₁ r₂ s₁ s₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr₁ : r₁.IsPositive) (hr₂ : r₂.IsPositive) (hs₁ : s₁.IsPositive) (hs₂ : s₂.IsPositive)
    (hsup₁ : r₁.HasSupportLE s₁) (hsup₂ : r₂.HasSupportLE s₂) :
    quantumRelativeEntropy (r₁ + r₂) (s₁ + s₂) ≤
      quantumRelativeEntropy r₁ s₁ + quantumRelativeEntropy r₂ s₂ := by
  have h := hJC hr₁ hr₂ hs₁ hs₂ hsup₁ hsup₂ (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (0:ℝ) ≤ 2⁻¹)
    (by norm_num : (2:ℝ)⁻¹ + 2⁻¹ = 1)
  rw [← smul_add, ← smul_add,
    quantumRelativeEntropy_smul_smul_of_hasSupportLE (hr₁.add hr₂) (hs₁.add hs₂)
      (hasSupportLE_add hs₁ hs₂ hsup₁ hsup₂) (by norm_num) (by norm_num),
    div_self (by norm_num : (2:ℝ)⁻¹ ≠ 0), Real.log_one, mul_zero, add_zero] at h
  linarith

/-- **Subadditivity of the generalized relative entropy for positive operators** (N&C Problem
11.2(2), eq. (11.133), faithful form). For positive `r₁, r₂, s₁, s₂` on the finite branch
`r₁.HasSupportLE s₁`, `r₂.HasSupportLE s₂`,
`S(r₁ + r₂ ‖ s₁ + s₂) ≤ S(r₁ ‖ s₁) + S(r₂ ‖ s₂)`. The concrete instance of
`quantumRelativeEntropy_subadditive_of_jointConvex_of_hasSupportLE` obtained by discharging the
joint-convexity hypothesis with the faithful Lindblad theorem (N&C Theorem 11.12,
`quantumRelativeEntropy_jointly_convex_of_hasSupportLE`). Strengthens
`quantumRelativeEntropy_subadditive` from strict positivity to the full positive-operator finite
branch. -/
theorem quantumRelativeEntropy_subadditive_of_hasSupportLE
    {r₁ r₂ s₁ s₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr₁ : r₁.IsPositive) (hr₂ : r₂.IsPositive) (hs₁ : s₁.IsPositive) (hs₂ : s₂.IsPositive)
    (hsup₁ : r₁.HasSupportLE s₁) (hsup₂ : r₂.HasSupportLE s₂) :
    quantumRelativeEntropy (r₁ + r₂) (s₁ + s₂) ≤
      quantumRelativeEntropy r₁ s₁ + quantumRelativeEntropy r₂ s₂ :=
  quantumRelativeEntropy_subadditive_of_jointConvex_of_hasSupportLE
    quantumRelativeEntropy_jointly_convex_of_hasSupportLE hr₁ hr₂ hs₁ hs₂ hsup₁ hsup₂

/-- **Subadditivity implies joint convexity, faithful form** (N&C Problem 11.2(3), the converse
direction of the `subadditivity ↔ joint convexity` equivalence, for positive operators on the finite
branch). Given the faithful subadditivity of the relative entropy (as the hypothesis `hSub`), for
positive `r₁, r₂, s₁, s₂` with `r₁.HasSupportLE s₁`, `r₂.HasSupportLE s₂` and convex weights
`t + u = 1`,
`S(t • r₁ + u • r₂ ‖ t • s₁ + u • s₂) ≤ t · S(r₁ ‖ s₁) + u · S(r₂ ‖ s₂)`. The boundary weights
`t = 0` / `u = 0` are trivial; on the interior apply `hSub` to the positive
`t • r₁, u • r₂, t • s₁, u • s₂`
(support conditions transported by `hasSupportLE_smul`) and rescale each summand via
`quantumRelativeEntropy_smul_smul_of_hasSupportLE` (with `log(t / t) = log 1 = 0`). Strengthens
`quantumRelativeEntropy_jointConvex_of_subadditive` from strict positivity to the full
positive-operator finite branch. -/
theorem quantumRelativeEntropy_jointConvex_of_subadditive_of_hasSupportLE
    (hSub : ∀ {a₁ a₂ b₁ b₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι},
      a₁.IsPositive → a₂.IsPositive → b₁.IsPositive → b₂.IsPositive →
        a₁.HasSupportLE b₁ → a₂.HasSupportLE b₂ →
          quantumRelativeEntropy (a₁ + a₂) (b₁ + b₂) ≤
            quantumRelativeEntropy a₁ b₁ + quantumRelativeEntropy a₂ b₂)
    {r₁ r₂ s₁ s₂ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr₁ : r₁.IsPositive) (hr₂ : r₂.IsPositive) (hs₁ : s₁.IsPositive) (hs₂ : s₂.IsPositive)
    (hsup₁ : r₁.HasSupportLE s₁) (hsup₂ : r₂.HasSupportLE s₂)
    {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (htu : t + u = 1) :
    quantumRelativeEntropy (t • r₁ + u • r₂) (t • s₁ + u • s₂) ≤
      t * quantumRelativeEntropy r₁ s₁ + u * quantumRelativeEntropy r₂ s₂ := by
  rcases eq_or_lt_of_le ht with rfl | ht0
  · have hu1 : u = 1 := by linarith
    subst hu1; simp
  rcases eq_or_lt_of_le hu with rfl | hu0
  · have ht1 : t = 1 := by linarith
    subst ht1; simp
  have h := hSub (hr₁.smul_real_of_nonneg ht0.le) (hr₂.smul_real_of_nonneg hu0.le)
    (hs₁.smul_real_of_nonneg ht0.le) (hs₂.smul_real_of_nonneg hu0.le)
    (hasSupportLE_smul ht0.ne' hsup₁) (hasSupportLE_smul hu0.ne' hsup₂)
  rw [quantumRelativeEntropy_smul_smul_of_hasSupportLE hr₁ hs₁ hsup₁ ht0 ht0,
    quantumRelativeEntropy_smul_smul_of_hasSupportLE hr₂ hs₂ hsup₂ hu0 hu0] at h
  simp only [div_self ht0.ne', div_self hu0.ne', Real.log_one, mul_zero, add_zero] at h
  exact h

/-! #### The mixture bound for arbitrary positive operators (part (4))

The last part of Problem 11.2 — the finite subadditivity, the mixture bound (11.134), and the
"pretty formula" (11.135) — likewise goes through on the finite branch for positive operators. -/

/-- **Nonzero scaling of the two operators by (possibly different) real scalars preserves the
support condition.** For `c ≠ 0`, `d ≠ 0`, scaling leaves both kernels unchanged
(`ker (e • τ) = ker τ` for `e ≠ 0`, since `(e : ℂ) ≠ 0`), so `ρ.HasSupportLE σ` upgrades to
`(c • ρ).HasSupportLE (d • σ)`. The
per-term support-condition input to the mixture bound: from `rᵢ.HasSupportLE sᵢ` it produces
`(pᵢ • rᵢ).HasSupportLE (qᵢ • sᵢ)`. Generalises `hasSupportLE_smul_left` (the `d = 1` case) to an
independent right scalar; cf. the equal-scalar `hasSupportLE_smul`. -/
theorem hasSupportLE_smul_smul {ρ σ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} {c d : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) (h : ρ.HasSupportLE σ) : (c • ρ).HasSupportLE (d • σ) := by
  have hker : ∀ (e : ℝ), e ≠ 0 → ∀ τ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι,
      (↑(e • τ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).ker
        = (↑τ : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).ker := fun e he τ => by
    rw [← Complex.coe_smul e τ, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.ker_smul _ _ (by exact_mod_cast he : (e : ℂ) ≠ 0)]
  unfold ContinuousLinearMap.HasSupportLE at h ⊢
  rwa [hker c hc ρ, hker d hd σ]

/-- **n-ary subadditivity of the generalized relative entropy for positive operators** (faithful
form). For a nonempty index `Finset t` and positive families
`r, s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι` on the finite branch
`(r i).HasSupportLE (s i)`, `S(∑ᵢ rᵢ ‖ ∑ᵢ sᵢ) ≤ ∑ᵢ S(rᵢ ‖ sᵢ)`. The finite iterate of the binary
faithful subadditivity `quantumRelativeEntropy_subadditive_of_hasSupportLE`, proved by induction on
`t` (`Finset.Nonempty.cons_induction`): the singleton case is reflexivity; the cons step splits off
one summand with binary subadditivity — the tail sum stays positive by `isPositive_sum` and inherits
the support condition by `hasSupportLE_sum_smul` (weights `1`) — then finishes with the inductive
hypothesis. Strengthens `quantumRelativeEntropy_sum_le_sum` from strict positivity to the full
positive-operator finite branch; the engine of the mixture bound (part 4). -/
theorem quantumRelativeEntropy_sum_le_sum_of_hasSupportLE {κ : Type*} {t : Finset κ}
    (ht : t.Nonempty) {r s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hr : ∀ i ∈ t, (r i).IsPositive) (hs : ∀ i ∈ t, (s i).IsPositive)
    (hsup : ∀ i ∈ t, (r i).HasSupportLE (s i)) :
    quantumRelativeEntropy (∑ i ∈ t, r i) (∑ i ∈ t, s i) ≤
      ∑ i ∈ t, quantumRelativeEntropy (r i) (s i) := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a u _ _ ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons]
    have hru : ∀ i ∈ u, (r i).IsPositive := fun i hi => hr i (Finset.mem_cons_of_mem hi)
    have hsu : ∀ i ∈ u, (s i).IsPositive := fun i hi => hs i (Finset.mem_cons_of_mem hi)
    have hsupu : ∀ i ∈ u, (r i).HasSupportLE (s i) := fun i hi => hsup i (Finset.mem_cons_of_mem hi)
    have hsupU : (∑ i ∈ u, r i).HasSupportLE (∑ i ∈ u, s i) := by
      simpa only [one_smul] using
        hasSupportLE_sum_smul (w := fun _ => (1 : ℝ)) u hsu hsupu fun i _ => zero_le_one
    calc quantumRelativeEntropy (r a + ∑ i ∈ u, r i) (s a + ∑ i ∈ u, s i)
        ≤ quantumRelativeEntropy (r a) (s a) +
            quantumRelativeEntropy (∑ i ∈ u, r i) (∑ i ∈ u, s i) :=
          quantumRelativeEntropy_subadditive_of_hasSupportLE (hr a (Finset.mem_cons_self a u))
            (isPositive_sum u hru) (hs a (Finset.mem_cons_self a u)) (isPositive_sum u hsu)
            (hsup a (Finset.mem_cons_self a u)) hsupU
      _ ≤ quantumRelativeEntropy (r a) (s a) + ∑ i ∈ u, quantumRelativeEntropy (r i) (s i) := by
          have := ih hru hsu hsupu; linarith

/-- **Mixture bound for the generalized relative entropy for positive operators** (N&C Problem
11.2(4), eq. (11.134), faithful form). For positive families `r, s` on the finite branch
`(r i).HasSupportLE (s i)`, positive weights `p, q` (`0 < pᵢ`, `0 < qᵢ`) on a nonempty index
`Finset t`,
`S(∑ᵢ pᵢ • rᵢ ‖ ∑ᵢ qᵢ • sᵢ) ≤ ∑ᵢ pᵢ · S(rᵢ ‖ sᵢ) + ∑ᵢ pᵢ · tr(rᵢ) · log(pᵢ / qᵢ)`,
where `tr(rᵢ)` is `re tr(rᵢ)`. Faithful n-ary subadditivity
(`quantumRelativeEntropy_sum_le_sum_of_hasSupportLE`) applied to the positive `pᵢ • rᵢ`, `qᵢ • sᵢ`
(each `(pᵢ • rᵢ).HasSupportLE (qᵢ • sᵢ)` from `hasSupportLE_smul_smul`) bounds the left-hand side by
`∑ᵢ S(pᵢ • rᵢ ‖ qᵢ • sᵢ)`, and the faithful scaling law
(`quantumRelativeEntropy_smul_smul_of_hasSupportLE`) rewrites each summand. Strengthens
`quantumRelativeEntropy_sum_smul_smul_le` from strict positivity to the full positive-operator
finite branch. As there, the bound needs only `pᵢ, qᵢ > 0`, not the normalization
`∑ pᵢ = ∑ qᵢ = 1`, so this is the stronger positive-weight form. -/
theorem quantumRelativeEntropy_sum_smul_smul_le_of_hasSupportLE {κ : Type*} {t : Finset κ}
    (ht : t.Nonempty) {r s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} {p q : κ → ℝ}
    (hr : ∀ i ∈ t, (r i).IsPositive) (hs : ∀ i ∈ t, (s i).IsPositive)
    (hsup : ∀ i ∈ t, (r i).HasSupportLE (s i))
    (hp : ∀ i ∈ t, 0 < p i) (hq : ∀ i ∈ t, 0 < q i) :
    quantumRelativeEntropy (∑ i ∈ t, p i • r i) (∑ i ∈ t, q i • s i) ≤
      (∑ i ∈ t, p i * quantumRelativeEntropy (r i) (s i)) +
        ∑ i ∈ t, p i * RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (r i).toLinearMap) *
          Real.log (p i / q i) := by
  refine (quantumRelativeEntropy_sum_le_sum_of_hasSupportLE ht
    (fun i hi => (hr i hi).smul_real_of_nonneg (hp i hi).le)
    (fun i hi => (hs i hi).smul_real_of_nonneg (hq i hi).le)
    (fun i hi => hasSupportLE_smul_smul (hp i hi).ne' (hq i hi).ne' (hsup i hi))).trans
    (le_of_eq ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    quantumRelativeEntropy_smul_smul_of_hasSupportLE (hr i hi) (hs i hi) (hsup i hi)
      (hp i hi) (hq i hi)

/-- **The "pretty formula" for the mixture bound, faithful form** (N&C Problem 11.2(4), eq.
(11.135)). When the `rᵢ` are density operators (`re tr(rᵢ) = 1`), the mixture-bound correction term
collapses to the classical relative entropy (Kullback–Leibler divergence)
`Real.relativeEntropy p q = ∑ᵢ pᵢ log(pᵢ / qᵢ)` of the weight distributions:
`S(∑ᵢ pᵢ • rᵢ ‖ ∑ᵢ qᵢ • sᵢ) ≤ ∑ᵢ pᵢ · S(rᵢ ‖ sᵢ) + D(p ‖ q)`, for positive families on the finite
branch `(r i).HasSupportLE (s i)`. Stated over `Finset.univ` of a nonempty `Fintype κ`, matching the
index range of `Real.relativeEntropy`; per-term, `re tr(rᵢ) = 1` and
`log(pᵢ / qᵢ) = log pᵢ − log qᵢ` (`Real.log_div`, valid since `pᵢ, qᵢ > 0`) turn the correction into
`∑ᵢ pᵢ (log pᵢ − log qᵢ)`. Strengthens
`quantumRelativeEntropy_sum_smul_smul_le_relativeEntropy` to the full positive-operator finite
branch. -/
theorem quantumRelativeEntropy_sum_smul_smul_le_relativeEntropy_of_hasSupportLE {κ : Type*}
    [Fintype κ] [Nonempty κ] {r s : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} {p q : κ → ℝ}
    (hr : ∀ i, (r i).IsPositive) (hs : ∀ i, (s i).IsPositive)
    (hsup : ∀ i, (r i).HasSupportLE (s i)) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (htr : ∀ i, RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι) (r i).toLinearMap) = 1) :
    quantumRelativeEntropy (∑ i, p i • r i) (∑ i, q i • s i) ≤
      (∑ i, p i * quantumRelativeEntropy (r i) (s i)) + Real.relativeEntropy p q := by
  refine (quantumRelativeEntropy_sum_smul_smul_le_of_hasSupportLE Finset.univ_nonempty
    (fun i _ => hr i) (fun i _ => hs i) (fun i _ => hsup i) (fun i _ => hp i)
    (fun i _ => hq i)).trans (le_of_eq ?_)
  rw [Real.relativeEntropy_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [htr i, mul_one, Real.log_div (hp i).ne' (hq i).ne']

end ContinuousLinearMap
