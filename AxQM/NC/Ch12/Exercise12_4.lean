/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChi
import AxQM.NC.Ch12.Problem12_1
import AxQM.Postulates.API.QubitSuperpositionMatrix
import AxQM.Postulates.API.BellReducedState
import AxQM.Postulates.API.EntropyComposite
import AxQM.Postulates.API.FidelityPure
import AxQM.Postulates.API.BlochHSOverlap
import AxQM.Concrete.SICQubitEnsemble
import ToMathlib.InformationTheory.Fano
import ToMathlib.InformationTheory.ConditionalCollisionEntropy

/-!
# Nielsen & Chuang, Exercise 12.4 (the tetrahedral / SIC qubit ensemble)

*(N&C p. 535.)*

For four given pure states, show max mutual info < 1 bit; construct achieving POVM.

The four states are the **tetrahedral (symmetric informationally complete, SIC) qubit ensemble**:
their Bloch vectors are the vertices of a regular tetrahedron `(0,0,1)` and three points at latitude
`z = -1/3`, which sum to zero. Consequently the equal mixture is the **maximally mixed state**
`ρ = ¼∑ₓ|Xₓ⟩⟨Xₓ| = I/2`, and the **Holevo χ quantity** of the ensemble is
`χ = S(ρ) − ∑ₓ ¼·S(|Xₓ⟩⟨Xₓ|) = S(I/2) − 0 = log 2` — exactly **one bit** (in nats, `log 2`).

## What is formalised here

* `sicQubitState` — the four pure states `|X₁⟩, …, |X₄⟩` as a family `Fin 4 → PureState qubit`,
  built from the concrete amplitude vectors `Concrete.sicKet` via `qubitSuperposition`.
* `sicQubitState_mix_eq_maximallyMixed` — the equal mixture `¼∑ₓ|Xₓ⟩⟨Xₓ|` is the maximally mixed
  state `I/2` (the tetrahedron is balanced, i.e. **informationally complete**). Its proof reduces to
  the matrix identity `Concrete.sicOuterSelf_sum` (`∑ₓ ¼|Xₓ⟩⟨Xₓ| = ½I`), whose off-diagonal vanishes
  because `1 + ω + ω² = 0` for `ω = e^{2πi/3}`.
* `sicQubitState_fidelity_eq_of_ne` / `sicQubitState_hsOverlap_eq_of_ne` — the ensemble is
  **symmetric**: the pairwise fidelity is the constant `F(Xᵢ, Xⱼ) = 1/√3` and the Hilbert–Schmidt
  overlap is `Tr(ρᵢ ρⱼ) = 1/3` (`= 1/(d+1)`, `d = 2`) for `i ≠ j`. In particular `0 < 1/√3 < 1`, so
  the four states are pairwise **non-orthogonal** — the property that obstructs saturation of the
  Holevo bound and underlies the exercise's *strict* cap.
* `holevoChi_sicQubitState_eq_log_two` — the Holevo χ of the ensemble is `log 2` (one bit).
* `mutualInfo_sicQubitState_le_log_two` — for *any* measurement `m`, the mutual information
  `H(X : Y) ≤ log 2`: the **Holevo bound** (N&C Theorem 12.1) `H(X : Y) ≤ χ` instantiated at this
  ensemble, `χ = log 2`.
* `sicQubitState_bornProb_sq_sum_le` — the **per-outcome Born collision bound**: for any
  measurement `m` and outcome `u`, `∑ₓ (m.bornProb ρₓ u)² ≤ ⅓·(∑ₓ m.bornProb ρₓ u)²`, i.e. the
  conditional collision probability `∑ₓ p(x|u)² ≤ ⅓`. This is the sharp ensemble-specific input to
  the strict cap (below), obtained from the SIC tight-frame/2-design inequality
  `Concrete.sicKet_quadForm_re_sq_sum_le`.
* `mutualInfo_sicQubitState_le_log_four_div_three` — the **sharp** accessible-information cap: for
  *any* measurement `m`, `H(X : Y) ≤ log(4/3)` (`≈ 0.415` bits, the known optimum the exercise
  mentions). This is the maximum over all measurements, bounded uniformly.
* `mutualInfo_sicQubitState_lt_log_two` — **the headline of Exercise 12.4**: for *any* measurement
  `m`, `H(X : Y) < log 2`; i.e. the maximum mutual information is *strictly* less than one bit.

## The strict cap (headline of the exercise), and what is not formalised

The exercise's headline — *the maximum over all measurements of `H(X : Y)` is strictly less than
one bit* — is `mutualInfo_sicQubitState_lt_log_two`: the cap `H(X : Y) < log 2` holds for *every*
measurement `m` (of arbitrarily many outcomes), so the maximum is strictly below `log 2` with no
explicit supremum needed.

It is proved by the **elementary collision-entropy route** (SIC 2-design), self-contained and
avoiding the general Holevo/χ-monotonicity *equality* condition:
`H(X : Y) = H(X) − H(X | Y) = log 4 − H(X | Y)`, and for *every* outcome `u` the conditional
collision probability `∑ₓ p(x|u)² ≤ ⅓` (`sicQubitState_bornProb_sq_sum_le`) forces
`H(X | Y = u) ≥ log 3` (Shannon ≥ Rényi-2 collision entropy,
`Real.log_collisionProb_inv_le_entropy`), hence `H(X | Y) ≥ log 3` (chain rule
`Real.condEntropy_eq_sum_marginalSnd_mul_entropy`) and
`H(X : Y) ≤ log(4/3) < log 2` (`mutualInfo_sicQubitState_le_log_four_div_three`). The cap
`log(4/3)` (`≈ 0.415` bits) is exactly the known optimum the exercise names, so the bound is sharp.

The exercise's closing question — *"Can you construct [the ≈ 0.415-bit POVM] or, better yet, one
which achieves the Holevo bound?"* — is an open-ended constructive aside, not the proposition to
prove; it is not formalised here. (A Holevo-achieving POVM is in fact impossible for this ensemble:
the states are pairwise non-orthogonal, `sicQubitState_fidelity_eq_of_ne`, which is precisely what
makes the cap strict. Exhibiting a specific POVM that attains `log(4/3)` would be a separate
construction; the sharp *upper* bound above already certifies `log(4/3)` as the optimum.)
-/

open Complex Matrix

namespace AxQM

/-- The four pure states of Nielsen & Chuang Exercise 12.4 as a family `Fin 4 → PureState qubit`:
`|X₁⟩ = |0⟩` and `|Xₖ₊₁⟩ = √(1/3)(|0⟩ + √2 e^{2πik/3}|1⟩)`, `k = 0, 1, 2`. They are the tetrahedral
(SIC) qubit states, built from the concrete amplitude vectors `Concrete.sicKet` via
`qubitSuperposition` (which discharges normalisation, `Concrete.sicKet_normSq`). -/
noncomputable def sicQubitState (k : Fin 4) : PureState qubit :=
  qubitSuperposition (Concrete.sicKet k 0) (Concrete.sicKet k 1) (Concrete.sicKet_normSq k)

/-- The uniform (equal-weight) distribution `¼` over the four SIC states — Alice's "equal mixture".
Written point-free as `Function.const` (each of the four states carries probability `¼`). -/
noncomputable def sicProb : Fin 4 → ℝ := Function.const _ 4⁻¹

/-- The SIC weights are non-negative. -/
lemma sicProb_nonneg (k : Fin 4) : 0 ≤ sicProb k := by norm_num [sicProb, Function.const_apply]

/-- The SIC weights sum to one. -/
lemma sicProb_sum : ∑ k, sicProb k = 1 := by
  simp only [sicProb, Function.const_apply, Fin.sum_univ_four]; norm_num

/-- **The equal mixture of the four tetrahedral (SIC) states is the maximally mixed state `I/2`.**
`¼∑ₓ|Xₓ⟩⟨Xₓ| = I/2` (Nielsen & Chuang, Exercise 12.4). The four Bloch vectors form a regular
tetrahedron summing to zero, so the average density operator is maximally mixed. The proof passes to
matrices: each projector `|Xₓ⟩⟨Xₓ|` is `Matrix.toEuclideanCLM (Concrete.outerSelf ![·, ·])`
(`qubitSuperposition_toState_op`), the weighted sum is the matrix identity
`Concrete.sicOuterSelf_sum` (`∑ₓ ¼|Xₓ⟩⟨Xₓ| = ½I`, off-diagonal killed by `1 + ω + ω² = 0`), and
`maximallyMixedState_qubit_op`
identifies `(I/2).op` with `½·1`. -/
theorem sicQubitState_mix_eq_maximallyMixed :
    State.mix sicProb sicProb_nonneg sicProb_sum (fun k => (sicQubitState k).toState)
      = maximallyMixedState qubit := by
  apply State.ext
  have hmix : (State.mix sicProb sicProb_nonneg sicProb_sum
        (fun k => (sicQubitState k).toState)).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (∑ k : Fin 4, (4 : ℂ)⁻¹ •
            Concrete.outerSelf ![Concrete.sicKet k 0, Concrete.sicKet k 1]) := by
    rw [State.mix_op, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [sicQubitState]
    rw [map_smul, qubitSuperposition_toState_op]
    congr 1
    simp only [sicProb, Function.const_apply, Complex.ofReal_inv]
    norm_num
  have hmm : (maximallyMixedState qubit).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) ((2 : ℂ)⁻¹ • 1) := by
    rw [maximallyMixedState_qubit_op, map_smul, map_one]
    rfl
  rw [hmix, hmm, Concrete.sicOuterSelf_sum]

/-- **Nielsen & Chuang, Exercise 12.4: the Holevo χ of the tetrahedral (SIC) ensemble is one bit.**
`χ({¼, |Xₓ⟩}) = log 2`. Since the four states are pure, `χ` equals the entropy of the mixture
(`State.holevoChi_pure`), which is `S(I/2) = log (dim qubit) = log 2`
(`sicQubitState_mix_eq_maximallyMixed`, `State.vonNeumannEntropy_maximallyMixed`,
`finrank_qubit_space`). Combined with the Holevo bound `H(X : Y) ≤ χ` (N&C Theorem 12.1), this caps
the mutual information any measurement can extract at one bit. Entropies are in nats (`Real.log`);
`log 2` nats is one bit. -/
theorem holevoChi_sicQubitState_eq_log_two :
    State.holevoChi sicProb sicProb_nonneg sicProb_sum (fun k => (sicQubitState k).toState)
      = Real.log 2 := by
  rw [State.holevoChi_pure, sicQubitState_mix_eq_maximallyMixed,
    State.vonNeumannEntropy_maximallyMixed, finrank_qubit_space]
  norm_num

/-- **Nielsen & Chuang, Exercise 12.4: the accessible-information cap `H(X : Y) ≤ log 2`.**
For *any* measurement `m` Bob performs on Alice's transmission, the classical mutual information
between Bob's outcome `Y` and Alice's choice `X` (uniform over the four tetrahedral/SIC states
`|Xₓ⟩`) is at most one bit:

`H(X : Y) ≤ log 2`.

This is the **Holevo bound** (N&C Theorem 12.1) instantiated at the SIC ensemble —
`H(X : Y) ≤ χ` — together with `χ = log 2` for these states (`holevoChi_sicQubitState_eq_log_two`,
the average state being maximally mixed `I/2` with pure, zero-entropy components). Since the bound
holds for *every* measurement `m` (of arbitrarily many outcomes `Fin r`), the statement is exactly
"the **maximum** mutual information any measurement can extract is at most one bit" — the achievable
half of Exercise 12.4's claim. Entropies are in nats (`Real.log`); one bit is `log 2` nats.

The proof is a direct composition `H(X : Y) ≤ χ ≤ log 2`: the χ-form Holevo bound
`holevoBound_of_chi_monotone` (`H(X : Y) ≤ State.holevoChi …`, N&C Problem 12.1's assembled bound)
chained with the ensemble value `χ = log 2` (`holevoChi_sicQubitState_eq_log_two`).

This `≤ log 2` cap is the **Holevo-route** sub-fact; the exercise's *strict* headline
`H(X : Y) < log 2` (and the sharp `≤ log(4/3)`, the ≈ 0.415-bit optimum) is proved below by the
collision-entropy route in `mutualInfo_sicQubitState_lt_log_two` and
`mutualInfo_sicQubitState_le_log_four_div_three`, which supersede this bound. It is retained as the
clean Holevo instantiation and as the `χ = log 2` witness. -/
theorem mutualInfo_sicQubitState_le_log_two {r : ℕ} [NeZero r] (m : Measurement (Fin r) qubit) :
    Real.mutualInfo (fun xy : Fin 4 × Fin r =>
        sicProb xy.1 * m.bornProb (sicQubitState xy.1).toState xy.2) ≤ Real.log 2 :=
  (holevoBound_of_chi_monotone sicProb sicProb_nonneg sicProb_sum
    (fun k => (sicQubitState k).toState) m).trans holevoChi_sicQubitState_eq_log_two.le

/-- **The four tetrahedral (SIC) states have constant pairwise fidelity `F(Xᵢ, Xⱼ) = 1/√3`.**
For `i ≠ j`, the fidelity between the distinct SIC/tetrahedral qubit states is exactly `(√3)⁻¹`
(Nielsen & Chuang, Exercise 12.4). This is the defining **symmetric** property of the ensemble — the
constant overlap `|⟨Xᵢ|Xⱼ⟩| = 1/√(d+1) = 1/√3` in dimension `d = 2` (its Bloch vectors are the
vertices of a regular tetrahedron). Since `0 < 1/√3 < 1`, the states are pairwise **non-orthogonal**
yet distinct: this is exactly the obstruction to saturating the Holevo bound
(`mutualInfo_sicQubitState_le_log_two`), and hence the ensemble-specific input to the exercise's
**strict** cap `H(X : Y) < log 2` (see the module docstring).

The proof reads the fidelity off the amplitudes: `F(Xᵢ, Xⱼ) = ‖⟨Xᵢ|Xⱼ⟩‖`
(`fidelity_toState_toState`), the overlap is `conj(Xᵢ)₀·(Xⱼ)₀ + conj(Xᵢ)₁·(Xⱼ)₁`
(`qubitSuperposition_inner`), and its squared modulus is `1/3`
(`Concrete.sicKet_overlap_normSq_of_ne`), so `‖⟨Xᵢ|Xⱼ⟩‖ = √(1/3) = 1/√3`. -/
theorem sicQubitState_fidelity_eq_of_ne {i j : Fin 4} (h : i ≠ j) :
    (sicQubitState i).toState.fidelity (sicQubitState j).toState = (Real.sqrt 3)⁻¹ := by
  rw [State.fidelity_toState_toState]
  simp only [sicQubitState]
  rw [qubitSuperposition_inner, ← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    Concrete.sicKet_overlap_normSq_of_ne h, one_div, Real.sqrt_inv]

/-- **The tetrahedral (SIC) states have constant Hilbert–Schmidt overlap `Tr(ρᵢ ρⱼ) = 1/3`.**
For `i ≠ j`, `hsOverlap(|Xᵢ⟩⟨Xᵢ|, |Xⱼ⟩⟨Xⱼ|) = 1/3` (Nielsen & Chuang, Exercise 12.4) — the
trace-form of the symmetric-informationally-complete condition `Tr(ρᵢ ρⱼ) = 1/(d+1) = 1/3`. It is
the square of the fidelity (`fidelity_toState_sq_eq_hsOverlap`, `sicQubitState_fidelity_eq_of_ne`):
`(1/√3)² = 1/3`. Being nonzero, it again records the pairwise non-orthogonality of the states. -/
theorem sicQubitState_hsOverlap_eq_of_ne {i j : Fin 4} (h : i ≠ j) :
    (sicQubitState i).toState.hsOverlap (sicQubitState j).toState = 1 / 3 := by
  rw [← State.fidelity_toState_sq_eq_hsOverlap, sicQubitState_fidelity_eq_of_ne h, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

open scoped ComplexOrder in
/-- **Nielsen & Chuang, Exercise 12.4: the per-outcome Born collision bound.**
For *any* measurement `m` Bob performs (with an arbitrary finite outcome set `ι`) and *any* fixed
outcome `u`, the four transition probabilities `p(u|x) = ⟨Xₓ|Eᵤ|Xₓ⟩ = m.bornProb ρₓ u` of the
tetrahedral/SIC ensemble satisfy the **collision inequality**

`∑ₓ (m.bornProb (sicQubitState x).toState u)² ≤ ⅓·(∑ₓ m.bornProb (sicQubitState x).toState u)²`.

Equivalently, conditioned on outcome `u` the collision probability `∑ₓ p(x|u)²` is at most `⅓`
(`= 1/(d+1)`, `d = 2`), so no measurement outcome can make Alice's four equally-likely inputs more
than `⅓`-collision-concentrated. This is the sharp ensemble-specific input to the exercise's
*strict* accessible-information cap `H(X : Y) < log 2` (it forces conditional entropy `≥ log 3`,
hence `H(X : Y) ≤ log(4/3) < log 2`) — the deeper bound behind the ≈ 0.415-bit optimum.

The proof bridges the physics to the concrete SIC tight-frame/2-design inequality
`Concrete.sicKet_quadForm_re_sq_sum_le`. Writing `Eᵤ = Mᵤ†Mᵤ` for the (positive) POVM element of
outcome `u` and `M` for its `2×2` matrix (`M = toEuclideanCLM⁻¹ Eᵤ`, positive-semidefinite via
`isPositive_adjoint_comp_self` + `isPositive_toEuclideanCLM_iff`), each Born probability reads as
the matrix quadratic form `m.bornProb ρₓ u = Re⟨Xₓ|M|Xₓ⟩` (`bornProb_eq_re_trace_postOp`,
`qubitSuperposition_toState_op`, `trace_toEuclideanCLM`, `Concrete.trace_mul_outerSelf`), and the
tetrahedral resolution `∑ₓ|Xₓ⟩⟨Xₓ| = 2·I` gives `∑ₓ m.bornProb ρₓ u = 2·Re(Tr M)`
(`Concrete.sicKet_quadForm_sum_eq_trace`). The concrete bound `∑ₓ⟨Xₓ|M|Xₓ⟩² ≤ 4/3·(Tr M)²` is then
`⅓·(2·Re Tr M)²`. -/
theorem sicQubitState_bornProb_sq_sum_le {ι : Type*} [Fintype ι]
    (m : Measurement ι qubit) (u : ι) :
    ∑ x, m.bornProb (sicQubitState x).toState u ^ 2
      ≤ 1 / 3 * (∑ x, m.bornProb (sicQubitState x).toState u) ^ 2 := by
  -- The POVM element `Eᵤ = Mᵤ†Mᵤ` and its positive-semidefinite matrix `M`.
  set E := (ContinuousLinearMap.adjoint (m.op u)).comp (m.op u) with hE
  have hEpos : E.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self (m.op u)
  obtain ⟨M, hME⟩ : ∃ M : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M = E :=
    ⟨(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).symm E,
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).apply_symm_apply E⟩
  have hMpsd : M.PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanCLM_iff, hME]; exact hEpos
  -- Each Born probability is the concrete quadratic form `Re⟨Xₓ|M|Xₓ⟩`.
  have hbridge : ∀ x, m.bornProb (sicQubitState x).toState u
      = (star (Concrete.sicKet x) ⬝ᵥ M.mulVec (Concrete.sicKet x)).re := by
    intro x
    have hop : (sicQubitState x).toState.op
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
            (Concrete.outerSelf (Concrete.sicKet x)) := by
      rw [sicQubitState, qubitSuperposition_toState_op, Concrete.sicKet_eta]
    -- `Eᵤ · ρₓ = toEuclideanCLM (M · |Xₓ⟩⟨Xₓ|)` (algebra-hom, composition = matrix product).
    have hcomp : E.comp (sicQubitState x).toState.op
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
            (M * Concrete.outerSelf (Concrete.sicKet x)) := by
      rw [hop, ← hME]
      exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) M _).symm
    -- `Tr(Eᵤ · ρₓ) = ⟨Xₓ|M|Xₓ⟩` (`Tr` over `qubit.space` is the matrix trace, the space being
    -- `EuclideanSpace ℂ (Fin 2)`; the `exact` closes the `qubit.space ≡ EuclideanSpace` defeq).
    have hkey : (LinearMap.trace ℂ qubit.space) ↑(E.comp (sicQubitState x).toState.op)
        = star (Concrete.sicKet x) ⬝ᵥ M.mulVec (Concrete.sicKet x) := by
      have h1 : (LinearMap.trace ℂ qubit.space) ↑(E.comp (sicQubitState x).toState.op)
          = (M * Concrete.outerSelf (Concrete.sicKet x)).trace := by
        rw [hcomp]; exact Matrix.trace_toEuclideanCLM _
      rw [h1, Concrete.trace_mul_outerSelf]
    rw [Measurement.bornProb_eq_re_trace_postOp, ContinuousLinearMap.trace_postOp,
      ← ContinuousLinearMap.comp_assoc, ← hE, hkey]
    rfl
  -- The total weight `∑ₓ p(u|x)` is `2·Re(Tr M)` (tetrahedral resolution `∑ₓ|Xₓ⟩⟨Xₓ| = 2·I`).
  have hsum : ∑ x, (star (Concrete.sicKet x) ⬝ᵥ M.mulVec (Concrete.sicKet x)).re
      = 2 * (M.trace).re := by
    rw [← Complex.re_sum, Concrete.sicKet_quadForm_sum_eq_trace, Complex.mul_re]; simp
  -- Assemble against the concrete tight-frame collision inequality.
  simp only [hbridge]
  rw [hsum]
  have hcoll := Concrete.sicKet_quadForm_re_sq_sum_le M hMpsd
  have harith : (1 : ℝ) / 3 * (2 * (M.trace).re) ^ 2 = 4 / 3 * (M.trace).re ^ 2 := by ring
  rw [harith]; exact hcoll

/-- **Nielsen & Chuang, Exercise 12.4: the sharp accessible-information cap `H(X : Y) ≤ log(4/3)`.**
For *any* measurement `m` Bob performs on Alice's transmission (an arbitrary finite outcome set
`ι`), the classical mutual information between Bob's outcome `Y` and Alice's uniformly-chosen state
`X ∈ {|Xₓ⟩}` (the four tetrahedral/SIC qubit states) is at most `log(4/3)`:

`H(X : Y) ≤ log(4/3)`  (`≈ 0.415` bits).

Since the bound holds for *every* `m`, this is exactly "the **maximum** mutual information any
measurement can extract is `≤ log(4/3)`", and `log(4/3)` is precisely the `≈ 0.415`-bit optimum the
exercise mentions. Together with `mutualInfo_sicQubitState_lt_log_two` (`log(4/3) < log 2`) it
delivers the exercise's headline: the accessible information is *strictly* less than one bit.

The proof is the elementary collision-entropy / SIC 2-design route, uniform over all measurements
(no accessible-information optimisation, no Holevo-equality condition). Write the joint law
`p(x, y) = ¼·m.bornProb ρₓ y`. Then `H(X : Y) = H(X) − H(X | Y)`
(`Real.mutualInfo_eq_entropy_marginalFst_sub_condEntropy`) with:
* `H(X) = log 4`: the first marginal `p_X = ¼` is uniform on the four states
  (`m.sum_bornProb_eq_one`, `Real.entropy_uniform`).
* `H(X | Y) ≥ log 3`: by the chain rule `H(X | Y) = ∑ᵤ p_Y(u)·H(X | Y = u)`
  (`Real.condEntropy_eq_sum_marginalSnd_mul_entropy`), for *every* outcome `u` the conditional
  collision probability `∑ₓ p(x | u)² ≤ ⅓` — the per-outcome Born collision bound
  `sicQubitState_bornProb_sq_sum_le` transported to the posterior via
  `Real.marginalSnd_sq_mul_condCollisionProb` — so `H(X | Y = u) ≥ log((∑ₓ p(x|u)²)⁻¹) ≥ log 3`
  (Shannon ≥ Rényi-2, `Real.log_collisionProb_inv_le_entropy`); averaging with `∑ᵤ p_Y(u) = 1`
  gives `H(X | Y) ≥ log 3`.

Hence `H(X : Y) ≤ log 4 − log 3 = log(4/3)`. Entropies are in nats (`Real.log`); one bit is
`log 2` nats. -/
theorem mutualInfo_sicQubitState_le_log_four_div_three {ι : Type*} [Fintype ι]
    (m : Measurement ι qubit) :
    Real.mutualInfo (fun xy : Fin 4 × ι =>
        sicProb xy.1 * m.bornProb (sicQubitState xy.1).toState xy.2) ≤ Real.log (4 / 3) := by
  set p : Fin 4 × ι → ℝ :=
    fun xy => sicProb xy.1 * m.bornProb (sicQubitState xy.1).toState xy.2 with hpdef
  have hp_nonneg : ∀ q, 0 ≤ p q := fun q =>
    mul_nonneg (sicProb_nonneg _) (m.bornProb_nonneg _ _)
  -- `H(X) = log 4`: the first marginal is uniform on the four states.
  have hmarg : Real.marginalFst p = fun _ => ((Fintype.card (Fin 4) : ℝ))⁻¹ := by
    funext x
    rw [Real.marginalFst_apply]
    simp only [hpdef, sicProb, Function.const_apply, Fintype.card_fin, Nat.cast_ofNat]
    rw [← Finset.mul_sum, m.sum_bornProb_eq_one, mul_one]
  have hHX : Real.entropy (Real.marginalFst p) = Real.log 4 := by
    rw [hmarg, Real.entropy_uniform, Fintype.card_fin]; norm_num
  -- `p` is a probability distribution: total mass and second-marginal mass are `1`.
  have htot : ∑ q, p q = 1 := by
    rw [Fintype.sum_prod_type]
    have hfib : ∀ x : Fin 4, ∑ u, p (x, u) = sicProb x := by
      intro x
      simp only [hpdef]
      rw [← Finset.mul_sum, m.sum_bornProb_eq_one, mul_one]
    rw [Finset.sum_congr rfl fun x _ => hfib x, sicProb_sum]
  have hms1 : ∑ u, Real.marginalSnd p u = 1 := by rw [Real.sum_marginalSnd, htot]
  -- The ensemble-specific input: every outcome `u` has conditional collision probability `≤ ⅓`.
  have hcc_le : ∀ u, Real.condCollisionProb p u ≤ 1 / 3 := by
    intro u
    rcases eq_or_ne (Real.marginalSnd p u) 0 with hu | hu
    · -- Zero-marginal outcome: the conditional distribution is `0`, so its collision prob is `0`.
      have hz : Real.condCollisionProb p u = 0 := by
        have hd : Real.condDistribGivenSnd p u = fun _ => (0 : ℝ) := by
          funext x; rw [Real.condDistribGivenSnd_apply, hu, div_zero]
        unfold Real.condCollisionProb
        rw [hd, Real.collisionProb_eq]; simp
      rw [hz]; norm_num
    · -- `∑ₓ p(x|u)² ≤ ⅓`: transport the Born collision bound `sicQubitState_bornProb_sq_sum_le`
      -- to the posterior via `marginalSnd_sq_mul_condCollisionProb`.
      have hkey := Real.marginalSnd_sq_mul_condCollisionProb hp_nonneg u
      have hpx2 : ∑ x, p (x, u) ^ 2
          = (4 : ℝ)⁻¹ ^ 2 * ∑ x, m.bornProb (sicQubitState x).toState u ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [hpdef, sicProb, Function.const_apply]; ring
      have hms : Real.marginalSnd p u
          = (4 : ℝ)⁻¹ * ∑ x, m.bornProb (sicQubitState x).toState u := by
        rw [Real.marginalSnd_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [hpdef, sicProb, Function.const_apply]
      have hborn := sicQubitState_bornProb_sq_sum_le m u
      have hpos : 0 < Real.marginalSnd p u ^ 2 :=
        pow_pos (lt_of_le_of_ne (Real.marginalSnd_nonneg hp_nonneg u) (Ne.symm hu)) 2
      have hbound : Real.marginalSnd p u ^ 2 * Real.condCollisionProb p u
          ≤ Real.marginalSnd p u ^ 2 * (1 / 3) := by
        rw [hkey, hpx2, hms, mul_comm _ (1 / 3 : ℝ)]
        calc (4 : ℝ)⁻¹ ^ 2 * ∑ x, m.bornProb (sicQubitState x).toState u ^ 2
            ≤ (4 : ℝ)⁻¹ ^ 2 *
                (1 / 3 * (∑ x, m.bornProb (sicQubitState x).toState u) ^ 2) :=
              mul_le_mul_of_nonneg_left hborn (by positivity)
          _ = 1 / 3 * ((4 : ℝ)⁻¹ * ∑ x, m.bornProb (sicQubitState x).toState u) ^ 2 := by ring
      exact le_of_mul_le_mul_left hbound hpos
  -- `H(X | Y) ≥ log 3`: the general conditional-collision → conditional-entropy bound
  -- `Real.log_inv_le_condEntropy_of_condCollisionProb_le` at `c = ⅓` (`(⅓)⁻¹ = 3`); only the
  -- ensemble-specific `hcc_le` is SIC-particular, the averaging skeleton is a `ToMathlib` lemma.
  have hcond : Real.log 3 ≤ Real.condEntropy p := by
    have h := Real.log_inv_le_condEntropy_of_condCollisionProb_le hp_nonneg hms1 hcc_le
    rwa [show (1 / 3 : ℝ)⁻¹ = 3 by norm_num] at h
  -- Assemble: `H(X : Y) = H(X) − H(X | Y) ≤ log 4 − log 3 = log(4/3)`.
  rw [Real.mutualInfo_eq_entropy_marginalFst_sub_condEntropy, hHX,
    show Real.log (4 / 3) = Real.log 4 - Real.log 3 from Real.log_div (by norm_num) (by norm_num)]
  linarith

/-- **Nielsen & Chuang, Exercise 12.4 (headline): the maximum mutual information is *strictly* less
than one bit.** For *any* measurement `m` (arbitrary finite outcome set `ι`),

`H(X : Y) < log 2`,

where `X` is Alice's uniform choice among the four tetrahedral/SIC states `|Xₓ⟩` and `Y` is Bob's
outcome. As this holds for every `m`, the *maximum over all measurements* of the accessible
information is strictly below one bit — the exact claim of Exercise 12.4.

Immediate from the sharp cap `H(X : Y) ≤ log(4/3)`
(`mutualInfo_sicQubitState_le_log_four_div_three`) and `log(4/3) < log 2` (as `4/3 < 2`). The strict
gap is the quantitative signature of the pairwise **non-orthogonality** of the SIC states
(`sicQubitState_fidelity_eq_of_ne`: constant fidelity `1/√3 ∈ (0, 1)`), which obstructs saturation
of the Holevo bound. Entropies are in nats; one bit is `log 2` nats. -/
theorem mutualInfo_sicQubitState_lt_log_two {ι : Type*} [Fintype ι]
    (m : Measurement ι qubit) :
    Real.mutualInfo (fun xy : Fin 4 × ι =>
        sicProb xy.1 * m.bornProb (sicQubitState xy.1).toState xy.2) < Real.log 2 :=
  (mutualInfo_sicQubitState_le_log_four_div_three m).trans_lt
    (Real.log_lt_log (by norm_num) (by norm_num))

end AxQM
