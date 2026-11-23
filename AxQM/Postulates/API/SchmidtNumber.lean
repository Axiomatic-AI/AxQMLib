/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite
import AxQM.Postulates.API.Purity
import AxQM.Postulates.API.SchmidtDecomposition
import ToMathlib.Analysis.InnerProductSpace.Matricization
import ToMathlib.Analysis.InnerProductSpace.MatricizationRank
import ToMathlib.Analysis.InnerProductSpace.SingularValues
import ToMathlib.Analysis.InnerProductSpace.Dual
import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# AxQM — the Schmidt number of a bipartite pure state 

The **Schmidt number** of a pure state `ψ` of a composite system `S ⊗ T`
(Nielsen–Chuang §2.5): the number of non-zero *Schmidt coefficients* in the
Schmidt decomposition `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩` (N&C Theorem 2.7). The Schmidt
coefficients are exactly the singular values of the *coefficient operator*
`M = matricize ψ.vec : T.space →L S.space` — the linear map whose matrix in fixed
orthonormal bases is the coefficient array `a` with `ψ = ∑ⱼₖ aⱼₖ |j⟩|k⟩` — so the
Schmidt number is the number of non-zero singular values of `M`.

Defining it directly from the singular values (rather than as the rank of the
reduced density operator) keeps **Problem 2.2(1)** — *the Schmidt number equals
the rank of `ρᴬ`* — a genuine theorem rather than a definitional tautology.

The statements about them (Problem 2.2) are in `AxQM/NC/Ch2/Problem2_2.lean`.

## Main definitions

* `AxQM.PureState.schmidtNumber` — the Schmidt number of a bipartite pure
  state (number of non-zero singular values of the matricized coefficient operator).
* `AxQM.State.rank` — the rank of a (density-operator) state: the dimension
  of the range of its operator.

## Main results

* `PureState.schmidtNumber_eq_finrank_range_matricize` — the Schmidt number equals
  the rank (`finrank` of range) of the matricized coefficient operator.
* `PureState.reducedLeft_toState_op` — the `_op` bridge `ρᴬ = M Mᵀ` for the left
  reduced state (`partialTraceRight_rankOne_self`); citable, reused by Parts 2/3.
* `State.rank_reducedLeft_toState_eq_finrank_range_matricize` — the rank of the left
  reduced state `ρᴬ = tr_B(|ψ⟩⟨ψ|)` equals the same rank, via `reducedLeft_toState_op`
  and `range (M Mᵀ) = range M`.
* `PureState.schmidtNumber_le_card_of_sum_tmul` — **Problem 2.2(2)**: if `|ψ⟩ = ∑ⱼ |αⱼ⟩|βⱼ⟩`
  is a product decomposition into `s.card` (un-normalized) terms, then `Sch(ψ) ≤ s.card`.
  The hypothesis is an equation between the state vectors.
* `PureState.natAbs_sub_schmidtNumber_le` — **Problem 2.2(3)**: if `|ψ⟩ = α|φ⟩ + β|γ⟩` with
  `α, β ≠ 0`, then `Sch(ψ) ≥ |Sch(φ) − Sch(γ)|` (a reverse-triangle bound). The nonzero
  amplitudes are a genuine correctness hypothesis, not a weakening: with `α = 0` the state is
  `|ψ⟩ = β|γ⟩` and the inequality fails (take `|φ⟩` maximally entangled, `|γ⟩` a product state).
  The hypothesis relates the state vectors.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- The **coefficient operator** of a bipartite pure state, matricized against the
standard orthonormal basis of the *right* factor `T`: the continuous linear map
`M : T.space →L[ℂ] S.space` whose singular values are the Schmidt coefficients of
`ψ` (the matrix of `M` in fixed orthonormal bases is the coefficient array `a` with
`ψ = ∑ⱼₖ aⱼₖ |j⟩|k⟩`). It is used by the Schmidt-number results below and
by the subadditivity/triangle results (Problem 2.2(2),(3)). -/
def PureState.schmidtOp (ψ : PureState (S ⊗ T)) : T.space →L[ℂ] S.space :=
  TensorProduct.matricize (stdOrthonormalBasis ℂ T.space) (ψ.vec : S.space ⊗[ℂ] T.space)

/-- **Schmidt number** of a bipartite pure state (Nielsen–Chuang §2.5): the number of
non-zero Schmidt coefficients `λᵢ` in the Schmidt decomposition `|ψ⟩ = ∑ᵢ λᵢ |iᴬ⟩|iᴮ⟩`.
The Schmidt coefficients are the singular values of the matricized coefficient operator
`M = matricize ψ.vec`, so this counts its non-zero singular values. -/
def PureState.schmidtNumber (ψ : PureState (S ⊗ T)) : ℕ :=
  ψ.schmidtOp.toLinearMap.singularValues.support.card

/-- **Rank of a state**: the dimension of the range of its density operator. For a pure
state's reduced state this is the Schmidt number (`PureState.schmidtNumber_eq_rank_reducedLeft`);
in general it is the number of non-zero eigenvalues of `ρ`. -/
def State.rank (ρ : State S) : ℕ :=
  Module.finrank ℂ (LinearMap.range (ρ.op : S.space →ₗ[ℂ] S.space))

/-- The Schmidt number is the rank (`finrank` of the range) of the matricized
coefficient operator — the number of non-zero singular values equals the rank
(`LinearMap.card_support_singularValues`). -/
theorem PureState.schmidtNumber_eq_finrank_range_matricize (ψ : PureState (S ⊗ T)) :
    ψ.schmidtNumber
      = Module.finrank ℂ (LinearMap.range ψ.schmidtOp.toLinearMap) :=
  LinearMap.card_support_singularValues _

/-- The operator of the left reduced state `ρᴬ = tr_B(|ψ⟩⟨ψ|)` of a bipartite pure state
equals `M Mᵀ`, where `M = ψ.schmidtOp` is the matricized coefficient operator. The
purification/`_op` bridge behind Problem 2.2(1) (`partialTraceRight_rankOne_self`); a
citable identity reused by the Schmidt subadditivity/triangle results (Parts 2/3). -/
theorem PureState.reducedLeft_toState_op (ψ : PureState (S ⊗ T)) :
    ((ψ.toState.reducedLeft).op : S.space →ₗ[ℂ] S.space)
      = ↑(ψ.schmidtOp.comp (ContinuousLinearMap.adjoint ψ.schmidtOp)) := by
  rw [State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op]
  exact TensorProduct.partialTraceRight_rankOne_self
    (stdOrthonormalBasis ℂ T.space) (ψ.vec : S.space ⊗[ℂ] T.space)

/-- The rank of the left reduced state `ρᴬ = tr_B(|ψ⟩⟨ψ|)` equals the rank of the
matricized coefficient operator `M`. This is the structural half of Problem 2.2(1):
the purification identity `ρᴬ = M Mᵀ` (`PureState.reducedLeft_toState_op`) plus
`range (M ∘ Mᵀ) = range M` (`range_self_comp_adjoint`). -/
theorem State.rank_reducedLeft_toState_eq_finrank_range_matricize (ψ : PureState (S ⊗ T)) :
    (ψ.toState.reducedLeft).rank
      = Module.finrank ℂ (LinearMap.range ψ.schmidtOp.toLinearMap) := by
  rw [State.rank, ψ.reducedLeft_toState_op, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace, LinearMap.range_self_comp_adjoint]

/-- **The Schmidt number is the number of terms of any reduced Schmidt decomposition.** If
`(l, a, b)` is a Schmidt decomposition of `ψ` over `Fin n` (`ψ.IsSchmidtDecomposition l a b`:
strictly positive coefficients, orthonormal Schmidt bases, `∑ lᵢ² = 1`, `ψ.vec = ∑ᵢ lᵢ • aᵢ⊗bᵢ`),
then `ψ.schmidtNumber = n`. Because the Schmidt coefficients are the singular values of the
coefficient operator, every such decomposition has exactly `Sch(ψ)` terms: from the decomposition
the left marginal diagonalises as `ρᴬ = ∑ᵢ lᵢ² |aᵢ⟩⟨aᵢ|`
(`partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt`), which has rank `n` (the `lᵢ² ≠ 0`,
`finrank_range_sum_smul_rankOne_self`); with `Sch(ψ) = rank ρᴬ` this is `n` (the two matricization
bridges above, whose composite is Problem 2.2(1) `schmidtNumber_eq_rank_reducedLeft`). The companion
to `exists_isSchmidtDecomposition`, letting a *concrete* exhibited decomposition (e.g. the entangled
state of Exercise 2.79) fix the Schmidt number. -/
theorem PureState.schmidtNumber_eq_of_isSchmidtDecomposition {n : ℕ} (ψ : PureState (S ⊗ T))
    {l : Fin n → ℝ} {a : Fin n → S.space} {b : Fin n → T.space}
    (h : ψ.IsSchmidtDecomposition l a b) : ψ.schmidtNumber = n := by
  obtain ⟨hpos, ha, hb, _, hdecomp⟩ := h
  have hcne : ∀ i, ((l i : ℂ)) ^ 2 ≠ 0 := fun i =>
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt (hpos i)))
  have hL : (ψ.toState.reducedLeft.op : S.space →ₗ[ℂ] S.space)
      = ∑ i, ((l i : ℂ)) ^ 2 • (InnerProductSpace.rankOne ℂ (a i) (a i)).toLinearMap := by
    rw [State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op]
    exact LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt
      (stdOrthonormalBasis ℂ T.space) l a b hb hdecomp
  have hsr : ψ.schmidtNumber = ψ.toState.reducedLeft.rank :=
    (ψ.schmidtNumber_eq_finrank_range_matricize).trans
      (State.rank_reducedLeft_toState_eq_finrank_range_matricize ψ).symm
  rw [hsr, State.rank, hL]
  exact InnerProductSpace.finrank_range_sum_smul_rankOne_self a _ ha hcne

/-- **Problem 2.2(2).** If a bipartite pure state `|ψ⟩` has a product decomposition
`|ψ⟩ = ∑ⱼ |αⱼ⟩|βⱼ⟩` into `s.card` (possibly un-normalized) terms, then its Schmidt number is
at most the number of terms, `Sch(ψ) ≤ s.card`.

The coefficient operator matricizes to `M = ∑ⱼ matricize(αⱼ ⊗ βⱼ)` (matricization is linear);
each summand is a rank-`≤ 1` operator (`TensorProduct.finrank_range_matricize_tmul_le_one`), so
by rank subadditivity (`LinearMap.finrank_range_sum_le`) `Sch(ψ) = finrank (range M) ≤ ∑ⱼ 1 =
s.card`. The exercise is stated in `AxQM/NC/Ch2/Problem2_2.lean`. -/
theorem PureState.schmidtNumber_le_card_of_sum_tmul {ι : Type*} (s : Finset ι)
    (ψ : PureState (S ⊗ T)) (a : ι → S.space) (b : ι → T.space)
    (h : (ψ.vec : S.space ⊗[ℂ] T.space) = ∑ j ∈ s, a j ⊗ₜ[ℂ] b j) :
    ψ.schmidtNumber ≤ s.card := by
  have hM : ψ.schmidtOp = ∑ j ∈ s, TensorProduct.matricize (stdOrthonormalBasis ℂ T.space)
      (a j ⊗ₜ[ℂ] b j) := by
    rw [PureState.schmidtOp, h, map_sum]
  rw [ψ.schmidtNumber_eq_finrank_range_matricize, hM, ContinuousLinearMap.toLinearMap_sum]
  refine (LinearMap.finrank_range_sum_le s _).trans ?_
  calc ∑ j ∈ s, Module.finrank ℂ ↥(LinearMap.range
          (TensorProduct.matricize (stdOrthonormalBasis ℂ T.space) (a j ⊗ₜ[ℂ] b j)).toLinearMap)
      ≤ ∑ _j ∈ s, 1 :=
        Finset.sum_le_sum fun j _ =>
          TensorProduct.finrank_range_matricize_tmul_le_one _ (a j) (b j)
    _ = s.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- **Problem 2.2(3).** If a bipartite pure state `|ψ⟩` is a superposition `|ψ⟩ = α|φ⟩ + β|γ⟩`
of two pure states with *nonzero* amplitudes `α, β`, then its Schmidt number satisfies the
reverse-triangle bound `Sch(ψ) ≥ |Sch(φ) − Sch(γ)|`.

The nonzero amplitudes are a genuine correctness hypothesis, not a weakening of N&C: with
`α = 0` the state is `|ψ⟩ = β|γ⟩`, physically `|γ⟩`, so `Sch(ψ) = Sch(γ)`; taking `|φ⟩`
maximally entangled and `|γ⟩` a product state then makes `|Sch(φ) − Sch(γ)|` exceed `Sch(ψ)`
and the inequality genuinely fails. N&C's statement tacitly assumes a two-term superposition,
so `α, β ≠ 0` is the faithful reading.

Matricization is `ℂ`-linear (`schmidtOp = matricize`, a `LinearEquiv`), so the coefficient
operators combine as `M_ψ = α • M_φ + β • M_γ`. The rank triangle inequality
(`LinearMap.finrank_range_le_finrank_range_add_add`) applied to `α • M_φ` and `β • M_γ`, with
`Sch = finrank ∘ range` (`schmidtNumber_eq_finrank_range_matricize`) and range-invariance under a
nonzero scalar (`LinearMap.range_smul`), gives `Sch(φ) ≤ Sch(ψ) + Sch(γ)`; the symmetric argument
gives `Sch(γ) ≤ Sch(ψ) + Sch(φ)`, and together they yield `|Sch(φ) − Sch(γ)| ≤ Sch(ψ)`. The
hypothesis relates the state vectors `ψ.vec`/`φ.vec`/`γ.vec`. The exercise is stated in
`AxQM/NC/Ch2/Problem2_2.lean`. -/
theorem PureState.natAbs_sub_schmidtNumber_le (α β : ℂ) (φ γ ψ : PureState (S ⊗ T))
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hψ : (ψ.vec : S.space ⊗[ℂ] T.space)
        = α • (φ.vec : S.space ⊗[ℂ] T.space) + β • (γ.vec : S.space ⊗[ℂ] T.space)) :
    ((φ.schmidtNumber : ℤ) - γ.schmidtNumber).natAbs ≤ ψ.schmidtNumber := by
  -- The coefficient operators combine linearly, since `matricize` is a `LinearEquiv`. (The
  -- linearity lemmas are applied in term mode: `S.space ⊗[ℂ] T.space` and `(S ⊗ T).space` carry
  -- defeq-but-not-syntactically-equal additive structure, so `rw`/`simp` cannot match them.)
  have hop : ψ.schmidtOp = α • φ.schmidtOp + β • γ.schmidtOp := by
    simp only [PureState.schmidtOp, hψ]
    exact (map_add (TensorProduct.matricize (stdOrthonormalBasis ℂ T.space)) _ _).trans
      (congrArg₂ (· + ·)
        (map_smul (TensorProduct.matricize (stdOrthonormalBasis ℂ T.space)) α _)
        (map_smul (TensorProduct.matricize (stdOrthonormalBasis ℂ T.space)) β _))
  -- Push the identity down to the underlying linear maps.
  have hlin : ψ.schmidtOp.toLinearMap
      = (α • φ.schmidtOp).toLinearMap + (β • γ.schmidtOp).toLinearMap := by
    rw [hop, ContinuousLinearMap.toLinearMap_add]
  -- Express the three Schmidt numbers as ranks of the (scaled) coefficient operators.
  have hψrank : ψ.schmidtNumber
      = Module.finrank ℂ ↥(LinearMap.range
          ((α • φ.schmidtOp).toLinearMap + (β • γ.schmidtOp).toLinearMap)) := by
    rw [ψ.schmidtNumber_eq_finrank_range_matricize, hlin]
  have hφrank : φ.schmidtNumber
      = Module.finrank ℂ ↥(LinearMap.range (α • φ.schmidtOp).toLinearMap) := by
    rw [φ.schmidtNumber_eq_finrank_range_matricize, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.range_smul _ _ hα]
  have hγrank : γ.schmidtNumber
      = Module.finrank ℂ ↥(LinearMap.range (β • γ.schmidtOp).toLinearMap) := by
    rw [γ.schmidtNumber_eq_finrank_range_matricize, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.range_smul _ _ hβ]
  -- The two reverse-triangle directions, from the rank triangle inequality.
  have dirφ : φ.schmidtNumber ≤ ψ.schmidtNumber + γ.schmidtNumber := by
    rw [hφrank, hψrank, hγrank]
    exact LinearMap.finrank_range_le_finrank_range_add_add _ _
  have dirγ : γ.schmidtNumber ≤ ψ.schmidtNumber + φ.schmidtNumber := by
    rw [hγrank, hψrank, hφrank,
      add_comm (α • φ.schmidtOp).toLinearMap (β • γ.schmidtOp).toLinearMap]
    exact LinearMap.finrank_range_le_finrank_range_add_add _ _
  omega

/-- The **Schmidt number of any bipartite pure state is at least `1`**. Its coefficient operator
`M = matricize ψ.vec = ψ.schmidtOp` is non-zero (`matricize` is a linear equivalence and the unit
vector `ψ.vec` is non-zero), so its range in `Sch(ψ) = finrank (range M)` is non-trivial. In
particular `Sch(ψ) = 1` is the minimal non-degenerate value. -/
theorem PureState.one_le_schmidtNumber (ψ : PureState (S ⊗ T)) : 1 ≤ ψ.schmidtNumber := by
  have hvec : ψ.vec ≠ 0 := norm_ne_zero_iff.mp (by rw [ψ.normalized]; exact one_ne_zero)
  rw [ψ.schmidtNumber_eq_finrank_range_matricize, Nat.one_le_iff_ne_zero, Ne,
    Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  intro hzero
  have hz2 : ψ.schmidtOp = 0 := by
    ext v; simpa using congrFun (congrArg DFunLike.coe hzero) v
  rw [PureState.schmidtOp] at hz2
  -- Name `ψ.vec` at the generic `S.space ⊗[ℂ] T.space` type via a `let` — an inline ascription does
  -- not stick (it only checks defeq of the whole ascribed expression, it does not change which
  -- instances the surrounding `TensorProduct.matricize` application's implicit `E` unifies
  -- against).
  let ψvecLM : S.space ⊗[ℂ] T.space := ψ.vec
  have hz2' : (TensorProduct.matricize (stdOrthonormalBasis ℂ T.space)) ψvecLM = 0 := hz2
  rw [(TensorProduct.matricize _).map_eq_zero_iff] at hz2'
  exact hvec hz2'

/-- A **pure state has rank `1`**: being a rank-one projector `|v⟩⟨v|` for a unit vector `v`, its
density operator has a one-dimensional range. The easy direction of "pure ↔ rank one"; the converse
(a rank-one density operator is pure) is not needed by its consumers. -/
theorem State.rank_eq_one_of_isPure {ρ : State S} (h : ρ.IsPure) : ρ.rank = 1 := by
  obtain ⟨v, hv, hop⟩ := ρ.isPure_iff_exists_rankOne.mp h
  rw [State.rank, hop]
  refine le_antisymm (InnerProductSpace.finrank_range_rankOne_le_one v v) ?_
  rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  intro hz
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  have hrz : (InnerProductSpace.rankOne ℂ v v) = 0 := by
    ext w; simpa using congrFun (congrArg DFunLike.coe hz) w
  rw [InnerProductSpace.rankOne_eq_zero] at hrz
  tauto

end AxQM
