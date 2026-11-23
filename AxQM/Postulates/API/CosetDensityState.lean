/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CosetStateOrthonormal
import AxQM.Concrete.CosetStateCommute
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# AxQM.Postulates.API — the group system `ℂ[G]`, the coset states, and `σ_K` as a state

Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem): this file promotes the
concrete objects of `AxQM.Concrete.CosetState` / `CosetStateOrthonormal` to states on the group
register.

For a finite group `G` and a subgroup `K ≤ G` (with `[DecidablePred (· ∈ K)]`) this file defines:

* `groupSystem G` — the **group quantum system**, whose Hilbert space is the group algebra
  `ℂ[G] = EuclideanSpace ℂ G` (basis `{|g⟩}_{g ∈ G}`). This is the register the Problem 5.5 query
  state `|G|^{-m/2} ∑_{g₁,…,gₘ} |g₁,…,gₘ⟩|f(g₁),…,f(gₘ)⟩` (eq. 5.80) lives on. Its dimension is
  `|G|` (`groupSystem_dim`).
* `cosetPureState K q` — the **normalized coset state** `|C_q⟩` (`q ∈ G ⧸ K`) as a `PureState` of
  `groupSystem G`, the unit vector `Concrete.cosetState K q`. The family is orthonormal
  (`cosetPureState_orthonormal`), lifting `Concrete.cosetState_orthonormal`.
* `cosetDensityState K` — the **coset density matrix** `σ_K` as a `State` of `groupSystem G`: the
  concrete matrix `Concrete.cosetDensity K` promoted through the `⋆`-algebra isomorphism
  `Matrix.toEuclideanCLM`. It is a density operator because `Concrete.cosetDensity K` is positive
  semidefinite (`Concrete.cosetDensity_posSemidef`) and of trace one
  (`Concrete.cosetDensity_trace_eq_one`), both transported across the isomorphism — the same bridge
  route as `blochState`.
* `cosetDensityState_op_eq_sum` — the **coset ensemble / spectral form of the state**
  `σ_K = ∑_{q ∈ G ⧸ K} (|K|/|G|) |C_q⟩⟨C_q|` at the operator level: `σ_K` is the uniform mixture of
  the orthonormal coset-state projectors (eigenvalue `|K|/|G|` on each `|C_q⟩`). This is
  `Concrete.cosetDensity_eq_sum_cosetState` transported through the isomorphism, using the
  bridge `Matrix.toEuclideanCLM_vecMulVec` (`Matrix.toEuclideanCLM` of an outer product is the
  rank-one operator `|x⟩⟨y|`).

`σ_K` is the single-copy reduced state of the query register (5.80) after the range register is
traced out: `f` is constant and distinct on cosets, so measuring `f` reveals exactly which of the
`gᵢ` share a coset, leaving the group registers in `σ_K^{⊗m}`. Promoting `σ_K` to a `State` here
lets the identifiability argument — the fidelity bound for distinct subgroups and the distinguishing
measurement — speak about `σ_K` as a *quantum state*, not merely as a matrix.

## Design notes

* `groupSystem G` mirrors `qudit d = QSystem.ofModel (EuclideanSpace ℂ (Fin d))` with the finite
  index type `G` in place of `Fin d`. Only `[Fintype G]` is needed for the system itself; the coset
  states and `σ_K` additionally need the group structure, `[DecidableEq G]` (for
  `Matrix.toEuclideanCLM`), and `[DecidablePred (· ∈ K)]`.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The **group quantum system** on `G`: the system whose state space is the group algebra
`ℂ[G] = EuclideanSpace ℂ G`, with computational basis `{|g⟩}_{g ∈ G}`. It is the register the
Nielsen & Chuang Problem 5.5 query state (5.80) lives on; `qudit d` is the special case
`G = Fin d`. Only the finiteness of `G` is used here. -/
def groupSystem (G : Type*) [Fintype G] : QSystem := QSystem.ofModel (EuclideanSpace ℂ G)

@[simp]
theorem groupSystem_space (G : Type*) [Fintype G] :
    (groupSystem G).space = EuclideanSpace ℂ G := rfl

/-- The **dimension of the group system is `|G|`**: `finrank ℂ (EuclideanSpace ℂ G) = |G|`. This is
the `|G|` in the Problem 5.5 success bound `1 - 1/|G|`. -/
theorem groupSystem_dim (G : Type*) [Fintype G] : (groupSystem G).dim = Fintype.card G := by
  rw [QSystem.dim]
  change Module.finrank ℂ (EuclideanSpace ℂ G) = _
  rw [finrank_euclideanSpace]

/-- The group system's state space is nontrivial (it contains the basis vectors `|g⟩`) whenever `G`
is nonempty — in particular for any group. Supplies the `Nontrivial S.space` hypothesis that some
state constructions require. -/
instance groupSystem_space_nontrivial (G : Type*) [Fintype G] [Nonempty G] :
    Nontrivial (groupSystem G).space := by
  change Nontrivial (EuclideanSpace ℂ G); infer_instance

variable (K : Subgroup G) [DecidablePred (· ∈ K)]

/-- The **normalized coset state** `|C_q⟩ = |K|^{-1/2} ∑_{g ∈ q} |g⟩` (`q ∈ G ⧸ K`) as a `PureState`
of the group system `groupSystem G`: the concrete unit vector `Concrete.cosetState K q`, normalized
because the coset states form an orthonormal family (`Concrete.cosetState_orthonormal`). -/
def cosetPureState (q : G ⧸ K) : PureState (groupSystem G) where
  vec := Concrete.cosetState K q
  normalized := (Concrete.cosetState_orthonormal K).norm_eq_one q

omit [DecidableEq G] in
@[simp]
theorem cosetPureState_vec (q : G ⧸ K) :
    (cosetPureState K q).vec = Concrete.cosetState K q := rfl

omit [DecidableEq G] in
/-- **The coset pure states form an orthonormal family** `(|C_q⟩)_{q ∈ G ⧸ K}`, lifting
`Concrete.cosetState_orthonormal` to `PureState`s of `groupSystem G`. -/
theorem cosetPureState_orthonormal :
    Orthonormal ℂ (fun q => (cosetPureState K q).vec) :=
  Concrete.cosetState_orthonormal K

/-- The **coset density matrix `σ_K` as a state** of the group system `groupSystem G` (Nielsen &
Chuang, Problem 5.5): the concrete matrix `Concrete.cosetDensity K` promoted through the `⋆`-algebra
isomorphism `Matrix.toEuclideanCLM`. It is a density operator because `Concrete.cosetDensity K` is
positive semidefinite (`Concrete.cosetDensity_posSemidef`, from the Gram factorisation) and of trace
one (`Concrete.cosetDensity_trace_eq_one`), both transported across the isomorphism. This is the
single-copy reduced state of the query register (5.80). -/
def cosetDensityState : State (groupSystem G) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G) (Concrete.cosetDensity K)
  isDensity :=
    ⟨(Matrix.isPositive_toEuclideanCLM_iff _).mpr (Concrete.cosetDensity_posSemidef K),
      (Matrix.trace_toEuclideanCLM _).trans (Concrete.cosetDensity_trace_eq_one K)⟩

/-- The underlying density operator of `cosetDensityState K` is the `Matrix.toEuclideanCLM` image of
the concrete coset density matrix `Concrete.cosetDensity K`. A `simp` lemma. -/
@[simp]
theorem cosetDensityState_op :
    (cosetDensityState K).op =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G) (Concrete.cosetDensity K) :=
  rfl

/-- **The coset density state is the uniform mixture of the coset-state projectors** (its spectral
decomposition), at the operator level:
`σ_K = ∑_{q ∈ G ⧸ K} (|K|/|G|) |C_q⟩⟨C_q|`.
Since `(|C_q⟩)_q` is orthonormal (`cosetPureState_orthonormal`), this exhibits `σ_K` as diagonal
with eigenvalue `|K|/|G|` on each coset state — the "coset ensemble as a state". It is
`Concrete.cosetDensity_eq_sum_cosetState` (the entrywise mixture form of the matrix) transported
through `Matrix.toEuclideanCLM`, each outer product `vecMulVec |C_q⟩ ⟨C_q|` becoming the rank-one
projector `|C_q⟩⟨C_q|` via the bridge `Matrix.toEuclideanCLM_vecMulVec`. -/
theorem cosetDensityState_op_eq_sum :
    (cosetDensityState K).op =
      ∑ q : G ⧸ K, ((Fintype.card K / Fintype.card G : ℝ) : ℂ) •
        (cosetPureState K q).toState.op := by
  rw [cosetDensityState_op, Concrete.cosetDensity_eq_sum_cosetState, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, PureState.toState_op, cosetPureState_vec]
  congr 1
  exact Matrix.toEuclideanCLM_vecMulVec (Concrete.cosetState K q) (Concrete.cosetState K q)

/-- **The coset density operators of an abelian group commute** (Nielsen & Chuang, Problem 5.5).
For a commutative finite group `G` and two subgroups `K₁, K₂ ≤ G`, the density operators of their
coset reduced states commute:

`σ_{K₁} · σ_{K₂} = σ_{K₂} · σ_{K₁}`.

This is the bridge of the concrete matrix commutation `Concrete.cosetDensity_commute` (the `σ_K` are
convolution operators, which commute on an abelian group): `(cosetDensityState K).op =
Matrix.toEuclideanCLM (Concrete.cosetDensity K)` and `Matrix.toEuclideanCLM` is a `⋆`-algebra
isomorphism, hence a multiplicative homomorphism, so it carries the matrix commutation to the
operator commutation (`Commute.map`). It discharges the pairwise-commutation hypothesis of
`State.pairedTraceBound_of_commute` for the coset reduced states of an **abelian** hidden-subgroup
instance, making the identification theorem (Nielsen & Chuang, Problem 5.5) unconditional there. -/
theorem cosetDensityState_op_commute {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (K₁ K₂ : Subgroup G) [DecidablePred (· ∈ K₁)] [DecidablePred (· ∈ K₂)] :
    Commute (cosetDensityState K₁).op (cosetDensityState K₂).op := by
  simp only [cosetDensityState_op]
  exact (Concrete.cosetDensity_commute K₁ K₂).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G))

end AxQM
