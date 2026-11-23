/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PseudoInverse
import AxQM.Postulates.API.TypicalSubspace
import AxQM.Postulates.API.Fidelity
import AxQM.Postulates.Measurement
import ToMathlib.Analysis.Convex.Majorization
import ToMathlib.Analysis.InnerProductSpace.PolarUnitary
import ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# AxQM — majorization of quantum states and the reverse operator-majorization theorem

This is the spectral foundation for **Nielsen's theorem** (Nielsen–Chuang, Theorem 12.15): a
bipartite pure state `|ψ⟩` can be transformed to `|ϕ⟩` by LOCC iff `λ_ψ ≺ λ_ϕ`, where `λ_ψ` is the
vector of squared Schmidt coefficients — equivalently the eigenvalues of the reduced density
operator `ρ_ψ`. The condition `λ_ψ ≺ λ_ϕ` is *majorization of the reduced states*, which we make
first-class here.

The spectral data of a density operator used here — `State.eigenbasis` and its
`op_apply_eigenbasis` / `inner_eigenbasis_self` / `norm_eigenbasis` lemmas — are in
`Postulates/API/PseudoInverse.lean` (alongside `State.op_apply_eigenvectorBasis`).

## What is defined and proved

* `AxQM.State.Majorize ρ σ` — **majorization of quantum states**: the eigenvalue
  distribution `ρ.eigenvalueDist` is majorized by `σ.eigenvalueDist` (in the vector sense
  `Majorize` of `ToMathlib.Analysis.Convex.Majorization`). This is N&C's `ρ ≺ σ` for density
  operators, defined spectrally like `State.vonNeumannEntropy`.
* `AxQM.State.inner_op_self_eq_sum_eigenvalueDist` — the **spectral quadratic form**
  `⟪u, σ u⟫ = ∑ₗ λₗ ‖⟪fₗ, u⟫‖²` (`fₗ = σ.eigenbasis l`, `λₗ = σ.eigenvalueDist l`).
* `AxQM.State.majorize_of_op_eq_sum_unitary_conj` — the **reverse operator-majorization
  theorem** (the state-level reverse direction of N&C Theorem 12.13): if
  `ρ = ∑ⱼ pⱼ Uⱼ σ Uⱼ†` is a convex combination (`pⱼ ≥ 0`, `∑ pⱼ = 1`) of *unitary* conjugates of
  `σ`, then `ρ ≺ σ`. This is exactly the input Nielsen's theorem invokes ("`ρ_ψ = ∑ pⱼ Uⱼ ρ_ϕ Uⱼ†`
  whence `λ_ψ ≺ λ_ϕ` by Theorem 12.13").
* `AxQM.State.exists_op_eq_sum_unitary_conj_of_majorize` — the **forward
  operator-majorization theorem** (state-level forward direction of N&C Theorem 12.13): if `ρ ≺ σ`
  then `ρ` *is* such a convex combination `ρ = ∑ⱼ pⱼ Uⱼ σ Uⱼ†` of unitary conjugates of `σ`.
  Together with the reverse above this is Theorem 12.13 for density operators. Proved
  operator-natively:
  Proposition 12.11 (`majorize_iff_exists_sum_perm`) expands `λ_ρ = ∑_π w_π (λ_σ ∘ π)`, and each
  permutation `π` becomes a unitary change of eigenbasis `σ.eigenbasis.equiv ρ.eigenbasis π⁻¹`.
* `AxQM.State.LOCCConvertible ρ σ` — **one-way LOCC convertibility of reduced states** (the
  standard protocol form of N&C Proposition 12.14): there is a measurement `{Mⱼ}` and a probability
  distribution `pⱼ` with `Mⱼ ρ Mⱼ† = pⱼ σ` for every outcome `j`. This is the density-operator
  content of "`|ψ⟩ → |ϕ⟩` by LOCC" stated for states and measurements; the general
  LOCC-protocol quantifier is not formalised (see the predicate's docstring).
* `AxQM.State.LOCCConvertible.majorize` — the **forward direction of Nielsen's theorem**
  (N&C Theorem 12.15, `⟹`): `ρ.LOCCConvertible σ → ρ ≺ σ`. Polar-decomposing `Aⱼ = Mⱼ √ρ` gives
  `ρ = ∑ⱼ pⱼ Uⱼ† σ Uⱼ`, and `majorize_of_op_eq_sum_unitary_conj` closes it.

## Proof of the reverse operator-majorization theorem

Reading the `(k, k)` entry of the mixture in `ρ`'s eigenbasis `e` and expanding `σ`'s quadratic
form in its eigenbasis `f` gives, with `uⱼₖ = Uⱼ† eₖ`,
`λ_ρ(k) = ⟪eₖ, ρ eₖ⟫ = ∑ⱼ pⱼ ⟪uⱼₖ, σ uⱼₖ⟫ = ∑ₗ (∑ⱼ pⱼ ‖⟪fₗ, uⱼₖ⟫‖²) λ_σ(l) = ∑ₗ Dₖₗ λ_σ(l)`,
so `λ_ρ = D λ_σ` where `Dₖₗ = ∑ⱼ pⱼ ‖⟪fₗ, uⱼₖ⟫‖²`. The matrix `D` is doubly stochastic — its rows
sum to one because `∑ₗ ‖⟪fₗ, uⱼₖ⟫‖² = ‖uⱼₖ‖² = ‖eₖ‖² = 1` (Parseval + `Uⱼ†` unitary) and
`∑ⱼ pⱼ = 1`, and its columns because `∑ₖ ‖⟪fₗ, Uⱼ† eₖ⟫‖² = ∑ₖ ‖⟪Uⱼ fₗ, eₖ⟫‖² = ‖Uⱼ fₗ‖² = 1`.
`Majorize.of_mem_doublyStochastic` (the easy direction of N&C Proposition 12.11) then gives
`D λ_σ ≺ λ_σ`, i.e. `ρ ≺ σ`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace State

/-- **Spectral action on the eigenbasis, in `eigenvalueDist` form** (majorization plumbing):
`ρ (bⱼ) = (ρ.eigenvalueDist j) • bⱼ`. The `eigenvalueDist`-phrasing of the general
`State.op_apply_eigenbasis` (`Postulates/API/PseudoInverse`); `ρ.eigenvalueDist j` is definitionally
`ρ.isDensity.isSymmetric.eigenvalues rfl j`, so this is `op_apply_eigenbasis` unchanged. -/
private theorem op_apply_eigenbasis' (ρ : State S) (j : Fin (Module.finrank ℂ S.space)) :
    ρ.op (ρ.eigenbasis j) = (ρ.eigenvalueDist j : ℂ) • ρ.eigenbasis j :=
  ρ.op_apply_eigenbasis j

/-- **Majorization of quantum states.** `ρ.Majorize σ` (N&C's `ρ ≺ σ` for density operators) holds
when the eigenvalue distribution of `ρ` is majorized by that of `σ` (`Majorize` on the eigenvalue
vectors). This is the exact condition `λ_ψ ≺ λ_ϕ` of Nielsen's theorem when `ρ`, `σ` are the reduced
states of bipartite pure states. -/
def Majorize (ρ σ : State S) : Prop :=
  _root_.Majorize ρ.eigenvalueDist σ.eigenvalueDist

/-- **Eigenvalue distribution from any eigenbasis (as a multiset).** If an orthonormal basis `b`
diagonalizes the density operator `ρ.op` with real eigenvalues `p` (`ρ.op (b i) = p i • b i`), then
the multiset of `ρ.eigenvalueDist` equals the multiset of `p`.  The canonical eigenvalue
distribution is a specific ordering of the spectrum, so it agrees with *any* eigenbasis's diagonal
only up to a permutation; this records that agreement multiset-wise (all `Majorize` needs, being
permutation-invariant on each vector).  Proved by the eigenvalue-recognition theorem
`LinearMap.IsSymmetric.eigenvalues_multiset_map_eq_of_eigenbasis`. -/
theorem eigenvalueDist_multiset_map_eq {ι : Type*} [Fintype ι] (ρ : State S)
    (b : OrthonormalBasis ι ℂ S.space) (p : ι → ℝ)
    (hb : ∀ i, ρ.op (b i) = (p i : ℂ) • b i) :
    Multiset.map ρ.eigenvalueDist Finset.univ.val = Multiset.map p Finset.univ.val := by
  refine (LinearMap.IsSymmetric.eigenvalues_multiset_map_eq_of_eigenbasis
    ρ.isDensity.isSymmetric rfl b.toBasis fun i => ?_).symm
  simp only [OrthonormalBasis.coe_toBasis]
  exact hb i

/-- **The spectral quadratic form.** For a state `σ` with eigenbasis `f = σ.eigenbasis` and
eigenvalues `λ = σ.eigenvalueDist`, `⟪u, σ u⟫ = ∑ₗ λₗ · ‖⟪fₗ, u⟫‖²`. This is the diagonalization of
`σ.op` read off against an arbitrary vector `u`. -/
theorem inner_op_self_eq_sum_eigenvalueDist (σ : State S) (u : S.space) :
    inner ℂ u (σ.op u) =
      ∑ l, (σ.eigenvalueDist l : ℂ) * ((‖inner ℂ (σ.eigenbasis l) u‖ ^ 2 : ℝ) : ℂ) := by
  have hu : ∑ l, inner ℂ (σ.eigenbasis l) u • σ.eigenbasis l = u := by
    simpa [OrthonormalBasis.repr_apply_apply] using σ.eigenbasis.sum_repr u
  calc
    inner ℂ u (σ.op u)
        = inner ℂ u (σ.op (∑ l, inner ℂ (σ.eigenbasis l) u • σ.eigenbasis l)) := by rw [hu]
      _ = inner ℂ u
            (∑ l, inner ℂ (σ.eigenbasis l) u • ((σ.eigenvalueDist l : ℂ) • σ.eigenbasis l)) := by
            rw [map_sum]
            simp_rw [map_smul, σ.op_apply_eigenbasis']
      _ = ∑ l, (σ.eigenvalueDist l : ℂ) *
            (inner ℂ (σ.eigenbasis l) u * inner ℂ u (σ.eigenbasis l)) := by
            rw [inner_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [inner_smul_right, inner_smul_right]
            ring
      _ = ∑ l, (σ.eigenvalueDist l : ℂ) * ((‖inner ℂ (σ.eigenbasis l) u‖ ^ 2 : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [show inner ℂ u (σ.eigenbasis l)
                  = (starRingEnd ℂ) (inner ℂ (σ.eigenbasis l) u) from
                (inner_conj_symm u (σ.eigenbasis l)).symm, RCLike.mul_conj]
            norm_num

/-- **Reverse operator-majorization** (state-level reverse direction of N&C Theorem 12.13). If a
state `ρ` is a convex combination `ρ = ∑ⱼ pⱼ Uⱼ σ Uⱼ†` of unitary conjugates of a state `σ` (with
`pⱼ ≥ 0`, `∑ pⱼ = 1`, each `Uⱼ` unitary), then `ρ ≺ σ`. This is the mathematical input Nielsen's
theorem invokes: from `ρ_ψ = ∑ pⱼ Uⱼ ρ_ϕ Uⱼ†` conclude `λ_ψ ≺ λ_ϕ`. -/
theorem majorize_of_op_eq_sum_unitary_conj {ι : Type*} [Fintype ι]
    (ρ σ : State S) {p : ι → ℝ} {U : ι → S.space →L[ℂ] S.space}
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hU : ∀ j, U j ∈ unitary (S.space →L[ℂ] S.space))
    (hρ : ρ.op = ∑ j, (p j : ℂ) • (U j).comp (σ.op.comp (adjoint (U j)))) :
    ρ.Majorize σ := by
  classical
  -- adjoints of the `Uⱼ` are unitary too
  have hUadj : ∀ j, adjoint (U j) ∈ unitary (S.space →L[ℂ] S.space) := by
    intro j
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mem (hU j)
  -- the doubly stochastic matrix `Dₖₗ = ∑ⱼ pⱼ ‖⟪fₗ, Uⱼ† eₖ⟫‖²`
  set D : Matrix (Fin (Module.finrank ℂ S.space)) (Fin (Module.finrank ℂ S.space)) ℝ :=
    Matrix.of fun k l =>
      ∑ j, p j * ‖inner ℂ (σ.eigenbasis l) (adjoint (U j) (ρ.eigenbasis k))‖ ^ 2
  have hDentry : ∀ k l, D k l =
      ∑ j, p j * ‖inner ℂ (σ.eigenbasis l) (adjoint (U j) (ρ.eigenbasis k))‖ ^ 2 := fun _ _ => rfl
  -- `D` is doubly stochastic
  have hDmem : D ∈ doublyStochastic ℝ (Fin (Module.finrank ℂ S.space)) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · -- nonnegative entries
      intro k l
      rw [hDentry]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (sq_nonneg _)
    · -- rows sum to one
      intro k
      have hone : ∀ j,
          ∑ l, ‖inner ℂ (σ.eigenbasis l) (adjoint (U j) (ρ.eigenbasis k))‖ ^ 2 = 1 := by
        intro j
        rw [σ.eigenbasis.sum_sq_norm_inner_right,
          ContinuousLinearMap.norm_map_of_mem_unitary (hUadj j), ρ.norm_eigenbasis k, one_pow]
      have : ∑ l, D k l = ∑ j, p j := by
        simp_rw [hDentry]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, hone j, mul_one]
      rw [this, hsum]
    · -- columns sum to one
      intro l
      have hone : ∀ j,
          ∑ k, ‖inner ℂ (σ.eigenbasis l) (adjoint (U j) (ρ.eigenbasis k))‖ ^ 2 = 1 := by
        intro j
        have hswap : ∀ k, inner ℂ (σ.eigenbasis l) (adjoint (U j) (ρ.eigenbasis k))
            = inner ℂ ((U j) (σ.eigenbasis l)) (ρ.eigenbasis k) := fun k => by
          rw [adjoint_inner_right]
        simp_rw [hswap]
        rw [ρ.eigenbasis.sum_sq_norm_inner_left,
          ContinuousLinearMap.norm_map_of_mem_unitary (hU j), σ.norm_eigenbasis l, one_pow]
      have : ∑ k, D k l = ∑ j, p j := by
        simp_rw [hDentry]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, hone j, mul_one]
      rw [this, hsum]
  -- `λ_ρ = D λ_σ`
  have hEq : D.mulVec σ.eigenvalueDist = ρ.eigenvalueDist := by
    funext k
    have hterm : ∀ j, inner ℂ (ρ.eigenbasis k)
        (((p j : ℂ) • (U j).comp (σ.op.comp (adjoint (U j)))) (ρ.eigenbasis k))
        = (p j : ℂ) * ∑ l, (σ.eigenvalueDist l : ℂ) *
            ((‖inner ℂ (σ.eigenbasis l) (adjoint (U j) (ρ.eigenbasis k))‖ ^ 2 : ℝ) : ℂ) := by
      intro j
      rw [_root_.smul_apply, inner_smul_right, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply,
        ← adjoint_inner_left (U j) (σ.op (adjoint (U j) (ρ.eigenbasis k))) (ρ.eigenbasis k),
        σ.inner_op_self_eq_sum_eigenvalueDist (adjoint (U j) (ρ.eigenbasis k))]
    have key : (ρ.eigenvalueDist k : ℂ) = ∑ l, (D k l : ℂ) * (σ.eigenvalueDist l : ℂ) :=
      calc (ρ.eigenvalueDist k : ℂ)
          = inner ℂ (ρ.eigenbasis k) (ρ.op (ρ.eigenbasis k)) := by
            rw [ρ.op_apply_eigenbasis' k, inner_smul_right, ρ.inner_eigenbasis_self k, mul_one]
        _ = ∑ j, inner ℂ (ρ.eigenbasis k)
              (((p j : ℂ) • (U j).comp (σ.op.comp (adjoint (U j)))) (ρ.eigenbasis k)) := by
            rw [hρ, _root_.sum_apply, inner_sum]
        _ = ∑ j, ∑ l, (p j : ℂ) * ((σ.eigenvalueDist l : ℂ) *
              ((‖inner ℂ (σ.eigenbasis l) (adjoint (U j) (ρ.eigenbasis k))‖ ^ 2 : ℝ) : ℂ)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hterm j, Finset.mul_sum]
        _ = ∑ l, ∑ j, (p j : ℂ) * ((σ.eigenvalueDist l : ℂ) *
              ((‖inner ℂ (σ.eigenbasis l) (adjoint (U j) (ρ.eigenbasis k))‖ ^ 2 : ℝ) : ℂ)) :=
            Finset.sum_comm
        _ = ∑ l, (D k l : ℂ) * (σ.eigenvalueDist l : ℂ) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hDentry]
            push_cast
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
    have hmv : (D.mulVec σ.eigenvalueDist) k = ∑ l, D k l * σ.eigenvalueDist l := by
      simp only [Matrix.mulVec, dotProduct]
    rw [hmv]
    have hcast : ((∑ l, D k l * σ.eigenvalueDist l : ℝ) : ℂ) = (ρ.eigenvalueDist k : ℂ) := by
      rw [key]; push_cast; ring
    exact_mod_cast hcast
  rw [State.Majorize, ← hEq]
  exact Majorize.of_mem_doublyStochastic hDmem σ.eigenvalueDist

/-- **Forward operator-majorization** (state-level forward direction of N&C Theorem 12.13). If a
state `ρ` is majorized by `σ` (`ρ ≺ σ`), then `ρ` is a convex combination `ρ = ∑ⱼ pⱼ Uⱼ σ Uⱼ†` of
*unitary* conjugates of `σ` (`pⱼ ≥ 0`, `∑ pⱼ = 1`, each `Uⱼ` unitary). Paired with the reverse
`majorize_of_op_eq_sum_unitary_conj`, this is N&C Theorem 12.13 (`H ≺ K ↔ H = ∑ pⱼ Uⱼ K Uⱼ†`) at the
level of density operators — the "unitary-mixture" characterization Nielsen's theorem produces from
`λ_ψ ≺ λ_ϕ` before realizing it as a measurement.

The proof is operator-native (no matrix bridge). Proposition 12.11 (`majorize_iff_exists_sum_perm`)
expands `ρ`'s eigenvalue vector as a convex combination `λ_ρ = ∑_π w_π (λ_σ ∘ π)` of permutations of
`σ`'s. Each permutation `π` is realized as the unitary change of eigenbasis
`Uπ = σ.eigenbasis.equiv ρ.eigenbasis π⁻¹` (sending `σ`'s `i`-th eigenvector to `ρ`'s `π⁻¹ i`-th),
for which `Uπ σ Uπ† (ρ.eigenbasis q) = λ_σ(π q) • ρ.eigenbasis q`; weighting by `w_π` and summing
reconstructs `ρ.op` diagonally in `ρ`'s own eigenbasis (`OrthonormalBasis.ext_inner_basis`). The
index type is `Equiv.Perm (Fin d)` (`d = dim S.space`). -/
theorem exists_op_eq_sum_unitary_conj_of_majorize {ρ σ : State S} (h : ρ.Majorize σ) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℝ) (U : ι → (S.space →L[ℂ] S.space)),
      (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧
        (∀ j, U j ∈ unitary (S.space →L[ℂ] S.space)) ∧
        ρ.op = ∑ j, (p j : ℂ) • (U j).comp (σ.op.comp (adjoint (U j))) := by
  classical
  have h' : _root_.Majorize ρ.eigenvalueDist σ.eigenvalueDist := h
  obtain ⟨w, hw0, hwsum, hwdist⟩ := majorize_iff_exists_sum_perm.mp h'
  -- the isometry realizing permutation `π` as a change of eigenbasis (`σ`'s → `ρ`'s)
  set e : Equiv.Perm (Fin (Module.finrank ℂ S.space)) → (S.space ≃ₗᵢ[ℂ] S.space) :=
    fun π => σ.eigenbasis.equiv ρ.eigenbasis π⁻¹ with he
  set U : Equiv.Perm (Fin (Module.finrank ℂ S.space)) → (S.space →L[ℂ] S.space) :=
    fun π => (↑(e π).toContinuousLinearEquiv : S.space →L[ℂ] S.space) with hU
  -- `Uπ` carries `σ.eigenbasis (π q)` to `ρ.eigenbasis q`
  have hUapply : ∀ (π : Equiv.Perm (Fin (Module.finrank ℂ S.space)))
      (q : Fin (Module.finrank ℂ S.space)), U π (σ.eigenbasis (π q)) = ρ.eigenbasis q := by
    intro π q
    simp only [hU, he, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, OrthonormalBasis.equiv_apply_basis,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  -- `Uπ†` carries `ρ.eigenbasis q` to `σ.eigenbasis (π q)`
  have hadj : ∀ (π : Equiv.Perm (Fin (Module.finrank ℂ S.space)))
      (q : Fin (Module.finrank ℂ S.space)),
      adjoint (U π) (ρ.eigenbasis q) = σ.eigenbasis (π q) := by
    intro π q
    have hst : adjoint (U π) = (↑(e π).symm.toContinuousLinearEquiv : S.space →L[ℂ] S.space) := by
      simp only [hU]; exact LinearIsometryEquiv.adjoint_eq_symm (e π)
    rw [hst, he]
    simp only [OrthonormalBasis.equiv_symm, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, OrthonormalBasis.equiv_apply_basis,
      Equiv.Perm.inv_def, Equiv.symm_symm]
  -- each `Uπ` is unitary
  have hunit : ∀ π, U π ∈ unitary (S.space →L[ℂ] S.space) := by
    intro π
    simp only [hU]
    rw [← Unitary.coe_symm_linearIsometryEquiv_apply]
    exact SetLike.coe_mem _
  -- `ρ.op = ∑ π, w π • Uπ σ.op Uπ†`, checked on `ρ`'s eigenbasis
  have hvec : ∀ q : Fin (Module.finrank ℂ S.space), ρ.op (ρ.eigenbasis q)
      = (∑ π, (w π : ℂ) • (U π).comp (σ.op.comp (adjoint (U π)))) (ρ.eigenbasis q) := by
    intro q
    rw [op_apply_eigenbasis', _root_.sum_apply]
    have hterm : ∀ π, ((w π : ℂ) • (U π).comp (σ.op.comp (adjoint (U π)))) (ρ.eigenbasis q)
        = ((w π : ℂ) * (σ.eigenvalueDist (π q) : ℂ)) • ρ.eigenbasis q := by
      intro π
      rw [_root_.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, hadj π q, op_apply_eigenbasis', map_smul, hUapply π q,
        smul_smul]
    rw [Finset.sum_congr rfl (fun π _ => hterm π), ← Finset.sum_smul]
    have hpt : (ρ.eigenvalueDist q : ℂ) = ∑ π, (w π : ℂ) * (σ.eigenvalueDist (π q) : ℂ) := by
      have hc : ρ.eigenvalueDist q = ∑ π, w π * σ.eigenvalueDist (π q) := by
        have h0 := congrFun hwdist q
        rw [Finset.sum_apply] at h0
        simpa only [Pi.smul_apply, Matrix.permMatrix_mulVec, Function.comp_apply,
          smul_eq_mul] using h0
      rw [hc]; push_cast; ring
    rw [hpt]
  refine ⟨_, inferInstance, w, U, hw0, hwsum, hunit, ?_⟩
  exact ρ.eigenbasis.ext_inner_basis (fun p q => by rw [hvec q])

/-- **The inverse-square-root pseudo-inverse `(√ρ)⁺` of a density operator.** The spectral operator
`∑ₖ (√λₖ)⁻¹ |bₖ⟩⟨bₖ|` over `ρ`'s orthonormal eigenbasis `bₖ = ρ.eigenbasis k` with eigenvalues
`λₖ = ρ.eigenvalueDist k`, inverting each *non-zero* `√λₖ` and sending the kernel (zero eigenvalues)
to `0` (the real field inverse is `0` at `0`). It is the Moore–Penrose pseudo-inverse of `√ρ`:
`sqrtPseudoInverse ρ` squares to `ρ.pseudoInverse` and is the operator that "divides by `√ρ` on the
support" in the converse of Nielsen's theorem. Defined spectrally, mirroring
`State.pseudoInverse`. -/
def sqrtPseudoInverse (ρ : State S) : S.space →L[ℂ] S.space :=
  ∑ k, (((Real.sqrt (ρ.eigenvalueDist k))⁻¹ : ℝ) : ℂ) •
    rankOne ℂ (ρ.eigenbasis k) (ρ.eigenbasis k)

/-- **Spectral action of `(√ρ)⁺`**: `(√ρ)⁺ bⱼ = (√λⱼ)⁻¹ bⱼ` on each eigenvector `bⱼ`, mapping the
kernel (zero eigenvalues) to `0`. -/
@[simp]
theorem sqrtPseudoInverse_apply_eigenbasis (ρ : State S)
    (j : Fin (Module.finrank ℂ S.space)) :
    ρ.sqrtPseudoInverse (ρ.eigenbasis j)
      = (((Real.sqrt (ρ.eigenvalueDist j))⁻¹ : ℝ) : ℂ) • ρ.eigenbasis j := by
  rw [sqrtPseudoInverse, _root_.sum_apply, Finset.sum_eq_single j]
  · rw [_root_.smul_apply, rankOne_apply, inner_eigenbasis_self, one_smul]
  · intro k _ hk
    rw [_root_.smul_apply, rankOne_apply,
      orthonormal_iff_ite.mp ρ.eigenbasis.orthonormal k j, ite_eq_right hk, zero_smul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- `(√ρ)⁺` is self-adjoint: each summand `(√λₖ)⁻¹ |bₖ⟩⟨bₖ|` is a real scalar times a self-adjoint
rank-one projector. -/
theorem isSelfAdjoint_sqrtPseudoInverse (ρ : State S) : IsSelfAdjoint ρ.sqrtPseudoInverse := by
  rw [sqrtPseudoInverse]
  refine isSelfAdjoint_sum Finset.univ fun k _ => ?_
  rw [Complex.coe_smul]
  refine (IsSelfAdjoint.all _).smul ?_
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

/-- `(√ρ)⁺ ∘ (√ρ)⁺ = ρ⁻¹`: the square of the inverse-square-root pseudo-inverse is the
Moore–Penrose pseudo-inverse of `ρ`, eigenvalue-by-eigenvalue `((√λ)⁻¹)² = λ⁻¹`. -/
theorem sqrtPseudoInverse_comp_self (ρ : State S) :
    ρ.sqrtPseudoInverse.comp ρ.sqrtPseudoInverse = ρ.pseudoInverse := by
  refine ContinuousLinearMap.coe_injective (ρ.eigenbasis.toBasis.ext fun j => ?_)
  have hpi : ρ.pseudoInverse (ρ.eigenbasis j)
      = (((ρ.eigenvalueDist j)⁻¹ : ℝ) : ℂ) • ρ.eigenbasis j :=
    ρ.pseudoInverse_apply_eigenvectorBasis j
  have hsq : (Real.sqrt (ρ.eigenvalueDist j))⁻¹ * (Real.sqrt (ρ.eigenvalueDist j))⁻¹
      = (ρ.eigenvalueDist j)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (ρ.eigenvalueDist_nonneg j)]
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, sqrtPseudoInverse_apply_eigenbasis, map_smul, smul_smul, hpi]
  rw [← Complex.ofReal_mul, hsq]

/-- `(√ρ)⁺` commutes with `ρ`: `(√ρ)⁺ ∘ ρ = ρ ∘ (√ρ)⁺` (both are spectral in `ρ`). -/
theorem sqrtPseudoInverse_comp_op_comm (ρ : State S) :
    ρ.sqrtPseudoInverse.comp ρ.op = ρ.op.comp ρ.sqrtPseudoInverse := by
  refine ContinuousLinearMap.coe_injective (ρ.eigenbasis.toBasis.ext fun j => ?_)
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, op_apply_eigenbasis', sqrtPseudoInverse_apply_eigenbasis,
    map_smul]
  rw [smul_comm]

/-- **One-way LOCC convertibility of reduced states** (the standard protocol form, N&C
Proposition 12.14). `ρ.LOCCConvertible σ` holds when Alice can perform a single measurement `{Mⱼ}`
on her system that carries the reduced state `ρ` to `σ` *deterministically*: for a probability
distribution `pⱼ` and **every** outcome `j`, `Mⱼ ρ Mⱼ† = pⱼ σ`.

Operationally (Nielsen's theorem, N&C Theorem 12.15): Alice measures `{Mⱼ}`, obtains outcome `j`
with probability `pⱼ`, and her reduced state is `σ` regardless of `j`; Bob then rotates his half to
the target pure state by a local unitary (Exercises 2.80/2.81). This is the density-operator content
of "`|ψ⟩` may be transformed to `|φ⟩` by LOCC". The quantifier over *general* LOCC protocols is not
formalised: Proposition 12.14 (`Proposition12_14`) reduces any finite-round two-way protocol to
exactly this one-way form, so this predicate captures the operational condition without a
protocol-tree formalism (which the library does not provide). -/
def LOCCConvertible (ρ σ : State S) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (m : Measurement ι S) (p : ι → ℝ),
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧
      ∀ j, (m.op j).comp (ρ.op.comp (adjoint (m.op j))) = (p j : ℂ) • σ.op

/-- **Forward direction of Nielsen's theorem** (N&C Theorem 12.15, `⟹`): if the reduced state `ρ`
can be converted to `σ` by a one-way LOCC measurement, then `ρ ≺ σ`.

Following N&C's proof, polar-decompose `Aⱼ := Mⱼ √ρ`. Since `√ρ` is self-adjoint with `√ρ √ρ = ρ`,
we have `Aⱼ Aⱼ† = Mⱼ ρ Mⱼ† = pⱼ σ` (the LOCC hypothesis) while `Aⱼ† Aⱼ = √ρ Mⱼ† Mⱼ √ρ`. The
polar-decomposition unitary equivalence `Aⱼ† Aⱼ = Uⱼ† (Aⱼ Aⱼ†) Uⱼ`
(`ContinuousLinearMap.exists_unitary_star_mul_self_eq_conj`, `Uⱼ` unitary) then gives
`Aⱼ† Aⱼ = pⱼ Uⱼ† σ Uⱼ`. Summing over `j` and
using the completeness relation `∑ⱼ Mⱼ† Mⱼ = 1` collapses the left side to `√ρ √ρ = ρ`, so
`ρ = ∑ⱼ pⱼ Uⱼ† σ Uⱼ = ∑ⱼ pⱼ Wⱼ σ Wⱼ†` with `Wⱼ := Uⱼ†` unitary. The reverse operator-majorization
theorem `majorize_of_op_eq_sum_unitary_conj` (the state-level reverse of N&C Theorem 12.13)
then gives `ρ ≺ σ`. All the operator algebra is carried out in the `*`/`star` endomorphism ring of
`S.space →L[ℂ] S.space` (where `f * g = f.comp g` and `star = adjoint`). -/
theorem LOCCConvertible.majorize {ρ σ : State S} (h : ρ.LOCCConvertible σ) : ρ.Majorize σ := by
  classical
  obtain ⟨ι, hfin, m, p, hp, hsum, heq⟩ := h
  let := hfin
  -- `√ρ`, self-adjoint with `√ρ √ρ = ρ`.
  set sq : S.space →L[ℂ] S.space := cfc Real.sqrt ρ.op with hsqdef
  have hsqsa : adjoint sq = sq := by rw [hsqdef]; exact ρ.adjoint_cfc_sqrt_op
  have hsqsa_star : star sq = sq := by rw [ContinuousLinearMap.star_eq_adjoint]; exact hsqsa
  have hsqsq : sq * sq = ρ.op := by
    have hh := ContinuousLinearMap.cfc_sqrt_comp_adjoint_eq_self_of_nonneg ρ.isDensity.nonneg
    rw [← hsqdef, hsqsa] at hh
    rwa [← ContinuousLinearMap.mul_def] at hh
  -- The completeness relation `∑ⱼ Mⱼ† Mⱼ = 1`, in `*`/`star` form.
  have hcomplete : ∑ j, star (m.op j) * m.op j = 1 := by
    have := m.complete
    simpa only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint] using this
  -- `Aⱼ := Mⱼ √ρ`.
  set A : ι → (S.space →L[ℂ] S.space) := fun j => (m.op j) * sq with hAdef
  -- Per outcome, a unitary `Uⱼ` witnessing `Aⱼ† Aⱼ = pⱼ • Uⱼ† σ Uⱼ`: the polar-decomposition
  -- unitary equivalence `Aⱼ† Aⱼ = Uⱼ† (Aⱼ Aⱼ†) Uⱼ` (general lemma) fed `Aⱼ Aⱼ† = pⱼ σ` (physics).
  have hUexists : ∀ j, ∃ U ∈ unitary (S.space →L[ℂ] S.space),
      star (A j) * A j = (p j : ℂ) • (star U * σ.op * U) := by
    intro j
    obtain ⟨U, hU, hswap⟩ := ContinuousLinearMap.exists_unitary_star_mul_self_eq_conj (A j)
    -- `Aⱼ Aⱼ† = Mⱼ ρ Mⱼ† = pⱼ • σ`.
    have hAAstar_eq : A j * star (A j) = (p j : ℂ) • σ.op := by
      have e1 : A j * star (A j) = (m.op j) * (sq * sq) * star (m.op j) := by
        simp only [hAdef]
        rw [star_mul, hsqsa_star]
        simp only [mul_assoc]
      rw [e1, hsqsq]
      have hj := heq j
      rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
        ← ContinuousLinearMap.star_eq_adjoint, ← mul_assoc] at hj
      exact hj
    exact ⟨U, hU, by rw [hswap, hAAstar_eq, mul_smul_comm, smul_mul_assoc]⟩
  -- `∑ⱼ Aⱼ† Aⱼ = √ρ (∑ⱼ Mⱼ† Mⱼ) √ρ = √ρ √ρ = ρ`.
  have hSumAA : ∑ j, star (A j) * A j = ρ.op := by
    have hterm : ∀ j, star (A j) * A j = sq * (star (m.op j) * m.op j) * sq := by
      intro j
      simp only [hAdef]
      rw [star_mul, hsqsa_star]
      simp only [mul_assoc]
    calc ∑ j, star (A j) * A j
        = ∑ j, sq * (star (m.op j) * m.op j) * sq := by simp_rw [hterm]
      _ = sq * (∑ j, star (m.op j) * m.op j) * sq := by rw [Finset.mul_sum, Finset.sum_mul]
      _ = sq * 1 * sq := by rw [hcomplete]
      _ = ρ.op := by rw [mul_one, hsqsq]
  -- Assemble `ρ = ∑ⱼ pⱼ Uⱼ† σ Uⱼ` and apply the reverse operator-majorization theorem.
  choose U hU hUeq using hUexists
  have hfinal : ρ.op = ∑ j, (p j : ℂ) • (star (U j) * σ.op * U j) := by
    rw [← hSumAA]
    exact Finset.sum_congr rfl fun j _ => hUeq j
  refine majorize_of_op_eq_sum_unitary_conj ρ σ hp hsum (fun j => Unitary.star_mem (hU j)) ?_
  rw [hfinal]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, star_star,
    mul_assoc]

/-- `ρ.op` is self-adjoint (a positive operator is self-adjoint). A local helper; the public
`State.isSelfAdjoint_op` lives in a different module, so this avoids a cross-module name clash. -/
private theorem op_isSelfAdjoint (ρ : State S) : IsSelfAdjoint ρ.op :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp ρ.isDensity.nonneg).isSelfAdjoint

/-- `(√ρ)⁺ (√ρ)⁺ = ρ⁻¹` in `*`-ring form. -/
private theorem sqrtPseudoInverse_mul_self_eq (ρ : State S) :
    ρ.sqrtPseudoInverse * ρ.sqrtPseudoInverse = ρ.pseudoInverse := by
  rw [ContinuousLinearMap.mul_def]; exact ρ.sqrtPseudoInverse_comp_self

/-- The Moore–Penrose identity `ρ ρ⁻¹ ρ = ρ` in `*`-ring form. -/
private theorem op_mul_pseudoInverse_mul_op (ρ : State S) :
    ρ.op * ρ.pseudoInverse * ρ.op = ρ.op := by
  have hh := ρ.op_comp_pseudoInverse_comp_op
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← mul_assoc] at hh
  exact hh

/-- **The support projector `Pₛ = (√ρ)⁺ ρ (√ρ)⁺`** of a density operator: the orthogonal projector
onto the support (range) of `ρ`. Built from the inverse-square-root pseudo-inverse `(√ρ)⁺`; it is a
self-adjoint idempotent (`isSelfAdjoint_supportProjector`, `isIdempotentElem_supportProjector`) that
restricts to the identity on the support (`supportProjector_comp_op` : `Pₛ ρ = ρ`). Defined
spectrally. -/
def supportProjector (ρ : State S) : S.space →L[ℂ] S.space :=
  ρ.sqrtPseudoInverse * ρ.op * ρ.sqrtPseudoInverse

/-- **The kernel projector `Pₖ = 1 - Pₛ`** of a density operator: the orthogonal projector onto
`ker ρ`, complementary to the support projector. Self-adjoint idempotent
(`isSelfAdjoint_kernelProjector`, `isIdempotentElem_kernelProjector`) that annihilates `ρ`
(`kernelProjector_comp_op` : `Pₖ ρ = 0`). -/
def kernelProjector (ρ : State S) : S.space →L[ℂ] S.space :=
  1 - ρ.supportProjector

/-- The support projector is self-adjoint. -/
theorem isSelfAdjoint_supportProjector (ρ : State S) : IsSelfAdjoint ρ.supportProjector := by
  have hsi : star ρ.sqrtPseudoInverse = ρ.sqrtPseudoInverse := ρ.isSelfAdjoint_sqrtPseudoInverse
  have hop : star ρ.op = ρ.op := ρ.op_isSelfAdjoint
  change star ρ.supportProjector = ρ.supportProjector
  rw [supportProjector]
  simp only [star_mul, hsi, hop, mul_assoc]

/-- **The support projector restricts to the identity on the support: `Pₛ ρ = ρ`** (Moore–Penrose).
`(√ρ)⁺ ρ (√ρ)⁺ ρ = (√ρ)⁺ ρ (√ρ)⁺·... ` collapses via `(√ρ)⁺(√ρ)⁺ = ρ⁻¹` and `ρ ρ⁻¹ ρ = ρ`. -/
theorem supportProjector_comp_op (ρ : State S) : ρ.supportProjector.comp ρ.op = ρ.op := by
  have hcomm : ρ.sqrtPseudoInverse * ρ.op = ρ.op * ρ.sqrtPseudoInverse := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
    exact ρ.sqrtPseudoInverse_comp_op_comm
  rw [← ContinuousLinearMap.mul_def, supportProjector, hcomm,
    show ρ.op * ρ.sqrtPseudoInverse * ρ.sqrtPseudoInverse * ρ.op
        = ρ.op * (ρ.sqrtPseudoInverse * ρ.sqrtPseudoInverse) * ρ.op by simp only [mul_assoc],
    ρ.sqrtPseudoInverse_mul_self_eq, ρ.op_mul_pseudoInverse_mul_op]

/-- The support projector is idempotent: `Pₛ Pₛ = Pₛ`. -/
theorem isIdempotentElem_supportProjector (ρ : State S) :
    IsIdempotentElem ρ.supportProjector := by
  change ρ.supportProjector * ρ.supportProjector = ρ.supportProjector
  rw [supportProjector,
    show (ρ.sqrtPseudoInverse * ρ.op * ρ.sqrtPseudoInverse) *
          (ρ.sqrtPseudoInverse * ρ.op * ρ.sqrtPseudoInverse)
        = ρ.sqrtPseudoInverse * ρ.op * (ρ.sqrtPseudoInverse * ρ.sqrtPseudoInverse) *
            (ρ.op * ρ.sqrtPseudoInverse) by simp only [mul_assoc], ρ.sqrtPseudoInverse_mul_self_eq,
    show ρ.sqrtPseudoInverse * ρ.op * ρ.pseudoInverse * (ρ.op * ρ.sqrtPseudoInverse)
        = ρ.sqrtPseudoInverse * (ρ.op * ρ.pseudoInverse * ρ.op) * ρ.sqrtPseudoInverse by
        simp only [mul_assoc], ρ.op_mul_pseudoInverse_mul_op]

/-- The kernel projector is self-adjoint. -/
theorem isSelfAdjoint_kernelProjector (ρ : State S) : IsSelfAdjoint ρ.kernelProjector := by
  change star ρ.kernelProjector = ρ.kernelProjector
  rw [kernelProjector, star_sub, star_one, ρ.isSelfAdjoint_supportProjector]

/-- The kernel projector is idempotent: `Pₖ Pₖ = Pₖ`. -/
theorem isIdempotentElem_kernelProjector (ρ : State S) :
    IsIdempotentElem ρ.kernelProjector := by
  change ρ.kernelProjector * ρ.kernelProjector = ρ.kernelProjector
  have hpr : ρ.supportProjector * ρ.supportProjector = ρ.supportProjector :=
    ρ.isIdempotentElem_supportProjector
  rw [kernelProjector, show (1 - ρ.supportProjector) * (1 - ρ.supportProjector)
      = 1 - ρ.supportProjector - ρ.supportProjector + ρ.supportProjector * ρ.supportProjector by
      noncomm_ring, hpr]
  abel

/-- **The kernel projector annihilates `ρ`: `Pₖ ρ = 0`.** Since `Pₛ ρ = ρ`, `(1 - Pₛ) ρ = 0`. -/
theorem kernelProjector_comp_op (ρ : State S) : ρ.kernelProjector.comp ρ.op = 0 := by
  have hsupp : ρ.supportProjector * ρ.op = ρ.op := by
    rw [ContinuousLinearMap.mul_def]; exact ρ.supportProjector_comp_op
  rw [← ContinuousLinearMap.mul_def, kernelProjector, sub_mul, one_mul, hsupp, sub_self]

/-- **Converse of Nielsen's theorem** (Nielsen–Chuang Theorem 12.15, `⟸`), the reduced-state crux:
if `ρ ≺ σ` then `ρ` can be converted to `σ` by a one-way LOCC measurement. This is the direction
that *constructs* the protocol from the majorization condition, and it needs **no invertibility
hypothesis** on `ρ` (N&C Exercise 12.20): the measurement operators are built from the
inverse-square-root pseudo-inverse `(√ρ)⁺`, which acts on the support of `ρ` and sends its kernel to
`0`.

By the forward operator-majorization theorem (`exists_op_eq_sum_unitary_conj_of_majorize`, N&C
Theorem 12.13) `ρ = ∑ⱼ pⱼ Uⱼ σ Uⱼ†` with each `Uⱼ` unitary. Take measurement operators
`Mⱼ = √pⱼ · √σ Uⱼ† (√ρ)⁺` (indexed by `some j`) together with one extra outcome `M₀ = Pₖ`, the
projector onto `ker ρ`, with probability `0`. Writing `Pₛ = (√ρ)⁺ ρ (√ρ)⁺` for the projector onto
the support of `ρ` (so `Pₖ = 1 - Pₛ`):

* **completeness** `∑ Mᵢ† Mᵢ = (√ρ)⁺ ρ (√ρ)⁺ + Pₖ = Pₛ + Pₖ = 1`;
* **support outcomes** `Mⱼ ρ Mⱼ† = pⱼ √σ Uⱼ† Pₛ Uⱼ √σ = pⱼ σ`: since `Pₛ = 1 - Pₖ`, this needs
  `pⱼ (√σ Uⱼ† Pₖ Uⱼ √σ) = 0`, which holds because `√σ Uⱼ† Pₖ = 0` whenever `pⱼ > 0` — from
  `Pₖ ρ Pₖ = 0` and `⟪u, Pₖ ρ Pₖ u⟫ = ∑ₖ pₖ ‖√σ Uₖ† Pₖ u‖²`, every summand with `pⱼ > 0` vanishes;
  and `Mⱼ = 0` when `pⱼ = 0`;
* **kernel outcome** `M₀ ρ M₀† = Pₖ ρ Pₖ = 0 = 0 · σ`.

All the operator algebra is carried out in the `*`/`star` endomorphism ring. Combined with the
forward `LOCCConvertible.majorize`, this is Nielsen's theorem for the reduced states. -/
theorem LOCCConvertible_of_majorize {ρ σ : State S} (h : ρ.Majorize σ) :
    ρ.LOCCConvertible σ := by
  classical
  obtain ⟨ι, hfin, p, U, hp, hsum, hU, hρ⟩ := ρ.exists_op_eq_sum_unitary_conj_of_majorize h
  let := hfin
  -- `√σ`, self-adjoint with `√σ √σ = σ`.
  set sσ : S.space →L[ℂ] S.space := cfc Real.sqrt σ.op with hsσdef
  have hsσadj : adjoint sσ = sσ := by rw [hsσdef]; exact σ.adjoint_cfc_sqrt_op
  have hsσsa : star sσ = sσ := by rw [ContinuousLinearMap.star_eq_adjoint]; exact hsσadj
  have hsσsq : sσ * sσ = σ.op := by
    have hh := ContinuousLinearMap.cfc_sqrt_comp_adjoint_eq_self_of_nonneg σ.isDensity.nonneg
    rw [← hsσdef, hsσadj] at hh
    rwa [← ContinuousLinearMap.mul_def] at hh
  -- `(√ρ)⁺`, self-adjoint.
  set si : S.space →L[ℂ] S.space := ρ.sqrtPseudoInverse with hsidef
  have hsisa : star si = si := ρ.isSelfAdjoint_sqrtPseudoInverse
  -- `ρ` as a `*`-ring sum of unitary conjugates of `σ`.
  have hρ' : ρ.op = ∑ j, (p j : ℂ) • (U j * σ.op * star (U j)) := by
    rw [hρ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.star_eq_adjoint, ← mul_assoc]
  -- The named support/kernel projectors and the projector facts they carry (API above).
  set pr : S.space →L[ℂ] S.space := ρ.supportProjector with hprdef
  set pk : S.space →L[ℂ] S.space := ρ.kernelProjector with hpkdef
  have hpr_si : pr = si * ρ.op * si := by rw [hprdef, hsidef, supportProjector]
  have hpksa : star pk = pk := ρ.isSelfAdjoint_kernelProjector
  have hpkpk : pk * pk = pk := ρ.isIdempotentElem_kernelProjector
  have hpkop : pk * ρ.op = 0 := by
    rw [hpkdef, ContinuousLinearMap.mul_def]; exact ρ.kernelProjector_comp_op
  have hpr_eq : pr = 1 - pk := by rw [hprdef, hpkdef, kernelProjector]; abel
  -- The measurement over `Option ι`: the support operators plus the kernel projector `pk`.
  set M : Option ι → (S.space →L[ℂ] S.space) :=
    fun i => i.elim pk (fun j => (Real.sqrt (p j) : ℂ) • (sσ * star (U j) * si))
  set pp : Option ι → ℝ := fun i => i.elim 0 p
  have hMnone : M none = pk := rfl
  have hMsome : ∀ j, M (some j) = (Real.sqrt (p j) : ℂ) • (sσ * star (U j) * si) := fun _ => rfl
  have hppnone : pp none = 0 := rfl
  have hppsome : ∀ j, pp (some j) = p j := fun _ => rfl
  have hMstar : ∀ j, star (M (some j)) = (Real.sqrt (p j) : ℂ) • (si * U j * sσ) := by
    intro j
    rw [hMsome, star_smul, star_mul, star_mul, hsisa, star_star, hsσsa,
      show star ((Real.sqrt (p j) : ℝ) : ℂ) = ((Real.sqrt (p j) : ℝ) : ℂ) from
        Complex.conj_ofReal _, mul_assoc]
  -- The kernel lemma: `pⱼ (√σ Uⱼ† pk Uⱼ √σ) = 0` for every outcome.
  have hkernel : ∀ j, (p j : ℂ) • (sσ * star (U j) * pk * U j * sσ) = 0 := by
    have hpkoppk : pk * ρ.op * pk = 0 := by rw [hpkop, zero_mul]
    have hpkadj : adjoint pk = pk := by rw [← ContinuousLinearMap.star_eq_adjoint]; exact hpksa
    have hqf : ∀ u : S.space, ∑ k, p k * ‖(sσ * star (U k) * pk) u‖ ^ 2 = 0 := by
      intro u
      have hval : inner ℂ (pk u) (ρ.op (pk u)) = 0 := by
        have e : inner ℂ (pk u) (ρ.op (pk u)) = inner ℂ u ((pk * ρ.op * pk) u) := by
          rw [show (pk * ρ.op * pk) u = pk (ρ.op (pk u)) by
                simp only [mul_apply_eq_comp]]
          conv_rhs => rw [← ContinuousLinearMap.adjoint_inner_left, hpkadj]
        rw [e, hpkoppk, _root_.zero_apply, inner_zero_right]
      have hexp : inner ℂ (pk u) (ρ.op (pk u))
          = ((∑ k, p k * ‖(sσ * star (U k) * pk) u‖ ^ 2 : ℝ) : ℂ) := by
        rw [hρ', Complex.ofReal_sum]
        simp only [_root_.sum_apply, _root_.smul_apply,
          mul_apply_eq_comp, inner_sum, inner_smul_right]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← ContinuousLinearMap.adjoint_inner_left (U k), ← ContinuousLinearMap.star_eq_adjoint,
          ← hsσsq, mul_apply_eq_comp,
          ← ContinuousLinearMap.adjoint_inner_left sσ, hsσadj,
          show sσ (star (U k) (pk u)) = (sσ * star (U k) * pk) u by
            simp only [mul_apply_eq_comp],
          inner_self_eq_norm_sq_to_K]
        norm_num
      rw [hval] at hexp
      exact_mod_cast hexp.symm
    intro j
    rcases eq_or_lt_of_le (hp j) with h0 | hpos
    · rw [← h0, Complex.ofReal_zero, zero_smul]
    · have hG : sσ * star (U j) * pk = 0 := by
        refine ContinuousLinearMap.ext fun u => ?_
        have hterm : p j * ‖(sσ * star (U j) * pk) u‖ ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun k (_ : k ∈ Finset.univ) => mul_nonneg (hp k) (sq_nonneg _))).mp (hqf u) j
            (Finset.mem_univ j)
        have hn2 : ‖(sσ * star (U j) * pk) u‖ ^ 2 = 0 := by
          rcases mul_eq_zero.mp hterm with hh | hh
          · exact absurd hh hpos.ne'
          · exact hh
        have : ‖(sσ * star (U j) * pk) u‖ = 0 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hn2
          simpa using this
        rw [_root_.zero_apply]
        exact norm_eq_zero.mp this
      rw [show sσ * star (U j) * pk * U j * sσ = (sσ * star (U j) * pk) * (U j * sσ) by
            simp only [mul_assoc], hG, zero_mul, smul_zero]
  -- Completeness `∑ Mᵢ† Mᵢ = 1`.
  have hcomplete : ∑ i, (adjoint (M i)).comp (M i) = 1 := by
    have hnone : (adjoint (M none)).comp (M none) = pk := by
      rw [hMnone, ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, hpksa,
        hpkpk]
    have hsome : ∀ j, (adjoint (M (some j))).comp (M (some j))
        = (p j : ℂ) • (si * U j * σ.op * star (U j) * si) := by
      intro j
      rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, hMstar j, hMsome,
        show ((Real.sqrt (p j) : ℂ) • (si * U j * sσ)) *
              ((Real.sqrt (p j) : ℂ) • (sσ * star (U j) * si))
            = ((Real.sqrt (p j) : ℂ) * (Real.sqrt (p j) : ℂ)) •
                ((si * U j * sσ) * (sσ * star (U j) * si)) by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul],
        ← Complex.ofReal_mul, Real.mul_self_sqrt (hp j)]
      congr 1
      rw [show (si * U j * sσ) * (sσ * star (U j) * si) = si * U j * (sσ * sσ) * star (U j) * si by
            simp only [mul_assoc], hsσsq]
    rw [Fintype.sum_option, hnone]
    rw [show (∑ j, (adjoint (M (some j))).comp (M (some j))) = pr by
      rw [hpr_si, hρ', Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsome j]
      simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]]
    rw [hpr_eq]; abel
  -- The state-transfer condition `Mᵢ ρ Mᵢ† = ppᵢ • σ`.
  have htransfer : ∀ i, (M i).comp (ρ.op.comp (adjoint (M i))) = (pp i : ℂ) • σ.op := by
    rintro (_ | j)
    · rw [hMnone, hppnone]
      simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint, hpksa]
      rw [← mul_assoc, hpkop, zero_mul, Complex.ofReal_zero, zero_smul]
    · have hUunit : star (U j) * U j = 1 := (Unitary.mem_iff.mp (hU j)).1
      rw [hppsome]
      simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint]
      rw [hMstar j, hMsome,
        show ((Real.sqrt (p j) : ℂ) • (sσ * star (U j) * si)) *
              (ρ.op * ((Real.sqrt (p j) : ℂ) • (si * U j * sσ)))
            = ((Real.sqrt (p j) : ℂ) * (Real.sqrt (p j) : ℂ)) •
                ((sσ * star (U j) * si) * (ρ.op * (si * U j * sσ))) by
          rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul],
        ← Complex.ofReal_mul, Real.mul_self_sqrt (hp j),
        show (sσ * star (U j) * si) * (ρ.op * (si * U j * sσ))
            = sσ * star (U j) * (si * ρ.op * si) * U j * sσ by simp only [mul_assoc],
        ← hpr_si, hpr_eq,
        show sσ * star (U j) * (1 - pk) * U j * sσ
            = sσ * (star (U j) * U j) * sσ - sσ * star (U j) * pk * U j * sσ by noncomm_ring,
        hUunit, mul_one, hsσsq, smul_sub, hkernel, sub_zero]
  -- Probabilities are a distribution.
  have hpp_nonneg : ∀ i, 0 ≤ pp i := by
    rintro (_ | j)
    · exact le_of_eq hppnone.symm
    · rw [hppsome]; exact hp j
  have hpp_sum : ∑ i, pp i = 1 := by
    rw [Fintype.sum_option, hppnone, zero_add]
    simp only [hppsome]
    exact hsum
  exact ⟨Option ι, inferInstance, ⟨M, hcomplete⟩, pp, hpp_nonneg, hpp_sum, htransfer⟩

end State

end AxQM
