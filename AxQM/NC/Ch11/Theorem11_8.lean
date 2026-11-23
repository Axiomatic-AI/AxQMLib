/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Purity
import AxQM.Postulates.API.PureMarginalEntropy

/-!
# Nielsen & Chuang, Theorem 11.8 (Basic properties of von Neumann entropy)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.8, p. 513.

The theorem collects the basic properties of the von Neumann entropy `S(ρ)` of a state `ρ`:

1. `S(ρ) ≥ 0`, with `S(ρ) = 0` **iff** `ρ` is pure.
2. In a `d`-dimensional space `S(ρ) ≤ log d`, with equality **iff** `ρ` is the maximally mixed
   state `I/d`.
3. If a composite system `AB` is in a pure state then `S(A) = S(B)`.
4. If probabilities `pᵢ` and states `ρᵢ` have support on mutually orthogonal subspaces, then
   `S(∑ᵢ pᵢ ρᵢ) = H(pᵢ) + ∑ᵢ pᵢ S(ρᵢ)`.
5. **Joint entropy theorem:** for probabilities `pᵢ`, orthonormal states `|i⟩` of a system `A`, and
   arbitrary states `ρᵢ` of a system `B`, `S(∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ) = H(pᵢ) + ∑ᵢ pᵢ S(ρᵢ)`.

**Base convention.** The library measures entropy in *nats* (natural logarithm), so `S` and `log`
throughout are natural log. Every statement below is invariant under the choice of logarithm base
(both sides scale by the same factor), a faithful reformulation of N&C's base-2 presentation.

## The formalisation

Theorem 11.8 is a five-part theorem, most parts requiring their own spectral development.

**Forward directions and value facts of parts (1)–(2):**

* Part 1, non-negativity `S(ρ) ≥ 0` — `AxQM.State.vonNeumannEntropy_nonneg`
  (`AxQM/Postulates/API/Entropy.lean`).
* Part 1, `ρ` pure `⇒ S(ρ) = 0` — `AxQM.PureState.vonNeumannEntropy_toState_eq_zero`
  (for a `PureState`) and, for a general state satisfying `State.IsPure`,
  `AxQM.State.vonNeumannEntropy_eq_zero_of_isPure` **(this file)**.
* Part 1, converse `S(ρ) = 0 ⇒ ρ` pure — `AxQM.State.isPure_of_vonNeumannEntropy_eq_zero`,
  and hence the full first-item characterization `S(ρ) = 0 ↔ ρ` pure —
  `AxQM.State.vonNeumannEntropy_eq_zero_iff_isPure` **(this file)**.
* Part 2, upper bound `S(ρ) ≤ log d` — `AxQM.State.vonNeumannEntropy_le_log_finrank`
  (`AxQM/Postulates/API/Entropy.lean`).
* Part 2, value at the maximally mixed state `S(I/d) = log d` —
  `AxQM.State.vonNeumannEntropy_maximallyMixed` (`AxQM/Postulates/API/EntropyComposite.lean`).
* Part 2, equality characterization `S(ρ) = log d ↔ ρ = I/d` —
  `AxQM.State.vonNeumannEntropy_eq_log_finrank_iff_eq_maximallyMixed`, assembled from the
  forward value above and the converse `State.eq_maximallyMixed_of_vonNeumannEntropy_eq_log_finrank`
  (`AxQM/Postulates/API/EntropyExtremal.lean`).

**Analytic engine for the remaining parts.** Parts (3)–(5) and the equality-*characterizations* of
(1)–(2) all reduce a von Neumann entropy to the Shannon entropy of an eigenvalue spectrum presented
in a task-specific eigenbasis. That reduction is
`AxQM.State.vonNeumannEntropy_eq_entropy_of_isEigenbasis`
(`AxQM/Postulates/API/EntropySpectral.lean`): `S(ρ) = H(μ)` for any orthonormal basis diagonalizing
`ρ.op` with real eigenvalues `μ`.

**Part 3, `S(A) = S(B)` for a pure composite.**
`AxQM.PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`
(`AxQM/Postulates/API/PureMarginalEntropy.lean`): both reduced states of a bipartite pure state have
von Neumann entropy `H(λ²)`, the Shannon entropy of the squared Schmidt coefficients, so they agree.
The two reduced operators are read off a Schmidt decomposition `|ψ⟩ = ∑ᵢ λᵢ |aᵢ⟩|bᵢ⟩` as
`ρᴬ = ∑ᵢ λᵢ² |aᵢ⟩⟨aᵢ|` and `ρᴮ = ∑ᵢ λᵢ² |bᵢ⟩⟨bᵢ|`
(`LinearMap.partialTrace{Right,Left}_rankOne_eq_sum_rankOne_of_schmidt`), and the shared
orthonormal-eigenfamily engine `State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum`
(`AxQM/Postulates/API/EntropySpectral.lean`) evaluates each entropy to `H(λ²)`. It is also used in
Exercise 11.14 and in the reverse direction of Theorem 11.10.

**Part 4, orthogonal-support mixture identity.**
`AxQM.State.vonNeumannEntropy_mix_orthogonalSupport`
(`AxQM/Postulates/API/EntropyOrthogonalMixture.lean`): for a probability distribution `pᵢ` and
states `ρᵢ` with *pairwise orthogonal supports*, `S(∑ᵢ pᵢ ρᵢ) = H(pᵢ) + ∑ᵢ pᵢ S(ρᵢ)` (eq. (11.57)).
Here `State.support` is a `Submodule ℂ S.space`, built from the density operator `.op`. The proof
assembles the summands' eigenbases into a rank-one decomposition of the mixture that is orthonormal
on its support (orthogonal supports ⇒ cross terms vanish), applies the degenerate-weight engine
`State.vonNeumannEntropy_eq_entropy_of_rankOne_sum_orthonormal_on_ne_zero`
(`AxQM/Postulates/API/EntropySpectral.lean`), and splits the resulting Shannon entropy with the
grouping identity `Real.entropy_sigma_mul`
(`ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean`). The same file also contains the
equivalent constructive form `State.vonNeumannEntropy_mix_of_orthonormal_rankOne` (the
Theorem 11.10 equality "if" direction), which takes the jointly-orthonormal eigen-decompositions
as hypotheses rather than deriving them.

**Part 5, the joint entropy theorem.**
`AxQM.State.vonNeumannEntropy_jointEntropyTheorem`
(`AxQM/Postulates/API/EntropyJointTheorem.lean`): for probabilities `pᵢ`, an orthonormal family of
pure states `|i⟩ = e i` of a system `A` (`Orthonormal ℂ (fun i => (e i).vec)`), and *arbitrary*
states `ρᵢ` of a system `B`, `S(∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ) = H(pᵢ) + ∑ᵢ pᵢ S(ρᵢ)` (eq. (11.58)).
The orthonormality hypothesis is stated for the state vectors `.vec`. As N&C notes, it is "immediate
from the preceding result": the block states `|i⟩⟨i| ⊗ ρᵢ` have mutually orthogonal supports (their
operator product vanishes because `⟪i|j⟫ = 0` for `i ≠ j`), so part (4)
`State.vonNeumannEntropy_mix_orthogonalSupport` applies, and tensor additivity
`State.vonNeumannEntropy_tmul` with `S(|i⟩⟨i|) = 0` (`PureState.vonNeumannEntropy_toState_eq_zero`)
collapses each `S(|i⟩⟨i| ⊗ ρᵢ) = S(ρᵢ)`.
-/

namespace AxQM

variable {S : QSystem}

/-- **A pure state has zero von Neumann entropy** (Nielsen–Chuang Theorem 11.8, part (1), forward
direction, for a general state). If `ρ` is pure — `ρ = |ψ⟩⟨ψ|` for some `PureState ψ` — then
`S(ρ) = 0`. This is the `State.IsPure` form of `PureState.vonNeumannEntropy_toState_eq_zero`:
purity means `ρ.op` is a rank-one projector `|v⟩⟨v|` (`State.isPure_iff_exists_rankOne`), whose
spectrum is `(1, 0, …, 0)` and hence has zero Shannon entropy
(`ContinuousLinearMap.vonNeumannEntropy_rankOne_self`). -/
theorem State.vonNeumannEntropy_eq_zero_of_isPure (ρ : State S) (h : ρ.IsPure) :
    ρ.vonNeumannEntropy = 0 := by
  obtain ⟨v, hv, hop⟩ := ρ.isPure_iff_exists_rankOne.mp h
  rw [State.vonNeumannEntropy_def, hop]
  exact ContinuousLinearMap.vonNeumannEntropy_rankOne_self hv

/-- **A state of zero von Neumann entropy is pure** (Nielsen–Chuang Theorem 11.8, part (1),
converse direction): if `S(ρ) = 0` then `ρ` is pure.

Diagonalize `ρ.op` in its canonical orthonormal eigenbasis `e` with eigenvalue spectrum `μ`, a
probability distribution (`IsDensityOp.eigenvalues_nonneg` / `eigenvalues_sum_eq_one`). Then
`S(ρ) = H(μ)` (`vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq`), so `S(ρ) = 0` means the
Shannon entropy of the spectrum vanishes; the general point-mass characterization
`Real.entropy_eq_zero_iff` then forces exactly one eigenvalue `μ_k = 1` with the rest `0`. Hence the
spectral reconstruction `ρ.op = ∑ᵢ μᵢ |eᵢ⟩⟨eᵢ|` (`IsSelfAdjoint.spectral_sum`) collapses to the
single rank-one projector `|e_k⟩⟨e_k|` of the unit vector `e_k`, so `ρ` is pure by
`State.isPure_iff_exists_rankOne`. -/
theorem State.isPure_of_vonNeumannEntropy_eq_zero (ρ : State S) (h : ρ.vonNeumannEntropy = 0) :
    ρ.IsPure := by
  classical
  have := ρ.nontrivial_space
  have hsa : IsSelfAdjoint ρ.op := ρ.isDensity.isPositive.isSelfAdjoint
  have hfin : Module.finrank ℂ S.space = Module.finrank ℂ S.space := rfl
  have : Nonempty (Fin (Module.finrank ℂ S.space)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  -- The canonical spectrum `μ` is a probability distribution and `S(ρ) = H(μ) = 0`.
  have hnonneg : ∀ i, 0 ≤ hsa.isSymmetric.eigenvalues hfin i :=
    fun i => ρ.isDensity.eigenvalues_nonneg hfin i
  have hsum : ∑ i, hsa.isSymmetric.eigenvalues hfin i = 1 :=
    ρ.isDensity.eigenvalues_sum_eq_one hfin
  have hent : Real.entropy (fun i => hsa.isSymmetric.eigenvalues hfin i) = 0 := by
    rw [← ContinuousLinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq
      hsa.isSymmetric hfin, ← State.vonNeumannEntropy_def]
    exact h
  -- The vanishing entropy of the probability spectrum forces a point mass: `μ_k = 1`, rest `0`.
  obtain ⟨k, hμk, hrest⟩ := (Real.entropy_eq_zero_iff hnonneg hsum).mp hent
  -- Spectral reconstruction collapses to the single rank-one projector `|e_k⟩⟨e_k|`.
  refine ρ.isPure_iff_exists_rankOne.mpr
    ⟨hsa.isSymmetric.eigenvectorBasis hfin k,
      (hsa.isSymmetric.eigenvectorBasis hfin).norm_eq_one k, ?_⟩
  refine (hsa.spectral_sum hfin).trans ?_
  rw [Finset.sum_eq_single k (fun i _ hik => by simp [hrest i hik])
      (fun hknot => absurd (Finset.mem_univ k) hknot),
    hμk]
  simp

/-- **The von Neumann entropy vanishes exactly on pure states** (Nielsen–Chuang Theorem 11.8,
part (1)): `S(ρ) = 0 ↔ ρ` is pure. The forward direction is
`State.isPure_of_vonNeumannEntropy_eq_zero`; the backward direction is
`State.vonNeumannEntropy_eq_zero_of_isPure`. Together with `State.vonNeumannEntropy_nonneg`
(`S(ρ) ≥ 0`) this is the full first item of the theorem. -/
theorem State.vonNeumannEntropy_eq_zero_iff_isPure (ρ : State S) :
    ρ.vonNeumannEntropy = 0 ↔ ρ.IsPure :=
  ⟨ρ.isPure_of_vonNeumannEntropy_eq_zero, ρ.vonNeumannEntropy_eq_zero_of_isPure⟩

end AxQM
