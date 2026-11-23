/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SameNonzeroSpectrum
import AxQM.Postulates.API.SchmidtDecomposition
import AxQM.Postulates.API.EntropySpectral
import AxQM.Postulates.PartialTrace

/-!
# AxQM.Postulates.API — the reduced spectrum of a bipartite pure state

For a bipartite pure state `|ψ⟩ = ∑ᵢ λᵢ |aᵢ⟩|bᵢ⟩` (a Schmidt decomposition, N&C Theorem 2.7) the
left reduced density operator is `ρ_A = tr_B|ψ⟩⟨ψ| = ∑ᵢ λᵢ² |aᵢ⟩⟨aᵢ|`, so the **non-zero eigenvalues
of `ρ_A` are exactly the squared Schmidt coefficients `λᵢ²`**. This file records that fact and reads
off **both directions** of Nielsen & Chuang Exercise 12.22's reduced-spectrum comparison,
assembling the iff
`ψ.SameSchmidtCoeffs φ ↔ ρ_A(ψ) ≅ ρ_A(φ)`:

* **reduced spectrum from Schmidt coefficients** — `λ_{ρ_A} ≅ (λ²)`
  (`PureState.sameNonzero_sq_reducedLeft_eigenvalueDist`);
* **forward — identical Schmidt coefficients ⟹ same reduced spectrum** — two pure states sharing
  Schmidt coefficients have `≅` left reduced spectra
  (`PureState.sameNonzeroSpectrum_reducedLeft_of_sameSchmidtCoeffs`);
* **reverse — same reduced spectrum ⟹ identical Schmidt coefficients** — a `≅` on the reduced
  spectra promotes (via strict positivity of the coefficients) to a common ordered Schmidt family
  (`PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft`), and the two directions combine
  into the iff `PureState.sameSchmidtCoeffs_iff_sameNonzeroSpectrum_reducedLeft`.

The engine is a `SameNonzero` companion of the entropy workhorse
`State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum`: if `ρ.op = ∑ᵢ wᵢ |eᵢ⟩⟨eᵢ|` for an
*orthonormal* (possibly incomplete) family `e`, then the eigenvalue distribution of `ρ` has the same
non-zero entries as the weight list `w`
(`State.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum`).
Both read-offs share the eigenbasis-extension construction
`State.exists_eigenbasis_of_orthonormal_rankOne_sum` (extend `e` to a full basis by adjoining an
orthonormal basis of `(span e)ᗮ`, whose vectors are eigenvectors with eigenvalue `0`); here the
padded zeros drop out of the non-zero spectrum (`nonzeroEntries_sum_elim_zero`).

## Main statements

* `State.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum` — `w ≅ λ_ρ` whenever
  `ρ.op = ∑ᵢ wᵢ |eᵢ⟩⟨eᵢ|` for an orthonormal family `e`.
* `PureState.sameNonzero_sq_reducedLeft_eigenvalueDist` — `(λ²) ≅ λ_{ρ_A}` for a Schmidt-form
  decomposition of `ψ`; `PureState.sameNonzero_sq_reducedRight_eigenvalueDist` its right-factor
  mirror `(λ²) ≅ λ_{ρ_B}`.
* `PureState.sameNonzeroSpectrum_reducedLeft_reducedRight` — a pure state's two marginals are
  isospectral, `ρ_A(ψ) ≅ ρ_B(ψ)` (the reduced-spectrum bridge for Prop 12.14 off the swap-symmetric
  normal form).
* `PureState.sameNonzeroSpectrum_reducedLeft_of_sameSchmidtCoeffs` — the forward direction of
  Ex. 12.22's bridge: `ψ.SameSchmidtCoeffs φ ⟹ ρ_A(ψ) ≅ ρ_A(φ)`.
* `PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft` — the reverse direction:
  `ρ_A(ψ) ≅ ρ_A(φ) ⟹ ψ.SameSchmidtCoeffs φ`.
* `PureState.sameSchmidtCoeffs_iff_sameNonzeroSpectrum_reducedLeft` — the iff assembling both
  directions; `PureState.sameSchmidtCoeffs_iff_sameNonzeroSpectrum_reducedRight` the right-factor
  companion (via the marginal duality).
-/

open scoped TensorProduct

namespace AxQM

variable {S T : QSystem} {ι : Type*} [Fintype ι]

/-- **Same non-zero spectrum from an orthonormal eigenfamily.** If the density operator `ρ.op` is a
weighted sum of rank-one projectors onto an *orthonormal* family `e : ι → S.space` —
`ρ.op = ∑ᵢ wᵢ |eᵢ⟩⟨eᵢ|` — then the eigenvalue distribution `ρ.eigenvalueDist` has the same non-zero
entries as the weight list, `w ≅ λ_ρ`.

The `SameNonzero` companion of `State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum`, with
which it shares the eigenbasis-extension construction
`State.exists_eigenbasis_of_orthonormal_rankOne_sum`: that lemma extends `e` to a full orthonormal
basis `B` diagonalizing `ρ.op` with eigenvalue family `Sum.elim w 0` (the adjoined complement
vectors carry eigenvalue `0`). Feeding `B` into `State.sameNonzero_eigenvalueDist_of_isEigenbasis`
gives `(w ⊕ 0) ≅ λ_ρ`, and the padded zeros drop out (`nonzeroEntries_sum_elim_zero`). -/
theorem State.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum (ρ : State S)
    {e : ι → S.space} (he : Orthonormal ℂ e) (w : ι → ℝ)
    (hop : ρ.op = ∑ i, (w i : ℂ) • (InnerProductSpace.rankOne ℂ (e i)) (e i)) :
    SameNonzero w ρ.eigenvalueDist := by
  obtain ⟨B, hdiag⟩ := ρ.exists_eigenbasis_of_orthonormal_rankOne_sum he w hop
  exact (nonzeroEntries_sum_elim_zero w).symm.trans
    (ρ.sameNonzero_eigenvalueDist_of_isEigenbasis B hdiag)

/-- **The left reduced operator in the Schmidt basis.** For a bipartite pure state `ψ` with a
Schmidt-form decomposition `|ψ⟩ = ∑ᵢ lᵢ |aᵢ⟩|bᵢ⟩` (right factors `b` orthonormal — the only datum
the partial trace needs), the left reduced density operator is diagonal in Alice's Schmidt basis
with the squared coefficients: `ρ_A = tr_B|ψ⟩⟨ψ| = ∑ᵢ lᵢ² |aᵢ⟩⟨aᵢ|`. The left reduced operator is
the right partial trace of `|ψ⟩⟨ψ|`, which
`LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt` expands into this rank-one sum. The
`op`-level companion of `PureState.reducedLeft_toState_op` (`ρ_A = M M†`), in the form the
Schmidt-basis-identification argument of Proposition 12.14 consumes. -/
theorem PureState.reducedLeft_op_eq_sum_rankOne (ψ : PureState (S.compose T)) {n : ℕ}
    {l : Fin n → ℝ} {a : Fin n → S.space} {b : Fin n → T.space} (hb : Orthonormal ℂ b)
    (hψ : ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i) :
    ψ.toState.reducedLeft.op
      = ∑ i, ((l i ^ 2 : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (a i)) (a i) := by
  apply ContinuousLinearMap.coe_injective
  rw [State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op,
    ContinuousLinearMap.toLinearMap_sum]
  simp only [ContinuousLinearMap.toLinearMap_smul, Complex.ofReal_pow]
  exact LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt
    (stdOrthonormalBasis ℂ T.space) (Ψ := ψ.vec) l a b hb hψ

/-- **The right reduced operator in the Schmidt basis.** For a bipartite pure state `ψ` with a
Schmidt-form decomposition `|ψ⟩ = ∑ᵢ lᵢ |aᵢ⟩|bᵢ⟩` (left factors `a` orthonormal), the right reduced
density operator is diagonal in Bob's Schmidt basis with the squared coefficients:
`ρ_B = tr_A|ψ⟩⟨ψ| = ∑ᵢ lᵢ² |bᵢ⟩⟨bᵢ|`. The right-factor mirror of
`PureState.reducedLeft_op_eq_sum_rankOne`, via the *left* partial trace. -/
theorem PureState.reducedRight_op_eq_sum_rankOne (ψ : PureState (S.compose T)) {n : ℕ}
    {l : Fin n → ℝ} {a : Fin n → S.space} {b : Fin n → T.space} (ha : Orthonormal ℂ a)
    (hψ : ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i) :
    ψ.toState.reducedRight.op
      = ∑ i, ((l i ^ 2 : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (b i)) (b i) := by
  apply ContinuousLinearMap.coe_injective
  rw [State.reducedRight_op, LinearMap.coe_toContinuousLinearMap, PureState.toState_op,
    ContinuousLinearMap.toLinearMap_sum]
  simp only [ContinuousLinearMap.toLinearMap_smul, Complex.ofReal_pow]
  exact LinearMap.partialTraceLeft_rankOne_eq_sum_rankOne_of_schmidt
    (stdOrthonormalBasis ℂ S.space) (Ψ := ψ.vec) l a b
    (fun i j _ _ => orthonormal_iff_ite.mp ha i j) hψ

/-- **The left reduced spectrum is the squared Schmidt coefficients.** For a bipartite pure state
`ψ` with a Schmidt-form decomposition `|ψ⟩ = ∑ᵢ lᵢ |aᵢ⟩|bᵢ⟩` (orthonormal families `a`, `b`), the
eigenvalue distribution of the left reduced state `ρ_A = tr_B|ψ⟩⟨ψ|` has the same non-zero entries
as `(l²)`: `(λ²) ≅ λ_{ρ_A}`. This is the spectral content of Nielsen & Chuang Exercise 12.22 for a
single state.

Proof: `ρ_A.op = ∑ᵢ lᵢ² |aᵢ⟩⟨aᵢ|` (`PureState.reducedLeft_op_eq_sum_rankOne`), the sum of rank-one
projectors onto the orthonormal `a`. Recognition
(`State.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum`) then identifies the weight list `l²`
with the reduced spectrum. -/
theorem PureState.sameNonzero_sq_reducedLeft_eigenvalueDist (ψ : PureState (S.compose T)) {n : ℕ}
    {l : Fin n → ℝ} {a : Fin n → S.space} {b : Fin n → T.space} (ha : Orthonormal ℂ a)
    (hb : Orthonormal ℂ b) (hψ : ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i) :
    SameNonzero (fun i => l i ^ 2) ψ.toState.reducedLeft.eigenvalueDist :=
  ψ.toState.reducedLeft.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum ha
    (fun i => l i ^ 2) (ψ.reducedLeft_op_eq_sum_rankOne hb hψ)

/-- **The right reduced spectrum is the squared Schmidt coefficients.** For a bipartite pure state
`ψ` with a Schmidt-form decomposition `|ψ⟩ = ∑ᵢ lᵢ |aᵢ⟩|bᵢ⟩` (orthonormal families `a`, `b`), the
eigenvalue distribution of the *right* reduced state `ρ_B = tr_A|ψ⟩⟨ψ|` has the same non-zero
entries as `(l²)`: `(λ²) ≅ λ_{ρ_B}`. The right-factor mirror of
`PureState.sameNonzero_sq_reducedLeft_eigenvalueDist`.

Proof: `ρ_B.op = ∑ᵢ lᵢ² |bᵢ⟩⟨bᵢ|` — the right reduced operator is the *left* partial trace of
`|ψ⟩⟨ψ|`, which `LinearMap.partialTraceLeft_rankOne_eq_sum_rankOne_of_schmidt` (needing only that
the left factors `a` are orthonormal on the support, supplied here by full orthonormality via
`orthonormal_iff_ite`) expands into this sum of rank-one projectors onto the orthonormal `b`.
Recognition (`State.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum`) then identifies the
weight list `l²` with the reduced spectrum. -/
theorem PureState.sameNonzero_sq_reducedRight_eigenvalueDist (ψ : PureState (S.compose T)) {n : ℕ}
    {l : Fin n → ℝ} {a : Fin n → S.space} {b : Fin n → T.space} (ha : Orthonormal ℂ a)
    (hb : Orthonormal ℂ b) (hψ : ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i) :
    SameNonzero (fun i => l i ^ 2) ψ.toState.reducedRight.eigenvalueDist :=
  ψ.toState.reducedRight.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum hb
    (fun i => l i ^ 2) (ψ.reducedRight_op_eq_sum_rankOne ha hψ)

/-- **A bipartite pure state's two reduced spectra coincide.** For any bipartite pure state `ψ` the
left and right reduced density operators `ρ_A = tr_B|ψ⟩⟨ψ|` and `ρ_B = tr_A|ψ⟩⟨ψ|` have the same
non-zero spectrum, `ρ_A(ψ) ≅ ρ_B(ψ)`. This is the spectral form of the Schmidt decomposition's
symmetry between the two factors — both reduced operators are diagonal in their respective Schmidt
bases with the *same* eigenvalues `λᵢ²` — and is the standard fact that a pure state's two marginals
are isospectral.

It is the load-bearing bridge for **Nielsen & Chuang, Proposition 12.14** away from the
swap-symmetric normal form (`AxQM/NC/Ch12/Proposition12_14.lean`): the reduced state Bob obtains on
his factor after a local operation is isospectral to the one Alice obtains on her factor, so a
measurement Bob performs on a shared pure state produces a post-measurement state with the *same*
Schmidt coefficients as the one Alice's simulating measurement produces — the equal-Schmidt-spectrum
hypothesis of Exercise 2.80 that supplies the local unitary. Proof: both spectra are `≅` the shared
squared-coefficient list `(l²)` of a common Schmidt decomposition
(`sameNonzero_sq_reducedLeft_eigenvalueDist` and `sameNonzero_sq_reducedRight_eigenvalueDist`), so
they are `≅` each other by symmetry and transitivity. -/
theorem PureState.sameNonzeroSpectrum_reducedLeft_reducedRight (ψ : PureState (S.compose T)) :
    ψ.toState.reducedLeft.SameNonzeroSpectrum ψ.toState.reducedRight := by
  obtain ⟨n, l, a, b, _, ha, hb, _, hψ⟩ := ψ.exists_schmidt_decomposition
  exact (ψ.sameNonzero_sq_reducedLeft_eigenvalueDist ha hb hψ).symm.trans
    (ψ.sameNonzero_sq_reducedRight_eigenvalueDist ha hb hψ)

/-- **Identical Schmidt coefficients give the same reduced spectrum** (the forward direction of
Nielsen & Chuang Exercise 12.22's reduced-spectrum bridge). If two bipartite pure states `ψ` and `φ`
have identical Schmidt coefficients (`PureState.SameSchmidtCoeffs`), then their left reduced states
have the same non-zero spectrum: `ρ_A(ψ) ≅ ρ_A(φ)`.

Both reduced spectra are `≅` the shared squared-coefficient list `(l²)`
(`PureState.sameNonzero_sq_reducedLeft_eigenvalueDist`, applied to each state's Schmidt
decomposition), so they are `≅` each other by symmetry and transitivity. -/
theorem PureState.sameNonzeroSpectrum_reducedLeft_of_sameSchmidtCoeffs
    {ψ φ : PureState (S.compose T)} (h : ψ.SameSchmidtCoeffs φ) :
    ψ.toState.reducedLeft.SameNonzeroSpectrum φ.toState.reducedLeft := by
  obtain ⟨n, l, a, a', b, b', _, ha, hb, ha', hb', hψ, hφ⟩ := h
  exact (ψ.sameNonzero_sq_reducedLeft_eigenvalueDist ha hb hψ).symm.trans
    (φ.sameNonzero_sq_reducedLeft_eigenvalueDist ha' hb' hφ)

/-- **The same reduced spectrum forces identical Schmidt coefficients** (the reverse direction of
Nielsen & Chuang Exercise 12.22's reduced-spectrum bridge). If two bipartite pure states `ψ` and `φ`
have left reduced states with the same non-zero spectrum (`ρ_A(ψ) ≅ ρ_A(φ)`), then they have
identical Schmidt coefficients (`PureState.SameSchmidtCoeffs`).

Take Schmidt decompositions `|ψ⟩ = ∑ᵢ lψᵢ |aᵢ⟩|bᵢ⟩`, `|φ⟩ = ∑ⱼ lφⱼ |a'ⱼ⟩|b'ⱼ⟩` with strictly
positive coefficients. Each reduced spectrum is `≅` its squared coefficients
(`PureState.sameNonzero_sq_reducedLeft_eigenvalueDist`), so with the two spectra `≅` each other the
squared families `(lψ²)` and `(lφ²)` are `≅`. Being strictly positive they are nowhere zero, so this
promotes to an index bijection `e : Fin nψ ≃ Fin nφ` with `lφ (e i)² = lψ i²`
(`SameNonzero.exists_equiv`), whence `lφ (e i) = lψ i` by taking positive square roots. Reindexing
`φ`'s Schmidt sum by `e` — its bases stay orthonormal (`Orthonormal.comp`, `e` injective) — rewrites
`|φ⟩` over the *common ordered* coefficient family `lψ`, exhibiting the shared coefficients. -/
theorem PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft
    {ψ φ : PureState (S.compose T)}
    (h : ψ.toState.reducedLeft.SameNonzeroSpectrum φ.toState.reducedLeft) :
    ψ.SameSchmidtCoeffs φ := by
  obtain ⟨nψ, lψ, a, b, hlψ, ha, hb, _, hψ⟩ := ψ.exists_schmidt_decomposition
  obtain ⟨nφ, lφ, a', b', hlφ, ha', hb', _, hφ⟩ := φ.exists_schmidt_decomposition
  have hsq : SameNonzero (fun i => lψ i ^ 2) (fun j => lφ j ^ 2) :=
    ((ψ.sameNonzero_sq_reducedLeft_eigenvalueDist ha hb hψ).trans h).trans
      (φ.sameNonzero_sq_reducedLeft_eigenvalueDist ha' hb' hφ).symm
  obtain ⟨e, he⟩ := hsq.exists_equiv (fun i => pow_ne_zero 2 (hlψ i).ne')
    (fun j => pow_ne_zero 2 (hlφ j).ne')
  have hcoeff : ∀ i, lφ (e i) = lψ i := fun i => by
    rw [← Real.sqrt_sq (hlφ (e i)).le, he i, Real.sqrt_sq (hlψ i).le]
  have hφ' : φ.vec = ∑ i, (lψ i : ℂ) • a' (e i) ⊗ₜ[ℂ] b' (e i) := by
    rw [hφ, ← Equiv.sum_comp e (fun j => (lφ j : ℂ) • a' j ⊗ₜ[ℂ] b' j)]
    exact Finset.sum_congr rfl fun i _ => by rw [hcoeff i]
  exact ⟨nψ, lψ, a, fun i => a' (e i), b, fun i => b' (e i), hlψ, ha, hb,
    ha'.comp _ e.injective, hb'.comp _ e.injective, hψ, hφ'⟩

/-- **Schmidt-coefficient equality is the same-reduced-spectrum relation** (Nielsen & Chuang
Exercise 12.22's reduced-spectrum bridge, both directions). Two bipartite pure states have identical
Schmidt coefficients iff their left reduced states have the same non-zero spectrum:
`ψ.SameSchmidtCoeffs φ ↔ ρ_A(ψ) ≅ ρ_A(φ)`. Assembles the forward direction
(`PureState.sameNonzeroSpectrum_reducedLeft_of_sameSchmidtCoeffs`) with the reverse
(`PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft`). -/
theorem PureState.sameSchmidtCoeffs_iff_sameNonzeroSpectrum_reducedLeft
    {ψ φ : PureState (S.compose T)} :
    ψ.SameSchmidtCoeffs φ ↔ ψ.toState.reducedLeft.SameNonzeroSpectrum φ.toState.reducedLeft :=
  ⟨PureState.sameNonzeroSpectrum_reducedLeft_of_sameSchmidtCoeffs,
    PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft⟩

/-- **Identical Schmidt coefficients give the same right reduced spectrum** — the right-factor
mirror of `PureState.sameNonzeroSpectrum_reducedLeft_of_sameSchmidtCoeffs`. If two bipartite pure
states `ψ` and `φ` have identical Schmidt coefficients then their *right* reduced states have the
same non-zero spectrum: `ρ_B(ψ) ≅ ρ_B(φ)`. Both spectra are `≅` the shared squared-coefficient list
via `PureState.sameNonzero_sq_reducedRight_eigenvalueDist`. -/
theorem PureState.sameNonzeroSpectrum_reducedRight_of_sameSchmidtCoeffs
    {ψ φ : PureState (S.compose T)} (h : ψ.SameSchmidtCoeffs φ) :
    ψ.toState.reducedRight.SameNonzeroSpectrum φ.toState.reducedRight := by
  obtain ⟨n, l, a, a', b, b', _, ha, hb, ha', hb', hψ, hφ⟩ := h
  exact (ψ.sameNonzero_sq_reducedRight_eigenvalueDist ha hb hψ).symm.trans
    (φ.sameNonzero_sq_reducedRight_eigenvalueDist ha' hb' hφ)

/-- **The same right reduced spectrum forces identical Schmidt coefficients** — the right-factor
mirror of `PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft`. If two bipartite pure
states have *right* reduced states with the same non-zero spectrum (`ρ_B(ψ) ≅ ρ_B(φ)`) then they
have identical Schmidt coefficients. Each state's two marginals are isospectral
(`PureState.sameNonzeroSpectrum_reducedLeft_reducedRight`), so the hypothesis transports to the left
factor `ρ_A(ψ) ≅ ρ_A(φ)`, whence the left reverse bridge
(`PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft`) applies. -/
theorem PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedRight
    {ψ φ : PureState (S.compose T)}
    (h : ψ.toState.reducedRight.SameNonzeroSpectrum φ.toState.reducedRight) :
    ψ.SameSchmidtCoeffs φ :=
  PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedLeft
    ((ψ.sameNonzeroSpectrum_reducedLeft_reducedRight.trans h).trans
      φ.sameNonzeroSpectrum_reducedLeft_reducedRight.symm)

/-- **Schmidt-coefficient equality is the same-right-reduced-spectrum relation** (Nielsen & Chuang
Exercise 12.22's reduced-spectrum bridge, right factor). Two bipartite pure states have identical
Schmidt coefficients iff their *right* reduced states have the same non-zero spectrum:
`ψ.SameSchmidtCoeffs φ ↔ ρ_B(ψ) ≅ ρ_B(φ)`. The right-factor companion of
`PureState.sameSchmidtCoeffs_iff_sameNonzeroSpectrum_reducedLeft`, assembling the forward and
reverse right-factor directions. -/
theorem PureState.sameSchmidtCoeffs_iff_sameNonzeroSpectrum_reducedRight
    {ψ φ : PureState (S.compose T)} :
    ψ.SameSchmidtCoeffs φ ↔ ψ.toState.reducedRight.SameNonzeroSpectrum φ.toState.reducedRight :=
  ⟨PureState.sameNonzeroSpectrum_reducedRight_of_sameSchmidtCoeffs,
    PureState.sameSchmidtCoeffs_of_sameNonzeroSpectrum_reducedRight⟩

end AxQM
