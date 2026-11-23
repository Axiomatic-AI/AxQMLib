/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerCodeDimension
import AxQM.Postulates.API.PauliTrotter
import AxQM.Postulates.API.Eigenstate
import AxQM.Postulates.API.PureState

/-!
# The pure state stabilized by a full set of commuting Pauli generators

For a family of honest Pauli-string generators `g : Fin m → Fin n → Fin 4` on the `n`-qubit
register `qudit (2ⁿ)`, the **stabilizer-code physics** turns entirely on the *simultaneous
`+1`-eigenspace* of the generators — the subspace of register states `ψ` with
`(pauliStringHamiltonian (g i) 1) ψ = ψ` for every `i`. Nielsen & Chuang Proposition 10.5
(`Concrete.stabilizedSubspace_finrank`) computes the dimension of this space *on the matrix side*:
`n - k` independent commuting generators cut out a `2ᵏ`-dimensional code space. This file transports
that dimension count to the register `qudit (2ⁿ)`, so that "the code space has
dimension `d`" becomes a statement about `PureState`s.

The bridge is a single reindexing linear equivalence `registerReindex n` between the tensor-indexed
space `(Fin n → Fin 2) → ℂ` — on which `Concrete.stabilizedSubspace` and the phase-free matrices
`Concrete.pauliString` live — and the register `qudit (2ⁿ)` (`EuclideanSpace ℂ (Fin 2ⁿ)`), on which
`pauliStringHamiltonian` acts through `Matrix.toEuclideanCLM (pauliStringStd g)`. Under it the two
descriptions of the `+1`-eigenspace correspond (`registerReindex_op_comm`, `mem_registerStab`), so
the dimension transports verbatim (`LinearEquiv.finrank_map_eq`).

The two consequences are exactly the *existence* and *uniqueness* of the stabilized state:

* `exists_hasEigenstate_one_of_stabilizedSubspace_finrank_eq_one` — when the stabilized subspace is
  a **line** (`finrank = 1`) there **is** a pure state fixed by every generator: the code space is
  nonempty, so the stabilizer construction prepares *something*.
* `hasEigenstate_one_toState_eq_of_stabilizedSubspace_finrank_eq_one` — and that state is **unique
  up to a global phase**: any two states fixed by every generator have the same density operator.
  The construction prepares a *well-defined* state.

These are the content of "measuring a full independent set of commuting Pauli
operators and fixing all signs to `+1` prepares a unique codeword", used by the encoded-state
preparation exercises (e.g. the five-qubit encoded `|0⟩`, Exercise 10.74).
-/

open scoped Matrix

namespace AxQM

variable {n m : ℕ}

/-- **The register reindexing.** The `ℂ`-linear equivalence between the tensor-indexed space
`(Fin n → Fin 2) → ℂ` — the index type of the phase-free Pauli matrices `Concrete.pauliString` and
of `Concrete.stabilizedSubspace` — and the `n`-qubit register `qudit (2ⁿ)` (`EuclideanSpace ℂ
(Fin 2ⁿ)`). It precomposes with `finFunctionFinEquiv.symm` (the same bit-string↔`Fin 2ⁿ` reindexing
that defines `Concrete.pauliStringStd`) and drops into the `WithLp` wrapper of the Euclidean
register. -/
noncomputable def registerReindex (n : ℕ) :
    ((Fin n → Fin 2) → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (2 ^ n)) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (finFunctionFinEquiv (m := 2) (n := n)).symm).trans
    (WithLp.linearEquiv 2 ℂ (Fin (2 ^ n) → ℂ)).symm

@[simp]
lemma registerReindex_ofLp (w : (Fin n → Fin 2) → ℂ) :
    (registerReindex n w).ofLp = fun I => w (finFunctionFinEquiv.symm I) := by
  simp only [registerReindex, LinearEquiv.trans_apply, WithLp.coe_symm_linearEquiv,
    WithLp.ofLp_toLp, LinearEquiv.funCongrLeft_apply]
  rfl

/-- On the register, an honest Pauli-string Hamiltonian acts by `mulVec` of the standard-indexed
Pauli matrix (`Complex.ofReal_one`/`one_smul` clearing the unit coefficient). -/
lemma pauliStringHamiltonian_one_op_ofLp (g : Fin n → Fin 4)
    (x : EuclideanSpace ℂ (Fin (2 ^ n))) :
    ((pauliStringHamiltonian g 1).op x).ofLp = (Concrete.pauliStringStd g).mulVec x.ofLp := by
  rw [pauliStringHamiltonian_op]
  simp only [Complex.ofReal_one, one_smul]
  exact Matrix.ofLp_toEuclideanCLM (Concrete.pauliStringStd g) x

/-- **The reindexing intertwines the two descriptions of a generator.** On the register, the
Pauli-string Hamiltonian acts through `Matrix.toEuclideanCLM (pauliStringStd g)`; on the
tensor-indexed space the same operator is `mulVec` by the phase-free matrix `pauliString g`. Under
`registerReindex` they agree. -/
lemma registerReindex_op_comm (g : Fin n → Fin 4) (w : (Fin n → Fin 2) → ℂ) :
    (pauliStringHamiltonian g 1).op (registerReindex n w)
      = registerReindex n ((Concrete.pauliString g).mulVec w) := by
  have hcomp : (fun J => w (finFunctionFinEquiv.symm J)) ∘ ⇑finFunctionFinEquiv = w := by
    funext x; simp
  apply WithLp.ofLp_injective
  rw [pauliStringHamiltonian_one_op_ofLp, registerReindex_ofLp, registerReindex_ofLp]
  simp only [Concrete.pauliStringStd]
  erw [Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm, hcomp]
  rfl

/-- **The register-side stabilized subspace.** The image of `Concrete.stabilizedSubspace g` under
`registerReindex` — the simultaneous `+1`-eigenspace of the Pauli-string Hamiltonians `g` inside the
register `qudit (2ⁿ)`. -/
noncomputable def registerStab (g : Fin m → Fin n → Fin 4) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 ^ n))) :=
  Submodule.map (registerReindex n : _ →ₗ[ℂ] _) (Concrete.stabilizedSubspace g)

/-- **Membership in the register-side stabilized subspace.** A register vector `v` lies in
`registerStab g` iff it is fixed by every generator's Pauli-string Hamiltonian, `(P_{gᵢ}) v = v`. -/
lemma mem_registerStab (g : Fin m → Fin n → Fin 4) (v : EuclideanSpace ℂ (Fin (2 ^ n))) :
    v ∈ registerStab g ↔ ∀ i, (pauliStringHamiltonian (g i) 1).op v = v := by
  rw [registerStab, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    rw [Concrete.mem_stabilizedSubspace] at hw
    simp only [LinearEquiv.coe_coe]
    rw [registerReindex_op_comm, hw i]
  · intro hv
    refine ⟨(registerReindex n).symm v, ?_, by simp⟩
    rw [Concrete.mem_stabilizedSubspace]
    intro i
    apply (registerReindex n).injective
    rw [← registerReindex_op_comm, LinearEquiv.apply_symm_apply]
    exact hv i

/-- **The register-side stabilized subspace has the same dimension as the matrix-side one**
(transported along the reindexing equivalence). -/
lemma finrank_registerStab (g : Fin m → Fin n → Fin 4) :
    Module.finrank ℂ (registerStab g) = Module.finrank ℂ (Concrete.stabilizedSubspace g) := by
  rw [registerStab, LinearEquiv.finrank_map_eq]

/-- **Existence of the stabilized state.** If the stabilized subspace of a generating set `g` is a
line (`finrank = 1`), then there is a pure state `ψ` on the register that is a common
`+1`-eigenstate of every generator's Pauli-string Hamiltonian. Physically: a full independent set of
commuting Pauli operators has a (nonempty) code space, so measuring them and fixing all signs to
`+1` prepares a state. -/
theorem exists_hasEigenstate_one_of_stabilizedSubspace_finrank_eq_one
    (g : Fin m → Fin n → Fin 4)
    (hfr : Module.finrank ℂ (Concrete.stabilizedSubspace g) = 1) :
    ∃ ψ : PureState (qudit (2 ^ n)), ∀ i, (pauliStringHamiltonian (g i) 1).HasEigenstate 1 ψ := by
  have hfr' : Module.finrank ℂ (registerStab g) = 1 := by rw [finrank_registerStab]; exact hfr
  have hne : registerStab g ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hfr'; exact one_ne_zero hfr'.symm
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hne
  refine ⟨PureState.normalize v hv_ne, fun i => ?_⟩
  simp only [Observable.HasEigenstate, Complex.ofReal_one, one_smul]
  exact (mem_registerStab g _).mp (Submodule.smul_mem _ _ hv_mem) i

/-- **Uniqueness of the stabilized state up to a global phase.** If the stabilized subspace of a
generating set `g` is a line (`finrank = 1`), then any two pure states `ψ`, `φ` that are common
`+1`-eigenstates of every generator's Pauli-string Hamiltonian have the same density operator,
`ψ.toState = φ.toState`. Physically: measuring a full independent set of commuting Pauli operators
and post-selecting the all-`+1` outcome pins the prepared state down to a single codeword (up to an
invisible global phase). -/
theorem hasEigenstate_one_toState_eq_of_stabilizedSubspace_finrank_eq_one
    (g : Fin m → Fin n → Fin 4)
    (hfr : Module.finrank ℂ (Concrete.stabilizedSubspace g) = 1)
    {ψ φ : PureState (qudit (2 ^ n))}
    (hψ : ∀ i, (pauliStringHamiltonian (g i) 1).HasEigenstate 1 ψ)
    (hφ : ∀ i, (pauliStringHamiltonian (g i) 1).HasEigenstate 1 φ) :
    ψ.toState = φ.toState := by
  have hfr' : Module.finrank ℂ (registerStab g) = 1 := by rw [finrank_registerStab]; exact hfr
  have hψmem : ψ.vec ∈ registerStab g := (mem_registerStab g ψ.vec).mpr fun i => by
    have := hψ i; simpa only [Observable.HasEigenstate, Complex.ofReal_one, one_smul] using this
  have hφmem : φ.vec ∈ registerStab g := (mem_registerStab g φ.vec).mpr fun i => by
    have := hφ i; simpa only [Observable.HasEigenstate, Complex.ofReal_one, one_smul] using this
  obtain ⟨u, -, hu_span⟩ := finrank_eq_one_iff'.mp hfr'
  obtain ⟨a, ha⟩ := hu_span ⟨ψ.vec, hψmem⟩
  obtain ⟨b, hb⟩ := hu_span ⟨φ.vec, hφmem⟩
  have hav : a • (u : EuclideanSpace ℂ (Fin (2 ^ n))) = ψ.vec := by
    have := congrArg Subtype.val ha; simpa using this
  have hbv : b • (u : EuclideanSpace ℂ (Fin (2 ^ n))) = φ.vec := by
    have := congrArg Subtype.val hb; simpa using this
  have hb0 : b ≠ 0 := by
    rintro rfl; rw [zero_smul] at hbv; exact φ.vec_ne_zero hbv.symm
  have e2 : (a * b⁻¹) • (b • (u : EuclideanSpace ℂ (Fin (2 ^ n))))
      = a • (u : EuclideanSpace ℂ (Fin (2 ^ n))) := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  have step : (a * b⁻¹) • (b • (u : EuclideanSpace ℂ (Fin (2 ^ n)))) = (a * b⁻¹) • φ.vec :=
    congrArg (fun x => (a * b⁻¹) • x) hbv
  have hkey : ψ.vec = (a * b⁻¹) • φ.vec := hav.symm.trans (e2.symm.trans step)
  have hnorm : ‖a * b⁻¹‖ = 1 := by
    have h1 := ψ.normalized
    rwa [hkey, norm_smul, φ.normalized, mul_one] at h1
  exact PureState.toState_eq_of_vec_eq_smul hnorm hkey

end AxQM
