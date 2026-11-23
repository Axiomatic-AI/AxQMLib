/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Evolution
import AxQM.Postulates.Observable
import AxQM.Postulates.API.PureState
import AxQM.Postulates.API.Purity
import Mathlib.Analysis.CStarAlgebra.Exponential

/-!
# AxQM.Postulates.API — the Hamiltonian propagator

The connection between the **continuous-time** picture of dynamics
(Nielsen–Chuang's Postulate 2′, the Schrödinger equation `iℏ d|ψ⟩/dt = H|ψ⟩` with a
Hermitian **Hamiltonian** `H`) and the **discrete-time** picture (Postulate 5 here / N&C's
Postulate 2, a unitary `Evolution`). Solving the Schrödinger equation for a
time-independent `H` gives (N&C eq. 2.90–2.91)
`|ψ(t₂)⟩ = U(t₁,t₂) |ψ(t₁)⟩`,  `U(t₁,t₂) ≡ exp(-i H (t₂ - t₁) / ℏ)`.

* `Observable.propagator H ℏ t₁ t₂` — the **time-evolution operator** `U(t₁,t₂)`, packaged
  as an `Evolution S`. An `Evolution` *bundles* the unitarity obligation, so the
  very existence of this term is Nielsen–Chuang **Exercise 2.55** ("prove that `U(t₁,t₂)` is
  unitary"): the construction discharges exactly that proof obligation.
* `Observable.propagator_op` — its form exposing the operator as the exponential
  `exp(-i H (t₂ - t₁) / ℏ)` (N&C eq. 2.91).
* `Observable.propagator_op_mem_unitary` — the literal statement of Exercise 2.55: that
  exponential lies in the unitary group.

This file also provides the general constructor `Evolution.ofLinearIsometryEquiv`, packaging a
linear isometry equivalence of `S.space` as a unitary `Evolution S`, and its inverse
`Evolution.toIsometryEquiv`, repackaging a unitary `Evolution` as a `≃ₗᵢ`. They are the standard
bridges used wherever a state is transformed by an *explicitly constructed* unitary — e.g. the
local unitaries relating two states with identical Schmidt coefficients (N&C Exercise 2.80) or two
purifications (Exercise 2.81) — or wherever an `Evolution`-valued unitary must feed an API expecting
a `≃ₗᵢ`.

## Why the exponential is unitary

Write the exponent as `i • a` with `a = (-(t₂ - t₁)/ℏ) • H.op` a **self-adjoint** operator
(a real multiple of the self-adjoint `H.op`). For self-adjoint `a`, `exp(i • a)` is unitary
— this is Mathlib's `selfAdjoint.expUnitary`, whose underlying fact is `(exp(i a))† =
exp(-i a) = exp(i a)⁻¹`. Physically this is why probability is conserved: a Hermitian
generator produces a norm-preserving evolution.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A linear isometry equivalence of `S.space`, packaged as a unitary evolution of `S`.** The
standard bridge from an explicitly constructed unitary (as a `LinearIsometryEquiv`) to the
`Evolution` structure: `Evolution` bundles the unitarity obligation, discharged here from
`Unitary.linearIsometryEquiv` (unitary operators on a Hilbert space are exactly its linear
isometry equivalences). Its action is `L` itself (`Evolution.ofLinearIsometryEquiv_op_apply`). -/
def Evolution.ofLinearIsometryEquiv (L : S.space ≃ₗᵢ[ℂ] S.space) : Evolution S :=
  letI : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  ⟨↑(Unitary.linearIsometryEquiv.symm L), (Unitary.linearIsometryEquiv.symm L).2⟩

/-- The evolution `Evolution.ofLinearIsometryEquiv L` acts as `L` on vectors: its underlying
operator applied to `x` is `L x`. -/
@[simp]
theorem Evolution.ofLinearIsometryEquiv_op_apply (L : S.space ≃ₗᵢ[ℂ] S.space) (x : S.space) :
    (Evolution.ofLinearIsometryEquiv L).op x = L x := by
  simp [Evolution.ofLinearIsometryEquiv, Unitary.coe_symm_linearIsometryEquiv_apply]

/-- **A unitary `Evolution` packaged as a linear isometry equivalence** of `S.space` — the inverse
direction of `Evolution.ofLinearIsometryEquiv`. A unitary operator on a (finite-dimensional, hence
complete) Hilbert space is exactly a linear isometry equivalence (`Unitary.linearIsometryEquiv`), so
this repackages `U.op` losslessly. The general bridge used wherever an `Evolution`-valued unitary
must be handed to an API expecting a `≃ₗᵢ` (e.g. feeding a gate schedule into a
recursion typed over `S.space ≃ₗᵢ[ℂ] S.space`). Its action is `U.op` itself
(`Evolution.toIsometryEquiv_apply`). -/
def Evolution.toIsometryEquiv (U : Evolution S) : S.space ≃ₗᵢ[ℂ] S.space :=
  letI : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  Unitary.linearIsometryEquiv ⟨U.op, U.unitary⟩

/-- The linear isometry equivalence `Evolution.toIsometryEquiv U` acts as the evolution's operator
`U.op` on vectors. -/
@[simp]
theorem Evolution.toIsometryEquiv_apply (U : Evolution S) (x : S.space) :
    U.toIsometryEquiv x = U.op x := by
  let : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  exact DFunLike.congr_fun (Unitary.coe_linearIsometryEquiv_apply ⟨U.op, U.unitary⟩) x

/-- **The evolved-state operator as a conjugation by an isometry equivalence.** The density
operator `U ρ U†` of the evolved state `U.evolve ρ` is `ρ.op` conjugated by the isometry
equivalence `U.toIsometryEquiv`:

`(U.evolve ρ).op = (U.toIsometryEquiv).conjStarAlgEquiv ρ.op`.

The `Evolution.evolve` counterpart of the transport bridges `State.congr_op` / `Evolution.congr_op`
(which deliver the same `…conjStarAlgEquiv …` form for a *system* isomorphism): it repackages the
composition form `U.op ∘ ρ.op ∘ U.op†` of `Evolution.evolve_op` as a `conjStarAlgEquiv`, so any
spectral/unitary-invariance lemma stated over `conjStarAlgEquiv` (e.g.
`ContinuousLinearMap.vonNeumannEntropy_conjStarAlgEquiv`) can be consumed by name. -/
theorem Evolution.evolve_op_conjStarAlgEquiv (U : Evolution S) (ρ : State S) :
    (U.evolve ρ).op = U.toIsometryEquiv.conjStarAlgEquiv ρ.op := by
  ext x
  rw [Evolution.evolve_op, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  simp only [ContinuousLinearMap.comp_apply, Evolution.toIsometryEquiv_apply]
  congr 2

/-- **Conjugation by a self-adjoint unitary.** When the unitary `U` of an evolution is self-adjoint
(`U† = U`, e.g. a reflection, a Pauli, or a sign operator), the evolved-state operator is the plain
two-sided product `(U.evolve ρ).op = U ρ U`, since the adjoint in `U ρ U†` collapses. The reusable
bridge behind the conjugation identities of such involutive unitaries. -/
theorem Evolution.evolve_op_of_isSelfAdjoint {U : Evolution S} (hU : IsSelfAdjoint U.op)
    (ρ : State S) : (U.evolve ρ).op = U.op * ρ.op * U.op := by
  have hadj : adjoint U.op = U.op := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hU.star_eq
  rw [Evolution.evolve_op, hadj, ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
    mul_assoc]

/-- **The Hamiltonian propagator** `U(t₁,t₂) ≡ exp(-i H (t₂ - t₁) / ℏ)` (Nielsen–Chuang
eq. 2.91), packaged as an `Evolution S`. Given the Hamiltonian `H` (an `Observable`, i.e. a
Hermitian operator), Planck's constant `ℏ`, and two times `t₁ t₂`, this is the operator that
solves the Schrödinger equation, `|ψ(t₂)⟩ = U(t₁,t₂)|ψ(t₁)⟩`.

Because `Evolution` bundles the unitarity obligation, producing this term *is* the content of
**N&C Exercise 2.55**: `U(t₁,t₂)` is unitary. The exponent `-i H (t₂ - t₁)/ℏ` equals
`i • ((-(t₂ - t₁)/ℏ) • H.op)`, i.e. `i` times a self-adjoint operator, and the exponential of
`i` times a self-adjoint operator is unitary (`selfAdjoint.expUnitary`). -/
def Observable.propagator (H : Observable S) (ℏ t₁ t₂ : ℝ) : Evolution S where
  op := NormedSpace.exp (((-Complex.I) * ((t₂ - t₁ : ℝ) : ℂ) / (ℏ : ℂ)) • H.op)
  unitary := by
    -- Reshape the physical exponent `-i(t₂-t₁)/ℏ • H.op` as `i • (s • H.op)` with the real
    -- scalar `s = -(t₂-t₁)/ℏ`, i.e. `i` times the self-adjoint operator `s • H.op`.
    have ha : IsSelfAdjoint (((-(t₂ - t₁) / ℏ : ℝ) : ℂ) • H.op) :=
      ((Complex.im_eq_zero_iff_isSelfAdjoint _).mp rfl).smul H.selfAdjoint
    have hc : ((-Complex.I) * ((t₂ - t₁ : ℝ) : ℂ) / (ℏ : ℂ)) • H.op
        = Complex.I • (((-(t₂ - t₁) / ℏ : ℝ) : ℂ) • H.op) := by
      rw [smul_smul]; push_cast; ring_nf
    rw [hc, ← selfAdjoint.expUnitary_coe ⟨((-(t₂ - t₁) / ℏ : ℝ) : ℂ) • H.op,
      selfAdjoint.mem_iff.mpr ha⟩]
    exact (selfAdjoint.expUnitary _).2

@[simp]
theorem Observable.propagator_op (H : Observable S) (ℏ t₁ t₂ : ℝ) :
    (H.propagator ℏ t₁ t₂).op
      = NormedSpace.exp (((-Complex.I) * ((t₂ - t₁ : ℝ) : ℂ) / (ℏ : ℂ)) • H.op) := rfl

/-- **Nielsen–Chuang Exercise 2.55.** The time-evolution operator
`U(t₁,t₂) = exp(-i H (t₂ - t₁) / ℏ)` (eq. 2.91) generated by a Hamiltonian `H` is unitary.
The citable operator-level statement; it is exactly the unitarity field of
`Observable.propagator` read through `Observable.propagator_op`. -/
theorem Observable.propagator_op_mem_unitary (H : Observable S) (ℏ t₁ t₂ : ℝ) :
    NormedSpace.exp (((-Complex.I) * ((t₂ - t₁ : ℝ) : ℂ) / (ℏ : ℂ)) • H.op)
      ∈ unitary (S →L[ℂ] S) :=
  (H.propagator ℏ t₁ t₂).unitary

/-! ### Adjoint (inverse) evolution and eigenstates -/

/-- **The adjoint evolution** `U†`, whose operator is the Hilbert-space adjoint of `U.op`.
Because `U` is unitary (`U† U = U U† = 1`), `U†` is again a unitary `Evolution` and is the
inverse gate `U⁻¹`; it reverses the action of `U` (`U†` after `U` is the identity, via
`Evolution.adjoint_comp_self`). It is the "uncompute" step of a compute–phase–uncompute
circuit (N&C Problem 4.1). -/
def Evolution.adjoint (U : Evolution S) : Evolution S where
  op := ContinuousLinearMap.adjoint U.op
  unitary := by
    -- `U.adjoint.op = star U.op`, so unitarity is the star-closure of the unitary group.
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mem U.unitary

@[simp]
theorem Evolution.adjoint_op (U : Evolution S) :
    U.adjoint.op = ContinuousLinearMap.adjoint U.op := rfl

/-- The co-isometry identity `U U† = 1` extracted from unitarity: the `U U† = 1` companion of the
frozen `Evolution.adjoint_comp_self` (which gives the isometry identity `U† U = 1`). Both halves of
unitarity are then citable facts for controlled/composed-unitarity proofs. -/
theorem Evolution.comp_adjoint_self (U : Evolution S) :
    U.op.comp (ContinuousLinearMap.adjoint U.op) = 1 := by
  have h := (Unitary.mem_iff.mp U.unitary).2
  rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] at h

/-- **Uncompute cancellation** `U†(Uψ) = ψ`: applying the adjoint gate `U†` after `U` returns any
pure state unchanged, since `U` is unitary (`U† U = 1`, `Evolution.adjoint_comp_self`). The
pure-state form of the compute–uncompute identity. -/
theorem Evolution.evolvePure_adjoint_evolvePure (U : Evolution S) (ψ : PureState S) :
    U.adjoint.evolvePure (U.evolvePure ψ) = ψ := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, Evolution.adjoint_op]
  rw [← ContinuousLinearMap.comp_apply, Evolution.adjoint_comp_self,
    one_apply_eq_self]

/-- **Uncompute cancellation** `U(U†ψ) = ψ`: applying `U` after its adjoint `U†` returns any pure
state unchanged, since `U` is unitary (`U U† = 1`, `Evolution.comp_adjoint_self`). The companion of
`Evolution.evolvePure_adjoint_evolvePure` with the roles of `U` and `U†` swapped. -/
theorem Evolution.evolvePure_adjoint_evolvePure' (U : Evolution S) (ψ : PureState S) :
    U.evolvePure (U.adjoint.evolvePure ψ) = ψ := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, Evolution.adjoint_op]
  rw [← ContinuousLinearMap.comp_apply, Evolution.comp_adjoint_self,
    one_apply_eq_self]

/-- **A unitary maps `normalize v` to `normalize (U v)`.** If a gate `U` sends the nonzero vector
`v` to `w`, then it sends the unit vector `normalize v` to `normalize w`: `U` preserves norms
(`Evolution.norm_op_apply`), so the two normalisation factors agree. The general bridge that lifts
an operator identity `U.op v = w` to a `PureState` equality
`U.evolvePure (normalize v) = normalize w`. -/
theorem Evolution.evolvePure_normalize_of_op_eq (U : Evolution S) {v w : S}
    (hv : v ≠ 0) (hw : w ≠ 0) (h : U.op v = w) :
    U.evolvePure (PureState.normalize v hv) = PureState.normalize w hw := by
  ext1
  have hn : ‖v‖ = ‖w‖ := by rw [← h, U.norm_op_apply]
  rw [Evolution.evolvePure_vec, PureState.normalize_vec, map_smul, h, PureState.normalize_vec, hn]

/-- **Gate-level co-isometry cancellation** `U ∘ U† = id`: a unitary evolution followed by its
adjoint is the identity gate. The `Evolution`-valued companion of the op-level
`Evolution.comp_adjoint_self` (`U U† = 1`), and the `U`/`U†`-swapped partner of the frozen
`Evolution.adjoint_comp_self'` (`U† ∘ U = id`). Together they say `U†` is a *two-sided* inverse
gate for `U`, so `U` is invertible in the composition monoid. -/
theorem Evolution.comp_adjoint_self' (U : Evolution S) : U.comp U.adjoint = Evolution.id := by
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.adjoint_op, Evolution.id_op, U.comp_adjoint_self]

/-- **State-level uncompute cancellation** `U†(U ρ U†)U = ρ`: conjugating a density operator `ρ`
by a unitary `U` and then by its adjoint `U†` returns `ρ` unchanged, since `U` is unitary
(`U† U = 1`, `Evolution.adjoint_comp_self`). This is the mixed-state (density-operator) form of
`Evolution.evolvePure_adjoint_evolvePure`, and it is the round-trip that makes conjugation of a
state by a unitary invertible — so a channel `ρ ↦ U ρ U†` has the two-sided inverse `ρ ↦ U† ρ U`. -/
theorem Evolution.evolve_adjoint_evolve (U : Evolution S) (ρ : State S) :
    U.adjoint.evolve (U.evolve ρ) = ρ := by
  apply State.ext
  have hUU : ContinuousLinearMap.adjoint U.op * U.op = 1 := by
    rw [ContinuousLinearMap.mul_def]; exact U.adjoint_comp_self
  -- `U†(U ρ U†)U = ρ`: unfold the two conjugations to a product and cancel `U† U = 1` twice.
  simp only [Evolution.evolve_op, Evolution.adjoint_op, ContinuousLinearMap.adjoint_adjoint,
    ← ContinuousLinearMap.mul_def]
  rw [mul_assoc U.op (ρ.op * ContinuousLinearMap.adjoint U.op) U.op,
    mul_assoc ρ.op (ContinuousLinearMap.adjoint U.op) U.op, hUU, mul_one, ← mul_assoc, hUU,
    one_mul]

/-- **Reversal of a composite circuit under the adjoint** `(U ∘ V)† = V† ∘ U†`: the adjoint
(inverse) of a composition of gates runs the individual adjoints in the *reverse* order. This is the
formal content of the textbook recipe "to reverse a quantum circuit, apply the inverse of each gate
in reverse order": a circuit `U = g_L ∘ ⋯ ∘ g_1` has inverse circuit `U† = g_1† ∘ ⋯ ∘ g_L†`. Lifts
the operator-level `ContinuousLinearMap.adjoint_comp` to the `Evolution` gate monoid. It is the
principle behind the inverse quantum Fourier transform (Nielsen & Chuang Exercise 5.5). -/
theorem Evolution.adjoint_comp (U V : Evolution S) :
    (U.comp V).adjoint = V.adjoint.comp U.adjoint := by
  apply Evolution.ext
  rw [Evolution.adjoint_op, Evolution.comp_op, Evolution.comp_op, Evolution.adjoint_op,
    Evolution.adjoint_op, ContinuousLinearMap.adjoint_comp]

/-- **The adjoint is an involution** `U†† = U`: inverting an evolution twice returns the original
gate. Lifts `ContinuousLinearMap.adjoint_adjoint` to `Evolution`. In particular every gate is the
inverse of its own inverse, so e.g. the quantum Fourier transform is recovered by inverting the
inverse-QFT circuit (`qftInverseEvolution_adjoint`). -/
theorem Evolution.adjoint_adjoint (U : Evolution S) : U.adjoint.adjoint = U := by
  apply Evolution.ext
  rw [Evolution.adjoint_op, Evolution.adjoint_op, ContinuousLinearMap.adjoint_adjoint]

/-- **State-level uncompute cancellation, swapped** `U (U† ρ U) U† = ρ`: conjugating a density
operator `ρ` by the adjoint `U†` and then by `U` returns `ρ` unchanged, since `U U† = 1`. The
`U`/`U†`-swapped partner of `Evolution.evolve_adjoint_evolve`; derived from it applied to `U†`
together with the involutivity `U†† = U` (`Evolution.adjoint_adjoint`). Together the two lemmas say
`ρ ↦ U ρ U†` and `ρ ↦ U† ρ U` are two-sided inverse channels, the fact behind the *symmetry* of
channel equivalence (N&C Problem 10.1). -/
theorem Evolution.evolve_adjoint_evolve' (U : Evolution S) (ρ : State S) :
    U.evolve (U.adjoint.evolve ρ) = ρ := by
  have h := U.adjoint.evolve_adjoint_evolve ρ
  rwa [Evolution.adjoint_adjoint] at h

/-- **The identity evolution acts trivially on states** `1 ρ 1† = ρ`: conjugating a state by the
identity gate returns it unchanged. The density-operator (mixed-state) companion of the pure-state
`Evolution.id_evolvePure`, and the reflexivity witness for channel equivalence (N&C Problem 10.1):
`E = id ∘ E ∘ id`. -/
@[simp]
theorem Evolution.evolve_id (ρ : State S) : (Evolution.id : Evolution S).evolve ρ = ρ := by
  apply State.ext
  rw [Evolution.evolve_op, Evolution.id_op, ← ContinuousLinearMap.star_eq_adjoint, star_one,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

/-- **`ψ` is an eigenstate of the evolution `U` with eigenvalue `μ`.** The pure-state
eigenvalue equation `U ψ = μ ψ`, with `μ : ℂ` a complex number (a unitary's eigenvalues lie on
the unit circle, so `μ` is generally complex — unlike an observable's real eigenvalues, cf.
`Observable.HasEigenstate`). `U.HasEigenstate μ ψ` is the eigenvalue equation of a unitary on a
state. -/
def Evolution.HasEigenstate (U : Evolution S) (μ : ℂ) (ψ : PureState S) : Prop :=
  U.op ψ.vec = μ • ψ.vec

/-- **A `+1` eigenstate of a unitary evolution is fixed by its `evolvePure`.** If
`U.HasEigenstate 1 ψ` then `U.evolvePure ψ = ψ` — the form for code states of "`ψ` is
stabilized by `U`" (every stabilizer element fixes every code state). -/
theorem Evolution.HasEigenstate.evolvePure_eq {U : Evolution S} {ψ : PureState S}
    (h : U.HasEigenstate 1 ψ) : U.evolvePure ψ = ψ := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, h, one_smul]

/-- **A pure state fixed by `evolvePure` is a `+1` eigenstate.** The converse of
`Evolution.HasEigenstate.evolvePure_eq`: if `U.evolvePure ψ = ψ` then `U.HasEigenstate 1 ψ`. Proved
from `evolvePure_vec`, mirroring the forward direction. -/
theorem Evolution.hasEigenstate_one_of_evolvePure_eq {U : Evolution S} {ψ : PureState S}
    (h : U.evolvePure ψ = ψ) : U.HasEigenstate 1 ψ := by
  change U.op ψ.vec = (1 : ℂ) • ψ.vec
  rw [← Evolution.evolvePure_vec, h, one_smul]

/-! ### Global-phase invariance of the induced channel -/

/-- **Global-phase invariance of the induced channel.** If the operators of two evolutions `U`, `V`
differ by a unit-modulus scalar `c` (`‖c‖ = 1`, `U.op = c • V.op`) — i.e. `U = V` *up to a global
phase* — then `U` and `V` induce the *same* state evolution `ρ ↦ U ρ U†`. The phase cancels in the
conjugation: `(c • V) ρ (c • V)† = (c · conj c) V ρ V† = ‖c‖² V ρ V† = V ρ V†`. This is the precise
sense in which a global phase is physically unobservable, and the shared lemma behind every
"up to a global phase, two gates are equal" statement (e.g. N&C Exercises 4.3, 4.14). -/
theorem Evolution.evolve_eq_of_op_eq_phase_smul (U V : Evolution S) {c : ℂ}
    (hc : ‖c‖ = 1) (h : U.op = c • V.op) (ρ : State S) : U.evolve ρ = V.evolve ρ := by
  apply State.ext
  have key : star c * c = 1 := by rw [← starRingEnd_apply, Complex.conj_mul', hc]; norm_num
  simp only [Evolution.evolve_op, h, ← ContinuousLinearMap.star_eq_adjoint, star_smul,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, smul_smul, key, one_smul]

/-! ### Linearity of the operator over scalar-multiplied sums -/

/-- **`Evolution.op` distributes over a scalar-multiplied finite sum:**
`V.op (c • Σᵢ g i) = c • Σᵢ V.op (g i)`.  An immediate consequence of `Evolution.op` being a
continuous `ℂ`-linear map (`map_smul`/`map_sum`), so it needs nothing about the particular system
`S`.  It is used for pushing a gate through an explicit `½ Σ …` basis sum — e.g. the
gate-teleportation assembly's `cnotGate.onRight` over the reshaped register — without
`toLinearMap` bundling. -/
theorem Evolution.op_smul_sum (V : Evolution S) {ι : Type*} [Fintype ι] (c : ℂ)
    (g : ι → S.space) : V.op (c • ∑ i, g i) = c • ∑ i, V.op (g i) := by
  rw [map_smul, map_sum]

/-! ### The operator of a product of gates -/

/-- **`Evolution.op` respects monoid (list) products:** the operator of a product of `Evolution`
gates is the product of their operators, `l.prod.op = (l.map Evolution.op).prod`. Both `Evolution`'s
composition monoid and the operator ring `S.space →L[ℂ] S.space` are monoids and `Evolution.op` is
multiplicative (`Evolution.comp_op` + `ContinuousLinearMap.mul_def`), so this is the induced
list-product homomorphism. The reusable bridge from an `Evolution`-level gate product (a circuit as
a product of gates) to the operator-level product — e.g. it lets the symmetric-Trotter step's
palindromic product be reduced to a product of propagator operators. -/
theorem Evolution.op_prod (l : List (Evolution S)) :
    l.prod.op = (l.map Evolution.op).prod := by
  induction l with
  | nil => simp
  | cons U l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, Evolution.mul_def, Evolution.comp_op, ih,
      ContinuousLinearMap.mul_def]

/-- **`Evolution.op` respects monoid powers:** the operator of an `m`-fold gate power is the
`m`-fold operator power, `(Uᵐ).op = U.opᵐ`. The power specialization of `Evolution.op_prod`:
`Evolution.op` is multiplicative (`Evolution.comp_op`) and unit-preserving (`Evolution.id_op`), so
it commutes with `_ ^ m`. Used to identify the `m`-fold repetition of a gate with the corresponding
operator power — e.g. to rewrite `(e^{-iHt})ᵐ` as `e^{-imHt}` in the propagator power law below. -/
theorem Evolution.op_pow (U : Evolution S) (m : ℕ) : (U ^ m).op = U.op ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Evolution.mul_def, Evolution.comp_op, ih, pow_succ, ContinuousLinearMap.mul_def]

/-- **The propagator semigroup / power law** (Nielsen–Chuang eq. 2.91 iterated): repeating the
unit-`ℏ` propagator over time `t` a total of `m` times is the propagator over time `m·t`,
`(H.propagator 1 0 t)ᵐ = H.propagator 1 0 (m·t)`. Physically, evolving for time `t` `m` times in a
row is evolving for time `m·t`: the `m` exponentials all share the generator `H.op`, so they add.
This is the identity `(e^{-iHt})ᵐ = e^{-imHt}` that Exercise 4.50(b) uses to write the `m`-fold
symmetric-Trotter target `(e^{-2iHΔt})ᵐ` as the exact long-time propagator `e^{-2miHΔt}`. Proved at
the operator level: `Evolution.op_pow` turns the `m`-fold gate power into `exp(_)ᵐ`,
`NormedSpace.exp_nsmul` collects it into a single `exp(m • _)`, and the exponent scalars agree by
`push_cast; ring`. -/
theorem Observable.propagator_pow (H : Observable S) (t : ℝ) (m : ℕ) :
    (H.propagator 1 0 t) ^ m = H.propagator 1 0 ((m : ℝ) * t) := by
  have : NormedAlgebra ℚ (S.space →L[ℂ] S.space) := NormedAlgebra.restrictScalars ℚ ℝ _
  apply Evolution.ext
  rw [Evolution.op_pow]
  simp only [Observable.propagator_op]
  rw [← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring

/-- **The two pictures of unitary dynamics agree on a pure state** (Nielsen & Chuang, Exercise 8.1).
The density operator of the unitarily-evolved pure state equals the pure state's density operator
evolved by conjugation: `(U.evolvePure ψ).toState = U.evolve ψ.toState`, i.e.
`|Uψ⟩⟨Uψ| = U|ψ⟩⟨ψ|U†`. This is the equivalence between the vector picture `|ψ⟩ → U|ψ⟩` and the
density picture `ρ → E(ρ) ≡ UρU†` for `ρ = |ψ⟩⟨ψ|`. Reduces (`State.ext`) to the operator identity
`U(|ψ⟩⟨ψ|)U† = |Uψ⟩⟨Uψ|`, discharged by the rank-one composition lemmas. It is the
bridge between `evolvePure` (vector) and `evolve` (density), used wherever a
pure state is transported by a unitary (e.g. Ex 8.1, and the CSS-code equivalence of Ex 10.27). -/
theorem toState_evolvePure (U : Evolution S) (ψ : PureState S) :
    (U.evolvePure ψ).toState = U.evolve ψ.toState := by
  apply State.ext
  simp only [PureState.toState_op, Evolution.evolvePure_vec, Evolution.evolve_op,
    InnerProductSpace.rankOne_comp, InnerProductSpace.comp_rankOne,
    ContinuousLinearMap.adjoint_adjoint]

/-- **Unitary evolution preserves purity.** If a state `ρ` is pure, so is its evolution
`U.evolve ρ = UρU†`: the quantum operation `E(ρ) = UρU†` maps pure states to pure states. Immediate
from `toState_evolvePure`, with `U.evolvePure ψ` the witnessing pure state of the evolved density
operator. -/
theorem isPure_evolve (U : Evolution S) {ρ : State S} (hρ : ρ.IsPure) :
    (U.evolve ρ).IsPure := by
  obtain ⟨ψ, rfl⟩ := hρ
  exact ⟨U.evolvePure ψ, (toState_evolvePure U ψ).symm⟩

end AxQM
