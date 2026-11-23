/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Evolution
import ToMathlib.Analysis.InnerProductSpace.PolarNormal
import ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# AxQM.Postulates.API — the `d`-level system (qudit) and diagonal phase gates

A finite `d`-level system and the diagonal (phase) unitaries on it, generalizing
`AxQM/Postulates/API/Qubit.lean` (`qubit = qudit 2`) to arbitrary dimension. It is the register
model used by the circuit constructions of Nielsen & Chuang, Chapter 4 (e.g. Problem 4.1's
input and ancilla registers of dimension `2^m` / `2^n`).

* `qudit d` — the `d`-level quantum system, `QSystem.ofModel (EuclideanSpace ℂ (Fin d))`.
* `quditBasis i` (`|i⟩`) — the **computational-basis pure state** `|i⟩` of `qudit d`, the
  normalized standard basis vector `EuclideanSpace.single i 1` (mirrors `qubitBasis`).
* `diagPhase θ` — the **diagonal phase gate** `diag(e^{iθ₀},…,e^{iθ_{d-1}})` for a real
  angle vector `θ : Fin d → ℝ`, packaged as a unitary `Evolution (qudit d)`. It is unitary
  because a diagonal operator with unit-modulus entries (`|e^{iθ}| = 1`) is unitary; the
  construction discharges that obligation. `diagPhase` models the layer of single-qubit phase
  gates that, applied to a computational-basis register, imprints a computable phase — the `n`
  one-qubit gates of Problem 4.1.
* `diagPhase_op_apply_quditBasis` — the **eigenvalue action** `D|i⟩ = e^{iθᵢ}|i⟩`: a diagonal
  phase gate scales each computational-basis vector by its phase. The key computational input
  for phase-kickback arguments.

## Design notes

* `diagPhase θ`'s operator is built directly on the spectral-operator API
  `OrthonormalBasis.diagonalOperator` (`ToMathlib.Analysis.InnerProductSpace.PolarNormal`),
  `b.diagonalOperator w = ∑ᵢ wᵢ • |bᵢ⟩⟨bᵢ|`, for `b = EuclideanSpace.basisFun (Fin d) ℂ` (the
  computational basis) and `w i = e^{iθᵢ}`. Unitarity is `diagonalOperator_mem_unitary` (a
  diagonal operator with unit-modulus diagonal is unitary), and the eigenvalue action is
  `diagonalOperator_apply_self` (`(b.diagonalOperator w) (b q) = w q • b q`) — reusing the
  purpose-built API rather than an entrywise matrix computation.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **`d`-level quantum system (qudit)**: the system whose state space is the standard
`d`-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin d)`. The qubit is `qudit 2`;
`qudit (2^n)` is an `n`-qubit register. -/
def qudit (d : ℕ) : QSystem := QSystem.ofModel (EuclideanSpace ℂ (Fin d))

@[simp]
theorem qudit_space (d : ℕ) : (qudit d).space = EuclideanSpace ℂ (Fin d) := rfl

/-- The state space of `qudit d` is nontrivial when `d ≥ 1` (it contains the computational-basis
vectors `|i⟩`). Supplies the `Nontrivial S.space` hypothesis that state constructions such as the
maximally mixed state `I/d` require. -/
instance qudit_space_nontrivial {d : ℕ} [NeZero d] : Nontrivial (qudit d).space := by
  rw [qudit_space]; infer_instance

/-- **The qudit has dimension `d`**: `finrank ℂ (qudit d).space = d`, since `(qudit d).space` is
`EuclideanSpace ℂ (Fin d)`. The `d`-level generalization of `finrank_qubit_space`; for `qudit (2^n)`
this is `2^n`, and for `qudit 4` it gives the `2⁻² = ¼` high-temperature prefactor of Exercise 7.36
(`n = 2`). -/
theorem finrank_qudit (d : ℕ) : Module.finrank ℂ (qudit d).space = d := by
  change Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = d
  exact finrank_euclideanSpace_fin

/-- The **computational-basis pure state** `|i⟩` of `qudit d`: the standard basis vector
`EuclideanSpace.single i 1`, normalized because `‖EuclideanSpace.single i 1‖ = ‖(1 : ℂ)‖ = 1`.
The `d`-level generalization of `qubitBasis`. -/
def quditBasis {d : ℕ} (i : Fin d) : PureState (qudit d) where
  vec := EuclideanSpace.single i 1
  normalized := by
    change ‖EuclideanSpace.single i (1 : ℂ)‖ = 1
    simp

@[simp]
theorem quditBasis_vec {d : ℕ} (i : Fin d) :
    (quditBasis i).vec = EuclideanSpace.single i 1 := rfl

/-- The **computational basis of `qudit d` is orthonormal** (`⟨i|j⟩ = δᵢⱼ`), being the standard
`EuclideanSpace.single` basis (`EuclideanSpace.orthonormal_single`). -/
theorem quditBasis_orthonormal (d : ℕ) :
    Orthonormal ℂ (fun i : Fin d => (quditBasis i).vec) := by
  simp only [quditBasis_vec]
  exact EuclideanSpace.orthonormal_single

/-- **Inner product of two computational-basis states** (orthonormality in δ-form):
`⟨x, y⟩ = δₓᵧ`, i.e. `1` if `x = y` and `0` otherwise. The δ-form of `quditBasis_orthonormal`, the
citable input to every amplitude computation over the computational basis. -/
theorem quditBasis_inner {d : ℕ} (x y : Fin d) :
    inner ℂ (quditBasis x).vec (quditBasis y).vec = if x = y then (1 : ℂ) else 0 :=
  orthonormal_iff_ite.mp (quditBasis_orthonormal d) x y

/-- The **qudit computational basis reindexed along `Fintype.equivFin`** by an arbitrary finite
index type `ι` is orthonormal: `fun i => (quditBasis (Fintype.equivFin ι i)).vec` is an orthonormal
family. The reindexed form consumed whenever a classical register indexed by a general `Fintype ι`
is realised on `qudit (Fintype.card ι)` (e.g. the Holevo classical–quantum state). Orthonormality
of the underlying basis (`quditBasis_orthonormal`) is stable under precomposition with the injective
reindexing bijection `Fintype.equivFin ι`. -/
theorem quditBasis_equivFin_orthonormal (ι : Type*) [Fintype ι] :
    Orthonormal ℂ (fun i => (quditBasis (Fintype.equivFin ι i)).vec) :=
  (quditBasis_orthonormal (Fintype.card ι)).comp _ (Fintype.equivFin ι).injective

/-- **A qudit gate is determined by its action on the computational basis.** Two evolutions
`A`, `B` of `qudit d` are equal as soon as their operators agree on every basis vector `|i⟩`
(`i : Fin d`). The `d`-level generalization of `qubit_evolution_ext`; it is the extensionality
lemma that reduces an operator identity between diagonal gates (e.g. a phase layer written two
ways) to a per-basis-vector eigenvalue comparison. -/
theorem qudit_evolution_ext {d : ℕ} {A B : Evolution (qudit d)}
    (h : ∀ i : Fin d, A.op (quditBasis i).vec = B.op (quditBasis i).vec) : A = B := by
  apply Evolution.ext
  apply ContinuousLinearMap.coe_injective
  refine Module.Basis.ext (EuclideanSpace.basisFun (Fin d) ℂ).toBasis (fun i => ?_)
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  exact (by simpa only [quditBasis_vec] using h i :
    A.op (EuclideanSpace.single i 1) = B.op (EuclideanSpace.single i 1))

/-- The **diagonal phase gate** `D = diag(e^{iθ₀}, …, e^{iθ_{d-1}})` on `qudit d`, for a real
angle vector `θ : Fin d → ℝ`, as a unitary `Evolution`. Its operator is the operator diagonal in
the computational basis with entries `e^{iθⱼ}`, i.e.
`(EuclideanSpace.basisFun (Fin d) ℂ).diagonalOperator (fun j => exp (θⱼ · i))`; it is unitary
because each diagonal entry `e^{iθⱼ}` has unit modulus
(`OrthonormalBasis.diagonalOperator_mem_unitary`). This is the phase layer used in the
computable-phase-shift circuit (N&C Problem 4.1). -/
def diagPhase {d : ℕ} (θ : Fin d → ℝ) : Evolution (qudit d) where
  op := (EuclideanSpace.basisFun (Fin d) ℂ).diagonalOperator
          (fun i => Complex.exp ((θ i : ℂ) * Complex.I))
  unitary := by
    change (EuclideanSpace.basisFun (Fin d) ℂ).diagonalOperator
        (fun i => Complex.exp ((θ i : ℂ) * Complex.I))
        ∈ unitary (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    exact OrthonormalBasis.diagonalOperator_mem_unitary _ _ (fun i => by simp [Complex.norm_exp])

@[simp]
theorem diagPhase_op {d : ℕ} (θ : Fin d → ℝ) :
    (diagPhase θ).op = (EuclideanSpace.basisFun (Fin d) ℂ).diagonalOperator
        (fun i => Complex.exp ((θ i : ℂ) * Complex.I)) := rfl

/-- **Action of a computational-basis diagonal operator on a standard basis vector:**
`(basisFun.diagonalOperator w)|i⟩ = wᵢ|i⟩`, since `|i⟩ = EuclideanSpace.basisFun … i`
(`OrthonormalBasis.diagonalOperator_apply_self`). The computation behind
`diagPhase_op_apply_quditBasis`. -/
theorem basisFun_diagonalOperator_apply_single {d : ℕ} (w : Fin d → ℂ) (i : Fin d) :
    (EuclideanSpace.basisFun (Fin d) ℂ).diagonalOperator w (EuclideanSpace.single i 1)
      = w i • EuclideanSpace.single i (1 : ℂ) := by
  rw [← EuclideanSpace.basisFun_apply, OrthonormalBasis.diagonalOperator_apply_self]

/-- **Eigenvalue action of a diagonal phase gate:** `D|i⟩ = e^{iθᵢ}|i⟩`. The diagonal phase
gate `diagPhase θ` scales the `i`-th computational-basis vector by its phase `e^{iθᵢ}`. This
is the computational lever behind phase kickback: an ancilla left in `|f(x)⟩` picks up exactly
`e^{iθ_{f(x)}}`. -/
theorem diagPhase_op_apply_quditBasis {d : ℕ} (θ : Fin d → ℝ) (i : Fin d) :
    (diagPhase θ).op (quditBasis i).vec
      = Complex.exp ((θ i : ℂ) * Complex.I) • (quditBasis i).vec :=
  basisFun_diagonalOperator_apply_single (fun j => Complex.exp ((θ j : ℂ) * Complex.I)) i

end AxQM
