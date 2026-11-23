/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BlochState
import AxQM.Postulates.API.MaximallyMixed
import AxQM.NC.Ch2.Exercise2_71

/-!
# Nielsen & Chuang, Exercise 2.72 — the Bloch sphere for mixed states

*(N&C p. 105.)* The Bloch-sphere picture of a single-qubit pure state
(§1.2) generalizes to mixed states: every qubit density operator is `ρ = ½(I + r⃗·σ⃗)` (eq. 2.175)
for a real three-vector `r⃗` — the **Bloch vector** — with `‖r⃗‖ ≤ 1`.

The matrix and operator facts used are:

* the Bloch matrix `½(I + r·σ)` and its Hermitian / trace-one / positive-semidefinite
  facts — `AxQM.Concrete.blochMatrix` and lemmas (`AxQM/Concrete/BlochMatrix.lean`);
* its promotion to a qubit density operator `blochState r h` and the `Matrix.toEuclideanCLM`
  positivity / trace bridges — `AxQM.blochState` (`AxQM/Postulates/API/BlochState.lean`).

## What is proved here

* `State.exists_blochState` — **part (1):** every qubit state `ρ : State qubit` is `blochState r h`
  for some Bloch vector `r` with `‖r‖² = r₀² + r₁² + r₂² ≤ 1`. Recovering the matrix `M` of `ρ.op`
  across `Matrix.toEuclideanCLM`, `M` is Hermitian, trace one and positive semidefinite (from `ρ`
  being a density operator), so `Concrete.exists_blochMatrix_of_isHermitian_trace_one` gives `r`
  with `M = Concrete.blochMatrix r`, and `Concrete.blochMatrix_posSemidef_iff` gives `‖r‖² ≤ 1`.
* `blochState_injective` — **part (1), uniqueness:** the Bloch vector is unique — `blochState r₁ h₁
  = blochState r₂ h₂ → r₁ = r₂` — since `Matrix.toEuclideanCLM` and `Concrete.blochMatrix` are both
  injective. Together with `State.exists_blochState` this is the bijection between qubit states and
  the closed Bloch ball `‖r⃗‖ ≤ 1`.

* `blochState_zero_eq_maximallyMixed` — **part (2):** the state with Bloch vector `r⃗ = 0` is the
  maximally mixed state, `blochState 0 = maximallyMixedState qubit`. This is
  the form of "the Bloch vector representation of `ρ = I/2` is `r⃗ = 0`", stated against the
  library's canonical `maximallyMixedState` (whose operator is `I/2`, `dim qubit = 2`); with
  `blochState_injective` the unique Bloch vector of `I/2` is `0`. The underlying operator identity
  `(blochState 0).op = ½ I` is the lemma `AxQM.blochState_zero_op` in
  `AxQM/Postulates/API/BlochState.lean`.

* `blochState_purity` — the **purity** `tr(ρ²)` of a Bloch state is `(1 + ‖r⃗‖²)/2`. The density
  operator is `Matrix.toEuclideanCLM (Concrete.blochMatrix r)`, so `ρ²` is `toEuclideanCLM` of
  `Concrete.blochMatrix r * Concrete.blochMatrix r` (`toEuclideanCLM` is a `⋆`-algebra
  homomorphism), whose trace is `(1 + ‖r⃗‖²)/2` (`Concrete.blochMatrix_sq_trace`,
  `Matrix.trace_toEuclideanCLM`).
* `blochState_isPure_iff_norm_one` — **part (3):** a qubit state is pure iff its Bloch vector is a
  unit vector, `(blochState r h).IsPure ↔ ‖r⃗‖² = r₀² + r₁² + r₂² = 1` (i.e. `‖r⃗‖ = 1`, since
  `‖r⃗‖ ≥ 0`). Immediate from `blochState_purity` and the Exercise 2.71 purity criterion
  `State.purity_eq_one_iff_isPure` (`tr(ρ²) = 1 ↔ ρ` pure): the purity `(1 + ‖r⃗‖²)/2` equals `1`
  exactly when `‖r⃗‖² = 1`. Together with `State.exists_blochState` this is the Bloch-sphere
  picture: the pure states are the *surface* `‖r⃗‖ = 1` of the Bloch ball, the mixed states its
  interior.

* `blochPureState_toState_eq_blochState` — **part (4):** for pure states the Bloch vector coincides
  with the §1.2 parametrization. The §1.2 pure state `|ψ(θ,φ)⟩ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩`
  (eq. 1.4, `blochPureState θ φ`) equals `blochState (blochSphereVector θ φ)`, the Bloch state whose
  vector is the §1.2 Cartesian point `r⃗ = (sin θ cos φ, sin θ sin φ, cos θ)`
  (`Concrete.blochSphereVector`). That is, the density operator `|ψ⟩⟨ψ|` of the §1.2 pure state is
  `½(I + r⃗·σ⃗)` for exactly the §1.2 vector, so the part-(1) Bloch vector read off `½(I + r⃗·σ⃗)`
  is the §1.2 one. Immediate from the operator identity `blochPureState_toState_op`, `blochState_op`
  (both operators are `Matrix.toEuclideanCLM (Concrete.blochMatrix (blochSphereVector θ φ))`); the
  `‖r⃗‖ ≤ 1` side condition is `Concrete.blochSphereVector_normSq` (`‖r⃗‖ = 1`, consistent with part
  (3)). Together with `blochState_injective` this pins the Bloch vector of `|ψ(θ,φ)⟩` to `(sin θ cos
  φ, sin θ sin φ, cos θ)`, completing the §1.2 Bloch-sphere picture generalized to mixed states.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.72(1): every qubit density operator is a Bloch state.** For any
qubit state `ρ`, there is a real three-vector `r` with `‖r‖² = r₀² + r₁² + r₂² ≤ 1` such that
`ρ = blochState r h`, i.e. `ρ = ½(I + r⃗·σ⃗)` (eq. 2.175). The vector `r` is the state's Bloch
vector, lying in the closed unit ball `‖r⃗‖ ≤ 1`.

Proof: the matrix `M := (Matrix.toEuclideanCLM).symm ρ.op` of the density operator is positive
semidefinite (`ρ.op` is positive, transported by `toEuclideanCLM_isPositive_iff`), hence Hermitian
(`Matrix.PosSemidef.1`), and has trace one (`ρ` has trace one, transported by
`toEuclideanCLM_trace`). `Concrete.exists_blochMatrix_of_isHermitian_trace_one` then yields `r` with
`M = Concrete.blochMatrix r`, and `Concrete.blochMatrix_posSemidef_iff` turns positivity of `M` into
`‖r‖² ≤ 1`. -/
theorem State.exists_blochState (ρ : State qubit) :
    ∃ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1), ρ = blochState r h := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).symm ρ.op
    with hMdef
  have hop : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M = ρ.op := by
    rw [hMdef]; exact StarAlgEquiv.apply_symm_apply _ _
  have hpsd : M.PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanCLM_iff, hop]; exact ρ.isPositive_op
  have htr : M.trace = 1 := by
    rw [← Matrix.trace_toEuclideanCLM, hop]; exact ρ.trace_op_eq_one
  obtain ⟨r, hr⟩ := Concrete.exists_blochMatrix_of_isHermitian_trace_one hpsd.1 htr
  refine ⟨r, (Concrete.blochMatrix_posSemidef_iff r).mp (hr ▸ hpsd), ?_⟩
  apply State.ext
  rw [blochState_op, ← hr, hop]

/-- **Nielsen & Chuang, Exercise 2.72(1): the Bloch vector is unique.** If two Bloch states are
equal, their Bloch vectors are equal: `blochState r₁ h₁ = blochState r₂ h₂ → r₁ = r₂`. The
underlying operators agree, so the `Matrix.toEuclideanCLM` images of `Concrete.blochMatrix r₁` and
`Concrete.blochMatrix r₂` agree; both `Matrix.toEuclideanCLM` and `Concrete.blochMatrix` are
injective, giving `r₁ = r₂`. Together with `State.exists_blochState` this is the bijection between
qubit states and the closed Bloch ball. -/
theorem blochState_injective {r₁ r₂ : Fin 3 → ℝ}
    {h₁ : r₁ 0 ^ 2 + r₁ 1 ^ 2 + r₁ 2 ^ 2 ≤ 1} {h₂ : r₂ 0 ^ 2 + r₂ 1 ^ 2 + r₂ 2 ^ 2 ≤ 1}
    (heq : blochState r₁ h₁ = blochState r₂ h₂) : r₁ = r₂ := by
  have hop : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix r₁)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.blochMatrix r₂) := by
    rw [← blochState_op r₁ h₁, ← blochState_op r₂ h₂, heq]
  exact Concrete.blochMatrix_injective
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective hop)

/-- **Nielsen & Chuang, Exercise 2.72(2): the Bloch representation of `ρ = I/2` is `r⃗ = 0`.**
The state with Bloch vector `r⃗ = 0` is the maximally mixed state `I/2` — `blochState 0 =
maximallyMixedState qubit`. Both density operators are `½ I` — `blochState_zero_op` for the left
side and `maximallyMixedState_op` with `finrank_qubit_space` (`dim qubit = 2`) for the right — so
the states agree by `State.ext`. With `blochState_injective`, the unique Bloch vector of the
maximally mixed state is `0`. -/
theorem blochState_zero_eq_maximallyMixed :
    blochState (0 : Fin 3 → ℝ) (by simp) = maximallyMixedState qubit := by
  apply State.ext
  rw [blochState_zero_op, maximallyMixedState_op, finrank_qubit_space]
  norm_num

/-- **The purity `tr(ρ²)` of a Bloch state is `(1 + ‖r‖²)/2`** (with `‖r‖² = r₀² + r₁² + r₂²`).
For a Bloch vector `r` in the closed unit ball, `(blochState r h).purity = (1 + (r₀²+r₁²+r₂²))/2`.

Proof: the density operator `(blochState r h).op` is `Matrix.toEuclideanCLM (Concrete.blochMatrix
r)`, so — `Matrix.toEuclideanCLM` being a `⋆`-algebra homomorphism (`map_mul`) — its square is
`Matrix.toEuclideanCLM (Concrete.blochMatrix r * Concrete.blochMatrix r)`. Its operator trace is
the matrix trace `(Concrete.blochMatrix r * Concrete.blochMatrix r).trace`
(`Matrix.trace_toEuclideanCLM`), which is the real `(1 + ‖r‖²)/2` (`Concrete.blochMatrix_sq_trace`);
`RCLike.re` of that real coercion is the real itself. This is the purity that decides part (3). -/
theorem blochState_purity (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    (blochState r h).purity = (1 + (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)) / 2 := by
  -- `ρ.op²` is `toEuclideanCLM` of the squared Bloch matrix (`toEuclideanCLM` is `⋆`-algebra).
  have hop : (blochState r h).op * (blochState r h).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Concrete.blochMatrix r * Concrete.blochMatrix r) := by
    rw [blochState_op]
    exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) _ _).symm
  rw [State.purity, hop]
  -- `qubit.space` is defeq to `EuclideanSpace ℂ (Fin 2)`; rephrase the trace there so the matrix
  -- trace bridge `Matrix.trace_toEuclideanCLM` matches syntactically.
  change RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin 2))
      ↑(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
        (Concrete.blochMatrix r * Concrete.blochMatrix r)))
      = (1 + (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2)) / 2
  rw [Matrix.trace_toEuclideanCLM, Concrete.blochMatrix_sq_trace]
  simp [-Complex.ofReal_pow]

/-- **Nielsen & Chuang, Exercise 2.72(3): a qubit state is pure iff `‖r⃗‖ = 1`.** The Bloch state
`ρ = ½(I + r⃗·σ⃗)` is pure exactly when its Bloch vector is a unit vector,
`(blochState r h).IsPure ↔ r₀² + r₁² + r₂² = 1` (i.e. `‖r⃗‖ = 1`, since `‖r⃗‖ ≥ 0`).

Proof: by the Exercise 2.71 purity criterion `State.purity_eq_one_iff_isPure` a state is pure iff
its purity `tr(ρ²)` is `1`, and the purity of a Bloch state is `(1 + ‖r⃗‖²)/2`
(`blochState_purity`); `(1 + ‖r⃗‖²)/2 = 1` iff `‖r⃗‖² = 1`.

Combined with `State.exists_blochState` (part 1), this completes the Bloch-sphere picture for a
single qubit: qubit states correspond to the closed Bloch ball `‖r⃗‖ ≤ 1`, the pure states being
exactly its surface `‖r⃗‖ = 1` and the mixed states its interior `‖r⃗‖ < 1`. -/
theorem blochState_isPure_iff_norm_one (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1) :
    (blochState r h).IsPure ↔ r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1 := by
  rw [← State.purity_eq_one_iff_isPure, blochState_purity]
  constructor <;> intro hp <;> linarith

/-- **Nielsen & Chuang, Exercise 2.72(4): for pure states the Bloch vector coincides with the §1.2
parametrization.** The §1.2 single-qubit pure state `|ψ(θ,φ)⟩ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩`
(eq. 1.4, `blochPureState θ φ`) is the Bloch state `blochState (blochSphereVector θ φ)` whose Bloch
vector is the §1.2 Cartesian point `r⃗ = (sin θ cos φ, sin θ sin φ, cos θ)`: its density operator
`|ψ⟩⟨ψ|` equals `½(I + r⃗·σ⃗)` (eq. 2.175) for exactly the §1.2 vector.

So the Bloch vector attached to a pure state by the mixed-state representation of part (1) — the
`r⃗` read off `ρ = ½(I + r⃗·σ⃗)` — coincides with the §1.2 Bloch-sphere point of the state. The side
condition `‖r⃗‖ ≤ 1` is `Concrete.blochSphereVector_normSq` (in fact `‖r⃗‖ = 1`, matching part (3):
pure states lie on the surface). With `blochState_injective` this `r⃗` is the unique Bloch vector of
`|ψ(θ,φ)⟩`, so the two descriptions of the Bloch vector agree.

Proof: both density operators are `Matrix.toEuclideanCLM (Concrete.blochMatrix (blochSphereVector θ
φ))` — the left by `blochPureState_toState_op` (the rank-one projector `|ψ⟩⟨ψ|` is the
`toEuclideanCLM` image of the outer product `|ψ⟩⟨ψ|`, which
`Concrete.outerSelf_blochKet_eq_blochMatrix` identifies with the §1.2 Bloch matrix), the right by
`blochState_op` — so the states agree by
`State.ext`. -/
theorem blochPureState_toState_eq_blochState (θ φ : ℝ) :
    (blochPureState θ φ).toState
      = blochState (Concrete.blochSphereVector θ φ) (Concrete.blochSphereVector_normSq θ φ).le := by
  apply State.ext
  rw [blochPureState_toState_op, blochState_op]

end AxQM
