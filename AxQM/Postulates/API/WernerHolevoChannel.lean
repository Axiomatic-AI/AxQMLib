/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumChannel
import AxQM.Postulates.API.RandomUnitaryChannel
import AxQM.Postulates.API.MaximallyMixed
import AxQM.Postulates.API.Qudit
import AxQM.Concrete.WernerHolevo
import ToMathlib.Analysis.CStarAlgebra.Matrix
import ToMathlib.Analysis.InnerProductSpace.OperatorSumMatrix

/-!
# AxQM.Postulates.API — the Werner–Holevo qutrit channel

The **Werner–Holevo channel** on a qutrit (`qudit 3`),
`Φ(ρ) = ½(tr(ρ)·I − ρᵀ)`,
is the Landau–Streater counterexample of Nielsen & Chuang, **Problem 8.3**: a genuine unital CPTP
quantum channel in dimension `3` that is *not* a random-unitary average `∑ₖ pₖ Uₖ ρ Uₖ†`. This file
defines the **channel** and proves it is a unital channel — the `IsChannel ∧ IsUnital` half
of the counterexample. (Its non-membership in the random-unitary set is the theorem
`¬ IsRandomUnitary wernerHolevoChannel` in `AxQM/NC/Ch8/Problem8_3.lean`.)

Its operator-sum (Kraus) representation uses the three real antisymmetric `𝔰𝔬(3)` generators
`Aₐ = wernerHolevoGen a` (`Concrete/WernerHolevo.lean`), scaled by `1/√2`:

* `AxQM.wernerHolevoKraus` — the Kraus operators `Aₐ/√2` as operators on `(qudit 3).space`.
* `AxQM.wernerHolevoKraus_completeness` — the **completeness relation**
  `∑ₐ (Aₐ/√2)† (Aₐ/√2) = I`, transporting the matrix identity `∑ₐ Aₐᴴ Aₐ = 2·I`
  (`Concrete.wernerHolevoGen_conjTranspose_mul_self_sum`) through the `⋆`-algebra isomorphism
  `Matrix.toEuclideanCLM`. It certifies the channel is trace preserving.
* `AxQM.wernerHolevoChannel` — the channel `Φ(ρ) = ∑ₐ (Aₐ/√2) ρ (Aₐ/√2)†` as a state-map on
  `qudit 3`. The output is a genuine `State`: positivity is complete positivity of the Kraus map
  (`krausSumₗ_isPositive`) and trace `1` is the completeness relation (`trace_krausSumₗ`).
* `AxQM.wernerHolevoChannel_op` — the **closed form** `Φ(ρ) = ½(tr(ρ)·I − ρᵀ)` in the
  computational basis: for `ρ.op = Matrix.toEuclideanCLM M`, the output operator is
  `Matrix.toEuclideanCLM (½·(tr(M)·I − Mᵀ))`, transporting the operator-sum identity
  `∑ₐ Aₐ M Aₐᴴ = tr(M)·I − Mᵀ` (`Concrete.wernerHolevoGen_sum_conj`). This is the identity the
  non-membership argument evaluates on pure states.
* `AxQM.wernerHolevoChannel_isChannel` — `Φ` is a **CPTP quantum channel** (`IsChannel`),
  via the operator-sum constructor `isChannel_of_kraus` and the completeness relation.
* `AxQM.wernerHolevoChannel_isUnital` — `Φ` is **unital** (`IsUnital`, `Φ(I/3) = I/3`):
  from the closed form with `M = I/3` (`tr(I/3) = 1`, `(I/3)ᵀ = I/3`, so `Φ(I/3) = ½(I − I/3) =
  I/3`). Together with `wernerHolevoChannel_isChannel` this exhibits `Φ` as a *unital channel* — the
  object Problem 8.3's counterexample requires.

## Design notes

* **Why `qudit 3`, and the operator-sum route to positivity.** The counterexample is genuinely
  `3`-dimensional (in dimension `2` every unital channel *is* random-unitary), so the
  system is `qudit 3`. Unlike the depolarizing channel — a manifest convex
  combination of states — the Werner–Holevo output `½(tr(ρ)I − ρᵀ)` is not obviously a density
  operator; its positivity comes precisely from the operator-sum form (`krausSumₗ_isPositive`),
  which is why the `State` is built as `krausSumₗ wernerHolevoKraus ρ.op` and the closed form is a
  consequence.
* **Why the closed form is stated with a matrix hypothesis.** The transpose `ρᵀ` is a
  basis-dependent (computational-basis) notion with no basis-free operator form, so `Φ`'s closed
  form is phrased through `Matrix.toEuclideanCLM`: given `ρ.op = Matrix.toEuclideanCLM M`, the
  output is `Matrix.toEuclideanCLM (½·(tr(M)·I − Mᵀ))`. This is the shape the pure-state evaluation
  of the non-membership argument consumes (with `M = ψ ⬝ ψ†` the outer-product matrix).
-/

open scoped InnerProductSpace ComplexOrder Matrix
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- `star (1/√2) = 1/√2` over `ℂ` (the scalar `1/√2` is real, hence fixed by conjugation). -/
private theorem star_inv_sqrt_two : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]

/-- `(1/√2)·(1/√2) = 1/2` over `ℂ`: the scalar produced by pairing two Werner–Holevo Kraus factors.
-/
private theorem inv_sqrt_two_mul_self :
    ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The Werner–Holevo Kraus operators as scaled matrices `Aₐ/√2` (before transport to operators):
`(1/√2)·wernerHolevoGen a`. -/
private def wernerHolevoKrausMatrix (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • Concrete.wernerHolevoGen a

/-- **The Werner–Holevo Kraus operators** `Aₐ/√2` on `qudit 3`, for `a : Fin 3`: the three
antisymmetric generators `Aₐ = Concrete.wernerHolevoGen a` (a basis of `𝔰𝔬(3)`) scaled by `1/√2`,
transported to operators on `(qudit 3).space = EuclideanSpace ℂ (Fin 3)` by `Matrix.toEuclideanCLM`.
Their operator sum `∑ₐ (Aₐ/√2) ρ (Aₐ/√2)†` is the Werner–Holevo channel `wernerHolevoChannel`. -/
def wernerHolevoKraus (a : Fin 3) : (qudit 3).space →L[ℂ] (qudit 3).space :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3) (wernerHolevoKrausMatrix a)

/-- **The completeness relation** `∑ₐ (Aₐ/√2)† (Aₐ/√2) = I` for the Werner–Holevo Kraus operators
(Nielsen & Chuang's trace condition, certifying the channel is trace preserving). Each summand is
`(1/2)·Aₐᴴ Aₐ` transported to an operator, and `∑ₐ Aₐᴴ Aₐ = 2·I`
(`Concrete.wernerHolevoGen_conjTranspose_mul_self_sum`), so the sum is
`(1/2)·toEuclideanCLM(2·I) = toEuclideanCLM(I) = I`. -/
theorem wernerHolevoKraus_completeness :
    ∑ a, (adjoint (wernerHolevoKraus a)).comp (wernerHolevoKraus a) = 1 := by
  have hmat : (∑ a, (wernerHolevoKrausMatrix a)ᴴ * wernerHolevoKrausMatrix a)
      = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    simp only [wernerHolevoKrausMatrix, Matrix.conjTranspose_smul, star_inv_sqrt_two,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_sqrt_two_mul_self]
    rw [← Finset.smul_sum, Concrete.wernerHolevoGen_conjTranspose_mul_self_sum, smul_smul,
      inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
  -- `qudit 3 := QSystem.ofModel (EuclideanSpace ℂ (Fin 3))`, so `(qudit 3).space` reduces to the
  -- bare `EuclideanSpace` by `rfl`, but `Matrix.toEuclideanCLM` naturally produces the bare-typed
  -- CLM, and `calc`'s `Trans` resolution needs syntactic, not just defeq, type agreement across
  -- steps — so each intermediate fact is stated (and ascribed at the bundled type) as its own
  -- `have`, then chained with a plain `rw`, bypassing `calc` entirely.
  have step1 : ∑ a, (adjoint (wernerHolevoKraus a)).comp (wernerHolevoKraus a)
      = (∑ a, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)
          ((wernerHolevoKrausMatrix a)ᴴ * wernerHolevoKrausMatrix a) :
          (qudit 3).space →L[ℂ] (qudit 3).space) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have hadj : adjoint (wernerHolevoKraus a)
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3) ((wernerHolevoKrausMatrix a)ᴴ) :=
      (Matrix.toEuclideanCLM_conjTranspose_eq_adjoint (wernerHolevoKrausMatrix a)).symm
    -- Build the fully bare-typed identity as its own standalone fact first: `rw`-ing `hadj`
    -- straight into the bundled goal would leave the `.comp` node's *other* operand
    -- (`wernerHolevoKraus a`, still bundled) mismatched against `hadj`'s bare RHS. `exact` (full
    -- defeq, unlike `rw`'s syntactic matching) bridges both that and `wernerHolevoKraus`'s own
    -- unfolding in one shot.
    have hmul : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3) ((wernerHolevoKrausMatrix a)ᴴ)
          ∘SL Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3) (wernerHolevoKrausMatrix a)
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)
            ((wernerHolevoKrausMatrix a)ᴴ * wernerHolevoKrausMatrix a) := by
      rw [← ContinuousLinearMap.mul_def]
      exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)) _ _).symm
    rw [hadj]
    exact hmul
  have step2 : (∑ a, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)
        ((wernerHolevoKrausMatrix a)ᴴ * wernerHolevoKrausMatrix a) :
        (qudit 3).space →L[ℂ] (qudit 3).space)
      = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)
          (∑ a, (wernerHolevoKrausMatrix a)ᴴ * wernerHolevoKrausMatrix a) :
          (qudit 3).space →L[ℂ] (qudit 3).space) := (map_sum _ _ _).symm
  rw [step1, step2, hmat, map_one]
  rfl

/-- **The Werner–Holevo qutrit channel** `Φ(ρ) = ∑ₐ (Aₐ/√2) ρ (Aₐ/√2)† = ½(tr(ρ)·I − ρᵀ)` as a
state-map on `qudit 3` (Nielsen & Chuang, Problem 8.3; the Landau–Streater counterexample). The
output is a genuine `State` — positivity from complete positivity of the Kraus map and trace `1`
from the completeness relation (`isDensityOp_krausSumₗ` with `wernerHolevoKraus_completeness`). -/
def wernerHolevoChannel (ρ : State (qudit 3)) : State (qudit 3) where
  op := (krausSumₗ wernerHolevoKraus) ρ.op
  isDensity :=
    isDensityOp_krausSumₗ wernerHolevoKraus wernerHolevoKraus_completeness ρ.isDensity

/-- The operator of `wernerHolevoChannel ρ` is the Kraus sum `∑ₐ (Aₐ/√2) ρ (Aₐ/√2)†`. -/
@[simp]
theorem wernerHolevoChannel_op_krausSum (ρ : State (qudit 3)) :
    (wernerHolevoChannel ρ).op = (krausSumₗ wernerHolevoKraus) ρ.op := rfl

/-- **The closed form of the Werner–Holevo channel** `Φ(ρ) = ½(tr(ρ)·I − ρᵀ)` in the computational
basis. If a state's operator is `ρ.op = Matrix.toEuclideanCLM M`, then
`(Φ ρ).op = Matrix.toEuclideanCLM (½·(tr(M)·I − Mᵀ))`. Proved by transporting the entrywise
operator-sum identity `∑ₐ Aₐ M Aₐᴴ = tr(M)·I − Mᵀ` (`Concrete.wernerHolevoGen_sum_conj`) through
`Matrix.toEuclideanCLM` (`krausSumₗ_toEuclideanCLM`), each Kraus pairing contributing
`(1/√2)² = 1/2`. -/
theorem wernerHolevoChannel_op {M : Matrix (Fin 3) (Fin 3) ℂ} (ρ : State (qudit 3))
    (hM : ρ.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3) M) :
    (wernerHolevoChannel ρ).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)
          ((2 : ℂ)⁻¹ • (M.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - Mᵀ)) := by
  have hmat : (∑ a, wernerHolevoKrausMatrix a * M * (wernerHolevoKrausMatrix a)ᴴ)
      = (2 : ℂ)⁻¹ • (M.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - Mᵀ) := by
    simp only [wernerHolevoKrausMatrix, Matrix.conjTranspose_smul, star_inv_sqrt_two,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_sqrt_two_mul_self]
    rw [← Finset.smul_sum, Concrete.wernerHolevoGen_sum_conj]
  rw [wernerHolevoChannel_op_krausSum, hM]
  change (krausSumₗ fun a =>
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3) (wernerHolevoKrausMatrix a))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3) M) = _
  rw [krausSumₗ_toEuclideanCLM, hmat]

/-- **The Werner–Holevo channel is a CPTP quantum channel** (`IsChannel`). Its operation elements
are the Werner–Holevo Kraus operators `Aₐ/√2`, whose completeness relation
`∑ₐ (Aₐ/√2)† (Aₐ/√2) = I` (`wernerHolevoKraus_completeness`) certifies trace preservation; complete
positivity is automatic for an operator-sum map (`isChannel_of_kraus`). -/
theorem wernerHolevoChannel_isChannel : IsChannel wernerHolevoChannel :=
  isChannel_of_kraus wernerHolevoKraus wernerHolevoKraus_completeness (fun _ => rfl)

/-- **The Werner–Holevo channel is unital**, `Φ(I/3) = I/3` (Nielsen & Chuang's `E(I) = I` in the
fixed-point form over `maximallyMixedState`). Immediate from the closed form
`wernerHolevoChannel_op` with `M = I/3`: `tr(I/3) = 1` and `(I/3)ᵀ = I/3`, so
`Φ(I/3) = ½(1·I − I/3) = ½·(2/3)·I = I/3`. Together with `wernerHolevoChannel_isChannel` this makes
`Φ` a **unital channel** — the object over which Problem 8.3's counterexample is posed. -/
theorem wernerHolevoChannel_isUnital : IsUnital wernerHolevoChannel := by
  have hfin : Module.finrank ℂ (qudit 3).space = 3 := finrank_euclideanSpace_fin
  have hM : (maximallyMixedState (qudit 3)).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)
          ((3 : ℂ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
    rw [maximallyMixedState_op, hfin, map_smul, map_one]
    congr 1
  apply State.ext
  rw [wernerHolevoChannel_op (maximallyMixedState (qudit 3)) hM, hM]
  congr 1
  rw [Matrix.trace_smul, Matrix.trace_one, Matrix.transpose_smul, Matrix.transpose_one,
    Fintype.card_fin, smul_eq_mul]
  module

end AxQM
