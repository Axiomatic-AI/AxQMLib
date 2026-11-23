/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FidelityPure
import AxQM.Postulates.API.HSOverlap
import AxQM.Postulates.API.BlochState
import AxQM.Concrete.BlochMatrixMulTrace
import ToMathlib.Analysis.InnerProductSpace.RankOneTrace

/-!
# AxQM.Postulates.API — pure-state fidelity via the Hilbert–Schmidt overlap, and the
Bloch overlap

Two facts that turn a **squared fidelity** into an algebraic Bloch
computation:

* `State.fidelity_toState_sq_eq_hsOverlap` — for a **pure** state `|ψ⟩` and any state `σ`, the
  squared fidelity is the Hilbert–Schmidt overlap `F(|ψ⟩, σ)² = tr(|ψ⟩⟨ψ| σ) = hsOverlap(|ψ⟩⟨ψ|,
  σ)`. This upgrades `State.fidelity_toState_sq` (`F² = ⟨ψ|σ|ψ⟩`) to the symmetric trace form,
  using `tr(|v⟩⟨v| ∘ A) = ⟨v, A v⟩` (`InnerProductSpace.trace_rankOne_self_comp`).
* `blochState_hsOverlap` — the Hilbert–Schmidt overlap of two qubit Bloch states is
  `hsOverlap(ρ_r, ρ_s) = (1 + r⃗·s⃗)/2`, the concrete trace identity `blochMatrix_mul_trace`
  transported across `Matrix.toEuclideanCLM`. It is the off-diagonal generalisation of
  `blochState_purity` (the `r = s` case, `(1 + ‖r⃗‖²)/2`).

Composing the two: for a pure Bloch state `|ψ_r⟩` (`‖r⃗‖ = 1`) and any Bloch state `ρ_s`,
`F(|ψ_r⟩, ρ_s)² = (1 + r⃗·s⃗)/2`. This is the workhorse behind the depolarizing-channel fidelity of
Nielsen & Chuang Exercise 10.12.

The notions involved are `State.fidelity`, `State.hsOverlap` and `blochState`.
-/

open Matrix

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The squared pure-state fidelity is the Hilbert–Schmidt overlap.** For a pure state `|ψ⟩` and
any state `σ`, `F(|ψ⟩, σ)² = tr(|ψ⟩⟨ψ| σ) = hsOverlap(|ψ⟩⟨ψ|, σ)`.

Proof: `State.fidelity_toState_sq` gives `F(|ψ⟩, σ)² = ⟨ψ| σ |ψ⟩`; and `hsOverlap(|ψ⟩⟨ψ|, σ) = re
tr(|ψ⟩⟨ψ| σ)` with `|ψ⟩⟨ψ| = ψ.toState.op` a rank-one projector (`PureState.toState_op`), so
`tr(|ψ⟩⟨ψ| ∘ σ) = ⟨ψ| σ |ψ⟩` by `InnerProductSpace.trace_rankOne_self_comp`. -/
theorem State.fidelity_toState_sq_eq_hsOverlap (ψ : PureState S) (σ : State S) :
    (ψ.toState.fidelity σ) ^ 2 = ψ.toState.hsOverlap σ := by
  rw [State.fidelity_toState_sq, State.hsOverlap, PureState.toState_op,
    ← InnerProductSpace.trace_rankOne_self_comp ψ.vec σ.op]
  rfl

/-- **The Hilbert–Schmidt overlap of two qubit Bloch states.** For Bloch vectors `r⃗, s⃗` in the
closed unit ball, `hsOverlap(ρ_r, ρ_s) = (1 + r⃗·s⃗)/2`, where `r⃗·s⃗ = r₀s₀ + r₁s₁ + r₂s₂`.

The two density operators are `Matrix.toEuclideanCLM` of `blochMatrix r`, `blochMatrix s`
(`blochState_op`); their product is `toEuclideanCLM` of the matrix product (`toEuclideanCLM` is a
`⋆`-algebra map), whose trace is `(1 + r⃗·s⃗)/2` (`Concrete.blochMatrix_mul_trace`), carried to the
operator trace by `Matrix.trace_toEuclideanCLM`. The diagonal `r⃗ = s⃗` case is
`blochState_purity`. -/
theorem blochState_hsOverlap (r s : Fin 3 → ℝ) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1)
    (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 ≤ 1) :
    (blochState r hr).hsOverlap (blochState s hs)
      = (1 + (r 0 * s 0 + r 1 * s 1 + r 2 * s 2)) / 2 := by
  have hop : (blochState r hr).op * (blochState s hs).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Concrete.blochMatrix r * Concrete.blochMatrix s) := by
    rw [blochState_op, blochState_op]
    exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) _ _).symm
  rw [State.hsOverlap, hop]
  change RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin 2))
      ↑(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
        (Concrete.blochMatrix r * Concrete.blochMatrix s)))
      = (1 + (r 0 * s 0 + r 1 * s 1 + r 2 * s 2)) / 2
  rw [Matrix.trace_toEuclideanCLM, Concrete.blochMatrix_mul_trace]
  simp [-Complex.ofReal_pow]

end AxQM
