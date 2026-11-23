/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Concrete: the amplitude-damping master equation and its operator-sum solution (N&C Problem 8.1)

This file works, at the level of `2 × 2` complex matrices, through the steps of Nielsen & Chuang,
*Quantum Computation and Quantum Information*, **Problem 8.1** (p. 395). The problem asks to solve
the single-qubit Lindblad (master) equation for spontaneous emission — the interaction-picture
amplitude-damping equation of §8.4.1 —

`ρ̇ = -(λ/2) (σ₊σ₋ ρ + ρ σ₊σ₋ - 2 σ₋ ρ σ₊)`   (N&C eq. 8.188)

for `ρ(t)`, and to express the resulting map `ρ(0) ↦ ρ(t)` in the operator-sum (Kraus) form
`ρ(t) = Σₖ Eₖ(t) ρ(0) Eₖ(t)†`.

Here `σ₋ = |0⟩⟨1|` is the atomic lowering operator and `σ₊ = σ₋† = |1⟩⟨0|` the raising operator
(N&C §8.4.1). Writing `ρ` in the computational basis, the equation decouples into four scalar
ordinary differential equations whose solution is

`ρ(t) = !![ρ₀₀ + (1 - e^{-λt}) ρ₁₁,   e^{-λt/2} ρ₀₁;   e^{-λt/2} ρ₁₀,   e^{-λt} ρ₁₁]`,

which is exactly the amplitude-damping channel with damping parameter `γ = 1 - e^{-λt}` and
operation elements `E₀ = diag(1, √(1-γ)) = diag(1, e^{-λt/2})` and `E₁ = √γ |0⟩⟨1|`
(N&C eqs. 8.145–8.146, matching the §8.3.5 amplitude-damping channel).

## Contents

* `sigmaMinus`, `sigmaPlus` — the atomic lowering / raising operators `|0⟩⟨1|`, `|1⟩⟨0|`, with
  `sigmaPlus_eq_conjTranspose_sigmaMinus` recording `σ₊ = σ₋†`.
* `lindbladGenerator lam ρ` — the right-hand side of (8.188), the Lindblad generator; its closed
  form is `lindbladGenerator_eq`.
* `dampedRho lam t ρ₀` — the claimed solution `ρ(t)`, with `dampedRho_zero` the initial condition
  `ρ(0) = ρ₀`.
* `dampedRho_hasDerivAt` — `ρ(t)` **solves** the master equation: entrywise,
  `d/dt ρ(t) = lindbladGenerator lam (ρ(t))`.
* `krausAmplitudeDampingZero`, `krausAmplitudeDampingOne` — the operation elements `E₀(t)`, `E₁(t)`.
* `dampedRho_eq_kraus` — the operator-sum representation
  `ρ(t) = E₀(t) ρ(0) E₀(t)† + E₁(t) ρ(0) E₁(t)†` (for `0 ≤ λ`, `0 ≤ t`, so the damping parameter
  `γ = 1 - e^{-λt} ∈ [0, 1]` and its square root is genuine).
* `krausAmplitudeDamping_completeness` — the trace-preservation / completeness relation
  `E₀† E₀ + E₁† E₁ = I`, certifying the map is a genuine (trace-preserving) quantum operation.

The map `ρ(0) ↦ ρ(t)` is *not* unitary, so it is not an instance of the closed-system `Evolution`;
the general operator-sum / quantum-operation formalism (N&C Theorem 8.1) is not yet in the library,
so this concrete instance is stated and solved directly at the matrix level.

## Design notes

* `λ` and `t` are kept as separate real parameters (`lam t : ℝ`) rather than folded into a single
  `γ`, so that the differential equation `dampedRho_hasDerivAt` — the "solve the ODE" half of the
  problem — can be stated with `t` as the differentiation variable. The ODE-solution result holds
  for *all* real `λ, t`; only the operator-sum decomposition needs `0 ≤ λ, 0 ≤ t` (so that
  `γ = 1 - e^{-λt} ≥ 0` and `√γ` is a genuine square root), matching N&C's physical regime of a
  nonnegative emission rate `λ` and forward time `t`.
* Matrix identities are proved entrywise via `Matrix.ext_iff` + `Fin.forall_fin_two` (which yields
  literal indices `0, 1`), expanding products with `Matrix.mul_apply`; the nonlinear facts
  `(e^{-λt/2})² = e^{-λt}` and `(√γ)² = γ` are folded into the closed forms before the pure-`ring`
  matrix computation, so the algebraic content is isolated from the matrix bookkeeping.
-/

open Matrix Complex

noncomputable section

namespace AxQM.Concrete

/-- The atomic **lowering operator** `σ₋ = |0⟩⟨1| = !![0, 1; 0, 0]` (N&C §8.4.1): it sends the
excited state `|1⟩` to the ground state `|0⟩`. -/
def sigmaMinus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The atomic **raising operator** `σ₊ = |1⟩⟨0| = !![0, 0; 1, 0]` (N&C §8.4.1), the adjoint of the
lowering operator (`sigmaPlus_eq_conjTranspose_sigmaMinus`). -/
def sigmaPlus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The raising operator is the adjoint of the lowering operator: `σ₊ = σ₋†` (N&C: `σ₊ ≡ σ₋†`). -/
theorem sigmaPlus_eq_conjTranspose_sigmaMinus : sigmaPlus = sigmaMinusᴴ := by
  rw [← Matrix.ext_iff]
  simp [Fin.forall_fin_two, sigmaPlus, sigmaMinus, Matrix.conjTranspose_apply]

/-- The **Lindblad generator** of (8.188): the right-hand side
`-(λ/2) (σ₊σ₋ ρ + ρ σ₊σ₋ - 2 σ₋ ρ σ₊)` of the interaction-picture amplitude-damping master
equation, as a function of the density matrix `ρ`. -/
def lindbladGenerator (lam : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -((lam : ℂ) / 2) • (sigmaPlus * sigmaMinus * ρ + ρ * (sigmaPlus * sigmaMinus)
    - (2 : ℂ) • (sigmaMinus * ρ * sigmaPlus))

/-- Closed form of the Lindblad generator: expanding the products `σ₊σ₋ = |1⟩⟨1|` and
`σ₋ ρ σ₊` shows `-(λ/2)(σ₊σ₋ρ + ρσ₊σ₋ - 2σ₋ρσ₊)` decouples entrywise into
`!![λ ρ₁₁, -(λ/2) ρ₀₁; -(λ/2) ρ₁₀, -λ ρ₁₁]` — the diagonal population `ρ₁₁` decays at rate `λ`,
feeding `ρ₀₀`, and the coherences `ρ₀₁, ρ₁₀` decay at rate `λ/2`. -/
theorem lindbladGenerator_eq (lam : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    lindbladGenerator lam ρ =
      !![(lam : ℂ) * ρ 1 1, -((lam : ℂ) / 2) * ρ 0 1;
         -((lam : ℂ) / 2) * ρ 1 0, -(lam : ℂ) * ρ 1 1] := by
  rw [lindbladGenerator, sigmaMinus, sigmaPlus, Matrix.eta_fin_two ρ]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring

/-- The claimed solution `ρ(t)` of the master equation (8.188) with initial condition `ρ₀`: the
amplitude-damped density matrix
`!![ρ₀₀ + (1 - e^{-λt}) ρ₁₁, e^{-λt/2} ρ₀₁; e^{-λt/2} ρ₁₀, e^{-λt} ρ₁₁]`. -/
def dampedRho (lam t : ℝ) (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ρ₀ 0 0 + (1 - (Real.exp (-(lam * t)) : ℂ)) * ρ₀ 1 1, (Real.exp (-(lam * t) / 2) : ℂ) * ρ₀ 0 1;
     (Real.exp (-(lam * t) / 2) : ℂ) * ρ₀ 1 0, (Real.exp (-(lam * t)) : ℂ) * ρ₀ 1 1]

/-- **Initial condition:** at `t = 0` the solution is the initial state, `ρ(0) = ρ₀`
(`e^0 = 1`, so the damping factors are `1` and the extra `(1 - e^0) ρ₁₁` term vanishes). -/
theorem dampedRho_zero (lam : ℝ) (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) : dampedRho lam 0 ρ₀ = ρ₀ := by
  rw [← Matrix.ext_iff]
  simp [Fin.forall_fin_two, dampedRho]

/-- **The damped density matrix solves the master equation.** For every entry `(i, j)`, the time
derivative of `ρ(t)ᵢⱼ` equals the corresponding entry of the Lindblad generator applied to `ρ(t)`,
i.e. `d/dt ρ(t) = lindbladGenerator λ (ρ(t))` (N&C eq. 8.188). This is the "explicitly work through
the steps to solve the differential equation" half of Problem 8.1. -/
theorem dampedRho_hasDerivAt (lam t : ℝ) (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    HasDerivAt (fun s => dampedRho lam s ρ₀ i j)
      (lindbladGenerator lam (dampedRho lam t ρ₀) i j) t := by
  have hexp : HasDerivAt (fun s : ℝ => (Real.exp (-(lam * s)) : ℂ))
      (-(lam : ℂ) * Real.exp (-(lam * t))) t := by
    have h : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t := by
      have h' := (hasDerivAt_id t).const_mul (-lam)
      simpa [neg_mul] using h'
    have h2 := ((Real.hasDerivAt_exp (-(lam * t))).comp t h).ofReal_comp
    convert h2 using 1
    · simp
    · push_cast; ring
  have hexp2 : HasDerivAt (fun s : ℝ => (Real.exp (-(lam * s) / 2) : ℂ))
      (-(lam : ℂ) / 2 * Real.exp (-(lam * t) / 2)) t := by
    have h : HasDerivAt (fun s : ℝ => -(lam * s) / 2) (-lam / 2) t := by
      have h' := (hasDerivAt_id t).const_mul (-lam / 2)
      have heq : (fun s : ℝ => -(lam * s) / 2) = fun s : ℝ => (-lam / 2) * s := by
        funext s; ring
      rw [heq]
      simpa using h'
    have h2 := (HasDerivAt.comp (h₂ := Real.exp) t (Real.hasDerivAt_exp _) h).ofReal_comp
    convert h2 using 1
    · simp
    · push_cast; ring
  rw [lindbladGenerator_eq]
  fin_cases i <;> fin_cases j
  · -- (0, 0): `ρ₀₀ + (1 - e^{-λt}) ρ₁₁`, derivative `λ e^{-λt} ρ₁₁`
    change HasDerivAt (fun s => ρ₀ 0 0 + (1 - (Real.exp (-(lam * s)) : ℂ)) * ρ₀ 1 1)
      ((lam : ℂ) * ((Real.exp (-(lam * t)) : ℂ) * ρ₀ 1 1)) t
    convert (((hasDerivAt_const t (1 : ℂ)).sub hexp).mul_const (ρ₀ 1 1)).const_add (ρ₀ 0 0) using 1
    ring
  · -- (0, 1): `e^{-λt/2} ρ₀₁`, derivative `-(λ/2) e^{-λt/2} ρ₀₁`
    change HasDerivAt (fun s => (Real.exp (-(lam * s) / 2) : ℂ) * ρ₀ 0 1)
      (-((lam : ℂ) / 2) * ((Real.exp (-(lam * t) / 2) : ℂ) * ρ₀ 0 1)) t
    convert hexp2.mul_const (ρ₀ 0 1) using 1
    ring
  · -- (1, 0): `e^{-λt/2} ρ₁₀`
    change HasDerivAt (fun s => (Real.exp (-(lam * s) / 2) : ℂ) * ρ₀ 1 0)
      (-((lam : ℂ) / 2) * ((Real.exp (-(lam * t) / 2) : ℂ) * ρ₀ 1 0)) t
    convert hexp2.mul_const (ρ₀ 1 0) using 1
    ring
  · -- (1, 1): `e^{-λt} ρ₁₁`, derivative `-λ e^{-λt} ρ₁₁`
    change HasDerivAt (fun s => (Real.exp (-(lam * s)) : ℂ) * ρ₀ 1 1)
      (-(lam : ℂ) * ((Real.exp (-(lam * t)) : ℂ) * ρ₀ 1 1)) t
    convert hexp.mul_const (ρ₀ 1 1) using 1
    ring

/-- The **first operation element** `E₀(t) = diag(1, e^{-λt/2}) = diag(1, √(1-γ))` of the
amplitude-damping channel (N&C eq. 8.145), where `γ = 1 - e^{-λt}`. It leaves `|0⟩` unchanged and
shrinks the `|1⟩` amplitude, representing "no decay occurred". -/
def krausAmplitudeDampingZero (lam t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, (Real.exp (-(lam * t) / 2) : ℂ)]

/-- The **second operation element** `E₁(t) = √γ |0⟩⟨1|` of the amplitude-damping channel
(N&C eq. 8.146), where `γ = 1 - e^{-λt}`. It maps `|1⟩` to `|0⟩`, representing "a decay
(spontaneous emission) occurred". -/
def krausAmplitudeDampingOne (lam t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (Real.sqrt (1 - Real.exp (-(lam * t))) : ℂ); 0, 0]

/-! ### Shared scalar facts about the damping parameter `γ = 1 - e^{-λt}`

The two square identities `(√γ)² = γ` and `e^{-λt} = (e^{-λt/2})²` (cast to `ℂ`) are the only
nonlinear inputs to both the operator-sum representation and the completeness relation below; they
are proved here once so each theorem can cite them rather than re-derive them inline. -/

/-- The damping parameter `γ = 1 - e^{-λt}` is nonnegative for `0 ≤ λ`, `0 ≤ t`. -/
theorem one_sub_exp_neg_nonneg {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    (0 : ℝ) ≤ 1 - Real.exp (-(lam * t)) := by
  have : Real.exp (-(lam * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hlam ht])
  linarith

/-- `e^{-λt} = (e^{-λt/2})²`, cast to `ℂ`. -/
theorem ofReal_exp_neg_eq_sq (lam t : ℝ) :
    (Real.exp (-(lam * t)) : ℂ)
      = (Real.exp (-(lam * t) / 2) : ℂ) * (Real.exp (-(lam * t) / 2) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.exp_add,
    show -(lam * t) / 2 + -(lam * t) / 2 = -(lam * t) from by ring]

/-- `(√γ)² = γ` for the nonnegative damping parameter `γ = 1 - e^{-λt}`, cast to `ℂ`. -/
theorem sq_ofReal_sqrt_one_sub_exp_neg {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    (Real.sqrt (1 - Real.exp (-(lam * t))) : ℂ)
        * (Real.sqrt (1 - Real.exp (-(lam * t))) : ℂ)
      = (1 : ℂ) - (Real.exp (-(lam * t)) : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (one_sub_exp_neg_nonneg hlam ht)]; push_cast; ring

/-- **Operator-sum (Kraus) representation** of the amplitude-damping map, N&C Problem 8.1: the
solution `ρ(t)` of the master equation is
`ρ(t) = E₀(t) ρ(0) E₀(t)† + E₁(t) ρ(0) E₁(t)†`.
The hypotheses `0 ≤ λ`, `0 ≤ t` ensure the damping parameter `γ = 1 - e^{-λt}` lies in `[0, 1]`, so
that `√γ` — the entry of `E₁` — squares back to `γ`. -/
theorem dampedRho_eq_kraus (lam t : ℝ) (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    dampedRho lam t ρ₀ =
      krausAmplitudeDampingZero lam t * ρ₀ * (krausAmplitudeDampingZero lam t)ᴴ
        + krausAmplitudeDampingOne lam t * ρ₀ * (krausAmplitudeDampingOne lam t)ᴴ := by
  -- `γ = 1 - e^{-λt} = (√γ)²` and `e^{-λt} = (e^{-λt/2})²`, cast to `ℂ` (shared scalar facts).
  have hsqC := (sq_ofReal_sqrt_one_sub_exp_neg hlam ht).symm
  have hexpC := ofReal_exp_neg_eq_sq lam t
  -- Pure matrix computation with opaque real entries `c = e^{-λt/2}`, `s = √γ`.
  have aux : ∀ (c s : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ),
      !![1, 0; 0, (c : ℂ)] * ρ * (!![1, 0; 0, (c : ℂ)])ᴴ
        + !![0, (s : ℂ); 0, 0] * ρ * (!![0, (s : ℂ); 0, 0])ᴴ
        = !![ρ 0 0 + (s : ℂ) * s * ρ 1 1, (c : ℂ) * ρ 0 1;
             (c : ℂ) * ρ 1 0, (c : ℂ) * c * ρ 1 1] := by
    intro c s ρ
    rw [← Matrix.ext_iff]
    simp only [Fin.forall_fin_two, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      RCLike.star_def, map_one, map_zero, Complex.conj_ofReal]
    and_intros <;> ring
  rw [krausAmplitudeDampingZero, krausAmplitudeDampingOne, dampedRho, hsqC, hexpC]
  exact (aux (Real.exp (-(lam * t) / 2)) (Real.sqrt (1 - Real.exp (-(lam * t)))) ρ₀).symm

/-- **Completeness / trace preservation** (N&C eq. 8.147 context): the operation elements satisfy
`E₀(t)† E₀(t) + E₁(t)† E₁(t) = I`, so the amplitude-damping map is trace-preserving — a genuine
quantum operation. Needs `0 ≤ λ`, `0 ≤ t` so that `(√(1-e^{-λt}))² = 1 - e^{-λt}`. -/
theorem krausAmplitudeDamping_completeness (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    (krausAmplitudeDampingZero lam t)ᴴ * krausAmplitudeDampingZero lam t
      + (krausAmplitudeDampingOne lam t)ᴴ * krausAmplitudeDampingOne lam t = 1 := by
  -- Shared scalar facts (see above): `(√γ)² = γ` and `(e^{-λt/2})² = e^{-λt}`, cast to `ℂ`.
  have hsqC := sq_ofReal_sqrt_one_sub_exp_neg hlam ht
  have hexpC := (ofReal_exp_neg_eq_sq lam t).symm
  have aux : ∀ (c s : ℝ),
      (!![1, 0; 0, (c : ℂ)])ᴴ * !![1, 0; 0, (c : ℂ)]
        + (!![0, (s : ℂ); 0, 0])ᴴ * !![0, (s : ℂ); 0, 0]
        = !![1, 0; 0, (c : ℂ) * c + (s : ℂ) * s] := by
    intro c s
    rw [← Matrix.ext_iff]
    simp only [Fin.forall_fin_two, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      RCLike.star_def, map_one, map_zero, Complex.conj_ofReal]
    and_intros <;> ring
  rw [krausAmplitudeDampingZero, krausAmplitudeDampingOne,
    aux (Real.exp (-(lam * t) / 2)) (Real.sqrt (1 - Real.exp (-(lam * t)))),
    show (Real.exp (-(lam * t) / 2) : ℂ) * (Real.exp (-(lam * t) / 2) : ℂ)
        + (Real.sqrt (1 - Real.exp (-(lam * t))) : ℂ) * (Real.sqrt (1 - Real.exp (-(lam * t))) : ℂ)
        = 1 from by rw [hsqC, hexpC]; ring]
  exact Matrix.one_fin_two.symm

end AxQM.Concrete

end
