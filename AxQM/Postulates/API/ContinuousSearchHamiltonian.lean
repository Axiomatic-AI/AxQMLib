/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ProjectorHamiltonian
import AxQM.Postulates.API.PureState
import ToMathlib.Analysis.Normed.Algebra.ExponentialEigenvector
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# AxQM.Postulates.API — the continuous-time search Hamiltonian

The Hamiltonian behind Nielsen & Chuang's **quantum-search-as-simulation**
picture (§6.2, and the multiple-solution generalisation of Exercise 6.11): the two-projector
Hamiltonian

`H = |a⟩⟨a| + |ψ⟩⟨ψ|`   (N&C eq. 6.18, `|a⟩` the target and `|ψ⟩` the starting state)

and the explicit continuous-time evolution it generates. This is the *abstract* engine — a pair of
pure states `a`, `ψ` with a **real overlap** `⟨a, ψ⟩ = α` — that both the single-solution search
of §6.2 (`a = |x⟩`, `α = 1/√N`) and the multiple-solution search of Exercise 6.11
(`a = |β⟩`, the uniform superposition over the `M` solutions, `α = √(M/N)`) instantiate.

## The mathematics (N&C eqs. 6.20–6.23)

Working with the real overlap `α = ⟨a, ψ⟩`, the vectors `a ± ψ` are eigenvectors of `H`:

`H (a + ψ) = (1 + α)(a + ψ)`,   `H (a - ψ) = (1 - α)(a - ψ)`

(the reality of `α` is exactly what makes `a ± ψ` eigenvectors). Since the propagator acts on an
eigenvector by a global phase (`Observable.propagator_op_apply_of_apply_eq_smul`), decomposing
`ψ = ½(a + ψ) - ½(a - ψ)` and re-collecting gives N&C eq. 6.23:

`exp(-i H t) |ψ⟩ = e^{-it} (cos(α t) |ψ⟩ - i sin(α t) |a⟩)`.

At `t = π/(2α)` this is `-i e^{-it} |a⟩`, i.e. the target `|a⟩` up to a global phase: the evolution
has rotated `|ψ⟩` exactly onto `|a⟩`, solving the search problem.

## What is formalised

* `Observable.propagator_op_apply_of_apply_eq_smul` — **energy eigenstate → phase**: if
  `H |v⟩ = μ |v⟩` then `exp(-iHt) |v⟩ = e^{-iμt} |v⟩`. A reusable fact about the propagator
  (built on the lemma `ContinuousLinearMap.exp_apply_of_apply_eq_smul`).
* `Observable.propagator_op_apply_of_two_state_eigen` / `evolvePure_toState_of_two_state_eigen` —
  the **operator-agnostic two-state rotation**: for *any* `H` with `H(a ± ψ) = (c ± d)(a ± ψ)`,
  `exp(-iHt)|ψ⟩ = e^{-ict}(cos(dt)|ψ⟩ - i sin(dt)|a⟩)`, reaching `|a⟩` (up to a global phase) at
  `t = π/(2d)` (for `d ≠ 0`). This is the shared core both this search Hamiltonian (`c=1, d=α`) and
  the Exercise 6.12 coupling Hamiltonian (`c=α, d=1`, in `Postulates/API/CouplingHamiltonian.lean`)
  instantiate — the `_propagator_op_apply` / `_reaches_target` below are one-line derivations of it.
* `PureState.searchHamiltonian a ψ` — the Hamiltonian `|a⟩⟨a| + |ψ⟩⟨ψ|` as an `Observable`
  (self-adjoint as a sum of two projector observables).
* `PureState.searchHamiltonian_apply_add` / `_apply_sub` — the eigenvector equations for `a ± ψ`.
* `PureState.searchHamiltonian_propagator_op_apply` — **N&C eq. 6.23**, the closed form of the
  evolved state `exp(-iHt) |ψ⟩`.
* `PureState.searchHamiltonian_reaches_target` — at `t = π/(2α)` (for `α > 0`) the evolved state
  equals the target `|a⟩` up to a global phase,
  `((H.propagator 1 0 (π/(2α))).evolvePure ψ).toState = a.toState`: the search problem is solved.

These definitions are used in `AxQM/NC/Ch6/Exercise6_11.lean`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **An energy eigenstate evolves by a global phase.** If `v` is an eigenvector of the Hamiltonian
`H` with (necessarily real, but here allowed complex) eigenvalue `μ` — `H.op v = μ • v` — then the
propagator acts on it by the scalar phase `e^{-iμt}`: `(H.propagator 1 0 t).op v = e^{-iμt} • v`.
The proof rewrites the propagator as `exp(t • -i • H.op)` (`Observable.propagator_op`), computes
`(t • -i • H.op) v = (-i μ t) • v`, and applies the lemma
`ContinuousLinearMap.exp_apply_of_apply_eq_smul`. -/
theorem Observable.propagator_op_apply_of_apply_eq_smul (H : Observable S) {v : S.space} {μ : ℂ}
    (t : ℝ) (h : H.op v = μ • v) :
    (H.propagator 1 0 t).op v = Complex.exp (-(Complex.I * (μ * (t : ℂ)))) • v := by
  rw [Observable.propagator_op]
  refine ContinuousLinearMap.exp_apply_of_apply_eq_smul _ v _ ?_
  rw [smul_apply, h, smul_smul]; push_cast; ring_nf

/-- **Two-state rotation — the propagator of any Hamiltonian whose `a ± ψ` are eigenvectors.** If a
Hamiltonian `H` has `H (a + ψ) = (c + d)(a + ψ)` and `H (a − ψ) = (c − d)(a − ψ)` — i.e. `a ± ψ`
are eigenvectors with eigenvalues `c ± d` — then it rotates the start `ψ` as

`exp(−i H t) |ψ⟩ = e^{−ict} (cos(dt) · |ψ⟩ − i sin(dt) · |a⟩)`.

This is the **operator-agnostic core** of the continuous-time search evolutions, shared by every
Hamiltonian of the `c ± d` eigenvalue shape: the §6.2 projector Hamiltonian `|a⟩⟨a| + |ψ⟩⟨ψ|` has
`(c, d) = (1, α)` (`searchHamiltonian_propagator_op_apply`), and the off-diagonal coupling
`|a⟩⟨ψ| + |ψ⟩⟨a|` of Exercise 6.12 has `(c, d) = (α, 1)` (`couplingHamiltonian_propagator_op_apply`)
— the same closed form, differing only in which of `1`, `α` is the phase rate `c` and which is the
rotation rate `d`. The proof decomposes `ψ = ½(a + ψ) − ½(a − ψ)`, evolves each eigenvector by its
phase (`propagator_op_apply_of_apply_eq_smul`, eigenvalues `c ± d`), and re-collects the `a` and `ψ`
components using `e^{−i(c±d)t} = e^{−ict} e^{∓idt}` and Euler's formula. -/
theorem Observable.propagator_op_apply_of_two_state_eigen (H : Observable S) (a ψ : PureState S)
    {c d : ℝ} (t : ℝ)
    (hadd : H.op (a.vec + ψ.vec) = ((c + d : ℝ) : ℂ) • (a.vec + ψ.vec))
    (hsub : H.op (a.vec - ψ.vec) = ((c - d : ℝ) : ℂ) • (a.vec - ψ.vec)) :
    (H.propagator 1 0 t).op ψ.vec
      = Complex.exp (-(Complex.I * ((c * t : ℝ) : ℂ)))
        • ((Real.cos (d * t) : ℂ) • ψ.vec - (Complex.I * (Real.sin (d * t) : ℂ)) • a.vec) := by
  have ep := H.propagator_op_apply_of_apply_eq_smul t hadd
  have em := H.propagator_op_apply_of_apply_eq_smul t hsub
  have hψ : ψ.vec = (1 / 2 : ℂ) • (a.vec + ψ.vec) - (1 / 2 : ℂ) • (a.vec - ψ.vec) := by module
  -- split each eigenvalue phase `e^{-i(c±d)t}` as `e^{-ict}·e^{∓idt}` (shared by `hcP`/`hcA`)
  have e1 : -(Complex.I * (((c + d : ℝ) : ℂ) * (t : ℂ)))
      = -(Complex.I * ((c * t : ℝ) : ℂ)) + (-((d * t : ℝ) : ℂ)) * Complex.I := by push_cast; ring
  have e2 : -(Complex.I * (((c - d : ℝ) : ℂ) * (t : ℂ)))
      = -(Complex.I * ((c * t : ℝ) : ℂ)) + (((d * t : ℝ) : ℂ)) * Complex.I := by push_cast; ring
  have hcP : (1 / 2 : ℂ) * Complex.exp (-(Complex.I * (((c + d : ℝ) : ℂ) * (t : ℂ))))
        + (1 / 2) * Complex.exp (-(Complex.I * (((c - d : ℝ) : ℂ) * (t : ℂ))))
      = Complex.exp (-(Complex.I * ((c * t : ℝ) : ℂ))) * (Real.cos (d * t) : ℂ) := by
    rw [e1, e2, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]; ring
  have hcA : (1 / 2 : ℂ) * Complex.exp (-(Complex.I * (((c + d : ℝ) : ℂ) * (t : ℂ))))
        - (1 / 2) * Complex.exp (-(Complex.I * (((c - d : ℝ) : ℂ) * (t : ℂ))))
      = -(Complex.exp (-(Complex.I * ((c * t : ℝ) : ℂ)))
          * (Complex.I * (Real.sin (d * t) : ℂ))) := by
    rw [e1, e2, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg, Complex.ofReal_sin]; ring
  conv_lhs => rw [hψ]
  rw [map_sub, map_smul, map_smul, ep, em]
  match_scalars
  · linear_combination (norm := (push_cast; ring1)) hcA
  · linear_combination (norm := (push_cast; ring1)) hcP

/-- **Two-state rotation reaches the target at `t = π/(2d)`.** Under the hypotheses of
`propagator_op_apply_of_two_state_eigen` (so `a ± ψ` are eigenvectors with eigenvalues `c ± d`)
together with `d ≠ 0`, evolving `ψ` for time `t = π/(2d)` produces the target `a` up to a global
phase — the density operators coincide,
`((H.propagator 1 0 (π/(2d))).evolvePure ψ).toState = a.toState`. At `t = π/(2d)` we have
`d t = π/2`, so `cos(d t) = 0`, `sin(d t) = 1` and the evolved vector is `−i e^{−icπ/(2d)} |a⟩`, a
unit-modulus phase times `|a⟩`; a global phase is invisible to the state
(`toState_eq_of_vec_eq_smul`). The observation time is set by the rotation rate `d` alone (the phase
rate `c` only feeds the invisible global phase) — for the projector search `(c, d) = (1, α)` this is
`t = π/(2α) = O(√N)`, whereas for the coupling Hamiltonian `(c, d) = (α, 1)` it is
`t = π/2 = O(1)`. -/
theorem Observable.evolvePure_toState_of_two_state_eigen (H : Observable S) (a ψ : PureState S)
    {c d : ℝ} (hd : d ≠ 0)
    (hadd : H.op (a.vec + ψ.vec) = ((c + d : ℝ) : ℂ) • (a.vec + ψ.vec))
    (hsub : H.op (a.vec - ψ.vec) = ((c - d : ℝ) : ℂ) • (a.vec - ψ.vec)) :
    ((H.propagator 1 0 (Real.pi / (2 * d))).evolvePure ψ).toState = a.toState := by
  have hdt : d * (Real.pi / (2 * d)) = Real.pi / 2 := by field_simp
  have hvec : (H.propagator 1 0 (Real.pi / (2 * d))).op ψ.vec
      = (-(Complex.exp (-(Complex.I * ((c * (Real.pi / (2 * d)) : ℝ) : ℂ))) * Complex.I))
        • a.vec := by
    rw [H.propagator_op_apply_of_two_state_eigen a ψ _ hadd hsub, hdt]
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ofReal_zero, Complex.ofReal_one,
      zero_smul, zero_sub, mul_one, smul_neg, smul_smul, neg_smul]
  refine PureState.toState_eq_of_vec_eq_smul
    (c := -(Complex.exp (-(Complex.I * ((c * (Real.pi / (2 * d)) : ℝ) : ℂ))) * Complex.I)) ?_ ?_
  · rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_exp]
    have hre : (-(Complex.I * ((c * (Real.pi / (2 * d)) : ℝ) : ℂ))).re = 0 := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, neg_zero]
    rw [hre, Real.exp_zero]
  · rw [Evolution.evolvePure_vec]; exact hvec

/-- **The continuous-time search Hamiltonian** `H = |a⟩⟨a| + |ψ⟩⟨ψ|` (Nielsen & Chuang eq. 6.18)
of a target pure state `a` and a starting pure state `ψ`, as an `Observable`. It is the sum of the
two projector Hamiltonians `a.projObservable` and `ψ.projObservable`, hence self-adjoint. Evolving
`ψ` under `H` rotates it towards `a` (`searchHamiltonian_propagator_op_apply`); this is the
Hamiltonian whose simulation reproduces the quantum search algorithm. -/
def PureState.searchHamiltonian (a ψ : PureState S) : Observable S where
  op := a.projObservable.op + ψ.projObservable.op
  selfAdjoint := a.projObservable.selfAdjoint.add ψ.projObservable.selfAdjoint

/-- The action of the search Hamiltonian `H = |a⟩⟨a| + |ψ⟩⟨ψ|` on a vector `v`:
`H v = ⟨a, v⟩ |a⟩ + ⟨ψ, v⟩ |ψ⟩`. -/
theorem PureState.searchHamiltonian_op_apply (a ψ : PureState S) (v : S.space) :
    (a.searchHamiltonian ψ).op v
      = (inner ℂ a.vec v) • a.vec + (inner ℂ ψ.vec v) • ψ.vec := by
  simp only [PureState.searchHamiltonian, add_apply,
    PureState.projObservable_op, rankOne_apply]

/-- **The action of the search Hamiltonian on the target `|a⟩`.** For pure states `a`, `ψ` with
real overlap `⟨a, ψ⟩ = α`, `H |a⟩ = |a⟩ + α |ψ⟩` (using `⟨a, a⟩ = 1` and the Hermitian symmetry
`⟨ψ, a⟩ = conj⟨a, ψ⟩ = α`, which uses the reality of `α`). -/
theorem PureState.searchHamiltonian_apply_left (a ψ : PureState S) {α : ℝ}
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (a.searchHamiltonian ψ).op a.vec = a.vec + (α : ℂ) • ψ.vec := by
  have hpa : inner ℂ ψ.vec a.vec = (α : ℂ) := by rw [← inner_conj_symm, h, Complex.conj_ofReal]
  rw [PureState.searchHamiltonian_op_apply, a.inner_self, hpa, one_smul]

/-- **The action of the search Hamiltonian on the start `|ψ⟩`.** For pure states `a`, `ψ` with real
overlap `⟨a, ψ⟩ = α`, `H |ψ⟩ = α |a⟩ + |ψ⟩` (using `⟨a, ψ⟩ = α` and `⟨ψ, ψ⟩ = 1`). -/
theorem PureState.searchHamiltonian_apply_right (a ψ : PureState S) {α : ℝ}
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (a.searchHamiltonian ψ).op ψ.vec = (α : ℂ) • a.vec + ψ.vec := by
  rw [PureState.searchHamiltonian_op_apply, h, ψ.inner_self, one_smul]

/-- **The `(1 + α)`-eigenvector of the search Hamiltonian.** For pure states `a`, `ψ` with real
overlap `⟨a, ψ⟩ = α`, the vector `a + ψ` is an eigenvector of `H = |a⟩⟨a| + |ψ⟩⟨ψ|` with
eigenvalue `1 + α`: `H (a + ψ) = (1 + α)(a + ψ)`. (Reality of `α` — via `⟨ψ, a⟩ = conj⟨a, ψ⟩ = α`
— is what makes this an eigenvector.) -/
theorem PureState.searchHamiltonian_apply_add (a ψ : PureState S) {α : ℝ}
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (a.searchHamiltonian ψ).op (a.vec + ψ.vec) = ((1 + α : ℝ) : ℂ) • (a.vec + ψ.vec) := by
  rw [map_add, a.searchHamiltonian_apply_left ψ h, a.searchHamiltonian_apply_right ψ h]
  push_cast; module

/-- **The `(1 - α)`-eigenvector of the search Hamiltonian.** For pure states `a`, `ψ` with real
overlap `⟨a, ψ⟩ = α`, the vector `a - ψ` is an eigenvector of `H = |a⟩⟨a| + |ψ⟩⟨ψ|` with
eigenvalue `1 - α`: `H (a - ψ) = (1 - α)(a - ψ)`. -/
theorem PureState.searchHamiltonian_apply_sub (a ψ : PureState S) {α : ℝ}
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (a.searchHamiltonian ψ).op (a.vec - ψ.vec) = ((1 - α : ℝ) : ℂ) • (a.vec - ψ.vec) := by
  rw [map_sub, a.searchHamiltonian_apply_left ψ h, a.searchHamiltonian_apply_right ψ h]
  push_cast; module

/-- **Nielsen & Chuang eq. 6.23 — the continuous-time search evolution.** For pure states `a`, `ψ`
with real overlap `⟨a, ψ⟩ = α`, the state evolved under `H = |a⟩⟨a| + |ψ⟩⟨ψ|` for time `t` is

`exp(-i H t) |ψ⟩ = e^{-it} (cos(α t) |ψ⟩ - i sin(α t) |a⟩)`.

This is the two-state rotation `propagator_op_apply_of_two_state_eigen` at `(c, d) = (1, α)`: the
eigenvectors `a ± ψ` have eigenvalues `1 ± α` (`searchHamiltonian_apply_add` / `_apply_sub`), so the
phase rate is `c = 1` and the rotation rate is `d = α`. -/
theorem PureState.searchHamiltonian_propagator_op_apply (a ψ : PureState S) {α : ℝ} (t : ℝ)
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    ((a.searchHamiltonian ψ).propagator 1 0 t).op ψ.vec
      = Complex.exp (-(Complex.I * (t : ℂ)))
        • ((Real.cos (α * t) : ℂ) • ψ.vec - (Complex.I * (Real.sin (α * t) : ℂ)) • a.vec) := by
  have := (a.searchHamiltonian ψ).propagator_op_apply_of_two_state_eigen a ψ (c := 1) (d := α) t
    (a.searchHamiltonian_apply_add ψ h) (a.searchHamiltonian_apply_sub ψ h)
  simpa only [one_mul] using this

/-- **The search Hamiltonian solves the search problem (N&C §6.2, eqs. 6.23–6.24).** For pure
states `a`, `ψ` with real, positive overlap `⟨a, ψ⟩ = α > 0`, evolving `ψ` under
`H = |a⟩⟨a| + |ψ⟩⟨ψ|` for time `t = π/(2α)` produces the target state `a` up to a global phase —
the density operators coincide:
`((H.propagator 1 0 (π/(2α))).evolvePure ψ).toState = a.toState`. This is the two-state landing
`evolvePure_toState_of_two_state_eigen` at `(c, d) = (1, α)` (rotation rate `d = α`, so the
observation time is `π/(2α)`): at `t = π/(2α)`, `cos(α t) = 0` and `sin(α t) = 1`, giving
`-i e^{-it} |a⟩`, a unit-modulus phase times `|a⟩` (invisible to the state,
`PureState.toState_eq_of_vec_eq_smul`). For the single-solution search `α = 1/√N`, this is the
observation time `t = π√N/2`. -/
theorem PureState.searchHamiltonian_reaches_target (a ψ : PureState S) {α : ℝ} (hα : 0 < α)
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (((a.searchHamiltonian ψ).propagator 1 0 (Real.pi / (2 * α))).evolvePure ψ).toState
      = a.toState :=
  (a.searchHamiltonian ψ).evolvePure_toState_of_two_state_eigen a ψ (c := 1) (d := α)
    (ne_of_gt hα) (a.searchHamiltonian_apply_add ψ h) (a.searchHamiltonian_apply_sub ψ h)

end AxQM
