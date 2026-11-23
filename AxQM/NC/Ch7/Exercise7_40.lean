/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DipolarRefocusing

/-!
# Nielsen & Chuang, Exercise 7.40 (Refocusing dipolar interactions)

Refocusing dipolar interactions: give a pulse sequence turning dipolar coupling H^D_{1,2} into the
form (7.138).

(N&C §7.7.3, p. 332.) The through-space dipolar coupling of two spin-½ nuclei is (eq. 7.136)

`H^D_{1,2}(n̂) = (γ₁ γ₂ ℏ / 4r³) · [ σ⃗₁·σ⃗₂ − 3 (σ⃗₁·n̂)(σ⃗₂·n̂) ]`,

and the target (7.138) is the weak-coupling / secular Ising form `H^J_{12} ≈ (ℏ J / 4) · Z₁Z₂`.

**Answer.** Refocus with the two `180°` `ẑ`-rotation pulses `R²_{z1}`, `R²_{z2}` (eq. 7.149 read
with `ẑ` in place of `x̂`). Each is the propagator `exp(−iπZ/2) = −iZ`, so — exactly as in the
refocusing identity (7.150), where the two `−i` global phases cancel — conjugating by the pulse
equals
conjugating by the Pauli `Z`. Interleaving the free dipolar evolution with these pulses realises the
four toggling frames `{I⊗I, Z⊗I, I⊗Z, Z⊗Z}` (the `Z`-type Pauli group), and the zeroth-order
average (toggling-frame) Hamiltonian is the symmetric average
`H ↦ ¼(H + Z₁HZ₁ + Z₂HZ₂ + Z₁Z₂HZ₁Z₂)`. This projects onto the `Z`-diagonal Paulis — a term
survives iff it commutes with both `Z₁` and `Z₂` — so of the nine coupling terms `∑_{a,b} D_{ab}
σ^a₁σ^b₂` only `Z₁Z₂` remains, leaving `(ℏ J_eff / 4) Z₁Z₂` with `J_eff = γ₁γ₂(1−3n_z²)/r³` — the
form of (7.138), the residual coupling being the secular dipolar constant `∝ (1 − 3 cos²θ)`.

The content is a statement about `4 × 4` complex matrices: the dipolar Hamiltonian
`Concrete.dipolarCoupling` (Exercise 7.35), conjugation by the Pauli-`Z` refocusing pulses, and
their average. Compare `AxQM/Concrete/DipolarCoupling.lean` (Exercise 7.35) and
`AxQM/Concrete/Refocusing.lean` (Exercise 7.38).

## The formalisation

In `AxQM/Concrete/DipolarRefocusing.lean` (namespace `AxQM.Concrete`):

* `diagPart A = ½(A + Z A Z)` — the single-spin `Z`-diagonal part (average over `{I, Z}`), with
  `diagPart_pauliX`/`_pauliY` (`= 0`), `diagPart_pauliZ` (`= Z`) and `diagPart_pauliDot`
  (`diagPart (n·σ) = n_z • Z`).
* `refocusZ₁ = Z⊗I`, `refocusZ₂ = I⊗Z`, `refocusZ₁₂ = Z⊗Z` — the `ẑ`-refocusing pulses, with
  `refocusZ₁_mul_refocusZ₂` certifying `Z⊗Z` is their product.
* `zRefocusAverage H = ¼(H + Z₁HZ₁ + Z₂HZ₂ + Z₁Z₂HZ₁Z₂)` — the toggling-frame average, ℂ-linear
  (`zRefocusAverage_add`/`_smul`/`_sub`) with the structural identity `zRefocusAverage (A⊗B) =
  diagPart A ⊗ diagPart B` (`zRefocusAverage_kronecker`).
* `zRefocusAverage_spinSpinCoupling` (`= Z⊗Z`), `zRefocusAverage_spinDirProduct`
  (`= n_z² • (Z⊗Z)`), `zRefocusAverage_dipolarBracket` (`= (1 − 3n_z²) • (Z⊗Z)`).
* `dipolarEffectiveCoupling γ₁ γ₂ r n = γ₁γ₂(1−3n_z²)/r³` and **Exercise 7.40 itself**,
  `zRefocusAverage_dipolarCoupling`: `⟨H^D_{1,2}(n̂)⟩_pulses = (ℏ J_eff / 4) • (Z⊗Z)`, for every
  choice of the physical constants `γ₁, γ₂, ℏ, r` and every direction `n̂` — the form (7.138).

## Fidelity

The formalisation is faithful: `dipolarCoupling` is N&C's genuine `H^D_{1,2}` of
(7.136); the pulses are the physical `180°` `ẑ`-refocusing pulses (conjugation by `Z`, phases
cancelling as in (7.150)); and the result is a *pure* `Z₁Z₂` interaction — the form of (7.138), with
the honest residual scalar `(ℏ γ₁γ₂(1−3n_z²)/4r³)`. The scope claimed is the zeroth-order average
(toggling-frame) Hamiltonian the pulse cycle produces — the standard, physically operative content
of the "sequence of pulses" answer; the higher-order Magnus corrections and the exact multi-period
propagator are deliberately not claimed.
-/
