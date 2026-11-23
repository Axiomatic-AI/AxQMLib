/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliAverage
import AxQM.Concrete.BlochPauliTwirl
import AxQM.Concrete.PauliExponential
import AxQM.Concrete.BlochUnitaryRotation

/-!
# Concrete: three-dimensional refocusing of a single-spin Hamiltonian (Nielsen & Chuang, Ex 7.39)

This file works entirely with the `2 × 2` Pauli matrices and the combination
`pauliDot c = c₀ X + c₁ Y + c₂ Z`.

Nielsen & Chuang, **Exercise 7.39 (three-dimensional refocusing)**, asks: *what set of pulses can
be used to refocus evolution under an arbitrary single-spin Hamiltonian* `Hsys = Σₖ cₖ σₖ`? The
single-term refocusing of §7.7.3 / Exercise 7.38 (eq. 7.150), `X e^{-iaZt} X = e^{+iaZt}`, works
because a `π`-pulse about `x̂` (conjugation by `X`) *reverses the sign* of the `Z` generator, which
anticommutes with `X`. For a general `Hsys` no single pulse suffices — conjugation by a unitary
rotates the Bloch axis but cannot invert all three components at once — so the answer is a
**sequence of `π`-pulses about two orthogonal axes**, whose toggling-frame conjugations run over the
Pauli group `{I, X, Y, Z}` and *average the Hamiltonian to zero*.

The mathematics behind this answer, formalised here (tracelessness of `Hsys` is the existing
`pauliDot_trace` of `Concrete/BlochUnitaryRotation.lean`, reused, not re-proved):

* `pauli_conj_pauliDot` — **the refocusing mechanism.** Conjugating `Hsys` by the `k`-th Pauli
  `σₖ` reflects the coefficient vector: `σₖ (c·σ) σₖ = (pauliBlochFlip k c)·σ`. The identity fixes
  `c`; each of `X, Y, Z` negates the two components orthogonal to its axis. This exhibits the
  Bloch-vector map `pauliBlochFlip` (of `BlochPauliTwirl`) as literally realised by matrix
  conjugation on `pauliDot`.
* `pauliDot_add_conj_pauliX` — **why one axis is not enough** (eq. 7.150–7.151). A single `x̂`-pulse
  pair refocuses the `ŷ, ẑ` components but leaves — indeed *doubles* — the `x̂` component:
  `H + X H X = (2 c₀) • X`.
* `pauliDot_conjSum_eq_zero` — **the refocusing identity.** Averaging over the full pulse group
  `{I, X, Y, Z}` annihilates any single-spin Hamiltonian: `H + X H X + Y H Y + Z H Z = 0`. This is
  the traceless case of the Pauli-twirl sum `pauliConjSum_eq`.
* `pauliZ_conj_eq_pauliX_pauliY_conj` — **two orthogonal axes suffice.** The `ẑ`-pulse conjugation
  is the composite of a `ŷ`-pulse then an `x̂`-pulse (`X Y = i Z`), so `π`-pulses about `x̂` and `ŷ`
  alone generate all four toggling frames; `pauliDot_conjSum_twoAxis_eq_zero` restates the
  refocusing identity using only `X`- and `Y`-conjugations.
* `pauli_conj_propagator` — **the exact evolution-level statement** (generalising eq. 7.150 /
  Ex 7.38). Conjugating the free-evolution propagator `e^{-i t H}` by a `π`-pulse `σₖ` produces the
  propagator of the *reflected* Hamiltonian: `σₖ e^{-i t H} σₖ = e^{-i t (pauliBlochFlip k c)·σ}`.
  For `H = a Z` and `k = 1` (an `x̂`-pulse) this is Exercise 7.38, `X e^{-iaZt} X = e^{iaZt}`.

## Design notes

* The single-spin Hamiltonian `Hsys = Σₖ cₖ σₖ` is the existing `pauliDot c` (`Concrete.Pauli`), so
  no new object is introduced — the file states the *refocusing* facts about it.
* The refocusing certificate is the vanishing of the equal-weight toggling-frame average
  `¼ Σ_{P ∈ {I,X,Y,Z}} P H P = 0` (the zeroth-order average Hamiltonian), which is the standard
  meaning of refocusing a *non-commuting* Hamiltonian; `pauli_conj_propagator` records the exact
  propagator identity underlying each individual toggling frame.
* Coefficient reflections reuse `pauliBlochFlip` from `BlochPauliTwirl`, tying the matrix algebra
  here to the Bloch-vector action already recorded there.
* The conjugation mechanism `pauli_conj_pauliDot` is proved *directly* per axis rather than derived
  from the general SU(2)→SO(3) statement `blochRotationOfUnitary_conj_pauliDot`
  (`Concrete/BlochUnitaryRotation.lean`), of which it is the Pauli instance. This is deliberate: the
  derivation would additionally need a bridge `blochRotationOfUnitary (pauli k) = pauliBlochFlip k`
  of comparable cost, and the direct per-axis lemmas `pauliX/Y/Z_conj_pauliDot` are themselves the
  useful, citable form.
-/

namespace AxQM.Concrete

open Matrix Complex NormedSpace
open scoped Matrix.Norms.Operator

/-- **`x̂`-pulse conjugation reflects the coefficient vector.** Conjugating `Hsys = c·σ` by the
Pauli `X` (a `π`-pulse about `x̂`) fixes the `x̂` component and negates the `ŷ, ẑ` components:
`X (c·σ) X = (c₀, −c₁, −c₂)·σ`, since `X` commutes with itself and anticommutes with `Y, Z`. -/
theorem pauliX_conj_pauliDot (c : Fin 3 → ℝ) :
    pauliX * pauliDot c * pauliX = pauliDot ![c 0, -c 1, -c 2] := by
  rw [pauliDot_eq, pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one] <;>
    push_cast <;> ring

/-- **`ŷ`-pulse conjugation reflects the coefficient vector.** Conjugating `Hsys = c·σ` by the
Pauli `Y` (a `π`-pulse about `ŷ`) fixes the `ŷ` component and negates the `x̂, ẑ` components:
`Y (c·σ) Y = (−c₀, c₁, −c₂)·σ`. -/
theorem pauliY_conj_pauliDot (c : Fin 3 → ℝ) :
    pauliY * pauliDot c * pauliY = pauliDot ![-c 0, c 1, -c 2] := by
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  rw [pauliDot_eq, pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one] <;>
    push_cast <;> ring_nf <;> (try rw [hI3]) <;> rw [Complex.I_sq] <;> ring

/-- **`ẑ`-pulse conjugation reflects the coefficient vector.** Conjugating `Hsys = c·σ` by the
Pauli `Z` (a `π`-pulse about `ẑ`) fixes the `ẑ` component and negates the `x̂, ŷ` components:
`Z (c·σ) Z = (−c₀, −c₁, c₂)·σ`. -/
theorem pauliZ_conj_pauliDot (c : Fin 3 → ℝ) :
    pauliZ * pauliDot c * pauliZ = pauliDot ![-c 0, -c 1, c 2] := by
  rw [pauliDot_eq, pauliDot_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one] <;>
    push_cast <;> ring

/-- **The refocusing mechanism, uniformly.** Conjugating the single-spin Hamiltonian `c·σ` by the
`k`-th Pauli matrix `σₖ` reflects its coefficient vector by `pauliBlochFlip k`:
`σₖ (c·σ) σₖ = (pauliBlochFlip k c)·σ`. The identity (`k = 0`) fixes `c`; each of `X, Y, Z`
(`k = 1, 2, 3`) negates the two components of `c` orthogonal to its axis and fixes its own. This
realises the Bloch-vector map `pauliBlochFlip` (of `BlochPauliTwirl`) by matrix conjugation, and
packages `pauliX_conj_pauliDot`, `pauliY_conj_pauliDot`, `pauliZ_conj_pauliDot` over the index. -/
theorem pauli_conj_pauliDot (k : Fin 4) (c : Fin 3 → ℝ) :
    pauli k * pauliDot c * pauli k = pauliDot (pauliBlochFlip k c) := by
  fin_cases k
  · simp [pauli, pauliBlochFlip]
  · exact pauliX_conj_pauliDot c
  · exact pauliY_conj_pauliDot c
  · exact pauliZ_conj_pauliDot c

/-- **A single refocusing axis is not enough** (Nielsen & Chuang eqs. 7.150–7.151). A `π`-pulse pair
about `x̂` (conjugation by `X`) refocuses the two components of `Hsys = c·σ` orthogonal to `x̂`
(they cancel), but leaves — in fact *doubles* — the `x̂` term: `(c·σ) + X (c·σ) X = (2 c₀) • X`.
To remove this surviving term one needs a second, orthogonal pulse axis. -/
theorem pauliDot_add_conj_pauliX (c : Fin 3 → ℝ) :
    pauliDot c + pauliX * pauliDot c * pauliX = ((2 * c 0 : ℝ) : ℂ) • pauliX := by
  rw [pauliX_conj_pauliDot, ← pauliDot_add]
  have hc : c + ![c 0, -c 1, -c 2] = ![2 * c 0, 0, 0] := by
    funext i
    fin_cases i <;> simp [two_mul]
  rw [hc, pauliDot]
  simp

/-- **The refocusing identity** — the answer to Exercise 7.39. Averaging any single-spin Hamiltonian
`Hsys = c·σ` over conjugation by the full Pauli pulse group `{I, X, Y, Z}` gives zero:
`(c·σ) + X (c·σ) X + Y (c·σ) Y + Z (c·σ) Z = 0`. Equivalently the equal-weight toggling-frame
average `¼ Σ_P P Hsys P` vanishes — the zeroth-order average Hamiltonian is zero, so the evolution
is refocused. This is the traceless case of the Pauli-twirl sum `pauliConjSum_eq`
(`= (2 · tr Hsys) • I`) together with `pauliDot_trace`. -/
theorem pauliDot_conjSum_eq_zero (c : Fin 3 → ℝ) :
    pauliDot c + pauliX * pauliDot c * pauliX + pauliY * pauliDot c * pauliY
      + pauliZ * pauliDot c * pauliZ = 0 := by
  rw [pauliConjSum_eq, pauliDot_trace, mul_zero, zero_smul]

/-- **Two orthogonal axes suffice.** Conjugation by the `ẑ`-pulse `Z` equals the composite of a
`ŷ`-pulse then an `x̂`-pulse, `Z M Z = X (Y M Y) X`, because `X Y = i Z` and `Y X = −i Z` (the phase
`i · (−i) = 1` cancels). Hence `π`-pulses about the two orthogonal axes `x̂` and `ŷ` alone realise
all four toggling frames `{I, X, Y, Z}` of the refocusing identity. -/
theorem pauliZ_conj_eq_pauliX_pauliY_conj (M : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliZ * M * pauliZ = pauliX * (pauliY * M * pauliY) * pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-- **The refocusing identity using only two orthogonal pulse axes.** Rewriting the `ẑ`-pulse term
of `pauliDot_conjSum_eq_zero` via `pauliZ_conj_eq_pauliX_pauliY_conj`, the refocusing of any
single-spin Hamiltonian is achieved with `π`-pulses about `x̂` and `ŷ` alone:
`(c·σ) + X (c·σ) X + Y (c·σ) Y + X (Y (c·σ) Y) X = 0`. This is the concrete "two orthogonal axes"
answer to Exercise 7.39. -/
theorem pauliDot_conjSum_twoAxis_eq_zero (c : Fin 3 → ℝ) :
    pauliDot c + pauliX * pauliDot c * pauliX + pauliY * pauliDot c * pauliY
      + pauliX * (pauliY * pauliDot c * pauliY) * pauliX = 0 := by
  rw [← pauliZ_conj_eq_pauliX_pauliY_conj, pauliDot_conjSum_eq_zero]

/-- **The exact evolution-level refocusing statement**, generalising Nielsen & Chuang eq. 7.150
(Exercise 7.38). Conjugating the free-evolution propagator `e^{-i t Hsys}` of a single-spin
Hamiltonian `Hsys = c·σ` by the `π`-pulse `σₖ` yields the propagator of the *reflected* Hamiltonian:
`σₖ · e^{-i t (c·σ)} · σₖ = e^{-i t ((pauliBlochFlip k c)·σ)}`.

The proof is `Matrix.exp_conj` (the exponential commutes with conjugation by a unit; `σₖ` is a unit
with `σₖ⁻¹ = σₖ` since `σₖ² = I`) applied to `pauli_conj_pauliDot`. Specialising to `H = a Z`
(`c = (0, 0, a)`) and `k = 1` (an `x̂`-pulse) gives `pauliBlochFlip 1 c = (0, 0, −a)`, i.e.
`X e^{-i a Z t} X = e^{+i a Z t}` — exactly Exercise 7.38. -/
theorem pauli_conj_propagator (k : Fin 4) (c : Fin 3 → ℝ) (t : ℝ) :
    pauli k * exp ((-(t : ℂ) * Complex.I) • pauliDot c) * pauli k
      = exp ((-(t : ℂ) * Complex.I) • pauliDot (pauliBlochFlip k c)) := by
  have hU : IsUnit (pauli k) := ⟨⟨pauli k, pauli k, pauli_mul_self k, pauli_mul_self k⟩, rfl⟩
  have hinv : (pauli k)⁻¹ = pauli k := Matrix.inv_eq_right_inv (pauli_mul_self k)
  have key : pauli k * ((-(t : ℂ) * Complex.I) • pauliDot c) * (pauli k)⁻¹
      = (-(t : ℂ) * Complex.I) • pauliDot (pauliBlochFlip k c) := by
    rw [hinv, mul_smul_comm, smul_mul_assoc, pauli_conj_pauliDot]
  rw [← key, Matrix.exp_conj _ _ hU, hinv]

end AxQM.Concrete
