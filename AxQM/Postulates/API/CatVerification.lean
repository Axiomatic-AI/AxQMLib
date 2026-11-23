/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CSSCode
import AxQM.Postulates.API.MeasureObservable

/-!
# AxQM.Postulates.API — the `n`-qubit cat ancilla and its parity-check verification

Infrastructure for the **verification** stage of the fault-tolerant cat-state
measurement (Nielsen & Chuang §10.6.3, Exercise 10.69), formalised at **general qubit count**. To
measure an encoded observable fault-tolerantly N&C prepare an ancilla in a *cat state*
`|0…0⟩ + |1…1⟩` and then **verify** it by measuring the two-qubit parities `ZᵢZⱼ`: a genuine cat has
even parity across every pair, so a `−1` outcome flags a bit-flip error and the ancilla is
discarded. N&C's Figure 10.28 draws the cat on three qubits "for simplicity"; the real construction
(the seven-qubit Steane code) needs more, and it is only for `n ≥ 5` that the verification does
strictly more than the cat's own `X^{⊗n}` symmetry. This file therefore works over an **arbitrary**
qubit index type `ι` — the `n`-qubit register `bitReg ι` of `Postulates/API/CSSCode.lean`, with its
computational basis `regBasis`, bit-flip strings `bitString` (`X^v`, `|w⟩ ↦ |w + v⟩`) and phase
strings `phaseString` (`Z^u`, `|w⟩ ↦ (−1)^{u·w} |w⟩`).

* `catVec ι` / `catState ι` — the (unnormalised, then normalised) `+`-signed cat ancilla
  `|0…0⟩ + |1…1⟩` on `bitReg ι` (`catVec_norm`: `‖catVec ι‖ = √2`).
* `zPairObservable i j` — the **two-qubit parity check** `ZᵢZⱼ`, the `±1` observable obtained from
  the self-adjoint unitary phase string `Z^{eᵢ + eⱼ}` (`Evolution.toObservable`). Its `+1`/`−1`
  outcome is the *even*/*odd* parity of qubits `i, j`.
* `zPairObservable_op_catVec` — the ideal cat **passes** every check: `ZᵢZⱼ |cat⟩ = |cat⟩`.
* `zPairObservable_op_bitString_op_catVec` — the **syndrome of a patterned bit-flip error**: the
  errored cat `X^{p}|cat⟩` is an eigenvector of `ZᵢZⱼ` with eigenvalue `(−1)^{(pᵢ + pⱼ)}`; `+1`
  (accept) iff `pᵢ = pⱼ`, `−1` (reject) iff `pᵢ ≠ pⱼ`. Both kets `|p⟩` and `|1+p⟩` of the errored
  cat carry the **same** sign because the check has *even support* (`u·1 = 0`), so complementing
  all bits leaves `pᵢ + pⱼ` fixed.
* `bitString_one_op_catVec` — the cat's `X^{⊗n}` symmetry: flipping **every** qubit fixes `|cat⟩`.

The statements built from these — the ideal cat passing verification, the syndrome eigenvalues,
and the detection dichotomy (every non-constant residue is caught, every constant one is harmless) —
are in `AxQM/NC/Ch10/Exercise10_69.lean`. This file builds on the `bitReg`/`bitString`/`phaseString`
framework (`CSSCode`).
-/

open scoped Matrix
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The `n`-qubit cat ancilla -/

variable (ι) in
/-- **The unnormalised `n`-qubit cat vector** `|0…0⟩ + |1…1⟩` on the register `bitReg ι`: the sum of
the all-zeros and all-ones computational-basis vectors. This is the ancilla N&C prepare (and then
verify) for a fault-tolerant measurement (§10.6.3); the `+`-signed cat, encoding `|+⟩` under the
repetition structure. -/
def catVec : (bitReg ι).space := regBasis ι 0 + regBasis ι 1

/-- **The cat vector has inner product `2` with itself:** `⟪catVec, catVec⟫ = 2`, since it is the
sum of two orthonormal computational-basis vectors `|0…0⟩` and `|1…1⟩` (distinct on a nonempty
register, so orthogonal). -/
theorem catVec_inner [Nonempty ι] :
    (inner ℂ (catVec ι) (catVec ι) : ℂ) = 2 := by
  have hii := (orthonormal_iff_ite (𝕜 := ℂ)).1 (regBasis ι).orthonormal
  simp only [catVec, inner_add_left, inner_add_right, hii]
  norm_num

/-- **The cat vector is nonzero** (on a nonempty register). Immediate from `⟪catVec, catVec⟫ = 2 ≠
0` (`catVec_inner`). -/
theorem catVec_ne_zero [Nonempty ι] : catVec ι ≠ 0 := by
  intro h
  have hi := catVec_inner (ι := ι)
  rw [h, inner_zero_right] at hi
  exact (by norm_num : (2 : ℂ) ≠ 0) hi.symm

/-- **The cat vector has norm `√2`:** `‖catVec ι‖ = √2`, since `⟪catVec, catVec⟫ = 2`
(`catVec_inner`). The common normalisation constant of the cat ancilla. -/
theorem catVec_norm [Nonempty ι] : ‖catVec ι‖ = Real.sqrt 2 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), catVec_inner]
  norm_num

variable (ι) in
/-- **The normalised `n`-qubit cat ancilla** `catState ι = |cat⟩/√2 = (|0…0⟩ + |1…1⟩)/√2`, a
`PureState` of `bitReg ι`. Built from `catVec ι` through the shared `PureState.normalize`
constructor. -/
def catState [Nonempty ι] : PureState (bitReg ι) :=
  PureState.normalize (catVec ι) catVec_ne_zero

/-! ### The two-qubit parity check `ZᵢZⱼ` -/

/-- **The phase string `Z^u` is self-adjoint.** Its operator is the diagonal sign operator on
`regBasis` with real `±1` entries `(−1)^{(u·w)}`, and a real-diagonal operator equals its own
adjoint (`OrthonormalBasis.diagonalOperator_adjoint`, `star (−1)^k = (−1)^k`). This is what makes
`Z^u` a genuine `±1` observable. -/
theorem phaseString_op_isSelfAdjoint (u : ι → ZMod 2) : IsSelfAdjoint (phaseString u).op := by
  rw [phaseString_op, isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint,
    (regBasis ι).diagonalOperator_adjoint]
  congr 1
  funext w
  simp [star_pow]

/-- **The two-qubit parity observable `ZᵢZⱼ`** on `bitReg ι`, the phase string `Z^{eᵢ + eⱼ}` viewed
as a `±1` observable (`Evolution.toObservable`, self-adjoint by `phaseString_op_isSelfAdjoint`). Its
`+1`/`−1` outcome measures the *parity* of qubits `i` and `j`: even (accept) or odd (reject). This
is the verification check of the cat ancilla (N&C §10.6.3). -/
def zPairObservable (i j : ι) : Observable (bitReg ι) :=
  (phaseString (Pi.single i 1 + Pi.single j 1)).toObservable (phaseString_op_isSelfAdjoint _)

/-- **The operator of `ZᵢZⱼ` is the phase string `Z^{eᵢ + eⱼ}`.** Definitional bridge to the
action lemmas of `phaseString`. -/
theorem zPairObservable_op (i j : ι) :
    (zPairObservable i j).op = (phaseString (Pi.single i 1 + Pi.single j 1)).op := rfl

/-! ### Parity syndromes of the cat ancilla -/

/-- **The `Z^{eᵢ + eⱼ}` sign of a bit string is `wᵢ + wⱼ`:** `(eᵢ + eⱼ) · w = wᵢ + wⱼ`. The
two-qubit parity check reads exactly the sum (mod 2) of the two bits it couples. -/
theorem single_pair_dotProduct (i j : ι) (w : ι → ZMod 2) :
    (Pi.single i 1 + Pi.single j 1) ⬝ᵥ w = w i + w j := by
  rw [add_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]

/-- **The bit-flip error string acts on the cat by translating both corners:**
`X^{p}|cat⟩ = |p⟩ + |1 + p⟩`. From `bitString_op_regBasis` (`X^p|w⟩ = |w + p⟩`) on the two corners
`|0…0⟩` and `|1…1⟩`. -/
theorem bitString_op_catVec (p : ι → ZMod 2) :
    (bitString p).op (catVec ι) = regBasis ι p + regBasis ι (1 + p) := by
  rw [catVec, map_add, bitString_op_regBasis, bitString_op_regBasis, zero_add]

/-- **A bit flip on all `n` qubits fixes the cat ancilla:** `X^{⊗n}|cat⟩ = |cat⟩`. Flipping every
qubit swaps the two corners `|0…0⟩ ↔ |1…1⟩`, so it leaves the `+` cat invariant. This is the cat's
bit-flip symmetry `X^{⊗n} = 1` on the codeword — the `n`-qubit analogue of `blockXGate`'s action on
the three-qubit block. -/
theorem bitString_one_op_catVec :
    (bitString (1 : ι → ZMod 2)).op (catVec ι) = catVec ι := by
  have h11 : (1 : ι → ZMod 2) + 1 = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero (1 : ZMod 2)
  rw [bitString_op_catVec, h11, catVec, add_comm (regBasis ι 1) (regBasis ι 0)]

/-- **A bit flip by the zero pattern fixes the cat ancilla** (it is the identity): `X^{0}|cat⟩ =
|cat⟩`. -/
theorem bitString_zero_op_catVec :
    (bitString (0 : ι → ZMod 2)).op (catVec ι) = catVec ι := by
  rw [bitString_op_catVec, catVec, add_zero]

/-- **The ideal cat ancilla passes every verification check:** `ZᵢZⱼ |cat⟩ = |cat⟩`, i.e. the cat is
a `+1` eigenvector of every parity `ZᵢZⱼ`. Every pair of qubits in the genuine cat has even parity —
the defining property N&C's verification tests. Both corners `|0…0⟩` and `|1…1⟩` are fixed because
`(eᵢ + eⱼ)·0 = 0` and `(eᵢ + eⱼ)·1 = 1 + 1 = 0` (even support). -/
theorem zPairObservable_op_catVec (i j : ι) :
    (zPairObservable i j).op (catVec ι) = catVec ι := by
  have hc0 : ((Pi.single i 1 + Pi.single j 1) ⬝ᵥ (0 : ι → ZMod 2)).val = 0 := by
    rw [single_pair_dotProduct]; simp
  have hc1 : ((Pi.single i 1 + Pi.single j 1) ⬝ᵥ (1 : ι → ZMod 2)).val = 0 := by
    rw [single_pair_dotProduct]; simp only [Pi.one_apply]; decide
  rw [zPairObservable_op, catVec, map_add, phaseString_op_regBasis, phaseString_op_regBasis,
    hc0, hc1]
  simp only [pow_zero, one_smul]

/-- **The parity syndrome of a patterned bit-flip error.** For every bit-flip pattern
`p : ι → ZMod 2`, the errored cat `X^{p}|cat⟩` is an eigenvector of the parity check `ZᵢZⱼ` with
eigenvalue `(−1)^{(pᵢ + pⱼ)}`: measuring `ZᵢZⱼ` gives `+1` (accept) iff `pᵢ = pⱼ`, and `−1`
(reject) iff `pᵢ ≠ pⱼ`. Both kets `|p⟩` and `|1 + p⟩` of the errored cat carry this **same** sign,
because the check couples an *even* number of qubits (`(eᵢ + eⱼ)·1 = 0`), so complementing every bit
leaves `pᵢ + pⱼ` unchanged. This is the algebraic heart of the verification detection. -/
theorem zPairObservable_op_bitString_op_catVec (i j : ι) (p : ι → ZMod 2) :
    (zPairObservable i j).op ((bitString p).op (catVec ι))
      = (-1 : ℂ) ^ (p i + p j : ZMod 2).val • ((bitString p).op (catVec ι)) := by
  have e1 : (Pi.single i 1 + Pi.single j 1) ⬝ᵥ p = p i + p j := single_pair_dotProduct i j p
  have e2 : (Pi.single i 1 + Pi.single j 1) ⬝ᵥ (1 + p) = p i + p j := by
    rw [single_pair_dotProduct]
    simp only [Pi.add_apply, Pi.one_apply]
    have h : ∀ a b : ZMod 2, (1 + a) + (1 + b) = a + b := by decide
    exact h (p i) (p j)
  rw [bitString_op_catVec, zPairObservable_op, map_add, phaseString_op_regBasis,
    phaseString_op_regBasis, e1, e2, smul_add]

end AxQM
