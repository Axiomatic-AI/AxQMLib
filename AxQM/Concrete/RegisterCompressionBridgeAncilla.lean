/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RegisterCompressionBridge
import AxQM.Concrete.MultiControlledSingleQubitABCReduction
import AxQM.Concrete.MultiControlledNotPermProduct
import AxQM.Concrete.AxisAngleGateValues

/-!
# Concrete: compressing an ancilla-target / reversible placement to the data register (matrix level)

Every statement is about matrices — the multiply-controlled single-qubit gate `mcCtrlSingleQubit`,
the uncontrolled wire gate `singleQubitOnWire`, the phase-block matrix `phaseGate`, the named phase
gate `sMatrix`, the `≤ 2`-control reversible gates `IsToffoliPermGate`, and the coordinate-subspace
compression `compress` — together with the register-layout equivalences of
`AxQM/Concrete/RegisterCompressionBridge.lean`.

## Why this file: the two placement idioms `compress_wireGate_dataTarget` does not cover

`Concrete/RegisterCompressionBridge.lean` reads off the data-register action of a wire gate placed
on a **data** target (`compress_wireGate_dataTarget`,
`compress_mcCtrlSingleQubit_of_ancilla_controls`). Nielsen & Chuang's register realisation of the
Deutsch gate `G = C²(iR_x(πα))` (Exercise 4.44) needs two further idioms, supplied here.

* **The phase gate `S` (ancilla target).** `G`'s second dense single-qubit axis is the phase gate
  `S = diag(1, i)`, obtained from the *controlled global phase* `C(i · I)`: place `G` with one
  control on an ancilla wire held `|1⟩`, the *other control on the data wire* `w`, and the target on
  a throwaway ancilla, with the global-phase block `z · I` (`z = i`). Because the block is diagonal,
  the whole placement is a *diagonal* matrix (`mcCtrlSingleQubit_smul_one_eq_diagonal`), so its
  compression is again diagonal — and the accumulated phase `z` lands on the data-wire control,
  giving `singleQubitOnWire dataEnc w (phaseGate z)`, i.e. `S` on wire `w` when `z = i`
  (`sMatrix = phaseGate i`) and `S†` when `z = -i`. The target being an ancilla, this is *not* an
  instance of `compress_wireGate_dataTarget`; it goes through the diagonal.
* **The reversible gates `Toffoli`/`CNOT`/`NOT` (data target, mixed controls).** These have a data
  target, so `compress_wireGate_dataTarget` applies; the point is that when the full control set `S`
  restricts, on the ancilla-`|1⟩` subspace, to a data control condition on `C ⊆` data wires (some
  controls are ancillas held `|1⟩`, so vanish; the rest are data wires), the compression is the
  data-register gate `mcCtrlSingleQubit dataEnc C j g`. For `g = X` and `|C| ≤ 2` this is a
  `Toffoli`/`CNOT`/`NOT` on the data register (`IsToffoliPermGate`) — a `Toffoli` `C²(X)` placed
  with `k` of its controls on ancillas held `|1⟩` acts as a `C^{2-k}(X)` on the data wires.

## The construction and results

The diagonal facts this file rests on are generic and live in their home modules:
`compress_diagonal` / `preservesRange_diagonal` (a diagonal compresses to the diagonal of its
restriction, and every diagonal preserves the coordinate subspace, so a diagonal placement is
`compressionInvariant`) in `Concrete/SubspaceCompression.lean`, and `singleQubitOnWire_diagonal`
(a diagonal single-qubit block on a wire is `diag(fun i => v (bit j of i))`) in
`Concrete/SingleQubitWire.lean`.

* `compress_mcCtrlSingleQubit_smul_one_ancillaTarget` — **the phase-gate bridge**: a global-phase
  block `z · I` placed with target on a throwaway ancilla, one control on the data wire `w`, one on
  an ancilla held `|1⟩`, compresses to `singleQubitOnWire dataEnc w (phaseGate z)`. Its `z = i` /
  `z = -i` corollaries name the phase gate `S` / `S†`
  (`..._eq_sMatrix` / `..._eq_sMatrixConjTranspose`), and
  `mcCtrlSingleQubit_smul_one_mem_compressionInvariant` records that such a diagonal placement is
  compressible.
* `forall_mem_regExtend_eq_one_iff` — the control-condition descent: on the ancilla-`|1⟩`
  subspace, a full control condition over `S` is the data control condition over the data wires
  `C` of `S`.
* `compress_mcCtrlSingleQubit_dataTarget_of_ctrl_iff` — **the reversible bridge**: a data-target
  gate whose full control condition descends to a data condition over `C` compresses to
  `mcCtrlSingleQubit dataEnc C j g`; and `isToffoliPermGate_compress_mcCtrlSingleQubit_pauliX` reads
  off `IsToffoliPermGate` for `g = X`, `|C| ≤ 2`.
-/

namespace AxQM.Concrete

open Matrix

variable {M m n D d : ℕ}

/-- **A diagonal global-phase placement is compressible.** For a target wire `j ∉ S`, the placement
`mcCtrlSingleQubit fullEnc S j (z • 1)` is a diagonal matrix
(`mcCtrlSingleQubit_smul_one_eq_diagonal`), hence lies in `compressionInvariant (regEmbed …)`
(`preservesRange_diagonal`) — so `compressHom` applies to it and to its products. This covers the
phase-gate placement `compress_mcCtrlSingleQubit_smul_one_ancillaTarget`, whose target is an
ancilla wire. -/
theorem mcCtrlSingleQubit_smul_one_mem_compressionInvariant (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) (S : Finset (Fin M))
    {j : Fin M} (hj : j ∉ S) (z : ℂ) :
    mcCtrlSingleQubit fullEnc S j (z • 1)
      ∈ compressionInvariant (regEmbed fullEnc dataEnc e) := by
  rw [mcCtrlSingleQubit_smul_one_eq_diagonal fullEnc hj]
  exact preservesRange_diagonal (regEmbed fullEnc dataEnc e) _

/-- **The phase-gate register bridge** (Nielsen & Chuang, Exercise 4.44). Placing the global-phase
block `z · I` with the target on a throwaway ancilla wire `e.symm (Sum.inr t)`, one control on the
data wire `e.symm (Sum.inl w)`, and one control on an ancilla wire `e.symm (Sum.inr a)` (held `|1⟩`
on the subspace, `a ≠ t`), and reading off the data-register action, gives
`singleQubitOnWire dataEnc w (phaseGate z)`: the *controlled global phase* `C(z · I)` becomes the
phase-block gate `diag(1, z)` on the data-wire control `w`.

The block is diagonal, so the whole placement is a diagonal matrix
(`mcCtrlSingleQubit_smul_one_eq_diagonal`); compressing a diagonal is again diagonal
(`compress_diagonal`), and its `x`-th diagonal entry is `z` exactly when the control condition holds
at the embedded state — i.e. when the ancilla control (always `1`) and the data control `w` are set,
which reduces to `bit w of x = 1`. That is the `x`-th diagonal entry of
`singleQubitOnWire dataEnc w (phaseGate z)` (`phaseGate_eq_diagonal`, `singleQubitOnWire_diagonal`).
For `z = i` this is the phase gate `S` on wire `w` (`sMatrix = phaseGate i`), the second dense
single-qubit axis of `G`. -/
theorem compress_mcCtrlSingleQubit_smul_one_ancillaTarget (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) (a t : Fin n) (hat : a ≠ t)
    (w : Fin m) (z : ℂ) :
    compress (regEmbed fullEnc dataEnc e)
        (mcCtrlSingleQubit fullEnc {e.symm (Sum.inr a), e.symm (Sum.inl w)} (e.symm (Sum.inr t))
          (z • 1))
      = singleQubitOnWire dataEnc w (phaseGate z) := by
  have htgt : e.symm (Sum.inr t) ∉
      ({e.symm (Sum.inr a), e.symm (Sum.inl w)} : Finset (Fin M)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => hat (Sum.inr_injective (e.symm.injective h)).symm, fun h => ?_⟩
    exact Sum.inr_ne_inl (e.symm.injective h)
  rw [mcCtrlSingleQubit_smul_one_eq_diagonal fullEnc htgt,
    compress_diagonal (regEmbed_injective fullEnc dataEnc e), phaseGate_eq_diagonal,
    singleQubitOnWire_diagonal]
  congr 1
  funext x
  simp only [Function.comp_apply, regEmbed, Equiv.symm_apply_apply, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq, regExtend_apply_symm_inr,
    regExtend_apply_symm_inl, true_and]
  generalize (dataEnc.symm x) w = b
  fin_cases b <;> simp

/-- **The phase gate `S` from `G` on register wires.** The `z = i` case of
`compress_mcCtrlSingleQubit_smul_one_ancillaTarget`: the controlled global phase `C(i · I)`
compresses to `singleQubitOnWire dataEnc w sMatrix`, the phase gate `S = diag(1, i)` on the
data-wire control `w` — the register realisation of `G`'s second dense single-qubit axis
(`sMatrix = phaseGate i` definitionally). -/
theorem compress_mcCtrlSingleQubit_smul_one_ancillaTarget_eq_sMatrix
    (fullEnc : (Fin M → Fin 2) ≃ Fin D) (dataEnc : (Fin m → Fin 2) ≃ Fin d)
    (e : Fin M ≃ Fin m ⊕ Fin n) (a t : Fin n) (hat : a ≠ t) (w : Fin m) :
    compress (regEmbed fullEnc dataEnc e)
        (mcCtrlSingleQubit fullEnc {e.symm (Sum.inr a), e.symm (Sum.inl w)} (e.symm (Sum.inr t))
          (Complex.I • 1))
      = singleQubitOnWire dataEnc w sMatrix := by
  have hS : sMatrix = phaseGate Complex.I := rfl
  rw [hS, compress_mcCtrlSingleQubit_smul_one_ancillaTarget fullEnc dataEnc e a t hat w Complex.I]

/-- **The adjoint phase gate `S†` from `G` on register wires.** The `z = -i` case of
`compress_mcCtrlSingleQubit_smul_one_ancillaTarget`: with block `-i · I` the compression is
`singleQubitOnWire dataEnc w sMatrix†`, the second generator (`S†`) of the single-qubit gates `G`
reaches on a wire (`sMatrix† = diag(1, -i) = phaseGate (-i)`). -/
theorem compress_mcCtrlSingleQubit_smul_one_ancillaTarget_eq_sMatrixConjTranspose
    (fullEnc : (Fin M → Fin 2) ≃ Fin D) (dataEnc : (Fin m → Fin 2) ≃ Fin d)
    (e : Fin M ≃ Fin m ⊕ Fin n) (a t : Fin n) (hat : a ≠ t) (w : Fin m) :
    compress (regEmbed fullEnc dataEnc e)
        (mcCtrlSingleQubit fullEnc {e.symm (Sum.inr a), e.symm (Sum.inl w)} (e.symm (Sum.inr t))
          ((-Complex.I) • 1))
      = singleQubitOnWire dataEnc w sMatrix.conjTranspose := by
  have hSc : sMatrix.conjTranspose = phaseGate (-Complex.I) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sMatrix, phaseGate, Matrix.conjTranspose]
  rw [compress_mcCtrlSingleQubit_smul_one_ancillaTarget fullEnc dataEnc e a t hat w (-Complex.I),
    hSc]

/-- **The control-condition descent to the data register.** On the ancilla-`|1⟩` subspace, a full
control condition over `S` is exactly the data control condition over the data wires of `S`: for
`C` the set of data wires `c` with `e.symm (Sum.inl c) ∈ S` (characterised by `hC`), and any data
bit-string `x`, `(∀ k ∈ S, regExtend e x k = 1) ↔ (∀ c ∈ C, x c = 1)`. The data wires of `S`
contribute their data bits `x c`; the ancilla wires of `S` are held `|1⟩` by the extension, so their
condition is automatic (`regExtend_apply_symm_inr`). This is the hypothesis the reversible bridge
consumes. -/
theorem forall_mem_regExtend_eq_one_iff (e : Fin M ≃ Fin m ⊕ Fin n) (S : Finset (Fin M))
    (C : Finset (Fin m)) (hC : ∀ c : Fin m, c ∈ C ↔ e.symm (Sum.inl c) ∈ S) (x : Fin m → Fin 2) :
    (∀ k ∈ S, regExtend e x k = 1) ↔ (∀ c ∈ C, x c = 1) := by
  constructor
  · intro h c hc
    have hk := h (e.symm (Sum.inl c)) ((hC c).mp hc)
    rwa [regExtend_apply_symm_inl] at hk
  · intro h k hk
    rcases hek : e k with c | r
    · have hks : e.symm (Sum.inl c) = k := by rw [← hek, Equiv.symm_apply_apply]
      rw [← hks, regExtend_apply_symm_inl]
      exact h c ((hC c).mpr (hks ▸ hk))
    · simp only [regExtend, hek, Sum.elim_inr]

/-- **The reversible register bridge** (data target, controls descending to the data register).
Placing a single-qubit block `g` on a **data** wire `e.symm (Sum.inl j)` with a full control set `S`
whose condition descends, on the ancilla-`|1⟩` subspace, to a data control condition over
`C ⊆` data wires (`hSC`, e.g. from `forall_mem_regExtend_eq_one_iff`) compresses to the
data-register gate `mcCtrlSingleQubit dataEnc C j g`. A one-step consequence of the generic
data-target bridge
`compress_wireGate_dataTarget`: the descended control condition rewrites the block family
fibrewise. -/
theorem compress_mcCtrlSingleQubit_dataTarget_of_ctrl_iff (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) (S : Finset (Fin M))
    (j : Fin m) (C : Finset (Fin m)) (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hSC : ∀ x : Fin m → Fin 2, (∀ k ∈ S, regExtend e x k = 1) ↔ (∀ c ∈ C, x c = 1)) :
    compress (regEmbed fullEnc dataEnc e) (mcCtrlSingleQubit fullEnc S (e.symm (Sum.inl j)) g)
      = mcCtrlSingleQubit dataEnc C j g := by
  simp only [mcCtrlSingleQubit]
  rw [compress_wireGate_dataTarget]
  congr 1
  funext x
  by_cases h : ∀ k ∈ S, regExtend e x k = 1
  · rw [ite_eq_left h, ite_eq_left ((hSC x).mp h)]
  · rw [ite_eq_right h, ite_eq_right fun hc => h ((hSC x).mpr hc)]

/-- **The reversible gates `Toffoli`/`CNOT`/`NOT` from `G` on register wires.** For a Pauli-`X`
block on a data wire `e.symm (Sum.inl j)` with `≤ 2` data controls `C` (`j ∉ C`) whose condition
descends from the full control set `S` (`hSC`), the compressed data-register gate is a `≤ 2`-control
reversible permutation gate `IsToffoliPermGate dataEnc`: the multiply-controlled `NOT`
`mcCtrlSingleQubit dataEnc C j X` is the permutation gate `permGate dataEnc (mcNotPerm C j)`
(`mcCtrlSingleQubit_pauliX_eq_permGate`), a `Toffoli`/`CNOT`/`NOT` since `|C| ≤ 2`. This is how a
`Toffoli` `C²(X)` placed with some controls on ancillas held `|1⟩` realises the reduced reversible
gates on the data register. -/
theorem isToffoliPermGate_compress_mcCtrlSingleQubit_pauliX (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) (S : Finset (Fin M))
    (j : Fin m) (C : Finset (Fin m)) (hj : j ∉ C) (hcard : C.card ≤ 2)
    (hSC : ∀ x : Fin m → Fin 2, (∀ k ∈ S, regExtend e x k = 1) ↔ (∀ c ∈ C, x c = 1)) :
    IsToffoliPermGate dataEnc
      (compress (regEmbed fullEnc dataEnc e)
        (mcCtrlSingleQubit fullEnc S (e.symm (Sum.inl j)) pauliX)) := by
  rw [compress_mcCtrlSingleQubit_dataTarget_of_ctrl_iff fullEnc dataEnc e S j C pauliX hSC,
    mcCtrlSingleQubit_pauliX_eq_permGate dataEnc C hj]
  exact ⟨C, j, hj, hcard, rfl⟩

end AxQM.Concrete
