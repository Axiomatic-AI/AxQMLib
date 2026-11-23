/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.SingleQubitWire

/-!
# Concrete: a fibrewise wire gate under a change of encoding (N&C Ex 4.44)

Every statement here concerns matrices — the fibrewise gate `wireGate` and its instances
`mcCtrlSingleQubit` / `singleQubitOnWire` — and encoding equivalences.

## Why this file: comparing two encodings of the same register

The register-realisation of the Deutsch gate `G = C²(iR_x(πα))` (Nielsen & Chuang, Exercise 4.44)
names `G` placed on register wires by transporting the base three-wire bridge
(`Concrete/DeutschRegisterBridge.lean`, `Concrete/DeutschTensorSplit.lean`) — which is stated
against the *specific* tensor-split encoding `regTensorEnc e restEnc` — onto an *arbitrary* register
encoding `fullEnc`. The wire *relabelling* of `Concrete/WireGateRelabel.lean` moves a gate's wires
inside a *fixed* encoding; this file gives the complementary move: changing the *encoding*
while keeping the wires fixed.

A fibrewise gate `wireGate enc j f` reads the encoding `enc` only through its
inverse `enc.symm` (the block condition and the fibre representative are read off the decoded
bit-string). So two encodings `enc₁, enc₂` of the same register give the *same* gate up to a
relabelling of the `d` basis indices by the permutation `enc₂.symm.trans enc₁` — i.e. a `submatrix`:

  `wireGate enc₂ j f = (wireGate enc₁ j f).submatrix (enc₂.symm.trans enc₁) (enc₂.symm.trans enc₁)`.

Together with the wire relabelling this reduces a placement on arbitrary wires of an arbitrary
encoding to the base three-wire placement of `regTensorEnc`, from which `deutschGate α` is named
(the `quditGate`-level companion `quditGate_submatrix_eq_conj` promotes the `submatrix` to
conjugation by the register permutation `quditPerm`).

## The construction and results

* `wireGate_encoding_change` — the general identity for the fibrewise gate.
* `mcCtrlSingleQubit_encoding_change` — its specialisation to the multiply-controlled single-qubit
  gate (same control set `S`, same target `j`).
* `singleQubitOnWire_encoding_change` — the uncontrolled corollary.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **A fibrewise gate under a change of encoding is a `submatrix`.** Since `wireGate enc j f` reads
the encoding only through `enc.symm` (both the fibre condition and the block representative are read
off the decoded bit-string), two encodings `enc₁, enc₂` of the same `d`-index register give the same
gate up to the relabelling of basis indices by `enc₂.symm.trans enc₁`:

  `wireGate enc₂ j f = (wireGate enc₁ j f).submatrix (enc₂.symm.trans enc₁) (enc₂.symm.trans enc₁)`.

Entrywise: `(wireGate enc₁ j f).submatrix ρ ρ I I' = wireGate enc₁ j f (ρ I) (ρ I')`, and with
`ρ = enc₂.symm.trans enc₁` the decoded strings `enc₁.symm (ρ I) = enc₂.symm I` agree, so the two
entries coincide (`Equiv.symm_apply_apply`). -/
theorem wireGate_encoding_change (enc₁ enc₂ : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :
    wireGate enc₂ j f
      = (wireGate enc₁ j f).submatrix (enc₂.symm.trans enc₁) (enc₂.symm.trans enc₁) := by
  ext I I'
  rw [Matrix.submatrix_apply, wireGate_apply, wireGate_apply]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

/-- **The multiply-controlled single-qubit gate under a change of encoding is a `submatrix`.** Same
control set `S` and target `j`, the encoding `enc₁` replaced by `enc₂`, and the two gates related by
the basis relabelling `enc₂.symm.trans enc₁` — the specialisation of `wireGate_encoding_change` at
the multiply-controlled block `fun y => if ∀ k ∈ S, y k = 1 then M2 else 1`. -/
theorem mcCtrlSingleQubit_encoding_change (enc₁ enc₂ : (Fin m → Fin 2) ≃ Fin d)
    (S : Finset (Fin m)) (j : Fin m) (M2 : Matrix (Fin 2) (Fin 2) ℂ) :
    mcCtrlSingleQubit enc₂ S j M2
      = (mcCtrlSingleQubit enc₁ S j M2).submatrix (enc₂.symm.trans enc₁)
          (enc₂.symm.trans enc₁) := by
  rw [mcCtrlSingleQubit, mcCtrlSingleQubit, wireGate_encoding_change enc₁ enc₂]

/-- **The uncontrolled single-qubit wire gate under a change of encoding is a `submatrix`.** The
`S = ∅` case of `mcCtrlSingleQubit_encoding_change` (through `mcCtrlSingleQubit_empty`). -/
theorem singleQubitOnWire_encoding_change (enc₁ enc₂ : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    singleQubitOnWire enc₂ j g
      = (singleQubitOnWire enc₁ j g).submatrix (enc₂.symm.trans enc₁) (enc₂.symm.trans enc₁) := by
  rw [← mcCtrlSingleQubit_empty enc₁ j g, ← mcCtrlSingleQubit_empty enc₂ j g,
    mcCtrlSingleQubit_encoding_change enc₁ enc₂]

end AxQM.Concrete
