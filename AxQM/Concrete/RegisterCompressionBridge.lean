/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubspaceCompression
import AxQM.Concrete.MultiControlledSingleQubit

/-!
# Concrete: compressing a wire-gate placement to the data register (matrix level)

Every statement is about matrices — the fibrewise wire gate `wireGate`, the multiply-controlled
single-qubit gate `mcCtrlSingleQubit`, the uncontrolled wire gate `singleQubitOnWire`, and the
coordinate-subspace compression `compress` — together with the encoding equivalences and a
wire-splitting equivalence.

## Why this file: reading off the data-register action of an ancilla circuit

Nielsen & Chuang's register realisations place a gate on the wires of a large register — some
**data** wires together with **ancilla** wires held in a fixed state `|1…1⟩` — and read off its
action on the *data* register. `Concrete/SubspaceCompression.lean` provides the algebraic core: the
compression `compress ι M = M.submatrix ι ι` to the coordinate subspace `range ι` picked out by the
ancilla-`|1⟩` basis states is a continuous monoid homomorphism on the range-preserving matrices.
This file supplies the **register layout**: the concrete embedding `ι` of the data basis into the
full basis (data bits on the data wires, `1` on the ancilla wires), and the identity that a
single-qubit gate placed on a **data** wire — with any controls on ancilla wires held `|1⟩` —
compresses to exactly that single-qubit gate on the data register.

## The construction

Fix a full-register encoding `fullEnc : (Fin M → Fin 2) ≃ Fin D`, a data-register encoding
`dataEnc : (Fin m → Fin 2) ≃ Fin d`, and a **wire-splitting** equivalence
`e : Fin M ≃ Fin m ⊕ Fin n` identifying the full wires as the data wires (`Sum.inl`) together with
the `n` ancilla wires (`Sum.inr`).

* `regExtend e x` — the full bit-string extending the data bit-string `x`: it carries `x` on the
  data wires and `1` on the ancilla wires (`regExtend e x k = Sum.elim x (fun _ => 1) (e k)`).
* `regEmbed fullEnc dataEnc e i := fullEnc (regExtend e (dataEnc.symm i))` — the induced embedding
  `Fin d → Fin D` of the data basis indices into the full basis indices, injective
  (`regEmbed_injective`). Its range is exactly the ancilla-`|1⟩` basis states
  (`mem_range_regEmbed_iff`).

## The bridge

* `preservesRange_wireGate_dataTarget` — a fibrewise gate on a **data** wire preserves `range`
  (`compressionInvariant`): it only ever changes a data bit, so it maps the ancilla-`|1⟩` subspace
  to itself. Hence a `mcCtrlSingleQubit`/`singleQubitOnWire` placement on a data wire is
  compressible (`mcCtrlSingleQubit_dataTarget_mem_compressionInvariant`).
* `compress_wireGate_dataTarget` — **the generic bridge**: compressing a data-wire fibrewise gate
  `wireGate fullEnc (data wire j) F` gives the data-register fibrewise gate
  `wireGate dataEnc j (F ∘ regExtend e)` — the block family read at the extended bit-strings.
* `compress_mcCtrlSingleQubit_of_ancilla_controls` — **the headline application**: a single-qubit
  gate `g` placed on a data wire `j` with all controls on **ancilla** wires (held `|1⟩` in the
  subspace) compresses to the uncontrolled single-qubit gate `singleQubitOnWire dataEnc j g` on the
  data register — the controls are satisfied on the whole subspace, so they vanish. This is the
  register realisation of a dense single-qubit axis: a doubly-controlled single-qubit gate whose two
  controls are ancillas held `|1⟩` acts as the bare single-qubit gate on the data wire.
-/

namespace AxQM.Concrete

open Matrix

variable {M m n D d : ℕ}

/-- **The register extension of a data bit-string.** Relative to a wire-splitting equivalence
`e : Fin M ≃ Fin m ⊕ Fin n`, `regExtend e x` is the full `M`-bit string carrying the data bits `x`
on the data wires (`Sum.inl`) and `1` on the ancilla wires (`Sum.inr`):
`regExtend e x k = Sum.elim x (fun _ => 1) (e k)`. It is the bit-string picture of holding the
ancilla wires at `|1⟩`. -/
def regExtend (e : Fin M ≃ Fin m ⊕ Fin n) (x : Fin m → Fin 2) : Fin M → Fin 2 :=
  fun k => Sum.elim x (fun _ => (1 : Fin 2)) (e k)

/-- On a data wire `e.symm (Sum.inl j)`, the register extension reads the data bit `x j`. -/
@[simp] theorem regExtend_apply_symm_inl (e : Fin M ≃ Fin m ⊕ Fin n) (x : Fin m → Fin 2)
    (j : Fin m) : regExtend e x (e.symm (Sum.inl j)) = x j := by
  simp only [regExtend, Equiv.apply_symm_apply, Sum.elim_inl]

/-- On an ancilla wire `e.symm (Sum.inr r)`, the register extension is `1` (the held ancilla value),
regardless of the data bits. -/
@[simp] theorem regExtend_apply_symm_inr (e : Fin M ≃ Fin m ⊕ Fin n) (x : Fin m → Fin 2)
    (r : Fin n) : regExtend e x (e.symm (Sum.inr r)) = 1 := by
  simp only [regExtend, Equiv.apply_symm_apply, Sum.elim_inr]

/-- **Updating a data bit commutes with the register extension.** Setting the data wire
`e.symm (Sum.inl j)` of `regExtend e x` to `v` is the same as extending the data bit-string with `x`
already updated at `j`: `(regExtend e x)[e.symm (inl j) ↦ v] = regExtend e (x[j ↦ v])`. Both change
only the one data wire, leaving every other wire (data or ancilla) untouched. -/
theorem update_regExtend_symm_inl (e : Fin M ≃ Fin m ⊕ Fin n) (x : Fin m → Fin 2) (j : Fin m)
    (v : Fin 2) :
    Function.update (regExtend e x) (e.symm (Sum.inl j)) v
      = regExtend e (Function.update x j v) := by
  funext k
  rcases eq_or_ne k (e.symm (Sum.inl j)) with rfl | hk
  · rw [Function.update_self, regExtend_apply_symm_inl, Function.update_self]
  · rw [Function.update_of_ne hk]
    simp only [regExtend]
    rcases hek : e k with j' | r
    · have hj' : j' ≠ j := fun h => hk (by rw [← h, ← hek, Equiv.symm_apply_apply])
      rw [Sum.elim_inl, Sum.elim_inl, Function.update_of_ne hj']
    · rw [Sum.elim_inr, Sum.elim_inr]

/-- **Agreement off a data wire descends to the data register.** Two extended bit-strings agree on
every full wire but the data wire `e.symm (Sum.inl j)` iff the underlying data bit-strings agree on
every data wire but `j`: the ancilla wires always agree (both `1`), and the remaining data wires
agree iff their bits do. This is the fibre-condition equivalence that carries `wireGate` through the
compression. -/
theorem forall_ne_regExtend_iff (e : Fin M ≃ Fin m ⊕ Fin n) (j : Fin m) (x y : Fin m → Fin 2) :
    (∀ k, k ≠ e.symm (Sum.inl j) → regExtend e x k = regExtend e y k)
      ↔ ∀ k, k ≠ j → x k = y k := by
  constructor
  · intro h k hk
    have hne : e.symm (Sum.inl k) ≠ e.symm (Sum.inl j) :=
      fun he => hk (Sum.inl_injective (e.symm.injective he))
    simpa using h (e.symm (Sum.inl k)) hne
  · intro h k hk
    simp only [regExtend]
    rcases hek : e k with j' | r
    · have hj' : j' ≠ j := fun hj => hk (by rw [← hj, ← hek, Equiv.symm_apply_apply])
      rw [Sum.elim_inl, Sum.elim_inl, h j' hj']
    · rw [Sum.elim_inr, Sum.elim_inr]

/-- **The data-into-full-register basis embedding.** `regEmbed fullEnc dataEnc e i` sends the data
basis index `i` to the full basis index of the extended bit-string `regExtend e (dataEnc.symm i)` —
the data bits of `i` on the data wires and `1` on the ancilla wires. It is the index map `ι` picking
out the ancilla-`|1⟩` coordinate subspace, along which `compress` reads a full-register gate's data
action. -/
def regEmbed (fullEnc : (Fin M → Fin 2) ≃ Fin D) (dataEnc : (Fin m → Fin 2) ≃ Fin d)
    (e : Fin M ≃ Fin m ⊕ Fin n) : Fin d → Fin D :=
  fun i => fullEnc (regExtend e (dataEnc.symm i))

/-- **The register extension is injective**: the data bits are recovered from the extension by
reading the data wires (`regExtend_apply_symm_inl`). -/
theorem regExtend_injective (e : Fin M ≃ Fin m ⊕ Fin n) :
    Function.Injective (regExtend e) := by
  intro x y hxy
  funext j
  have := congrFun hxy (e.symm (Sum.inl j))
  rwa [regExtend_apply_symm_inl, regExtend_apply_symm_inl] at this

/-- **The data-into-full-register embedding is injective** — a composite of the injective
`dataEnc.symm`, `regExtend e`, and `fullEnc`. Injectivity is what makes the compression along
`regEmbed` send the identity to the identity (`compress_one`). -/
theorem regEmbed_injective (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) :
    Function.Injective (regEmbed fullEnc dataEnc e) :=
  fullEnc.injective.comp ((regExtend_injective e).comp dataEnc.symm.injective)

/-- **The embedded subspace is exactly the ancilla-`|1⟩` basis states.** A full basis index `r` lies
in `range (regEmbed fullEnc dataEnc e)` iff its bit-string is `1` on every ancilla wire — the
coordinate subspace with the ancillas held `|1⟩`, whatever the data bits. -/
theorem mem_range_regEmbed_iff (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) (r : Fin D) :
    r ∈ Set.range (regEmbed fullEnc dataEnc e)
      ↔ ∀ rr : Fin n, fullEnc.symm r (e.symm (Sum.inr rr)) = 1 := by
  constructor
  · rintro ⟨s, rfl⟩ rr
    rw [regEmbed, Equiv.symm_apply_apply, regExtend_apply_symm_inr]
  · intro h
    refine ⟨dataEnc (fun j => fullEnc.symm r (e.symm (Sum.inl j))), ?_⟩
    have hext : regExtend e (fun j => fullEnc.symm r (e.symm (Sum.inl j))) = fullEnc.symm r := by
      funext k
      rcases hek : e k with j' | rr
      · have hk : e.symm (Sum.inl j') = k := by rw [← hek, Equiv.symm_apply_apply]
        simp only [regExtend, hek, Sum.elim_inl, hk]
      · have hk : e.symm (Sum.inr rr) = k := by rw [← hek, Equiv.symm_apply_apply]
        simp only [regExtend, hek, Sum.elim_inr]
        rw [← h rr, hk]
    simp only [regEmbed, Equiv.symm_apply_apply, hext, Equiv.apply_symm_apply]

/-- **A fibrewise gate on a data wire preserves the ancilla-`|1⟩` subspace.** For a data wire
`e.symm (Sum.inl j)` and any block family `F`, `wireGate fullEnc (e.symm (Sum.inl j)) F` is
range-preserving (`PreservesRange (regEmbed …)`): a non-zero column entry forces the row's
bit-string to agree with an embedded (ancilla-`|1⟩`) column off the data wire, so its ancilla wires
are all `1`, placing the row in `range (regEmbed …)`. Physically, a gate acting only on a data wire
never touches
the ancillas, so it maps the held subspace to itself — the invariance `compress_mul` needs to be a
monoid homomorphism. -/
theorem preservesRange_wireGate_dataTarget (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) (j : Fin m)
    (F : (Fin M → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :
    PreservesRange (regEmbed fullEnc dataEnc e) (wireGate fullEnc (e.symm (Sum.inl j)) F) := by
  intro s r hr
  rw [wireGate_apply]
  by_cases hcond : ∀ k, k ≠ e.symm (Sum.inl j) →
      fullEnc.symm r k = fullEnc.symm (regEmbed fullEnc dataEnc e s) k
  · refine absurd ((mem_range_regEmbed_iff fullEnc dataEnc e r).mpr fun rr => ?_) hr
    have hne : e.symm (Sum.inr rr) ≠ e.symm (Sum.inl j) :=
      fun he => by simpa using e.symm.injective he
    rw [hcond _ hne]
    simp only [regEmbed, Equiv.symm_apply_apply, regExtend_apply_symm_inr]
  · rw [ite_eq_right hcond]

/-- **The generic data-target compression bridge.** Compressing a full-register fibrewise gate on a
**data** wire `e.symm (Sum.inl j)` to the ancilla-`|1⟩` subspace gives the data-register fibrewise
gate whose block family is `F` read at the extended bit-strings — i.e.
`compress (regEmbed …) (wireGate fullEnc (e.symm (Sum.inl j)) F)` equals
`wireGate dataEnc j (fun x => F (regExtend e x))`.

The fibre condition of the full gate descends to that of the data gate (`forall_ne_regExtend_iff`),
the target-wire bits agree with the data bits (`regExtend_apply_symm_inl`), and the block's fibre
representative pulls back through the extension (`update_regExtend_symm_inl`). This is the core
identity every register-layout bridge is an instance of. -/
theorem compress_wireGate_dataTarget (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) (j : Fin m)
    (F : (Fin M → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :
    compress (regEmbed fullEnc dataEnc e) (wireGate fullEnc (e.symm (Sum.inl j)) F)
      = wireGate dataEnc j (fun x => F (regExtend e x)) := by
  ext x y
  rw [compress_apply, wireGate_apply, wireGate_apply]
  simp only [regEmbed, Equiv.symm_apply_apply]
  set X := dataEnc.symm x with hX
  set Y := dataEnc.symm y with hY
  by_cases hcond : ∀ k, k ≠ j → X k = Y k
  · rw [ite_eq_left ((forall_ne_regExtend_iff e j X Y).mpr hcond), ite_eq_left hcond,
      update_regExtend_symm_inl, regExtend_apply_symm_inl, regExtend_apply_symm_inl]
  · rw [ite_eq_right (fun h => hcond ((forall_ne_regExtend_iff e j X Y).mp h)), ite_eq_right hcond]

/-- **A data-target multiply-controlled single-qubit gate is compressible.** The placement
`mcCtrlSingleQubit fullEnc S (e.symm (Sum.inl j)) g` on a data wire lies in `compressionInvariant`
(it is a `wireGate` on a data wire, so range-preserving) — hence `compressHom` applies to it and to
its products. -/
theorem mcCtrlSingleQubit_dataTarget_mem_compressionInvariant
    (fullEnc : (Fin M → Fin 2) ≃ Fin D) (dataEnc : (Fin m → Fin 2) ≃ Fin d)
    (e : Fin M ≃ Fin m ⊕ Fin n) (S : Finset (Fin M)) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    mcCtrlSingleQubit fullEnc S (e.symm (Sum.inl j)) g
      ∈ compressionInvariant (regEmbed fullEnc dataEnc e) :=
  preservesRange_wireGate_dataTarget fullEnc dataEnc e j _

/-- **Register realisation of a single-qubit gate with ancilla controls** (the dense-axis bridge).
A single-qubit gate `g` placed on a data wire `e.symm (Sum.inl j)` with **all controls on ancilla
wires** (each `k ∈ S` an `e.symm (Sum.inr rr)`, held `|1⟩` in the subspace) compresses to the
uncontrolled single-qubit gate on the data register:
`compress (regEmbed …) (mcCtrlSingleQubit fullEnc S (e.symm (Sum.inl j)) g)` equals
`singleQubitOnWire dataEnc j g`.

The control condition is satisfied throughout the ancilla-`|1⟩` subspace, so the placed gate acts as
the bare block `g` on the data wire. This realises a dense single-qubit axis of the register
universality argument: a doubly-controlled single-qubit gate whose two controls are ancillas held
`|1⟩` acts as the single-qubit gate itself on the data wire. -/
theorem compress_mcCtrlSingleQubit_of_ancilla_controls (fullEnc : (Fin M → Fin 2) ≃ Fin D)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) {S : Finset (Fin M)}
    (hS : ∀ k ∈ S, ∃ rr : Fin n, e k = Sum.inr rr) (j : Fin m) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    compress (regEmbed fullEnc dataEnc e) (mcCtrlSingleQubit fullEnc S (e.symm (Sum.inl j)) g)
      = singleQubitOnWire dataEnc j g := by
  have hcond : ∀ x : Fin m → Fin 2, ∀ k ∈ S, regExtend e x k = 1 := by
    intro x k hk
    obtain ⟨rr, hrr⟩ := hS k hk
    simp only [regExtend, hrr, Sum.elim_inr]
  rw [mcCtrlSingleQubit, compress_wireGate_dataTarget, singleQubitOnWire_eq_wireGate]
  congr 1
  funext x
  exact ite_eq_left (hcond x)

end AxQM.Concrete
