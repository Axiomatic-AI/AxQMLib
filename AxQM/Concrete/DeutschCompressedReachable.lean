/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RegisterCompressionBridgeAncilla
import AxQM.Concrete.DeutschWirePlacement
import AxQM.Concrete.DeutschWireUniversality

/-!
# Concrete: the single-qubit gates the Deutsch gate reaches on a data wire, from compressed
`G`-placements (matrix level, N&C Ex 4.44)

Every statement is about matrices: the multiply-controlled single-qubit wire gate
`mcCtrlSingleQubit`, the uncontrolled wire gate `singleQubitOnWire`, the coordinate-subspace
compression `compress`, the placed Deutsch iterates `deutschWirePlacedReachable`, the Deutsch
single-qubit submonoid `deutschWireGateSubmonoid`, and the phase gate `sMatrix`, together with the
register-layout equivalences of `Concrete/RegisterCompressionBridge.lean`.

## Realising `G`'s single-qubit gates as compressed `G`-placements

The universality density core `exists_phase_smul_mem_closure_deutschReachableCircuits`
(`Concrete/DeutschReachableCircuits.lean`) states that the circuits assembled from the *abstract*
gate set `deutschReachableGateSet dataEnc α` are dense in `U(2ⁿ)` up to a global phase. That set's
single-qubit generators are `singleQubitOnWire dataEnc j g` with `g ∈ deutschWireGateSubmonoid α` —
the single-qubit gates the Deutsch gate `G = C²(iR_x(πα))` reaches on a wire. The **honest
realisation** of those gates from `G` uses control ancillas: place `G` on register wires with the
ancilla wires held `|1⟩` and read off the action on the data register — the coordinate-subspace
compression `compress ι M = M.submatrix ι ι` to the ancilla-`|1⟩` subspace picked out by
`ι = regEmbed fullEnc dataEnc e` (`Concrete/RegisterCompressionBridge.lean`).

This file assembles that realisation for the **single-qubit half**. It collects the `G`-placements
that both are reachable from `G` and preserve the ancilla-`|1⟩` subspace into a submonoid `M`
(`deutschAncillaReachableCircuits`), compresses it to the data register
(`deutschDataReachableCircuits`, a submonoid because `compress` is a monoid homomorphism on the
range-preserving matrices), and shows
that *every* single-qubit gate `singleQubitOnWire dataEnc j g` with `g ∈ deutschWireGateSubmonoid α`
lies in that compressed submonoid — i.e. is the data-register action of an actual `G`-placement
circuit with ancillas.

## The construction and results

Fix a full-register encoding `fullEnc`, a data-register encoding `dataEnc`, a wire-splitting
`e : Fin M ≃ Fin m ⊕ Fin n` (data wires `Sum.inl`, ancilla wires `Sum.inr`), and two distinct
ancilla wires `a₀ ≠ a₁`.

* `deutschAncillaReachableGates fullEnc dataEnc e α` — the `G`-placement circuits that (a) preserve
  the ancilla-`|1⟩` subspace (`compressionInvariant ι`) and (b) are reachable from `G` on some three
  register wires (`closure (deutschWirePlacedReachable fullEnc a b j α)`); and
  `deutschAncillaReachableCircuits`, the submonoid they generate.
* `deutschAncillaReachableCircuits_le_compressionInvariant` — that submonoid preserves the subspace,
  so `compress` is a monoid homomorphism on it.
* `deutschDataReachableCircuits fullEnc dataEnc e α` — the compressed data-register image
  `compress ι '' M`, a submonoid (identity via `compress_one`, products via `compress_mul`).
* `singleQubitOnWire_mem_deutschDataReachableCircuits` — **the single-qubit realisation** (`α`
  irrational): every `singleQubitOnWire dataEnc j g` with `g ∈ deutschWireGateSubmonoid α` lies in
  `deutschDataReachableCircuits`. The dense `x`-axis orbit blocks come from an ancilla-controlled
  data-target placement (`compress_mcCtrlSingleQubit_of_ancilla_controls`), the phase gate `S` from
  the controlled global phase `C(i · I)` with the target on a throwaway ancilla and one control on
  the data wire (`compress_mcCtrlSingleQubit_smul_one_ancillaTarget_eq_sMatrix`), and `S†` as `S³`
  (`sMatrix.conjTranspose = S · S · S`, so it needs no extra placement); the submonoid structure
  handles products and the identity via `Submonoid.closure_induction`.

The reversible generators (`IsToffoliPermGate`) and the transfer of the density core through this
compressed submonoid are the concern of the sibling file that consumes this one; together they lift
the abstract density core to the honest statement that the data-register actions of `G`-placement
circuits are dense in `U(2ⁿ)` up to a global phase.
-/

namespace AxQM.Concrete

open Matrix

variable {M m n D d : ℕ} (fullEnc : (Fin M → Fin 2) ≃ Fin D)
  (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n)

/-- **The reachable, ancilla-preserving `G`-placement gate set.** A full-register matrix `N` is a
member when it (a) preserves the ancilla-`|1⟩` coordinate subspace `range (regEmbed …)`
(`compressionInvariant`), so its data-register action is well defined, and (b) is reachable from the
Deutsch gate `G = C²(iR_x(πα))` placed on some three register wires `a, b, j`
(`closure (deutschWirePlacedReachable fullEnc a b j α)`). These are the elementary `G`-placement
circuits whose compressions realise the single-qubit / reversible generators of the universality
density core. -/
noncomputable def deutschAncillaReachableGates (α : ℝ) : Set (Matrix (Fin D) (Fin D) ℂ) :=
  {N | N ∈ compressionInvariant (regEmbed fullEnc dataEnc e) ∧
    ∃ a b j : Fin M, N ∈ closure (deutschWirePlacedReachable fullEnc a b j α)}

/-- **The reachable, ancilla-preserving `G`-placement circuits** — the submonoid generated by
`deutschAncillaReachableGates`, i.e. the finite products of reachable ancilla-preserving
`G`-placements. Its compression to the data register (`deutschDataReachableCircuits`) collects the
data-register actions of the `G`-placement circuits with ancillas held `|1⟩`. -/
noncomputable def deutschAncillaReachableCircuits (α : ℝ) : Submonoid (Matrix (Fin D) (Fin D) ℂ) :=
  Submonoid.closure (deutschAncillaReachableGates fullEnc dataEnc e α)

/-- The reachable `G`-placement circuits all preserve the ancilla-`|1⟩` subspace: every generator
does (by definition), and `compressionInvariant` is a submonoid, so `Submonoid.closure_le` lifts the
membership to the whole submonoid. This is what makes `compress` a monoid homomorphism on it. -/
theorem deutschAncillaReachableCircuits_le_compressionInvariant (α : ℝ) :
    deutschAncillaReachableCircuits fullEnc dataEnc e α
      ≤ compressionInvariant (regEmbed fullEnc dataEnc e) :=
  Submonoid.closure_le.2 fun _ hN => hN.1

/-- **The compressed data-register circuits reachable from `G`.** The image
`compress ι '' (deutschAncillaReachableCircuits …)` of the reachable ancilla-preserving
`G`-placement circuits under the compression to the data register, as a submonoid: it contains the
identity (`compress ι 1 = 1`, `compress_one`) and is closed under products (`compress_mul`, whose
range-preservation hypothesis holds because the circuits lie in `compressionInvariant`). Its members
are exactly the data-register actions of `G`-placement circuits with the ancillas held `|1⟩`. -/
noncomputable def deutschDataReachableCircuits (α : ℝ) : Submonoid (Matrix (Fin d) (Fin d) ℂ) where
  carrier := compress (regEmbed fullEnc dataEnc e) ''
    ↑(deutschAncillaReachableCircuits fullEnc dataEnc e α)
  one_mem' := ⟨1, one_mem _, compress_one (regEmbed_injective fullEnc dataEnc e)⟩
  mul_mem' := by
    rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    exact ⟨A * B, mul_mem hA hB,
      compress_mul (regEmbed_injective fullEnc dataEnc e) A
        (deutschAncillaReachableCircuits_le_compressionInvariant fullEnc dataEnc e α hB)⟩

/-- **The single-qubit gates the Deutsch gate reaches on a data wire are compressed `G`-placements**
(Nielsen & Chuang, Exercise 4.44, single-qubit half). When `α` is irrational, for every data wire
`j` and every `g ∈ deutschWireGateSubmonoid α`, the uncontrolled single-qubit gate
`singleQubitOnWire dataEnc j g` lies in `deutschDataReachableCircuits` — it is the data-register
action of a `G`-placement circuit with the ancillas held `|1⟩`.

The submonoid `deutschWireGateSubmonoid α` is generated by the dense `x`-axis orbit
`deutschTargetOrbit α` together with the phase gate `S = sMatrix` and its adjoint `S†`; the claim is
proved by `Submonoid.closure_induction` over these generators:

* an orbit block `g₀` is placed on the data wire `j` with both controls on the ancillas `a₀, a₁`
  held `|1⟩`; the placement is a *forward* Deutsch iterate (a data-target gate, hence
  ancilla-preserving), and compresses to `singleQubitOnWire dataEnc j g₀`
  (`compress_mcCtrlSingleQubit_of_ancilla_controls`);
* the phase gate `S` is the controlled global phase `C(i · I)` — place `G` with the target on the
  throwaway ancilla `a₁`, one control on the ancilla `a₀` held `|1⟩`, the other control on the data
  wire `j`; the placement is diagonal (hence ancilla-preserving) and reachable (`i · I` is a closure
  limit of the orbit), and compresses to `singleQubitOnWire dataEnc j sMatrix`
  (`compress_mcCtrlSingleQubit_smul_one_ancillaTarget_eq_sMatrix`);
* `S† = S³` (`sMatrix_conjTranspose_eq_mul_self_mul_self`, `S = diag(1, i)` so
  `S³ = diag(1, -i) = S†`), a product of the `S` case;
* the identity and products close under the submonoid structure (`singleQubitOnWire` is a monoid
  homomorphism, `singleQubitOnWire_one` / `singleQubitOnWire_mul`).

This is the single-qubit half of the realisation of the Deutsch gate's gates with ancillas. -/
theorem singleQubitOnWire_mem_deutschDataReachableCircuits {α : ℝ} (hα : Irrational α)
    (a₀ a₁ : Fin n) (ha : a₀ ≠ a₁) (j : Fin m) {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g ∈ deutschWireGateSubmonoid α) :
    singleQubitOnWire dataEnc j g ∈ deutschDataReachableCircuits fullEnc dataEnc e α := by
  -- The dense `x`-axis: an orbit block placed on data wire `j` with both controls on ancillas.
  have hOrbit : ∀ g₀ ∈ deutschTargetOrbit α,
      singleQubitOnWire dataEnc j g₀ ∈ deutschDataReachableCircuits fullEnc dataEnc e α := by
    intro g₀ hg₀
    have hplace : mcCtrlSingleQubit fullEnc {e.symm (Sum.inr a₀), e.symm (Sum.inr a₁)}
        (e.symm (Sum.inl j)) g₀ ∈ deutschAncillaReachableCircuits fullEnc dataEnc e α := by
      apply Submonoid.subset_closure
      exact ⟨mcCtrlSingleQubit_dataTarget_mem_compressionInvariant fullEnc dataEnc e _ j g₀,
        e.symm (Sum.inr a₀), e.symm (Sum.inr a₁), e.symm (Sum.inl j),
        subset_closure (Set.mem_image_of_mem _ hg₀)⟩
    have hcomp : compress (regEmbed fullEnc dataEnc e)
        (mcCtrlSingleQubit fullEnc {e.symm (Sum.inr a₀), e.symm (Sum.inr a₁)}
          (e.symm (Sum.inl j)) g₀) = singleQubitOnWire dataEnc j g₀ := by
      apply compress_mcCtrlSingleQubit_of_ancilla_controls
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk'
      · exact ⟨a₀, e.apply_symm_apply _⟩
      · rw [Finset.mem_singleton] at hk'; subst hk'; exact ⟨a₁, e.apply_symm_apply _⟩
    rw [← hcomp]
    exact ⟨_, hplace, rfl⟩
  -- The phase gate `S`: the controlled global phase `C(i · I)` with a data-wire control.
  have hSgen : singleQubitOnWire dataEnc j sMatrix
      ∈ deutschDataReachableCircuits fullEnc dataEnc e α := by
    have htgt : e.symm (Sum.inr a₁) ∉
        ({e.symm (Sum.inr a₀), e.symm (Sum.inl j)} : Finset (Fin M)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha.symm (Sum.inr_injective (e.symm.injective h)),
        fun h => Sum.inr_ne_inl (e.symm.injective h)⟩
    have hplace : mcCtrlSingleQubit fullEnc {e.symm (Sum.inr a₀), e.symm (Sum.inl j)}
        (e.symm (Sum.inr a₁)) (Complex.I • 1)
        ∈ deutschAncillaReachableCircuits fullEnc dataEnc e α := by
      apply Submonoid.subset_closure
      exact ⟨mcCtrlSingleQubit_smul_one_mem_compressionInvariant fullEnc dataEnc e _ htgt Complex.I,
        e.symm (Sum.inr a₀), e.symm (Sum.inl j), e.symm (Sum.inr a₁),
        mcCtrlSingleQubit_iScalar_mem_closure_deutschWirePlacedReachable hα fullEnc _ _ _⟩
    rw [← compress_mcCtrlSingleQubit_smul_one_ancillaTarget_eq_sMatrix fullEnc dataEnc e a₀ a₁ ha j]
    exact ⟨_, hplace, rfl⟩
  -- Induction over the generators of `deutschWireGateSubmonoid α`.
  have hg' : g ∈ Submonoid.closure (deutschTargetOrbit α ∪ {sMatrix, sMatrix.conjTranspose}) := hg
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hOrbit x hx
    · rcases hx with rfl | hx
      · exact hSgen
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        -- `S† = S³`, a product of the phase-gate case.
        rw [sMatrix_conjTranspose_eq_mul_self_mul_self, ← singleQubitOnWire_mul,
          ← singleQubitOnWire_mul]
        exact mul_mem (mul_mem hSgen hSgen) hSgen
  | one => rw [singleQubitOnWire_one]; exact one_mem _
  | mul x y _ _ ihx ihy => rw [← singleQubitOnWire_mul]; exact mul_mem ihx ihy

end AxQM.Concrete
