/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.PlacedMultiControlledX

/-!
# Realising a *chosen* `Cᵏ(X)` gate `(S, t)` (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing `Cⁿ(X)`. The recursive Barenco construction bottoms out
into a sequence of multiply-controlled `NOT` gates `Cᵏ(X)` (`k ≤ 2` are exactly the
`Toffoli`/`CNOT`/`NOT` gates), **each addressed to a prescribed control set `S` and target wire
`t`** of the register — the gate `Concrete.mcNot S t` of the classical circuit
`Concrete.mcNotDenote`.

The gate `Evolution.placedMcCtrlX k b σ` realises a `Cᵏ(X)` on the wire set `σ 0, …, σ k` carried
by an explicit wire permutation `σ : Equiv.Perm (Fin (k + 1 + b))`, and `placedMcCtrlX_congr`
proves the gate depends only on the resulting wire data `(Cσ, tσ)`. The combinatorial converse —
*given* a control set `S` and target `t`, build a `σ` that gathers them onto the front block — is
supplied here, and the file reads off the resulting gate's computational-basis truth table as
`Concrete.mcNot S t`, so the classical circuit's gates can each be turned into an `Evolution`.

## What is formalised

* `wireGatherPerm S t hk ht` — the **wire-gather permutation** of `Fin (k + 1 + b)`: for a control
  set `S` with `S.card = k` and a target `t ∉ S`, an `Equiv.Perm` that sends the `k` front control
  wires (`Fin.castAdd b ∘ Fin.castSucc`) onto `S` (in increasing order), the front target wire
  (`Fin.castAdd b (Fin.last k)`) onto `t`, and the remaining `b` wires onto the complement
  `(insert t S)ᶜ`. Built as `Equiv.ofBijective` of the piecewise function `gatherFun` assembled
  from the order embeddings `Finset.orderEmbOfFin` of `S` and of `(insert t S)ᶜ`.
* `wireGatherPerm_castAdd_last`, `wireGatherPerm_image_cnxControls` — the two **gather properties**:
  the front target wire maps to `t`, and the image of the `k` front control wires `cnxControls k`
  under `σ ∘ Fin.castAdd b` is exactly `S`. These are precisely the hypotheses
  `placedMcCtrlX_evolvePure_qubitBasis` reads its control set / target off of.
* `placedMcCtrlX_wireGather_evolvePure_qubitBasis` — the **payoff**: the placed gate
  `Evolution.placedMcCtrlX k b (wireGatherPerm S t hk ht)` acts on the computational product basis
  `⨂ₖ |c k⟩` exactly as the classical gate `Concrete.mcNot S t`. So a `Cᵏ(X)` addressed to *any*
  prescribed `(S, t)` (with `|S| = k`, `t ∉ S`) is realised as a genuine closed-system `Evolution`
  on the `(k+1+b)`-wire qubit register with the intended truth table — the per-gate realisation the
  circuit assembly composes.

Two general facts about the control-wire set `cnxControls` used here —
`mem_cnxControls` (membership is `(j : ℕ) < k`) and `cnxControls_eq_image_castSucc`
(`cnxControls k = Finset.univ.image Fin.castSucc`, the front `k` wires as the `Fin.castSucc`
image) — are proved next to the `cnxControls` definition in
`AxQM/Core/MultiControlledNotBasis.lean`.

## Design notes

* **Why the register is `Fin (k + 1 + b)`, not `Fin m`.** `Evolution.placedMcCtrlX k b σ` lives on
  `qubit ^⊗ₛ (k + 1 + b)` by construction, so the gather and its truth table are stated on that
  same register — no `cast`. A circuit's gates have *varying* control arity `kᵢ = |Sᵢ| ∈ {0, 1, 2}`,
  so a gate on a fixed ambient register `Fin m` has `kᵢ + 1 + bᵢ = m` only *propositionally*;
  reconciling the per-gate register `Fin (kᵢ + 1 + bᵢ)` with the common `Fin m` is the *separate*
  register-cast step (`QSystem.tensorPowCongr`), applied where the gates are composed.
  The gather here is kept free of that cast.
* **Why `Equiv.ofBijective` of a piecewise `gatherFun`.** The three domain blocks — the `k` front
  controls, the front target, the `b` back wires — map to the three *disjoint* codomain finsets
  `S`, `{t}`, `(insert t S)ᶜ` (a partition, since `|S| = k`, `t ∉ S`, `|(insert t S)ᶜ| = b`).
  Injectivity is a `Fin.addCases`/`Fin.lastCases` case analysis whose cross-block cases are closed
  by disjointness (`Finset.orderEmbOfFin_mem` places each value in its block, and the blocks are
  pairwise disjoint) and whose same-block cases are the injectivity of the order embeddings; on a
  finite type injective ⇒ bijective (`Finite.injective_iff_bijective`). Using `Finset.orderEmbOfFin`
  (whose values enumerate `S`) makes both the membership facts one-liners and the image equation
  `Finset.univ.image (S.orderEmbOfFin hk) = S` exactly `Finset.image_orderEmbOfFin_univ`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {k b : ℕ}

/-- The complement `(insert t S)ᶜ` of the gate's support has exactly `b` wires (the number of
ambient wires the placed gate acts on as identity): `|(insert t S)ᶜ| = (k+1+b) - (k+1) = b`, using
`|insert t S| = |S| + 1 = k + 1` (as `t ∉ S`). -/
theorem card_compl_insert (S : Finset (Fin (k + 1 + b))) (t : Fin (k + 1 + b))
    (hk : S.card = k) (ht : t ∉ S) : (insert t S)ᶜ.card = b := by
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem ht, hk]; omega

/-- The piecewise **gather function** on `Fin (k + 1 + b)` underlying `wireGatherPerm`: send the
front control wires `Fin.castAdd b (Fin.castSucc i)` to the `i`-th element of `S` (in increasing
order, `S.orderEmbOfFin`), the front target wire `Fin.castAdd b (Fin.last k)` to `t`, and the back
wires `Fin.natAdd (k+1) j` to the `j`-th element of the complement `(insert t S)ᶜ`. -/
def gatherFun (S : Finset (Fin (k + 1 + b))) (t : Fin (k + 1 + b))
    (hk : S.card = k) (ht : t ∉ S) : Fin (k + 1 + b) → Fin (k + 1 + b) :=
  Fin.addCases
    (fun y => Fin.lastCases (motive := fun _ => Fin (k + 1 + b)) t
      (fun i => S.orderEmbOfFin hk i) y)
    (fun j => (insert t S)ᶜ.orderEmbOfFin (card_compl_insert S t hk ht) j)

variable (S : Finset (Fin (k + 1 + b))) (t : Fin (k + 1 + b)) (hk : S.card = k) (ht : t ∉ S)

/-- `gatherFun` on a front control wire `Fin.castAdd b (Fin.castSucc i)` is the `i`-th element of
`S`. -/
theorem gatherFun_castAdd_castSucc (i : Fin k) :
    gatherFun S t hk ht (Fin.castAdd b (Fin.castSucc i)) = S.orderEmbOfFin hk i := by
  simp only [gatherFun, Fin.addCases_left, Fin.lastCases_castSucc]

/-- `gatherFun` on the front target wire `Fin.castAdd b (Fin.last k)` is the target `t`. -/
theorem gatherFun_castAdd_last :
    gatherFun S t hk ht (Fin.castAdd b (Fin.last k)) = t := by
  simp only [gatherFun, Fin.addCases_left, Fin.lastCases_last]

/-- `gatherFun` on a back wire `Fin.natAdd (k+1) j` is the `j`-th element of the complement. -/
theorem gatherFun_natAdd (j : Fin b) :
    gatherFun S t hk ht (Fin.natAdd (k + 1) j)
      = (insert t S)ᶜ.orderEmbOfFin (card_compl_insert S t hk ht) j := by
  simp only [gatherFun, Fin.addCases_right]

/-- **`gatherFun` is injective.** Its three domain blocks (front controls, front target, back
wires) map to the three disjoint finsets `S`, `{t}`, `(insert t S)ᶜ`; a
`Fin.addCases`/`Fin.lastCases` case analysis closes cross-block cases by disjointness and same-block
cases by the injectivity of the order embeddings. -/
theorem gatherFun_injective : Function.Injective (gatherFun S t hk ht) := by
  have hAmem : ∀ i, S.orderEmbOfFin hk i ∈ S := fun i => Finset.orderEmbOfFin_mem S hk i
  have hCmem : ∀ j, (insert t S)ᶜ.orderEmbOfFin (card_compl_insert S t hk ht) j ∈ (insert t S)ᶜ :=
    fun j => Finset.orderEmbOfFin_mem _ _ j
  intro x y hxy
  induction x using Fin.addCases with
  | left xl =>
    induction xl using Fin.lastCases with
    | last =>
      induction y using Fin.addCases with
      | left yl =>
        induction yl using Fin.lastCases with
        | last => rfl
        | cast yi =>
          rw [gatherFun_castAdd_last, gatherFun_castAdd_castSucc] at hxy
          exact absurd (hxy ▸ hAmem yi) ht
      | right yj =>
        rw [gatherFun_castAdd_last, gatherFun_natAdd] at hxy
        have hy := hCmem yj
        rw [Finset.mem_compl, Finset.mem_insert, not_or] at hy
        exact absurd hxy.symm hy.1
    | cast xi =>
      induction y using Fin.addCases with
      | left yl =>
        induction yl using Fin.lastCases with
        | last =>
          rw [gatherFun_castAdd_castSucc, gatherFun_castAdd_last] at hxy
          exact absurd (hxy ▸ hAmem xi) ht
        | cast yi =>
          rw [gatherFun_castAdd_castSucc, gatherFun_castAdd_castSucc] at hxy
          have := (S.orderEmbOfFin hk).injective hxy
          rw [this]
      | right yj =>
        rw [gatherFun_castAdd_castSucc, gatherFun_natAdd] at hxy
        have hx : S.orderEmbOfFin hk xi ∈ S := hAmem xi
        have hy := hCmem yj
        rw [Finset.mem_compl, Finset.mem_insert, not_or] at hy
        exact absurd (hxy ▸ hx) hy.2
  | right xj =>
    induction y using Fin.addCases with
    | left yl =>
      induction yl using Fin.lastCases with
      | last =>
        rw [gatherFun_natAdd, gatherFun_castAdd_last] at hxy
        have hx := hCmem xj
        rw [Finset.mem_compl, Finset.mem_insert, not_or] at hx
        exact absurd hxy hx.1
      | cast yi =>
        rw [gatherFun_natAdd, gatherFun_castAdd_castSucc] at hxy
        have hy : S.orderEmbOfFin hk yi ∈ S := hAmem yi
        have hx := hCmem xj
        rw [Finset.mem_compl, Finset.mem_insert, not_or] at hx
        exact absurd (hxy.symm ▸ hy) hx.2
    | right yj =>
      rw [gatherFun_natAdd, gatherFun_natAdd] at hxy
      have := ((insert t S)ᶜ.orderEmbOfFin (card_compl_insert S t hk ht)).injective hxy
      rw [this]

/-- **The wire-gather permutation** of `Fin (k + 1 + b)` for a control set `S` (`S.card = k`) and
target `t ∉ S`: the bijectivisation of `gatherFun`. It gathers the `k` front control wires onto
`S`, the front target wire onto `t`, and the `b` back wires onto `(insert t S)ᶜ` — the permutation
to feed into `Evolution.placedMcCtrlX` to place a `Cᵏ(X)` on the prescribed wires `(S, t)`. -/
def wireGatherPerm : Equiv.Perm (Fin (k + 1 + b)) :=
  Equiv.ofBijective (gatherFun S t hk ht)
    (Finite.injective_iff_bijective.mp (gatherFun_injective S t hk ht))

/-- `wireGatherPerm` applies as its underlying `gatherFun` (definitional). -/
theorem wireGatherPerm_apply (x : Fin (k + 1 + b)) :
    wireGatherPerm S t hk ht x = gatherFun S t hk ht x := rfl

/-- **Target gather property**: `wireGatherPerm` sends the front target wire
`Fin.castAdd b (Fin.last k)` to the prescribed target `t`. This is the target
`placedMcCtrlX_evolvePure_qubitBasis` reads off the placed gate. -/
theorem wireGatherPerm_castAdd_last :
    wireGatherPerm S t hk ht (Fin.castAdd b (Fin.last k)) = t := by
  rw [wireGatherPerm_apply, gatherFun_castAdd_last]

/-- **Controls gather property**: the image of the `k` front control wires `cnxControls k` under
`wireGatherPerm ∘ Fin.castAdd b` is exactly the prescribed control set `S`. This is the control set
`placedMcCtrlX_evolvePure_qubitBasis` reads off the placed gate. Proved by reindexing
`cnxControls k` as `Finset.univ.image Fin.castSucc`, evaluating the gather on each front control
wire to the matching element of `S`, and closing with `Finset.image_orderEmbOfFin_univ` (the order
embedding of `S` enumerates `S`). -/
theorem wireGatherPerm_image_cnxControls :
    (cnxControls k).image (fun j => wireGatherPerm S t hk ht (Fin.castAdd b j)) = S := by
  simp only [cnxControls_eq_image_castSucc, Finset.image_image, Function.comp_def,
    wireGatherPerm_apply, gatherFun_castAdd_castSucc]
  exact Finset.image_orderEmbOfFin_univ S hk

/-- **Computational-basis truth table of the `(S, t)`-addressed `Cᵏ(X)`.** Placing the `Cᵏ(X)` gate
on the wires gathered by `wireGatherPerm S t hk ht` yields a gate whose action on the computational
product basis `⨂ₖ |c k⟩` is exactly the classical multiply-controlled `NOT` `Concrete.mcNot S t`:
`placedMcCtrlX k b (wireGatherPerm S t hk ht) (⨂ₖ |c k⟩) = ⨂ₖ |mcNot S t c k⟩`.

So a `Cᵏ(X)` addressed to *any* prescribed control set `S` (`|S| = k`) and target `t ∉ S` is
realised as a genuine closed-system `Evolution` on the `(k+1+b)`-wire qubit register with the
intended truth table — the per-gate realisation the `O(n²)` circuit assembly composes (each gate of
`Concrete.mcNotDenote`). Immediate from `placedMcCtrlX_evolvePure_qubitBasis` once the
placed gate's control set and target are rewritten to `S` and `t` by the two gather properties. -/
theorem placedMcCtrlX_wireGather_evolvePure_qubitBasis (c : Fin (k + 1 + b) → Fin 2) :
    (Evolution.placedMcCtrlX k b (wireGatherPerm S t hk ht)).evolvePure
        (PureState.piTensor fun i => qubitBasis (c i))
      = PureState.piTensor fun i => qubitBasis (Concrete.mcNot S t c i) := by
  rw [placedMcCtrlX_evolvePure_qubitBasis, wireGatherPerm_image_cnxControls,
    wireGatherPerm_castAdd_last]

end AxQM
