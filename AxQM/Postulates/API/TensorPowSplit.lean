/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.PiTensor
import AxQM.Postulates.PiTensorState
import AxQM.Postulates.API.SystemIsoComm

/-!
# AxQM.Postulates.API — splitting a tensor power into factor blocks

**System isomorphisms** regrouping the `n`-fold symmetric tensor power `S ^⊗ₛ n` into
sub-blocks of factors:

* the "`succ`" **head-peel** `S ^⊗ₛ (n+1) ≃ₛ S ⊗ (S ^⊗ₛ n)`, splitting off the single head wire —
  the tensor-power analogue of `QSystem.binaryPiEquiv`, matching the head-prepend recursion of the
  right-nested control register `qtower (n+1) S = S ⊗ qtower n S` (`Core/MultiControlledReduction`);
* its **general-arity** form `S ^⊗ₛ (a+b) ≃ₛ (S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)` at an arbitrary block boundary
  `a + b` (the head-peel is the `a = 1` case, up to the singleton collapse) — used
  for placing a gate on a contiguous block of wires (via `Evolution.onLeft` across the split);
* the **factor relabelling** `S ^⊗ₛ a ≃ₛ S ^⊗ₛ b` induced by any reindexing `e : Fin a ≃ Fin b`
  (which forces `a = b`) — the register cast that identifies two tensor powers of propositionally
  equal arity, so gates whose control-arity varies (a placed `Cᵏ(X)`, `k + 1 + b = m`) compose on
  one fixed register.

## What is formalised

* `QSystem.tensorPowSuccHead S n` — the head-peel isomorphism `S ^⊗ₛ (n+1) ≃ₛ S ⊗ (S ^⊗ₛ n)`,
  built from the inner-product `PiTensorProduct` isometries of `ToMathlib`: reindex `Fin (n+1)` as
  `Fin 1 ⊕ Fin n` (`reindexₗᵢ`), split the tensor along the `Sum` (`tmulEquivDepₗᵢ`), and collapse
  the singleton head factor `⨂ᵢ : Fin 1, S.space ≃ S.space` (`subsingletonEquivₗᵢ`).
* `QSystem.tensorPowSuccHead_toIsometry_tprod` — its **action on a product state**:
  `⨂ᵢ |fᵢ⟩ ↦ |f 0⟩ ⊗ (⨂ⱼ |f j.succ⟩)`, the head factor split off from the tail.
* `QSystem.tensorPowSuccHead_symm_toIsometry_tmul_tprod` — the inverse **cons** action:
  `|a⟩ ⊗ (⨂ⱼ |bⱼ⟩) ↦ ⨂ᵢ |(Fin.cons a b) i⟩`, prepending a head wire to a tail register.
* `QSystem.tensorPowOne S` — the one-factor collapse `S ≃ₛ S ^⊗ₛ 1` (the `n = 0` base of the
  `qtower`-bridge induction), from the subsingleton-index isometry
  `PiTensorProduct.subsingletonEquivₗᵢ`; its action on a vector is `v ↦ ⨂ᵢ v`
  (`QSystem.tensorPowOne_toIsometry_apply`).
* `QSystem.blockSplit a b` — the index split `Fin (a+b) ≃ Fin a ⊕ Fin b` (`finSumFinEquiv.symm`)
  underlying the block isomorphism, with its inverse `QSystem.blockSplit_symm`.
* `QSystem.tensorPowAdd S a b` — the **general block-split isomorphism**
  `S ^⊗ₛ (a+b) ≃ₛ (S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)`, grouping the first `a` factors into the left block and
  the last `b` into the right; built by reindexing along `QSystem.blockSplit a b` then the
  `Sum`-split `tmulEquivDepₗᵢ` (no singleton collapse — neither block is forced to be one factor).
* `QSystem.tensorPowAdd_toIsometry_tprod` — its **action on a product state**:
  `⨂ₖ |fₖ⟩ ↦ (⨂ᵢ |f (Fin.castAdd b i)⟩) ⊗ (⨂ⱼ |f (Fin.natAdd a j)⟩)`, the two blocks read off the
  first `a` and last `b` wires.
* `QSystem.tensorPowAdd_symm_toIsometry_tmul_tprod` — the inverse **append** action:
  `(⨂ᵢ |uᵢ⟩) ⊗ (⨂ⱼ |vⱼ⟩) ↦ ⨂ₖ |(Fin.append u v) k⟩`, concatenating a length-`a` and a length-`b`
  block into one `(a+b)`-fold register.
* `QSystem.tensorPowCongr S e` — the **factor-relabelling isomorphism** `S ^⊗ₛ a ≃ₛ S ^⊗ₛ b` induced
  by a wire reindexing `e : Fin a ≃ Fin b`, the **constant-family case of the indexed reindex**
  `QSystem.piTensorReindex` (a thin named wrapper for the register-cast role), with product action
  `QSystem.tensorPowCongr_toIsometry_tprod` (`⨂ᵢ |fᵢ⟩ ↦ ⨂ⱼ |f (e.symm j)⟩`) and its two
  product-pure-state dictionaries `QSystem.tensorPowCongr_congr_piTensor`
  (`⨂ₚ ᵢ ψ i ↦ ⨂ₚ ⱼ ψ (e.symm j)`, the constant-family case of
  `PureState.piTensor_congr_piTensorReindex`) and `QSystem.tensorPowCongr_symm_congr_piTensor`
  (`⨂ₚ ⱼ φ j ↦ ⨂ₚ ᵢ φ (e i)`). Unlike the block splits it does **not** regroup — same system, same
  factor count, only the wire labelling changes — so it is the general-arity companion of the
  wire-permutation gate `Evolution.permWires` (the `a = b`, `e : Equiv.Perm (Fin a)` case).

## Design notes

* **Use in Exercise 4.29.** Connecting the `SWAP`-network wire-permutation gate
  `Evolution.permWires` (defined on the *symmetric* `S ^⊗ₛ n`, in
  `AxQM/Postulates/API/WirePermutation.lean`) to the multiply-controlled `NOT` `mcCtrl n pauliXGate`
  (defined on the *right-nested* tower `qtower n qubit`) requires an isomorphism
  `qtower n qubit ≃ₛ qubit ^⊗ₛ (n+1)`. That isomorphism is an induction whose single step is exactly
  the head-peel isomorphism (`qtower (n+1) qubit = qubit ⊗ qtower n qubit`, and
  `qubit ⊗ (qubit ^⊗ₛ n) ≃ₛ qubit ^⊗ₛ (n+1)`; see `AxQM/Core/QtowerTensorPow.lean`). Likewise
  `tensorPowAdd` is what places a Toffoli/`CNOT` on a **block** of `k+1` wires,
  `G.onLeft (S ^⊗ₛ b)` transported across `(tensorPowAdd S a b).symm`, before it is relabelled by
  `permWires` (see `AxQM/Postulates/API/BlockGatePlacement.lean`).
* **Why the `Fin _ ⊕ Fin _` route.** `S ^⊗ₛ n` is the symmetric `PiTensorProduct` over `Fin n`;
  re-indexing it along a `Fin _ ⊕ Fin _` split (`QSystem.headSplit : Fin (n+1) ≃ Fin 1 ⊕ Fin n`,
  head `0 ↦ inl 0`, `j.succ ↦ inr j`; or `QSystem.blockSplit : Fin (a+b) ≃ Fin a ⊕ Fin b`) puts it
  in the shape the `Sum`-split isometry `tmulEquivDepₗᵢ` (and, for the head-peel, the
  singleton-collapse `subsingletonEquivₗᵢ`) consume — the same assembly pattern as
  `QSystem.binaryPiIsometry`.
* **Symbolic-boundary elaboration hazards.** At the *symbolic* boundary `a + b` (absent at the
  numeral `n + 1` of the head-peel) the block-split isometry hits two `whnf`/`isDefEq` timeouts,
  handled by: keeping the index split a **named** def (`QSystem.blockSplit`) so the `.trans` type
  unification treats it opaquely (an inline `finSumFinEquiv.symm` is eagerly unfolded and loops); an
  explicit constant-family codomain ascription on the `reindexₗᵢ` step; and a documented, localized
  `maxHeartbeats` bump on the `QSystem.Iso ⟨⟩` wrap, whose defeq unfolds `piTensor.space` at `a + b`
  (heavy but finite — a plain defeq, not a loop).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem} {n : ℕ}

/-! ### The index split `Fin (n+1) ≃ Fin 1 ⊕ Fin n` -/

/-- The index reshuffle `Fin (n + 1) ≃ Fin 1 ⊕ Fin n` underlying the head-peel isometry: the head
`0` maps to `Sum.inl 0` and each `j.succ` to `Sum.inr j` (see `QSystem.headSplit_symm_inl` /
`QSystem.headSplit_symm_inr`). Built from `finSumFinEquiv` after commuting `n + 1 = 1 + n`. -/
def QSystem.headSplit (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n :=
  (finCongr (Nat.add_comm n 1)).trans finSumFinEquiv.symm

@[simp] theorem QSystem.headSplit_symm_inl (n : ℕ) :
    (QSystem.headSplit n).symm (Sum.inl 0) = (0 : Fin (n + 1)) := by
  simp only [QSystem.headSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm,
    finCongr_apply]
  ext
  simp only [finSumFinEquiv_apply_left, Fin.val_cast, Fin.val_castAdd, Fin.val_zero]

@[simp] theorem QSystem.headSplit_symm_inr (n : ℕ) (j : Fin n) :
    (QSystem.headSplit n).symm (Sum.inr j) = j.succ := by
  simp only [QSystem.headSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm,
    finCongr_apply]
  ext
  simp only [finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
  omega

/-! ### The head-peel isometry and system isomorphism -/

/-- The head-peel isometry `(S ^⊗ₛ (n+1)).space ≃ₗᵢ (S ⊗ S ^⊗ₛ n).space`: reindex the
factors along `QSystem.headSplit`, split off the `Sum` with `tmulEquivDepₗᵢ`, and collapse the
singleton head factor with `subsingletonEquivₗᵢ`. -/
noncomputable def QSystem.tensorPowSuccHeadIsometry (S : QSystem) (n : ℕ) :
    (⨂[ℂ] _ : Fin (n + 1), S.space) ≃ₗᵢ[ℂ] S.space ⊗[ℂ] (⨂[ℂ] _ : Fin n, S.space) :=
  (PiTensorProduct.reindexₗᵢ ℂ (fun _ : Fin (n + 1) => S.space) (QSystem.headSplit n)).trans
    ((PiTensorProduct.tmulEquivDepₗᵢ ℂ (fun _ : Fin 1 ⊕ Fin n => S.space)).symm.trans
      (TensorProduct.congrIsometry
        (PiTensorProduct.subsingletonEquivₗᵢ ℂ (fun _ : Fin 1 => S.space) 0)
        (LinearIsometryEquiv.refl ℂ (⨂[ℂ] _ : Fin n, S.space))))

/-- **The head-peel system isomorphism** `S ^⊗ₛ (n+1) ≃ₛ S ⊗ (S ^⊗ₛ n)`: split the `(n+1)`-fold
tensor power into its head wire and the remaining `n`-fold power. The tensor-power `succ`
structural conversion, matching `qtower (n+1) S = S ⊗ qtower n S`. -/
def QSystem.tensorPowSuccHead (S : QSystem) (n : ℕ) : S ^⊗ₛ (n + 1) ≃ₛ S ⊗ S ^⊗ₛ n :=
  ⟨QSystem.tensorPowSuccHeadIsometry S n⟩

/-- **Action of the head-peel isomorphism on a product state:** `⨂ᵢ |fᵢ⟩ ↦ |f 0⟩ ⊗ (⨂ⱼ |f j.succ⟩)`,
peeling the head factor `f 0` off the front of the tail register. -/
theorem QSystem.tensorPowSuccHead_toIsometry_tprod (S : QSystem) (n : ℕ)
    (f : Fin (n + 1) → S.space) :
    (QSystem.tensorPowSuccHead S n).toIsometry (⨂ₜ[ℂ] i, f i)
      = f 0 ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, f j.succ) := by
  change (QSystem.tensorPowSuccHeadIsometry S n) (⨂ₜ[ℂ] i, f i) = _
  rw [QSystem.tensorPowSuccHeadIsometry, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, PiTensorProduct.reindexₗᵢ_tprod,
    PiTensorProduct.tmulEquivDepₗᵢ_symm_tprod, TensorProduct.congrIsometry_tmul,
    PiTensorProduct.subsingletonEquivₗᵢ_tprod, LinearIsometryEquiv.coe_refl, id_eq]
  simp only [QSystem.headSplit_symm_inl, QSystem.headSplit_symm_inr]

/-- **Inverse (`cons`) action of the head-peel isomorphism:** `|a⟩ ⊗ (⨂ⱼ |bⱼ⟩) ↦ ⨂ᵢ |(Fin.cons a b)
i⟩`, prepending a head wire `a` to the tail register `⨂ⱼ |bⱼ⟩`. -/
theorem QSystem.tensorPowSuccHead_symm_toIsometry_tmul_tprod (S : QSystem) (n : ℕ) (a : S.space)
    (b : Fin n → S.space) :
    (QSystem.tensorPowSuccHead S n).toIsometry.symm (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, b j))
      = ⨂ₜ[ℂ] i, @Fin.cons n (fun _ => S.space) a b i := by
  have h : (QSystem.tensorPowSuccHead S n).toIsometry
      (⨂ₜ[ℂ] i, @Fin.cons n (fun _ => S.space) a b i) = a ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, b j) := by
    rw [QSystem.tensorPowSuccHead_toIsometry_tprod]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rfl
  apply (QSystem.tensorPowSuccHead S n).toIsometry.injective
  exact (LinearIsometryEquiv.apply_symm_apply _ _).trans h.symm

/-! ### The one-factor collapse `S ≃ₛ S ^⊗ₛ 1` -/

/-- **The one-factor collapse** `S ≃ₛ S ^⊗ₛ 1`: a single-factor tensor power is the system itself,
from the subsingleton-index isometry `PiTensorProduct.subsingletonEquivₗᵢ` over `Fin 1`. It is the
`n = 0` base case of the `qtower n qubit ≃ₛ qubit ^⊗ₛ (n+1)` bridge (`Core`) — the analogue, at the
bottom of the induction, of `QSystem.tensorPowSuccHead` at each successor step. -/
def QSystem.tensorPowOne (S : QSystem) : S ≃ₛ S ^⊗ₛ 1 :=
  ⟨(PiTensorProduct.subsingletonEquivₗᵢ ℂ (fun _ : Fin 1 => S.space) 0).symm⟩

/-- **Action of the one-factor collapse on a vector:** `v ↦ ⨂ᵢ v`, the one-factor product state. -/
theorem QSystem.tensorPowOne_toIsometry_apply (S : QSystem) (v : S.space) :
    (S.tensorPowOne).toIsometry v = ⨂ₜ[ℂ] _ : Fin 1, v := by
  change (PiTensorProduct.subsingletonEquivₗᵢ ℂ (fun _ : Fin 1 => S.space) 0).symm v = _
  apply (PiTensorProduct.subsingletonEquivₗᵢ ℂ (fun _ : Fin 1 => S.space) 0).injective
  rw [LinearIsometryEquiv.apply_symm_apply, PiTensorProduct.subsingletonEquivₗᵢ_tprod]

/-! ### The block split `S ^⊗ₛ (a + b) ≃ₛ S ^⊗ₛ a ⊗ S ^⊗ₛ b` -/

/-- The index split `Fin (a + b) ≃ Fin a ⊕ Fin b` underlying the block-split isometry: the first `a`
indices go to the left summand and the last `b` to the right (`finSumFinEquiv.symm`). Kept as a
*named* definition (like `QSystem.headSplit`) so the block-split isometry's type unification treats
it opaquely — an inline `finSumFinEquiv.symm` is eagerly unfolded and loops (`whnf` timeout). -/
def QSystem.blockSplit (a b : ℕ) : Fin (a + b) ≃ Fin a ⊕ Fin b := finSumFinEquiv.symm

/-- The inverse of `QSystem.blockSplit` is `finSumFinEquiv` (undoing the `.symm`). -/
@[simp] theorem QSystem.blockSplit_symm (a b : ℕ) :
    (QSystem.blockSplit a b).symm = finSumFinEquiv := by
  rw [QSystem.blockSplit, Equiv.symm_symm]

/-- The block-split isometry
`(S ^⊗ₛ (a+b)).space ≃ₗᵢ (S ^⊗ₛ a ⊗ S ^⊗ₛ b).space`: reindex the `a + b` factors along
`QSystem.blockSplit a b : Fin (a+b) ≃ Fin a ⊕ Fin b`, then split the `Sum` with `tmulEquivDepₗᵢ`.
The general-arity companion of `QSystem.tensorPowSuccHeadIsometry` — no singleton collapse is needed
because neither block is forced to be a single factor.

The reindex step carries an explicit codomain ascription `⨂[Fin a ⊕ Fin b] S.space`: it forces the
reindexed (constant) family into that form up front, avoiding a `whnf` timeout the `.trans`
unification otherwise hits reducing `(blockSplit a b).symm j` under the general symbolic split. -/
noncomputable def QSystem.tensorPowAddIsometry (S : QSystem) (a b : ℕ) :
    (⨂[ℂ] _ : Fin (a + b), S.space) ≃ₗᵢ[ℂ]
      (⨂[ℂ] _ : Fin a, S.space) ⊗[ℂ] (⨂[ℂ] _ : Fin b, S.space) :=
  ((PiTensorProduct.reindexₗᵢ ℂ (fun _ : Fin (a + b) => S.space) (QSystem.blockSplit a b) :
      (⨂[ℂ] _ : Fin (a + b), S.space) ≃ₗᵢ[ℂ] ⨂[ℂ] _ : Fin a ⊕ Fin b, S.space)).trans
    (PiTensorProduct.tmulEquivDepₗᵢ ℂ (fun _ : Fin a ⊕ Fin b => S.space)).symm

set_option maxHeartbeats 1000000 in
-- The `QSystem.Iso` ⟨⟩ constructor checks the raw isometry's types against
-- `(S ^⊗ₛ (a+b)).space` / `((S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)).space`; unfolding `piTensor.space` at the
-- *symbolic* index `a + b` is markedly heavier than at the numeral `n + 1` of `tensorPowSuccHead`
-- (but finite — a plain defeq, not a loop), so the default heartbeat budget is raised for it.
/-- **The block-split system isomorphism** `S ^⊗ₛ (a + b) ≃ₛ (S ^⊗ₛ a) ⊗ (S ^⊗ₛ b)`: split the
`(a+b)`-fold tensor power into its first `a` factors and its last `b` factors. The general-arity
tensor-power split, generalising the `succ` head-peel `QSystem.tensorPowSuccHead` (the `a = 1` case,
up to the singleton collapse of the head factor). This is what allows embedding a
gate acting on a contiguous block of `a` wires into the larger `(a+b)`-wire register (via
`Evolution.onLeft` across this split), the wire-addressed placement the `Cᵏ(X)`-block `Toffoli`
reduction of Exercise 4.29 needs. -/
def QSystem.tensorPowAdd (S : QSystem) (a b : ℕ) : S ^⊗ₛ (a + b) ≃ₛ (S ^⊗ₛ a) ⊗ (S ^⊗ₛ b) :=
  ⟨QSystem.tensorPowAddIsometry S a b⟩

/-- **Action of the block split on a product state:**
`⨂ₖ |fₖ⟩ ↦ (⨂ᵢ |f (Fin.castAdd b i)⟩) ⊗ (⨂ⱼ |f (Fin.natAdd a j)⟩)`, grouping the first `a` factors
into the left block and the last `b` factors into the right block. The block boundaries are the
reduced indices `Fin.castAdd b i` (first `a` wires) and `Fin.natAdd a j` (last `b` wires) — matching
the reduced-index form of the sibling head-peel `tensorPowSuccHead_toIsometry_tprod` (`f 0`,
`f j.succ`). -/
theorem QSystem.tensorPowAdd_toIsometry_tprod (S : QSystem) (a b : ℕ) (f : Fin (a + b) → S.space) :
    (QSystem.tensorPowAdd S a b).toIsometry (⨂ₜ[ℂ] i, f i)
      = (⨂ₜ[ℂ] i, f (Fin.castAdd b i))
          ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, f (Fin.natAdd a j)) := by
  change (QSystem.tensorPowAddIsometry S a b) (⨂ₜ[ℂ] i, f i) = _
  rw [QSystem.tensorPowAddIsometry, LinearIsometryEquiv.trans_apply,
    PiTensorProduct.reindexₗᵢ_tprod, PiTensorProduct.tmulEquivDepₗᵢ_symm_tprod]
  simp only [QSystem.blockSplit_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

/-- **Inverse (`append`) action of the block split:**
`(⨂ᵢ |uᵢ⟩) ⊗ (⨂ⱼ |vⱼ⟩) ↦ ⨂ₖ |(Fin.append u v) k⟩`, concatenating a length-`a` block `u` and a
length-`b` block `v` into one `(a+b)`-fold product register. The direction consumed when a gate
built on the first block is transported back onto the full register. -/
theorem QSystem.tensorPowAdd_symm_toIsometry_tmul_tprod (S : QSystem) (a b : ℕ)
    (u : Fin a → S.space) (v : Fin b → S.space) :
    (QSystem.tensorPowAdd S a b).toIsometry.symm ((⨂ₜ[ℂ] i, u i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, v j))
      = ⨂ₜ[ℂ] k, Fin.append u v k := by
  have h : (QSystem.tensorPowAdd S a b).toIsometry (⨂ₜ[ℂ] k, Fin.append u v k)
      = (⨂ₜ[ℂ] i, u i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, v j) := by
    rw [QSystem.tensorPowAdd_toIsometry_tprod]
    simp only [Fin.append_left, Fin.append_right]
    rfl
  apply (QSystem.tensorPowAdd S a b).toIsometry.injective
  exact (LinearIsometryEquiv.apply_symm_apply _ _).trans h.symm

/-! ### Relabelling the factors `S ^⊗ₛ a ≃ₛ S ^⊗ₛ b` -/

/-- **The factor-relabelling system isomorphism** `S ^⊗ₛ a ≃ₛ S ^⊗ₛ b` induced by a wire reindexing
`e : Fin a ≃ Fin b`. As a `Fin a ≃ Fin b` forces `a = b`, this re-labels the factors of a tensor
power by `e` without regrouping — the general-arity analogue of the wire-permutation gate
`Evolution.permWires` (the case `a = b`, `e : Equiv.Perm (Fin a)`), here across a *propositional*
size match.

It is the **constant-family case of the indexed reindex** `QSystem.piTensorReindex`: since
`S ^⊗ₛ a = ⨂ₛ _ : Fin a, S`, reindexing the constant family `fun _ : Fin a => S` along `e` lands on
`⨂ₛ _ : Fin b, S = S ^⊗ₛ b`. A thin named wrapper (matching the register-cast role of its
`tensorPowSuccHead`/`tensorPowAdd` file-siblings), so its action dictionaries below reduce to the
`piTensorReindex` API rather than re-deriving a `reindexₗᵢ` from scratch.

Its role in Exercise 4.29 is the **register cast**: identifying the register `qubit ^⊗ₛ (k + 1 + b)`
a placed `Cᵏ(X)` gate `Evolution.placedMcCtrlX` lives on with a circuit's fixed ambient register
`qubit ^⊗ₛ m` whenever `k + 1 + b = m` (via `e = finCongr`), so gates of varying control-arity `k`
compose on one register. -/
def QSystem.tensorPowCongr (S : QSystem) {a b : ℕ} (e : Fin a ≃ Fin b) : S ^⊗ₛ a ≃ₛ S ^⊗ₛ b :=
  QSystem.piTensorReindex e (fun _ : Fin a => S)

/-- **Action of the factor relabelling on a product state:** `⨂ᵢ |fᵢ⟩ ↦ ⨂ⱼ |f (e.symm j)⟩` — the
factor that sat at wire `e.symm j` is read at wire `j`. Read off
`QSystem.piTensorReindex_toIsometry` (`tensorPowCongr` *is* the constant-family `piTensorReindex`)
plus `PiTensorProduct.reindexₗᵢ_tprod`. -/
theorem QSystem.tensorPowCongr_toIsometry_tprod (S : QSystem) {a b : ℕ} (e : Fin a ≃ Fin b)
    (f : Fin a → S.space) :
    (QSystem.tensorPowCongr S e).toIsometry (⨂ₜ[ℂ] i, f i) = ⨂ₜ[ℂ] j, f (e.symm j) := by
  rw [QSystem.tensorPowCongr, QSystem.piTensorReindex_toIsometry]
  exact PiTensorProduct.reindexₗᵢ_tprod e f

/-- **`PureState` action of the factor relabelling:** `⨂ₚ ᵢ ψ i ↦ ⨂ₚ ⱼ ψ (e.symm j)`, the register
cast on product pure states — the **constant-family case** of the general naturality lemma
`PureState.piTensor_congr_piTensorReindex`. The dictionary the register cast is read through when
transporting a placed gate's computational-basis truth table onto the relabelled register. -/
theorem QSystem.tensorPowCongr_congr_piTensor (S : QSystem) {a b : ℕ} (e : Fin a ≃ Fin b)
    (ψ : Fin a → PureState S) :
    PureState.congr (QSystem.tensorPowCongr S e) (PureState.piTensor ψ)
      = PureState.piTensor fun j => ψ (e.symm j) :=
  PureState.piTensor_congr_piTensorReindex e ψ

/-- **`PureState` action of the inverse factor relabelling:** `⨂ₚ ⱼ φ j ↦ ⨂ₚ ᵢ φ (e i)`, the
inverse dictionary of `QSystem.tensorPowCongr_congr_piTensor` (the wire at index `i` reads the
factor that will sit at `e i`). Used to *feed* a product-state input to a gate that was transported
onto the relabelled register. Derived from the forward dictionary by the `PureState.congr` roundtrip
`PureState.congr_symm_congr`. -/
theorem QSystem.tensorPowCongr_symm_congr_piTensor (S : QSystem) {a b : ℕ} (e : Fin a ≃ Fin b)
    (φ : Fin b → PureState S) :
    PureState.congr (QSystem.tensorPowCongr S e).symm (PureState.piTensor φ)
      = PureState.piTensor fun i => φ (e i) := by
  have h : PureState.congr (QSystem.tensorPowCongr S e) (PureState.piTensor fun i => φ (e i))
      = PureState.piTensor φ := by
    rw [QSystem.tensorPowCongr_congr_piTensor]
    simp only [Equiv.apply_symm_apply]
    rfl
  exact (congrArg (PureState.congr (QSystem.tensorPowCongr S e).symm) h.symm).trans
    (PureState.congr_symm_congr (QSystem.tensorPowCongr S e) _)

/-- **Backward singleton dictionary:** `(QSystem.tensorPowOne S).symm` collapses the one-factor
product pure state `⨂ₚ ᵢ k i` (`i : Fin 1`) back to its single factor `k 0`. The one-factor sibling
of `QSystem.tensorPowAdd_congr_piTensor` / `QSystem.tensorPowCongr_symm_congr_piTensor`; used to
feed a computational-basis input through a `tensorPowOne` collapse. -/
theorem QSystem.congr_tensorPowOne_symm_piTensor {S : QSystem} (k : Fin 1 → PureState S) :
    PureState.congr (S.tensorPowOne).symm (PureState.piTensor k) = k 0 := by
  have h1 : PureState.congr (S.tensorPowOne) (k 0)
      = PureState.piTensor (fun _ : Fin 1 => k 0) := by
    apply PureState.ext
    rw [PureState.congr_vec, PureState.piTensor_vec, QSystem.tensorPowOne_toIsometry_apply]
  have hk : k = (fun _ : Fin 1 => k 0) := funext fun i => by rw [Fin.eq_zero i]
  rw [hk, ← h1, PureState.congr_symm_congr]

end AxQM
