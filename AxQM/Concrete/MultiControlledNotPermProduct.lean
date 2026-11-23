/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNotGate
import AxQM.Concrete.MultiControlledNotCircuit

/-!
# Concrete: a combinatorial `mcNot` circuit lifts to a product of Toffoli/CNOT/NOT permutation gates

The §4.3 reduction of a controlled single-qubit gate
(`Concrete/ControlledSingleQubitABCReduction.lean`)
leaves the multiply-controlled `NOT` `N = ctrlSingleQubit enc j 1 pauliX` as its only *controlled*
residue, and `Concrete/MultiControlledNotGate.lean` identifies that matrix with the permutation gate
of the classical `mcNot`: `N = permGate enc (mcNotPerm (univ \ {j}) j)`. Nielsen & Chuang, Exercise
4.29, decomposes that classical `Cⁿ(X)` into a **circuit** of `Toffoli`, `CNOT` and `NOT` gates — a
`List (McNotGate m)` of `≤ 2`-control `mcNot`s whose denotation (`mcNotDenote`) is the whole gate
(`Concrete/MultiControlledNotCircuit.lean`, `exists_mcNotCircuit`).

This file carries that combinatorial decomposition over to the **matrix** level: a valid gate
circuit `gs` — every gate `(S, t)` with `t ∉ S`, so a genuine reversible permutation — realises the
`permGate enc (mcNotPerm S t)` as an *exact product* `Gs.prod` of the individual gates'
permutation-gate matrices, using only `permGate`'s `*`-homomorphism algebra (`permGate_one`,
`permGate_mul`). When moreover each gate has at most two controls (`S.card ≤ 2`) — the shape
`exists_mcNotCircuit` guarantees — every factor is a `Toffoli` (2 controls), `CNOT` (1) or `NOT` (0)
permutation gate, captured by the predicate `IsToffoliPermGate`; each such factor is unitary.

## Contents

* `IsToffoliPermGate enc G` — `G` is the permutation gate of an `mcNot` with `≤ 2` controls (a
  `Toffoli`/`CNOT`/`NOT`); `IsToffoliPermGate.mem_unitaryGroup` — each is unitary.
* `exists_isToffoliPermGate_list_prod_permGate` — the inductive core: a valid gate circuit `gs`
  yields a permutation `σ` with `⇑σ = mcNotDenote gs` and a matching list `Gs` of
  `IsToffoliPermGate` factors with `permGate enc σ = Gs.prod`.
* `exists_isToffoliPermGate_prod_eq_mcNotPermGate` — **the bridge**: if `mcNotDenote gs = mcNot S t`
  then `permGate enc (mcNotPerm S ht) = Gs.prod` for such a `Gs`.
* `exists_isToffoliPermGate_prod_eq_mcNotPermGate_of_spare` — the corollary that feeds
  `exists_mcNotCircuit`'s circuit (whenever a spare wire exists) straight into the bridge.

The all-controls case `mcNot (univ \ {j}) j` that `N` needs uses the *whole* register (no spare
wire), so its circuit is the Barenco tight-register construction — a separate (Exercise 4.29)
development — plugged into `exists_isToffoliPermGate_prod_eq_mcNotPermGate` once available. The
bridge here is exactly the reusable transport step, independent of which circuit supplies `gs`.

Everything is stated for raw complex matrices, the encoding equivalence, `permGate`, and the
classical `mcNot`/`mcNotDenote`/`McNotGate`.
-/

open Matrix

namespace AxQM.Concrete

variable {m d : ℕ}

/-- **A `≤ 2`-control reversible gate on the encoded register.** `IsToffoliPermGate enc G` holds
when `G` is the permutation gate `permGate enc (mcNotPerm S t)` of a multiply-controlled `NOT` with
at most two controls — a `Toffoli` (`|S| = 2`), `CNOT` (`|S| = 1`), or `NOT` (`|S| = 0`), the
elementary reversible gates N&C's universality reduction bottoms out in. -/
def IsToffoliPermGate (enc : (Fin m → Fin 2) ≃ Fin d) (G : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (S : Finset (Fin m)) (t : Fin m) (ht : t ∉ S), S.card ≤ 2 ∧ G = permGate enc (mcNotPerm S ht)

/-- **Every `≤ 2`-control reversible gate is unitary** — it is a permutation gate
(`permGate_mem_unitaryGroup`). This is the per-gate unitarity the §4.5.3 error-chaining calculus
consumes. -/
theorem IsToffoliPermGate.mem_unitaryGroup {enc : (Fin m → Fin 2) ≃ Fin d}
    {G : Matrix (Fin d) (Fin d) ℂ} (h : IsToffoliPermGate enc G) :
    G ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  obtain ⟨S, t, ht, _, rfl⟩ := h
  exact permGate_mem_unitaryGroup enc _

/-- **The inductive core of the circuit-to-matrix bridge.** A gate circuit `gs`, every gate `(S, t)`
of which has `≤ 2` controls and target `t ∉ S` (so a genuine permutation), yields a permutation `σ`
of the bit-strings whose action *is* the circuit denotation (`⇑σ = mcNotDenote gs`), together with a
list `Gs` of matrices — one per gate — every one a `Toffoli`/`CNOT`/`NOT` permutation gate
(`IsToffoliPermGate`), whose product is `permGate enc σ`. Proved by list induction: each gate
contributes its `mcNotPerm` to `σ` (composition of permutations = circuit denotation, head acting
last) and its `permGate` to `Gs`, the product identity following from `permGate`'s multiplicativity
(`permGate_mul`). -/
theorem exists_isToffoliPermGate_list_prod_permGate (enc : (Fin m → Fin 2) ≃ Fin d)
    (gs : List (McNotGate m)) (hgate : ∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) :
    ∃ (σ : Equiv.Perm (Fin m → Fin 2)) (Gs : List (Matrix (Fin d) (Fin d) ℂ)),
      ⇑σ = mcNotDenote gs ∧ (∀ G ∈ Gs, IsToffoliPermGate enc G) ∧
      permGate enc σ = Gs.prod := by
  revert hgate
  induction gs with
  | nil => exact fun _ => ⟨1, [], by funext x; simp [mcNotDenote], by simp, by simp⟩
  | cons g gs ih =>
      intro hgate
      obtain ⟨hc, hne⟩ := hgate g List.mem_cons_self
      obtain ⟨σ, Gs, hσ, hGs, hprod⟩ :=
        ih (fun g' hg' => hgate g' (List.mem_cons_of_mem _ hg'))
      refine ⟨mcNotPerm g.1 hne * σ, permGate enc (mcNotPerm g.1 hne) :: Gs, ?_, ?_, ?_⟩
      · funext x
        rw [mcNotDenote_cons, Equiv.Perm.mul_apply, mcNotPerm_apply, congrFun hσ x]
      · intro G hG
        rcases List.mem_cons.mp hG with rfl | hG
        · exact ⟨g.1, g.2, hne, hc, rfl⟩
        · exact hGs G hG
      · rw [List.prod_cons, ← hprod, permGate_mul]

/-- **The circuit-to-matrix bridge.** If a valid gate circuit `gs` (each gate `≤ 2`-controlled with
target off its controls) denotes the classical multiply-controlled `NOT` `mcNot S t`
(`mcNotDenote gs = mcNot S t`), then the matrix multiply-controlled `NOT` `permGate enc (mcNotPerm S
ht)` is an *exact product* `Gs.prod` of `Toffoli`/`CNOT`/`NOT` permutation gates. The circuit's
denotation and `mcNotPerm S ht` agree as functions, hence as permutations (`Equiv.ext`), so the
inductive core's product identity transports across. This is the reusable transport step: whichever
Exercise 4.29 circuit realises `mcNot S t` feeds straight in. -/
theorem exists_isToffoliPermGate_prod_eq_mcNotPermGate (enc : (Fin m → Fin 2) ≃ Fin d)
    {S : Finset (Fin m)} {t : Fin m} (ht : t ∉ S) (gs : List (McNotGate m))
    (hgate : ∀ g ∈ gs, g.1.card ≤ 2 ∧ g.2 ∉ g.1) (hden : mcNotDenote gs = mcNot S t) :
    ∃ Gs : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ G ∈ Gs, IsToffoliPermGate enc G) ∧ permGate enc (mcNotPerm S ht) = Gs.prod := by
  obtain ⟨σ, Gs, hσ, hGs, hprod⟩ := exists_isToffoliPermGate_list_prod_permGate enc gs hgate
  refine ⟨Gs, hGs, ?_⟩
  have heq : σ = mcNotPerm S ht :=
    Equiv.ext fun x => by rw [mcNotPerm_apply, ← congrFun hden x, ← congrFun hσ x]
  rw [← heq, hprod]

/-- **The bridge fed by the halving `Cⁿ(X)` circuit.** For any target `t ∉ S` on a register with at
least one spare wire (`(insert t S).card < m`), the matrix multiply-controlled `NOT`
`permGate enc (mcNotPerm S ht)` is an exact product of `Toffoli`/`CNOT`/`NOT` permutation gates —
`exists_mcNotCircuit`'s combinatorial circuit fed straight into
`exists_isToffoliPermGate_prod_eq_mcNotPermGate`. (The all-controls case `mcNot (univ \ {j}) j` uses
the whole register, so is *not* covered here — it needs the Barenco tight-register circuit.) -/
theorem exists_isToffoliPermGate_prod_eq_mcNotPermGate_of_spare (enc : (Fin m → Fin 2) ≃ Fin d)
    {S : Finset (Fin m)} {t : Fin m} (ht : t ∉ S) (hspare : (insert t S).card < m) :
    ∃ Gs : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ G ∈ Gs, IsToffoliPermGate enc G) ∧ permGate enc (mcNotPerm S ht) = Gs.prod := by
  obtain ⟨gs, hgate, hden, _⟩ := exists_mcNotCircuit S t ht hspare
  exact exists_isToffoliPermGate_prod_eq_mcNotPermGate enc ht gs hgate hden

end AxQM.Concrete
