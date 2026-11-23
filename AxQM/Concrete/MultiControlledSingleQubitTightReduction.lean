/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledSingleQubitSpareReduction
import AxQM.Concrete.MultiControlledSingleQubitBarenco

/-!
# Concrete: the tight-register `Cⁿ(X)` bottoms out — no spare-wire hypothesis (N&C §4.3)

(Nielsen & Chuang §4.3, p. 182 — the multiply-controlled-`NOT`/`Cⁿ(U)` reduction; Barenco *et al.*,
Lemma 7.5.)

The spare-wire reduction (`Concrete/MultiControlledSingleQubitSpareReduction.lean`) reduces a
*subset*-controlled single-qubit gate `mcCtrlSingleQubit enc S j Ũ` to a product of the terminal
gates `IsToffoliOrSingleQubitGate` **only when the register offers a spare wire**
(`(insert j S).card < m`). The **tight** case — the top `Cⁿ(X)` that controls *every* other wire
(`S = univ \ {j}`, so `(insert j S).card = m`) — is deliberately excluded there: as a permutation of
the `2^m` basis states it is a single transposition, hence **odd**, whereas every product of
`≤ 2`-control permutation gates on `≥ 4` wires is **even**, so it is provably *not* a product of
`Toffoli`/`CNOT`/`NOT` permutation gates (`Concrete/SqrtNot.lean`, the parity obstruction).

This file closes that last gap. The Barenco tight-register recursion
(`mcCtrlSingleQubit_pauliX_barenco_recursion`) peels one control off the tight `Cⁿ(X)` at the cost
of a genuine single-qubit `√X = sqrtNot` gate,

`Cⁿ(X) = C(√X) · Cⁿ⁻¹(X) · C(√X†) · Cⁿ⁻¹(X) · Cⁿ⁻¹(√X)`,

and **each of the five factors now has a spare wire**, so each bottoms out by the spare-wire
reduction. Chaining the two removes the spare-wire hypothesis entirely.

## The results

* `AxQM.Concrete.exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX'` — **the
  crux**: for *any* target `j ∉ S` (**no** spare-wire hypothesis) the multiply-controlled `NOT`
  `mcCtrlSingleQubit enc S j pauliX` is an exact product of terminal gates
  (`IsToffoliOrSingleQubitGate`). Removes the `(insert j S).card < m` hypothesis from
  `exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX`, so it covers the tight top
  `Cⁿ(X)`. Case split: a spare wire → the spare-wire lemma; `≤ 2` controls → directly a single
  `Toffoli`/`CNOT`/`NOT` (`mcCtrlSingleQubit_pauliX_eq_permGate`); otherwise (`≥ 3` controls, no
  spare wire) → the Barenco `√X` recursion, whose five factors are each spare-wire.
* `AxQM.Concrete.exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit'` — **the
  headline**: for any single-qubit unitary `Ũ` and *any* target `j ∉ S` (no spare-wire hypothesis),
  `mcCtrlSingleQubit enc S j Ũ` is an exact product of terminal gates. Removes the spare-wire
  hypothesis from `exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit`. For the tight case the
  subset-controlled ABC reduction rewrites the gate as three uncontrolled wire gates, two tight
  `Cⁿ(X)`s (bottomed out by the crux above), and a phase residual that **peels one control**
  (`mcCtrlSingleQubit_phase_peel`) into a *spare-wire* controlled phase-block gate.

So **every subset-controlled single-qubit gate on an encoded register bottoms out to
`Toffoli`/`CNOT`/single-qubit gates**, with no constraint on the control set — the §4.3 reduction of
`Cᵏ(U)` in full, the form the §4.5.2 controlled single-qubit gates of the universality argument feed
into.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The multiply-controlled `NOT` bottoms out — with no spare-wire hypothesis.** For any target
`j ∉ S` (in particular the tight top `Cⁿ(X)` controlling every other wire), the multiply-controlled
`NOT` `mcCtrlSingleQubit enc S j pauliX` is an exact product `gates.prod` of terminal gates
(`IsToffoliOrSingleQubitGate` — each a `Toffoli`/`CNOT`/`NOT` or an uncontrolled single-qubit
unitary on a wire).

This is the tight-register counterpart of
`exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX`, which requires a spare wire
(`(insert j S).card < m`). Three cases:
* a spare wire (`(insert j S).card < m`) — the spare-wire lemma;
* `S.card ≤ 2` — the gate is directly a `Toffoli`/`CNOT`/`NOT` permutation gate
  (`mcCtrlSingleQubit_pauliX_eq_permGate`), a single terminal factor;
* `S.card ≥ 3` and no spare wire (the genuinely tight case, `m = S.card + 1 ≥ 4`) — the Barenco
  `√X` recursion (`mcCtrlSingleQubit_pauliX_barenco_recursion`) peels one control `c`, and each of
  its five factors (`C(√X)`, `Cⁿ⁻¹(X)`, `C(√X†)`, `Cⁿ⁻¹(X)`, `Cⁿ⁻¹(√X)`) uses at most `m − 1` wires,
  hence has a spare wire and bottoms out by
  `exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit`(`_pauliX`). -/
theorem exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX'
    (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)} {j : Fin m} (hj : j ∉ S) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g ∈ gates, IsToffoliOrSingleQubitGate enc g) ∧
        mcCtrlSingleQubit enc S j pauliX = gates.prod := by
  by_cases hspare : (insert j S).card < m
  · -- A spare wire is available: the spare-wire `NOT` reduction applies verbatim.
    exact exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX enc hj hspare
  · by_cases hcard : S.card ≤ 2
    · -- `≤ 2` controls: the gate is a single `Toffoli`/`CNOT`/`NOT` permutation gate.
      refine ⟨[mcCtrlSingleQubit enc S j pauliX], ?_, (List.prod_singleton).symm⟩
      intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      exact Or.inl ⟨S, j, hj, hcard, mcCtrlSingleQubit_pauliX_eq_permGate enc S hj⟩
    · -- `≥ 3` controls and no spare wire (`m = S.card + 1 ≥ 4`): the Barenco `√X` recursion.
      have hScard : 3 ≤ S.card := by omega
      have hcard_ins : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hj
      have hle : (insert j S).card ≤ m :=
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)
      have htight : (insert j S).card = m := le_antisymm hle (not_lt.mp hspare)
      have hm : m = S.card + 1 := by omega
      -- Distinguish one control wire `c`.
      obtain ⟨c, hc⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
      have hjc : j ≠ c := by rintro rfl; exact hj hc
      have hcS' : c ∉ S.erase c := Finset.notMem_erase c S
      have hjS' : j ∉ S.erase c := fun h => hj (Finset.mem_of_mem_erase h)
      -- `C(√X)` / `C(√X†)`: single control `{c}` on wire `j`; spare since `m ≥ 4`.
      have hj1 : j ∉ ({c} : Finset (Fin m)) := Finset.notMem_singleton.mpr hjc
      have hs1 : (insert j ({c} : Finset (Fin m))).card < m := by
        rw [Finset.card_insert_of_notMem hj1, Finset.card_singleton]; omega
      obtain ⟨G1, hG1, hp1⟩ :=
        exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit enc hj1 hs1 sqrtNot_mem_unitaryGroup
      obtain ⟨G3, hG3, hp3⟩ :=
        exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit enc hj1 hs1
          sqrtNot_conjTranspose_mem_unitaryGroup
      -- `Cⁿ⁻¹(X)` (twice): control `S.erase c` on wire `c`; spare wire `j`.
      have hs2 : (insert c (S.erase c)).card < m := by rw [Finset.insert_erase hc]; omega
      obtain ⟨G2, hG2, hp2⟩ :=
        exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX enc hcS' hs2
      -- `Cⁿ⁻¹(√X)`: control `S.erase c` on wire `j`; spare wire `c`.
      have hs5 : (insert j (S.erase c)).card < m := by
        rw [Finset.card_insert_of_notMem hjS', Finset.card_erase_of_mem hc]; omega
      obtain ⟨G5, hG5, hp5⟩ :=
        exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit enc hjS' hs5
          sqrtNot_mem_unitaryGroup
      refine ⟨G1 ++ G2 ++ G3 ++ G2 ++ G5, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append] at hg
        rcases hg with ((((hg | hg) | hg) | hg) | hg)
        · exact hG1 g hg
        · exact hG2 g hg
        · exact hG3 g hg
        · exact hG2 g hg
        · exact hG5 g hg
      · rw [← Finset.insert_erase hc,
          mcCtrlSingleQubit_pauliX_barenco_recursion enc hcS' hjc hjS', hp1, hp2, hp3, hp5]
        simp only [List.prod_append]

/-- **The work-qubit-free reduction of a subset-controlled single-qubit gate** (Nielsen & Chuang
§4.3), with **no spare-wire hypothesis**. For any single-qubit unitary `Ũ` and any target `j ∉ S`,
`mcCtrlSingleQubit enc S j Ũ` is an exact product `gates.prod` of terminal gates
(`IsToffoliOrSingleQubitGate`).

Removes the spare-wire hypothesis `(insert j S).card < m` from
`exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit`. Case split:
* a spare wire → the spare-wire reduction;
* no controls (`S = ∅`) → the uncontrolled single-qubit wire gate, one terminal factor;
* controlled, no spare wire → the subset-controlled ABC reduction
  (`exists_abc_reduction_mcCtrlSingleQubit`) rewrites the gate as three uncontrolled wire gates, two
  tight `Cⁿ(X)`s (bottomed out by
  `exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX'`), and a phase residual that
  **peels one control** (`mcCtrlSingleQubit_phase_peel`) into
  `mcCtrlSingleQubit enc (S.erase c) c (phaseGate _)`, which now *has* a spare wire
  (`insert c (S.erase c) = S`, of card `m − 1 < m`) so bottoms out by the general spare-wire
  reduction. -/
theorem exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit'
    (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)} {j : Fin m} (hj : j ∉ S)
    {Ũ : Matrix (Fin 2) (Fin 2) ℂ} (hŨ : Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g ∈ gates, IsToffoliOrSingleQubitGate enc g) ∧
        mcCtrlSingleQubit enc S j Ũ = gates.prod := by
  by_cases hspare : (insert j S).card < m
  · -- A spare wire is available: the general spare-wire reduction applies verbatim.
    exact exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit enc hj hspare hŨ
  · rcases Finset.eq_empty_or_nonempty S with rfl | ⟨c, hc⟩
    · -- No controls: the uncontrolled single-qubit wire gate is itself terminal.
      refine ⟨[singleQubitOnWire enc j Ũ], ?_, ?_⟩
      · intro g hg
        rw [List.mem_singleton] at hg
        subst hg
        exact Or.inr ⟨j, Ũ, hŨ, rfl⟩
      · rw [mcCtrlSingleQubit_empty, List.prod_singleton]
    · -- Controlled, no spare wire: ABC reduction + phase-residual peel + the tight `NOT` crux.
      obtain ⟨α, A, B, C, hA, hB, hC, habc⟩ := exists_abc_reduction_mcCtrlSingleQubit enc S j hŨ
      obtain ⟨Gn, hGn, hNprod⟩ :=
        exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX' enc hj
      -- The phase residual peels the control `c ∈ S`, gaining wire `j` as a spare wire.
      have hcard_ins : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hj
      have hle : (insert j S).card ≤ m :=
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)
      have htight : (insert j S).card = m := le_antisymm hle (not_lt.mp hspare)
      have hspare_peel : (insert c (S.erase c)).card < m := by rw [Finset.insert_erase hc]; omega
      obtain ⟨Gp, hGp, hPprod⟩ :=
        exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit enc (Finset.notMem_erase c S)
          hspare_peel (phaseGate_exp_mem_unitaryGroup α)
      refine ⟨Gp ++ [singleQubitOnWire enc j A] ++ Gn ++ [singleQubitOnWire enc j B] ++ Gn
                ++ [singleQubitOnWire enc j C], ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with (((((hg | hg) | hg) | hg) | hg) | hg)
        · exact hGp g hg
        · subst hg; exact Or.inr ⟨j, A, hA, rfl⟩
        · exact hGn g hg
        · subst hg; exact Or.inr ⟨j, B, hB, rfl⟩
        · exact hGn g hg
        · subst hg; exact Or.inr ⟨j, C, hC, rfl⟩
      · rw [habc, mcCtrlSingleQubit_phase_peel enc hc hj, hPprod, hNprod]
        simp only [List.prod_append, List.prod_singleton, mul_assoc]

end AxQM.Concrete
