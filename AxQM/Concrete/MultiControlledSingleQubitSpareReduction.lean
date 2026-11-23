/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledSingleQubitABCReduction
import AxQM.Concrete.MultiControlledNotPermProduct
import AxQM.Concrete.ComplexExpUnit

/-!
# Concrete: the work-qubit-assisted reduction of a subset-controlled single-qubit gate (N&C §4.3)

(Nielsen & Chuang §4.3, p. 182 — the "with work qubits" reduction of `Cᵏ(U)`; Barenco *et al.*,
Lemma 7.2/7.5.)

The Barenco tight-register recursion (`Concrete/MultiControlledSingleQubitBarenco.lean`) factors the
tight `Cⁿ(X)` into *subset*-controlled single-qubit gates `mcCtrlSingleQubit enc S j Ũ` **each of
which now has a spare wire** (uses at most `n − 1` of the `n + 1` register wires). This file bottoms
those factors out: **a subset-controlled single-qubit gate with a spare wire is an exact product of
`Toffoli`/`CNOT`/`NOT` gates and uncontrolled single-qubit gates** — the elementary gates the whole
universality reduction terminates in.

## The terminal gate class

* `AxQM.Concrete.IsToffoliOrSingleQubitGate enc G` — `G` is either a `≤ 2`-control
  reversible gate (`IsToffoliPermGate`: a `Toffoli`/`CNOT`/`NOT`) or an uncontrolled single-qubit
  unitary on a wire (`singleQubitOnWire enc j U`, `U ∈ U(2)`). These are exactly the gates the §4.3
  reduction bottoms out in — each directly a `CNOT`/`Toffoli` or an arbitrary single-qubit gate.
  `IsToffoliOrSingleQubitGate.mem_unitaryGroup` — each is unitary (the per-gate norm bound the
  §4.5.3 error-chaining calculus consumes).

## The reduction

* `AxQM.Concrete.exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX` — the
  **spare-wire subset-controlled `NOT`** is a product of terminal gates: for `j ∉ S` with a spare
  wire (`(insert j S).card < m`), `mcCtrlSingleQubit enc S j pauliX = gates.prod` with every factor
  a `Toffoli`/`CNOT`/`NOT`. Composes the permutation bridge
  `mcCtrlSingleQubit_pauliX_eq_permGate` with the combinatorial `Cⁿ(X)` circuit
  (`exists_isToffoliPermGate_prod_eq_mcNotPermGate_of_spare`).
* `AxQM.Concrete.exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit` — **the
  headline**: for any `Ũ ∈ U(2)`, `j ∉ S`, and a spare wire (`(insert j S).card < m`),
  `mcCtrlSingleQubit enc S j Ũ = gates.prod` with **every** factor an `IsToffoliOrSingleQubitGate`.
  Proved by strong induction on the control set `S` (`Finset.strongInductionOn`):
  - `S = ∅` — the gate is the uncontrolled `singleQubitOnWire enc j Ũ` (`mcCtrlSingleQubit_empty`),
    a single terminal factor.
  - `S ≠ ∅` — the subset-controlled ABC reduction
    (`exists_abc_reduction_mcCtrlSingleQubit`) rewrites the gate as a subset-controlled *phase*
    residual times `singleQubitOnWire A · N · singleQubitOnWire B · N · singleQubitOnWire C`, with
    `N = mcCtrlSingleQubit enc S j pauliX`. The three wire gates are terminal; each `N` reduces by
    the spare-wire `NOT` lemma above; and the phase residual **peels one control**
    (`mcCtrlSingleQubit_phase_peel`) into `mcCtrlSingleQubit enc (S.erase c) c (phaseGate _)` — a
    subset-controlled single-qubit gate on the strictly smaller control set `S.erase c ⊂ S`, handled
    by the induction hypothesis (its own spare wire persists since `insert c (S.erase c) = S`).

The spare-wire hypothesis `(insert j S).card < m` is preserved down the recursion: the only
recursive call is on `S.erase c`, whose gate uses `insert c (S.erase c) = S` (`≤ m − 1` wires), so a
spare wire remains. The **tight** case `(insert j S).card = m` (the top `Cⁿ(X)` controlling every
other wire) is *not* covered here — it needs the Barenco `√X` construction first, whose factors then
feed this lemma.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The terminal gate class of the §4.3 reduction.** `IsToffoliOrSingleQubitGate enc G` holds when
`G` is either a `≤ 2`-control reversible gate (`IsToffoliPermGate` — a `Toffoli`/`CNOT`/`NOT`) or an
uncontrolled single-qubit unitary on a wire (`singleQubitOnWire enc j U` with `U ∈ U(2)`). Every
subset-controlled single-qubit gate with a spare wire reduces to a product of these
(`exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit`). -/
def IsToffoliOrSingleQubitGate (enc : (Fin m → Fin 2) ≃ Fin d) (G : Matrix (Fin d) (Fin d) ℂ) :
    Prop :=
  IsToffoliPermGate enc G ∨
    ∃ (j : Fin m) (U : Matrix (Fin 2) (Fin 2) ℂ),
      U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ G = singleQubitOnWire enc j U

/-- **Every terminal gate is unitary** — a `≤ 2`-control reversible gate is a permutation gate
(`IsToffoliPermGate.mem_unitaryGroup`), and a single-qubit unitary on a wire is unitary
(`singleQubitOnWire_mem_unitaryGroup`). This is the per-gate norm bound the §4.5.3 error-chaining
calculus consumes. -/
theorem IsToffoliOrSingleQubitGate.mem_unitaryGroup {enc : (Fin m → Fin 2) ≃ Fin d}
    {G : Matrix (Fin d) (Fin d) ℂ} (h : IsToffoliOrSingleQubitGate enc G) :
    G ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rcases h with h | ⟨j, U, hU, rfl⟩
  · exact h.mem_unitaryGroup
  · exact singleQubitOnWire_mem_unitaryGroup enc j hU

/-- **The phase-block gate of a global phase `e^{iα}` is unitary** — `star (e^{iα}) · e^{iα} = 1`
(the shared unit-modulus fact `star_exp_ofReal_mul_I_mul_self`), so `phaseGate (e^{iα}) ∈ U(2)`. The
residual of the subset-controlled ABC reduction peels into this gate. -/
theorem phaseGate_exp_mem_unitaryGroup (α : ℝ) :
    phaseGate (Complex.exp ((α : ℂ) * Complex.I)) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  phaseGate_mem_unitaryGroup (star_exp_ofReal_mul_I_mul_self α)

/-- **The spare-wire subset-controlled `NOT` is a product of `Toffoli`/`CNOT`/`NOT` gates.** For
`j ∉ S` on a register with a spare wire (`(insert j S).card < m`),
`mcCtrlSingleQubit enc S j pauliX` is an exact product `gates.prod` of terminal gates, every factor
a `≤ 2`-control reversible gate.
Composes the permutation bridge `mcCtrlSingleQubit_pauliX_eq_permGate` with the combinatorial
`Cⁿ(X)` circuit `exists_isToffoliPermGate_prod_eq_mcNotPermGate_of_spare`. -/
theorem exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX
    (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)} {j : Fin m} (hj : j ∉ S)
    (hspare : (insert j S).card < m) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g ∈ gates, IsToffoliOrSingleQubitGate enc g) ∧
        mcCtrlSingleQubit enc S j pauliX = gates.prod := by
  obtain ⟨Gs, hGs, hprod⟩ := exists_isToffoliPermGate_prod_eq_mcNotPermGate_of_spare enc hj hspare
  refine ⟨Gs, fun G hG => Or.inl (hGs G hG), ?_⟩
  rw [mcCtrlSingleQubit_pauliX_eq_permGate enc S hj, hprod]

/-- **The work-qubit-assisted reduction of a subset-controlled single-qubit gate** (Nielsen & Chuang
§4.3, the reduction of `Cᵏ(U)` with work qubits available). For any single-qubit unitary `Ũ`, target
`j ∉ S`, and a register with a spare wire (`(insert j S).card < m`), the subset-controlled gate
`mcCtrlSingleQubit enc S j Ũ` is an exact product `gates.prod` of terminal gates — every factor an
`IsToffoliOrSingleQubitGate` (a `Toffoli`/`CNOT`/`NOT` or an uncontrolled single-qubit unitary on a
wire). Proved by strong induction on the control set `S`: the subset-controlled ABC reduction plus
the phase-residual peel express the gate as three uncontrolled wire gates, two spare-wire
subset-controlled `NOT`s (each a `Toffoli`/`CNOT`/`NOT` product), and one subset-controlled gate on
the strictly smaller control set `S.erase c` (the induction hypothesis). This is the machine that
discharges every Barenco recursion factor — the "recurse until every gate is a
`Toffoli`/`CNOT`/single-qubit gate" step of Exercise 4.43
(`AxQM/NC/Ch4/Exercise4_43.lean`). -/
theorem exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit
    (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)} {j : Fin m} (hj : j ∉ S)
    (hspare : (insert j S).card < m) {Ũ : Matrix (Fin 2) (Fin 2) ℂ}
    (hŨ : Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g ∈ gates, IsToffoliOrSingleQubitGate enc g) ∧
        mcCtrlSingleQubit enc S j Ũ = gates.prod := by
  suffices H : ∀ (S : Finset (Fin m)) (j : Fin m), j ∉ S → (insert j S).card < m →
      ∀ (U : Matrix (Fin 2) (Fin 2) ℂ), U ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
          (∀ g ∈ gates, IsToffoliOrSingleQubitGate enc g) ∧
            mcCtrlSingleQubit enc S j U = gates.prod by
    exact H S j hj hspare Ũ hŨ
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro j hj hspare U hU
    rcases Finset.eq_empty_or_nonempty S with rfl | ⟨c, hc⟩
    · -- Base case: no controls — the gate is the uncontrolled single-qubit wire gate.
      refine ⟨[singleQubitOnWire enc j U], ?_, ?_⟩
      · intro g hg
        rw [List.mem_singleton] at hg
        subst hg
        exact Or.inr ⟨j, U, hU, rfl⟩
      · rw [mcCtrlSingleQubit_empty, List.prod_singleton]
    · -- Step: ABC reduction + phase-residual peel + spare-wire `NOT`s.
      obtain ⟨α, A, B, C, hA, hB, hC, habc⟩ := exists_abc_reduction_mcCtrlSingleQubit enc S j hU
      obtain ⟨Gn, hGn, hNprod⟩ :=
        exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX enc hj hspare
      have hspare' : (insert c (S.erase c)).card < m := by
        rw [Finset.insert_erase hc]
        have hins : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hj
        omega
      obtain ⟨Gp, hGp, hPprod⟩ :=
        ih (S.erase c) (Finset.erase_ssubset hc) c (Finset.notMem_erase c S) hspare'
          (phaseGate (Complex.exp ((α : ℂ) * Complex.I))) (phaseGate_exp_mem_unitaryGroup α)
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
