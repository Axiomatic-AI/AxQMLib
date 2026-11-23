/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.UnitaryControlledProduct
import AxQM.Concrete.MultiControlledSingleQubitTightReduction
import AxQM.Concrete.ControlledSingleQubitNormalisation

/-!
# Every unitary on an `m`-qubit register is an exact product of `Toffoli`/`CNOT`/single-qubit gates

*(Supports N&C Exercise 4.43 — universality of `H, S, CNOT, Toffoli`.)*

This file composes the two completed halves of the Nielsen & Chuang §4.5/§4.3 development into the
exact-decomposition milestone of Exercise 4.43's `n`-qubit lift:

* the §4.5 first stage `exists_isCtrlSingleQubit_list_prod_eq` writes any unitary `U ∈ U(d)`
  (`d = 2^m`, at least one qubit) as an exact product of **controlled** single-qubit gates
  (`IsCtrlSingleQubit`, i.e. `ctrlSingleQubit enc j c Ũ`, controlled on *all* other wires matching a
  pattern `c`);
* the §4.3 spare-wire-free reduction `exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit'`
  reduces any **subset**-controlled single-qubit gate `mcCtrlSingleQubit enc S j Ũ` to an exact
  product of the **terminal** gate class `IsToffoliOrSingleQubitGate` (a `Toffoli`/`CNOT`/`NOT`, or
  an uncontrolled single-qubit unitary on a wire).

The bridge between them is N&C's §4.3 control-pattern normalisation: an arbitrary control pattern is
conjugated to the all-`1` pattern by a product of `X`-on-wire gates
(`exists_wireFlipProd_conj_ctrlSingleQubit_one`), and the all-`1`-controlled gate is the
full-control member of the subset-controlled family (`mcCtrlSingleQubit_univ_sdiff`:
`mcCtrlSingleQubit enc (univ \ {j}) j Ũ = ctrlSingleQubit enc j 1 Ũ`). The conjugating `X`-on-wire
gates are themselves terminal gates (uncontrolled single-qubit unitaries on a wire), so the whole
`ctrlSingleQubit` factor reduces to terminal gates.

## Results

* `exists_isToffoliOrSingleQubit_prod_eq_wireFlipProd` — a `wireFlipProd enc L` (the normalising
  product of `X`-on-wire gates) is an exact product of terminal gates: each factor is the
  uncontrolled `NOT`-on-wire `singleQubitOnWire enc k (Matrix.swap ℂ 0 1)`, itself terminal.
* `exists_isToffoliOrSingleQubit_prod_eq_of_isCtrlSingleQubit` — **the bridge**: a controlled
  single-qubit gate `IsCtrlSingleQubit enc g` is an exact product of terminal gates. Normalise the
  control pattern, identify the all-`1`-controlled gate as the full subset-controlled gate, and
  discharge it with the §4.3 reduction; the two normalising `wireFlipProd` conjugation factors are
  terminal-gate products.
* `exists_isToffoliOrSingleQubit_prod_eq_of_forall_isCtrlSingleQubit` — the list step: a list all of
  whose members are controlled single-qubit gates yields one flattened list of terminal gates with
  the same product (list induction, concatenating the per-factor bridges).
* `exists_isToffoliOrSingleQubit_list_prod_eq` — **the headline**: for an encoding
  `enc : (Fin m → Fin 2) ≃ Fin d`
  with at least one qubit (`Nontrivial (Fin m → Fin 2)`) and any `U ∈ U(d)`, there is an explicit
  list `gates`, **every** member an `IsToffoliOrSingleQubitGate`, with `gates.prod = U`. Feeds the
  §4.5 controlled-single-qubit decomposition of `U` through the bridge. This is the *exact*
  gate-decomposition input the §4.5.3 approximation calculus (per-wire density
  `exists_phase_smul_singleQubitOnWire_mem_closure` + the chaining inequality
  `norm_listProd_sub_listProd_le`) will turn into approximate `n`-qubit universality over
  `H, S, CNOT, Toffoli`.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The normalising product of `X`-on-wire gates is a product of terminal gates.**
`wireFlipProd enc L` is by definition the product of `NOT`-on-wire gates
`singleQubitOnWire enc k (Matrix.swap ℂ 0 1)` over `k ∈ L`, and each such gate is an uncontrolled
single-qubit unitary on a wire (the `2 × 2` block `Matrix.swap ℂ 0 1 = X` is unitary,
`swapTwo_mem_unitaryGroup`), hence an `IsToffoliOrSingleQubitGate`. -/
theorem exists_isToffoliOrSingleQubit_prod_eq_wireFlipProd (enc : (Fin m → Fin 2) ≃ Fin d)
    (L : List (Fin m)) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g ∈ gates, IsToffoliOrSingleQubitGate enc g) ∧ gates.prod = wireFlipProd enc L := by
  refine ⟨L.map fun k => singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1), ?_, rfl⟩
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨k, _, rfl⟩ := hg
  exact Or.inr ⟨k, Matrix.swap ℂ (0 : Fin 2) 1, swapTwo_mem_unitaryGroup, rfl⟩

/-- **A controlled single-qubit gate is an exact product of `Toffoli`/`CNOT`/single-qubit gates.**
For `IsCtrlSingleQubit enc g` (so `g = ctrlSingleQubit enc j c Ũ` with `Ũ ∈ U(2)`) there is a list
`gates`, every member an `IsToffoliOrSingleQubitGate`, with `gates.prod = g`.

Proof (N&C §4.3): normalise the control pattern to all-`1` by conjugating with a product of
`X`-on-wire gates (`exists_wireFlipProd_conj_ctrlSingleQubit_one`,
`g = wireFlipProd enc L.reverse * ctrlSingleQubit enc j 1 Ũ * wireFlipProd enc L`); the
all-`1`-controlled gate is the full subset-controlled gate
(`mcCtrlSingleQubit_univ_sdiff`,
`ctrlSingleQubit enc j 1 Ũ = mcCtrlSingleQubit enc (univ \ {j}) j Ũ`), reduced to terminal gates by
the §4.3 spare-wire-free reduction `exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit'`; and
the two conjugating `wireFlipProd` factors are terminal-gate products
(`exists_isToffoliOrSingleQubit_prod_eq_wireFlipProd`). Concatenating the three lists gives the
result. -/
theorem exists_isToffoliOrSingleQubit_prod_eq_of_isCtrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d)
    {g : Matrix (Fin d) (Fin d) ℂ} (hg : IsCtrlSingleQubit enc g) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g' ∈ gates, IsToffoliOrSingleQubitGate enc g') ∧ gates.prod = g := by
  obtain ⟨j, c, Ũ, hŨ, rfl⟩ := hg
  obtain ⟨L, _hL, hnorm⟩ := exists_wireFlipProd_conj_ctrlSingleQubit_one enc j c Ũ
  have hjS : j ∉ (Finset.univ \ {j} : Finset (Fin m)) := by simp
  obtain ⟨Gm, hGm, hGmprod⟩ :=
    exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit' enc hjS hŨ
  obtain ⟨Gr, hGr, hGrprod⟩ := exists_isToffoliOrSingleQubit_prod_eq_wireFlipProd enc L.reverse
  obtain ⟨Gl, hGl, hGlprod⟩ := exists_isToffoliOrSingleQubit_prod_eq_wireFlipProd enc L
  refine ⟨Gr ++ Gm ++ Gl, ?_, ?_⟩
  · exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨hGr, hGm⟩, hGl⟩
  · rw [List.prod_append, List.prod_append, hGrprod, hGlprod, ← hGmprod,
      mcCtrlSingleQubit_univ_sdiff, hnorm]

/-- **A list of controlled single-qubit gates flattens to a list of terminal gates with the same
product.** If every member of `cgates` is an `IsCtrlSingleQubit`, there is a single list `gates`,
every member an `IsToffoliOrSingleQubitGate`, with `gates.prod = cgates.prod`. Proved by list
induction, concatenating the per-factor terminal-gate expansions
(`exists_isToffoliOrSingleQubit_prod_eq_of_isCtrlSingleQubit`). -/
theorem exists_isToffoliOrSingleQubit_prod_eq_of_forall_isCtrlSingleQubit
    (enc : (Fin m → Fin 2) ≃ Fin d) :
    ∀ cgates : List (Matrix (Fin d) (Fin d) ℂ), (∀ g ∈ cgates, IsCtrlSingleQubit enc g) →
      ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
        (∀ g ∈ gates, IsToffoliOrSingleQubitGate enc g) ∧ gates.prod = cgates.prod := by
  intro cgates
  induction cgates with
  | nil => intro _; exact ⟨[], by simp, rfl⟩
  | cons g cg ih =>
    intro hall
    obtain ⟨gG, hgG, hgGprod⟩ := exists_isToffoliOrSingleQubit_prod_eq_of_isCtrlSingleQubit enc
      (hall g (List.mem_cons_self ..))
    obtain ⟨gR, hgR, hgRprod⟩ := ih fun g' hg' => hall g' (List.mem_cons_of_mem g hg')
    refine ⟨gG ++ gR, ?_, ?_⟩
    · exact List.forall_mem_append.2 ⟨hgG, hgR⟩
    · rw [List.prod_append, hgGprod, hgRprod, List.prod_cons]

/-- **Every unitary on an `m`-qubit register is an exact product of `Toffoli`/`CNOT`/single-qubit
gates** (Nielsen & Chuang §4.5 + §4.3, the exact-decomposition milestone of Exercise 4.43). For an
encoding `enc : (Fin m → Fin 2) ≃ Fin d` with at least one qubit (`Nontrivial (Fin m → Fin 2)`) and
any `U ∈ U(d)`, there is an explicit list `gates`, **every** member of which is an
`IsToffoliOrSingleQubitGate` (a `Toffoli`/`CNOT`/`NOT` or an uncontrolled single-qubit unitary on a
wire), with `gates.prod = U`.

Composes the §4.5 controlled-single-qubit decomposition (`exists_isCtrlSingleQubit_list_prod_eq`)
with the §4.3 reduction of each controlled single-qubit gate to terminal gates (the bridge
`exists_isToffoliOrSingleQubit_prod_eq_of_forall_isCtrlSingleQubit`). This is the *exact* gate
decomposition; the residual global phase on each uncontrolled wire gate — harmless, unlike a
relative phase on a controlled gate — is what the §4.5.3 approximation calculus then discharges to
obtain
approximate universality over `H, S, CNOT, Toffoli` on any number of qubits. -/
theorem exists_isToffoliOrSingleQubit_list_prod_eq [Nontrivial (Fin m → Fin 2)]
    (enc : (Fin m → Fin 2) ≃ Fin d) {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g ∈ gates, IsToffoliOrSingleQubitGate enc g) ∧ gates.prod = U := by
  obtain ⟨cgates, hcg, hcgprod⟩ := exists_isCtrlSingleQubit_list_prod_eq enc hU
  obtain ⟨gates, hgates, hgprod⟩ :=
    exists_isToffoliOrSingleQubit_prod_eq_of_forall_isCtrlSingleQubit enc cgates hcg
  exact ⟨gates, hgates, hgprod.trans hcgprod⟩

end AxQM.Concrete
