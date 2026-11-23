/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelControlledProduct
import AxQM.Concrete.TwoLevelDecomposition

/-!
# Concrete: every `2ⁿ × 2ⁿ` unitary is a product of controlled single-qubit gates (N&C §4.5)

(Nielsen & Chuang §4.5, p. 189–193 — the `n`-qubit lift, first stage.)

This file composes the two structural halves of §4.5 that are already in place:

* **§4.5.1** (`exists_twoLevelUnitaryList_prod_eq`, `Concrete/TwoLevelDecomposition.lean`) — every
  `d × d` unitary is an explicit product of *two-level* unitaries.
* **§4.5.2** (`twoLevelUnitary_isProd_ctrlSingleQubit`, `Concrete/TwoLevelControlledProduct.lean`) —
  a two-level unitary supported on two *distinct* encoded basis states `{enc s, enc t}` (`s ≠ t`) is
  an explicit product of controlled single-qubit gates.

Chaining them gives the §4.5 milestone that Exercise 4.43's `n`-qubit lift rests on: **any unitary
on an `m`-bit register (`enc : (Fin m → Fin 2) ≃ Fin d`, `m ≥ 1`) is an exact product of controlled
single-qubit gates.**

## The pieces

* `AxQM.Concrete.isProd_ctrlSingleQubit_of_isTwoLevelUnitary` — **the bridge**: *any*
  two-level unitary `V` (in the sense of `IsTwoLevelUnitary`, whose support pair `{p, q}` may be
  *degenerate*, `p = q`, i.e. a single-coordinate phase) is a product of controlled single-qubit
  gates. When `p ≠ q` this is `twoLevelUnitary_isProd_ctrlSingleQubit` applied at
  `(enc.symm p, enc.symm q)`. When `p = q` the support `{p}` sits inside `{p, p'}` for *any* other
  index `p'` (one exists because there is at least one qubit, `Nontrivial (Fin m → Fin 2)`), so `V`
  still satisfies the two-index support hypothesis at the distinct pair `(enc.symm p, p')` and the
  same theorem applies — the single-coordinate phase is realised as a controlled single-qubit gate
  with a diagonal `2 × 2` block on that (arbitrary) partner qubit.
* `AxQM.Concrete.isProd_ctrlSingleQubit_of_forall_isTwoLevelUnitary` — **the list step**:
  a list `L` all of whose members are two-level unitaries yields a single list of controlled
  single-qubit gates with the *same* product (concatenate the per-factor decompositions; list
  induction, one application of the bridge per factor).
* `AxQM.Concrete.exists_isCtrlSingleQubit_list_prod_eq` — **the headline**: for
  `enc : (Fin m → Fin 2) ≃ Fin d` with at least one qubit and any `U ∈ U(d)`, there is a list
  `gates`, every member a controlled single-qubit gate (`IsCtrlSingleQubit enc`), with
  `gates.prod = U`. It feeds the §4.5.1 two-level decomposition of `U` through the list step.

The `Nontrivial (Fin m → Fin 2)` hypothesis is exactly "at least one qubit" (`m ≥ 1`): on a
zero-qubit system (`Fin 1`) there are no gates at all, and the §4.5.1 decomposition of a genuine
`d × d` unitary contains single-coordinate `phaseShift` factors (`p = q`) that can only be hosted as
controlled gates once a partner qubit exists, so this is the faithful hypothesis, not a weakening.

The statement of Exercise 4.43 is in `AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The bridge — any two-level unitary is a product of controlled single-qubit gates.** For an
encoding `enc : (Fin m → Fin 2) ≃ Fin d` with at least one qubit (`Nontrivial (Fin m → Fin 2)`),
every `V` with `IsTwoLevelUnitary V` equals `gates.prod` for a list `gates` all of whose members are
controlled single-qubit gates (`IsCtrlSingleQubit enc`).

`IsTwoLevelUnitary` allows a *degenerate* support pair `p = q` (a single-coordinate phase). Such a
`V` is supported on `{p} ⊆ {p, enc t}` for any second bit-string `t ≠ enc.symm p` (one exists by
nontriviality), so it satisfies the two-*distinct*-index support hypothesis of
`twoLevelUnitary_isProd_ctrlSingleQubit` at `(enc.symm p, t)`; the honest two-level case `p ≠ q`
uses that theorem directly at `(enc.symm p, enc.symm q)`. -/
theorem isProd_ctrlSingleQubit_of_isTwoLevelUnitary {m d : ℕ} [Nontrivial (Fin m → Fin 2)]
    (enc : (Fin m → Fin 2) ≃ Fin d) {V : Matrix (Fin d) (Fin d) ℂ}
    (hV : IsTwoLevelUnitary V) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g ∈ gates, IsCtrlSingleQubit enc g) ∧ V = gates.prod := by
  obtain ⟨hVu, p, q, hsupp⟩ := hV
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨t, ht⟩ := exists_ne (enc.symm p)
    refine twoLevelUnitary_isProd_ctrlSingleQubit enc (s := enc.symm p) (t := t)
      (fun h => ht h.symm) hVu ?_
    intro i j hij
    simp only [Equiv.apply_symm_apply] at hij
    exact hsupp i j (hij.imp (fun h => ⟨h.1, h.1⟩) (fun h => ⟨h.1, h.1⟩))
  · refine twoLevelUnitary_isProd_ctrlSingleQubit enc (s := enc.symm p) (t := enc.symm q)
      (fun h => hpq (enc.symm.injective h)) hVu ?_
    intro i j hij
    simp only [Equiv.apply_symm_apply] at hij
    exact hsupp i j hij

/-- **The list step — a list of two-level unitaries becomes a list of controlled single-qubit gates
with the same product.** If every member of `L` is a two-level unitary then there is a list `gates`,
every member a controlled single-qubit gate, with `gates.prod = L.prod`. Proved by list induction,
applying `isProd_ctrlSingleQubit_of_isTwoLevelUnitary` to each factor and concatenating the
results. -/
theorem isProd_ctrlSingleQubit_of_forall_isTwoLevelUnitary {m d : ℕ} [Nontrivial (Fin m → Fin 2)]
    (enc : (Fin m → Fin 2) ≃ Fin d) :
    ∀ L : List (Matrix (Fin d) (Fin d) ℂ), (∀ V ∈ L, IsTwoLevelUnitary V) →
      ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
        (∀ g ∈ gates, IsCtrlSingleQubit enc g) ∧ gates.prod = L.prod := by
  intro L
  induction L with
  | nil => exact fun _ => ⟨[], by simp, by simp⟩
  | cons V L' ih =>
    intro hL
    obtain ⟨gV, hgV, hgVprod⟩ :=
      isProd_ctrlSingleQubit_of_isTwoLevelUnitary enc (hL V (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨gL', hgL', hgL'prod⟩ := ih (fun W hW => hL W (List.mem_cons.mpr (Or.inr hW)))
    refine ⟨gV ++ gL', ?_, ?_⟩
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with h | h
      · exact hgV g h
      · exact hgL' g h
    · rw [List.prod_append, ← hgVprod, hgL'prod, List.prod_cons]

/-- **Every unitary on an `m`-bit register is an exact product of controlled single-qubit gates
(N&C §4.5).** For an encoding `enc : (Fin m → Fin 2) ≃ Fin d` with at least one qubit
(`Nontrivial (Fin m → Fin 2)`) and any `U ∈ U(d)`, there is an explicit list `gates`, **every**
member of which is a controlled single-qubit gate (`IsCtrlSingleQubit enc`), with `gates.prod = U`.

This is the composition of the two §4.5 halves: the §4.5.1 two-level decomposition
(`exists_twoLevelUnitaryList_prod_eq`) writes `U` as a product of two-level unitaries, and the list
step turns each two-level factor into controlled single-qubit gates (via the §4.5.2 gate-list form).
It is the first stage of Exercise 4.43's `n`-qubit lift: reducing an arbitrary unitary to the
controlled single-qubit gates that are later realised over `H, S, CNOT, Toffoli`. -/
theorem exists_isCtrlSingleQubit_list_prod_eq {m d : ℕ} [Nontrivial (Fin m → Fin 2)]
    (enc : (Fin m → Fin 2) ≃ Fin d) {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ gates : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ g ∈ gates, IsCtrlSingleQubit enc g) ∧ gates.prod = U := by
  obtain ⟨L, hL, hLprod⟩ := exists_twoLevelUnitaryList_prod_eq U hU
  obtain ⟨gates, hgates, hgprod⟩ :=
    isProd_ctrlSingleQubit_of_forall_isTwoLevelUnitary enc L hL
  exact ⟨gates, hgates, hgprod.trans hLprod⟩

end AxQM.Concrete
