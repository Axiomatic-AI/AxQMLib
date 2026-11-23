/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliString
import AxQM.Concrete.DensityMatrixRealDimension

/-!
# Concrete: how many NMR tomography experiments for `n` spins (Nielsen & Chuang, Exercise 7.46)

This file supplies the combinatorial core answering **Nielsen & Chuang, Exercise 7.46** (p. 337,
§7.7.4) — *"How many [tomography] experiments are sufficient for three spins? Necessary?"* — the
direct sequel to Exercise 7.45, whose answer for **two** spins is *nine*. Everything here is stated
in terms of index/combinatorial data (`Fin n → Fin 3`, `Fin n → Fin 4`, `Finset`,
`Concrete.pauliString`/`pauliBasis`). The statement of Exercise 7.46 is in
`AxQM/NC/Ch7/Exercise7_46.lean`; compare the NMR exercises 7.44 (logical labeling) and 4.46 (the `4ⁿ
− 1` parameter count this exercise reuses).

## The physics of NMR state tomography (N&C §7.7.4, eqs. 7.166–7.168)

An `n`-spin density matrix expands in the `4ⁿ` Pauli strings `P_g = σ_{g₁} ⊗ ⋯ ⊗ σ_{gₙ}`
(`Concrete.pauliString`, `g : Fin n → Fin 4` choosing `{I, X, Y, Z}` per spin), and by the trace
orthogonality `tr(P_g P_h) = 2ⁿ δ_{gh}` (N&C eq. 7.167, generalized; `pauliString_trace_mul`) is
reconstructed from the `4ⁿ` coefficients `tr(ρ P_g)` — of which one, `tr(ρ P_0) = tr ρ = 1`, is
fixed by normalization, leaving `4ⁿ − 1` free real numbers (`Exercise4_46`;
`finrank_tracelessSelfAdjoint_matrix_two_pow`). Measurement of the NMR observable (N&C eq. 7.143),
*preceded by single-qubit pulses*, reads out these coefficients (eq. 7.168).

The scheme of Exercise 7.45 applies, to each spin independently, one of three pre-rotations
`{I, R_x, R_y}` — equivalently, it **measures each spin in one of three bases** `{Z, Y, X}`. We
model a measurement configuration as a **setting** `s : Fin n → Fin 3` (a basis per spin). Under
setting `s`, a Pauli string `P_g` is read out exactly when each of its non-identity factors matches
that spin's measured basis: `SettingObserves s g`, i.e. `∀ i, g i = 0 ∨ g i = (s i).succ` (the
three non-identity Pauli indices `1, 2, 3 : Fin 4` are `(·).succ` of the three bases `0, 1, 2 :
Fin 3`). A finite family of settings `T` is **tomographically complete** when *every* non-identity
Pauli string is observed by some setting in `T` (`TomographyComplete T`) — then all `4ⁿ − 1`
informative coefficients are measured, and with the normalization-fixed identity coefficient the
whole state is determined (`TomographyComplete.matrix_ext`).

## The answer

* **Sufficient.** The full family of all `3ⁿ` settings is complete (`tomographyComplete_univ`): for
  three spins, `3³ = 27` experiments suffice (`nmrTomographyExperiments_three`), extending the
  `3² = 9` of Exercise 7.45 (`nmrTomographyExperiments_two`).
* **Necessary.** `3ⁿ` is also necessary — indeed the complete family is *unique*
  (`TomographyComplete.eq_univ`): a *full-weight* Pauli string `P_{s.succ}` (every factor
  non-identity) is observed by the **single** setting `s`, so completeness forces every setting into
  `T`. Hence any complete family has exactly `3ⁿ` settings (`TomographyComplete.card_eq`): for three
  spins, **27** experiments are both sufficient and necessary.
* **Information count.** Independently, reconstructing an `n`-spin state requires determining
  `4ⁿ − 1` real parameters (`Exercise4_46`); for three spins, `4³ − 1 = 63`
  (`nmrTomographyParams_three`). Each of the `3ⁿ` settings reads out `2ⁿ` coefficients
  (`card_settingObserves`), so the `27` experiments over-determine the `63` parameters — the two
  numbers answer *"how many experiments"* vs *"how many real parameters"*, the two halves of the
  exercise's question.

## Fidelity

The three-basis-per-spin scheme is exactly Exercise 7.45's `{I, R_x, R_y}` construction (whose
two-spin count `9` is reproduced here), read as a product-basis measurement. Both directions are
proved: `3ⁿ` settings suffice **and** are necessary (with the completeness family pinned uniquely to
`univ`), and completeness genuinely determines the density matrix (`matrix_ext`), not merely covers
an abstract index set. No dimension is specialized and no hypothesis is added beyond `0 < n` (needed
only for necessity; `n = 0` has no spins to measure). The answer is neither weakened nor overstated.
-/

open Matrix
open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The tomography scheme: settings and observability -/

/-- A **measurement setting** `s : Fin n → Fin 3` (one of three bases `{Z, Y, X}` per spin, realized
by the pre-pulses `{I, R_x, R_y}`) **observes** the Pauli string `g : Fin n → Fin 4` when each of
`g`'s non-identity factors matches that spin's measured basis: `∀ i, g i = 0 ∨ g i = (s i).succ`.
The three non-identity Pauli indices `1, 2, 3 : Fin 4` are the images `(·).succ` of the three
bases `0, 1, 2 : Fin 3`; a factor `g i = 0` (identity) is observed under any basis. -/
def SettingObserves (s : Fin n → Fin 3) (g : Fin n → Fin 4) : Prop :=
  ∀ i, g i = 0 ∨ g i = (s i).succ

instance (s : Fin n → Fin 3) : DecidablePred (SettingObserves s) := fun g =>
  inferInstanceAs (Decidable (∀ i, g i = 0 ∨ g i = (s i).succ))

/-- A finite family of settings `T` is **tomographically complete** when every non-identity Pauli
string `g` is observed by some setting in `T`. Then the measurements determine all `4ⁿ − 1`
informative Pauli coefficients of the state, and — with the normalization-fixed identity coefficient
`tr ρ = 1` — the whole density matrix (`TomographyComplete.matrix_ext`). This is the precise reading
of "`T` provides sufficient data from which `ρ` can be reconstructed" (Exercise 7.45). -/
def TomographyComplete (T : Finset (Fin n → Fin 3)) : Prop :=
  ∀ g : Fin n → Fin 4, g ≠ 0 → ∃ s ∈ T, SettingObserves s g

/-- Each setting `s` observes its own **full-weight** Pauli string `P_{s.succ}` (the one with every
factor non-identity, `g i = (s i).succ`): trivially, each factor matches. -/
theorem settingObserves_succ (s : Fin n → Fin 3) :
    SettingObserves s (fun i => (s i).succ) := fun _ => Or.inr rfl

/-- A full-weight Pauli string `P_{s.succ}` is observed **only** by its own setting `s`: since every
factor `(s i).succ ≠ 0`, the observability disjunct forces `(s i).succ = (s' i).succ`, hence
`s = s'` by injectivity of `Fin.succ`. This uniqueness is the engine of necessity. -/
theorem eq_of_settingObserves_succ {s s' : Fin n → Fin 3}
    (h : SettingObserves s' (fun i => (s i).succ)) : s' = s := by
  funext i
  rcases h i with h0 | hmatch
  · exact absurd h0 (Fin.succ_ne_zero (s i))
  · exact (Fin.succ_injective 3 hmatch).symm

/-! ### Sufficiency: all `3ⁿ` settings are complete -/

/-- **Sufficiency.** The full family of all `3ⁿ` settings is tomographically complete: any Pauli
string `g` is observed by the setting matching `g`'s non-identity factors (`s i = (g i).pred` where
`g i ≠ 0`, arbitrary elsewhere). For three spins this is the `27`-experiment scheme; for two spins
the `9` of Exercise 7.45. -/
theorem tomographyComplete_univ :
    TomographyComplete (Finset.univ : Finset (Fin n → Fin 3)) := by
  intro g _
  refine ⟨fun i => if h : g i = 0 then 0 else (g i).pred h, Finset.mem_univ _, fun i => ?_⟩
  by_cases h : g i = 0
  · exact Or.inl h
  · refine Or.inr ?_
    simp only [dite_eq_right h]
    exact (Fin.succ_pred (g i) h).symm

/-! ### Necessity: `3ⁿ` settings are necessary, and the complete family is unique -/

/-- **Necessity (uniqueness).** The *only* tomographically complete family is the full one: for each
setting `s`, its full-weight string `P_{s.succ}` (which is `≠ 0` when there is at least one spin) is
observed **only** by `s` (`eq_of_settingObserves_succ`), so completeness forces `s ∈ T`. Hence
`T = univ`. Requires `0 < n` — with no spins every family, even the empty one, is vacuously
complete. -/
theorem TomographyComplete.eq_univ (hn : 0 < n) {T : Finset (Fin n → Fin 3)}
    (hT : TomographyComplete T) : T = Finset.univ := by
  refine Finset.eq_univ_of_forall fun s => ?_
  have hne : (fun i => (s i).succ) ≠ (0 : Fin n → Fin 4) := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hn
    intro hcontra
    have hi := congrFun hcontra i
    simp only [Pi.zero_apply] at hi
    exact Fin.succ_ne_zero (s i) hi
  obtain ⟨s', hs'T, hobs⟩ := hT _ hne
  exact (eq_of_settingObserves_succ hobs) ▸ hs'T

/-- **The number of NMR tomography experiments for `n` spins**: `3ⁿ`, both sufficient
(`tomographyComplete_univ`) and necessary (`TomographyComplete.card_eq`). -/
def nmrTomographyExperiments (n : ℕ) : ℕ := 3 ^ n

/-- The number of settings for `n` spins is `nmrTomographyExperiments n = 3ⁿ`, i.e.
`Fintype.card (Fin n → Fin 3)`. -/
theorem card_univ_setting :
    (Finset.univ : Finset (Fin n → Fin 3)).card = nmrTomographyExperiments n := by
  change (Finset.univ : Finset (Fin n → Fin 3)).card = 3 ^ n
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **The count.** For `0 < n` spins, any tomographically complete family has exactly
`nmrTomographyExperiments n = 3ⁿ` settings (it is `univ`, `TomographyComplete.eq_univ`): `3ⁿ`
experiments are both sufficient (`tomographyComplete_univ`) and necessary. -/
theorem TomographyComplete.card_eq (hn : 0 < n) {T : Finset (Fin n → Fin 3)}
    (hT : TomographyComplete T) : T.card = nmrTomographyExperiments n := by
  rw [hT.eq_univ hn, card_univ_setting]

/-- Each experiment (setting `s`) reads out exactly `2ⁿ` Pauli coefficients: the strings it observes
are those choosing, per spin, either the identity factor `0` or the matched basis `(s i).succ` — two
options each. Via the bijection `(Fin n → Fin 2) ≃ {g | SettingObserves s g}` sending a per-spin bit
`b` to `if b i = 0 then 0 else (s i).succ`. -/
theorem card_settingObserves (s : Fin n → Fin 3) :
    (Finset.univ.filter (fun g : Fin n → Fin 4 => SettingObserves s g)).card = 2 ^ n := by
  have hset : (Finset.univ.filter (fun g : Fin n → Fin 4 => SettingObserves s g))
      = Fintype.piFinset (fun i => ({0, (s i).succ} : Finset (Fin 4))) := by
    ext g
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    unfold SettingObserves
    simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  rw [hset, Fintype.card_piFinset,
    Finset.prod_congr rfl (fun i _ => Finset.card_pair (Fin.succ_ne_zero (s i)).symm),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The reconstruction is genuine: completeness determines the density matrix

The identity coefficient is pinned by the trace via the general Pauli-basis facts
`Concrete.pauliString_const_zero` (`P_0 = I`) and `Concrete.trace_pauliString_mul_eq_repr`
(`tr(P_m · M) = (pauliBasis.repr M m) · 2ⁿ`, the tomography readout functional, N&C eq. 7.168),
both living with the Pauli API in `Concrete/PauliString.lean`. -/

/-- **Genuine reconstruction.** If a family `T` is tomographically complete, then two density
matrices `M₁, M₂` agreeing on the trace (`tr M₁ = tr M₂`, the fixed normalization) and on every
observed Pauli coefficient are equal. In words: the measured data of a complete tomography scheme
determine the state — "sufficient data from which `ρ` can be reconstructed" (Exercise 7.45), now
proved for the `n`-spin scheme. The coefficient at `g = 0` is pinned by the trace
(`trace_pauliString_mul_eq_repr`, `pauliString_const_zero`); every other coefficient by
completeness; and equal Pauli coordinates force `M₁ = M₂` (`pauliBasis`). -/
theorem TomographyComplete.matrix_ext {T : Finset (Fin n → Fin 3)}
    (hT : TomographyComplete T)
    {M₁ M₂ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ}
    (htr : M₁.trace = M₂.trace)
    (hobs : ∀ g : Fin n → Fin 4, (∃ s ∈ T, SettingObserves s g) →
        pauliBasis.repr M₁ g = pauliBasis.repr M₂ g) :
    M₁ = M₂ := by
  have hrepr : ∀ g, pauliBasis.repr M₁ g = pauliBasis.repr M₂ g := by
    intro g
    by_cases hg : g = 0
    · subst hg
      have hP0 : pauliString (0 : Fin n → Fin 4) = 1 := pauliString_const_zero
      have e1 := trace_pauliString_mul_eq_repr M₁ (0 : Fin n → Fin 4)
      have e2 := trace_pauliString_mul_eq_repr M₂ (0 : Fin n → Fin 4)
      rw [hP0, Matrix.one_mul] at e1 e2
      have hcancel : pauliBasis.repr M₁ 0 * (2 : ℂ) ^ n = pauliBasis.repr M₂ 0 * (2 : ℂ) ^ n := by
        rw [← e1, ← e2, htr]
      exact mul_right_cancel₀ (pow_ne_zero n two_ne_zero) hcancel
    · exact hobs g (hT g hg)
  exact pauliBasis.repr.injective (Finsupp.ext hrepr)

/-! ### The numeric answers -/

/-- Two spins: `3² = 9` experiments — Exercise 7.45's "nine experiments". -/
theorem nmrTomographyExperiments_two : nmrTomographyExperiments 2 = 9 := by
  norm_num [nmrTomographyExperiments]

/-- **Exercise 7.46, sufficient & necessary count.** Three spins: `3³ = 27` experiments. -/
theorem nmrTomographyExperiments_three : nmrTomographyExperiments 3 = 27 := by
  norm_num [nmrTomographyExperiments]

/-- **Exercise 7.46, real-parameter count.** Reconstructing a three-spin state requires determining
`4³ − 1 = 63` real numbers (`Exercise4_46`, specialized to `n = 3`). -/
theorem nmrTomographyParams_three :
    Module.finrank ℝ (tracelessSelfAdjoint (2 ^ 3)) = 63 := by
  rw [finrank_tracelessSelfAdjoint_matrix_two_pow]; norm_num

end AxQM.Concrete
