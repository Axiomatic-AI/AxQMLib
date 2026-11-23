/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChi
import AxQM.Postulates.API.TwoPureMixtureEntropy
import AxQM.Postulates.API.FidelityPure
import AxQM.NC.Ch12.Problem12_1

/-!
# N&C Problem 12.2 — no-cloning from the monotonicity of the Holevo χ quantity

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Problem 12.2, p. 602:

Prove no-cloning by showing cloning non-orthogonal pure states increases chi.

The argument runs a two-element ensemble `{½, |ψ₁⟩; ½, |ψ₂⟩}` of pure states through the χ machinery
built in Problem 12.1:

* **Cloning strictly increases χ.** Both ensembles are pure, so their Holevo χ is the entropy of
  the mixture (`State.holevoChi_pure`). For the equiprobable two-pure-state mixture that
  entropy is `H((1 ± c)/2)` with `c = ‖⟨ψ₁ | ψ₂⟩‖` the overlap
  (`State.vonNeumannEntropy_mixPair_pure`). The cloned states `|ψᵢ⟩|ψᵢ⟩` have overlap
  `‖⟨ψ₁|ψ₂⟩⟨ψ₁|ψ₂⟩‖ = c²` (`TensorProduct.inner_tmul`); since `H((1 + ·)/2)` is strictly decreasing
  and `c² < c` for `0 < c < 1`, the cloned χ is strictly larger — this is
  `holevoChi_lt_holevoChi_clone`.
* **But a quantum process cannot increase χ.** This is exactly "the previous problem", N&C
  Problem 12.1(2) (`State.holevoChi_dilatedChannel_le`): the Holevo χ decreases under any quantum
  operation. A cloner is such an operation (present it by its Chapter-8 dilation on `S ⊗ S`, adjoin
  a blank target and an environment, evolve, discard the environment), so it would force the cloned
  χ *down*, contradicting the strict increase. Hence no cloner exists for non-orthogonal, distinct
  pure states — `no_cloning`.

We also record the textbook special case `no_cloning_unitary` (Wootters–Zurek): a *unitary* cloner
`U` on `S ⊗ S` is impossible, using only the unitary invariance of χ (`State.holevoChi_evolve`) in
place of the full operation-monotonicity.

## Non-orthogonality

"Non-orthogonal and distinct" is `0 < F(|ψ₁⟩, |ψ₂⟩) < 1`, phrased through the **fidelity**
`State.fidelity` rather than a raw inner product.
`F(|ψ₁⟩, |ψ₂⟩) = ‖⟨ψ₁ | ψ₂⟩‖ = c` for pure states
(`State.fidelity_toState_toState`, in `AxQM/Postulates/API/FidelityPure.lean`), so
`0 < F` is orthogonality's negation and `F < 1` is distinctness up to phase; the two boundary cases
`c = 0` (orthogonal) and `c = 1` (equal up to phase) are exactly where cloning is possible and the
argument gives no contradiction.

## Dependencies

The statements use `State.holevoChi`, `State.fidelity`, `State.dilatedChannel`,
`Evolution.evolve`/`evolvePure`, `State.tmul`, `PureState.tmul` and `PureState.toState`. The
proofs below use the bridge `State.fidelity_toState_toState` (fidelity equals overlap) from
`AxQM/Postulates/API/FidelityPure.lean`, and `State.vonNeumannEntropy_mixPair_pure`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The uniform two-point distribution `(½, ½)`, the weights of the equiprobable two-state ensemble
driving the no-cloning argument. -/
private def unif2 : Fin 2 → ℝ := ![1 / 2, 1 / 2]

private theorem unif2_nonneg : ∀ i, 0 ≤ unif2 i := by intro i; fin_cases i <;> norm_num [unif2]

private theorem unif2_sum : ∑ i, unif2 i = 1 := by norm_num [unif2, Fin.sum_univ_two]

/-- A two-element uniform mixture is the honest binary mixture: `mix (½, ½) [ρ, σ] = mixPair ½ ρ σ`.
Both density operators are `½ ρ + ½ σ` (`State.mix_op`, `State.mixPair_op`), so the states agree by
`State.ext`. Bridges the `State.mix`-based Holevo χ generator to the `State.mixPair`-based
two-pure-state entropy lemma. -/
private theorem mix_unif2_eq_mixPair (ρ : Fin 2 → State S) :
    State.mix unif2 unif2_nonneg unif2_sum ρ
      = State.mixPair (p := 1 / 2) (by norm_num) (by norm_num) (ρ 0) (ρ 1) := by
  apply State.ext
  rw [State.mix_op, Fin.sum_univ_two, State.mixPair_op]
  simp only [unif2, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **Cloning strictly increases the Holevo χ quantity** (the heart of Nielsen & Chuang
Problem 12.2). For two non-orthogonal, distinct pure states — `0 < F(|ψ₁⟩, |ψ₂⟩)` and
`F(|ψ₁⟩, |ψ₂⟩) < 1`, i.e. overlap `0 < c < 1` — the Holevo χ of the *cloned* equiprobable ensemble
`{½, |ψ₁⟩|ψ₁⟩; ½, |ψ₂⟩|ψ₂⟩}` strictly exceeds that of `{½, |ψ₁⟩; ½, |ψ₂⟩}`:

`χ({½, |ψᵢ⟩}) < χ({½, |ψᵢ⟩|ψᵢ⟩})`.

Both ensembles are pure, so their χ is the mixture entropy (`State.holevoChi_pure`), which for an
equiprobable two-pure-state mixture is `H((1 ± overlap)/2)`
(`State.vonNeumannEntropy_mixPair_pure`). The input overlap is `c`; the cloned overlap is
`‖⟨ψ₁|ψ₂⟩⟨ψ₁|ψ₂⟩‖ = c²` (`TensorProduct.inner_tmul`).
As `c² < c` for `0 < c < 1` and the symmetric binary entropy `H((1 ± ·)/2)` is strictly decreasing
(`Real.entropy_pair_lt`), the cloned entropy is strictly larger. -/
theorem holevoChi_lt_holevoChi_clone (ψ₁ ψ₂ : PureState S)
    (h0 : 0 < ψ₁.toState.fidelity ψ₂.toState) (h1 : ψ₁.toState.fidelity ψ₂.toState < 1) :
    State.holevoChi unif2 unif2_nonneg unif2_sum (fun i => (![ψ₁, ψ₂] i).toState)
      < State.holevoChi unif2 unif2_nonneg unif2_sum
          (fun i => (![ψ₁.tmul ψ₁, ψ₂.tmul ψ₂] i).toState) := by
  rw [State.fidelity_toState_toState] at h0 h1
  set c := ‖inner ℂ ψ₁.vec ψ₂.vec‖ with hc
  have hclone_overlap : ‖inner ℂ (ψ₁.tmul ψ₁).vec (ψ₂.tmul ψ₂).vec‖ = c ^ 2 := by
    rw [PureState.tmul_vec, PureState.tmul_vec]
    change ‖inner ℂ (ψ₁.vec ⊗ₜ[ℂ] ψ₁.vec) (ψ₂.vec ⊗ₜ[ℂ] ψ₂.vec)‖ = c ^ 2
    rw [TensorProduct.inner_tmul ℂ, norm_mul, ← hc]; ring
  rw [State.holevoChi_pure unif2 unif2_nonneg unif2_sum ![ψ₁, ψ₂],
    State.holevoChi_pure unif2 unif2_nonneg unif2_sum ![ψ₁.tmul ψ₁, ψ₂.tmul ψ₂],
    mix_unif2_eq_mixPair, mix_unif2_eq_mixPair]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [State.vonNeumannEntropy_mixPair_pure ψ₁ ψ₂,
    State.vonNeumannEntropy_mixPair_pure (ψ₁.tmul ψ₁) (ψ₂.tmul ψ₂),
    hclone_overlap, ← hc, show (1 - c ^ 2) / 2 = 1 - (1 + c ^ 2) / 2 from by ring]
  exact Real.entropy_pair_lt (by positivity) (by nlinarith [h0, h1]) (le_of_lt h1)
    (by rw [show 2 * ((1 + c ^ 2) / 2) - 1 = c ^ 2 from by ring, abs_of_nonneg (by positivity)]
        nlinarith [mul_pos h0 (sub_pos.mpr h1)])

/-- **The no-cloning theorem** (Nielsen & Chuang Problem 12.2), via the monotonicity of the Holevo χ
quantity under quantum operations. There is **no** cloning process for two non-orthogonal, distinct
pure states `|ψ₁⟩`, `|ψ₂⟩` (`0 < F(|ψ₁⟩, |ψ₂⟩) < 1`).

A cloning process is presented as a quantum operation on `S ⊗ S` by its Chapter-8 dilation
(N&C Problem 12.1(2), `State.dilatedChannel`): adjoin a blank target `|blank⟩` and an environment
`|ω⟩`, evolve by a unitary `U` on `(S ⊗ S) ⊗ C`, and discard the environment. Cloning means
`E(|ψᵢ⟩ ⊗ |blank⟩) = |ψᵢ⟩ ⊗ |ψᵢ⟩`. Then the Holevo χ of the cloned ensemble
`{½, |ψᵢ⟩|ψᵢ⟩}` equals `χ(E∘{½, |ψᵢ⟩ ⊗ |blank⟩})`, which by operation-monotonicity
(`State.holevoChi_dilatedChannel_le`, "the previous problem") is at most
`χ({½, |ψᵢ⟩ ⊗ |blank⟩}) = χ({½, |ψᵢ⟩})` (appending the fixed pure blank leaves χ unchanged,
`State.holevoChi_tmul_pure_right`). But `holevoChi_lt_holevoChi_clone` shows the cloned χ is
*strictly greater* — a contradiction. -/
theorem no_cloning {C : QSystem} (ψ₁ ψ₂ blank : PureState S) (U : Evolution ((S ⊗ S) ⊗ C))
    (ω : PureState C)
    (hclone₁ : State.dilatedChannel (ψ₁.toState.tmul blank.toState) U ω = (ψ₁.tmul ψ₁).toState)
    (hclone₂ : State.dilatedChannel (ψ₂.toState.tmul blank.toState) U ω = (ψ₂.tmul ψ₂).toState)
    (h0 : 0 < ψ₁.toState.fidelity ψ₂.toState)
    (h1 : ψ₁.toState.fidelity ψ₂.toState < 1) : False := by
  have hstrict := holevoChi_lt_holevoChi_clone ψ₁ ψ₂ h0 h1
  have hout : (fun i => (![ψ₁.tmul ψ₁, ψ₂.tmul ψ₂] i).toState)
      = fun i => State.dilatedChannel ((![ψ₁, ψ₂] i).toState.tmul blank.toState) U ω := by
    funext i
    fin_cases i
    · exact hclone₁.symm
    · exact hclone₂.symm
  have hle : State.holevoChi unif2 unif2_nonneg unif2_sum
        (fun i => (![ψ₁.tmul ψ₁, ψ₂.tmul ψ₂] i).toState)
      ≤ State.holevoChi unif2 unif2_nonneg unif2_sum (fun i => (![ψ₁, ψ₂] i).toState) := by
    rw [hout]
    calc State.holevoChi unif2 unif2_nonneg unif2_sum
            (fun i => State.dilatedChannel ((![ψ₁, ψ₂] i).toState.tmul blank.toState) U ω)
        ≤ State.holevoChi unif2 unif2_nonneg unif2_sum
            (fun i => (![ψ₁, ψ₂] i).toState.tmul blank.toState) :=
          State.holevoChi_dilatedChannel_le unif2 unif2_nonneg unif2_sum
            (fun i => (![ψ₁, ψ₂] i).toState.tmul blank.toState) U ω
      _ = State.holevoChi unif2 unif2_nonneg unif2_sum (fun i => (![ψ₁, ψ₂] i).toState) :=
          State.holevoChi_tmul_pure_right unif2 unif2_nonneg unif2_sum
            (fun i => (![ψ₁, ψ₂] i).toState) blank
  linarith [hstrict, hle]

/-- **The no-cloning theorem, unitary form** (Wootters–Zurek). There is **no** unitary `U` on
`S ⊗ S` cloning two non-orthogonal, distinct pure states from a blank target,
`U(|ψᵢ⟩ ⊗ |blank⟩) = |ψᵢ⟩ ⊗ |ψᵢ⟩`.

The special case of `no_cloning` in which the process is a bare unitary (no environment to discard).
It needs only the *invariance* of χ under a unitary (`State.holevoChi_evolve`) — not the full
operation-monotonicity — together with `State.holevoChi_tmul_pure_right`: the cloned χ equals
`χ({½, |ψᵢ⟩ ⊗ |blank⟩}) = χ({½, |ψᵢ⟩})`, contradicting the strict increase
`holevoChi_lt_holevoChi_clone`. -/
theorem no_cloning_unitary (ψ₁ ψ₂ blank : PureState S) (U : Evolution (S ⊗ S))
    (hclone₁ : U.evolvePure (ψ₁.tmul blank) = ψ₁.tmul ψ₁)
    (hclone₂ : U.evolvePure (ψ₂.tmul blank) = ψ₂.tmul ψ₂)
    (h0 : 0 < ψ₁.toState.fidelity ψ₂.toState)
    (h1 : ψ₁.toState.fidelity ψ₂.toState < 1) : False := by
  have hstrict := holevoChi_lt_holevoChi_clone ψ₁ ψ₂ h0 h1
  have hc1 : U.evolve ((ψ₁.tmul blank).toState) = (ψ₁.tmul ψ₁).toState := by
    rw [← toState_evolvePure, hclone₁]
  have hc2 : U.evolve ((ψ₂.tmul blank).toState) = (ψ₂.tmul ψ₂).toState := by
    rw [← toState_evolvePure, hclone₂]
  have hout : (fun i => (![ψ₁.tmul ψ₁, ψ₂.tmul ψ₂] i).toState)
      = fun i => U.evolve ((![ψ₁, ψ₂] i).tmul blank).toState := by
    funext i
    fin_cases i
    · exact hc1.symm
    · exact hc2.symm
  have heq : State.holevoChi unif2 unif2_nonneg unif2_sum
        (fun i => (![ψ₁.tmul ψ₁, ψ₂.tmul ψ₂] i).toState)
      = State.holevoChi unif2 unif2_nonneg unif2_sum (fun i => (![ψ₁, ψ₂] i).toState) := by
    rw [hout, State.holevoChi_evolve unif2 unif2_nonneg unif2_sum
      (fun i => ((![ψ₁, ψ₂] i).tmul blank).toState) U,
      show (fun i => ((![ψ₁, ψ₂] i).tmul blank).toState)
          = fun i => (![ψ₁, ψ₂] i).toState.tmul blank.toState from by
        funext i; rw [PureState.toState_tmul],
      State.holevoChi_tmul_pure_right unif2 unif2_nonneg unif2_sum
        (fun i => (![ψ₁, ψ₂] i).toState) blank]
  linarith [hstrict, heq]

end AxQM
