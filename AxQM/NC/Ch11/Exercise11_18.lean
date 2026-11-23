/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyConcavity

/-!
# N&C Exercise 11.18 — Equality in the concavity inequality (11.79)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.18, p. 517.

The von Neumann entropy is a concave function of its input (§11.3.5, eq. (11.79)): for probabilities
`pᵢ ≥ 0` with `∑ᵢ pᵢ = 1` and states `ρᵢ`,

`∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`.

Exercise 11.18 asks to prove that this inequality is *strict* unless the components coincide — the
entropy is **strictly** concave: equality holds **iff all the `ρᵢ`s are the same**.

## The statement (this file)

`State.vonNeumannEntropy_mix_eq_sum_iff_forall_eq` is the exercise, stated with no side hypotheses,
in the literal "all the `ρᵢ`s are the same" form N&C prints. For a probability distribution `p` and
a family of states `ρ : ι → State S`,

`S(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ S(ρᵢ)  ↔  ∀ i j, 0 < pᵢ → 0 < pⱼ → ρ i = ρ j`.

The positive-weight guard `0 < pᵢ, 0 < pⱼ` is the precise reading of "all the `ρᵢ`s are the same":
components carrying **zero** weight do not enter the mixture `∑ᵢ pᵢ ρᵢ` and are genuinely free, so
they cannot be — and are not — constrained by an equality that only sees the mixture and the
weighted entropy sum. (Dropping the guard would make the biconditional *false*: pad any equality
case with an extra branch of weight `0` carrying an arbitrary, different state.) This is exactly the
subtlety N&C itself flags in the concavity discussion on p. 517 ("all the states `ρᵢ` **for which
`pᵢ > 0`** are identical").

## Where the reusable machinery lives

The proof uses the concavity development in
`AxQM/Postulates/API/EntropyConcavity.lean`, shared with Exercises 11.19–11.22 and the
Araki–Lieb equality conditions (Exercise 11.16):

* `State.sum_mul_quantumRelativeEntropy_mix` — the **mixing identity**
  `∑ᵢ pᵢ S(ρᵢ ‖ μ) = S(μ) − ∑ᵢ pᵢ S(ρᵢ)` (`μ = ∑ᵢ pᵢ ρᵢ`); the algebraic heart, needs no
  faithfulness.
* `State.sum_mul_vonNeumannEntropy_le_vonNeumannEntropy_mix'` — the concavity inequality (11.79)
  itself, `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`, with no faithfulness hypothesis.
* `State.vonNeumannEntropy_mix_eq_sum_iff'` — the equality condition in the equivalent
  "every positive-weight component equals the mixture" form, `… ↔ ∀ i, 0 < pᵢ → ρ i = μ`, again with
  no faithfulness hypothesis.

Those use the support condition (each positive-weight component is supported inside the mixture,
`State.hasSupportLE_mix`, so Klein's inequality and its equality condition apply without demanding
a faithful mixture); the statement of this exercise is the consequence below.

## Proof route and faithfulness

Rather than N&C's own argument (concavity from subadditivity via an auxiliary index system `B`, with
the equality condition read off the subadditivity equality condition `ρ_AB = ρ_A ⊗ ρ_B`), the
formalisation uses the equivalent, more direct relative-entropy identity

`S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ) = ∑ᵢ pᵢ S(ρᵢ ‖ ∑ⱼ pⱼ ρⱼ)`.

The right-hand side is a sum of non-negative terms (Klein's inequality via the support condition),
so the gap is `≥ 0` (concavity) and vanishes iff each positive-weight term does, i.e. iff each such
`ρᵢ` equals the mixture `μ` (Klein's equality condition, `S(ρ ‖ σ) = 0 ↔ ρ = σ`) — equivalently, iff
all positive-weight `ρᵢ` coincide. The last step is the equivalence: "all coincide" ⟺ "each
equals `μ`" is `State.mix_eq_of_forall_pos_eq` (a mixture whose positive-weight components all equal
a fixed state is that state) run forwards and backwards.

The finite real-valued relative-entropy engine (`cfc Real.log`) would need a **faithful** second
argument for the raw Klein inequality; the support-condition form used here removes that requirement
entirely — only the *support* containment `supp ρᵢ ⊆ supp μ` is needed, and it holds automatically
for the mixture. Hence **no faithfulness hypothesis appears**: the statement is Exercise 11.18 in
full generality, for arbitrary (possibly rank-deficient) states `ρᵢ`.

The faithful-mixture specialisation `State.vonNeumannEntropy_mix_eq_sum_iff`
(`IsStrictlyPositive μ.op`) is in `AxQM/Postulates/API/EntropyConcavity.lean`; the
maximally-mixed reference of the maximal-entropy uniqueness result (Exercise 11.19) is full rank. It
is a corollary of the general statement here.
-/

namespace AxQM

variable {S : QSystem}

/-- **Strict concavity of the von Neumann entropy** (Nielsen & Chuang **Exercise 11.18**, p. 517).
For a probability distribution `p` and a family of states `ρ : ι → State S`, equality holds in the
concavity inequality (11.79) `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)`,

`S(∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ S(ρᵢ)`,

**iff all the components carrying positive weight are the same**,
`∀ i j, 0 < pᵢ → 0 < pⱼ → ρ i = ρ j`.

This is the literal form of N&C's "equality holds iff all the `ρᵢ`s are the same"; the
positive-weight guard is the exercise's own qualifier "for which `pᵢ > 0`" (a zero-weight component
is absent from the mixture and hence unconstrained). No faithfulness hypothesis is needed — the
statement is fully general (arbitrary, possibly rank-deficient `ρᵢ`).

Proof: apply the faithfulness-free equality condition
`State.vonNeumannEntropy_mix_eq_sum_iff'` (equality ↔ every positive-weight component equals the
mixture `μ`), then convert between "each equals `μ`" and "all coincide": forwards, two components
equal to `μ` are equal to each other; backwards, `State.mix_eq_of_forall_pos_eq` identifies `μ` with
the common value. See the module docstring for the shared concavity development this builds on. -/
theorem State.vonNeumannEntropy_mix_eq_sum_iff_forall_eq {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S) :
    (State.mix p hp hsum ρ).vonNeumannEntropy = ∑ i, p i * (ρ i).vonNeumannEntropy
      ↔ ∀ i j, 0 < p i → 0 < p j → ρ i = ρ j := by
  rw [State.vonNeumannEntropy_mix_eq_sum_iff' p hp hsum ρ]
  constructor
  · -- each positive-weight component equals the mixture ⇒ any two coincide
    intro hall i j hpi hpj
    rw [hall i hpi, hall j hpj]
  · -- all positive-weight components coincide ⇒ each equals the mixture `μ`
    intro hall i hpi
    exact (State.mix_eq_of_forall_pos_eq p hp hsum ρ (ρ i) fun j hpj => hall j i hpj hpi).symm

end AxQM
