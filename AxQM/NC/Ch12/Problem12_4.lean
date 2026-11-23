/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MixPairTmul

/-!
# N&C Problem 12.4 — linearity forbids cloning

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Problem 12.4, p. 603:

Linearity forbids cloning: mixtures of rho1,rho2 not copied by linear procedure.

This is the *linearity* form of no-cloning (complementing `NC/Ch12/Problem12_2.lean`, the Holevo-χ
form): it uses **no** entropy, unitarity, or trace preservation — only that a copier is linear.

## The argument

Take the nontrivial mixture `ρ := p ρ₁ + (1 − p) ρ₂` for `0 < p < 1`. Linearity gives
```
𝓔(ρ ⊗ σ) = 𝓔(p (ρ₁ ⊗ σ) + (1 − p) (ρ₂ ⊗ σ)) = p 𝓔(ρ₁ ⊗ σ) + (1 − p) 𝓔(ρ₂ ⊗ σ)
         = p (ρ₁ ⊗ ρ₁) + (1 − p) (ρ₂ ⊗ ρ₂),
```
using `State.mixPair_tmul` (tensoring the fixed target `σ` onto the mixture distributes), linearity
(`hlinear`), and the cloning hypotheses. Correct copying would instead demand
`𝓔(ρ ⊗ σ) = ρ ⊗ ρ = (p ρ₁ + (1 − p) ρ₂) ⊗ (p ρ₁ + (1 − p) ρ₂)`. But these two candidate outputs are
**unequal**: their difference is `p (1 − p) (ρ₁ − ρ₂) ⊗ (ρ₁ − ρ₂) ≠ 0` since `ρ₁ ≠ ρ₂`
(`State.mixPair_tmul_self_ne_tmul_mixPair`). Hence `𝓔(ρ ⊗ σ) ≠ ρ ⊗ ρ`: the mixture is not copied.

## Modelling "a linear function `𝓔`"

The copier is a map `E : State (S ⊗ B) → State (S ⊗ S)` (data slot `S`, target slot `B` holding the
standard state; the copy lands on the doubled data system `S ⊗ S`). The book's hypothesis that `𝓔`
is **linear** is captured by `hlinear`: `E` sends every binary mixture to the corresponding mixture
of images,
```
E (p τ₁ + (1 − p) τ₂) = p (E τ₁) + (1 − p) (E τ₂).
```
This is exactly the restriction of linearity to the (convex, not linear) set of states — the only
consequence of linearity the proof uses, and one that every genuine quantum operation also
satisfies. Assuming just this mixture-affinity, rather than a full linear map on the raw operator
space, makes the theorem *stronger* (a weaker hypothesis). The statement involves only
`State.mixPair`, `State.tmul` and the abstract map `E`; the algebra on the underlying matrices
is discharged by the two lemmas of `AxQM/Postulates/API/MixPairTmul.lean` used below.

The conclusion `E (ρ ⊗ σ) ≠ ρ ⊗ ρ` is stated for every nontrivial weight `0 < p < 1` — N&C's "any
mixture of `ρ₁` and `ρ₂`" (the degenerate weights `p ∈ {0, 1}` give back `ρ₁` or `ρ₂`, which *are*
copied, so they are correctly excluded).
-/

noncomputable section

namespace AxQM

variable {S B : QSystem}

/-- **Linearity forbids cloning** (Nielsen & Chuang Problem 12.4). Let
`E : State (S ⊗ B) → State (S ⊗ S)` be a copying procedure that is **linear on states** — it
preserves every binary mixture (`hlinear`) — and let `σ : State B` be the fixed standard target
state. Suppose `E` correctly copies two *distinct* states `ρ₁ ≠ ρ₂` from the target,
`E (ρ₁ ⊗ σ) = ρ₁ ⊗ ρ₁` and `E (ρ₂ ⊗ σ) = ρ₂ ⊗ ρ₂`. Then for **any** nontrivial mixture
`ρ = p ρ₁ + (1 − p) ρ₂` (`0 < p < 1`), the procedure does **not** copy `ρ`:
```
E (ρ ⊗ σ) ≠ ρ ⊗ ρ.
```

The proof: linearity turns `E (ρ ⊗ σ)` into `p (ρ₁ ⊗ ρ₁) + (1 − p) (ρ₂ ⊗ ρ₂)` (`State.mixPair_tmul`
distributes the tensor over the mixture, then `hlinear` and the two cloning hypotheses), whereas
correct copying needs `ρ ⊗ ρ = (p ρ₁ + (1 − p) ρ₂) ⊗ (p ρ₁ + (1 − p) ρ₂)`; these differ by
`p (1 − p) (ρ₁ − ρ₂) ⊗ (ρ₁ − ρ₂) ≠ 0` (`State.mixPair_tmul_self_ne_tmul_mixPair`). -/
theorem linearity_forbids_cloning (E : State (S ⊗ B) → State (S ⊗ S))
    (hlinear : ∀ {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (τ₁ τ₂ : State (S ⊗ B)),
      E (State.mixPair hq0 hq1 τ₁ τ₂) = State.mixPair hq0 hq1 (E τ₁) (E τ₂))
    (σ : State B) {ρ₁ ρ₂ : State S} (hne : ρ₁ ≠ ρ₂)
    (hclone₁ : E (ρ₁.tmul σ) = ρ₁.tmul ρ₁) (hclone₂ : E (ρ₂.tmul σ) = ρ₂.tmul ρ₂)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    E ((State.mixPair hp0.le hp1.le ρ₁ ρ₂).tmul σ)
      ≠ (State.mixPair hp0.le hp1.le ρ₁ ρ₂).tmul (State.mixPair hp0.le hp1.le ρ₁ ρ₂) := by
  rw [State.mixPair_tmul, hlinear hp0.le hp1.le, hclone₁, hclone₂]
  exact State.mixPair_tmul_self_ne_tmul_mixPair hp0 hp1 hne

end AxQM
