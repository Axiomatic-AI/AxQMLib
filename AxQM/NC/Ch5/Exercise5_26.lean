/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Fourier.FiniteAbelian.SubgroupCharacterSum

/-!
# Nielsen & Chuang, Exercise 5.26 — re-expressing (5.77) for the Abelian hidden subgroup problem

*(N&C p. 242, §5.4.3 "The hidden subgroup problem".)*

Re-express (5.77) to show determining l'_i lets one sample from the cyclic subgroup K_{p_i} of K.

In the Abelian-HSP algorithm the quantum Fourier transform of a function constant on the cosets of a
hidden subgroup `K ≤ G` produces a state whose amplitude at the character index `ℓ` is governed by

> `∑_{h ∈ K} e^{-2πi ℓ·h/|G|} = |K|`   (5.77)

— the condition for `ℓ` to be a possible measurement outcome. Writing `G = ℤ_{p₁} × ⋯ × ℤ_{p_M}` as
a product of cyclic groups of prime-power order (the structure theorem), the character factorizes,

> `e^{2πi ℓ·g/|G|} = ∏ᵢ e^{2πi ℓᵢ·gᵢ/pᵢ}`   (5.78),

and the exercise's premise is that this "also decomposes `K`", i.e. `K = ∏ᵢ K_{pᵢ}` (the primary
decomposition). Substituting (5.78) into (5.77) re-expresses the single character sum as a product
of independent per-factor sums, and the maximal-sum condition (5.77) then holds iff *each*
per-factor sum is maximal — i.e. iff each component `ℓᵢ` annihilates `K_{pᵢ}`. Determining `ℓᵢ`
thus yields a constraint on (a sample from the dual of) the cyclic subgroup `K_{pᵢ}`, the exercise.

## The declarations

Equation (5.77) is a **scalar identity about a character sum** `∑_{h ∈ K} χ_ℓ(h)` over a subgroup of
a finite abelian group, that is, harmonic analysis on finite abelian groups (compare the closely
related Fourier computation of Exercise 5.20).

All in `ToMathlib/Analysis/Fourier/FiniteAbelian/SubgroupCharacterSum.lean` (namespace `AddChar`),
for a finite abelian group / character valued in a characteristic-zero integral domain `R` (e.g.
`ℂ`) and a finite index `ι` of finite abelian factors `Aᵢ`:

* `AddChar.sum_subgroup_eq_natCard_iff` — **(5.77) as an annihilator condition**: for a subgroup
  `K ≤ A`, `∑_{h ∈ K} ψ h = |K| ↔ ∀ h ∈ K, ψ h = 1` (otherwise the sum vanishes). The character
  index `ℓ` survives exactly when `χ_ℓ` is trivial on `K`.
* `AddChar.pi` / `AddChar.pi_apply` — the **product character** `(∏ᵢ ψᵢ)(g) = ∏ᵢ ψᵢ (gᵢ)`: the
  abstract form of the phase factorization (5.78).
* `AddChar.pi_eq_one_on_pi_iff` — the **annihilator factorizes**:
  `(∀ g ∈ ∏ᵢ Kᵢ, ∏ᵢ ψᵢ gᵢ = 1) ↔ ∀ i, ∀ h ∈ Kᵢ, ψᵢ h = 1`. `ℓ` annihilates `K` iff each `ℓᵢ`
  annihilates `K_{pᵢ}` — the crisp "sample from `K_{pᵢ}`" statement.
* `AddChar.sum_pi_subgroup_prod` — the **literal re-expression of (5.77) via (5.78)**:
  `∑_{h ∈ ∏ᵢ Kᵢ} ∏ᵢ ψᵢ hᵢ = ∏ᵢ (∑_{h ∈ Kᵢ} ψᵢ h)`.
* `AddChar.sum_pi_subgroup_eq_natCard_iff` — the **decoupled maximal-sum condition**:
  `(∑_{h ∈ ∏ᵢ Kᵢ} ∏ᵢ ψᵢ hᵢ = |∏ᵢ Kᵢ|) ↔ ∀ i, (∑_{h ∈ Kᵢ} ψᵢ h = |Kᵢ|)`.
* `AddChar.sum_pi_subgroup_zmod_prod` / `AddChar.sum_pi_subgroup_zmod_eq_natCard_iff` — the two
  results above specialised to the exercise's **literal group `G = ∏ᵢ ℤ_{nᵢ}`** with the explicit
  root-of-unity phase `ZMod.stdAddChar (ℓᵢ · hᵢ) = e^{2πi ℓᵢ hᵢ / nᵢ}`.

## Design notes

* **Fidelity.** The results are stated for an arbitrary finite index `ι` and
  arbitrary finite abelian factors `Aᵢ` with an arbitrary character-valued domain `R`. This is
  *strictly more general* than — hence faithful to — the concrete `∏ᵢ ℤ_{pᵢ}` / `e^{-2πi·/·}`
  instance of the book, since a character of `ℤ_{pᵢ}` *is* such a phase (Pontryagin duality). The
  `_zmod_` corollaries pin this down at the exercise's literal group with the explicit exponential.
  N&C's `-` sign is the conjugate character (index `-ℓ`); it is immaterial to (5.77), which is a
  condition on the *set* of surviving indices (the annihilator).
* **The premise `K = ∏ᵢ Kᵢ`.** The exercise states "this also decomposes `K`" — the primary
  decomposition of the subgroup — as a given; it is modelled by `K = AddSubgroup.pi Set.univ K′`,
  the product of the factors `K_{pᵢ}`, not derived here.
-/
