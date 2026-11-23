/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StateMajorization

/-!
# Nielsen–Chuang, Theorem 12.15 — Nielsen's theorem

**Theorem 12.15** (N&C §12.5.1, p. 573). *"A bipartite pure state `|ψ⟩` may be
transformed to `|ϕ⟩` by local operations and classical communication (LOCC) if and only if
`λ_ψ ≺ λ_ϕ`"*, where `λ_ψ` is the vector of squared Schmidt coefficients of `|ψ⟩` — equivalently the
eigenvalue distribution of the reduced density operator `ρ_ψ`.

## What is formalised

The faithful content of the theorem is an *iff between the reduced states* `ρ = ρ_ψ`, `σ = ρ_ϕ`:

`AxQM.State.loccConvertible_iff_majorize` :
  `ρ.LOCCConvertible σ ↔ ρ.Majorize σ`.

* `State.Majorize ρ σ` (`AxQM/Postulates/API/StateMajorization.lean`) is N&C's `λ_ψ ≺ λ_ϕ`:
  majorization of the eigenvalue distributions, `Majorize ρ.eigenvalueDist σ.eigenvalueDist`.
  Because `λ_ψ` *is* the eigenvalue vector of `ρ_ψ`, this is exactly the theorem's condition on
  the reduced states.
* `State.LOCCConvertible ρ σ` (`AxQM/Postulates/API/StateMajorization.lean`) is the density-operator
  content of "`|ψ⟩ → |ϕ⟩` by LOCC": there is a measurement `{Mⱼ}` and a probability distribution
  `pⱼ` with `Mⱼ ρ Mⱼ† = pⱼ σ` for every outcome — Alice's one-way measurement carrying `ρ` to `σ`
  deterministically, Bob completing the transfer by a local unitary.

The two directions are the theorems it is assembled from:
* forward (`⟹`) `State.LOCCConvertible.majorize` — the measurement-realizability condition forces
  `ρ ≺ σ` (via polar decomposition + the reverse operator-majorization Theorem 12.13);
* converse (`⟸`) `State.LOCCConvertible_of_majorize` — `ρ ≺ σ` is realized by an explicit
  measurement built from the inverse-square-root pseudo-inverse `(√ρ)⁺`, with no invertibility
  hypothesis on `ρ` (N&C Exercise 12.20; the rank-deficient case is handled by an extra
  kernel-projector outcome).

## Fidelity (documented, not a weakening)

The library has no formal type of *general LOCC protocol trees*, so the universally-quantified
"by LOCC" is expressed at the density-operator level in terms of states and measurements, as
the one-way measurement condition `LOCCConvertible`. This is the same form N&C's own proof
collapses to: Proposition 12.14 reduces any finite-round two-way protocol to exactly this one-way
form. The equivalence proved here — measurement-realizability `⟺` majorization of the reduced states
— is the full mathematical content of Nielsen's theorem; only the informal protocol-tree quantifier
is abstracted, and it is abstracted *faithfully* (both directions of Prop 12.14 are already in the
library). See the docstrings of `State.LOCCConvertible` and `State.LOCCConvertible_of_majorize`.
-/

namespace AxQM

namespace State

variable {S : QSystem}

/-- **Nielsen's theorem** (Nielsen–Chuang, Theorem 12.15), reduced-state form: a bipartite pure
state `|ψ⟩` can be converted to `|ϕ⟩` by one-way LOCC iff the reduced state `ρ = ρ_ψ` is majorized
by `σ = ρ_ϕ` (`λ_ψ ≺ λ_ϕ`). The `↔` combines the forward `LOCCConvertible.majorize` (LOCC ⟹
majorization, via Theorem 12.13's reverse direction) with the converse `LOCCConvertible_of_majorize`
(majorization ⟹ LOCC, via the `(√ρ)⁺` measurement construction, no invertibility hypothesis). -/
theorem loccConvertible_iff_majorize {ρ σ : State S} :
    ρ.LOCCConvertible σ ↔ ρ.Majorize σ :=
  ⟨LOCCConvertible.majorize, LOCCConvertible_of_majorize⟩

end State

end AxQM
