/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RankMajorization
import AxQM.NC.Ch2.Problem2_2

/-!
# Nielsen–Chuang, Exercise 12.24 — the Schmidt number is LOCC-monotone

N&C §12.5.2, p. 580: LOCC cannot increase the Schmidt number of a bipartite pure state (its number
of non-zero Schmidt coefficients), and hence cannot increase the number of Bell pairs shared by
Alice and Bob.

## What is formalised

* `AxQM.PureState.schmidtNumber_le_of_reducedLeft_loccConvertible` — **the Schmidt number
  cannot be increased by LOCC.** If `|ψ⟩` can be converted to `|φ⟩` by one-way LOCC — encoded, as in
  Nielsen's theorem, by `ψ.toState.reducedLeft.LOCCConvertible φ.toState.reducedLeft` (Alice's
  measurement carrying her marginal `ρ_ψ` to `ρ_φ`) — then `φ.schmidtNumber ≤ ψ.schmidtNumber`.

* `AxQM.PureState.bellCount_le_of_reducedLeft_loccConvertible` — **the number of Bell
  states cannot be increased by LOCC.** A shared resource of `k` Bell pairs is a bipartite pure
  state of Schmidt number `2 ^ k` (a single Bell pair `|Φ⁺⟩` has Schmidt number `2 = 2 ^ 1`,
  `bellPhiPlus_schmidtNumber`; `k` independent pairs multiply the Schmidt spectra to `2 ^ k`). So if
  `ψ` carries `m` Bell pairs (`ψ.schmidtNumber = 2 ^ m`) and `φ` carries `n` (`φ.schmidtNumber =
  2 ^ n`), LOCC-convertibility forces `2 ^ n ≤ 2 ^ m`, hence `n ≤ m`: the Bell-pair count is
  non-increasing.

## Proof

Both are corollaries of Nielsen's theorem (N&C Theorem 12.15). Its forward direction
`State.LOCCConvertible.majorize` turns the LOCC hypothesis into majorization of the reduced states
`ρ_ψ ≺ ρ_φ`; the spectral bridge `State.rank_le_of_majorize` (a majorized state has at least as
many non-zero eigenvalues) then gives `ρ_φ.rank ≤ ρ_ψ.rank`; and the Schmidt number *is* the
reduced-state rank (`schmidtNumber_eq_rank_reducedLeft`, N&C Problem 2.2). The Bell-count corollary
adds only the strict monotonicity of `k ↦ 2 ^ k` (`Nat.pow_le_pow_iff_right`).

## Fidelity of the formalisation

As in `Theorem12_15`, "by LOCC" is expressed at the density-operator level
as the one-way measurement condition `State.LOCCConvertible`,
which N&C's own Proposition 12.14 shows is the general form of any finite-round LOCC protocol acting
on the reduced states. The Bell-count statement takes the `2 ^ k` Schmidt spectrum of a
`k`-Bell-pair resource as a hypothesis rather than constructing the tensor power `|Φ⁺⟩^{⊗k}`: the
content is precisely the monotonicity of that exponent, which is exactly what is proved. Nothing is
specialised or hypothesis-strengthened beyond N&C's own statement.
-/

namespace AxQM

namespace PureState

variable {S T : QSystem}

/-- **The Schmidt number cannot be increased by LOCC** (Nielsen–Chuang, Exercise 12.24, part 1). If
the bipartite pure state `|ψ⟩` can be converted to `|φ⟩` by one-way LOCC — encoded via Nielsen's
theorem as convertibility of Alice's reduced states,
`ψ.toState.reducedLeft.LOCCConvertible φ.toState.reducedLeft` — then the Schmidt number does not
increase: `φ.schmidtNumber ≤ ψ.schmidtNumber`.

The forward direction of Nielsen's theorem (`State.LOCCConvertible.majorize`) gives `ρ_ψ ≺ ρ_φ`,
whence `ρ_φ.rank ≤ ρ_ψ.rank` (`State.rank_le_of_majorize`); the Schmidt number is the reduced-state
rank (`schmidtNumber_eq_rank_reducedLeft`). -/
theorem schmidtNumber_le_of_reducedLeft_loccConvertible {ψ φ : PureState (S.compose T)}
    (h : ψ.toState.reducedLeft.LOCCConvertible φ.toState.reducedLeft) :
    φ.schmidtNumber ≤ ψ.schmidtNumber := by
  rw [ψ.schmidtNumber_eq_rank_reducedLeft, φ.schmidtNumber_eq_rank_reducedLeft]
  exact State.rank_le_of_majorize h.majorize

/-- **The number of Bell states cannot be increased by LOCC** (Nielsen–Chuang, Exercise 12.24,
part 2). A resource of `k` shared Bell pairs is a bipartite pure state of Schmidt number `2 ^ k`
(one Bell pair `|Φ⁺⟩` has Schmidt number `2 = 2 ^ 1`, `bellPhiPlus_schmidtNumber`). So if `ψ`
carries `m` Bell pairs (`ψ.schmidtNumber = 2 ^ m`) and `φ` carries `n` (`φ.schmidtNumber = 2 ^ n`),
and `|ψ⟩` can be converted to `|φ⟩` by LOCC, then `n ≤ m`: the Bell-pair count is non-increasing.

Immediate from part 1 (`schmidtNumber_le_of_reducedLeft_loccConvertible`) and the strict
monotonicity of `k ↦ 2 ^ k`. -/
theorem bellCount_le_of_reducedLeft_loccConvertible {ψ φ : PureState (S.compose T)} {m n : ℕ}
    (hψ : ψ.schmidtNumber = 2 ^ m) (hφ : φ.schmidtNumber = 2 ^ n)
    (h : ψ.toState.reducedLeft.LOCCConvertible φ.toState.reducedLeft) :
    n ≤ m := by
  have hle : (2 : ℕ) ^ n ≤ 2 ^ m := by
    rw [← hφ, ← hψ]
    exact schmidtNumber_le_of_reducedLeft_loccConvertible h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

end PureState

end AxQM
