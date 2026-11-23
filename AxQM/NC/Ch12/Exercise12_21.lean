/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Theorem12_15
import AxQM.Postulates.API.CatalysisStates

/-!
# Nielsen & Chuang, Exercise 12.21 (Entanglement catalysis)

*(N&C p. 577.)*

Entanglement catalysis: |psi> cannot go to |phi> by LOCC but |psi>|c> can.

## The formalisation

By **Nielsen's theorem** (N&C Theorem 12.15, `AxQM.State.loccConvertible_iff_majorize`), a
bipartite pure state `|ψ⟩` can be converted to `|φ⟩` by (one-way) LOCC iff the reduced density
operators satisfy `ρ_ψ ≺ ρ_φ` — i.e. iff their eigenvalue distributions (the squared Schmidt
coefficients) are majorization-ordered. So the two physical claims are statements about the *reduced
states*, whose eigenvalue distributions are the concrete spectra `λ_ψ = (0.4, 0.4, 0.1, 0.1)`,
`λ_φ = (0.5, 0.25, 0.25, 0)`, `λ_c = (0.6, 0.4)`.

The two theorems, stated for `State.LOCCConvertible`, are:

* `catalysisState_not_loccConvertible` : `¬ ρ_ψ.LOCCConvertible ρ_φ` — **no** direct LOCC
  conversion `|ψ⟩ → |φ⟩`, because `λ_ψ` is *not* majorized by `λ_φ` (their two largest entries sum
  to `0.8 > 0.75`);
* `catalysisState_tmul_loccConvertible` : `(ρ_ψ ⊗ ρ_c).LOCCConvertible (ρ_φ ⊗ ρ_c)` — the
  **catalysed** conversion `|ψ⟩|c⟩ → |φ⟩|c⟩` succeeds, because `λ_ψ ⊗ λ_c` *is* majorized by
  `λ_φ ⊗ λ_c` — the borrowed entanglement `|c⟩` is returned unchanged.

Together these are entanglement catalysis.

### Supporting results

The reduced states `catalysisStatePsi`, `catalysisStatePhi`, `catalysisStateCat` and the
identification of their eigenvalue distributions with the concrete spectra are in
`AxQM/Postulates/API/CatalysisStates.lean`. The concrete majorization facts (`¬ λ_ψ ≺ λ_φ` and
`λ_ψ⊗λ_c ≺ λ_φ⊗λ_c`) are in `AxQM/Concrete/EntanglementCatalysis.lean`. The bridge from a state's
eigenvalue distribution to its concrete spectrum uses that majorization depends only on the value
multisets (`majorize_congr_multiset`, `ToMathlib/Analysis/Convex/Majorization.lean`). As for
Nielsen's theorem (Theorem 12.15) and Exercise 12.20, LOCC-convertibility of a bipartite pure state
is captured by `State.LOCCConvertible` on the reduced states.
-/

open AxQM.Concrete

namespace AxQM

/-- **No direct LOCC conversion `|ψ⟩ → |φ⟩`** (N&C Exercise 12.21, first part). The reduced state
`ρ_ψ` cannot be converted to `ρ_φ` by (one-way) LOCC, because `λ_ψ = (0.4, 0.4, 0.1, 0.1)` is not
majorized by `λ_φ = (0.5, 0.25, 0.25, 0)`. Via Nielsen's theorem
(`State.loccConvertible_iff_majorize`) LOCC-convertibility is majorization of the eigenvalue
distributions, which agree (as multisets) with the concrete spectra, so this reduces to
`Concrete.catalysisPsiSpec_not_majorize`. -/
theorem catalysisState_not_loccConvertible :
    ¬ catalysisStatePsi.LOCCConvertible catalysisStatePhi := by
  rw [State.loccConvertible_iff_majorize]
  intro hmaj
  have hmaj' : Majorize catalysisStatePsi.eigenvalueDist catalysisStatePhi.eigenvalueDist := hmaj
  exact catalysisPsiSpec_not_majorize ((majorize_congr_multiset
    catalysisStatePsi_eigenvalueDist_multiset
    catalysisStatePhi_eigenvalueDist_multiset).mp hmaj')

/-- **Catalysed LOCC conversion `|ψ⟩|c⟩ → |φ⟩|c⟩`** (N&C Exercise 12.21, catalysis part). Tensoring
both states with the catalyst `ρ_c` makes the conversion possible: `ρ_ψ ⊗ ρ_c` *can* be converted to
`ρ_φ ⊗ ρ_c` by (one-way) LOCC, because the product spectrum `λ_ψ ⊗ λ_c` *is* majorized by
`λ_φ ⊗ λ_c` (`Concrete.catalysisTensorSpec_majorize`) — the borrowed entanglement `|c⟩` is returned
unchanged. Together with `catalysisState_not_loccConvertible`, this is entanglement catalysis. -/
theorem catalysisState_tmul_loccConvertible :
    (catalysisStatePsi.tmul catalysisStateCat).LOCCConvertible
      (catalysisStatePhi.tmul catalysisStateCat) := by
  rw [State.loccConvertible_iff_majorize]
  exact (majorize_congr_multiset catalysisStatePsiCat_eigenvalueDist_multiset
    catalysisStatePhiCat_eigenvalueDist_multiset).mpr catalysisTensorSpec_majorize

end AxQM
