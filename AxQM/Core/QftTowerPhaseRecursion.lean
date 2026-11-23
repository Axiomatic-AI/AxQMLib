/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftTowerProductForm

/-!
# The tower QFT product form's phase recursion (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) is assembled by an induction over the tower
depth. Its computational core is Nielsen & Chuang's product form (eq. 5.4, stated as
`qftTowerEvolution_evolvePure_towerKet_towerProd`): the transported QFT sends the
tower ket `towerKet n b` to the product state `towerProd n (fun i => qubitPhasePlus
(qftTowerWirePhase n b i))`, a phased-plus state `(|0⟩ + e^{iθᵢ}|1⟩)/√2` on every wire. This file
supplies the **recursion of the per-wire phases** `qftTowerWirePhase` that the outer induction's
peel matches — the number-theoretic heart of "peel the head Figure 5.1 gates off `qftTowerEvolution
(n+1)` and recurse on the tail".

## The recursion (and why the naive head-first peel fails)

Writing `J = Σₘ b(m) 2ⁿ⁺¹⁻ᵐ` for the big-endian register index of the input, output wire `i` of the
`(n+1)`-tower carries the binary fraction `qftTowerWirePhase (n+1) b i = 2π·J / 2^{i+1}` (mod 2π).
The **symmetric** DFT bakes the Figure 5.1 output-reversal into this formula, so:

* the *first* `n+1` output wires `i.castSucc` (`i : Fin (n+1)`) carry exactly the phases of the
  **`n`-tower QFT of the tail input** `Fin.tail b`: `qftTowerWirePhase (n+1) b i.castSucc` and
  `qftTowerWirePhase n (Fin.tail b) i` differ by `2π·(b 0)·2^{i.rev}`, an integer multiple of `2π`
  (`qftTowerWirePhase_castSucc`), hence the phased-plus states agree
  (`qftTowerWirePhase_castSucc_qubitPhasePlus`);
* the *new*, last output wire `Fin.last (n+1)` carries the **full** fraction of all input bits,
  `π·(b 0) + Σₜ (Fin.tail b t)·2π·2^{t.rev}/2ⁿ⁺²` (`qftTowerWirePhase_last`) — precisely the angle
  a head Hadamard (`π·b 0`) then the head-wire controlled-`Rₖ` phase cascade (the sum) imprints.

The key consequence for the reduction's design: it is the *last* output wire, not the head wire,
that the head Figure 5.1 gates produce, so a naive head-first peel `qftTowerEvolution (n+1) = tail ∘
head-cascade ∘ head-Hadamard` with `tail = (qftTowerEvolution n).onRight qubit` does **not** hold —
the tail wire phases `qftTowerWirePhase (n+1) b (j.succ)` are *not* those of the `n`-tower QFT. The
faithful peel routes the head-produced wire to the last position by a cyclic wire permutation (the
Figure 5.1 swap layer, `Evolution.qtowerPermWires`); these phase identities are its bookkeeping.

The `2π`-periodicity of `qubitPhasePlus` this uses is `qubitPhasePlus_two_pi_nat_add`, in
`AxQM/Postulates/API/PhasedPlus.lean`; the arithmetic register peel
`finFunctionFinEquiv_rev_succ` is a `private` lemma of this file.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Peel the leading bit off the big-endian register index.** The register index the bridge
identifies `towerKet (n+1) b` with, `Σₘ b(m.rev)·2ᵐ` over `Fin (n+2)`, splits as `(b 0)·2ⁿ⁺¹` (the
most-significant bit `b 0`, on wire `Fin.last` after the reversal) plus the tail register index
`Σₘ (Fin.tail b)(m.rev)·2ᵐ` over `Fin (n+1)`. The arithmetic behind the tower QFT phase recursion:
splitting the leading input wire out of the Fourier sum. `private` — a pure-arithmetic one-off with
no physics content, kept local to this file, matching the library's convention for
`finFunctionFinEquiv` helpers (cf. the `private` `finFunctionFinEquiv_symm_last_eq_div` in
`Core/QftTowerBasis`). -/
private theorem finFunctionFinEquiv_rev_succ (n : ℕ) (b : Fin (n + 2) → Fin 2) :
    ((finFunctionFinEquiv (fun m => b m.rev) : Fin (2 ^ (n + 2))) : ℕ)
      = (b 0 : ℕ) * 2 ^ (n + 1)
        + ((finFunctionFinEquiv (fun m => (Fin.tail b) m.rev) : Fin (2 ^ (n + 1))) : ℕ) := by
  rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply, Fin.sum_univ_castSucc, Fin.rev_last,
    Fin.val_last, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.rev_castSucc, Fin.val_castSucc]
  rfl

/-- **The tower QFT phase recursion (tail wires).** The first `n+1` output wires of the
`(n+1)`-tower QFT carry exactly the phases of the `n`-tower QFT of the tail input `Fin.tail b`, up
to an integer multiple of `2π`:

  `qftTowerWirePhase (n+1) b i.castSucc = 2π·(b 0)·2^{i.rev} + qftTowerWirePhase n (Fin.tail b) i`.

Substituting the leading-bit peel `finFunctionFinEquiv_rev_succ` of the register index into the
phase formula: the extra term is the leading input bit `b 0`, which only shifts the phase by an
integer
multiple of `2π` on these wires (`2^{i.rev}` is a natural number). -/
theorem qftTowerWirePhase_castSucc (n : ℕ) (b : Fin (n + 2) → Fin 2) (i : Fin (n + 1)) :
    qftTowerWirePhase (n + 1) b i.castSucc
      = 2 * Real.pi * (((b 0 : ℕ) * 2 ^ (i.rev : ℕ) : ℕ) : ℝ)
        + qftTowerWirePhase n (Fin.tail b) i := by
  rw [qftTowerWirePhase, qftTowerWirePhase, Fin.rev_castSucc, finFunctionFinEquiv_rev_succ,
    Fin.val_succ, pow_succ (2 : ℝ) (i.rev : ℕ), pow_succ (2 : ℝ) (n + 1)]
  push_cast
  field_simp

/-- **The tower QFT phase recursion, at the level of the phased-plus output wires.** On the first
`n+1` output wires, the transported `(n+1)`-tower QFT and the transported `n`-tower QFT of the tail
input produce the *same* phased-plus state:

  `qubitPhasePlus (qftTowerWirePhase (n+1) b i.castSucc) = qubitPhasePlus (qftTowerWirePhase n
  (Fin.tail b) i)`.

The `2π·(b 0)·2^{i.rev}` phase difference (`qftTowerWirePhase_castSucc`) is invisible to the
phased-plus state (`qubitPhasePlus_two_pi_nat_add`). This is the per-wire statement the outer
induction's peel matches against the tail recursion `(qftTowerEvolution n).onRight qubit`. -/
theorem qftTowerWirePhase_castSucc_qubitPhasePlus (n : ℕ) (b : Fin (n + 2) → Fin 2)
    (i : Fin (n + 1)) :
    qubitPhasePlus (qftTowerWirePhase (n + 1) b i.castSucc)
      = qubitPhasePlus (qftTowerWirePhase n (Fin.tail b) i) := by
  rw [qftTowerWirePhase_castSucc, qubitPhasePlus_two_pi_nat_add]

/-- **The tower QFT phase recursion (the new last wire).** The last output wire of the `(n+1)`-tower
QFT — the wire the recursion *adds* — carries the full binary fraction of all input bits:

  `qftTowerWirePhase (n+1) b (Fin.last (n+1))
    = π·(b 0) + Σₜ (Fin.tail b t)·(2π·2^{t.rev}/2ⁿ⁺²)`.

This is exactly the phase a head Hadamard (contributing `π·(b 0)`, since `H|b₀⟩ = |+_{π·b₀}⟩`)
followed by the head control wire's controlled-`Rₖ` phase cascade (contributing the sum, one term
`2π·2^{t.rev}/2ⁿ⁺²` per tail wire `t`) imprints — the Figure 5.1 head layer the reduction defers the
measurement past. Proved by peeling the leading bit `b 0` (contributing `π·(b 0)`) out of the
register index and re-indexing the remaining Fourier sum over the tail wires by `Fin.rev`. -/
theorem qftTowerWirePhase_last (n : ℕ) (b : Fin (n + 2) → Fin 2) :
    qftTowerWirePhase (n + 1) b (Fin.last (n + 1))
      = Real.pi * (b 0 : ℕ)
        + ∑ t : Fin (n + 1),
            (Fin.tail b t : ℕ) * (2 * Real.pi * 2 ^ (t.rev : ℕ) / 2 ^ (n + 2)) := by
  rw [qftTowerWirePhase, Fin.rev_last, finFunctionFinEquiv_rev_succ, finFunctionFinEquiv_apply,
    Fin.val_zero, pow_zero, mul_one,
    -- Re-index the tail register sum `Σₘ (tail b)(m.rev)·2ᵐ` over the wires `t = m.rev`.
    show (∑ m : Fin (n + 1), ((Fin.tail b m.rev : Fin 2) : ℕ) * 2 ^ (m : ℕ) : ℕ)
        = ∑ t : Fin (n + 1), ((Fin.tail b t : Fin 2) : ℕ) * 2 ^ (t.rev : ℕ) from
      Fintype.sum_equiv Fin.revPerm _ _ (fun m => by simp [Fin.rev_rev])]
  push_cast
  rw [mul_add, add_div, Finset.mul_sum, Finset.sum_div]
  congr 1
  · rw [pow_succ]
    field_simp
    ring
  · refine Finset.sum_congr rfl fun t _ => ?_
    ring

end AxQM
