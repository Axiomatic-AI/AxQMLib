/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Hadamard
import AxQM.Concrete.HadamardPauliConjugation
import AxQM.Concrete.PauliOuterProduct
import AxQM.Concrete.SqrtSwapCNOT
import ToMathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete: the augmented search oracle from one oracle call (N&C Exercise 6.5)

Nielsen & Chuang, §6.1.4 (p. 255): to search a space in which *more than half* the items may be
solutions, one **doubles** the search space by adjoining a single extra qubit `|q⟩`, and builds an
**augmented oracle** `O'` that marks an item `(x, q)` iff `x` is a solution *and* the extra bit is
`q = 0`. Exercise 6.5 asks to show `O'` can be constructed from **one call** to the original oracle
`O` together with **elementary quantum gates**.

The original bit-flip oracle acts on an index register `|x⟩` and a response qubit `|r⟩` by
`O|x⟩|r⟩ = |x⟩|r ⊕ f(x)⟩` (`f(x) = 1` iff `x` is a solution). Because `O` does not mix different
`x`, the whole construction acts block-by-block in `x`: on the block of a fixed item `x` the oracle
is the single-qubit bit flip `X^{f(x)}` on the response, and the circuit acts on the two remaining
qubits — the extra qubit `q` and the response `r` — as one fixed two-qubit unitary depending only on
`c := f(x) ∈ Bool`. **This file formalises that two-qubit response block**, which is the crux of the
one-call construction; the assembly over the whole search space and its grounding as an `Evolution`
are built separately.

## The construction (phase kickback)

With the response qubit `r` supplied as a fresh work qubit in `|0⟩`, the circuit is, in time order,
`X_r`, `CNOT_{q→r}`, `H_r`, then the single oracle call (a bit flip `X^c` on `r`), then
`H_r`, `CNOT_{q→r}`, `X_r`. Preparing `r` as `|−⟩` exactly when `q = 0` turns the one oracle call
into a **phase kickback**: it imprints `(-1)^{c}` precisely on the `q = 0` branch and nothing on the
`q = 1` branch — which is the mark "solution ∧ `q = 0`" the augmented oracle applies. The heart of
the proof is the Hadamard conjugation `H X H = Z` (`Concrete.hadamardC_mul_pauliX_mul_hadamardC`),
which collapses the oracle sandwich `H_r · X^c_r · H_r` to the diagonal `Z^c_r`, after which the two
flanking permutation gates make the whole block diagonal.

## What is formalised

* `oracleFlipResp c` — the oracle's action on the `(q, r)` block: the bit flip `X^c` on the response
  (identity on the extra qubit), `c : Bool` the solution flag of the item.
* `cnotExtraResp` (`CNOT_{q→r}`), `hadResp` (`H_r`), `xFlipResp` (`X_r`) — the elementary gates.
* `augResponseCircuit c` — the seven-factor block circuit built from **one** `oracleFlipResp c` and
  the elementary gates.
* `augResponseCircuit_eq_diagonal` — the key identity: the block circuit is the **diagonal** gate
  marking `|q⟩|r⟩` with `-1` iff `c` (a solution) and `q = r`. Equivalently
  (`augResponseCircuit_mulVec_ancilla`), on the physical input `r = 0` it applies the
  augmented-oracle phase `(-1)^{c ∧ (q = 0)}` and returns the work qubit to `|0⟩`.
* `augResponseCircuit_mem_unitaryGroup` — the block circuit is unitary (a product of unitaries).

## Related items

Every statement is about complex matrices (`Matrix`, `Matrix.kronecker`, `Matrix.diagonal`,
`Matrix.mulVec`) and the gate matrices `pauliX`/`pauliZ`/`hadamardC`. The assembly of the full
augmented oracle over the search space and its grounding as an `Evolution` build on this file; see
`AxQM/NC/Ch6/Exercise6_5.lean`.
-/

open Matrix Kronecker

namespace AxQM.Concrete

noncomputable section

/-- The single-qubit bit flip raised to a boolean power: `X^c` is `pauliX` when `c = true` and the
identity when `c = false`. Models the oracle's response-qubit action `X^{f(x)}` for an item whose
solution flag is `c`. -/
def flipPow (c : Bool) : Matrix (Fin 2) (Fin 2) ℂ := if c then pauliX else 1

@[simp] theorem flipPow_true : flipPow true = pauliX := rfl
@[simp] theorem flipPow_false : flipPow false = 1 := rfl

/-- The Hadamard conjugate of `X^c` is `Z^c`: `H · X^c · H = pauliZ` when `c = true` (N&C's
`H X H = Z`, `hadamardC_mul_pauliX_mul_hadamardC`) and `1` when `c = false` (`H² = I`). The single
identity that turns the one oracle call into a diagonal phase. -/
theorem hadamardC_mul_flipPow_mul_hadamardC (c : Bool) :
    hadamardC * flipPow c * hadamardC = if c then pauliZ else 1 := by
  cases c with
  | false => simp [flipPow, hadamardC_mul_self]
  | true => simpa [flipPow] using hadamardC_mul_pauliX_mul_hadamardC

/-- **The oracle call on the `(q, r)` response block:** the bit flip `X^c` on the response qubit `r`
and the identity on the extra qubit `q`, i.e. `1 ⊗ₖ X^c`. This is the *single* application of the
original oracle `O` used in the construction (restricted to one item's block). -/
def oracleFlipResp (c : Bool) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1 ⊗ₖ flipPow c

/-- **The elementary gate `X_r`:** `pauliX` on the response qubit, identity on the extra qubit. -/
def xFlipResp : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1 ⊗ₖ pauliX

/-- **The elementary gate `H_r`:** the Hadamard on the response qubit, identity on the extra
qubit. -/
def hadResp : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1 ⊗ₖ hadamardC

/-- **The elementary gate `CNOT_{q→r}`:** the controlled-NOT with the extra qubit `q` as control and
the response qubit `r` as target, `|q, r⟩ ↦ |q, r ⊕ q⟩`. A real symmetric permutation matrix. This
is the generic two-qubit `CNOT` (control = first qubit) `Concrete.twoQubitCNOT`
(`cnotExtraResp_eq_twoQubitCNOT`); it is kept here under the oracle-circuit name for readability,
and its gate lemmas are inherited from the canonical `twoQubitCNOT` rather than re-proved. -/
def cnotExtraResp : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun a b => if a.1 = b.1 ∧ a.2 = b.2 + b.1 then (1 : ℂ) else 0

/-- The oracle-circuit `CNOT_{q→r}` is the generic two-qubit `CNOT` `Concrete.twoQubitCNOT` (control
= first qubit): the two `if`-conditions coincide, `a.2 = b.2 + b.1 ↔ a = (b.1, b.1 + b.2)`, by
commutativity of `+` on `Fin 2`. This bridge lets the reusable gate lemmas about `twoQubitCNOT`
(`twoQubitCNOT_conjTranspose`/`_mul_self`/`_mem_unitaryGroup`, in `Concrete/SqrtSwapCNOT.lean`)
serve as the single source for `cnotExtraResp`'s unitary trio below. -/
theorem cnotExtraResp_eq_twoQubitCNOT : cnotExtraResp = twoQubitCNOT := by
  ext a b
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [cnotExtraResp, twoQubitCNOT_apply, Matrix.of_apply, Prod.mk.injEq]
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;> simp [Fin.add_def]

/-- **The one-call augmented-oracle block circuit.** In time order `X_r`, `CNOT_{q→r}`, `H_r`, the
oracle call `X^c_r`, `H_r`, `CNOT_{q→r}`, `X_r` — a palindrome of elementary gates around a
**single** oracle call `oracleFlipResp c`. Its net action is diagonal
(`augResponseCircuit_eq_diagonal`). -/
def augResponseCircuit (c : Bool) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  xFlipResp * cnotExtraResp * hadResp * oracleFlipResp c * hadResp * cnotExtraResp * xFlipResp

/-- The Hadamard sandwich of the oracle call is the diagonal `Z^c` on the response:
`H_r · X^c_r · H_r = 1 ⊗ₖ Z^c`. Follows from `H X^c H = Z^c` factored through the Kronecker product
(`Matrix.mul_kronecker_mul`). This is where the *one* oracle call becomes a phase. -/
theorem hadResp_mul_oracleFlipResp_mul_hadResp (c : Bool) :
    hadResp * oracleFlipResp c * hadResp = 1 ⊗ₖ (if c then pauliZ else 1) := by
  rw [hadResp, oracleFlipResp, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hadamardC_mul_flipPow_mul_hadamardC, mul_one, mul_one]

/-- `CNOT_{q→r}` is an involution: `CNOT² = I`. It flips the response twice, restoring it. Inherited
from the canonical `twoQubitCNOT_mul_self` via `cnotExtraResp_eq_twoQubitCNOT`. -/
theorem cnotExtraResp_mul_self : cnotExtraResp * cnotExtraResp = 1 := by
  rw [cnotExtraResp_eq_twoQubitCNOT]; exact twoQubitCNOT_mul_self

/-- `CNOT_{q→r}` is Hermitian: it is a real symmetric permutation matrix. Inherited from the
canonical `twoQubitCNOT_conjTranspose` via `cnotExtraResp_eq_twoQubitCNOT`. -/
theorem cnotExtraResp_isHermitian : cnotExtraResp.IsHermitian := by
  rw [cnotExtraResp_eq_twoQubitCNOT]; exact twoQubitCNOT_conjTranspose

/-- `CNOT_{q→r}` is unitary (a Hermitian involution). -/
theorem cnotExtraResp_mem_unitaryGroup :
    cnotExtraResp ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  cnotExtraResp_isHermitian.mem_unitaryGroup cnotExtraResp_mul_self

/-- The boolean-power bit flip `X^c` is unitary. -/
theorem flipPow_mem_unitaryGroup (c : Bool) : flipPow c ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  cases c with
  | false => simp only [flipPow_false]; exact one_mem _
  | true => simp only [flipPow_true]; exact pauliX_mem_unitaryGroup

/-- **The key identity (N&C Exercise 6.5).** The one-call block circuit `augResponseCircuit c` is
the **diagonal** gate that marks `|q⟩|r⟩` with `-1` exactly when the item is a solution (`c`) and
`q = r` — and with `+1` otherwise. The oracle call is used once; the Hadamard conjugation
`H X^c H = Z^c` (`hadResp_mul_oracleFlipResp_mul_hadResp`) makes the middle diagonal, and the two
flanking permutation gates `CNOT_{q→r}`, `X_r` conjugate it to this final diagonal. -/
theorem augResponseCircuit_eq_diagonal (c : Bool) :
    augResponseCircuit c
      = Matrix.diagonal (fun p : Fin 2 × Fin 2 => if c ∧ p.1 = p.2 then (-1 : ℂ) else 1) := by
  have hre : augResponseCircuit c
      = xFlipResp * cnotExtraResp * (1 ⊗ₖ (if c then pauliZ else 1))
          * cnotExtraResp * xFlipResp := by
    rw [augResponseCircuit, ← hadResp_mul_oracleFlipResp_mul_hadResp c]
    simp only [mul_assoc]
  rw [hre]
  ext a b
  cases c <;>
    (fin_cases a <;> fin_cases b <;>
      simp [xFlipResp, cnotExtraResp, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_prod_type,
        Matrix.one_apply, pauliX, pauliZ])

/-- **The block circuit is unitary** — a product of the unitary elementary gates and the single
unitary oracle call. -/
theorem augResponseCircuit_mem_unitaryGroup (c : Bool) :
    augResponseCircuit c ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  have hx : xFlipResp ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker_mem_unitary (one_mem _) pauliX_mem_unitaryGroup
  have hh : hadResp ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker_mem_unitary (one_mem _) hadamardC_mem_unitaryGroup
  have ho : oracleFlipResp c ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker_mem_unitary (one_mem _) (flipPow_mem_unitaryGroup c)
  rw [augResponseCircuit]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem hx cnotExtraResp_mem_unitaryGroup) hh) ho) hh) cnotExtraResp_mem_unitaryGroup) hx

/-- **The physical work-qubit-`|0⟩` computational-basis state** `|q⟩|0⟩` of the `(q, r)` block: the
extra qubit carries `q` and the response (work) qubit is the fresh `|0⟩`. -/
def responseAncilla (q : Fin 2) : (Fin 2 × Fin 2) → ℂ := Pi.single (q, 0) 1

/-- **The augmented oracle from one oracle call (N&C Exercise 6.5), physical form.** On the work
qubit supplied in `|0⟩`, the one-call block circuit applies the augmented-oracle phase and returns
the work qubit to `|0⟩`: `augResponseCircuit c` acting on `|q⟩|0⟩` scales it by `-1` exactly when
the item is a solution (`c`) *and* the extra bit is `q = 0`, and by `+1` otherwise. This is
precisely the mark "solution ∧ `q = 0`" defining the augmented oracle `O'`. -/
theorem augResponseCircuit_mulVec_ancilla (c : Bool) (q : Fin 2) :
    augResponseCircuit c *ᵥ responseAncilla q
      = (if c ∧ q = 0 then (-1 : ℂ) else 1) • responseAncilla q := by
  rw [augResponseCircuit_eq_diagonal, responseAncilla]
  funext i
  rw [Matrix.mulVec_diagonal]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hi : i = (q, 0)
  · subst hi; simp
  · simp [hi]

end

end AxQM.Concrete
