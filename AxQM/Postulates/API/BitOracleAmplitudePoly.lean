/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BitOracleQueryCircuit
import AxQM.Concrete.MethodOfPolynomials
import ToMathlib.Analysis.InnerProductSpace.PurificationFreedom

/-!
# AxQM.Postulates.API — the amplitude–evaluation bridge (method of polynomials)

The final structural step of the **method of polynomials** (Nielsen & Chuang §6.7, eqs. 6.58–6.61):
the bridge that identifies the *physical* amplitudes of the bit-oracle query circuit
(`Postulates/API/BitOracleQueryCircuit.lean`) with the *formal* amplitude polynomials of
`AxQM/Concrete/MethodOfPolynomials.lean`. It is what turns the abstract degree
bound `totalDegree_polyQueryState_le` into the concrete statement N&C actually uses: the amplitude
`⟨k | ψ(X)⟩` of a `T`-query algorithm's output, *as a function of the oracle string* `X`, is one
polynomial of total degree `≤ T`.

## The bridge

Fix a `QuantumQueryProblem` — a register with computational basis `|i,b,j⟩` indexed by
`σ × Bool × ω` — with a unitary schedule `U : ℕ → Evolution S` and an input `ψ`. Two data determine
the
matching between the physical circuit and the polynomial backbone:

* `unitaryMatrix (U s)` — the matrix elements `⟨k| U_s |l⟩` of each schedule gate in the
  computational basis, feeding `constUnitaryStep`'s constant matrices;
* the input amplitudes `⟨l | ψ⟩` embedded as constants `C ⟨l | ψ⟩`, feeding `polyQueryState`'s
  `v₀`.

With these, `queryState_amplitude_eq_eval` proves by induction on the query count `t`:

`⟨k | ψ(X)_t⟩ = eval (boolPoint X) (polyQueryState (U · matrix) (⟨· | ψ⟩) t k)`.

The induction has one lemma per circuit element: a unitary layer expands by the coordinate identity
`OrthonormalBasis.inner_op_eq_sum` (matching `constUnitaryStep_eval`), and the bit-oracle acts on a
coordinate by the
XOR reindexing `bitOracle_inner_basis` (matching `bitOracleStep_eval_boolPoint`) — the two backbone
steps line up term-by-term because the query schedules were defined with the same convention.

The corollary `exists_polynomial_queryState_amplitude` reads off N&C's conclusion: there is *one*
polynomial `P` of total degree `≤ T`, independent of the oracle string `X`, whose evaluation at
`boolPoint X` is the answer amplitude `⟨k | ψ(X)⟩`. (`Postulates/API/BitOracleZeroError.lean`
feeds the answer-`0` amplitude into `Concrete.orZeroError_query_lower_bound_of_totalDegree_le`
to obtain `Q₀(OR) ≥ N`.)

The underlying amplitude polynomials and their degree bound are in `AxQM/Concrete/`; this file
supplies only the bridge between them and the physical circuit.
-/

open scoped InnerProductSpace
open MvPolynomial AxQM.Concrete

noncomputable section

namespace AxQM

variable {S : QSystem} {σ ω : Type*}

/-- **The bit-flip permutation is an involution** (as a permutation): `O_X` is self-inverse, so
`bitFlipPerm X (bitFlipPerm X p) = p`. Repackages `bitFlip_involutive` at the `Equiv.Perm` level,
the fact used to reindex the oracle sum in `bitOracle_inner_basis`. -/
theorem bitFlipPerm_bitFlipPerm (X : σ → Bool) (p : σ × Bool × ω) :
    bitFlipPerm X (bitFlipPerm X p) = p :=
  bitFlip_involutive X p

namespace QuantumQueryProblem

variable [Fintype σ] [Fintype ω] (prob : QuantumQueryProblem S σ ω)

/-- **The matrix elements of a gate in the computational basis:** `unitaryMatrix U k l = ⟨k|U|l⟩`,
the amplitude for the gate `U` to take `|l⟩` to `|k⟩`. These are the constant scalars
that instantiate `Concrete.constUnitaryStep`, so that the polynomial backbone runs
on the *actual* matrix elements of the physical schedule. -/
def unitaryMatrix (T : Evolution S) : σ × Bool × ω → σ × Bool × ω → ℂ :=
  fun k l => inner ℂ (prob.basis k) (T.op (prob.basis l))

/-- **The bit-oracle acts on a coordinate by the XOR reindexing:**
`⟨l | O_X z⟩ = ⟨bitFlipPerm X l | z⟩`. Since `O_X` permutes the computational basis by
`bitFlipPerm X` (`bitOracle_op_basis`), reading off the `l`-th coordinate of `O_X z` is the same as
reading the `(bitFlipPerm X l)`-th coordinate of `z`. This is the operator counterpart of the
Boolean-point oracle evaluation `Concrete.bitOracleStep_eval_boolPoint`. -/
theorem bitOracle_inner_basis (X : σ → Bool) (l : σ × Bool × ω) (z : S.space) :
    inner ℂ (prob.basis l) ((prob.bitOracle X).op z)
      = inner ℂ (prob.basis (bitFlipPerm X l)) z := by
  classical
  rw [prob.basis.inner_op_eq_sum (prob.bitOracle X).op l z]
  simp_rw [prob.bitOracle_op_basis, OrthonormalBasis.inner_eq_ite]
  rw [Finset.sum_eq_single (bitFlipPerm X l)]
  · rw [bitFlipPerm_bitFlipPerm, ite_eq_left rfl, one_mul]
  · intro m _ hm
    have hne : l ≠ bitFlipPerm X m := fun hcon => hm (by rw [hcon, bitFlipPerm_bitFlipPerm])
    rw [ite_eq_right hne, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The amplitude–evaluation bridge** (Nielsen & Chuang §6.7, eqs. 6.58–6.61). The physical
amplitude `⟨k | ψ(X)_t⟩` of the `t`-query algorithm state equals the formal amplitude polynomial of
the method-of-polynomials backbone, evaluated at the Boolean oracle input `X`:

`⟨k | ψ(X)_t⟩ = eval (boolPoint X) (polyQueryState (unitaryMatrix ∘ U) (C ∘ ⟨· | ψ⟩) t k)`.

Proof by induction on `t`. The base case is one unitary layer `U₀` (the coordinate expansion
`OrthonormalBasis.inner_op_eq_sum` matching `constUnitaryStep_eval`, input amplitudes via `eval_C`).
Each inductive step is a query then a
unitary: the query reindexes coordinates by `bitFlipPerm X` on the operator side
(`bitOracle_inner_basis`) and on the polynomial side (`bitOracleStep_eval_boolPoint`), and the layer
expands identically on both sides — so the two `∑ l` normal forms agree term-by-term, closing with
the induction hypothesis at `bitFlipPerm X l`. -/
theorem queryState_amplitude_eq_eval (U : ℕ → Evolution S) (ψ : PureState S)
    (X : σ → Bool) (t : ℕ) (k : σ × Bool × ω) :
    inner ℂ (prob.basis k) (prob.queryState U ψ X t).vec
      = eval (boolPoint X)
          (polyQueryState (fun s => prob.unitaryMatrix (U s))
            (fun l => C (inner ℂ (prob.basis l) ψ.vec)) t k) := by
  induction t generalizing k with
  | zero =>
    simp only [queryState, queryPureState_zero, Evolution.evolvePure_vec, polyQueryState]
    rw [prob.basis.inner_op_eq_sum (U 0).op k, constUnitaryStep_eval]
    exact Finset.sum_congr rfl fun l _ => by rw [eval_C, unitaryMatrix]
  | succ t ih =>
    have hL : inner ℂ (prob.basis k) (prob.queryState U ψ X (t + 1)).vec
        = ∑ l, prob.unitaryMatrix (U (t + 1)) k l
            * inner ℂ (prob.basis (bitFlipPerm X l)) (prob.queryState U ψ X t).vec := by
      rw [queryState_succ, Evolution.evolvePure_vec, Evolution.evolvePure_vec,
        prob.basis.inner_op_eq_sum (U (t + 1)).op k]
      exact Finset.sum_congr rfl fun l _ => by rw [bitOracle_inner_basis, unitaryMatrix]
    have hR : eval (boolPoint X)
          (polyQueryState (fun s => prob.unitaryMatrix (U s))
            (fun l => C (inner ℂ (prob.basis l) ψ.vec)) (t + 1) k)
        = ∑ l, prob.unitaryMatrix (U (t + 1)) k l
            * inner ℂ (prob.basis (bitFlipPerm X l)) (prob.queryState U ψ X t).vec := by
      simp only [polyQueryState]
      rw [constUnitaryStep_eval]
      exact Finset.sum_congr rfl fun l _ => by
        rw [bitOracleStep_eval_boolPoint, ← bitFlipPerm_apply, ← ih (bitFlipPerm X l)]
    rw [hL, hR]

/-- **The physical query amplitude is a bounded-degree polynomial in the oracle bits** (Nielsen &
Chuang §6.7). There is a *single* polynomial `P` of total degree `≤ T`, independent of the oracle
string `X`, whose evaluation at the Boolean point `boolPoint X` is the answer amplitude
`⟨k | ψ(X)_T⟩` of the `T`-query algorithm. This is the exact statement the method of polynomials
delivers: the amplitude, viewed as a function of the `N` oracle bits, is a degree-`≤ T` polynomial —
the witness being the backbone polynomial `polyQueryState`, degree-bounded by
`totalDegree_polyQueryState_le` (its input amplitudes are constants) and matched to the physical
amplitude by `queryState_amplitude_eq_eval`. -/
theorem exists_polynomial_queryState_amplitude (U : ℕ → Evolution S) (ψ : PureState S)
    (T : ℕ) (k : σ × Bool × ω) :
    ∃ P : MvPolynomial σ ℂ, P.totalDegree ≤ T ∧
      ∀ X : σ → Bool, inner ℂ (prob.basis k) (prob.queryState U ψ X T).vec
        = eval (boolPoint X) P := by
  refine ⟨polyQueryState (fun s => prob.unitaryMatrix (U s))
      (fun l => C (inner ℂ (prob.basis l) ψ.vec)) T k, ?_, fun X => ?_⟩
  · exact totalDegree_polyQueryState_le _ _ (fun l => (totalDegree_C _).le) T k
  · exact prob.queryState_amplitude_eq_eval U ψ X T k

end QuantumQueryProblem

end AxQM
