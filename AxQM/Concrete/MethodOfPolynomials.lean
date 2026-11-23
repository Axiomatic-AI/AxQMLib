/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Concrete: the method of polynomials — a `T`-query circuit's amplitudes have degree `≤ T`

Nielsen & Chuang, §6.7 (*Black box algorithm limits*, eqs. 6.58–6.61, Figure 6.10): the algebraic
core of the **method of polynomials**, the tool Exercise 6.20 instructs one to use to prove
`Q₀(OR) ≥ N`.

The output amplitudes `cₖ` of an algorithm making `T` oracle queries are polynomials of degree at
most `T` in the oracle bits `X₀, …, X_{N-1}`: the unitaries between queries leave the degree
unchanged, and each query raises it by at most one.

## The model (N&C Figure 6.10)

A `T`-query algorithm is `U_T · O_X · U_{T-1} · O_X · ⋯ · O_X · U_0` applied to a fixed input
state, where `U_0, …, U_T` are arbitrary unitaries and `O_X` is the oracle for the bit-string
`X ∈ {0,1}ᴺ`. We track *amplitudes as polynomials in the oracle bits*: a state is a vector
`v : ι → MvPolynomial σ K` of amplitudes, one per computational-basis label
`ι = σ × Bool × ω` — the oracle-query index `i : σ` (N&C's `|i⟩`), the single answer qubit
`b : Bool` (N&C's `|Xᵢ⟩`), and the workspace `j : ω`. The oracle bits `Xᵢ` are the polynomial
variables (`X i : MvPolynomial σ K`).

* `bitOracleStep` — one oracle query. N&C's eq. 6.61: the oracle `|i⟩|b⟩|j⟩ ↦ |i⟩|b ⊕ Xᵢ⟩|j⟩`
  re-expressed on amplitudes sends `v` to the vector whose `(i, b, j)` component is
  `(1 − Xᵢ)·v(i,b,j) + Xᵢ·v(i,¬b,j)`. Each entry is degree `≤ 1` in `X`, so this raises the total
  degree by at most `1` (`totalDegree_bitOracleStep_le`).
* `constUnitaryStep` — one unitary layer, given by a *constant* (`X`-independent) matrix
  `M : ι → ι → K` acting as `(M · v)_k = ∑_l C (M k l) · v_l`. Its coefficients `C (M k l)` are
  degree `0`, so this does **not** raise the total degree (`totalDegree_constUnitaryStep_le`).
* `polyQueryState U v₀ t` — the amplitude vector after `t` oracle queries of the interleaved
  circuit `U_t · O_X · ⋯ · O_X · U_0` applied to the input amplitudes `v₀`.

The headline `totalDegree_polyQueryState_le` is exactly N&C's claim: if the input amplitudes are
constants (degree `0` in `X`, as `|ψ₀⟩` is), then after `t` oracle queries every amplitude of
`polyQueryState U v₀ t` has total degree `≤ t`.

## Relation to Exercise 6.20

This is the reusable *method-of-polynomials backbone*: the physics statement of Exercise 6.20
instantiates `U` as the matrix elements of a genuine unitary schedule and
`bitOracleStep` as the (evaluated) bit-oracle `Evolution`, so that the answer-`0` amplitude of a
zero-error `T`-query OR circuit — as a function of the oracle bits — agrees with one of these
degree-`≤ T` polynomials.

## Faithfulness

The register basis `σ × Bool × ω` is exactly N&C's `|i⟩|b⟩|j⟩`. The unitary layers are **arbitrary**
constant matrices (unitarity is irrelevant to the degree count, and demanding less of `M` makes the
bound stronger, not weaker). The oracle step is verbatim eq. 6.61. Everything is stated over an
arbitrary nontrivial commutative ring `K` (N&C's `K = ℝ`) and an arbitrary finite oracle-index type
`σ` (N&C's `σ = Fin N`).
-/

namespace AxQM.Concrete

open MvPolynomial

variable {σ ω K : Type*} [CommRing K]

/-- **One oracle query** (Nielsen & Chuang, eq. 6.61). The bit-oracle `|i⟩|b⟩|j⟩ ↦ |i⟩|b ⊕ Xᵢ⟩|j⟩`,
written on amplitude vectors over the polynomial ring (the oracle bits `Xᵢ` being the variables),
sends `v` to the vector whose `(i, b, j)` component is `(1 − Xᵢ)·v(i,b,j) + Xᵢ·v(i,¬b,j)`. Since
`Xᵢ` is `0` or `1` on the Boolean cube, this is the amplitude form of XOR-ing the answer qubit `b`
with the queried bit `Xᵢ`. -/
noncomputable def bitOracleStep (v : σ × Bool × ω → MvPolynomial σ K) :
    σ × Bool × ω → MvPolynomial σ K :=
  fun p => (1 - X p.1) * v p + X p.1 * v (p.1, !p.2.1, p.2.2)

/-- **One unitary layer** given by a constant (`X`-independent) matrix `M`. In an orthonormal
computational basis a unitary `U` acts on amplitudes by `(U · v)_k = ∑_l ⟨k|U|l⟩ · v_l`; here the
matrix elements `M k l = ⟨k|U|l⟩` are scalars, embedded into the polynomial ring by `C`. Because
they are constants, this layer preserves the polynomial degree. -/
noncomputable def constUnitaryStep [Fintype σ] [Fintype ω]
    (M : σ × Bool × ω → σ × Bool × ω → K) (v : σ × Bool × ω → MvPolynomial σ K) :
    σ × Bool × ω → MvPolynomial σ K :=
  fun k => ∑ l, C (M k l) * v l

/-- **The amplitude vector after `t` oracle queries** of the general query circuit
`U_t · O_X · U_{t-1} · O_X · ⋯ · O_X · U_0` applied to the input amplitudes `v₀` (Nielsen & Chuang,
Figure 6.10). `U : ℕ → (ι → ι → K)` is the unitary schedule (constant matrices); the oracle
`bitOracleStep` is interleaved between consecutive layers. `polyQueryState U v₀ 0 = U_0 · v₀` is the
state `|ψ₀⟩` right before the first query. -/
noncomputable def polyQueryState [Fintype σ] [Fintype ω]
    (U : ℕ → σ × Bool × ω → σ × Bool × ω → K)
    (v0 : σ × Bool × ω → MvPolynomial σ K) : ℕ → σ × Bool × ω → MvPolynomial σ K
  | 0 => constUnitaryStep (U 0) v0
  | t + 1 => constUnitaryStep (U (t + 1)) (bitOracleStep (polyQueryState U v0 t))

/-- **A constant unitary layer preserves the total degree** (N&C: "any unitary operation … cannot
change the degree of these polynomials"). If every amplitude of `v` has total degree `≤ d`, then so
does every amplitude of `constUnitaryStep M v`, because the matrix elements `C (M k l)` are
constants (total degree `0`). -/
theorem totalDegree_constUnitaryStep_le [Fintype σ] [Fintype ω]
    {M : σ × Bool × ω → σ × Bool × ω → K} {v : σ × Bool × ω → MvPolynomial σ K}
    {d : ℕ} (hv : ∀ l, (v l).totalDegree ≤ d) (k : σ × Bool × ω) :
    (constUnitaryStep M v k).totalDegree ≤ d := by
  refine MvPolynomial.totalDegree_finsetSum_le (fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact hv l

/-- **One oracle query raises the total degree by at most one** (N&C: "each oracle call can increase
the degree by at most one"). If every amplitude of `v` has total degree `≤ d`, then every amplitude
of `bitOracleStep v` has total degree `≤ d + 1`: each summand `(1 − Xᵢ)·v(…)` and `Xᵢ·v(…)`
multiplies a degree-`≤ d` amplitude by the degree-`≤ 1` factor `1 − Xᵢ` resp. `Xᵢ`. -/
theorem totalDegree_bitOracleStep_le [Nontrivial K]
    {v : σ × Bool × ω → MvPolynomial σ K} {d : ℕ} (hv : ∀ l, (v l).totalDegree ≤ d)
    (p : σ × Bool × ω) : (bitOracleStep v p).totalDegree ≤ d + 1 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : (1 - X p.1 : MvPolynomial σ K).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_sub _ _).trans (by simp [MvPolynomial.totalDegree_X])
    calc (1 - X p.1 : MvPolynomial σ K).totalDegree + (v p).totalDegree ≤ 1 + d :=
          Nat.add_le_add h1 (hv p)
      _ = d + 1 := by ring
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X]
    have := hv (p.1, !p.2.1, p.2.2)
    omega

/-- **The method of polynomials** (Nielsen & Chuang, eqs. 6.58–6.61). If the input amplitudes `v₀`
are constants (total degree `0` in the oracle bits `X`, as the amplitudes of `|ψ₀⟩` are), then after
`t` oracle queries every amplitude of `polyQueryState U v₀ t` is a polynomial of total degree `≤ t`
in `X`. Proof by induction on `t`: each constant unitary layer preserves the degree
(`totalDegree_constUnitaryStep_le`) and each oracle query raises it by at most one
(`totalDegree_bitOracleStep_le`). -/
theorem totalDegree_polyQueryState_le [Fintype σ] [Fintype ω] [Nontrivial K]
    (U : ℕ → σ × Bool × ω → σ × Bool × ω → K)
    (v0 : σ × Bool × ω → MvPolynomial σ K) (hv0 : ∀ l, (v0 l).totalDegree ≤ 0) :
    ∀ (t : ℕ) (k : σ × Bool × ω), (polyQueryState U v0 t k).totalDegree ≤ t := by
  intro t
  induction t with
  | zero => exact fun k => totalDegree_constUnitaryStep_le hv0 k
  | succ t ih =>
    intro k
    refine totalDegree_constUnitaryStep_le (fun l => ?_) k
    exact totalDegree_bitOracleStep_le ih l

/-! ### Evaluating the amplitude polynomials at a Boolean oracle input

The polynomials `polyQueryState U v₀ t` are functions of the *formal* oracle bits `X₀, …, X_{N-1}`.
To recover the action of the concrete oracle for a specific bit-string `X : σ → Bool` we evaluate at
the **Boolean point** `boolPoint X`, at which every variable `Xᵢ` takes its Boolean value (`0`/`1`).
At such a point the oracle step `bitOracleStep` collapses to the classical XOR reindexing, and a
unitary layer becomes a matrix-vector product — the two facts the amplitude–evaluation bridge (in
`Postulates/API`) matches against a genuine unitary schedule. -/

/-- The **Boolean evaluation point** `boolPoint X = (fun i => if Xᵢ then 1 else 0)` for a bit-string
`X : σ → Bool`. Evaluating an amplitude polynomial at this point substitutes each oracle variable
`Xᵢ` by its Boolean value, recovering the algorithm's amplitudes for the oracle input `X`. -/
def boolPoint (X : σ → Bool) : σ → K := fun i => if X i then 1 else 0

/-- **A unitary layer, evaluated, is a matrix–vector product.** Evaluation distributes over the
constant-matrix sum defining `constUnitaryStep`, and the constant coefficients `C (M k l)` evaluate
to `M k l` (`eval_C`): `eval e (constUnitaryStep M v k) = ∑ l, M k l · eval e (v l)`. This is the
polynomial-evaluation companion of `constUnitaryStep`, matched against the matrix-element expansion
of a genuine unitary's action on amplitudes. -/
theorem constUnitaryStep_eval [Fintype σ] [Fintype ω] (e : σ → K)
    (M : σ × Bool × ω → σ × Bool × ω → K) (v : σ × Bool × ω → MvPolynomial σ K)
    (k : σ × Bool × ω) :
    eval e (constUnitaryStep M v k) = ∑ l, M k l * eval e (v l) := by
  rw [constUnitaryStep, map_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul, eval_C]

/-- **An oracle query, evaluated at a Boolean point, is a classical XOR reindexing** (Nielsen &
Chuang eq. 6.61 on the Boolean cube). At `boolPoint X` the value `Xᵢ ∈ {0,1}` selects exactly one of
the two mixed terms `(1 − Xᵢ)·v(i,b,j)` and `Xᵢ·v(i,¬b,j)` of `bitOracleStep`, so evaluating it just
reads `v` at the flipped label `(i, bᵢ ⊕ Xᵢ, j)`. -/
theorem bitOracleStep_eval_boolPoint (X : σ → Bool)
    (v : σ × Bool × ω → MvPolynomial σ K) (l : σ × Bool × ω) :
    eval (boolPoint X) (bitOracleStep v l)
      = eval (boolPoint X) (v (l.1, xor l.2.1 (X l.1), l.2.2)) := by
  simp only [bitOracleStep, map_add, map_mul, map_sub, map_one, eval_X]
  cases hb : X l.1 with
  | false => simp [boolPoint, hb]
  | true => simp [boolPoint, hb]

end AxQM.Concrete
