/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrixSymplectic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Concrete: concatenating two `[n, 1]` stabilizer codes (Nielsen & Chuang, Exercise 10.62)

This file sets up the **explicit generator
construction** for the concatenation of two stabilizer codes and the reusable `𝔽₂` symplectic
linear-algebra toolkit its proofs consume. Everything here is stated for raw matrix / index data
(`Matrix`, `Concrete.pauliString`, `Concrete.checkRow`, `Fin n → Fin 4`, `ZMod 2`). The
statement of Exercise 10.62 is in `AxQM/NC/Ch10/Exercise10_62.lean`; compare the stabilizer
Exercises 10.53, 10.54 and 10.57.

Show concatenating [n1,1] and [n2,1] stabilizer codes gives an [n1n2,1] stabilizer code.
stabilizer code. — Nielsen & Chuang (p. 482).

## The construction

An `[n, 1]` stabilizer code (with distinguished logical operators) is packaged as `StabCode1 g`:
`g = n − 1` phase-free Pauli-string generators on `n = g + 1` qubits, together with a logical
`X̄`/`Z̄` pair. Its fields are N&C's defining data — the generators are **independent** (their check
rows are `𝔽₂`-linearly independent, Prop 10.3) and **commuting**, and `X̄, Z̄` form a **hyperbolic
pair** in the normalizer (each commutes with every generator; they anticommute with each other) —
exactly what makes `⟨gen⟩` an `[n, 1]` code (`n − 1` independent commuting generators ⇒ `k = 1`)
with logical operators `X̄, Z̄`.

**Concatenation.** Take `C₁ : StabCode1 g₁` as the *inner* code (`n₁ = g₁ + 1` qubits per block) and
`C₂ : StabCode1 g₂` as the *outer* code (`n₂ = g₂ + 1` blocks). The concatenated register has
`n₂ · n₁ = (g₂+1)(g₁+1)` qubits, indexed by `Fin (g₂+1) × Fin (g₁+1)` (block, inner qubit),
identified with `Fin ((g₂+1)(g₁+1))` via `finProdFinEquiv`. The generators (`concatRaw`,
`concatGen`), indexed by `(Fin (g₂+1) × Fin g₁) ⊕ Fin g₂`, are:

* the **inner** generators — `C₁.gen a` on block `b`, identity on the other blocks (`inl (b, a)`),
  `n₂ · g₁` of them; and
* the **encoded outer** generators — the outer generator `C₂.gen j`, with each single-qubit Pauli on
  block `b` replaced (via `encStr`) by the inner logical operator `X̄^{x} Z̄^{z}` realizing it
  (`inr j`), `g₂` of them.

This is `n₂ · g₁ + g₂ = (g₂+1)(g₁+1) − 1 = n₁n₂ − 1` generators on `n₁n₂` qubits (`concatIdx_card`):
`n₁n₂ − 1` independent commuting generators ⇒ `k = 1`, an `[n₁n₂, 1]` code. The independence and
commutation proofs, and the dimension conclusion via Proposition 10.5, are in the sibling files.

## The symplectic toolkit

The independence and commutation arguments are `𝔽₂` symplectic linear algebra over the check rows.
This file provides the general-index check rows (`checkVecG`, `checkRowG`) and the reusable facts
about `Concrete.symplecticForm`: it is bi-additive (`symplecticForm_add_left`), `𝔽₂`-linear
(`symplecticForm_smul_left`), **alternating** (`symplecticForm_self`, `= 0` over `ZMod 2`) and
**symmetric** (`symplecticForm_comm`), invariant under a qubit relabeling
(`symplecticForm_comp_sumMap`), and the key **hyperbolic-pair independence** lemma
`linearIndependent_sumElim_hyperbolic`: a linearly independent family orthogonal to a hyperbolic
pair `(x, z)` (`symplecticForm x z = 1`) extends, by that pair, to a linearly independent family.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

/-! ### General-index check-matrix rows -/

variable {ι κ : Type*}

/-- The **check-matrix row** `r(g) = (x_g | z_g)` of a Pauli string over an *arbitrary* qubit index
`ι` — the `X`-part and `Z`-part over `ZMod 2` (`Concrete.checkRow` for `ι = Fin n`, but with the
index kept general so it can name a product index `Fin (g₂+1) × Fin (g₁+1)`). -/
def checkRowG (g : ι → Fin 4) : (ι → ZMod 2) × (ι → ZMod 2) :=
  (fun k => (pauliBit (g k)).1, fun k => (pauliBit (g k)).2)

/-- The flat `2|ι|`-vector check row `r(g)` over an arbitrary qubit index `ι`, the `X`-bit on
`Sum.inl` and the `Z`-bit on `Sum.inr` (`Concrete.checkVec` for `ι = Fin n`). -/
def checkVecG (g : ι → Fin 4) : ι ⊕ ι → ZMod 2 :=
  Sum.elim (checkRowG g).1 (checkRowG g).2

/-- On the `Fin n` qubit index the general check row is the standard `checkRow`. -/
@[simp] theorem checkRowG_eq {n : ℕ} (g : Fin n → Fin 4) : checkRowG g = checkRow g := rfl

/-- On the `Fin n` qubit index the general flat check row is the standard `checkVec`. -/
@[simp] theorem checkVecG_eq {n : ℕ} (g : Fin n → Fin 4) : checkVecG g = checkVec g := rfl

/-- **The check row is a homomorphism** (flat form): `r(g ⊙ h) = r(g) + r(h)`, the flat-vector
restatement of `checkRow_pauliMulIndex`. -/
theorem checkVec_pauliMulIndex {n : ℕ} (g h : Fin n → Fin 4) :
    checkVec (pauliMulIndex g h) = checkVec g + checkVec h := by
  ext s; cases s <;> simp [checkVec, checkRow, pauliMulIndex, pauliBit_pauliMul]

/-- **The check row of the identity string is zero**: `r(𝟙) = 0`, since every single-qubit Pauli is
`I` (`pauliBit 0 = (0, 0)`). This is the check-vector reading of "the identity generator contributes
nothing" — used both by `encStr_checkVec` (the `I ↦ 𝟙` case) and when an inner concatenated
generator misses a block. -/
@[simp] theorem checkVec_const_zero {n : ℕ} : checkVec (fun _ : Fin n => (0 : Fin 4)) = 0 := by
  ext s; cases s <;> simp [checkVec, checkRow, pauliBit, pauliXBit, pauliZBit]

/-! ### The `symplecticForm` toolkit -/

variable [Fintype ι] [DecidableEq ι]

/-- `symplecticForm` is **additive in its first argument**: `ω(x + x', y) = ω(x, y) + ω(x', y)`. -/
theorem symplecticForm_add_left (x x' y : ι ⊕ ι → ZMod 2) :
    symplecticForm (x + x') y = symplecticForm x y + symplecticForm x' y := by
  simp only [symplecticForm, add_dotProduct]

/-- `symplecticForm` is **`𝔽₂`-linear in its first argument**: `ω(a • x, y) = a • ω(x, y)`. -/
theorem symplecticForm_smul_left (a : ZMod 2) (x y : ι ⊕ ι → ZMod 2) :
    symplecticForm (a • x) y = a • symplecticForm x y := by
  simp only [symplecticForm, smul_dotProduct]

/-- The first-argument slot of `symplecticForm` as an `𝔽₂`-linear map (used to distribute the form
over a `Finset.sum`). -/
def symplecticFormLeft (y : ι ⊕ ι → ZMod 2) : (ι ⊕ ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := symplecticForm x y
  map_add' x x' := symplecticForm_add_left x x' y
  map_smul' a x := by simpa using symplecticForm_smul_left a x y

/-- `symplecticForm` distributes over a finite sum in its first argument. -/
theorem symplecticForm_sum_left {α : Type*} (s : Finset α) (f : α → ι ⊕ ι → ZMod 2)
    (y : ι ⊕ ι → ZMod 2) :
    symplecticForm (∑ i ∈ s, f i) y = ∑ i ∈ s, symplecticForm (f i) y :=
  map_sum (symplecticFormLeft y) f s

/-- `symplecticForm` vanishes on the zero vector in its first argument. -/
@[simp] theorem symplecticForm_zero_left (y : ι ⊕ ι → ZMod 2) : symplecticForm 0 y = 0 :=
  map_zero (symplecticFormLeft y)

/-- **`symplecticForm` is alternating over `ZMod 2`**: `ω(x, x) = 0`. The two cross terms of the
twisted product are equal (dot product is commutative) and sum to `0` in characteristic `2`. -/
theorem symplecticForm_self (x : ι ⊕ ι → ZMod 2) : symplecticForm x x = 0 := by
  rw [symplecticForm_apply, dotProduct_comm (x ∘ Sum.inr) (x ∘ Sum.inl)]
  exact CharTwo.add_self_eq_zero _

/-- **`symplecticForm` is symmetric** (over `ZMod 2`, where `Λ` is symmetric):
`ω(x, y) = ω(y, x)`. -/
theorem symplecticForm_comm (x y : ι ⊕ ι → ZMod 2) :
    symplecticForm x y = symplecticForm y x := by
  rw [symplecticForm_apply, symplecticForm_apply,
    dotProduct_comm (x ∘ Sum.inl) (y ∘ Sum.inr), dotProduct_comm (x ∘ Sum.inr) (y ∘ Sum.inl)]
  ring

/-- **`symplecticForm` is invariant under a qubit relabeling** `e : κ ≃ ι`: pulling both check
vectors back along `Sum.map e e` leaves the twisted product unchanged. This transports a symplectic
computation on a product qubit index to the flattened `Fin N` index. -/
theorem symplecticForm_comp_sumMap [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (x y : ι ⊕ ι → ZMod 2) :
    symplecticForm (fun s => x (Sum.map e e s)) (fun s => y (Sum.map e e s)) =
      symplecticForm x y := by
  have hl : ∀ w : ι ⊕ ι → ZMod 2, (fun s => w (Sum.map e e s)) ∘ Sum.inl = (w ∘ Sum.inl) ∘ e := by
    intro w; funext k; simp
  have hr : ∀ w : ι ⊕ ι → ZMod 2, (fun s => w (Sum.map e e s)) ∘ Sum.inr = (w ∘ Sum.inr) ∘ e := by
    intro w; funext k; simp
  rw [symplecticForm_apply, symplecticForm_apply, hl, hr, hl, hr,
    comp_equiv_dotProduct_comp_equiv, comp_equiv_dotProduct_comp_equiv]

/-! ### The hyperbolic-pair independence lemma -/

/-- **A hyperbolic pair extends a linearly independent orthogonal family.** If `v` is an
`𝔽₂`-linearly independent family, each `v i` is symplectically orthogonal to both `x` and `z`, and
`(x, z)` is a hyperbolic pair (`ω(x, z) = 1`), then the family `v` extended by `x, z` (indexed by
`Fin m ⊕ Fin 2`) is again linearly independent. This is the check-row form of "the logical operators
`X̄, Z̄` are independent of the stabilizer generators and of each other": pairing a vanishing
combination with `z` (resp. `x`) isolates the `x`- (resp. `z`-) coefficient via `ω(x, z) = 1`
and the alternating law, and the remaining `∑ cᵢ • v i = 0` forces `cᵢ = 0` by independence
of `v`. -/
theorem linearIndependent_sumElim_hyperbolic {m : ℕ}
    (v : Fin m → (ι ⊕ ι → ZMod 2)) (x z : ι ⊕ ι → ZMod 2)
    (hv : LinearIndependent (ZMod 2) v)
    (hvx : ∀ i, symplecticForm (v i) x = 0)
    (hvz : ∀ i, symplecticForm (v i) z = 0)
    (hxz : symplecticForm x z = 1) :
    LinearIndependent (ZMod 2) (Sum.elim v ![x, z]) := by
  refine Fintype.linearIndependent_iff.mpr (fun c hc => ?_)
  -- Split the vanishing combination into the `v`-part `w` and the `x, z` tail.
  rw [Fintype.sum_sum_type] at hc
  set w : ι ⊕ ι → ZMod 2 := ∑ a : Fin m, c (Sum.inl a) • v a with hw
  have hsum : w + (c (Sum.inr 0) • x + c (Sum.inr 1) • z) = 0 := by
    rw [hw]
    have : ∑ b : Fin 2, c (Sum.inr b) • (Sum.elim v ![x, z]) (Sum.inr b)
        = c (Sum.inr 0) • x + c (Sum.inr 1) • z := by
      simp [Fin.sum_univ_two]
    simpa [this] using hc
  -- Pairing `w` with anything vanishes on the `x, z` targets.
  have hwx : symplecticForm w x = 0 := by
    rw [hw, symplecticForm_sum_left]
    exact Finset.sum_eq_zero fun a _ => by rw [symplecticForm_smul_left, hvx a, smul_zero]
  have hwz : symplecticForm w z = 0 := by
    rw [hw, symplecticForm_sum_left]
    exact Finset.sum_eq_zero fun a _ => by rw [symplecticForm_smul_left, hvz a, smul_zero]
  -- Pair the whole equation with `z`: only the `x`-coefficient survives (`ω(x,z)=1`).
  have hcx : c (Sum.inr 0) = 0 := by
    have h := congrArg (fun t => symplecticForm t z) hsum
    simp only [symplecticForm_add_left, symplecticForm_smul_left, hwz, symplecticForm_self, hxz,
      symplecticForm_zero_left, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h
    exact h
  -- Pair with `x`: only the `z`-coefficient survives (`ω(z,x)=1`).
  have hcz : c (Sum.inr 1) = 0 := by
    have hzx : symplecticForm z x = 1 := by rw [symplecticForm_comm]; exact hxz
    have h := congrArg (fun t => symplecticForm t x) hsum
    simp only [symplecticForm_add_left, symplecticForm_smul_left, hwx, symplecticForm_self, hzx,
      symplecticForm_zero_left, smul_eq_mul, mul_one, mul_zero, zero_add] at h
    exact h
  -- The `v`-combination now vanishes: independence of `v` finishes it.
  have hvcoeff : ∀ a : Fin m, c (Sum.inl a) = 0 := by
    have hw0 : w = 0 := by
      have := hsum
      rw [hcx, hcz, zero_smul, zero_smul, add_zero, add_zero] at this
      exact this
    have := Fintype.linearIndependent_iff.mp hv (fun a => c (Sum.inl a)) (by rw [← hw]; exact hw0)
    exact this
  rintro (a | b)
  · exact hvcoeff a
  · fin_cases b
    · exact hcx
    · exact hcz

/-! ### An `[n, 1]` stabilizer code with distinguished logical operators -/

/-- An **`[n, 1]` stabilizer code with a chosen logical `X̄`/`Z̄` pair**, on `n = g + 1` qubits with
`g` generators — the data N&C's construction consumes. `gen` are `g` phase-free Pauli-string
generators; they **commute** (`gen_commute`) and are **independent** (`gen_indep`: their check rows
are `𝔽₂`-linearly independent, N&C Prop 10.3), so `⟨gen⟩` is an `[g+1, 1]` stabilizer (`k = 1`). The
logical operators `logX`, `logZ` lie in the normalizer — each **commutes** with every generator
(`logX_commute`, `logZ_commute`) — and form a **hyperbolic pair**: they **anticommute**
(`logXZ_anticommute`). -/
structure StabCode1 (g : ℕ) where
  /-- The `g = n − 1` phase-free stabilizer generators on `n = g + 1` qubits. -/
  gen : Fin g → (Fin (g + 1) → Fin 4)
  /-- The logical `X̄` operator. -/
  logX : Fin (g + 1) → Fin 4
  /-- The logical `Z̄` operator. -/
  logZ : Fin (g + 1) → Fin 4
  /-- The generators pairwise commute. -/
  gen_commute : ∀ i j, Commute (pauliString (gen i)) (pauliString (gen j))
  /-- The generators are independent: their check rows are `𝔽₂`-linearly independent (Prop 10.3). -/
  gen_indep : LinearIndependent (ZMod 2) (fun i => checkRow (gen i))
  /-- `X̄` commutes with every generator (it is in the normalizer). -/
  logX_commute : ∀ i, Commute (pauliString logX) (pauliString (gen i))
  /-- `Z̄` commutes with every generator (it is in the normalizer). -/
  logZ_commute : ∀ i, Commute (pauliString logZ) (pauliString (gen i))
  /-- `X̄` and `Z̄` anticommute (they form a hyperbolic logical pair). -/
  logXZ_anticommute : ¬ Commute (pauliString logX) (pauliString logZ)

variable {g₁ g₂ : ℕ}

/-- The **encoded single-qubit Pauli** `p` for the code `C`: the inner logical operator
`X̄^{x} Z̄^{z}` (with `(x, z) = pauliBit p`) realizing `p` on an encoded block. `I ↦ 𝟙`, `X ↦ X̄`,
`Z ↦ Z̄`, `Y ↦ X̄ Z̄`. -/
def encStr (C : StabCode1 g₁) (p : Fin 4) : Fin (g₁ + 1) → Fin 4 :=
  if pauliXBit p = 0 then
    (if pauliZBit p = 0 then (fun _ => 0) else C.logZ)
  else
    (if pauliZBit p = 0 then C.logX else pauliMulIndex C.logX C.logZ)

/-- **The check row of an encoded Pauli** is the corresponding `𝔽₂` combination of the logical check
rows: `r(encStr C p) = x_p · r(X̄) + z_p · r(Z̄)`. This is the bridge that turns the outer
generators' symplectic algebra into the inner logical operators' symplectic algebra. -/
theorem encStr_checkVec (C : StabCode1 g₁) (p : Fin 4) :
    checkVec (encStr C p) =
      (pauliBit p).1 • checkVec C.logX + (pauliBit p).2 • checkVec C.logZ := by
  fin_cases p <;>
    simp [encStr, pauliBit, pauliXBit, pauliZBit, checkVec_pauliMulIndex]

/-- The **index set of the concatenated generators**: `n₂ = g₂ + 1` blocks each carrying `g₁` inner
generators (`inl (b, a)`), plus `g₂` encoded outer generators (`inr j`). -/
abbrev ConcatIdx (g₁ g₂ : ℕ) : Type := (Fin (g₂ + 1) × Fin g₁) ⊕ Fin g₂

/-- **The concatenated stabilizer generators, on the product qubit index** `Fin (g₂+1) × Fin (g₁+1)`
(block, inner qubit). `inl (b, a)` is the inner generator `C₁.gen a` on block `b` and identity
elsewhere; `inr j` is the outer generator `C₂.gen j` with its Pauli on each block `b`
replaced by the inner logical operator encoding it (`encStr`). -/
def concatRaw (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    ConcatIdx g₁ g₂ → (Fin (g₂ + 1) × Fin (g₁ + 1) → Fin 4)
  | Sum.inl (b, a) => fun q => if q.1 = b then C₁.gen a q.2 else 0
  | Sum.inr j => fun q => encStr C₁ (C₂.gen j q.1) q.2

/-- **The concatenated stabilizer generators on the flattened `Fin (n₁n₂)` register**, obtained from
`concatRaw` by identifying `Fin (g₂+1) × Fin (g₁+1) ≃ Fin ((g₂+1)(g₁+1))` (`finProdFinEquiv`). This
is the explicit generator family whose properties (commuting, independent, `⇒ [n₁n₂, 1]`)
the sibling files establish. -/
def concatGen (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    ConcatIdx g₁ g₂ → (Fin ((g₂ + 1) * (g₁ + 1)) → Fin 4) :=
  fun c => concatRaw C₁ C₂ c ∘ finProdFinEquiv.symm

/-- **The concatenated code has `n₁n₂ − 1` generators**: the index set has cardinality
`(g₂+1) · g₁ + g₂ = (g₂+1)(g₁+1) − 1 = n₁n₂ − 1`. Together with the `n₁n₂` qubits this is the
`[n₁n₂, 1]` parameter count (`n₁n₂ − (n₁n₂ − 1) = 1`). -/
theorem concatIdx_card : Fintype.card (ConcatIdx g₁ g₂) = (g₂ + 1) * (g₁ + 1) - 1 := by
  simp only [ConcatIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [Nat.mul_succ]
  omega

/-! ### The concatenated generators commute (Exercise 10.62, commutation half)

The `n₁n₂ − 1` concatenated generators pairwise **commute**. Via Exercise 10.33
(`pauliString_commute_iff_symplecticForm`) this reduces to the vanishing of the twisted product
`ω` of their check rows, which — by the *block decomposition* of `ω` over the `Fin (g₂+1)` blocks —
splits into three cases, each closed by an inner-code symplectic relation:

* **inner–inner** (`inl (b, a)` vs `inl (b', a')`): the two operators are supported on single
  blocks; disjoint blocks contribute `0`, a shared block contributes `ω(r(gᵃ), r(gᵃ'))` which is
  `0` because the *inner* generators commute;
* **inner–encoded-outer** (`inl (b, a)` vs `inr j`): only block `b` contributes, and there the
  encoded outer Pauli is an `𝔽₂`-combination of `X̄, Z̄`, each commuting with every inner generator;
* **encoded-outer–encoded-outer** (`inr j` vs `inr j'`): each block's contribution is the
  single-qubit symplectic pairing of the *outer* Paulis (the `X̄, Z̄` hyperbolic relation
  `ω(r(X̄), r(Z̄)) = 1` cancelling the encoding), so the block sum reassembles the *outer* twisted
  product `ω(r(gⱼ), r(gⱼ'))`, which is `0` because the outer generators commute.
-/

/-- `symplecticForm` is **additive in its second argument**: `ω(x, y + y') = ω(x, y) + ω(x, y')`
(from `symplecticForm_add_left` and symmetry). -/
theorem symplecticForm_add_right (x y y' : ι ⊕ ι → ZMod 2) :
    symplecticForm x (y + y') = symplecticForm x y + symplecticForm x y' := by
  rw [symplecticForm_comm, symplecticForm_add_left, symplecticForm_comm x y,
    symplecticForm_comm x y']

/-- `symplecticForm` is **`𝔽₂`-linear in its second argument**: `ω(x, a • y) = a • ω(x, y)`. -/
theorem symplecticForm_smul_right (a : ZMod 2) (x y : ι ⊕ ι → ZMod 2) :
    symplecticForm x (a • y) = a • symplecticForm x y := by
  rw [symplecticForm_comm, symplecticForm_smul_left, symplecticForm_comm x y]

/-- `symplecticForm` vanishes on the zero vector in its second argument. -/
@[simp] theorem symplecticForm_zero_right (x : ι ⊕ ι → ZMod 2) : symplecticForm x 0 = 0 := by
  rw [symplecticForm_comm]; exact symplecticForm_zero_left x

/-- **The twisted product of two `X̄/Z̄` combinations.** For a hyperbolic pair `(x, z)`
(`ω(x, z) = 1`), the symplectic form of `a•x + b•z` and `a'•x + b'•z` is `a·b' + b·a'` — the
single-qubit symplectic pairing of the coefficient pairs. Both diagonal terms vanish (`ω` is
alternating) and the two cross terms use `ω(x, z) = ω(z, x) = 1` (symmetry over `𝔽₂`). This is the
algebra that turns the *encoded* outer Paulis back into a single-qubit symplectic pairing. -/
theorem symplecticForm_smul_comb (a b a' b' : ZMod 2) (x z : ι ⊕ ι → ZMod 2)
    (hxz : symplecticForm x z = 1) :
    symplecticForm (a • x + b • z) (a' • x + b' • z) = a * b' + b * a' := by
  have hzx : symplecticForm z x = 1 := by rw [symplecticForm_comm]; exact hxz
  simp only [symplecticForm_add_left, symplecticForm_add_right, symplecticForm_smul_left,
    symplecticForm_smul_right, symplecticForm_self, hxz, hzx, smul_eq_mul, mul_zero, mul_one,
    zero_add, add_zero]
  ring

/-- **The twisted product in coordinate-sum form**, over an arbitrary qubit index `P`:
`ω(r(f), r(f')) = Σ_q (x_{f,q} z_{f',q} + z_{f,q} x_{f',q})`. Unfolds `symplecticForm` (the
`Λ`-swap) into the per-qubit `X`/`Z` bit products; the reusable presentation both the block
decomposition and the outer-form reassembly consume. -/
theorem symplecticForm_checkVecG_apply {P : Type*} [Fintype P] [DecidableEq P] (f f' : P → Fin 4) :
    symplecticForm (checkVecG f) (checkVecG f') =
      ∑ q : P, ((pauliBit (f q)).1 * (pauliBit (f' q)).2
        + (pauliBit (f q)).2 * (pauliBit (f' q)).1) := by
  rw [symplecticForm_apply]
  simp only [dotProduct, Function.comp_apply, checkVecG, checkRowG, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]

/-- `symplecticForm_checkVecG_apply` on the `Fin n` qubit index: the twisted product of two check
rows as a per-qubit bit-product sum. -/
theorem symplecticForm_checkVec_apply {n : ℕ} (u v : Fin n → Fin 4) :
    symplecticForm (checkVec u) (checkVec v) =
      ∑ k : Fin n, ((pauliBit (u k)).1 * (pauliBit (v k)).2
        + (pauliBit (u k)).2 * (pauliBit (v k)).1) := by
  rw [← checkVecG_eq u, ← checkVecG_eq v, symplecticForm_checkVecG_apply]

/-- **Block decomposition of the twisted product.** On the product qubit index
`Fin (g₂+1) × Fin (g₁+1)` (block, inner qubit), the symplectic form of two Pauli strings is the sum
over blocks `b` of the *inner* symplectic forms of their block restrictions:
`ω(r(f), r(f')) = Σ_b ω(r(f(b,·)), r(f'(b,·)))`. Immediate from `symplecticForm_checkVecG_apply` and
`Fintype.sum_prod_type`. This is the geometric heart of the commutation argument: it isolates each
block's contribution, so single-block generators contribute at most one term. -/
theorem symplecticForm_checkVecG_prod (f f' : Fin (g₂ + 1) × Fin (g₁ + 1) → Fin 4) :
    symplecticForm (checkVecG f) (checkVecG f') =
      ∑ b : Fin (g₂ + 1),
        symplecticForm (checkVec fun i => f (b, i)) (checkVec fun i => f' (b, i)) := by
  rw [symplecticForm_checkVecG_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [symplecticForm_checkVec_apply]

/-- **A qubit relabeling `e : Fin N ≃ P` pulls a check vector back coordinatewise.** The flat check
row of `f ∘ e` (on `Fin N`) is the check row of `f` (on `P`) precomposed with `Sum.map e e`. Lets a
computation on the flattened `Fin N` register be transported to the product qubit index. -/
theorem checkVec_comp_equiv {N : ℕ} {P : Type*} (e : Fin N ≃ P) (h : P → Fin 4) :
    checkVec (h ∘ e) = fun s => checkVecG h (Sum.map e e s) := by
  funext s; cases s <;> rfl

/-- **The logical `X̄, Z̄` of an `[n, 1]` code form a hyperbolic pair**: their check rows satisfy
`ω(r(X̄), r(Z̄)) = 1`. Since `X̄, Z̄` **anticommute** (`logXZ_anticommute`), Exercise 10.33 gives
`ω ≠ 0`, and over `𝔽₂` a nonzero value is `1`. -/
theorem logXZ_symplecticForm_one {g : ℕ} (C : StabCode1 g) :
    symplecticForm (checkVec C.logX) (checkVec C.logZ) = 1 := by
  have h : ¬ (symplecticForm (checkVec C.logX) (checkVec C.logZ) = 0) := by
    rw [← pauliString_commute_iff_symplecticForm]; exact C.logXZ_anticommute
  have h2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact h2 _ h

/-- **The twisted product of two encoded Paulis is their single-qubit symplectic pairing.**
Because `checkVec (encStr C p) = x_p • r(X̄) + z_p • r(Z̄)` (`encStr_checkVec`) and `(X̄, Z̄)` is
hyperbolic, `ω(r(encStr C p), r(encStr C p')) = x_p z_{p'} + z_p x_{p'}` — exactly the per-qubit
symplectic pairing of the *outer* single-qubit Paulis `p, p'`, with the inner encoding cancelled. -/
theorem encStr_encStr_symplecticForm {g : ℕ} (C : StabCode1 g)
    (hXZ : symplecticForm (checkVec C.logX) (checkVec C.logZ) = 1) (p p' : Fin 4) :
    symplecticForm (checkVec (encStr C p)) (checkVec (encStr C p')) =
      (pauliBit p).1 * (pauliBit p').2 + (pauliBit p).2 * (pauliBit p').1 := by
  rw [encStr_checkVec, encStr_checkVec, symplecticForm_smul_comb _ _ _ _ _ _ hXZ]

/-- **The block restriction of an inner concatenated generator.** The generator `inl (bb, a)` — the
inner generator `C₁.gen a` on block `bb`, identity elsewhere — restricts on block `b` to `C₁.gen a`
if `b = bb` and to the identity string otherwise. -/
theorem checkVec_concatRaw_inl (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂)
    (bb : Fin (g₂ + 1)) (a : Fin g₁) (b : Fin (g₂ + 1)) :
    checkVec (fun i => concatRaw C₁ C₂ (Sum.inl (bb, a)) (b, i))
      = if b = bb then checkVec (C₁.gen a) else 0 := by
  by_cases h : b = bb <;> simp [concatRaw, h]

/-- **The block restriction of an encoded outer concatenated generator.** The generator `inr j`
restricts on block `b` to the encoded single-qubit Pauli `encStr C₁ (C₂.gen j b)` — the inner
logical operator realizing the outer generator's `b`-th Pauli. -/
theorem checkVec_concatRaw_inr (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂)
    (j : Fin g₂) (b : Fin (g₂ + 1)) :
    checkVec (fun i => concatRaw C₁ C₂ (Sum.inr j) (b, i))
      = checkVec (encStr C₁ (C₂.gen j b)) := rfl

/-- **inner–inner commutation.** Two inner concatenated generators `inl (bb, a)`, `inl (bb', a')`
have vanishing twisted product: block-decomposed, disjoint-block terms are `0` and the shared-block
term is `ω(r(gᵃ), r(gᵃ')) = 0` because the inner generators commute. -/
theorem concatRaw_symplecticForm_inl_inl (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂)
    (bb : Fin (g₂ + 1)) (a : Fin g₁) (bb' : Fin (g₂ + 1)) (a' : Fin g₁) :
    symplecticForm (checkVecG (concatRaw C₁ C₂ (Sum.inl (bb, a))))
      (checkVecG (concatRaw C₁ C₂ (Sum.inl (bb', a')))) = 0 := by
  rw [symplecticForm_checkVecG_prod]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [checkVec_concatRaw_inl, checkVec_concatRaw_inl]
  by_cases hb : b = bb <;> by_cases hb' : b = bb'
  · rw [ite_eq_left hb, ite_eq_left hb']
    exact (pauliString_commute_iff_symplecticForm _ _).mp (C₁.gen_commute a a')
  · rw [ite_eq_left hb, ite_eq_right hb']; exact symplecticForm_zero_right _
  · rw [ite_eq_right hb, ite_eq_left hb']; exact symplecticForm_zero_left _
  · rw [ite_eq_right hb, ite_eq_right hb']; exact symplecticForm_zero_left _

/-- **inner–encoded-outer commutation.** An inner generator `inl (bb, a)` and an encoded outer
generator `inr j` have vanishing twisted product: only block `bb` contributes, and there the encoded
outer Pauli is an `𝔽₂`-combination of `X̄, Z̄`, each commuting with `C₁.gen a`. -/
theorem concatRaw_symplecticForm_inl_inr (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂)
    (bb : Fin (g₂ + 1)) (a : Fin g₁) (j : Fin g₂) :
    symplecticForm (checkVecG (concatRaw C₁ C₂ (Sum.inl (bb, a))))
      (checkVecG (concatRaw C₁ C₂ (Sum.inr j))) = 0 := by
  have hgX : symplecticForm (checkVec (C₁.gen a)) (checkVec C₁.logX) = 0 := by
    rw [symplecticForm_comm]
    exact (pauliString_commute_iff_symplecticForm _ _).mp (C₁.logX_commute a)
  have hgZ : symplecticForm (checkVec (C₁.gen a)) (checkVec C₁.logZ) = 0 := by
    rw [symplecticForm_comm]
    exact (pauliString_commute_iff_symplecticForm _ _).mp (C₁.logZ_commute a)
  rw [symplecticForm_checkVecG_prod]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [checkVec_concatRaw_inl, checkVec_concatRaw_inr]
  by_cases hb : b = bb
  · rw [ite_eq_left hb, encStr_checkVec, symplecticForm_add_right, symplecticForm_smul_right,
      symplecticForm_smul_right, hgX, hgZ, smul_zero, smul_zero, add_zero]
  · rw [ite_eq_right hb]; exact symplecticForm_zero_left _

/-- **encoded-outer–encoded-outer commutation.** Two encoded outer generators `inr j`, `inr j'`
have vanishing twisted product: each block's contribution is the single-qubit symplectic pairing of
the outer Paulis (`encStr_encStr_symplecticForm`), so the block sum reassembles the *outer* twisted
product `ω(r(gⱼ), r(gⱼ')) = 0` — the outer generators commute. -/
theorem concatRaw_symplecticForm_inr_inr (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂)
    (j j' : Fin g₂) :
    symplecticForm (checkVecG (concatRaw C₁ C₂ (Sum.inr j)))
      (checkVecG (concatRaw C₁ C₂ (Sum.inr j'))) = 0 := by
  have hXZ : symplecticForm (checkVec C₁.logX) (checkVec C₁.logZ) = 1 := logXZ_symplecticForm_one C₁
  rw [symplecticForm_checkVecG_prod]
  have hstep : (∑ b : Fin (g₂ + 1),
      symplecticForm (checkVec fun i => concatRaw C₁ C₂ (Sum.inr j) (b, i))
        (checkVec fun i => concatRaw C₁ C₂ (Sum.inr j') (b, i)))
      = symplecticForm (checkVec (C₂.gen j)) (checkVec (C₂.gen j')) := by
    rw [symplecticForm_checkVec_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [checkVec_concatRaw_inr, checkVec_concatRaw_inr, encStr_encStr_symplecticForm C₁ hXZ]
  rw [hstep]
  exact (pauliString_commute_iff_symplecticForm _ _).mp (C₂.gen_commute j j')

/-- **All concatenated generators have vanishing pairwise twisted product** (product-index form):
for every pair `c, c'` of concatenated generator indices, `ω(r(concatRaw c), r(concatRaw c')) = 0`.
Dispatches the three genuine cases above; the `inr`–`inl` case is the `inl`–`inr` case via symmetry
of `ω`. -/
theorem concatRaw_symplecticForm_zero (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂)
    (c c' : ConcatIdx g₁ g₂) :
    symplecticForm (checkVecG (concatRaw C₁ C₂ c)) (checkVecG (concatRaw C₁ C₂ c')) = 0 := by
  obtain (⟨bb, a⟩ | j) := c <;> obtain (⟨bb', a'⟩ | j') := c'
  · exact concatRaw_symplecticForm_inl_inl C₁ C₂ bb a bb' a'
  · exact concatRaw_symplecticForm_inl_inr C₁ C₂ bb a j'
  · rw [symplecticForm_comm]; exact concatRaw_symplecticForm_inl_inr C₁ C₂ bb' a' j
  · exact concatRaw_symplecticForm_inr_inr C₁ C₂ j j'

/-- **The concatenated twisted product equals its product-index form.** Reindexing the flattened
`Fin (n₁n₂)` register back to the product index `Fin (g₂+1) × Fin (g₁+1)` (via `finProdFinEquiv`)
leaves the twisted product unchanged (`symplecticForm_comp_sumMap`), so the symplectic form of the
`concatGen` check rows on `Fin N` is that of the `concatRaw` check rows on the product index. -/
theorem concatGen_symplecticForm (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂)
    (c c' : ConcatIdx g₁ g₂) :
    symplecticForm (checkVec (concatGen C₁ C₂ c)) (checkVec (concatGen C₁ C₂ c')) =
      symplecticForm (checkVecG (concatRaw C₁ C₂ c)) (checkVecG (concatRaw C₁ C₂ c')) := by
  simp only [concatGen]
  rw [checkVec_comp_equiv, checkVec_comp_equiv,
    symplecticForm_comp_sumMap finProdFinEquiv.symm]

/-- **Nielsen & Chuang, Exercise 10.62 (commutation half): the concatenated stabilizer generators
pairwise commute.** For any two concatenated generator indices `c, c'`, the Pauli strings
`concatGen c, concatGen c'` commute. Via Exercise 10.33 (`pauliString_commute_iff_symplecticForm`)
this is the vanishing of their twisted product, which — after reindexing to the product qubit
index (`concatGen_symplecticForm`) — is `concatRaw_symplecticForm_zero`. Together with the
independence (`concatGen_checkRow_linearIndependent`) this is what makes `⟨concatGen⟩` an
`[n₁n₂, 1]` stabilizer code. -/
theorem concatGen_commute (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) (c c' : ConcatIdx g₁ g₂) :
    Commute (pauliString (concatGen C₁ C₂ c)) (pauliString (concatGen C₁ C₂ c')) := by
  rw [pauliString_commute_iff_symplecticForm, concatGen_symplecticForm]
  exact concatRaw_symplecticForm_zero C₁ C₂ c c'

end AxQM.Concrete
