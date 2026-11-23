/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.GilbertVarshamov
public import ToMathlib.InformationTheory.Coding.DualCode
public import ToMathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The Gilbert–Varshamov existence bound for CSS quantum codes (combinatorial core)

The CSS (Calderbank–Shor–Steane) construction turns a *nested pair* of classical linear codes
`C₂ ⊆ C₁ ⊆ 𝔽₂ⁿ` in which **both `C₁` and `C₂⊥` correct `t` errors** into an `[n, k₁ - k₂]` quantum
code correcting `t` qubit errors (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
§10.4.2). Its **Gilbert–Varshamov bound** (N&C Problem 10.2, eq. (10.122)) asserts that such a pair
exists with rate `(k₁ - k₂)/n ≥ 1 - 2 H₂(2t/n)` — the classical factor `1 - H₂` appears *twice*,
once for the distance constraint on `C₁` and once for the constraint on `C₂⊥`.

This file proves both the **counting form** `exists_nestedPair_minDist_ge` (the purely combinatorial
heart of Problem 10.2) and the **entropy/rate form** `exists_nestedPair_correctsErrors_of_rate_le`
(eq. (10.122) itself), obtained from the counting form via the ball-volume entropy bound. The
quantum CSS construction turning such a pair into an `[n, k₁ - k₂]` quantum code correcting `t`
qubit errors is the established background of §10.4.2 (formalized separately under the CSS-code
exercises); Problem 10.2 is exactly the existence bound proved here.

## Main results

* `LinearCode.exists_nestedPair_minDist_ge`: for block length `n` and parameters `a, b, d` with
  `1 ≤ d`, `a ≤ n`, and the joint ball-volume condition
  `(∑_{i < d} C(n,i)) · (2 ^ (n - a) + 2 ^ (a + b)) < 2 ^ n`, there exist linear codes
  `C₂ ⊆ C₁ ⊆ (Fin n → ZMod 2)` with `d ≤ minDist C₁`, `d ≤ minDist C₂⊥`, and
  `b + dim C₂ ≤ dim C₁` (so the CSS dimension `dim C₁ - dim C₂ ≥ b`).
* `LinearCode.exists_nestedPair_correctsErrors_of_rate_le`: the rate form. For `4t ≤ n` and target
  CSS dimension `k` with `k + 4 ≤ n · (1 - 2 H₂(2t/n))`, there is a nested pair `C₂ ⊆ C₁` with both
  `C₁` and `C₂⊥` correcting `t` errors and `k + dim C₂ ≤ dim C₁` — the Gilbert–Varshamov rate
  `(dim C₁ - dim C₂)/n ≥ 1 - 2 H₂(2t/n)` of N&C (10.122)/(10.74).

## Implementation notes

The proof is a **single Varshamov averaging argument over one random matrix**
`M : Matrix (Fin (a + b)) (Fin n) (ZMod 2)`. Setting `C₁ := ker (top a rows of M)` and
`C₂ := ker M` makes `C₂ ⊆ C₁` automatic, and the two distance requirements become two families of
"bad" matrices whose union we bound below `2 ^ ((a+b)·n)`:

* **(cond1)** `minDist C₁ ≥ d` fails only if some nonzero word `w` of weight `< d` lies in `C₁`,
  i.e. the top `a` coordinates of `M *ᵥ w` vanish. For each fixed `w ≠ 0` the map
  `M ↦ (M *ᵥ w) ∘ castAdd` is a surjective linear map onto `Fin a → ZMod 2`, so at most
  `2 ^ ((a+b)·n - a)` matrices are killed; a union bound over the `< ∑_{i<d} C(n,i)` such words
  controls this family.
* **(cond2)** `minDist C₂⊥ ≥ d` fails only if the row space of `M` (which equals `C₂⊥`) contains a
  nonzero word of weight `< d`, i.e. `z ᵥ* M` has weight `< d` for some `z ≠ 0`. For each fixed
  `z ≠ 0` the map `M ↦ z ᵥ* M` is surjective onto `Fin n → ZMod 2`, so at most
  `(∑_{i<d} C(n,i)) · 2 ^ ((a+b)·n - n)` matrices land a low-weight word; a union bound over the
  `< 2 ^ (a+b)` nonzero `z` controls this family.

`card_fiber_apply_le` is the shared counting lemma (each fibre of a surjective linear map over a
finite field is equinumerous with the kernel, via Mathlib's
`AddMonoidHom.fiberEquivKerOfSurjective`), and `card_filter_hammingNorm_lt_le` of
`ToMathlib.InformationTheory.Coding.GilbertVarshamov` supplies the ball-volume bound. `C₁` and the
row space `C₂⊥` are packaged through the *composition* combinators `LinearMap.funLeft` (restrict to
the top `a` rows) and `Matrix.vecMulLinear` (row space) rather than `submatrix`/`transpose`, which
keeps the bundled maps light to elaborate. The dimension bookkeeping identifies `C₂⊥` with
`range (Matrix.vecMulLinear M)` via the general dual-of-kernel identity
`LinearCode.dual_ker_mulVecLin`; that space is `(a+b)`-dimensional because `Matrix.vecMulLinear M`
is injective (cond2 forces every nonzero `z` off the kernel), which reads off `dim C₂ = n - (a+b)`
and `dim C₁ ≥ n - a`.
-/

open Finset Matrix

public section

variable {n : ℕ}

/-- **Fibre-count bound.** For a surjective `ZMod 2`-linear map `φ : V → W` between
finite-dimensional spaces and any `g` agreeing with `φ` pointwise, the fibre `{v | g v = w}` is
equinumerous with the kernel, so has cardinality `2 ^ (dim V - dim W)`. This is the shared counting
step of the Varshamov union bound below; it is stated via `Nat.card` on the subtype (no
`DecidablePred`), and via a *raw* `g` (with `hg : ∀ v, φ v = g v`) so that call sites can plug in
their concrete map without the bundled `φ` ever appearing in the conclusion. The fibre ≃ kernel
equivalence is Mathlib's `AddMonoidHom.fiberEquivKerOfSurjective` (routed through
`φ.toAddMonoidHom`), not a bespoke coset bijection. -/
private theorem card_fiber_apply_le {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [FiniteDimensional (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (φ : V →ₗ[ZMod 2] W) {g : V → W} (hg : ∀ v, φ v = g v) (hφ : Function.Surjective φ) (w : W) :
    Nat.card {v // g v = w} ≤ 2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W) := by
  have hkerfr : Module.finrank (ZMod 2) ↥(LinearMap.ker φ)
      = Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.mpr hφ, finrank_top] at h
    omega
  -- the fibre is equinumerous with the kernel via the library equivalence for additive homs
  have hsurj' : Function.Surjective ⇑φ.toAddMonoidHom := by
    rw [LinearMap.toAddMonoidHom_coe]; exact hφ
  have e1 : {v // g v = w} ≃ ↑(⇑φ.toAddMonoidHom ⁻¹' {w}) :=
    Equiv.subtypeEquivRight fun v => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, LinearMap.toAddMonoidHom_coe, hg]
  have e3 : (↥φ.toAddMonoidHom.ker) ≃ ↥(LinearMap.ker φ) :=
    Equiv.subtypeEquivRight fun v => by
      simp only [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, LinearMap.mem_ker]
  have hcard : Nat.card {v // g v = w} = Nat.card ↥(LinearMap.ker φ) :=
    Nat.card_congr (e1.trans ((φ.toAddMonoidHom.fiberEquivKerOfSurjective hsurj' w).trans e3))
  have hval : Nat.card {v // g v = w}
      = 2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W) := by
    rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), hkerfr, Nat.card_eq_fintype_card,
      ZMod.card]
  exact hval.le

/-- **cond1 counting.** For a nonzero word `w`, at most `2 ^ ((a+b)·n - a)` of the `(a + b) × n`
binary matrices have the top `a` coordinates of `M *ᵥ w` all zero. -/
private theorem card_filter_mulVec_top_eq_zero_le (a b : ℕ) {w : Fin n → ZMod 2} (hw : w ≠ 0) :
    (Finset.univ.filter (fun M : Matrix (Fin (a + b)) (Fin n) (ZMod 2) =>
        (fun i => (M *ᵥ w) (Fin.castAdd b i)) = 0)).card ≤ 2 ^ ((a + b) * n - a) := by
  classical
  let φ : Matrix (Fin (a + b)) (Fin n) (ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2) :=
    { toFun := fun M => fun i => (M *ᵥ w) (Fin.castAdd b i)
      map_add' := fun A B => by funext i; simp [Matrix.add_mulVec]
      map_smul' := fun c A => by funext i; simp [Matrix.smul_mulVec] }
  have hsurj : Function.Surjective φ := by
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hw
    intro y
    refine ⟨Matrix.of (fun r cc => if cc = j0 then
      Fin.append y (0 : Fin b → ZMod 2) r * (w j0)⁻¹ else 0), ?_⟩
    funext i
    change ∑ j, (if j = j0 then Fin.append y (0 : Fin b → ZMod 2) (Fin.castAdd b i)
      * (w j0)⁻¹ else 0) * w j = y i
    rw [Finset.sum_eq_single j0]
    · rw [ite_eq_left rfl, Fin.append_left, mul_assoc, inv_mul_cancel₀ hj0, mul_one]
    · intro c _ hc; rw [ite_eq_right hc, zero_mul]
    · intro h; exact absurd (Finset.mem_univ j0) h
  have hexp : Module.finrank (ZMod 2) (Matrix (Fin (a + b)) (Fin n) (ZMod 2))
      - Module.finrank (ZMod 2) (Fin a → ZMod 2) = (a + b) * n - a := by
    simp [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← hexp]
  exact card_fiber_apply_le φ (g := fun M => fun i => (M *ᵥ w) (Fin.castAdd b i))
    (fun _ => rfl) hsurj 0

/-- **cond2 counting.** For a nonzero coefficient vector `z`, at most
`(∑_{i<d} C(n,i)) · 2 ^ ((a+b)·n - n)` of the `(a + b) × n` binary matrices have `z ᵥ* M`
(a codeword of the row space `C₂⊥`) of weight `< d`. -/
private theorem card_filter_vecMul_hammingNorm_lt_le (a b d : ℕ) {z : Fin (a + b) → ZMod 2}
    (hz : z ≠ 0) :
    (Finset.univ.filter (fun M : Matrix (Fin (a + b)) (Fin n) (ZMod 2) =>
        hammingNorm (Matrix.vecMul z M) < d)).card
      ≤ (∑ i ∈ Finset.range d, n.choose i) * 2 ^ ((a + b) * n - n) := by
  classical
  let φ : Matrix (Fin (a + b)) (Fin n) (ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    { toFun := fun M => Matrix.vecMul z M
      map_add' := fun A B => by funext i; simp [Matrix.vecMul_add]
      map_smul' := fun c A => by funext i; simp [Matrix.vecMul_smul] }
  have hsurj : Function.Surjective φ := by
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hz
    intro y
    refine ⟨Matrix.of (fun r c => if r = i0 then y c * (z i0)⁻¹ else 0), ?_⟩
    funext c
    change ∑ r, z r * (if r = i0 then y c * (z i0)⁻¹ else 0) = y c
    rw [Finset.sum_eq_single i0]
    · rw [ite_eq_left rfl, mul_comm, mul_assoc, inv_mul_cancel₀ hi0, mul_one]
    · intro r _ hr; rw [ite_eq_right hr, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i0) h
  have hsub : (Finset.univ.filter (fun M : Matrix (Fin (a + b)) (Fin n) (ZMod 2) =>
        hammingNorm (Matrix.vecMul z M) < d))
      ⊆ (Finset.univ.filter (fun v : Fin n → ZMod 2 => hammingNorm v < d)).biUnion
          (fun v => Finset.univ.filter (fun M => Matrix.vecMul z M = v)) := by
    intro M hM
    rw [Finset.mem_filter] at hM
    rw [Finset.mem_biUnion]
    exact ⟨Matrix.vecMul z M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM.2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  calc (Finset.univ.filter (fun M : Matrix (Fin (a + b)) (Fin n) (ZMod 2) =>
          hammingNorm (Matrix.vecMul z M) < d)).card
      ≤ ((Finset.univ.filter (fun v : Fin n → ZMod 2 => hammingNorm v < d)).biUnion
          (fun v => Finset.univ.filter (fun M => Matrix.vecMul z M = v))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n → ZMod 2 => hammingNorm v < d),
          (Finset.univ.filter (fun M => Matrix.vecMul z M = v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ Finset.univ.filter (fun v : Fin n → ZMod 2 => hammingNorm v < d),
          2 ^ ((a + b) * n - n) := by
        refine Finset.sum_le_sum (fun v _ => ?_)
        have hexp : Module.finrank (ZMod 2) (Matrix (Fin (a + b)) (Fin n) (ZMod 2))
            - Module.finrank (ZMod 2) (Fin n → ZMod 2) = (a + b) * n - n := by
          simp [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← hexp]
        exact card_fiber_apply_le φ (g := fun M => Matrix.vecMul z M) (fun _ => rfl) hsurj v
    _ = (Finset.univ.filter (fun v : Fin n → ZMod 2 => hammingNorm v < d)).card
          * 2 ^ ((a + b) * n - n) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (∑ i ∈ Finset.range d, n.choose i) * 2 ^ ((a + b) * n - n) := by
        gcongr
        exact card_filter_hammingNorm_lt_le d

namespace LinearCode

/-- **Gilbert–Varshamov existence for CSS codes** (counting form; Nielsen & Chuang, Problem 10.2,
eq. (10.122)). Given block length `n` and parameters `a, b, d` with `1 ≤ d`, `a ≤ n`, and the joint
Hamming-ball-volume condition `(∑_{i<d} C(n,i)) · (2 ^ (n - a) + 2 ^ (a + b)) < 2 ^ n`, there is a
nested pair of binary linear codes `C₂ ⊆ C₁ ⊆ (Fin n → ZMod 2)` with

* `d ≤ minDist C₁` (so `C₁` corrects `t` errors when `d = 2t + 1`);
* `d ≤ minDist C₂⊥` (so `C₂⊥` corrects `t` errors);
* `b + dim C₂ ≤ dim C₁`, i.e. the CSS code `CSS(C₁, C₂)` has dimension `dim C₁ - dim C₂ ≥ b`.

This is the combinatorial heart of the CSS Gilbert–Varshamov bound: with `d = 2t + 1` the two
distance requirements each consume one factor `H₂(2t/n)` of the ball volume, which is how the rate
`(dim C₁ - dim C₂)/n ≥ 1 - 2 H₂(2t/n)` acquires its factor of `2`. The proof is a single Varshamov
averaging argument over one random `(a + b) × n` matrix (see the module docstring). -/
theorem exists_nestedPair_minDist_ge (a b d : ℕ) (hd : 1 ≤ d) (han : a ≤ n)
    (hcond : (∑ i ∈ Finset.range d, n.choose i) * (2 ^ (n - a) + 2 ^ (a + b)) < 2 ^ n) :
    ∃ C₁ C₂ : LinearCode (ZMod 2) (Fin n),
      C₂ ≤ C₁ ∧ (d : ℕ∞) ≤ minDist C₁ ∧ (d : ℕ∞) ≤ minDist (dual C₂) ∧
        b + Module.finrank (ZMod 2) C₂ ≤ Module.finrank (ZMod 2) C₁ := by
  classical
  set V := ∑ i ∈ Finset.range d, n.choose i with hV
  have hV1 : 1 ≤ V := by
    rw [hV]
    calc 1 = n.choose 0 := (Nat.choose_zero_right n).symm
      _ ≤ _ := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hd)
  -- `a + b ≥ 1`: otherwise `a = 0` and the hypothesis becomes `V · (2ⁿ + 1) < 2ⁿ`, impossible.
  have hab1 : 1 ≤ a + b := by
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · exfalso
      have ha0 : a = 0 := by omega
      rw [h0, ha0, Nat.sub_zero, pow_zero] at hcond
      have hle : 2 ^ n + 1 ≤ V * (2 ^ n + 1) := le_mul_of_one_le_left (Nat.zero_le _) hV1
      omega
    · exact hpos
  have hnN : n ≤ (a + b) * n := le_mul_of_one_le_left (Nat.zero_le n) hab1
  have hpow1 : (2 : ℕ) ^ ((a + b) * n - a) = 2 ^ (n - a) * 2 ^ ((a + b) * n - n) := by
    rw [← pow_add]; congr 1; omega
  have hpow2 : (2 : ℕ) ^ n * 2 ^ ((a + b) * n - n) = 2 ^ ((a + b) * n) := by
    rw [← pow_add]; congr 1; omega
  have htot : Fintype.card (Matrix (Fin (a + b)) (Fin n) (ZMod 2)) = 2 ^ ((a + b) * n) := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Module.finrank_matrix]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  set bad1 : Finset (Fin n → ZMod 2) :=
    Finset.univ.filter (fun w => w ≠ 0 ∧ hammingNorm w < d) with hbad1
  set bad2 : Finset (Fin (a + b) → ZMod 2) := Finset.univ.filter (fun z => z ≠ 0) with hbad2
  set killers1 : (Fin n → ZMod 2) → Finset (Matrix (Fin (a + b)) (Fin n) (ZMod 2)) :=
    fun w => Finset.univ.filter (fun M => (fun i => (M *ᵥ w) (Fin.castAdd b i)) = 0) with hk1
  set killers2 : (Fin (a + b) → ZMod 2) → Finset (Matrix (Fin (a + b)) (Fin n) (ZMod 2)) :=
    fun z => Finset.univ.filter (fun M => hammingNorm (Matrix.vecMul z M) < d) with hk2
  -- cond1 family: at most `V · 2 ^ ((a+b)·n - a)` matrices.
  have hcard1 : (bad1.biUnion killers1).card ≤ V * 2 ^ ((a + b) * n - a) := by
    calc (bad1.biUnion killers1).card ≤ ∑ w ∈ bad1, (killers1 w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ bad1, 2 ^ ((a + b) * n - a) := by
          refine Finset.sum_le_sum (fun w hw => ?_)
          rw [hbad1, Finset.mem_filter] at hw
          exact card_filter_mulVec_top_eq_zero_le a b hw.2.1
      _ = bad1.card * 2 ^ ((a + b) * n - a) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ V * 2 ^ ((a + b) * n - a) := by
          gcongr
          calc bad1.card
              ≤ (Finset.univ.filter (fun w : Fin n → ZMod 2 => hammingNorm w < d)).card := by
                refine Finset.card_le_card (fun w hw => ?_)
                rw [hbad1, Finset.mem_filter] at hw
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.2.2⟩
            _ ≤ V := card_filter_hammingNorm_lt_le d
  -- cond2 family: at most `2 ^ (a+b) · (V · 2 ^ ((a+b)·n - n))` matrices.
  have hcard2 : (bad2.biUnion killers2).card ≤ 2 ^ (a + b) * (V * 2 ^ ((a + b) * n - n)) := by
    calc (bad2.biUnion killers2).card ≤ ∑ z ∈ bad2, (killers2 z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ bad2, V * 2 ^ ((a + b) * n - n) := by
          refine Finset.sum_le_sum (fun z hz => ?_)
          rw [hbad2, Finset.mem_filter] at hz
          exact card_filter_vecMul_hammingNorm_lt_le a b d hz.2
      _ = bad2.card * (V * 2 ^ ((a + b) * n - n)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ (a + b) * (V * 2 ^ ((a + b) * n - n)) := by
          gcongr
          calc bad2.card ≤ (Finset.univ : Finset (Fin (a + b) → ZMod 2)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = 2 ^ (a + b) := by
                rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
                  Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_fin_fun]
                simp [Nat.card_eq_fintype_card, ZMod.card]
  -- the bad matrices do not exhaust all `2 ^ ((a+b)·n)` matrices.
  have hlt : (bad1.biUnion killers1 ∪ bad2.biUnion killers2).card < 2 ^ ((a + b) * n) := by
    have hstrict : V * (2 ^ (n - a) + 2 ^ (a + b)) * 2 ^ ((a + b) * n - n)
        < 2 ^ n * 2 ^ ((a + b) * n - n) :=
      mul_lt_mul_of_pos_right hcond (by positivity)
    calc (bad1.biUnion killers1 ∪ bad2.biUnion killers2).card
        ≤ (bad1.biUnion killers1).card + (bad2.biUnion killers2).card := Finset.card_union_le _ _
      _ ≤ V * 2 ^ ((a + b) * n - a) + 2 ^ (a + b) * (V * 2 ^ ((a + b) * n - n)) :=
          Nat.add_le_add hcard1 hcard2
      _ = V * (2 ^ (n - a) + 2 ^ (a + b)) * 2 ^ ((a + b) * n - n) := by rw [hpow1]; ring
      _ < 2 ^ n * 2 ^ ((a + b) * n - n) := hstrict
      _ = 2 ^ ((a + b) * n) := hpow2
  -- so there is a matrix `M` satisfying both conditions.
  obtain ⟨M, -, hM⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := bad1.biUnion killers1 ∪ bad2.biUnion killers2) (t := Finset.univ)
    (by rw [Finset.card_univ, htot]; exact hlt)
  rw [Finset.mem_union, not_or] at hM
  obtain ⟨hM1, hM2⟩ := hM
  have hcond1 : ∀ w, w ≠ 0 → hammingNorm w < d → (fun i => (M *ᵥ w) (Fin.castAdd b i)) ≠ 0 := by
    intro w hw hwd hcontra
    exact hM1 (Finset.mem_biUnion.mpr ⟨w,
      by rw [hbad1]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hwd⟩,
      by rw [hk1]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontra⟩⟩)
  have hcond2 : ∀ z, z ≠ 0 → d ≤ hammingNorm (Matrix.vecMul z M) := by
    intro z hz
    by_contra hlt2
    rw [not_le] at hlt2
    exact hM2 (Finset.mem_biUnion.mpr ⟨z,
      by rw [hbad2]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩,
      by rw [hk2]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt2⟩⟩)
  -- `C₁ = ker (restrict to top a rows ∘ (M *ᵥ ·))`, `C₂ = ker (M *ᵥ ·)`.
  set f1 : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2) :=
    (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castAdd b)).comp M.mulVecLin with hf1
  -- `Matrix.vecMulLinear M` is injective (cond2), so the row space `C₂⊥` is `(a+b)`-dimensional.
  have hinj : Function.Injective (Matrix.vecMulLinear M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [Matrix.vecMulLinear_apply] at hz
    by_contra hz0
    have hcz := hcond2 z hz0
    rw [hz, hammingNorm_zero] at hcz
    omega
  have hfrT : Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.vecMulLinear M)) = a + b := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  have habn : a + b ≤ n := by
    have h := Submodule.finrank_le (LinearMap.range (Matrix.vecMulLinear M))
    rw [hfrT, Module.finrank_fin_fun] at h; exact h
  -- the row space `C₂⊥` is the dual of the kernel code — the general (M-independent) identity.
  have hdualeq : dual (LinearMap.ker M.mulVecLin) = LinearMap.range (Matrix.vecMulLinear M) :=
    LinearCode.dual_ker_mulVecLin M
  have hC2fr : Module.finrank (ZMod 2) ↥(LinearMap.ker M.mulVecLin) = n - (a + b) := by
    have hfd := finrank_dual (LinearMap.ker M.mulVecLin)
    rw [hdualeq, hfrT] at hfd
    simp only [Fintype.card_fin] at hfd
    omega
  have hC1fr : n - a ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker f1) := by
    have hrn1 := LinearMap.finrank_range_add_finrank_ker f1
    rw [Module.finrank_fin_fun] at hrn1
    have hrle1 : Module.finrank (ZMod 2) ↥(LinearMap.range f1) ≤ a := by
      have h := Submodule.finrank_le (LinearMap.range f1)
      rwa [Module.finrank_fin_fun] at h
    omega
  refine ⟨LinearMap.ker f1, LinearMap.ker M.mulVecLin, ?_, ?_, ?_, ?_⟩
  · -- `C₂ ⊆ C₁`.
    intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
    rw [LinearMap.mem_ker, hf1, LinearMap.comp_apply, Matrix.mulVecLin_apply, hx, map_zero]
  · -- `d ≤ minDist C₁`.
    rw [le_minDist_iff]
    intro c hc hc0
    rw [LinearMap.mem_ker, hf1, LinearMap.comp_apply, Matrix.mulVecLin_apply] at hc
    rw [Nat.cast_le]
    by_contra hlt3
    rw [not_le] at hlt3
    refine hcond1 c hc0 hlt3 ?_
    funext i
    rw [← LinearMap.funLeft_apply (ZMod 2) (ZMod 2) (Fin.castAdd b) (M *ᵥ c) i, hc]
  · -- `d ≤ minDist C₂⊥`.
    rw [hdualeq, le_minDist_iff]
    intro c hc hc0
    obtain ⟨z, rfl⟩ := hc
    rw [Nat.cast_le, Matrix.vecMulLinear_apply]
    refine hcond2 z (fun hz0 => hc0 ?_)
    rw [hz0]; exact map_zero _
  · -- dimension bound `b + dim C₂ ≤ dim C₁`.
    rw [hC2fr]
    omega

/-- **Gilbert–Varshamov bound for CSS codes, entropy (rate) form** (Nielsen & Chuang, Problem 10.2,
eqs. (10.122)/(10.74)). In the regime `4t ≤ n` (so the entropy argument `2t/n` lies in `[0, 1/2]`),
if the target CSS dimension `k` satisfies `k + 4 ≤ n · (1 - 2 H₂(2t/n))` — i.e.
`k / n ≥ 1 - 2 H₂(2t/n)` up to a vanishing additive constant, with `H₂ = Real.binEntropyBit` the
base-`2` binary entropy — then there is a nested pair of binary linear codes
`C₂ ⊆ C₁ ⊆ (Fin n → ZMod 2)` with

* `CorrectsErrors C₁ t` (i.e. `2t + 1 ≤ minDist C₁`);
* `CorrectsErrors (dual C₂) t` (i.e. `2t + 1 ≤ minDist C₂⊥`);
* `k + dim C₂ ≤ dim C₁`, i.e. the CSS code `CSS(C₁, C₂)` has dimension `dim C₁ - dim C₂ ≥ k`.

By the CSS construction of §10.4.2 (both `C₁` and `C₂⊥` correcting `t` errors), such a pair yields
an `[n, dim C₁ - dim C₂]` quantum code correcting `t` qubit errors; this rate statement is the
combinatorial content of the quantum Gilbert–Varshamov bound (10.74). The factor of `2` in front
of `H₂` comes from the two distance constraints, one on `C₁` and one on `C₂⊥`, each consuming one
factor `H₂(2t/n)` of the Hamming-ball volume.

The proof plugs `d = 2t + 1` into the counting form `exists_nestedPair_minDist_ge`, choosing the
`C₁`-codimension `a = s + 1` where `s = ⌈n · H₂(2t/n)⌉₊` bounds the ball volume
`V = ∑_{i ≤ 2t} C(n, i) ≤ 2 ^ (n H₂) ≤ 2 ^ s` (`sum_range_choose_le_rpow_mul_binEntropyBit`), and
`b = k`. The joint ball-volume hypothesis then reduces to `2 ^ (n-1) + 2 ^ (2s+1+k) < 2 ^ n`, which
holds because the rate bound forces `2s + 1 + k ≤ n - 2`. The small additive constant `4`
(negligible as `n → ∞`, matching N&C's asymptotic phrasing of (10.74)) absorbs the ceiling slack in
`s` and the strictness of the counting condition. -/
theorem exists_nestedPair_correctsErrors_of_rate_le {n k t : ℕ} (h4t : 4 * t ≤ n)
    (hrate : (k : ℝ) + 4 ≤ n * (1 - 2 * Real.binEntropyBit (2 * t / n))) :
    ∃ C₁ C₂ : LinearCode (ZMod 2) (Fin n),
      C₂ ≤ C₁ ∧ CorrectsErrors C₁ t ∧ CorrectsErrors (dual C₂) t ∧
        k + Module.finrank (ZMod 2) C₂ ≤ Module.finrank (ZMod 2) C₁ := by
  classical
  set H : ℝ := Real.binEntropyBit (2 * t / n) with hH
  -- `n > 0`: otherwise the rate hypothesis reads `k + 4 ≤ 0`.
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · subst hn0
      simp only [Nat.cast_zero, zero_mul] at hrate
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    · exact hpos
  -- Entropy regime `2·(2t) ≤ n` and `2t/n ∈ [0, 1]`, hence `H ≥ 0`.
  have hrn : 2 * (2 * t) ≤ n := by omega
  have hp0 : (0 : ℝ) ≤ 2 * t / n := by positivity
  have hp1 : (2 * (t : ℝ) / n) ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast (show 2 * t ≤ n by omega)) (by positivity)
  have hH0 : (0 : ℝ) ≤ H := by rw [hH]; exact Real.binEntropyBit_nonneg hp0 hp1
  -- Hamming-ball volume `V = ∑_{i ≤ 2t} C(n, i)`, and its natural power bound `V ≤ 2 ^ s`.
  set V : ℕ := ∑ i ∈ Finset.range (2 * t + 1), n.choose i with hV
  set s : ℕ := ⌈(n : ℝ) * H⌉₊ with hs
  have hnH0 : (0 : ℝ) ≤ (n : ℝ) * H := mul_nonneg (Nat.cast_nonneg n) hH0
  have hVR : (V : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * H) := by
    have hsum := sum_range_choose_le_rpow_mul_binEntropyBit (r := 2 * t) (n := n) hrn
    rw [hV, hH]; push_cast at hsum ⊢; exact hsum
  have hVs : V ≤ 2 ^ s := by
    have hle : (n : ℝ) * H ≤ (s : ℝ) := Nat.le_ceil _
    have h2 : (V : ℝ) ≤ (2 : ℝ) ^ (s : ℕ) := by
      refine hVR.trans ?_
      rw [← Real.rpow_natCast (2 : ℝ) s]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    exact_mod_cast h2
  -- Rate bound ⇒ the discrete budget `k + 2s + 3 ≤ n` (ceiling + strictness slack in the `+4`).
  have hlt : (s : ℝ) < (n : ℝ) * H + 1 := Nat.ceil_lt_add_one hnH0
  have hks : k + 2 * s + 3 ≤ n := by
    have hR : (k : ℝ) + 2 * (s : ℝ) + 3 < (n : ℝ) + 1 := by nlinarith [hlt, hrate]
    have : (k + 2 * s + 3 : ℕ) < n + 1 := by exact_mod_cast hR
    omega
  -- The joint ball-volume condition for the counting form, with `a = s + 1`, `b = k`, `d = 2t + 1`.
  have hcond : V * (2 ^ (n - (s + 1)) + 2 ^ (s + 1 + k)) < 2 ^ n := by
    have hpos : 0 < (2 : ℕ) ^ (n - 2) := pow_pos (by norm_num) _
    calc V * (2 ^ (n - (s + 1)) + 2 ^ (s + 1 + k))
        ≤ 2 ^ s * (2 ^ (n - (s + 1)) + 2 ^ (s + 1 + k)) := by gcongr
      _ = 2 ^ s * 2 ^ (n - (s + 1)) + 2 ^ s * 2 ^ (s + 1 + k) := by ring
      _ = 2 ^ (n - 1) + 2 ^ (2 * s + 1 + k) := by
          rw [← pow_add, ← pow_add]; congr 2 <;> omega
      _ ≤ 2 ^ (n - 1) + 2 ^ (n - 2) := by
          gcongr
          omega
      _ = 3 * 2 ^ (n - 2) := by rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; ring
      _ < 4 * 2 ^ (n - 2) := by omega
      _ = 2 ^ n := by
          conv_rhs => rw [show n = (n - 2) + 2 by omega]
          rw [pow_add]; ring
  -- Assemble via the counting form: the output existential unifies with the goal up to the
  -- `CorrectsErrors C t` ↦ `↑(2t+1) ≤ minDist C` defeq.
  exact exists_nestedPair_minDist_ge (s + 1) k (2 * t + 1) (by omega) (by omega) hcond

end LinearCode

end
