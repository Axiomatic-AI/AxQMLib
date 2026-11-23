/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelEmbedding
import AxQM.Concrete.RotationDecomposition
import AxQM.Concrete.ComplexExpUnit

/-!
# Concrete: beamsplitters and phase shifters generate every two-level unitary (N&C Problem 7.2.1)

Nielsen & Chuang, Problem 7.2 (p. 346), *Computing with linear optics*, considers quantum
computation with a single photon in a **unary** mode encoding: an `n`-qubit computational-basis
state `|k⟩` is a single photon occupying mode `k` of `d = 2ⁿ` optical modes, so an arbitrary
`n`-qubit gate is a `d × d` unitary acting on the mode amplitudes `Fin d → ℂ`. Part 1 asks to show
that any such unitary can be built entirely from two passive linear-optical elements —
**beamsplitters** and **phase shifters** — and no nonlinear media.

This file supplies the atomic decomposition at the raw-matrix level: every *two-level* unitary
(`AxQM.Concrete.IsTwoLevelUnitary`, the building block of the §4.5.1 decomposition of an
arbitrary `d × d` unitary) that is presented as an embedded `2 × 2` unitary `twoLevelEmbed p q G` is
a finite product of beamsplitter and phase-shifter matrices. Chained with the §4.5.1 headline
(`exists_twoLevelUnitaryList_prod_eq`, that every `d × d` unitary is a product of two-level
unitaries), this gives Part 1.

## The two elements

* `phaseMode p φ` — a **phase shifter** on optical mode `p`: the diagonal `d × d` matrix
  `diag(…, e^{iφ}, …)` with `e^{iφ}` in position `p` and `1` elsewhere. It multiplies the amplitude
  of mode `p` by the phase `e^{iφ}`, fixing every other mode. Always unitary (a diagonal matrix with
  unit-modulus entries), and a two-level unitary (nontrivial only at `(p, p)`).
* `beamSplitter p q θ` — a **beamsplitter** mixing modes `p` and `q`: the two-level embedding
  `twoLevelEmbed p q (R_y θ)` of the real rotation block `R_y(θ) = !![cos(θ/2), -sin(θ/2);
  sin(θ/2), cos(θ/2)]` (`Concrete.rotY`). It applies a real `2 × 2` rotation to the pair of mode
  amplitudes `(p, q)`, fixing the rest — the passive beamsplitter's action on the two spatial modes
  it couples. Unitary and (for `p ≠ q`) a two-level unitary.

`IsLinearOpticalElement V` records that `V` is one of these two — a beamsplitter (on a genuine pair
`p ≠ q`) or a phase shifter.

## The decomposition

The heart is `exists_linearOpticalList_prod_eq_twoLevelEmbed`: for `p ≠ q` and any `2 × 2` unitary
`G`, the embedded two-level unitary `twoLevelEmbed p q G` is the product of a list of linear-optical
elements. The construction is the standard Reck–Zeilinger element built from the **Z–Y
decomposition** (Nielsen & Chuang Theorem 4.1, `exists_zy_decomposition`): writing
`G = e^{iα} R_z(β) R_y(γ) R_z(δ)`, we push the global phase `e^{iα}` and the two diagonal
`R_z`-factors onto the pair `{p, q}` as phase shifters, and the single real `R_y`-rotation as one
beamsplitter:

```
  twoLevelEmbed p q G
    = phaseMode p α · phaseMode q α           -- global phase e^{iα} on both modes
    · phaseMode p (-β/2) · phaseMode q (β/2)  -- R_z(β) = diag(e^{-iβ/2}, e^{iβ/2})
    · beamSplitter p q γ                       -- R_y(γ)
    · phaseMode p (-δ/2) · phaseMode q (δ/2).  -- R_z(δ)
```

The two diagonal factors use `twoLevelEmbed_diag_eq`: embedding a diagonal `2 × 2` block
`diag(e^{iφ}, e^{iψ})` into `{p, q}` is exactly `phaseMode p φ · phaseMode q ψ`. Multiplicativity of
the embedding (`twoLevelEmbed_mul`) turns the four-factor product `(e^{iα} I) · R_z(β) · R_y(γ) ·
R_z(δ)` into the product of the four embedded factors.

The reading of these matrices as `Evolution (qudit d)` gates, and the
universality statement about them, are in `AxQM/NC/Ch7/Problem7_2.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-! ### The two elements -/

/-- **Phase shifter on mode `p`.** The diagonal `d × d` matrix `diag(…, e^{iφ}, …)` with the phase
`e^{iφ}` in position `p` and `1` on every other mode. It multiplies the amplitude of mode `p` by
`e^{iφ}` and fixes the rest — the action of a passive optical phase shifter placed in mode `p`. -/
noncomputable def phaseMode (p : Fin d) (φ : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => if i = p then Complex.exp ((φ : ℂ) * Complex.I) else 1)

/-- **Beamsplitter mixing modes `p` and `q`.** The two-level embedding of the real rotation block
`R_y(θ)` into the coordinate pair `{p, q}`: it applies the `2 × 2` rotation
`!![cos(θ/2), -sin(θ/2); sin(θ/2), cos(θ/2)]` to the amplitudes of modes `p, q` and fixes all other
modes — the passive beamsplitter's action on the two spatial modes it couples. -/
noncomputable def beamSplitter (p q : Fin d) (θ : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  twoLevelEmbed p q (rotY θ)

/-- **A linear-optical element** is a beamsplitter (on a genuine pair `p ≠ q`) or a phase shifter —
the two passive elements Problem 7.2 allows. `IsLinearOpticalElement V` holds when `V` is of one of
these two forms. -/
def IsLinearOpticalElement (V : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∃ (p q : Fin d) (θ : ℝ), p ≠ q ∧ V = beamSplitter p q θ) ∨
    (∃ (p : Fin d) (φ : ℝ), V = phaseMode p φ)

/-! ### Phase shifter -/

/-- Entry formula for a phase shifter: it is diagonal, with `e^{iφ}` at `(p, p)` and `1` on the rest
of the diagonal. -/
theorem phaseMode_apply (p : Fin d) (φ : ℝ) (i j : Fin d) :
    phaseMode p φ i j =
      if i = j then (if i = p then Complex.exp ((φ : ℂ) * Complex.I) else 1) else 0 := by
  simp only [phaseMode, Matrix.diagonal_apply]

/-- **A phase shifter is unitary.** It is a diagonal matrix whose diagonal entries (`e^{iφ}` and
`1`) all have unit modulus. -/
theorem phaseMode_mem_unitaryGroup (p : Fin d) (φ : ℝ) :
    phaseMode p φ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, phaseMode,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs with h
  · exact star_exp_ofReal_mul_I_mul_self φ
  · simp

/-- **A phase shifter is a two-level unitary**, acting non-trivially only on mode `p` (the
one-level / single-phase case `p = q` of `IsTwoLevelUnitary`). -/
theorem isTwoLevelUnitary_phaseMode (p : Fin d) (φ : ℝ) :
    IsTwoLevelUnitary (phaseMode p φ) := by
  refine ⟨phaseMode_mem_unitaryGroup p φ, p, p, ?_⟩
  intro i j hij
  rw [phaseMode_apply, Matrix.one_apply]
  by_cases hIJ : i = j
  · subst hIJ
    have hip : i ≠ p := by rcases hij with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
    simp [hip]
  · simp [hIJ]

/-! ### Beamsplitter -/

/-- **A beamsplitter is unitary** (its rotation block `R_y θ` is unitary, and the embedding
preserves unitarity). -/
theorem beamSplitter_mem_unitaryGroup {p q : Fin d} (h : p ≠ q) (θ : ℝ) :
    beamSplitter p q θ ∈ Matrix.unitaryGroup (Fin d) ℂ :=
  (isTwoLevelUnitary_twoLevelEmbed h (rotY_mem_unitaryGroup θ)).1

/-- **A beamsplitter is a two-level unitary**, acting non-trivially only on the mode pair `{p, q}`
(needs `p ≠ q`). -/
theorem isTwoLevelUnitary_beamSplitter {p q : Fin d} (h : p ≠ q) (θ : ℝ) :
    IsTwoLevelUnitary (beamSplitter p q θ) :=
  isTwoLevelUnitary_twoLevelEmbed h (rotY_mem_unitaryGroup θ)

/-- **Every linear-optical element is a two-level unitary.** (Used later to transfer the
two-level lower bound of Exercise 4.38 to a lower bound on the number of optical components.) -/
theorem isTwoLevelUnitary_of_isLinearOpticalElement {V : Matrix (Fin d) (Fin d) ℂ}
    (hV : IsLinearOpticalElement V) : IsTwoLevelUnitary V := by
  rcases hV with ⟨p, q, θ, hpq, rfl⟩ | ⟨p, φ, rfl⟩
  · exact isTwoLevelUnitary_beamSplitter hpq θ
  · exact isTwoLevelUnitary_phaseMode p φ

/-! ### The diagonal embedding is a product of two phase shifters -/

/-- **Embedding a diagonal `2 × 2` block is a product of two phase shifters.** For `p ≠ q`, if the
`2 × 2` block `G` is diagonal with entries `G₀₀ = e^{iφ}`, `G₁₁ = e^{iψ}`, then embedding it into
the mode pair `{p, q}` is exactly `phaseMode p φ · phaseMode q ψ` — a phase shifter on `p` and one
on `q`. This turns the diagonal `R_z` factors of the Z–Y decomposition into phase shifters. -/
theorem twoLevelEmbed_diag_eq {p q : Fin d} (h : p ≠ q) (φ ψ : ℝ)
    {G : Matrix (Fin 2) (Fin 2) ℂ} (h00 : G 0 0 = Complex.exp ((φ : ℂ) * Complex.I))
    (h11 : G 1 1 = Complex.exp ((ψ : ℂ) * Complex.I)) (h01 : G 0 1 = 0) (h10 : G 1 0 = 0) :
    twoLevelEmbed p q G = phaseMode p φ * phaseMode q ψ := by
  rw [phaseMode, phaseMode, Matrix.diagonal_mul_diagonal]
  ext i j
  rw [twoLevelEmbed_apply, Matrix.diagonal_apply, h00, h11, h01, h10]
  by_cases hip : i = p <;> by_cases hiq : i = q <;> by_cases hjp : j = p <;>
    by_cases hjq : j = q <;> by_cases hij : i = j <;>
    simp_all [Ne.symm h]

/-! ### The Z–Y (Reck–Zeilinger) decomposition of an embedded two-level unitary -/

/-- **A beamsplitter is the embedded `R_y` rotation** — unfolding `beamSplitter`. -/
theorem twoLevelEmbed_rotY_eq_beamSplitter (p q : Fin d) (θ : ℝ) :
    twoLevelEmbed p q (rotY θ) = beamSplitter p q θ := rfl

/-- **Embedding `R_z θ` is a product of two phase shifters.** `R_z(θ) = diag(e^{-iθ/2}, e^{iθ/2})`,
so its embedding into `{p, q}` is `phaseMode p (-θ/2) · phaseMode q (θ/2)`. -/
theorem twoLevelEmbed_rotZ_eq {p q : Fin d} (h : p ≠ q) (θ : ℝ) :
    twoLevelEmbed p q (rotZ θ) = phaseMode p (-(θ / 2)) * phaseMode q (θ / 2) := by
  refine twoLevelEmbed_diag_eq h (-(θ / 2)) (θ / 2) ?_ ?_ ?_ ?_
  · rw [rotZ_apply_zero_zero]; push_cast; ring_nf
  · rw [rotZ_apply_one_one]; push_cast; ring_nf
  · rw [rotZ_eq]; simp
  · rw [rotZ_eq]; simp

/-- **Embedding the global phase `e^{iα} I₂` is a product of two phase shifters** (`e^{iα}` on both
modes `p` and `q`). -/
theorem twoLevelEmbed_smul_one_eq {p q : Fin d} (h : p ≠ q) (α : ℝ) :
    twoLevelEmbed p q (Complex.exp ((α : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = phaseMode p α * phaseMode q α := by
  refine twoLevelEmbed_diag_eq h α α ?_ ?_ ?_ ?_ <;>
    simp [Matrix.smul_apply]

/-- **The Z–Y decomposition of an embedded two-level unitary as a linear-optical product**
(Nielsen & Chuang, Problem 7.2.1, atomic step). For `p ≠ q` and any `2 × 2` unitary `G`, the
two-level unitary `twoLevelEmbed p q G` is the product of the list

```
  [phaseMode p α, phaseMode q α, phaseMode p (-β/2), phaseMode q (β/2),
   beamSplitter p q γ, phaseMode p (-δ/2), phaseMode q (δ/2)]
```

of phase shifters and one beamsplitter, whose angles come from the Z–Y decomposition
`G = e^{iα} R_z(β) R_y(γ) R_z(δ)` (Theorem 4.1). Every factor `IsLinearOpticalElement`. This is the
Reck–Zeilinger realization of an arbitrary two-mode unitary from a single beamsplitter and phase
shifters. -/
theorem exists_linearOpticalList_prod_eq_twoLevelEmbed {p q : Fin d} (h : p ≠ q)
    {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ L : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ V ∈ L, IsLinearOpticalElement V) ∧ L.prod = twoLevelEmbed p q G := by
  obtain ⟨α, β, γ, δ, hzy⟩ := exists_zy_decomposition G hG
  -- rewrite `G` as a four-factor product with the global phase absorbed into an `e^{iα} I₂` head
  have hG' : (Complex.exp ((α : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      * rotZ β * rotY γ * rotZ δ = G := by
    rw [hzy, smul_mul_assoc, one_mul, smul_mul_assoc, smul_mul_assoc]
  refine ⟨[phaseMode p α, phaseMode q α, phaseMode p (-(β / 2)), phaseMode q (β / 2),
           beamSplitter p q γ, phaseMode p (-(δ / 2)), phaseMode q (δ / 2)], ?_, ?_⟩
  · intro V hV
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hV
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨p, α, rfl⟩
    · exact Or.inr ⟨q, α, rfl⟩
    · exact Or.inr ⟨p, -(β / 2), rfl⟩
    · exact Or.inr ⟨q, β / 2, rfl⟩
    · exact Or.inl ⟨p, q, γ, h, rfl⟩
    · exact Or.inr ⟨p, -(δ / 2), rfl⟩
    · exact Or.inr ⟨q, δ / 2, rfl⟩
  · have hblock : twoLevelEmbed p q G
        = phaseMode p α * phaseMode q α * (phaseMode p (-(β / 2)) * phaseMode q (β / 2))
          * beamSplitter p q γ * (phaseMode p (-(δ / 2)) * phaseMode q (δ / 2)) := by
      rw [← hG', ← twoLevelEmbed_mul h, ← twoLevelEmbed_mul h, ← twoLevelEmbed_mul h,
        twoLevelEmbed_smul_one_eq h, twoLevelEmbed_rotZ_eq h, twoLevelEmbed_rotY_eq_beamSplitter,
        twoLevelEmbed_rotZ_eq h]
    rw [hblock]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]

end AxQM.Concrete
