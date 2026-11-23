/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QFTTwoLevel

/-!
# Concrete: embedding a 2×2 unitary into a coordinate pair of a `d × d` matrix (N&C §4.5.1)

The two-level decomposition of an arbitrary `d × d` unitary (Nielsen & Chuang §4.5.1, p. 189) is
built from *two-level* unitaries, each of which is a single `2 × 2` unitary block placed into a
chosen coordinate pair `{p, q}` and acting as the identity everywhere else. This file provides that
general **embedding** `twoLevelEmbed p q G`, independently of the particular `2 × 2`
block chosen (the Givens rotation of `AxQM.Concrete.GivensRotation` is one such block) and
of the column-clearing induction (`Concrete/TwoLevelDecomposition.lean`).

## The construction and its algebra

`twoLevelEmbed p q G` is the `d × d` matrix whose `{p, q} × {p, q}` principal submatrix is `G` and
whose remaining entries are those of the identity. The key structural fact is that, for `p ≠ q`,
`twoLevelEmbed p q` is a **`*`-homomorphism on the `2 × 2` block**:

* `twoLevelEmbed_one` — it sends `1 ↦ 1`;
* `twoLevelEmbed_mul` — it is multiplicative, `embed A * embed B = embed (A * B)`;
* `twoLevelEmbed_conjTranspose` — it commutes with `ᴴ`, `(embed G)ᴴ = embed Gᴴ`.

Unitarity then needs no direct sum manipulation: `(embed G)ᴴ * embed G = embed Gᴴ * embed G =
embed (Gᴴ * G) = embed 1 = 1`. So a unitary `G` embeds to a two-level unitary
(`isTwoLevelUnitary_twoLevelEmbed`), with `{p, q}` as its distinguished block. The action on a
vector (`twoLevelEmbed_mulVec`) mixes only the `p`- and `q`-components via `G`, fixing the rest —
the form the column-clearing step consumes.

## Use

This is a shared building block for the §4.5.1 development (Exercise 4.43's `n`-qubit lift, also
used by Ex 4.37/4.38/4.39); the statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **The two-level embedding.** `twoLevelEmbed p q G` places the `2 × 2` matrix `G` into the
`{p, q} × {p, q}` block of a `d × d` matrix (`p ↦ 0`, `q ↦ 1`) and is the identity on all other
entries. -/
def twoLevelEmbed (p q : Fin d) (G : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j =>
    if i = p then (if j = p then G 0 0 else if j = q then G 0 1 else 0)
    else if i = q then (if j = p then G 1 0 else if j = q then G 1 1 else 0)
    else if i = j then 1 else 0

/-- Unfolding lemma for `twoLevelEmbed` entries. -/
theorem twoLevelEmbed_apply (p q : Fin d) (G : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin d) :
    twoLevelEmbed p q G i j =
      if i = p then (if j = p then G 0 0 else if j = q then G 0 1 else 0)
      else if i = q then (if j = p then G 1 0 else if j = q then G 1 1 else 0)
      else if i = j then 1 else 0 := rfl

variable {p q : Fin d} {G A B : Matrix (Fin 2) (Fin 2) ℂ}

/-- The embedding of the `2 × 2` identity is the `d × d` identity. -/
theorem twoLevelEmbed_one (h : p ≠ q) :
    twoLevelEmbed p q (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i j
  rw [twoLevelEmbed_apply]
  simp only [Matrix.one_apply]
  split_ifs <;> simp_all

/-- **`twoLevelEmbed p q` is multiplicative on the block** (`p ≠ q`): embedding respects matrix
products. This is the structural core making an embedded unitary two-level unitary. -/
theorem twoLevelEmbed_mul (h : p ≠ q) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevelEmbed p q A * twoLevelEmbed p q B = twoLevelEmbed p q (A * B) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hip : i = p
  · rw [Finset.sum_eq_add p q h
      (fun c _ hc => by simp [twoLevelEmbed_apply, hip, hc.1, hc.2]) (by simp) (by simp)]
    by_cases hjp : j = p <;> by_cases hjq : j = q <;>
      simp [twoLevelEmbed_apply, hip, hjp, hjq, Ne.symm h, Matrix.mul_apply,
        Fin.sum_univ_two]
  · by_cases hiq : i = q
    · rw [Finset.sum_eq_add p q h
        (fun c _ hc => by simp [twoLevelEmbed_apply, hiq, hc.1, hc.2]) (by simp) (by simp)]
      by_cases hjp : j = p <;> by_cases hjq : j = q <;>
        simp [twoLevelEmbed_apply, hiq, hjp, hjq, Ne.symm h, Matrix.mul_apply,
          Fin.sum_univ_two]
    · rw [Finset.sum_eq_single i
        (fun c _ hc => by simp [twoLevelEmbed_apply, hip, hiq, Ne.symm hc]) (by simp)]
      simp [twoLevelEmbed_apply, hip, hiq]

/-- **`twoLevelEmbed p q` commutes with the conjugate transpose**:
`(embed G)ᴴ = embed Gᴴ`. The block `ᴴ` is `G`'s, the identity part is real. -/
theorem twoLevelEmbed_conjTranspose (G : Matrix (Fin 2) (Fin 2) ℂ) :
    (twoLevelEmbed p q G)ᴴ = twoLevelEmbed p q Gᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, twoLevelEmbed_apply, twoLevelEmbed_apply]
  simp only [Matrix.conjTranspose_apply]
  split_ifs <;> simp <;> simp_all

/-- **An embedded `2 × 2` unitary is a two-level unitary** (`p ≠ q`), with `{p, q}` its
distinguished block. The unitarity follows from the `*`-homomorphism laws above:
`(embed G)ᴴ · embed G = embed (Gᴴ · G) = embed 1 = 1`. -/
theorem isTwoLevelUnitary_twoLevelEmbed (h : p ≠ q)
    (hG : G ∈ Matrix.unitaryGroup (Fin 2) ℂ) : IsTwoLevelUnitary (twoLevelEmbed p q G) := by
  refine ⟨?_, p, q, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff'] at hG ⊢
    rw [Matrix.star_eq_conjTranspose] at hG ⊢
    rw [twoLevelEmbed_conjTranspose, twoLevelEmbed_mul h, hG, twoLevelEmbed_one h]
  · intro i j hij
    rw [twoLevelEmbed_apply, Matrix.one_apply]
    rcases hij with ⟨hip, hiq⟩ | ⟨hjp, hjq⟩ <;> split_ifs <;> simp_all

/-- **The action of an embedded block on a vector** (`p ≠ q`): `twoLevelEmbed p q G` mixes only the
`p`- and `q`-components of `v` through `G`, leaving every other component fixed. This is the form
consumed by the column-clearing step of §4.5.1. -/
theorem twoLevelEmbed_mulVec (h : p ≠ q) (G : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin d → ℂ)
    (i : Fin d) :
    (twoLevelEmbed p q G *ᵥ v) i =
      if i = p then G 0 0 * v p + G 0 1 * v q
      else if i = q then G 1 0 * v p + G 1 1 * v q
      else v i := by
  simp only [Matrix.mulVec, dotProduct]
  by_cases hip : i = p
  · rw [Finset.sum_eq_add p q h
      (fun c _ hc => by simp [twoLevelEmbed_apply, hip, hc.1, hc.2]) (by simp) (by simp)]
    simp [twoLevelEmbed_apply, hip, Ne.symm h]
  · by_cases hiq : i = q
    · rw [Finset.sum_eq_add p q h
        (fun c _ hc => by simp [twoLevelEmbed_apply, hiq, hc.1, hc.2]) (by simp) (by simp)]
      simp [twoLevelEmbed_apply, hiq, Ne.symm h]
    · rw [Finset.sum_eq_single i
        (fun c _ hc => by simp [twoLevelEmbed_apply, hip, hiq, Ne.symm hc]) (by simp)]
      simp [twoLevelEmbed_apply, hip, hiq]

end AxQM.Concrete
