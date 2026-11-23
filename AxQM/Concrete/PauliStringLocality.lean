/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliString
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Concrete: locality of Pauli strings and the polynomial count of local terms

It supplies the combinatorial
core behind **Nielsen & Chuang, Exercise 4.48**: *the restriction of each term `Hₖ` in a
Hamiltonian `H = Σₖ Hₖ` (eq. 4.97) to involve at most a constant `c` particles implies that the
number of terms `L` is upper bounded by a polynomial in the particle count `n`.*

N&C's own examples of local terms are Pauli strings — "two-body interactions such as `XᵢXⱼ` and
one-body Hamiltonians such as `Xᵢ`" (§4.7.2). In this library a Pauli string on `n` qubits is the
index `g : Fin n → Fin 4` (a choice of `{I, X, Y, Z}` per qubit, `Concrete.pauliString`). The set
of qubits it acts on non-trivially — its **support** — is `{i | g i ≠ 0}`, and "the term acts on
at most `c` particles" is exactly `(support g).card ≤ c`.

The heart of N&C's argument is a *counting* fact: there are only polynomially many ways to choose
which `≤ c` of the `n` particles a term acts on. This file makes that precise and proves the
polynomial bound; the statement that these `g` index genuine Hamiltonian terms
`pauliStringHamiltonian g (h g)` (`Observable`s on the register `qudit (2ⁿ)`) is in
`AxQM/NC/Ch4/Exercise4_48.lean`.

Everything here is stated for raw index/combinatorial data (`Fin n → Fin 4`, `Finset`,
`Concrete.pauliString`).

## Main definitions

* `Concrete.pauliStringSupport g` — the support `{i | g i ≠ 0}` of the Pauli string `g`, the set
  of qubits it acts on non-trivially.
* `Concrete.localPauliStrings c n` — the Pauli strings on `n` qubits acting on at most `c`
  particles (support of size `≤ c`): the "menu" of `c`-local Hamiltonian terms.

## Main results

* `Concrete.pauliString_apply_eq_zero_of_notMem_support` — a Pauli string acts as the identity off
  its support: its `(i, j)` entry vanishes whenever some non-support qubit `k` has `i k ≠ j k`.
  This justifies the name "support".
* `Concrete.card_finset_card_le_le` — **the counting core**: the number of subsets of an
  `n`-element set of size `≤ c` is at most `(n + 1) ^ c`. This is N&C's "polynomially many ways to
  pick `≤ c` particles".
* `Concrete.card_localPauliStrings_le` — the number of `c`-local Pauli strings on `n` qubits is at
  most `4 ^ c * (n + 1) ^ c`, a polynomial in `n` of degree `c`.
* `Concrete.exists_polynomial_card_localPauliStrings_le` — the same as a literal
  `Polynomial ℕ` bound: a single polynomial `p` (independent of `n`) with
  `(localPauliStrings c n).card ≤ p.eval n` for all `n`.
* `Concrete.card_filter_pauliStringSupport_eq` / `Concrete.card_filter_pauliStringSupport_card_eq` /
  `Concrete.card_localPauliStrings_eq` — the **exact** counts sharpening the `≤` bounds: the fibre
  of fixed support `S` has `3 ^ |S|` strings, there are `C(n, j) · 3ʲ` strings of weight exactly
  `j`, and `(localPauliStrings t n).card = ∑_{j=0}^{t} C(n, j) · 3ʲ` (N&C eq. (10.50), the
  left-hand multiplicand of the quantum Hamming bound (10.51), Exercise 10.50).
-/

open Matrix
open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The support of a Pauli string -/

/-- The **support** of the Pauli string `g : Fin n → Fin 4`: the set of qubits `{i | g i ≠ 0}` on
which it acts non-trivially (`g i ≠ 0` means the `i`-th factor is one of `X, Y, Z`, not `I`). The
number of particles the corresponding local term acts on is `(pauliStringSupport g).card`. -/
def pauliStringSupport (g : Fin n → Fin 4) : Finset (Fin n) :=
  Finset.univ.filter (fun i => g i ≠ 0)

@[simp] theorem mem_pauliStringSupport {g : Fin n → Fin 4} {i : Fin n} :
    i ∈ pauliStringSupport g ↔ g i ≠ 0 := by
  simp [pauliStringSupport]

/-- The dual of `mem_pauliStringSupport`: a qubit `i` is **outside** the support of the Pauli
string `g` exactly when its factor is the identity, `g i = 0`. (Not a `simp` lemma: it is already
provable by `simp` via the `@[simp] mem_pauliStringSupport` above, so tagging it `@[simp]` would be
flagged as redundant; it is kept as a citable form for the local-term proofs.) -/
theorem notMem_pauliStringSupport {g : Fin n → Fin 4} {i : Fin n} :
    i ∉ pauliStringSupport g ↔ g i = 0 := by
  simp [pauliStringSupport]

/-- A Pauli string acts as the **identity off its support**: if `k` is not in the support
(`g k = 0`, so the `k`-th factor is `I`) and `i k ≠ j k`, then the `(i, j)` entry of `pauliString g`
is `0`. Hence `pauliString g` is diagonal in every non-support qubit, i.e. acts only on the
`(pauliStringSupport g)` qubits — justifying the name "support". -/
theorem pauliString_apply_eq_zero_of_notMem_support (g : Fin n → Fin 4) {i j : Fin n → Fin 2}
    {k : Fin n} (hk : k ∉ pauliStringSupport g) (hij : i k ≠ j k) :
    pauliString g i j = 0 := by
  rw [pauliString_apply]
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  simp [notMem_pauliStringSupport.mp hk, pauli, hij]

/-! ### The counting core: polynomially many subsets of bounded size -/

/-- **The counting core of Exercise 4.48.** The number of subsets of an `n`-element set of
cardinality at most `c` is bounded by the polynomial `(n + 1) ^ c`. This is the precise form of
N&C's "there are only polynomially many ways to choose which `≤ c` of the `n` particles a term acts
on": grouping the terms `Hₖ` by the set of particles they couple, `L` is at most this count.

Proof: fibring over the cardinality `k ≤ c`, the count is `Σ_{k=0}^{c} C(n, k)`; bounding each
binomial `C(n, k) ≤ nᵏ` (`Nat.choose_le_pow`) and then `nᵏ ≤ nᵏ · C(c, k)` (as `C(c, k) ≥ 1` for
`k ≤ c`), the sum is `Σ_{k=0}^{c} nᵏ C(c, k) = (n + 1)ᶜ` by the binomial theorem. -/
theorem card_finset_card_le_le (n c : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ c)).card ≤ (n + 1) ^ c := by
  classical
  have hmaps : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ c),
      S.card ∈ Finset.range (c + 1) := by
    intro S hS
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.mem_filter.mp hS).2
  have key : (n + 1) ^ c = ∑ k ∈ Finset.range (c + 1), n ^ k * c.choose k := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, Nat.cast_id]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ k ∈ Finset.range (c + 1),
          ((Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ c)).filter
            (fun S => S.card = k)).card
      ≤ ∑ k ∈ Finset.range (c + 1), n.choose k := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hsub :
            (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ c)).filter
                (fun S => S.card = k)
              ⊆ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k) := by
          intro S hS
          rw [Finset.mem_filter] at hS ⊢
          exact ⟨Finset.mem_univ S, hS.2⟩
        have heq : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = k)).card
            = n.choose k := by
          rw [Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ,
            Fintype.card_fin]
        exact le_trans (Finset.card_le_card hsub) (le_of_eq heq)
    _ ≤ ∑ k ∈ Finset.range (c + 1), n ^ k := Finset.sum_le_sum fun k _ => Nat.choose_le_pow n k
    _ ≤ ∑ k ∈ Finset.range (c + 1), n ^ k * c.choose k := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_range, Nat.lt_succ_iff] at hk
        exact Nat.le_mul_of_pos_right _ (Nat.choose_pos hk)
    _ = (n + 1) ^ c := key.symm

/-! ### The `c`-local Pauli strings and their polynomial count -/

/-- The **`c`-local Pauli strings** on `n` qubits: those acting on at most `c` particles
(`(pauliStringSupport g).card ≤ c`). This is the menu of possible `c`-local Hamiltonian terms in
the Pauli picture — each `g` names a term `h_g · g` of a Hamiltonian `H = Σ_g h_g g`. -/
def localPauliStrings (c n : ℕ) : Finset (Fin n → Fin 4) :=
  Finset.univ.filter (fun g => (pauliStringSupport g).card ≤ c)

@[simp] theorem mem_localPauliStrings {c : ℕ} {g : Fin n → Fin 4} :
    g ∈ localPauliStrings c n ↔ (pauliStringSupport g).card ≤ c := by
  simp [localPauliStrings]

/-- **The number of Pauli strings on `n` qubits with a fixed support `S` is at most `4 ^ |S|`.** A
Pauli string with support exactly `S` is determined by its values on `S` (it is `0` off `S`), and
those values lie in `Fin 4`; restriction to `S` is therefore injective on the fibre, bounding its
cardinality by `Fintype.card (S → Fin 4) = 4 ^ |S|`. -/
theorem card_filter_pauliStringSupport_eq_le (S : Finset (Fin n)) :
    (Finset.univ.filter (fun g : Fin n → Fin 4 => pauliStringSupport g = S)).card ≤ 4 ^ S.card := by
  classical
  calc (Finset.univ.filter (fun g : Fin n → Fin 4 => pauliStringSupport g = S)).card
      ≤ (Finset.univ : Finset (S → Fin 4)).card := by
        refine Finset.card_le_card_of_injOn (fun g => fun i : S => g i.1)
          (fun g _ => Finset.mem_univ _) ?_
        intro g₁ hg₁ g₂ hg₂ heq
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg₁ hg₂
        funext i
        by_cases hi : i ∈ S
        · exact congrFun heq ⟨i, hi⟩
        · have h1 : g₁ i = 0 := notMem_pauliStringSupport.mp (by rw [hg₁]; exact hi)
          have h2 : g₂ i = 0 := notMem_pauliStringSupport.mp (by rw [hg₂]; exact hi)
          rw [h1, h2]
    _ = 4 ^ S.card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

/-- **Exercise 4.48, combinatorial form.** The number of `c`-local Pauli strings on `n` qubits is
at most `4 ^ c * (n + 1) ^ c`, a polynomial in the particle count `n` (of degree `c`). Any
Hamiltonian `H = Σ_g h_g g` whose terms are each `c`-local therefore has at most polynomially many
terms `L`.

Proof: fibring over the support `S = pauliStringSupport g` (which ranges over the subsets of size
`≤ c`), each fibre has at most `4 ^ |S| ≤ 4 ^ c` members
(`card_filter_pauliStringSupport_eq_le`), and there are at most `(n + 1) ^ c` supports
(`card_finset_card_le_le`), giving `4 ^ c * (n + 1) ^ c`. -/
theorem card_localPauliStrings_le (c n : ℕ) :
    (localPauliStrings c n).card ≤ 4 ^ c * (n + 1) ^ c := by
  classical
  have hmaps : ∀ g ∈ localPauliStrings c n,
      pauliStringSupport g ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ c) := by
    intro g hg
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (mem_localPauliStrings).mp hg⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ c),
          ((localPauliStrings c n).filter (fun g => pauliStringSupport g = S)).card
      ≤ ∑ _S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ c), 4 ^ c := by
        refine Finset.sum_le_sum fun S hS => ?_
        have hSc : S.card ≤ c := (Finset.mem_filter.mp hS).2
        refine le_trans (Finset.card_le_card ?_)
          (le_trans (card_filter_pauliStringSupport_eq_le S)
            (Nat.pow_le_pow_right (by norm_num) hSc))
        intro g hg
        rw [Finset.mem_filter] at hg ⊢
        exact ⟨Finset.mem_univ g, hg.2⟩
    _ = (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ c)).card * 4 ^ c := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (n + 1) ^ c * 4 ^ c := Nat.mul_le_mul (card_finset_card_le_le n c) le_rfl
    _ = 4 ^ c * (n + 1) ^ c := by ring

/-- **Exercise 4.48, "`L` is bounded by a polynomial in `n`".** For a fixed locality bound `c`
there is a single polynomial `p : Polynomial ℕ` (namely `4ᶜ · (X + 1)ᶜ`, of degree `c` and
independent of `n`) such that the number of `c`-local Pauli strings on `n` qubits is at most
`p.eval n` for every `n`. This is the literal reading of "`L` is upper bounded by a polynomial in
`n`". -/
theorem exists_polynomial_card_localPauliStrings_le (c : ℕ) :
    ∃ p : Polynomial ℕ, ∀ n, (localPauliStrings c n).card ≤ p.eval n := by
  refine ⟨Polynomial.C (4 ^ c) * (Polynomial.X + 1) ^ c, fun n => ?_⟩
  simpa using card_localPauliStrings_le c n

/-! ### Exact counts of Pauli strings by weight (the quantum Hamming bound, N&C §10.3.4)

The `≤` bounds above suffice for the polynomial-locality statement of Exercise 4.48, but the
**quantum Hamming bound** (N&C eqs. (10.50)–(10.51), Exercise 10.50) needs the *exact* count of
Pauli strings of a given weight. A string with support exactly `S` carries one of the three
non-identity Paulis `X, Y, Z` on each of the `|S|` sites of `S` (and `I` off `S`), so its fibre has
cardinality exactly `3 ^ |S|`. Summing over the `C(n, j)` supports of each size `j ≤ t` gives the
number of Pauli strings of weight `≤ t` on `n` qubits as `∑_{j=0}^{t} C(n, j) · 3ʲ` (N&C
eq. (10.50)) — sharpening `card_localPauliStrings_le` from a `≤` bound to an equality. -/

/-- **The number of Pauli strings on `n` qubits with a fixed support `S` is exactly `3 ^ |S|`.** A
string with support exactly `S` is `0` off `S` and one of the three non-identity Paulis `X, Y, Z`
(the nonzero elements of `Fin 4`) on each of the `|S|` sites of `S`; the choices are independent,
so the fibre is `Fintype.piFinset (fun i => if i ∈ S then {1,2,3} else {0})`, of cardinality
`∏ᵢ (if i ∈ S then 3 else 1) = 3 ^ |S|`. This is the exact form of
`card_filter_pauliStringSupport_eq_le` (which only bounds the fibre by `4 ^ |S|`). -/
theorem card_filter_pauliStringSupport_eq (S : Finset (Fin n)) :
    (Finset.univ.filter (fun g : Fin n → Fin 4 => pauliStringSupport g = S)).card = 3 ^ S.card := by
  classical
  have hmem : ∀ x : Fin 4, x ∈ ({1, 2, 3} : Finset (Fin 4)) ↔ x ≠ 0 := by decide
  have hset : (Finset.univ.filter (fun g : Fin n → Fin 4 => pauliStringSupport g = S))
      = Fintype.piFinset (fun i => if i ∈ S then ({1, 2, 3} : Finset (Fin 4)) else {0}) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hg i
      by_cases hi : i ∈ S
      · simp only [hi, ite_true]; rw [hmem, ← mem_pauliStringSupport, hg]; exact hi
      · simp only [hi, ite_false, Finset.mem_singleton]
        rw [← notMem_pauliStringSupport, hg]; exact hi
    · intro hg
      ext i
      rw [mem_pauliStringSupport]
      by_cases hi : i ∈ S
      · have hgi := hg i; simp only [hi, ite_true, hmem] at hgi; exact iff_of_true hgi hi
      · have hgi := hg i; simp only [hi, ite_false, Finset.mem_singleton] at hgi
        exact iff_of_false (by rw [hgi]; simp) hi
  rw [hset, Fintype.card_piFinset]
  have hcard : ∀ i : Fin n,
      (if i ∈ S then ({1, 2, 3} : Finset (Fin 4)) else {0}).card = if i ∈ S then 3 else 1 := by
    intro i; by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [hcard]
  rw [Finset.prod_ite_mem Finset.univ S (fun _ => 3), Finset.univ_inter, Finset.prod_const]

/-- **The number of Pauli strings on `n` qubits of weight exactly `j` is `C(n, j) · 3ʲ`.** Fibring
over the support `S` (which ranges over the `C(n, j)` subsets of `Fin n` of size `j`), each fibre
has exactly `3 ^ j` members by `card_filter_pauliStringSupport_eq`. This is the `j`-th summand of
N&C's error count (10.50). -/
theorem card_filter_pauliStringSupport_card_eq (j : ℕ) :
    (Finset.univ.filter (fun g : Fin n → Fin 4 => (pauliStringSupport g).card = j)).card
      = n.choose j * 3 ^ j := by
  classical
  have hmaps : ∀ g ∈ Finset.univ.filter (fun g : Fin n → Fin 4 => (pauliStringSupport g).card = j),
      pauliStringSupport g ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = j) := by
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ _, hg.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hval : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = j),
      ((Finset.univ.filter (fun g : Fin n → Fin 4 => (pauliStringSupport g).card = j)).filter
        (fun g => pauliStringSupport g = S)).card = 3 ^ j := by
    intro S hS
    have hSj : S.card = j := (Finset.mem_filter.mp hS).2
    have hrw : (Finset.univ.filter (fun g : Fin n → Fin 4 =>
          (pauliStringSupport g).card = j)).filter (fun g => pauliStringSupport g = S)
        = Finset.univ.filter (fun g : Fin n → Fin 4 => pauliStringSupport g = S) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by rw [h, hSj], h⟩
    rw [hrw, card_filter_pauliStringSupport_eq, hSj]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Nielsen & Chuang eq. (10.50): the number of Pauli strings on `n` qubits of weight `≤ t` is
`∑_{j=0}^{t} C(n, j) · 3ʲ`.** These are exactly the errors correctable by a `t`-error-correcting
code (the identity on all but `≤ t` qubits, each of those carrying one of `X, Y, Z`); the count is
the left-hand multiplicand of the quantum Hamming bound (10.51). Fibring `localPauliStrings t n`
over the weight `j ∈ {0, …, t}` and applying `card_filter_pauliStringSupport_card_eq` on each fibre
gives the sum. This is the exact form of `card_localPauliStrings_le`. -/
theorem card_localPauliStrings_eq (t n : ℕ) :
    (localPauliStrings t n).card = ∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j := by
  classical
  have hmaps : ∀ g ∈ localPauliStrings t n,
      (pauliStringSupport g).card ∈ Finset.range (t + 1) := by
    intro g hg
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (mem_localPauliStrings).mp hg
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  have hrw : (localPauliStrings t n).filter (fun g => (pauliStringSupport g).card = j)
      = Finset.univ.filter (fun g : Fin n → Fin 4 => (pauliStringSupport g).card = j) := by
    ext g
    simp only [Finset.mem_filter, mem_localPauliStrings, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; refine ⟨?_, h⟩; rw [h]; exact hj
  rw [hrw, card_filter_pauliStringSupport_card_eq]

end AxQM.Concrete
