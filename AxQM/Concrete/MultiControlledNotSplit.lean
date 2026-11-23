/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledNotBorrowedMcNot

/-!
# Concrete: the one-dirty-ancilla `Cᵐ(X)` split (Barenco *Elementary gates*, Lemma 7.3)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for an `O(n²)` no-work-qubit circuit of `Toffoli`,
`CNOT` and single-qubit gates implementing the `n`-controlled `NOT` `Cⁿ(X)`. The linear-cascade
sub-project reaches the `O(n²)` count by bottoming each internal `Cᵏ(X)` block of `barencoNCircuit`
in a **linear** `O(k)` number of `Toffoli`s, borrowing the register's idle wires as **dirty**
ancillas.

`AxQM/Concrete/MultiControlledNotBorrowedMcNot.lean` builds the dirty `Cᵏ(X)`
`borrowedMcNot as cs tgt` (Barenco Lemma 7.2): a linear circuit for the `|cs|`-controlled `NOT`,
but requiring `|cs| - 2` borrowed dirty ancillas `as`. That is exactly enough for the **small**
blocks of `barencoNCircuit V (n-1) 0`: a `Cʲ(X)` block sits with `n - j` idle module wires, so the
`j - 2` needed ancillas fit iff `j ≤ n/2 + 1`. The **large** blocks — up to the top `C^{n-1}(X)`
with a *single* idle module wire — carry too few ancillas for Lemma 7.2 directly.

## Barenco Lemma 7.3 — the one-borrowed-wire split

This file closes that gap with Barenco's **Lemma 7.3**: a `Cᵐ(X)` needing only **one** borrowed
dirty wire `a`, by splitting the controls into two halves `A`, `B` (`|A|, |B| ≈ m/2`) and running

`splitMcNot asA A asB B a t = W · V · W · V`, where (reading right to left)

* `V := borrowedMcNot asA A a` is a `C^{|A|}(X)` on the borrowed wire `a`, using `|A| - 2` wires
  `asA` **taken from the other half `B`** as its dirty ancillas (idle while `V` runs);
* `W := borrowedMcNot asB (B ++ [a]) t` is a `C^{|B|+1}(X)` on the target `t`, controls
  `B ∪ {a}`, using `|B| - 1` wires `asB` **taken from `A`** as its dirty ancillas.

Because each `borrowedMcNot` restores its own borrowed ancillas
(`mcNotDenote_borrowedMcNot`), at the bit-string level the four sub-blocks collapse to the four
gates of the Barenco halving identity `mcNot_union_borrow`:
`mcNot (A ∪ B) t = mcNot (insert a B) t ∘ mcNot A a ∘ mcNot (insert a B) t ∘ mcNot A a`
— the borrowed wire `a` is toggled by the two `mcNot A a` (restored) and its dirty part cancels
between the two `mcNot (insert a B) t`, netting `t` flipped iff every control in `A ∪ B` is set
(`mcNotDenote_splitMcNot`). Every gate is a `Toffoli`/`CNOT`/`NOT` (`splitMcNot_gate_mem`, inherited
from the four cascades) and the length is **linear**, `≤ 8|asA| + 8|asB| + 4 = O(m)`
(`splitMcNot_length_le`) — four cascades of half-size each, so `4 · O(m/2) = O(m)`.

The one wire it must borrow (`a`) is the single idle module wire the big `barencoNCircuit` blocks
still have, so `splitMcNot` is the per-block reduction those blocks need; the two control halves
supply each other's Lemma-7.2 ancillas, so **no clean work qubit** and no extra register wire is
required.

Everything here is `Fin 2`/`Finset`/`List` combinatorics. Compare the other `MultiControlledNot*`
files.
-/

namespace AxQM.Concrete

variable {m : ℕ}

/-- **The one-borrowed-wire `Cᵐ(X)` split** (Barenco *Elementary gates*, Lemma 7.3). With controls
split into two halves `A`, `B`, target `t`, and a **single** borrowed dirty wire `a`,
`splitMcNot asA A asB B a t` is the four-block circuit `W · V · W · V` (right to left):
`V := borrowedMcNot asA A a` (a `C^{|A|}(X)` on `a`, dirty ancillas `asA ⊆ B`) alternated with
`W := borrowedMcNot asB (B ++ [a]) t` (a `C^{|B|+1}(X)` on `t`, controls `B ∪ {a}`, dirty ancillas
`asB ⊆ A`). With `|A| = |asA| + 2` and `|B| = |asB| + 1` it is a genuine `C^{|A|+|B|}(X)` restoring
every wire (`mcNotDenote_splitMcNot`), in a linear number of `Toffoli`/`CNOT`/`NOT` gates using just
one borrowed dirty wire. -/
def splitMcNot (asA A asB B : List (Fin m)) (a t : Fin m) : List (McNotGate m) :=
  borrowedMcNot asB (B ++ [a]) t ++ borrowedMcNot asA A a
    ++ borrowedMcNot asB (B ++ [a]) t ++ borrowedMcNot asA A a

/-- Unfolding of `splitMcNot` into its four `borrowedMcNot` blocks `W · V · W · V`. -/
theorem splitMcNot_eq (asA A asB B : List (Fin m)) (a t : Fin m) :
    splitMcNot asA A asB B a t
      = borrowedMcNot asB (B ++ [a]) t ++ borrowedMcNot asA A a
        ++ borrowedMcNot asB (B ++ [a]) t ++ borrowedMcNot asA A a := rfl

/-- **The `borrowedMcNot` preconditions for the `W`-block `B ++ [a]`.** From the atomic
hypotheses on the second control half `B`, its dirty ancillas `asB`, the borrowed wire `a`
(with `|B| = |asB| + 1`), and the target `t`, the snoc control list `B ++ [a]` (controls `B ∪ {a}`)
satisfies the four `borrowedMcNot` preconditions: `|B ++ [a]| = |asB| + 2`, `Nodup`, disjointness
from `asB`, and `t` outside it. Consumed by both `mcNotDenote_splitMcNot` and `splitMcNot_gate_mem`
(and by the assembly and `Evolution` lift, which re-derive the same `B ++ [a]`
facts). -/
theorem borrowedMcNot_snoc_hyps {asB B : List (Fin m)} {a t : Fin m}
    (hBlen : B.length = asB.length + 1) (hB : B.Nodup) (hBasB : B.Disjoint asB)
    (haB : a ∉ B) (haasB : a ∉ asB) (htB : t ∉ B) (hat : a ≠ t) :
    (B ++ [a]).length = asB.length + 2 ∧ (B ++ [a]).Nodup ∧
      (B ++ [a]).Disjoint asB ∧ t ∉ (B ++ [a]) := by
  refine ⟨?_, hB.append (List.nodup_singleton a) (List.disjoint_singleton.mpr haB), ?_, ?_⟩
  · rw [List.length_append, List.length_singleton]; omega
  · rw [List.disjoint_append_left]
    exact ⟨hBasB, List.singleton_disjoint.mpr haasB⟩
  · rw [List.mem_append, List.mem_singleton]
    exact fun h => h.elim htB fun h' => hat h'.symm

/-- **The one-borrowed-wire split is a genuine `Cᵐ(X)`** (Barenco Lemma 7.3). With `A` the first
control half (`|A| = |asA| + 2`, dirty ancillas `asA`), `B` the second (`|B| = |asB| + 1`, dirty
ancillas `asB`), target `t`, and one borrowed dirty wire `a` (outside `A`, `B`, `asB`, distinct
from `t`), the circuit `splitMcNot asA A asB B a t` acts on the bit-string `x` exactly as the
multiply-controlled `NOT` `mcNot (A.toFinset ∪ B.toFinset) t` — flipping only the target by the
full control AND and restoring every borrowed wire, with no dependence on any wire's dirty value.

Proof: each of the four `borrowedMcNot` blocks restores its own dirty ancillas
(`mcNotDenote_borrowedMcNot`), so the circuit denotes as the four-gate composition
`mcNot (insert a B) t ∘ mcNot A a ∘ mcNot (insert a B) t ∘ mcNot A a`, which is Barenco's halving
identity `mcNot_union_borrow` for the single borrowed wire `a`. -/
theorem mcNotDenote_splitMcNot (asA A asB B : List (Fin m)) (a t : Fin m)
    (hAlen : A.length = asA.length + 2) (hBlen : B.length = asB.length + 1)
    (hA : A.Nodup) (hasA : asA.Nodup) (hB : B.Nodup) (hasB : asB.Nodup)
    (hAasA : A.Disjoint asA) (hBasB : B.Disjoint asB)
    (haA : a ∉ A) (haasA : a ∉ asA) (haB : a ∉ B) (haasB : a ∉ asB)
    (htA : t ∉ A) (htB : t ∉ B) (htasB : t ∉ asB) (hat : a ≠ t)
    (x : Fin m → Fin 2) :
    mcNotDenote (splitMcNot asA A asB B a t) x = mcNot (A.toFinset ∪ B.toFinset) t x := by
  -- The `W`-block `borrowedMcNot asB (B ++ [a]) t` obligations, derived from the atomic hypotheses.
  obtain ⟨hWlen, hWnd, hWdisj, hWt⟩ := borrowedMcNot_snoc_hyps hBlen hB hBasB haB haasB htB hat
  -- The four blocks, each replaced by its net `mcNot` (dirty ancillas restored).
  have hV : ∀ y : Fin m → Fin 2, mcNotDenote (borrowedMcNot asA A a) y = mcNot A.toFinset a y :=
    fun y => mcNotDenote_borrowedMcNot asA A a hAlen hA hasA hAasA haA haasA y
  have hW : ∀ y : Fin m → Fin 2,
      mcNotDenote (borrowedMcNot asB (B ++ [a]) t) y = mcNot (B ++ [a]).toFinset t y :=
    fun y => mcNotDenote_borrowedMcNot asB (B ++ [a]) t hWlen hWnd hasB hWdisj hWt htasB y
  -- `(B ++ [a]).toFinset = insert a B.toFinset`.
  have hBa : (B ++ [a]).toFinset = insert a B.toFinset := by
    rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
      Finset.insert_eq, Finset.union_comm]
    simp
  -- The `mcNot_union_borrow` hypotheses, as `Finset` membership.
  have haA' : a ∉ A.toFinset := by rwa [List.mem_toFinset]
  have haB' : a ∉ B.toFinset := by rwa [List.mem_toFinset]
  have htA' : t ∉ A.toFinset := by rwa [List.mem_toFinset]
  have htB' : t ∉ B.toFinset := by rwa [List.mem_toFinset]
  rw [splitMcNot_eq]
  simp only [mcNotDenote_append, hV, hW, hBa]
  rw [mcNot_union_borrow A.toFinset B.toFinset haA' haB' hat htA' htB']
  simp only [Function.comp_apply]

/-- **Every gate of the one-borrowed-wire split is a `Toffoli`/`CNOT`/`NOT`** (`≤ 2` controls,
target not a control), inherited from the four `borrowedMcNot` cascades it concatenates. -/
theorem splitMcNot_gate_mem (asA A asB B : List (Fin m)) (a t : Fin m)
    (hAlen : A.length = asA.length + 2) (hBlen : B.length = asB.length + 1)
    (hA : A.Nodup) (hasA : asA.Nodup) (hB : B.Nodup) (hasB : asB.Nodup)
    (hAasA : A.Disjoint asA) (hBasB : B.Disjoint asB)
    (haA : a ∉ A) (haasA : a ∉ asA) (haB : a ∉ B) (haasB : a ∉ asB)
    (htB : t ∉ B) (htasB : t ∉ asB) (hat : a ≠ t) :
    ∀ g ∈ splitMcNot asA A asB B a t, g.1.card ≤ 2 ∧ g.2 ∉ g.1 := by
  obtain ⟨hWlen, hWnd, hWdisj, hWt⟩ := borrowedMcNot_snoc_hyps hBlen hB hBasB haB haasB htB hat
  have hVmem := borrowedMcNot_gate_mem asA A a hAlen hA hasA hAasA haA haasA
  have hWmem := borrowedMcNot_gate_mem asB (B ++ [a]) t hWlen hWnd hasB hWdisj hWt htasB
  intro g hg
  rw [splitMcNot_eq, List.mem_append, List.mem_append, List.mem_append] at hg
  rcases hg with (((h | h) | h) | h)
  · exact hWmem g h
  · exact hVmem g h
  · exact hWmem g h
  · exact hVmem g h

/-- **The one-borrowed-wire split is linear.** `splitMcNot asA A asB B a t` has at most
`8|asA| + 8|asB| + 4` gates — two copies each of the two `borrowedMcNot` cascades
(`≤ 4|asA| + 1` and `≤ 4|asB| + 1`). With `|asA| = |A| - 2` and `|asB| = |B| - 1` this is
`O(|A| + |B|) = O(m)` for `m = |A| + |B|` controls: four half-size cascades, `4 · O(m/2) = O(m)`. -/
theorem splitMcNot_length_le (asA A asB B : List (Fin m)) (a t : Fin m) :
    (splitMcNot asA A asB B a t).length ≤ 8 * asA.length + 8 * asB.length + 4 := by
  rw [splitMcNot_eq]
  simp only [List.length_append]
  have hV := borrowedMcNot_length_le asA A a
  have hW := borrowedMcNot_length_le asB (B ++ [a]) t
  omega

end AxQM.Concrete
