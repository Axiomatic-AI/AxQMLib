/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Concrete: the adaptive classical query (decision-tree) model

This is shared infrastructure for the classical query lower bounds of Nielsen & Chuang §6.3
(Exercise 6.14): "any classical counting algorithm ... must make `Ω(N)` oracle calls." To make
"any classical algorithm making at most `T` oracle calls" precise we use the standard
**decision-tree** model of classical query complexity.

A deterministic classical algorithm that consults a Boolean oracle `f : Fin N → Bool` is an
adaptive decision tree (`QueryTree N`): at each step it either stops and outputs a real estimate
(`leaf`) or it queries one index `i` and continues in a subtree chosen by the Boolean answer
(`node`). Running the tree against `f` (`eval`) yields the algorithm's output; the points it
actually consults along `f`'s path form `queried f`, whose size is bounded by the tree `depth`
(the worst-case number of oracle calls).

The key structural fact is **locality** (`eval_eq_of_agree`, `queried_eq_of_agree`): the algorithm's
behaviour depends only on the oracle's values at the points it queries. Two oracles that agree on
`queried f t` are indistinguishable to the algorithm — it takes the same path and returns the same
estimate. This is exactly what powers oracle lower bounds: an algorithm making few queries cannot
tell apart two oracles that differ only away from its (small) query set.
-/

namespace AxQM.Concrete

/-- An **adaptive classical decision tree** querying a Boolean oracle on `Fin N`: either stop and
output a real `estimate` (`leaf`), or query index `i` and continue in the subtree `branch b`
selected by the Boolean answer `b` (`node`). This is the standard model of a deterministic
classical algorithm making oracle calls. -/
inductive QueryTree (N : ℕ) : Type where
  | leaf (estimate : ℝ) : QueryTree N
  | node (i : Fin N) (branch : Bool → QueryTree N) : QueryTree N

namespace QueryTree

/-- The real estimate the algorithm outputs when run against the oracle `f`: follow the path
dictated by `f`'s answers to each query down to a leaf. -/
def eval {N : ℕ} (f : Fin N → Bool) : QueryTree N → ℝ
  | .leaf r => r
  | .node i br => eval f (br (f i))

/-- The set of indices the algorithm actually queries when run against the oracle `f` (the queries
along `f`'s path). -/
def queried {N : ℕ} (f : Fin N → Bool) : QueryTree N → Finset (Fin N)
  | .leaf _ => ∅
  | .node i br => insert i (queried f (br (f i)))

/-- The worst-case number of oracle calls the algorithm makes: the height of the decision tree. -/
def depth {N : ℕ} : QueryTree N → ℕ
  | .leaf _ => 0
  | .node _ br => max (depth (br false)) (depth (br true)) + 1

/-- **Locality of the query set.** If two oracles `f` and `g` agree on every index queried along
`f`'s path, then the algorithm queries exactly the same indices on `g` as on `f`. -/
lemma queried_eq_of_agree {N : ℕ} {f g : Fin N → Bool} :
    ∀ t : QueryTree N, (∀ x ∈ queried f t, g x = f x) → queried g t = queried f t
  | .leaf _, _ => rfl
  | .node i br, h => by
      have hi : g i = f i := h i (Finset.mem_insert_self _ _)
      have ih := queried_eq_of_agree (br (f i)) (fun x hx => h x (Finset.mem_insert_of_mem hx))
      simp only [queried, hi, ih]

/-- **Locality of the output.** If two oracles `f` and `g` agree on every index queried along `f`'s
path, then the algorithm returns the same estimate on `g` as on `f`. An algorithm cannot
distinguish two oracles that differ only off its query set. -/
lemma eval_eq_of_agree {N : ℕ} {f g : Fin N → Bool} :
    ∀ t : QueryTree N, (∀ x ∈ queried f t, g x = f x) → eval g t = eval f t
  | .leaf _, _ => rfl
  | .node i br, h => by
      have hi : g i = f i := h i (Finset.mem_insert_self _ _)
      have ih := eval_eq_of_agree (br (f i)) (fun x hx => h x (Finset.mem_insert_of_mem hx))
      simp only [eval, hi, ih]

/-- The number of indices queried along any path is at most the tree depth: an algorithm of depth
`T` makes at most `T` oracle calls. -/
lemma card_queried_le_depth {N : ℕ} (f : Fin N → Bool) :
    ∀ t : QueryTree N, (queried f t).card ≤ depth t
  | .leaf _ => by simp [queried, depth]
  | .node i br => by
      have ih := card_queried_le_depth f (br (f i))
      have h1 : (queried f (QueryTree.node i br)).card ≤ (queried f (br (f i))).card + 1 := by
        simpa [queried] using Finset.card_insert_le i (queried f (br (f i)))
      have h2 : depth (br (f i)) ≤ max (depth (br false)) (depth (br true)) := by
        cases f i
        · exact le_max_left _ _
        · exact le_max_right _ _
      have hd : depth (QueryTree.node i br) = max (depth (br false)) (depth (br true)) + 1 := rfl
      omega

end QueryTree

end AxQM.Concrete
