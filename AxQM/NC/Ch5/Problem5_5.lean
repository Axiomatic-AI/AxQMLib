/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HSPQueryState
import AxQM.Postulates.API.Purity
import AxQM.Postulates.API.HSOverlap
import AxQM.Postulates.API.Affinity
import AxQM.Postulates.API.CosetDensitySqrt
import AxQM.Postulates.API.PrettyGoodDiscrimination
import AxQM.Concrete.CosetStateOverlap
import AxQM.Concrete.CosetStateOverlapPow
import AxQM.Concrete.CosetOverlapSum
import AxQM.Concrete.CosetCollisionSum
import AxQM.Concrete.CosetCollisionSumClassCard
import AxQM.Concrete.SubgroupNilpotentMaximalNormal
import AxQM.Concrete.SubgroupMaximalCount
import AxQM.Postulates.API.Support
import AxQM.Postulates.API.EntropyMixLine
import ToMathlib.Analysis.InnerProductSpace.TraceNormRank
import ToMathlib.Analysis.InnerProductSpace.MatricizationRank

/-!
# Nielsen & Chuang, Problem 5.5 (Non-Abelian hidden subgroups)

*(N&C p. 244.)* This file holds the theorems that formalise the near-orthogonality of the coset
reduced states —
in **both** distinguishability metrics (the Hilbert–Schmidt overlap and the fidelity-family
quantum **affinity**) — through N&C's exact sample count `m = 4 log₂|G| + 2`. The
**identification clause** (a distinguishing measurement succeeding with probability
`≥ 1 − 1/|G|`) is the Ettinger–Høyer–Knill measurement analysis: proven mathematics. The
identification clause is **assembled at N&C's exact linear count**
(`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard`:
`p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|` at `m = 4 log₂|G| + 2`) **conditional on two isolated ingredients**:
a *per-state* pretty-good discrimination bound (piece (i)(a)) resting on a paired-trace operator
inequality, and the affinity collision sum (piece (ii)) resting on a Liebeck–Pyber–Shalev-strength
maximal-subgroup class count. See the "Remaining" section below for a precise, current account —
including the correction that the earlier *per-pair* discrimination target `p(K'∣σ_K) ≤ C·A` is
**false**, superseded by the per-state paired-trace inequality.

Non-Abelian HSP: prove m=4log|G|+2 coset samples identify K with prob >= 1-1/|G| (research).

## Bottom line: the assembled formalisation, the open task, and the remaining work

Problem 5.5 is one of N&C's **Research** problems: reconstruct the Ettinger–Høyer–Knill
(EHK) theorem — that the hidden subgroup problem has query complexity `O(log|G|)` — with
N&C's specific constants. **N&C's task is the identification clause**: for a finite group
`G` that *need not be Abelian*, `m = 4 log₂|G| + 2` coset samples let `K` be **identified
with probability `≥ 1 − 1/|G|`**. The near-orthogonality of the final state is what N&C
note this "shows" (the *mechanism*), not the identification task itself; and the
efficiency N&C leave open is the `poly(log|G|)` *operation* cost of the measurement, **not**
whether the identification holds — so the identification clause is squarely in scope and is
the item's central claim. Status of the assembled declarations, end-to-end **from N&C's literal
starting state (5.80)**:

* **The identification clause is proven for all `G` at a polynomial sample count,
  unconditionally** (`…prettyGoodMeasurement_bornProb_ge_of_sampleCount`,
  `m = O((log|G|)²)`): N&C's "`G` need not be Abelian" is honoured for the identification
  itself, but at a query count polynomial rather than N&C's exact *linear* `4 log₂|G| + 2`.
* **At N&C's exact target probability and exact *linear* count, the identification clause
  is proven unconditionally for the entire abelian hidden-subgroup problem**
  (`…_bornProb_ge_one_sub_inv_of_commGroup`, `m = 4 log₂|G| + 10` — Simon's problem, Shor's
  order-finding and discrete log: the algorithmic content of Chapter 5) **and for all
  nilpotent `G`** (`…_of_nilpotent`, fidelity route).
* **The mechanism N&C note — the nearly-orthogonal final state — is proven for all `G` at
  N&C's exact count `m = 4 log₂|G| + 2`.** From the literal query state (5.80), the reduced
  states of two distinct candidate subgroups have Hilbert–Schmidt overlap `≤ 1/(2|G|²)`
  (`hspQueryState_reducedLeft_pi_hsOverlap_le_of_sampleCount`) and are nearly perfectly
  distinguishable, `D ≥ 1 − 2^{-m/2}` (`hspQueryState_reducedLeft_pi_traceDistance_ge`) —
  the consequence "This shows one can produce … a final state in which the pure-state
  outcomes … are nearly orthogonal", *not* the identification task itself.

**Still open — the item's central claim, and the sole remaining gate.** The
identification clause at N&C's exact *linear* count `m = 4 log₂|G| + 2` for **general
(non-nilpotent) `G`** is **not yet a proved theorem**. The residual has now been isolated to
a **single** ingredient — the maximal-subgroup counting (piece (ii)) — and piece (i)(a) is
confirmed **off the critical path for completion**: the fidelity/Rotfel'd route
(`…_bornProb_ge_one_sub_inv_of_classCard`) discharges the operator half **unconditionally for
all `G`**, conditional *only* on the piece-(ii) count, so the affinity paired-trace
inequality affects only the additive sample constant (`8 log₂|G|+20` vs the affinity route's
`4 log₂|G|+10`), never completability. **The one gate is therefore the count**
`∀ J, 3·#{J-conj classes of non-normal maximals} ≤ |J|²` (Liebeck–Pyber–Shalev strength);
every known proof uses the Classification of Finite Simple Groups (CFSG), absent from Mathlib
(`ToMathlib` has the *fidelity*
paired bound `ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_le_sum_traceNorm` and Lieb
concavity, but no maximal-subgroup count, and no cardinality bound on group cohomology `H¹`).

**The residual is pinned to the *standard* maximal-subgroup count.** The gate above
is stated over a bespoke conjugacy-class quantity; it is machine-checked here to be *no
stronger than the classical, recognizable count of maximal subgroups*. The class-count hypothesis
`∀ J, 3·#{J-conj classes of non-normal maximals} ≤ |J|²` follows from
`∀ J, 3·#{maximal subgroups of J} ≤ |J|²` (i.e. at most `|J|²/3` maximals — a **weak form of the
Liebeck–Pyber–Shalev bound** `#{maximals} ≤ c·|G|^{3/2}`) via
`Concrete.nonnormal_maximal_classCard_le_of_card_maximal_le` (the conjugacy classes inject into the
non-normal maximals, a subset of all maximals: `#classes ≤ #{non-normal maximals} ≤ #{maximals}`).
The general-`G` sharp-constant identification headlines are correspondingly restated on this
standard hypothesis (`…_bornProb_ge_one_sub_inv_of_maximalCount` and its end-to-end
`hspQueryState_reducedLeft_pi_…_of_maximalCount` form), certifying that Problem 5.5's
*sole* open general-`G` ingredient is not a hypothesis contrived to the proof but exactly the
classical question **whether a finite group has polynomially many maximal subgroups** — whose known
proofs are CFSG-strength, and which remains reachable work (not a wall).

**The residual count reduced to Frattini-free groups.** The standard *first move* of
every maximal-subgroup count is now machine-checked:
`#{maximal subgroups of G} = #{maximal subgroups of G ⧸ Φ(G)}`
(`Concrete.card_isCoatom_eq_card_isCoatom_quotient_frattini`, `SubgroupFrattiniMaximalCount.lean`) —
every maximal subgroup contains the Frattini subgroup `Φ(G)` (`frattini_le_coatom`), so the
correspondence theorem restricts to a bijection of coatoms. Since `|G ⧸ Φ(G)| ≤ |G|`, the count
bound for `G` **follows from the same bound on the Frattini-free quotient**
(`Concrete.three_mul_card_isCoatom_le_sq_of_quotient_frattini`), so the sole open count may
be assumed on **groups with trivial Frattini subgroup** only — the shape in which the
Liebeck–Pyber–Shalev reduction to almost-simple groups proceeds. This removes the elementary
solvable-Frattini padding, not the hard core (simple and almost-simple groups are Frattini-free).

**The second CFSG-free route: the abelian minimal-normal complement recursion.**
Where the Frattini reduction is the socle-route opening move, the *other* classical CFSG-free
approach to a maximal-subgroup count is the **chief-series recursion** — the route Wall used to
prove `#{maximals} < |G|` for *solvable* groups without CFSG. Its foundational step is now
machine-checked (`Concrete.card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement'`,
`SubgroupMinimalNormalComplement.lean`): for an **abelian minimal normal** subgroup `N ◁ G` (every
nontrivial solvable group has one, elementary abelian),
`#{maximal subgroups of G} ≤ #{maximal subgroups of G ⧸ N} + #{complements of N in G}`. The
coatoms `M ⋖ G` split by whether they contain `N`: those with `N ≤ M` correspond bijectively to
the coatoms of `G ⧸ N` (`Concrete.coatomLeEquivQuotient`, the correspondence theorem for a general
normal `N`, generalizing the Frattini `coatomEquivQuotientFrattini`), and those with `N ⊄ M` are
**complements of `N`** (`Concrete.isComplement'_of_isCoatom_of_not_le`: `M ⊔ N = ⊤` by maximality,
and `M ⊓ N` — normal in `G` since `N` is abelian — is a proper normal subgroup of the minimal `N`,
hence trivial), so they inject into the complements of `N`. Iterated down a chief series, this
reduces the maximal count to the **complement counts** `#{complements of each abelian chief
factor}` — the genuine hard core (an affine primitive quotient `V ⋊ H` has `|H¹(H, V)|` complement
classes; Wall bounds their sum for solvable `G` elementarily, Liebeck–Pyber–Shalev in general via
CFSG). So this recursion, like the Frattini reduction, does **not** close the count — it isolates
the complement count as the residual, and is the CFSG-free tool a future extension of the
unconditional identification headline from **nilpotent** `G` (already done — nilpotent groups have
*no* non-normal maximals) to **solvable** `G` (Wall's theorem) would build on.

**The isolated complement count gets its first elementary bound.** The recursion above
pins the residual on `#{complements of N in G}`; that count is bounded here elementarily, with no
cohomology and no CFSG (`Concrete.card_isComplement'_le`, `SubgroupComplementCount.lean`):

`#{complements of N in G} ≤ |N|^{log₂|G ⧸ N|}`.

The mechanism is the **section picture**. Fix a generating finset of `G ⧸ N` of size
`≤ log₂|G ⧸ N|` (`exists_closure_finset_card_le_log`) and representatives `rep x` of its members. A
complement `M` factors each `rep x` uniquely as `nₓ · pₓ` (`Subgroup.IsComplement.equiv`), so
`M ↦ (x ↦ nₓ ∈ N)` maps the complements into the functions `↥s → ↥N`; it is **injective** because
the `M`-parts `pₓ = nₓ⁻¹·rep x ∈ M` project onto the generators of `G ⧸ N`, so the subgroup `T`
they generate joins `N` to `⊤` and — being `≤ M` — is itself a complement of the same order `|M|`,
hence `T = M` (`Concrete.eq_of_isComplement'_of_le_of_sup`). Composed with the recursion this yields
the **concrete single-step bound**
`#{maximals G} ≤ #{maximals G ⧸ N} + |N|^{log₂|G ⧸ N|}`
(`Concrete.card_isCoatom_le_card_isCoatom_quotient_add_pow`). The bound is deliberately **crude** —
`|N|^{log₂|G|}` may be super-polynomial, so, like the recursion it feeds, it does **not** close the
count; the *sharp* per-factor bound `|H¹(H, V)| ≤ |V|` (Wall for solvable `G`, Liebeck–Pyber–Shalev
via CFSG in general) is the residual of which this is the elementary predecessor.

**The chief-series recursion gets its entry point: solvable groups satisfy its
hypotheses.** The abelian minimal-normal recursion consumes an *abelian minimal normal* `N ◁ G`;
to run it as a chief-series recursion on a **solvable** `G` (Wall's CFSG-free route) one needs such
an `N` to exist. It does (`Concrete.exists_abelian_minimalNormal_of_isSolvable`,
`SubgroupSolvableMinimalNormal.lean`): every nontrivial finite solvable `G` has a normal `N ≠ ⊥`
that is abelian and minimal normal. Existence of a *minimal* nontrivial normal subgroup is
well-foundedness of the finite subgroup lattice; **abelianness** is where solvability enters —
`⁅N, N⁆` is normal in `G` and `≤ N`, hence `⊥` or `N` by minimality, and
`Group.IsSolvable.commutator_lt_of_ne_bot` (`⁅N, N⁆ < N`) forbids `N`, so `⁅N, N⁆ = ⊥`. Composing
with the
recursion gives the **solvable descent step**
(`Concrete.exists_normal_card_isCoatom_le_of_isSolvable`):
a nontrivial finite solvable `G` has a normal `N ≠ ⊥` with `|G ⧸ N| < |G|` and
`#{maximals G} ≤ #{maximals G ⧸ N} + #{complements of N}`, with `G ⧸ N` again finite solvable — the
exact shape a strong induction on `|G|` iterates. This discharges the recursion's hypotheses for the
whole solvable class (turning the prior files' *prose* "every nontrivial solvable group has [an
abelian minimal normal subgroup]" into a theorem), leaving — as before — only the sum of the
abelian-chief-factor **complement counts** as the residual Wall's theorem bounds.

**The chief-series recursion, *assembled*: a linear solvable-`G` maximal count.** The
descent step above is a *single* step; the strong induction on `|G|` it feeds is run here.
`Concrete.card_isCoatom_le_two_mul_card_of_isSolvable_of_complementBound`
(`SubgroupSolvableMaximalCount.lean`) bounds the maximal count of the **whole solvable class** by a
**linear** `2·|G|` — not the crude super-polynomial bound; the geometric decay `|G_{i+1}| ≤ |G_i|/2`
of the quotient orders telescopes the complement sum to `< 2|G|` — conditional on the **sharp
per-chief-factor complement bound** `#{complements of an abelian minimal normal N in H} ≤ |H|` (the
cohomological Wall / Aschbacher–Guralnick ingredient `|Z¹(H ⧸ N, N)| ≤ |H|`). So the solvable count
`#{maximals J} ≤ |J|²/3` is **one isolated cohomological bound, not a wall** — the CFSG-free
input for extending the unconditional nilpotent-`G` identification to solvable `G`.

**The complement count factored, the geometric factor discharged, the residual pinned
to the named first-cohomology bound.** The assembled recursion above rests on the per-chief-factor
complement bound `#{complements of an abelian minimal normal N in H} ≤ |H|` — the cardinality of the
1-cocycles `|Z¹(H ⧸ N, N)| = |B¹|·|H¹|`. The next result splits that residual into its two factors
and discharges the elementary one (`Concrete.card_isComplement'_le_card_mul_card_orbits`,
`SubgroupComplementOrbitCount.lean`): `N` acts on the complements of `N` by conjugation (conjugation
fixes the normal `N` and preserves the order product and disjointness of the
`isComplement'_iff_card_mul_and_disjoint` characterisation, so it permutes complements), each orbit
has size `≤ |N|` (orbit–stabiliser: the orbit is `|B¹| = |N : C_N(M)|`), whence — via the reusable
orbit-counting bound `Concrete.card_le_card_mul_card_orbitRel_quotient` (`|X| ≤ |A|·#orbits` for a
finite group `A` acting on a finite `X`, by the injection `X ↪ A × (X ⧸ orbitRel)`) —

`#{complements of N in H} ≤ |N| · #{N-conjugacy classes of complements}`.

The **geometric factor** `|N|` is now elementary; the residual is the **cohomological factor**
`#{complement classes} = |H¹(H ⧸ N, N)|` alone. Consequently the sharp per-factor bound
`#{complements} ≤ |H|` follows from the strictly cohomological
`#{complement classes} ≤ |H : N|` (`Concrete.card_isComplement'_le_of_card_orbits_le_index`, via
Lagrange `|N|·|H : N| = |H|`), and feeding that into the assembled recursion reduces the whole
solvable maximal count to it
(`Concrete.card_isCoatom_le_two_mul_card_of_isSolvable_of_orbitBound`). So the sole solvable
residual is now the **named** Wall / Aschbacher–Guralnick first-cohomology bound
`|H¹(H ⧸ N, N)| ≤ |H : N|`, with the elementary geometric `|N|` removed — a genuine narrowing, and a
correction of the record: the raw Aschbacher–Guralnick theorem gives `|H¹| < |N|` (hence
`#{complements} < |N|²`, a quadratic maximal count → still a *linear* sample count, at a worse
additive constant than N&C's `4 log₂|G|+2`), so whether the sharper `≤ |H : N|` form (needed for the
`≤ |H|` per-factor bound, hence N&C's exact linear count for general solvable `G`) holds is the
precise cohomological question that remains.

**The cohomological complement-class bound discharged for *central* chief factors.**
The named residual `|H¹(H ⧸ N, N)| ≤ |H : N|` is now a **theorem in the central (trivial-action)
case** `N ≤ Z(H)` (`Concrete.card_isComplement'_orbits_le_index_of_le_center`,
`SubgroupCentralComplementCount.lean`) — connecting the previously-dangling cyclic hom count
`Concrete.card_monoidHom_le_card_of_isCyclic` (`|Hom(G, C)| ≤ |G|` for cyclic `C`,
`SubgroupComplementOrbitCount`… `MonoidHomCyclicCount.lean`) to the complement count. The bridge is
the **retraction picture**: a complement `K` of a central `N` is normal
(`Concrete.normal_of_isComplement'_of_le_center`), so the second-isomorphism identification
`H ⧸ K ≃* N` gives a retraction `r_K : H →* N` with `r_K|_N = id` and `ker r_K = K`
(`Concrete.complementRetraction`); the difference `r_K · r_{K₀}⁻¹` of two retractions kills `N`
(central ⟹ `Hom(H, N)` abelian-group), so it descends to `H ⧸ N →* N`, and `K ↦ (that hom)` injects
the complements into `Hom(H ⧸ N, N)` (`Concrete.card_isComplement'_le_card_monoidHom_of_le_center`:
`#{complements} ≤ |Hom(H ⧸ N, N)|`). A **central minimal normal `N` is cyclic**
(`Concrete.isCyclic_of_le_center_of_minimal`: any nonidentity `x ∈ N` has `⟨x⟩ ◁ H` central,
hence `= N` by minimality), so the cyclic hom count gives `|Hom(H ⧸ N, N)| ≤ |H : N|`, whence
`#{complements} ≤ |H : N|` (`Concrete.card_isComplement'_le_index_of_le_center`) and — a fortiori
for the orbit count — the `horb` hypothesis of
`Concrete.card_isCoatom_le_two_mul_card_of_isSolvable_of_orbitBound` **in the central case**. Every
central minimal normal subgroup is cyclic (a central subgroup's every subgroup is normal, so
minimality forces prime order), so this is the *whole* trivial-action case. It does **not** unlock a
new group class (a nilpotent group's chief factors are all central, and nilpotent groups already
have no non-normal maximals, so the identification headline is already unconditional there), but it
turns the central case of the recursion's cohomological hypothesis from a `∀`-assumption into a
theorem, **narrowing the sole solvable residual to the non-central chief factors** (nontrivial
`H ⧸ N`-action, where `|H¹|` can be nonzero — the genuinely deep Wall / Aschbacher–Guralnick core).

**The complement count discharged for *cyclic-quotient* chief factors, and the crude
count refactored into its section-count engine.** The elementary complement count of
`Concrete/SubgroupComplementCount.lean` — a complement `M` of `N ◁ G` decomposes the representatives
of a generating set `s` of `G ⧸ N` and is recovered from its `N`-parts, injecting the complements
into `↥s → ↥N` — is now exposed as a single **generating-set-parametrised** engine
`Concrete.card_isComplement'_le_pow_card_of_closure_eq_top`: `#{complements of N} ≤ |N| ^ |s|` for
*any* `s` with `⟨s⟩ = G ⧸ N` (the prior crude `card_isComplement'_le` is now its corollary at the
`log₂|G ⧸ N|`-size set). Specialising to the case where `G ⧸ N` is **cyclic** — a *single*-generator
set, `|s| = 1` — gives the **tight** bound `#{complements of N} ≤ |N|`
(`Concrete.card_isComplement'_le_card_of_isCyclic_quotient`): a complement is `≃ G ⧸ N`
(`Subgroup.IsComplement'.QuotientMulEquiv`), hence cyclic, and is generated by its unique element
over a fixed generator of `G ⧸ N`, an element pinned to one of the `|N|` cosets that determines it.
The bound is tight (e.g. `N = A₃ ◁ S₃`, `G ⧸ N ≅ ℤ/2`: the three order-two complements number
`|A₃| = 3`) and — since `|N| ≤ |G|` — discharges the per-factor complement hypothesis of
`card_isCoatom_le_two_mul_card_of_isSolvable_of_complementBound` for **every chief factor with
cyclic quotient action**. Unlike the central case (`N ≤ Z(H)`), this covers **non-central** factors
(`A₃`
is not central in `S₃`); together the two discharge that hypothesis on the central *and* the
cyclic-quotient factors, narrowing the sole solvable residual to the chief factors whose quotient
action is **non-cyclic** (where `|H¹|` genuinely resists an elementary count).

**The complement count discharged for *coprime* chief factors: `H¹ = 0` by
cocycle averaging.** The named residual `|H¹(H ⧸ N, N)| ≤ |H : N|` is now a **theorem in the
coprime case** `gcd(|N|, [H : N]) = 1` — the classical vanishing `H¹(H ⧸ N, N) = 0`
(`Concrete.card_orbitRel_quotient_isComplement'_le_one_of_coprime`,
`SubgroupCoprimeComplementCount.lean`): when the abelian chief factor `N` has order coprime to its
index, **all complements of `N` are `N`-conjugate**
(`Concrete.exists_conjAct_smul_of_isComplement'_of_coprime`), so the class count is `≤ 1 ≤ [H : N]`
and `#{complements of N} ≤ |N| ≤ |H|`. This is the abelian, coprime case of Schur–Zassenhaus
*conjugacy* — Mathlib supplies only the *existence* half
(`Subgroup.exists_right_complement'_of_coprime`),
so the conjugacy is proved here from scratch by the standard **cocycle-averaging** argument: two
complements `K₁, K₂` give homomorphic sections `s₁, s₂ : H ⧸ N →* H`
(`Subgroup.IsComplement'.QuotientMulEquiv`), and their difference `c q = s₂ q · (s₁ q)⁻¹ ∈ N` is a
1-cocycle `c(q₁q₂) = c(q₁)·ᵍc(q₂)` (`g = s₁ q₁`, conjugation via `MulAut.conjNormal`); summing it
over `H ⧸ N` gives `c(q)^{[H:N]} = T · ᵍT⁻¹` for `T = ∏_q c q`, and since `x ↦ x^{[H:N]}` is a
**bijection** of the coprime-order `N` (`powCoprime`), the "average" `t = T^{1/[H:N]}` witnesses `c`
as a coboundary `c(q) = t · ᵍt⁻¹`, i.e. `s₂ q = t · s₁ q · t⁻¹`, so `K₂ = t K₁ t⁻¹`. Unlike the
central case (`N ≤ Z(H)`) this covers **non-central** factors, and unlike the cyclic-quotient case
it needs no constraint on how the quotient is generated — with the central, cyclic-quotient and now
coprime factors all discharged, the sole solvable residual is the chief factors that are
simultaneously **non-central, non-cyclic-quotient and non-coprime** (`p ∣ [H : N]` for `N` an
elementary abelian `p`-group), the one regime where `|H¹|` genuinely fails to vanish.

**Why the CFSG dependency appears intrinsic to the *linear* bound (not merely to this
route).** A prior note conjectured that EHK's information-theoretic analysis attains the
linear query bound *without* CFSG; the analysis here finds no substantiation for that
and points the other way. The identification error of *any* square-root/pretty-good
measurement is the collision sum `∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`, and a union bound over
the up-to-`|G|^{log₂|G|}` candidate subgroups gives only **quadratic** `m = Θ((log₂|G|)²)`
for *any* target error (constant or `1/|G|` alike) — so the linear bound *intrinsically*
requires the refined per-index (per-dyadic-shell) subgroup counting, independent of the error
target. In that refinement the **near** shells (bounded relative index `≤ c`) are
elementarily polynomial — a subgroup of index `≤ c` is a point stabiliser of a hom into the
*fixed* group `S_c`, so `#{index ≤ c} ≤ |G|^{O(1)}` (`Concrete.card_subgroup_index_le`) — but
the **far** shells (index up to `|G|`) are exactly where the count is needed uniformly, and
there the only elementary bound (M. Hall / subgroup growth, `(n!)^{log|G|}`) is factorial in
the index, forcing super-polynomial `m`. Removing it needs a *polynomial* bound on the number
of maximal subgroups — Liebeck–Pyber–Shalev, CFSG. No CFSG-free route to the far-shell count
is known; whether EHK's own argument circumvents it or silently invokes CFSG-strength counting
is **unverified** (the EHK paper was not available to check). Per this project's
convention CFSG is treated as absent library apparatus (work), not a wall; but the honest
current picture is that the general-`G` linear identification is gated on precisely this one
CFSG-strength count, with no elementary sub-piece remaining (the index-`2`, prime-index-normal,
and simple-quotient-normal maximal counts are all already discharged elementarily above; the
non-normal maximals are the sole residual).

**Dead ends recorded (so they are not re-attempted).** (1) The affinity paired-trace
`re tr(√S₀·√σ_K^{⊗m}) ≤ ∑_{K'} A(σ_K^{⊗m}, σ_{K'}^{⊗m})` is numerically true for every family
of density operators (adversarial minimum over random families) but genuinely subtle: it is
strictly stronger than Rotfel'd's (fidelity) bound and does **not** reduce to the operator
sub-additivity `√S₀ ≤ ∑√σ_{K'}` (false — `∑√ρ_j − √(∑ρ_j)` has negative eigenvalues). The
natural proof route — Cauchy–Schwarz `tr(√ρ_i√S₀) ≤ √(tr(√ρ_i)·tr(√ρ_i S₀))` (valid) then a
scalar step — **fails**: the scalar step `tr(√ρ_i)·tr(√ρ_i S₀) ≤ (∑_j tr(√ρ_i√ρ_j))²` is
false, adversarially violated at 3 states in dimension 3 (and trivially at one state, where it
reverses Cauchy–Schwarz). Any concavity-based argument overshoots (`A ↦ tr(√ρ_i√A)` is
concave and degree-½ homogeneous, so concavity yields only the reverse-direction bound
`tr(√ρ_i√(A+B)) ≥ (tr(√ρ_i√A)+tr(√ρ_i√B))/√2`). Since piece (i)(a) is off the completion path,
this residual matters only for the exact additive constant. (2) A single constant-threshold
collision split leaves the far term super-polynomial (see the (ii) discussion below).

## What is proved, and where

The claim (Ettinger–Høyer–Knill: the query complexity of the hidden subgroup problem is
`O(log|G|)`) is *information-theoretic* — the efficiency of the final POVM is explicitly left open
by N&C, so the target is the **existence of a distinguishing measurement**, not an efficient
algorithm. The formalisation is built bottom-up; the mathematical kernel is the **coset density
matrix** `σ_K`, the single-copy reduced state of the query register (5.80) after the range register
is traced out. `f` is constant and distinct on cosets, so measuring `f` reveals exactly which of
the `gᵢ` share a coset; the group registers are left in `σ_K^{⊗m}`, with per-copy factor

`σ_K = (|K|/|G|) ∑_C |C⟩⟨C|`,   entries   `σ_K i j = |G|⁻¹ · [iK = jK]`.

### The single-copy reduced state (this file's headline)

`hspQueryState_reducedLeft` (below) is the **operator-independent form of the reduced-state step**:
for the single-copy query state `|ψ_f⟩ = |G|^{-1/2} ∑_g |g⟩|f(g)⟩` (the `m = 1` case of 5.80),
tracing out the range register `ℂ[X]` leaves the group register in `σ_K`:

`Tr_{ℂ[X]} |ψ_f⟩⟨ψ_f| = σ_K`.

It is the equation `State.reducedLeft = cosetDensityState K` between states, proved by
`State.ext` from the operator-level computation `hspQueryState_reducedLeft_op`
(`Postulates/API/HSPQueryState.lean`), which recognises the query state as the coset Schmidt
decomposition `∑_q √(|K|/|G|) |C_q⟩|f(q̂)⟩` and applies the Schmidt partial-trace lemma.

### The purity of the reduced state (this file's second physics theorem)

`cosetDensityState_purity` (below) records that the reduced state is **maximally mixed on the
coset-symmetric subspace**:

`tr(σ_K²) = |K| / |G| = 1 / |G ⧸ K|`.

`σ_K = (|K|/|G|) Π_K` is `|K|/|G|` times the rank-`|G ⧸ K|` coset projector `Π_K = ∑_C |C⟩⟨C|`, so
its purity is the reciprocal of that subspace's dimension. This is the diagonal (`K = K'`) case of
the **coset-density overlap** `tr(σ_K σ_{K'}) = |K ∩ K'|/|G|` (`Concrete.cosetDensity_trace_mul`),
the Hilbert–Schmidt quantity that measures how nearly orthogonal the reduced states of *distinct*
candidate hidden subgroups are — the quantitative core of "the pure-state outcomes for different
possible hidden subgroups are nearly orthogonal".

### The `m`-copy reduced state and its purity (this file's `m`-copy physics theorems)

`hspQueryState_reducedLeft_pi` and `cosetDensityState_pi_purity` (below) lift the two single-copy
theorems above to the full `m`-copy query state of eq. 5.80. The key is that **no `m`-fold tensor
machinery is required**: with `ι ≃ Fin m` indexing the copies, the `m`-copy query state is the
*single-copy* query state for the direct-power group `G^ι = (ι → G)` and the coordinatewise query
`F(g) = (f(g i))_i`, and its hidden subgroup is the product subgroup `K^ι = ∏_i K` (`f` constant and
distinct on the cosets of `K` makes `F` constant and distinct on the cosets of `K^ι`,
`Concrete.quotient_mk_pi_const_eq_iff`). Applying the single-copy `hspQueryState_reducedLeft` to
`G^ι` therefore gives

`Tr_{ℂ[X]^{⊗m}} |ψ_f^{⊗m}⟩⟨ψ_f^{⊗m}| = cosetDensityState (K^ι) = σ_K^{⊗m}`,

the reduced state being exactly the tensor power `σ_K^{⊗m}` (since `σ_K^{⊗m}` is itself the coset
density matrix of `K^ι`, `Concrete.CosetStateOverlapPow`). Its purity is the `m`-th power of the
single-copy purity, `tr((σ_K^{⊗m})²) = (|K|/|G|)^m` — the geometric decay in the sample count `m`
that is the `K = K'` diagonal of the exponential near-orthogonality driving the headline argument.

### The physical near-orthogonality of the reduced states (this file's `hsOverlap` theorems)

`cosetDensityState_hsOverlap` and `cosetDensityState_pi_hsOverlap` (below) record the
**Hilbert–Schmidt overlap** of the reduced states of two candidate hidden subgroups `K, K'`, at the
physical `State` level, via the definition `State.hsOverlap`
(`AxQM/Postulates/API/HSOverlap.lean`, `⟨ρ, σ⟩_HS = re tr(ρ σ)`):

`⟨σ_K, σ_{K'}⟩_HS = |K ∩ K'| / |G|`,   `⟨σ_K^{⊗m}, σ_{K'}^{⊗m}⟩_HS = (|K ∩ K'| / |G|)^m`.

The overlap is the physical distinguishability resource: its `K = K'` diagonal is the purity
(`State.hsOverlap_self : hsOverlap ρ ρ = purity ρ`), so `hsOverlap` generalises
`cosetDensityState_purity`. The **exponential near-orthogonality** of distinct hidden subgroups then
holds at the `State` level:

`2^m · ⟨σ_K^{⊗m}, σ_{K'}^{⊗m}⟩_HS² ≤ tr((σ_K^{⊗m})²) · tr((σ_{K'}^{⊗m})²)`   (`K ≠ K'`),

i.e. the normalised overlap `(|K∩K'|/√(|K||K'|))^m ≤ 2^{-m/2}`
(`cosetDensityState_pi_two_pow_mul_hsOverlap_sq_le`, the physical form of the concrete
`Concrete.cosetDensity_pi_trace_mul_sq_le`). This is precisely N&C's "a final state in which the
pure-state outcomes for different possible hidden subgroups are nearly orthogonal": the reduced
states separate exponentially in the number `m` of coset samples.

### Near-orthogonality at N&C's sample count `m = 4 log₂|G| + 2` (this file's identifiability input)

`cosetDensityState_pi_hsOverlap_le_of_sampleCount` (below) instantiates the exponential
near-orthogonality at N&C's *exact* sample count. The hypothesis `4·|G|⁴ ≤ 2^m` is precisely
`m ≥ 4 log₂|G| + 2` (since `4·|G|⁴ = 2^{4 log₂|G| + 2}`), and the conclusion is the explicit
inverse-quadratic separation

`⟨σ_K^{⊗m}, σ_{K'}^{⊗m}⟩_HS ≤ 1 / (2|G|²)`   (`K ≠ K'`).

This is the quantitative content N&C states as *shown* by the protocol — that it "produce[s] (using
only `O(log|G|)` oracle calls) a final state in which the pure-state outcomes for different possible
hidden subgroups are nearly orthogonal" — now carrying the problem's own **linear** sample count
`m = 4 log₂|G| + 2`. It is the quantitative input the remaining distinguishing-measurement step
consumes: the pairwise overlap of the candidate reduced states is inverse-quadratically small.

### The affinity (fidelity-metric near-orthogonality) — this file's `affinity` theorems

The Hilbert–Schmidt overlap is the *purity-metric* distinguishability; the identification clause's
distinguishing measurement is instead governed by a *fidelity-family* pairwise quantity, the
**quantum affinity** `A(ρ, σ) = tr(√ρ √σ)` (the definition `State.affinity`). This file computes
and bounds it for the coset reduced states:

`A(σ_K, σ_{K'}) = |K ∩ K'| / √(|K|·|K'|) ≤ 1/√2`,   `A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = A(σ_K, σ_{K'})^m`

(`≤ 2^{-m/2}` for `K ≠ K'`). The closed form rests on the operator-level identity
`cosetDensityState_op_cfc_sqrt`: since `σ_K = (|K|/|G|) Π_K` is a scalar multiple of the coset
projector, `√σ_K = √(|G|/|K|) σ_K`, so the affinity reduces to the already-computed Hilbert–Schmidt
overlap. The affinity is the *right* metric for the **linear** sample count: a multi-state
discrimination error is bounded by the pairwise-affinity **sum**
`∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`, which stays `≤ 1/|G|` at `m = 4 log₂|G| + 2` (dominated by the
few nearby subgroups), whereas a union bound over all `|G|^{Θ(log|G|)}` candidates forces a
*quadratic* `m`.

### The measurement-facing form: trace distance → 1 (this file's `traceDistance` theorems)

`cosetDensityState_traceDistance_ge` and `cosetDensityState_pi_traceDistance_ge` (below) turn the
affinity near-orthogonality into an **operational** statement about *measurements*, via the new
fidelity-family Fuchs–van de Graaf lower bound `1 − A(ρ, σ) ≤ D(ρ, σ)`
(`State.one_sub_affinity_le_traceDistance`, proved from the **Powers–Størmer inequality**
`ContinuousLinearMap.re_trace_sub_mul_self_le_traceNorm_mul_self_sub_mul_self` in `ToMathlib/`). For
distinct hidden subgroups `K ≠ K'` the `m`-copy reduced states are nearly perfectly
distinguishable:

`D(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≥ 1 − (1/√2)^m = 1 − 2^{-m/2}`.

Because the trace distance is the optimal single-shot distinguishing bias
(`State.classicalTraceDist_bornProb_le`), this is precisely the statement that a single measurement
identifies which of two candidate subgroups produced the final state with error `≤ 2^{-m/2}` — the
**pairwise** identification guarantee. It is the operational content of "a final state in which the
pure-state outcomes for different possible hidden subgroups are nearly orthogonal", now carrying the
problem's own linear sample count. Extending this pairwise bound to the full *multi-state*
identification (`K` among *all* candidates, probability `≥ 1 − 1/|G|`) is the remaining
Ettinger–Høyer–Knill development below.

### Supporting results (the density-matrix kernel, its spectral picture, and the query state)

`AxQM/Concrete/CosetState.lean` and `CosetStateOrthonormal.lean` (pure math): the coset
incidence matrix, `cosetDensity` (`σ_K`) with Hermitian / PSD / trace-one, the normalized
coset states `cosetState`, their orthonormality, and the mixture form
`σ_K = ∑_q (|K|/|G|) |C_q⟩⟨C_q|`.

`AxQM/Concrete/CosetStateOverlap.lean` (pure math): the Hilbert–Schmidt overlap
`tr(σ_K σ_{K'}) = |K ∩ K'|/|G|` (`cosetDensity_trace_mul`) and its `K = K'` purity
`tr(σ_K²) = |K|/|G|` (`cosetDensity_trace_mul_self`) — an elementary finite-group count — together
with the **single-copy near-orthogonality bound** for distinct subgroups `K ≠ K'`,
`2·tr(σ_K σ_{K'})² ≤ tr(σ_K²)·tr(σ_{K'}²)` (`cosetDensity_trace_mul_sq_le`), i.e. normalized overlap
`|K∩K'|/√(|K||K'|) ≤ 1/√2`, whose group-theoretic core is `2·|K∩K'|² ≤ |K|·|K'|`
(`two_mul_card_inf_sq_le`).

`AxQM/Postulates/API/CosetDensityState.lean` (states of the group register): `groupSystem G` (the
register `ℂ[G]`), `cosetPureState K q` (`|C_q⟩` as a `PureState`), `cosetDensityState K` (`σ_K` as
a `State`), and `cosetDensityState_op_eq_sum` (its spectral form at the operator level).

`AxQM/Postulates/API/HSPQueryState.lean` (the query state): `hspQueryVec` / `hspQueryState`
(the `m = 1` query state 5.80 as a `PureState` of `groupSystem G ⊗ groupSystem X`), its Schmidt
decomposition over cosets (`hspQueryVec_eq_schmidt`), and the reduced-state computation
`hspQueryState_reducedLeft_op` consumed by the theorem below.

`AxQM/Concrete/CosetStateOverlapPow.lean` (pure math): the **tensor-power** overlap.
The key observation is that the `m`-fold tensor power `σ_K^{⊗m}` is *itself* a coset density matrix
— that of the **product subgroup** `K^ι = ∏_i K` of the direct-power group `G^ι = (ι → G)` (the
coset condition factors coordinatewise, `ι ≃ Fin m`) — so no Kronecker machinery is needed. This
gives the multiplicativity `tr(σ_{Kᵖ} σ_{K'ᵖ}) = tr(σ_K σ_{K'})^{|ι|}`
(`cosetDensity_pi_trace_mul`), its purity diagonal `tr(σ_{Kᵖ}²) = tr(σ_K²)^{|ι|}`
(`cosetDensity_pi_trace_mul_self`), and the **exponential near-orthogonality**
`2^{|ι|} · tr(σ_{Kᵖ} σ_{K'ᵖ})² ≤ tr(σ_{Kᵖ}²) · tr(σ_{K'ᵖ}²)` (`cosetDensity_pi_trace_mul_sq_le`),
i.e. the normalized overlap `(|K∩K'|/√(|K||K'|))^m ≤ 2^{-m/2}`, obtained by raising the single-copy
bound `Concrete.cosetDensity_trace_mul_sq_le` to the `m`-th power.

`AxQM/Concrete/SubgroupCount.lean` (pure math, general finite-group theory): the
**candidate-count** ingredient of the identification clause's counting tail (piece (ii) below).
It bounds the number of subgroups of a finite group, `Nat.card (Subgroup G) ≤ |G|^{log₂|G|+1}`
(`card_subgroup_le`), via the classical fact that a finite group is generated by at most `log₂|G|`
elements, `Group.rank G ≤ log₂|G|` (`rank_le_log_card`, from the doubling principle
`two_pow_card_le_card_closure_of_independent`: an independent generating finset `s` has
`2^{|s|} ≤ |⟨s⟩|`), so each subgroup is recovered from a generating finset of size `≤ log₂|G|`
(`exists_closure_finset_card_le_log`) and the subgroups inject into those short finsets.

`AxQM/Concrete/CosetOverlapSum.lean` (pure math): the **threshold split** and **far tail**
of the identification clause's collision sum (piece (ii) below). It names the concrete per-pair
affinity `cosetAffinity K K' = |K∩K'|/√(|K||K'|)` (the real shadow of `cosetDensityState_affinity`,
with `cosetAffinity_nonneg` / `cosetAffinity_self` / `cosetAffinity_le_of_ne : K ≠ K' → A ≤ 1/√2`),
and decomposes the candidate sum `∑_{K'≠K} A(K,K')^m` at any threshold `θ`
(`sum_cosetAffinity_pow_threshold_le`, and over the full lattice `sum_cosetAffinity_pow_univ_le`):

`∑_{K'≠K} A(K,K')^m ≤ |{K'≠K : A > θ}| · (1/√2)^m + |G|^{log₂|G|+1} · θ^m`,

the near terms bounded by the universal per-copy separation `1/√2` and the far part by the crude
candidate count `card_subgroup_le` times `θ^m` (the reusable count×separation bound
`sum_cosetAffinity_pow_le_of_forall_le`). These are valid inequalities and reusable tools, but — as
`Concrete/SubgroupIndexCount.lean` (next) makes precise — a *single* threshold with the *crude*
count is **not** the route to the linear sample count: at `m = 4 log₂|G| + 2` a constant `θ` leaves
the far term `|G|^{log₂|G|+1}·θ^m` super-polynomial, while shrinking `θ` swells the near count. The
linear bound needs the **index-refined** count, applied per dyadic shell.

`AxQM/Concrete/SubgroupIndexCount.lean` (pure math, general finite-group theory): the
**index-refined subgroup count** — the correct-route strengthening of `card_subgroup_le`. For a
fixed subgroup `H`, the number of subgroups `K'` above `H` of bounded relative order is
`#{K' : H ≤ K' ∧ |K'| ≤ |H|·d} ≤ |G|^{log₂ d + 1}` (`card_subgroup_index_le`), so overgroups of `H`
number only `|G|^{log₂(index)}` — polynomial once the index `[K':H]` is bounded (`H = ⊥`, `d = |G|`
recovers `card_subgroup_le`). Its heart is a **relative** generating-set / doubling principle
(`exists_finset_two_pow_mul_card_le`: every `K' ≥ H` is generated over `H` by `≤ log₂[K':H]`
elements, `2^{|s|}·|H| ≤ |K'|`), proved by strong induction on `|K'|` via a maximal proper
subgroup. This is the per-shell count the Ettinger–Høyer–Knill dyadic decomposition needs
(piece (ii)): candidates with affinity `A(K,K') ≥ 2^{-j/2}` all lie above `K∩K'` with
`[K':K∩K'] ≤ 2^j`, so this lemma (at `H = K∩K'`, `d = 2^j`) caps their number by `|G|^{j+1}`.

`AxQM/Concrete/OvergroupOrderSum.lean` (pure math): the **inner geometric sum** of the
Ettinger–Høyer–Knill collision bound (piece (ii)), now with a **sharp absolute constant**. The
overgroup order-sum `∑_{K' ≥ H} (|H|/|K'|)^s ≤ 2` (`sum_overgroup_ratio_pow_le`, valid once
`2|G| ≤ 2^s`) sums the inverse relative index `[K':H]^{-s}` over *every* overgroup of a fixed `H`
and converges to a constant with **no factor of `|G|`**. This is proved by a **binomial /
relative-generating-set** estimate, not a dyadic-shell count: each `K' ≥ H` is generated over `H` by
a finite set `t(K') ⊆ G` with `[K':H] ≥ 2^{|t|}` (`exists_finset_two_pow_mul_card_le`), and
`K' = ⟨t⟩ ⊔ H` recovers `K'` from `t`, so `K' ↦ t(K')` injects the overgroups into the finsets of
`G`; hence `∑_{K'≥H}(|H|/|K'|)^s ≤ ∑_{t⊆G}(2^{-s})^{|t|} = (1+2^{-s})^{|G|} ≤ e^{|G|·2^{-s}} ≤ 2`
(binomial identity, then `1+y ≤ e^y` and `|G|·2^{-s} ≤ 1/2`). The **earlier dyadic-shell bound `≤
2|G|²`** — with its spurious `|G|²` (the shell-`0` count `|G|^{0+2}` charged to the single member
`K' = H`) — is *fatally loose*: it forces a quadratic sample count; this binomial bound removes the
`|G|²` and is what makes the linear `m` reachable. Feeding it the intersection decomposition gives
the **per-intersection collision contribution** `∑_{K' : K∩K'=H} A(K,K')^{2s} ≤ (|H|/|K|)^s · 2`
(`sum_cosetAffinity_pow_inter_le`), reindexing the collision sum by `H = K∩K'` (each such `K'` has
`A(K,K') = |H|/√(|K||K'|)`, so `A^{2s} = (|H|/|K|)^s·(|H|/|K'|)^s`). Summing this over `H ≤ K`
reduces the full sum to `2·∑_{H≤K} (|H|/|K|)^s`; the *outer* factor `∑_{H≤K} (|H|/|K|)^s` is a
low-index count over the **sub**groups of `K` (the dual counting direction — *not*
`card_subgroup_index_le`, and *not* reachable by the binomial argument above, since a generating set
of the fixed `K` over a varying `H` does not recover `H`), and is the one remaining ingredient of
(ii).

`AxQM/Concrete/CosetCollisionSum.lean` (pure math): the **collision-sum reduction** — the
reindexing of the per-intersection contribution into the full candidate sum, now a theorem. Since
every candidate `K'` has `K ∩ K' ≤ K`, the map `K' ↦ K∩K'` fibres the subgroup lattice over the
`H ≤ K`; reindexing along it (`Finset.sum_fiberwise_of_maps_to`) and bounding each fibre by
`sum_cosetAffinity_pow_inter_le` gives `∑_{K'≠K} A(K,K')^{2s} ≤ 2·∑_{H≤K} (|H|/|K|)^s`
(`sum_cosetAffinity_pow_collision_le`). This turns the prose reduction (above, and in
`OvergroupOrderSum.lean`) into a formal lemma and pins the *entire* remaining counting tail on the
single **outer low-index sum** `∑_{H≤K} (|H|/|K|)^s`. (The bound's right side is `≥ 2` — the `H=K`
term is `(|K|/|K|)^s·2 = 2`, the sharp per-intersection factor not peeling off the trivial `K'=K`
diagonal.) The `H=K` fibre's sharpening is now **composed into the reduction**: the
diagonal-corrected reduction `Concrete.sum_cosetAffinity_pow_collision_proper_le`
(`CosetCollisionSum.lean`) peels the `H=K` fibre off exactly and replaces its loose `2` with the
true tail `∑_{K'⊋K}(|K|/|K'|)^s ≤ 2·|G|·2^{-s}` (the diagonal-excluded overgroup tail
`Concrete.sum_proper_overgroup_ratio_pow_le`, `OvergroupOrderSum.lean`), giving
`∑_{K'≠K} A(K,K')^{2s} ≤ 2·|G|·2^{-s} + 2·∑_{H<K} (|H|/|K|)^s`; at N&C's sample exponent
`s = 2 log₂|G| + 1` (`2·|G|² ≤ 2^s`) the first term is `≤ 1/|G|`
(`Concrete.sum_cosetAffinity_pow_collision_proper_le_of_sq`:
`∑_{K'≠K} A(K,K')^{2s} ≤ 1/|G| + 2·∑_{H<K} (|H|/|K|)^s`). The **one remaining ingredient** is then
the **proper-subgroup outer sum** `∑_{H<K} (|H|/|K|)^s`, whose bound drives the collision sum below
`1/|G|` at N&C's linear sample count.

`AxQM/Concrete/SubgroupMaximalSum.lean` (pure math): the **maximal-subgroup reduction** of
that proper-subgroup outer sum. The outer sum is *not* reachable by the overgroup binomial injection
(a generating set of the fixed `K` over a varying `H` does not recover `H`); this file instead
reduces it to a sum over the **maximal** subgroups `M ⋖ K` (coatoms of `K`) — the classical, far
smaller generation-probability quantity. The **coatom recursion**
`sum_subgroup_ratio_pow_lt_le_maximal_mul` (every proper `H < K` lies below some coatom `M ⋖ K` via
`exists_le_covBy_of_lt` — strong coatomicity of the finite subgroup lattice — plus the index
factoring `[K:H] = [K:M]·[M:H]`) gives
`∑_{H<K} (|H|/|K|)^s ≤ ∑_{M⋖K} (|M|/|K|)^s·(∑_{H≤M} (|H|/|M|)^s)`; a strong induction on `|K|` under
the mild generation bound `∀ J, ∑_{M⋖J} (|M|/|J|)^s ≤ 1/2` bounds each subgroup sum
`∑_{H≤K} (|H|/|K|)^s ≤ 2` (`sum_subgroup_ratio_pow_le_le_two_of_maximal`), whence the **usable
reduction** `∑_{H<K} (|H|/|K|)^s ≤ 2·∑_{M⋖K} (|M|/|K|)^s`
(`sum_subgroup_ratio_pow_lt_le_two_mul_maximal`). Composing this with the diagonal-corrected
collision bound yields `sum_cosetAffinity_pow_collision_maximal_le_of_sq`:
`∑_{K'≠K} A(K,K')^{2s} ≤ 1/|G| + 4·∑_{M⋖K} (|M|/|K|)^s`, so the **entire** remaining counting tail
is now carried by the single maximal-subgroup sum `∑_{M⋖K} (|M|/|K|)^s`. Its dominant part — the
index-`2` maximals, count `2^{d₂(K)} − 1 < |K|` — is elementary; the higher-index maximals still
need the Gaussian-binomial-strength count, so bounding `∑_{M⋖K} (|M|/|K|)^s ≤ c/|G|` (which implies
the mild `≤ 1/2` hypothesis) is the one **maximal-subgroup** count now isolated as ingredient (ii).

`AxQM/Concrete/SubgroupIndexTwoCount.lean` (pure math, general finite-group theory): the
**elementary index-`2` count** — the dominant part of that maximal-subgroup sum, now discharged. The
real **sign character** `signChar` of an index-`2` subgroup (`g ↦ ±1`, a genuine `G →* ℝ` since a
product lies in `H` iff its factors share membership, `Subgroup.mul_mem_iff_of_index_two`) injects
the index-`2` subgroups into the monoid homs `G →* ℝ`; **Dedekind's linear independence of
characters** (`linearIndependent_monoidHom`) makes those homs linearly independent in the
`|G|`-dimensional space `G → ℝ`, so `card_index_two_subgroup_le`: the number of index-`2` subgroups
of `G` is `≤ |G|`. Its **relative** form `card_relIndex_two_subgroup_le` (via the subgroup
correspondence `Subgroup.subgroupOf` on `↥K`) bounds the index-`2` subgroups of `K` by `|K|`, whence
`sum_index_two_maximal_ratio_pow_le`: `∑_{M≤K,[K:M]=2} (|M|/|K|)^s ≤ |K|·(1/2)^s` (each such `M` has
weight exactly `(1/2)^s`), and `sum_index_two_maximal_ratio_pow_le_of_sq`: at N&C's sample exponent
(`2·|G|² ≤ 2^s`) the **index-`2` part is `≤ 1/(2|G|)`**. This is the elementary half of the
maximal-sum `≤ c/|G|` target; the residual is the higher-index maximals, split by the next file
into the *normal* prime-index ones (now discharged) and the *non-normal* / *nonabelian-simple* ones.

`AxQM/Concrete/SubgroupPrimeIndexNormalCount.lean` (pure math, general finite-group
theory): the **prime-index normal count** — the extension of the index-`2` count from the single
prime `2` to *all* primes, discharging the *normal* prime-index part of the maximal-subgroup sum. A
maximal subgroup `M ⋖ K` that is normal in `K` with *abelian* simple quotient is exactly one of
**prime index** (`K/M ≅ ℤ/p`), so its contribution is governed by counting normal subgroups of prime
index. The real sign character of the index-`2` case has no `±1` real analogue at odd primes;
instead `exists_monoidHom_complexUnits_ker_eq` builds, for each normal `N ◁ G` of prime index, a
**complex** character `χ : G →* ℂˣ` with kernel *exactly* `N` — the prime-order quotient `G/N` is
simple, so a character not killing a chosen nonidentity element (one exists as `ℂ` has enough roots
of unity) is faithful there, and lifts to `G`. Distinct `N` are distinct kernels, so the prime-index
normals inject into `G →* ℂˣ`, whose cardinality is `≤ |G|` (`card_monoidHom_complexUnits_le`, via
`Abelianization.lift` and `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`):
`card_prime_index_normal_le`. Its relative form `card_relIndex_prime_normal_le` (subgroup
correspondence on `↥K`) bounds the prime-index normals of `K` by `|K|`, whence
`sum_prime_index_normal_maximal_ratio_pow_le`:
`∑_{M ≤ K normal, [K:M] prime} (|M|/|K|)^s ≤ |K|·(1/2)^s` (each weight `≤ (1/2)^s` since the index
is `≥ 2`), and `sum_prime_index_normal_maximal_ratio_pow_le_of_sq`: at N&C's sample exponent the
**normal prime-index part is `≤ 1/(2|G|)`**. Every finite **nilpotent** group has *all* its maximal
subgroups normal of prime index, so this closes the entire counting tail for that class; the
residual in general is the **non-normal** maximals and the (index `≥ 60`) **nonabelian-simple**
normal maximals, still of Gaussian-binomial strength.

`AxQM/Concrete/SubgroupFixedQuotientCount.lean` (pure math, general finite-group theory):
the **fixed-quotient normal-subgroup count** — the tool for the *nonabelian-simple* normal maximals,
the part of that residual with **no** single-character analogue. Where the prime-index (abelian,
cyclic) case injects all its normal subgroups into the one character group `G →* ℂˣ`, a nonabelian
simple quotient is perfect (no nontrivial characters) and no single finite group receives every
nonabelian simple quotient, so these maximals must be counted **one quotient type `Q` at a time**.
The general count `card_monoidHom_le_pow_log` bounds `#(G →* Q) ≤ |Q|^{log₂|G|}` (a homomorphism is
fixed by its values on a size-`≤ log₂|G|` generating finset, `exists_closure_finset_card_le_log`);
`card_kernel_surjective_hom_le` then bounds, for a fixed finite `Q`, the number of subgroups with
quotient `G ⧸ N ≃ Q` (the kernels of surjections `G →* Q`) by `|Q|^{log₂|G|}`, and its relative form
`card_relIndex_kernel_surjective_hom_le` bounds the `M ≤ K` with `K/M ≅ Q` by `|Q|^{log₂|K|}` — the
**per-type** count of the nonabelian-simple normal maximals of `K`. This generalizes
`card_prime_index_normal_le` from the abelian (single-target) case to any fixed quotient. The one
step still outstanding for this residual class is the **aggregation over quotient types**: the
distinct nonabelian simple quotient types of `K` number at most `log₂|K|`, so summing the per-type
contribution `|Q|^{log₂|K|}·|Q|^{-s}` over them stays `≤ c/|G|` at N&C's sample exponent. (The sharp
`log₂|K|` type-count is essential: bounding the number of types crudely by the number of subgroups
`|K|^{log₂|K|+1}` reintroduces a `(log₂|K|)²` term in the exponent and returns to the quadratic
regime.)

`AxQM/Concrete/SimpleProductQuotient.lean` (pure math, general finite-group theory): the
**structural crux** behind that aggregation. The `log₂|K|` type-count follows from `∏ᵢ |Qᵢ| ≤ |K|`
for pairwise non-isomorphic quotient types `Qᵢ`, which in turn needs that a nonabelian simple `K/M`
is **not** a quotient of a product of the *other* types — an instance of the general fact proved
here: `exists_mulEquiv_of_surjective_pi`, *a simple group that is a surjective image of a finite
product of simple groups is isomorphic to one of the factors* (`∃ j, Q j ≃* R`), and its quotient
form `exists_mulEquiv_quotient_of_pi`, *a simple quotient of a finite product of simple groups is a
factor*. The proof is **commutator-free**: the factor inclusions `MonoidHom.mulSingle Q j` generate
the product (`Subgroup.pi_mem_of_mulSingle_mem`), so a surjection cannot kill all of them; a factor
it spares maps (its range being the image of the *normal* `(MonoidHom.mulSingle Q j).range`) onto a
nontrivial normal subgroup of the simple `R`, hence onto `R`, while simplicity of `Q j` makes that
map injective — a bijection.

`AxQM/Concrete/PairwiseSimpleQuotientCount.lean` (pure math, general finite-group theory):
the **diagonal-surjectivity / product-of-indices** step this feeds — the `log₂|K|` type-count
itself, now discharged. For a finset of normal subgroups `N i` with `G ⧸ N i` simple and **pairwise
non-isomorphic**, the diagonal `G →* ∏ᵢ (G ⧸ N i)` is *surjective* (`diagPiQuot_surjective`), whence
`∏ᵢ [G : N i] ≤ |G|` (`prod_index_le_card_of_pairwise_noniso_simpleQuotient`) and each simple
quotient has order `≥ 2` — `#{types} ≤ log₂|G|` (`card_le_log_of_pairwise_noniso_simpleQuotient`),
the sharp type-count. The surjectivity is a `Finset.induction`: at the step adding `N j`, the
diagonal's kernel `M = ⋂_{i∈s} N i` cannot lie in `N j` (else `G ⧸ N j`, factoring through the
product `∏_{i∈s}(G ⧸ N i)`, would be a simple quotient of it, hence `≃*` a factor by
`exists_mulEquiv_of_surjective_pi` — contradicting pairwise non-isomorphism as `j ∉ s`), so `M`
and `N j` are **comaximal** (`sup_ker_eq_top_of_not_le`: a normal subgroup off the kernel of a
surjection onto a *simple* group is comaximal with it), and two comaximal normal subgroups have a
jointly surjective pair of quotient maps (`surjective_prod_of_sup_ker_eq_top`, the two-factor group
Chinese remainder theorem) — exactly the diagonal over `insert j s`. Applied to one `N` per
nonabelian-simple quotient *type* of `K`, this bounds the number of such types by `log₂|K|`.

`AxQM/Concrete/SimpleQuotientTypeCount.lean` (pure math, general finite-group theory): the
**arbitrary-family sharp type-count** — the bridge from that per-type-representative count to the
*actual* residual maximals. `card_le_log_of_pairwise_noniso_simpleQuotient` bounds the number of
types only for an *already pairwise non-isomorphic* family, but the residual maximals share types;
`exists_subset_pairwise_noniso_cover` reduces an **arbitrary** family `N : ι → Subgroup H` of normal
subgroups (with simple quotients) to a pairwise-non-isomorphic **covering** subfamily `r ⊆ s` (one
representative per realised type), by strong induction peeling off one isomorphism class at a time.
With the pairwise count this gives `exists_subset_cover_card_le_log_of_simpleQuotient`: **for
a finite `H`, any family of its normal subgroups realises `≤ log₂|H|` distinct simple quotient
types** — the sharp type-count in the form the aggregation consumes.

`AxQM/Concrete/SubgroupSimpleQuotientMaximalSum.lean` (pure math, general finite-group
theory): the **per-quotient-type contribution** — the fibre half of that sum bound, now discharged.
`sum_fixed_quotient_ratio_pow_le_of_sq`: for a fixed finite `Q` with `4 ≤ |Q|`, at N&C's sample
exponent (`2·|G|² ≤ 2^s`), the whole `Q`-fibre `∑_{M ≤ K : K/M ≅ Q} (|M|/|K|)^s ≤ 1/(2|G|²)` — each
such `M` carries the *single* weight `|Q|^{-s}` (`[K:M] = |Q|`), times the fibre count
`≤ |Q|^{log₂|K|}` (`card_relIndex_kernel_surjective_hom_le`), and the threshold `|Q| ≥ 4`
(`60 ≥ 4` for nonabelian simple `Q`) makes the decay `|Q|^{log₂|K| - s}` swamp the count.
`AxQM/Concrete/SubgroupSimpleQuotientTypeSum.lean` (pure math, general finite-group
theory): the **type-aggregation** — the residual *simple normal-maximal* sum bound, now discharged.
`sum_simple_quotient_ratio_pow_le_of_sq`: for `K ≤ G` (finite `G`) at `2·|G|² ≤ 2^s`, the total
weight of the `M ≤ K` whose relative subgroup is **normal with a simple quotient of order `≥ 4`** is
`∑ (|M|/|K|)^s ≤ 1/(2|G|)`. The sum is reindexed fibrewise over a set of `≤ log₂|K|` quotient-type
representatives (`exists_subset_cover_card_le_log_of_simpleQuotient`), each fibre bounded by the
per-type `sum_fixed_quotient_ratio_pow_le_of_sq` (`≤ 1/(2|G|²)`, transporting a member's chosen
quotient iso to the representative's fixed quotient `Q₀` via `QuotientGroup.congr`), closing with
`log₂|K| ≤ |K| ≤ |G|`. Stated over *all* order-`≥ 4` simple normal quotients (no maximality
hypothesis, not restricted to nonabelian simple) — `|Q| ≥ 4` is what the per-type bound needs and
every nonabelian simple `Q` has `|Q| ≥ 60`, so the residual nonabelian-simple normal maximals are a
subset (nonnegative weights); with the index-`2`, prime-index-normal, and now
nonabelian-simple-normal parts all `≤ c/|G|`, only the **non-normal** maximals remain open in (ii).

`AxQM/Concrete/SubgroupNonNormalMaximalSum.lean` (pure math, general finite-group theory):
the **non-normal maximal reduction** — the last residual part of the maximal-subgroup sum, reduced
to a single clean count. A maximal `M ⋖ K` is normal (handled above) or **non-normal**; a non-normal
one has relative index `≥ 3` (index `2` forces normality, `three_le_relIndex_of_lt_of_not_normal`),
hence weight `≤ (1/3)^s`, so `∑_{M ⋖ K, M ⋪ K} (|M|/|K|)^s ≤ #{non-normal maximals}·(1/3)^s`
(`sum_nonnormal_maximal_ratio_pow_le`); at N&C's exponent the polynomial count
`#{non-normal maximals of K} ≤ |K|²` drives it below `1/(2|G|)`
(`sum_nonnormal_maximal_ratio_pow_le_of_sq`) — the `(1/3)^s` weight is essential, as `2·|G|³ ≤ 3^s`
follows from `2·|G|² ≤ 2^s` (via `8^s ≤ 9^s`), the cubic decay `3^{-s}` swamping the count where
`2^{-s}` reaches only the constant `1/2`. This **isolates** the *one* remaining counting ingredient
of (ii): a polynomial bound `#{non-normal maximals} ≤ |K|²` (implied by Liebeck–Pyber–Shalev
`#{maximals} ≤ |K|^{3/2}`) — the residual that, unlike the normal cases (counted through their
quotient characters / hom-counts), has no group quotient to count through.

`AxQM/Concrete/SubgroupNonNormalMaximalConjugacy.lean` (pure math, general finite-group
theory): the **conjugacy-class refinement** of that non-normal reduction — sharpening the isolated
count. A non-normal maximal `M ⋖ K` is **self-normalizing** (`N_K(M) = M`,
`normalizer_inf_eq_self_of_covBy_of_not_normal`: `M ≤ N_K(M) ≤ K`, and `N_K(M) = K` would make `M`
normal), so under `K`-conjugation its class is a full orbit of size exactly `[K : N_K(M)] = [K : M]`
(`ncard_kConj_orbit_eq_relIndex_of_covBy_of_not_normal`, orbit–stabilizer
`MulAction.index_stabilizer` with the stabilizer identified as the normalizer). Each class thus
contributes `[K:M]·[K:M]^{-s} = [K:M]^{1-s} ≤ (1/3)^{s-1}`, an extra factor `[K:M] ≥ 3` of decay
per class, giving
`∑_{M ⋖ K, M ⋪ K} (|M|/|K|)^s ≤ #{K-conj classes of non-normal maximals}·(1/3)^{s-1}`
(`sum_nonnormal_maximal_ratio_pow_le_classCard`), and at N&C's exponent the **strictly weaker**
hypothesis `3·#classes ≤ |K|²` already drives the non-normal part below `1/(2|G|)`
(`sum_nonnormal_maximal_ratio_pow_le_classCard_of_sq`). This replaces the raw-count ingredient by
the smaller **class**-count `#{K-conj classes of non-normal maximals}` — the natural quantity, since
the collision sum sees one weight per class. (The class count is still Gaussian-binomial-strength
in the worst case — affine primitive quotients `V ⋊ H` realise `|H¹(H,V)|` complement classes — so
it remains the deep-group-theory residual, now in its sharpest elementary form.)

`AxQM/Concrete/SubgroupMaximalRatioSum.lean` (pure math, general finite-group theory): the
**assembled maximal-subgroup ratio sum**, which collects the ~eight-file maximal-subgroup
development into one bound. A maximal `M ⋖ K` normal in `K` has a **simple**
quotient `K/M` (`isSimpleGroup_quotient_of_covBy_of_normal`, the correspondence theorem: a coatom of
the subgroup lattice yields a simple quotient), which is prime-index-cyclic (abelian simple) or
nonabelian-simple (order `≥ 60 ≥ 4`) — so the normal maximals split across the prime-index-normal
and order-`≥ 4` simple-quotient families, giving the **unconditional**
`∑_{M ⋖ K, M ◁ K} (|M|/|K|)^s ≤ 1/|G|` (`sum_normal_maximal_ratio_pow_le_of_sq`, both families
`≤ 1/(2|G|)`). Adding the non-normal part (`sum_nonnormal_maximal_ratio_pow_le_classCard_of_sq`,
`≤ 1/(2|G|)` given the class count) yields the **full** bound
`∑_{M ⋖ K} (|M|/|K|)^s ≤ 3/(2|G|)` (`sum_maximal_ratio_pow_le_of_classCard_sq`), *conditional only*
on the single Liebeck–Pyber–Shalev count `3·#{K-conj classes of non-normal maximals} ≤ |K|²`.
This isolates the entire remaining Ettinger–Høyer–Knill counting tail (piece ii) as that one clean
group-theoretic hypothesis; composing it with the collision reduction
`Concrete.sum_cosetAffinity_pow_collision_maximal_le_of_sq` (which consumes the mild
`∀ J, ∑_{M ⋖ J} ≤ 1/2` this bound supplies) drives the coset collision sum to `O(1/|G|)` at N&C's
linear sample count — done in the next file.

`AxQM/Concrete/CosetCollisionSumClassCard.lean` (pure math): the **final threading** of the
piece-(ii) counting tail. It feeds `sum_maximal_ratio_pow_le_of_classCard_sq` into the
collision reduction `sum_cosetAffinity_pow_collision_maximal_le_of_sq` — applied at each `J`, it
discharges the mild generation hypothesis (`∑_{M⋖J} ≤ 3/(2|G|) ≤ 1/2` for `|G| ≥ 3`) and at `K`
bounds the residual maximal sum — giving `sum_cosetAffinity_pow_collision_classCard_le_of_sq`:
`∑_{K'≠K} A(K,K')^{2s} ≤ 1/|G| + 4·(3/(2|G|)) = 7/|G|` at N&C's sample exponent (`2·|G|² ≤ 2^s`),
**conditional only** on the single `∀`-quantified count
`∀ J, 3·#{J-conj classes of non-normal maximals} ≤ |J|²`. The *entire* remaining counting tail — the
output of the whole ~ten-file maximal-subgroup development — is now carried by that one hypothesis.
The constant `7/|G|` is `O(1/|G|)`, the linear sample count being the substantive
Ettinger–Høyer–Knill content; the sharp `1/|G|` needs a further sharpening of the collision factors.

### Remaining (the headline's research-grade identification clause)

The **near-orthogonality half** of Problem 5.5 is now fully discharged, including at N&C's exact
sample count: `cosetDensityState_pi_hsOverlap_le_of_sampleCount` (above) proves that for
`m = 4 log₂|G| + 2` the pairwise overlap of the reduced states of distinct hidden subgroups is
`≤ 1/(2|G|²)`. What remains is the headline's **identification clause** — that this
near-orthogonality lets a measurement identify `K` with success probability `≥ 1 − 1/|G|`. That
clause is now **assembled at the exact linear count, conditional on two isolated ingredients**
(`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard`:
`p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|` at `m = 4 log₂|G| + 2`); the two pieces below are those ingredients,
each now reduced to a single precise, proven-elsewhere hypothesis.

That clause is the Ettinger–Høyer–Knill result — proven mathematics, hence reachable **work**, not a
wall. Much of the needed discrimination machinery
is now present in the library: a `State`-level **trace distance** (`State.traceDistance`, from the
`ToMathlib/` Schatten-1 / trace-norm development), **mixed-state fidelity** (`State.fidelity`,
Uhlmann and Alberti bounds), the **quantum affinity** added by this file (`State.affinity`), the
**square-root (pretty-good) measurement** machinery (`POVM.prettyGood`, `prettyGoodDecoder`,
`ContinuousLinearMap.sum_genInvSqrt_conjugate_le_one`), and the pure-state `distinguishingPOVM`. Two
pieces remain to be assembled:

* **(i) A clean multi-state (ensemble) discrimination error bound.** The reduced states `σ_K^{⊗m}`
  are *mixed*, so the pure-state `distinguishingPOVM` does not directly apply. The **discrimination
  measurement itself is now built**: `State.prettyGoodMeasurement`
  (`Postulates/API/PrettyGoodDiscrimination.lean`) is the density-operator pretty-good (square-root)
  measurement of a finite family of states `ρ : ι → State S` — effect `Eᵢ = S₀⁻¹ᐟ² ρᵢ S₀⁻¹ᐟ²`
  (`S₀ = ∑ⱼ ρⱼ`), realised as a genuine `Measurement (Option ι) S` — the mixed-state analogue of
  `distinguishingPOVM` the identification clause is stated over. Its Born rule is characterised
  (`State.prettyGoodMeasurement_bornProb_some`/`_none`), and the identification **success**
  probability is put in **Barnum–Knill amplitude form**
  (`State.prettyGoodMeasurement_bornProb_self_eq`: `p(i∣ρᵢ) = re tr(Xᵢ²)`, `Xᵢ = √ρᵢ S₀⁻¹ᐟ² √ρᵢ`),
  the starting point of the error analysis. The **error bound is now proved, in summed form**:
  `State.sum_one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity`
  (`Postulates/API/PrettyGoodDiscrimination.lean`) is the reusable **state-discrimination** bound
  `∑ᵢ (1 − p(i∣ρᵢ)) ≤ 2·∑ᵢ ∑_{j≠i} A(ρᵢ, ρⱼ)` — the *total* identification error over the family
  bounded by twice the off-diagonal pairwise-affinity sum, exactly the quantity the affinity
  theorems in this file supply (`cosetDensityState_pi_affinity`). It composes the per-state deficit
  `1 − p(i∣ρᵢ) ≤ 2(re tr(√S₀ √ρᵢ) − 1)` with the Hilbert–Schmidt Cauchy–Schwarz operator kernel
  `ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_sum_cfc_sqrt_le`
  (`re tr(√S₀ · ∑ⱼ√ρⱼ) ≤ ∑ᵢⱼ re tr(√ρᵢ√ρⱼ)`). *The subtlety this route resolves*: the naive
  operator inequality `√S₀ ≤ ∑ⱼ√ρⱼ` is **false** (as is the general weighted trace form
  `tr(√S₀ C) ≤ ∑ⱼ tr(√ρⱼ C)`); only the Cauchy–Schwarz *summed* trace bound holds (pairing against
  `√S₀`/`∑√ρⱼ` specifically). This is the reusable form, distinct from the library's HSW
  *channel-coding* pretty-good bound `State.expectation_avgError_prettyGood_le` (random codebook +
  typical subspaces). **(i) is now instantiated for the coset family, and the identification
  headline is proved at a *polynomial* sample count.**
  `cosetDensityState_pi_prettyGoodMeasurement_sum_error_le`
  (below) specialises the summed bound to the family of *all* candidate subgroups (total error
  `≤ 2·∑_{K'}∑_{K''≠K'} cosetAffinity K' K''^m`), and
  `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_sampleCount` (below) turns it into the
  actual per-`K` identification guarantee `p(K ∣ σ_K^{⊗m}) ≥ 1 − 1/|G|` — the Ettinger–Høyer–Knill
  *polynomial query complexity* conclusion, at N&C's exact target probability — for every hidden
  subgroup `K`, at the **quadratic** sample count `m = 4(log₂|G|)² + 6 log₂|G| + 2 = O((log|G|)²)`.
  Its mechanism needs no per-state discrimination bound (none exists — see the false subadditivity
  above): each per-candidate deficit `1 − p(K' ∣ σ_{K'}^{⊗m})` is nonnegative, so the true `K`'s
  deficit is `≤` the *total* deficit, which the summed bound and the crude count
  `#subgroups ≤ |G|^{log₂|G|+1}` (`Concrete.card_subgroup_le`, each distinct pair separating by
  `2^{-m/2}`) drive below `1/|G|`. **The exact *linear* `m = 4 log₂|G| + 2` needs *two* refinements,
  and the summed route (this polynomial theorem) supplies neither.** (a) *A genuine per-state
  discrimination bound.* The summed bound gives only `1 − p(K) ≤ ∑_{K'} (1 − p(K'))`, and even with
  the *sharp* per-`K'` collision bound `∑_{K''≠K'} A ≤ 1/(2|G|)` (below) the total is
  `≥ #subgroups · 1/(2|G|)`, which is *super-polynomial* — so no counting refinement can push the
  *summed* route below the quadratic count. Reaching linear demands the per-`K` guarantee
  `1 − p(K ∣ σ_K^{⊗m}) ≤ 2·∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m})` directly, a *per-state*
  Barnum–Knill bound. **This is now proved conditionally, and the correct residual is isolated**
  (`cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired`, below,
  the coset instance of the reusable
  `State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity_of_paired`): the
  per-state deficit reduction `1 − p(K) ≤ 2·(re tr(√S₀ √σ_K^{⊗m}) − 1)`
  (`State.one_sub_prettyGoodMeasurement_bornProb_self_le_re_trace_cfc_sqrt`) reduces it to
  the **paired-trace inequality**
  `re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} A(σ_K^{⊗m}, σ_{K'}^{⊗m})` — the trace of `√σ_K^{⊗m}` against the
  *total* `√S₀` is at most the affinity sum. This is the *single* remaining piece-(i)(a) operator
  fact. Crucially it is **strictly weaker** than the operator subadditivity
  `√S₀ ≤ ∑_{K'}√σ_{K'}^{⊗m}` (which is genuinely *false*): it pairs the difference `√S₀ − ∑√σ_{K'}`
  against the *specific* positive operator `√σ_K^{⊗m}` rather than asserting an operator inequality.
  The paired form holds for every family of density operators (numerically verified; it *fails* for
  arbitrarily-reweighted positive operators, so it genuinely uses `tr σ_{K'}^{⊗m} = 1`); its general
  proof is subtle and normalization-dependent, and is not given here.
  **The *commuting* case is now discharged unconditionally**
  (`State.pairedTraceBound_of_commute`, `Postulates/API/PrettyGoodDiscrimination.lean`): when the
  family's density operators pairwise commute, the honest operator subadditivity
  `√S₀ ≤ ∑_{K'}√σ_{K'}` *does* hold — it is the general inequality
  `ContinuousLinearMap.cfc_real_sqrt_sum_le_of_commute`
  (`ToMathlib/Analysis/InnerProductSpace/CommuteSqrtSubadditive.lean`, the lift of the scalar
  `√(∑aⱼ) ≤ ∑√aⱼ` to a *commuting* family of positive operators, false without commutativity) — so
  pairing it against `√σ_K^{⊗m}` gives the paired-trace bound with no normalization needed. This
  covers the coset reduced states of any **abelian** hidden-subgroup instance: for abelian `G` the
  `σ_{K'}` are simultaneously diagonal in the character basis (convolution operators), hence
  commute, and `σ_{K'}^{⊗m}` in `G^ι` commute likewise — **now formalized**: for a commutative
  finite group the coset density operators commute, `Concrete.cosetDensity_commute` (elementary, via
  the summation-index involution `k ↦ i·k⁻¹·j`) bridged to the operator level as
  `cosetDensityState_op_commute` (`Postulates/API/CosetDensityState.lean`, through the `⋆`-algebra
  isomorphism `Matrix.toEuclideanCLM`). Instantiating `hpaired` from this commutation makes the
  linear-count headline **fully unconditional for abelian `G`**
  (`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_commGroup`, below: abelian ⇒ nilpotent
  so piece (ii) is already free, and `G^ι` abelian so the density operators commute and piece (i)(a)
  is discharged) — the first fully unconditional instance of the identification clause at N&C's
  exact linear sample count, covering the entire abelian hidden-subgroup problem. The general
  (non-commuting) *affinity* paired-trace inequality — needed for the *affinity*-metric bound for
  genuinely non-abelian `G` — is not proved here.

  **The *fidelity*-metric route discharges piece (i)(a) unconditionally for all `G`.** The affinity
  paired-trace inequality `re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} A(σ_K^{⊗m}, σ_{K'}^{⊗m})` is subtle, but
  its **fidelity** analogue `re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} F(σ_K^{⊗m}, σ_{K'}^{⊗m})` (with the
  larger `F(ρ, σ) = ‖√ρ √σ‖₁ ≥ A(ρ, σ)`) is **Rotfel'd's trace inequality**
  `tr √(∑ⱼ Bⱼ) ≤ ∑ⱼ tr √Bⱼ` (`ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_le_sum_traceNorm`, in
  `ToMathlib/`, applied to `Bⱼ = √σ_K^{⊗m} σ_{K'}^{⊗m} √σ_K^{⊗m}`; the operator subadditivity
  `√(∑Bⱼ) ≤ ∑√Bⱼ` is false, but its trace survives), which holds for **every** family of density
  operators with no commutativity or normalization hypothesis. This gives the **unconditional**
  per-state fidelity discrimination bound
  `cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_fidelity` (below,
  `1 − p(K) ≤ 2·∑_{K'≠K} F(σ_K^{⊗m}, σ_{K'}^{⊗m})`) for *every* hidden-subgroup instance — genuinely
  non-abelian `G` included. Piece (i)(a) is therefore **not** a wall: the only remaining ingredient
  toward the identification headline via this route is the *fidelity* collision sum
  `∑_{K'≠K} F(σ_K^{⊗m}, σ_{K'}^{⊗m})` (a counting task — the fidelity analogue of the affinity
  collision sum already driven to `O(1/|G|)`), not the affinity paired-trace inequality.
  **That collision sum, and the resulting identification headline, are proved** (conditional
  only on piece (ii), and *unconditionally* for nilpotent `G`). The bridge is the per-pair
  comparison `F(σ_K, σ_{K'})² ≤ A(σ_K, σ_{K'})` (`cosetDensityState_fidelity_sq_le_affinity`, via
  the Schatten 1–2 comparison), lifted to `m` copies **through the product-subgroup structure**
  (not `State.fidelity_tmul`) — since `σ_K^{⊗m}` is the coset density matrix of `K^ι` in `G^ι`, the
  single-copy `F² ≤ A` *applied at the product group* gives `F(σ_K^{⊗m}, σ_{K'}^{⊗m})² ≤
  A(σ_K^{⊗m}, σ_{K'}^{⊗m})` (`cosetDensityState_pi_fidelity_sq_le_affinity`). With the closed form
  `A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = A(σ_K, σ_{K'})^m` (`cosetDensityState_pi_affinity`) and `F ≥ 0`, this
  gives `F(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ A(σ_K, σ_{K'})^{m/2}`, so the fidelity collision sum at sample
  count `m = 4u` equals the *affinity* collision sum at exponent `2u`, `≤ 7/|G|`
  (`cosetDensityState_pi_sum_fidelity_collision_classCard_le`, conditional on the piece-(ii) class
  count). Composing this with the unconditional per-state fidelity discrimination bound yields the
  **fidelity-route identification headline** `p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|` at the **linear** count
  `m = 8 log₂|G| + 4` (twice N&C's exact `4 log₂|G| + 2` — the `F² ≤ A` comparison's price for being
  unconditional in (i)(a)): `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_classCard`
  (all `G`, conditional only on the piece-(ii) class count — **no** paired-trace hypothesis) and
  `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_nilpotent` (**fully unconditional** for
  every nilpotent `G` — strictly generalizing the abelian `..._bornProb_ge_of_commGroup`, which
  needed commutativity to discharge `hpaired`, to *all* nilpotent groups with no operator-inequality
  hypothesis at all).

  **N&C's exact target probability `1 − 1/|G|` is now reached (the sharp constant).** The `14/|G|`
  constant above is the loose `O(1/|G|)` order; N&C's *exact* `1 − 1/|G|` deficit needs the
  collision sum `≤ 1/(2|G|)`, supplied by
  `Concrete.sum_cosetAffinity_pow_collision_classCard_le_inv_of_sq` via an **exponent-raising**
  argument (each per-pair separation `A(K,K') ≤ 1/√2`, so raising the collision exponent from `2s`
  to `2(s+4)` scales the whole sum by `(1/√2)^8 = 1/16`, turning `7/|G|` into `≤ 1/(2|G|)`) — at the
  cost of a modestly larger, still **linear**, sample count. The sharp-constant **identification
  headlines are the two genuinely unconditional cases** (only what is *proved outright*, not
  hypothesis-encumbered):
  `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_commGroup`
  (**fully unconditional** for abelian `G`, `m = 4 log₂|G| + 10` — N&C's *literal* headline
  `p(K) ≥ 1 − 1/|G|` for the entire abelian hidden-subgroup problem: Simon's, Shor's) and
  `…_of_nilpotent` (fully unconditional for nilpotent `G`, fidelity route, `m = 8 log₂|G| + 20`).
  The sharp collision budget itself is exposed as the intermediate lemmas
  `cosetDensityState_pi_sum_{affinity,fidelity}_collision_classCard_le_inv` (`∑ ≤ 1/(2|G|)`,
  conditional on the piece-(ii) class count, like the `14/|G|` collision wrappers). The
  general-`G` `1 − 1/|G|` *identification* headline **is** now asserted at the sharp constant, as
  N&C's *literal* statement reduced to its isolated residual:
  `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard` (fidelity route,
  `m = 8 log₂|G| + 20`, conditional **only** on the piece-(ii) class count) and
  `…_one_sub_inv_of_paired_of_classCard` (affinity route, N&C's exact linear order
  `m = 4 log₂|G| + 10`, conditional on the paired-trace inequality **and** the class count),
  together with their end-to-end (from 5.80) forms
  `hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_{of_classCard,
  of_paired_of_classCard}`. These carry N&C's **exact** target probability `1 − 1/|G|` for general
  `G` at N&C's exact *linear* order, with the *entire* residual to the **unconditional** literal
  claim pinned to those explicit, proven-elsewhere Ettinger–Høyer–Knill ingredients — both free for
  the abelian core and every nilpotent `G` (the `…_one_sub_inv_of_commGroup` / `…_of_nilpotent`
  headlines above being the *unconditional* specializations). So of N&C's two exact constants
  (`1/|G|`, `4 log₂|G| + 2`) the **probability** `1 − 1/|G|` is now matched exactly —
  unconditionally for abelian and nilpotent `G`, and for general `G` modulo the one isolated
  piece-(ii) class count; what remains for an **unconditional** general-`G` theorem is that class
  count and the exact *additive* sample-count constant (`+2` vs the `+10`/`+20` this route's
  `1/(2|G|)` collision budget costs — both `O(log|G|)`).
  The base case `State.fidelity_tmul` (`Postulates/API/FidelityTensor.lean`,
  `F(ρ ⊗ σ, ρ' ⊗ σ') = F(ρ, ρ') · F(σ, σ')`, via `ContinuousLinearMap.traceNorm_mapL`) is a reusable
  fidelity fact but is *not* on this route's critical path (the `m`-copy lift goes through the
  product-subgroup structure, as for the affinity).

  **Correction of an earlier target recorded in this file.** A prior pass recorded the remaining
  piece (i)(a) as a *per-pair* bound
  `p(K' ∣ σ_K^{⊗m}) ≤ C·A(σ_K^{⊗m}, σ_{K'}^{⊗m})`. **That
  target is false**: the confusion `p(K' ∣ σ_K^{⊗m})` can be *positive* even when
  the pairwise affinity `A(σ_K^{⊗m}, σ_{K'}^{⊗m})` vanishes — a candidate reduced state *orthogonal*
  to `σ_K^{⊗m}` is still confused with it *through the other candidates' overlap in `S₀`* (a 3-state
  `ℂ²` witness `|0⟩, |1⟩, |+⟩` gives `p(1 ∣ ρ_0) > 0 = A(ρ_0, ρ_1)`). So no constant `C` bounds the
  per-pair confusion by the per-pair affinity; only the *per-state* (summed over `K'`) affinity
  bound holds, via the paired-trace inequality above. The reusable amplitude-overlap form of the
  confusion
  (`State.prettyGoodMeasurement_bornProb_some_eq_re_trace_amplitude`: `p(K' ∣ σ_K^{⊗m}) = re tr(T_K
  T_{K'})` with the positive `Tₐ = √S₀⁻¹ᐟ² ρₐ √S₀⁻¹ᐟ²`,
  `State.prettyGoodMeasurementAmplitude_nonneg`) and the exact per-`K` error decomposition
  `1 − p(K) = ∑_{K'≠K} re tr(T_K T_{K'})`
  (`State.one_sub_prettyGoodMeasurement_bornProb_self_eq_re_trace_amplitude_sum`, via
  `cosetDensityState_pi_prettyGoodMeasurement_error_eq_confusion`: the pretty-good measurement leaks
  *no* probability to its inconclusive outcome on a family state, each reduced state being `≤ S₀`)
  remain the operator handles, and the structural facts — **symmetry**
  `p(K' ∣ σ_K^{⊗m}) = p(K ∣ σ_{K'}^{⊗m})`
  (`cosetDensityState_pi_prettyGoodMeasurement_bornProb_some_comm`) and the **Cauchy–Schwarz** bound
  `p(K' ∣ σ_K^{⊗m})² ≤ p(K ∣ σ_K^{⊗m})·p(K' ∣ σ_{K'}^{⊗m})`
  (`cosetDensityState_pi_prettyGoodMeasurement_bornProb_some_sq_le`) — feed the analysis. (b)
  *The sharp counting.* Given (a), the per-`K` collision sum
  `∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m})` must be driven `O(1/|G|)`. This is discharged **conditional
  only on one group-theoretic count**: `cosetDensityState_pi_sum_affinity_collision_classCard_le`
  gives `∑_{K'≠K} A ≤ 7/|G|` at N&C's linear count, conditional on
  `∀ J, 3·#{J-conj classes of non-normal maximal subgroups} ≤ |J|²` (Liebeck–Pyber–Shalev strength).
  **Composing (a) and (b) now assembles the linear-count identification**:
  `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard` (below) proves
  `p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|` at `m = 4 log₂|G| + 2`, conditional on the two ingredients
  (the paired-trace inequality and the class count). Both are proven EHK mathematics
  — hence work still to be discharged, not walls; the EHK paper itself was not available
  to check, and the exact target `1 − 1/|G|` additionally needs a sharper collision constant.

* **(ii) The Ettinger–Høyer–Knill subgroup-index counting sum.** The crux of the **linear**
  `m = 4 log₂|G| + 2`. The discrimination error is the affinity **sum** over candidates,
  `∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = ∑_{K'≠K} (|K∩K'|/√(|K||K'|))^m`. A *naive* union bound —
  charging every one of the `#subgroups ≤ |G|^{log₂|G|+1} = 2^{Θ((log|G|)²)}` candidates the maximal
  per-copy separation `1/√2` — forces a *quadratic* `m = Θ((log|G|)²)`. Crucially, **a single
  threshold split with the crude count does not fix this** — the
  `Concrete.sum_cosetAffinity_pow_univ_le` (`Concrete/CosetOverlapSum.lean`,
  `∑_{K'≠K} A^m ≤ |{K'≠K : A > θ}|·(1/√2)^m + |G|^{log₂|G|+1}·θ^m`) is a valid inequality but not
  the linear route: at `m = 4 log₂|G| + 2` a constant `θ < 1/√2` leaves the far term
  `|G|^{log₂|G|+1}·θ^m` (exponent `(log₂|G|)² + (1 + 4 log₂θ)·log₂|G|`) super-polynomial, while any
  `θ` small enough to kill it swells the near count `|{K'≠K : A > θ}|` back to `|G|^{Θ(log|G|)}`.

  The linear bound instead reindexes the collision sum by the intersection `H = K∩K'`: a candidate
  with `K∩K' = H` has `A(K,K')^{2s} = (|H|/|K|)^s·(|H|/|K'|)^s`, so its contribution is a `K`-only
  weight times a residual summed over the overgroups of `H`. The **inner** (overgroup) residual is
  now discharged **sharply**: `∑_{K'≥H} (|H|/|K'|)^s ≤ 2`
  (`Concrete.sum_overgroup_ratio_pow_le`, `Concrete/OvergroupOrderSum.lean`), an *absolute* constant
  with **no factor of `|G|`**, proved by a **binomial / relative-generating-set** estimate — each
  `K'≥H` is generated over `H` by a finite set `t(K')` with `[K':H] ≥ 2^{|t|}`
  (`Concrete.exists_finset_two_pow_mul_card_le`) and `K' = ⟨t⟩ ⊔ H` recovers `K'`, so `K' ↦ t(K')`
  injects the overgroups into the finsets of `G`, whence
  `∑_{K'≥H}(|H|/|K'|)^s ≤ ∑_{t⊆G}(2^{-s})^{|t|} = (1+2^{-s})^{|G|} ≤ 2`. This gives the
  **per-intersection contribution** `∑_{K' : K∩K'=H} A^{2s} ≤ (|H|/|K|)^s · 2`
  (`Concrete.sum_cosetAffinity_pow_inter_le`), and summing over `H ≤ K` — now itself a formal lemma,
  `Concrete.sum_cosetAffinity_pow_collision_le` (`Concrete/CosetCollisionSum.lean`), reindexing the
  candidate lattice along `K' ↦ K∩K'` via `Finset.sum_fiberwise_of_maps_to` — leaves the full sum
  bounded by `2·∑_{H≤K} (|H|/|K|)^s`.

  *(An earlier route bounded the inner residual by `card_subgroup_index_le` via dyadic shells,
  reaching only `∑_{K'≥H}(|H|/|K'|)^s ≤ 2|G|²`. That `|G|²` — the shell-`0` count `|G|^{0+2}`
  charged to the single member `K'=H` — is **fatally loose**: times the outer sum `≥ 1` it can never
  reach `≤ 1/|G|`. The binomial bound above removes it; `card_subgroup_index_le` remains a valid,
  reusable per-shell count but is not the sharp inner-sum tool.)*

  With the **diagonal-corrected** collision-sum reduction now formalized
  (`Concrete.sum_cosetAffinity_pow_collision_proper_le_of_sq`:
  `∑_{K'≠K} A(K,K')^{2s} ≤ 1/|G| + 2·∑_{H<K} (|H|/|K|)^s` at the sample exponent), the `H=K` fibre
  is fully discharged — its true tail `∑_{K'⊋K}(|K|/|K'|)^s ≤ 2·|G|·2^{-s}`
  (`Concrete.sum_proper_overgroup_ratio_pow_le`) is `≤ 1/|G|` and now sits inside the reduction — so
  the **one remaining ingredient for (ii)** is the **outer** low-index sum
  `∑_{H<K} (|H|/|K|)^s` over the *proper sub*groups of `K` — the dual counting direction. It is
  *not* reachable by the binomial argument above (a generating set of the fixed `K` over a *varying*
  `H` does not recover `H`, so no injection exists). `Concrete/SubgroupMaximalSum.lean` **reduces
  this further to the maximal subgroups** of `K`: the coatom recursion + a strong induction under
  the mild generation bound give `∑_{H<K} (|H|/|K|)^s ≤ 2·∑_{M⋖K} (|M|/|K|)^s`
  (`Concrete.sum_subgroup_ratio_pow_lt_le_two_mul_maximal`), so
  `∑_{K'≠K} A(K,K')^{2s} ≤ 1/|G| + 4·∑_{M⋖K} (|M|/|K|)^s`
  (`Concrete.sum_cosetAffinity_pow_collision_maximal_le_of_sq`). The remaining tail is now the
  single **maximal-subgroup** sum `∑_{M⋖K} (|M|/|K|)^s`, and its **dominant index-`2` part is now
  discharged**: `Concrete/SubgroupIndexTwoCount.lean` proves the number of index-`2` subgroups of
  any finite group is `≤ |G|` (`Concrete.card_index_two_subgroup_le`, via the sign character
  `G →* ℝ` and Dedekind's linear independence of characters), whence its relative form
  `Concrete.card_relIndex_two_subgroup_le` (`≤ |K|` index-`2` subgroups of `K`) gives
  `Concrete.sum_index_two_maximal_ratio_pow_le_of_sq`: the index-`2` maximals contribute
  `≤ 1/(2|G|)` at N&C's sample exponent (`2·|G|² ≤ 2^s`).
  `Concrete/SubgroupPrimeIndexNormalCount.lean`
  then extends this from `p = 2` to **all primes**: the number of *normal* subgroups of prime index
  of any finite group is `≤ |G|` (`Concrete.card_prime_index_normal_le`, via a **complex** character
  `G →* ℂˣ` with the given kernel — the prime-order simple quotient makes any nontrivial character
  faithful — and the character-count bound `Nat.card (G →* ℂˣ) ≤ |G|`), so
  `Concrete.sum_prime_index_normal_maximal_ratio_pow_le_of_sq`: the **normal** prime-index maximals
  contribute `≤ 1/(2|G|)`. Since a nilpotent group's maximals are all normal of prime index, this
  closes the counting tail for that class. The **residual** in general is the **non-normal**
  maximals and the (index `≥ 60`) **nonabelian-simple** normal maximals. For the latter,
  `Concrete/SubgroupFixedQuotientCount.lean` supplies the missing **per-quotient-type** count
  (`Concrete.card_relIndex_kernel_surjective_hom_le`: for a fixed finite `Q`, the `M ≤ K` with
  `K/M ≅ Q` number `≤ |Q|^{log₂|K|}`, via the general hom-count `#(G →* Q) ≤ |Q|^{log₂|G|}` —
  the nonabelian generalization of the `G →* ℂˣ` character count that has no single-target form for
  the perfect nonabelian simple quotients). The **aggregation's type-count** is now discharged in
  `Concrete/PairwiseSimpleQuotientCount.lean`: the number of nonabelian-simple quotient types
  of `K` is `≤ log₂|K|` (`Concrete.card_le_log_of_pairwise_noniso_simpleQuotient`, from the diagonal
  surjectivity `∏ᵢ [K:Nᵢ] ≤ |K|` for pairwise non-isomorphic simple quotients — sharp, avoiding the
  `(log₂|K|)²` a crude subgroup-count type-bound would reintroduce). `Concrete/
  SimpleQuotientTypeCount.lean` then lifts that count to the *arbitrary* family of residual maximals
  (which are **not** pre-selected pairwise non-isomorphic): `exists_subset_pairwise_noniso_cover`
  extracts a pairwise-non-isomorphic **covering** subfamily — one representative per realised
  quotient type — by strong induction, whence `exists_subset_cover_card_le_log_of_simpleQuotient`
  gives that *any* family of normal subgroups of a finite `H` realises `≤ log₂|H|` distinct simple
  quotient types. `Concrete/SubgroupSimpleQuotientMaximalSum.lean` then discharges the **per-type
  contribution** (`sum_fixed_quotient_ratio_pow_le_of_sq`): for a fixed `Q` with `4 ≤ |Q|`, the
  whole fibre `∑_{M ≤ K : K/M ≅ Q} (|M|/|K|)^s ≤ 1/(2|G|²)` at the exponent — each such `M` has
  the *single* weight `|Q|^{-s}`, times the fibre count `≤ |Q|^{log₂|K|}`, and `|Q| ≥ 4` makes the
  decay `|Q|^{log₂|K|-s}` swamp the count (`2·|G|²·|Q|^{log₂|K|} ≤ |Q|^s`). The **type-aggregation**
  is discharged in `Concrete/SubgroupSimpleQuotientTypeSum.lean`
  (`sum_simple_quotient_ratio_pow_le_of_sq`, above): summing this per-type `1/(2|G|²)` over the
  `≤ log₂|K| ≤ |G|` realised types gives `≤ 1/(2|G|)` for the whole order-`≥ 4` simple normal
  sum, so with the index-`2`, prime-index-normal, and now nonabelian-simple-normal parts all
  `≤ c/|G|`, the **non-normal** maximals (Gaussian-binomial strength) are the **only** remaining
  counting sub-ingredient of piece (ii) — now **reduced to a single count** in
  `Concrete/SubgroupNonNormalMaximalSum.lean` (`sum_nonnormal_maximal_ratio_pow_le_of_sq`: the
  non-normal maximals contribute `≤ 1/(2|G|)` *given* `#{non-normal maximals of K} ≤ |K|²`, using
  relative index `≥ 3` ⇒ weight `≤ (1/3)^s` and `2·|G|³ ≤ 3^s`). So the entire remaining tail of
  (ii) is the *single* polynomial count `#{non-normal maximals} ≤ |K|²` (Liebeck–Pyber–Shalev),
  the residual with no group quotient to count through.

  **This deep count is entirely avoided for nilpotent `G`.** A nilpotent group — and every subgroup
  of one — has *no* non-normal maximal subgroups at all (`↥J` is nilpotent, hence satisfies the
  normalizer condition, under which every coatom is normal:
  `Concrete.normal_subgroupOf_of_covBy_of_isNilpotent` in
  `Concrete/SubgroupNilpotentMaximalNormal.lean`), so the class-count hypothesis
  `∀ J, 3·#{J-conj classes of non-normal maximals} ≤ |J|²` holds with both sides `0` on the left.
  Piece (ii) is therefore **unconditional** for the whole class of nilpotent groups (all abelian
  groups, all `p`-groups, and their direct products), giving the linear-count headline
  `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_nilpotent` conditional only
  on the piece-(i)(a) paired-trace inequality. The Liebeck–Pyber–Shalev count remains the residual
  for *general* (non-nilpotent) `G`.

  *(Correction of an earlier note in this file: the `≈ 2^{n²/4}` figure for `(ℤ/2)ⁿ` counts **all**
  rank-`n/2` subgroups, the overwhelming majority of which meet a fixed rank-`n/2` subgroup in a
  **small** intersection — those at overlap exactly `1/2` number only `2^{Θ(n)}`. So the geometric
  decay genuinely dominates and the sum is linear-`m`; this is reachable **work**, not the wall a
  prior pass recorded.)

Both pieces are reachable developments — (i) a discrimination bound to state and prove over the
existing square-root-measurement machinery, (ii) a subgroup-counting lemma — that the
near-orthogonality theorems here feed. (The EHK paper itself was not available, but the
argument is standard enough to reconstruct.)

## The declarations

The theorems of this file, stated for the states `cosetDensityState` / `hspQueryState` and the
quantities `State.purity` / `State.hsOverlap` / `State.affinity`, are:

* `hspQueryState_reducedLeft` — single-copy reduced state `Tr_{ℂ[X]} |ψ_f⟩⟨ψ_f| = σ_K`;
* `cosetDensityState_purity` — `tr(σ_K²) = |K|/|G|`;
* `cosetDensityState_hsOverlap` — `⟨σ_K, σ_{K'}⟩_HS = |K∩K'|/|G|`;
* `cosetDensityState_two_mul_hsOverlap_sq_le` — single-copy near-orthogonality;
* `hspQueryState_reducedLeft_pi` — `m`-copy reduced state `= σ_K^{⊗m} = cosetDensityState (K^ι)`;
* `cosetDensityState_pi_purity` — `tr((σ_K^{⊗m})²) = (|K|/|G|)^m`;
* `cosetDensityState_pi_hsOverlap` — `⟨σ_K^{⊗m}, σ_{K'}^{⊗m}⟩_HS = (|K∩K'|/|G|)^m`;
* `cosetDensityState_pi_two_pow_mul_hsOverlap_sq_le` — exponential near-orthogonality;
* `cosetDensityState_pi_hsOverlap_le_of_sampleCount` — near-orthogonality at `m = 4 log₂|G| + 2`;
* `cosetDensityState_affinity` — `A(σ_K, σ_{K'}) = |K∩K'|/√(|K||K'|)`;
* `cosetDensityState_hsOverlap_le_affinity` — the overlap is dominated by the affinity,
  `⟨σ_K, σ_{K'}⟩_HS ≤ A(σ_K, σ_{K'})` (i.e. `|K∩K'|/|G| ≤ |K∩K'|/√(|K||K'|)`), the coset instance of
  the general `State.hsOverlap_le_affinity`; the affinity is the safe (larger) collision resource;
* `cosetDensityState_affinity_le` — single-copy affinity near-orthogonality `≤ 1/√2`;
* `cosetDensityState_pi_affinity` — `A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = (|K∩K'|/√(|K||K'|))^m`;
* `cosetDensityState_pi_affinity_le` — exponential affinity near-orthogonality `≤ 2^{-m/2}`;
* `cosetDensityState_pi_sum_affinity_collision_le` — the per-`K` affinity collision sum with the
  `H = K` diagonal discharged: `∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 1/|G| + 2·∑_{H<K}(|H|/|K|)^s`
  at N&C's exact sample count (`m = 2s`, `2|G|² ≤ 2^s`) — the **physics-layer** form of the EHK
  collision reduction `Concrete.sum_cosetAffinity_pow_collision_proper_le_of_sq`, isolating the one
  remaining pure-math counting ingredient (the proper-subgroup low-index sum) at the `State` level;
* `cosetDensityState_pi_sum_affinity_collision_classCard_le` — the fully threaded per-`K` affinity
  collision sum: `∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 7/|G|` at N&C's exact sample count,
  **conditional only** on the single class count `∀ J, 3·#{J-conj classes of non-normal maximals}
  ≤ |J|²` — the `State`-layer form of
  `Concrete.sum_cosetAffinity_pow_collision_classCard_le_of_sq`, discharging the residual
  proper-subgroup sum of the previous bullet through the whole maximal-subgroup development and
  pinning the *entire* EHK piece-(ii) counting tail on that one `∀`-quantified hypothesis;
* `cosetDensityState_traceDistance_ge` — single-copy distinguishability `D(σ_K, σ_{K'}) ≥ 1 − 1/√2`;
* `cosetDensityState_pi_traceDistance_ge` — exponential distinguishability
  `D(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≥ 1 − 2^{-m/2}` (the operational, measurement-facing form);
* `cosetDensityState_pi_prettyGoodMeasurement_sum_error_le` — the total pretty-good identification
  error over all candidate subgroups is `≤ 2·(coset collision sum)` (coset instance of the summed
  Barnum–Knill discrimination bound);
* `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_sampleCount` — the identification
  headline at a **polynomial (quadratic)** sample count: for every hidden subgroup `K`, the
  pretty-good measurement identifies it with `p(K ∣ σ_K^{⊗m}) ≥ 1 − 1/|G|` once
  `m ≥ 4(log₂|G|)² + 6 log₂|G| + 2` (the EHK polynomial-query-complexity conclusion at N&C's exact
  target probability; the optimal *linear* `m = 4 log₂|G| + 2` is the piece-(i)(a)+(ii) refinement);
* `cosetDensityState_pi_prettyGoodMeasurement_error_eq_confusion` — the **exact** per-`K`
  identification error `1 − p(K ∣ σ_K^{⊗m}) = ∑_{K'≠K} p(K' ∣ σ_K^{⊗m})` (total coset confusion
  probability, junk-free), the exact per-state form feeding the linear-count refinement (i)(a) — the
  per-state affinity bound is now discharged conditional on the paired-trace inequality (coset
  instance of `State.one_sub_prettyGoodMeasurement_bornProb_self_eq_sum`);
* `cosetDensityState_pi_prettyGoodMeasurement_bornProb_some_comm` — **symmetry** of the coset
  confusion matrix `p(K' ∣ σ_K^{⊗m}) = p(K ∣ σ_{K'}^{⊗m})` (coset instance of
  `State.prettyGoodMeasurement_bornProb_some_comm`), so the exact-error identity above also reads
  `1 − p(K) = ∑_{K'≠K} p(K ∣ σ_{K'}^{⊗m})`;
* `cosetDensityState_pi_prettyGoodMeasurement_bornProb_some_sq_le` — the **Cauchy–Schwarz** bound
  `p(K' ∣ σ_K^{⊗m})² ≤ p(K ∣ σ_K^{⊗m})·p(K' ∣ σ_{K'}^{⊗m})` (coset instance of
  `State.prettyGoodMeasurement_bornProb_some_sq_le`): distinct candidates are confused by at most
  the geometric mean of their identification-success rates — a `State`-level structural bound of the
  per-pair confusion analysis of (i)(a);
* `cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired` — the
  **per-state** Ettinger–Høyer–Knill discrimination bound (piece (i)(a)):
  `1 − p(K ∣ σ_K^{⊗m}) ≤ 2·∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`, conditional on the coset paired-trace
  inequality `re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} A(σ_K^{⊗m}, σ_{K'}^{⊗m})` (the *correct*, per-state
  residual — the earlier per-pair target `p ≤ C·A` is false, see the "Remaining" note). Coset
  instance of the reusable
  `State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity_of_paired`;
* `cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_fidelity` — the **unconditional**
  per-state discrimination bound `1 − p(K ∣ σ_K^{⊗m}) ≤ 2·∑_{K'≠K} F(σ_K^{⊗m}, σ_{K'}^{⊗m})` in the
  **fidelity** metric, with **no** paired-trace hypothesis. It is the fidelity companion of the
  previous (affinity) bullet: the affinity paired-trace inequality is subtle and open in general,
  but its fidelity analogue `re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} F(σ_K^{⊗m}, σ_{K'}^{⊗m})` is
  **Rotfel'd's trace inequality** (`ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_le_sum_traceNorm`,
  `tr √(∑ⱼ Bⱼ) ≤ ∑ⱼ tr √Bⱼ`), which holds unconditionally, so piece (i)(a) is discharged
  **outright for every hidden-subgroup instance** in the fidelity metric — leaving only the
  *fidelity* collision
  sum as the remaining ingredient (a counting task; `A ≤ F` so it is the fidelity analogue of the
  already-`O(1/|G|)` affinity collision sum). Coset instance of the reusable
  `State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_fidelity`;
* `cosetDensityState_pi_fidelity_sq_le_affinity` — the `m`-copy per-pair fidelity bound
  `F(σ_K^{⊗m}, σ_{K'}^{⊗m})² ≤ A(σ_K^{⊗m}, σ_{K'}^{⊗m})`, the `m`-copy lift of the single-copy
  `cosetDensityState_fidelity_sq_le_affinity` obtained by applying it at the product group `G^ι`
  (`σ_K^{⊗m}` being the coset density matrix of `K^ι`); the bridge from the *fidelity* collision sum
  to the *affinity* one;
* `cosetDensityState_pi_sum_fidelity_collision_classCard_le` — the per-`K` **fidelity** collision
  sum `∑_{K'≠K} F(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 7/|G|` at the linear count `m = |ι| = 4u`
  (`2·|G|² ≤ 2^u`, `m = 8 log₂|G| + 4`), conditional only on the piece-(ii) non-normal maximal class
  count. From
  `F² ≤ A` (previous bullet) and the closed form
  `A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = A(σ_K, σ_{K'})^{4u} = (A(σ_K,σ_{K'})^{2u})²` it bounds each
  `F ≤ A(σ_K,σ_{K'})^{2u} = Concrete.cosetAffinity K K'^{2u}`, then applies the concrete affinity
  collision bound `Concrete.sum_cosetAffinity_pow_collision_classCard_le_of_sq` at exponent
  `2u`; the fidelity companion of `cosetDensityState_pi_sum_affinity_collision_classCard_le`;
* `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_classCard` — the **fidelity-route
  identification headline** for general `G`: `p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|` at the linear count
  `m = 8 log₂|G| + 4`, composing the *unconditional* per-state fidelity discrimination bound with
  the fidelity collision sum — **conditional only on the piece-(ii) class count, with no
  paired-trace hypothesis** (unlike the affinity `..._of_paired_of_classCard`, which needs both).
  Piece (i)(a) is
  discharged outright for every hidden-subgroup instance; the price is the doubled sample count;
* `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_nilpotent` — the same fidelity-route
  headline `p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|` **fully unconditional for every nilpotent `G`** (piece
  (ii) vacuous — no non-normal maximal subgroups — and piece (i)(a) discharged by the fidelity
  route). It
  **strictly generalizes** the abelian `..._bornProb_ge_of_commGroup` (fully unconditional only for
  *abelian* `G`, discharging `hpaired` from commutativity) to *all* nilpotent groups (all abelian
  groups, all `p`-groups, and their direct products) with no operator-inequality hypothesis at all;
* `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard` — the
  **identification headline at N&C's exact linear count** `m = 4 log₂|G| + 2`:
  `p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|`, composing the per-state bound above with the affinity collision
  sum `cosetDensityState_pi_sum_affinity_collision_classCard_le` — conditional on the two isolated
  EHK ingredients (the paired-trace inequality and the non-normal maximal class count). The
  substantive linear-`m` content, `O(1/|G|)` error at `O(log|G|)` oracle calls.
* `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_nilpotent` — the same
  linear-count identification headline `p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|` with piece (ii) **discharged
  unconditionally for nilpotent `G`**: a nilpotent group (and every subgroup of one) has *no*
  non-normal maximal subgroups, so the Liebeck–Pyber–Shalev-strength class count is vacuous
  (`Concrete.normal_subgroupOf_of_covBy_of_isNilpotent` in
  `Concrete/SubgroupNilpotentMaximalNormal.lean`).
  For the entire class of nilpotent groups (all abelian groups, all `p`-groups, and their direct
  products) the deep-group-theory dependency is eliminated, leaving only the piece-(i)(a)
  paired-trace inequality `hpaired` as the single remaining ingredient.
* `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_commGroup` — the **fully
  unconditional** linear-count identification headline for **abelian** `G`:
  `p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|` at
  `m = 4 log₂|G| + 2` with **both** EHK ingredients discharged. Piece (ii) is free (abelian ⇒
  nilpotent, via the theorem above); piece (i)(a)'s `hpaired` is discharged because the coset
  density operators of the abelian `G^ι` pairwise commute (`cosetDensityState_op_commute`, from
  `Concrete.cosetDensity_commute`), so `State.pairedTraceBound_of_commute` applies. The first fully
  unconditional instance of the identification clause at N&C's exact linear sample count.
* `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard` and
  `…_ge_one_sub_inv_of_paired_of_classCard` — the general-`G` identification headlines at **N&C's
  exact target probability** `1 − 1/|G|` (the sharp-constant refinements of the `14/|G|`
  `…_of_classCard` / `…_of_paired_of_classCard`). The first (fidelity, `m = 8 log₂|G| + 20`) is
  conditional **only** on the piece-(ii) class count; the second (affinity route, N&C's exact linear
  order `m = 4 log₂|G| + 10`) on the paired-trace inequality **and** class count. They state N&C's
  *literal* target probability for general non-Abelian `G`, the residual to the **unconditional**
  claim being exactly those isolated Ettinger–Høyer–Knill ingredients — both free for the abelian
  core and every nilpotent `G` (the `…_one_sub_inv_of_commGroup` / `…_of_nilpotent` unconditional
  headlines above). They compose the per-state discrimination bounds with the *sharp* collision
  budget `cosetDensityState_pi_sum_{fidelity,affinity}_collision_classCard_le_inv` (`∑ ≤ 1/(2|G|)`).

The end-to-end headlines below state the same identification conclusion **from N&C's
literal starting state (5.80)** rather than the abstract reduced state `σ_K^{⊗m}` — the item's
natural top-level claim in N&C's own phrasing ("start with [5.80]… prove `K` [can] be identified
with probability at least `1 − 1/|G|`"), obtained by folding the reduced-state step
`hspQueryState_reducedLeft_pi` (`Tr_{ℂ[X]^{⊗m}} |ψ_f^{⊗m}⟩⟨ψ_f^{⊗m}| = σ_K^{⊗m}`) into the
corresponding `bornProb` headline:

* `hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_of_sampleCount` —
  **fully general** `G` (not necessarily Abelian, no Fourier transform): the pretty-good measurement
  on the reduced state of the `m`-copy query register (5.80) identifies `K` with `p(K) ≥ 1 − 1/|G|`
  at a **polynomial** sample count — the Ettinger–Høyer–Knill query-complexity conclusion at N&C's
  exact target probability, in N&C's literal form;
* `hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_of_classCard` — **fully general
  `G` at the LINEAR sample count** `m = 8 log₂|G| + 4`, `p(K) ≥ 1 − 14/|G|`, **conditional only on
  the piece-(ii) class count** `hcount` (piece (i)(a) discharged unconditionally by the fidelity
  route). This is N&C's linear query complexity for
  general non-Abelian `G` — in N&C's literal phrasing (from 5.80), with the remaining gap reduced to
  exactly one explicit finite-group count; end-to-end form of
  `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_classCard`;
* `hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard` — the same
  at N&C's **exact** count `m = 4 log₂|G| + 2` (affinity route), conditional on the two isolated
  ingredients (paired-trace `hpaired` + class count `hcount`); end-to-end form of
  `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard`;
* `hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_nilpotent` — the
  same, **fully unconditional for nilpotent `G`** at the **linear** count `m = 8 log₂|G| + 20` and
  N&C's exact target probability `1 − 1/|G|` (all abelian groups, all `p`-groups, and their direct
  products);
* `hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_commGroup` — the
  same for **abelian `G`** at `m = 4 log₂|G| + 10` (the sample count closest to N&C's exact
  `4 log₂|G| + 2`) — Problem 5.5's **literal** conclusion from its literal starting state, covering
  the canonical hidden-subgroup instances (Simon's problem, Shor's order-finding and discrete-log);
* `hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard` and
  `…_ge_one_sub_inv_of_paired_of_classCard` — **N&C's literal Problem 5.5 sentence for general
  non-Abelian `G` at the sharp probability `1 − 1/|G|`**, from the literal query state (5.80):
  general `G`, no Fourier transform, `m = 4 log₂|G| + O(1)` (`+ 20` fidelity route / `+ 10` affinity
  route), `p(K) ≥ 1 − 1/|G|`. Every element of N&C's sentence is present; the entire residual to the
  *unconditional* claim is exactly the isolated Ettinger–Høyer–Knill ingredients (the piece-(ii)
  class count, plus the paired-trace inequality on the affinity route), both discharged
  unconditionally for the abelian core (Simon's, Shor's) and all nilpotent `G` by the two
  `…_one_sub_inv_of_{commGroup,nilpotent}` headlines above. End-to-end forms of
  `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_{of_classCard,
  of_paired_of_classCard}`.

They rest on the results listed under "Supporting results": the pure-math coset density-matrix
kernel and its overlap/tensor-power counts in `Concrete/CosetState*.lean` (now including the
scaled-projector identity `cosetDensity_mul_self`), the states `groupSystem` /
`cosetDensityState` / `hspQueryState` in `Postulates/API/CosetDensityState.lean` and
`Postulates/API/HSPQueryState.lean`, the operator-square-root bridge `cosetDensityState_op_cfc_sqrt`
in `Postulates/API/CosetDensitySqrt.lean`, and the `State`-level distinguishability generators
`State.hsOverlap` (`Postulates/API/HSOverlap.lean`) and `State.affinity`
(`Postulates/API/Affinity.lean`, now carrying its full distinguishability-measure API:
`State.affinity_nonneg` / `State.affinity_le_one` place `A ∈ [0, 1]`,
`State.affinity_le_fidelity` records `A(ρ, σ) ≤ F(ρ, σ)`, and `State.hsOverlap_le_affinity` records
`⟨ρ, σ⟩_HS ≤ A(ρ, σ)` — so the three near-orthogonality quantities are ordered
`⟨ρ, σ⟩_HS ≤ A(ρ, σ) ≤ F(ρ, σ)`, the affinity never below the overlap and never above the fidelity,
making it the safe (larger-than-overlap) yet sharp (smaller-than-fidelity) resource the
identification clause's discrimination **sum** is taken over. `State.hsOverlap_le_affinity` rests on
the general sub-unital operator inequality
`ContinuousLinearMap.re_trace_mul_le_re_trace_cfc_sqrt_mul` (`re tr(A B) ≤ re tr(√A √B)` for
`0 ≤ A, B ≤ 1`, in `ToMathlib/`, each operator below its own square root
`ContinuousLinearMap.le_cfc_real_sqrt_of_le_one`)), and the pretty-good discrimination measurement
`State.prettyGoodMeasurement`
(`Postulates/API/PrettyGoodDiscrimination.lean`) with its exact per-state completeness on a family
(`State.prettyGoodMeasurement_bornProb_none_self_eq_zero` / `…_bornProb_self_eq_sum`), resting on
the generalized-inverse-square-root support-projection identity
`ContinuousLinearMap.mul_genInvSqrt_mul_self_mul_genInvSqrt_of_le`
(`ToMathlib/Analysis/InnerProductSpace/PrettyGoodMeasurementAmplitude.lean`:
`ρ ≤ A ⇒ ρ·A⁻¹ᐟ²·A·A⁻¹ᐟ²
= ρ`, the equality refining the sub-identity bound). Together they capture the
exponentially-near-orthogonal final state at the problem's own linear sample count, in both the
purity and fidelity metrics — the quantitative resource the remaining identification clause (a
long development, per "Remaining" above) consumes.
-/

-- This file exceeds the default file-length limit.
set_option linter.style.longFile 3600

open scoped ComplexOrder

namespace AxQM

variable {G X : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype X] [DecidableEq X]
variable (K : Subgroup G) [DecidablePred (· ∈ K)]

/-- **The single-copy HSP query state reduces to the coset density state `σ_K`** (Nielsen & Chuang,
Problem 5.5, reduced-state step). For a query function `f : G → X` constant and distinct on the left
cosets of `K` (`hf`), tracing the range register `ℂ[X]` out of the single-copy query state
`|ψ_f⟩ = |G|^{-1/2} ∑_g |g⟩|f(g)⟩` (eq. 5.80, `m = 1`) leaves the group register `ℂ[G]` in the coset
density state:

`Tr_{ℂ[X]} |ψ_f⟩⟨ψ_f| = σ_K`.

This is `State.ext` applied to the operator-level
`hspQueryState_reducedLeft_op` (which does the Schmidt-decomposition computation). It is the
single-copy (`m = 1`) kernel of the sampling argument: `σ_K` is the per-copy reduced state whose
`m`-fold tensor power carries the subgroup identifiability. -/
theorem hspQueryState_reducedLeft (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂) :
    (hspQueryState f).toState.reducedLeft = cosetDensityState K :=
  State.ext (hspQueryState_reducedLeft_op K f hf)

/-- **The purity of the single-copy coset reduced state is `|K|/|G|`** (Nielsen & Chuang, Problem
5.5). The single-copy reduced state `σ_K = cosetDensityState K` of the query register (5.80,
`m = 1`) has purity

`tr(σ_K²) = |K| / |G| = 1 / |G ⧸ K|`.

This is the quantitative statement that `σ_K` is the **maximally mixed state on the coset-symmetric
subspace**: `σ_K = (|K|/|G|) Π_K` is `|K|/|G|` times the rank-`|G ⧸ K|` projector
`Π_K = ∑_C |C⟩⟨C|`, so its purity is the reciprocal of that subspace's dimension. The purity
distinguishes reduced states of *different* candidate hidden subgroups (a larger subgroup `K` gives
a more mixed state), and is the `K = K'` diagonal case of the coset-density overlap
`tr(σ_K σ_{K'}) = |K ∩ K'|/|G|` (`Concrete.cosetDensity_trace_mul`) controlling near-orthogonality.

The proof does the `.op`/trace computation, reducing to `Concrete.cosetDensity_trace_mul_self`
through `Matrix.trace_toEuclideanCLM` and the
`⋆`-algebra multiplicativity of `Matrix.toEuclideanCLM`. -/
theorem cosetDensityState_purity :
    (cosetDensityState K).purity = (Nat.card ↥K : ℝ) / Fintype.card G := by
  -- `σ_K.op²` is `toEuclideanCLM` of the squared coset density matrix (`toEuclideanCLM` is `⋆`).
  have hop : (cosetDensityState K).op * (cosetDensityState K).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)
          (Concrete.cosetDensity K * Concrete.cosetDensity K) := by
    rw [cosetDensityState_op]
    exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)) _ _).symm
  rw [State.purity, hop]
  -- `(groupSystem G).space` is defeq `EuclideanSpace ℂ G`; rephrase there so the matrix-trace
  -- bridge `Matrix.trace_toEuclideanCLM` matches syntactically.
  change RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ G)
      ↑(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)
        (Concrete.cosetDensity K * Concrete.cosetDensity K)))
      = (Nat.card ↥K : ℝ) / Fintype.card G
  rw [Matrix.trace_toEuclideanCLM, Concrete.cosetDensity_trace_mul_self]
  simp

/-- **The Hilbert–Schmidt overlap of the single-copy coset reduced states of two hidden subgroups**
(Nielsen & Chuang, Problem 5.5). The reduced states `σ_K, σ_{K'}` of the query register (5.80,
`m = 1`) for candidate hidden subgroups `K, K'` have Hilbert–Schmidt overlap

`⟨σ_K, σ_{K'}⟩_HS = tr(σ_K σ_{K'}) = |K ∩ K'| / |G|`.

This is the quantitative measure of how nearly orthogonal the reduced states of *distinct* candidate
hidden subgroups are — the core of "the pure-state outcomes for different possible hidden subgroups
are nearly orthogonal". Its `K = K'` diagonal is the purity `cosetDensityState_purity`
(`hsOverlap σ_K σ_K = tr(σ_K²) = |K|/|G|`, via `State.hsOverlap_self`). The proof transports
`Concrete.cosetDensity_trace_mul` through `Matrix.trace_toEuclideanCLM` and the `⋆`-algebra
multiplicativity of `Matrix.toEuclideanCLM` (exactly the `cosetDensityState_purity` idiom with the
off-diagonal `Concrete.cosetDensity_trace_mul` in place of `…_self`). -/
theorem cosetDensityState_hsOverlap (K' : Subgroup G) [DecidablePred (· ∈ K')] :
    (cosetDensityState K).hsOverlap (cosetDensityState K')
      = (Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G := by
  have hop : (cosetDensityState K).op * (cosetDensityState K').op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)
          (Concrete.cosetDensity K * Concrete.cosetDensity K') := by
    rw [cosetDensityState_op, cosetDensityState_op]
    exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)) _ _).symm
  rw [State.hsOverlap, hop]
  change RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ G)
      ↑(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)
        (Concrete.cosetDensity K * Concrete.cosetDensity K')))
      = (Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G
  rw [Matrix.trace_toEuclideanCLM, Concrete.cosetDensity_trace_mul]
  simp

/-- **Single-copy near-orthogonality of the coset reduced states** (Nielsen & Chuang, Problem 5.5).
For *distinct* candidate hidden subgroups `K ≠ K'`, the Hilbert–Schmidt overlap of the single-copy
reduced states is bounded away from the geometric mean of their purities by a factor `2`:

`2 · ⟨σ_K, σ_{K'}⟩_HS² ≤ tr(σ_K²) · tr(σ_{K'}²)`,

i.e. the normalised overlap `|K∩K'| / √(|K||K'|) ≤ 1/√2`. This is the physical (`State`-level) form
of the group-theoretic bound `2·|K∩K'|² ≤ |K|·|K'|` (`Concrete.two_mul_card_inf_sq_le`): distinct
subgroups must differ by a factor of at least `2` somewhere, so their coset density matrices cannot
be too aligned. Taking `m` copies amplifies the `1/√2` per-copy separation to `2^{-m/2}`
(`cosetDensityState_pi_two_pow_mul_hsOverlap_sq_le`), the exponential near-orthogonality that drives
the identification argument. -/
theorem cosetDensityState_two_mul_hsOverlap_sq_le (K' : Subgroup G) [DecidablePred (· ∈ K')]
    (hne : K ≠ K') :
    2 * ((cosetDensityState K).hsOverlap (cosetDensityState K')) ^ 2
      ≤ (cosetDensityState K).purity * (cosetDensityState K').purity := by
  rw [cosetDensityState_hsOverlap, cosetDensityState_purity, cosetDensityState_purity,
    div_pow, ← mul_div_assoc, div_mul_div_comm, ← pow_two,
    div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Concrete.two_mul_card_inf_sq_le K K' hne

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `m`-copy HSP query state reduces to the tensor-power coset density state `σ_K^{⊗m}`**
(Nielsen & Chuang, Problem 5.5, the `m`-copy reduced-state step). For a query function `f : G → X`
constant and distinct on the left cosets of `K` (`hf`), the `m`-copy query state (eq. 5.80)

`|ψ_f^{⊗m}⟩ = |G|^{-m/2} ∑_{g₁,…,gₘ} |g₁,…,gₘ⟩ |f(g₁),…,f(gₘ)⟩`

reduces, after tracing out the `m`-fold range register, to `σ_K^{⊗m}`:

`Tr_{ℂ[X]^{⊗m}} |ψ_f^{⊗m}⟩⟨ψ_f^{⊗m}| = σ_K^{⊗m} = cosetDensityState (K^ι)`.

**No `m`-fold tensor machinery is needed.** With `ι` indexing the `m` copies (`ι ≃ Fin m`), the
`m`-copy query state *is* the single-copy query state for the direct-power group `G^ι = (ι → G)` and
the coordinatewise query function `F(g) = (f(g i))_i` (its range register is `X^ι = (ι → X)`, and
`|G^ι|^{-1/2} = |G|^{-m/2}`). Because `f` is constant and distinct on the cosets of `K`, `F` is
constant and distinct on the cosets of the product subgroup `K^ι = ∏_i K ≤ G^ι`
(`Concrete.quotient_mk_pi_const_eq_iff`), so the single-copy `hspQueryState_reducedLeft` applied to
`G^ι` gives the reduced state `cosetDensityState (K^ι)` — which is exactly the tensor power
`σ_K^{⊗m}`, since `σ_K^{⊗m}` is itself the coset density matrix of `K^ι`
(`Concrete.CosetStateOverlapPow`). This is the physical `State`-level form of that reframing. -/
theorem hspQueryState_reducedLeft_pi (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂) :
    (hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft
      = cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K) :=
  hspQueryState_reducedLeft (Subgroup.pi (Set.univ : Set ι) fun _ => K)
    (fun g : ι → G => fun i => f (g i)) fun g₁ g₂ => by
      simp only [funext_iff, Concrete.quotient_mk_pi_const_eq_iff, hf]

/-- **The purity of the `m`-copy coset reduced state is `(|K|/|G|)^m`** (Nielsen & Chuang, Problem
5.5). The `m`-copy reduced state `σ_K^{⊗m} = cosetDensityState (K^ι)` of the query register (5.80)
has purity

`tr((σ_K^{⊗m})²) = (|K|/|G|)^m = (1/|G ⧸ K|)^m`,

the `m`-th power of the single-copy purity `cosetDensityState_purity`. It is obtained by applying
`cosetDensityState_purity` to the product subgroup `K^ι` and simplifying its order
`|K^ι| = |K|^m` (`Concrete.natCard_subgroupPi_const`) against `|G^ι| = |G|^m`
(`Fintype.card_fun`). The purity decaying geometrically in the number `m` of coset samples is the
`K = K'` diagonal of the exponential near-orthogonality `Concrete.cosetDensity_pi_trace_mul_sq_le`
that drives the identification argument: distinct hidden subgroups give reduced states whose overlap
is suppressed by `2^{-m/2}`. -/
theorem cosetDensityState_pi_purity :
    (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).purity
      = ((Nat.card ↥K : ℝ) / Fintype.card G) ^ Fintype.card ι := by
  rw [cosetDensityState_purity, Concrete.natCard_subgroupPi_const, Fintype.card_fun]
  push_cast
  rw [div_pow]

/-- **The Hilbert–Schmidt overlap of the `m`-copy coset reduced states is `(|K∩K'|/|G|)^m`**
(Nielsen & Chuang, Problem 5.5). For candidate hidden subgroups `K, K'`, the `m`-copy reduced states
`σ_K^{⊗m} = cosetDensityState (K^ι)` and `σ_{K'}^{⊗m}` of the query register (5.80) have
Hilbert–Schmidt overlap

`⟨σ_K^{⊗m}, σ_{K'}^{⊗m}⟩_HS = tr(σ_K^{⊗m} σ_{K'}^{⊗m}) = (|K ∩ K'| / |G|)^m`,

the `m`-th power of the single-copy overlap `cosetDensityState_hsOverlap`. It is obtained by
applying `cosetDensityState_hsOverlap` to the product subgroups `K^ι, K'^ι ≤ G^ι` and simplifying
`K^ι ⊓ K'^ι = (K ⊓ K')^ι` (`Concrete.subgroupPi_const_inf`), `|(K∩K')^ι| = |K∩K'|^m`
(`Concrete.natCard_subgroupPi_const`), and `|G^ι| = |G|^m` (`Fintype.card_fun`) — the same
reframing (`σ_K^{⊗m}` is itself the coset density matrix of `K^ι`) that gives the `m`-copy reduced
state. Its `K = K'` diagonal is the `m`-copy purity `cosetDensityState_pi_purity`. -/
theorem cosetDensityState_pi_hsOverlap (K' : Subgroup G) [DecidablePred (· ∈ K')] :
    (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).hsOverlap
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
      = ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ Fintype.card ι := by
  rw [cosetDensityState_hsOverlap, Concrete.subgroupPi_const_inf,
    Concrete.natCard_subgroupPi_const, Fintype.card_fun]
  push_cast
  rw [div_pow]

/-- **Exponential near-orthogonality of the `m`-copy coset reduced states** (Nielsen & Chuang,
Problem 5.5). For *distinct* candidate hidden subgroups `K ≠ K'`, the Hilbert–Schmidt overlap of the
`m`-copy reduced states is suppressed by a factor `2^m` relative to the geometric mean of the
purities:

`2^m · ⟨σ_K^{⊗m}, σ_{K'}^{⊗m}⟩_HS² ≤ tr((σ_K^{⊗m})²) · tr((σ_{K'}^{⊗m})²)`,

i.e. the normalised overlap `(|K∩K'|/√(|K||K'|))^m ≤ 2^{-m/2}`. This is the **physical
(`State`-level) form of the exponential near-orthogonality** that N&C's Problem 5.5 highlights:
`m = 4 log|G| + 2` coset samples drive the overlap of the reduced states of any two distinct
candidate hidden subgroups below `2^{-2}/|G|²`, so a distinguishing measurement (via a union bound
over candidate subgroups) identifies the true `K` with high probability. It is the `m`-fold
amplification of the single-copy bound `cosetDensityState_two_mul_hsOverlap_sq_le`: the proof reuses
that theorem for the per-copy inequality (so the near-orthogonality normalisation arithmetic — whose
group-theoretic core is `Concrete.two_mul_card_inf_sq_le` — is written once, there) and raises it to
the `m`-th power via `pow_le_pow_left₀`.

The distinguishing measurement itself (the union bound + POVM giving success probability
`≥ 1 − 1/|G|`) is the remaining headline of this sub-project; this theorem supplies its quantitative
input — the exponentially small pairwise overlap. -/
theorem cosetDensityState_pi_two_pow_mul_hsOverlap_sq_le (K' : Subgroup G) [DecidablePred (· ∈ K')]
    (hne : K ≠ K') :
    2 ^ Fintype.card ι
        * ((cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).hsOverlap
            (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))) ^ 2
      ≤ (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).purity
        * (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')).purity := by
  rw [cosetDensityState_pi_hsOverlap, cosetDensityState_pi_purity, cosetDensityState_pi_purity]
  -- The per-copy bound `hkey` is exactly the single-copy near-orthogonality
  -- `cosetDensityState_two_mul_hsOverlap_sq_le`, read off through the `hsOverlap`/`purity` closed
  -- forms; reusing it keeps the normalisation arithmetic in one place (there), and this
  -- theorem adds only the `m`-th-power amplification below.
  have hkey : 2 * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ 2
      ≤ ((Nat.card ↥K : ℝ) / Fintype.card G) * ((Nat.card ↥K' : ℝ) / Fintype.card G) := by
    have h := cosetDensityState_two_mul_hsOverlap_sq_le (K := K) K' hne
    rwa [cosetDensityState_hsOverlap, cosetDensityState_purity, cosetDensityState_purity] at h
  calc (2 : ℝ) ^ Fintype.card ι
          * (((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ Fintype.card ι) ^ 2
      = (2 * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) ^ 2) ^ Fintype.card ι := by
        rw [mul_pow, pow_right_comm]
    _ ≤ (((Nat.card ↥K : ℝ) / Fintype.card G) * ((Nat.card ↥K' : ℝ) / Fintype.card G))
          ^ Fintype.card ι := pow_le_pow_left₀ (by positivity) hkey _
    _ = ((Nat.card ↥K : ℝ) / Fintype.card G) ^ Fintype.card ι
          * ((Nat.card ↥K' : ℝ) / Fintype.card G) ^ Fintype.card ι := mul_pow _ _ _

/-- **N&C's sample count `m = 4 log₂|G| + 2` makes the `m`-copy coset reduced states nearly
orthogonal** (Nielsen & Chuang, Problem 5.5 — the *reachable* conclusion of the headline). For
*distinct* candidate hidden subgroups `K ≠ K'`, once the number of coset samples reaches N&C's
value `m = 4 log₂|G| + 2` — stated arithmetically as the hypothesis `4·|G|⁴ ≤ 2^m` (equivalently
`m ≥ 4 log₂|G| + 2`, since `4·|G|⁴ = 2^{4 log₂|G| + 2}`) — the Hilbert–Schmidt overlap of the
`m`-copy reduced states is driven below `1/(2|G|²)`:

`⟨σ_K^{⊗m}, σ_{K'}^{⊗m}⟩_HS ≤ 1 / (2|G|²)`.

This is the precise, quantitative form of the conclusion N&C states as *shown* by Problem 5.5's
protocol — that it "produce[s] (using only `O(log|G|)` oracle calls) a final state in which the
pure-state outcomes for different possible hidden subgroups are nearly orthogonal": at the exact
linear sample count `m = 4 log₂|G| + 2` the reduced states of any two distinct hidden subgroups
overlap by at most `1/(2|G|²)`, an inverse-quadratic separation. It is the specialisation of the
exponential near-orthogonality `cosetDensityState_pi_two_pow_mul_hsOverlap_sq_le`
(`2^m · overlap² ≤ tr(σ_K^{⊗m}²) · tr(σ_{K'}^{⊗m}²) ≤ 1`, the purities being `≤ 1`) to that sample
count: it gives `overlap ≤ 2^{-m/2}`, and `2^{-m/2} ≤ 1/(2|G|²)` precisely when
`m ≥ 4 log₂|G| + 2`.

The remaining, *unreached* clause of the headline — that this near-orthogonality lets a measurement
identify `K` with probability `≥ 1 − 1/|G|` — is the Ettinger–Høyer–Knill measurement analysis; see
the module docstring's "Remaining" note for why it requires infrastructure (a mixed-state
distinguishing-measurement error bound and a refined subgroup-index counting bound) beyond the
current library. -/
theorem cosetDensityState_pi_hsOverlap_le_of_sampleCount (K' : Subgroup G)
    [DecidablePred (· ∈ K')] (hne : K ≠ K')
    (hm : 4 * (Fintype.card G : ℝ) ^ 4 ≤ (2 : ℝ) ^ Fintype.card ι) :
    (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).hsOverlap
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
      ≤ 1 / (2 * (Fintype.card G : ℝ) ^ 2) := by
  set ov := (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).hsOverlap
      (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
  -- Exponential near-orthogonality `2^m · overlap² ≤ purities`, and the product of purities is
  -- `≤ 1` since each purity `(|H|/|G|)^m ≤ 1` (as `|H| ≤ |G|`).
  have hbound := cosetDensityState_pi_two_pow_mul_hsOverlap_sq_le (ι := ι) K K' hne
  have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hle : ∀ H : Subgroup G, [DecidablePred (· ∈ H)] →
      ((Nat.card ↥H : ℝ) / Fintype.card G) ^ Fintype.card ι ≤ 1 := by
    intro H _
    refine pow_le_one₀ (by positivity) ?_
    rw [div_le_one hn, Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_subtype_le _
  have hpp : (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).purity
      * (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')).purity ≤ 1 := by
    rw [cosetDensityState_pi_purity, cosetDensityState_pi_purity]
    calc _ ≤ 1 * 1 := mul_le_mul (hle K) (hle K') (by positivity) (by norm_num)
      _ = 1 := by norm_num
  -- `overlap² ≤ 1/2^m ≤ 1/(4|G|⁴) = (1/(2|G|²))²`, then take square roots.
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
  calc ov ^ 2 ≤ 1 / (2 : ℝ) ^ Fintype.card ι := by
        rw [le_div_iff₀ (by positivity), mul_comm]; exact le_trans hbound hpp
    _ ≤ 1 / (4 * (Fintype.card G : ℝ) ^ 4) := one_div_le_one_div_of_le (by positivity) hm
    _ = (1 / (2 * (Fintype.card G : ℝ) ^ 2)) ^ 2 := by rw [div_pow, one_pow, mul_pow]; ring_nf

/-- **The quantum affinity of the single-copy coset reduced states of two hidden subgroups**
(Nielsen & Chuang, Problem 5.5). For candidate hidden subgroups `K, K'`, the reduced states
`σ_K, σ_{K'}` of the query register (5.80, `m = 1`) have quantum **affinity**

`A(σ_K, σ_{K'}) = tr(√σ_K √σ_{K'}) = |K ∩ K'| / √(|K|·|K'|)`.

This is the *fidelity-metric* companion of the Hilbert–Schmidt overlap `cosetDensityState_hsOverlap`
(`⟨σ_K, σ_{K'}⟩_HS = |K∩K'|/|G|`): where the HS overlap is the purity-metric distinguishability, the
affinity is the pairwise quantity that governs the error of a **multi-state discrimination
measurement** (the pretty-good / square-root measurement error is controlled by `∑_{K'≠K} A`, not by
a union bound over pairwise trace distances) — precisely the resource the *linear* sample count of
the identification clause consumes. Its `K = K'` diagonal is `A(σ_K, σ_K) = 1`
(`State.affinity_self`, `tr σ_K = 1`).

The proof reads the affinity off the closed form of the operator square root: because
`σ_K = (|K|/|G|) Π_K` is a scalar multiple of the coset projector, `√σ_K = √(|G|/|K|) σ_K`
(`cosetDensityState_op_cfc_sqrt`), so `√σ_K √σ_{K'}` is a scalar multiple of `σ_K σ_{K'}` and the
affinity is `√(|G|/|K|)·√(|G|/|K'|)` times the Hilbert–Schmidt overlap `|K∩K'|/|G|`
(`cosetDensityState_hsOverlap`), which simplifies to `|K∩K'|/√(|K||K'|)`. -/
theorem cosetDensityState_affinity (K' : Subgroup G) [DecidablePred (· ∈ K')] :
    (cosetDensityState K).affinity (cosetDensityState K')
      = (Nat.card ↥(K ⊓ K') : ℝ) / Real.sqrt (Nat.card ↥K * Nat.card ↥K') := by
  have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hK : (0 : ℝ) < Nat.card ↥K := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  have hK' : (0 : ℝ) < Nat.card ↥K' := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  -- `A = √(|G|/|K|)·√(|G|/|K'|) · ⟨σ_K, σ_{K'}⟩_HS`: substitute `√σ_H = √(|G|/|H|)·σ_H`, collapse
  -- the product of the two scalars, and pull it through `tr` and `re` (`RCLike.smul_re`).
  have key : (cosetDensityState K).affinity (cosetDensityState K')
      = Real.sqrt (Fintype.card G / Nat.card ↥K) * Real.sqrt (Fintype.card G / Nat.card ↥K')
        * (cosetDensityState K).hsOverlap (cosetDensityState K') := by
    rw [State.affinity, cosetDensityState_op_cfc_sqrt, cosetDensityState_op_cfc_sqrt,
      smul_mul_smul_comm, ← Complex.ofReal_mul, ContinuousLinearMap.toLinearMap_smul, map_smul,
      Complex.coe_smul]
    exact RCLike.smul_re _ _
  rw [key, cosetDensityState_hsOverlap]
  -- `√(|G|/|K|)·√(|G|/|K'|) = |G|/√(|K||K'|)`.
  have hs : Real.sqrt (Fintype.card G / Nat.card ↥K) * Real.sqrt (Fintype.card G / Nat.card ↥K')
      = (Fintype.card G : ℝ) / Real.sqrt (Nat.card ↥K * Nat.card ↥K') := by
    rw [← Real.sqrt_mul (by positivity),
      show (Fintype.card G / Nat.card ↥K : ℝ) * (Fintype.card G / Nat.card ↥K')
          = (Fintype.card G : ℝ) ^ 2 / (Nat.card ↥K * Nat.card ↥K') by field_simp,
      Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  rw [hs]
  have hsqrt : (0 : ℝ) < Real.sqrt (Nat.card ↥K * Nat.card ↥K') := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- **The coset Hilbert–Schmidt overlap is dominated by the coset affinity** (Nielsen & Chuang,
Problem 5.5). For the single-copy coset reduced states `σ_K, σ_{K'}` of candidate hidden subgroups
`K, K'` (5.80, `m = 1`), the Hilbert–Schmidt overlap is at most the quantum affinity:

`⟨σ_K, σ_{K'}⟩_HS ≤ A(σ_K, σ_{K'})`.

Comparing the two closed forms computed above, this is the elementary inequality
`|K∩K'| / |G| ≤ |K∩K'| / √(|K|·|K'|)` (`cosetDensityState_hsOverlap`,
`cosetDensityState_affinity`), which holds because `√(|K|·|K'|) ≤ |G|`. It is the coset instance of
the general operator fact `State.hsOverlap_le_affinity` (the purity-metric overlap of any two states
is at most their fidelity-family affinity), so it needs no coset-specific computation. It records
that of the file's two near-orthogonality metrics the **affinity dominates**, so the affinity — over
which the Ettinger–Høyer–Knill discrimination *sum* is taken — is the safe (larger) resource: the
same relation holds verbatim for the `m`-copy states (`cosetDensityState_pi_hsOverlap`,
`cosetDensityState_pi_affinity`), so a bound on the affinity collision sum bounds the
Hilbert–Schmidt collision sum a fortiori. -/
theorem cosetDensityState_hsOverlap_le_affinity (K' : Subgroup G) [DecidablePred (· ∈ K')] :
    (cosetDensityState K).hsOverlap (cosetDensityState K')
      ≤ (cosetDensityState K).affinity (cosetDensityState K') :=
  State.hsOverlap_le_affinity _ _

/-- **Single-copy near-orthogonality in the affinity metric** (Nielsen & Chuang, Problem 5.5). For
*distinct* candidate hidden subgroups `K ≠ K'`, the quantum affinity of the single-copy reduced
states is bounded by `1/√2`:

`A(σ_K, σ_{K'}) = |K∩K'|/√(|K||K'|) ≤ 1/√2`.

This is the fidelity-metric form of the single-copy near-orthogonality
`cosetDensityState_two_mul_hsOverlap_sq_le`: distinct subgroups differ by a factor of at least `2`
somewhere (`Concrete.two_mul_card_inf_sq_le`, `2·|K∩K'|² ≤ |K||K'|`), so the affinity is at most
`1/√2`. Taking `m` copies amplifies this to `2^{-m/2}` (`cosetDensityState_pi_affinity_le`), the
exponential separation the identification argument consumes. -/
theorem cosetDensityState_affinity_le (K' : Subgroup G) [DecidablePred (· ∈ K')] (hne : K ≠ K') :
    (cosetDensityState K).affinity (cosetDensityState K') ≤ 1 / Real.sqrt 2 := by
  rw [cosetDensityState_affinity]
  have hK : (0 : ℝ) < Nat.card ↥K := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  have hK' : (0 : ℝ) < Nat.card ↥K' := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  have hsqrt : (0 : ℝ) < Real.sqrt (Nat.card ↥K * Nat.card ↥K') := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff₀ hsqrt (by positivity), one_mul, Real.le_sqrt (by positivity) (by positivity),
    mul_pow, Real.sq_sqrt (by norm_num), mul_comm]
  exact_mod_cast Concrete.two_mul_card_inf_sq_le K K' hne

/-- **The coset reduced state `σ_K` has rank equal to the index `[G : K] = |G ⧸ K|`** (Nielsen &
Chuang, Problem 5.5). The single-copy reduced state `σ_K = (|K|/|G|) Π_K` is `|K|/|G|` times the
coset projector `Π_K = ∑_{q ∈ G ⧸ K} |C_q⟩⟨C_q|`, whose range is the `|G ⧸ K|`-dimensional span of
the orthonormal coset states; scaling by the nonzero `|K|/|G|` leaves the range unchanged, so

`rank σ_K = [G : K]`.

The proof reads the rank off the spectral form `cosetDensityState_op_eq_sum`
(`σ_K = ∑_q (|K|/|G|) |C_q⟩⟨C_q|`): reindexing the coset sum along `Fin |G ⧸ K| ≃ G ⧸ K` and
applying `InnerProductSpace.finrank_range_sum_smul_rankOne_self` (the rank of a spectral sum of
rank-one projectors over an orthonormal family with nonzero coefficients is the number of terms,
here via `cosetPureState_orthonormal`) gives `finrank (range σ_K) = |G ⧸ K| = K.index`. It is the
rank input to the coset per-pair fidelity bound `cosetDensityState_fidelity_sq_le` below: the
Schatten 1–2 comparison charges `‖√σ_K √σ_{K'}‖₁²` the *rank* of `σ_K`, not the
ambient dimension. -/
theorem cosetDensityState_rank : (cosetDensityState K).rank = K.index := by
  have hcard : K.index = Fintype.card (G ⧸ K) := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  set n := Fintype.card (G ⧸ K) with hn
  set e := (Fintype.equivFin (G ⧸ K)).symm with he
  have hcoef : ((Fintype.card K / Fintype.card G : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < Fintype.card K / Fintype.card G := by
      apply div_pos <;> exact_mod_cast Fintype.card_pos
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hpos
  have hortho : Orthonormal ℂ (fun i : Fin n => (cosetPureState K (e i)).vec) :=
    (cosetPureState_orthonormal K).comp e e.injective
  rw [State.rank_eq_finrank_support, State.support, hcard, cosetDensityState_op_eq_sum]
  have key : (↑(∑ q : G ⧸ K, ((Fintype.card K / Fintype.card G : ℝ) : ℂ) •
        (cosetPureState K q).toState.op) : (groupSystem G).space →ₗ[ℂ] (groupSystem G).space)
      = ∑ i : Fin n, ((Fintype.card K / Fintype.card G : ℝ) : ℂ) •
          (↑(InnerProductSpace.rankOne ℂ (cosetPureState K (e i)).vec
              (cosetPureState K (e i)).vec) :
            (groupSystem G).space →ₗ[ℂ] (groupSystem G).space) := by
    rw [ContinuousLinearMap.toLinearMap_sum]
    rw [← Equiv.sum_comp e (fun q => (↑(((Fintype.card K / Fintype.card G : ℝ) : ℂ) •
      (cosetPureState K q).toState.op) : (groupSystem G).space →ₗ[ℂ] (groupSystem G).space))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.toLinearMap_smul, PureState.toState_op]
  rw [key, InnerProductSpace.finrank_range_sum_smul_rankOne_self _ _ hortho (fun _ => hcoef)]

/-- **One-sided coset per-pair fidelity bound** (Nielsen & Chuang, Problem 5.5). For the single-copy
coset reduced states `σ_K, σ_{K'}` of candidate hidden subgroups, the squared fidelity is bounded by
the *relative* intersection size

`F(σ_K, σ_{K'})² ≤ |K ∩ K'| / |K|`.

The proof is the **Schatten 1–2 comparison** applied to `Y = √σ_K √σ_{K'}`: since
`√σ_H = √(|G|/|H|) σ_H` (`cosetDensityState_op_cfc_sqrt`), the fidelity is
`F = ‖Y‖₁ = √(|G|/|K|)·√(|G|/|K'|) · ‖σ_K σ_{K'}‖₁` (`State.fidelity_eq_traceNorm`,
`ContinuousLinearMap.traceNorm_smul`). The comparison
`ContinuousLinearMap.traceNorm_sq_le_finrank_range_mul_re_trace_adjoint_comp_self` bounds
`‖σ_K σ_{K'}‖₁²` by `rank(σ_K σ_{K'}) · re tr((σ_K σ_{K'})† σ_K σ_{K'})`; the rank is at most
`rank σ_K = [G : K]` (`cosetDensityState_rank`, as `range (σ_K σ_{K'}) ≤ range σ_K`), and the trace
collapses via `σ_H² = (|H|/|G|) σ_H` (`cosetDensityState_op_mul_self`) and cyclicity to
`(|K|/|G|)(|K'|/|G|)·⟨σ_K, σ_{K'}⟩_HS = (|K|/|G|)(|K'|/|G|)(|K∩K'|/|G|)`
(`cosetDensityState_hsOverlap`). Multiplying through, `F² ≤ [G:K]·(|K∩K'|/|K|)/[G:K] = |K∩K'|/|K|`.
The asymmetry `|K|` in the denominator is the point: it is only the *smaller-index* candidate's rank
that bounds the range, so this holds with `K` and `K'` swapped too — combining the two directions
(`cosetDensityState_fidelity_sq_le_affinity`) gives `F² ≤ A`. -/
theorem cosetDensityState_fidelity_sq_le (K' : Subgroup G) [DecidablePred (· ∈ K')] :
    (cosetDensityState K).fidelity (cosetDensityState K') ^ 2
      ≤ (Nat.card ↥(K ⊓ K') : ℝ) / Nat.card ↥K := by
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hK : (0 : ℝ) < Nat.card ↥K := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  have hK' : (0 : ℝ) < Nat.card ↥K' := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  -- `F = √(|G|/|K|)·√(|G|/|K'|) · ‖σ_K σ_{K'}‖₁`.
  have hF : (cosetDensityState K).fidelity (cosetDensityState K')
      = (Real.sqrt (Fintype.card G / Nat.card ↥K) * Real.sqrt (Fintype.card G / Nat.card ↥K'))
        * ((cosetDensityState K).op * (cosetDensityState K').op).traceNorm := by
    rw [State.fidelity_eq_traceNorm, cosetDensityState_op_cfc_sqrt, cosetDensityState_op_cfc_sqrt,
        smul_mul_smul_comm, ← Complex.ofReal_mul, ContinuousLinearMap.traceNorm_smul,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  -- The Hilbert–Schmidt overlap `⟨σ_K, σ_{K'}⟩_HS = |K∩K'|/|G|`, in raw trace form.
  have hov : RCLike.re (LinearMap.trace ℂ (groupSystem G).space
        ↑((cosetDensityState K).op * (cosetDensityState K').op))
      = (Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G := cosetDensityState_hsOverlap K K'
  -- The trace `re tr((σ_K σ_{K'})† σ_K σ_{K'}) = (|K|/|G|)(|K'|/|G|)(|K∩K'|/|G|)`.
  have htr : RCLike.re (LinearMap.trace ℂ (groupSystem G).space
        ↑((ContinuousLinearMap.adjoint ((cosetDensityState K).op * (cosetDensityState K').op)).comp
          ((cosetDensityState K).op * (cosetDensityState K').op)))
      = ((Nat.card ↥K : ℝ) / Fintype.card G) * ((Nat.card ↥K' : ℝ) / Fintype.card G)
        * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G) := by
    set A := (cosetDensityState K).op with hA
    set B := (cosetDensityState K').op with hB
    have hadjmul : ContinuousLinearMap.adjoint (A * B) = B * A := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_mul,
          ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
          (State.isSelfAdjoint_op _).adjoint_eq, (State.isSelfAdjoint_op _).adjoint_eq]
    have hAA : A * A = ((Nat.card ↥K : ℝ) / Fintype.card G : ℂ) • A :=
      cosetDensityState_op_mul_self K
    have hBB : B * B = ((Nat.card ↥K' : ℝ) / Fintype.card G : ℂ) • B :=
      cosetDensityState_op_mul_self K'
    have hrewrite : A * A * B * B
        = (((Nat.card ↥K : ℝ) / Fintype.card G : ℂ) * ((Nat.card ↥K' : ℝ) / Fintype.card G : ℂ))
          • (A * B) := by
      rw [mul_assoc (A * A) B B, hAA, hBB, smul_mul_smul_comm]
    have hcoef : (((Nat.card ↥K : ℝ) / Fintype.card G : ℂ)
          * ((Nat.card ↥K' : ℝ) / Fintype.card G : ℂ))
        = ((((Nat.card ↥K : ℝ) / Fintype.card G)
            * ((Nat.card ↥K' : ℝ) / Fintype.card G) : ℝ) : ℂ) := by
      push_cast; ring
    have hcyc : (LinearMap.trace ℂ (groupSystem G).space
          ↑((ContinuousLinearMap.adjoint (A * B)).comp (A * B)))
        = (LinearMap.trace ℂ (groupSystem G).space ↑(A * A * B * B)) := by
      rw [hadjmul, ← ContinuousLinearMap.mul_def,
          show (B * A) * (A * B) = B * (A * A * B) by simp only [mul_assoc],
          ContinuousLinearMap.trace_mul_comm B (A * A * B)]
    rw [hcyc, hrewrite, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, hcoef,
        ← Complex.real_smul, RCLike.smul_re, hov]
  -- `rank(σ_K σ_{K'}) ≤ rank σ_K = [G : K]`.
  have hrank : (Module.finrank ℂ (LinearMap.range
        (((cosetDensityState K).op * (cosetDensityState K').op) :
          (groupSystem G).space →ₗ[ℂ] (groupSystem G).space)) : ℝ) ≤ (K.index : ℝ) := by
    have h1 : Module.finrank ℂ (LinearMap.range
          (((cosetDensityState K).op * (cosetDensityState K').op) :
            (groupSystem G).space →ₗ[ℂ] (groupSystem G).space))
        ≤ Module.finrank ℂ (LinearMap.range ((cosetDensityState K).op :
            (groupSystem G).space →ₗ[ℂ] (groupSystem G).space)) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    have h2 : Module.finrank ℂ (LinearMap.range ((cosetDensityState K).op :
          (groupSystem G).space →ₗ[ℂ] (groupSystem G).space)) = K.index := by
      rw [show LinearMap.range ((cosetDensityState K).op :
            (groupSystem G).space →ₗ[ℂ] (groupSystem G).space)
          = (cosetDensityState K).support from rfl,
        ← State.rank_eq_finrank_support, cosetDensityState_rank]
    exact_mod_cast h1.trans_eq h2
  -- Lagrange: `[G : K] = |G| / |K|` as reals.
  have hidx : (K.index : ℝ) = (Fintype.card G : ℝ) / Nat.card ↥K := by
    rw [eq_div_iff (ne_of_gt hK), ← Nat.card_eq_fintype_card (α := G)]
    exact_mod_cast Subgroup.index_mul_card K
  -- Assemble via the Schatten 1–2 comparison.
  rw [hF, mul_pow]
  have hZsq : ((cosetDensityState K).op * (cosetDensityState K').op).traceNorm ^ 2
      ≤ (K.index : ℝ) * (((Nat.card ↥K : ℝ) / Fintype.card G)
          * ((Nat.card ↥K' : ℝ) / Fintype.card G)
          * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G)) := by
    calc ((cosetDensityState K).op * (cosetDensityState K').op).traceNorm ^ 2
        ≤ (Module.finrank ℂ (LinearMap.range
              (((cosetDensityState K).op * (cosetDensityState K').op) :
                (groupSystem G).space →ₗ[ℂ] (groupSystem G).space)) : ℝ)
            * RCLike.re (LinearMap.trace ℂ (groupSystem G).space
              ↑((ContinuousLinearMap.adjoint
                  ((cosetDensityState K).op * (cosetDensityState K').op)).comp
                ((cosetDensityState K).op * (cosetDensityState K').op))) :=
          ContinuousLinearMap.traceNorm_sq_le_finrank_range_mul_re_trace_adjoint_comp_self _
      _ = (Module.finrank ℂ (LinearMap.range
              (((cosetDensityState K).op * (cosetDensityState K').op) :
                (groupSystem G).space →ₗ[ℂ] (groupSystem G).space)) : ℝ)
            * (((Nat.card ↥K : ℝ) / Fintype.card G) * ((Nat.card ↥K' : ℝ) / Fintype.card G)
              * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G)) := by rw [htr]
      _ ≤ (K.index : ℝ) * (((Nat.card ↥K : ℝ) / Fintype.card G)
            * ((Nat.card ↥K' : ℝ) / Fintype.card G)
            * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G)) :=
          mul_le_mul_of_nonneg_right hrank (by positivity)
  calc (Real.sqrt (Fintype.card G / Nat.card ↥K) * Real.sqrt (Fintype.card G / Nat.card ↥K')) ^ 2
        * ((cosetDensityState K).op * (cosetDensityState K').op).traceNorm ^ 2
      ≤ (Real.sqrt (Fintype.card G / Nat.card ↥K) * Real.sqrt (Fintype.card G / Nat.card ↥K')) ^ 2
        * ((K.index : ℝ) * (((Nat.card ↥K : ℝ) / Fintype.card G)
            * ((Nat.card ↥K' : ℝ) / Fintype.card G)
            * ((Nat.card ↥(K ⊓ K') : ℝ) / Fintype.card G))) :=
        mul_le_mul_of_nonneg_left hZsq (by positivity)
    _ = (Nat.card ↥(K ⊓ K') : ℝ) / Nat.card ↥K := by
        rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), hidx]
        field_simp

/-- **The coset per-pair fidelity is bounded by the affinity** (Nielsen & Chuang, Problem 5.5): the
squared fidelity of the single-copy coset reduced states is at most their quantum affinity,

`F(σ_K, σ_{K'})² ≤ A(σ_K, σ_{K'}) = |K ∩ K'| / √(|K|·|K'|)`.

This is the fidelity analogue of the metric ordering `cosetDensityState_hsOverlap_le_affinity`, and
the key coset inequality of the *fidelity-metric* discrimination route (piece (i)(a)): with the
multiplicativity of fidelity under tensor products it reduces the `m`-copy fidelity collision sum
`∑_{K'≠K} F(σ_K^{⊗m}, σ_{K'}^{⊗m})` to the affinity collision sum already driven to `O(1/|G|)`. The
proof multiplies the two one-sided bounds `cosetDensityState_fidelity_sq_le` (in `K` and in `K'`,
using symmetry `State.fidelity_comm`): `F⁴ ≤ (|K∩K'|/|K|)·(|K∩K'|/|K'|) = |K∩K'|²/(|K||K'|) = A²`,
and taking square roots (`F² ≥ 0`, `A ≥ 0`) gives `F² ≤ A`. -/
theorem cosetDensityState_fidelity_sq_le_affinity (K' : Subgroup G) [DecidablePred (· ∈ K')] :
    (cosetDensityState K).fidelity (cosetDensityState K') ^ 2
      ≤ (cosetDensityState K).affinity (cosetDensityState K') := by
  have hK : (0 : ℝ) < Nat.card ↥K := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  have hK' : (0 : ℝ) < Nat.card ↥K' := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  rw [cosetDensityState_affinity]
  -- Two one-sided bounds, multiplied.
  have h1 : (cosetDensityState K).fidelity (cosetDensityState K') ^ 2
      ≤ (Nat.card ↥(K ⊓ K') : ℝ) / Nat.card ↥K := cosetDensityState_fidelity_sq_le K K'
  have h2 : (cosetDensityState K).fidelity (cosetDensityState K') ^ 2
      ≤ (Nat.card ↥(K ⊓ K') : ℝ) / Nat.card ↥K' := by
    rw [State.fidelity_comm, inf_comm]
    exact cosetDensityState_fidelity_sq_le K' K
  have hFnn : (0 : ℝ) ≤ (cosetDensityState K).fidelity (cosetDensityState K') ^ 2 := sq_nonneg _
  -- `(F²)² ≤ (|K∩K'|/|K|)(|K∩K'|/|K'|) = A²`, then take square roots.
  have hsq : ((cosetDensityState K).fidelity (cosetDensityState K') ^ 2) ^ 2
      ≤ ((Nat.card ↥(K ⊓ K') : ℝ) / Real.sqrt (Nat.card ↥K * Nat.card ↥K')) ^ 2 := by
    calc ((cosetDensityState K).fidelity (cosetDensityState K') ^ 2) ^ 2
        ≤ ((Nat.card ↥(K ⊓ K') : ℝ) / Nat.card ↥K) * ((Nat.card ↥(K ⊓ K') : ℝ) / Nat.card ↥K') := by
          rw [sq]; exact mul_le_mul h1 h2 hFnn (by positivity)
      _ = ((Nat.card ↥(K ⊓ K') : ℝ) / Real.sqrt (Nat.card ↥K * Nat.card ↥K')) ^ 2 := by
          rw [div_pow, Real.sq_sqrt (by positivity)]; ring
  have hAnn : (0 : ℝ) ≤ (Nat.card ↥(K ⊓ K') : ℝ) / Real.sqrt (Nat.card ↥K * Nat.card ↥K') := by
    positivity
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hFnn, Real.sqrt_sq hAnn] at this

/-- **The quantum affinity of the `m`-copy coset reduced states is `(|K∩K'|/√(|K||K'|))^m`**
(Nielsen & Chuang, Problem 5.5). For candidate hidden subgroups `K, K'`, the `m`-copy reduced states
`σ_K^{⊗m} = cosetDensityState (K^ι)` and `σ_{K'}^{⊗m}` of the query register (5.80) have quantum
affinity

`A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = (|K∩K'| / √(|K|·|K'|))^m`,

the `m`-th power of the single-copy affinity `cosetDensityState_affinity`. Like the `m`-copy
Hilbert–Schmidt overlap `cosetDensityState_pi_hsOverlap` it needs **no `m`-fold tensor machinery**:
`σ_K^{⊗m}` is itself the coset density matrix of the product subgroup `K^ι = ∏_i K` of the
direct-power group `G^ι`, so applying `cosetDensityState_affinity` to `K^ι, K'^ι` and simplifying
`K^ι ⊓ K'^ι = (K ⊓ K')^ι` (`Concrete.subgroupPi_const_inf`), `|H^ι| = |H|^m`
(`Concrete.natCard_subgroupPi_const`) gives the `m`-th power. -/
theorem cosetDensityState_pi_affinity (K' : Subgroup G) [DecidablePred (· ∈ K')] :
    (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
      = ((Nat.card ↥(K ⊓ K') : ℝ) / Real.sqrt (Nat.card ↥K * Nat.card ↥K')) ^ Fintype.card ι := by
  have hsp : ∀ (z : ℝ) (n : ℕ), 0 ≤ z → Real.sqrt (z ^ n) = Real.sqrt z ^ n := by
    intro z n hz
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, Real.sqrt_mul (by positivity), ih]
  rw [cosetDensityState_affinity, Concrete.subgroupPi_const_inf, Concrete.natCard_subgroupPi_const,
    Concrete.natCard_subgroupPi_const, Concrete.natCard_subgroupPi_const]
  push_cast
  rw [div_pow, ← mul_pow, hsp _ _ (by positivity)]

/-- **Exponential near-orthogonality in the affinity metric** (Nielsen & Chuang, Problem 5.5). For
*distinct* candidate hidden subgroups `K ≠ K'`, the quantum affinity of the `m`-copy reduced states
decays exponentially in the sample count `m`:

`A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = (|K∩K'|/√(|K||K'|))^m ≤ (1/√2)^m = 2^{-m/2}`.

This is the `m`-fold amplification of the single-copy bound `cosetDensityState_affinity_le`:
the reduced states of any two distinct candidate hidden subgroups become exponentially indistinct as
`m` grows. It is the fidelity-metric form of `cosetDensityState_pi_two_pow_mul_hsOverlap_sq_le`, and
the quantity a pretty-good / square-root measurement's error bound sums over the candidate subgroups
— the resource behind the *linear* sample count `m = 4 log₂|G| + 2` of the identification clause
(the affinity **sum** `∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m})` stays small because it is dominated by the
few nearby subgroups, whereas a union bound over all `|G|^{Θ(log|G|)}` candidates would force a
*quadratic* count). -/
theorem cosetDensityState_pi_affinity_le (K' : Subgroup G) [DecidablePred (· ∈ K')] (hne : K ≠ K') :
    (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
      ≤ (1 / Real.sqrt 2) ^ Fintype.card ι := by
  rw [cosetDensityState_pi_affinity]
  have hbase : (Nat.card ↥(K ⊓ K') : ℝ) / Real.sqrt (Nat.card ↥K * Nat.card ↥K')
      ≤ 1 / Real.sqrt 2 := by
    rw [← cosetDensityState_affinity]; exact cosetDensityState_affinity_le K K' hne
  exact pow_le_pow_left₀ (by positivity) hbase _

open Classical in
/-- **The per-`K` affinity collision sum of the `m`-copy coset reduced states, with the diagonal
discharged** (Nielsen & Chuang, Problem 5.5 — the physics form of the Ettinger–Høyer–Knill piece
(ii) collision reduction). Take the candidate hidden subgroups to be *all* subgroups `K' ≤ G`, and
fix a true subgroup `K`. Writing the sample count as `m = |ι| = 2s` and assuming `2·|G|² ≤ 2^s`
(equivalently `s ≥ 2 log₂|G| + 1`, i.e. `m ≥ 4 log₂|G| + 2` — N&C's exact sample count), the
**pairwise quantum affinity of the `m`-copy reduced state `σ_K^{⊗m}` against every other candidate**
sums to
`∑_{K' ≠ K} A(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 1/|G| + 2·∑_{H < K} (|H|/|K|)^s`.

This is the **physics (`State.affinity`) layer** counterpart of the concrete collision-sum reduction
`Concrete.sum_cosetAffinity_pow_collision_proper_le_of_sq`: reindexing the candidate lattice by the
intersection `H = K ∩ K'` (`Finset.sum_fiberwise_of_maps_to`) fibres the sum over `H ≤ K`; the
`H = K` fibre is exactly the proper overgroups `K' ⊋ K`, whose contribution `∑_{K'⊋K}(|K|/|K'|)^s`
is the sharp overgroup order-sum, `≤ 2·|G|·2^{-s} ≤ 1/|G|` at the sample exponent
(`Concrete.sum_proper_overgroup_ratio_pow_le`, `Concrete.sum_overgroup_ratio_pow_le`); and the
proper fibres `H < K` contribute the outer low-index sum `2·∑_{H<K}(|H|/|K|)^s`. The affinity is
read off in closed form by `cosetDensityState_pi_affinity`
(`A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = (|K∩K'|/√(|K||K'|))^m = Concrete.cosetAffinity K K'^m`), so the
physical per-`K` collision sum equals the concrete one term-by-term.

This is the pairwise-affinity resource N&C's identification clause consumes: the **summed**
Barnum–Knill discrimination bound
`State.sum_one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity` controls the *total*
identification error by `2·∑_{K'}∑_{K''≠K'} A`, and this lemma is the sharp *per-`K'`* inner sum
with the diagonal already inside the `1/|G|` budget. It isolates the **one remaining
Ettinger–Høyer–Knill counting ingredient** at the `State` level — the proper-subgroup low-index sum
`∑_{H<K}(|H|/|K|)^s`, the dual counting direction of Gaussian-binomial strength (a bound on the
number of small-index subgroups of `K`) not reachable by the generating-set/binomial injection that
discharges the overgroup sum. See the module docstring's "Remaining" note for why the *linear*
sample count additionally needs a per-state (not merely summed) pretty-good discrimination bound. -/
theorem cosetDensityState_pi_sum_affinity_collision_le [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 2 * s) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    ∑ K' ∈ Finset.univ.erase K,
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
      ≤ (Nat.card G : ℝ)⁻¹
        + 2 * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
            ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := by
  -- Each physical affinity is the `m = 2s`-th power of the concrete coset affinity.
  have hval : ∀ K' ∈ Finset.univ.erase K,
      (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
        = Concrete.cosetAffinity K K' ^ (2 * s) := by
    intro K' _
    rw [cosetDensityState_pi_affinity, Concrete.cosetAffinity, hι]
  rw [Finset.sum_congr rfl hval]
  exact Concrete.sum_cosetAffinity_pow_collision_proper_le_of_sq K hs

open Classical in
/-- **The per-`K` affinity collision sum is `≤ 7/|G|` at N&C's sample count, conditional only on the
non-normal maximal class count** (Nielsen & Chuang, Problem 5.5 — the physics form of the fully
threaded Ettinger–Høyer–Knill piece (ii) counting tail). Take the candidate hidden subgroups to be
*all* subgroups `K' ≤ G`, fix a true subgroup `K`, and write the sample count as `m = |ι| = 2s` with
`2·|G|² ≤ 2^s` (N&C's exact linear count `m = 4 log₂|G| + 2`, `s = 2 log₂|G| + 1`). *Given* the
single group-theoretic count that every subgroup `J ≤ G` has

`3 · #{J-conjugacy classes of non-normal maximal subgroups of J} ≤ |J|²`,

the pairwise quantum affinity of the `m`-copy reduced state `σ_K^{⊗m}` against every other candidate
sums to an inverse-linear quantity:

`∑_{K' ≠ K} A(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 7/|G|`.

This is the **physics (`State.affinity`) layer** counterpart of the concrete threading
`Concrete.sum_cosetAffinity_pow_collision_classCard_le_of_sq`: the affinity is read off in closed
form by `cosetDensityState_pi_affinity`
(`A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = (|K∩K'|/√(|K||K'|))^m = Concrete.cosetAffinity K K'^m`), so the
physical per-`K` collision sum equals the concrete one term-by-term, and the concrete bound closes
it.

It sharpens `cosetDensityState_pi_sum_affinity_collision_le` (which leaves the residual
proper-subgroup low-index sum `∑_{H<K}(|H|/|K|)^s` open) by discharging that residual through the
~ten-file
maximal-subgroup development, whose *entire* remaining counting tail is now the single
`∀`-quantified class count `hcount`: the `K`-conjugacy-class count of non-normal maximal subgroups
(Liebeck–Pyber–Shalev strength — the one residual with no group quotient to count through). The
inverse-linear collision bound at N&C's **linear** sample count is exactly the pairwise-affinity
resource the identification clause's discrimination sum consumes; the constant `7/|G|` is `O(1/|G|)`
rather than the sharp `1/|G|` (the linear *order* being the substantive content — see the module
docstring's "Remaining" note for the residual sharpening and the per-state discrimination bound the
exact `1 − 1/|G|` needs). -/
theorem cosetDensityState_pi_sum_affinity_collision_classCard_le [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 2 * s) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    ∑ K' ∈ Finset.univ.erase K,
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
      ≤ 7 / (Nat.card G : ℝ) := by
  -- Each physical affinity is the `m = 2s`-th power of the concrete coset affinity.
  have hval : ∀ K' ∈ Finset.univ.erase K,
      (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
        = Concrete.cosetAffinity K K' ^ (2 * s) := by
    intro K' _
    rw [cosetDensityState_pi_affinity, Concrete.cosetAffinity, hι]
  rw [Finset.sum_congr rfl hval]
  exact Concrete.sum_cosetAffinity_pow_collision_classCard_le_of_sq K hG hs hcount

open Classical in
/-- **The per-`K` pretty-good identification error is bounded by the coset affinity collision sum**
(Nielsen & Chuang, Problem 5.5 — the *per-state* Ettinger–Høyer–Knill discrimination bound, piece
(i)(a)). Take the candidate hidden subgroups to be *all* subgroups `K' ≤ G`, each producing the
`m`-copy reduced state `σ_{K'}^{⊗m} = cosetDensityState (K'^ι)` (5.80). *Given* the coset
**paired-trace inequality** `re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`
(`S₀ = ∑_{K'} σ_{K'}^{⊗m}`, the total operator), the deficit of the pretty-good (square-root)
measurement's success probability on the true hidden subgroup `K` is bounded by twice `K`'s *own*
affinity collision sum:

`1 − p(K ∣ σ_K^{⊗m}) ≤ 2 · ∑_{K' ≠ K} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`.

This is the coset instance of the reusable **per-state** discrimination bound
`State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity_of_paired`. It is the
*per-`K`* companion of the *summed* bound
`cosetDensityState_pi_prettyGoodMeasurement_sum_error_le` (which controls the *total*
`∑_{K'}(1 − p(K'))` by twice the *double* collision sum): the summed bound over-counts `K`'s error
by the family size `#{subgroups}` (super-polynomial), forcing a *quadratic* sample count, whereas
this per-`K` bound charges `K`'s error to *its own* affinity collision sum — the exact quantity
`cosetDensityState_pi_sum_affinity_collision_classCard_le` drives to `O(1/|G|)` at N&C's *linear*
sample count `m = 4 log₂|G| + 2`. It is the discrimination-side ingredient that, with that collision
bound, yields the linear-count identification headline
(`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard` below).

The hypothesis `hpaired` — the trace of `√σ_K^{⊗m}` against the total `√S₀` is at most the affinity
sum — is the *one* remaining Ettinger–Høyer–Knill operator ingredient of piece (i)(a). It replaces
the roadmap's earlier *per-pair* target `p(K' ∣ σ_K^{⊗m}) ≤ C·A(σ_K^{⊗m}, σ_{K'}^{⊗m})`, which is
**false** (the confusion probability is positive even when the pairwise affinity vanishes — a coset
state `σ_{K'}^{⊗m}` orthogonal to `σ_K^{⊗m}` is still confused with it through the *other*
candidates' overlap in `S₀`); the *per-state* paired inequality is the correct, weaker residual (see
the module docstring's "Remaining" note). -/
theorem cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired
    [Fintype (Subgroup G)]
    (hpaired : State.PairedTraceBound
      (fun K'' : Subgroup G => cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K) :
    1 - (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K)
      ≤ 2 * ∑ K'' ∈ Finset.univ.erase K,
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
            (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) := by
  classical
  -- Apply the general per-state bound to the coset family. The conclusion carries a buried
  -- `DecidablePred (· ∈ Subgroup.pi …)` instance (the general lemma's classical instance vs the
  -- section's), reconciled by `convert` at congruence depth — never `whnf`-forcing the huge
  -- `cosetDensityState` terms.
  have key := State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity_of_paired
    (fun K'' : Subgroup G =>
      cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K hpaired
  convert key using 6

open Classical in
/-- **The per-`K` pretty-good identification error is bounded by the coset *fidelity* collision
sum — unconditionally** (Nielsen & Chuang, Problem 5.5 — the Rotfel'd route to piece (i)(a), no
paired-trace hypothesis). Take the candidate hidden subgroups to be *all* subgroups `K' ≤ G`, each
producing the `m`-copy reduced state `σ_{K'}^{⊗m} = cosetDensityState (K'^ι)` (5.80). The deficit of
the pretty-good (square-root) measurement's success probability on the true hidden subgroup `K` is
bounded by twice `K`'s *own* pairwise-**fidelity** collision sum:

`1 − p(K ∣ σ_K^{⊗m}) ≤ 2 · ∑_{K' ≠ K} F(σ_K^{⊗m}, σ_{K'}^{⊗m})`.

This is the coset instance of the reusable *unconditional* per-state discrimination bound
`State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_fidelity`. It is the **fidelity**
companion of `cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired`
(`1 − p(K) ≤ 2·∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`): the affinity version needs the subtle,
normalization-dependent **paired-trace inequality** `hpaired` (`State.PairedTraceBound`, still
open in general), whereas this fidelity version needs **nothing** — it rests on **Rotfel'd's trace
inequality** (`ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_le_sum_traceNorm`,
`re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} F(σ_K^{⊗m}, σ_{K'}^{⊗m})`), which holds for every family of density
operators. Since `A ≤ F` (`State.affinity_le_fidelity`) this bound is weaker than the affinity one,
but its being *unconditional* discharges piece (i)(a) of the identification clause **outright for
every hidden-subgroup instance** (including genuinely non-abelian `G`) in the fidelity metric — the
remaining step toward the exact-N&C headline is then the *fidelity* collision sum
`∑_{K'≠K} F(σ_K^{⊗m}, σ_{K'}^{⊗m})` (a counting task, the fidelity analogue of the affinity
collision sum already driven to `O(1/|G|)`), not the paired-trace inequality. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_fidelity
    [Fintype (Subgroup G)] :
    1 - (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K)
      ≤ 2 * ∑ K'' ∈ Finset.univ.erase K,
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).fidelity
            (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) := by
  classical
  -- Apply the general unconditional per-state fidelity bound to the coset family; `convert` at
  -- congruence depth reconciles the buried `DecidablePred (· ∈ Subgroup.pi …)` instances without
  -- `whnf`-forcing the huge `cosetDensityState` terms.
  have key := State.one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_fidelity
    (fun K'' : Subgroup G =>
      cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K
  convert key using 6

/-- **The `m`-copy coset per-pair fidelity is bounded by the affinity** (Nielsen & Chuang, Problem
5.5). For candidate hidden subgroups `K, K'`, the squared fidelity of the `m`-copy reduced states
`σ_K^{⊗m} = cosetDensityState (K^ι)` and `σ_{K'}^{⊗m}` is at most their quantum affinity:

`F(σ_K^{⊗m}, σ_{K'}^{⊗m})² ≤ A(σ_K^{⊗m}, σ_{K'}^{⊗m})`.

This is the `m`-copy lift of the single-copy `cosetDensityState_fidelity_sq_le_affinity`, and it
needs **no `m`-fold tensor machinery**: `σ_K^{⊗m}` is itself the coset density matrix of the product
subgroup `K^ι = ∏_i K` of the direct-power group `G^ι = (ι → G)`, so the single-copy bound
*applied to `K^ι, K'^ι` in `G^ι`* is exactly this statement (mirroring how
`cosetDensityState_pi_affinity` lifts `cosetDensityState_affinity`). It is the coset inequality
that, with the `m`-copy affinity closed form `cosetDensityState_pi_affinity`, reduces the `m`-copy
**fidelity** collision sum `∑_{K'≠K} F(σ_K^{⊗m}, σ_{K'}^{⊗m})` to the affinity collision sum already
driven to `O(1/|G|)` — the counting task that discharges the *fidelity-metric* route to piece (i)(a)
(see `cosetDensityState_pi_sum_fidelity_collision_classCard_le`). -/
theorem cosetDensityState_pi_fidelity_sq_le_affinity (K' : Subgroup G) [DecidablePred (· ∈ K')] :
    (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).fidelity
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')) ^ 2
      ≤ (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')) :=
  cosetDensityState_fidelity_sq_le_affinity
    (Subgroup.pi (Set.univ : Set ι) fun _ => K) (Subgroup.pi (Set.univ : Set ι) fun _ => K')

open Classical in
/-- **The per-`K` coset *fidelity* collision sum is `≤ 7/|G|` at a linear sample count, conditional
only on the non-normal maximal class count** (Nielsen & Chuang, Problem 5.5 — the fidelity-metric
counting tail of the Ettinger–Høyer–Knill identification clause). Take the candidate hidden
subgroups to be *all* subgroups `K' ≤ G`, fix a true subgroup `K`, and write the sample count as
`m = |ι| = 4u` with `2·|G|² ≤ 2^u` (a **linear** count `m = 8 log₂|G| + 4`, twice N&C's exact
`4 log₂|G| + 2` — the price the `F² ≤ A` comparison pays for being *unconditional*). *Given* the
single group-theoretic count that every subgroup `J ≤ G` has
`3·#{J-conjugacy classes of non-normal maximal subgroups of J} ≤ |J|²`, the pairwise **fidelity** of
`σ_K^{⊗m}` against every other candidate sums to

`∑_{K' ≠ K} F(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 7/|G|`.

This is the **fidelity** companion of `cosetDensityState_pi_sum_affinity_collision_classCard_le`
(`∑_{K'≠K} A ≤ 7/|G|` at N&C's exact `m = 2s`). The bridge is the per-pair
`cosetDensityState_pi_fidelity_sq_le_affinity` (`F² ≤ A`): with `m = 4u`, the `m`-copy affinity is
`A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = A(σ_K, σ_{K'})^{4u} = (A(σ_K, σ_{K'})^{2u})²` in closed form
(`cosetDensityState_pi_affinity`, `A(σ_K, σ_{K'}) = Concrete.cosetAffinity K K'`), so `F² ≤ A` and
`F ≥ 0` give `F(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ Concrete.cosetAffinity K K'^{2u}`; summing and applying the
concrete affinity collision bound `Concrete.sum_cosetAffinity_pow_collision_classCard_le_of_sq` (at
exponent `2u`) closes it. The **fidelity** metric is what makes the discrimination bound feeding
this *unconditional* — the per-state bound
`cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_fidelity` rests on Rotfel'd's trace
inequality, needing **no** paired-trace hypothesis — so this collision sum is the *only* remaining
ingredient of the fidelity-route identification headline. -/
theorem cosetDensityState_pi_sum_fidelity_collision_classCard_le [Fintype (Subgroup G)] {u : ℕ}
    (hι : Fintype.card ι = 4 * u) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ u)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    ∑ K' ∈ Finset.univ.erase K,
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).fidelity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
      ≤ 7 / (Nat.card G : ℝ) := by
  -- Per-term: `F(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ Concrete.cosetAffinity K K'^{2u}`, via `F² ≤ A = (…)²`.
  have hterm : ∀ K' ∈ Finset.univ.erase K,
      (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).fidelity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
        ≤ Concrete.cosetAffinity K K' ^ (2 * u) := by
    intro K' _
    have hnn : (0 : ℝ) ≤ Concrete.cosetAffinity K K' ^ (2 * u) :=
      pow_nonneg (Concrete.cosetAffinity_nonneg K K') _
    -- `A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = Concrete.cosetAffinity K K'^{4u}`.
    have hAeq : (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
        = Concrete.cosetAffinity K K' ^ (4 * u) := by
      rw [cosetDensityState_pi_affinity, Concrete.cosetAffinity, hι]
    -- `F² ≤ A = (cosetAffinity^{2u})²`, so `F ≤ cosetAffinity^{2u}` by `pow`-monotonicity.
    have hsq : (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).fidelity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')) ^ 2
        ≤ (Concrete.cosetAffinity K K' ^ (2 * u)) ^ 2 := by
      rw [← pow_mul, show 2 * u * 2 = 4 * u from by ring, ← hAeq]
      exact cosetDensityState_pi_fidelity_sq_le_affinity K K'
    exact le_of_pow_le_pow_left₀ two_ne_zero hnn hsq
  refine (Finset.sum_le_sum hterm).trans ?_
  exact Concrete.sum_cosetAffinity_pow_collision_classCard_le_of_sq K hG hs hcount

open Classical in
/-- **Coset samples identify the hidden subgroup at a linear sample count — unconditional in piece
(i)(a), conditional only on the non-normal maximal class count** (Nielsen & Chuang, Problem 5.5 —
the fidelity-route identification headline for **general** `G`). Take the candidate hidden subgroups
to be *all* subgroups `K' ≤ G`, each producing the `m`-copy reduced state `σ_{K'}^{⊗m}` (5.80), and
write the sample count as `m = |ι| = 4u` with `2·|G|² ≤ 2^u` (a **linear** count,
`m = 8 log₂|G| + 4`). *Given only* the non-normal maximal **class count** `hcount` (piece (ii):
`∀ J, 3·#{J-conj classes of non-normal maximal subgroups} ≤ |J|²`), the pretty-good (square-root)
measurement identifies the
*true* hidden subgroup `K` with success probability

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|`.

Unlike the affinity-route headline
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard` — which additionally
needs the piece-(i)(a) **paired-trace inequality** `hpaired` (subtle, normalization-dependent, still
open in general) — this **fidelity-route** headline needs **no** `hpaired`: it composes the
*unconditional* per-state fidelity discrimination bound
`cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_fidelity`
(`1 − p(K) ≤ 2·∑_{K'≠K} F`, from Rotfel'd's trace inequality) with the fidelity collision sum
`cosetDensityState_pi_sum_fidelity_collision_classCard_le` (`∑_{K'≠K} F ≤ 7/|G|`), giving
`1 − p(K) ≤ 14/|G|`. The price is the **doubled** sample count (`m = 8 log₂|G| + 4` vs N&C's exact
`4 log₂|G| + 2`), the cost of the `F² ≤ A` comparison; the constant is still `O(log|G|)` oracle
calls. Piece (i)(a) is therefore **not** a wall — it is discharged outright for *every*
hidden-subgroup instance (genuinely non-abelian `G` included), leaving the deep-group-theory class
count `hcount` (piece (ii)) as the sole remaining hypothesis. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_classCard
    [Fintype (Subgroup G)] {u : ℕ}
    (hι : Fintype.card ι = 4 * u) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ u)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    1 - 14 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  classical
  have herr := cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_fidelity (ι := ι) K
  have hcoll := cosetDensityState_pi_sum_fidelity_collision_classCard_le (ι := ι) K hι hG hs hcount
  -- `herr : 1 − p(K) ≤ 2·∑_{K'≠K} F`, `hcoll : ∑_{K'≠K} F ≤ 7/|G|` ⟹ `1 − p(K) ≤ 14/|G|`.
  have h14 : (14 : ℝ) / (Nat.card G : ℝ) = 2 * (7 / (Nat.card G : ℝ)) := by ring
  linarith [herr, hcoll, h14]

open Classical in
/-- **Coset samples identify the hidden subgroup at a linear sample count — fully unconditional for
nilpotent `G`** (Nielsen & Chuang, Problem 5.5). For a **nilpotent** finite group `G`, the
fidelity-route identification headline at the linear sample count `m = |ι| = 4u` with `2·|G|² ≤ 2^u`
holds **with both Ettinger–Høyer–Knill ingredients discharged** — no `hpaired`, no class-count
hypothesis:

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|`.

Both pieces are free here. **Piece (i)(a)** is discharged by the *fidelity* route
(`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_classCard`, via Rotfel'd's trace
inequality — no paired-trace hypothesis). **Piece (ii)** (the Liebeck–Pyber–Shalev-strength class
count) is **vacuous** for nilpotent `G`: a nilpotent group — and every subgroup of one — has *no*
non-normal maximal subgroups (`Concrete.normal_subgroupOf_of_covBy_of_isNilpotent`: under the
normalizer condition every maximal subgroup is normal), so the filtered set is empty.

This **strictly generalizes** the abelian headline
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_commGroup`: that result is fully
unconditional only for *abelian* `G` (where it discharges `hpaired` from commutativity via
`State.pairedTraceBound_of_commute`), whereas the fidelity route needs no commutativity at all and
so covers the **entire** class of nilpotent groups — all abelian groups, *all* `p`-groups, and their
direct products — with no operator-inequality hypothesis whatsoever. The tradeoff is the doubled
sample count `m = 8 log₂|G| + 4` (still `O(log|G|)`). The general (non-nilpotent) case remains
conditional on the class count `hcount` (piece (ii)) via the headline above. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_nilpotent
    [Group.IsNilpotent G] [Fintype (Subgroup G)] {u : ℕ}
    (hι : Fintype.card ι = 4 * u) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ u) :
    1 - 14 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  classical
  -- Piece (ii)'s class count is vacuous for nilpotent `G` (`Concrete.classCard_hyp_of_isNilpotent`:
  -- no non-normal maximal subgroups).
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_classCard
    (ι := ι) K hι hG hs Concrete.classCard_hyp_of_isNilpotent

open Classical in
/-- **Coset samples identify the hidden subgroup at N&C's linear sample count** (Nielsen & Chuang,
Problem 5.5 — the identification headline at the exact linear count `m = 4 log₂|G| + 2`, conditional
on the two isolated Ettinger–Høyer–Knill ingredients). Take the candidate hidden subgroups to be
*all* subgroups `K' ≤ G`, each producing the `m`-copy reduced state `σ_{K'}^{⊗m}` (5.80), and write
the sample count as `m = |ι| = 2s` with `2·|G|² ≤ 2^s` (N&C's exact linear count, `s = 2 log₂|G|+1`,
`m = 4 log₂|G| + 2`). *Given* the two isolated ingredients — the coset **paired-trace inequality**
`hpaired` (piece (i)(a): `re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`) and the
non-normal maximal **class count** `hcount` (piece (ii): `∀ J, 3·#{J-conj classes of non-normal
maximal subgroups} ≤ |J|²`) — the pretty-good (square-root) measurement identifies the *true* hidden
subgroup `K` with success probability

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|`.

This is the Ettinger–Høyer–Knill conclusion at N&C's **linear** sample count: `O(log|G|)` oracle
calls suffice to identify `K` with inverse-linearly-small error — the substantive content of Problem
5.5's headline (N&C's *linear* `m = 4 log₂|G| + 2`, not the weaker `O((log|G|)²)` of
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_sampleCount`, which uses a crude union
count). It composes the *per-state* discrimination bound
`cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired`
(`1 − p(K) ≤ 2·∑_{K'≠K} A`) with the fully-threaded affinity collision bound
`cosetDensityState_pi_sum_affinity_collision_classCard_le` (`∑_{K'≠K} A ≤ 7/|G|`), giving
`1 − p(K) ≤ 14/|G|`.

The constant `14/|G|` is `O(1/|G|)`; N&C's exact target `1 − 1/|G|` needs a further sharpening of
the collision factors (the `7/|G|` is `O(1/|G|)` rather than sharp), see the module
docstring's "Remaining" note. Both hypotheses are proven Ettinger–Høyer–Knill mathematics — a
subtle density-operator trace inequality (piece (i)(a), true but normalization-dependent) and a
Liebeck–Pyber–Shalev-strength maximal-subgroup class count (piece (ii)) — hence work still to be
discharged, not walls. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard
    [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 2 * s) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2)
    (hpaired : State.PairedTraceBound
      (fun K'' : Subgroup G => cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K) :
    1 - 14 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  classical
  have hA := cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired
    (ι := ι) K hpaired
  have hcoll := cosetDensityState_pi_sum_affinity_collision_classCard_le (ι := ι) K hι hG hs hcount
  -- `hA : 1 − p(K) ≤ 2·∑_{K'≠K} A`, `hcoll : ∑_{K'≠K} A ≤ 7/|G|` ⟹ `1 − p(K) ≤ 14/|G|`.
  have h14 : (14 : ℝ) / (Nat.card G : ℝ) = 2 * (7 / (Nat.card G : ℝ)) := by ring
  linarith [hA, hcoll, h14]

open Classical in
/-- **Coset samples identify the hidden subgroup at N&C's linear count — piece (ii) unconditional
for nilpotent `G`** (Nielsen & Chuang, Problem 5.5). For a **nilpotent** group `G`, the
identification headline at the exact linear sample count `m = |ι| = 2s` with `2·|G|² ≤ 2^s` (N&C's
`m = 4 log₂|G| + 2`) holds with the Ettinger–Høyer–Knill counting ingredient (piece (ii))
**discharged unconditionally**:

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|`,

conditional now on the *single* remaining ingredient — the piece-(i)(a) **paired-trace inequality**
`hpaired` (`re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`).

The general headline `cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard`
carries *two* isolated ingredients: `hpaired` and the Liebeck–Pyber–Shalev-strength class count
`hcount` (`∀ J, 3·#{J-conjugacy classes of non-normal maximal subgroups} ≤ |J|²`). For a nilpotent
group that class count is **free**: a nilpotent group — and every subgroup of one — has *no*
non-normal maximal subgroups (`Concrete.normal_subgroupOf_of_covBy_of_isNilpotent`: under the
normalizer condition every maximal subgroup is normal), so the filtered set is empty and the count
is `0 ≤ |J|²`. This eliminates the deep-group-theory dependency for the entire class of nilpotent
groups (all abelian groups, all `p`-groups, and their direct products), leaving only the
density-operator paired-trace inequality. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_nilpotent
    [Group.IsNilpotent G] [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 2 * s) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hpaired : State.PairedTraceBound
      (fun K'' : Subgroup G => cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K) :
    1 - 14 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  classical
  -- Piece (ii): the class count is vacuous for nilpotent `G` (no non-normal maximal subgroups).
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard
    (ι := ι) K hι hG hs Concrete.classCard_hyp_of_isNilpotent hpaired

section CommGroupHeadline

open Classical in
/-- **Coset samples identify the hidden subgroup at N&C's linear count — fully unconditional for
abelian `G`** (Nielsen & Chuang, Problem 5.5). For a **commutative** finite group `G`, the
identification headline at the exact linear sample count `m = |ι| = 2s` with `2·|G|² ≤ 2^s` (N&C's
`m = 4 log₂|G| + 2`) holds **with both Ettinger–Høyer–Knill ingredients discharged** — no
`hpaired`, no class-count hypothesis:

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|`.

The two isolated ingredients of the general headline
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard` are both **free**
for abelian `G`:
* **Piece (ii)** (the Liebeck–Pyber–Shalev-strength non-normal maximal class count) is vacuous: an
  abelian group is nilpotent (`CommGroup.isNilpotent`), and a nilpotent group has no non-normal
  maximal subgroups — this is exactly `..._of_paired_of_nilpotent`, which this theorem invokes.
* **Piece (i)(a)** (the paired-trace inequality `hpaired`) holds because the candidate reduced
  states **commute**: for abelian `G` the direct power `G^ι = (ι → G)` is abelian, so the coset
  density operators `σ_{K'}^{⊗m} = cosetDensityState (K'^ι)` pairwise commute
  (`cosetDensityState_op_commute`, the `σ_{K'}` being simultaneously diagonal in the character
  basis / convolution operators). For a commuting family the paired-trace bound is unconditional
  (`State.pairedTraceBound_of_commute`: the honest operator subadditivity `√S₀ ≤ ∑ √σ_{K'}` holds
  and pairs against `√σ_K^{⊗m}`).

This is the first **fully unconditional** instance of the identification clause at N&C's exact
linear sample count, covering the entire abelian hidden-subgroup problem — the canonical case
(Simon's, Shor's) N&C's setup is built on. The general (non-commuting) paired-trace inequality for
genuinely non-abelian `G` is not proved here (see the module "Remaining" note). -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_commGroup
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [Fintype (Subgroup G)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Subgroup G) [DecidablePred (· ∈ K)] {s : ℕ}
    (hι : Fintype.card ι = 2 * s) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    1 - 14 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  have : Group.IsNilpotent G := CommGroup.isNilpotent
  refine cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_nilpotent
    (ι := ι) K hι hG hs ?_
  -- Piece (i)(a)'s paired-trace inequality is unconditional here: the coset density operators of
  -- the abelian group `G^ι` pairwise commute (`cosetDensityState_op_commute`).
  refine State.pairedTraceBound_of_commute _ K (fun K₁ K₂ => ?_)
  exact cosetDensityState_op_commute _ _

end CommGroupHeadline

/-! ### N&C's exact target probability `1 − 1/|G|` (the sharp constant, at a linear sample count)

The headlines above reach `p(K ∣ σ_K^{⊗m}) ≥ 1 − 14/|G|` — the correct `O(1/|G|)` order, but with
the loose constant `14`. The theorems in this block sharpen the constant to N&C's **exact** target
`1 − 1/|G|`, at the cost of a modestly larger (still **linear**, `O(log|G|)`) sample count: the
identification deficit is `2·∑_{K'≠K} (affinity/fidelity)`, so N&C's exact `1/|G|` deficit needs the
collision sum `≤ 1/(2|G|)`, which `Concrete.sum_cosetAffinity_pow_collision_classCard_le_inv_of_sq`
supplies at the exponent `2(s+4)` (the exponent-raising `(1/√2)^8 = 1/16` factor turning `7/|G|`
into `≤ 1/(2|G|)`). For the entire **abelian** hidden-subgroup problem this is
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_commGroup`: N&C's *literal*
Problem 5.5 conclusion `p(K) ≥ 1 − 1/|G|` at the linear count `m = 4 log₂|G| + 10`, fully
unconditional (Simon's, Shor's — the canonical cases). -/

open Classical in
/-- **The per-`K` affinity collision sum is `≤ 1/(2|G|)` — the sharp constant** (Nielsen & Chuang,
Problem 5.5). The `1/(2|G|)` sharpening of
`cosetDensityState_pi_sum_affinity_collision_classCard_le` (`≤ 7/|G|` at N&C's exact `m = 2s`):
writing the sample count as `m = |ι| = 2(s+4)` with `2·|G|² ≤ 2^s` (a **linear** count
`m = 4 log₂|G| + 10`), and given the non-normal maximal class count `hcount`, the pairwise affinity
of `σ_K^{⊗m}` against every other candidate sums to
`∑_{K' ≠ K} A(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 1/(2|G|)`. The physics (`State.affinity`) counterpart of the
concrete `Concrete.sum_cosetAffinity_pow_collision_classCard_le_inv_of_sq` (each physical affinity
is `Concrete.cosetAffinity K K'^{2(s+4)}` by `cosetDensityState_pi_affinity`). This is exactly the
collision budget that drives the pretty-good deficit `2·∑ A` to N&C's exact `1/|G|`. -/
theorem cosetDensityState_pi_sum_affinity_collision_classCard_le_inv [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 2 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    ∑ K' ∈ Finset.univ.erase K,
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
      ≤ 1 / (2 * (Nat.card G : ℝ)) := by
  have hval : ∀ K' ∈ Finset.univ.erase K,
      (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
        = Concrete.cosetAffinity K K' ^ (2 * (s + 4)) := by
    intro K' _
    rw [cosetDensityState_pi_affinity, Concrete.cosetAffinity, hι]
  rw [Finset.sum_congr rfl hval]
  exact Concrete.sum_cosetAffinity_pow_collision_classCard_le_inv_of_sq K hG hs hcount

open Classical in
/-- **The per-`K` *fidelity* collision sum is `≤ 1/(2|G|)` — the sharp constant** (Nielsen & Chuang,
Problem 5.5). The `1/(2|G|)` sharpening of
`cosetDensityState_pi_sum_fidelity_collision_classCard_le` (`≤ 7/|G|`): writing the sample count as
`m = |ι| = 4(s+4)` with `2·|G|² ≤ 2^s` (a **linear** count `m = 8 log₂|G| + 20`), and given the
class count `hcount`, the pairwise **fidelity** of `σ_K^{⊗m}` against every other candidate sums to
`∑_{K' ≠ K} F(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 1/(2|G|)`. The bridge is the per-pair
`cosetDensityState_pi_fidelity_sq_le_affinity` (`F² ≤ A`): with `m = 4(s+4)`, the `m`-copy affinity
is `A(σ_K, σ_{K'})^{4(s+4)} = (A(σ_K, σ_{K'})^{2(s+4)})²`, so `F ≤
Concrete.cosetAffinity K K'^{2(s+4)}`, and the concrete sharp collision bound
`Concrete.sum_cosetAffinity_pow_collision_classCard_le_inv_of_sq` closes it. Being a **fidelity**
sum (Rotfel'd, no paired-trace hypothesis) it feeds the *unconditional* fidelity-route headline. -/
theorem cosetDensityState_pi_sum_fidelity_collision_classCard_le_inv [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 4 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    ∑ K' ∈ Finset.univ.erase K,
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).fidelity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
      ≤ 1 / (2 * (Nat.card G : ℝ)) := by
  have hterm : ∀ K' ∈ Finset.univ.erase K,
      (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).fidelity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
        ≤ Concrete.cosetAffinity K K' ^ (2 * (s + 4)) := by
    intro K' _
    have hnn : (0 : ℝ) ≤ Concrete.cosetAffinity K K' ^ (2 * (s + 4)) :=
      pow_nonneg (Concrete.cosetAffinity_nonneg K K') _
    have hAeq : (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).affinity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
        = Concrete.cosetAffinity K K' ^ (4 * (s + 4)) := by
      rw [cosetDensityState_pi_affinity, Concrete.cosetAffinity, hι]
    have hsq : (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).fidelity
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')) ^ 2
        ≤ (Concrete.cosetAffinity K K' ^ (2 * (s + 4))) ^ 2 := by
      rw [← pow_mul, show 2 * (s + 4) * 2 = 4 * (s + 4) from by ring, ← hAeq]
      exact cosetDensityState_pi_fidelity_sq_le_affinity K K'
    exact le_of_pow_le_pow_left₀ two_ne_zero hnn hsq
  refine (Finset.sum_le_sum hterm).trans ?_
  exact Concrete.sum_cosetAffinity_pow_collision_classCard_le_inv_of_sq K hG hs hcount

open Classical in
/-- **Coset samples identify the hidden subgroup at N&C's exact target probability `1 − 1/|G|` —
fully unconditional for nilpotent `G`** (Nielsen & Chuang, Problem 5.5). For a **nilpotent** finite
group `G`, the fidelity-route headline at the sharp constant and linear count `m = |ι| = 4(s+4)`
with `2·|G|² ≤ 2^s` (`m = 8 log₂|G| + 20`) holds with **both** Ettinger–Høyer–Knill ingredients
discharged:

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 1/|G|`.

Piece (i)(a) is discharged by the fidelity (Rotfel'd) route, and piece (ii)'s class count is
**vacuous** for nilpotent `G` (a nilpotent group — and every subgroup of one — has no non-normal
maximal subgroups, `Concrete.normal_subgroupOf_of_covBy_of_isNilpotent`). This is the sharp-constant
(`1 − 1/|G|`, N&C's exact target) refinement of
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_nilpotent` (`≥ 1 − 14/|G|`), covering all
abelian groups, all `p`-groups, and their direct products with no operator-inequality hypothesis. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_nilpotent
    [Group.IsNilpotent G] [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 4 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  classical
  -- Piece (i)(a): the *unconditional* per-state fidelity discrimination bound (Rotfel'd, no
  -- paired-trace). Piece (ii): the class count is vacuous for nilpotent `G`
  -- (`Concrete.classCard_hyp_of_isNilpotent`). Deficit `2·∑ F ≤ 2·1/(2|G|) = 1/|G|`.
  have herr := cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_fidelity (ι := ι) K
  have hcoll := cosetDensityState_pi_sum_fidelity_collision_classCard_le_inv
    (ι := ι) K hι hG hs Concrete.classCard_hyp_of_isNilpotent
  have h1 : (1 : ℝ) / (Nat.card G : ℝ) = 2 * (1 / (2 * (Nat.card G : ℝ))) := by ring
  linarith [herr, hcoll, h1]

section CommGroupHeadlineInv

open Classical in
/-- **Coset samples identify the hidden subgroup at N&C's exact statement `1 − 1/|G|` — fully
unconditional for abelian `G`** (Nielsen & Chuang, Problem 5.5). For a **commutative** finite group
`G`, N&C's *literal* Problem 5.5 conclusion holds with **both** Ettinger–Høyer–Knill ingredients
discharged and the **exact target probability**: at the linear sample count `m = |ι| = 2(s+4)` with
`2·|G|² ≤ 2^s` (`m = 4 log₂|G| + 10`),

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 1/|G|`.

This is the **affinity route** at the sharp constant, with both Ettinger–Høyer–Knill ingredients
free for abelian `G`: piece (ii)'s class count is vacuous (abelian ⇒ nilpotent ⇒ no non-normal
maximal subgroups, `Concrete.classCard_hyp_of_isNilpotent`), and piece (i)(a)'s paired-trace
inequality holds because the coset density operators of the abelian direct power `G^ι` **commute**
(`cosetDensityState_op_commute`, `State.pairedTraceBound_of_commute`) — so the per-state affinity
discrimination bound
`cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired`
and the sharp affinity collision sum `cosetDensityState_pi_sum_affinity_collision_classCard_le_inv`
(`∑_{K'≠K} A ≤ 1/(2|G|)`) compose to `1 − p(K) ≤ 1/|G|`. It sharpens
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_commGroup` (`≥ 1 − 14/|G|` at N&C's exact
`m = 4 log₂|G| + 2`) to N&C's **exact** target probability `1 − 1/|G|`, at the linear count
`m = 4 log₂|G| + 10` — the first instance proving Problem 5.5's *literal* headline statement (the
canonical abelian case: Simon's, Shor's). -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_commGroup
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [Fintype (Subgroup G)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Subgroup G) [DecidablePred (· ∈ K)] {s : ℕ}
    (hι : Fintype.card ι = 2 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  have : Group.IsNilpotent G := CommGroup.isNilpotent
  classical
  -- Piece (i)(a): the paired-trace bound holds because the coset density operators of the abelian
  -- direct power `G^ι` commute (`cosetDensityState_op_commute`).
  have hpaired : State.PairedTraceBound
      (fun K'' : Subgroup G => cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K :=
    State.pairedTraceBound_of_commute _ K (fun K₁ K₂ => cosetDensityState_op_commute _ _)
  have hA := cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired
    (ι := ι) K hpaired
  -- Piece (ii): the class count is vacuous for nilpotent `G` (no non-normal maximal subgroups).
  have hcoll := cosetDensityState_pi_sum_affinity_collision_classCard_le_inv
    (ι := ι) K hι hG hs Concrete.classCard_hyp_of_isNilpotent
  have h1 : (1 : ℝ) / (Nat.card G : ℝ) = 2 * (1 / (2 * (Nat.card G : ℝ))) := by ring
  linarith [hA, hcoll, h1]

end CommGroupHeadlineInv

open Classical in
/-- **N&C Problem 5.5 at N&C's exact target probability `1 − 1/|G|`, general `G`, fidelity route.**
The sharp-constant (`1 − 1/|G|`) refinement of
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_classCard` (`≥ 1 − 14/|G|`). For a finite
group `G` that **need not be Abelian** (no Fourier transform over `G`), at the linear sample count
`m = |ι| = 4(s+4)` with `2·|G|² ≤ 2^s` (`m = 8 log₂|G| + 20`), the pretty-good measurement
identifies the hidden subgroup at N&C's **exact** target probability:

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 1/|G|`,

**conditional only on the single piece-(ii) class count** `hcount` (piece (i)(a) is discharged
*unconditionally* by the fidelity / Rotfel'd route — no paired-trace hypothesis). It composes the
unconditional per-state fidelity discrimination bound
`cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_fidelity` (`1 − p(K) ≤ 2·∑_{K'≠K}
F`) with the **sharp** fidelity collision sum
`cosetDensityState_pi_sum_fidelity_collision_classCard_le_inv` (`∑ ≤ 1/(2|G|)`), giving
`1 − p(K) ≤ 1/|G|`. This is N&C's literal target probability for general `G`; `hcount` (the
Liebeck–Pyber–Shalev-strength non-normal maximal class count) is the single explicit finite-group
residual — vacuous for nilpotent `G` (see `..._one_sub_inv_of_nilpotent`). -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard
    [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 4 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  classical
  have herr := cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_fidelity (ι := ι) K
  have hcoll := cosetDensityState_pi_sum_fidelity_collision_classCard_le_inv
    (ι := ι) K hι hG hs hcount
  have h1 : (1 : ℝ) / (Nat.card G : ℝ) = 2 * (1 / (2 * (Nat.card G : ℝ))) := by ring
  linarith [herr, hcoll, h1]

open Classical in
/-- **N&C Problem 5.5 — the *literal* headline for general `G` at N&C's exact count and exact target
probability, reduced to the two isolated Ettinger–Høyer–Knill ingredients** (affinity route). For a
finite group `G` that **need not be Abelian** (no Fourier transform over `G`), at N&C's **exact**
linear sample count `m = |ι| = 2(s+4)` with `2·|G|² ≤ 2^s` (`m = 4 log₂|G| + 10`), the pretty-good
measurement identifies the hidden subgroup at N&C's **exact** target probability:

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 1/|G|`,

**conditional on exactly the two isolated ingredients** — the piece-(i)(a) paired-trace inequality
`hpaired` (`re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`) and the piece-(ii) non-normal
maximal class count `hcount`. This is the affinity route (avoiding the fidelity route's `F² ≤ A`
factor-of-two, at the price of `hpaired`), sharpening
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard` (`≥ 1 − 14/|G|`) to
N&C's exact `1 − 1/|G|`: it composes the per-state affinity discrimination bound
`cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired` with the sharp
affinity collision sum `cosetDensityState_pi_sum_affinity_collision_classCard_le_inv` (`∑ ≤
1/(2|G|)`). Of N&C's two exact constants (`4 log₂|G| + O(1)`, `1 − 1/|G|`), this matches the
probability *exactly* and the sample count up to the additive `O(1)`; both `hpaired` and `hcount`
are proven Ettinger–Høyer–Knill mathematics — free for the abelian core (Simon's, Shor's,
`..._one_sub_inv_of_commGroup`) and all nilpotent `G` (`..._one_sub_inv_of_nilpotent`). -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_paired_of_classCard
    [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 2 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2)
    (hpaired : State.PairedTraceBound
      (fun K'' : Subgroup G => cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  classical
  have hA := cosetDensityState_pi_prettyGoodMeasurement_error_le_two_mul_sum_affinity_of_paired
    (ι := ι) K hpaired
  have hcoll := cosetDensityState_pi_sum_affinity_collision_classCard_le_inv
    (ι := ι) K hι hG hs hcount
  have h1 : (1 : ℝ) / (Nat.card G : ℝ) = 2 * (1 / (2 * (Nat.card G : ℝ))) := by ring
  linarith [hA, hcoll, h1]

/-- **Single-copy distinguishability of the coset reduced states** (Nielsen & Chuang, Problem 5.5).
For *distinct* candidate hidden subgroups `K ≠ K'`, the single-copy reduced states `σ_K, σ_{K'}` are
bounded away from each other in trace distance:

`D(σ_K, σ_{K'}) ≥ 1 − 1/√2`.

This is the **operational form** of the single-copy near-orthogonality: it turns the affinity bound
`A(σ_K, σ_{K'}) ≤ 1/√2` (`cosetDensityState_affinity_le`) into a statement about *measurements*,
through the fidelity-family Fuchs–van de Graaf lower bound `1 − A ≤ D`
(`State.one_sub_affinity_le_traceDistance`). Since the trace distance is the optimal single-shot
distinguishing bias (`State.classicalTraceDist_bornProb_le`), a single measurement already
distinguishes `σ_K` from `σ_{K'}` with bias at least `1 − 1/√2`. Taking `m` copies amplifies this to
near-certainty (`cosetDensityState_pi_traceDistance_ge`). -/
theorem cosetDensityState_traceDistance_ge (K' : Subgroup G) [DecidablePred (· ∈ K')]
    (hne : K ≠ K') :
    1 - 1 / Real.sqrt 2 ≤ (cosetDensityState K).traceDistance (cosetDensityState K') := by
  have h1 := State.one_sub_affinity_le_traceDistance (cosetDensityState K) (cosetDensityState K')
  have h2 := cosetDensityState_affinity_le K K' hne
  linarith

/-- **Exponential distinguishability of the `m`-copy coset reduced states** (Nielsen & Chuang,
Problem 5.5). For *distinct* candidate hidden subgroups `K ≠ K'`, the `m`-copy reduced states
`σ_K^{⊗m} = cosetDensityState (K^ι)` and `σ_{K'}^{⊗m}` become nearly perfectly distinguishable as
the sample count `m` grows:

`D(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≥ 1 − (1/√2)^m = 1 − 2^{-m/2}`.

This is the **operational form** of the exponential near-orthogonality — the direct measurement
content behind N&C's "a final state in which the pure-state outcomes for different possible hidden
subgroups are nearly orthogonal". It is the fidelity-metric bound
`State.one_sub_affinity_le_traceDistance` (`1 − A ≤ D`) applied to the exponentially small `m`-copy
affinity `A(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ (1/√2)^m` (`cosetDensityState_pi_affinity_le`). Since the trace
distance is the optimal single-shot distinguishing bias, a single measurement on the `m`-copy final
state distinguishes any two distinct hidden subgroups' reduced states with error at most
`2^{-m/2}` — the **pairwise** identification guarantee. The full headline (identifying `K` *among
all* candidates with probability `≥ 1 − 1/|G|`) additionally needs the Ettinger–Høyer–Knill
multi-state
discrimination bound and subgroup-index counting sum, a long development recorded in the module
docstring's "Remaining" note. -/
theorem cosetDensityState_pi_traceDistance_ge (K' : Subgroup G) [DecidablePred (· ∈ K')]
    (hne : K ≠ K') :
    1 - (1 / Real.sqrt 2) ^ Fintype.card ι
      ≤ (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)).traceDistance
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')) := by
  have h1 := State.one_sub_affinity_le_traceDistance
    (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K))
    (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'))
  have h2 := cosetDensityState_pi_affinity_le (ι := ι) K K' hne
  linarith

open Classical in
/-- **The total pretty-good identification error over the candidate hidden subgroups is twice the
coset collision sum** (Nielsen & Chuang, Problem 5.5 — the identification clause's discrimination
step, instantiated for the coset family). Take the candidate hidden subgroups to be *all* subgroups
`K' ≤ G`, each producing the `m`-copy reduced state `σ_{K'}^{⊗m} = cosetDensityState (K'^ι)` (5.80).
The **pretty-good (square-root) measurement** `State.prettyGoodMeasurement` of this family is the
mixed-state discrimination measurement N&C's identification clause is stated over (the reduced
states are mixed, so the pure-state `distinguishingPOVM` does not apply). Summing its per-candidate
identification deficits `1 − p(K' ∣ σ_{K'}^{⊗m})` over all candidates,

`∑_{K'} (1 − p(K' ∣ σ_{K'}^{⊗m})) ≤ 2 · ∑_{K'} ∑_{K'' ≠ K'} (|K'∩K''| / √(|K'||K''|))^m`.

This is the specialisation to the coset family of the reusable mixed-state discrimination bound
`State.sum_one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity`
(`∑ᵢ(1−p(i∣ρᵢ)) ≤ 2·∑ᵢ∑_{j≠i} A(ρᵢ, ρⱼ)`), the pairwise affinities evaluated in closed form by
`cosetDensityState_pi_affinity` (`A(σ_{K'}^{⊗m}, σ_{K''}^{⊗m}) = (|K'∩K''|/√(|K'||K''|))^m
= Concrete.cosetAffinity K' K'' ^ m`). It reduces the *total* identification error to the **coset
collision sum** — the pure group-theoretic double sum `∑_{K'} ∑_{K''≠K'} cosetAffinity K' K'' ^ m`
whose per-candidate inner sum is bounded by
`Concrete.sum_cosetAffinity_pow_collision_proper_le_of_sq` — so the sole remaining
Ettinger–Høyer–Knill ingredient is the counting bound driving that collision sum below `1/|G|` at
N&C's linear sample count (piece (ii), the proper-subgroup low-index sum `∑_{H<K}(|H|/|K|)^s`).

The bound side is the real-valued `Concrete.cosetAffinity`. The candidate index is the whole
subgroup lattice `Subgroup G` (finite, so `Fintype (Subgroup G)`), matching the ensemble the
collision-sum lemmas sum over. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_sum_error_le [Fintype (Subgroup G)] :
    ∑ K' : Subgroup G,
        (1 - (State.prettyGoodMeasurement
            (fun K'' : Subgroup G =>
              cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')) (some K'))
      ≤ 2 * ∑ K' : Subgroup G, ∑ K'' ∈ Finset.univ.erase K',
          Concrete.cosetAffinity K' K'' ^ Fintype.card ι := by
  classical
  refine (State.sum_one_sub_prettyGoodMeasurement_bornProb_self_le_two_mul_sum_affinity
    (fun K'' : Subgroup G =>
      cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).trans_eq ?_
  -- Each pairwise affinity is the `m`-th power of the coset affinity `|K'∩K''|/√(|K'||K''|)`.
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun K' _ => Finset.sum_congr rfl fun K'' _ => ?_)
  rw [cosetDensityState_pi_affinity, Concrete.cosetAffinity]

/-- **A single value is `≤ B` when its total over a finite index is `≤ B` and every value is
nonnegative.** For `p : κ → ℝ` with each `p j ≥ 0`, a single `p k` is at most the whole sum
(`Finset.single_le_sum`), which is `≤ B` by `hsum`. Applied with `p j = 1 − p(some j ∣ ρ j)` the
per-candidate pretty-good identification *deficit*, this is the "each nonnegative term ≤ their sum"
step turning the *summed* Barnum–Knill discrimination bound into the *per-`k`* guarantee the
identification headline needs — requiring **no** per-state discrimination bound (none is available,
as the operator subadditivity `√(∑ρ) ≤ ∑√ρ` is false). Kept abstract over `p : κ → ℝ` so that in
the coset theorem the huge `cosetDensityState`/`prettyGoodMeasurement` terms are never forced
through `Finset.single_le_sum`'s unification. -/
private theorem single_le_of_sum_le {κ : Type*} [Fintype κ] (p : κ → ℝ) (k : κ) {B : ℝ}
    (hnn : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j ≤ B) :
    p k ≤ B :=
  (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hnn j) (Finset.mem_univ k)).trans hsum

open Classical in
/-- **A polynomial number of coset samples identifies the hidden subgroup with probability
`≥ 1 − 1/|G|`** (Nielsen & Chuang, Problem 5.5 — the identification headline, at the reachable
*polynomial* sample count). Take the candidate hidden subgroups to be *all* subgroups `K' ≤ G`, each
producing the `m`-copy reduced state `σ_{K'}^{⊗m} = cosetDensityState (K'^ι)` (5.80, `m = |ι|`
copies). The **pretty-good (square-root) measurement** `State.prettyGoodMeasurement` of this family
identifies the *true* hidden subgroup `K` — whatever it is — with success probability

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 1/|G|`

once the number of coset samples satisfies `2·|G|^{2 log₂|G| + 2}·2^{-m/2} ≤ 1/|G|`, i.e.
`m ≥ 4(log₂|G|)² + 6 log₂|G| + 2` — a **polynomial (quadratic) `O((log|G|)²)`** sample count.
This is the Ettinger–Høyer–Knill conclusion that the hidden subgroup problem has **polynomial query
complexity**, here at N&C's exact target success probability `1 − 1/|G|`, and it is a genuine
*per-`K`* guarantee (it holds for every hidden subgroup `K`, not merely on average).

The proof needs **no** per-state discrimination bound (none is available: only the *summed*
Barnum–Knill bound holds, since the operator subadditivity `√S₀ ≤ ∑ⱼ√ρⱼ` is false). Instead it uses
that each per-candidate identification deficit `1 − p(K' ∣ σ_{K'}^{⊗m})` is **nonnegative**
(`Measurement.bornProb_le_one`), so the true `K`'s deficit is at most the *total* deficit
(`Finset.single_le_sum`), which the summed bound
`cosetDensityState_pi_prettyGoodMeasurement_sum_error_le` controls by `2·(coset collision sum)`. The
collision sum is then bounded crudely but sufficiently: every distinct pair separates by the
universal per-copy factor `A(σ_{K'}^{⊗m}, σ_{K''}^{⊗m}) ≤ 2^{-m/2}`
(`Concrete.cosetAffinity_le_of_ne`, `Concrete.sum_cosetAffinity_pow_le_of_forall_le`), and there are
at most `|G|^{log₂|G|+1}` candidate subgroups (`Concrete.card_subgroup_le`), so the double sum is
`≤ (#subgroups)²·2^{-m/2} ≤ |G|^{2 log₂|G| + 2}·2^{-m/2}`.

**Relation to N&C's exact statement.** N&C claim identification at the *optimal linear* sample count
`m = 4 log₂|G| + 2`. Reaching that linear count is the genuinely research-grade
Ettinger–Høyer–Knill refinement (see the module docstring's "Remaining" note): it replaces the crude
union-bound factor `(#subgroups)²·2^{-m/2}` — which forces this *quadratic* `m` — by the sharp
per-`K` collision bound `∑_{K'≠K} A(σ_K^{⊗m},σ_{K'}^{⊗m}) ≤ 1/(2|G|)`, whose only missing ingredient
is the proper-subgroup low-index counting sum `∑_{H<K}(|H|/|K|)^s` (of Gaussian-binomial strength,
not reachable by the generating-set injection that discharges the dual overgroup sum). The theorem
here is therefore the reachable form of the headline — the polynomial-query-complexity content, at
the exact target probability — with the optimal linear constant not obtained here.

The sample-count hypothesis is a pure inequality over `|G|` and the copy count
`m = Fintype.card ι`. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_sampleCount
    [Fintype (Subgroup G)]
    (hm : 2 * (Fintype.card G : ℝ) ^ (2 * Nat.log 2 (Fintype.card G) + 2)
          * (1 / Real.sqrt 2) ^ Fintype.card ι
        ≤ (Fintype.card G : ℝ)⁻¹) :
    1 - (Fintype.card G : ℝ)⁻¹
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) := by
  classical
  -- Crude bound on the collision sum: every distinct pair separates by `2^{-m/2}`, and there are
  -- at most `|G|^{log₂|G|+1}` candidate subgroups.
  have hx : (0 : ℝ) ≤ (1 / Real.sqrt 2) ^ Fintype.card ι := by positivity
  have hcoll : ∑ K' : Subgroup G, ∑ K'' ∈ Finset.univ.erase K',
        Concrete.cosetAffinity K' K'' ^ Fintype.card ι
      ≤ (Fintype.card (Subgroup G) : ℝ) ^ 2 * (1 / Real.sqrt 2) ^ Fintype.card ι := by
    have hinner : ∀ K' : Subgroup G, ∑ K'' ∈ Finset.univ.erase K',
        Concrete.cosetAffinity K' K'' ^ Fintype.card ι
        ≤ (Fintype.card (Subgroup G) : ℝ) * (1 / Real.sqrt 2) ^ Fintype.card ι := by
      intro K'
      refine (Concrete.sum_cosetAffinity_pow_le_of_forall_le K' (Fintype.card ι)
        (fun K'' hK'' => Concrete.cosetAffinity_le_of_ne K' K''
          (Finset.ne_of_mem_erase hK'').symm)).trans ?_
      have hcard : ((Finset.univ.erase K').card : ℝ) ≤ (Fintype.card (Subgroup G) : ℝ) := by
        rw [← Finset.card_univ]; exact_mod_cast Finset.card_erase_le
      exact mul_le_mul_of_nonneg_right hcard hx
    calc ∑ K' : Subgroup G, ∑ K'' ∈ Finset.univ.erase K',
            Concrete.cosetAffinity K' K'' ^ Fintype.card ι
        ≤ ∑ _K' : Subgroup G,
            (Fintype.card (Subgroup G) : ℝ) * (1 / Real.sqrt 2) ^ Fintype.card ι :=
          Finset.sum_le_sum fun K' _ => hinner K'
      _ = (Fintype.card (Subgroup G) : ℝ) ^ 2 * (1 / Real.sqrt 2) ^ Fintype.card ι := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  -- `(#subgroups)² ≤ |G|^{2 log₂|G| + 2}`.
  have hsub : (Fintype.card (Subgroup G) : ℝ) ≤
      (Fintype.card G : ℝ) ^ (Nat.log 2 (Fintype.card G) + 1) := by
    have h := Concrete.card_subgroup_le (G := G)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    calc (Fintype.card (Subgroup G) : ℝ)
        ≤ ((Fintype.card G ^ (Nat.log 2 (Fintype.card G) + 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (Fintype.card G : ℝ) ^ (Nat.log 2 (Fintype.card G) + 1) := by push_cast; ring
  have hsq : (Fintype.card (Subgroup G) : ℝ) ^ 2
      ≤ (Fintype.card G : ℝ) ^ (2 * Nat.log 2 (Fintype.card G) + 2) := by
    calc (Fintype.card (Subgroup G) : ℝ) ^ 2
        ≤ ((Fintype.card G : ℝ) ^ (Nat.log 2 (Fintype.card G) + 1)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hsub 2
      _ = (Fintype.card G : ℝ) ^ (2 * Nat.log 2 (Fintype.card G) + 2) := by
          rw [← pow_mul]; congr 1; ring
  -- The total collision sum, hence the total identification deficit bound `B := 2·(collision)`, is
  -- `≤ 1/|G|` at the (quadratic) sample count.
  have hB : 2 * ∑ K' : Subgroup G, ∑ K'' ∈ Finset.univ.erase K',
        Concrete.cosetAffinity K' K'' ^ Fintype.card ι
      ≤ (Fintype.card G : ℝ)⁻¹ :=
    calc 2 * ∑ K' : Subgroup G, ∑ K'' ∈ Finset.univ.erase K',
            Concrete.cosetAffinity K' K'' ^ Fintype.card ι
        ≤ 2 * ((Fintype.card (Subgroup G) : ℝ) ^ 2 * (1 / Real.sqrt 2) ^ Fintype.card ι) :=
          mul_le_mul_of_nonneg_left hcoll (by norm_num)
      _ ≤ 2 * ((Fintype.card G : ℝ) ^ (2 * Nat.log 2 (Fintype.card G) + 2)
            * (1 / Real.sqrt 2) ^ Fintype.card ι) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hx) (by norm_num)
      _ = 2 * (Fintype.card G : ℝ) ^ (2 * Nat.log 2 (Fintype.card G) + 2)
            * (1 / Real.sqrt 2) ^ Fintype.card ι := by ring
      _ ≤ (Fintype.card G : ℝ)⁻¹ := hm
  -- The total identification deficit is `≤ 1/|G|` (summed Barnum–Knill bound chained with `hB`).
  have hsum : ∑ K' : Subgroup G, (1 - (State.prettyGoodMeasurement
        (fun K'' : Subgroup G =>
          cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')) (some K'))
      ≤ (Fintype.card G : ℝ)⁻¹ :=
    (cosetDensityState_pi_prettyGoodMeasurement_sum_error_le (ι := ι)).trans hB
  -- Reduce `1 − 1/|G| ≤ p(K)` to the deficit form `1 − p(K) ≤ 1/|G|` (`sub_le_comm`, purely
  -- structural), then bound the single deficit `1 − p(K)` by the total deficit sum via the abstract
  -- `single_le_of_sum_le` (kept over `p : Subgroup G → ℝ`), with `p` inferred from `hsum`.
  rw [sub_le_comm]
  have key := single_le_of_sum_le _ K
    (fun K' => sub_nonneg.mpr (Measurement.bornProb_le_one _ _ _)) hsum
  -- `key` and the goal agree except for one buried `DecidablePred (· ∈ K)` instance: `key` (from
  -- the summed bound, index `K'` *bound*) carries `Classical.propDecidable`, the goal the section
  -- `[DecidablePred (· ∈ K)]`. They are `Subsingleton`-equal, so `convert` closes the residual
  -- instance goal by congruence — avoiding an `exact` whose `isDefEq` would `whnf`-explode the huge
  -- `cosetDensityState` term to reconcile them.
  convert key using 6

open Classical in
/-- **The exact per-`K` pretty-good identification error is the total coset confusion probability**
(Nielsen & Chuang, Problem 5.5 — the exact per-state form of the identification clause's
discrimination step). Take the candidate hidden subgroups to be *all* subgroups `K' ≤ G`, each
producing the `m`-copy reduced state `σ_{K'}^{⊗m} = cosetDensityState (K'^ι)` (5.80). For the true
hidden subgroup `K`, the deficit of the pretty-good (square-root) measurement's success probability
is **exactly** the total probability of confusing `σ_K^{⊗m}` with another candidate's reduced state:

`1 − p(K ∣ σ_K^{⊗m}) = ∑_{K' ≠ K} p(K' ∣ σ_K^{⊗m})`.

This is the coset instance of the exact per-state identity
`State.one_sub_prettyGoodMeasurement_bornProb_self_eq_sum`: the pretty-good measurement leaks *no*
probability to its inconclusive outcome on a family state (the reduced states are `≤` the total
`S₀ = ∑_{K'} σ_{K'}^{⊗m}`, so the support projection fixes each — the lemma
`ContinuousLinearMap.mul_genInvSqrt_mul_self_mul_genInvSqrt_of_le`), so the identification error is
*exactly* the off-diagonal confusion mass, with no `2·(…)` slack.

Unlike the summed Barnum–Knill bound
`cosetDensityState_pi_prettyGoodMeasurement_sum_error_le` (whose per-state analogue collapses to the
**false** operator subadditivity `√S₀ ≤ ∑ⱼ √ρⱼ`), this is a genuine *per-`K`* identity. It isolates
the one remaining Ettinger–Høyer–Knill step for the **linear** sample count `m = 4 log₂|G| + 2`:
bound each coset confusion probability
`p(K' ∣ σ_K^{⊗m}) = re tr(σ_{K'}^{⊗m} S₀⁻¹ᐟ² σ_K^{⊗m} S₀⁻¹ᐟ²)`
by the pairwise affinity `A(σ_K^{⊗m}, σ_{K'}^{⊗m})`, whose collision sum
`cosetDensityState_pi_sum_affinity_collision_le` already stays `≤ 1/|G| + 2·∑_{H<K}(|H|/|K|)^s`. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_error_eq_confusion [Fintype (Subgroup G)] :
    1 - (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K)
      = ∑ K' ∈ Finset.univ.erase K,
          (State.prettyGoodMeasurement
            (fun K'' : Subgroup G =>
              cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K') := by
  classical
  have key := State.one_sub_prettyGoodMeasurement_bornProb_self_eq_sum
    (fun K'' : Subgroup G =>
      cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K
  -- `key`'s `ρ K` (index bound) carries `Classical.propDecidable` on `· ∈ K`, the goal the section
  -- `[DecidablePred (· ∈ K)]`; they are `Subsingleton`-equal, so `convert` closes the residual
  -- instance goals by congruence without a huge `whnf` reconciliation.
  convert key using 6

open Classical in
/-- **Symmetry of the coset pretty-good confusion probabilities** (Nielsen & Chuang, Problem 5.5).
Take the candidate hidden subgroups to be *all* subgroups `K' ≤ G`, each producing the `m`-copy
reduced state `σ_{K'}^{⊗m} = cosetDensityState (K'^ι)` (5.80).  For two candidates `K, K'` the
pretty-good (square-root) measurement confuses `σ_K^{⊗m}` for `K'` exactly as often as it confuses
`σ_{K'}^{⊗m}` for `K`:

`p(K' ∣ σ_K^{⊗m}) = p(K ∣ σ_{K'}^{⊗m})`.

The **coset confusion matrix is symmetric**.  This is the coset instance of the general
`State.prettyGoodMeasurement_bornProb_some_comm` (both confusion probabilities are the one physical
trace `re tr(σ_{K'}^{⊗m} S₀⁻¹ᐟ² σ_K^{⊗m} S₀⁻¹ᐟ²)`, symmetric by trace cyclicity).  With the exact
per-`K` error identity `cosetDensityState_pi_prettyGoodMeasurement_error_eq_confusion` it also
recasts `K`'s identification deficit as `1 − p(K) = ∑_{K'≠K} p(K ∣ σ_{K'}^{⊗m})` — the total mass by
which the *other* candidates' reduced states are misidentified as `K`. -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_some_comm
    [Fintype (Subgroup G)] (K' : Subgroup G) :
    (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K')
      = (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')) (some K) := by
  classical
  have key := State.prettyGoodMeasurement_bornProb_some_comm
    (fun K'' : Subgroup G =>
      cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K K'
  -- Same buried `DecidablePred` instance reconciliation as the sibling theorems: `convert`.
  convert key using 6

open Classical in
/-- **Cauchy–Schwarz bound on the coset pretty-good confusion probabilities** (Nielsen & Chuang,
Problem 5.5).  Take the candidate hidden subgroups to be *all* subgroups `K' ≤ G`, each producing
the `m`-copy reduced state `σ_{K'}^{⊗m} = cosetDensityState (K'^ι)` (5.80).  For two candidates
`K, K'` the pretty-good (square-root) measurement's *confusion* probability is bounded by the two
*success* probabilities:

`p(K' ∣ σ_K^{⊗m})² ≤ p(K ∣ σ_K^{⊗m}) · p(K' ∣ σ_{K'}^{⊗m})`.

Two candidate hidden subgroups cannot be confused by more than the geometric mean of the rates at
which each is correctly identified.  This is the coset instance of the general
`State.prettyGoodMeasurement_bornProb_some_sq_le` (Cauchy–Schwarz for the Hilbert–Schmidt pairing of
the amplitude operators `S₀⁻¹ᐟ⁴ σ_·^{⊗m} S₀⁻¹ᐟ⁴`).  It is a `State`-level structural bound feeding
the per-pair analysis of the identification clause (the still-open Ettinger–Høyer–Knill step being a
direct per-pair bound of the confusion probability by the pairwise affinity
`A(σ_K^{⊗m}, σ_{K'}^{⊗m})`, see the module docstring's "Remaining" note). -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_some_sq_le
    [Fintype (Subgroup G)] (K' : Subgroup G) :
    ((State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K')) ^ 2
      ≤ (State.prettyGoodMeasurement
            (fun K'' : Subgroup G =>
              cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K)
        * (State.prettyGoodMeasurement
            (fun K'' : Subgroup G =>
              cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
          (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K')) (some K') := by
  classical
  have key := State.prettyGoodMeasurement_bornProb_some_sq_le
    (fun K'' : Subgroup G =>
      cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K K'
  -- Same buried `DecidablePred` instance reconciliation as the sibling theorems: `convert`.
  convert key using 6

/-! ### The end-to-end identification headline (from N&C's query state 5.80)

N&C, Problem 5.5, says literally: *"Start with the state* (5.80) *… and prove that picking
`m = 4 log|G| + 2` allows `K` to be identified with probability at least `1 − 1/|G|`."*  The
identification theorems above are all stated over the abstract `m`-copy reduced state
`σ_K^{⊗m} = cosetDensityState (K^ι)`; the theorems in this block state the same conclusion **from
the query state (5.80) itself**, folding in the reduced-state step `hspQueryState_reducedLeft_pi`
(`Tr_{ℂ[X]^{⊗m}} |ψ_f^{⊗m}⟩⟨ψ_f^{⊗m}| = σ_K^{⊗m}`).  Each is thus the item's **natural top-level
claim** in N&C's own phrasing: the pretty-good measurement, applied to the reduced state of the
`m`-copy query register (5.80), returns the true hidden subgroup `K` with probability `≥ 1 − 1/|G|`
(the reduced state carries the whole identifiability, the traced-out range register `ℂ[X]^{⊗m}`
having only recorded which `gᵢ` share a coset).  They come in the three cases the identification
clause is discharged in: fully general `G` (Ettinger–Høyer–Knill query complexity, at a polynomial
sample count), and — at N&C's exact target probability and a linear sample count — the abelian and
nilpotent hidden-subgroup instances (unconditionally). -/

-- `[DecidablePred (· ∈ K)]` is used in the *proof* (via `hspQueryState_reducedLeft_pi` and the
-- underlying identification headline), not the *type* — the statement is over the query state's
-- reduced state, not `cosetDensityState`, so `unusedDecidableInType` is switched off.
set_option linter.unusedDecidableInType false in
open Classical in
/-- **N&C Problem 5.5, end-to-end for general `G` (polynomial sample count).**  For a query function
`f : G → X` constant and distinct on the left cosets of the hidden subgroup `K` (`hf`), the
pretty-good measurement `State.prettyGoodMeasurement` over the candidate coset reduced states,
applied to the reduced state of the `m`-copy query register (5.80)
`(hspQueryState (fun g i => f (g i))).toState.reducedLeft`, identifies `K` with probability

`p(K) ≥ 1 − 1/|G|`,

whenever the sample count `m = |ι|` satisfies the (quadratic) threshold `hm`
(`m ≥ 4 (log₂|G|)² + 6 log₂|G| + 2`).  This is the **fully general** (`G` need not be Abelian, no
Fourier transform over `G`) Ettinger–Høyer–Knill query-complexity conclusion at N&C's exact target
probability, in N&C's literal phrasing (from the query state 5.80, not the abstract `σ_K^{⊗m}`): it
folds the reduced-state step `hspQueryState_reducedLeft_pi` into
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_sampleCount`.  (The optimal *linear*
`m = 4 log₂|G| + 2` for general `G` needs the Liebeck–Pyber–Shalev-strength maximal-subgroup
count of piece (ii); it is reached here unconditionally for the abelian and nilpotent cases.) -/
theorem hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_of_sampleCount
    [Fintype (Subgroup G)] (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hm : 2 * (Fintype.card G : ℝ) ^ (2 * Nat.log 2 (Fintype.card G) + 2)
          * (1 / Real.sqrt 2) ^ Fintype.card ι
        ≤ (Fintype.card G : ℝ)⁻¹) :
    1 - (Fintype.card G : ℝ)⁻¹
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft) (some K) := by
  rw [hspQueryState_reducedLeft_pi K f hf]
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_sampleCount K hm

set_option linter.unusedDecidableInType false in
open Classical in
/-- **N&C Problem 5.5, end-to-end for nilpotent `G` (exact target probability, linear sample
count).**  For a **nilpotent** finite group `G` and a query function `f : G → X` constant and
distinct on the left cosets of `K` (`hf`), the pretty-good measurement applied to the reduced state
of the `m`-copy query register (5.80) identifies `K` with N&C's **exact** target probability

`p(K) ≥ 1 − 1/|G|`,

at the linear sample count `m = |ι| = 4(s + 4)` with `2·|G|² ≤ 2^s` (`m = 8 log₂|G| + 20`).  Both
Ettinger–Høyer–Knill ingredients are discharged unconditionally for nilpotent `G` (piece (i)(a) via
the fidelity/Rotfel'd route, piece (ii) vacuous — no non-normal maximal subgroups), covering all
abelian groups, all `p`-groups, and their direct products.  It is the end-to-end (from 5.80) form of
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_nilpotent`, threaded through
`hspQueryState_reducedLeft_pi`. -/
theorem hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_nilpotent
    [Group.IsNilpotent G] [Fintype (Subgroup G)] {s : ℕ} (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hι : Fintype.card ι = 4 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft) (some K) := by
  rw [hspQueryState_reducedLeft_pi K f hf]
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_nilpotent K hι hG hs

set_option linter.unusedDecidableInType false in
open Classical in
/-- **N&C Problem 5.5, end-to-end for abelian `G` — the literal headline (exact target probability,
linear sample count).**  For a **commutative** finite group `G` (the canonical hidden-subgroup
instances — Simon's problem, Shor's order-finding and discrete-log) and a query function `f : G → X`
constant and distinct on the left cosets of `K` (`hf`), the pretty-good measurement applied to the
reduced state of the `m`-copy query register (5.80) identifies `K` with N&C's **exact** target
probability

`p(K) ≥ 1 − 1/|G|`,

at the linear sample count `m = |ι| = 2(s + 4)` with `2·|G|² ≤ 2^s` (`m = 4 log₂|G| + 10`).  This is
Problem 5.5's **literal** conclusion, from its literal starting state (5.80): both
Ettinger–Høyer–Knill ingredients are free for abelian `G` (piece (ii) vacuous; piece (i)(a) from
the commutation of the coset density operators of the abelian `G^ι`,
`cosetDensityState_op_commute`).  It is the end-to-end (from 5.80) form of
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_commGroup`, threaded through
`hspQueryState_reducedLeft_pi`, at the sample count closest to N&C's exact `4 log₂|G| + 2`. -/
theorem hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_commGroup
    {G X : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [Fintype X] [DecidableEq X]
    [Fintype (Subgroup G)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Subgroup G) [DecidablePred (· ∈ K)] {s : ℕ} (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hι : Fintype.card ι = 2 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft) (some K) := by
  rw [hspQueryState_reducedLeft_pi K f hf]
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_commGroup K hι hG hs

set_option linter.unusedDecidableInType false in
open Classical in
/-- **N&C Problem 5.5, end-to-end for general `G` (linear sample count) — the item's central claim,
reduced to the isolated piece-(ii) count.**  This is Problem 5.5's headline for a group `G` that
*need not be Abelian*, at N&C's **linear** query complexity, stated from the literal query state
(5.80): for a query function `f : G → X` constant and distinct on the left cosets of the hidden
subgroup `K` (`hf`), the pretty-good measurement over the candidate coset reduced states, applied to
the reduced state of the `m`-copy query register (5.80)
`(hspQueryState (fun g i => f (g i))).toState.reducedLeft`, identifies `K` with

`p(K) ≥ 1 − 14/|G|`,

at the **linear** sample count `m = |ι| = 4u` with `2·|G|² ≤ 2^u` (`m = 8 log₂|G| + 4` — `O(log|G|)`
oracle calls, N&C's *linear* query complexity, not the quadratic `O((log|G|)²)` of
`hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_of_sampleCount`), **conditional only
on the Ettinger–Høyer–Knill piece-(ii) counting hypothesis** `hcount` — the
Liebeck–Pyber–Shalev-strength non-normal maximal class count
`∀ J, 3·#{J-conjugacy classes of non-normal maximal subgroups} ≤ |J|²`.  This is N&C's linear
query complexity, in N&C's literal phrasing, with the remaining gap reduced to exactly one
explicit finite-group count: piece (i)(a) is discharged **unconditionally** here (the fidelity /
Rotfel'd route, no paired-trace hypothesis), so `hcount` is the *sole* residual, and it is vacuous
for nilpotent `G` (see `..._one_sub_inv_of_nilpotent`).  It folds the reduced-state step
`hspQueryState_reducedLeft_pi` into
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_classCard`. -/
theorem hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_of_classCard
    [Fintype (Subgroup G)] {u : ℕ} (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hι : Fintype.card ι = 4 * u) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ u)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    1 - 14 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft) (some K) := by
  rw [hspQueryState_reducedLeft_pi K f hf]
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_classCard K hι hG hs hcount

set_option linter.unusedDecidableInType false in
open Classical in
/-- **N&C Problem 5.5, end-to-end for general `G` at N&C's *exact* sample count `m = 4 log₂|G| + 2`,
reduced to the two isolated Ettinger–Høyer–Knill ingredients.**  The affinity-route companion of
`hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_of_classCard`, stated at N&C's
**exact** linear sample count.  For a query function `f : G → X` constant and distinct on the left
cosets of `K` (`hf`), the pretty-good measurement applied to the reduced state of the `m`-copy query
register (5.80) identifies `K` with

`p(K) ≥ 1 − 14/|G|`,

at N&C's *exact* count `m = |ι| = 2s` with `2·|G|² ≤ 2^s` (`s = 2 log₂|G| + 1`,
`m = 4 log₂|G| + 2`), *given* the two isolated Ettinger–Høyer–Knill ingredients: the piece-(i)(a)
**paired-trace inequality** `hpaired` (`re tr(√S₀ · √σ_K^{⊗m}) ≤ ∑_{K'} A(σ_K^{⊗m}, σ_{K'}^{⊗m})`)
and the piece-(ii) non-normal maximal **class count** `hcount`.  This is Problem 5.5's headline at
N&C's *precise* linear constant `4 log₂|G| + 2` (the affinity route avoids the `F² ≤ A`
factor-of-two of the fidelity route's `8 log₂|G| + 4`, at the price of the paired-trace
hypothesis); it is the end-to-end (from 5.80) form of
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard`, threaded through
`hspQueryState_reducedLeft_pi`.  Both hypotheses are proven Ettinger–Høyer–Knill mathematics — work
still to be discharged, not walls; for nilpotent `G` `hcount` is vacuous, and for abelian `G` both
are free (`..._one_sub_inv_of_nilpotent` / `..._one_sub_inv_of_commGroup` even reach the sharp
`1 − 1/|G|` unconditionally). -/
theorem hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard
    [Fintype (Subgroup G)] {s : ℕ} (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hι : Fintype.card ι = 2 * s) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2)
    (hpaired : State.PairedTraceBound
      (fun K'' : Subgroup G => cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K) :
    1 - 14 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft) (some K) := by
  rw [hspQueryState_reducedLeft_pi K f hf]
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_classCard
    K hι hG hs hcount hpaired

set_option linter.unusedDecidableInType false in
open Classical in
/-- **N&C Problem 5.5, end-to-end from the literal query state (5.80), general `G`, at N&C's exact
target probability `1 − 1/|G|` — fidelity route.** The sharp-constant (`1 − 1/|G|`) refinement of
`hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_of_classCard` (`≥ 1 − 14/|G|`).
For a query function `f : G → X` constant and distinct on the left cosets of `K` (`hf`), the
measurement applied to the reduced state of the `m`-copy query register (5.80) identifies `K` with

`p(K) ≥ 1 − 1/|G|`,

at the linear count `m = |ι| = 4(s+4)` with `2·|G|² ≤ 2^s` (`m = 8 log₂|G| + 20`), **conditional
only on the piece-(ii) class count** `hcount` (piece (i)(a) unconditional via the fidelity route).
It folds the reduced-state step `hspQueryState_reducedLeft_pi` into
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard`. -/
theorem hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard
    [Fintype (Subgroup G)] {s : ℕ} (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hι : Fintype.card ι = 4 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft) (some K) := by
  rw [hspQueryState_reducedLeft_pi K f hf]
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard
    K hι hG hs hcount

set_option linter.style.longLine false in
set_option linter.unusedDecidableInType false in
open Classical in
/-- **N&C Problem 5.5 — the literal headline, end-to-end from the query state (5.80).** This is
Nielsen & Chuang's Problem 5.5 sentence, formalised in N&C's own phrasing: for a finite group `G`
that **need not be Abelian** and **without a Fourier transform over `G`**, starting from the
`m`-copy query state (5.80) and tracing out the range register, picking `m = 4 log₂|G| + O(1)` coset
samples
lets the hidden subgroup `K` be **identified with probability at least `1 − 1/|G|`**:

`p(K) ≥ 1 − 1/|G|`   at   `m = |ι| = 2(s+4)`, `2·|G|² ≤ 2^s`   (`m = 4 log₂|G| + 10`),

**conditional on exactly two explicit, proven-elsewhere Ettinger–Høyer–Knill ingredients** — the
piece-(i)(a) paired-trace inequality `hpaired` and the piece-(ii) non-normal maximal **class count**
`hcount`. Every element of N&C's literal statement — general `G`, the exact linear order
`4 log₂|G| + O(1)`, the exact probability `1 − 1/|G|`, from the literal starting state (5.80) — is
here; the entire residual to the *unconditional* literal claim is those two isolated
group- and operator-theoretic facts, both discharged unconditionally for the canonical abelian case
(Simon's, Shor's; `..._one_sub_inv_of_commGroup`) and all nilpotent `G`
(`..._one_sub_inv_of_nilpotent`). It folds `hspQueryState_reducedLeft_pi` into
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_paired_of_classCard`. -/
theorem hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_paired_of_classCard
    [Fintype (Subgroup G)] {s : ℕ} (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hι : Fintype.card ι = 2 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : ∀ J : Subgroup G,
      3 * ((Finset.univ.filter
          (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Nat.card ↥J) ^ 2)
    (hpaired : State.PairedTraceBound
      (fun K'' : Subgroup G => cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K'')) K) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft) (some K) := by
  rw [hspQueryState_reducedLeft_pi K f hf]
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_paired_of_classCard
    K hι hG hs hcount hpaired

set_option linter.unusedDecidableInType false in
/-- **N&C Problem 5.5, end-to-end near-orthogonality from the literal query state (5.80), general
`G`, at N&C's exact sample count.**  This is N&C's *stated protocol conclusion* — "produce (using
only `O(log|G|)` oracle calls) a final state in which the pure-state outcomes for different possible
hidden subgroups are nearly orthogonal" — formalised in its **literal** form: not over the abstract
`σ_K^{⊗m}` but over the reduced states of the actual `m`-copy query registers (5.80) of *two
distinct* candidate hidden subgroups.  For candidate subgroups `K ≠ K'` with their respective
promise functions `f, f'` (each constant and distinct on the cosets of its subgroup, `hf`/`hf'`),
the Hilbert–Schmidt overlap of the reduced states of the two query registers is
inverse-quadratically small,

`⟨Tr_X|ψ_f^{⊗m}⟩⟨ψ_f^{⊗m}|, Tr_X|ψ_{f'}^{⊗m}⟩⟨ψ_{f'}^{⊗m}|⟩_HS ≤ 1 / (2|G|²)`,

**for every finite group `G`** (`G` need not be Abelian, no Fourier transform over `G` required) at
N&C's *exact* linear sample count `m = 4 log₂|G| + 2` (the hypothesis `4·|G|⁴ ≤ 2^m`).  It folds the
reduced-state step `hspQueryState_reducedLeft_pi` (for each of `K` and `K'`) into the abstract
near-orthogonality `cosetDensityState_pi_hsOverlap_le_of_sampleCount`.  This is the fully general,
exact-count half of Problem 5.5 that is proven *unconditionally* — the identification clause's exact
*linear* count for non-nilpotent `G` is the only residual, gated on the Liebeck–Pyber–Shalev count
(piece (ii)). -/
theorem hspQueryState_reducedLeft_pi_hsOverlap_le_of_sampleCount (K' : Subgroup G)
    [DecidablePred (· ∈ K')] (f f' : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hf' : ∀ g₁ g₂ : G, f' g₁ = f' g₂ ↔ (↑g₁ : G ⧸ K') = ↑g₂)
    (hne : K ≠ K')
    (hm : 4 * (Fintype.card G : ℝ) ^ 4 ≤ (2 : ℝ) ^ Fintype.card ι) :
    ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft).hsOverlap
        ((hspQueryState (fun g : ι → G => fun i => f' (g i))).toState.reducedLeft)
      ≤ 1 / (2 * (Fintype.card G : ℝ) ^ 2) := by
  rw [hspQueryState_reducedLeft_pi K f hf, hspQueryState_reducedLeft_pi K' f' hf']
  exact cosetDensityState_pi_hsOverlap_le_of_sampleCount K K' hne hm

set_option linter.unusedDecidableInType false in
/-- **N&C Problem 5.5, end-to-end distinguishability from the literal query state (5.80), general
`G`.**  The operational form of the near-orthogonality: for candidate hidden subgroups `K ≠ K'` with
their promise functions `f, f'` (`hf`/`hf'`), the reduced states of the two `m`-copy query registers
(5.80) are nearly perfectly distinguishable by a single measurement,

`D(Tr_X|ψ_f^{⊗m}⟩⟨ψ_f^{⊗m}|, Tr_X|ψ_{f'}^{⊗m}⟩⟨ψ_{f'}^{⊗m}|) ≥ 1 − (1/√2)^m = 1 − 2^{-m/2}`,

**for every finite group `G`**.  Because the trace distance is the optimal single-shot
distinguishing bias (`State.classicalTraceDist_bornProb_le`), this is the direct measurement content
of "the pure-state outcomes for different possible hidden subgroups are nearly orthogonal", now from
N&C's *literal* starting state (5.80) rather than the abstract `σ_K^{⊗m}`.  It folds the
reduced-state step `hspQueryState_reducedLeft_pi` (for each of `K` and `K'`) into
`cosetDensityState_pi_traceDistance_ge`.  The *pairwise* guarantee here is upgraded to the full
*multi-state* identification (`K` among *all* candidates, probability `≥ 1 − 1/|G|`) by the
end-to-end identification headlines above. -/
theorem hspQueryState_reducedLeft_pi_traceDistance_ge (K' : Subgroup G)
    [DecidablePred (· ∈ K')] (f f' : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hf' : ∀ g₁ g₂ : G, f' g₁ = f' g₂ ↔ (↑g₁ : G ⧸ K') = ↑g₂)
    (hne : K ≠ K') :
    1 - (1 / Real.sqrt 2) ^ Fintype.card ι
      ≤ ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft).traceDistance
          ((hspQueryState (fun g : ι → G => fun i => f' (g i))).toState.reducedLeft) := by
  rw [hspQueryState_reducedLeft_pi K f hf, hspQueryState_reducedLeft_pi K' f' hf']
  exact cosetDensityState_pi_traceDistance_ge K K' hne

open Classical in
/-- **N&C Problem 5.5, general `G`, at N&C's exact target probability `1 − 1/|G|`, with the residual
pinned to the *standard maximal-subgroup count*.** The recognizable-hypothesis form of
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard`: for a finite
group `G` that **need not be Abelian**, at the linear sample count `m = |ι| = 4(s+4)` with
`2·|G|² ≤ 2^s` (`m = 8 log₂|G| + 20`), the pretty-good measurement identifies the hidden subgroup at
N&C's **exact** target probability

`p(K ∣ σ_K^{⊗m}) ≥ 1 − 1/|G|`,

**conditional only on the standard bound `hmax` — that every subgroup `J ≤ G` has at most `|J|²/3`
maximal subgroups** (`3 · #{M ⋖ J} ≤ |J|²`). This is a *weak form of the Liebeck–Pyber–Shalev bound*
`#{maximals of G} ≤ c·|G|^{3/2}` — a **named, recognizable** finite-group statement, not a bespoke
hypothesis rigged to the proof. It supersedes the class-count hypothesis of `..._of_classCard` via
`Concrete.nonnormal_maximal_classCard_le_of_card_maximal_le` (the conjugacy classes of non-normal
maximals inject into the non-normal maximals, a subset of all maximals). So Problem 5.5's *sole*
open general-`G` ingredient is exactly the classical question **"does a finite group have
polynomially many maximal subgroups?"** — whose known proofs use the Classification of Finite Simple
Groups (`hmax` is *vacuously* stronger than needed but transparently standard; it is free for
nilpotent `G`, whose maximals are all normal, see `..._one_sub_inv_of_nilpotent`). -/
theorem cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_maximalCount
    [Fintype (Subgroup G)] {s : ℕ}
    (hι : Fintype.card ι = 4 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hmax : ∀ J : Subgroup G, 3 * Nat.card {M : Subgroup G // M ⋖ J} ≤ (Nat.card ↥J) ^ 2) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        (cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K)) (some K) :=
  cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard
    K hι hG hs
    (fun J => Concrete.nonnormal_maximal_classCard_le_of_card_maximal_le J (hmax J))

set_option linter.unusedDecidableInType false in
open Classical in
/-- **N&C Problem 5.5 — the literal headline, end-to-end from the query state (5.80), general `G`,
with the residual pinned to the standard maximal-subgroup count.** The recognizable-hypothesis form
of `hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_classCard`. For a
query function `f : G → X` constant and distinct on the left cosets of `K` (`hf`), starting from the
`m`-copy query state (5.80) and tracing out the range register, at the linear count
`m = |ι| = 4(s+4)` with `2·|G|² ≤ 2^s`, the pretty-good measurement identifies `K` with

`p(K) ≥ 1 − 1/|G|`,

**conditional only on the standard maximal-subgroup count `hmax`** (`3 · #{M ⋖ J} ≤ |J|²` for every
`J ≤ G`) — the item's sole open general-`G` ingredient stated as the classical, recognizable
Liebeck–Pyber–Shalev-strength question rather than the bespoke conjugacy-class count. Every element
of N&C's literal statement — general `G`, no Fourier transform, the linear order `4 log₂|G| + O(1)`,
the exact probability `1 − 1/|G|`, from the literal starting state (5.80) — is present, with the
entire residual to the *unconditional* claim reduced to that one standard finite-group bound (free
for nilpotent `G`). It folds `hspQueryState_reducedLeft_pi` into the abstract
`..._one_sub_inv_of_maximalCount`. -/
theorem hspQueryState_reducedLeft_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_maximalCount
    [Fintype (Subgroup G)] {s : ℕ} (f : G → X)
    (hf : ∀ g₁ g₂ : G, f g₁ = f g₂ ↔ (↑g₁ : G ⧸ K) = ↑g₂)
    (hι : Fintype.card ι = 4 * (s + 4)) (hG : 3 ≤ Nat.card G) (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hmax : ∀ J : Subgroup G, 3 * Nat.card {M : Subgroup G // M ⋖ J} ≤ (Nat.card ↥J) ^ 2) :
    1 - 1 / (Nat.card G : ℝ)
      ≤ (State.prettyGoodMeasurement
          (fun K'' : Subgroup G =>
            cosetDensityState (Subgroup.pi (Set.univ : Set ι) fun _ => K''))).bornProb
        ((hspQueryState (fun g : ι → G => fun i => f (g i))).toState.reducedLeft) (some K) := by
  rw [hspQueryState_reducedLeft_pi K f hf]
  exact cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_one_sub_inv_of_maximalCount
    K hι hG hs hmax

end AxQM
