# AxQM

A Lean 4 formalization of Nielsen & Chuang, *Quantum Computation and Quantum Information*
(tenth-anniversary edition), in which every quantum notion is grounded in the postulates of quantum
mechanics. It accompanies the paper *Autonomous formalisation of finite-dimensional quantum
mechanics grounded in axiomatic foundations* (W. W. Yin, J. M. Taylor, D. R. Englund,
F. H. L. Koppens), which describes how the library was produced.

Of the book's 687 numbered items, 505 are formalised. For 16 of them the library proves that the
printed statement is false and proves a corrected one; for 12 more it proves a corrected statement
only.

## Finding a result

Every numbered item of the book has one file, `AxQM/NC/Ch<N>/<Item>.lean`; Theorem 2.7 is
[`AxQM/NC/Ch2/Theorem2_7.lean`](AxQM/NC/Ch2/Theorem2_7.lean). The index
[`AxQM/NC/README.md`](AxQM/NC/README.md) lists every item with its page, a one-line summary, its
file and its status. Search it for `refuted` or `corrected` to find the items where the book is
wrong.

[The Lean documentation for AxQM](https://axiomatic-ai.github.io/AxQMLib/)

Each item's file opens with a paraphrase of the item and then either

- states the result itself, as one or more `theorem`s in the file, or
- names the declarations elsewhere in the library that state it, with their file.

Pure mathematics, such as the singular value decomposition (Corollary 2.4), is stated in
`ToMathlib/` or `AxQM/Concrete/`, and the item's file points there.

You only need to read the statements. Lean has checked every proof, so a `theorem` whose statement
you accept needs no further checking.

### Notation

| Nielsen & Chuang | Lean | Defined in |
|---|---|---|
| quantum system with state space `H` | `S : QSystem` | `Postulates/QSystem.lean` |
| density operator `ρ`; pure state `\|ψ⟩` | `ρ : State S`; `ψ : PureState S` | `Postulates/StateSpace.lean` |
| unitary evolution `ρ ↦ UρU†`, `\|ψ⟩ ↦ U\|ψ⟩` | `U : Evolution S`; `U.evolve ρ`, `U.evolvePure ψ` | `Postulates/Evolution.lean` |
| measurement `{Mₘ}`; `p(m)`; post-measurement state | `M : Measurement ι S`; `M.bornProb ρ m`; `M.postMeasurement ρ m hp` (`hp : p(m) ≠ 0`) | `Postulates/Measurement.lean` |
| observable `A`; `⟨A⟩` | `A : Observable S`; `ρ.expectation A`, `ψ.expectation A` | `Postulates/Observable.lean` |
| composite system; `\|ψ⟩⊗\|φ⟩`, `ρ⊗σ`, `U⊗V` | `S ⊗ T`; `ψ ⊗ φ`, `ρ ⊗ σ`, `U ⊗ V` | `Postulates/Composite.lean` |
| reduced states `tr_B ρ^{AB}`, `tr_A ρ^{AB}` | `ρ.reducedLeft`, `ρ.reducedRight` | `Postulates/PartialTrace.lean` |
| ensemble `{pᵢ, \|ψᵢ⟩}`; mixture `∑ᵢ pᵢρᵢ` | `Ensemble S`; `State.mix p hp hsum ρ` | `Postulates/API/Ensemble.lean`, `Postulates/API/Mixture.lean` |
| qubit; `n⃗·σ⃗` | `qubit`; `pauliObservable n` | `Postulates/API/Qubit.lean` |
| `S(ρ)`; `S(A\|B)` | `ρ.vonNeumannEntropy`; `ρ.condVonNeumannEntropy` | `Postulates/API/Entropy.lean`, `Core/ConditionalEntropy.lean` |
| fidelity; trace distance | `State.fidelity`; `State.traceDistance` | `Postulates/API/` |

Paths are relative to `AxQM/`. `ρ.op` is the density operator of `ρ` as a linear map, and `ψ.vec`
is the state vector of `ψ`.

## What you have to trust

The Lean kernel, Mathlib, the statements you read, and the definitions those statements use. Those
definitions are built from the postulates in [`AxQM/Postulates/`](AxQM/Postulates/), which is where
the physics enters. In the density-operator form of N&C §2.4, the postulates are:

| N&C | File |
|---|---|
| Postulate 1: state space | [`StateSpace.lean`](AxQM/Postulates/StateSpace.lean), [`QSystem.lean`](AxQM/Postulates/QSystem.lean) |
| Postulate 2: evolution | [`Evolution.lean`](AxQM/Postulates/Evolution.lean) |
| Postulate 3: measurement | [`Measurement.lean`](AxQM/Postulates/Measurement.lean), [`Observable.lean`](AxQM/Postulates/Observable.lean) |
| Postulate 4: composite systems, and reduced states (§2.4.3) | [`Composite.lean`](AxQM/Postulates/Composite.lean), [`PartialTrace.lean`](AxQM/Postulates/PartialTrace.lean) |

Every other quantum notion is defined from these, and the statements of the core and textbook
layers refer only to them, never directly to the underlying matrices and vectors: they are
*grounded*. During development, linters checked this. They are not part of this release.

[`AxQM/Meta/Integrity.lean`](AxQM/Meta/Integrity.lean) checks that no declaration of the library is
an `axiom` or depends on an axiom other than Lean's standard `propext`, `Classical.choice` and
`Quot.sound`:

```lean
import ToMathlib
import AxQM
#check_integrity
```

## Layout

| Layer | Directory | Contents |
|---|---|---|
| General mathematics | `ToMathlib/` | Mathematics the library needs that Mathlib does not yet have |
| Concrete mathematics | `AxQM/Concrete/` | Specific matrices, groups, codes and functions |
| Postulates | `AxQM/Postulates/*.lean` | The postulates above |
| Derived | `AxQM/Postulates/API/` | Constructions on the postulates, which may refer to the underlying matrices and vectors |
| Core | `AxQM/Core/` | Physics stated through the postulates alone |
| Textbook | `AxQM/NC/` | The book's numbered items, one file each |

## Building

Lean `v4.36.0` and Mathlib at commit `8b36beaa`, as pinned in `lean-toolchain` and
`lakefile.lean`:

```
lake exe cache get
lake build
```

To browse, open the repository in VS Code with the Lean 4 extension after building. Hovering over
a name shows its type and docstring, and go-to-definition opens its definition in the library or
in Mathlib.

## Using AxQM in your project

Add it to your `lakefile.lean`, using the same Lean toolchain:

```lean
require axqm from git "https://github.com/Axiomatic-AI/AxQMLib" @ "main"
```

and `import AxQM` (and `import ToMathlib` for the general mathematics).

## Licence

Apache License 2.0; see `LICENSE`. `NOTICE` sets out what is original to this repository, what is
not, and how the library relates to the book.

## Citing

See `CITATION.cff`.
