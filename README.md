# Synthetic Differential Geometry in Lean 4

A formalization of Synthetic Differential Geometry (SDG) in [Lean 4](https://lean-lang.org/), following Anders Kock's book [*Synthetic Differential Geometry*](https://users-math.au.dk/kock/sdg99.pdf).

## Overview

Synthetic Differential Geometry develops differential calculus axiomatically, working in a ring `R` that contains nilpotent infinitesimals: elements `d` with `d^2 = 0`. The **Kock-Lawvere axiom** states that every function on these infinitesimals is uniquely affine, giving a purely algebraic foundation for derivatives, Taylor expansions, and multivariate calculus -- without limits, epsilon-delta arguments, or classical logic.

This project formalizes:
- The **Kock-Lawvere axiom** in first-order (`IsKockLawvere_one`) and general (`IsKockLawvere`) forms
- The **synthetic derivative** `∂f` as a formal `Derivation`, with the Leibniz rule, chain rule, and power rule
- **Partial derivatives** `∂_[i]f` for multivariate functions, with commutativity of mixed partials
- **Taylor's theorem** in one variable (`taylor_k`) and multiple variables (`taylor_multi`)
- **Incompatibility with classical logic**: the axiom system is genuinely constructive

The only custom axiom is a weak form of choice (unique choice):
```lean
axiom axiom_unique_choice (h : ∃! (_ : α), True) : α
```

A custom linter (`detectClassical`) warns whenever `Classical.choice` is used, keeping the formalization free of classical axioms.

## Building

The project depends on a custom fork of [Mathlib4](https://github.com/riccardobrasca/mathlib4/tree/less_choice) that limits the use of `Classical.choice`. For the same reason it also uses a custom form of [Lean](https://github.com/riccardobrasca/lean4/tree/less_choice) and [batteries](https://github.com/riccardobrasca/batteries/tree/less_choice). For more details
see [here](https://github.com/leanprover-community/mathlib4/pull/35685).

```bash
# Fetch the dependencies and the Mathlib cache -- use this script, not
# `lake exe cache get`, and do not run `lake update` first
./scripts/cache-get.sh

# Build the project
lake build SDG
```

Building the project type-checks all files; there is no separate test command.

### Getting the cache

Use `./scripts/cache-get.sh`. **Plain `lake exe cache get` downloads nothing
here** and leaves you recompiling the whole of Mathlib, which takes hours.

The reason is that our Mathlib is a branch of a fork built with a custom Lean
toolchain. Upstream Mathlib CI does not build such branches, so its compiled
files are not on the official cache server. They are hosted on
webusers.imj-prg.fr instead, and the script points `lake exe cache` there:

```bash
MATHLIB_CACHE_GET_URL=https://webusers.imj-prg.fr/~riccardo.brasca/mathlib-cache \
  lake exe cache get --repo=riccardobrasca/mathlib4
```

`cache` only asks for files named after the hash of your exact Mathlib sources
and toolchain, so it never fetches files built for another commit.

On a fresh clone the script first fetches the dependencies at the revisions
pinned in `lake-manifest.json`. Do not use `lake update` for that: it moves
Mathlib to the tip of the `less_choice` branch, which may not have a cache yet.
When you do run `lake update` on purpose, Mathlib prints "You should run
`lake exe cache get` manually"; run `./scripts/cache-get.sh` instead.

The script passes its arguments through to `lake exe cache`, so you can also say:

```bash
./scripts/cache-get.sh get!                  # re-download everything
./scripts/cache-get.sh Mathlib.Logic.Pairwise   # just this module and its imports
```

The cache only ever covers the dependencies (Mathlib, Batteries, Aesop, ...),
never SDG's own files: those are always compiled locally by `lake build SDG`.

CI does the same thing through the `MATHLIB_CACHE_GET_URL` environment
variable; see `.github/workflows/build-project.yml`.

## File structure

### Axioms and infrastructure (`SDG/Axiom/`)
- `UniqueChoice.lean` -- The unique choice axiom and derived utilities
- `Instances.lean` -- Type class instances to bypass classical choice
- `BigOperators.lean` -- Classical-choice-free re-proofs of Mathlib `Finset` lemmas

### Core definitions (`SDG/Basic/`)
- `Defs.lean` -- `D R`, `𝔻 R k`, `IsKockLawvere_one`, `IsKockLawvere`, `deriv_fun`
- `D.lean` -- Algebraic properties of nilpotent subsemigroups

### One-variable calculus (`SDG/IsKockLawvere_one/`)
- `Basic.lean` -- Infinitesimal cancellation (`cancel_d`)
- `Deriv.lean` -- Synthetic derivative `∂f` as a `Derivation`; Taylor's theorem, chain rule, Leibniz rule, power rule
- `PartialDeriv.lean` -- Partial derivatives `∂_[i]f` and commutativity of mixed partials
- `EM.lean` -- The Kock-Lawvere axiom contradicts classical logic

### Higher-order and multivariate calculus (`SDG/IsKockLawvere/`)
- `Taylor.lean` -- Taylor's theorem: `f(x+δ) = Σ ∂^[n]f(x) * δ^n / n!` for `δ ∈ 𝔻 R k`
- `TaylorMulti.lean` -- Multivariate Taylor theorem with mixed partial derivatives `∂[k]f`

### Notation

| Notation | Meaning |
|---|---|
| `D R` | `{x : R \| x^2 = 0}` |
| `𝔻 R k` | `{x : R \| x^(k+1) = 0}` |
| `∂f` | synthetic derivative of `f : R → R` |
| `∂^[n]f` | n-th iterated derivative |
| `∂_[i]f` | partial derivative w.r.t. coordinate `i` |
| `∂[k]f` | mixed partial derivative indexed by `k : Fin n → ℕ` |

## Authors

- **Riccardo Brasca** ([riccardo.brasca@gmail.com](mailto:riccardo.brasca@gmail.com))
- **Gabriella Clemente** ([gabriella.clemente@cnrs.fr](mailto:gabriella.clemente@cnrs.fr))
