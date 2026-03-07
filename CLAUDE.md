# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 formalization of **Synthetic Differential Geometry** (SDG), following Anders Kock's book [Synthetic Differential Geometry](https://users-math.au.dk/kock/sdg99.pdf). The project depends on a custom fork of Mathlib4 (`riccardobrasca/mathlib4`, branch `less_choice`) that avoids `Classical.choice`.

## Build Commands

```bash
# Get Mathlib cache
lake exe cache get

# Build the project
lake build SDG

# Keep the root import file up to date after adding new .lean files
lake exe mk_all
# or check it is up to date:
lake exe mk_all --check
```

There is no separate test command — building the project IS the test. All files are type-checked by `lake build SDG`.

## Key Axiom

The project introduces a single custom axiom in `SDG/Axiom/UniqueChoice.lean`:

```lean
axiom axiom_unique_choice (h : ∃! (_ : α), True) : α
```

This is a weak form of choice (unique choice). The `detectClassical` linter (in `SDG/Linters/choice.lean`) warns whenever `Classical.choice` or `sorryAx` is used — keeping the formalization free of classical logic where possible.

## Architecture

### Core layers (bottom to top)

1. **`SDG/Axiom/UniqueChoice.lean`** — The unique choice axiom and derived utilities (`unique_choice`, `unique_choice_fun`, `unique_choice_fun_spec`).

2. **`SDG/Basic/Defs.lean`** — Core definitions:
   - `𝔻 R k` — the subsemigroup `{x : R | x^(k+1) = 0}` (nilpotent elements of order k)
   - `D R = 𝔻 R 1` — the "first-order infinitesimals" (`x^2 = 0`)
   - `IsKockLawvere_one R` — the Kock-Lawvere axiom for `D R`: every `g : D R → R` is uniquely of the form `g d = g 0 + b * d`
   - `IsKockLawvere R` — the general axiom for `𝔻 R k`: every `g : 𝔻 R k → R` is a unique polynomial in `d` of degree `k`
   - `derivFun f : R → R` — the synthetic derivative, constructed from unique choice

3. **`SDG/Basic/D.lean`** — Lemmas about `D R` and `𝔻 R k`: membership, products, powers, sums of nilpotents.

4. **`SDG/Basic/FactorialInv.lean`** — The `Divisible R` typeclass (all nonzero naturals are invertible in `R`), plus factorial invertibility lemmas.

### One-variable calculus (`SDG/IsKockLawvere_one/`)

- **`Basic.lean`** — `cancel_d` (infinitesimal cancellation), `cancel_d_fun` (iterated version), `D_neq_zero`.
- **`Deriv.lean`** — The derivative `∂f` (notation for `derivFun f`) as a `Derivation R (R→R) (R→R)`. Proves: `taylor_one`, `chain_rule`, `deriv_mul`, `deriv_X_pow`, etc.
- **`PartialDeriv.lean`** — Partial derivatives `∂_[i]f` for multivariate functions `(Fin n → R) → R`. Proves commutativity of partial derivatives (`partial_deriv_comm`), `partial_taylor_one`, and `prop41_ex` (a representation theorem for functions `(Fin n → D R) → R`).
- **`Alpha.lean`** — Shows `DualNumber R ≃ (D R → R)` via the algebra map `α`, with injectivity and surjectivity under `IsKockLawvere_one`.
- **`EM.lean`** — Related results.

### Higher-order / multivariate calculus (`SDG/IsKockLawvere/`)

- **`Taylor.lean`** — Taylor theorems: `taylor_one`, `taylor_two`, `taylor_k` (general Taylor expansion `f(x+δ) = Σ ∂^[n]f(x) * δ^n * ⅟(n!)` for `δ : 𝔻 R k`).
- **`TaylorMulti.lean`** — Multivariate Taylor theorem (work in progress, some `sorry`s). Defines `mixed_partial_deriv k f` (notation `∂[k]f`) via `foldl` of iterated partial derivatives.

### Notation summary

| Notation | Meaning |
|---|---|
| `D R` | `{x : R \| x^2 = 0}` |
| `𝔻 R k` | `{x : R \| x^(k+1) = 0}` |
| `∂f` | derivative of `f : R → R` |
| `∂^[n]f` | n-th iterate of `∂` |
| `∂_[i]f` | partial derivative w.r.t. coordinate `i` |
| `∂_[i]^[k]f` | k-th iterated partial derivative w.r.t. `i` |
| `∂[k]f` | mixed partial derivative indexed by `k : Fin n → ℕ` |

## Linter Settings

From `lakefile.toml`:
- `autoImplicit = false`, `relaxedAutoImplicit = false` — all variables must be explicit.
- `linter.flexible = true` — no rigid tactics (e.g. `exact`) after flexible tactics (e.g. `simp`).
- `linter.mathlibStandardSet = true` — Mathlib's standard linter set is active.
- `weak.linter.verbose.detectClassical = true` — warns on use of `Classical.choice`.
- `warn.sorry = false` — sorry warnings are suppressed (some files have in-progress `sorry`s).
