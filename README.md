# Irreducibility of an arithmetic-progression polynomial

This repository contains a Lean 4 proof that, for every integer **n ≥ 2**,

$$
f_n(x)=\sum_{k=1}^{n}kx^{n-k}
=x^{n-1}+2x^{n-2}+\cdots +(n-1)x+n
$$

is irreducible over both **ℚ** and **ℤ**. The parameter `n` is the constant coefficient; the degree is `n - 1`. The case `n = 1` is excluded because the polynomial is the unit `1`.

## Files

- [Proof.lean](Proof.lean): the complete formalization in one file.
- [proof.tex](proof.tex): a concise mathematical exposition, organized as lemmas and a theorem; a standalone source for pdfLaTeX or Overleaf using standard LaTeX packages.
- `proof.pdf`: the existing PDF, left unchanged in this documentation update. Regenerate it from the new `proof.tex` before using it as the exposition.

## Main theorem in Lean

The polynomial is defined by ascending coefficients:

```lean
noncomputable def fInt (n : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range n, monomial j ((n - j : ℕ) : ℤ)

noncomputable def fQ (n : ℕ) : ℚ[X] :=
  (fInt n).map (Int.castRingHom ℚ)
```

The final declarations, in the namespace `EventualIrreducibility`, are:

```lean
theorem universal_irreducible_rat (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (fQ n)

theorem universal_irreducible_int (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (fInt n)
```

Both are unconditional. Despite the historical namespace name, the conclusion covers **every** `n ≥ 2`. There is no numerical cutoff, finite verification of the remaining parameters, or Stewart–Yu assumption.

## Proof idea

Suppose `f_n = gh` is a nontrivial monic integer factorization, and write `a = g(0)`, `b = h(0)`, and `N = n + 1`.

1. **Roots and coefficients.** The identity `(x - 1)² f_n = xᴺ - Nx + n` places every root in a thin annulus outside the unit circle. The constants satisfy `ab = n` and `gcd(a,b) = 1`. A small integer formed from two coefficients of `g` is divisible by every prime dividing `bN`.
2. **Local resultants.** Newton polygons describe the root clusters at primes dividing `nN`. Assigning their irreducible blocks to `g` or `h` gives a weighted cut problem and a sharp bound on each valuation of `Res(g,h)`. A separate discriminant argument handles the initial quartic at the prime `2`.
3. **Small constants.** Cyclotomic resultants exclude prime-power values of `N`. The coefficient divisibility then forces `a,b ≥ 13`, hence `n ≥ 182` in any hypothetical factorization.
4. **The contradiction.** An upper estimate for `Disc(g)` from the root annulus is incompatible with the local resultant bounds, through the exact identity

   $$
   |\mathrm{Disc}(g)|\,|\mathrm{Res}(g,h)|\,a\,g(1)=(nN)^{\deg g}.
   $$

   Elementary inequalities cover all `n ≥ 182`, completing the proof.

The LaTeX exposition includes the local block calculation, the binary exception, the small-constant argument, and the final inequalities.

## Formalization status

The final source contains no `sorry`, `admit`, custom axioms, or suppressed linters. The local field inputs are proved as well: extension to a valued splitting field, factors selected by root valuation, and the complete discrete valued field with the required roots of unity. The latter construction uses Witt vectors, a fraction field, and completion.

The final theorems depend only on Lean's foundational axioms `propext`, `Classical.choice`, and `Quot.sound`, as reported by `#print axioms` at the end of the file.

The identical source was previously checked through **AXLE MCP in its Lean 4.33.0 environment**, with no permitted proof omissions, no failed declarations, **zero errors and zero warnings**. Verification request: `42513406-6b3b-496b-9068-698487ba1863`.

SHA-256 of that verified `Proof.lean`:

```text
E74000ACF6FF3FDD14063A8FED7D1787C2F5E17A4B5D499DD8DA53D4CF0C0ADD
```

This repository pins **Lean 4.33.1 and Mathlib v4.33.1**, with `autoImplicit = false`. Those local project settings differ from the recorded verification environment. No local Lean build was run during this documentation update; the verification statement above applies to the recorded AXLE environment.
