# Irreducibility of an arithmetic-progression polynomial

For every integer **n ≥ 2**, the polynomial

$$
f_n(x)=x^{n-1}+2x^{n-2}+\cdots+(n-1)x+n
$$

is irreducible over **ℚ** and **ℤ**.

- [Proof.lean](Proof.lean): complete Lean 4 proof, without `sorry` or custom axioms.
- [proof.pdf](proof.pdf): mathematical exposition.
- [proof.tex](proof.tex): LaTeX source.

The exposition proves the case **n ≥ 1000** by comparing resultant bounds from complex root estimates and p-adic Newton polygons, after excluding factor constant terms below 5. It checks **2 ≤ n < 1000** by computer and also gives an argument avoiding those computations.

## Lean formalization

The Lean proof covers every **n ≥ 2** without checking cases individually.

In the namespace `EventualIrreducibility`, the polynomial is defined by:

```lean
noncomputable def fInt (n : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range n, monomial j ((n - j : ℕ) : ℤ)

noncomputable def fQ (n : ℕ) : ℚ[X] :=
  (fInt n).map (Int.castRingHom ℚ)
```

The final theorem statements are:

```lean
theorem universal_irreducible_rat (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (fQ n)

theorem universal_irreducible_int (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (fInt n)
```
