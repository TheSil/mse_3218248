import Mathlib

/-!
# Universal irreducibility of arithmetic-progression polynomials

For every n >= 2, f_n is irreducible over Q and Z. All three standard
local-field inputs are proved. No admitted lemma or custom axiom is used.
This consolidated source retains a conservative dependency closure of the
final proof and the complete newly constructed unramified-field package.
-/

open Polynomial

namespace EventualIrreducibility

noncomputable def fInt (n : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range n, monomial j ((n - j : ℕ) : ℤ)

noncomputable def fQ (n : ℕ) : ℚ[X] :=
  (fInt n).map (Int.castRingHom ℚ)

lemma coeff_fInt (n j : ℕ) :
    (fInt n).coeff j = if j < n then ((n - j : ℕ) : ℤ) else 0 := by
  classical
  simp [fInt, coeff_monomial]

lemma coeff_top (n : ℕ) (hn : 0 < n) : (fInt n).coeff (n - 1) = 1 := by
  rw [coeff_fInt, if_pos (by omega)]
  have h : n - (n - 1) = 1 := by omega
  simp [h]

lemma natDegree_fInt (n : ℕ) (hn : 0 < n) : (fInt n).natDegree = n - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_fInt, if_neg (by omega)]
  · rw [coeff_top n hn]
    norm_num

lemma monic_fInt (n : ℕ) (hn : 0 < n) : (fInt n).Monic := by
  show (fInt n).leadingCoeff = 1
  simpa only [Polynomial.leadingCoeff, natDegree_fInt n hn] using coeff_top n hn

lemma irreducible_int_iff_rat (n : ℕ) (hn : 0 < n) :
    Irreducible (fInt n) ↔ Irreducible (fQ n) := by
  exact (monic_fInt n hn).irreducible_iff_irreducible_map_fraction_map (K := ℚ)

lemma fInt_succ (n : ℕ) : fInt (n + 1) = X * fInt n + C ((n + 1 : ℕ) : ℤ) := by
  ext j
  cases j with
  | zero => simp [coeff_fInt]
  | succ j => simp [coeff_fInt, coeff_X_mul, coeff_one]

lemma two_mul_eval_one (n : ℕ) :
    2 * (fInt n).eval 1 = (n : ℤ) * ((n : ℤ) + 1) := by
  induction n with
  | zero => simp [fInt]
  | succ n ih =>
    rw [fInt_succ]
    simp only [eval_add, eval_mul, eval_X, one_mul, eval_C, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma eval_one_ne_zero (n : ℕ) (hn : 0 < n) : (fInt n).eval 1 ≠ 0 := by
  have hnreal : (0 : ℤ) < n := by exact_mod_cast hn
  have hprod : (0 : ℤ) < (n : ℤ) * ((n : ℤ) + 1) := by positivity
  intro h
  have hh := two_mul_eval_one n
  rw [h] at hh
  nlinarith

lemma trinomial_identity (n : ℕ) :
    (X - 1) ^ 2 * fInt n =
      X ^ (n + 1) - C ((n + 1 : ℕ) : ℤ) * X + C (n : ℤ) := by
  induction n with
  | zero => simp [fInt]
  | succ n ih =>
    rw [fInt_succ]
    calc
      (X - 1) ^ 2 * (X * fInt n + C ((n + 1 : ℕ) : ℤ)) =
          X * ((X - 1) ^ 2 * fInt n) +
            (X - 1) ^ 2 * C ((n + 1 : ℕ) : ℤ) := by ring
      _ = X ^ (n + 1 + 1) - C ((n + 1 + 1 : ℕ) : ℤ) * X +
          C ((n + 1 : ℕ) : ℤ) := by
        rw [ih]
        simp only [Nat.cast_add, Nat.cast_one, map_add, map_one, pow_succ]
        ring

def radical (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

lemma radical_dvd_of_prime_dvd (m : ℕ) (z : ℤ)
    (h : ∀ p ∈ m.primeFactors, (p : ℤ) ∣ z) :
    (radical m : ℤ) ∣ z := by
  by_cases hz : z = 0
  · simp [hz]
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  apply Int.natCast_dvd.mpr
  apply (Nat.prod_primeFactors_dvd_iff hz').mpr
  intro p hp
  exact (Nat.mem_primeFactors.mp hp).1.mem_primeFactors
    (Int.natCast_dvd.mp (h p hp)) hz'

def ResidueSupport (p δ : ℕ) (c : ℕ → ℤ) : Prop :=
  ∀ k, k % p ≠ δ → (p : ℤ) ∣ c k

structure FactorSeries (n : ℕ) where
  factor : ℤ[X]
  monic : factor.Monic
  divides : factor ∣ fInt n
  degree_pos : 0 < factor.natDegree
  degree_lt : factor.natDegree < (fInt n).natDegree

noncomputable def quotientSeries (g : ℤ[X]) : PowerSeries ℤ :=
  PowerSeries.invOfUnit (g.reverse : PowerSeries ℤ) 1 * (g : PowerSeries ℤ)

lemma reverse_mul_quotientSeries (g : ℤ[X]) (hg : g.Monic) :
    (g.reverse : PowerSeries ℤ) * quotientSeries g = (g : PowerSeries ℤ) := by
  have hconst : PowerSeries.constantCoeff (g.reverse : PowerSeries ℤ) =
      ↑(1 : ℤˣ) := by
    simpa only [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse,
      Units.val_one] using hg.leadingCoeff
  unfold quotientSeries
  rw [← mul_assoc, PowerSeries.mul_invOfUnit _ _ hconst, one_mul]

noncomputable def FactorSeries.coeff {n : ℕ} (s : FactorSeries n) (k : ℕ) : ℤ :=
  PowerSeries.coeff k (quotientSeries s.factor)

lemma FactorSeries.quotient_identity {n : ℕ} (s : FactorSeries n) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), s.factor.reverse.coeff i * s.coeff (k - i) =
      s.factor.coeff k := by
  have h := congrArg (PowerSeries.coeff k) (reverse_mul_quotientSeries s.factor s.monic)
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [Polynomial.coeff_coe, FactorSeries.coeff, Nat.succ_eq_add_one] using h

lemma FactorSeries.coeff_zero {n : ℕ} (s : FactorSeries n) :
    s.coeff 0 = s.factor.coeff 0 := by
  have h := s.quotient_identity 0
  simpa [Polynomial.coeff_zero_reverse, s.monic.leadingCoeff] using h

def LocalInput : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ s : FactorSeries n,
    ∀ p : ℕ, p.Prime → p ∣ n * (n + 1) →
      ∃ δ : ℕ, δ ≤ 1 ∧ ResidueSupport p δ s.coeff

def AnalyticInput : Prop :=
  ∀ n : ℕ, 10 ^ 17 ≤ n → ¬ Irreducible (fQ n) →
    ∃ s : FactorSeries n, ∃ k : ℕ,
      s.coeff k ≠ 0 ∧ s.coeff (k + 1) ≠ 0 ∧
      ((s.coeff k).natAbs : ℝ) < 3500 * (Real.log (n : ℝ)) ^ 2 ∧
      ((s.coeff (k + 1)).natAbs : ℝ) < 3500 * (Real.log (n : ℝ)) ^ 2

lemma coeff_pow_char_of_not_dvd {R : Type*} [CommRing R]
    (p : ℕ) (hp : p ≠ 0) [ExpChar R p]
    (T : PowerSeries R) (k : ℕ) (hk : ¬ p ∣ k) :
    PowerSeries.coeff k (T ^ p) = 0 := by
  change MvPowerSeries.coeff (Finsupp.single () k) (T ^ p) = 0
  rw [← MvPowerSeries.map_frobenius_expand p hp, MvPowerSeries.coeff_map]
  rw [MvPowerSeries.coeff_expand_of_not_dvd p hp T (i := ()) (by simpa using hk)]
  exact map_zero _

lemma coeff_shifted_pow_of_wrong_residue (p : ℕ) (hp : p.Prime)
    (δ : ℕ) (hδ : δ ≤ 1) (T : PowerSeries (ZMod p)) (k : ℕ)
    (hk : k % p ≠ δ) :
    PowerSeries.coeff k (PowerSeries.X ^ δ * T ^ p) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hδcases : δ = 0 ∨ δ = 1 := by omega
  rcases hδcases with rfl | rfl
  · simp only [pow_zero, one_mul]
    exact coeff_pow_char_of_not_dvd p hp.ne_zero T k (by
      intro h
      exact hk (Nat.mod_eq_zero_of_dvd h))
  · simp only [pow_one]
    cases k with
    | zero => simp
    | succ k =>
      rw [PowerSeries.coeff_succ_X_mul]
      apply coeff_pow_char_of_not_dvd p hp.ne_zero
      intro h
      have hmod : k % p = 0 := Nat.mod_eq_zero_of_dvd h
      apply hk
      simp [Nat.add_mod, hmod, Nat.mod_eq_of_lt hp.one_lt]

lemma reverse_pow_domain {R : Type*} [Semiring R] [NoZeroDivisors R]
    (P : R[X]) (k : ℕ) : (P ^ k).reverse = P.reverse ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    simpa only [map_one] using (Polynomial.reverse_C (1 : R))
  | succ k ih =>
    simp only [pow_succ, Polynomial.reverse_mul_of_domain, ih]

lemma reverse_X_sub_one {R : Type*} [Ring R] [Nontrivial R] :
    (X - (1 : R[X])).reverse = 1 - X := by
  unfold Polynomial.reverse
  have hd : (X - (1 : R[X])).natDegree = 1 := by
    simpa only [map_one] using (Polynomial.natDegree_X_sub_C (1 : R))
  rw [hd]
  simp

lemma reverse_map_monic {R S : Type*} [Semiring R] [Semiring S] [Nontrivial S]
    (g : R[X]) (hg : g.Monic) (f : R →+* S) :
    g.reverse.map f = (g.map f).reverse := by
  unfold Polynomial.reverse
  rw [hg.natDegree_map f, Polynomial.reflect_map]

lemma reverse_of_reduction_shape {F : Type*} [Field F]
    (P H : F[X]) (δ t p : ℕ)
    (h : P = X ^ δ * (X - 1) ^ t * H ^ p) :
    P.reverse = (1 - X) ^ t * H.reverse ^ p := by
  rw [h, mul_assoc, Polynomial.reverse_X_pow_mul, Polynomial.reverse_mul_of_domain,
    reverse_pow_domain, reverse_pow_domain, reverse_X_sub_one]

lemma coeff_map_frobenius_form (p : ℕ) (hp : p.Prime)
    (S : PowerSeries ℤ) (δ : ℕ) (hδ : δ ≤ 1)
    (a : ZMod p) (T : PowerSeries (ZMod p))
    (h : PowerSeries.map (Int.castRingHom (ZMod p)) S =
      PowerSeries.C a * PowerSeries.X ^ δ * T ^ p) :
    ∀ k, k % p ≠ δ → (p : ℤ) ∣ PowerSeries.coeff k S := by
  intro k hk
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have hc : ((PowerSeries.coeff k S : ℤ) : ZMod p) =
      PowerSeries.coeff k (PowerSeries.map (Int.castRingHom (ZMod p)) S) := by
    simp only [PowerSeries.coeff_map, Int.coe_castRingHom]
  rw [hc, h, mul_assoc, PowerSeries.coeff_C_mul,
    coeff_shifted_pow_of_wrong_residue p hp δ hδ T k hk, mul_zero]

lemma reciprocal_shape_mul {R : Type*} [CommRing R]
    (x h r u : R) (δ t p : ℕ) (hu : r * u = 1) :
    ((1 - x) ^ t * r ^ p) * ((-1) ^ t * x ^ δ * (h * u) ^ p) =
      x ^ δ * (x - 1) ^ t * h ^ p := by
  have huP : r ^ p * u ^ p = 1 := by rw [← mul_pow, hu, one_pow]
  have hs : (-1 : R) ^ t * (1 - x) ^ t = (x - 1) ^ t := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    ((1 - x) ^ t * r ^ p) * ((-1) ^ t * x ^ δ * (h * u) ^ p) =
        x ^ δ * ((-1) ^ t * (1 - x) ^ t) * h ^ p * (r ^ p * u ^ p) := by
      rw [mul_pow]
      ring
    _ = x ^ δ * (x - 1) ^ t * h ^ p := by rw [huP, hs, mul_one]

lemma quotient_map_of_reduction_shape (g : ℤ[X]) (hg : g.Monic)
    (p : ℕ) [Fact p.Prime] (δ t : ℕ) (H : (ZMod p)[X])
    (hshape : g.map (Int.castRingHom (ZMod p)) =
      X ^ δ * (X - 1) ^ t * H ^ p) :
    PowerSeries.map (Int.castRingHom (ZMod p)) (quotientSeries g) =
      PowerSeries.C ((-1 : ZMod p) ^ t) * PowerSeries.X ^ δ *
        ((H : PowerSeries (ZMod p)) * (H.reverse : PowerSeries (ZMod p))⁻¹) ^ p := by
  have hp : p.Prime := Fact.out
  let f : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hP : (g.map f).Monic := hg.map f
  have hH : H ≠ 0 := by
    intro hz
    have hzero : g.map f = 0 := by
      simpa only [hz, zero_pow hp.ne_zero, mul_zero] using hshape
    exact hP.ne_zero hzero
  have hRconst : PowerSeries.constantCoeff (H.reverse : PowerSeries (ZMod p)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hH
  have hunit := PowerSeries.mul_inv_cancel
    (H.reverse : PowerSeries (ZMod p)) hRconst
  have hBconst : PowerSeries.constantCoeff
      ((g.map f).reverse : PowerSeries (ZMod p)) = 1 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse, hP.leadingCoeff]
  have hB : ((g.map f).reverse : PowerSeries (ZMod p)) ≠ 0 := by
    intro hz
    have hh := congrArg PowerSeries.constantCoeff hz
    rw [hBconst, map_zero] at hh
    exact one_ne_zero hh
  have hmul : ((g.map f).reverse : PowerSeries (ZMod p)) *
      PowerSeries.map f (quotientSeries g) = (g.map f : PowerSeries (ZMod p)) := by
    have hh := congrArg (PowerSeries.map f) (reverse_mul_quotientSeries g hg)
    simpa only [map_mul, ← Polynomial.polynomial_map_coe,
      reverse_map_monic g hg f] using hh
  have hrevshape := reverse_of_reduction_shape (g.map f) H δ t p hshape
  apply mul_left_cancel₀ hB
  calc
    ((g.map f).reverse : PowerSeries (ZMod p)) *
        PowerSeries.map f (quotientSeries g) =
        (g.map f : PowerSeries (ZMod p)) := hmul
    _ = ((g.map f).reverse : PowerSeries (ZMod p)) *
        (PowerSeries.C ((-1 : ZMod p) ^ t) * PowerSeries.X ^ δ *
          ((H : PowerSeries (ZMod p)) * (H.reverse : PowerSeries (ZMod p))⁻¹) ^ p) := by
      rw [hrevshape, hshape]
      simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub,
        Polynomial.coe_X, Polynomial.coe_one, map_pow, map_neg, map_one]
      exact (reciprocal_shape_mul PowerSeries.X (H : PowerSeries (ZMod p))
        (H.reverse : PowerSeries (ZMod p)) (H.reverse : PowerSeries (ZMod p))⁻¹
        δ t p hunit).symm

def ReductionShapeInput : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ s : FactorSeries n,
    ∀ p : ℕ, p.Prime → p ∣ n * (n + 1) →
      ∃ δ t : ℕ, ∃ H : (ZMod p)[X], δ ≤ 1 ∧
        s.factor.map (Int.castRingHom (ZMod p)) =
          X ^ δ * (X - 1) ^ t * H ^ p

theorem localInput_of_reductionShape (hshape : ReductionShapeInput) : LocalInput := by
  intro n hn s p hp hpd
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨δ, t, H, hδ, hG⟩ := hshape n hn s p hp hpd
  refine ⟨δ, hδ, ?_⟩
  have hform := quotient_map_of_reduction_shape s.factor s.monic p δ t H hG
  exact coeff_map_frobenius_form p hp (quotientSeries s.factor) δ hδ
    ((-1 : ZMod p) ^ t)
    ((H : PowerSeries (ZMod p)) * (H.reverse : PowerSeries (ZMod p))⁻¹) hform

lemma exists_small_monic_divisor {P : ℤ[X]}
    (hP : P.Monic) (hP1 : P ≠ 1) (hred : ¬ Irreducible P) :
    ∃ g : ℤ[X], g.Monic ∧ g ∣ P ∧
      0 < g.natDegree ∧ g.natDegree < P.natDegree ∧
      g.natDegree ≤ P.natDegree / 2 := by
  rw [hP.irreducible_iff_lt_natDegree_lt hP1] at hred
  push Not at hred
  rcases hred with ⟨g, hg, hdeg, hdiv⟩
  have hd := Finset.mem_Ioc.mp hdeg
  refine ⟨g, hg, hdiv, hd.1, ?_, hd.2⟩
  omega

lemma exists_small_factorSeries (n : ℕ) (hn : 2 ≤ n)
    (hred : ¬ Irreducible (fQ n)) :
    ∃ s : FactorSeries n, s.factor.natDegree ≤ (n - 1) / 2 := by
  have hnpos : 0 < n := by omega
  have h1 : fInt n ≠ 1 := by
    intro h
    have hd := natDegree_fInt n hnpos
    rw [h, Polynomial.natDegree_one] at hd
    omega
  have hredZ : ¬ Irreducible (fInt n) := by
    rw [irreducible_int_iff_rat n hnpos]
    exact hred
  obtain ⟨g, hg, hdiv, hpos, hlt, hhalf⟩ :=
    exists_small_monic_divisor (monic_fInt n hnpos) h1 hredZ
  refine ⟨⟨g, hg, hdiv, hpos, hlt⟩, ?_⟩
  simpa only [natDegree_fInt n hnpos] using hhalf

structure CoefficientWindow (c : ℕ → ℤ) (B : ℝ) where
  K : ℕ
  q : ℕ → ℝ
  beta : ℕ → ℝ
  a : ℝ
  b : ℝ
  U : ℝ
  E : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  scale : ∀ j ∈ Finset.Icc K (2 * K), (c j : ℝ) = a * q j
  beta_lower : ∀ j ∈ Finset.Icc K (2 * K), 2 * b ≤ |beta j|
  beta_upper : ∀ j ∈ Finset.Icc K (2 * K), |beta j| ≤ U
  energy : (∑ j ∈ Finset.Icc K (2 * K), (q j - beta j) ^ 2) ≤ E
  density : 2 * (E / b ^ 2) < (K : ℝ)
  size : a * (U + b) < B

lemma choose_pred_prime_power_not_dvd (p : ℕ) (hp : p.Prime)
    (r M k : ℕ) (hM : 0 < M) (hdiv : p ^ r ∣ M) (hk : k < p ^ r) :
    ¬ p ∣ (M - 1).choose k := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  induction r generalizing M k with
  | zero =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    simpa only [Nat.choose_zero_right] using hp.not_dvd_one
  | succ r ih =>
    obtain ⟨a, ha⟩ := hdiv
    have haPos : 0 < a := by
      by_contra h
      have ha0 : a = 0 := by omega
      simp [ha0] at ha
      omega
    let L : ℕ := p ^ r * a
    have hL : 0 < L := mul_pos (pow_pos hp.pos r) haPos
    have hML : M = p * L := by
      rw [ha]
      dsimp [L]
      rw [pow_succ]
      ring
    have hpredp : p - 1 < p := by omega
    have hdecomp : M - 1 = p * (L - 1) + (p - 1) := by
      have hL1 : L - 1 + 1 = L := by omega
      have hmul : p * L = p * (L - 1) + p := by
        calc
          p * L = p * (L - 1 + 1) := by rw [hL1]
          _ = p * (L - 1) + p := by ring
      omega
    have hmod : (M - 1) % p = p - 1 := by
      rw [hdecomp, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hpredp]
    have hquot : (M - 1) / p = L - 1 := by
      rw [hdecomp, Nat.mul_add_div hp.pos,
        Nat.div_eq_of_lt hpredp, Nat.add_zero]
    have hkquot : k / p < p ^ r := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
      simpa only [pow_succ] using hk
    have hright : ¬ p ∣ (L - 1).choose (k / p) :=
      ih L (k / p) hL ⟨a, rfl⟩ hkquot
    have hleft : ¬ p ∣ (p - 1).choose (k % p) := by
      apply hp.coprime_iff_not_dvd.mp
      apply hp.coprime_choose_of_lt hpredp
      have hkp := Nat.mod_lt k hp.pos
      omega
    have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := M - 1) (k := k) (p := p)
    rw [hmod, hquot] at hlucas
    intro hd
    have hprod := (hlucas.dvd_iff (dvd_refl p)).mp hd
    rcases hp.dvd_mul.mp hprod with h | h
    · exact hleft h
    · exact hright h

lemma choose_valuation_add (p : ℕ) (hp : p.Prime)
    (r M j : ℕ) (hM : 0 < M) (hdiv : p ^ r ∣ M)
    (hj : 0 < j) (hjbound : j ≤ p ^ r) :
    padicValNat p (M.choose j) + padicValNat p j = padicValNat p M := by
  let : Fact p.Prime := ⟨hp⟩
  have hpowM : p ^ r ≤ M := Nat.le_of_dvd hM hdiv
  have hjM : j ≤ M := hjbound.trans hpowM
  have hu := choose_pred_prime_power_not_dvd p hp r M (j - 1) hM hdiv (by omega)
  have hpred : (M - 1).choose (j - 1) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hchoose : M.choose j ≠ 0 := Nat.choose_ne_zero hjM
  have hid : M * (M - 1).choose (j - 1) = M.choose j * j := by
    have hh := Nat.add_one_mul_choose_eq (M - 1) (j - 1)
    have hM1 : M - 1 + 1 = M := by omega
    have hj1 : j - 1 + 1 = j := by omega
    simpa only [hM1, hj1] using hh
  have hv := congrArg (padicValNat p) hid
  rw [padicValNat.mul (by omega : M ≠ 0) hpred,
    padicValNat.mul hchoose (by omega : j ≠ 0),
    padicValNat.eq_zero_of_not_dvd hu] at hv
  omega

lemma choose_successor_valuation_add (p : ℕ) (hp : p.Prime)
    (r M j : ℕ) (hr : 1 ≤ r) (hM : 0 < M) (hdiv : p ^ r ∣ M)
    (hj : 2 ≤ j) (hjbound : j ≤ p ^ r + 1) :
    padicValNat p ((M + 1).choose j) + padicValNat p (j * (j - 1)) =
      padicValNat p M := by
  let : Fact p.Prime := ⟨hp⟩
  have hpowM : p ^ r ≤ M := Nat.le_of_dvd hM hdiv
  have hjM : j ≤ M + 1 := by omega
  have hppow : p ∣ p ^ r := by
    cases r with
    | zero => omega
    | succ r =>
      refine ⟨p ^ r, ?_⟩
      rw [pow_succ]
      ring
  have hpd : p ∣ M := hppow.trans hdiv
  have hnext : ¬ p ∣ M + 1 := by
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_iff_left hpd).mpr (by simpa [Nat.add_comm] using h))
  have hu := choose_pred_prime_power_not_dvd p hp r M (j - 2) hM hdiv (by omega)
  have hpred : (M - 1).choose (j - 2) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hchoose : (M + 1).choose j ≠ 0 := Nat.choose_ne_zero hjM
  have hM1 : M - 1 + 1 = M := by omega
  have hj1 : j - 1 + 1 = j := by omega
  have hj2 : j - 2 + 1 = j - 1 := by omega
  have hfirst : (M + 1) * M.choose (j - 1) = (M + 1).choose j * j := by
    simpa only [hj1] using Nat.add_one_mul_choose_eq M (j - 1)
  have hsecond : M * (M - 1).choose (j - 2) = M.choose (j - 1) * (j - 1) := by
    simpa only [hM1, hj2] using Nat.add_one_mul_choose_eq (M - 1) (j - 2)
  have hid : (M + 1).choose j * j * (j - 1) =
      M * (M + 1) * (M - 1).choose (j - 2) := by
    rw [← hfirst]
    calc
      ((M + 1) * M.choose (j - 1)) * (j - 1) =
          (M + 1) * (M.choose (j - 1) * (j - 1)) := by ring
      _ = (M + 1) * (M * (M - 1).choose (j - 2)) := by rw [← hsecond]
      _ = M * (M + 1) * (M - 1).choose (j - 2) := by ring
  have hM0 : M ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  have hjpred : j - 1 ≠ 0 := by omega
  have hMnext : M + 1 ≠ 0 := by omega
  have hv := congrArg (padicValNat p) hid
  rw [padicValNat.mul (mul_ne_zero hchoose hj0) hjpred,
    padicValNat.mul hchoose hj0,
    padicValNat.mul (mul_ne_zero hM0 hMnext) hpred,
    padicValNat.mul hM0 hMnext,
    padicValNat.eq_zero_of_not_dvd hu,
    padicValNat.eq_zero_of_not_dvd hnext] at hv
  rw [padicValNat.mul hj0 hjpred]
  omega

noncomputable def shiftedTrinomial {R : Type*} [CommRing R] (n : ℕ) (z : R) : R[X] :=
  (X + C z) ^ (n + 1) - C ((n + 1 : ℕ) : R) * (X + C z) + C (n : R)

lemma shiftedTrinomial_eq_comp {R : Type*} [CommRing R] (n : ℕ) (z : R) :
    shiftedTrinomial n z =
      (X ^ (n + 1) - C ((n + 1 : ℕ) : R) * X + C (n : R)).comp (X + C z) := by
  simp [shiftedTrinomial]

lemma shiftedTrinomial_coeff_zero {R : Type*} [CommRing R] (n : ℕ) (z : R) :
    (shiftedTrinomial n z).coeff 0 = z ^ (n + 1) - ((n + 1 : ℕ) : R) * z + (n : R) := by
  simp [shiftedTrinomial, Polynomial.coeff_X_add_C_pow]

lemma shiftedTrinomial_coeff_one {R : Type*} [CommRing R] (n : ℕ) (z : R) :
    (shiftedTrinomial n z).coeff 1 = ((n + 1 : ℕ) : R) * (z ^ n - 1) := by
  unfold shiftedTrinomial
  rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  simp [Polynomial.coeff_X]
  ring

lemma shiftedTrinomial_coeff_ge_two {R : Type*} [CommRing R]
    (n : ℕ) (z : R) (j : ℕ) (hj : 2 ≤ j) :
    (shiftedTrinomial n z).coeff j =
      (((n + 1).choose j : ℕ) : R) * z ^ (n + 1 - j) := by
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  unfold shiftedTrinomial
  rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  simp [Polynomial.coeff_X, Polynomial.coeff_C, hj0, Ne.symm hj1, mul_comm]

lemma shiftedTrinomial_const_of_root_N {R : Type*} [CommRing R]
    (n : ℕ) (z : R) (hz : z ^ (n + 1) = 1) :
    (shiftedTrinomial n z).coeff 0 = ((n + 1 : ℕ) : R) * (1 - z) := by
  rw [shiftedTrinomial_coeff_zero, hz]
  push_cast
  ring

lemma shiftedTrinomial_const_of_root_n {R : Type*} [CommRing R]
    (n : ℕ) (z : R) (hz : z ^ n = 1) :
    (shiftedTrinomial n z).coeff 0 = (n : R) * (1 - z) := by
  rw [shiftedTrinomial_coeff_zero, pow_succ, hz]
  push_cast
  ring

lemma shiftedTrinomial_linear_of_root_n {R : Type*} [CommRing R]
    (n : ℕ) (z : R) (hz : z ^ n = 1) :
    (shiftedTrinomial n z).coeff 1 = 0 := by
  rw [shiftedTrinomial_coeff_one, hz]
  ring

theorem window_numeric_bounds
    (K : ℕ) (delta eta T a ell : ℝ)
    (hK : 0 < K) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (heta : 0 < eta) (hT : 0 < T) (_ha : 0 < a) (_hell : 0 < ell)
    (hbudget : eta * T ≤ (1 - delta) / 65)
    (hsize : a * (delta / T + delta * (1 - delta) / (8 * T)) < 3500 * ell ^ 2) :
    0 < delta * (1 - delta) / (8 * T) ∧
      2 * ((32 * (K : ℝ) * delta ^ 2 * eta ^ 2) /
        (delta * (1 - delta) / (8 * T)) ^ 2) < (K : ℝ) ∧
      a * (delta / T + delta * (1 - delta) / (8 * T)) <
        3500 * ell ^ 2 := by
  let b : ℝ := delta * (1 - delta) / (8 * T)
  let U : ℝ := delta / T
  let E : ℝ := 32 * (K : ℝ) * delta ^ 2 * eta ^ 2
  change 0 < b ∧ 2 * (E / b ^ 2) < (K : ℝ) ∧
    a * (U + b) < 3500 * ell ^ 2
  have hs : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hden : 0 < (8 : ℝ) * T := by positivity
  have hbrel : b * (8 * T) = delta * (1 - delta) := by
    dsimp [b]
    field_simp [ne_of_gt hT]
  have hbudget_scaled : (65 : ℝ) * (eta * T) ≤ 1 - delta := by
    have h := (le_div_iff₀ (show 0 < (65 : ℝ) by norm_num)).mp hbudget
    nlinarith
  have hb_large : 8 * (delta * eta) < b := by
    have hm : (8 * (delta * eta)) * (8 * T) < b * (8 * T) := by
      calc
        (8 * (delta * eta)) * (8 * T) = delta * (64 * (eta * T)) := by ring
        _ < delta * (65 * (eta * T)) :=
          mul_lt_mul_of_pos_left
            (mul_lt_mul_of_pos_right (by norm_num : (64 : ℝ) < 65)
              (mul_pos heta hT)) hdelta
        _ ≤ delta * (1 - delta) :=
          mul_le_mul_of_nonneg_left hbudget_scaled hdelta.le
        _ = b * (8 * T) := hbrel.symm
    by_contra hnot
    have hrev := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hden.le
    linarith
  have hsq : 64 * delta ^ 2 * eta ^ 2 < b ^ 2 := by
    have hplus : 0 < b + 8 * (delta * eta) := by positivity
    have hp : 0 < (b - 8 * (delta * eta)) * (b + 8 * (delta * eta)) :=
      mul_pos (sub_pos.mpr hb_large) hplus
    nlinarith
  have hdensity : 2 * (E / b ^ 2) < (K : ℝ) := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (pow_pos hb 2)).2
    calc
      2 * E = (K : ℝ) * (64 * delta ^ 2 * eta ^ 2) := by
        dsimp [E]
        ring
      _ < (K : ℝ) * b ^ 2 := mul_lt_mul_of_pos_left hsq hKR
  exact ⟨hb, hdensity, hsize⟩

noncomputable def coefficientWindow_of_estimates
    (K : ℕ) (c : ℕ → ℤ) (q beta : ℕ → ℝ) (delta eta T a ell : ℝ)
    (hK : 0 < K) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (heta : 0 < eta) (hT : 0 < T) (ha : 0 < a) (hell : 0 < ell)
    (hcast : ∀ j ∈ Finset.Icc K (2 * K), (c j : ℝ) = a * q j)
    (hbeta_lower : ∀ j ∈ Finset.Icc K (2 * K),
      delta * (1 - delta) / (4 * T) ≤ |beta j|)
    (hbeta_upper : ∀ j ∈ Finset.Icc K (2 * K), |beta j| ≤ delta / T)
    (henergy : (∑ j ∈ Finset.Icc K (2 * K), (q j - beta j) ^ 2) ≤
      32 * (K : ℝ) * delta ^ 2 * eta ^ 2)
    (hbudget : eta * T ≤ (1 - delta) / 65)
    (hsize : a * (delta / T + delta * (1 - delta) / (8 * T)) < 3500 * ell ^ 2) :
    CoefficientWindow c (3500 * ell ^ 2) := by
  obtain ⟨hb, hdensity, hfinal⟩ :=
    window_numeric_bounds K delta eta T a ell hK hdelta hdelta1 heta hT ha hell hbudget hsize
  refine {
    K := K
    q := q
    beta := beta
    a := a
    b := delta * (1 - delta) / (8 * T)
    U := delta / T
    E := 32 * (K : ℝ) * delta ^ 2 * eta ^ 2
    a_pos := ha
    b_pos := hb
    scale := hcast
    beta_lower := ?_
    beta_upper := hbeta_upper
    energy := henergy
    density := hdensity
    size := hfinal
  }
  intro j hj
  have hid : 2 * (delta * (1 - delta) / (8 * T)) =
      delta * (1 - delta) / (4 * T) := by
    field_simp
    ring
  rw [hid]
  exact hbeta_lower j hj

section GaussEdges
variable {R : Type*} [Ring R] {v : AbsoluteValue R ℝ} {c : ℝ}
theorem weighted_product_coefficient_lt
    (hna : IsNonarchimedean v) (hc : 0 < c)
    (P Q : R[X]) (s : ℕ) (B : ℝ)
    (hterms : ∀ k ≤ s,
      (v (P.coeff k) * c ^ k) * (v (Q.coeff (s - k)) * c ^ (s - k)) < B) :
    v ((P * Q).coeff s) * c ^ s < B := by
  let l : ℕ → R := fun k => P.coeff k * Q.coeff (s - k)
  obtain ⟨k, hk, hsum⟩ :=
    IsNonarchimedean.finset_image_add (map_zero v) (fun x => v.nonneg x)
      hna l (Finset.range (s + 1))
  have hmem : k ∈ Finset.range (s + 1) := hk (by simp)
  have hks : k ≤ s := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hmem
  have hid : k + (s - k) = s := Nat.add_sub_of_le hks
  calc
    v ((P * Q).coeff s) * c ^ s =
        v (∑ k ∈ Finset.range (s + 1), l k) * c ^ s := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ ≤ v (l k) * c ^ s := mul_le_mul_of_nonneg_right hsum (le_of_lt (pow_pos hc s))
    _ = (v (P.coeff k) * c ^ k) * (v (Q.coeff (s - k)) * c ^ (s - k)) := by
      dsimp [l]
      have hpow : c ^ s = c ^ k * c ^ (s - k) := by rw [← pow_add, hid]
      rw [map_mul, hpow]
      ring
    _ < B := hterms k hks

theorem weighted_product_coefficient_eq
    (hna : IsNonarchimedean v) (hc : 0 < c)
    (P Q : R[X]) (i j : ℕ)
    (hterms : ∀ k ≤ i + j, k ≠ i →
      (v (P.coeff k) * c ^ k) * (v (Q.coeff (i + j - k)) * c ^ (i + j - k)) <
      (v (P.coeff i) * c ^ i) * (v (Q.coeff j) * c ^ j)) :
    v ((P * Q).coeff (i + j)) * c ^ (i + j) =
      (v (P.coeff i) * c ^ i) * (v (Q.coeff j) * c ^ j) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    IsNonarchimedean.apply_sum_eq_of_lt hna (k := i) (by simp) (by simp)]
  · simp only [Nat.add_sub_cancel_left, map_mul, pow_add]
    ring
  intro k hk hki
  have hks : k ≤ i + j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hid : k + (i + j - k) = i + j := Nat.add_sub_of_le hks
  apply lt_of_mul_lt_mul_right _ (le_of_lt (pow_pos hc (i + j)))
  have hpow : c ^ (i + j) = c ^ k * c ^ (i + j - k) := by rw [← pow_add, hid]
  calc
    v (P.coeff k * Q.coeff (i + j - k)) * c ^ (i + j) =
      (v (P.coeff k) * c ^ k) * (v (Q.coeff (i + j - k)) * c ^ (i + j - k)) := by
        rw [map_mul, hpow]
        ring
    _ < (v (P.coeff i) * c ^ i) * (v (Q.coeff j) * c ^ j) := hterms k hks hki
    _ = v (P.coeff i * Q.coeff (i + j - i)) * c ^ (i + j) := by
        simp only [Nat.add_sub_cancel_left, map_mul, pow_add]
        ring

def IsMinGaussIndex (P : R[X]) (v : AbsoluteValue R ℝ) (c : ℝ) (i : ℕ) : Prop :=
  P.gaussNorm v c = v (P.coeff i) * c ^ i ∧
  ∀ k < i, v (P.coeff k) * c ^ k < P.gaussNorm v c

def IsMaxGaussIndex (P : R[X]) (v : AbsoluteValue R ℝ) (c : ℝ) (i : ℕ) : Prop :=
  P.gaussNorm v c = v (P.coeff i) * c ^ i ∧
  ∀ k, i < k → v (P.coeff k) * c ^ k < P.gaussNorm v c

theorem gaussNorm_pos_of_ne_zero (hc : 0 < c) (P : R[X]) (hP : P ≠ 0) :
    0 < P.gaussNorm v c := by
  have hn := P.gaussNorm_nonneg v hc.le
  have hz : P.gaussNorm v c ≠ 0 := by
    intro h
    exact hP ((P.gaussNorm_eq_zero_iff v (fun x hx => (v.eq_zero).mp hx) hc).mp h)
  exact lt_of_le_of_ne hn (Ne.symm hz)

theorem minGaussIndex_mul
    (hna : IsNonarchimedean v) (hc : 0 < c)
    (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (i j : ℕ)
    (hi : IsMinGaussIndex P v c i) (hj : IsMinGaussIndex Q v c j) :
    IsMinGaussIndex (P * Q) v c (i + j) := by
  have hPpos := gaussNorm_pos_of_ne_zero (v := v) hc P hP
  have hQpos := gaussNorm_pos_of_ne_zero (v := v) hc Q hQ
  have hterm : ∀ k l, k < i ∨ l < j →
      (v (P.coeff k) * c ^ k) * (v (Q.coeff l) * c ^ l) <
      P.gaussNorm v c * Q.gaussNorm v c := by
    intro k l hkl
    rcases hkl with hk | hl
    · calc
        _ ≤ (v (P.coeff k) * c ^ k) * Q.gaussNorm v c :=
          mul_le_mul_of_nonneg_left (Q.le_gaussNorm v hc.le l)
            (mul_nonneg (v.nonneg _) (pow_nonneg hc.le _))
        _ < P.gaussNorm v c * Q.gaussNorm v c :=
          mul_lt_mul_of_pos_right (hi.2 k hk) hQpos
    · calc
        _ ≤ P.gaussNorm v c * (v (Q.coeff l) * c ^ l) :=
          mul_le_mul_of_nonneg_right (P.le_gaussNorm v hc.le k)
            (mul_nonneg (v.nonneg _) (pow_nonneg hc.le _))
        _ < P.gaussNorm v c * Q.gaussNorm v c :=
          mul_lt_mul_of_pos_left (hj.2 l hl) hPpos
  constructor
  · rw [Polynomial.gaussNorm_mul hna hc, hi.1, hj.1]
    apply Eq.symm
    apply weighted_product_coefficient_eq hna hc
    intro k hk hki
    rw [← hi.1, ← hj.1]
    exact hterm k (i + j - k) (by omega)
  · intro s hs
    rw [Polynomial.gaussNorm_mul hna hc]
    apply weighted_product_coefficient_lt hna hc
    intro k hk
    exact hterm k (s - k) (by omega)
theorem maxGaussIndex_mul
    (hna : IsNonarchimedean v) (hc : 0 < c)
    (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (i j : ℕ)
    (hi : IsMaxGaussIndex P v c i) (hj : IsMaxGaussIndex Q v c j) :
    IsMaxGaussIndex (P * Q) v c (i + j) := by
  have hPpos := gaussNorm_pos_of_ne_zero (v := v) hc P hP
  have hQpos := gaussNorm_pos_of_ne_zero (v := v) hc Q hQ
  have hterm : ∀ k l, i < k ∨ j < l →
      (v (P.coeff k) * c ^ k) * (v (Q.coeff l) * c ^ l) <
      P.gaussNorm v c * Q.gaussNorm v c := by
    intro k l hkl
    rcases hkl with hk | hl
    · calc
        _ ≤ (v (P.coeff k) * c ^ k) * Q.gaussNorm v c :=
          mul_le_mul_of_nonneg_left (Q.le_gaussNorm v hc.le l)
            (mul_nonneg (v.nonneg _) (pow_nonneg hc.le _))
        _ < P.gaussNorm v c * Q.gaussNorm v c :=
          mul_lt_mul_of_pos_right (hi.2 k hk) hQpos
    · calc
        _ ≤ P.gaussNorm v c * (v (Q.coeff l) * c ^ l) :=
          mul_le_mul_of_nonneg_right (P.le_gaussNorm v hc.le k)
            (mul_nonneg (v.nonneg _) (pow_nonneg hc.le _))
        _ < P.gaussNorm v c * Q.gaussNorm v c :=
          mul_lt_mul_of_pos_left (hj.2 l hl) hPpos
  constructor
  · rw [Polynomial.gaussNorm_mul hna hc, hi.1, hj.1]
    apply Eq.symm
    apply weighted_product_coefficient_eq hna hc
    intro k hk hki
    rw [← hi.1, ← hj.1]
    exact hterm k (i + j - k) (by omega)
  · intro s hs
    rw [Polynomial.gaussNorm_mul hna hc]
    apply weighted_product_coefficient_lt hna hc
    intro k hk
    exact hterm k (s - k) (by omega)

theorem exists_maxGaussIndex (hc : 0 < c) (P : R[X]) (hP : P ≠ 0) :
    ∃ i, IsMaxGaussIndex P v c i := by
  classical
  have hpos := gaussNorm_pos_of_ne_zero (v := v) hc P hP
  have hbound : ∀ i, P.gaussNorm v c = v (P.coeff i) * c ^ i → i ≤ P.natDegree := by
    intro i hi
    apply le_natDegree_of_ne_zero
    intro hzero
    rw [hzero, map_zero, zero_mul] at hi
    linarith
  let S := (Finset.range (P.natDegree + 1)).filter
    (fun i => P.gaussNorm v c = v (P.coeff i) * c ^ i)
  have hS : S.Nonempty := by
    obtain ⟨i, hi, _⟩ := P.exists_min_eq_gaussNorm v hc.le
    refine ⟨i, Finset.mem_filter.mpr ⟨?_, hi⟩⟩
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hbound i hi
  refine ⟨S.max' hS, (Finset.mem_filter.mp (S.max'_mem hS)).2, ?_⟩
  intro k hk
  apply lt_of_le_of_ne (P.le_gaussNorm v hc.le k)
  intro heq
  have hmem : k ∈ S := by
    refine Finset.mem_filter.mpr ⟨?_, heq.symm⟩
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hbound k heq.symm
  have := Finset.le_max' S k hmem
  omega

theorem minGaussIndex_le_maxGaussIndex (P : R[X]) (i j : ℕ)
    (hi : IsMinGaussIndex P v c i) (hj : IsMaxGaussIndex P v c j) : i ≤ j := by
  by_contra h
  have hlt := hi.2 j (by omega)
  rw [hj.1] at hlt
  exact (lt_irrefl _) hlt

theorem gauss_attaining_index_mono
    {d : ℝ} (hc : 0 < c) (hcd : c < d)
    (P : R[X]) (hP : P ≠ 0) (i j : ℕ)
    (hi : P.gaussNorm v c = v (P.coeff i) * c ^ i)
    (hj : P.gaussNorm v d = v (P.coeff j) * d ^ j) : i ≤ j := by
  have hd : 0 < d := lt_trans hc hcd
  have hi0 : P.coeff i ≠ 0 := by
    intro hz
    have hp := gaussNorm_pos_of_ne_zero (v := v) hc P hP
    rw [hi, hz, map_zero, zero_mul] at hp
    exact lt_irrefl 0 hp
  have hj0 : P.coeff j ≠ 0 := by
    intro hz
    have hp := gaussNorm_pos_of_ne_zero (v := v) hd P hP
    rw [hj, hz, map_zero, zero_mul] at hp
    exact lt_irrefl 0 hp
  have hi_pos := v.pos hi0
  have hj_pos := v.pos hj0
  have hfirst : v (P.coeff j) * c ^ j ≤ v (P.coeff i) * c ^ i := by
    rw [← hi]
    exact P.le_gaussNorm v hc.le j
  have hsecond : v (P.coeff i) * d ^ i ≤ v (P.coeff j) * d ^ j := by
    rw [← hj]
    exact P.le_gaussNorm v hd.le i
  have hlog1 := Real.log_le_log (mul_pos hj_pos (pow_pos hc j)) hfirst
  have hlog2 := Real.log_le_log (mul_pos hi_pos (pow_pos hd i)) hsecond
  rw [Real.log_mul (ne_of_gt hj_pos) (ne_of_gt (pow_pos hc j)),
      Real.log_mul (ne_of_gt hi_pos) (ne_of_gt (pow_pos hc i)),
      Real.log_pow, Real.log_pow] at hlog1
  rw [Real.log_mul (ne_of_gt hi_pos) (ne_of_gt (pow_pos hd i)),
      Real.log_mul (ne_of_gt hj_pos) (ne_of_gt (pow_pos hd j)),
      Real.log_pow, Real.log_pow] at hlog2
  have hlogcd := Real.log_lt_log hc hcd
  have hreal : (i : ℝ) ≤ (j : ℝ) := by nlinarith
  exact_mod_cast hreal

theorem integer_tie_width_dvd (a : ℤ) (b i j : ℕ) (yi yj : ℤ)
    (hij : i ≤ j) (hcop : IsCoprime (b : ℤ) a)
    (htie : (b : ℤ) * yi + a * (i : ℤ) = (b : ℤ) * yj + a * (j : ℤ)) :
    b ∣ j - i := by
  have hd : (b : ℤ) ∣ (j : ℤ) - (i : ℤ) := by
    apply hcop.dvd_of_dvd_mul_left
    refine ⟨yi - yj, ?_⟩
    nlinarith [htie]
  rw [← Int.natCast_sub hij] at hd
  exact Int.natCast_dvd_natCast.mp hd

end GaussEdges

open scoped BigOperators

lemma dvd_upper_of_dvd_lower_and_width
    (p lower upper : ℕ) (hle : lower ≤ upper)
    (hlower : p ∣ lower) (hwidth : p ∣ upper - lower) :
    p ∣ upper := by
  have hsplit : upper = lower + (upper - lower) := by omega
  rw [hsplit]
  exact dvd_add hlower hwidth

theorem residue_index_dvd_of_finite_face_partition
    (p count : ℕ) (hcount : 0 < count)
    (lower upper otherLower otherUpper vertex : ℕ → ℕ)
    (terminal otherTerminal : ℕ)
    (hfirst : vertex 0 = 0)
    (hleft : ∀ i, i < count → lower i + otherLower i = vertex i)
    (hright : ∀ i, i < count → upper i + otherUpper i = vertex (i + 1))
    (hwithin : ∀ i, i < count → lower i ≤ upper i)
    (hnext : ∀ i, i + 1 < count → upper i ≤ lower (i + 1))
    (hotherNext : ∀ i, i + 1 < count → otherUpper i ≤ otherLower (i + 1))
    (hterminal : upper (count - 1) ≤ terminal)
    (hotherTerminal : otherUpper (count - 1) ≤ otherTerminal)
    (hterminalSum : terminal + otherTerminal = vertex count)
    (hwidth : ∀ i, i < count → p ∣ upper i - lower i) :
    p ∣ terminal := by
  have hzero : lower 0 = 0 := by
    have h := hleft 0 hcount
    omega

  have hjoin : ∀ i, i + 1 < count → upper i = lower (i + 1) := by
    intro i hi
    have hi' : i < count := by omega
    have hr := hright i hi'
    have hl := hleft (i + 1) hi
    have hn := hnext i hi
    have ho := hotherNext i hi
    omega

  have hlower : ∀ i, i < count → p ∣ lower i := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [hzero]
      exact dvd_zero p
    | succ i ih =>
      intro hi
      have hi' : i < count := by omega
      have hiNext : i + 1 < count := by omega
      have hu : p ∣ upper i :=
        dvd_upper_of_dvd_lower_and_width p (lower i) (upper i)
          (hwithin i hi') (ih hi') (hwidth i hi')
      rw [← hjoin i hiNext]
      exact hu

  have hlast : count - 1 < count := by omega
  have hlastSucc : count - 1 + 1 = count := by omega
  have hterminalEq : upper (count - 1) = terminal := by
    have hr := hright (count - 1) hlast
    rw [hlastSucc] at hr
    omega

  have hu : p ∣ upper (count - 1) :=
    dvd_upper_of_dvd_lower_and_width p (lower (count - 1)) (upper (count - 1))
      (hwithin (count - 1) hlast) (hlower (count - 1) hlast)
      (hwidth (count - 1) hlast)
  simpa only [hterminalEq] using hu

section ResidueOrder
variable {R S : Type*} [Ring R] [Ring S] {v : AbsoluteValue R ℝ}

theorem gaussNorm_one_eq_one (P : R[X])
    (hbound : ∀ j, v (P.coeff j) ≤ 1)
    (hunit : ∃ j, v (P.coeff j) = 1) :
    P.gaussNorm v 1 = 1 := by
  obtain ⟨i, hi, _⟩ := P.exists_min_eq_gaussNorm v (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨j, hj⟩ := hunit
  have hle : P.gaussNorm v 1 ≤ 1 := by
    simpa only [hi, one_pow, mul_one] using hbound i
  have hge := P.le_gaussNorm v (show (0 : ℝ) ≤ 1 by norm_num) j
  simp only [hj, one_pow, mul_one] at hge
  exact le_antisymm hle hge

theorem minGaussIndex_reduction_iff
    (P : R[X]) (red : R →+* S) (i : ℕ)
    (hbound : ∀ j, v (P.coeff j) ≤ 1)
    (hunit : ∃ j, v (P.coeff j) = 1)
    (hred : ∀ a, red a ≠ 0 ↔ v a = 1) :
    IsMinGaussIndex P v 1 i ↔
      (P.map red).coeff i ≠ 0 ∧ ∀ j < i, (P.map red).coeff j = 0 := by
  have hnorm := gaussNorm_one_eq_one P hbound hunit
  constructor
  · intro hi
    refine ⟨?_, ?_⟩
    · rw [Polynomial.coeff_map]
      apply (hred _).mpr
      simpa only [hnorm, one_pow, mul_one] using hi.1.symm
    · intro j hj
      rw [Polynomial.coeff_map]
      by_contra hnonzero
      have heq := (hred _).mp hnonzero
      have hlt := hi.2 j hj
      simp only [hnorm, heq, one_pow, mul_one] at hlt
      exact (lt_irrefl 1) hlt
  · rintro ⟨hi, hbelow⟩
    constructor
    · rw [Polynomial.coeff_map] at hi
      simp only [hnorm, (hred _).mp hi, one_pow, mul_one]
    · intro j hj
      simp only [hnorm, one_pow, mul_one]
      apply lt_of_le_of_ne (hbound j)
      intro heq
      have hnonzero := (hred _).mpr heq
      exact hnonzero (by simpa only [Polynomial.coeff_map] using hbelow j hj)

theorem minGaussIndex_reduction_order
    (P : R[X]) (red : R →+* S) (i : ℕ)
    (hbound : ∀ j, v (P.coeff j) ≤ 1)
    (hunit : ∃ j, v (P.coeff j) = 1)
    (hred : ∀ a, red a ≠ 0 ↔ v a = 1)
    (hi : IsMinGaussIndex P v 1 i) :
    (X : S[X]) ^ i ∣ P.map red ∧ ¬ (X : S[X]) ^ (i + 1) ∣ P.map red := by
  obtain ⟨hnonzero, hbelow⟩ :=
    (minGaussIndex_reduction_iff P red i hbound hunit hred).mp hi
  refine ⟨Polynomial.X_pow_dvd_iff.mpr hbelow, ?_⟩
  intro h
  exact hnonzero (Polynomial.X_pow_dvd_iff.mp h i (by omega))

theorem monic_minGaussIndex_reduction_order [Nontrivial R]
    (P : R[X]) (hP : P.Monic) (red : R →+* S) (i : ℕ)
    (hbound : ∀ j, v (P.coeff j) ≤ 1)
    (hred : ∀ a, red a ≠ 0 ↔ v a = 1)
    (hi : IsMinGaussIndex P v 1 i) :
    (X : S[X]) ^ i ∣ P.map red ∧ ¬ (X : S[X]) ^ (i + 1) ∣ P.map red := by
  apply minGaussIndex_reduction_order P red i hbound _ hred hi
  refine ⟨P.natDegree, ?_⟩
  simp [hP.coeff_natDegree]
end ResidueOrder

theorem exp_weighted_tie_integer (b i j : ℕ) (hb : 0 < b) (yi yj : ℤ)
    (htie : Real.exp (-(yi : ℝ)) * (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ i =
      Real.exp (-(yj : ℝ)) * (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ j) :
    (b : ℤ) * yi + (i : ℤ) = (b : ℤ) * yj + (j : ℤ) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hlog := congrArg Real.log htie
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (pow_pos (Real.exp_pos _) _)),
      Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (pow_pos (Real.exp_pos _) _)),
      Real.log_exp, Real.log_exp, Real.log_pow, Real.log_pow,
      Real.log_exp] at hlog
  have hreal : (b : ℝ) * (yi : ℝ) + (i : ℝ) = (b : ℝ) * (yj : ℝ) + (j : ℝ) := by
    field_simp at hlog
    nlinarith [hlog]
  exact_mod_cast hreal

theorem discrete_gauss_width_dvd
    {R : Type*} [Ring R] {v : AbsoluteValue R ℝ}
    (P : R[X]) (hP : P ≠ 0) (b i j : ℕ) (hb : 0 < b) (hij : i ≤ j)
    (hdiscrete : ∀ a : R, a ≠ 0 → ∃ z : ℤ, v a = Real.exp (-(z : ℝ)))
    (hi : P.gaussNorm v (Real.exp (-(1 : ℝ) / (b : ℝ))) =
      v (P.coeff i) * (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ i)
    (hj : P.gaussNorm v (Real.exp (-(1 : ℝ) / (b : ℝ))) =
      v (P.coeff j) * (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ j) :
    b ∣ j - i := by
  have hpos := gaussNorm_pos_of_ne_zero (v := v)
    (Real.exp_pos (-(1 : ℝ) / (b : ℝ))) P hP
  have hi0 : P.coeff i ≠ 0 := by
    intro hz
    rw [hi, hz, map_zero, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  have hj0 : P.coeff j ≠ 0 := by
    intro hz
    rw [hj, hz, map_zero, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨yi, hyi⟩ := hdiscrete (P.coeff i) hi0
  obtain ⟨yj, hyj⟩ := hdiscrete (P.coeff j) hj0
  have htie := hi.symm.trans hj
  rw [hyi, hyj] at htie
  have hwidth := exp_weighted_tie_integer b i j hb yi yj htie
  apply integer_tie_width_dvd 1 b i j yi yj hij (by exact ⟨0, 1, by ring⟩)
  simpa only [one_mul] using hwidth

end EventualIrreducibility

open Polynomial

namespace EventualIrreducibility

section LocalGaussAssembly

variable {R : Type*} [Ring R] {v : AbsoluteValue R ℝ}

lemma assembly_min_unique
    (P : R[X]) (c : ℝ) (i j : ℕ)
    (hi : IsMinGaussIndex P v c i)
    (hj : IsMinGaussIndex P v c j) : i = j := by
  apply le_antisymm
  · by_contra h
    have hlt := hi.2 j (by omega)
    rw [hj.1] at hlt
    exact (lt_irrefl _) hlt
  · by_contra h
    have hlt := hj.2 i (by omega)
    rw [hi.1] at hlt
    exact (lt_irrefl _) hlt

lemma assembly_max_unique
    (P : R[X]) (c : ℝ) (i j : ℕ)
    (hi : IsMaxGaussIndex P v c i)
    (hj : IsMaxGaussIndex P v c j) : i = j := by
  apply le_antisymm
  · by_contra h
    have hlt := hj.2 i (by omega)
    rw [hi.1] at hlt
    exact (lt_irrefl _) hlt
  · by_contra h
    have hlt := hi.2 j (by omega)
    rw [hj.1] at hlt
    exact (lt_irrefl _) hlt

theorem minGaussIndex_one_dvd_of_critical_faces
    (hna : IsNonarchimedean v)
    (G H : R[X]) (hG : G ≠ 0) (hH : H ≠ 0)
    (p count : ℕ) (hcount : 0 < count)
    (denom vertex : ℕ → ℕ)
    (hdiscrete : ∀ a : R, a ≠ 0 → ∃ z : ℤ, v a = Real.exp (-(z : ℝ)))
    (hfirst : vertex 0 = 0)
    (hdenom : ∀ i, i < count → 0 < denom i)
    (hprime_denom : ∀ i, i < count → p ∣ denom i)
    (hnextRadius : ∀ i, i + 1 < count →
      Real.exp (-(1 : ℝ) / (denom i : ℝ)) <
        Real.exp (-(1 : ℝ) / (denom (i + 1) : ℝ)))
    (hlastRadius : Real.exp (-(1 : ℝ) / (denom (count - 1) : ℝ)) < 1)
    (hproductMin : ∀ i, i < count →
      IsMinGaussIndex (G * H) v
        (Real.exp (-(1 : ℝ) / (denom i : ℝ))) (vertex i))
    (hproductMax : ∀ i, i < count →
      IsMaxGaussIndex (G * H) v
        (Real.exp (-(1 : ℝ) / (denom i : ℝ))) (vertex (i + 1)))
    (hproductTerminal : IsMinGaussIndex (G * H) v 1 (vertex count))
    (terminal : ℕ) (hterminal : IsMinGaussIndex G v 1 terminal) :
    p ∣ terminal := by
  classical
  let radius : ℕ → ℝ := fun i => Real.exp (-(1 : ℝ) / (denom i : ℝ))
  have hradiusPos : ∀ i, 0 < radius i := fun i => Real.exp_pos _

  have hminG : ∀ i : ℕ, ∃ j, IsMinGaussIndex G v (radius i) j := by
    intro i
    exact G.exists_min_eq_gaussNorm v (hradiusPos i).le
  have hmaxG : ∀ i : ℕ, ∃ j, IsMaxGaussIndex G v (radius i) j := by
    intro i
    exact exists_maxGaussIndex (hradiusPos i) G hG
  have hminH : ∀ i : ℕ, ∃ j, IsMinGaussIndex H v (radius i) j := by
    intro i
    exact H.exists_min_eq_gaussNorm v (hradiusPos i).le
  have hmaxH : ∀ i : ℕ, ∃ j, IsMaxGaussIndex H v (radius i) j := by
    intro i
    exact exists_maxGaussIndex (hradiusPos i) H hH

  choose lower hLower using hminG
  choose upper hUpper using hmaxG
  choose otherLower hOtherLower using hminH
  choose otherUpper hOtherUpper using hmaxH
  obtain ⟨otherTerminal, hOtherTerminal⟩ :=
    H.exists_min_eq_gaussNorm v (show (0 : ℝ) ≤ 1 by norm_num)

  have hleft : ∀ i, i < count →
      lower i + otherLower i = vertex i := by
    intro i hi
    exact assembly_min_unique (G * H) (radius i)
      (lower i + otherLower i) (vertex i)
      (minGaussIndex_mul hna (hradiusPos i) G H hG hH
        (lower i) (otherLower i) (hLower i) (hOtherLower i))
      (hproductMin i hi)

  have hright : ∀ i, i < count →
      upper i + otherUpper i = vertex (i + 1) := by
    intro i hi
    exact assembly_max_unique (G * H) (radius i)
      (upper i + otherUpper i) (vertex (i + 1))
      (maxGaussIndex_mul hna (hradiusPos i) G H hG hH
        (upper i) (otherUpper i) (hUpper i) (hOtherUpper i))
      (hproductMax i hi)

  have hwithin : ∀ i, i < count → lower i ≤ upper i := by
    intro i _
    exact minGaussIndex_le_maxGaussIndex G (lower i) (upper i)
      (hLower i) (hUpper i)

  have hnext : ∀ i, i + 1 < count → upper i ≤ lower (i + 1) := by
    intro i hi
    exact gauss_attaining_index_mono (hradiusPos i) (hnextRadius i hi)
      G hG (upper i) (lower (i + 1)) (hUpper i).1 (hLower (i + 1)).1

  have hotherNext : ∀ i, i + 1 < count →
      otherUpper i ≤ otherLower (i + 1) := by
    intro i hi
    exact gauss_attaining_index_mono (hradiusPos i) (hnextRadius i hi)
      H hH (otherUpper i) (otherLower (i + 1))
      (hOtherUpper i).1 (hOtherLower (i + 1)).1

  have hterminalLe : upper (count - 1) ≤ terminal :=
    gauss_attaining_index_mono (hradiusPos (count - 1)) hlastRadius
      G hG (upper (count - 1)) terminal (hUpper (count - 1)).1 hterminal.1

  have hotherTerminalLe : otherUpper (count - 1) ≤ otherTerminal :=
    gauss_attaining_index_mono (hradiusPos (count - 1)) hlastRadius
      H hH (otherUpper (count - 1)) otherTerminal
      (hOtherUpper (count - 1)).1 hOtherTerminal.1

  have hterminalSum : terminal + otherTerminal = vertex count :=
    assembly_min_unique (G * H) 1 (terminal + otherTerminal) (vertex count)
      (minGaussIndex_mul hna (by norm_num) G H hG hH
        terminal otherTerminal hterminal hOtherTerminal)
      hproductTerminal

  have hwidth : ∀ i, i < count → p ∣ upper i - lower i := by
    intro i hi
    exact dvd_trans (hprime_denom i hi)
      (discrete_gauss_width_dvd G hG (denom i) (lower i) (upper i)
        (hdenom i hi) (hwithin i hi) hdiscrete (hLower i).1 (hUpper i).1)

  exact residue_index_dvd_of_finite_face_partition p count hcount
    lower upper otherLower otherUpper vertex terminal otherTerminal
    hfirst hleft hright hwithin hnext hotherNext hterminalLe
    hotherTerminalLe hterminalSum hwidth

end LocalGaussAssembly

end EventualIrreducibility

open Polynomial
namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility

lemma FactorSeries.constant_ne_zero {n : ℕ} (s : FactorSeries n) (hn : 0 < n) :
    s.factor.coeff 0 ≠ 0 := by
  intro hz
  obtain ⟨h, hh⟩ := s.divides
  have hc := congrArg (fun p : ℤ[X] => p.coeff 0) hh
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [coeff_fInt, hn, if_true, Nat.sub_zero, mul_coeff_zero, hz, zero_mul] at hc
  exact hnz hc

noncomputable def FactorSeries.normalizedReal {n : ℕ} (s : FactorSeries n) :
    PowerSeries ℝ :=
  PowerSeries.C ((s.factor.coeff 0 : ℝ)⁻¹) *
    PowerSeries.map (Int.castRingHom ℝ) (quotientSeries s.factor)

end EventualIrreducibility

open Polynomial
open scoped BigOperators

namespace EventualIrreducibility.ConcreteRootProducts

lemma reverse_X_sub_C_complex (a : ℂ) :
    (X - C a : ℂ[X]).reverse = 1 - C a * X := by
  simp [Polynomial.reverse]

lemma reverse_prod_X_sub_C_complex {ι : Type*}
    (s : Finset ι) (alpha : ι → ℂ) :
    (∏ i ∈ s, (X - C (alpha i) : ℂ[X])).reverse =
      ∏ i ∈ s, (1 - C (alpha i) * X : ℂ[X]) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.reverse]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Polynomial.reverse_mul_of_domain,
      reverse_X_sub_C_complex, ih]

lemma X_sub_C_eq_scaled_inverse_factor (a : ℂ) (ha : a ≠ 0) :
    (X - C a : ℂ[X]) = C (-a) * (1 - C a⁻¹ * X) := by
  have hmul : (C (-a) : ℂ[X]) * C a⁻¹ = -1 := by
    rw [← Polynomial.C_mul]
    simp [ha]
  calc
    (X - C a : ℂ[X]) = C (-a) - (-1) * X := by simp only [map_neg]; ring
    _ = C (-a) - (C (-a) * C a⁻¹) * X := by rw [hmul]
    _ = C (-a) * (1 - C a⁻¹ * X) := by ring

theorem normalized_and_reversed_of_factorization {ι : Type*}
    (s : Finset ι) (alpha : ι → ℂ) (g : ℂ[X])
    (hfactor : g = ∏ i ∈ s, (X - C (alpha i) : ℂ[X]))
    (ha : g.coeff 0 ≠ 0) :
    (∀ i ∈ s, alpha i ≠ 0) ∧
      g.reverse = ∏ i ∈ s, (1 - C (alpha i) * X : ℂ[X]) ∧
      C ((g.coeff 0)⁻¹) * g =
        ∏ i ∈ s, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
  classical
  have hconstant : g.coeff 0 = ∏ i ∈ s, -(alpha i) := by
    have heval := congrArg (fun P : ℂ[X] => P.eval 0) hfactor
    simpa [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod] using heval
  have hproduct_ne_zero : (∏ i ∈ s, -(alpha i)) ≠ 0 := by
    rw [← hconstant]
    exact ha
  have hroot_ne_zero : ∀ i ∈ s, alpha i ≠ 0 := by
    intro i hi
    have hneg := (Finset.prod_ne_zero_iff.mp hproduct_ne_zero) i hi
    simpa only [neg_ne_zero] using hneg
  refine ⟨hroot_ne_zero, ?_, ?_⟩
  · rw [hfactor]
    exact reverse_prod_X_sub_C_complex s alpha
  · have hscaled : g = C (g.coeff 0) *
        ∏ i ∈ s, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
      calc
        g = ∏ i ∈ s, (X - C (alpha i) : ℂ[X]) := hfactor
        _ = ∏ i ∈ s,
            (C (-(alpha i)) * (1 - C ((alpha i)⁻¹) * X) : ℂ[X]) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact X_sub_C_eq_scaled_inverse_factor (alpha i) (hroot_ne_zero i hi)
        _ = (∏ i ∈ s, (C (-(alpha i)) : ℂ[X])) *
            ∏ i ∈ s, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) :=
          Finset.prod_mul_distrib
        _ = C (∏ i ∈ s, -(alpha i)) *
            ∏ i ∈ s, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
          simp only [map_prod]
        _ = C (g.coeff 0) *
            ∏ i ∈ s, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
          rw [← hconstant]
    calc
      C ((g.coeff 0)⁻¹) * g =
          C ((g.coeff 0)⁻¹) * (C (g.coeff 0) *
            ∏ i ∈ s, (1 - C ((alpha i)⁻¹) * X : ℂ[X])) :=
        congrArg (fun P : ℂ[X] => C ((g.coeff 0)⁻¹) * P) hscaled
      _ =
          (C ((g.coeff 0)⁻¹) * C (g.coeff 0)) *
            ∏ i ∈ s, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
        ring
      _ = ∏ i ∈ s, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1, one_mul]

lemma prod_fin_toList {M : Type*} [CommMonoid M]
    (s : Multiset ℂ) (F : ℂ → M) :
    (∏ i : Fin s.toList.length, F (s.toList[(i : ℕ)])) = (s.map F).prod := by
  calc
    (∏ i : Fin s.toList.length, F (s.toList[(i : ℕ)])) =
        (List.ofFn (fun i : Fin s.toList.length => F (s.toList[(i : ℕ)]))).prod :=
      List.prod_ofFn.symm
    _ = (s.toList.map F).prod := by
      rw [List.ofFn_getElem_eq_map]
    _ = (s.map F).prod := Multiset.prod_map_toList s F

theorem exists_concrete_root_products (g : ℂ[X])
    (hg : g.Monic) (ha : g.coeff 0 ≠ 0) :
    ∃ d : ℕ, ∃ alpha : Fin d → ℂ,
      d = g.natDegree ∧
      (∀ i, alpha i ≠ 0) ∧
      g = ∏ i, (X - C (alpha i) : ℂ[X]) ∧
      g.reverse = ∏ i, (1 - C (alpha i) * X : ℂ[X]) ∧
      C ((g.coeff 0)⁻¹) * g =
        ∏ i, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
  classical
  have hs : g.Splits := IsAlgClosed.splits g
  let d : ℕ := g.roots.toList.length
  let alpha : Fin d → ℂ := fun i => g.roots.toList[(i : ℕ)]
  have hd : d = g.natDegree := by
    dsimp [d]
    simpa only [Multiset.length_toList] using hs.natDegree_eq_card_roots.symm
  have hfactor : g = ∏ i : Fin d, (X - C (alpha i) : ℂ[X]) := by
    calc
      g = (g.roots.map (fun a => (X - C a : ℂ[X]))).prod :=
        hs.eq_prod_roots_of_monic hg
      _ = ∏ i : Fin d, (X - C (alpha i) : ℂ[X]) := by
        symm
        simpa only [d, alpha] using
          (prod_fin_toList g.roots (fun a => (X - C a : ℂ[X])))
  obtain ⟨hroot, hreverse, hnormalized⟩ :=
    normalized_and_reversed_of_factorization Finset.univ alpha g hfactor ha
  refine ⟨d, alpha, hd, ?_, hfactor, hreverse, hnormalized⟩
  intro i
  exact hroot i (Finset.mem_univ i)

end EventualIrreducibility.ConcreteRootProducts

open scoped BigOperators PowerSeries

namespace EventualIrreducibility.RootProductBridge

variable {R : Type*} [Field R]

noncomputable def linearFactor (b : R) : PowerSeries R :=
  1 - PowerSeries.C b * PowerSeries.X

end EventualIrreducibility.RootProductBridge

namespace EventualIrreducibility

lemma coe_prod_root_linear {ι : Type*} (s : Finset ι) (alpha : ι → ℂ) :
    (((∏ i ∈ s, (1 - C (alpha i) * X)) : ℂ[X]) : PowerSeries ℂ) =
      ∏ i ∈ s, RootProductBridge.linearFactor (alpha i) := by
  change Polynomial.coeToPowerSeries.ringHom (∏ i ∈ s, (1 - C (alpha i) * X)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub,
    Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
    RootProductBridge.linearFactor]

lemma FactorSeries.map_normalizedReal {n : ℕ} (s : FactorSeries n) :
    PowerSeries.map Complex.ofRealHom s.normalizedReal =
      PowerSeries.C ((s.factor.coeff 0 : ℂ)⁻¹) *
        PowerSeries.map (Int.castRingHom ℂ) (quotientSeries s.factor) := by
  apply PowerSeries.ext
  intro j
  simp [PowerSeries.coeff_map, FactorSeries.normalizedReal, PowerSeries.coeff_C_mul]

theorem FactorSeries.exists_root_product_identity {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) :
    ∃ d : ℕ, ∃ alpha : Fin d → ℂ,
      d = s.factor.natDegree ∧
      (∀ i, alpha i ≠ 0) ∧
      (s.factor.map (Int.castRingHom ℂ)) =
        ∏ i, (X - C (alpha i) : ℂ[X]) ∧
      (∏ i, RootProductBridge.linearFactor (alpha i)) *
        PowerSeries.map Complex.ofRealHom s.normalizedReal =
          ∏ i, RootProductBridge.linearFactor ((alpha i)⁻¹) := by
  classical
  let phi : ℤ →+* ℂ := Int.castRingHom ℂ
  let P : ℂ[X] := s.factor.map phi
  have hP : P.Monic := s.monic.map phi
  have hP0 : P.coeff 0 = (s.factor.coeff 0 : ℂ) := by
    change (s.factor.map phi).coeff 0 = _
    rw [Polynomial.coeff_map]
    rfl
  have ha : P.coeff 0 ≠ 0 := by
    rw [hP0]
    exact_mod_cast s.constant_ne_zero hn
  obtain ⟨d, alpha, hd, hroots, hfactor, hreverse, hnormalized⟩ :=
    ConcreteRootProducts.exists_concrete_root_products P hP ha
  have hdegree : d = s.factor.natDegree := by
    rw [hd]
    exact s.monic.natDegree_map phi
  refine ⟨d, alpha, hdegree, hroots, hfactor, ?_⟩
  have hrev : (P.reverse : PowerSeries ℂ) =
      ∏ i, RootProductBridge.linearFactor (alpha i) := by
    rw [hreverse]
    exact coe_prod_root_linear Finset.univ alpha
  have hnorm : PowerSeries.C ((s.factor.coeff 0 : ℂ)⁻¹) * (P : PowerSeries ℂ) =
      ∏ i, RootProductBridge.linearFactor ((alpha i)⁻¹) := by
    have hh := congrArg (fun p : ℂ[X] => (p : PowerSeries ℂ)) hnormalized
    simpa only [Polynomial.coe_mul, Polynomial.coe_C, coe_prod_root_linear, hP0] using hh
  have hmul : (P.reverse : PowerSeries ℂ) *
      PowerSeries.map phi (quotientSeries s.factor) = (P : PowerSeries ℂ) := by
    have hh := congrArg (PowerSeries.map phi)
      (reverse_mul_quotientSeries s.factor s.monic)
    simpa only [map_mul, ← Polynomial.polynomial_map_coe,
      reverse_map_monic s.factor s.monic phi] using hh
  rw [← hrev, s.map_normalizedReal]
  calc
    (P.reverse : PowerSeries ℂ) *
        (PowerSeries.C ((s.factor.coeff 0 : ℂ)⁻¹) *
          PowerSeries.map phi (quotientSeries s.factor)) =
        PowerSeries.C ((s.factor.coeff 0 : ℂ)⁻¹) *
          ((P.reverse : PowerSeries ℂ) *
            PowerSeries.map phi (quotientSeries s.factor)) := by ring
    _ = PowerSeries.C ((s.factor.coeff 0 : ℂ)⁻¹) * (P : PowerSeries ℂ) := by rw [hmul]
    _ = ∏ i, RootProductBridge.linearFactor ((alpha i)⁻¹) := hnorm

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

open Polynomial

namespace EventualIrreducibility.FirstFace

def firstFaceLast (p r : ℕ) : ℕ := if p = 2 ∧ 2 ≤ r then 4 else p

lemma exists_power_band (p r j : ℕ) (hj : 1 ≤ j) (hjr : j < p ^ r) :
    ∃ k : ℕ, k < r ∧ p ^ k ≤ j ∧ j < p ^ (k + 1) := by
  revert hjr
  induction r with
  | zero =>
    intro hjr
    simp only [pow_zero] at hjr
    omega
  | succ r ih =>
    intro hjr
    by_cases hlow : j < p ^ r
    · obtain ⟨k, hk, hkj, hjk⟩ := ih hlow
      exact ⟨k, by omega, hkj, hjk⟩
    · exact ⟨r, by omega, Nat.le_of_not_gt hlow, hjr⟩

lemma mul_index_le_pow (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    p * k ≤ p ^ k := by
  revert hk
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hk1 : 1 ≤ k := by omega
      have hi := ih hk1
      have hp_le_pow : p ≤ p ^ k := by nlinarith
      calc
        p * (k + 1) = p * k + p := by ring
        _ ≤ p ^ k + p ^ k := Nat.add_le_add hi hp_le_pow
        _ ≤ p ^ k * p := by nlinarith
        _ = p ^ (k + 1) := (pow_succ p k).symm

lemma mul_index_lt_pow_of_three (p k : ℕ) (hp : 2 ≤ p) (hk : 3 ≤ k) :
    p * k < p ^ k := by
  revert hk
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    by_cases hk2 : k = 2
    · subst k
      have hsquare : 4 ≤ p * p := by nlinarith
      have hcube := Nat.mul_le_mul_left p hsquare
      norm_num [pow_succ] at hcube ⊢
      nlinarith
    · have hk3 : 3 ≤ k := by omega
      have hi := ih hk3
      have hp_le_pow : p ≤ p ^ k := by
        have hweak := mul_index_le_pow p k hp (by omega)
        nlinarith
      calc
        p * (k + 1) = p * k + p := by ring
        _ < p ^ k + p ^ k := Nat.add_lt_add_of_lt_of_le hi hp_le_pow
        _ ≤ p ^ k * p := by nlinarith
        _ = p ^ (k + 1) := (pow_succ p k).symm

lemma le_firstFaceLast (p r : ℕ) (_hp : 2 ≤ p) : p ≤ firstFaceLast p r := by
  by_cases h : p = 2 ∧ 2 ≤ r
  · simp [firstFaceLast, h]
  · simp [firstFaceLast, h]

lemma first_face_strict_index (p r k j : ℕ) (hp : 2 ≤ p)
    (hkr : k ≤ r) (hkj : p ^ k ≤ j) (hj : firstFaceLast p r < j) :
    p * k < j := by
  by_cases hk0 : k = 0
  · subst k
    simp only [mul_zero]
    have := le_firstFaceLast p r hp
    omega
  by_cases hk1 : k = 1
  · subst k
    simp only [mul_one]
    exact lt_of_le_of_lt (le_firstFaceLast p r hp) hj
  by_cases hk2 : k = 2
  · subst k
    by_cases hp2 : p = 2
    · have hr2 : 2 ≤ r := hkr
      simpa [firstFaceLast, hp2, hr2] using hj
    · have hp3 : 3 ≤ p := by omega
      have hstrict : p * 2 < p ^ 2 := by
        rw [pow_two]
        nlinarith
      exact lt_of_lt_of_le hstrict hkj
  · have hk3 : 3 ≤ k := by omega
    exact lt_of_lt_of_le (mul_index_lt_pow_of_three p k hp hk3) hkj

lemma exp_first_weight (p r k j : ℕ) :
    Real.exp (-(r : ℝ) + (k : ℝ)) *
        (Real.exp (-(1 : ℝ) / (p : ℝ))) ^ j =
      Real.exp (-(r : ℝ) + (k : ℝ) - (j : ℝ) / (p : ℝ)) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

section Envelope

variable {R : Type*} [Ring R] {v : AbsoluteValue R ℝ}

lemma exists_coefficient_level
    (P : R[X]) (p r : ℕ)
    (hband : ∀ k, k < r → ∀ j, p ^ k ≤ j → j < p ^ (k + 1) →
      v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ)))
    (htail : ∀ j, p ^ r ≤ j → v (P.coeff j) ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ k : ℕ, k ≤ r ∧ p ^ k ≤ j ∧
      v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ)) := by
  by_cases hjr : j < p ^ r
  · obtain ⟨k, hk, hkj, hjk⟩ := exists_power_band p r j hj hjr
    exact ⟨k, hk.le, hkj, hband k hk j hkj hjk⟩
  · have hge : p ^ r ≤ j := Nat.le_of_not_gt hjr
    refine ⟨r, le_rfl, hge, ?_⟩
    simpa only [neg_add_cancel, Real.exp_zero] using htail j hge

lemma coefficient_lt_one_below
    (P : R[X]) (p r : ℕ) (hr : 1 ≤ r)
    (hzero : v (P.coeff 0) = Real.exp (-(r : ℝ)))
    (hband : ∀ k, k < r → ∀ j, p ^ k ≤ j → j < p ^ (k + 1) →
      v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ)))
    (j : ℕ) (hj : j < p ^ r) : v (P.coeff j) < 1 := by
  by_cases hj0 : j = 0
  · subst j
    rw [hzero]
    apply Real.exp_lt_one_iff.mpr
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  · obtain ⟨k, hk, hkj, hjk⟩ := exists_power_band p r j (by omega) hj
    apply lt_of_le_of_lt (hband k hk j hkj hjk)
    apply Real.exp_lt_one_iff.mpr
    have hkR : (k : ℝ) < (r : ℝ) := by exact_mod_cast hk
    linarith

theorem terminal_minimum_of_envelope
    (P : R[X]) (p r : ℕ) (hr : 1 ≤ r)
    (hzero : v (P.coeff 0) = Real.exp (-(r : ℝ)))
    (hvertex : v (P.coeff (p ^ r)) = 1)
    (hband : ∀ k, k < r → ∀ j, p ^ k ≤ j → j < p ^ (k + 1) →
      v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ)))
    (htail : ∀ j, p ^ r ≤ j → v (P.coeff j) ≤ 1) :
    IsMinGaussIndex P v 1 (p ^ r) := by
  have hbound : ∀ j, v (P.coeff j) ≤ 1 := by
    intro j
    by_cases hj : j < p ^ r
    · exact (coefficient_lt_one_below P p r hr hzero hband j hj).le
    · exact htail j (Nat.le_of_not_gt hj)
  have hnorm : P.gaussNorm v 1 = 1 :=
    gaussNorm_one_eq_one P hbound ⟨p ^ r, hvertex⟩
  constructor
  · simp only [hnorm, hvertex, one_pow, mul_one]
  · intro j hj
    simpa only [hnorm, one_pow, mul_one] using
      coefficient_lt_one_below P p r hr hzero hband j hj

lemma first_weight_le_from_level
    (P : R[X]) (p r k j : ℕ) (hp : 2 ≤ p)
    (hindex : p * k ≤ j)
    (hcoeff : v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ))) :
    v (P.coeff j) * (Real.exp (-(1 : ℝ) / (p : ℝ))) ^ j ≤
      Real.exp (-(r : ℝ)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hindexR : (k : ℝ) * (p : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast (show k * p ≤ j by simpa only [mul_comm] using hindex)
  have hdiv : (k : ℝ) ≤ (j : ℝ) / (p : ℝ) :=
    (le_div_iff₀ hpR).mpr hindexR
  calc
    v (P.coeff j) * (Real.exp (-(1 : ℝ) / (p : ℝ))) ^ j ≤
        Real.exp (-(r : ℝ) + (k : ℝ)) *
          (Real.exp (-(1 : ℝ) / (p : ℝ))) ^ j :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (Real.exp_pos _).le j)
    _ = Real.exp (-(r : ℝ) + (k : ℝ) - (j : ℝ) / (p : ℝ)) :=
      exp_first_weight p r k j
    _ ≤ Real.exp (-(r : ℝ)) := Real.exp_le_exp.mpr (by linarith)

lemma first_weight_lt_from_level
    (P : R[X]) (p r k j : ℕ) (hp : 2 ≤ p)
    (hindex : p * k < j)
    (hcoeff : v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ))) :
    v (P.coeff j) * (Real.exp (-(1 : ℝ) / (p : ℝ))) ^ j <
      Real.exp (-(r : ℝ)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hindexR : (k : ℝ) * (p : ℝ) < (j : ℝ) := by
    exact_mod_cast (show k * p < j by simpa only [mul_comm] using hindex)
  have hdiv : (k : ℝ) < (j : ℝ) / (p : ℝ) :=
    (lt_div_iff₀ hpR).mpr hindexR
  calc
    v (P.coeff j) * (Real.exp (-(1 : ℝ) / (p : ℝ))) ^ j ≤
        Real.exp (-(r : ℝ) + (k : ℝ)) *
          (Real.exp (-(1 : ℝ) / (p : ℝ))) ^ j :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (Real.exp_pos _).le j)
    _ = Real.exp (-(r : ℝ) + (k : ℝ) - (j : ℝ) / (p : ℝ)) :=
      exp_first_weight p r k j
    _ < Real.exp (-(r : ℝ)) := Real.exp_lt_exp.mpr (by linarith)

theorem first_face_and_terminal_of_envelope
    (P : R[X]) (p r : ℕ) (hp : 2 ≤ p) (hr : 1 ≤ r)
    (hzero : v (P.coeff 0) = Real.exp (-(r : ℝ)))
    (hvertex : ∀ k, 1 ≤ k → k ≤ r →
      v (P.coeff (p ^ k)) = Real.exp (-(r : ℝ) + (k : ℝ)))
    (hband : ∀ k, k < r → ∀ j, p ^ k ≤ j → j < p ^ (k + 1) →
      v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ)))
    (htail : ∀ j, p ^ r ≤ j → v (P.coeff j) ≤ 1) :
    IsMinGaussIndex P v (Real.exp (-(1 : ℝ) / (p : ℝ))) 0 ∧
      IsMaxGaussIndex P v (Real.exp (-(1 : ℝ) / (p : ℝ))) (firstFaceLast p r) ∧
      IsMinGaussIndex P v 1 (p ^ r) := by
  let c : ℝ := Real.exp (-(1 : ℝ) / (p : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hbound : ∀ j, v (P.coeff j) * c ^ j ≤ Real.exp (-(r : ℝ)) := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp only [hzero, pow_zero, mul_one, le_refl]
    · obtain ⟨k, hkr, hkj, hcoeff⟩ :=
        exists_coefficient_level P p r hband htail j (by omega)
      have hindex : p * k ≤ j := by
        by_cases hk0 : k = 0
        · simp [hk0]
        · exact (mul_index_le_pow p k hp (by omega)).trans hkj
      exact first_weight_le_from_level P p r k j hp hindex hcoeff
  have hnorm : P.gaussNorm v c = Real.exp (-(r : ℝ)) := by
    obtain ⟨i, hi, _⟩ := P.exists_min_eq_gaussNorm v hc.le
    apply le_antisymm
    · rw [hi]
      exact hbound i
    · simpa only [hzero, pow_zero, mul_one] using P.le_gaussNorm v hc.le 0
  have hright : v (P.coeff (firstFaceLast p r)) * c ^ (firstFaceLast p r) =
      Real.exp (-(r : ℝ)) := by
    by_cases hbinary : p = 2 ∧ 2 ≤ r
    · have hcoeff : v (P.coeff 4) = Real.exp (-(r : ℝ) + (2 : ℝ)) := by
        simpa [hbinary.1] using hvertex 2 (by omega) hbinary.2
      simp only [firstFaceLast, if_pos hbinary]
      rw [hcoeff]
      change Real.exp (-(r : ℝ) + (2 : ℝ)) *
        (Real.exp (-(1 : ℝ) / (p : ℝ))) ^ 4 = _
      have he := exp_first_weight p r 2 4
      norm_num [hbinary.1] at he ⊢
      simpa only [add_sub_cancel_right] using he
    · have hcoeff : v (P.coeff p) = Real.exp (-(r : ℝ) + (1 : ℝ)) := by
        simpa only [pow_one, Nat.cast_one] using hvertex 1 (by omega) hr
      simp only [firstFaceLast, if_neg hbinary]
      rw [hcoeff]
      change Real.exp (-(r : ℝ) + (1 : ℝ)) *
        (Real.exp (-(1 : ℝ) / (p : ℝ))) ^ p = _
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
      simpa only [Nat.cast_one, div_self hpR, add_sub_cancel_right] using
        exp_first_weight p r 1 p
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · simpa only [hzero, pow_zero, mul_one] using hnorm
    · intro j hj
      omega
  · constructor
    · exact hnorm.trans hright.symm
    · intro j hj
      obtain ⟨k, hkr, hkj, hcoeff⟩ :=
        exists_coefficient_level P p r hband htail j (by omega)
      rw [hnorm]
      exact first_weight_lt_from_level P p r k j hp
        (first_face_strict_index p r k j hp hkr hkj hj) hcoeff
  · apply terminal_minimum_of_envelope P p r hr hzero _ hband htail
    simpa only [neg_add_cancel, Real.exp_zero] using hvertex r hr le_rfl

end Envelope

end EventualIrreducibility.FirstFace

open Polynomial

namespace EventualIrreducibility.FirstFace

def laterDenom (p k : ℕ) : ℕ := p ^ k * (p - 1)

lemma affine_le_prime_power (p t : ℕ) (hp : 2 ≤ p) :
    1 + (p - 1) * t ≤ p ^ t := by
  have hs : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  induction t with
  | zero => simp
  | succ t ih =>
    have hpow : 1 ≤ p ^ t := by omega
    calc
      1 + (p - 1) * (t + 1) = (1 + (p - 1) * t) + (p - 1) := by ring
      _ ≤ p ^ t + (p - 1) := Nat.add_le_add_right ih _
      _ ≤ p ^ t + p ^ t * (p - 1) := by nlinarith
      _ = p ^ (t + 1) := by
        rw [pow_succ]
        nlinarith [hs]

lemma affine_lt_prime_power (p t : ℕ) (hp : 2 ≤ p) (ht : 2 ≤ t) :
    1 + (p - 1) * t < p ^ t := by
  have hs : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  revert ht
  induction t with
  | zero => intro ht; omega
  | succ t ih =>
    intro ht
    by_cases ht1 : t = 1
    · subst t
      have hsq := Nat.mul_le_mul_left p hp
      norm_num [pow_succ] at hsq ⊢
      nlinarith [hs]
    · have ht2 : 2 ≤ t := by omega
      have hi := ih ht2
      have hpow : 1 ≤ p ^ t := by
        have := affine_le_prime_power p t hp
        omega
      calc
        1 + (p - 1) * (t + 1) = (1 + (p - 1) * t) + (p - 1) := by ring
        _ < p ^ t + (p - 1) := Nat.add_lt_add_right hi _
        _ ≤ p ^ t + p ^ t * (p - 1) := by nlinarith
        _ = p ^ (t + 1) := by
          rw [pow_succ]
          nlinarith [hs]

lemma laterDenom_pos (p k : ℕ) (hp : 2 ≤ p) : 0 < laterDenom p k := by
  unfold laterDenom
  exact Nat.mul_pos (pow_pos (by omega) k) (by omega)

lemma prime_power_le_laterDenom (p k : ℕ) (hp : 2 ≤ p) :
    p ^ k ≤ laterDenom p k := by
  unfold laterDenom
  have hs : 1 ≤ p - 1 := by omega
  simpa only [mul_one] using Nat.mul_le_mul_left (p ^ k) hs

lemma later_line_strict_below_level (p k l : ℕ) (hp : 2 ≤ p) (hl : l < k) :
    p ^ k + laterDenom p k * l < p ^ l + laterDenom p k * k := by
  have hpow : 0 < p ^ l := pow_pos (by omega) l
  calc
    p ^ k + laterDenom p k * l ≤
        laterDenom p k + laterDenom p k * l :=
      Nat.add_le_add_right (prime_power_le_laterDenom p k hp) _
    _ = laterDenom p k * (l + 1) := by ring
    _ ≤ laterDenom p k * k := Nat.mul_le_mul_left _ (by omega)
    _ < p ^ l + laterDenom p k * k := by omega

lemma later_line_le (p k l : ℕ) (hp : 2 ≤ p) :
    p ^ k + laterDenom p k * l ≤ p ^ l + laterDenom p k * k := by
  by_cases hl : l < k
  · exact (later_line_strict_below_level p k l hp hl).le
  · have hkl : k ≤ l := Nat.le_of_not_gt hl
    let t : ℕ := l - k
    have hlt : k + t = l := Nat.add_sub_of_le hkl
    have hpower := affine_le_prime_power p t hp
    calc
      p ^ k + laterDenom p k * l =
          p ^ k * (1 + (p - 1) * t) + laterDenom p k * k := by
        rw [← hlt]
        unfold laterDenom
        ring
      _ ≤ p ^ k * p ^ t + laterDenom p k * k :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (p ^ k) hpower) _
      _ = p ^ l + laterDenom p k * k := by rw [← pow_add, hlt]

lemma later_line_strict_of_not_endpoints (p k l : ℕ) (hp : 2 ≤ p)
    (hlk : l ≠ k) (hlk1 : l ≠ k + 1) :
    p ^ k + laterDenom p k * l < p ^ l + laterDenom p k * k := by
  by_cases hl : l < k
  · exact later_line_strict_below_level p k l hp hl
  · have hkl : k ≤ l := Nat.le_of_not_gt hl
    let t : ℕ := l - k
    have hlt : k + t = l := Nat.add_sub_of_le hkl
    have ht : 2 ≤ t := by omega
    have hpower := affine_lt_prime_power p t hp ht
    have hq : 0 < p ^ k := pow_pos (by omega) k
    calc
      p ^ k + laterDenom p k * l =
          p ^ k * (1 + (p - 1) * t) + laterDenom p k * k := by
        rw [← hlt]
        unfold laterDenom
        ring
      _ < p ^ k * p ^ t + laterDenom p k * k :=
        Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hpower hq) _
      _ = p ^ l + laterDenom p k * k := by rw [← pow_add, hlt]

lemma later_line_endpoint_eq (p k : ℕ) (hp : 2 ≤ p) :
    p ^ k + laterDenom p k * (k + 1) =
      p ^ (k + 1) + laterDenom p k * k := by
  have hs : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  unfold laterDenom
  rw [pow_succ]
  have hm := congrArg (fun a : ℕ => p ^ k * a) hs
  nlinarith [hm]

lemma later_line_le_at_index (p k l j : ℕ) (hp : 2 ≤ p) (hj : p ^ l ≤ j) :
    p ^ k + laterDenom p k * l ≤ j + laterDenom p k * k :=
  (later_line_le p k l hp).trans (Nat.add_le_add_right hj _)

lemma later_line_strict_at_index (p k l j : ℕ) (hp : 2 ≤ p)
    (hj : p ^ l ≤ j) (houtside : j < p ^ k ∨ p ^ (k + 1) < j) :
    p ^ k + laterDenom p k * l < j + laterDenom p k * k := by
  have hnext : p ^ k ≤ p ^ (k + 1) := by
    rw [pow_succ]
    simpa only [mul_one] using Nat.mul_le_mul_left (p ^ k) (show 1 ≤ p by omega)
  by_cases hlk : l = k
  · subst l
    have hjstrict : p ^ k < j := by omega
    exact Nat.add_lt_add_right hjstrict _
  by_cases hlk1 : l = k + 1
  · subst l
    have hjstrict : p ^ (k + 1) < j := by omega
    rw [later_line_endpoint_eq p k hp]
    exact Nat.add_lt_add_right hjstrict _
  · exact (later_line_strict_of_not_endpoints p k l hp hlk hlk1).trans_le
      (Nat.add_le_add_right hj _)

lemma later_constant_line_strict (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k)
    (hnotBinary : ¬ (p = 2 ∧ k = 1)) :
    p ^ k < laterDenom p k * k := by
  have hs : 1 ≤ p - 1 := by omega
  have hsk : 1 < (p - 1) * k := by
    by_cases hk1 : k = 1
    · subst k
      have hp3 : 3 ≤ p := by omega
      omega
    · have hk2 : 2 ≤ k := by omega
      nlinarith
  have hq : 0 < p ^ k := pow_pos (by omega) k
  have hmul := Nat.mul_lt_mul_of_pos_left hsk hq
  simpa only [mul_one, laterDenom, mul_assoc] using hmul

section Coefficients

variable {R : Type*} [Ring R] {v : AbsoluteValue R ℝ}

lemma later_weight_le_from_line (P : R[X]) (b r k l j q : ℕ) (hb : 0 < b)
    (hline : q + b * l ≤ j + b * k)
    (hcoeff : v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (l : ℝ))) :
    v (P.coeff j) * (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ j ≤
      Real.exp (-(r : ℝ) + (k : ℝ) - (q : ℝ) / (b : ℝ)) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  have hlineR : (q : ℝ) + (b : ℝ) * (l : ℝ) ≤
      (j : ℝ) + (b : ℝ) * (k : ℝ) := by exact_mod_cast hline
  have hexponent : (l : ℝ) - (j : ℝ) / (b : ℝ) ≤
      (k : ℝ) - (q : ℝ) / (b : ℝ) := by
    apply le_of_mul_le_mul_right (a := (b : ℝ)) _ hbR
    nlinarith [div_mul_cancel₀ (j : ℝ) hbne, div_mul_cancel₀ (q : ℝ) hbne]
  calc
    v (P.coeff j) * (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ j ≤
        Real.exp (-(r : ℝ) + (l : ℝ)) *
          (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ j :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (Real.exp_pos _).le j)
    _ = Real.exp (-(r : ℝ) + (l : ℝ) - (j : ℝ) / (b : ℝ)) :=
      exp_first_weight b r l j
    _ ≤ Real.exp (-(r : ℝ) + (k : ℝ) - (q : ℝ) / (b : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)

lemma later_weight_lt_from_line (P : R[X]) (b r k l j q : ℕ) (hb : 0 < b)
    (hline : q + b * l < j + b * k)
    (hcoeff : v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (l : ℝ))) :
    v (P.coeff j) * (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ j <
      Real.exp (-(r : ℝ) + (k : ℝ) - (q : ℝ) / (b : ℝ)) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  have hlineR : (q : ℝ) + (b : ℝ) * (l : ℝ) <
      (j : ℝ) + (b : ℝ) * (k : ℝ) := by exact_mod_cast hline
  have hexponent : (l : ℝ) - (j : ℝ) / (b : ℝ) <
      (k : ℝ) - (q : ℝ) / (b : ℝ) := by
    apply lt_of_mul_lt_mul_right (a0 := hbR.le)
    nlinarith [div_mul_cancel₀ (j : ℝ) hbne, div_mul_cancel₀ (q : ℝ) hbne]
  calc
    v (P.coeff j) * (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ j ≤
        Real.exp (-(r : ℝ) + (l : ℝ)) *
          (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ j :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (Real.exp_pos _).le j)
    _ = Real.exp (-(r : ℝ) + (l : ℝ) - (j : ℝ) / (b : ℝ)) :=
      exp_first_weight b r l j
    _ < Real.exp (-(r : ℝ) + (k : ℝ) - (q : ℝ) / (b : ℝ)) :=
      Real.exp_lt_exp.mpr (by linarith)

theorem later_face_of_envelope
    (P : R[X]) (p r k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) (hkr : k < r)
    (hnotBinary : ¬ (p = 2 ∧ k = 1))
    (hzero : v (P.coeff 0) = Real.exp (-(r : ℝ)))
    (hvertex : ∀ l, 1 ≤ l → l ≤ r →
      v (P.coeff (p ^ l)) = Real.exp (-(r : ℝ) + (l : ℝ)))
    (hband : ∀ l, l < r → ∀ j, p ^ l ≤ j → j < p ^ (l + 1) →
      v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (l : ℝ)))
    (htail : ∀ j, p ^ r ≤ j → v (P.coeff j) ≤ 1) :
    IsMinGaussIndex P v (Real.exp (-(1 : ℝ) / (laterDenom p k : ℝ))) (p ^ k) ∧
      IsMaxGaussIndex P v
        (Real.exp (-(1 : ℝ) / (laterDenom p k : ℝ))) (p ^ (k + 1)) := by
  let b : ℕ := laterDenom p k
  let c : ℝ := Real.exp (-(1 : ℝ) / (b : ℝ))
  let B : ℝ := Real.exp (-(r : ℝ) + (k : ℝ) - ((p ^ k : ℕ) : ℝ) / (b : ℝ))
  have hb : 0 < b := laterDenom_pos p k hp
  have hc : 0 < c := Real.exp_pos _
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  have hconstant : v (P.coeff 0) * c ^ 0 < B := by
    rw [hzero, pow_zero, mul_one]
    apply Real.exp_lt_exp.mpr
    have hline := later_constant_line_strict p k hp hk hnotBinary
    have hlineR : ((p ^ k : ℕ) : ℝ) < (k : ℝ) * (b : ℝ) := by
      exact_mod_cast (show p ^ k < k * b by simpa only [b, mul_comm] using hline)
    have hdiv : ((p ^ k : ℕ) : ℝ) / (b : ℝ) < (k : ℝ) :=
      (div_lt_iff₀ hbR).mpr hlineR
    change -(r : ℝ) < -(r : ℝ) + (k : ℝ) - ((p ^ k : ℕ) : ℝ) / (b : ℝ)
    linarith
  have hbound : ∀ j, v (P.coeff j) * c ^ j ≤ B := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      exact hconstant.le
    · obtain ⟨l, hlr, hlj, hcoeff⟩ :=
        exists_coefficient_level P p r hband htail j (by omega)
      exact later_weight_le_from_line P b r k l j (p ^ k) hb
        (later_line_le_at_index p k l j hp hlj) hcoeff
  have hleft : v (P.coeff (p ^ k)) * c ^ (p ^ k) = B := by
    rw [hvertex k hk hkr.le]
    exact exp_first_weight b r k (p ^ k)
  have hright : v (P.coeff (p ^ (k + 1))) * c ^ (p ^ (k + 1)) = B := by
    rw [hvertex (k + 1) (by omega) (by omega)]
    change Real.exp (-(r : ℝ) + ((k + 1 : ℕ) : ℝ)) *
      (Real.exp (-(1 : ℝ) / (b : ℝ))) ^ (p ^ (k + 1)) = B
    rw [exp_first_weight b r (k + 1) (p ^ (k + 1))]
    apply congrArg Real.exp
    have hline := later_line_endpoint_eq p k hp
    have hlineR : ((p ^ k : ℕ) : ℝ) + (b : ℝ) * ((k + 1 : ℕ) : ℝ) =
        ((p ^ (k + 1) : ℕ) : ℝ) + (b : ℝ) * (k : ℝ) := by exact_mod_cast hline
    change -(r : ℝ) + ((k + 1 : ℕ) : ℝ) -
        ((p ^ (k + 1) : ℕ) : ℝ) / (b : ℝ) =
      -(r : ℝ) + (k : ℝ) - ((p ^ k : ℕ) : ℝ) / (b : ℝ)
    apply mul_left_cancel₀ hbne
    nlinarith [div_mul_cancel₀ ((p ^ k : ℕ) : ℝ) hbne,
      div_mul_cancel₀ ((p ^ (k + 1) : ℕ) : ℝ) hbne]
  have hnorm : P.gaussNorm v c = B := by
    obtain ⟨i, hi, _⟩ := P.exists_min_eq_gaussNorm v hc.le
    apply le_antisymm
    · rw [hi]
      exact hbound i
    · rw [← hleft]
      exact P.le_gaussNorm v hc.le (p ^ k)
  constructor
  · constructor
    · exact hnorm.trans hleft.symm
    · intro j hj
      rw [hnorm]
      by_cases hj0 : j = 0
      · subst j
        exact hconstant
      · obtain ⟨l, hlr, hlj, hcoeff⟩ :=
          exists_coefficient_level P p r hband htail j (by omega)
        exact later_weight_lt_from_line P b r k l j (p ^ k) hb
          (later_line_strict_at_index p k l j hp hlj (Or.inl hj)) hcoeff
  · constructor
    · exact hnorm.trans hright.symm
    · intro j hj
      rw [hnorm]
      obtain ⟨l, hlr, hlj, hcoeff⟩ :=
        exists_coefficient_level P p r hband htail j (by omega)
      exact later_weight_lt_from_line P b r k l j (p ^ k) hb
        (later_line_strict_at_index p k l j hp hlj (Or.inr hj)) hcoeff

end Coefficients

end EventualIrreducibility.FirstFace

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility.RootGeometry

open scoped BigOperators

theorem geometric_sum_trinomial (z : ℂ) (n : ℕ) :
    (z - 1) * ((∑ j ∈ Finset.range n, z ^ (j + 1)) - (n : ℂ)) =
      z ^ (n + 1) - ((n : ℂ) + 1) * z + (n : ℂ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      calc
        (z - 1) *
            ((∑ j ∈ Finset.range n, z ^ (j + 1)) + z ^ (n + 1) -
              ((n : ℂ) + 1)) =
            (z - 1) * ((∑ j ∈ Finset.range n, z ^ (j + 1)) - (n : ℂ)) +
              (z - 1) * (z ^ (n + 1) - 1) := by ring
        _ = (z ^ (n + 1) - ((n : ℂ) + 1) * z + (n : ℂ)) +
              (z - 1) * (z ^ (n + 1) - 1) := by rw [ih]
        _ = z ^ ((n + 1) + 1) - (((n : ℂ) + 1) + 1) * z +
              ((n : ℂ) + 1) := by
          simp only [pow_succ]
          ring

theorem sum_powers_of_trinomial
    {z : ℂ} {n : ℕ} (hne : z ≠ 1)
    (htrin : z ^ (n + 1) - ((n : ℂ) + 1) * z + (n : ℂ) = 0) :
    (∑ j ∈ Finset.range n, z ^ (j + 1)) = (n : ℂ) := by
  have hproduct :
      (z - 1) * ((∑ j ∈ Finset.range n, z ^ (j + 1)) - (n : ℂ)) = 0 := by
    rw [geometric_sum_trinomial]
    exact htrin
  have hsub : (∑ j ∈ Finset.range n, z ^ (j + 1)) - (n : ℂ) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr hne)
  exact sub_eq_zero.mp hsub

theorem norm_pow_le_one
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ∀ k : ℕ, ‖z‖ ^ k ≤ 1 := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ]
      calc
        ‖z‖ ^ k * ‖z‖ ≤ (1 : ℝ) * 1 :=
          mul_le_mul ih hz (norm_nonneg z) (by norm_num)
        _ = 1 := by ring

theorem re_eq_one_of_norm_le_one_of_sum_powers
    {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : ‖z‖ ≤ 1)
    (hsum : (∑ j ∈ Finset.range n, z ^ (j + 1)) = (n : ℂ)) :
    z.re = 1 := by
  have hrealSum :
      (∑ j ∈ Finset.range n, (z ^ (j + 1)).re) = (n : ℝ) := by
    simpa using congrArg Complex.re hsum
  have hterm : ∀ j ∈ Finset.range n, (z ^ (j + 1)).re ≤ 1 := by
    intro j hj
    calc
      (z ^ (j + 1)).re ≤ ‖z ^ (j + 1)‖ := Complex.re_le_norm _
      _ = ‖z‖ ^ (j + 1) := norm_pow _ _
      _ ≤ 1 := norm_pow_le_one hz (j + 1)
  have hgapNonneg :
      ∀ j ∈ Finset.range n, 0 ≤ 1 - (z ^ (j + 1)).re := by
    intro j hj
    exact sub_nonneg.mpr (hterm j hj)
  have hgapSum :
      (∑ j ∈ Finset.range n, (1 - (z ^ (j + 1)).re)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp [hrealSum]
  have hzeroMem : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
  have hzeroLe :
      1 - (z ^ (0 + 1)).re ≤
        ∑ j ∈ Finset.range n, (1 - (z ^ (j + 1)).re) :=
    Finset.single_le_sum hgapNonneg hzeroMem
  have hzeroNonneg : 0 ≤ 1 - z.re := by
    simpa using hgapNonneg 0 hzeroMem
  have hzeroNonpos : 1 - z.re ≤ 0 := by
    simpa only [Nat.zero_add, pow_one, hgapSum] using hzeroLe
  linarith

theorem complex_sq_norm (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simpa only [Complex.normSq_apply, pow_two] using
    (Complex.normSq_eq_norm_sq z).symm

theorem eq_one_of_norm_le_one_of_sum_powers
    {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : ‖z‖ ≤ 1)
    (hsum : (∑ j ∈ Finset.range n, z ^ (j + 1)) = (n : ℂ)) :
    z = 1 := by
  have hre : z.re = 1 := re_eq_one_of_norm_le_one_of_sum_powers hn hz hsum
  have hnormSquare : ‖z‖ ^ 2 ≤ 1 := norm_pow_le_one hz 2
  have hnormIdentity := complex_sq_norm z
  have himSquare : z.im ^ 2 = 0 := by
    nlinarith [sq_nonneg z.im]
  have him : z.im = 0 := (sq_eq_zero_iff).mp himSquare
  apply Complex.ext
  · simpa using hre
  · simpa using him

theorem one_lt_norm_of_sum_powers
    {z : ℂ} {n : ℕ} (hn : 0 < n) (hne : z ≠ 1)
    (hsum : (∑ j ∈ Finset.range n, z ^ (j + 1)) = (n : ℂ)) :
    1 < ‖z‖ := by
  by_contra hnot
  have hz : ‖z‖ ≤ 1 := le_of_not_gt hnot
  exact hne (eq_one_of_norm_le_one_of_sum_powers hn hz hsum)

theorem one_lt_norm_of_trinomial
    {z : ℂ} {n : ℕ} (hn : 0 < n) (hne : z ≠ 1)
    (htrin : z ^ (n + 1) - ((n : ℂ) + 1) * z + (n : ℂ) = 0) :
    1 < ‖z‖ :=
  one_lt_norm_of_sum_powers hn hne (sum_powers_of_trinomial hne htrin)

end EventualIrreducibility.RootGeometry

namespace EventualIrreducibility.RootGeometry
open Polynomial

lemma trinomial_of_root {n : ℕ} {z : ℂ}
    (hz : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) :
    z ^ (n + 1) - ((n : ℂ) + 1) * z + (n : ℂ) = 0 := by
  have hroot : (fInt n).eval₂ (Int.castRingHom ℂ) z = 0 := by
    simpa only [Polynomial.eval_map] using hz
  have h := congrArg (fun P : ℤ[X] => P.eval₂ (Int.castRingHom ℂ) z)
    (trinomial_identity n)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_one, hroot, mul_zero,
    Polynomial.eval₂_add, Polynomial.eval₂_C, map_natCast, Nat.cast_add, Nat.cast_one] at h
  simpa only [map_add, map_natCast, map_one, Polynomial.eval₂_natCast] using h.symm

lemma root_ne_one {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) : z ≠ 1 := by
  intro h
  subst z
  rw [Polynomial.eval_map, Polynomial.eval₂_at_one] at hz
  change (((fInt n).eval 1 : ℤ) : ℂ) = 0 at hz
  have hzero : (fInt n).eval 1 = 0 := by exact_mod_cast hz
  exact eval_one_ne_zero n hn hzero

theorem one_lt_norm_root {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) :
    1 < ‖z‖ :=
  one_lt_norm_of_trinomial hn (root_ne_one hn hz) (trinomial_of_root hz)

theorem norm_root_pow_lt {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) :
    ‖z‖ ^ n < 2 * (n : ℝ) + 1 := by
  have hlow := one_lt_norm_root hn hz
  have ht := trinomial_of_root hz
  have heq : z ^ (n + 1) = ((n : ℂ) + 1) * z - (n : ℂ) := by
    linear_combination ht
  have hnorm : ‖z‖ ^ (n + 1) ≤ ((n : ℝ) + 1) * ‖z‖ + (n : ℝ) := by
    calc
      ‖z‖ ^ (n + 1) = ‖z ^ (n + 1)‖ := (norm_pow _ _).symm
      _ = ‖((n : ℂ) + 1) * z - (n : ℂ)‖ := congrArg norm heq
      _ ≤ ‖((n : ℂ) + 1) * z‖ + ‖(n : ℂ)‖ := norm_sub_le _ _
      _ = ((n : ℝ) + 1) * ‖z‖ + (n : ℝ) := by
        rw [norm_mul]
        norm_cast
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [pow_succ] at hnorm
  by_contra hnot
  have hge : 2 * (n : ℝ) + 1 ≤ ‖z‖ ^ n := le_of_not_gt hnot
  have hm := mul_le_mul_of_nonneg_right hge (norm_nonneg z)
  nlinarith

end EventualIrreducibility.RootGeometry

namespace EventualIrreducibility.RootGeometry
open Polynomial

theorem norm_root_lt_rpow {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) :
    ‖z‖ < (2 * (n : ℝ) + 1) ^ (1 / (n : ℝ)) := by
  have hbase : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
  have hr : 0 ≤ (2 * (n : ℝ) + 1) ^ (1 / (n : ℝ)) := Real.rpow_nonneg hbase _
  have hpow : ((2 * (n : ℝ) + 1) ^ (1 / (n : ℝ))) ^ n =
      2 * (n : ℝ) + 1 := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hbase (Nat.ne_of_gt hn)
  by_contra hnot
  have hle : (2 * (n : ℝ) + 1) ^ (1 / (n : ℝ)) ≤ ‖z‖ := le_of_not_gt hnot
  have hm := pow_le_pow_left₀ hr hle n
  rw [hpow] at hm
  exact (not_lt_of_ge hm) (norm_root_pow_lt hn hz)

theorem root_of_mapped_factor {n : ℕ} (s : FactorSeries n) {z : ℂ}
    (hz : (s.factor.map (Int.castRingHom ℂ)).eval z = 0) :
    ((fInt n).map (Int.castRingHom ℂ)).eval z = 0 := by
  obtain ⟨h, hh⟩ := s.divides
  rw [hh, Polynomial.map_mul, Polynomial.eval_mul, hz, zero_mul]

theorem factor_root_annulus {n : ℕ} (s : FactorSeries n) (hn : 0 < n) {z : ℂ}
    (hz : (s.factor.map (Int.castRingHom ℂ)).eval z = 0) :
    1 < ‖z‖ ∧ ‖z‖ < (2 * (n : ℝ) + 1) ^ (1 / (n : ℝ)) := by
  have hf := root_of_mapped_factor s hz
  exact ⟨one_lt_norm_root hn hf, norm_root_lt_rpow hn hf⟩

end EventualIrreducibility.RootGeometry

open Polynomial

namespace EventualIrreducibility.FirstFace

def faceChainOffset (p r : ℕ) : ℕ := if p = 2 ∧ 2 ≤ r then 1 else 0

def faceChainCount (p r : ℕ) : ℕ := r - faceChainOffset p r

def faceChainDenom (p r i : ℕ) : ℕ :=
  if i = 0 then p else p ^ (i + faceChainOffset p r) * (p - 1)

def faceChainVertex (p r i : ℕ) : ℕ :=
  if i = 0 then 0 else p ^ (i + faceChainOffset p r)

lemma faceChainOffset_lt (p r : ℕ) (hr : 1 ≤ r) : faceChainOffset p r < r := by
  unfold faceChainOffset
  split_ifs with h
  · omega
  · omega

lemma faceChainCount_pos (p r : ℕ) (hr : 1 ≤ r) : 0 < faceChainCount p r := by
  have h := faceChainOffset_lt p r hr
  unfold faceChainCount
  omega

lemma faceChainCount_add_offset (p r : ℕ) (hr : 1 ≤ r) :
    faceChainCount p r + faceChainOffset p r = r := by
  exact Nat.sub_add_cancel (faceChainOffset_lt p r hr).le

lemma faceChainVertex_zero (p r : ℕ) : faceChainVertex p r 0 = 0 := by
  simp [faceChainVertex]

lemma faceChainVertex_one (p r : ℕ) :
    faceChainVertex p r 1 = firstFaceLast p r := by
  by_cases h : p = 2 ∧ 2 ≤ r
  · simp [faceChainVertex, faceChainOffset, firstFaceLast, h]
  · simp [faceChainVertex, faceChainOffset, firstFaceLast, h]

lemma faceChainVertex_succ (p r i : ℕ) :
    faceChainVertex p r (i + 1) = p ^ ((i + faceChainOffset p r) + 1) := by
  have hi : i + 1 ≠ 0 := by omega
  simp only [faceChainVertex, hi, if_false]
  congr 1
  omega

lemma faceChainVertex_at_count (p r : ℕ) (hr : 1 ≤ r) :
    faceChainVertex p r (faceChainCount p r) = p ^ r := by
  have hc : faceChainCount p r ≠ 0 := Nat.ne_of_gt (faceChainCount_pos p r hr)
  simp only [faceChainVertex, hc, if_false, faceChainCount_add_offset p r hr]

lemma faceChainDenom_pos (p r i : ℕ) (hp : 2 ≤ p) : 0 < faceChainDenom p r i := by
  by_cases hi : i = 0
  · simp only [faceChainDenom, hi, if_true]
    omega
  · simp only [faceChainDenom, hi, if_false]
    exact Nat.mul_pos (pow_pos (by omega) _) (by omega)

lemma prime_dvd_faceChainDenom (p r i : ℕ) : p ∣ faceChainDenom p r i := by
  by_cases hi : i = 0
  · simp [faceChainDenom, hi]
  · have he : 1 ≤ i + faceChainOffset p r := by omega
    have hs : i + faceChainOffset p r = (i + faceChainOffset p r - 1) + 1 := by omega
    simp only [faceChainDenom, hi, if_false]
    refine ⟨p ^ (i + faceChainOffset p r - 1) * (p - 1), ?_⟩
    calc
      p ^ (i + faceChainOffset p r) * (p - 1) =
          p ^ ((i + faceChainOffset p r - 1) + 1) * (p - 1) :=
        congrArg (fun e : ℕ => p ^ e * (p - 1)) hs
      _ = p * (p ^ (i + faceChainOffset p r - 1) * (p - 1)) := by
        rw [pow_succ]
        ring

lemma faceChainDenom_step_nonzero (p r i : ℕ) (hi : i ≠ 0) :
    faceChainDenom p r (i + 1) = p * faceChainDenom p r i := by
  have hi1 : i + 1 ≠ 0 := by omega
  have he : i + 1 + faceChainOffset p r = (i + faceChainOffset p r) + 1 := by omega
  simp only [faceChainDenom, hi, hi1, if_false]
  rw [he, pow_succ]
  ring

lemma faceChainDenom_strict (p r i : ℕ) (hp : 2 ≤ p)
    (hi : i + 1 < faceChainCount p r) :
    faceChainDenom p r i < faceChainDenom p r (i + 1) := by
  by_cases hi0 : i = 0
  · subst i
    by_cases hbinary : p = 2 ∧ 2 ≤ r
    · norm_num [faceChainDenom, faceChainOffset, hbinary, hbinary.1]
    · have hpne : p ≠ 2 := by
        intro hp2
        have hoff : faceChainOffset p r = 0 := by simp [faceChainOffset, hbinary]
        have hcount : faceChainCount p r = r := by simp [faceChainCount, hoff]
        have hr2 : 2 ≤ r := by omega
        exact hbinary ⟨hp2, hr2⟩
      have hp3 : 3 ≤ p := by omega
      have hs : 2 ≤ p - 1 := by omega
      change p < p ^ (1 + faceChainOffset p r) * (p - 1)
      have hoff : faceChainOffset p r = 0 := by simp [faceChainOffset, hbinary]
      rw [hoff, Nat.add_zero, pow_one]
      nlinarith
  · rw [faceChainDenom_step_nonzero p r i hi0]
    have hpos := faceChainDenom_pos p r i hp
    nlinarith

lemma exp_radius_strict_of_denominators (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    Real.exp (-(1 : ℝ) / (a : ℝ)) < Real.exp (-(1 : ℝ) / (b : ℝ)) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  apply Real.exp_lt_exp.mpr
  apply (div_lt_div_iff₀ haR hbR).mpr
  nlinarith

lemma exp_radius_lt_one (a : ℕ) (ha : 0 < a) :
    Real.exp (-(1 : ℝ) / (a : ℝ)) < 1 := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (by norm_num) haR

lemma faceChain_later_index (p r i : ℕ) (hr : 1 ≤ r)
    (hi0 : i ≠ 0) (hi : i < faceChainCount p r) :
    1 ≤ i + faceChainOffset p r ∧
      i + faceChainOffset p r < r ∧
      ¬ (p = 2 ∧ i + faceChainOffset p r = 1) := by
  have htotal := faceChainCount_add_offset p r hr
  have hk : 1 ≤ i + faceChainOffset p r := by omega
  have hkr : i + faceChainOffset p r < r := by omega
  refine ⟨hk, hkr, ?_⟩
  rintro ⟨hp2, hk1⟩
  have hr2 : 2 ≤ r := by omega
  have hoff : faceChainOffset p r = 1 := by simp [faceChainOffset, hp2, hr2]
  omega

section Coefficients

variable {R : Type*} [Ring R] {v : AbsoluteValue R ℝ}

theorem faceChain_certificates_of_envelope
    (P : R[X]) (p r : ℕ) (hp : 2 ≤ p) (hr : 1 ≤ r)
    (hzero : v (P.coeff 0) = Real.exp (-(r : ℝ)))
    (hvertex : ∀ k, 1 ≤ k → k ≤ r →
      v (P.coeff (p ^ k)) = Real.exp (-(r : ℝ) + (k : ℝ)))
    (hband : ∀ k, k < r → ∀ j, p ^ k ≤ j → j < p ^ (k + 1) →
      v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ)))
    (htail : ∀ j, p ^ r ≤ j → v (P.coeff j) ≤ 1) :
    (∀ i, i < faceChainCount p r →
      IsMinGaussIndex P v (Real.exp (-(1 : ℝ) / (faceChainDenom p r i : ℝ)))
        (faceChainVertex p r i)) ∧
    (∀ i, i < faceChainCount p r →
      IsMaxGaussIndex P v (Real.exp (-(1 : ℝ) / (faceChainDenom p r i : ℝ)))
        (faceChainVertex p r (i + 1))) ∧
      IsMinGaussIndex P v 1 (faceChainVertex p r (faceChainCount p r)) := by
  obtain ⟨hfirstMin, hfirstMax, hterminal⟩ :=
    first_face_and_terminal_of_envelope P p r hp hr hzero hvertex hband htail
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa [faceChainDenom, faceChainVertex] using hfirstMin
    · obtain ⟨hk, hkr, hnot⟩ := faceChain_later_index p r i hr hi0 hi
      have hface := later_face_of_envelope P p r (i + faceChainOffset p r)
        hp hk hkr hnot hzero hvertex hband htail
      simpa only [faceChainDenom, faceChainVertex, hi0, if_false, laterDenom]
        using hface.1
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      rw [show (0 : ℕ) + 1 = 1 by omega, faceChainVertex_one]
      simpa [faceChainDenom] using hfirstMax
    · obtain ⟨hk, hkr, hnot⟩ := faceChain_later_index p r i hr hi0 hi
      have hface := later_face_of_envelope P p r (i + faceChainOffset p r)
        hp hk hkr hnot hzero hvertex hband htail
      rw [faceChainVertex_succ]
      simpa only [faceChainDenom, hi0, if_false, laterDenom] using hface.2
  · rw [faceChainVertex_at_count p r hr]
    exact hterminal

theorem minGaussIndex_one_dvd_of_envelope
    (hna : IsNonarchimedean v)
    (G H : R[X]) (hG : G ≠ 0) (hH : H ≠ 0)
    (p r : ℕ) (hp : 2 ≤ p) (hr : 1 ≤ r)
    (hdiscrete : ∀ a : R, a ≠ 0 → ∃ z : ℤ, v a = Real.exp (-(z : ℝ)))
    (hzero : v ((G * H).coeff 0) = Real.exp (-(r : ℝ)))
    (hvertex : ∀ k, 1 ≤ k → k ≤ r →
      v ((G * H).coeff (p ^ k)) = Real.exp (-(r : ℝ) + (k : ℝ)))
    (hband : ∀ k, k < r → ∀ j, p ^ k ≤ j → j < p ^ (k + 1) →
      v ((G * H).coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ)))
    (htail : ∀ j, p ^ r ≤ j → v ((G * H).coeff j) ≤ 1)
    (terminal : ℕ) (hterminal : IsMinGaussIndex G v 1 terminal) :
    p ∣ terminal := by
  obtain ⟨hmin, hmax, hlast⟩ := faceChain_certificates_of_envelope
    (G * H) p r hp hr hzero hvertex hband htail
  exact minGaussIndex_one_dvd_of_critical_faces hna G H hG hH p
    (faceChainCount p r) (faceChainCount_pos p r hr)
    (faceChainDenom p r) (faceChainVertex p r) hdiscrete
    (faceChainVertex_zero p r)
    (fun i _ => faceChainDenom_pos p r i hp)
    (fun i _ => prime_dvd_faceChainDenom p r i)
    (fun i hi => exp_radius_strict_of_denominators
      (faceChainDenom p r i) (faceChainDenom p r (i + 1))
      (faceChainDenom_pos p r i hp) (faceChainDenom_strict p r i hp hi))
    (exp_radius_lt_one (faceChainDenom p r (faceChainCount p r - 1))
      (faceChainDenom_pos p r (faceChainCount p r - 1) hp))
    hmin hmax hlast terminal hterminal

end Coefficients

end EventualIrreducibility.FirstFace

namespace EventualIrreducibility.FactorPositive

open Filter

theorem eval_pos_of_dvd_of_pos_later
    {F g : Polynomial ℝ}
    (hF : ∀ x : ℝ, 0 ≤ x → 0 < F.eval x)
    (hdiv : g ∣ F)
    {x t : ℝ} (hx : 0 ≤ x) (hxt : x ≤ t)
    (hgt : 0 < g.eval t) :
    0 < g.eval x := by
  by_contra hnot
  have hgx : g.eval x ≤ 0 := le_of_not_gt hnot
  have hcontinuous : Continuous (fun u : ℝ => g.eval u) := by
    fun_prop
  have hIV :
      Set.Icc (g.eval x) (g.eval t) ⊆
        (fun u : ℝ => g.eval u) '' Set.Icc x t :=
    intermediate_value_Icc hxt hcontinuous.continuousOn
  have hzero : (0 : ℝ) ∈ Set.Icc (g.eval x) (g.eval t) :=
    ⟨hgx, le_of_lt hgt⟩
  rcases hIV hzero with ⟨u, hu, hgu⟩
  change g.eval u = 0 at hgu
  have hu_nonneg : 0 ≤ u := le_trans hx hu.1
  have hFu_pos : 0 < F.eval u := hF u hu_nonneg
  rcases hdiv with ⟨h, hfactor⟩
  have hFu_zero : F.eval u = 0 := by
    rw [hfactor, Polynomial.eval_mul, hgu, zero_mul]
  linarith

theorem eval_pos_of_dvd_of_eventually_pos
    {F g : Polynomial ℝ}
    (hF : ∀ x : ℝ, 0 ≤ x → 0 < F.eval x)
    (hdiv : g ∣ F)
    (heventual : ∀ᶠ t : ℝ in atTop, 0 < g.eval t)
    {x : ℝ} (hx : 0 ≤ x) :
    0 < g.eval x := by
  rcases (heventual.and (eventually_ge_atTop x)).exists with ⟨t, ht⟩
  exact eval_pos_of_dvd_of_pos_later hF hdiv hx ht.2 ht.1

theorem coeff_zero_pos_of_dvd_of_eventually_pos
    {F g : Polynomial ℝ}
    (hF : ∀ x : ℝ, 0 ≤ x → 0 < F.eval x)
    (hdiv : g ∣ F)
    (heventual : ∀ᶠ t : ℝ in atTop, 0 < g.eval t) :
    0 < g.coeff 0 := by
  simpa only [← Polynomial.coeff_zero_eq_eval_zero] using
    (eval_pos_of_dvd_of_eventually_pos hF hdiv heventual
      (x := 0) (by norm_num))

theorem coeff_zero_pos_of_dvd_of_tendsto
    {F g : Polynomial ℝ}
    (hF : ∀ x : ℝ, 0 ≤ x → 0 < F.eval x)
    (hdiv : g ∣ F)
    (hlimit : Tendsto (fun t : ℝ => g.eval t) atTop atTop) :
    0 < g.coeff 0 := by
  have heventual : ∀ᶠ t : ℝ in atTop, 0 < g.eval t :=
    hlimit.eventually (eventually_gt_atTop (0 : ℝ))
  exact coeff_zero_pos_of_dvd_of_eventually_pos hF hdiv heventual

theorem coeff_zero_pos_of_monic_dvd
    {F g : Polynomial ℝ}
    (hF : ∀ x : ℝ, 0 ≤ x → 0 < F.eval x)
    (hdiv : g ∣ F) (hg : g.Monic) :
    0 < g.coeff 0 := by
  by_cases hdegree_zero : g.natDegree = 0
  · have hleading : g.leadingCoeff = 1 := hg
    have hcoeff : g.coeff g.natDegree = 1 :=
      hg.coeff_natDegree
    have hzero : g.coeff 0 = 1 := by
      simpa only [hdegree_zero] using hcoeff
    rw [hzero]
    norm_num
  · have hdegree_pos : 0 < g.natDegree := Nat.pos_of_ne_zero hdegree_zero
    have hleading_pos : 0 < g.leadingCoeff := by
      rw [hg.leadingCoeff]
      norm_num
    have hlimit : Tendsto (fun t : ℝ => g.eval t) atTop atTop := by
      exact Polynomial.tendsto_atTop_of_leadingCoeff_nonneg g
        (Polynomial.natDegree_pos_iff_degree_pos.mp hdegree_pos)
        (le_of_lt hleading_pos)
    exact coeff_zero_pos_of_dvd_of_tendsto hF hdiv hlimit

end EventualIrreducibility.FactorPositive

namespace EventualIrreducibility

lemma real_eval_fInt_nonneg (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ ((fInt n).map (Int.castRingHom ℝ)).eval x := by
  induction n with
  | zero => simp [fInt]
  | succ n ih =>
    rw [fInt_succ]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, Int.coe_castRingHom, Int.cast_natCast]
    exact add_nonneg (mul_nonneg hx ih) (by positivity)

lemma real_eval_fInt_pos (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    0 < ((fInt n).map (Int.castRingHom ℝ)).eval x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [fInt_succ]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, Int.coe_castRingHom, Int.cast_natCast]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg hx (real_eval_fInt_nonneg m x hx)) (by positivity)

lemma FactorSeries.constant_pos {n : ℕ} (s : FactorSeries n) (hn : 0 < n) :
    0 < s.factor.coeff 0 := by
  have h := FactorPositive.coeff_zero_pos_of_monic_dvd
    (real_eval_fInt_pos n hn) (Polynomial.map_dvd (Int.castRingHom ℝ) s.divides)
    (s.monic.map (Int.castRingHom ℝ))
  have hreal : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using h
  exact_mod_cast hreal

end EventualIrreducibility

open Polynomial

namespace EventualIrreducibility.ActualEnvelope

lemma prime_dvd_positive_power (p k : ℕ) (hk : 1 ≤ k) : p ∣ p ^ k := by
  cases k with
  | zero => omega
  | succ k =>
    refine ⟨p ^ k, ?_⟩
    rw [pow_succ]
    ring

lemma prime_power_ge_two (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) : 2 ≤ p ^ k := by
  exact hp.two_le.trans
    (Nat.le_of_dvd (pow_pos hp.pos k) (prime_dvd_positive_power p k hk))

lemma prime_power_le_of_index_le (p a b : ℕ) (hp : p.Prime) (hab : a ≤ b) :
    p ^ a ≤ p ^ b :=
  Nat.le_of_dvd (pow_pos hp.pos b) (pow_dvd_pow p hab)

lemma power_dvd_of_padicVal_eq (p M r : ℕ) (hp : p.Prime)
    (hM : 0 < M) (hval : padicValNat p M = r) : p ^ r ∣ M := by
  let : Fact p.Prime := ⟨hp⟩
  apply (padicValNat_dvd_iff_le (p := p) (a := M) (n := r) (Nat.ne_of_gt hM)).mpr
  rw [hval]

lemma padicVal_le_of_lt_power (p j k : ℕ) (hp : p.Prime)
    (hj : 0 < j) (hbound : j < p ^ (k + 1)) : padicValNat p j ≤ k := by
  let : Fact p.Prime := ⟨hp⟩
  by_contra h
  have hdiv : p ^ (k + 1) ∣ j :=
    (padicValNat_dvd_iff_le (p := p) (a := j) (n := k + 1)
      (Nat.ne_of_gt hj)).mpr (by omega)
  have hle := Nat.le_of_dvd hj hdiv
  omega

lemma pred_not_dvd_of_dvd (p j : ℕ) (hp : p.Prime)
    (hj : 1 ≤ j) (hdiv : p ∣ j) : ¬ p ∣ j - 1 := by
  intro hpred
  have hsum : p ∣ (j - 1) + 1 := by
    simpa only [Nat.sub_add_cancel hj] using hdiv
  exact hp.not_dvd_one
    ((Nat.dvd_add_iff_left hpred).mpr (by simpa only [Nat.add_comm] using hsum))

lemma padicVal_mul_pred_le_of_lt_power (p j k : ℕ) (hp : p.Prime)
    (hj : 2 ≤ j) (hbound : j < p ^ (k + 1)) :
    padicValNat p (j * (j - 1)) ≤ k := by
  let : Fact p.Prime := ⟨hp⟩
  have hj0 : j ≠ 0 := by omega
  have hjpred0 : j - 1 ≠ 0 := by omega
  rw [padicValNat.mul hj0 hjpred0]
  by_cases hdiv : p ∣ j
  · rw [padicValNat.eq_zero_of_not_dvd (pred_not_dvd_of_dvd p j hp (by omega) hdiv),
      Nat.add_zero]
    exact padicVal_le_of_lt_power p j k hp (by omega) hbound
  · rw [padicValNat.eq_zero_of_not_dvd hdiv, Nat.zero_add]
    exact padicVal_le_of_lt_power p (j - 1) k hp (by omega) (by omega)

lemma padicVal_prime_power_mul_pred (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    padicValNat p (p ^ k * (p ^ k - 1)) = k := by
  let : Fact p.Prime := ⟨hp⟩
  have hq2 := prime_power_ge_two p k hp hk
  have hq0 : p ^ k ≠ 0 := by omega
  have hpred0 : p ^ k - 1 ≠ 0 := by omega
  have hpred : ¬ p ∣ p ^ k - 1 :=
    pred_not_dvd_of_dvd p (p ^ k) hp (by omega) (prime_dvd_positive_power p k hk)
  rw [padicValNat.mul hq0 hpred0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hpred, Nat.add_zero]

section ValuedRing

variable {R : Type*} [CommRing R] [Nontrivial R] {v : AbsoluteValue R ℝ}

structure TaylorEnvelope (P : R[X]) (v : AbsoluteValue R ℝ) (p r : ℕ) : Prop where
  zero_eq : v (P.coeff 0) = Real.exp (-(r : ℝ))
  vertex_eq : ∀ k, 1 ≤ k → k ≤ r →
    v (P.coeff (p ^ k)) = Real.exp (-(r : ℝ) + (k : ℝ))
  band_le : ∀ k, k < r → ∀ j, p ^ k ≤ j → j < p ^ (k + 1) →
    v (P.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ))
  tail_le : ∀ j, p ^ r ≤ j → v (P.coeff j) ≤ 1

omit [Nontrivial R] in
lemma norm_natCast_le_one (p : ℕ)
    (hnorm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat p m : ℝ)))
    (m : ℕ) : v (m : R) ≤ 1 := by
  by_cases hm : m = 0
  · subst m
    simp
  · rw [hnorm m hm]
    apply Real.exp_le_one_iff.mpr
    have hnonneg : (0 : ℝ) ≤ (padicValNat p m : ℝ) := Nat.cast_nonneg _
    linarith

lemma higher_coefficient_norm (n j : ℕ) (z : R)
    (hz : v z = 1) (hj : 2 ≤ j) :
    v ((shiftedTrinomial n z).coeff j) = v (((n + 1).choose j : ℕ) : R) := by
  rw [shiftedTrinomial_coeff_ge_two n z j hj, map_mul, map_pow, hz,
    one_pow, mul_one]

theorem taylor_envelope_of_scalar_valuations
    (n p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (z : R)
    (hnorm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat p m : ℝ)))
    (hz : v z = 1) (hpower : p ^ r ≤ n + 1)
    (hzero : v ((shiftedTrinomial n z).coeff 0) = Real.exp (-(r : ℝ)))
    (hlinear : v ((shiftedTrinomial n z).coeff 1) ≤ Real.exp (-(r : ℝ)))
    (D : ℕ → ℕ)
    (hvaluation : ∀ j, 2 ≤ j → j ≤ p ^ r →
      padicValNat p ((n + 1).choose j) + D j = r)
    (hDvertex : ∀ k, 1 ≤ k → D (p ^ k) = k)
    (hDband : ∀ k j, 2 ≤ j → j < p ^ (k + 1) → D j ≤ k) :
    TaylorEnvelope (shiftedTrinomial n z) v p r := by
  have hnormCoeff : ∀ j, 2 ≤ j → j ≤ p ^ r →
      v ((shiftedTrinomial n z).coeff j) =
        Real.exp (-(padicValNat p ((n + 1).choose j) : ℝ)) := by
    intro j hj hjr
    rw [higher_coefficient_norm n j z hz hj]
    apply hnorm
    exact Nat.choose_ne_zero (hjr.trans hpower)
  refine ⟨hzero, ?_, ?_, ?_⟩
  · intro k hk hkr
    have hj2 := prime_power_ge_two p k hp hk
    have hjr := prime_power_le_of_index_le p k r hp hkr
    rw [hnormCoeff (p ^ k) hj2 hjr]
    apply congrArg Real.exp
    have hval := hvaluation (p ^ k) hj2 hjr
    rw [hDvertex k hk] at hval
    have hvalR : (padicValNat p ((n + 1).choose (p ^ k)) : ℝ) + (k : ℝ) =
        (r : ℝ) := by exact_mod_cast hval
    linarith
  · intro k hkr j hlow hhigh
    have hjpos : 0 < j := lt_of_lt_of_le (pow_pos hp.pos k) hlow
    by_cases hj1 : j = 1
    · subst j
      apply hlinear.trans
      apply Real.exp_le_exp.mpr
      have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    · have hj2 : 2 ≤ j := by omega
      have hnext : p ^ (k + 1) ≤ p ^ r :=
        prime_power_le_of_index_le p (k + 1) r hp (by omega)
      have hjr : j ≤ p ^ r := by omega
      rw [hnormCoeff j hj2 hjr]
      apply Real.exp_le_exp.mpr
      have hval := hvaluation j hj2 hjr
      have hD := hDband k j hj2 hhigh
      have hvalR : (padicValNat p ((n + 1).choose j) : ℝ) + (D j : ℝ) =
          (r : ℝ) := by exact_mod_cast hval
      have hDR : (D j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hD
      linarith
  · intro j hj
    have hq2 := prime_power_ge_two p r hp hr
    have hj2 : 2 ≤ j := by omega
    rw [higher_coefficient_norm n j z hz hj2]
    exact norm_natCast_le_one p hnorm ((n + 1).choose j)

omit [Nontrivial R] in

lemma root_N_linear_unit_norm (n : ℕ) (z : R)
    (hroot : z ^ (n + 1) = 1) (hz : v z = 1) (hsep : v (1 - z) = 1) :
    v (z ^ n - 1) = 1 := by
  have hid : z * (z ^ n - 1) = 1 - z := by
    calc
      z * (z ^ n - 1) = z ^ n * z - z := by ring
      _ = 1 - z := by rw [← pow_succ, hroot]
  have hv := congrArg v hid
  simpa only [map_mul, hz, one_mul, hsep] using hv

theorem taylor_envelope_of_root_N
    (n p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r)
    (hval : padicValNat p (n + 1) = r) (z : R)
    (hnorm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat p m : ℝ)))
    (hroot : z ^ (n + 1) = 1) (hz : v z = 1) (hsep : v (1 - z) = 1) :
    TaylorEnvelope (shiftedTrinomial n z) v p r := by
  let : Fact p.Prime := ⟨hp⟩
  have hM : 0 < n + 1 := by omega
  have hM0 : n + 1 ≠ 0 := by omega
  have hdiv : p ^ r ∣ n + 1 := power_dvd_of_padicVal_eq p (n + 1) r hp hM hval
  have hpower : p ^ r ≤ n + 1 := Nat.le_of_dvd hM hdiv
  have hzero : v ((shiftedTrinomial n z).coeff 0) = Real.exp (-(r : ℝ)) := by
    rw [shiftedTrinomial_const_of_root_N n z hroot, map_mul, hsep, mul_one,
      hnorm (n + 1) hM0, hval]
  have hlinearEq : v ((shiftedTrinomial n z).coeff 1) = Real.exp (-(r : ℝ)) := by
    rw [shiftedTrinomial_coeff_one, map_mul, root_N_linear_unit_norm n z hroot hz hsep,
      mul_one, hnorm (n + 1) hM0, hval]
  apply taylor_envelope_of_scalar_valuations n p r hp hr z hnorm hz hpower
    hzero hlinearEq.le (fun j => padicValNat p j)
  · intro j hj hjr
    have h := choose_valuation_add p hp r (n + 1) j hM hdiv (by omega) hjr
    simpa only [hval] using h
  · intro k hk
    exact padicValNat.prime_pow k
  · intro k j hj hjbound
    exact padicVal_le_of_lt_power p j k hp (by omega) hjbound

theorem taylor_envelope_of_root_n
    (n p r : ℕ) (hn : 0 < n) (hp : p.Prime) (hr : 1 ≤ r)
    (hval : padicValNat p n = r) (z : R)
    (hnorm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat p m : ℝ)))
    (hroot : z ^ n = 1) (hz : v z = 1) (hsep : v (1 - z) = 1) :
    TaylorEnvelope (shiftedTrinomial n z) v p r := by
  let : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hdiv : p ^ r ∣ n := power_dvd_of_padicVal_eq p n r hp hn hval
  have hpower_n : p ^ r ≤ n := Nat.le_of_dvd hn hdiv
  have hpower : p ^ r ≤ n + 1 := by omega
  have hzero : v ((shiftedTrinomial n z).coeff 0) = Real.exp (-(r : ℝ)) := by
    rw [shiftedTrinomial_const_of_root_n n z hroot, map_mul, hsep, mul_one,
      hnorm n hn0, hval]
  have hlinear : v ((shiftedTrinomial n z).coeff 1) ≤ Real.exp (-(r : ℝ)) := by
    rw [shiftedTrinomial_linear_of_root_n n z hroot, map_zero]
    exact (Real.exp_pos _).le
  apply taylor_envelope_of_scalar_valuations n p r hp hr z hnorm hz hpower
    hzero hlinear (fun j => padicValNat p (j * (j - 1)))
  · intro j hj hjr
    have h := choose_successor_valuation_add p hp r n j hr hn hdiv hj (by omega)
    simpa only [hval] using h
  · intro k hk
    exact padicVal_prime_power_mul_pred p k hp hk
  · intro k j hj hjbound
    exact padicVal_mul_pred_le_of_lt_power p j k hp hj hjbound

end ValuedRing

end EventualIrreducibility.ActualEnvelope

open scoped BigOperators
open Polynomial

namespace EventualIrreducibility

lemma size_one_le_prod {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 1 ≤ u i) : 1 ≤ ∏ i ∈ s, u i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hi1 : 1 ≤ u i := hu i (Finset.mem_insert_self i s)
      have hs1 : 1 ≤ ∏ j ∈ s, u j :=
        ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
      rw [Finset.prod_insert hi]
      nlinarith

lemma size_one_lt_prod {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hne : s.Nonempty) (hu : ∀ i ∈ s, 1 < u i) :
    1 < ∏ i ∈ s, u i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert i s hi ih =>
      have hi1 : 1 < u i := hu i (Finset.mem_insert_self i s)
      have hs1 : 1 ≤ ∏ j ∈ s, u j :=
        size_one_le_prod s u (fun j hj =>
          (hu j (Finset.mem_insert_of_mem hj)).le)
      rw [Finset.prod_insert hi]
      nlinarith

lemma size_prod_le_const_pow_card {ι : Type*} (s : Finset ι)
    (u : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ B) :
    (∏ i ∈ s, u i) ≤ B ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiu := hu i (Finset.mem_insert_self i s)
      have htail := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
      have htail0 : 0 ≤ ∏ j ∈ s, u j :=
        Finset.prod_nonneg (fun j hj => (hu j (Finset.mem_insert_of_mem hj)).1)
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
      calc
        u i * (∏ j ∈ s, u j) ≤ B * B ^ s.card :=
          mul_le_mul hiu.2 htail htail0 hB
        _ = B ^ s.card * B := mul_comm _ _

lemma size_prod_lt_const_pow_card {ι : Type*} (s : Finset ι)
    (u : ι → ℝ) (B : ℝ) (hB : 0 < B) (hne : s.Nonempty)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i < B) :
    (∏ i ∈ s, u i) < B ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert i s hi ih =>
      have hiu := hu i (Finset.mem_insert_self i s)
      have htail : (∏ j ∈ s, u j) ≤ B ^ s.card :=
        size_prod_le_const_pow_card s u B hB.le
          (fun j hj =>
            ⟨(hu j (Finset.mem_insert_of_mem hj)).1,
              (hu j (Finset.mem_insert_of_mem hj)).2.le⟩)
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
      calc
        u i * (∏ j ∈ s, u j) ≤ u i * B ^ s.card :=
          mul_le_mul_of_nonneg_left htail hiu.1
        _ < B * B ^ s.card :=
          mul_lt_mul_of_pos_right hiu.2 (pow_pos hB _)
        _ = B ^ s.card * B := mul_comm _ _

lemma size_prod_pow {ι : Type*} (s : Finset ι)
    (u : ι → ℝ) (n : ℕ) :
    (∏ i ∈ s, u i) ^ n = ∏ i ∈ s, (u i) ^ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.prod_insert, hi, mul_pow, ih]

lemma size_norm_prod {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖∏ i ∈ s, u i‖ = ∏ i ∈ s, ‖u i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.prod_insert, hi, ih]

lemma constant_norm_eq_root_norm_product {d : ℕ} (g : ℂ[X])
    (alpha : Fin d → ℂ)
    (hprod : g = ∏ i, (X - C (alpha i) : ℂ[X])) :
    ‖g.coeff 0‖ = ∏ i, ‖alpha i‖ := by
  classical
  rw [Polynomial.coeff_zero_eq_eval_zero, hprod, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  rw [size_norm_prod]
  simp only [norm_neg]

lemma root_product_constant_size {n d : ℕ} (g : ℂ[X])
    (alpha : Fin d → ℂ) (hd : 0 < d)
    (hprod : g = ∏ i, (X - C (alpha i) : ℂ[X]))
    (hB : 0 < 2 * (n : ℝ) + 1)
    (hroot : ∀ i, 1 < ‖alpha i‖ ∧ ‖alpha i‖ ^ n < 2 * (n : ℝ) + 1) :
    1 < ‖g.coeff 0‖ ∧
      ‖g.coeff 0‖ ^ n < (2 * (n : ℝ) + 1) ^ d := by
  classical
  have hne : (Finset.univ : Finset (Fin d)).Nonempty :=
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  rw [constant_norm_eq_root_norm_product g alpha hprod]
  constructor
  · exact size_one_lt_prod Finset.univ (fun i => ‖alpha i‖) hne
      (fun i _ => (hroot i).1)
  · rw [size_prod_pow]
    simpa using size_prod_lt_const_pow_card Finset.univ
      (fun i => ‖alpha i‖ ^ n) (2 * (n : ℝ) + 1) hB hne
      (fun i _ => ⟨pow_nonneg (norm_nonneg _) _, (hroot i).2⟩)

lemma FactorSeries.constant_abs_size {n : ℕ} (s : FactorSeries n)
    (hn : 0 < n) :
    1 < |(s.factor.coeff 0 : ℝ)| ∧
      |(s.factor.coeff 0 : ℝ)| ^ n <
        (2 * (n : ℝ) + 1) ^ s.factor.natDegree := by
  classical
  obtain ⟨d, alpha, hd, hnonzero, hprod, hquot⟩ :=
    s.exists_root_product_identity hn
  have hdpos : 0 < d := by rw [hd]; exact s.degree_pos
  have hroot (i : Fin d) :
      (s.factor.map (Int.castRingHom ℂ)).eval (alpha i) = 0 := by
    rw [hprod, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hb (i : Fin d) :
      1 < ‖alpha i‖ ∧ ‖alpha i‖ ^ n < 2 * (n : ℝ) + 1 := by
    constructor
    · exact (RootGeometry.factor_root_annulus s hn (hroot i)).1
    · exact RootGeometry.norm_root_pow_lt hn
        (RootGeometry.root_of_mapped_factor s (hroot i))
  have hcast : ‖(s.factor.map (Int.castRingHom ℂ)).coeff 0‖ =
      |(s.factor.coeff 0 : ℝ)| := by
    simp only [Polynomial.coeff_map, Int.coe_castRingHom]
    exact Complex.norm_intCast (s.factor.coeff 0)
  have h := root_product_constant_size
    (s.factor.map (Int.castRingHom ℂ)) alpha hdpos hprod (by positivity) hb
  simpa only [hcast, hd] using h

end EventualIrreducibility

namespace EventualIrreducibility.Simplicity

open Polynomial

section Field

variable {K : Type*} [Field K]

theorem derivative_trinomial (n : ℕ) :
    (X ^ (n + 1) - C ((n : K) + 1) * X + C (n : K)).derivative =
      C ((n : K) + 1) * (X ^ n - 1) := by
  simp [Polynomial.derivative_mul]; ring

theorem bezout_identity_of_trinomial
    {n : ℕ} {P : K[X]}
    (hP : (X - 1) ^ 2 * P =
      X ^ (n + 1) - C ((n : K) + 1) * X + C (n : K)) :
    X * (X - 1) * P.derivative +
        ((2 : K[X]) * X - C ((n : K) + 1) * (X - 1)) * P =
      C ((n : K) * ((n : K) + 1)) := by
  have hderivative :
      (((X - 1) ^ 2 * P).derivative) =
        C ((n : K) + 1) * (X ^ n - 1) := by
    rw [hP, derivative_trinomial]
  have hproductDerivative :
      ((2 : K[X]) * (X - 1)) * P + (X - 1) ^ 2 * P.derivative =
        C ((n : K) + 1) * (X ^ n - 1) := by
    calc
      ((2 : K[X]) * (X - 1)) * P + (X - 1) ^ 2 * P.derivative =
          (((X - 1) ^ 2 * P).derivative) := by
        simp only [pow_two, Polynomial.derivative_mul, Polynomial.derivative_sub,
          Polynomial.derivative_X, Polynomial.derivative_one]
        ring
      _ = C ((n : K) + 1) * (X ^ n - 1) := hderivative
  have hX : (X - 1 : K[X]) ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun Q : K[X] => Q.coeff 1) hzero
    norm_num [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one] at hcoeff
  apply mul_left_cancel₀ hX
  calc
    (X - 1) *
        (X * (X - 1) * P.derivative +
          ((2 : K[X]) * X - C ((n : K) + 1) * (X - 1)) * P) =
        X * (((2 : K[X]) * (X - 1)) * P + (X - 1) ^ 2 * P.derivative) -
          C ((n : K) + 1) * ((X - 1) ^ 2 * P) := by ring
    _ = X * (C ((n : K) + 1) * (X ^ n - 1)) -
          C ((n : K) + 1) *
            (X ^ (n + 1) - C ((n : K) + 1) * X + C (n : K)) := by
      rw [hproductDerivative, hP]
    _ = (X - 1) * C ((n : K) * ((n : K) + 1)) := by
      simp only [pow_succ, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_1]
      ring

theorem separable_of_trinomial_of_nonzero_constant
    {n : ℕ} {P : K[X]}
    (hP : (X - 1) ^ 2 * P =
      X ^ (n + 1) - C ((n : K) + 1) * X + C (n : K))
    (hc : (n : K) * ((n : K) + 1) ≠ 0) :
    P.Separable := by
  let A : K[X] := X * (X - 1)
  let B : K[X] := (2 : K[X]) * X - C ((n : K) + 1) * (X - 1)
  let c : K := (n : K) * ((n : K) + 1)
  have hc' : c ≠ 0 := hc
  have hidentity : A * P.derivative + B * P = C c := by
    simpa only [A, B, c] using bezout_identity_of_trinomial hP
  rw [Polynomial.separable_def']
  refine ⟨C c⁻¹ * B, C c⁻¹ * A, ?_⟩
  calc
    C c⁻¹ * B * P + C c⁻¹ * A * P.derivative =
        C c⁻¹ * (A * P.derivative + B * P) := by ring
    _ = C c⁻¹ * C c := by rw [hidentity]
    _ = C (c⁻¹ * c) := Polynomial.C_mul.symm
    _ = 1 := by simp [hc']

theorem root_derivative_identity_of_trinomial
    {n : ℕ} {P : K[X]}
    (hP : (X - 1) ^ 2 * P =
      X ^ (n + 1) - C ((n : K) + 1) * X + C (n : K))
    {z : K} (hz : P.eval z = 0) :
    z * (z - 1) * P.derivative.eval z = (n : K) * ((n : K) + 1) := by
  have h := congrArg (fun Q : K[X] => Q.eval z)
    (bezout_identity_of_trinomial hP)
  simpa [hz] using h

end Field

section CharZero

variable {K : Type*} [Field K] [CharZero K]

theorem nat_mul_succ_ne_zero {n : ℕ} (hn : 0 < n) :
    (n : K) * ((n : K) + 1) ≠ 0 := by
  have hnK : (n : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hNK : ((n : K) + 1) ≠ 0 := by
    have hsucc : ((n + 1 : ℕ) : K) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    simpa only [Nat.cast_add, Nat.cast_one] using hsucc
  exact mul_ne_zero hnK hNK

theorem separable_of_trinomial
    {n : ℕ} {P : K[X]} (hn : 0 < n)
    (hP : (X - 1) ^ 2 * P =
      X ^ (n + 1) - C ((n : K) + 1) * X + C (n : K)) :
    P.Separable :=
  separable_of_trinomial_of_nonzero_constant hP (nat_mul_succ_ne_zero hn)

omit [CharZero K] in
theorem mapped_trinomial_from_integer
    {n : ℕ} {P : ℤ[X]}
    (hP : (X - 1) ^ 2 * P =
      X ^ (n + 1) - C ((n + 1 : ℕ) : ℤ) * X + C (n : ℤ)) :
    (X - 1) ^ 2 * P.map (Int.castRingHom K) =
      X ^ (n + 1) - C ((n : K) + 1) * X + C (n : K) := by
  have h := congrArg (Polynomial.map (Int.castRingHom K)) hP
  simpa using h

theorem mapped_family_separable
    (family : ℕ → ℤ[X])
    (hidentity : ∀ n : ℕ, (X - 1) ^ 2 * family n =
      X ^ (n + 1) - C ((n + 1 : ℕ) : ℤ) * X + C (n : ℤ))
    {n : ℕ} (hn : 0 < n) :
    ((family n).map (Int.castRingHom K)).Separable :=
  separable_of_trinomial hn (mapped_trinomial_from_integer (hidentity n))

theorem mapped_divisor_separable
    (family : ℕ → ℤ[X])
    (hidentity : ∀ n : ℕ, (X - 1) ^ 2 * family n =
      X ^ (n + 1) - C ((n + 1 : ℕ) : ℤ) * X + C (n : ℤ))
    {n : ℕ} (hn : 0 < n) {g : ℤ[X]} (hdiv : g ∣ family n) :
    (g.map (Int.castRingHom K)).Separable := by
  apply (mapped_family_separable family hidentity hn).of_dvd
  rcases hdiv with ⟨h, hfactor⟩
  refine ⟨h.map (Int.castRingHom K), ?_⟩
  simpa using congrArg (Polynomial.map (Int.castRingHom K)) hfactor

end CharZero

end EventualIrreducibility.Simplicity

namespace EventualIrreducibility

lemma FactorSeries.separable_map {n : ℕ} (s : FactorSeries n)
    (K : Type*) [Field K] [CharZero K] (hn : 0 < n) :
    (s.factor.map (Int.castRingHom K)).Separable :=
  Simplicity.mapped_divisor_separable fInt trinomial_identity hn s.divides

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility

end EventualIrreducibility

namespace EventualIrreducibility.Angular

open Set

noncomputable def sectorInterval (a c : ℝ) : Set ℝ :=
  Ioo (c / a) (min ((c + Real.pi / 2) / a) ((c + Real.pi) / (a + 1)))

end EventualIrreducibility.Angular

open Polynomial
open scoped BigOperators

namespace EventualIrreducibility.FiniteFieldDescent

theorem derivative_eq_zero_of_splits_multiplicity_dvd
    {L : Type*} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (Q : L[X]) (hs : Q.Splits)
    (hm : ∀ a : L, p ∣ Q.rootMultiplicity a) :
    Q.derivative = 0 := by
  classical
  let T : L[X] := ∏ a ∈ Q.roots.toFinset,
    (X - C a) ^ (Q.rootMultiplicity a / p)
  have hprod :
      (∏ a ∈ Q.roots.toFinset, (X - C a) ^ Q.rootMultiplicity a) = T ^ p := by
    dsimp [T]
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro a ha
    rw [← pow_mul, Nat.div_mul_cancel (hm a)]
  have hQ : Q = C Q.leadingCoeff * T ^ p := by
    calc
      Q = C Q.leadingCoeff * (Q.roots.map (X - C ·)).prod := hs.eq_prod_roots
      _ = C Q.leadingCoeff *
          (∏ a ∈ Q.roots.toFinset, (X - C a) ^ Q.rootMultiplicity a) := by
        rw [Polynomial.prod_multiset_root_eq_finset_root]
      _ = C Q.leadingCoeff * T ^ p := by rw [hprod]
  calc
    Q.derivative = (C Q.leadingCoeff * T ^ p).derivative := congrArg derivative hQ
    _ = 0 := by simp [Polynomial.derivative_mul, Polynomial.derivative_pow]

theorem exists_pow_of_derivative_eq_zero
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectRing K p] (Q : K[X]) (hQ : Q.derivative = 0) :
    ∃ H : K[X], Q = H ^ p := by
  refine ⟨(Polynomial.contract p Q).map (frobeniusEquiv K p).symm, ?_⟩
  calc
    Q = Polynomial.expand K p (Polynomial.contract p Q) :=
      (Polynomial.expand_contract p hQ (Fact.out : p.Prime).ne_zero).symm
    _ = _ := polynomial_expand_eq K p _

theorem exists_pow_of_map_splits_multiplicity_dvd
    {K L : Type*} [Field K] [Field L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    [PerfectRing K p] (i : K →+* L) (Q : K[X])
    (hs : (Q.map i).Splits)
    (hm : ∀ a : L, p ∣ (Q.map i).rootMultiplicity a) :
    ∃ H : K[X], Q = H ^ p := by
  have hd : (Q.map i).derivative = 0 :=
    derivative_eq_zero_of_splits_multiplicity_dvd p (Q.map i) hs hm
  have hd' : Q.derivative = 0 := by
    apply Polynomial.map_injective i i.injective
    simpa only [Polynomial.derivative_map, Polynomial.map_zero] using hd
  exact exists_pow_of_derivative_eq_zero p Q hd'

theorem exists_reduction_shape_of_root_multiplicities
    {K L : Type*} [Field K] [Field L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    [PerfectRing K p] (i : K →+* L)
    (G : K[X]) (hG : G ≠ 0)
    (hs : (G.map i).Splits)
    (hzero : (G.map i).rootMultiplicity 0 ≤ 1)
    (hother : ∀ a : L, a ≠ 0 → a ≠ 1 →
      p ∣ (G.map i).rootMultiplicity a) :
    ∃ ε s : ℕ, ∃ H : K[X], ε ≤ 1 ∧
      G = X ^ ε * (X - 1) ^ s * H ^ p := by
  classical
  obtain ⟨B, hGB, hB0⟩ :=
    G.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hG 0
  have hB : B ≠ 0 := by
    intro h
    apply hG
    simpa [h] using hGB
  obtain ⟨Q, hBQ, hQ1⟩ :=
    B.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hB 1
  let ε := G.rootMultiplicity 0
  let s := B.rootMultiplicity 1
  have hshape : G = X ^ ε * (X - 1) ^ s * Q := by
    rw [hGB, hBQ]
    simp only [C_0, sub_zero, C_1, ε, s, mul_assoc]
  have hQ : Q ≠ 0 := by
    intro h
    apply hG
    simpa [h] using hshape
  have hBnot0 : ¬ B.IsRoot 0 := by
    intro h
    exact hB0 (Polynomial.dvd_iff_isRoot.mpr h)
  have hQnot0 : ¬ Q.IsRoot 0 := by
    intro h
    apply hBnot0
    change B.eval 0 = 0
    rw [hBQ, Polynomial.eval_mul]
    simp [h.eq_zero]
  have hQnot1 : ¬ Q.IsRoot 1 := by
    intro h
    exact hQ1 (Polynomial.dvd_iff_isRoot.mpr h)
  have hQmap0 : (Q.map i).rootMultiplicity 0 = 0 := by
    simpa only [map_zero] using
      (Polynomial.eq_rootMultiplicity_map (p := Q) i.injective (0 : K)).symm.trans
        (Polynomial.rootMultiplicity_eq_zero hQnot0)
  have hQmap1 : (Q.map i).rootMultiplicity 1 = 0 := by
    simpa only [map_one] using
      (Polynomial.eq_rootMultiplicity_map (p := Q) i.injective (1 : K)).symm.trans
        (Polynomial.rootMultiplicity_eq_zero hQnot1)
  have hGmap : G.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hG
  have hmap : G.map i =
      ((X : L[X]) ^ ε * (X - 1) ^ s) * Q.map i := by
    rw [hshape]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_one]
  have hQdiv : Q.map i ∣ G.map i := by
    refine ⟨(X : L[X]) ^ ε * (X - 1) ^ s, ?_⟩
    rw [hmap, mul_comm]
  have hQs : (Q.map i).Splits := hs.of_dvd hGmap hQdiv
  have hQmult : ∀ a : L, p ∣ (Q.map i).rootMultiplicity a := by
    intro a
    by_cases ha0 : a = 0
    · simpa only [ha0, hQmap0] using (dvd_zero p)
    by_cases ha1 : a = 1
    · simpa only [ha1, hQmap1] using (dvd_zero p)
    have hA : ¬ (((X : L[X]) ^ ε * (X - 1) ^ s).IsRoot a) := by
      change _ ≠ 0
      simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_one] using
        mul_ne_zero (pow_ne_zero _ ha0) (pow_ne_zero _ (sub_ne_zero.mpr ha1))
    have hm : (G.map i).rootMultiplicity a = (Q.map i).rootMultiplicity a := by
      rw [hmap, Polynomial.rootMultiplicity_mul (hmap ▸ hGmap),
        Polynomial.rootMultiplicity_eq_zero hA, zero_add]
    exact hm ▸ hother a ha0 ha1
  obtain ⟨H, hH⟩ :=
    exists_pow_of_map_splits_multiplicity_dvd p i Q hQs hQmult
  refine ⟨ε, s, H, ?_, ?_⟩
  · have he : ε = (G.map i).rootMultiplicity 0 := by
      simpa only [ε, map_zero] using
        Polynomial.eq_rootMultiplicity_map (p := G) i.injective (0 : K)
    rw [he]
    exact hzero
  · rw [hshape, hH]

end EventualIrreducibility.FiniteFieldDescent

open scoped BigOperators
open Polynomial

namespace EventualIrreducibility.DiscriminantBridge

lemma norm_finset_prod {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖∏ i ∈ s, u i‖ = ∏ i ∈ s, ‖u i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.prod_insert, hi, ih]

lemma resultant_root_product_eval {d : ℕ} (alpha : Fin d → ℂ)
    (G Q : ℂ[X]) (hprod : G = ∏ i, (X - C (alpha i) : ℂ[X]))
    (m : ℕ) (hm : Q.natDegree ≤ m) :
    G.resultant Q G.natDegree m = ∏ i, Q.eval (alpha i) := by
  classical
  subst G
  rw [Polynomial.resultant_prod_left Finset.univ
    (fun i => (X - C (alpha i) : ℂ[X])) Q m (by simp) hm]
  apply Finset.prod_congr rfl
  intro i hi
  simpa using Polynomial.resultant_X_sub_C_left Q m (alpha i) hm

lemma eval_derivative_root_product {d : ℕ} (alpha : Fin d → ℂ)
    (G : ℂ[X]) (hprod : G = ∏ i, (X - C (alpha i) : ℂ[X]))
    (i : Fin d) :
    G.derivative.eval (alpha i) =
      Finset.prod ((Finset.univ : Finset (Fin d)).erase i)
        (fun j : Fin d => alpha i - alpha j) := by
  classical
  have hfac : G = (X - C (alpha i)) *
      (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
        (X - C (alpha j) : ℂ[X])) := by
    rw [hprod]
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [hfac, Polynomial.derivative_mul]
  simp [Polynomial.eval_prod]

lemma root_product_injective_of_separable {d : ℕ} (alpha : Fin d → ℂ)
    (G : ℂ[X]) (hprod : G = ∏ i, (X - C (alpha i) : ℂ[X]))
    (hsep : G.Separable) : Function.Injective alpha := by
  rw [hprod] at hsep
  exact hsep.injective_of_prod_X_sub_C

lemma discr_abs_eq_ordered_root_norm_prod {d : ℕ}
    (g : ℤ[X]) (hg : g.Monic) (hgpos : 0 < g.natDegree)
    (alpha : Fin d → ℂ)
    (hprod : g.map (Int.castRingHom ℂ) =
      ∏ i, (X - C (alpha i) : ℂ[X])) :
    |(g.discr : ℝ)| =
      ∏ i, ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
        ‖alpha i - alpha j‖ := by
  classical
  let G := g.map (Int.castRingHom ℂ)
  have hGdeg : G.natDegree = g.natDegree := hg.natDegree_map _
  have hderivdeg : G.derivative.natDegree ≤ g.natDegree - 1 := by
    simpa only [hGdeg] using Polynomial.natDegree_derivative_le G
  have hresmap :
      G.resultant G.derivative g.natDegree (g.natDegree - 1) =
      ((g.resultant g.derivative g.natDegree (g.natDegree - 1) : ℤ) : ℂ) := by
    dsimp only [G]
    rw [Polynomial.derivative_map]
    exact Polynomial.resultant_map_map g g.derivative g.natDegree
      (g.natDegree - 1) (Int.castRingHom ℂ)
  have hresdisc :
      g.resultant g.derivative g.natDegree (g.natDegree - 1) =
      (-1) ^ (g.natDegree * (g.natDegree - 1) / 2) * g.discr := by
    simpa only [hg.leadingCoeff, mul_one] using
      (Polynomial.resultant_deriv
        (Polynomial.natDegree_pos_iff_degree_pos.mp hgpos))
  have hnormres :
      ‖G.resultant G.derivative g.natDegree (g.natDegree - 1)‖ =
      |(g.discr : ℝ)| := by
    rw [hresmap, hresdisc]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact Complex.norm_intCast g.discr
  have heval :
      G.resultant G.derivative g.natDegree (g.natDegree - 1) =
      ∏ i, G.derivative.eval (alpha i) := by
    simpa only [hGdeg] using
      resultant_root_product_eval alpha G G.derivative hprod
        (g.natDegree - 1) hderivdeg
  calc
    |(g.discr : ℝ)| =
        ‖G.resultant G.derivative g.natDegree (g.natDegree - 1)‖ := hnormres.symm
    _ = ‖∏ i, G.derivative.eval (alpha i)‖ := congrArg (fun z : ℂ => ‖z‖) heval
    _ = ∏ i, ‖G.derivative.eval (alpha i)‖ := norm_finset_prod _ _
    _ = ∏ i, ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
        ‖alpha i - alpha j‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [eval_derivative_root_product alpha G hprod i, norm_finset_prod]

lemma log_finset_prod_pos {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 < u i) :
    Real.log (∏ i ∈ s, u i) = ∑ i ∈ s, Real.log (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hi0 := hu i (Finset.mem_insert_self i s)
      have ht : ∀ j ∈ s, 0 < u j := fun j hj => hu j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        Real.log_mul (ne_of_gt hi0) (ne_of_gt (Finset.prod_pos ht)), ih ht]

lemma log_discr_eq_ordered_root_log_sum {d : ℕ}
    (g : ℤ[X]) (hg : g.Monic) (hgpos : 0 < g.natDegree)
    (alpha : Fin d → ℂ)
    (hprod : g.map (Int.castRingHom ℂ) =
      ∏ i, (X - C (alpha i) : ℂ[X]))
    (hinj : Function.Injective alpha) :
    Real.log |(g.discr : ℝ)| =
      ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i,
        Real.log ‖alpha i - alpha j‖ := by
  classical
  have hpair (i : Fin d) (j : Fin d)
      (hj : j ∈ (Finset.univ : Finset (Fin d)).erase i) :
      0 < ‖alpha i - alpha j‖ := by
    apply norm_pos_iff.mpr
    intro hz
    exact (Finset.mem_erase.mp hj).1 (hinj (sub_eq_zero.mp hz)).symm
  rw [discr_abs_eq_ordered_root_norm_prod g hg hgpos alpha hprod,
    log_finset_prod_pos _ _ (fun i _ => Finset.prod_pos (hpair i))]
  apply Finset.sum_congr rfl
  intro i hi
  exact log_finset_prod_pos _ _ (hpair i)

end EventualIrreducibility.DiscriminantBridge

open Polynomial

namespace EventualIrreducibility.ResidueCluster

section Ambient

variable {R k : Type*} [CommRing R] [IsDomain R] [Field k]
variable {v : AbsoluteValue R ℝ}

lemma rootMultiplicity_zero_eq_of_monic_minGaussIndex
    (P : R[X]) (hP : P.Monic) (red : R →+* k)
    (hintegral : ∀ a : R, v a ≤ 1)
    (hred : ∀ a, red a ≠ 0 ↔ v a = 1)
    (t : ℕ) (ht : IsMinGaussIndex P v 1 t) :
    (P.map red).rootMultiplicity 0 = t := by
  obtain ⟨hdiv, hnotdiv⟩ :=
    monic_minGaussIndex_reduction_order P hP red t
      (fun j => hintegral (P.coeff j)) hred ht
  have hPbar : P.map red ≠ 0 := (hP.map red).ne_zero
  have hlo : t ≤ (P.map red).rootMultiplicity 0 := by
    apply (Polynomial.le_rootMultiplicity_iff hPbar).mpr
    simpa only [Polynomial.C_0, sub_zero] using hdiv
  have hhi : ¬ t + 1 ≤ (P.map red).rootMultiplicity 0 := by
    intro h
    apply hnotdiv
    simpa only [Polynomial.C_0, sub_zero] using
      (Polynomial.le_rootMultiplicity_iff hPbar).mp h
  omega

theorem rootMultiplicity_dvd_of_normalized_lift
    (red : R →+* k)
    (hna : IsNonarchimedean v)
    (hintegral : ∀ a : R, v a ≤ 1)
    (hdiscrete : ∀ a : R, a ≠ 0 → ∃ j : ℤ, v a = Real.exp (-(j : ℝ)))
    (hred : ∀ a, red a ≠ 0 ↔ v a = 1)
    (n p r : ℕ) (hn : 0 < n) (hp : p.Prime) (hr : 1 ≤ r)
    (hnorm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat p m : ℝ)))
    (g h : R[X]) (hg : g.Monic)
    (hfactor : (X - 1) ^ 2 * (g * h) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : R) * X + C (n : R))
    (z : R) (hz : v z = 1) (hsep : v (1 - z) = 1)
    (hcase : (padicValNat p n = r ∧ z ^ n = 1) ∨
      (padicValNat p (n + 1) = r ∧ z ^ (n + 1) = 1)) :
    p ∣ (g.map red).rootMultiplicity (red z) := by
  let G : R[X] := g.comp (X + C z)
  let H : R[X] := (((X - 1) ^ 2) * h).comp (X + C z)
  have hGmonic : G.Monic := hg.comp_X_add_C z
  have hGH : G * H = shiftedTrinomial n z := by
    calc
      G * H = ((X - 1) ^ 2 * (g * h)).comp (X + C z) := by
        simp only [G, H, Polynomial.mul_comp]
        ring
      _ = shiftedTrinomial n z := by
        rw [hfactor, ← shiftedTrinomial_eq_comp]
  have henv : ActualEnvelope.TaylorEnvelope (shiftedTrinomial n z) v p r := by
    rcases hcase with ⟨hval, hroot⟩ | ⟨hval, hroot⟩
    · exact ActualEnvelope.taylor_envelope_of_root_n n p r hn hp hr hval z
        hnorm hroot hz hsep
    · exact ActualEnvelope.taylor_envelope_of_root_N n p r hp hr hval z
        hnorm hroot hz hsep
  have henvGH : ActualEnvelope.TaylorEnvelope (G * H) v p r := by
    rw [hGH]
    exact henv
  have hprod : G * H ≠ 0 := by
    intro heq
    have hzero : (0 : ℝ) = Real.exp (-(r : ℝ)) := by
      simpa only [heq, Polynomial.coeff_zero, map_zero] using henvGH.zero_eq
    exact (Real.exp_ne_zero _ hzero.symm).elim
  have hH : H ≠ 0 := by
    intro heq
    apply hprod
    simp [heq]
  obtain ⟨t, ht⟩ := G.exists_min_eq_gaussNorm v (show (0 : ℝ) ≤ 1 by norm_num)
  have hpt : p ∣ t :=
    FirstFace.minGaussIndex_one_dvd_of_envelope hna G H hGmonic.ne_zero hH
      p r hp.two_le hr hdiscrete henvGH.zero_eq henvGH.vertex_eq
      henvGH.band_le henvGH.tail_le t ht
  have htRoot : (G.map red).rootMultiplicity 0 = t :=
    rootMultiplicity_zero_eq_of_monic_minGaussIndex G hGmonic red
      hintegral hred t ht
  have hmapShift : G.map red = (g.map red).comp (X + C (red z)) := by
    simp only [G, Polynomial.map_comp, Polynomial.map_add,
      Polynomial.map_X, Polynomial.map_C]
  have hrootShift : (g.map red).rootMultiplicity (red z) =
      (G.map red).rootMultiplicity 0 := by
    rw [Polynomial.rootMultiplicity_eq_rootMultiplicity, hmapShift]
  rw [hrootShift, htRoot]
  exact hpt

theorem integer_factor_cluster_multiplicity_dvd
    (red : R →+* k)
    (hna : IsNonarchimedean v)
    (hintegral : ∀ a : R, v a ≤ 1)
    (hdiscrete : ∀ a : R, a ≠ 0 → ∃ j : ℤ, v a = Real.exp (-(j : ℝ)))
    (hred : ∀ a, red a ≠ 0 ↔ v a = 1)
    (n p r : ℕ) (hn : 0 < n) (hp : p.Prime) (hr : 1 ≤ r)
    (hnorm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat p m : ℝ)))
    (g h : ℤ[X]) (hg : g.Monic) (hfactor : g * h = fInt n)
    (z : R) (hz : v z = 1) (hsep : v (1 - z) = 1)
    (hcase : (padicValNat p n = r ∧ z ^ n = 1) ∨
      (padicValNat p (n + 1) = r ∧ z ^ (n + 1) = 1)) :
    p ∣ (g.map (Int.castRingHom k)).rootMultiplicity (red z) := by
  have hzfactor : (X - 1) ^ 2 * (g * h) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : ℤ) * X + C (n : ℤ) := by
    rw [hfactor]
    exact trinomial_identity n
  have hRfactor : (X - 1) ^ 2 *
      (g.map (Int.castRingHom R) * h.map (Int.castRingHom R)) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : R) * X + C (n : R) := by
    have heq := congrArg (Polynomial.map (Int.castRingHom R)) hzfactor
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C,
      map_natCast, Polynomial.map_natCast] using heq
  have hlocal := rootMultiplicity_dvd_of_normalized_lift red hna hintegral
    hdiscrete hred n p r hn hp hr hnorm
    (g.map (Int.castRingHom R)) (h.map (Int.castRingHom R))
    (hg.map (Int.castRingHom R)) hRfactor z hz hsep hcase
  have hmaps : (g.map (Int.castRingHom R)).map red =
      g.map (Int.castRingHom k) := by
    ext j
    simp only [Polynomial.coeff_map, Int.coe_castRingHom, map_intCast]
  simpa only [hmaps] using hlocal

end Ambient

end EventualIrreducibility.ResidueCluster

open Polynomial

namespace EventualIrreducibility.LocalShapeAssembly

structure NormalizedIntegralRootLift (p M : ℕ) (L : Type*) [Field L] (a : L) where
  R : Type
  [commRing : CommRing R]
  [isDomain : IsDomain R]
  v : AbsoluteValue R ℝ
  red : R →+* L
  nonarchimedean : IsNonarchimedean v
  integral : ∀ x : R, v x ≤ 1
  discrete : ∀ x : R, x ≠ 0 → ∃ j : ℤ, v x = Real.exp (-(j : ℝ))
  residue_unit : ∀ x : R, red x ≠ 0 ↔ v x = 1
  nat_norm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat p m : ℝ))
  z : R
  reduces : red z = a
  root : z ^ M = 1
  unit : v z = 1
  separated : v (1 - z) = 1

attribute [instance] NormalizedIntegralRootLift.commRing
attribute [instance] NormalizedIntegralRootLift.isDomain

def UnramifiedRootLiftInput : Prop :=
  ∀ (p M : ℕ), p.Prime → 0 < M → p ∣ M →
    ∀ (L : Type) [Field L] [CharP L p] (a : L),
      a ≠ 0 → a ≠ 1 → a ^ M = 1 →
        Nonempty (NormalizedIntegralRootLift p M L a)

section CoefficientsAndRoots

variable {L : Type*} [Field L]

theorem factor_rootMultiplicity_zero_le_one
    (n : ℕ) (hn : 2 ≤ n) (g h : ℤ[X]) (hg : g.Monic)
    (hfactor : g * h = fInt n) :
    (g.map (Int.castRingHom L)).rootMultiplicity 0 ≤ 1 := by
  by_contra hbad
  have htwo : 2 ≤ (g.map (Int.castRingHom L)).rootMultiplicity 0 := by omega
  have hgbar : g.map (Int.castRingHom L) ≠ 0 :=
    (hg.map (Int.castRingHom L)).ne_zero
  have hXg : (X : L[X]) ^ 2 ∣ g.map (Int.castRingHom L) := by
    simpa only [Polynomial.C_0, sub_zero] using
      (Polynomial.le_rootMultiplicity_iff hgbar).mp htwo
  have hgf : g.map (Int.castRingHom L) ∣ (fInt n).map (Int.castRingHom L) := by
    rw [← hfactor, Polynomial.map_mul]
    exact dvd_mul_right _ _
  have hXf := hXg.trans hgf
  have hc0 := Polynomial.X_pow_dvd_iff.mp hXf 0 (by omega)
  have hc1 := Polynomial.X_pow_dvd_iff.mp hXf 1 (by omega)
  have hn0 : (n : L) = 0 := by
    simpa [Polynomial.coeff_map, coeff_fInt, show 0 < n by omega] using hc0
  have hn1 : ((n - 1 : ℕ) : L) = 0 := by
    simpa [Polynomial.coeff_map, coeff_fInt, show 1 < n by omega] using hc1
  have hnat : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hcast : ((n - 1 : ℕ) : L) + 1 = (n : L) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun m : ℕ => (m : L)) hnat
  rw [hn0, hn1, zero_add] at hcast
  exact one_ne_zero hcast

theorem trinomial_eq_zero_of_factor_root
    (n : ℕ) (g h : ℤ[X]) (hfactor : g * h = fInt n)
    (a : L) (ha : (g.map (Int.castRingHom L)).IsRoot a) :
    a ^ (n + 1) - ((n : L) + 1) * a + (n : L) = 0 := by
  have hf : ((fInt n).map (Int.castRingHom L)).eval a = 0 := by
    rw [← hfactor, Polynomial.map_mul, Polynomial.eval_mul, ha.eq_zero, zero_mul]
  have hf' : (fInt n).eval₂ (Int.castRingHom L) a = 0 := by
    simpa only [Polynomial.eval_map] using hf
  have heq := congrArg (fun P : ℤ[X] => P.eval₂ (Int.castRingHom L) a)
    (trinomial_identity n)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_one, hf', mul_zero,
    Polynomial.eval₂_add, Polynomial.eval₂_C, map_natCast,
    Nat.cast_add, Nat.cast_one] at heq
  simpa only [map_add, map_natCast, map_one, Polynomial.eval₂_natCast] using heq.symm

theorem factor_root_power_of_dvd_n
    (p : ℕ) [CharP L p] (n : ℕ) (hpn : p ∣ n)
    (g h : ℤ[X]) (hfactor : g * h = fInt n)
    (a : L) (ha0 : a ≠ 0) (ha : (g.map (Int.castRingHom L)).IsRoot a) :
    a ^ n = 1 := by
  have hncast : (n : L) = 0 := (CharP.cast_eq_zero_iff L p n).mpr hpn
  have ht := trinomial_eq_zero_of_factor_root n g h hfactor a ha
  have hproduct : a * (a ^ n - 1) = 0 := by
    calc
      a * (a ^ n - 1) = a ^ (n + 1) - a := by rw [pow_succ]; ring
      _ = 0 := by simpa only [hncast, zero_add, one_mul, add_zero] using ht
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left ha0)

theorem factor_root_power_of_dvd_N
    (p : ℕ) [CharP L p] (n : ℕ) (hpN : p ∣ n + 1)
    (g h : ℤ[X]) (hfactor : g * h = fInt n)
    (a : L) (ha : (g.map (Int.castRingHom L)).IsRoot a) :
    a ^ (n + 1) = 1 := by
  have hNcast : (n : L) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (CharP.cast_eq_zero_iff L p (n + 1)).mpr hpN
  have hncast : (n : L) = -1 := eq_neg_of_add_eq_zero_left hNcast
  have ht := trinomial_eq_zero_of_factor_root n g h hfactor a ha
  have hsub : a ^ (n + 1) - 1 = 0 := by
    simpa only [hNcast, hncast, neg_add_cancel, zero_mul, sub_zero, sub_eq_add_neg, neg_zero, add_zero] using ht
  exact sub_eq_zero.mp hsub

end CoefficientsAndRoots

theorem factor_nonexceptional_multiplicity_dvd
    (hlift : UnramifiedRootLiftInput)
    (p : ℕ) (hp : p.Prime) (L : Type) [Field L] [CharP L p]
    (n : ℕ) (hn : 2 ≤ n) (hpd : p ∣ n * (n + 1))
    (g h : ℤ[X]) (hg : g.Monic) (hfactor : g * h = fInt n)
    (a : L) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    p ∣ (g.map (Int.castRingHom L)).rootMultiplicity a := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases ha : (g.map (Int.castRingHom L)).IsRoot a
  · rcases hp.dvd_mul.mp hpd with hpn | hpN
    · have hnpos : 0 < n := by omega
      have hroot := factor_root_power_of_dvd_n p n hpn g h hfactor a ha0 ha
      obtain ⟨D⟩ := hlift p n hp hnpos hpn L a ha0 ha1 hroot
      have hr : 1 ≤ padicValNat p n := by
        apply (padicValNat_dvd_iff_le (p := p) (a := n) (n := 1)
          (Nat.ne_of_gt hnpos)).mp
        simpa only [pow_one] using hpn
      have hd := ResidueCluster.integer_factor_cluster_multiplicity_dvd
        (v := D.v) D.red D.nonarchimedean D.integral D.discrete D.residue_unit
        n p (padicValNat p n) hnpos hp hr D.nat_norm
        g h hg hfactor D.z D.unit D.separated (Or.inl ⟨rfl, D.root⟩)
      simpa only [D.reduces] using hd
    · have hnpos : 0 < n := by omega
      have hNpos : 0 < n + 1 := by omega
      have hroot := factor_root_power_of_dvd_N p n hpN g h hfactor a ha
      obtain ⟨D⟩ := hlift p (n + 1) hp hNpos hpN L a ha0 ha1 hroot
      have hr : 1 ≤ padicValNat p (n + 1) := by
        apply (padicValNat_dvd_iff_le (p := p) (a := n + 1) (n := 1)
          (Nat.ne_of_gt hNpos)).mp
        simpa only [pow_one] using hpN
      have hd := ResidueCluster.integer_factor_cluster_multiplicity_dvd
        (v := D.v) D.red D.nonarchimedean D.integral D.discrete D.residue_unit
        n p (padicValNat p (n + 1)) hnpos hp hr D.nat_norm
        g h hg hfactor D.z D.unit D.separated (Or.inr ⟨rfl, D.root⟩)
      simpa only [D.reduces] using hd
  · rw [Polynomial.rootMultiplicity_eq_zero ha]
    exact dvd_zero p

theorem reductionShapeInput_of_unramifiedRootLiftInput
    (hlift : UnramifiedRootLiftInput) : ReductionShapeInput := by
  intro n hn s p hp hpd
  let : Fact p.Prime := ⟨hp⟩
  let K := ZMod p
  let L := AlgebraicClosure K
  let i : K →+* L := algebraMap K L
  let G : K[X] := s.factor.map (Int.castRingHom K)
  obtain ⟨h, hfactor⟩ := s.divides
  have hfactor' : s.factor * h = fInt n := hfactor.symm
  have hmaps : G.map i = s.factor.map (Int.castRingHom L) := by
    ext j
    simp only [G, Polynomial.coeff_map, Int.coe_castRingHom, map_intCast]
  apply FiniteFieldDescent.exists_reduction_shape_of_root_multiplicities
    p i G (s.monic.map (Int.castRingHom K)).ne_zero
      (IsAlgClosed.splits (G.map i))
  · rw [hmaps]
    exact factor_rootMultiplicity_zero_le_one n hn s.factor h s.monic hfactor'
  · intro a ha0 ha1
    rw [hmaps]
    exact factor_nonexceptional_multiplicity_dvd hlift p hp L n hn hpd
      s.factor h s.monic hfactor' a ha0 ha1

end EventualIrreducibility.LocalShapeAssembly

namespace EventualIrreducibility.SectorReconstruction

open Real

theorem sine_equations_of_polar_equations
    {n : ℕ} {rho theta phi : ℝ} (hrho : 0 < rho)
    (hre : rho ^ (n + 1) * cos (phi + theta) =
      ((n : ℝ) + 1) * rho * cos theta - (n : ℝ))
    (him : rho ^ (n + 1) * sin (phi + theta) =
      ((n : ℝ) + 1) * rho * sin theta) :
    rho ^ (n + 1) * sin phi = (n : ℝ) * sin theta ∧
      rho ^ n * sin (phi + theta) = ((n : ℝ) + 1) * sin theta := by
  have htrig :
      sin (phi + theta) * cos theta - cos (phi + theta) * sin theta =
        sin phi := by
    simpa using (Real.sin_sub (phi + theta) theta).symm
  have hfirst :
      rho ^ (n + 1) *
          (sin (phi + theta) * cos theta - cos (phi + theta) * sin theta) =
        (n : ℝ) * sin theta := by
    linear_combination cos theta * him - sin theta * hre
  have hsecond :
      rho * (rho ^ n * sin (phi + theta)) =
        rho * (((n : ℝ) + 1) * sin theta) := by
    calc
      _ = rho ^ (n + 1) * sin (phi + theta) := by rw [pow_succ]; ring
      _ = ((n : ℝ) + 1) * rho * sin theta := him
      _ = _ := by ring
  exact ⟨by simpa only [htrig] using hfirst,
    mul_left_cancel₀ (ne_of_gt hrho) hsecond⟩

noncomputable def polar (rho theta : ℝ) : ℂ := ⟨rho * cos theta, rho * sin theta⟩

theorem polar_mul (rho theta sigma psi : ℝ) :
    polar rho theta * polar sigma psi = polar (rho * sigma) (theta + psi) := by
  apply Complex.ext <;>
    simp [polar, Complex.mul_re, Complex.mul_im, Real.cos_add, Real.sin_add] <;> ring

theorem polar_pow (rho theta : ℝ) (m : ℕ) :
    (polar rho theta) ^ m = polar (rho ^ m) ((m : ℝ) * theta) := by
  induction m with
  | zero => apply Complex.ext <;> simp [polar]
  | succ m hm =>
      rw [pow_succ, hm, polar_mul, pow_succ]
      congr 1
      push_cast
      ring

theorem root_polar_equations
    {n : ℕ} {z : ℂ} {rho theta phi : ℝ}
    (hz : z = polar rho theta)
    (hroot : z ^ (n + 1) = ((n : ℂ) + 1) * z - (n : ℂ))
    (hcos : cos (((n : ℝ) + 1) * theta) = cos (phi + theta))
    (hsin : sin (((n : ℝ) + 1) * theta) = sin (phi + theta)) :
    rho ^ (n + 1) * cos (phi + theta) =
        ((n : ℝ) + 1) * rho * cos theta - (n : ℝ) ∧
      rho ^ (n + 1) * sin (phi + theta) =
        ((n : ℝ) + 1) * rho * sin theta := by
  rw [hz, polar_pow] at hroot
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  constructor
  · simpa [polar, Complex.mul_re, Nat.cast_add, Nat.cast_one, hcos, mul_assoc] using hre
  · simpa [polar, Complex.mul_im, Nat.cast_add, Nat.cast_one, hsin, mul_assoc] using him

end EventualIrreducibility.SectorReconstruction

namespace EventualIrreducibility.SectorReconstruction

open Real

theorem polar_eq_complex_trig (rho theta : ℝ) :
    polar rho theta =
      (rho : ℂ) * (Complex.cos (theta : ℂ) + Complex.sin (theta : ℂ) * Complex.I) := by
  apply Complex.ext <;> simp [polar, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem power_coordinates_of_root
    {n : ℕ} {z : ℂ} {rho theta : ℝ} (hrho : 0 < rho)
    (hz : z = polar rho theta)
    (hroot : z ^ (n + 1) = ((n : ℂ) + 1) * z - (n : ℂ)) :
    (z ^ n).re = ((n : ℝ) + 1) - ((n : ℝ) / rho) * cos theta ∧
      (z ^ n).im = ((n : ℝ) / rho) * sin theta := by
  have hprod : z * polar rho⁻¹ (-theta) = 1 := by
    rw [hz, polar_mul]
    apply Complex.ext <;> simp [polar, ne_of_gt hrho]
  have hpower : z ^ n = ((n : ℂ) + 1) - (n : ℂ) * polar rho⁻¹ (-theta) := by
    rw [pow_succ] at hroot
    linear_combination polar rho⁻¹ (-theta) * hroot -
      (z ^ n - ((n : ℂ) + 1)) * hprod
  constructor
  · simpa [polar, Complex.mul_re, div_eq_mul_inv, mul_assoc] using
      congrArg Complex.re hpower
  · simpa [polar, Complex.mul_im, div_eq_mul_inv, mul_assoc] using
      congrArg Complex.im hpower

theorem first_quadrant_of_power_coordinates
    {n : ℕ} (hn : 0 < n) {w : ℂ} {rho theta : ℝ}
    (hrho : 1 < rho) (htheta : 0 < theta) (htheta_pi : theta < π)
    (hre : w.re = ((n : ℝ) + 1) - ((n : ℝ) / rho) * cos theta)
    (him : w.im = ((n : ℝ) / rho) * sin theta) :
    0 < w.re ∧ 0 < w.im := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrhopos : 0 < rho := lt_trans zero_lt_one hrho
  have hdivpos : 0 < (n : ℝ) / rho := div_pos hnpos hrhopos
  have hdivlt : (n : ℝ) / rho < (n : ℝ) := by
    apply (div_lt_iff₀ hrhopos).2
    nlinarith
  have hcos : ((n : ℝ) / rho) * cos theta ≤ (n : ℝ) / rho := by
    simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one theta) hdivpos.le
  constructor
  · rw [hre]
    linarith
  · rw [him]
    exact mul_pos hdivpos (Real.sin_pos_of_pos_of_lt_pi htheta htheta_pi)

theorem arg_first_quadrant {w : ℂ} (hre : 0 < w.re) (him : 0 < w.im) :
    0 < Complex.arg w ∧ Complex.arg w < π / 2 := by
  have hnonneg : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.mpr him.le
  have hne : Complex.arg w ≠ 0 := by
    intro h
    have hz := (Complex.arg_eq_zero_iff.mp h).2
    linarith
  exact ⟨lt_of_le_of_ne hnonneg hne.symm,
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)⟩

theorem phase_of_first_quadrant
    {rho t : ℝ} (hrho : 0 < rho) (ht : 0 < t)
    (hre : 0 < (polar rho t).re) (him : 0 < (polar rho t).im) :
    ∃ k : ℤ, ∃ phi : ℝ,
      0 ≤ k ∧ 0 < phi ∧ phi < π / 2 ∧ t = 2 * π * (k : ℝ) + phi := by
  let phi : ℝ := Complex.arg (polar rho t)
  let k : ℤ := -⌊(π - t) / (2 * π)⌋
  have hphi := arg_first_quadrant hre him
  have hphase := Complex.arg_mul_cos_add_sin_mul_I_sub hrho t
  rw [← polar_eq_complex_trig] at hphase
  have heq : t = 2 * π * (k : ℝ) + phi := by
    dsimp [k, phi]
    push_cast
    linarith [hphase]
  have hk : 0 ≤ k := by
    by_contra hknonneg
    have hkneg : k ≤ -1 := by omega
    have hkreal : (k : ℝ) ≤ -1 := by exact_mod_cast hkneg
    have hterm : 2 * π * (k : ℝ) ≤ -(2 * π) := by
      nlinarith [Real.pi_pos]
    change 0 < phi ∧ phi < π / 2 at hphi
    linarith [hphi.2, Real.pi_pos]
  exact ⟨k, phi, hk, hphi.1, hphi.2, heq⟩

theorem phase_compatibility
    {n : ℕ} {theta phi : ℝ} {k : ℤ}
    (hphase : (n : ℝ) * theta = 2 * π * (k : ℝ) + phi) :
    cos (((n : ℝ) + 1) * theta) = cos (phi + theta) ∧
      sin (((n : ℝ) + 1) * theta) = sin (phi + theta) := by
  have hangle : ((n : ℝ) + 1) * theta =
      (phi + theta) + (k : ℝ) * (2 * π) := by linarith [hphase]
  rw [hangle]
  exact ⟨Real.cos_add_int_mul_two_pi _ _, Real.sin_add_int_mul_two_pi _ _⟩

theorem phase_sum_lt_pi
    {theta phi : ℝ} (_htheta : 0 < theta) (htheta_pi : theta < π)
    (hphi : 0 < phi) (hphi_upper : phi < π / 2)
    (hsin : 0 < sin (phi + theta)) : phi + theta < π := by
  by_contra hsum
  have hnonneg : 0 ≤ phi + theta - π := by linarith
  have hupper : phi + theta - π ≤ π := by linarith [Real.pi_pos]
  have hbad := Real.sin_nonneg_of_mem_Icc ⟨hnonneg, hupper⟩
  rw [Real.sin_sub_pi] at hbad
  linarith

theorem positive_sine_sum
    {n : ℕ} (hn : 0 < n) {rho theta : ℝ}
    (hrho : 0 < rho) (htheta : 0 < theta)
    (htop : (n : ℝ) * theta < π) :
    0 < ∑ j ∈ Finset.range n,
      rho ^ (j + 1) * sin (((j + 1 : ℕ) : ℝ) * theta) := by
  apply Finset.sum_pos
  · intro j hj
    have hjn : j + 1 ≤ n := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hjnreal : ((j + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    have hjpos : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
    apply mul_pos (pow_pos hrho _)
    apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hjpos htheta)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hjnreal htheta.le) htop
  · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)

theorem zero_sector_impossible
    {n : ℕ} (hn : 0 < n) {rho theta phi : ℝ}
    (hrho : 0 < rho) (htheta : 0 < theta) (hphi_upper : phi < π / 2)
    (hphase : (n : ℝ) * theta = phi)
    (hzero : (∑ j ∈ Finset.range n,
      rho ^ (j + 1) * sin (((j + 1 : ℕ) : ℝ) * theta)) = 0) : False := by
  have htop : (n : ℝ) * theta < π := by linarith [Real.pi_pos]
  have hpositive := positive_sine_sum hn hrho htheta htop
  linarith

theorem upper_root_sector
    {n : ℕ} (hn : 0 < n) {z : ℂ} {rho theta : ℝ}
    (hrho : 1 < rho) (htheta : 0 < theta) (htheta_pi : theta < π)
    (hz : z = polar rho theta)
    (hroot : z ^ (n + 1) = ((n : ℂ) + 1) * z - (n : ℂ))
    (hsum : (∑ j ∈ Finset.range n, z ^ (j + 1)) = (n : ℂ)) :
    ∃ k : ℤ, ∃ phi : ℝ,
      0 < k ∧ 0 < phi ∧ phi < π / 2 ∧
        (n : ℝ) * theta = 2 * π * (k : ℝ) + phi ∧ phi + theta < π := by
  have hrhopos : 0 < rho := lt_trans zero_lt_one hrho
  obtain ⟨hre, him⟩ := power_coordinates_of_root hrhopos hz hroot
  obtain ⟨hqu, hqv⟩ := first_quadrant_of_power_coordinates hn hrho htheta htheta_pi hre him
  have hzpow : z ^ n = polar (rho ^ n) ((n : ℝ) * theta) := by rw [hz, polar_pow]
  rw [hzpow] at hqu hqv
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨k, phi, hk, hphi, hphi_upper, hphase⟩ :=
    phase_of_first_quadrant (pow_pos hrhopos _) (mul_pos hnpos htheta) hqu hqv
  obtain ⟨hcos, hsin⟩ := phase_compatibility hphase
  obtain ⟨hpolar_re, hpolar_im⟩ := root_polar_equations hz hroot hcos hsin
  obtain ⟨-, hsine⟩ := sine_equations_of_polar_equations hrhopos hpolar_re hpolar_im
  have hsumsin : 0 < sin (phi + theta) := by
    have hright : 0 < ((n : ℝ) + 1) * sin theta :=
      mul_pos (by positivity) (Real.sin_pos_of_pos_of_lt_pi htheta htheta_pi)
    have hleft : 0 < rho ^ n * sin (phi + theta) := by rwa [hsine]
    by_contra h
    have hnonpos : rho ^ n * sin (phi + theta) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_pos hrhopos _).le (le_of_not_gt h)
    linarith
  have hsumlt := phase_sum_lt_pi htheta htheta_pi hphi hphi_upper hsumsin
  have hkne : k ≠ 0 := by
    intro hkzero
    have hphasezero : (n : ℝ) * theta = phi := by simpa [hkzero] using hphase
    have hsum_im := congrArg Complex.im hsum
    have hzero : (∑ j ∈ Finset.range n,
        rho ^ (j + 1) * sin (((j + 1 : ℕ) : ℝ) * theta)) = 0 := by
      simp only [hz, polar_pow] at hsum_im
      simpa [polar, Complex.im_sum] using hsum_im
    exact zero_sector_impossible hn hrhopos htheta hphi_upper hphasezero hzero
  exact ⟨k, phi, by omega, hphi, hphi_upper, hphase, hsumlt⟩

end EventualIrreducibility.SectorReconstruction

namespace EventualIrreducibility.UpperSector

open Real SectorReconstruction

noncomputable def sectorOffset (k : ℕ) : ℝ := 2 * π * (k : ℝ)

theorem polar_norm_arg (z : ℂ) : z = polar ‖z‖ (Complex.arg z) := by
  apply Complex.ext
  · change z.re = ‖z‖ * cos (Complex.arg z)
    exact (Complex.norm_mul_cos_arg z).symm
  · change z.im = ‖z‖ * sin (Complex.arg z)
    exact (Complex.norm_mul_sin_arg z).symm

theorem arg_mem_upper_half {z : ℂ} (him : 0 < z.im) :
    0 < Complex.arg z ∧ Complex.arg z < π := by
  have hnonneg : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr him.le
  have hne : Complex.arg z ≠ 0 := by
    intro hz
    have himzero := (Complex.arg_eq_zero_iff.mp hz).2
    linarith
  exact ⟨lt_of_le_of_ne hnonneg hne.symm,
    Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt him))⟩

theorem phase_mem_interval
    {n : ℕ} (hn : 0 < n) {k : ℕ} {theta phi : ℝ}
    (hphi : 0 < phi) (hphi_upper : phi < π / 2)
    (hphase : (n : ℝ) * theta = sectorOffset k + phi)
    (hsum : phi + theta < π) :
    theta ∈ Angular.sectorInterval (n : ℝ) (sectorOffset k) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hNpos : 0 < (n : ℝ) + 1 := by positivity
  change sectorOffset k / (n : ℝ) < theta ∧
    theta < min ((sectorOffset k + π / 2) / (n : ℝ))
      ((sectorOffset k + π) / ((n : ℝ) + 1))
  refine ⟨(div_lt_iff₀ hnpos).2 (by nlinarith), ?_⟩
  apply lt_min_iff.mpr
  exact ⟨(lt_div_iff₀ hnpos).2 (by nlinarith),
    (lt_div_iff₀ hNpos).2 (by nlinarith)⟩

theorem twice_index_lt_degree_parameter
    {n k : ℕ} (hn : 0 < n) {theta phi : ℝ}
    (htheta_pi : theta < π) (hphi : 0 < phi)
    (hphase : (n : ℝ) * theta = sectorOffset k + phi) : 2 * k < n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have htop := mul_lt_mul_of_pos_left htheta_pi hnpos
  have hscaled : ((2 : ℝ) * (k : ℝ)) * π < (n : ℝ) * π := by
    dsimp [sectorOffset] at hphase
    nlinarith
  have hreal : (2 : ℝ) * (k : ℝ) < (n : ℝ) :=
    by nlinarith [Real.pi_pos]
  exact_mod_cast hreal

theorem exists_nat_sector_of_polar_root
    {n : ℕ} (hn : 0 < n) {z : ℂ} {rho theta : ℝ}
    (hrho : 1 < rho) (htheta : 0 < theta) (htheta_pi : theta < π)
    (hz : z = polar rho theta)
    (hroot : z ^ (n + 1) = ((n : ℂ) + 1) * z - (n : ℂ))
    (hsum : (∑ j ∈ Finset.range n, z ^ (j + 1)) = (n : ℂ)) :
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧
      theta ∈ Angular.sectorInterval (n : ℝ) (sectorOffset k) := by
  obtain ⟨k, phi, hk, hphi, hphi_upper, hphase, hsumphi⟩ :=
    SectorReconstruction.upper_root_sector hn hrho htheta htheta_pi hz hroot hsum
  have hk_nonneg : 0 ≤ k := le_of_lt hk
  have hkcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
  have hkreal : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast hkcast
  have hknat : 0 < k.toNat := by omega
  have hphase_nat : (n : ℝ) * theta = sectorOffset k.toNat + phi := by
    simpa only [sectorOffset, hkreal] using hphase
  exact ⟨k.toNat, hknat,
    twice_index_lt_degree_parameter hn htheta_pi hphi hphase_nat,
    phase_mem_interval hn hphi hphi_upper hphase_nat hsumphi⟩

theorem exists_nat_sector_of_upper_root
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hnorm : 1 < ‖z‖) (him : 0 < z.im)
    (hroot : z ^ (n + 1) = ((n : ℂ) + 1) * z - (n : ℂ))
    (hsum : (∑ j ∈ Finset.range n, z ^ (j + 1)) = (n : ℂ)) :
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧
      Complex.arg z ∈ Angular.sectorInterval (n : ℝ) (sectorOffset k) := by
  obtain ⟨htheta, htheta_pi⟩ := arg_mem_upper_half him
  exact exists_nat_sector_of_polar_root hn hnorm htheta htheta_pi
    (polar_norm_arg z) hroot hsum

theorem root_trinomial_eq
    {n : ℕ} {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) :
    z ^ (n + 1) = ((n : ℂ) + 1) * z - (n : ℂ) := by
  have htrin := RootGeometry.trinomial_of_root hf
  linear_combination htrin

theorem exists_nat_sector_of_fInt_root
    {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0)
    (him : 0 < z.im) :
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧
      Complex.arg z ∈ Angular.sectorInterval (n : ℝ) (sectorOffset k) := by
  have hnorm := RootGeometry.one_lt_norm_root hn hf
  have hsum := RootGeometry.sum_powers_of_trinomial
    (RootGeometry.root_ne_one hn hf) (RootGeometry.trinomial_of_root hf)
  exact exists_nat_sector_of_upper_root hn hnorm him (root_trinomial_eq hf) hsum

end EventualIrreducibility.UpperSector

namespace EventualIrreducibility
open Real

end EventualIrreducibility

namespace EventualIrreducibility
open Real

end EventualIrreducibility

noncomputable section
open scoped BigOperators ComplexConjugate

namespace EventualIrreducibility.AngularKernel

lemma ratio_add_inv_le {q t : ℝ} (hq : 0 < q) (ht : 0 < t)
    (hlo : t ≤ q) (hhi : q ≤ t⁻¹) :
    q + q⁻¹ ≤ t + t⁻¹ := by
  have hp : 0 ≤ (q - t) * (t⁻¹ - q) :=
    mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  have hqinv : q * q⁻¹ = 1 := mul_inv_cancel₀ hq.ne'
  have htinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hm : q * (q + q⁻¹) ≤ q * (t + t⁻¹) := by nlinarith
  by_contra hnot
  have hdiff : 0 < q + q⁻¹ - (t + t⁻¹) := sub_pos.mpr (lt_of_not_ge hnot)
  have hpos := mul_pos hq hdiff
  nlinarith

lemma radius_ratio_bounds {rho sigma tau : ℝ}
    (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hlog : |Real.log rho - Real.log sigma| ≤ tau) :
    Real.exp (-tau) ≤ rho / sigma ∧
      rho / sigma ≤ (Real.exp (-tau))⁻¹ := by
  have heq : Real.exp (Real.log rho - Real.log sigma) = rho / sigma := by
    rw [Real.exp_sub, Real.exp_log hrho, Real.exp_log hsigma]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hlog
  constructor
  · rw [← heq]
    exact Real.exp_le_exp.mpr hlo
  · rw [← heq, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr hhi

lemma unit_coordinate_sq {u : ℂ} (hu : ‖u‖ = 1) :
    u.re ^ 2 + u.im ^ 2 = 1 := by
  calc
    u.re ^ 2 + u.im ^ 2 = ‖u‖ ^ 2 := by
      rw [Complex.sq_norm]
      change u.re ^ 2 + u.im ^ 2 = u.re * u.re + u.im * u.im
      ring
    _ = 1 := by rw [hu]; norm_num

lemma scaled_difference_sq (rho sigma : ℝ) (u v : ℂ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖(rho : ℂ) * u - (sigma : ℂ) * v‖ ^ 2 =
      rho ^ 2 + sigma ^ 2 - 2 * rho * sigma * (u * conj v).re := by
  have hu2 := unit_coordinate_sq hu
  have hv2 := unit_coordinate_sq hv
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, sub_zero, add_zero]
  linear_combination rho ^ 2 * hu2 + sigma ^ 2 * hv2

lemma unit_kernel_sq (t : ℝ) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖1 - (t : ℂ) * w‖ ^ 2 = 1 + t ^ 2 - 2 * t * w.re := by
  have hw2 := unit_coordinate_sq hw
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  linear_combination t ^ 2 * hw2

lemma angular_kernel_bound_of_ratio {rho sigma t : ℝ} {u v : ℂ}
    (hrho : 0 < rho) (hsigma : 0 < sigma) (ht : 0 < t)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hlo : t ≤ rho / sigma) (hhi : rho / sigma ≤ t⁻¹) :
    ‖(rho : ℂ) * u - (sigma : ℂ) * v‖ ^ 2 / (rho * sigma) ≤
      t⁻¹ * ‖1 - (t : ℂ) * u * conj v‖ ^ 2 := by
  have hw : ‖u * conj v‖ = 1 := by simp [hu, hv]
  have hrad : rho / sigma + sigma / rho ≤ t + t⁻¹ := by
    simpa only [inv_div] using
      ratio_add_inv_le (div_pos hrho hsigma) ht hlo hhi
  have hleft :
      ‖(rho : ℂ) * u - (sigma : ℂ) * v‖ ^ 2 / (rho * sigma) =
        rho / sigma + sigma / rho - 2 * (u * conj v).re := by
    rw [scaled_difference_sq rho sigma u v hu hv]
    field_simp [hrho.ne', hsigma.ne']
  have hright :
      t⁻¹ * ‖1 - (t : ℂ) * u * conj v‖ ^ 2 =
        t + t⁻¹ - 2 * (u * conj v).re := by
    rw [mul_assoc, unit_kernel_sq t (u * conj v) hw]
    field_simp [ht.ne']
    ring
  rw [hleft, hright]
  linarith

lemma angular_kernel_bound {rho sigma tau : ℝ} {u v : ℂ}
    (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hlog : |Real.log rho - Real.log sigma| ≤ tau) :
    ‖(rho : ℂ) * u - (sigma : ℂ) * v‖ ^ 2 / (rho * sigma) ≤
      (Real.exp (-tau))⁻¹ *
        ‖1 - (Real.exp (-tau) : ℂ) * u * conj v‖ ^ 2 := by
  obtain ⟨hlo, hhi⟩ := radius_ratio_bounds hrho hsigma hlog
  exact angular_kernel_bound_of_ratio hrho hsigma (Real.exp_pos _) hu hv hlo hhi

lemma angular_kernel_bound_explicit {alpha beta u v : ℂ} {rho sigma tau : ℝ}
    (halpha : alpha = (rho : ℂ) * u)
    (hbeta : beta = (sigma : ℂ) * v)
    (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hlog : |Real.log rho - Real.log sigma| ≤ tau) :
    ‖alpha - beta‖ ^ 2 / (rho * sigma) ≤
      (Real.exp (-tau))⁻¹ *
        ‖1 - (Real.exp (-tau) : ℂ) * u * conj v‖ ^ 2 := by
  rw [halpha, hbeta]
  exact angular_kernel_bound hrho hsigma hu hv hlog

lemma kernel_norm_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    0 < ‖1 - (t : ℂ) * u * conj v‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hnorm : ‖(t : ℂ) * u * conj v‖ = t := by
    simp [hu, hv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
  have heq := congrArg (fun z : ℂ => ‖z‖) (sub_eq_zero.mp hz)
  rw [norm_one, hnorm] at heq
  linarith

lemma angular_kernel_log_bound {alpha beta u v : ℂ} {rho sigma tau : ℝ}
    (halpha : alpha = (rho : ℂ) * u)
    (hbeta : beta = (sigma : ℂ) * v)
    (hrho : 0 < rho) (hsigma : 0 < sigma) (htau : 0 < tau)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hdist : alpha ≠ beta)
    (hlog : |Real.log rho - Real.log sigma| ≤ tau) :
    2 * Real.log ‖alpha - beta‖ - Real.log rho - Real.log sigma ≤
      tau + 2 * Real.log ‖1 - (Real.exp (-tau) : ℂ) * u * conj v‖ := by
  have ht : 0 < Real.exp (-tau) := Real.exp_pos _
  have ht1 : Real.exp (-tau) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hD : 0 < ‖alpha - beta‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hdist)
  have hK := kernel_norm_pos ht ht1 hu hv
  have hp := angular_kernel_bound_explicit halpha hbeta hrho hsigma hu hv hlog
  have hlogineq := Real.log_le_log
    (div_pos (pow_pos hD 2) (mul_pos hrho hsigma)) hp
  rw [Real.log_div (pow_ne_zero 2 hD.ne') (mul_ne_zero hrho.ne' hsigma.ne'),
    Real.log_pow, Real.log_mul hrho.ne' hsigma.ne',
    Real.log_mul (inv_ne_zero ht.ne') (pow_ne_zero 2 hK.ne'),
    Real.log_inv, Real.log_exp, Real.log_pow] at hlogineq
  norm_num only [Nat.cast_ofNat, neg_neg] at hlogineq
  linarith

def offDiagSum {d : ℕ} (A : Fin d → Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, A i j

lemma offDiagSum_add {d : ℕ} (A B : Fin d → Fin d → ℝ) :
    offDiagSum (fun i j => A i j + B i j) = offDiagSum A + offDiagSum B := by
  simp only [offDiagSum, Finset.sum_add_distrib]

lemma offDiagSum_sub {d : ℕ} (A B : Fin d → Fin d → ℝ) :
    offDiagSum (fun i j => A i j - B i j) = offDiagSum A - offDiagSum B := by
  simp only [offDiagSum, Finset.sum_sub_distrib]

lemma offDiagSum_mul {d : ℕ} (c : ℝ) (A : Fin d → Fin d → ℝ) :
    offDiagSum (fun i j => c * A i j) = c * offDiagSum A := by
  simp only [offDiagSum, Finset.mul_sum]

lemma offDiagSum_first {d : ℕ} (r : Fin d → ℝ) :
    offDiagSum (fun i _ => r i) = ((d - 1 : ℕ) : ℝ) * ∑ i, r i := by
  classical
  simp only [offDiagSum, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]

lemma offDiagSum_second {d : ℕ} (hd : 0 < d) (r : Fin d → ℝ) :
    offDiagSum (fun _ j => r j) = ((d - 1 : ℕ) : ℝ) * ∑ i, r i := by
  classical
  unfold offDiagSum
  simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_sub (by omega : 1 ≤ d)]
  norm_num
  ring

lemma offDiagSum_const {d : ℕ} (c : ℝ) :
    offDiagSum (fun (_ : Fin d) (_ : Fin d) => c) =
      (d : ℝ) * ((d - 1 : ℕ) : ℝ) * c := by
  rw [offDiagSum_first]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma kernel_diagonal_norm {t : ℝ} (ht1 : t < 1) {u : ℂ}
    (hu : ‖u‖ = 1) : ‖1 - (t : ℂ) * u * conj u‖ = 1 - t := by
  have hu2 := unit_coordinate_sq hu
  have hc : u * conj u = 1 := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re]
      nlinarith
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_im]
      ring
  rw [mul_assoc, hc, mul_one]
  have heq : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by simp
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1)]

lemma fullSum_eq_diagonal_add_offDiag {d : ℕ} (K : Fin d → Fin d → ℝ) :
    (∑ i, ∑ j, K i j) = (∑ i, K i i) + offDiagSum K := by
  classical
  have hrow (i : Fin d) : (∑ j, K i j) =
      K i i + ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, K i j := by
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  rfl

end EventualIrreducibility.AngularKernel

noncomputable section
open scoped BigOperators ComplexConjugate

namespace EventualIrreducibility.FourierKernel

lemma hasSum_finset_complex {ι : Type*} (s : Finset ι)
    (f : ι → ℕ → ℂ) (a : ι → ℂ)
    (hf : ∀ i ∈ s, HasSum (f i) (a i)) :
    HasSum (fun j => ∑ i ∈ s, f i j) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hiSum := hf i (Finset.mem_insert_self i s)
      have htSum := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      simpa only [Finset.sum_insert hi] using hiSum.add htSum

lemma finite_power_pair_identity {d : ℕ} (u : Fin d → ℂ) (t : ℝ) (j : ℕ) :
    (∑ i, ∑ h, ((t : ℂ) * u i * conj (u h)) ^ j / (j : ℂ)) =
      ((t ^ j / (j : ℝ) * ‖∑ i, u i ^ j‖ ^ 2 : ℝ) : ℂ) := by
  classical
  calc
    (∑ i, ∑ h, ((t : ℂ) * u i * conj (u h)) ^ j / (j : ℂ)) =
        ((t : ℂ) ^ j / (j : ℂ)) *
          ((∑ i, u i ^ j) * conj (∑ h, u h ^ j)) := by
      have hpair : (∑ i, u i ^ j) * conj (∑ h, u h ^ j) =
          ∑ i, ∑ h, u i ^ j * conj (u h ^ j) := by
        rw [map_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      rw [hpair, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      simp only [mul_pow, map_pow]
      ring
    _ = ((t : ℂ) ^ j / (j : ℂ)) *
        (‖∑ i, u i ^ j‖ ^ 2 : ℂ) := by
      rw [Complex.mul_conj']
    _ = ((t ^ j / (j : ℝ) * ‖∑ i, u i ^ j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl

lemma kernel_argument_norm {t : ℝ} (ht : 0 ≤ t) {u v : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖(t : ℂ) * u * conj v‖ = t := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, Complex.norm_conj, hu, hv, mul_one]

lemma kernel_pair_hasSum {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    HasSum (fun j : ℕ => ((t : ℂ) * u * conj v) ^ j / (j : ℂ))
      (-Complex.log (1 - (t : ℂ) * u * conj v)) := by
  apply Complex.hasSum_taylorSeries_neg_log
  rw [kernel_argument_norm ht hu hv]
  exact ht1

lemma fourier_kernel_hasSum {d : ℕ} (u : Fin d → ℂ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (hu : ∀ i, ‖u i‖ = 1) :
    HasSum
      (fun j : ℕ => t ^ j / (j : ℝ) * ‖∑ i, u i ^ j‖ ^ 2)
      (-(∑ i, ∑ h, Real.log ‖1 - (t : ℂ) * u i * conj (u h)‖)) := by
  classical
  have hcomplex :
      HasSum
        (fun j : ℕ =>
          ∑ i, ∑ h, ((t : ℂ) * u i * conj (u h)) ^ j / (j : ℂ))
        (∑ i, ∑ h, -Complex.log (1 - (t : ℂ) * u i * conj (u h))) := by
    apply hasSum_finset_complex Finset.univ
      (fun i j => ∑ h, ((t : ℂ) * u i * conj (u h)) ^ j / (j : ℂ))
      (fun i => ∑ h, -Complex.log (1 - (t : ℂ) * u i * conj (u h)))
    intro i hi
    apply hasSum_finset_complex Finset.univ
      (fun h j => ((t : ℂ) * u i * conj (u h)) ^ j / (j : ℂ))
      (fun h => -Complex.log (1 - (t : ℂ) * u i * conj (u h)))
    intro h hh
    exact kernel_pair_hasSum ht ht1 (hu i) (hu h)
  have hreal := Complex.hasSum_re hcomplex
  simpa only [finite_power_pair_identity, Complex.ofReal_re,
    Complex.re_sum, Complex.neg_re, Complex.log_re, Finset.sum_neg_distrib] using hreal

lemma fourier_kernel_prefix_le {d : ℕ} (u : Fin d → ℂ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (hu : ∀ i, ‖u i‖ = 1) (M : ℕ) :
    (∑ j ∈ Finset.range (M + 1),
      t ^ j / (j : ℝ) * ‖∑ i, u i ^ j‖ ^ 2) ≤
      -(∑ i, ∑ h, Real.log ‖1 - (t : ℂ) * u i * conj (u h)‖) := by
  have hs := fourier_kernel_hasSum u ht ht1 hu
  rw [← hs.tsum_eq]
  apply hs.summable.sum_le_tsum
  intro j hj
  positivity

end EventualIrreducibility.FourierKernel

namespace EventualIrreducibility.FourierEnergy
open scoped BigOperators ComplexConjugate

noncomputable def direction {d : ℕ} (alpha : Fin d → ℂ) (i : Fin d) : ℂ :=
  alpha i / (‖alpha i‖ : ℂ)

lemma direction_properties {d : ℕ} (alpha : Fin d → ℂ)
    (ha : ∀ i, alpha i ≠ 0) :
    (∀ i, ‖direction alpha i‖ = 1) ∧
      (∀ i, alpha i = (‖alpha i‖ : ℂ) * direction alpha i) := by
  constructor
  · intro i
    have hn : ‖alpha i‖ ≠ 0 := norm_ne_zero_iff.mpr (ha i)
    simp [direction, Complex.norm_real, hn]
  · intro i
    have hn : (‖alpha i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (ha i)
    dsimp only [direction]
    field_simp

lemma root_of_fin_product {d : ℕ} (G : ℂ[X]) (alpha : Fin d → ℂ)
    (hprod : G = ∏ i, (X - C (alpha i) : ℂ[X])) (i : Fin d) :
    G.eval (alpha i) = 0 := by
  classical
  rw [hprod, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

end EventualIrreducibility.FourierEnergy

open Polynomial
open scoped BigOperators

namespace EventualIrreducibility.RealRoots

lemma complex_eval_of_real (P : ℤ[X]) (x : ℝ) :
    ((((P.map (Int.castRingHom ℝ)).eval x) : ℝ) : ℂ) =
      (P.map (Int.castRingHom ℂ)).eval (x : ℂ) := by
  have hmaps : (P.map (Int.castRingHom ℝ)).map Complex.ofRealHom =
      P.map (Int.castRingHom ℂ) := by
    ext j
    simp [Polynomial.coeff_map]
  have heq := Polynomial.eval₂_at_apply
    (p := P.map (Int.castRingHom ℝ)) Complex.ofRealHom x
  rw [← Polynomial.eval_map, hmaps] at heq
  exact heq.symm

theorem no_nonnegative_real_root
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    ((fInt n).map (Int.castRingHom ℂ)).eval (x : ℂ) ≠ 0 := by
  intro hroot
  have hc : ((((fInt n).map (Int.castRingHom ℝ)).eval x : ℝ) : ℂ) = 0 :=
    (complex_eval_of_real (fInt n) x).trans hroot
  have hr : ((fInt n).map (Int.castRingHom ℝ)).eval x = 0 := by exact_mod_cast hc
  exact (ne_of_gt (EventualIrreducibility.real_eval_fInt_pos n hn x hx)) hr

end EventualIrreducibility.RealRoots

namespace EventualIrreducibility.AngularHarmonic

open Finset

end EventualIrreducibility.AngularHarmonic

namespace EventualIrreducibility.ActualAngularHarmonic

open Real Finset
open scoped ComplexConjugate

theorem eval_int_conj (P : ℤ[X]) (z : ℂ) :
    (P.map (Int.castRingHom ℂ)).eval (conj z) =
      conj ((P.map (Int.castRingHom ℂ)).eval z) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial j a => simp

theorem conjugate_root {n : ℕ} {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) :
    ((fInt n).map (Int.castRingHom ℂ)).eval (conj z) = 0 := by
  rw [eval_int_conj, hf]
  simp

theorem real_root_arg_eq_pi {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) (him : z.im = 0) :
    Complex.arg z = π := by
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  have hreneg : z.re < 0 := by
    by_contra h
    have hnonneg : 0 ≤ z.re := le_of_not_gt h
    exact RealRoots.no_nonnegative_real_root n hn z.re hnonneg (by simpa [hzreal] using hf)
  rw [← hzreal]
  exact Complex.arg_ofReal_of_neg hreneg

end EventualIrreducibility.ActualAngularHarmonic

open Set
open scoped BigOperators

noncomputable section

namespace EventualIrreducibility.WittLift

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [CharP L p]

omit [CharP L p] in
lemma exists_coeff_ne_zero (x : WittVector p L) (hx : x ≠ 0) :
    ∃ i : ℕ, x.coeff i ≠ 0 := by
  by_contra! h
  apply hx
  ext i
  simp [h]

def ord (x : WittVector p L) : ℕ := by
  classical
  exact if hx : x = 0 then 0 else Nat.find (exists_coeff_ne_zero x hx)

omit [CharP L p] in
lemma ord_spec (x : WittVector p L) (hx : x ≠ 0) : x.coeff (ord x) ≠ 0 := by
  classical
  simp only [ord, dif_neg hx]
  exact Nat.find_spec (exists_coeff_ne_zero x hx)

omit [CharP L p] in
lemma coeff_eq_zero_below_ord (x : WittVector p L) (hx : x ≠ 0)
    (i : ℕ) (hi : i < ord x) : x.coeff i = 0 := by
  classical
  simp only [ord, dif_neg hx] at hi
  exact not_not.mp (Nat.find_min (exists_coeff_ne_zero x hx) hi)

omit [CharP L p] in
lemma ord_eq_of_leading (x : WittVector p L) (n : ℕ)
    (hn : x.coeff n ≠ 0) (hbelow : ∀ i < n, x.coeff i = 0) : ord x = n := by
  classical
  have hx : x ≠ 0 := by intro h; subst x; simp at hn
  apply Nat.le_antisymm
  · simp only [ord, dif_neg hx]
    exact Nat.find_min' (exists_coeff_ne_zero x hx) hn
  · by_contra h
    exact ord_spec x hx (hbelow _ (by omega))

lemma ord_mul (x y : WittVector p L) (hx : x ≠ 0) (hy : y ≠ 0) :
    ord (x * y) = ord x + ord y := by
  have ex : x = (WittVector.verschiebung^[ord x]) (x.shift (ord x)) :=
    WittVector.eq_iterate_verschiebung (coeff_eq_zero_below_ord x hx)
  have ey : y = (WittVector.verschiebung^[ord y]) (y.shift (ord y)) :=
    WittVector.eq_iterate_verschiebung (coeff_eq_zero_below_ord y hy)
  apply ord_eq_of_leading
  · conv_lhs => arg 1; rw [ex, ey]
    rw [WittVector.iterate_verschiebung_mul_coeff]
    apply mul_ne_zero
    · apply pow_ne_zero
      simpa [WittVector.shift_coeff] using ord_spec x hx
    · apply pow_ne_zero
      simpa [WittVector.shift_coeff] using ord_spec y hy
  · intro i hi
    conv_lhs => rw [ex, ey]
    rw [WittVector.iterate_verschiebung_mul]
    exact WittVector.iterate_verschiebung_coeff_eq_zero _ hi

omit [CharP L p] in
lemma iterate_verschiebung_add (n : ℕ) (x y : WittVector p L) :
    WittVector.verschiebung^[n] (x + y) =
      WittVector.verschiebung^[n] x + WittVector.verschiebung^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih, map_add]

omit [CharP L p] in
lemma ord_add (x y : WittVector p L) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (ord x) (ord y) ≤ ord (x + y) := by
  let k := min (ord x) (ord y)
  have ex : x = WittVector.verschiebung^[k] (x.shift k) :=
    WittVector.eq_iterate_verschiebung fun i hi =>
      coeff_eq_zero_below_ord x hx i (lt_of_lt_of_le hi (min_le_left _ _))
  have ey : y = WittVector.verschiebung^[k] (y.shift k) :=
    WittVector.eq_iterate_verschiebung fun i hi =>
      coeff_eq_zero_below_ord y hy i (lt_of_lt_of_le hi (min_le_right _ _))
  have below : ∀ i < k, (x + y).coeff i = 0 := by
    intro i hi
    conv_lhs => rw [ex, ey]
    rw [← iterate_verschiebung_add]
    exact WittVector.iterate_verschiebung_coeff_eq_zero _ hi
  by_contra h
  exact ord_spec (x + y) hxy (below _ (by omega))

def norm (x : WittVector p L) : ℝ := by
  classical
  exact if x = 0 then 0 else Real.exp (-(ord x : ℝ))

omit [CharP L p] in
lemma norm_zero : norm (0 : WittVector p L) = 0 := by simp [norm]

omit [CharP L p] in
lemma norm_of_ne_zero (x : WittVector p L) (hx : x ≠ 0) :
    norm x = Real.exp (-(ord x : ℝ)) := by simp [norm, hx]

omit [CharP L p] in
lemma norm_nonneg (x : WittVector p L) : 0 ≤ norm x := by
  by_cases hx : x = 0
  · simp [hx, norm_zero]
  · rw [norm_of_ne_zero x hx]
    exact (Real.exp_pos _).le

omit [CharP L p] in
lemma norm_eq_zero_iff (x : WittVector p L) : norm x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [hx, norm_zero]
  · simp [norm_of_ne_zero x hx, Real.exp_ne_zero, hx]

lemma norm_mul (x y : WittVector p L) : norm (x * y) = norm x * norm y := by
  by_cases hx : x = 0
  · simp [hx, norm_zero]
  by_cases hy : y = 0
  · simp [hy, norm_zero]
  rw [norm_of_ne_zero _ (mul_ne_zero hx hy), norm_of_ne_zero x hx,
    norm_of_ne_zero y hy, ord_mul x y hx hy, Nat.cast_add, neg_add, Real.exp_add]

omit [CharP L p] in
lemma norm_nonarchimedean (x y : WittVector p L) :
    norm (x + y) ≤ max (norm x) (norm y) := by
  by_cases hx : x = 0
  · simp [hx, norm_zero]
  by_cases hy : y = 0
  · simp [hy, norm_zero]
  by_cases hxy : x + y = 0
  · rw [hxy, norm_zero]
    exact le_trans (norm_nonneg x) (le_max_left _ _)
  rw [norm_of_ne_zero _ hxy, norm_of_ne_zero x hx, norm_of_ne_zero y hy]
  have h := ord_add x y hx hy hxy
  rcases le_total (ord x) (ord y) with hle | hle
  · rw [min_eq_left hle] at h
    exact le_trans (Real.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast h))) (le_max_left _ _)
  · rw [min_eq_right hle] at h
    exact le_trans (Real.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast h))) (le_max_right _ _)

def abv : AbsoluteValue (WittVector p L) ℝ where
  toFun := norm
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' := norm_eq_zero_iff
  add_le' x y := le_trans (norm_nonarchimedean x y)
    (max_le (le_add_of_nonneg_right (norm_nonneg y))
      (le_add_of_nonneg_left (norm_nonneg x)))

omit [CharP L p] in
lemma norm_integral (x : WittVector p L) : norm x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, norm_zero]
  · rw [norm_of_ne_zero x hx, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)

omit [CharP L p] in
lemma norm_discrete (x : WittVector p L) (hx : x ≠ 0) :
    ∃ j : ℤ, norm x = Real.exp (-(j : ℝ)) := by
  exact ⟨(ord x : ℤ), by simpa using norm_of_ne_zero x hx⟩

omit [CharP L p] in
lemma norm_residue (x : WittVector p L) :
    WittVector.constantCoeff x ≠ 0 ↔ norm x = 1 := by
  by_cases hx : x = 0
  · simp [hx, norm_zero]
  rw [norm_of_ne_zero x hx, Real.exp_eq_one_iff, neg_eq_zero, Nat.cast_eq_zero]
  constructor
  · intro h
    exact ord_eq_of_leading x 0 h (by omega)
  · intro h
    simpa [h, WittVector.constantCoeff_apply] using ord_spec x hx

end EventualIrreducibility.WittLift

namespace EventualIrreducibility.WittLift

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [Field L] [CharP L p]

lemma nat_eq_unit_mul_padic_power (m : ℕ) (hm : m ≠ 0) :
    ∃ q : ℕ, m = q * p ^ padicValNat p m ∧ ¬ p ∣ q := by
  have hdiv : p ^ padicValNat p m ∣ m :=
    (padicValNat_dvd_iff_le hm).mpr le_rfl
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨q, ?_, ?_⟩
  · simpa only [Nat.mul_comm] using hq
  · intro hpdvd
    obtain ⟨b, hb⟩ := hpdvd
    apply pow_succ_padicValNat_not_dvd (p := p) hm
    refine ⟨b, ?_⟩
    calc
      m = p ^ padicValNat p m * q := hq
      _ = p ^ (padicValNat p m + 1) * b := by rw [hb, pow_succ]; ring

omit [CharP L p] in
lemma natCast_coeff_zero (m : ℕ) :
    (m : WittVector p L).coeff 0 = (m : L) := by
  change (WittVector.constantCoeff : WittVector p L →+* L)
    (m : WittVector p L) = (m : L)
  exact map_natCast _ m

theorem natCast_leading_coefficients (m : ℕ) (hm : m ≠ 0) :
    (m : WittVector p L).coeff (padicValNat p m) ≠ 0 ∧
      ∀ i < padicValNat p m, (m : WittVector p L).coeff i = 0 := by
  obtain ⟨q, hfac, hq⟩ := nat_eq_unit_mul_padic_power (p := p) m hm
  have hqL : (q : L) ≠ 0 := by
    intro hz
    exact hq ((CharP.cast_eq_zero_iff (R := L) (p := p) q).mp hz)
  have hcast : (m : WittVector p L) =
      (q : WittVector p L) * (p : WittVector p L) ^ padicValNat p m := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun t : ℕ => (t : WittVector p L)) hfac
  constructor
  · rw [hcast]
    have hlead := WittVector.mul_pow_charP_coeff_succ
      (p := p) (R := L) (q : WittVector p L)
      (m := 0) (n := padicValNat p m)
    have hlead' :
        ((q : WittVector p L) * (p : WittVector p L) ^ padicValNat p m).coeff
          (padicValNat p m) = (q : L) ^ p ^ padicValNat p m := by
      simpa only [zero_add, natCast_coeff_zero] using hlead
    rw [hlead']
    exact pow_ne_zero _ hqL
  · intro i hi
    rw [hcast]
    exact WittVector.mul_pow_charP_coeff_zero
      (p := p) (R := L) (q : WittVector p L) hi

theorem natCast_ne_zero (m : ℕ) (hm : m ≠ 0) :
    (m : WittVector p L) ≠ 0 := by
  intro hz
  have h := (natCast_leading_coefficients (p := p) (L := L) m hm).1
  rw [hz, WittVector.zero_coeff] at h
  exact h rfl

omit [CharP L p] in
lemma residue_teichmuller (a : L) :
    (WittVector.constantCoeff : WittVector p L →+* L)
      (WittVector.teichmuller p a) = a := by
  exact WittVector.teichmuller_coeff_zero p a

omit [CharP L p] in
lemma teichmuller_pow_eq_one (M : ℕ) (a : L) (ha : a ^ M = 1) :
    (WittVector.teichmuller p a) ^ M = 1 := by
  rw [← map_pow, ha, map_one]

omit [CharP L p] in
lemma residue_one_sub_teichmuller (a : L) :
    (WittVector.constantCoeff : WittVector p L →+* L)
      (1 - WittVector.teichmuller p a) = 1 - a := by
  rw [map_sub, map_one, residue_teichmuller]

theorem ord_natCast (m : ℕ) (hm : m ≠ 0) :
    ord (m : WittVector p L) = padicValNat p m := by
  obtain ⟨hlead, hbelow⟩ := natCast_leading_coefficients (p := p) (L := L) m hm
  exact ord_eq_of_leading (m : WittVector p L) (padicValNat p m) hlead hbelow

theorem norm_natCast (m : ℕ) (hm : m ≠ 0) :
    norm (m : WittVector p L) = Real.exp (-(padicValNat p m : ℝ)) := by
  have hne := natCast_ne_zero (p := p) (L := L) m hm
  simp only [norm, if_neg hne, ord_natCast m hm]

omit [CharP L p] in
theorem norm_teichmuller (a : L) (ha : a ≠ 0) :
    norm (WittVector.teichmuller p a) = 1 := by
  apply (norm_residue (WittVector.teichmuller p a)).mp
  simpa only [residue_teichmuller] using ha

omit [CharP L p] in
theorem norm_one_sub_teichmuller (a : L) (ha : a ≠ 1) :
    norm (1 - WittVector.teichmuller p a) = 1 := by
  apply (norm_residue (1 - WittVector.teichmuller p a)).mp
  rw [residue_one_sub_teichmuller]
  exact sub_ne_zero.mpr (Ne.symm ha)

end EventualIrreducibility.WittLift

namespace EventualIrreducibility.WittLift

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p]

def normalizedIntegralRootLift (M : ℕ) (a : L)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (haM : a ^ M = 1) :
    LocalShapeAssembly.NormalizedIntegralRootLift p M L a where
  R := WittVector p L
  v := abv
  red := WittVector.constantCoeff
  nonarchimedean := norm_nonarchimedean
  integral := norm_integral
  discrete := norm_discrete
  residue_unit := norm_residue
  nat_norm := norm_natCast
  z := WittVector.teichmuller p a
  reduces := residue_teichmuller a
  root := teichmuller_pow_eq_one M a haM
  unit := norm_teichmuller a ha0
  separated := norm_one_sub_teichmuller a ha1

end EventualIrreducibility.WittLift

namespace EventualIrreducibility

theorem unramifiedRootLiftInput_of_witt : LocalShapeAssembly.UnramifiedRootLiftInput := by
  intro p M hp hM hpM L instField instCharP a ha0 ha1 haM
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨WittLift.normalizedIntegralRootLift M a ha0 ha1 haM⟩

end EventualIrreducibility

namespace EventualIrreducibility

theorem reductionShapeInput_proved : ReductionShapeInput :=
  LocalShapeAssembly.reductionShapeInput_of_unramifiedRootLiftInput
    unramifiedRootLiftInput_of_witt

theorem localInput_proved : LocalInput :=
  localInput_of_reductionShape reductionShapeInput_proved

end EventualIrreducibility

open Polynomial
open scoped BigOperators ComplexConjugate

namespace UniversalIrreducibility

lemma constants_isCoprime_of_linear {a b u v : ℤ}
    (h : a * v + b * u = a * b - 1) : IsCoprime a b := by
  refine ⟨b - v, -u, ?_⟩
  nlinarith

lemma first_difference_isCoprime {a b u v c : ℤ}
    (h : a * v + b * u = a * b - 1) :
    IsCoprime a (u - a * c) := by
  refine ⟨b - v - b * c, -b, ?_⟩
  nlinarith

lemma first_difference_ne_zero {a b u v c : ℤ}
    (ha : 1 < a) (h : a * v + b * u = a * b - 1) :
    u - a * c ≠ 0 := by
  intro hz
  have hc := first_difference_isCoprime (c := c) h
  rw [hz, isCoprime_zero_right] at hc
  have habs : |a| = 1 := Int.isUnit_iff_abs_eq.mp hc
  rw [abs_of_pos (by omega)] at habs
  omega

lemma polynomial_constants_and_linear {g h P : ℤ[X]} {n : ℤ}
    (hgh : g * h = P) (h0 : P.coeff 0 = n)
    (h1 : P.coeff 1 = n - 1) :
    g.coeff 0 * h.coeff 0 = n ∧
      g.coeff 0 * h.coeff 1 + h.coeff 0 * g.coeff 1 = n - 1 := by
  constructor
  · simpa only [Polynomial.mul_coeff_zero] using
      (congrArg (fun q : ℤ[X] => q.coeff 0) hgh).trans h0
  · have he := (congrArg (fun q : ℤ[X] => q.coeff 1) hgh).trans h1
    simpa only [Polynomial.mul_coeff_one, mul_comm (g.coeff 1)] using he

lemma polynomial_constant_coprime {g h P : ℤ[X]} {n : ℤ}
    (hgh : g * h = P) (h0 : P.coeff 0 = n)
    (h1 : P.coeff 1 = n - 1) :
    IsCoprime (g.coeff 0) (h.coeff 0) := by
  obtain ⟨hc, hl⟩ := polynomial_constants_and_linear hgh h0 h1
  apply constants_isCoprime_of_linear (u := g.coeff 1) (v := h.coeff 1)
  rwa [hc]

lemma norm_sq_metric_identity (z : ℂ) (r : ℝ) :
    ‖z - (r : ℂ)‖ ^ 2 - r * ‖z - 1‖ ^ 2 =
      (1 - r) * (‖z‖ ^ 2 - r) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im]
  ring

lemma norm_metric_sq_lt {z : ℂ} {r : ℝ}
    (hz : 1 < ‖z‖) (hr : r < 1) :
    r * ‖z - 1‖ ^ 2 < ‖z - (r : ℂ)‖ ^ 2 := by
  have hsq : r < ‖z‖ ^ 2 := by nlinarith
  have hp := mul_pos (sub_pos.mpr hr) (sub_pos.mpr hsq)
  rw [← norm_sq_metric_identity z r] at hp
  linarith

end UniversalIrreducibility

namespace UniversalScalar

theorem bridge_mirror_polynomial (ell c : ℝ)
    (he0 : 26 / 5 ≤ ell) (he1 : ell ≤ 7)
    (hc0 : 69 / 100 ≤ c) :
    (1 / 2) * ell ^ 2 - ell * c - (3 / 2) * c ^ 2 -
      (47 / 15) * ell - (47 / 15) * c + 187 / 40 < 0 := by
  have hepos : 0 ≤ ell := by linarith
  have hcross := mul_nonneg (sub_nonneg.mpr hc0) hepos
  have hsq : (69 / 100 : ℝ) ^ 2 ≤ c ^ 2 := by
    nlinarith [sq_nonneg (c - 69 / 100)]
  have hquad := mul_nonneg (sub_nonneg.mpr he0) (sub_nonneg.mpr he1)
  nlinarith

theorem bridge_mirror_negative (ell L A m : ℝ)
    (he0 : 26 / 5 ≤ ell) (he1 : ell ≤ 7)
    (hc0 : 69 / 100 ≤ L - ell)
    (hA : 51 / 20 ≤ A) (hm : m ≤ 9 / 5) :
    ell + m - (A + L / 2) * (1 + (L - 11 / 6) / (2 * L)) < 0 := by
  have hL : 0 < L := by linarith
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hp := bridge_mirror_polynomial ell (L - ell) he0 he1 hc0
  have ha := mul_nonneg (sub_nonneg.mpr hA)
    (show 0 ≤ 3 * L - 11 / 6 by linarith)
  have hx := mul_nonneg (show 0 ≤ 2 * L by linarith)
    (sub_nonneg.mpr hm)
  have hnum :
      2 * L * (ell + m) -
        (A + L / 2) * (3 * L - 11 / 6) < 0 := by
    nlinarith
  have hid :
      (2 * L) * (ell + m -
        (A + L / 2) * (1 + (L - 11 / 6) / (2 * L))) =
      2 * L * (ell + m) -
        (A + L / 2) * (3 * L - 11 / 6) := by
    field_simp
    ring
  rw [← hid] at hnum
  nlinarith

theorem balanced_lower (ell c m : ℝ)
    (hc : c < 7 / 10) (hm : 7 / 5 < m) :
    ell / 8 + m / 2 - 3 * c / 8 + 11 / 48 >
      ell / 8 + 2 / 3 := by
  linarith

theorem bridge_final_contradiction (ell G : ℝ)
    (hlo : ell / 8 + 2 / 3 < G)
    (hhi : G < ell / 8 + 33 / 50) : False := by
  linarith

end UniversalScalar

namespace UniversalScalar

noncomputable def radialMoment (ell W A delta m : ℝ) : ℝ :=
  delta * (ell - A + m) - W * delta ^ 2 / 2

noncomputable def radialEndpoint (ell L W A m : ℝ) : ℝ :=
  A * (ell + m) / L - A ^ 2 * (L + W / 2) / L ^ 2

noncomputable def largeEndpoint (ell L A m : ℝ) : ℝ :=
  A * (ell + m - 3 * A / 2) / L

lemma radialEndpoint_self (ell L A m : ℝ) (hL : L ≠ 0) :
    radialEndpoint ell L L A m = largeEndpoint ell L A m := by
  unfold radialEndpoint largeEndpoint
  field_simp
  ring

lemma radialMoment_gt_endpoint (ell L W A delta m : ℝ)
    (hL : 0 < L) (hW : 0 < W)
    (hdelta : delta < 1 / 2) (hAL : A < delta * L)
    (hmargin : 0 < ell - L / 2 + m - W / 2) :
    radialEndpoint ell L W A m < radialMoment ell W A delta m := by
  let x : ℝ := A / L
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hx : x < delta := by
    dsimp [x]
    exact (div_lt_iff₀ hL).2 hAL
  have hxhalf : x < 1 / 2 := lt_trans hx hdelta
  have hAhalf : A < L / 2 := by nlinarith
  have hw : W * (delta + x) < W := by nlinarith
  have hbracket : 0 < ell - A + m - W * (delta + x) / 2 := by
    linarith
  have hpos := mul_pos (sub_pos.mpr hx) hbracket
  have hid :
      radialMoment ell W A delta m - radialEndpoint ell L W A m =
        (delta - x) * (ell - A + m - W * (delta + x) / 2) := by
    dsimp [radialMoment, radialEndpoint, x]
    field_simp
    ring
  rw [← hid] at hpos
  linarith

lemma concave_quadratic_positive_between (u v x p c q : ℝ)
    (huv : u < v) (hux : u ≤ x) (hxv : x ≤ v) (hc : 0 ≤ c)
    (hu : 0 < p * u + q - c * u ^ 2)
    (hv : 0 < p * v + q - c * v ^ 2) :
    0 < p * x + q - c * x ^ 2 := by
  by_cases hx : x = v
  · simpa [hx] using hv
  have hxv' : x < v := lt_of_le_of_ne hxv hx
  have hleft := mul_pos (sub_pos.mpr hxv') hu
  have hright := mul_nonneg (sub_nonneg.mpr hux) (le_of_lt hv)
  have hcurve := mul_nonneg
    (mul_nonneg (mul_nonneg hc (sub_nonneg.mpr hux))
      (sub_nonneg.mpr hxv)) (le_of_lt (sub_pos.mpr huv))
  have hid :
      (v - u) * (p * x + q - c * x ^ 2) =
        (v - x) * (p * u + q - c * u ^ 2) +
        (x - u) * (p * v + q - c * v ^ 2) +
        c * (x - u) * (v - x) * (v - u) := by ring
  have hm : 0 < (v - u) * (p * x + q - c * x ^ 2) := by
    rw [hid]
    linarith
  exact (mul_pos_iff_of_pos_left (sub_pos.mpr huv)).1 hm

theorem bridge_closure (ell L A delta m : ℝ)
    (he0 : 26 / 5 ≤ ell) (he1 : ell ≤ 7)
    (hc0 : 69 / 100 ≤ L - ell) (hc1 : L - ell < 7 / 10)
    (hA : 51 / 20 ≤ A) (hd : delta < 1 / 2)
    (hAL : A < delta * L)
    (hm0 : 7 / 5 < m) (hm1 : m ≤ 9 / 5)
    (hbudget : radialMoment ell (L - 11 / 6) A delta m <
      ell / 8 + 33 / 50) : False := by
  have hL : 0 < L := by linarith
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hW : 0 < L - 11 / 6 := by linarith
  have hAhalf : A < L / 2 := by nlinarith
  have hg := radialMoment_gt_endpoint ell L (L - 11 / 6) A delta m
    hL hW hd hAL (by linarith)
  have hmirror := bridge_mirror_negative ell L A m he0 he1 hc0 hA hm1
  have hp := mul_nonneg_of_nonpos_of_nonpos
    (show A - L / 2 ≤ 0 by linarith) (le_of_lt hmirror)
  let bal : ℝ := ell / 8 + m / 2 - 3 * (L - ell) / 8 + 11 / 48
  have hid :
      L * (radialEndpoint ell L (L - 11 / 6) A m - bal) =
        (A - L / 2) *
          (ell + m - (A + L / 2) *
            (1 + (L - 11 / 6) / (2 * L))) := by
    dsimp [radialEndpoint, bal]
    field_simp
    ring
  have hbal : bal ≤ radialEndpoint ell L (L - 11 / 6) A m := by
    by_contra hbad
    have hpbad := mul_pos hL (sub_pos.mpr (lt_of_not_ge hbad))
    nlinarith [hid]
  have hblo : ell / 8 + 2 / 3 < bal := by
    dsimp [bal]
    exact balanced_lower ell (L - ell) m hc1 hm0
  exact bridge_final_contradiction ell
    (radialMoment ell (L - 11 / 6) A delta m)
    (lt_trans (lt_of_lt_of_le hblo hbal) hg) hbudget

lemma large_low_A (ell L A m : ℝ)
    (he : 69 / 10 ≤ ell) (hc : L - ell < 7 / 10)
    (hL : 0 < L) (hm : 2 < m)
    (hA0 : 51 / 20 ≤ A) (hA1 : A ≤ 3) :
    11 * A / 60 + 109 / 100 < largeEndpoint ell L A m := by
  have hApos : 0 < A := by linarith
  have hL0 : L ≠ 0 := ne_of_gt hL
  let H0 : ℝ := A * (89 - 15 * A) / 76
  have hquad := mul_nonneg (sub_nonneg.mpr hA0) (sub_nonneg.mpr hA1)
  have hH0 : 11 * A / 60 + 109 / 100 < H0 := by
    dsimp [H0]
    nlinarith
  have hp1 := mul_nonneg
    (show 0 ≤ 15 * A - 13 by linarith) (sub_nonneg.mpr he)
  have hp2 := mul_nonneg
    (show 0 ≤ 89 - 15 * A by linarith)
    (show 0 ≤ ell + 7 / 10 - L by linarith)
  have hp3 : 0 < 76 * (m - 2) := by linarith
  have hpos := mul_pos hApos (show 0 <
      (15 * A - 13) * (ell - 69 / 10) +
        (89 - 15 * A) * (ell + 7 / 10 - L) + 76 * (m - 2) by
    linarith)
  have hid :
      (76 * L) * (largeEndpoint ell L A m - H0) =
      A * ((15 * A - 13) * (ell - 69 / 10) +
        (89 - 15 * A) * (ell + 7 / 10 - L) + 76 * (m - 2)) := by
    dsimp [largeEndpoint, H0]
    field_simp
    ring
  rw [← hid] at hpos
  have hdiff : H0 < largeEndpoint ell L A m := by nlinarith
  exact lt_trans hH0 hdiff

lemma large_middle_A (ell L A m : ℝ)
    (hc : L - ell < 7 / 10) (hL : 0 < L) (hm : 2 < m)
    (hA0 : 3 ≤ A) (hA1 : A ≤ ell / 4) :
    11 * A / 60 + 109 / 100 < largeEndpoint ell L A m := by
  have hApos : 0 < A := by linarith
  have hb : 0 < ell + m - 3 * A / 2 - 5 * L / 8 := by linarith
  have hp := mul_pos hApos hb
  have hh : 5 * A / 8 < largeEndpoint ell L A m := by
    unfold largeEndpoint
    apply (lt_div_iff₀ hL).2
    nlinarith
  have hlin : 11 * A / 60 + 109 / 100 < 5 * A / 8 := by linarith
  exact lt_trans hlin hh

lemma large_balanced_endpoint (ell L m : ℝ)
    (hL : 0 < L) (hc : L - ell < 7 / 10) (hm : 2 < m) :
    ell / 8 + 33 / 50 < largeEndpoint ell L (L / 2) m := by
  have hid : largeEndpoint ell L (L / 2) m =
      ell / 8 + m / 2 - 3 * (L - ell) / 8 := by
    unfold largeEndpoint
    field_simp
    ring
  rw [hid]
  linarith

lemma large_endpoint_three (ell L m : ℝ)
    (he0 : 69 / 10 ≤ ell) (he1 : ell ≤ 12)
    (hL : 0 < L) (hc : L - ell < 7 / 10) (hm : 2 < m) :
    ell / 8 + 33 / 50 < largeEndpoint ell L 3 m := by
  have hT : 0 < ell / 8 + 33 / 50 := by linarith
  have hx := mul_lt_mul_of_pos_right
    (show L < ell + 7 / 10 by linarith) hT
  have hquad := mul_nonneg (sub_nonneg.mpr he0) (sub_nonneg.mpr he1)
  have hb : (ell + 7 / 10) * (ell / 8 + 33 / 50) <
      3 * (ell - 5 / 2) := by nlinarith
  unfold largeEndpoint
  apply (lt_div_iff₀ hL).2
  nlinarith

lemma large_endpoint_quarter (ell L m : ℝ)
    (he : 12 ≤ ell) (hL : 0 < L)
    (hc : L - ell < 7 / 10) (hm : 2 < m) :
    ell / 8 + 33 / 50 < largeEndpoint ell L (ell / 4) m := by
  have hT : 0 < ell / 8 + 33 / 50 := by linarith
  have hx := mul_lt_mul_of_pos_right
    (show L < ell + 7 / 10 by linarith) hT
  have hquad := mul_nonneg (show 0 ≤ ell by linarith) (sub_nonneg.mpr he)
  have hb : (ell + 7 / 10) * (ell / 8 + 33 / 50) <
      (ell / 4) * (ell + 2 - 3 * (ell / 4) / 2) := by nlinarith
  have hextra := mul_pos (show 0 < ell / 4 by linarith)
    (show 0 < m - 2 by linarith)
  unfold largeEndpoint
  apply (lt_div_iff₀ hL).2
  nlinarith

lemma large_high_A (ell L A m : ℝ)
    (he : 69 / 10 ≤ ell) (hL : 0 < L)
    (hc : L - ell < 7 / 10) (hm : 2 < m)
    (hA0 : 3 ≤ A) (hA1 : ell / 4 ≤ A) (hA2 : A < L / 2) :
    ell / 8 + 33 / 50 < largeEndpoint ell L A m := by
  let T : ℝ := ell / 8 + 33 / 50
  have hv := large_balanced_endpoint ell L m hL hc hm
  have hv' : 0 < (ell + m) * (L / 2) - L * T -
      (3 / 2) * (L / 2) ^ 2 := by
    unfold largeEndpoint at hv
    have hvn := (lt_div_iff₀ hL).1 hv
    dsimp [T]
    nlinarith
  have hx : 0 < (ell + m) * A - L * T - (3 / 2) * A ^ 2 := by
    by_cases hel : ell ≤ 12
    · have hu := large_endpoint_three ell L m he hel hL hc hm
      have hu' : 0 < (ell + m) * 3 - L * T - (3 / 2) * (3 : ℝ) ^ 2 := by
        unfold largeEndpoint at hu
        have hun := (lt_div_iff₀ hL).1 hu
        dsimp [T]
        nlinarith
      have hh := concave_quadratic_positive_between 3 (L / 2) A
        (ell + m) (3 / 2) (-L * T) (by linarith) hA0
        (le_of_lt hA2) (by norm_num) (by nlinarith [hu']) (by nlinarith [hv'])
      nlinarith [hh]
    · have he12 : 12 ≤ ell := by linarith
      have hu := large_endpoint_quarter ell L m he12 hL hc hm
      have hu' : 0 < (ell + m) * (ell / 4) - L * T -
          (3 / 2) * (ell / 4) ^ 2 := by
        unfold largeEndpoint at hu
        have hun := (lt_div_iff₀ hL).1 hu
        dsimp [T]
        nlinarith
      have hh := concave_quadratic_positive_between (ell / 4) (L / 2) A
        (ell + m) (3 / 2) (-L * T) (by linarith) hA1
        (le_of_lt hA2) (by norm_num) (by nlinarith [hu']) (by nlinarith [hv'])
      nlinarith [hh]
  unfold largeEndpoint
  apply (lt_div_iff₀ hL).2
  dsimp [T] at hx
  nlinarith

theorem large_closure (ell L A delta m : ℝ)
    (he : 69 / 10 ≤ ell) (hL : 0 < L)
    (hc : L - ell < 7 / 10) (hm : 2 < m)
    (hA : 51 / 20 ≤ A) (hd : delta < 1 / 2)
    (hAL : A < delta * L)
    (hsmall : radialMoment ell L A delta m < 11 * A / 60 + 109 / 100)
    (hbudget : radialMoment ell L A delta m < ell / 8 + 33 / 50) : False := by
  have hAhalf : A < L / 2 := by nlinarith
  have hg := radialMoment_gt_endpoint ell L L A delta m
    hL hL hd hAL (by linarith)
  rw [radialEndpoint_self ell L A m (ne_of_gt hL)] at hg
  by_cases ha3 : A ≤ 3
  · have hh := large_low_A ell L A m he hc hL hm hA ha3
    linarith
  · have ha3' : 3 ≤ A := by linarith
    by_cases haquarter : A ≤ ell / 4
    · have hh := large_middle_A ell L A m hc hL hm ha3' haquarter
      linarith
    · have hq : ell / 4 ≤ A := by linarith
      have hh := large_high_A ell L A m he hL hc hm ha3' hq hAhalf
      linarith

end UniversalScalar

namespace UniversalScalar

lemma log_tangent_at (x b : ℝ) (hx : 0 < x) (hb : 0 < b) :
    Real.log x ≤ Real.log b + (x - b) / b := by
  have ht := Real.log_le_sub_one_of_pos (div_pos hx hb)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hb)] at ht
  have hid : x / b - 1 = (x - b) / b := by field_simp
  rw [hid] at ht
  linarith

lemma log_power_two_lower (x : ℝ) (hx : 0 < x) (k j : ℕ) :
    (j : ℝ) * Real.log 2 + 1 - (2 : ℝ) ^ j / x ^ k ≤
      (k : ℝ) * Real.log x := by
  have ht := Real.log_le_sub_one_of_pos
    (div_pos (show 0 < (2 : ℝ) ^ j by positivity) (pow_pos hx k))
  rw [Real.log_div (by positivity) (ne_of_gt (pow_pos hx k)),
    Real.log_pow, Real.log_pow] at ht
  linarith

lemma log_power_two_upper (x : ℝ) (hx : 0 < x) (k j : ℕ) :
    (k : ℝ) * Real.log x ≤
      (j : ℝ) * Real.log 2 + x ^ k / (2 : ℝ) ^ j - 1 := by
  have ht := Real.log_le_sub_one_of_pos
    (div_pos (pow_pos hx k) (show 0 < (2 : ℝ) ^ j by positivity))
  rw [Real.log_div (ne_of_gt (pow_pos hx k)) (by positivity),
    Real.log_pow, Real.log_pow] at ht
  linarith

lemma log_two_rational_bounds :
    (6931 / 10000 : ℝ) < Real.log 2 ∧ Real.log 2 < 1733 / 2500 := by
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

lemma log_182_gt : (26 / 5 : ℝ) < Real.log 182 := by
  have h := log_power_two_lower 182 (by norm_num) 2 15
  norm_num at h
  linarith [log_two_rational_bounds.1]

lemma log_13_gt : (51 / 20 : ℝ) < Real.log 13 := by
  have h := log_power_two_lower 13 (by norm_num) 3 11
  norm_num at h
  linarith [log_two_rational_bounds.1]

lemma log_1000_bounds :
    (69 / 10 : ℝ) < Real.log 1000 ∧ Real.log 1000 < 7 := by
  have hlo := log_power_two_lower 1000 (by norm_num) 1 10
  have hhi := log_power_two_upper 1000 (by norm_num) 1 10
  norm_num at hlo hhi
  constructor <;> linarith [log_two_rational_bounds.1, log_two_rational_bounds.2]

lemma log_182_lt : Real.log (182 : ℝ) < 7 := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 182)
    (by norm_num : (182 : ℝ) < 1000)
  exact lt_trans h log_1000_bounds.2

lemma log_2001_gt : (15 / 2 : ℝ) < Real.log 2001 := by
  have h := log_power_two_lower 2001 (by norm_num) 1 11
  norm_num at h
  linarith [log_two_rational_bounds.1]

lemma log_fifteen_halves_gt : (2 : ℝ) < Real.log (15 / 2) := by
  have h := log_power_two_lower (15 / 2) (by norm_num) 2 6
  norm_num at h
  linarith [log_two_rational_bounds.1]

lemma log_bridge_width_lower : (7 / 5 : ℝ) < Real.log (1217 / 300) := by
  have h := log_power_two_lower (1217 / 300) (by norm_num) 1 2
  norm_num at h
  linarith [log_two_rational_bounds.1]

lemma log_six_lt : Real.log (6 : ℝ) < 9 / 5 := by
  have h := log_power_two_upper 6 (by norm_num) 2 5
  norm_num at h
  linarith [log_two_rational_bounds.2]

lemma inner_radius_log_certificate : (11 / 6 : ℝ) < Real.log (157 / 25) := by
  have h := log_power_two_lower (157 / 25) (by norm_num) 3 8
  norm_num at h
  linarith [log_two_rational_bounds.1]

lemma log_three_lt : Real.log (3 : ℝ) < 11 / 10 := by
  have h := log_power_two_upper 3 (by norm_num) 7 11
  norm_num at h
  linarith [log_two_rational_bounds.2]

lemma log_five_lt : Real.log (5 : ℝ) < 13 / 8 := by
  have h := log_power_two_upper 5 (by norm_num) 3 7
  norm_num at h
  linarith [log_two_rational_bounds.2]

lemma log_seven_lt : Real.log (7 : ℝ) < 2 := by
  have h := log_power_two_upper 7 (by norm_num) 3 8
  norm_num at h
  linarith [log_two_rational_bounds.2]

lemma log_603_hundredths_lt : Real.log (603 / 100 : ℝ) < 2 := by
  have h := log_power_two_upper (603 / 100) (by norm_num) 1 3
  norm_num at h
  linarith [log_two_rational_bounds.2]

lemma log_three_K_lt {K : ℝ} (hK : 0 < K) (hKhi : K < 201 / 100) :
    Real.log (3 * K) < 2 := by
  have h := Real.log_lt_log (show 0 < 3 * K by positivity)
    (show 3 * K < (603 / 100 : ℝ) by linarith)
  exact lt_trans h log_603_hundredths_lt

lemma log_factor_constant_lower {a : ℝ} (ha : 13 ≤ a) :
    (51 / 20 : ℝ) < Real.log a := by
  exact lt_of_lt_of_le log_13_gt (Real.log_le_log (by norm_num) ha)

lemma log_n_width_shift {n : ℝ} (hn : 182 ≤ n) :
    (69 / 100 : ℝ) < Real.log (2 * n + 1) - Real.log n ∧
      Real.log (2 * n + 1) - Real.log n < 7 / 10 := by
  have hnpos : 0 < n := by linarith
  have htwo : 0 < 2 * n := by positivity
  have hlo := Real.log_lt_log htwo (show 2 * n < 2 * n + 1 by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hnpos)] at hlo
  have hhi := log_tangent_at (2 * n + 1) (2 * n) (by positivity) htwo
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hnpos)] at hhi
  have hinv : (1 : ℝ) / n ≤ 1 / 182 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 182) hn
  have hid : (2 * n + 1 - 2 * n) / (2 * n) = (1 / n) / 2 := by
    field_simp
    ring
  rw [hid] at hhi
  constructor <;> linarith [log_two_rational_bounds.1, log_two_rational_bounds.2]

theorem bridge_log_hypotheses {n : ℝ} (hn0 : 182 ≤ n) (hn1 : n < 1000) :
    26 / 5 ≤ Real.log n ∧ Real.log n ≤ 7 ∧
    69 / 100 ≤ Real.log (2 * n + 1) - Real.log n ∧
    Real.log (2 * n + 1) - Real.log n < 7 / 10 ∧
    7 / 5 < Real.log (Real.log (2 * n + 1) - 11 / 6) ∧
    Real.log (Real.log (2 * n + 1) - 11 / 6) ≤ 9 / 5 := by
  have hnpos : 0 < n := by linarith
  have helllo : 26 / 5 < Real.log n :=
    lt_of_lt_of_le log_182_gt (Real.log_le_log (by norm_num) hn0)
  have hellhi : Real.log n < 7 :=
    lt_trans (Real.log_lt_log hnpos hn1) log_1000_bounds.2
  obtain ⟨hclo, hchi⟩ := log_n_width_shift hn0
  have hWlo : (1217 / 300 : ℝ) < Real.log (2 * n + 1) - 11 / 6 := by
    linarith
  have hWpos : 0 < Real.log (2 * n + 1) - 11 / 6 := by linarith
  have hWloLog := Real.log_lt_log (by norm_num : (0 : ℝ) < 1217 / 300) hWlo
  have hWltSix : Real.log (2 * n + 1) - 11 / 6 < 6 := by linarith
  have hWhiLog := Real.log_lt_log hWpos hWltSix
  exact ⟨helllo.le, hellhi.le, hclo.le, hchi,
    lt_trans log_bridge_width_lower hWloLog,
    (lt_trans hWhiLog log_six_lt).le⟩

theorem large_log_hypotheses {n : ℝ} (hn : 1000 ≤ n) :
    69 / 10 ≤ Real.log n ∧ 0 < Real.log (2 * n + 1) ∧
    Real.log (2 * n + 1) - Real.log n < 7 / 10 ∧
    2 < Real.log (Real.log (2 * n + 1)) := by
  have helllo := lt_of_lt_of_le log_1000_bounds.1
    (Real.log_le_log (by norm_num : (0 : ℝ) < 1000) hn)
  have hLlo : (15 / 2 : ℝ) < Real.log (2 * n + 1) :=
    lt_of_lt_of_le log_2001_gt
      (Real.log_le_log (by norm_num) (show (2001 : ℝ) ≤ 2 * n + 1 by linarith))
  have hm := Real.log_lt_log (by norm_num : (0 : ℝ) < 15 / 2) hLlo
  exact ⟨helllo.le, by linarith, (log_n_width_shift (by linarith : 182 ≤ n)).2,
    lt_trans log_fifteen_halves_gt hm⟩

lemma log_n_affine_182 {n : ℝ} (hn : 182 ≤ n) :
    Real.log n < n / 182 + 6 := by
  have ht := log_tangent_at n 182 (by linarith) (by norm_num)
  linarith [log_182_lt]

lemma log_n_affine_1000 {n : ℝ} (hn : 1000 ≤ n) :
    Real.log n < n / 1000 + 6 := by
  have ht := log_tangent_at n 1000 (by linarith) (by norm_num)
  linarith [log_1000_bounds.2]

theorem actual_budget_error {n : ℝ} (hn : 182 ≤ n) :
    (Real.log n / 8 + 13 / 20 + 1 / 16 + 1 / (16 * n)) / n < 1 / 100 := by
  have hnpos : 0 < n := by linarith
  have ht := log_n_affine_182 hn
  have hi : (1 : ℝ) / (16 * n) ≤ 1 / 16 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16)
      (show (16 : ℝ) ≤ 16 * n by nlinarith)
  apply (div_lt_iff₀ hnpos).2
  linarith

theorem actual_small_support_error {n : ℝ} (hn : 1000 ≤ n) :
    (21 * Real.log n / 10 + 1) / n < 1 / 50 := by
  have hnpos : 0 < n := by linarith
  have ht := log_n_affine_1000 hn
  apply (div_lt_iff₀ hnpos).2
  linarith

end UniversalScalar

namespace UniversalScalar

lemma half_log_successive_product_le {n : ℝ} (hn : 0 < n) :
    Real.log (n * (n + 1)) / 2 ≤ Real.log n + 1 / (2 * n) := by
  have hN : 0 < n + 1 := by linarith
  have ht := log_tangent_at (n + 1) n hN hn
  have hid : (n + 1 - n) / n = 1 / n := by congr 1; ring
  rw [hid] at ht
  rw [Real.log_mul (ne_of_gt hn) (ne_of_gt hN)]
  have hid2 : (1 : ℝ) / (2 * n) = (1 / n) / 2 := by field_simp
  rw [hid2]
  linarith

lemma log_half_successive_product_eq {n : ℝ} (hn : 0 < n) :
    Real.log (n * (n + 1) / 2) = Real.log (n * (n + 1)) - Real.log 2 := by
  exact Real.log_div (by positivity) (by norm_num)

lemma log_half_successive_product_lt {n : ℝ} (hn : 1 < n) :
    Real.log (n * (n + 1) / 2) < 2 * Real.log n := by
  have hnpos : 0 < n := by linarith
  have hprod := mul_pos hnpos (show 0 < n - 1 by linarith)
  have hlt : n * (n + 1) / 2 < n ^ 2 := by nlinarith
  have hl := Real.log_lt_log (show 0 < n * (n + 1) / 2 by positivity) hlt
  rw [Real.log_pow] at hl
  norm_num at hl
  exact hl

lemma evaluation_log_bounds {n F : ℝ} (hn : 1 < n)
    (hF : F ≤ Real.log (n * (n + 1) / 2)) :
    F ≤ 2 * (Real.log (n * (n + 1)) / 2) - Real.log 2 ∧
      F < 2 * Real.log n := by
  have heq := log_half_successive_product_eq (by linarith : 0 < n)
  constructor
  · rw [heq] at hF
    linarith
  · exact lt_of_le_of_lt hF (log_half_successive_product_lt hn)

end UniversalScalar

namespace UniversalScalar

lemma log_thirteen_lt_eighteen_sevenths : Real.log (13 : ℝ) < 18 / 7 := by
  have h := log_power_two_upper 13 (by norm_num) 3 11
  norm_num at h
  linarith [log_two_rational_bounds.2]

lemma log_seven_lt_thirtynine_twentieths : Real.log (7 : ℝ) < 39 / 20 := by
  have h := log_power_two_upper 7 (by norm_num) 5 14
  norm_num at h
  linarith [log_two_rational_bounds.2]

lemma two_sinh_cubic_bound (x : ℝ) (hx : |x| ≤ 1) :
    |2 * Real.sinh x - 2 * x| ≤ |x| ^ 3 := by
  have hp := Real.exp_bound (x := x) (n := 3) hx (by omega)
  have hm := Real.exp_bound (x := -x) (n := 3)
    (by simpa only [abs_neg] using hx) (by omega)
  have hid : 2 * Real.sinh x - 2 * x =
      (Real.exp x - ∑ m ∈ Finset.range 3, x ^ m / m.factorial) -
      (Real.exp (-x) - ∑ m ∈ Finset.range 3, (-x) ^ m / m.factorial) := by
    norm_num [Finset.sum_range_succ, Nat.factorial, Real.sinh_eq]
    ring
  rw [hid]
  have htri := abs_sub
    (Real.exp x - ∑ m ∈ Finset.range 3, x ^ m / m.factorial)
    (Real.exp (-x) - ∑ m ∈ Finset.range 3, (-x) ^ m / m.factorial)
  norm_num [Nat.factorial, abs_neg] at hp hm
  nlinarith [pow_nonneg (abs_nonneg x) 3]

lemma root_tau_small {n : ℝ} (hn : 6 ≤ n) :
    0 < Real.log (2 * n + 1) / n ∧ Real.log (2 * n + 1) / n < 3 / 7 := by
  have hnpos : 0 < n := by linarith
  have hlpos : 0 < Real.log (2 * n + 1) := Real.log_pos (by linarith)
  have ht := log_tangent_at (2 * n + 1) 13 (by linarith) (by norm_num)
  constructor
  · exact div_pos hlpos hnpos
  · apply (div_lt_iff₀ hnpos).2
    linarith [log_thirteen_lt_eighteen_sevenths]

lemma root_tau_large {n : ℝ} (hn : 1000 ≤ n) :
    0 < Real.log (2 * n + 1) / n ∧ Real.log (2 * n + 1) / n < 1 / 125 := by
  have hnpos : 0 < n := by linarith
  have hlpos : 0 < Real.log (2 * n + 1) := Real.log_pos (by linarith)
  have ha := log_n_affine_1000 hn
  have hc := (log_n_width_shift (by linarith : 182 ≤ n)).2
  constructor
  · exact div_pos hlpos hnpos
  · apply (div_lt_iff₀ hnpos).2
    linarith

end UniversalScalar

namespace UniversalScalar

lemma log_successive_ratio_nonneg {n : ℝ} (hn : 0 < n) :
    0 ≤ Real.log ((n + 1) / n) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ hn).2
  linarith

theorem budget_upper_from_energy {n delta R F B C G : ℝ}
    (hn : 182 ≤ n) (hdelta : 0 ≤ delta)
    (hB : B ≤ Real.log n + 1 / (2 * n)) (hC : C ≤ 13 / 20)
    (hR : R ≤ ((n + 1) / 8 - 2) * B + (n + 1) * C)
    (hF : F ≤ 2 * B - Real.log 2)
    (henergy : G ≤ (R + F) / n - delta * Real.log ((n + 1) / n)) :
    G < Real.log n / 8 + 33 / 50 := by
  have hnpos : 0 < n := by linarith
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hratio := log_successive_ratio_nonneg hnpos
  have hneg := mul_nonneg hdelta hratio
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog2n := div_nonneg hlog2 hnpos.le
  have hpair : R + F ≤ ((n + 1) / 8) * B + (n + 1) * C - Real.log 2 := by
    nlinarith
  have hpairdiv := div_le_div_of_nonneg_right hpair hnpos.le
  have hscaleB : 0 ≤ (n + 1) / (8 * n) := by positivity
  have hscaleC : 0 ≤ (n + 1) / n := by positivity
  have hb := mul_le_mul_of_nonneg_left hB hscaleB
  have hc := mul_le_mul_of_nonneg_left hC hscaleC
  have hid0 :
      (((n + 1) / 8) * B + (n + 1) * C - Real.log 2) / n =
      ((n + 1) / (8 * n)) * B + ((n + 1) / n) * C - Real.log 2 / n := by
    field_simp
  rw [hid0] at hpairdiv
  have hupper :
      G ≤ ((n + 1) / (8 * n)) * (Real.log n + 1 / (2 * n)) +
        ((n + 1) / n) * (13 / 20) := by
    linarith
  have hid1 :
      ((n + 1) / (8 * n)) * (Real.log n + 1 / (2 * n)) +
        ((n + 1) / n) * (13 / 20) =
      Real.log n / 8 + 13 / 20 +
        (Real.log n / 8 + 13 / 20 + 1 / 16 + 1 / (16 * n)) / n := by
    field_simp
    ring
  rw [hid1] at hupper
  have he := actual_budget_error hn
  linarith

theorem small_support_upper_from_energy {n delta R F S A z G : ℝ}
    (hn : 1000 ≤ n) (hdelta : 0 ≤ delta)
    (hSglobal : S ≤ Real.log n / 10 + 97 / 100 + 1 / (10 * n))
    (hSfactor : S < 3 * A / 20 + z / 10 + 97 / 100)
    (hz : z ≤ 1 + A / 3)
    (hR : R ≤ (n + 1) * S) (hF : F ≤ 2 * Real.log n)
    (henergy : G ≤ (R + F) / n - delta * Real.log ((n + 1) / n)) :
    G < 11 * A / 60 + 109 / 100 := by
  have hnpos : 0 < n := by linarith
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hratio := log_successive_ratio_nonneg hnpos
  have hneg := mul_nonneg hdelta hratio
  have hpair : R + F ≤ (n + 1) * S + 2 * Real.log n := by linarith
  have hpairdiv := div_le_div_of_nonneg_right hpair hnpos.le
  have hid : ((n + 1) * S + 2 * Real.log n) / n =
      S + (S + 2 * Real.log n) / n := by
    field_simp
    ring
  rw [hid] at hpairdiv
  have hi : (1 : ℝ) / (10 * n) ≤ 1 / 100 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100)
      (show (100 : ℝ) ≤ 10 * n by nlinarith)
  have hs : S + 2 * Real.log n ≤ 21 * Real.log n / 10 + 1 := by linarith
  have hsdiv := div_le_div_of_nonneg_right hs hnpos.le
  have herr := actual_small_support_error hn
  have hG : G < S + 1 / 50 := by linarith
  linarith

theorem large_closure_from_resultants
    {n A delta R F B C S z : ℝ}
    (hn : 1000 ≤ n) (hA : 51 / 20 ≤ A)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1 / 2)
    (hAL : A < delta * Real.log (2 * n + 1))
    (hB : B ≤ Real.log n + 1 / (2 * n)) (hC : C ≤ 13 / 20)
    (hRbudget : R ≤ ((n + 1) / 8 - 2) * B + (n + 1) * C)
    (hFbudget : F ≤ 2 * B - Real.log 2)
    (hSglobal : S ≤ Real.log n / 10 + 97 / 100 + 1 / (10 * n))
    (hSfactor : S < 3 * A / 20 + z / 10 + 97 / 100)
    (hz : z ≤ 1 + A / 3)
    (hRsupport : R ≤ (n + 1) * S) (hFsupport : F ≤ 2 * Real.log n)
    (henergy : radialMoment (Real.log n) (Real.log (2 * n + 1)) A delta
      (Real.log (Real.log (2 * n + 1))) ≤
        (R + F) / n - delta * Real.log ((n + 1) / n)) : False := by
  obtain ⟨he, hL, hc, hm⟩ := large_log_hypotheses hn
  have hsmall := small_support_upper_from_energy hn hdelta0
    hSglobal hSfactor hz hRsupport hFsupport henergy
  have hbudget := budget_upper_from_energy
    (by linarith : 182 ≤ n) hdelta0 hB hC hRbudget hFbudget henergy
  exact large_closure (Real.log n) (Real.log (2 * n + 1)) A delta
    (Real.log (Real.log (2 * n + 1))) he hL hc hm hA hdelta1 hAL hsmall hbudget

theorem bridge_closure_from_resultants {n A delta R F B C : ℝ}
    (hn0 : 182 ≤ n) (hn1 : n < 1000) (hA : 51 / 20 ≤ A)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1 / 2)
    (hAL : A < delta * Real.log (2 * n + 1))
    (hB : B ≤ Real.log n + 1 / (2 * n)) (hC : C ≤ 13 / 20)
    (hRbudget : R ≤ ((n + 1) / 8 - 2) * B + (n + 1) * C)
    (hFbudget : F ≤ 2 * B - Real.log 2)
    (henergy : radialMoment (Real.log n) (Real.log (2 * n + 1) - 11 / 6) A delta
      (Real.log (Real.log (2 * n + 1) - 11 / 6)) ≤
        (R + F) / n - delta * Real.log ((n + 1) / n)) : False := by
  obtain ⟨he0, he1, hc0, hc1, hm0, hm1⟩ := bridge_log_hypotheses hn0 hn1
  have hbudget := budget_upper_from_energy hn0 hdelta0 hB hC hRbudget hFbudget henergy
  exact bridge_closure (Real.log n) (Real.log (2 * n + 1)) A delta
    (Real.log (Real.log (2 * n + 1) - 11 / 6))
    he0 he1 hc0 hc1 hA hdelta1 hAL hm0 hm1 hbudget

end UniversalScalar

open Polynomial
open scoped BigOperators

namespace UniversalScalar

lemma log_finite_positive_product {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 < u i) :
    Real.log (∏ i ∈ s, u i) = ∑ i ∈ s, Real.log (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hi0 := hu i (Finset.mem_insert_self i s)
      have ht : ∀ j ∈ s, 0 < u j := fun j hj => hu j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        Real.log_mul (ne_of_gt hi0) (ne_of_gt (Finset.prod_pos ht)), ih ht]

lemma root_product_norm_constant {d : ℕ} (g : ℂ[X]) (alpha : Fin d → ℂ)
    (hprod : g = ∏ i, (X - C (alpha i) : ℂ[X])) :
    ∏ i, ‖alpha i‖ = ‖g.coeff 0‖ := by
  classical
  have he := congrArg (fun f : ℂ[X] => f.eval 0) hprod
  rw [← Polynomial.coeff_zero_eq_eval_zero] at he
  have hc : g.coeff 0 = ∏ i, -alpha i := by
    simpa only [Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, zero_sub] using he
  have hn := congrArg (fun z : ℂ => ‖z‖) hc
  simpa only [norm_prod, norm_neg] using hn.symm

lemma integer_root_product_norm_constant {d : ℕ}
    (g : ℤ[X]) (alpha : Fin d → ℂ)
    (hprod : g.map (Int.castRingHom ℂ) = ∏ i, (X - C (alpha i) : ℂ[X])) :
    ∏ i, ‖alpha i‖ = |(g.coeff 0 : ℝ)| := by
  have h := root_product_norm_constant (g.map (Int.castRingHom ℂ)) alpha hprod
  have hc : ‖(g.map (Int.castRingHom ℂ)).coeff 0‖ = |(g.coeff 0 : ℝ)| := by
    simp only [Polynomial.coeff_map, Int.coe_castRingHom]
    exact Complex.norm_intCast (g.coeff 0)
  simpa only [hc] using h

lemma sum_root_logs {d : ℕ} (rho : Fin d → ℝ) {a : ℝ}
    (hrho : ∀ i, 0 < rho i) (hprod : ∏ i, rho i = a) :
    ∑ i, Real.log (rho i) = Real.log a := by
  have h := log_finite_positive_product Finset.univ rho (fun i _ => hrho i)
  rw [hprod] at h
  exact h.symm

lemma root_log_degree_constraint {d : ℕ} (hd : 0 < d)
    (rho : Fin d → ℝ) {a n L : ℝ}
    (hrho : ∀ i, 0 < rho i) (hprod : ∏ i, rho i = a)
    (hupper : ∀ i, Real.log (rho i) < L / n) :
    Real.log a < ((d : ℝ) / n) * L := by
  classical
  have hsum : (∑ i, Real.log (rho i)) < ∑ _i : Fin d, L / n := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (hupper i).le
    · exact ⟨⟨0, hd⟩, Finset.mem_univ _, hupper ⟨0, hd⟩⟩
  rw [sum_root_logs rho hrho hprod] at hsum
  have hid : (∑ _i : Fin d, L / n) = ((d : ℝ) / n) * L := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simpa only [hid] using hsum

lemma log_root_upper_from_power {n : ℕ} (hn : 0 < n) {rho B : ℝ}
    (hrho : 0 < rho) (hpow : rho ^ n < B) :
    Real.log rho < Real.log B / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := Real.log_lt_log (pow_pos hrho n) hpow
  rw [Real.log_pow] at hl
  apply (lt_div_iff₀ hnpos).2
  nlinarith

lemma radial_difference_sinh {rho : ℝ} (hrho : 0 < rho) :
    rho - rho⁻¹ = 2 * Real.sinh (Real.log rho) := by
  rw [Real.sinh_eq, Real.exp_log hrho, Real.exp_neg, Real.exp_log hrho]
  ring

lemma sinh_linear_envelope {t tau : ℝ}
    (ht0 : 0 ≤ t) (httau : t ≤ tau) (htau1 : tau ≤ 1) :
    2 * Real.sinh t ≤ (2 + tau ^ 2) * t := by
  have ht1 : t ≤ 1 := le_trans httau htau1
  have htau0 : 0 ≤ tau := le_trans ht0 httau
  have hrem := two_sinh_cubic_bound t (by rw [abs_of_nonneg ht0]; exact ht1)
  rw [abs_of_nonneg ht0] at hrem
  have hup := le_trans (le_abs_self (2 * Real.sinh t - 2 * t)) hrem
  have hsq : t ^ 2 ≤ tau ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr httau) (add_nonneg htau0 ht0)
    nlinarith
  have hcube := mul_le_mul_of_nonneg_right hsq ht0
  nlinarith

lemma J_bound_from_radial_sum {d : ℕ} (rho : Fin d → ℝ)
    {a J tau : ℝ} (ha : 0 ≤ a)
    (hrho : ∀ i, 1 ≤ rho i) (hprod : ∏ i, rho i = a)
    (hupper : ∀ i, Real.log (rho i) ≤ tau) (htau1 : tau ≤ 1)
    (hJ : |J| ≤ a * ∑ i, (rho i - (rho i)⁻¹)) :
    |J| ≤ (2 + tau ^ 2) * a * Real.log a := by
  have hpos : ∀ i, 0 < rho i := fun i => lt_of_lt_of_le zero_lt_one (hrho i)
  have hlog0 : ∀ i, 0 ≤ Real.log (rho i) := fun i => Real.log_nonneg (hrho i)
  have hp : ∀ i, rho i - (rho i)⁻¹ ≤ (2 + tau ^ 2) * Real.log (rho i) := by
    intro i
    rw [radial_difference_sinh (hpos i)]
    exact sinh_linear_envelope (hlog0 i) (hupper i) htau1
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin d))) => hp i)
  rw [← Finset.mul_sum, sum_root_logs rho hpos hprod] at hs
  have hm := mul_le_mul_of_nonneg_left hs ha
  nlinarith

lemma J_bound_from_radial_sum_strict {d : ℕ} (rho : Fin d → ℝ)
    {a J tau K : ℝ} (ha : 1 < a)
    (hrho : ∀ i, 1 ≤ rho i) (hprod : ∏ i, rho i = a)
    (hupper : ∀ i, Real.log (rho i) ≤ tau) (htau1 : tau ≤ 1)
    (hK : 2 + tau ^ 2 < K)
    (hJ : |J| ≤ a * ∑ i, (rho i - (rho i)⁻¹)) :
    |J| < K * a * Real.log a := by
  have hb := J_bound_from_radial_sum rho (by linarith : 0 ≤ a)
    hrho hprod hupper htau1 hJ
  have hp := mul_pos (show 0 < a by linarith) (Real.log_pos ha)
  have hk := mul_lt_mul_of_pos_right hK hp
  nlinarith

lemma quadratic_kernel_small {n : ℝ} (hn : 6 ≤ n) :
    2 + (Real.log (2 * n + 1) / n) ^ 2 < 107 / 49 := by
  obtain ⟨ht0, ht1⟩ := root_tau_small hn
  have hp := mul_pos
    (show 0 < 3 / 7 - Real.log (2 * n + 1) / n by linarith)
    (show 0 < 3 / 7 + Real.log (2 * n + 1) / n by linarith)
  nlinarith

lemma quadratic_kernel_large {n : ℝ} (hn : 1000 ≤ n) :
    2 + (Real.log (2 * n + 1) / n) ^ 2 < 201 / 100 := by
  obtain ⟨ht0, ht1⟩ := root_tau_large hn
  have hp := mul_pos
    (show 0 < 1 / 125 - Real.log (2 * n + 1) / n by linarith)
    (show 0 < 1 / 125 + Real.log (2 * n + 1) / n by linarith)
  nlinarith

theorem J_small_root_bound {d : ℕ} (rho : Fin d → ℝ)
    {n a J : ℝ} (hn : 6 ≤ n) (ha : 1 < a)
    (hrho : ∀ i, 1 ≤ rho i) (hprod : ∏ i, rho i = a)
    (hupper : ∀ i, Real.log (rho i) < Real.log (2 * n + 1) / n)
    (hJ : |J| ≤ a * ∑ i, (rho i - (rho i)⁻¹)) :
    |J| < (107 / 49) * a * Real.log a := by
  exact J_bound_from_radial_sum_strict rho ha hrho hprod (fun i => (hupper i).le)
    (by linarith [(root_tau_small hn).2]) (quadratic_kernel_small hn) hJ

end UniversalScalar

namespace UniversalScalar

lemma abs_re_root_difference_le {z : ℂ} (hz : 1 ≤ ‖z‖) :
    |(z - z⁻¹).re| ≤ ‖z‖ - ‖z‖⁻¹ := by
  have hnorm : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz
  have hnorm0 : ‖z‖ ≠ 0 := ne_of_gt hnorm
  have hsq : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
  have hinv : (1 : ℝ) / ‖z‖ ^ 2 ≤ 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsq
    simpa using h
  have hfactor : 0 ≤ 1 - 1 / ‖z‖ ^ 2 := by linarith
  have hid : (z - z⁻¹).re = z.re * (1 - 1 / ‖z‖ ^ 2) := by
    rw [Complex.sub_re, Complex.inv_re, Complex.normSq_eq_norm_sq]
    ring
  rw [hid, abs_mul, abs_of_nonneg hfactor]
  calc
    |z.re| * (1 - 1 / ‖z‖ ^ 2) ≤ ‖z‖ * (1 - 1 / ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) hfactor
    _ = ‖z‖ - ‖z‖⁻¹ := by field_simp

theorem J_radial_bound_from_complex_trace {d : ℕ} (alpha : Fin d → ℂ)
    {a J : ℝ} (ha : 0 ≤ a) (hroot : ∀ i, 1 ≤ ‖alpha i‖)
    (hJ : (J : ℂ) = (a : ℂ) * ∑ i, (alpha i - (alpha i)⁻¹)) :
    |J| ≤ a * ∑ i, (‖alpha i‖ - ‖alpha i‖⁻¹) := by
  classical
  have hreal : J = a * ∑ i, (alpha i - (alpha i)⁻¹).re := by
    have h := congrArg Complex.re hJ
    simpa only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.re_sum, zero_mul, sub_zero] using h
  have hsum : |∑ i, (alpha i - (alpha i)⁻¹).re| ≤
      ∑ i, |(alpha i - (alpha i)⁻¹).re| := by
    simpa only [Real.norm_eq_abs] using
      (norm_sum_le Finset.univ (fun i : Fin d => (alpha i - (alpha i)⁻¹).re))
  have hpoint := Finset.sum_le_sum
    (fun i (_hi : i ∈ (Finset.univ : Finset (Fin d))) =>
      abs_re_root_difference_le (hroot i))
  rw [hreal, abs_mul, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (le_trans hsum hpoint) ha

end UniversalScalar

open Polynomial
open scoped BigOperators

namespace UniversalScalar

lemma polynomial_coeff_one_mul (P Q : ℂ[X]) :
    (P * Q).coeff 1 = P.coeff 0 * Q.coeff 1 + P.coeff 1 * Q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

lemma inverse_linear_coeff_zero (z : ℂ) :
    (1 - C z * X : ℂ[X]).coeff 0 = 1 := by simp

lemma inverse_linear_coeff_one (z : ℂ) :
    (1 - C z * X : ℂ[X]).coeff 1 = -z := by norm_num [Polynomial.coeff_one]

lemma inverse_linear_product_coeff_zero {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    (∏ i ∈ s, (1 - C (z i) * X : ℂ[X])).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [Polynomial.eval_prod]

lemma inverse_linear_product_coeff_one {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    (∏ i ∈ s, (1 - C (z i) * X : ℂ[X])).coeff 1 = -∑ i ∈ s, z i := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num [Polynomial.coeff_one]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, polynomial_coeff_one_mul,
        inverse_linear_coeff_zero, inverse_linear_coeff_one,
        inverse_linear_product_coeff_zero, ih, Finset.sum_insert hi]
      ring

lemma root_linear_reverse (z : ℂ) :
    (X - C z : ℂ[X]).reverse = 1 - C z * X := by
  simp [Polynomial.reverse]

lemma complete_root_product_reverse {ι : Type*} (s : Finset ι) (alpha : ι → ℂ) :
    (∏ i ∈ s, (X - C (alpha i) : ℂ[X])).reverse =
      ∏ i ∈ s, (1 - C (alpha i) * X : ℂ[X]) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.reverse]
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Polynomial.reverse_mul_of_domain,
        root_linear_reverse, ih]

lemma scaled_inverse_linear (z : ℂ) (hz : z ≠ 0) :
    (X - C z : ℂ[X]) = C (-z) * (1 - C z⁻¹ * X) := by
  have hm : (C (-z) : ℂ[X]) * C z⁻¹ = -1 := by
    rw [← Polynomial.C_mul]
    simp [hz]
  calc
    (X - C z : ℂ[X]) = C (-z) - (-1) * X := by simp; ring
    _ = C (-z) - (C (-z) * C z⁻¹) * X := by rw [hm]
    _ = C (-z) * (1 - C z⁻¹ * X) := by ring

lemma complete_root_product_normalized {d : ℕ} (g : ℂ[X]) (alpha : Fin d → ℂ)
    (hprod : g = ∏ i, (X - C (alpha i) : ℂ[X]))
    (hne : ∀ i, alpha i ≠ 0) :
    g.coeff 0 ≠ 0 ∧
      C ((g.coeff 0)⁻¹) * g =
        ∏ i, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
  classical
  have hconstant : g.coeff 0 = ∏ i, -(alpha i) := by
    have he := congrArg (fun P : ℂ[X] => P.eval 0) hprod
    simpa [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod] using he
  have ha : g.coeff 0 ≠ 0 := by
    rw [hconstant]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => neg_ne_zero.mpr (hne i))
  have hscaled : g = C (g.coeff 0) *
      ∏ i, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
    calc
      g = ∏ i, (X - C (alpha i) : ℂ[X]) := hprod
      _ = ∏ i, (C (-(alpha i)) * (1 - C ((alpha i)⁻¹) * X) : ℂ[X]) := by
        apply Finset.prod_congr rfl
        intro i _
        exact scaled_inverse_linear (alpha i) (hne i)
      _ = (∏ i, (C (-(alpha i)) : ℂ[X])) *
          ∏ i, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := Finset.prod_mul_distrib
      _ = C (∏ i, -(alpha i)) *
          ∏ i, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by simp only [map_prod]
      _ = C (g.coeff 0) *
          ∏ i, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by rw [← hconstant]
  refine ⟨ha, ?_⟩
  calc
    C ((g.coeff 0)⁻¹) * g = C ((g.coeff 0)⁻¹) *
        (C (g.coeff 0) * ∏ i, (1 - C ((alpha i)⁻¹) * X : ℂ[X])) :=
      congrArg (fun P : ℂ[X] => C ((g.coeff 0)⁻¹) * P) hscaled
    _ = (C ((g.coeff 0)⁻¹) * C (g.coeff 0)) *
        ∏ i, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by ring
    _ = ∏ i, (1 - C ((alpha i)⁻¹) * X : ℂ[X]) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1, one_mul]

theorem J_trace_reverse_coefficient {d : ℕ} (g : ℂ[X]) (alpha : Fin d → ℂ)
    (hprod : g = ∏ i, (X - C (alpha i) : ℂ[X]))
    (hne : ∀ i, alpha i ≠ 0) :
    g.coeff 1 - g.coeff 0 * g.reverse.coeff 1 =
      g.coeff 0 * ∑ i, (alpha i - (alpha i)⁻¹) := by
  obtain ⟨ha, hnorm⟩ := complete_root_product_normalized g alpha hprod hne
  have hrev : g.reverse = ∏ i, (1 - C (alpha i) * X : ℂ[X]) := by
    rw [hprod]
    exact complete_root_product_reverse Finset.univ alpha
  have hr : g.reverse.coeff 1 = -∑ i, alpha i := by
    rw [hrev]
    exact inverse_linear_product_coeff_one Finset.univ alpha
  have hi : (g.coeff 0)⁻¹ * g.coeff 1 = -∑ i, (alpha i)⁻¹ := by
    have hc := congrArg (fun P : ℂ[X] => P.coeff 1) hnorm
    simpa only [Polynomial.coeff_C_mul, inverse_linear_product_coeff_one] using hc
  have hlin : g.coeff 1 = -(g.coeff 0) * ∑ i, (alpha i)⁻¹ := by
    have hm := congrArg (fun z : ℂ => g.coeff 0 * z) hi
    simpa only [← mul_assoc, mul_inv_cancel₀ ha, one_mul, mul_neg, neg_mul] using hm
  rw [hr, hlin, Finset.sum_sub_distrib]
  ring

lemma reverse_coefficient_one (g : ℂ[X]) (hd : 0 < g.natDegree) :
    g.reverse.coeff 1 = g.coeff (g.natDegree - 1) := by
  have h1 : 1 ≤ g.natDegree := by omega
  rw [Polynomial.coeff_reverse]
  change g.coeff (if 1 ≤ g.natDegree then g.natDegree - 1 else 1) = _
  rw [if_pos h1]

theorem J_trace_penultimate_coefficient {d : ℕ} (g : ℂ[X]) (alpha : Fin d → ℂ)
    (hd : 0 < g.natDegree)
    (hprod : g = ∏ i, (X - C (alpha i) : ℂ[X]))
    (hne : ∀ i, alpha i ≠ 0) :
    g.coeff 1 - g.coeff 0 * g.coeff (g.natDegree - 1) =
      g.coeff 0 * ∑ i, (alpha i - (alpha i)⁻¹) := by
  have h := J_trace_reverse_coefficient g alpha hprod hne
  rw [reverse_coefficient_one g hd] at h
  exact h

end UniversalScalar

namespace UniversalScalar

lemma log_twelve_lt_five_halves : Real.log (12 : ℝ) < 5 / 2 := by
  have hid : Real.log (12 : ℝ) = Real.log 3 + 2 * Real.log 2 := by
    rw [show (12 : ℝ) = 3 * 2 ^ (2 : ℕ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [hid]
  linarith [log_three_lt, log_two_rational_bounds.2]

end UniversalScalar

namespace UniversalIrreducibility

lemma log_product_identity {d : ℕ} {n D R a F : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hR : 0 < R) (ha : 0 < a) (hF : 0 < F)
    (hprod : D * R * a * F = (n * (n + 1)) ^ d) :
    Real.log D + Real.log R + Real.log a + Real.log F =
      (d : ℝ) * (Real.log n + Real.log (n + 1)) := by
  have hh := congrArg Real.log hprod
  simpa only [Real.log_mul (ne_of_gt (mul_pos (mul_pos hD hR) ha)) (ne_of_gt hF),
    Real.log_mul (ne_of_gt (mul_pos hD hR)) (ne_of_gt ha),
    Real.log_mul (ne_of_gt hD) (ne_of_gt hR), Real.log_pow,
    Real.log_mul (ne_of_gt hn) (ne_of_gt (show 0 < n + 1 by linarith))] using hh

lemma energy_inequality_from_discriminant {n d A D R F w : ℝ}
    (hn : 0 < n) (hw : 0 < w)
    (hidentity : D + R + A + F = d * (Real.log n + Real.log (n + 1)))
    (hdisc : D ≤ (d - 1) * A + (w / n) * d ^ 2 / 2 - d * Real.log (w / n)) :
    UniversalScalar.radialMoment (Real.log n) w A (d / n) (Real.log w) ≤
      (R + F) / n - (d / n) * Real.log ((n + 1) / n) := by
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hN0 : n + 1 ≠ 0 := by linarith
  rw [Real.log_div (ne_of_gt hw) hn0] at hdisc
  have hid :
      (UniversalScalar.radialMoment (Real.log n) w A (d / n) (Real.log w) +
        (d / n) * Real.log ((n + 1) / n)) * n =
      d * (Real.log (n + 1) - A + Real.log w) - (w / n) * d ^ 2 / 2 := by
    rw [Real.log_div hN0 hn0]
    unfold UniversalScalar.radialMoment
    field_simp
    ring
  apply (le_sub_iff_add_le).2
  apply (le_div_iff₀ hn).2
  rw [hid]
  nlinarith

end UniversalIrreducibility

namespace EventualIrreducibility.UniversalPointNorm

open Polynomial

lemma root_product_signed_point_norm
    {K : Type*} [Field K] {d : ℕ} (alpha : Fin d → K)
    (P : K[X]) (n : ℕ) (N r : K)
    (hprod : P = ∏ i, (X - C (alpha i) : K[X]))
    (hpower : ∀ i, alpha i ^ (n + 1) = N * (alpha i - r)) :
    (-1 : K) ^ (n * d) * (P.coeff 0) ^ (n + 1) = N ^ d * P.eval r := by
  classical
  have hzero : P.coeff 0 = (-1 : K) ^ d * ∏ i, alpha i := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hprod, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    rw [Finset.prod_neg]
    simp
  have hpoint : P.eval r = (-1 : K) ^ d * ∏ i, (alpha i - r) := by
    rw [hprod, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hterm (i : Fin d) : r - alpha i = (-1 : K) * (alpha i - r) := by ring
    simp_rw [hterm]
    rw [Finset.prod_mul_distrib]
    simp
  have hpowers : (∏ i, alpha i) ^ (n + 1) = N ^ d * ∏ i, (alpha i - r) := by
    rw [← Finset.prod_pow]
    calc
      (∏ i, alpha i ^ (n + 1)) = ∏ i, N * (alpha i - r) :=
        Finset.prod_congr rfl (fun i _ => hpower i)
      _ = N ^ d * ∏ i, (alpha i - r) := by rw [Finset.prod_mul_distrib]; simp
  have hsign : (-1 : K) ^ (n * d) * ((-1 : K) ^ d) ^ (n + 1) = (-1 : K) ^ d := by
    rw [← pow_mul, ← pow_add]
    have hexp : n * d + d * (n + 1) = 2 * (n * d) + d := by ring
    rw [hexp, pow_add, pow_mul]
    norm_num
  calc
    (-1 : K) ^ (n * d) * (P.coeff 0) ^ (n + 1) =
        ((-1 : K) ^ (n * d) * ((-1 : K) ^ d) ^ (n + 1)) *
          (∏ i, alpha i) ^ (n + 1) := by rw [hzero, mul_pow]; ring
    _ = (-1 : K) ^ d * (N ^ d * ∏ i, (alpha i - r)) := by rw [hsign, hpowers]
    _ = N ^ d * P.eval r := by rw [hpoint]; ring

lemma eval_real_to_complex (P : ℤ[X]) (x : ℝ) :
    (((P.map (Int.castRingHom ℝ)).eval x : ℝ) : ℂ) =
      (P.map (Int.castRingHom ℂ)).eval (x : ℂ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial j a => simp

lemma even_of_signed_positive {k : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : (-1 : ℝ) ^ k * a = b) : Even k := by
  by_contra hne
  have hodd : Odd k := Nat.not_even_iff_odd.mp hne
  rw [hodd.neg_one_pow] at h
  linarith

end EventualIrreducibility.UniversalPointNorm

namespace EventualIrreducibility

open Filter Polynomial

lemma FactorSeries.eval_real_pos {n : ℕ} (s : FactorSeries n)
    (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < (s.factor.map (Int.castRingHom ℝ)).eval x := by
  let G : ℝ[X] := s.factor.map (Int.castRingHom ℝ)
  have hG : G.Monic := s.monic.map _
  have hd : 0 < G.natDegree := by
    dsimp only [G]
    rw [s.monic.natDegree_map]
    exact s.degree_pos
  have hlim : Tendsto (fun t : ℝ => G.eval t) atTop atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg G
      (Polynomial.natDegree_pos_iff_degree_pos.mp hd) (by rw [hG.leadingCoeff]; norm_num)
  exact FactorPositive.eval_pos_of_dvd_of_eventually_pos (real_eval_fInt_pos n hn)
    (Polynomial.map_dvd (Int.castRingHom ℝ) s.divides)
    (hlim.eventually (eventually_gt_atTop (0 : ℝ))) hx

theorem FactorSeries.signed_point_norm_complex {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) :
    (-1 : ℂ) ^ (n * s.factor.natDegree) * (s.factor.coeff 0 : ℂ) ^ (n + 1) =
      ((n : ℂ) + 1) ^ s.factor.natDegree *
        (s.factor.map (Int.castRingHom ℂ)).eval ((n : ℂ) / ((n : ℂ) + 1)) := by
  classical
  obtain ⟨d, alpha, hd, -, hprod, -⟩ := s.exists_root_product_identity hn
  have hroot (i : Fin d) : ((fInt n).map (Int.castRingHom ℂ)).eval (alpha i) = 0 := by
    apply RootGeometry.root_of_mapped_factor s
    rw [hprod, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hN : (n : ℂ) + 1 ≠ 0 := by
    have hR : (n : ℝ) + 1 ≠ 0 := by positivity
    exact_mod_cast hR
  have hpower (i : Fin d) : alpha i ^ (n + 1) =
      ((n : ℂ) + 1) * (alpha i - (n : ℂ) / ((n : ℂ) + 1)) := by
    rw [mul_sub, mul_div_cancel₀ _ hN]
    exact UpperSector.root_trinomial_eq (hroot i)
  have h := UniversalPointNorm.root_product_signed_point_norm alpha
    (s.factor.map (Int.castRingHom ℂ)) n ((n : ℂ) + 1)
    ((n : ℂ) / ((n : ℂ) + 1)) hprod hpower
  simpa only [hd, Polynomial.coeff_map, Int.coe_castRingHom] using h

theorem FactorSeries.signed_point_norm_real {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) :
    (-1 : ℝ) ^ (n * s.factor.natDegree) * (s.factor.coeff 0 : ℝ) ^ (n + 1) =
      ((n : ℝ) + 1) ^ s.factor.natDegree *
        (s.factor.map (Int.castRingHom ℝ)).eval ((n : ℝ) / ((n : ℝ) + 1)) := by
  apply Complex.ofReal_injective
  push_cast
  rw [UniversalPointNorm.eval_real_to_complex]
  push_cast
  exact s.signed_point_norm_complex hn

theorem FactorSeries.even_mul_degree {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) : Even (n * s.factor.natDegree) := by
  have ha : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by exact_mod_cast s.constant_pos hn
  have hpoint : 0 < (s.factor.map (Int.castRingHom ℝ)).eval
      ((n : ℝ) / ((n : ℝ) + 1)) := s.eval_real_pos hn (by positivity)
  exact UniversalPointNorm.even_of_signed_positive (pow_pos ha (n + 1))
    (mul_pos (by positivity) hpoint) (s.signed_point_norm_real hn)

theorem FactorSeries.point_norm_real {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) :
    (s.factor.coeff 0 : ℝ) ^ (n + 1) =
      ((n : ℝ) + 1) ^ s.factor.natDegree *
        (s.factor.map (Int.castRingHom ℝ)).eval ((n : ℝ) / ((n : ℝ) + 1)) := by
  simpa only [(s.even_mul_degree hn).neg_one_pow, one_mul] using s.signed_point_norm_real hn

end EventualIrreducibility

open Polynomial
open scoped BigOperators

namespace UniversalScalar

lemma finite_product_strict_of_all {ι : Type*} (S : Finset ι)
    (hS : S.Nonempty) (f g : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) (hfg : ∀ i ∈ S, f i < g i) :
    (∏ i ∈ S, f i) < ∏ i ∈ S, g i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hS
  | @insert i S hi _ih =>
    have hfi := hf i (Finset.mem_insert_self i S)
    have hfgi := hfg i (Finset.mem_insert_self i S)
    have hft : ∀ j ∈ S, 0 < f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hfgt : ∀ j ∈ S, f j ≤ g j :=
      fun j hj => (hfg j (Finset.mem_insert_of_mem hj)).le
    have ht : (∏ j ∈ S, f j) ≤ ∏ j ∈ S, g j :=
      Finset.prod_le_prod (fun j hj => (hft j hj).le) hfgt
    have htp : 0 < ∏ j ∈ S, f j := Finset.prod_pos hft
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hfgi htp)
      (mul_le_mul_of_nonneg_left ht (lt_trans hfi hfgi).le)

lemma integer_real_eval (P : ℤ[X]) (x : ℤ) :
    (P.map (Int.castRingHom ℝ)).eval (x : ℝ) = ((P.eval x : ℤ) : ℝ) := by
  rw [Polynomial.eval_map]
  change P.eval₂ (Int.castRingHom ℝ) ((Int.castRingHom ℝ) x) = _
  rw [Polynomial.eval₂_hom]
  rfl

lemma complete_root_product_eval_norm {d : ℕ} (g : ℤ[X])
    (alpha : Fin d → ℂ)
    (hprod : g.map (Int.castRingHom ℂ) = ∏ i, (X - C (alpha i) : ℂ[X]))
    (x : ℝ) :
    (∏ i, ‖alpha i - (x : ℂ)‖) = |(g.map (Int.castRingHom ℝ)).eval x| := by
  have he := congrArg (fun P : ℂ[X] => P.eval (x : ℂ)) hprod
  have hn := congrArg (fun z : ℂ => ‖z‖) he
  rw [← EventualIrreducibility.UniversalPointNorm.eval_real_to_complex] at hn
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, norm_prod, Complex.norm_real, Real.norm_eq_abs] at hn
  calc
    (∏ i, ‖alpha i - (x : ℂ)‖) = ∏ i, ‖(x : ℂ) - alpha i‖ :=
      Finset.prod_congr rfl (fun i _ => norm_sub_rev _ _)
    _ = |(g.map (Int.castRingHom ℝ)).eval x| := hn.symm

theorem metric_eval_square_product {d : ℕ} (hd : 0 < d)
    (g : ℤ[X]) (alpha : Fin d → ℂ)
    (hprod : g.map (Int.castRingHom ℂ) = ∏ i, (X - C (alpha i) : ℂ[X]))
    (hroot : ∀ i, 1 < ‖alpha i‖) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hevalr : 0 < (g.map (Int.castRingHom ℝ)).eval r)
    (heval1 : 0 < (g.map (Int.castRingHom ℝ)).eval 1) :
    r ^ d * ((g.map (Int.castRingHom ℝ)).eval 1) ^ 2 <
      ((g.map (Int.castRingHom ℝ)).eval r) ^ 2 := by
  classical
  have hone (i : Fin d) : alpha i - 1 ≠ 0 := by
    intro hz
    have he : alpha i = 1 := sub_eq_zero.mp hz
    have hm := hroot i
    simp only [he, norm_one] at hm
    exact lt_irrefl 1 hm
  have hleft (i : Fin d) : 0 < r * ‖alpha i - 1‖ ^ 2 :=
    mul_pos hr (sq_pos_of_pos (norm_pos_iff.mpr (hone i)))
  have hpoint (i : Fin d) : r * ‖alpha i - 1‖ ^ 2 < ‖alpha i - (r : ℂ)‖ ^ 2 :=
    UniversalIrreducibility.norm_metric_sq_lt (hroot i) hr1
  have hp := finite_product_strict_of_all (Finset.univ : Finset (Fin d))
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    (fun i => r * ‖alpha i - 1‖ ^ 2) (fun i => ‖alpha i - (r : ℂ)‖ ^ 2)
    (fun i _ => hleft i) (fun i _ => hpoint i)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow] at hp
  have hnorm1 := complete_root_product_eval_norm g alpha hprod 1
  simp only [Complex.ofReal_one] at hnorm1
  rw [hnorm1, complete_root_product_eval_norm g alpha hprod r,
    abs_of_pos heval1, abs_of_pos hevalr] at hp
  exact hp

lemma metric_power_scalar {n a F B : ℝ} {d m : ℕ}
    (hn : 0 < n) (ha : 0 < a) (hF : 0 < F) (_hB : 0 < B)
    (hpoint : a ^ m = (n + 1) ^ d * B)
    (hmetric : (n / (n + 1)) ^ d * F ^ 2 < B ^ 2) :
    (Real.sqrt (n * (n + 1))) ^ d * F < a ^ m := by
  have hN : 0 < n + 1 := by linarith
  have hN0 : n + 1 ≠ 0 := ne_of_gt hN
  have hscale : 0 < ((n + 1) ^ d) ^ 2 := by positivity
  have hm := mul_lt_mul_of_pos_left hmetric hscale
  have hswap : ((n + 1) ^ d) ^ 2 = ((n + 1) ^ 2) ^ d := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm d 2]
  have hrad : (n + 1) ^ 2 * (n / (n + 1)) = n * (n + 1) := by
    field_simp
  have hleft : ((n + 1) ^ d) ^ 2 * ((n / (n + 1)) ^ d * F ^ 2) =
      (n * (n + 1)) ^ d * F ^ 2 := by
    rw [hswap, ← mul_assoc, ← mul_pow, hrad]
  have hright : ((n + 1) ^ d) ^ 2 * B ^ 2 = (a ^ m) ^ 2 := by
    rw [← mul_pow, ← hpoint]
  rw [hleft, hright] at hm
  have hsqrt : ((Real.sqrt (n * (n + 1))) ^ d * F) ^ 2 =
      (n * (n + 1)) ^ d * F ^ 2 := by
    rw [mul_pow]
    have hsw : ((Real.sqrt (n * (n + 1))) ^ d) ^ 2 =
        ((Real.sqrt (n * (n + 1))) ^ 2) ^ d := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm d 2]
    rw [hsw, Real.sq_sqrt (by positivity)]
  rw [← hsqrt] at hm
  have hapos : 0 < a ^ m := pow_pos ha m
  have htarget : 0 ≤ Real.sqrt (n * (n + 1)) ^ d * F := by positivity
  nlinarith

end UniversalScalar

namespace EventualIrreducibility

theorem FactorSeries.eval_one_real_ge_one {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) : (1 : ℝ) ≤ ((s.factor.eval 1 : ℤ) : ℝ) := by
  have hpos := s.eval_real_pos hn (x := 1) (by norm_num)
  have he := UniversalScalar.integer_real_eval s.factor 1
  simp only [Int.cast_one] at he
  rw [he] at hpos
  have hpZ : (0 : ℤ) < s.factor.eval 1 := by exact_mod_cast hpos
  have hpZ1 : (1 : ℤ) ≤ s.factor.eval 1 := by omega
  exact_mod_cast hpZ1

theorem FactorSeries.constant_norm_metric_with_eval {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) :
    (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) ^ s.factor.natDegree *
        ((s.factor.eval 1 : ℤ) : ℝ) < (s.factor.coeff 0 : ℝ) ^ (n + 1) := by
  obtain ⟨d, alpha, hd, _hne, hprod, _hquot⟩ := s.exists_root_product_identity hn
  subst d
  have hroot (i : Fin s.factor.natDegree) : 1 < ‖alpha i‖ := by
    apply (RootGeometry.factor_root_annulus s hn ?_).1
    rw [hprod, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hr : 0 < (n : ℝ) / ((n : ℝ) + 1) := div_pos hnR hN
  have hr1 : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
    (div_lt_one hN).2 (by linarith)
  have hevalr := s.eval_real_pos hn hr.le
  have heval1 := s.eval_real_pos hn (x := 1) (by norm_num)
  have hm := UniversalScalar.metric_eval_square_product s.degree_pos s.factor alpha hprod
    hroot hr hr1 hevalr heval1
  have ha : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by exact_mod_cast s.constant_pos hn
  have hb := UniversalScalar.metric_power_scalar hnR ha heval1 hevalr
    (s.point_norm_real hn) hm
  have he := UniversalScalar.integer_real_eval s.factor 1
  simp only [Int.cast_one] at he
  simpa only [he] using hb

theorem FactorSeries.constant_norm_metric {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) :
    (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) ^ s.factor.natDegree <
      (s.factor.coeff 0 : ℝ) ^ (n + 1) := by
  have heval := s.eval_one_real_ge_one hn
  have hle := mul_le_mul_of_nonneg_left heval
    (show 0 ≤ (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) ^ s.factor.natDegree by positivity)
  rw [mul_one] at hle
  exact lt_of_le_of_lt hle (s.constant_norm_metric_with_eval hn)

end EventualIrreducibility

namespace EventualIrreducibility.UniversalInnerRadius

open Real
open scoped ComplexConjugate

lemma coordinate_norm_square {w : ℂ} {N q theta : ℝ}
    (hre : w.re = N - q * Real.cos theta) (him : w.im = q * Real.sin theta) :
    ‖w‖ ^ 2 = N ^ 2 + q ^ 2 - 2 * N * q * Real.cos theta := by
  rw [RootGeometry.complex_sq_norm, hre, him]
  linear_combination q ^ 2 * (Real.sin_sq_add_cos_sq theta)

lemma ray_distance_lower {w : ℂ} {N q theta : ℝ}
    (hN : 0 ≤ N) (hsin : 0 ≤ Real.sin theta)
    (hre : w.re = N - q * Real.cos theta) (him : w.im = q * Real.sin theta) :
    N * Real.sin theta ≤ ‖w‖ := by
  have hsq : ‖w‖ ^ 2 - (N * Real.sin theta) ^ 2 = (q - N * Real.cos theta) ^ 2 := by
    rw [RootGeometry.complex_sq_norm, hre, him]
    linear_combination (q ^ 2 - N ^ 2) * (Real.sin_sq_add_cos_sq theta)
  have hp : 0 ≤ N * Real.sin theta := mul_nonneg hN hsin
  nlinarith [sq_nonneg (q - N * Real.cos theta), norm_nonneg w]

lemma obtuse_distance_strict {w : ℂ} {N q theta : ℝ}
    (hN : 0 ≤ N) (hq : 0 < q) (hcos : Real.cos theta ≤ 0)
    (hre : w.re = N - q * Real.cos theta) (him : w.im = q * Real.sin theta) :
    N < ‖w‖ := by
  have hs := coordinate_norm_square hre him
  have hcross : 0 ≤ -(2 * N * q * Real.cos theta) := by
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * N * q) hcos
    linarith
  nlinarith [sq_pos_of_pos hq, norm_nonneg w]

lemma pi_rational_bounds : (157 / 50 : ℝ) < π ∧ π < 63 / 20 := by
  constructor
  · convert Real.pi_gt_d2 using 1 ; norm_num
  · convert Real.pi_lt_d2 using 1 ; norm_num

lemma two_pi_lt_successor_mul_sin {x : ℝ} (hx : 8 ≤ x) :
    2 * π < (x + 1) * Real.sin (2 * π / x) := by
  have hx0 : 0 < x := by linarith
  have hp0 := Real.pi_pos
  have hp := pi_rational_bounds.2
  have hpiSq : 2 * π ^ 2 / 3 < 64 / 9 := by nlinarith
  have hxSq : (64 / 9 : ℝ) * (x + 1) ≤ x ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 8)
      (by linarith : 0 ≤ x + 8 - 64 / 9)]
  have hcore : 0 < 3 * x ^ 2 - 2 * π ^ 2 * (x + 1) := by
    have hmul := mul_lt_mul_of_pos_right hpiSq (by linarith : 0 < x + 1)
    nlinarith
  have hpoly : 2 * π < (x + 1) * (2 * π / x - (2 * π / x) ^ 3 / 6) := by
    have hid : (x + 1) * (2 * π / x - (2 * π / x) ^ 3 / 6) - 2 * π =
        (2 * π / (3 * x ^ 3)) * (3 * x ^ 2 - 2 * π ^ 2 * (x + 1)) := by
      field_simp
      ring
    have hpos : 0 < (2 * π / (3 * x ^ 3)) *
        (3 * x ^ 2 - 2 * π ^ 2 * (x + 1)) :=
      mul_pos (by positivity) hcore
    linarith
  have hsin := Real.sin_gt_sub_cube (div_pos (by positivity : 0 < 2 * π) hx0)
  exact lt_trans hpoly (mul_lt_mul_of_pos_left hsin (by linarith))

lemma theta_lower_of_actual_upper_root
    {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0)
    (him : 0 < z.im) : 2 * π / (n : ℝ) < Complex.arg z := by
  obtain ⟨k, hk, -, hmem⟩ := UpperSector.exists_nat_sector_of_fInt_root hn hf him
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hnum : 2 * π ≤ UpperSector.sectorOffset k := by
    dsimp [UpperSector.sectorOffset]
    nlinarith [Real.pi_pos]
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hnum hnR.le) hmem.1

lemma actual_power_coordinates
    {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) :
    (z ^ n).re = ((n : ℝ) + 1) - ((n : ℝ) / ‖z‖) * Real.cos (Complex.arg z) ∧
      (z ^ n).im = ((n : ℝ) / ‖z‖) * Real.sin (Complex.arg z) := by
  have hrho : 0 < ‖z‖ := lt_trans zero_lt_one (RootGeometry.one_lt_norm_root hn hf)
  exact SectorReconstruction.power_coordinates_of_root hrho
    (UpperSector.polar_norm_arg z) (UpperSector.root_trinomial_eq hf)

lemma upper_root_power_gt_four
    {n : ℕ} (hn : 3 ≤ n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0)
    (him : 0 < z.im) : 4 < ‖z‖ ^ n := by
  have hn0 : 0 < n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hrho : 0 < ‖z‖ := lt_trans zero_lt_one (RootGeometry.one_lt_norm_root hn0 hf)
  obtain ⟨htheta, htheta_pi⟩ := UpperSector.arg_mem_upper_half him
  obtain ⟨hre, himcoord⟩ := actual_power_coordinates hn0 hf
  by_cases hacute : Complex.arg z < π / 2
  · have hlo := theta_lower_of_actual_upper_root hn0 hf him
    have hchord := Real.mul_le_sin htheta.le hacute.le
    have hquot : 4 / (n : ℝ) < (2 / π) * Complex.arg z := by
      have hmul := (div_lt_iff₀ hnpos).mp hlo
      apply (div_lt_iff₀ hnpos).2
      have hp0 := Real.pi_pos
      field_simp
      nlinarith
    have hsin : 4 / (n : ℝ) < Real.sin (Complex.arg z) := lt_of_lt_of_le hquot hchord
    have hray := ray_distance_lower (by positivity : 0 ≤ (n : ℝ) + 1)
      (Real.sin_pos_of_pos_of_lt_pi htheta htheta_pi).le hre himcoord
    have hmul := mul_lt_mul_of_pos_left hsin (by positivity : 0 < (n : ℝ) + 1)
    have hfour : 4 < ((n : ℝ) + 1) * (4 / (n : ℝ)) := by
      rw [← mul_div_assoc]
      apply (lt_div_iff₀ hnpos).2
        (show 4 * (n : ℝ) < ((n : ℝ) + 1) * 4 by linarith)
    rw [norm_pow] at hray
    linarith
  · have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hacute)
      (by linarith [Real.pi_pos] : Complex.arg z ≤ π + π / 2)
    have hlarge := obtuse_distance_strict (by positivity : 0 ≤ (n : ℝ) + 1)
      (div_pos hnpos hrho) hcos hre himcoord
    rw [norm_pow] at hlarge
    linarith

lemma upper_root_power_gt_two_pi
    {n : ℕ} (hn : 8 ≤ n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0)
    (him : 0 < z.im) : 2 * π < ‖z‖ ^ n := by
  have hn0 : 0 < n := by omega
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hrho : 0 < ‖z‖ := lt_trans zero_lt_one (RootGeometry.one_lt_norm_root hn0 hf)
  obtain ⟨htheta, htheta_pi⟩ := UpperSector.arg_mem_upper_half him
  obtain ⟨hre, himcoord⟩ := actual_power_coordinates hn0 hf
  by_cases hacute : Complex.arg z < π / 2
  · have hlo := theta_lower_of_actual_upper_root hn0 hf him
    have hsin := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(π / 2) ≤ 2 * π / (n : ℝ) by
        have hleft : -(π / 2) ≤ (0 : ℝ) := by linarith [Real.pi_pos]
        exact hleft.trans (by positivity)) hacute.le hlo
    have hendpoint := two_pi_lt_successor_mul_sin hnR
    have hmul := mul_lt_mul_of_pos_left hsin (by positivity : 0 < (n : ℝ) + 1)
    have hray := ray_distance_lower (by positivity : 0 ≤ (n : ℝ) + 1)
      (Real.sin_pos_of_pos_of_lt_pi htheta htheta_pi).le hre himcoord
    rw [norm_pow] at hray
    linarith
  · have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hacute)
      (by linarith [Real.pi_pos] : Complex.arg z ≤ π + π / 2)
    have hlarge := obtuse_distance_strict (by positivity : 0 ≤ (n : ℝ) + 1)
      (div_pos hnpos hrho) hcos hre himcoord
    rw [norm_pow] at hlarge
    linarith [Real.pi_lt_four]

lemma real_root_power_gt_successor
    {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0)
    (him : z.im = 0) : (n : ℝ) + 1 < ‖z‖ ^ n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrho : 0 < ‖z‖ := lt_trans zero_lt_one (RootGeometry.one_lt_norm_root hn hf)
  obtain ⟨hre, himcoord⟩ := actual_power_coordinates hn hf
  have harg := ActualAngularHarmonic.real_root_arg_eq_pi hn hf him
  have hcos : Real.cos (Complex.arg z) ≤ 0 := by rw [harg]; norm_num
  simpa only [norm_pow] using obtuse_distance_strict
    (by positivity : 0 ≤ (n : ℝ) + 1) (div_pos hnpos hrho) hcos hre himcoord

theorem root_power_gt_four
    {n : ℕ} (hn : 3 ≤ n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) : 4 < ‖z‖ ^ n := by
  rcases lt_trichotomy z.im 0 with him | him | him
  · have hconj := ActualAngularHarmonic.conjugate_root hf
    have himconj : 0 < (conj z).im := by simpa using neg_pos.mpr him
    simpa using upper_root_power_gt_four hn hconj himconj
  · have hlarge := real_root_power_gt_successor (by omega : 0 < n) hf him
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · exact upper_root_power_gt_four hn hf him

theorem root_power_gt_two_pi
    {n : ℕ} (hn : 8 ≤ n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) : 2 * π < ‖z‖ ^ n := by
  rcases lt_trichotomy z.im 0 with him | him | him
  · have hconj := ActualAngularHarmonic.conjugate_root hf
    have himconj : 0 < (conj z).im := by simpa using neg_pos.mpr him
    simpa using upper_root_power_gt_two_pi hn hconj himconj
  · have hlarge := real_root_power_gt_successor (by omega : 0 < n) hf him
    have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.pi_lt_four]
  · exact upper_root_power_gt_two_pi hn hf him

theorem root_log_radius_gt_eleven_sixths
    {n : ℕ} (hn : 8 ≤ n) {z : ℂ}
    (hf : ((fInt n).map (Int.castRingHom ℂ)).eval z = 0) :
    (11 / 6 : ℝ) < (n : ℝ) * Real.log ‖z‖ := by
  have hlarge := root_power_gt_two_pi hn hf
  have hbase : (157 / 25 : ℝ) < ‖z‖ ^ n := by
    linarith [pi_rational_bounds.1]
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 157 / 25) hbase
  rw [Real.log_pow] at hlog
  exact lt_trans UniversalScalar.inner_radius_log_certificate hlog

end EventualIrreducibility.UniversalInnerRadius

open Polynomial
open scoped BigOperators

namespace EventualIrreducibility

noncomputable def FactorSeries.firstDifference {n : ℕ} (s : FactorSeries n) : ℤ :=
  s.factor.coeff 1 - s.factor.coeff 0 * s.factor.coeff (s.factor.natDegree - 1)

lemma FactorSeries.constant_gt_one_for_J {n : ℕ} (s : FactorSeries n) (hn : 0 < n) :
    (1 : ℝ) < (s.factor.coeff 0 : ℝ) := by
  have hpos : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by
    exact_mod_cast s.constant_pos hn
  have h := (s.constant_abs_size hn).1
  simpa only [abs_of_pos hpos] using h

lemma coeff_fInt_linear_int {n : ℕ} (hn : 0 < n) :
    (fInt n).coeff 1 = (n : ℤ) - 1 := by
  by_cases h : 1 < n
  · rw [coeff_fInt, if_pos h, Nat.cast_sub (show 1 ≤ n by omega)]
    norm_num
  · have hn1 : n = 1 := by omega
    subst n
    norm_num [coeff_fInt]

theorem FactorSeries.firstDifference_ne_zero {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) : s.firstDifference ≠ 0 := by
  obtain ⟨h, hh⟩ := s.divides
  have h0 : (fInt n).coeff 0 = (n : ℤ) := by simp [coeff_fInt, hn]
  obtain ⟨hc, hl⟩ := UniversalIrreducibility.polynomial_constants_and_linear
    hh.symm h0 (coeff_fInt_linear_int hn)
  have hlinear : s.factor.coeff 0 * h.coeff 1 + h.coeff 0 * s.factor.coeff 1 =
      s.factor.coeff 0 * h.coeff 0 - 1 := by rw [hc]; exact hl
  have ha : (1 : ℤ) < s.factor.coeff 0 := by
    exact_mod_cast s.constant_gt_one_for_J hn
  simpa only [FactorSeries.firstDifference] using
    (UniversalIrreducibility.first_difference_ne_zero
      (c := s.factor.coeff (s.factor.natDegree - 1)) ha hlinear)

theorem FactorSeries.exists_J_root_data {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) :
    ∃ d : ℕ, ∃ alpha : Fin d → ℂ,
      d = s.factor.natDegree ∧
      (∀ i, alpha i ≠ 0) ∧
      s.factor.map (Int.castRingHom ℂ) =
        ∏ i, (X - C (alpha i) : ℂ[X]) ∧
      (∀ i, 1 < ‖alpha i‖) ∧
      (∏ i, ‖alpha i‖) = (s.factor.coeff 0 : ℝ) ∧
      (∀ i, Real.log ‖alpha i‖ < Real.log (2 * (n : ℝ) + 1) / (n : ℝ)) ∧
      (s.firstDifference : ℂ) = (s.factor.coeff 0 : ℂ) *
        ∑ i, (alpha i - (alpha i)⁻¹) := by
  classical
  obtain ⟨d, alpha, hd, hne, hprod, _hquot⟩ := s.exists_root_product_identity hn
  have hroot (i : Fin d) :
      (s.factor.map (Int.castRingHom ℂ)).eval (alpha i) = 0 := by
    rw [hprod, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hmod (i : Fin d) : 1 < ‖alpha i‖ :=
    (RootGeometry.factor_root_annulus s hn (hroot i)).1
  have hconst : (∏ i, ‖alpha i‖) = (s.factor.coeff 0 : ℝ) := by
    have h := UniversalScalar.integer_root_product_norm_constant s.factor alpha hprod
    have ha : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by exact_mod_cast s.constant_pos hn
    simpa only [abs_of_pos ha] using h
  have hlog (i : Fin d) :
      Real.log ‖alpha i‖ < Real.log (2 * (n : ℝ) + 1) / (n : ℝ) := by
    apply UniversalScalar.log_root_upper_from_power hn
      (show 0 < ‖alpha i‖ by linarith [hmod i])
    exact RootGeometry.norm_root_pow_lt hn (RootGeometry.root_of_mapped_factor s (hroot i))
  have hmapdegree : (s.factor.map (Int.castRingHom ℂ)).natDegree = s.factor.natDegree :=
    s.monic.natDegree_map (Int.castRingHom ℂ)
  have hmapdegreepos : 0 < (s.factor.map (Int.castRingHom ℂ)).natDegree := by
    rw [hmapdegree]
    exact s.degree_pos
  have htrace := UniversalScalar.J_trace_penultimate_coefficient
    (s.factor.map (Int.castRingHom ℂ)) alpha hmapdegreepos hprod hne
  rw [hmapdegree] at htrace
  have htrace' : (s.firstDifference : ℂ) = (s.factor.coeff 0 : ℂ) *
      ∑ i, (alpha i - (alpha i)⁻¹) := by
    simpa only [FactorSeries.firstDifference, Polynomial.coeff_map,
      Int.coe_castRingHom, Int.cast_sub, Int.cast_mul] using htrace
  exact ⟨d, alpha, hd, hne, hprod, hmod, hconst, hlog, htrace'⟩

theorem FactorSeries.firstDifference_small_bound {n : ℕ}
    (s : FactorSeries n) (hn : 6 ≤ n) :
    |(s.firstDifference : ℝ)| <
      (107 / 49) * (s.factor.coeff 0 : ℝ) * Real.log (s.factor.coeff 0 : ℝ) := by
  have hnpos : 0 < n := by omega
  obtain ⟨d, alpha, _hd, _hne, _hprod, hmod, hconst, hlog, htrace⟩ :=
    s.exists_J_root_data hnpos
  have ha := s.constant_gt_one_for_J hnpos
  have htraceR : ((s.firstDifference : ℝ) : ℂ) =
      ((s.factor.coeff 0 : ℝ) : ℂ) * ∑ i, (alpha i - (alpha i)⁻¹) := by
    simpa using htrace
  have hrad := UniversalScalar.J_radial_bound_from_complex_trace alpha
    (show (0 : ℝ) ≤ (s.factor.coeff 0 : ℝ) by linarith)
    (fun i => (hmod i).le) htraceR
  exact UniversalScalar.J_small_root_bound (fun i => ‖alpha i‖)
    (by exact_mod_cast hn) ha (fun i => (hmod i).le) hconst hlog hrad

end EventualIrreducibility

open scoped BigOperators ComplexConjugate

namespace UniversalIrreducibility

lemma log_one_sub_exp_neg_lower {s : ℝ} (hs : 0 < s) :
    Real.log s - s / 2 ≤ Real.log (1 - Real.exp (-s)) := by
  have hle : s ≤ 2 * Real.sinh (s / 2) := by
    have hh := Real.self_le_sinh_iff.mpr (show 0 ≤ s / 2 by positivity)
    linarith
  have hpos : 0 < 2 * Real.sinh (s / 2) := lt_of_lt_of_le hs hle
  have hid : 1 - Real.exp (-s) =
      Real.exp (-s / 2) * (2 * Real.sinh (s / 2)) := by
    rw [Real.sinh_eq]
    have he0 : Real.exp (-s / 2) * Real.exp (s / 2) = 1 := by
      rw [← Real.exp_add]
      have hz : -s / 2 + s / 2 = 0 := by ring
      rw [hz, Real.exp_zero]
    have he1 : Real.exp (-s / 2) * Real.exp (-(s / 2)) = Real.exp (-s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith
  rw [hid, Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hpos), Real.log_exp]
  have hlog := Real.log_le_log hs hle
  linarith

lemma log_support_tangent {K A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (hbase : Real.log (3 * K) < 2) :
    Real.log (K * A) < 1 + A / 3 := by
  have ha3 : 0 < A / 3 := by positivity
  have ht := Real.log_le_sub_one_of_pos ha3
  have hid : K * A = (3 * K) * (A / 3) := by ring
  rw [hid, Real.log_mul (by positivity) (ne_of_gt ha3)]
  linarith

lemma discriminant_energy_scalar {D d A s : ℝ}
    (hd : 0 ≤ d) (hs : 0 < s)
    (hdisc : D ≤ (d - 1) * A + s * d * (d - 1) / 2 -
      d * Real.log (1 - Real.exp (-s))) :
    D ≤ (d - 1) * A + s * d ^ 2 / 2 - d * Real.log s := by
  have hb := log_one_sub_exp_neg_lower hs
  have hm := mul_le_mul_of_nonneg_left hb hd
  nlinarith

end UniversalIrreducibility

namespace UniversalIrreducibility

open EventualIrreducibility.AngularKernel
open EventualIrreducibility.FourierKernel
open EventualIrreducibility.DiscriminantBridge

lemma finite_pair_log_upper {d : ℕ} (hd : 0 < d)
    (F K : Fin d → Fin d → ℝ) (r : Fin d → ℝ) (s : ℝ)
    (hpair : ∀ i j, i ≠ j → 2 * F i j - r i - r j ≤ s + 2 * K i j) :
    offDiagSum F ≤ ((d - 1 : ℕ) : ℝ) * (∑ i, r i) +
      s * (d : ℝ) * ((d - 1 : ℕ) : ℝ) / 2 + offDiagSum K := by
  classical
  have hsum : offDiagSum (fun i j => 2 * F i j - r i - r j) ≤
      offDiagSum (fun i j => s + 2 * K i j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact hpair i j (Finset.mem_erase.mp hj).1.symm
  rw [offDiagSum_sub, offDiagSum_sub, offDiagSum_mul,
    offDiagSum_first, offDiagSum_second hd, offDiagSum_add,
    offDiagSum_const, offDiagSum_mul] at hsum
  linarith

lemma kernel_full_sum_nonpos {d : ℕ} (u : Fin d → ℂ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (hu : ∀ i, ‖u i‖ = 1) :
    (∑ i, ∑ j, Real.log ‖1 - (t : ℂ) * u i * conj (u j)‖) ≤ 0 := by
  have h := fourier_kernel_prefix_le u ht ht1 hu 0
  simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton,
    pow_zero, Nat.cast_zero, div_zero, zero_mul] at h
  linarith

lemma kernel_offdiag_upper {d : ℕ} (u : Fin d → ℂ) {s : ℝ}
    (hs : 0 < s) (hu : ∀ i, ‖u i‖ = 1) :
    offDiagSum (fun i j => Real.log
      ‖1 - (Real.exp (-s) : ℂ) * u i * conj (u j)‖) ≤
      -(d : ℝ) * Real.log (1 - Real.exp (-s)) := by
  have ht1 : Real.exp (-s) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hfull := kernel_full_sum_nonpos u (le_of_lt (Real.exp_pos _)) ht1 hu
  rw [fullSum_eq_diagonal_add_offDiag] at hfull
  simp_rw [kernel_diagonal_norm ht1 (hu _)] at hfull
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hfull
  linarith

lemma logarithmic_root_discriminant_bound {d : ℕ} (hd : 0 < d)
    (alpha u : Fin d → ℂ) (rho : Fin d → ℝ) {s : ℝ}
    (halpha : ∀ i, alpha i = (rho i : ℂ) * u i)
    (hrho : ∀ i, 0 < rho i) (hs : 0 < s)
    (hu : ∀ i, ‖u i‖ = 1) (hinj : Function.Injective alpha)
    (hrad : ∀ i j, |Real.log (rho i) - Real.log (rho j)| ≤ s) :
    offDiagSum (fun i j => Real.log ‖alpha i - alpha j‖) ≤
      ((d : ℝ) - 1) * (∑ i, Real.log (rho i)) +
      s * (d : ℝ) ^ 2 / 2 - (d : ℝ) * Real.log s := by
  have hp := finite_pair_log_upper hd
    (fun i j => Real.log ‖alpha i - alpha j‖)
    (fun i j => Real.log ‖1 - (Real.exp (-s) : ℂ) * u i * conj (u j)‖)
    (fun i => Real.log (rho i)) s
    (fun i j hij => angular_kernel_log_bound (halpha i) (halpha j)
      (hrho i) (hrho j) hs (hu i) (hu j)
      (fun h => hij (hinj h)) (hrad i j))
  have hk := kernel_offdiag_upper u hs hu
  have hdcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  rw [hdcast] at hp
  apply discriminant_energy_scalar (by positivity) hs
  linarith

lemma integer_discriminant_log_bound {d : ℕ} (hd : 0 < d)
    (g : ℤ[X]) (hg : g.Monic) (hgpos : 0 < g.natDegree)
    (alpha u : Fin d → ℂ) (rho : Fin d → ℝ) {s A : ℝ}
    (hprod : g.map (Int.castRingHom ℂ) =
      ∏ i, (Polynomial.X - Polynomial.C (alpha i) : ℂ[X]))
    (halpha : ∀ i, alpha i = (rho i : ℂ) * u i)
    (hrho : ∀ i, 0 < rho i) (hs : 0 < s)
    (hu : ∀ i, ‖u i‖ = 1) (hinj : Function.Injective alpha)
    (hrad : ∀ i j, |Real.log (rho i) - Real.log (rho j)| ≤ s)
    (hA : ∑ i, Real.log (rho i) = A) :
    Real.log |(g.discr : ℝ)| ≤ ((d : ℝ) - 1) * A +
      s * (d : ℝ) ^ 2 / 2 - (d : ℝ) * Real.log s := by
  rw [log_discr_eq_ordered_root_log_sum g hg hgpos alpha hprod hinj]
  have h := logarithmic_root_discriminant_bound hd alpha u rho halpha hrho hs hu hinj hrad
  simpa only [hA, offDiagSum] using h

end UniversalIrreducibility

open Polynomial
open scoped BigOperators

namespace UniversalIrreducibility

open EventualIrreducibility.DiscriminantBridge

lemma integer_resultant_abs_eq_root_norm_prod
    (g h : ℤ[X]) (hg : g.Monic) (alpha : Fin g.natDegree → ℂ)
    (hprod : g.map (Int.castRingHom ℂ) = ∏ i, (X - C (alpha i) : ℂ[X])) :
    |(g.resultant h g.natDegree h.natDegree : ℝ)| =
      ∏ i, ‖(h.map (Int.castRingHom ℂ)).eval (alpha i)‖ := by
  have hmap := Polynomial.resultant_map_map g h g.natDegree h.natDegree
    (Int.castRingHom ℂ)
  have hres := resultant_root_product_eval alpha
    (g.map (Int.castRingHom ℂ)) (h.map (Int.castRingHom ℂ)) hprod
    h.natDegree Polynomial.natDegree_map_le
  rw [hg.natDegree_map] at hres
  rw [hmap] at hres
  have hn := congrArg (fun z : ℂ => ‖z‖) hres
  simpa only [Int.coe_castRingHom, Complex.norm_intCast, norm_finset_prod] using hn

lemma integer_discriminant_abs_eq_derivative_norm_prod
    (g : ℤ[X]) (hg : g.Monic) (hd : 0 < g.natDegree)
    (alpha : Fin g.natDegree → ℂ)
    (hprod : g.map (Int.castRingHom ℂ) = ∏ i, (X - C (alpha i) : ℂ[X])) :
    |(g.discr : ℝ)| =
      ∏ i, ‖(g.map (Int.castRingHom ℂ)).derivative.eval (alpha i)‖ := by
  rw [discr_abs_eq_ordered_root_norm_prod g hg hd alpha hprod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [eval_derivative_root_product alpha _ hprod i, norm_finset_prod]

lemma integer_eval_abs_eq_root_norm_prod (g : ℤ[X])
    (alpha : Fin g.natDegree → ℂ)
    (hprod : g.map (Int.castRingHom ℂ) = ∏ i, (X - C (alpha i) : ℂ[X]))
    (x : ℤ) : |((g.eval x : ℤ) : ℝ)| = ∏ i, ‖(x : ℂ) - alpha i‖ := by
  have he := congrArg (fun P : ℂ[X] => P.eval (x : ℂ)) hprod
  rw [Polynomial.eval_map] at he
  change g.eval₂ (Int.castRingHom ℂ) ((Int.castRingHom ℂ) x) = _ at he
  rw [Polynomial.eval₂_hom] at he
  have hn := congrArg (fun z : ℂ => ‖z‖) he
  simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, norm_finset_prod, Int.coe_castRingHom, Complex.norm_intCast] using hn

theorem integer_discriminant_resultant_identity
    (n : ℕ) (g h : ℤ[X]) (hg : g.Monic) (hd : 0 < g.natDegree)
    (alpha : Fin g.natDegree → ℂ)
    (hprod : g.map (Int.castRingHom ℂ) = ∏ i, (X - C (alpha i) : ℂ[X]))
    (htri : (X - 1) ^ 2 * (g * h) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : ℤ) * X + C (n : ℤ)) :
    |(g.discr : ℝ)| * |(g.resultant h g.natDegree h.natDegree : ℝ)| *
      |(g.coeff 0 : ℝ)| * |((g.eval 1 : ℤ) : ℝ)| =
        ((n : ℝ) * ((n : ℝ) + 1)) ^ g.natDegree := by
  classical
  let G := g.map (Int.castRingHom ℂ)
  let H := h.map (Int.castRingHom ℂ)
  have hroot (i : Fin g.natDegree) : G.eval (alpha i) = 0 := by
    rw [show G = ∏ j, (X - C (alpha j) : ℂ[X]) from hprod, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have htriC := EventualIrreducibility.Simplicity.mapped_trinomial_from_integer
    (K := ℂ) htri
  rw [Polynomial.map_mul] at htriC
  have hpoint (i : Fin g.natDegree) :
      ‖alpha i‖ * ‖alpha i - 1‖ * ‖G.derivative.eval (alpha i)‖ *
        ‖H.eval (alpha i)‖ = (n : ℝ) * ((n : ℝ) + 1) := by
    have hp := EventualIrreducibility.Simplicity.root_derivative_identity_of_trinomial
      htriC (z := alpha i) (by simp [Polynomial.eval_mul, hroot i, G])
    have hder : (G * H).derivative.eval (alpha i) =
        G.derivative.eval (alpha i) * H.eval (alpha i) := by
      rw [Polynomial.derivative_mul]
      simp [hroot i]
    change alpha i * (alpha i - 1) * (G * H).derivative.eval (alpha i) = _ at hp
    rw [hder] at hp
    have hnorm := congrArg (fun z : ℂ => ‖z‖) hp
    have hN : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      norm_cast
    simpa only [norm_mul, Complex.norm_natCast, hN, mul_assoc] using hnorm
  have htotal := Finset.prod_congr (s₁ := (Finset.univ : Finset (Fin g.natDegree)))
    (s₂ := Finset.univ) rfl (fun i _ => hpoint i)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at htotal
  have hzero := integer_eval_abs_eq_root_norm_prod g alpha hprod 0
  rw [← Polynomial.coeff_zero_eq_eval_zero] at hzero
  simp only [Int.cast_zero, zero_sub, norm_neg] at hzero
  have hone := integer_eval_abs_eq_root_norm_prod g alpha hprod 1
  simp only [Int.cast_one] at hone
  simp_rw [norm_sub_rev (1 : ℂ) (alpha _)] at hone
  rw [integer_discriminant_abs_eq_derivative_norm_prod g hg hd alpha hprod,
    integer_resultant_abs_eq_root_norm_prod g h hg alpha hprod, hzero, hone]
  dsimp only [G, H] at htotal
  simpa only [mul_pow, mul_comm, mul_left_comm, mul_assoc] using htotal

end UniversalIrreducibility

open Polynomial
open scoped BigOperators

namespace EventualIrreducibility

lemma factor_eval_one_nonzero {n : ℕ} (hn : 0 < n) {g h : ℤ[X]}
    (hgh : g * h = fInt n) : g.eval 1 ≠ 0 ∧ h.eval 1 ≠ 0 := by
  have he : g.eval 1 * h.eval 1 = (fInt n).eval 1 := by
    simpa only [Polynomial.eval_mul] using congrArg (fun P : ℤ[X] => P.eval 1) hgh
  have hprod : g.eval 1 * h.eval 1 ≠ 0 := by rw [he]; exact eval_one_ne_zero n hn
  exact mul_ne_zero_iff.mp hprod

lemma integer_abs_real_ge_one {z : ℤ} (hz : z ≠ 0) :
    (1 : ℝ) ≤ |(z : ℝ)| := by
  have hn : 1 ≤ z.natAbs := by
    have hp := Int.natAbs_pos.mpr hz
    omega
  have hr : (1 : ℝ) ≤ (z.natAbs : ℝ) := by exact_mod_cast hn
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hr

theorem factor_eval_one_abs_bound {n : ℕ} (hn : 0 < n) {g h : ℤ[X]}
    (hgh : g * h = fInt n) :
    0 < |((g.eval 1 : ℤ) : ℝ)| ∧
      |((g.eval 1 : ℤ) : ℝ)| ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  obtain ⟨hg1, hh1⟩ := factor_eval_one_nonzero hn hgh
  have hgR : ((g.eval 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hg1
  have hH := integer_abs_real_ge_one hh1
  have he : ((g.eval 1 : ℤ) : ℝ) * ((h.eval 1 : ℤ) : ℝ) =
      (((fInt n).eval 1 : ℤ) : ℝ) := by
    have heZ := congrArg (fun P : ℤ[X] => P.eval 1) hgh
    simpa only [Polynomial.eval_mul, Int.cast_mul] using
      congrArg (fun z : ℤ => (z : ℝ)) heZ
  have htwo : 2 * (((fInt n).eval 1 : ℤ) : ℝ) =
      (n : ℝ) * ((n : ℝ) + 1) := by
    exact_mod_cast two_mul_eval_one n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfpos : 0 < (((fInt n).eval 1 : ℤ) : ℝ) := by nlinarith
  have habs := congrArg (fun x : ℝ => |x|) he
  rw [abs_mul, abs_of_pos hfpos] at habs
  have hle := mul_le_mul_of_nonneg_left hH (abs_nonneg ((g.eval 1 : ℤ) : ℝ))
  rw [mul_one, habs] at hle
  exact ⟨abs_pos.mpr hgR, by linarith⟩

theorem FactorSeries.eval_one_abs_bound {n : ℕ} (s : FactorSeries n) (hn : 0 < n) :
    0 < |((s.factor.eval 1 : ℤ) : ℝ)| ∧
      |((s.factor.eval 1 : ℤ) : ℝ)| ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  obtain ⟨h, hh⟩ := s.divides
  exact factor_eval_one_abs_bound hn hh.symm

theorem FactorSeries.log_discriminant_resultant_identity {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) (h : ℤ[X]) (hh : s.factor * h = fInt n) :
    Real.log |(s.factor.discr : ℝ)| +
        Real.log |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| +
        Real.log (s.factor.coeff 0 : ℝ) + Real.log |((s.factor.eval 1 : ℤ) : ℝ)| =
      (s.factor.natDegree : ℝ) * (Real.log (n : ℝ) + Real.log ((n : ℝ) + 1)) := by
  obtain ⟨d, alpha, hd, _hne, hprod, _hmod, _hconst, _hlog, _htrace⟩ :=
    s.exists_J_root_data hn
  subst d
  have htri : (X - 1) ^ 2 * (s.factor * h) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : ℤ) * X + C (n : ℤ) := by
    rw [hh]
    exact trinomial_identity n
  have hid := UniversalIrreducibility.integer_discriminant_resultant_identity
    n s.factor h s.monic s.degree_pos alpha hprod htri
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haR : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by exact_mod_cast s.constant_pos hn
  rw [abs_of_pos haR] at hid
  have hF := (s.eval_one_abs_bound hn).1
  have htotal : 0 < |(s.factor.discr : ℝ)| *
      |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| *
      (s.factor.coeff 0 : ℝ) * |((s.factor.eval 1 : ℤ) : ℝ)| := by
    rw [hid]
    positivity
  have hD : 0 < |(s.factor.discr : ℝ)| := by
    rcases lt_or_eq_of_le (abs_nonneg (s.factor.discr : ℝ)) with hd | hd
    · exact hd
    · rw [← hd] at htotal
      norm_num at htotal
  have hR : 0 < |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| := by
    rcases lt_or_eq_of_le
      (abs_nonneg (s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)) with hr | hr
    · exact hr
    · rw [← hr] at htotal
      norm_num at htotal
  exact UniversalIrreducibility.log_product_identity hnR hD hR haR hF hid

theorem FactorSeries.energy_of_lower_radial {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) (h : ℤ[X]) (hh : s.factor * h = fInt n)
    (eta : ℝ)
    (hlower : ∀ z : ℂ,
      (s.factor.map (Int.castRingHom ℂ)).eval z = 0 →
      eta ≤ (n : ℝ) * Real.log ‖z‖) :
    UniversalScalar.radialMoment (Real.log (n : ℝ))
      (Real.log (2 * (n : ℝ) + 1) - eta)
      (Real.log (s.factor.coeff 0 : ℝ))
      ((s.factor.natDegree : ℝ) / (n : ℝ))
      (Real.log (Real.log (2 * (n : ℝ) + 1) - eta)) ≤
        (Real.log |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| +
          Real.log |((s.factor.eval 1 : ℤ) : ℝ)|) / (n : ℝ) -
        ((s.factor.natDegree : ℝ) / (n : ℝ)) *
          Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
  classical
  obtain ⟨d, alpha, hd, hne, hprod, hmod, hconst, hlog, _htrace⟩ :=
    s.exists_J_root_data hn
  subst d
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot (i : Fin s.factor.natDegree) :
      (s.factor.map (Int.castRingHom ℂ)).eval (alpha i) = 0 :=
    FourierEnergy.root_of_fin_product _ alpha hprod i
  have hinj : Function.Injective alpha :=
    DiscriminantBridge.root_product_injective_of_separable alpha
      (s.factor.map (Int.castRingHom ℂ)) hprod (s.separable_map ℂ hn)
  obtain ⟨hu, halpha⟩ := FourierEnergy.direction_properties alpha hne
  have hlow (i : Fin s.factor.natDegree) :
      eta / (n : ℝ) ≤ Real.log ‖alpha i‖ := by
    apply (div_le_iff₀ hnR).2
    nlinarith only [hlower (alpha i) (hroot i)]
  let i0 : Fin s.factor.natDegree := ⟨0, s.degree_pos⟩
  have hw : 0 < Real.log (2 * (n : ℝ) + 1) - eta := by
    have hi := lt_of_le_of_lt (hlow i0) (hlog i0)
    have he := (div_lt_div_iff_of_pos_right hnR).mp hi
    linarith
  have hs : 0 < (Real.log (2 * (n : ℝ) + 1) - eta) / (n : ℝ) := div_pos hw hnR
  have hrad (i j : Fin s.factor.natDegree) :
      |Real.log ‖alpha i‖ - Real.log ‖alpha j‖| ≤
        (Real.log (2 * (n : ℝ) + 1) - eta) / (n : ℝ) := by
    rw [sub_div]
    apply abs_le.mpr
    constructor <;> linarith [hlow i, hlow j, (hlog i).le, (hlog j).le]
  have hA : (∑ i, Real.log ‖alpha i‖) = Real.log (s.factor.coeff 0 : ℝ) :=
    UniversalScalar.sum_root_logs (fun i => ‖alpha i‖)
      (fun i => lt_trans zero_lt_one (hmod i)) hconst
  have hdisc := UniversalIrreducibility.integer_discriminant_log_bound
    s.degree_pos s.factor s.monic s.degree_pos alpha (FourierEnergy.direction alpha)
    (fun i => ‖alpha i‖) hprod halpha
    (fun i => lt_trans zero_lt_one (hmod i)) hs hu hinj hrad hA
  exact UniversalIrreducibility.energy_inequality_from_discriminant hnR hw
    (s.log_discriminant_resultant_identity hn h hh) hdisc

theorem FactorSeries.energy_outer {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) (h : ℤ[X]) (hh : s.factor * h = fInt n) :
    UniversalScalar.radialMoment (Real.log (n : ℝ)) (Real.log (2 * (n : ℝ) + 1))
      (Real.log (s.factor.coeff 0 : ℝ))
      ((s.factor.natDegree : ℝ) / (n : ℝ)) (Real.log (Real.log (2 * (n : ℝ) + 1))) ≤
        (Real.log |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| +
          Real.log |((s.factor.eval 1 : ℤ) : ℝ)|) / (n : ℝ) -
        ((s.factor.natDegree : ℝ) / (n : ℝ)) *
          Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
  have hlo (z : ℂ) (hz : (s.factor.map (Int.castRingHom ℂ)).eval z = 0) :
      (0 : ℝ) ≤ (n : ℝ) * Real.log ‖z‖ := by
    have hrho := (RootGeometry.factor_root_annulus s hn hz).1
    exact mul_nonneg (by positivity) (Real.log_pos hrho).le
  simpa only [sub_zero] using s.energy_of_lower_radial hn h hh 0 hlo

theorem FactorSeries.energy_inner {n : ℕ}
    (s : FactorSeries n) (hn : 8 ≤ n) (h : ℤ[X]) (hh : s.factor * h = fInt n) :
    UniversalScalar.radialMoment (Real.log (n : ℝ))
      (Real.log (2 * (n : ℝ) + 1) - 11 / 6)
      (Real.log (s.factor.coeff 0 : ℝ))
      ((s.factor.natDegree : ℝ) / (n : ℝ))
      (Real.log (Real.log (2 * (n : ℝ) + 1) - 11 / 6)) ≤
        (Real.log |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| +
          Real.log |((s.factor.eval 1 : ℤ) : ℝ)|) / (n : ℝ) -
        ((s.factor.natDegree : ℝ) / (n : ℝ)) *
          Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
  apply s.energy_of_lower_radial (by omega : 0 < n) h hh (11 / 6)
  intro z hz
  exact (UniversalInnerRadius.root_log_radius_gt_eleven_sixths hn
    (RootGeometry.root_of_mapped_factor s hz)).le

theorem FactorSeries.eval_one_log_closure_bounds {n : ℕ}
    (s : FactorSeries n) (hn : 1 < n) :
    Real.log |((s.factor.eval 1 : ℤ) : ℝ)| ≤
        2 * (Real.log ((n : ℝ) * ((n : ℝ) + 1)) / 2) - Real.log 2 ∧
      Real.log |((s.factor.eval 1 : ℤ) : ℝ)| < 2 * Real.log (n : ℝ) := by
  obtain ⟨hpos, hle⟩ := s.eval_one_abs_bound (by omega : 0 < n)
  apply UniversalScalar.evaluation_log_bounds (by exact_mod_cast hn)
  exact Real.log_le_log hpos hle

end EventualIrreducibility

noncomputable section
namespace EventualIrreducibility.UniversalLocalDraft

abbrev Vertex := ℕ × Bool

def totalWeight : List Vertex → ℕ
  | [] => 0
  | v :: xs => v.1 + totalWeight xs

def colorWeight (b : Bool) : List Vertex → ℕ
  | [] => 0
  | (w, c) :: xs => (if c = b then w else 0) + colorWeight b xs

def cutWeight : List Vertex → ℕ
  | [] => 0
  | (_, b) :: xs => colorWeight (!b) xs + cutWeight xs

lemma colorWeight_partition (xs : List Vertex) :
    colorWeight false xs + colorWeight true xs = totalWeight xs := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
      rcases v with ⟨w, b⟩
      cases b <;> simp [colorWeight, totalWeight] <;> omega

lemma two_vertex_cut_bound (xs : List Vertex) (u v : ℕ) (c d : Bool)
    (hu : totalWeight xs ≤ u) :
    cutWeight ((v, d) :: (u, c) :: xs) ≤
      cutWeight xs + totalWeight xs + u := by
  have hpart := colorWeight_partition xs
  cases c <;> cases d <;> simp [cutWeight, colorWeight] <;> omega

def prefixWeight (w : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, w i

def coloredPrefix (w : ℕ → ℕ) (c : ℕ → Bool) : ℕ → List Vertex
  | 0 => []
  | r + 1 => (w r, c r) :: coloredPrefix w c r

lemma totalWeight_coloredPrefix (w : ℕ → ℕ) (c : ℕ → Bool) (r : ℕ) :
    totalWeight (coloredPrefix w c r) = prefixWeight w r := by
  induction r with
  | zero => simp [coloredPrefix, totalWeight, prefixWeight]
  | succ r ih =>
      simp [coloredPrefix, totalWeight, prefixWeight,
        Finset.sum_range_succ, ih, Nat.add_comm]

def cutBound (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | r + 2 => cutBound w r + prefixWeight w (r + 1)

theorem cutWeight_coloredPrefix_le (w : ℕ → ℕ) (c : ℕ → Bool)
    (hdom : ∀ r, prefixWeight w r ≤ w r) :
    ∀ r, cutWeight (coloredPrefix w c r) ≤ cutBound w r
  | 0 => by simp [coloredPrefix, cutWeight, cutBound]
  | 1 => by simp [coloredPrefix, cutWeight, colorWeight, cutBound]
  | r + 2 => by
      have hu : totalWeight (coloredPrefix w c r) ≤ w r := by
        rw [totalWeight_coloredPrefix]
        exact hdom r
      have hs := two_vertex_cut_bound (coloredPrefix w c r)
        (w r) (w (r + 1)) (c r) (c (r + 1)) hu
      have ih := cutWeight_coloredPrefix_le w c hdom r
      calc
        cutWeight (coloredPrefix w c (r + 2)) ≤
            cutWeight (coloredPrefix w c r) + prefixWeight w r + w r := by
              simpa only [coloredPrefix, totalWeight_coloredPrefix] using hs
        _ ≤ cutBound w r + prefixWeight w r + w r := by omega
        _ = cutBound w (r + 2) := by
          simp only [cutBound, prefixWeight, Finset.sum_range_succ]
          omega

def packetWeight (p δ : ℕ) : ℕ → ℕ
  | 0 => p - δ
  | k + 1 => p ^ (k + 1) * (p - 1)

lemma packet_prefix (p δ : ℕ) (hp : 1 ≤ p) (hδ : δ ≤ p) (r : ℕ) :
    prefixWeight (packetWeight p δ) (r + 1) + δ = p ^ (r + 1) := by
  induction r with
  | zero =>
      simp [prefixWeight, packetWeight, Nat.sub_add_cancel hδ]
  | succ r ih =>
      have hs : prefixWeight (packetWeight p δ) (r + 1 + 1) =
          prefixWeight (packetWeight p δ) (r + 1) +
            p ^ (r + 1) * (p - 1) := by
        simp [prefixWeight, Finset.sum_range_succ, packetWeight]
      calc
        prefixWeight (packetWeight p δ) (r + 1 + 1) + δ =
            (prefixWeight (packetWeight p δ) (r + 1) + δ) +
              p ^ (r + 1) * (p - 1) := by rw [hs]; omega
        _ = p ^ (r + 1) + p ^ (r + 1) * (p - 1) := by rw [ih]
        _ = p ^ (r + 1) * ((p - 1) + 1) := by ring
        _ = p ^ (r + 1) * p := by rw [Nat.sub_add_cancel hp]
        _ = p ^ (r + 1 + 1) := (pow_succ p (r + 1)).symm

lemma packet_dominance (p δ : ℕ) (hp : 2 ≤ p) (hδ : δ ≤ p) :
    ∀ r, prefixWeight (packetWeight p δ) r ≤ packetWeight p δ r
  | 0 => by simp [prefixWeight, packetWeight]
  | r + 1 => by
      have hs := packet_prefix p δ (by omega) hδ r
      have hm : 1 ≤ p - 1 := by omega
      calc
        prefixWeight (packetWeight p δ) (r + 1) ≤ p ^ (r + 1) := by omega
        _ = p ^ (r + 1) * 1 := by omega
        _ ≤ p ^ (r + 1) * (p - 1) := Nat.mul_le_mul_left _ hm
        _ = packetWeight p δ (r + 1) := rfl

def exactCut (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | r + 2 => exactCut p r + p ^ (r + 1)

lemma cutBound_packet (p δ : ℕ) (hp : 1 ≤ p) (hδ : δ ≤ p) :
    ∀ r, cutBound (packetWeight p δ) r + δ * (r / 2) = exactCut p r
  | 0 => by simp [cutBound, exactCut]
  | 1 => by simp [cutBound, exactCut]
  | r + 2 => by
      have ih := cutBound_packet p δ hp hδ r
      have hs := packet_prefix p δ hp hδ r
      have hd : (r + 2) / 2 = r / 2 + 1 := by omega
      rw [cutBound, exactCut, hd, Nat.mul_add, Nat.mul_one]
      omega

theorem packet_cut_bound (p δ r : ℕ) (hp : 2 ≤ p) (hδ : δ ≤ p)
    (c : ℕ → Bool) :
    cutWeight (coloredPrefix (packetWeight p δ) c r) + δ * (r / 2) ≤
      exactCut p r := by
  have hc := cutWeight_coloredPrefix_le (packetWeight p δ) c
    (packet_dominance p δ hp hδ) r
  have he := cutBound_packet p δ (by omega) hδ r
  omega

def layerSum (p : ℕ) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range s, 1 / (p : ℝ) ^ (2 * j + 1)

lemma layerSum_succ_last (p s : ℕ) :
    layerSum p (s + 1) = layerSum p s + 1 / (p : ℝ) ^ (2 * s + 1) := by
  simp [layerSum, Finset.sum_range_succ]

lemma layerSum_succ_first (p s : ℕ) :
    layerSum p (s + 1) = 1 / (p : ℝ) + layerSum p s / (p : ℝ) ^ 2 := by
  have ht (j : ℕ) : 1 / (p : ℝ) ^ (2 * (j + 1) + 1) =
      (1 / (p : ℝ) ^ (2 * j + 1)) / (p : ℝ) ^ 2 := by
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, pow_add, div_div]
  simp only [layerSum, Finset.sum_range_succ']
  simp only [Nat.mul_zero, zero_add, pow_one]
  simp_rw [ht]
  rw [Finset.sum_div]
  ring

lemma normalized_exactCut_step (p r : ℕ) (hp : 0 < p) :
    (exactCut p (r + 2) : ℝ) / (p : ℝ) ^ (r + 2) =
      1 / (p : ℝ) + ((exactCut p r : ℝ) / (p : ℝ) ^ r) / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  simp only [exactCut, Nat.cast_add, Nat.cast_pow, Nat.cast_mul, pow_add, pow_one]
  field_simp [hp0]; ring

theorem normalized_exactCut_layers (p : ℕ) (hp : 0 < p) :
    ∀ r, (exactCut p r : ℝ) / (p : ℝ) ^ r = layerSum p (r / 2)
  | 0 => by simp [exactCut, layerSum]
  | 1 => by simp [exactCut, layerSum]
  | r + 2 => by
      have hd : (r + 2) / 2 = r / 2 + 1 := by omega
      rw [normalized_exactCut_step p r hp, normalized_exactCut_layers p hp r,
        hd, layerSum_succ_first]

def firstExcess (p : ℕ) : ℝ := max 0 (1 / (p : ℝ) - 1 / 8)

lemma log_nat_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  · apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp)

lemma later_layer_le_eighth (p j : ℕ) (hp : 2 ≤ p) (hj : 1 ≤ j) :
    1 / (p : ℝ) ^ (2 * j + 1) ≤ (1 : ℝ) / 8 := by
  have he : 3 ≤ 2 * j + 1 := by omega
  have hpow : 8 ≤ p ^ (2 * j + 1) := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ p ^ 3 := by gcongr
      _ ≤ p ^ (2 * j + 1) := by gcongr; omega
  have hreal : (8 : ℝ) ≤ (p : ℝ) ^ (2 * j + 1) := by
    exact_mod_cast hpow
  exact one_div_le_one_div_of_le (by norm_num) hreal

lemma layerSum_le_eighth (p : ℕ) (hp : 2 ≤ p) (s : ℕ) :
    layerSum p s ≤ (s : ℝ) / 8 + firstExcess p := by
  induction s with
  | zero => simp [layerSum, firstExcess]
  | succ s ih =>
      by_cases hs : s = 0
      · subst s
        have hm : 1 / (p : ℝ) - 1 / 8 ≤ firstExcess p :=
          le_max_right _ _
        simp only [layerSum, Finset.sum_range_one, Nat.mul_zero, zero_add,
          pow_one, Nat.cast_one]
        linarith
      · have ht := later_layer_le_eighth p s hp (by omega)
        rw [layerSum_succ_last]
        push_cast
        linarith

def smallPrimes : Finset ℕ := {2, 3, 5, 7}

lemma prime_lt_eight (p : ℕ) (hp : p.Prime) (h8 : p < 8) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have h2 := hp.two_le
  have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
  have hp6 : p ≠ 6 := by rintro rfl; norm_num at hp
  omega

lemma firstExcess_eq_zero (p : ℕ) (hp : 8 ≤ p) : firstExcess p = 0 := by
  have hr : (8 : ℝ) ≤ p := by exact_mod_cast hp
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hr
  exact max_eq_left (sub_nonpos.mpr h)

def C8 : ℝ :=
  (3 / 8 : ℝ) * Real.log 2 + (5 / 24 : ℝ) * Real.log 3 +
    (3 / 40 : ℝ) * Real.log 5 + (1 / 56 : ℝ) * Real.log 7

lemma sum_small_excess :
    (∑ p ∈ smallPrimes, firstExcess p * Real.log (p : ℝ)) = C8 := by
  norm_num [smallPrimes, firstExcess, C8]; ring

lemma sum_excess_le_C8 (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, firstExcess p * Real.log (p : ℝ)) ≤ C8 := by
  have hsupp (p : ℕ) (hp : p ∈ P) (hn : p ∉ smallPrimes) :
      firstExcess p * Real.log (p : ℝ) = 0 := by
    have h8 : 8 ≤ p := by
      by_contra hc
      have he := prime_lt_eight p (hP p hp) (by omega)
      simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hn
      tauto
    simp [firstExcess_eq_zero p h8]
  calc
    (∑ p ∈ P, firstExcess p * Real.log (p : ℝ)) =
        ∑ p ∈ P ∩ smallPrimes, firstExcess p * Real.log (p : ℝ) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro p hp hn
      exact hsupp p hp (by simpa [hp] using hn)
    _ ≤ ∑ p ∈ smallPrimes, firstExcess p * Real.log (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro p hp hn
      exact mul_nonneg (le_max_left _ _) (log_nat_nonneg p)
    _ = C8 := sum_small_excess

def halfBudget (P : Finset ℕ) (r : ℕ → ℕ) : ℝ :=
  ∑ p ∈ P, ((r p / 2 : ℕ) : ℝ) * Real.log (p : ℝ)

def primeLayerBudget (P : Finset ℕ) (r : ℕ → ℕ) : ℝ :=
  ∑ p ∈ P, layerSum p (r p / 2) * Real.log (p : ℝ)

lemma primeLayerBudget_le (P : Finset ℕ) (r : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeLayerBudget P r ≤ halfBudget P r / 8 + C8 := by
  have he := sum_excess_le_C8 P hP
  calc
    primeLayerBudget P r ≤
        ∑ p ∈ P, ((((r p / 2 : ℕ) : ℝ) / 8) + firstExcess p) *
          Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (layerSum_le_eighth p (hP p hp).two_le (r p / 2)) (log_nat_nonneg p)
    _ = halfBudget P r / 8 + ∑ p ∈ P, firstExcess p * Real.log (p : ℝ) := by
      simp only [add_mul, Finset.sum_add_distrib, halfBudget, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ halfBudget P r / 8 + C8 := by linarith

lemma two_halfBudget_le (P : Finset ℕ) (r : ℕ → ℕ) :
    2 * halfBudget P r ≤ ∑ p ∈ P, (r p : ℝ) * Real.log (p : ℝ) := by
  unfold halfBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hn : 2 * (r p / 2) ≤ r p := by omega
  have hr : (2 : ℝ) * ((r p / 2 : ℕ) : ℝ) ≤ (r p : ℝ) := by
    exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hr (log_nat_nonneg p)
  nlinarith

theorem exponent_budget8 (P : Finset ℕ) (r : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N B V : ℝ)
    (hN : 16 ≤ N) (hB : halfBudget P r ≤ B)
    (hV : V ≤ N * primeLayerBudget P r - 2 * halfBudget P r) :
    V ≤ (N / 8 - 2) * B + N * C8 := by
  have hL := primeLayerBudget_le P r hP
  have hN0 : 0 ≤ N := by linarith
  have hc : 0 ≤ N / 8 - 2 := by linarith
  calc
    V ≤ N * primeLayerBudget P r - 2 * halfBudget P r := hV
    _ ≤ N * (halfBudget P r / 8 + C8) - 2 * halfBudget P r := by
      nlinarith [mul_le_mul_of_nonneg_left hL hN0]
    _ = (N / 8 - 2) * halfBudget P r + N * C8 := by ring
    _ ≤ (N / 8 - 2) * B + N * C8 := by
      nlinarith [mul_le_mul_of_nonneg_left hB hc]

lemma C8_lt_of_log_bounds
    (h2 : Real.log 2 < 7 / 10) (h3 : Real.log 3 < 11 / 10)
    (h5 : Real.log 5 < 13 / 8) (h7 : Real.log 7 < 2) : C8 < 13 / 20 := by
  unfold C8
  linarith

end EventualIrreducibility.UniversalLocalDraft

open Polynomial

universe u

namespace EventualIrreducibility.UniversalSlopeDraft

def PureGauss {E : Type u} [Field E]
    (P : E[X]) (v : AbsoluteValue E ℝ) (c : ℝ) : Prop :=
  IsMinGaussIndex P v c 0 ∧ IsMaxGaussIndex P v c P.natDegree

section PureAlgebra

variable {E : Type u} [Field E] {v : AbsoluteValue E ℝ} {c : ℝ}

lemma gauss_attainer_le_degree (P : E[X]) (hP : P ≠ 0) (hc : 0 < c)
    (i : ℕ) (hi : P.gaussNorm v c = v (P.coeff i) * c ^ i) :
    i ≤ P.natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  intro hz
  have hpos := gaussNorm_pos_of_ne_zero (v := v) hc P hP
  rw [hi, hz, map_zero, zero_mul] at hpos
  exact (lt_irrefl 0) hpos

theorem pureGauss_of_mul (hna : IsNonarchimedean v) (hc : 0 < c)
    (A B : E[X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : PureGauss (A * B) v c) :
    PureGauss A v c ∧ PureGauss B v c := by
  obtain ⟨i, hi⟩ := A.exists_min_eq_gaussNorm v hc.le
  obtain ⟨j, hj⟩ := B.exists_min_eq_gaussNorm v hc.le
  change IsMinGaussIndex A v c i at hi
  change IsMinGaussIndex B v c j at hj
  obtain ⟨k, hk⟩ := exists_maxGaussIndex (v := v) hc A hA
  obtain ⟨l, hl⟩ := exists_maxGaussIndex (v := v) hc B hB
  have hmin : i + j = 0 :=
    assembly_min_unique (A * B) c (i + j) 0
      (minGaussIndex_mul hna hc A B hA hB i j hi hj) hAB.1
  have hmax : k + l = (A * B).natDegree :=
    assembly_max_unique (A * B) c (k + l) (A * B).natDegree
      (maxGaussIndex_mul hna hc A B hA hB k l hk hl) hAB.2
  have hkdeg := gauss_attainer_le_degree A hA hc k hk.1
  have hldeg := gauss_attainer_le_degree B hB hc l hl.1
  have hdeg : (A * B).natDegree = A.natDegree + B.natDegree :=
    Polynomial.natDegree_mul hA hB
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  have hk0 : k = A.natDegree := by omega
  have hl0 : l = B.natDegree := by omega
  exact ⟨⟨by simpa only [hi0] using hi, by simpa only [hk0] using hk⟩,
    ⟨by simpa only [hj0] using hj, by simpa only [hl0] using hl⟩⟩

theorem pureGauss_of_dvd (hna : IsNonarchimedean v) (hc : 0 < c)
    (P D : E[X]) (hP : P ≠ 0) (hpure : PureGauss P v c) (hD : D ∣ P) :
    PureGauss D v c := by
  rcases hD with ⟨H, rfl⟩
  have hD0 : D ≠ 0 := (mul_ne_zero_iff.mp hP).1
  have hH0 : H ≠ 0 := (mul_ne_zero_iff.mp hP).2
  exact (pureGauss_of_mul hna hc D H hD0 hH0 hpure).1

theorem denominator_dvd_pure_degree (P : E[X]) (hP : P ≠ 0)
    (b : ℕ) (hb : 0 < b)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (hpure : PureGauss P v (Real.exp (-(1 : ℝ) / (b : ℝ)))) :
    b ∣ P.natDegree := by
  simpa only [Nat.sub_zero] using
    discrete_gauss_width_dvd P hP b 0 P.natDegree hb (Nat.zero_le _)
      hdiscrete hpure.1.1 hpure.2.1

theorem irreducible_of_pure_degree (P : E[X]) (hP : P.Monic)
    (hna : IsNonarchimedean v) (b : ℕ) (hb : 0 < b)
    (hdegree : P.natDegree = b)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (hpure : PureGauss P v (Real.exp (-(1 : ℝ) / (b : ℝ)))) :
    Irreducible P := by
  have hP1 : P ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hdegree
    omega
  rw [hP.irreducible_iff_lt_natDegree_lt hP1]
  intro D hD hsize hdiv
  have hDp := pureGauss_of_dvd hna (Real.exp_pos _) P D hP.ne_zero hpure hdiv
  have hdvd := denominator_dvd_pure_degree D hD.ne_zero b hb hdiscrete hDp
  have hd := Finset.mem_Ioc.mp hsize
  have hbD : b ≤ D.natDegree := Nat.le_of_dvd hd.1 hdvd
  rw [hdegree] at hd
  omega

theorem denominator_dvd_divisor_degree (P D : E[X]) (hP : P.Monic)
    (hD : D.Monic) (hdiv : D ∣ P) (hna : IsNonarchimedean v)
    (b : ℕ) (hb : 0 < b)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (hpure : PureGauss P v (Real.exp (-(1 : ℝ) / (b : ℝ)))) :
    b ∣ D.natDegree := by
  exact denominator_dvd_pure_degree D hD.ne_zero b hb hdiscrete
    (pureGauss_of_dvd hna (Real.exp_pos _) P D hP.ne_zero hpure hdiv)

end PureAlgebra

section BaseChange

variable {E K : Type u} [Field E] [Field K]
    {v : AbsoluteValue E ℝ} {w : AbsoluteValue K ℝ}

lemma gaussNorm_map_isometric (ι : E →+* K)
    (hι : ∀ x, w (ι x) = v x) (P : E[X]) (c : ℝ) (hc : 0 ≤ c) :
    (P.map ι).gaussNorm w c = P.gaussNorm v c := by
  obtain ⟨i, hi, _⟩ := P.exists_min_eq_gaussNorm v hc
  obtain ⟨j, hj, _⟩ := (P.map ι).exists_min_eq_gaussNorm w hc
  apply le_antisymm
  · rw [hj, Polynomial.coeff_map, hι]
    exact P.le_gaussNorm v hc j
  · rw [hi]
    have h := (P.map ι).le_gaussNorm w hc i
    simpa only [Polynomial.coeff_map, hι] using h

theorem pureGauss_map (ι : E →+* K) (hι : ∀ x, w (ι x) = v x)
    (P : E[X]) (hP : P.Monic) (c : ℝ) (hc : 0 ≤ c)
    (hpure : PureGauss P v c) : PureGauss (P.map ι) w c := by
  have hnorm := gaussNorm_map_isometric ι hι P c hc
  constructor
  · constructor
    · rw [hnorm, Polynomial.coeff_map, hι]
      exact hpure.1.1
    · intro j hj
      rw [Polynomial.coeff_map, hι, hnorm]
      exact hpure.1.2 j hj
  · change IsMaxGaussIndex (P.map ι) w c (P.map ι).natDegree
    rw [hP.natDegree_map ι]
    constructor
    · rw [hnorm, Polynomial.coeff_map, hι]
      exact hpure.2.1
    · intro j hj
      rw [Polynomial.coeff_map, hι, hnorm]
      exact hpure.2.2 j hj

theorem root_norm_of_pureGauss (P : K[X]) (hP : P.Monic)
    (hna : IsNonarchimedean w) (c : ℝ) (hc : 0 < c)
    (hpure : PureGauss P w c) (α : K) (hroot : P.IsRoot α) : w α = c := by
  have hlin : (X - C α : K[X]) ∣ P := Polynomial.dvd_iff_isRoot.mpr hroot
  have hp := pureGauss_of_dvd hna hc P (X - C α) hP.ne_zero hpure hlin
  have ht := hp.1.1.symm.trans hp.2.1
  simpa using ht

theorem mapped_packet_root_norm (ι : E →+* K)
    (hι : ∀ x, w (ι x) = v x) (hna : IsNonarchimedean w)
    (P : E[X]) (hP : P.Monic) (c : ℝ) (hc : 0 < c)
    (hpure : PureGauss P v c) (α : K) (hroot : (P.map ι).IsRoot α) :
    w α = c := by
  exact root_norm_of_pureGauss (P.map ι) (hP.map ι) hna c hc
    (pureGauss_map ι hι P hP c hc.le hpure) α hroot

end BaseChange

structure PrimeToPUnramifiedData (p m : ℕ) where
  E : Type
  [normedField : NormedField E]
  [charZero : CharZero E]
  [completeSpace : CompleteSpace E]
  v : AbsoluteValue E ℝ
  nonarchimedean : IsNonarchimedean v
  norm_eq : ∀ x : E, v x = ‖x‖
  discrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ))
  nat_norm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ))
  ζ : Fin m → E
  roots : ∀ i, ζ i ^ m = 1
  units : ∀ i, v (ζ i) = 1
  separated : ∀ i j, i ≠ j → v (ζ i - ζ j) = 1
  one_root : ∃ i, ζ i = 1
  factorization : (X ^ m - 1 : E[X]) = ∏ i, (X - C (ζ i))

attribute [instance] PrimeToPUnramifiedData.normedField
  PrimeToPUnramifiedData.charZero PrimeToPUnramifiedData.completeSpace

def StandardUnramifiedInput : Prop :=
  ∀ p m : ℕ, p.Prime → 0 < m → ¬ p ∣ m →
    Nonempty (PrimeToPUnramifiedData p m)

structure ValuedSplittingData (E : Type u) [NormedField E]
    (v : AbsoluteValue E ℝ) (P : E[X]) where
  K : Type u
  [normedField : NormedField K]
  [algebra : Algebra E K]
  [finiteDimensional : FiniteDimensional E K]
  [completeSpace : CompleteSpace K]
  w : AbsoluteValue K ℝ
  nonarchimedean : IsNonarchimedean w
  norm_eq : ∀ x : K, w x = ‖x‖
  restrict : ∀ x : E, w (algebraMap E K x) = v x
  splits : (P.map (algebraMap E K)).Splits

attribute [instance] ValuedSplittingData.normedField ValuedSplittingData.algebra
  ValuedSplittingData.finiteDimensional ValuedSplittingData.completeSpace

def StandardValuedSplittingInput : Prop :=
  ∀ (E : Type u) [NormedField E] [CompleteSpace E]
    (v : AbsoluteValue E ℝ), IsNonarchimedean v →
    (∀ x : E, v x = ‖x‖) → ∀ P : E[X], P ≠ 0 →
      Nonempty (ValuedSplittingData E v P)

structure SlopeFactorData {E : Type u} [Field E]
    (P : E[X]) (v : AbsoluteValue E ℝ) (c : ℝ) (i j : ℕ) where
  Q : E[X]
  R : E[X]
  monic_Q : Q.Monic
  monic_R : R.Monic
  factorization : P = Q * R
  degree_Q : Q.natDegree = j - i
  pure_Q : PureGauss Q v c
  rest_min : IsMinGaussIndex R v c i
  rest_max : IsMaxGaussIndex R v c i

def StandardSlopeFactorInput : Prop :=
  ∀ (E : Type u) [NormedField E] [CompleteSpace E]
    (v : AbsoluteValue E ℝ), IsNonarchimedean v →
    (∀ x : E, v x = ‖x‖) → ∀ (P : E[X]), P.Monic →
    ∀ c : ℝ, 0 < c → ∀ i j : ℕ,
      IsMinGaussIndex P v c i → IsMaxGaussIndex P v c j →
        Nonempty (SlopeFactorData P v c i j)

section InterfaceConsequences

variable {E : Type u} [NormedField E] [CompleteSpace E]
    (v : AbsoluteValue E ℝ)

theorem exists_irreducible_slope_factor (hstd : StandardSlopeFactorInput.{u})
    (hna : IsNonarchimedean v) (hnorm : ∀ x : E, v x = ‖x‖)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (P : E[X]) (hP : P.Monic) (b i j : ℕ) (hb : 0 < b)
    (hwidth : j - i = b)
    (hmin : IsMinGaussIndex P v (Real.exp (-(1 : ℝ) / (b : ℝ))) i)
    (hmax : IsMaxGaussIndex P v (Real.exp (-(1 : ℝ) / (b : ℝ))) j) :
    ∃ D : SlopeFactorData P v (Real.exp (-(1 : ℝ) / (b : ℝ))) i j,
      Irreducible D.Q := by
  obtain ⟨D⟩ := hstd E v hna hnorm P hP _ (Real.exp_pos _) i j hmin hmax
  refine ⟨D, ?_⟩
  exact irreducible_of_pure_degree D.Q D.monic_Q hna b hb
    (D.degree_Q.trans hwidth) hdiscrete D.pure_Q

end InterfaceConsequences

end EventualIrreducibility.UniversalSlopeDraft

open Polynomial

namespace EventualIrreducibility.UniversalOrdinaryFacesDraft

open ActualEnvelope FirstFace UniversalSlopeDraft

section ActualCoefficients

variable {R : Type u} [CommRing R] [Nontrivial R]
    {v : AbsoluteValue R ℝ}

def OrdinaryRootSource (n p r : ℕ) (z : R) : Prop :=
  (padicValNat p n = r ∧ z ^ n = 1) ∨
    (padicValNat p (n + 1) = r ∧ z ^ (n + 1) = 1)

theorem actual_ordinary_envelope (n p r : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hr : 1 ≤ r) (z : R)
    (hnorm : ∀ t : ℕ, t ≠ 0 →
      v (t : R) = Real.exp (-(padicValNat p t : ℝ)))
    (hz : v z = 1) (hsep : v (1 - z) = 1)
    (hsource : OrdinaryRootSource n p r z) :
    TaylorEnvelope (shiftedTrinomial n z) v p r := by
  rcases hsource with ⟨hval, hroot⟩ | ⟨hval, hroot⟩
  · exact taylor_envelope_of_root_n n p r hn hp hr hval z
      hnorm hroot hz hsep
  · exact taylor_envelope_of_root_N n p r hp hr hval z
      hnorm hroot hz hsep

structure OrdinaryFaces (P : R[X]) (v : AbsoluteValue R ℝ) (p r : ℕ) : Prop where
  first_min : IsMinGaussIndex P v (Real.exp (-(1 : ℝ) / (p : ℝ))) 0
  first_max : IsMaxGaussIndex P v (Real.exp (-(1 : ℝ) / (p : ℝ)))
    (firstFaceLast p r)
  later : ∀ k, 1 ≤ k → k < r → ¬ (p = 2 ∧ k = 1) →
    IsMinGaussIndex P v (Real.exp (-(1 : ℝ) / (laterDenom p k : ℝ))) (p ^ k) ∧
      IsMaxGaussIndex P v (Real.exp (-(1 : ℝ) / (laterDenom p k : ℝ)))
        (p ^ (k + 1))
  terminal : IsMinGaussIndex P v 1 (p ^ r)

theorem actual_ordinary_faces (n p r : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hr : 1 ≤ r) (z : R)
    (hnorm : ∀ t : ℕ, t ≠ 0 →
      v (t : R) = Real.exp (-(padicValNat p t : ℝ)))
    (hz : v z = 1) (hsep : v (1 - z) = 1)
    (hsource : OrdinaryRootSource n p r z) :
    OrdinaryFaces (shiftedTrinomial n z) v p r := by
  have H := actual_ordinary_envelope n p r hn hp hr z hnorm hz hsep hsource
  have hf := first_face_and_terminal_of_envelope (shiftedTrinomial n z)
    p r hp.two_le hr H.zero_eq H.vertex_eq H.band_le H.tail_le
  refine ⟨hf.1, hf.2.1, ?_, hf.2.2⟩
  intro k hk hkr hnot
  exact later_face_of_envelope (shiftedTrinomial n z) p r k hp.two_le hk hkr hnot
    H.zero_eq H.vertex_eq H.band_le H.tail_le

omit [Nontrivial R] in
lemma root_of_dividing_exponent (z : R) (m M : ℕ)
    (hdiv : m ∣ M) (hroot : z ^ m = 1) : z ^ M = 1 := by
  obtain ⟨t, rfl⟩ := hdiv
  rw [pow_mul, hroot, one_pow]

lemma shiftedTrinomial_natDegree (n : ℕ) (hn : 0 < n) (z : R) :
    (shiftedTrinomial n z).natDegree = n + 1 := by
  have htop : (shiftedTrinomial n z).coeff (n + 1) = 1 := by
    rw [shiftedTrinomial_coeff_ge_two n z (n + 1) (by omega)]
    simp
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [shiftedTrinomial_coeff_ge_two n z j (by omega)]
    simp [Nat.choose_eq_zero_of_lt hj]
  · rw [htop]
    exact one_ne_zero

lemma shiftedTrinomial_monic (n : ℕ) (hn : 0 < n) (z : R) :
    (shiftedTrinomial n z).Monic := by
  show (shiftedTrinomial n z).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, shiftedTrinomial_natDegree n hn z,
    shiftedTrinomial_coeff_ge_two n z (n + 1) (by omega)]
  simp

end ActualCoefficients

def ordinaryLeft (p i : ℕ) : ℕ := if i = 0 then 0 else p ^ i
def ordinaryRight (p i : ℕ) : ℕ := p ^ (i + 1)
def ordinaryDenom (p i : ℕ) : ℕ := if i = 0 then p else p ^ i * (p - 1)

lemma ordinary_width (p i : ℕ) :
    ordinaryRight p i - ordinaryLeft p i = ordinaryDenom p i := by
  by_cases hi : i = 0
  · simp [ordinaryRight, ordinaryLeft, ordinaryDenom, hi]
  · simp only [ordinaryRight, ordinaryLeft, ordinaryDenom, hi, if_false,
      pow_succ, Nat.mul_sub_left_distrib, Nat.mul_one]

lemma ordinaryDenom_pos (p i : ℕ) (hp : 2 ≤ p) : 0 < ordinaryDenom p i := by
  by_cases hi : i = 0
  · simp only [ordinaryDenom, hi, if_true]
    omega
  · simp only [ordinaryDenom, hi, if_false]
    exact mul_pos (pow_pos (by omega) i) (by omega)

theorem ordinary_odd_face {R : Type u} [CommRing R] [Nontrivial R]
    {v : AbsoluteValue R ℝ} (P : R[X]) (p r : ℕ) (hpodd : p ≠ 2)
    (H : OrdinaryFaces P v p r) (i : ℕ) (hi : i < r) :
    IsMinGaussIndex P v (Real.exp (-(1 : ℝ) / (ordinaryDenom p i : ℝ)))
      (ordinaryLeft p i) ∧
    IsMaxGaussIndex P v (Real.exp (-(1 : ℝ) / (ordinaryDenom p i : ℝ)))
      (ordinaryRight p i) := by
  by_cases hi0 : i = 0
  · subst i
    simpa [ordinaryDenom, ordinaryLeft, ordinaryRight, firstFaceLast, hpodd]
      using And.intro H.first_min H.first_max
  · have hnot : ¬ (p = 2 ∧ i = 1) := by tauto
    have h := H.later i (by omega) hi hnot
    simpa only [ordinaryDenom, ordinaryLeft, ordinaryRight, hi0, if_false,
      laterDenom] using h

section Extraction

variable {E : Type u} [NormedField E] [CompleteSpace E]
    {v : AbsoluteValue E ℝ}

theorem actual_ordinary_odd_packet
    (hstd : StandardSlopeFactorInput.{u})
    (hna : IsNonarchimedean v) (hmetric : ∀ x : E, v x = ‖x‖)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (n p r : ℕ) (hn : 0 < n) (hp : p.Prime) (hpodd : p ≠ 2) (hr : 1 ≤ r)
    (z : E)
    (hnorm : ∀ t : ℕ, t ≠ 0 →
      v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (hz : v z = 1) (hsep : v (1 - z) = 1)
    (hsource : OrdinaryRootSource n p r z) (i : ℕ) (hi : i < r) :
    ∃ D : SlopeFactorData (shiftedTrinomial n z) v
        (Real.exp (-(1 : ℝ) / (ordinaryDenom p i : ℝ)))
        (ordinaryLeft p i) (ordinaryRight p i),
      Irreducible D.Q := by
  have H := actual_ordinary_faces n p r hn hp hr z hnorm hz hsep hsource
  have hf := ordinary_odd_face (shiftedTrinomial n z) p r hpodd H i hi
  exact exists_irreducible_slope_factor v hstd hna hmetric hdiscrete
    (shiftedTrinomial n z) (shiftedTrinomial_monic n hn z)
    (ordinaryDenom p i) (ordinaryLeft p i) (ordinaryRight p i)
    (ordinaryDenom_pos p i hp.two_le) (ordinary_width p i) hf.1 hf.2

end Extraction

end EventualIrreducibility.UniversalOrdinaryFacesDraft

open Polynomial

namespace EventualIrreducibility.UniversalResidueOneProfileDraft

open ActualEnvelope FirstFace

section Coefficients

variable {R : Type u} [CommRing R] [Nontrivial R]
    {v : AbsoluteValue R ℝ}

noncomputable def oneTranslate (n : ℕ) : R[X] :=
  ∑ j ∈ Finset.range n, monomial j (((n + 1).choose (j + 2) : ℕ) : R)

omit [Nontrivial R] in
lemma coeff_oneTranslate (n j : ℕ) :
    (oneTranslate n : R[X]).coeff j = (((n + 1).choose (j + 2) : ℕ) : R) := by
  classical
  have hc : (oneTranslate n : R[X]).coeff j =
      if j < n then (((n + 1).choose (j + 2) : ℕ) : R) else 0 := by
    simp [oneTranslate, Polynomial.coeff_monomial]
  rw [hc]
  split_ifs with hj
  · rfl
  · simp [Nat.choose_eq_zero_of_lt (show n + 1 < j + 2 by omega)]

omit [Nontrivial R] in
lemma oneTranslate_mul_Xsq (n : ℕ) :
    (X : R[X]) ^ 2 * oneTranslate n = shiftedTrinomial n (1 : R) := by
  rw [pow_two, mul_assoc]
  ext j
  cases j with
  | zero =>
      simp [shiftedTrinomial_coeff_zero]
  | succ j =>
      cases j with
      | zero =>
          simp [shiftedTrinomial_coeff_one]
      | succ k =>
          simp only [Polynomial.coeff_X_mul]
          rw [coeff_oneTranslate,
            shiftedTrinomial_coeff_ge_two n (1 : R) (k + 2) (by omega)]
          simp

lemma oneTranslate_natDegree (n : ℕ) (hn : 0 < n) :
    (oneTranslate n : R[X]).natDegree = n - 1 := by
  have ht : (oneTranslate n : R[X]).coeff (n - 1) = 1 := by
    rw [coeff_oneTranslate, show n - 1 + 2 = n + 1 by omega]
    simp
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_oneTranslate]
    simp [Nat.choose_eq_zero_of_lt (show n + 1 < j + 2 by omega)]
  · rw [ht]
    exact one_ne_zero

lemma oneTranslate_monic (n : ℕ) (hn : 0 < n) : (oneTranslate n : R[X]).Monic := by
  show (oneTranslate n : R[X]).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, oneTranslate_natDegree n hn,
    coeff_oneTranslate, show n - 1 + 2 = n + 1 by omega]
  simp

structure OneProfile (Q : R[X]) (v : AbsoluteValue R ℝ) (p r : ℕ) : Prop where
  level : ∀ j : ℕ, ∃ k : ℕ, k ≤ r ∧ p ^ k ≤ j + 2 ∧
    v (Q.coeff j) ≤ Real.exp (-(r : ℝ) + (k : ℝ))
  vertex : ∀ k, 1 ≤ k → k ≤ r →
    v (Q.coeff (p ^ k - 2)) = Real.exp (-(r : ℝ) + (k : ℝ))
  odd_zero : p ≠ 2 → v (Q.coeff 0) = Real.exp (-(r : ℝ))

omit [Nontrivial R] in
theorem one_profile_of_scalar_valuations
    (n p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (Q : R[X])
    (hcoeff : ∀ j, Q.coeff j = (((n + 1).choose (j + 2) : ℕ) : R))
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : R) = Real.exp (-(padicValNat p t : ℝ)))
    (hpower : p ^ r ≤ n + 1) (D : ℕ → ℕ)
    (hval : ∀ J, 2 ≤ J → J ≤ p ^ r →
      padicValNat p ((n + 1).choose J) + D J = r)
    (hDvertex : ∀ k, 1 ≤ k → D (p ^ k) = k)
    (hDband : ∀ k J, 2 ≤ J → J < p ^ (k + 1) → D J ≤ k)
    (hDtwo : p ≠ 2 → D 2 = 0) : OneProfile Q v p r := by
  have hnormCoeff (j : ℕ) (hj : j + 2 ≤ p ^ r) :
      v (Q.coeff j) = Real.exp (-(padicValNat p ((n + 1).choose (j + 2)) : ℝ)) := by
    rw [hcoeff]
    exact hnorm _ (Nat.choose_ne_zero (hj.trans hpower))
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hj : j + 2 < p ^ r
    · obtain ⟨k, hk, hkj, hjk⟩ := exists_power_band p r (j + 2) (by omega) hj
      refine ⟨k, hk.le, hkj, ?_⟩
      rw [hnormCoeff j hj.le]
      apply Real.exp_le_exp.mpr
      have hv := hval (j + 2) (by omega) hj.le
      have hD := hDband k (j + 2) (by omega) hjk
      have hvR : (padicValNat p ((n + 1).choose (j + 2)) : ℝ) +
          (D (j + 2) : ℝ) = (r : ℝ) := by exact_mod_cast hv
      have hDR : (D (j + 2) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hD
      linarith
    · refine ⟨r, le_rfl, by omega, ?_⟩
      rw [hcoeff]
      simpa only [neg_add_cancel, Real.exp_zero] using
        norm_natCast_le_one p hnorm ((n + 1).choose (j + 2))
  · intro k hk hkr
    have hpk := prime_power_ge_two p k hp hk
    have hbound := prime_power_le_of_index_le p k r hp hkr
    have hidx : p ^ k - 2 + 2 = p ^ k := by omega
    rw [hnormCoeff (p ^ k - 2) (by omega), hidx]
    apply congrArg Real.exp
    have hv := hval (p ^ k) hpk hbound
    rw [hDvertex k hk] at hv
    have hvR : (padicValNat p ((n + 1).choose (p ^ k)) : ℝ) +
        (k : ℝ) = (r : ℝ) := by exact_mod_cast hv
    linarith
  · intro hpne
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpr : p ≤ p ^ r := by
      simpa using prime_power_le_of_index_le p 1 r hp hr
    have hb : 2 ≤ p ^ r := by omega
    rw [hnormCoeff 0 (by simpa using hb)]
    apply congrArg Real.exp
    have hv := hval 2 (by omega) hb
    rw [hDtwo hpne, Nat.add_zero] at hv
    simp only [Nat.zero_add, hv]

lemma prime_not_dvd_two (p : ℕ) (hp : p.Prime) (hpne : p ≠ 2) : ¬ p ∣ 2 := by
  intro h
  have hlo := hp.two_le
  have hhi := Nat.le_of_dvd (by norm_num : 0 < (2 : ℕ)) h
  omega

omit [Nontrivial R] in
theorem actual_one_profile (n p r : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hr : 1 ≤ r)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : R) = Real.exp (-(padicValNat p t : ℝ)))
    (hsource : padicValNat p n = r ∨ padicValNat p (n + 1) = r) :
    OneProfile (oneTranslate n : R[X]) v p r := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hsource with hval | hval
  · have hdiv := power_dvd_of_padicVal_eq p n r hp hn hval
    have hpower : p ^ r ≤ n + 1 := (Nat.le_of_dvd hn hdiv).trans (by omega)
    apply one_profile_of_scalar_valuations n p r hp hr (oneTranslate n)
      (coeff_oneTranslate n) hnorm hpower (fun J => padicValNat p (J * (J - 1)))
    · intro J hJ hJr
      simpa only [hval] using
        choose_successor_valuation_add p hp r n J hr hn hdiv hJ (by omega)
    · intro k hk
      exact padicVal_prime_power_mul_pred p k hp hk
    · intro k J hJ hJr
      exact padicVal_mul_pred_le_of_lt_power p J k hp hJ hJr
    · intro hpne
      simpa using padicValNat.eq_zero_of_not_dvd (prime_not_dvd_two p hp hpne)
  · have hN : 0 < n + 1 := by omega
    have hdiv := power_dvd_of_padicVal_eq p (n + 1) r hp hN hval
    have hpower : p ^ r ≤ n + 1 := Nat.le_of_dvd hN hdiv
    apply one_profile_of_scalar_valuations n p r hp hr (oneTranslate n)
      (coeff_oneTranslate n) hnorm hpower (fun J => padicValNat p J)
    · intro J hJ hJr
      simpa only [hval] using choose_valuation_add p hp r (n + 1) J hN hdiv (by omega) hJr
    · intro k hk
      exact padicValNat.prime_pow k
    · intro k J hJ hJr
      exact padicVal_le_of_lt_power p J k hp (by omega) hJr
    · intro hpne
      exact padicValNat.eq_zero_of_not_dvd (prime_not_dvd_two p hp hpne)

end Coefficients

section TranslationIdentity

variable {E : Type u} [Field E]

lemma oneTranslate_eq_comp (n : ℕ) :
    (oneTranslate n : E[X]) =
      ((fInt n).map (Int.castRingHom E)).comp (X + C 1) := by
  have ht := congrArg (fun P : E[X] => P.comp (X + C 1))
    (Simplicity.mapped_trinomial_from_integer (K := E) (trinomial_identity n))
  have ht' : (X : E[X]) ^ 2 *
      ((fInt n).map (Int.castRingHom E)).comp (X + C 1) =
        shiftedTrinomial n (1 : E) := by
    simpa [shiftedTrinomial] using ht
  apply mul_left_cancel₀ (pow_ne_zero 2 (Polynomial.X_ne_zero : (X : E[X]) ≠ 0))
  exact (oneTranslate_mul_Xsq n).trans ht'.symm

end TranslationIdentity

end EventualIrreducibility.UniversalResidueOneProfileDraft

open Polynomial

namespace EventualIrreducibility.UniversalResidueOneFacesDraft

open FirstFace UniversalResidueOneProfileDraft

lemma pow_ge_two (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) : 2 ≤ p ^ k := by
  have h := mul_index_le_pow p k hp hk
  nlinarith

lemma shifted_first_line_le (p k j : ℕ) (hp : 2 ≤ p)
    (hlevel : p ^ k ≤ j + 2) : (p - 2) * k ≤ j := by
  by_cases hk : k = 0
  · simp [hk]
  · have hk1 : 1 ≤ k := by omega
    have h := mul_index_le_pow p k hp hk1
    have hp' : p - 2 + 2 = p := Nat.sub_add_cancel hp
    nlinarith

lemma shifted_first_line_strict (p k j : ℕ) (hp : 2 ≤ p)
    (hlevel : p ^ k ≤ j + 2) (hj : p - 2 < j) : (p - 2) * k < j := by
  by_cases hk0 : k = 0
  · simp only [hk0, mul_zero]
    omega
  by_cases hk1 : k = 1
  · simpa only [hk1, mul_one] using hj
  have hk2 : 2 ≤ k := by omega
  have h := mul_index_le_pow p k hp (by omega)
  have hp' : p - 2 + 2 = p := Nat.sub_add_cancel hp
  nlinarith

lemma shifted_later_line_le (p k l j : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k)
    (hlevel : p ^ l ≤ j + 2) :
    (p ^ k - 2) + laterDenom p k * l ≤ j + laterDenom p k * k := by
  have h := later_line_le_at_index p k l (j + 2) hp hlevel
  have hpow := pow_ge_two p k hp hk
  omega

lemma shifted_later_line_strict (p k l j : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k)
    (hlevel : p ^ l ≤ j + 2)
    (hout : j < p ^ k - 2 ∨ p ^ (k + 1) - 2 < j) :
    (p ^ k - 2) + laterDenom p k * l < j + laterDenom p k * k := by
  have hpow := pow_ge_two p k hp hk
  have hpow' := pow_ge_two p (k + 1) hp (by omega)
  have hout' : j + 2 < p ^ k ∨ p ^ (k + 1) < j + 2 := by
    rcases hout with h | h
    · left; omega
    · right; omega
  have h := later_line_strict_at_index p k l (j + 2) hp hlevel hout'
  omega

lemma shifted_later_endpoint_eq (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (p ^ k - 2) + laterDenom p k * (k + 1) =
      (p ^ (k + 1) - 2) + laterDenom p k * k := by
  have h := later_line_endpoint_eq p k hp
  have hpow := pow_ge_two p k hp hk
  have hpow' := pow_ge_two p (k + 1) hp (by omega)
  omega

section Faces

variable {R : Type u} [CommRing R] [Nontrivial R]
    {v : AbsoluteValue R ℝ}

omit [Nontrivial R] in
lemma one_profile_coeff_le_one (Q : R[X]) (p r : ℕ) (H : OneProfile Q v p r)
    (j : ℕ) : v (Q.coeff j) ≤ 1 := by
  obtain ⟨k, hkr, _, hk⟩ := H.level j
  apply hk.trans
  apply Real.exp_le_one_iff.mpr
  have hkrR : (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hkr
  linarith

omit [Nontrivial R] in
theorem one_first_face_odd (Q : R[X]) (p r : ℕ) (hp : 3 ≤ p) (hr : 1 ≤ r)
    (H : OneProfile Q v p r) :
    IsMinGaussIndex Q v (Real.exp (-(1 : ℝ) / ((p - 2 : ℕ) : ℝ))) 0 ∧
      IsMaxGaussIndex Q v (Real.exp (-(1 : ℝ) / ((p - 2 : ℕ) : ℝ))) (p - 2) := by
  let b : ℕ := p - 2
  let c : ℝ := Real.exp (-(1 : ℝ) / (b : ℝ))
  have hb : 0 < b := by dsimp [b]; omega
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hc : 0 < c := Real.exp_pos _
  have hzero := H.odd_zero (by omega : p ≠ 2)
  have hbound (j : ℕ) : v (Q.coeff j) * c ^ j ≤ Real.exp (-(r : ℝ)) := by
    obtain ⟨k, _, hlevel, hk⟩ := H.level j
    have hline := shifted_first_line_le p k j (by omega) hlevel
    have ht := later_weight_le_from_line Q b r 0 k j 0 hb
      (by simpa only [zero_add, mul_zero, add_zero, b] using hline) hk
    simpa only [Nat.cast_zero, add_zero, zero_div, sub_zero, c] using ht
  have hnorm : Q.gaussNorm v c = Real.exp (-(r : ℝ)) := by
    obtain ⟨j, hj, _⟩ := Q.exists_min_eq_gaussNorm v hc.le
    apply le_antisymm
    · rw [hj]
      exact hbound j
    · simpa only [hzero, pow_zero, mul_one] using Q.le_gaussNorm v hc.le 0
  have hvertex : v (Q.coeff b) = Real.exp (-(r : ℝ) + 1) := by
    simpa only [pow_one, Nat.cast_one, b] using H.vertex 1 (by omega) hr
  have hright : v (Q.coeff b) * c ^ b = Real.exp (-(r : ℝ)) := by
    rw [hvertex]
    have ht := exp_first_weight b r 1 b
    simpa only [Nat.cast_one, div_self hbR, add_sub_cancel_right, c] using ht
  constructor
  · constructor
    · simpa only [hzero, pow_zero, mul_one] using hnorm
    · intro j hj
      omega
  · constructor
    · exact hnorm.trans hright.symm
    · intro j hj
      rw [hnorm]
      obtain ⟨k, _, hlevel, hk⟩ := H.level j
      have hline := shifted_first_line_strict p k j (by omega) hlevel hj
      have ht := later_weight_lt_from_line Q b r 0 k j 0 hb
        (by simpa only [zero_add, mul_zero, add_zero, b] using hline) hk
      simpa only [Nat.cast_zero, add_zero, zero_div, sub_zero, c] using ht

omit [Nontrivial R] in
theorem one_later_face (Q : R[X]) (p r k : ℕ)
    (hp : 2 ≤ p) (hk : 1 ≤ k) (hkr : k < r) (H : OneProfile Q v p r) :
    IsMinGaussIndex Q v (Real.exp (-(1 : ℝ) / (laterDenom p k : ℝ)))
        (p ^ k - 2) ∧
      IsMaxGaussIndex Q v (Real.exp (-(1 : ℝ) / (laterDenom p k : ℝ)))
        (p ^ (k + 1) - 2) := by
  let b : ℕ := laterDenom p k
  let c : ℝ := Real.exp (-(1 : ℝ) / (b : ℝ))
  let q : ℕ := p ^ k - 2
  let q' : ℕ := p ^ (k + 1) - 2
  let B : ℝ := Real.exp (-(r : ℝ) + (k : ℝ) - (q : ℝ) / (b : ℝ))
  have hb : 0 < b := laterDenom_pos p k hp
  have hc : 0 < c := Real.exp_pos _
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  have hbound (j : ℕ) : v (Q.coeff j) * c ^ j ≤ B := by
    obtain ⟨l, _, hlevel, hl⟩ := H.level j
    exact later_weight_le_from_line Q b r k l j q hb
      (shifted_later_line_le p k l j hp hk hlevel) hl
  have hleft : v (Q.coeff q) * c ^ q = B := by
    rw [H.vertex k hk hkr.le]
    exact exp_first_weight b r k q
  have hright : v (Q.coeff q') * c ^ q' = B := by
    rw [H.vertex (k + 1) (by omega) (by omega)]
    rw [exp_first_weight b r (k + 1) q']
    apply congrArg Real.exp
    have hline := shifted_later_endpoint_eq p k hp hk
    have hlineR : (q : ℝ) + (b : ℝ) * ((k + 1 : ℕ) : ℝ) =
        (q' : ℝ) + (b : ℝ) * (k : ℝ) := by exact_mod_cast hline
    apply mul_left_cancel₀ hbne
    nlinarith [div_mul_cancel₀ (q : ℝ) hbne, div_mul_cancel₀ (q' : ℝ) hbne]
  have hnorm : Q.gaussNorm v c = B := by
    obtain ⟨j, hj, _⟩ := Q.exists_min_eq_gaussNorm v hc.le
    apply le_antisymm
    · rw [hj]
      exact hbound j
    · rw [← hleft]
      exact Q.le_gaussNorm v hc.le q
  constructor
  · constructor
    · exact hnorm.trans hleft.symm
    · intro j hj
      rw [hnorm]
      obtain ⟨l, _, hlevel, hl⟩ := H.level j
      exact later_weight_lt_from_line Q b r k l j q hb
        (shifted_later_line_strict p k l j hp hk hlevel (Or.inl hj)) hl
  · constructor
    · exact hnorm.trans hright.symm
    · intro j hj
      rw [hnorm]
      obtain ⟨l, _, hlevel, hl⟩ := H.level j
      exact later_weight_lt_from_line Q b r k l j q hb
        (shifted_later_line_strict p k l j hp hk hlevel (Or.inr hj)) hl

omit [Nontrivial R] in
theorem one_terminal_minimum (Q : R[X]) (p r : ℕ)
    (hp : 2 ≤ p) (hr : 1 ≤ r) (H : OneProfile Q v p r) :
    IsMinGaussIndex Q v 1 (p ^ r - 2) := by
  have hvertex : v (Q.coeff (p ^ r - 2)) = 1 := by
    simpa only [neg_add_cancel, Real.exp_zero] using H.vertex r hr le_rfl
  have hnorm : Q.gaussNorm v 1 = 1 := gaussNorm_one_eq_one Q
    (one_profile_coeff_le_one Q p r H) ⟨p ^ r - 2, hvertex⟩
  constructor
  · simp only [hnorm, hvertex, one_pow, mul_one]
  · intro j hj
    obtain ⟨k, hkr, hlevel, hk⟩ := H.level j
    have hpow := pow_ge_two p r hp hr
    have hklt : k < r := by
      by_contra h
      have heq : k = r := by omega
      rw [heq] at hlevel
      omega
    have hkR : (k : ℝ) < (r : ℝ) := by exact_mod_cast hklt
    simp only [one_pow, mul_one, hnorm]
    exact hk.trans_lt (Real.exp_lt_one_iff.mpr (by linarith))

omit [Nontrivial R] in
theorem binary_one_r1 (Q : R[X]) (H : OneProfile Q v 2 1) :
    v (Q.coeff 0) = 1 ∧ IsMinGaussIndex Q v 1 0 := by
  constructor
  · simpa using H.vertex 1 (by omega) (by omega)
  · simpa using one_terminal_minimum Q 2 1 (by omega) (by omega) H

end Faces

section ActualFaces

variable {R : Type u} [CommRing R] [Nontrivial R] {v : AbsoluteValue R ℝ}

omit [Nontrivial R] in
theorem actual_residue_one_faces (n p r : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hr : 1 ≤ r)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : R) = Real.exp (-(padicValNat p t : ℝ)))
    (hsource : padicValNat p n = r ∨ padicValNat p (n + 1) = r) :
    (p ≠ 2 →
      IsMinGaussIndex (oneTranslate n : R[X]) v
          (Real.exp (-(1 : ℝ) / ((p - 2 : ℕ) : ℝ))) 0 ∧
        IsMaxGaussIndex (oneTranslate n : R[X]) v
          (Real.exp (-(1 : ℝ) / ((p - 2 : ℕ) : ℝ))) (p - 2)) ∧
    (∀ k, 1 ≤ k → k < r →
      IsMinGaussIndex (oneTranslate n : R[X]) v
          (Real.exp (-(1 : ℝ) / (laterDenom p k : ℝ))) (p ^ k - 2) ∧
        IsMaxGaussIndex (oneTranslate n : R[X]) v
          (Real.exp (-(1 : ℝ) / (laterDenom p k : ℝ))) (p ^ (k + 1) - 2)) ∧
    IsMinGaussIndex (oneTranslate n : R[X]) v 1 (p ^ r - 2) := by
  have H := actual_one_profile n p r hn hp hr hnorm hsource
  refine ⟨?_, ?_, one_terminal_minimum _ p r hp.two_le hr H⟩
  · intro hpne
    exact one_first_face_odd _ p r (by have := hp.two_le; omega) hr H
  · intro k hk hkr
    exact one_later_face _ p r k hp.two_le hk hkr H

end ActualFaces

end EventualIrreducibility.UniversalResidueOneFacesDraft

open Polynomial

namespace EventualIrreducibility.UniversalResidueOneExtractionDraft

open FirstFace UniversalSlopeDraft UniversalResidueOneProfileDraft
  UniversalResidueOneFacesDraft

lemma residue_one_later_width (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (p ^ (k + 1) - 2) - (p ^ k - 2) = laterDenom p k := by
  have hpow := pow_ge_two p k hp hk
  have hpow' := pow_ge_two p (k + 1) hp (by omega)
  have hmul : p ^ k * (p - 1) + p ^ k = p ^ (k + 1) := by
    have hp' : p - 1 + 1 = p := by omega
    calc
      p ^ k * (p - 1) + p ^ k = p ^ k * (p - 1 + 1) := by ring
      _ = p ^ (k + 1) := by rw [hp', pow_succ]
  dsimp [laterDenom]
  omega

section Extraction

variable {E : Type u} [NormedField E] [CompleteSpace E]
    {v : AbsoluteValue E ℝ}

theorem actual_one_odd_first_packet
    (hstd : StandardSlopeFactorInput.{u})
    (hna : IsNonarchimedean v) (hmetric : ∀ x : E, v x = ‖x‖)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (n p r : ℕ) (hn : 0 < n) (hp : p.Prime) (hpodd : p ≠ 2) (hr : 1 ≤ r)
    (hnorm : ∀ t : ℕ, t ≠ 0 →
      v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (hsource : padicValNat p n = r ∨ padicValNat p (n + 1) = r) :
    ∃ D : SlopeFactorData (oneTranslate n : E[X]) v
        (Real.exp (-(1 : ℝ) / ((p - 2 : ℕ) : ℝ))) 0 (p - 2),
      Irreducible D.Q := by
  have hf := (actual_residue_one_faces n p r hn hp hr hnorm hsource).1 hpodd
  exact exists_irreducible_slope_factor v hstd hna hmetric hdiscrete
    (oneTranslate n) (oneTranslate_monic n hn) (p - 2) 0 (p - 2)
    (by have := hp.two_le; omega) (by omega) hf.1 hf.2

theorem actual_one_later_packet
    (hstd : StandardSlopeFactorInput.{u})
    (hna : IsNonarchimedean v) (hmetric : ∀ x : E, v x = ‖x‖)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (n p r k : ℕ) (hn : 0 < n) (hp : p.Prime) (hr : 1 ≤ r)
    (hk : 1 ≤ k) (hkr : k < r)
    (hnorm : ∀ t : ℕ, t ≠ 0 →
      v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (hsource : padicValNat p n = r ∨ padicValNat p (n + 1) = r) :
    ∃ D : SlopeFactorData (oneTranslate n : E[X]) v
        (Real.exp (-(1 : ℝ) / (laterDenom p k : ℝ)))
        (p ^ k - 2) (p ^ (k + 1) - 2),
      Irreducible D.Q := by
  have hf := (actual_residue_one_faces n p r hn hp hr hnorm hsource).2.1 k hk hkr
  exact exists_irreducible_slope_factor v hstd hna hmetric hdiscrete
    (oneTranslate n) (oneTranslate_monic n hn)
    (laterDenom p k) (p ^ k - 2) (p ^ (k + 1) - 2)
    (laterDenom_pos p k hp.two_le) (residue_one_later_width p k hp.two_le hk)
    hf.1 hf.2

end Extraction

end EventualIrreducibility.UniversalResidueOneExtractionDraft

open Polynomial

namespace EventualIrreducibility.UniversalPacketResultantDraft

variable {K : Type u} [Field K] (v : AbsoluteValue K ℝ)

lemma sub_norm_eq_right (hna : IsNonarchimedean v) (x y : K)
    (hxy : v x < v y) : v (x - y) = v y := by
  have hu : v (x - y) ≤ max (v x) (v y) := by
    simpa only [sub_eq_add_neg, AbsoluteValue.map_neg] using hna x (-y)
  have hl : v y ≤ max (v (x - y)) (v x) := by
    have h := hna (-(x - y)) x
    have hid : -(x - y) + x = y := by ring
    simpa only [hid, AbsoluteValue.map_neg] using h
  apply le_antisymm
  · simpa only [max_eq_right hxy.le] using hu
  · rcases le_max_iff.mp hl with h | h
    · exact h
    · exact False.elim ((not_le_of_gt hxy) h)

lemma sub_norm_eq_left (hna : IsNonarchimedean v) (x y : K)
    (hyx : v y < v x) : v (x - y) = v x := by
  have hu : v (x - y) ≤ max (v x) (v y) := by
    simpa only [sub_eq_add_neg, AbsoluteValue.map_neg] using hna x (-y)
  have hl : v x ≤ max (v (x - y)) (v y) := by
    simpa only [sub_add_cancel] using hna (x - y) y
  apply le_antisymm
  · simpa only [max_eq_left hyx.le] using hu
  · rcases le_max_iff.mp hl with h | h
    · exact h
    · exact False.elim ((not_le_of_gt hyx) h)

theorem same_center_difference_norm (hna : IsNonarchimedean v)
    (α β ζ : K) (a b : ℝ)
    (hα : v (α - ζ) = a) (hβ : v (β - ζ) = b) (hab : a < b) :
    v (α - β) = b := by
  have h := sub_norm_eq_right v hna (α - ζ) (β - ζ) (by simpa [hα, hβ])
  have hid : (α - ζ) - (β - ζ) = α - β := by ring
  simpa only [hid, hβ] using h

theorem distinct_center_difference_norm (hna : IsNonarchimedean v)
    (α β ζ ξ : K)
    (hsep : v (ζ - ξ) = 1)
    (hα : v (α - ζ) < 1) (hβ : v (β - ξ) < 1) : v (α - β) = 1 := by
  have hsep' : v (ξ - ζ) = 1 := by
    have hid : ξ - ζ = -(ζ - ξ) := by ring
    simpa only [hid, AbsoluteValue.map_neg] using hsep
  have hαξ : v (α - ξ) = 1 :=
    same_center_difference_norm v hna α ξ ζ (v (α - ζ)) 1 rfl hsep' hα
  have h := sub_norm_eq_left v hna (α - ξ) (β - ξ) (by simpa [hαξ])
  have hid : (α - ξ) - (β - ξ) = α - β := by ring
  simpa only [hid, hαξ] using h

lemma abv_finset_prod {ι : Type*} (s : Finset ι) (f : ι → K) :
    v (∏ i ∈ s, f i) = ∏ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.prod_insert, hi, ih, map_mul]

lemma resultant_root_product_eval {d : ℕ} (α : Fin d → K)
    (G H : K[X]) (hG : G = ∏ i, (X - C (α i) : K[X])) :
    G.resultant H G.natDegree H.natDegree = ∏ i, H.eval (α i) := by
  classical
  subst G
  rw [Polynomial.resultant_prod_left Finset.univ
    (fun i => (X - C (α i) : K[X])) H H.natDegree (by simp) le_rfl]
  apply Finset.prod_congr rfl
  intro i hi
  simp

end EventualIrreducibility.UniversalPacketResultantDraft

open Polynomial

namespace EventualIrreducibility.UniversalPacketProductDraft

open UniversalSlopeDraft UniversalPacketResultantDraft

section Algebra

variable {E K : Type u} [Field E] [Field K]

lemma unshift_dvd (P Q : E[X]) (ζ : E)
    (hdiv : Q ∣ P.comp (X + C ζ)) : Q.comp (X - C ζ) ∣ P := by
  obtain ⟨R, hR⟩ := hdiv
  refine ⟨R.comp (X - C ζ), ?_⟩
  have h := congrArg (fun T : E[X] => T.comp (X - C ζ)) hR
  simpa [Polynomial.mul_comp, Polynomial.comp_assoc] using h

lemma unshift_shift (Q : E[X]) (ζ : E) :
    (Q.comp (X - C ζ)).comp (X + C ζ) = Q := by
  simp [Polynomial.comp_assoc]

lemma unshift_monic (Q : E[X]) (hQ : Q.Monic) (ζ : E) :
    (Q.comp (X - C ζ)).Monic := by
  simpa only [sub_eq_add_neg, ← Polynomial.C_neg] using hQ.comp_X_add_C (-ζ)

lemma unshift_natDegree (Q : E[X]) (ζ : E) :
    (Q.comp (X - C ζ)).natDegree = Q.natDegree := by
  simp only [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]

lemma isCoprime_linear_of_eval_ne_zero (Q : E[X]) (a : E)
    (h : Q.eval a ≠ 0) : IsCoprime Q (X - C a) := by
  apply IsCoprime.symm
  apply (Polynomial.isUnit_resultant_iff_isCoprime (Polynomial.monic_X_sub_C a)).mp
  apply isUnit_iff_ne_zero.mpr
  simpa using h

lemma remove_double_one (P Q : E[X]) (hdiv : Q ∣ (X - 1) ^ 2 * P)
    (haway : Q.eval 1 ≠ 0) : Q ∣ P := by
  have hc : IsCoprime Q (X - 1) := by
    simpa using isCoprime_linear_of_eval_ne_zero Q 1 haway
  have hc2 : IsCoprime Q ((X - 1) ^ 2) := by
    simpa only [pow_two] using hc.mul_right hc
  exact hc2.dvd_of_dvd_mul_left hdiv

lemma coprime_of_mapped_disjoint_roots (ι : E →+* K)
    (Q R : E[X]) (hQ : Q.Monic) (hR : R.Monic)
    (hQsplit : (Q.map ι).Splits)
    (hdisjoint : ∀ α : K, (Q.map ι).IsRoot α → ¬ (R.map ι).IsRoot α) :
    IsCoprime Q R := by
  have hresMap : (Q.map ι).resultant (R.map ι) ≠ 0 := by
    rw [Polynomial.resultant_eq_prod_eval _ _ _ le_rfl hQsplit,
      (hQ.map ι).leadingCoeff, one_pow, one_mul]
    apply Multiset.prod_ne_zero
    intro hz
    obtain ⟨α, hα, he⟩ := Multiset.mem_map.mp hz
    exact hdisjoint α (Polynomial.isRoot_of_mem_roots hα) he
  have hmap : (Q.map ι).resultant (R.map ι) = ι (Q.resultant R) := by
    simpa only [hQ.natDegree_map ι, hR.natDegree_map ι] using
      Polynomial.resultant_map_map Q R Q.natDegree R.natDegree ι
  have hres : Q.resultant R ≠ 0 := by
    intro hzero
    apply hresMap
    rw [hmap, hzero, map_zero]
  exact (Polynomial.isUnit_resultant_iff_isCoprime hQ).mp
    (isUnit_iff_ne_zero.mpr hres)

theorem polynomial_eq_product_of_degree_exhaustion
    {I : Type*} [Fintype I] (P : E[X]) (hP : P.Monic)
    (Q : I → E[X]) (hQ : ∀ i, (Q i).Monic)
    (hdiv : ∀ i, Q i ∣ P) (hcop : Pairwise (fun i j => IsCoprime (Q i) (Q j)))
    (hdegree : ∑ i, (Q i).natDegree = P.natDegree) : P = ∏ i, Q i := by
  have hprodmonic : (∏ i, Q i).Monic :=
    Polynomial.monic_prod_of_monic _ Q (fun i _ => hQ i)
  have hproddiv : (∏ i, Q i) ∣ P := Fintype.prod_dvd_of_coprime hcop hdiv
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hprodmonic hP hproddiv
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => hQ i), hdegree]

end Algebra

structure LocatedPacket {E : Type u} [Field E]
    (P : E[X]) (v : AbsoluteValue E ℝ) where
  Q : E[X]
  monic : Q.Monic
  divides : Q ∣ P
  center : E
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  pure_shift : PureGauss (Q.comp (X + C center)) v radius

section Locations

variable {E K : Type u} [Field E] [Field K]
    {v : AbsoluteValue E ℝ} {w : AbsoluteValue K ℝ}

def LocatedPacket.divisor (P : E[X]) (A : LocatedPacket P v)
    (hna : IsNonarchimedean v) (D : E[X]) (hD : D.Monic) (hdiv : D ∣ A.Q) :
    LocatedPacket P v where
  Q := D
  monic := hD
  divides := hdiv.trans A.divides
  center := A.center
  radius := A.radius
  radius_pos := A.radius_pos
  radius_lt_one := A.radius_lt_one
  pure_shift := by
    apply pureGauss_of_dvd hna A.radius_pos
      (A.Q.comp (X + C A.center)) (D.comp (X + C A.center))
      (A.monic.comp_X_add_C A.center).ne_zero A.pure_shift
    obtain ⟨H, hH⟩ := hdiv
    refine ⟨H.comp (X + C A.center), ?_⟩
    simpa only [Polynomial.mul_comp] using
      congrArg (fun T : E[X] => T.comp (X + C A.center)) hH

lemma LocatedPacket.denominator_dvd_divisor_degree
    (P : E[X]) (A : LocatedPacket P v) (hna : IsNonarchimedean v)
    (b : ℕ) (hb : 0 < b) (hradius : A.radius = Real.exp (-(1 : ℝ) / (b : ℝ)))
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (D : E[X]) (hD : D.Monic) (hdiv : D ∣ A.Q) : b ∣ D.natDegree := by
  let B := A.divisor P hna D hD hdiv
  have hpure := B.pure_shift
  change PureGauss (D.comp (X + C A.center)) v A.radius at hpure
  rw [hradius] at hpure
  have hd := denominator_dvd_pure_degree (D.comp (X + C A.center))
    (hD.comp_X_add_C A.center).ne_zero b hb hdiscrete hpure
  simpa only [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one] using hd

lemma LocatedPacket.irreducible_of_degree
    (P : E[X]) (A : LocatedPacket P v) (hna : IsNonarchimedean v)
    (b : ℕ) (hb : 0 < b) (hradius : A.radius = Real.exp (-(1 : ℝ) / (b : ℝ)))
    (hdegree : A.Q.natDegree = b)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ))) :
    Irreducible A.Q := by
  have hA1 : A.Q ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hdegree
    omega
  rw [A.monic.irreducible_iff_lt_natDegree_lt hA1]
  intro D hD hsize hdiv
  have hdvd := A.denominator_dvd_divisor_degree P hna b hb hradius hdiscrete D hD hdiv
  have hd := Finset.mem_Ioc.mp hsize
  have hbD : b ≤ D.natDegree := Nat.le_of_dvd hd.1 hdvd
  rw [hdegree] at hd
  omega

lemma LocatedPacket.root_radius (P : E[X]) (A : LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (α : K) (hroot : (A.Q.map ι).IsRoot α) :
    w (α - ι A.center) = A.radius := by
  have hshiftroot : ((A.Q.comp (X + C A.center)).map ι).IsRoot
      (α - ι A.center) := by
    simpa [Polynomial.IsRoot, Polynomial.map_comp, Polynomial.eval_comp] using hroot
  exact mapped_packet_root_norm ι hrestrict hna
    (A.Q.comp (X + C A.center)) (A.monic.comp_X_add_C A.center)
    A.radius A.radius_pos A.pure_shift (α - ι A.center) hshiftroot

lemma located_disjoint_of_centers_or_radii
    (P : E[X]) (A B : LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w)
    (hsep : (A.center = B.center ∧ A.radius ≠ B.radius) ∨
      v (A.center - B.center) = 1) :
    ∀ α : K, (A.Q.map ι).IsRoot α → ¬ (B.Q.map ι).IsRoot α := by
  intro α hA hB
  have ha := A.root_radius P ι hrestrict hna α hA
  have hb := B.root_radius P ι hrestrict hna α hB
  rcases hsep with ⟨hc, hr⟩ | hc
  · apply hr
    rw [hc] at ha
    exact ha.symm.trans hb
  · have hcenter : w (ι A.center - ι B.center) = 1 := by
      rw [← map_sub, hrestrict, hc]
    have hzero := distinct_center_difference_norm w hna α α
      (ι A.center) (ι B.center) hcenter
      (ha.trans_lt A.radius_lt_one) (hb.trans_lt B.radius_lt_one)
    simp at hzero

theorem located_packet_product
    {I : Type*} [Fintype I] (P : E[X]) (hP : P.Monic)
    (A : I → LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hsplit : (P.map ι).Splits)
    (hsep : Pairwise (fun i j =>
      ((A i).center = (A j).center ∧ (A i).radius ≠ (A j).radius) ∨
        v ((A i).center - (A j).center) = 1))
    (hdegree : ∑ i, (A i).Q.natDegree = P.natDegree) :
    P = ∏ i, (A i).Q := by
  apply polynomial_eq_product_of_degree_exhaustion P hP (fun i => (A i).Q)
    (fun i => (A i).monic) (fun i => (A i).divides) ?_ hdegree
  intro i j hij
  have hdivmap : (A i).Q.map ι ∣ P.map ι := by
    obtain ⟨R, hR⟩ := (A i).divides
    exact ⟨R.map ι, by simpa only [Polynomial.map_mul] using congrArg (Polynomial.map ι) hR⟩
  have hQsplit := hsplit.of_dvd (hP.map ι).ne_zero hdivmap
  exact coprime_of_mapped_disjoint_roots ι (A i).Q (A j).Q
    (A i).monic (A j).monic hQsplit
    (located_disjoint_of_centers_or_radii P (A i) (A j) ι hrestrict hna (hsep hij))

end Locations

section FromSlope

variable {E : Type u} [Field E] {v : AbsoluteValue E ℝ}

noncomputable def packet_of_shift_slope (P : E[X]) (ζ : E) (c : ℝ)
    (hc : 0 < c) (hc1 : c < 1) (i j : ℕ)
    (D : SlopeFactorData (P.comp (X + C ζ)) v c i j) : LocatedPacket P v where
  Q := D.Q.comp (X - C ζ)
  monic := unshift_monic D.Q D.monic_Q ζ
  divides := unshift_dvd P D.Q ζ ⟨D.R, D.factorization⟩
  center := ζ
  radius := c
  radius_pos := hc
  radius_lt_one := hc1
  pure_shift := by rw [unshift_shift]; exact D.pure_Q

noncomputable def ordinary_packet_of_slope
    (hna : IsNonarchimedean v)
    (P F : E[X]) (hF : F = (X - 1) ^ 2 * P)
    (ζ : E) (hsep : v (1 - ζ) = 1) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (i j : ℕ) (D : SlopeFactorData (F.comp (X + C ζ)) v c i j) :
    LocatedPacket P v := by
  let A : LocatedPacket F v := packet_of_shift_slope F ζ c hc hc1 i j D
  have haway : A.Q.eval 1 ≠ 0 := by
    intro hzero
    have hr : v (1 - ζ) = c := by
      have hroot : A.Q.IsRoot 1 := hzero
      have h := A.root_radius F (RingHom.id E) (fun _ => rfl) hna 1
        (by simpa using hroot)
      simpa only [A, packet_of_shift_slope, RingHom.id_apply] using h
    rw [hsep] at hr
    exact (ne_of_lt hc1) hr.symm
  exact { A with divides := remove_double_one P A.Q (hF ▸ A.divides) haway }

end FromSlope

end EventualIrreducibility.UniversalPacketProductDraft

open Polynomial

namespace EventualIrreducibility.UniversalPacketAllocationDraft

open UniversalPacketProductDraft UniversalPacketResultantDraft

variable {E : Type u} [Field E]

lemma monic_split_divisor (Q G H : E[X]) (hQ : Q.Monic) (hdiv : Q ∣ G * H) :
    ∃ A B : E[X], A.Monic ∧ B.Monic ∧ A ∣ G ∧ B ∣ H ∧ Q = A * B := by
  classical
  obtain ⟨A, B, hAdiv, hBdiv, hfactor⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  have hA0 : A ≠ 0 := by intro h; apply hQ.ne_zero; simp [hfactor, h]
  have hB0 : B ≠ 0 := by intro h; apply hQ.ne_zero; simp [hfactor, h]
  refine ⟨normalize A, normalize B, Polynomial.monic_normalize hA0,
    Polynomial.monic_normalize hB0, ?_, ?_, ?_⟩
  · simpa only [normalize_dvd_iff] using hAdiv
  · simpa only [normalize_dvd_iff] using hBdiv
  · rw [← normalize_mul, ← hfactor, hQ.normalize_eq_self]

structure PacketAllocation {I : Type*} [Fintype I]
    (Q : I → E[X]) (G H : E[X]) where
  left : I → E[X]
  right : I → E[X]
  monic_left : ∀ i, (left i).Monic
  monic_right : ∀ i, (right i).Monic
  divides_left : ∀ i, left i ∣ G
  divides_right : ∀ i, right i ∣ H
  pair_product : ∀ i, Q i = left i * right i
  left_product : G = ∏ i, left i
  right_product : H = ∏ i, right i

theorem exists_packet_allocation {I : Type*} [Fintype I]
    (P G H : E[X]) (hG : G.Monic) (hH : H.Monic)
    (Q : I → E[X]) (hQ : ∀ i, (Q i).Monic)
    (hcop : Pairwise (fun i j => IsCoprime (Q i) (Q j)))
    (hP : P = ∏ i, Q i) (hfactor : P = G * H) :
    Nonempty (PacketAllocation Q G H) := by
  classical
  have hdiv (i : I) : Q i ∣ G * H := by
    rw [← hfactor, hP]
    exact Finset.dvd_prod_of_mem Q (Finset.mem_univ i)
  choose A B hAm hBm hAd hBd hAB using fun i => monic_split_divisor (Q i) G H (hQ i) (hdiv i)
  have hAdivQ (i : I) : A i ∣ Q i := ⟨B i, hAB i⟩
  have hBdivQ (i : I) : B i ∣ Q i := ⟨A i, by rw [hAB i, mul_comm]⟩
  have hAcop : Pairwise (fun i j => IsCoprime (A i) (A j)) := by
    intro i j hij
    exact ((hcop hij).of_isCoprime_of_dvd_left (hAdivQ i)).of_isCoprime_of_dvd_right
      (hAdivQ j)
  have hBcop : Pairwise (fun i j => IsCoprime (B i) (B j)) := by
    intro i j hij
    exact ((hcop hij).of_isCoprime_of_dvd_left (hBdivQ i)).of_isCoprime_of_dvd_right
      (hBdivQ j)
  have hAprdiv : (∏ i, A i) ∣ G := Fintype.prod_dvd_of_coprime hAcop hAd
  have hBprdiv : (∏ i, B i) ∣ H := Fintype.prod_dvd_of_coprime hBcop hBd
  have hAprm : (∏ i, A i).Monic := Polynomial.monic_prod_of_monic _ A (fun i _ => hAm i)
  have hBprm : (∏ i, B i).Monic := Polynomial.monic_prod_of_monic _ B (fun i _ => hBm i)
  have hproducts : G * H = (∏ i, A i) * ∏ i, B i := by
    rw [← hfactor, hP]
    simp_rw [hAB]
    exact Finset.prod_mul_distrib
  have htotal := congrArg Polynomial.natDegree hproducts
  rw [Polynomial.natDegree_mul hG.ne_zero hH.ne_zero,
    Polynomial.natDegree_mul hAprm.ne_zero hBprm.ne_zero] at htotal
  have hAle := Polynomial.natDegree_le_of_dvd hAprdiv hG.ne_zero
  have hBle := Polynomial.natDegree_le_of_dvd hBprdiv hH.ne_zero
  have hGA : G = ∏ i, A i :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hAprm hG hAprdiv (by omega)
  have hHB : H = ∏ i, B i :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hBprm hH hBprdiv (by omega)
  exact ⟨⟨A, B, hAm, hBm, hAd, hBd, hAB, hGA, hHB⟩⟩

theorem irreducible_packet_allocation {I : Type*} [Fintype I]
    (Q : I → E[X]) (G H : E[X]) (A : PacketAllocation Q G H)
    (i : I) (hi : Irreducible (Q i)) :
    (A.left i = Q i ∧ A.right i = 1) ∨
      (A.left i = 1 ∧ A.right i = Q i) := by
  rcases hi.isUnit_or_isUnit (A.pair_product i) with hl | hr
  · right
    have hleft := (A.monic_left i).eq_one_of_isUnit hl
    refine ⟨hleft, ?_⟩
    simpa only [hleft, one_mul] using (A.pair_product i).symm
  · left
    have hright := (A.monic_right i).eq_one_of_isUnit hr
    refine ⟨?_, hright⟩
    simpa only [hright, mul_one] using (A.pair_product i).symm

theorem resultant_of_packet_allocation {I : Type*} [Fintype I]
    (Q : I → E[X]) (G H : E[X]) (A : PacketAllocation Q G H) :
    G.resultant H = ∏ i, ∏ j, (A.left i).resultant (A.right j) := by
  calc
    G.resultant H = (∏ i, A.left i).resultant (∏ j, A.right j) :=
      congrArg₂ (fun F B : E[X] => F.resultant B) A.left_product A.right_product
    _ = ∏ i, ∏ j, (A.left i).resultant (A.right j) := by
      rw [Polynomial.resultant_prod_left Finset.univ A.left (∏ j, A.right j)
        (∏ j, A.right j).natDegree (by simp [(A.monic_left _).leadingCoeff]) le_rfl]
      apply Finset.prod_congr rfl
      intro i hi
      exact Polynomial.resultant_prod_right Finset.univ (A.left i) A.right
        (A.left i).natDegree le_rfl (by simp [(A.monic_right _).leadingCoeff])

theorem resultant_norm_of_packet_allocation {I : Type*} [Fintype I]
    (v : AbsoluteValue E ℝ)
    (Q : I → E[X]) (G H : E[X]) (A : PacketAllocation Q G H) :
    v (G.resultant H) = ∏ i, ∏ j, v ((A.left i).resultant (A.right j)) := by
  rw [resultant_of_packet_allocation Q G H A, abv_finset_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact abv_finset_prod v _ _

end EventualIrreducibility.UniversalPacketAllocationDraft

open Polynomial

namespace EventualIrreducibility.UniversalBinaryQuarticDraft

open UniversalSlopeDraft UniversalOrdinaryFacesDraft UniversalPacketResultantDraft

section PolynomialAlgebra

variable {K : Type u} [Field K] (v : AbsoluteValue K ℝ)

lemma shifted_derivative_formula (n : ℕ) (ζ : K) :
    (shiftedTrinomial n ζ).derivative =
      C ((n + 1 : ℕ) : K) * ((X + C ζ) ^ n - 1) := by
  simp only [shiftedTrinomial, Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_pow_succ,
    Polynomial.derivative_C, Polynomial.derivative_mul, Polynomial.derivative_X,
    zero_mul, mul_one, add_zero, Nat.cast_add, Nat.cast_one]
  ring

lemma shifted_root_derivative_identity (n : ℕ) (ζ α : K)
    (hroot : (shiftedTrinomial n ζ).eval α = 0) :
    (α + ζ) * (shiftedTrinomial n ζ).derivative.eval α =
      (n : K) * ((n + 1 : ℕ) : K) * (α + ζ - 1) := by
  have hscalar : (α + ζ) ^ (n + 1) -
      ((n + 1 : ℕ) : K) * (α + ζ) + (n : K) = 0 := by
    simpa [shiftedTrinomial] using hroot
  rw [shifted_derivative_formula]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one] at hscalar ⊢
  linear_combination ((n : K) + 1) * hscalar

lemma shifted_root_derivative_norm (n r : ℕ) (ζ α : K)
    (hroot : (shiftedTrinomial n ζ).eval α = 0)
    (hunit : v (α + ζ) = 1) (haway : v (α + ζ - 1) = 1)
    (hscalar : v ((n : K) * ((n + 1 : ℕ) : K)) = Real.exp (-(r : ℝ))) :
    v ((shiftedTrinomial n ζ).derivative.eval α) = Real.exp (-(r : ℝ)) := by
  have h := congrArg v (shifted_root_derivative_identity n ζ α hroot)
  rw [map_mul, hunit, one_mul] at h
  rw [map_mul, hscalar, haway, mul_one] at h
  exact h

lemma derivative_mul_eval_at_root (Q R : K[X]) (α : K)
    (hQ : Q.eval α = 0) :
    (Q * R).derivative.eval α = Q.derivative.eval α * R.eval α := by
  simp [Polynomial.derivative_mul, hQ]

end PolynomialAlgebra

section QuadraticBound

variable {K : Type u} [Field K] (v : AbsoluteValue K ℝ)

lemma discrete_half_bound (x : K)
    (hdiscrete : ∀ x : K, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (hx : v x ≤ Real.exp (-(1 : ℝ) / 2)) : v x ≤ Real.exp (-1) := by
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero]
    exact (Real.exp_pos _).le
  obtain ⟨z, hz⟩ := hdiscrete x hx0
  rw [hz] at hx ⊢
  have hzR : -(z : ℝ) ≤ -(1 : ℝ) / 2 := Real.exp_le_exp.mp hx
  have hz1 : 1 ≤ z := by
    by_contra h
    have hz0 : z ≤ 0 := by omega
    have hz0R : (z : ℝ) ≤ 0 := by exact_mod_cast hz0
    linarith
  have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  exact Real.exp_le_exp.mpr (by linarith)

lemma pure_quadratic_linear_norm
    (Q : K[X]) (hQ : Q.Monic) (hdegree : Q.natDegree = 2)
    (hdiscrete : ∀ x : K, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (hpure : PureGauss Q v (Real.exp (-(1 : ℝ) / 2))) :
    v (Q.coeff 1) ≤ Real.exp (-1) := by
  let c : ℝ := Real.exp (-(1 : ℝ) / 2)
  have hc : 0 < c := Real.exp_pos _
  have hnorm : Q.gaussNorm v c = c ^ 2 := by
    have h := hpure.2.1
    have htop : Q.coeff 2 = 1 := by rw [← hdegree]; exact hQ.coeff_natDegree
    simpa only [htop, map_one, one_mul, hdegree, c] using h
  have hlin := Q.le_gaussNorm v hc.le 1
  rw [hnorm, pow_one] at hlin
  have hhalf : v (Q.coeff 1) ≤ c := by nlinarith
  exact discrete_half_bound v (Q.coeff 1) hdiscrete hhalf

lemma monic_quadratic_derivative_eval (Q : K[X]) (hQ : Q.Monic)
    (hdegree : Q.natDegree = 2) (α : K) :
    Q.derivative.eval α = (2 : K) * α + Q.coeff 1 := by
  have htop : Q.coeff 2 = 1 := by
    rw [← hdegree]
    exact hQ.coeff_natDegree
  have hquad : Q = X ^ 2 + C (Q.coeff 1) * X + C (Q.coeff 0) := by
    ext j
    cases j with
    | zero => simp
    | succ j =>
      cases j with
      | zero => simp
      | succ j =>
        cases j with
        | zero => simpa using htop
        | succ k =>
          have hzero : Q.coeff (k + 3) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          simpa using hzero
  rw [hquad]
  simp only [Polynomial.derivative_add, Polynomial.derivative_pow,
    Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.derivative_C,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one]
  norm_num

end QuadraticBound

section Extraction

variable {E : Type u} [NormedField E] [CompleteSpace E]
    {v : AbsoluteValue E ℝ}

end Extraction

end EventualIrreducibility.UniversalBinaryQuarticDraft

open Polynomial

namespace EventualIrreducibility.UniversalZeroPacketDraft

open UniversalSlopeDraft

section Face

variable {R : Type u} [CommRing R] [Nontrivial R] {v : AbsoluteValue R ℝ}

lemma pow_succ_succ_lt (c : ℝ) (hc : 0 < c) (hc1 : c < 1) (k : ℕ) :
    c ^ (k + 2) < c := by
  induction k with
  | zero => norm_num; nlinarith
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
    calc
      c ^ (k + 2) * c < c * c := mul_lt_mul_of_pos_right ih hc
      _ < c := by nlinarith

omit [Nontrivial R] in
theorem zero_linear_face (P : R[X]) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hzero : v (P.coeff 0) = c) (hone : v (P.coeff 1) = 1)
    (hcoeff : ∀ j, v (P.coeff j) ≤ 1) :
    IsMinGaussIndex P v c 0 ∧ IsMaxGaussIndex P v c 1 := by
  have hhigher (j : ℕ) (hj : 1 < j) : v (P.coeff j) * c ^ j < c := by
    calc
      v (P.coeff j) * c ^ j ≤ 1 * c ^ j :=
        mul_le_mul_of_nonneg_right (hcoeff j) (pow_nonneg hc.le j)
      _ = c ^ j := one_mul _
      _ < c := by
        have heq : j - 2 + 2 = j := by omega
        simpa only [heq] using pow_succ_succ_lt c hc hc1 (j - 2)
  have hbound (j : ℕ) : v (P.coeff j) * c ^ j ≤ c := by
    by_cases hj0 : j = 0
    · simp [hj0, hzero]
    by_cases hj1 : j = 1
    · simp [hj1, hone]
    exact (hhigher j (by omega)).le
  have hnorm : P.gaussNorm v c = c := by
    obtain ⟨j, hj, _⟩ := P.exists_min_eq_gaussNorm v hc.le
    apply le_antisymm
    · rw [hj]
      exact hbound j
    · simpa only [hzero, pow_zero, mul_one] using P.le_gaussNorm v hc.le 0
  constructor
  · refine ⟨by simpa only [hzero, pow_zero, mul_one] using hnorm, ?_⟩
    intro j hj
    omega
  · refine ⟨by simpa only [hone, pow_one, one_mul] using hnorm, ?_⟩
    intro j hj
    rw [hnorm]
    exact hhigher j hj

omit [Nontrivial R] in
theorem actual_zero_linear_face
    (n p r : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hr : 1 ≤ r)
    (hval : padicValNat p n = r)
    (hnorm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat p m : ℝ))) :
    IsMinGaussIndex ((fInt n).map (Int.castRingHom R)) v
        (Real.exp (-(r : ℝ))) 0 ∧
      IsMaxGaussIndex ((fInt n).map (Int.castRingHom R)) v
        (Real.exp (-(r : ℝ))) 1 := by
  have hdivpow := ActualEnvelope.power_dvd_of_padicVal_eq p n r hp (by omega) hval
  have hpd : p ∣ n := dvd_trans
    (ActualEnvelope.prime_dvd_positive_power p r hr) hdivpow
  have hpred : ¬ p ∣ n - 1 := by
    intro h
    have hd : p ∣ n - (n - 1) := Nat.dvd_sub hpd h
    have heq : n - (n - 1) = 1 := by omega
    rw [heq] at hd
    have hple : p ≤ 1 := Nat.le_of_dvd (by omega) hd
    have hp2 := hp.two_le
    omega
  have hpredval : padicValNat p (n - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd hpred
  have hnormle (m : ℕ) : v (m : R) ≤ 1 := by
    by_cases hm : m = 0
    · simp [hm]
    rw [hnorm m hm]
    apply Real.exp_le_one_iff.mpr
    have hnonneg : (0 : ℝ) ≤ (padicValNat p m : ℝ) := Nat.cast_nonneg _
    linarith
  apply zero_linear_face _ (Real.exp (-(r : ℝ))) (Real.exp_pos _)
  · apply Real.exp_lt_one_iff.mpr
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    linarith
  · simp only [Polynomial.coeff_map, coeff_fInt, show 0 < n by omega,
      if_true, Nat.sub_zero, map_natCast]
    rw [hnorm n (by omega), hval]
  · simp only [Polynomial.coeff_map, coeff_fInt, show 1 < n by omega,
      if_true, map_natCast]
    rw [hnorm (n - 1) (by omega), hpredval]
    simp
  · intro j
    simp only [Polynomial.coeff_map, coeff_fInt]
    split_ifs
    · simpa only [map_natCast] using hnormle (n - j)
    · simp

end Face

section Extraction

variable {E : Type u} [NormedField E] [CompleteSpace E]
    {v : AbsoluteValue E ℝ}

theorem actual_zero_linear_packet
    (hstd : StandardSlopeFactorInput.{u})
    (hna : IsNonarchimedean v) (hmetric : ∀ x : E, v x = ‖x‖)
    (n p r : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hr : 1 ≤ r)
    (hval : padicValNat p n = r)
    (hnorm : ∀ m : ℕ, m ≠ 0 →
      v (m : E) = Real.exp (-(padicValNat p m : ℝ))) :
    ∃ D : SlopeFactorData ((fInt n).map (Int.castRingHom E)) v
        (Real.exp (-(r : ℝ))) 0 1,
      D.Q.natDegree = 1 := by
  have hf := actual_zero_linear_face n p r hn hp hr hval hnorm
  obtain ⟨D⟩ := hstd E v hna hmetric ((fInt n).map (Int.castRingHom E))
    ((monic_fInt n (by omega)).map (Int.castRingHom E))
    (Real.exp (-(r : ℝ))) (Real.exp_pos _) 0 1 hf.1 hf.2
  exact ⟨D, by simpa using D.degree_Q⟩

end Extraction

end EventualIrreducibility.UniversalZeroPacketDraft

open Polynomial

namespace EventualIrreducibility.UniversalBinaryParityDraft

open FirstFace UniversalResidueOneProfileDraft UniversalResidueOneFacesDraft

section FiniteAssembly

variable {R : Type*} [CommRing R] [Nontrivial R] {v : AbsoluteValue R ℝ}

omit [Nontrivial R] in
theorem binary_minGaussIndex_one_even
    (hna : IsNonarchimedean v) (G H : R[X]) (hG : G ≠ 0) (hH : H ≠ 0)
    (r : ℕ) (hr : 1 ≤ r)
    (hdiscrete : ∀ a : R, a ≠ 0 → ∃ z : ℤ, v a = Real.exp (-(z : ℝ)))
    (hprofile : OneProfile (G * H) v 2 r)
    (t : ℕ) (ht : IsMinGaussIndex G v 1 t) : 2 ∣ t := by
  by_cases hr1 : r = 1
  · subst r
    obtain ⟨u, hu⟩ := H.exists_min_eq_gaussNorm v (show (0 : ℝ) ≤ 1 by norm_num)
    change IsMinGaussIndex H v 1 u at hu
    have hp := minGaussIndex_mul hna (show (0 : ℝ) < 1 by norm_num)
      G H hG hH t u ht hu
    have hzero := (binary_one_r1 (G * H) hprofile).2
    have heq := assembly_min_unique (G * H) 1 (t + u) 0 hp hzero
    have ht0 : t = 0 := by omega
    rw [ht0]
    exact dvd_zero 2
  have hr2 : 2 ≤ r := by omega
  let denom : ℕ → ℕ := fun i => 2 ^ (i + 1)
  let vertex : ℕ → ℕ := fun i => 2 ^ (i + 1) - 2
  have hdenom (i : ℕ) : 0 < denom i := pow_pos (by omega) _
  have hpowstep (i : ℕ) : denom i < denom (i + 1) := by
    dsimp [denom]
    rw [pow_succ]
    have hpos : 0 < 2 ^ (i + 1) := pow_pos (by omega) _
    omega
  have hfaces (i : ℕ) (hi : i < r - 1) :
      IsMinGaussIndex (G * H) v
          (Real.exp (-(1 : ℝ) / (denom i : ℝ))) (vertex i) ∧
        IsMaxGaussIndex (G * H) v
          (Real.exp (-(1 : ℝ) / (denom i : ℝ))) (vertex (i + 1)) := by
    have hf := one_later_face (G * H) 2 r (i + 1)
      (by omega) (by omega) (by omega) hprofile
    simpa only [laterDenom, Nat.reduceSub, mul_one, denom, vertex] using hf
  refine minGaussIndex_one_dvd_of_critical_faces hna G H hG hH 2 (r - 1)
    (by omega) denom vertex hdiscrete ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t ht
  · norm_num [vertex]
  · intro i hi
    exact hdenom i
  · intro i hi
    dsimp [denom]
    exact ActualEnvelope.prime_dvd_positive_power 2 (i + 1) (by omega)
  · intro i hi
    exact exp_radius_strict_of_denominators (denom i) (denom (i + 1))
      (hdenom i) (hpowstep i)
  · exact exp_radius_lt_one (denom (r - 1 - 1)) (hdenom _)
  · intro i hi
    exact (hfaces i hi).1
  · intro i hi
    exact (hfaces i hi).2
  · have hterm := one_terminal_minimum (G * H) 2 r (by omega) hr hprofile
    simpa only [vertex, Nat.sub_add_cancel (by omega : 1 ≤ r)] using hterm

end FiniteAssembly

section Reduction

variable {R k : Type*} [CommRing R] [IsDomain R] [Field k]
    {v : AbsoluteValue R ℝ}

lemma translated_product_eq_oneTranslate
    (n : ℕ) (g h : R[X])
    (hfactor : (X - 1) ^ 2 * (g * h) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : R) * X + C (n : R)) :
    g.comp (X + C 1) * h.comp (X + C 1) = (oneTranslate n : R[X]) := by
  apply mul_left_cancel₀ (pow_ne_zero 2 (Polynomial.X_ne_zero : (X : R[X]) ≠ 0))
  rw [oneTranslate_mul_Xsq]
  calc
    (X : R[X]) ^ 2 * (g.comp (X + C 1) * h.comp (X + C 1)) =
        ((X - 1) ^ 2 * (g * h)).comp (X + C 1) := by
      simp [Polynomial.mul_comp]
    _ = shiftedTrinomial n (1 : R) := by
      rw [hfactor, ← shiftedTrinomial_eq_comp]

theorem binary_rootMultiplicity_one_even_of_normalized_lift
    (red : R →+* k) (hna : IsNonarchimedean v)
    (hintegral : ∀ a : R, v a ≤ 1)
    (hdiscrete : ∀ a : R, a ≠ 0 → ∃ z : ℤ, v a = Real.exp (-(z : ℝ)))
    (hred : ∀ a, red a ≠ 0 ↔ v a = 1)
    (n r : ℕ) (hn : 0 < n) (hr : 1 ≤ r)
    (hnorm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat 2 m : ℝ)))
    (g h : R[X]) (hg : g.Monic)
    (hfactor : (X - 1) ^ 2 * (g * h) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : R) * X + C (n : R))
    (hsource : padicValNat 2 n = r ∨ padicValNat 2 (n + 1) = r) :
    Even ((g.map red).rootMultiplicity 1) := by
  let G : R[X] := g.comp (X + C 1)
  let H : R[X] := h.comp (X + C 1)
  have hGmonic : G.Monic := hg.comp_X_add_C 1
  have hGH : G * H = (oneTranslate n : R[X]) :=
    translated_product_eq_oneTranslate n g h hfactor
  have hH : H ≠ 0 := by
    intro hzero
    have hQ := (oneTranslate_monic (R := R) n hn).ne_zero
    apply hQ
    rw [← hGH, hzero, mul_zero]
  have hprofile : OneProfile (G * H) v 2 r := by
    rw [hGH]
    exact actual_one_profile n 2 r hn Nat.prime_two hr hnorm hsource
  obtain ⟨t, ht⟩ := G.exists_min_eq_gaussNorm v (show (0 : ℝ) ≤ 1 by norm_num)
  change IsMinGaussIndex G v 1 t at ht
  have htEven : 2 ∣ t := binary_minGaussIndex_one_even hna G H hGmonic.ne_zero
    hH r hr hdiscrete hprofile t ht
  have htRoot : (G.map red).rootMultiplicity 0 = t :=
    ResidueCluster.rootMultiplicity_zero_eq_of_monic_minGaussIndex G hGmonic
      red hintegral hred t ht
  have hmapShift : G.map red = (g.map red).comp (X + C 1) := by
    simp only [G, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X,
      map_one, Polynomial.map_one]
  have hrootShift : (g.map red).rootMultiplicity 1 =
      (G.map red).rootMultiplicity 0 := by
    rw [Polynomial.rootMultiplicity_eq_rootMultiplicity, hmapShift]
  rw [hrootShift, htRoot]
  obtain ⟨u, hu⟩ := htEven
  exact ⟨u, by omega⟩

theorem integer_factor_rootMultiplicity_one_even
    (red : R →+* k) (hna : IsNonarchimedean v)
    (hintegral : ∀ a : R, v a ≤ 1)
    (hdiscrete : ∀ a : R, a ≠ 0 → ∃ z : ℤ, v a = Real.exp (-(z : ℝ)))
    (hred : ∀ a, red a ≠ 0 ↔ v a = 1)
    (n r : ℕ) (hn : 0 < n) (hr : 1 ≤ r)
    (hnorm : ∀ m : ℕ, m ≠ 0 → v (m : R) = Real.exp (-(padicValNat 2 m : ℝ)))
    (g h : ℤ[X]) (hg : g.Monic) (hfactor : g * h = fInt n)
    (hsource : padicValNat 2 n = r ∨ padicValNat 2 (n + 1) = r) :
    Even ((g.map (Int.castRingHom k)).rootMultiplicity 1) := by
  have hzfactor : (X - 1) ^ 2 * (g * h) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : ℤ) * X + C (n : ℤ) := by
    rw [hfactor]
    exact trinomial_identity n
  have hRfactor : (X - 1) ^ 2 *
      (g.map (Int.castRingHom R) * h.map (Int.castRingHom R)) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : R) * X + C (n : R) := by
    have heq := congrArg (Polynomial.map (Int.castRingHom R)) hzfactor
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C,
      map_natCast, Polynomial.map_natCast] using heq
  have hlocal := binary_rootMultiplicity_one_even_of_normalized_lift red hna
    hintegral hdiscrete hred n r hn hr hnorm
    (g.map (Int.castRingHom R)) (h.map (Int.castRingHom R))
    (hg.map (Int.castRingHom R)) hRfactor hsource
  have hmaps : (g.map (Int.castRingHom R)).map red =
      g.map (Int.castRingHom k) := by
    ext j
    simp only [Polynomial.coeff_map, Int.coe_castRingHom, map_intCast]
  simpa only [hmaps] using hlocal

end Reduction

end EventualIrreducibility.UniversalBinaryParityDraft

namespace EventualIrreducibility.UniversalFactorParity

open Polynomial

theorem exists_binary_shape_of_nonzero_multiplicities
    {K L : Type*} [Field K] [Field L] [CharP K 2] [CharP L 2]
    [PerfectRing K 2] (i : K →+* L) (G : K[X]) (hG : G ≠ 0)
    (hs : (G.map i).Splits)
    (hzero : (G.map i).rootMultiplicity 0 ≤ 1)
    (hm : ∀ a : L, a ≠ 0 → 2 ∣ (G.map i).rootMultiplicity a) :
    ∃ ε : ℕ, ∃ H : K[X], ε ≤ 1 ∧ G = X ^ ε * H ^ 2 ∧ H.eval 0 ≠ 0 := by
  classical
  obtain ⟨B, hGB, hB0⟩ := G.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hG 0
  let ε := G.rootMultiplicity 0
  have hshape : G = X ^ ε * B := by
    simpa only [C_0, sub_zero, ε] using hGB
  have hB : B ≠ 0 := by
    intro h
    apply hG
    simpa only [h, mul_zero] using hshape
  have hBnot0 : ¬ B.IsRoot 0 := by
    intro h
    exact hB0 (Polynomial.dvd_iff_isRoot.mpr h)
  have hmap : G.map i = X ^ ε * B.map i := by
    rw [hshape]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  have hGmap : G.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hG
  have hBdiv : B.map i ∣ G.map i := by
    refine ⟨X ^ ε, ?_⟩
    rw [hmap, mul_comm]
  have hBs : (B.map i).Splits := hs.of_dvd hGmap hBdiv
  have hBmult : ∀ a : L, 2 ∣ (B.map i).rootMultiplicity a := by
    intro a
    by_cases ha : a = 0
    · subst a
      have hBmap0 : (B.map i).rootMultiplicity 0 = 0 := by
        simpa only [map_zero] using
          (Polynomial.eq_rootMultiplicity_map (p := B) i.injective (0 : K)).symm.trans
            (Polynomial.rootMultiplicity_eq_zero hBnot0)
      rw [hBmap0]
      exact dvd_zero 2
    · have hA : ¬ ((X : L[X]) ^ ε).IsRoot a := by
        simpa [Polynomial.IsRoot] using pow_ne_zero ε ha
      have he : (G.map i).rootMultiplicity a = (B.map i).rootMultiplicity a := by
        rw [hmap, Polynomial.rootMultiplicity_mul (hmap ▸ hGmap),
          Polynomial.rootMultiplicity_eq_zero hA, zero_add]
      exact he ▸ hm a ha
  obtain ⟨H, hH⟩ := FiniteFieldDescent.exists_pow_of_map_splits_multiplicity_dvd
    2 i B hBs hBmult
  have hH0 : H.eval 0 ≠ 0 := by
    intro hz
    apply hBnot0
    change B.eval 0 = 0
    rw [hH, Polynomial.eval_pow, hz]
    norm_num
  refine ⟨ε, H, ?_, by rw [hshape, hH], hH0⟩
  have he : ε = (G.map i).rootMultiplicity 0 := by
    simpa only [ε, map_zero] using Polynomial.eq_rootMultiplicity_map (p := G) i.injective (0 : K)
  rw [he]
  exact hzero

theorem even_degree_iff_eval_zero_ne_of_binary_shape
    {K : Type*} [Field K] {G H : K[X]} {ε : ℕ}
    (hε : ε ≤ 1) (hshape : G = X ^ ε * H ^ 2) (hH0 : H.eval 0 ≠ 0) :
    Even G.natDegree ↔ G.eval 0 ≠ 0 := by
  have hH : H ≠ 0 := by intro h; simp [h] at hH0
  have hdeg : G.natDegree = ε + 2 * H.natDegree := by
    rw [hshape, Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
      (pow_ne_zero _ hH), Polynomial.natDegree_X_pow, Polynomial.natDegree_pow]
  have heval : G.eval 0 = (0 : K) ^ ε * (H.eval 0) ^ 2 := by rw [hshape]; simp
  rcases Nat.eq_zero_or_pos ε with hε0 | hεpos
  · have hev : Even G.natDegree := ⟨H.natDegree, by omega⟩
    have hne : G.eval 0 ≠ 0 := by
      rw [heval, hε0, pow_zero, one_mul]
      exact pow_ne_zero 2 hH0
    exact iff_of_true hev hne
  · have hε1 : ε = 1 := by omega
    have hodd : Odd G.natDegree := ⟨H.natDegree, by omega⟩
    have hnot : ¬ Even G.natDegree := Nat.not_even_iff_odd.mpr hodd
    have hzero : G.eval 0 = 0 := by simp [heval, hε1]
    exact iff_of_false hnot (by simp [hzero])

end EventualIrreducibility.UniversalFactorParity

namespace EventualIrreducibility

open Polynomial

theorem FactorSeries.binary_rootMultiplicity_one_even
    {n : ℕ} (s : FactorSeries n) (hn : 0 < n)
    (L : Type*) [Field L] [CharP L 2] :
    Even ((s.factor.map (Int.castRingHom L)).rootMultiplicity 1) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hfactor⟩ := s.divides
  have hfactor' : s.factor * h = fInt n := hfactor.symm
  have hpd : 2 ∣ n * (n + 1) := Nat.two_dvd_mul_add_one n
  rcases Nat.prime_two.dvd_mul.mp hpd with hpn | hpN
  · have hr : 1 ≤ padicValNat 2 n := by
      apply (padicValNat_dvd_iff_le (p := 2) (a := n) (n := 1) (Nat.ne_of_gt hn)).mp
      simpa only [pow_one] using hpn
    exact UniversalBinaryParityDraft.integer_factor_rootMultiplicity_one_even
      (v := WittLift.abv (p := 2) (L := L)) WittVector.constantCoeff
      WittLift.norm_nonarchimedean WittLift.norm_integral WittLift.norm_discrete
      WittLift.norm_residue n (padicValNat 2 n) hn hr WittLift.norm_natCast
      s.factor h s.monic hfactor' (Or.inl rfl)
  · have hr : 1 ≤ padicValNat 2 (n + 1) := by
      apply (padicValNat_dvd_iff_le (p := 2) (a := n + 1) (n := 1) (by omega)).mp
      simpa only [pow_one] using hpN
    exact UniversalBinaryParityDraft.integer_factor_rootMultiplicity_one_even
      (v := WittLift.abv (p := 2) (L := L)) WittVector.constantCoeff
      WittLift.norm_nonarchimedean WittLift.norm_integral WittLift.norm_discrete
      WittLift.norm_residue n (padicValNat 2 (n + 1)) hn hr WittLift.norm_natCast
      s.factor h s.monic hfactor' (Or.inr rfl)

theorem FactorSeries.even_degree_iff_odd_constant
    {n : ℕ} (s : FactorSeries n) (hn : 2 ≤ n) :
    Even s.factor.natDegree ↔ Odd (s.factor.coeff 0) := by
  classical
  let K := ZMod 2
  let L := AlgebraicClosure K
  let i : K →+* L := algebraMap K L
  let G : K[X] := s.factor.map (Int.castRingHom K)
  obtain ⟨h, hfactor⟩ := s.divides
  have hfactor' : s.factor * h = fInt n := hfactor.symm
  have hpd : 2 ∣ n * (n + 1) := Nat.two_dvd_mul_add_one n
  have hmaps : G.map i = s.factor.map (Int.castRingHom L) := by
    ext j
    simp only [G, Polynomial.coeff_map, Int.coe_castRingHom, map_intCast]
  have hone := s.binary_rootMultiplicity_one_even (by omega : 0 < n) L
  obtain ⟨ε, H, hε, hshape, hH0⟩ :=
    UniversalFactorParity.exists_binary_shape_of_nonzero_multiplicities i G
      (s.monic.map _).ne_zero (IsAlgClosed.splits (G.map i))
      (by
        rw [hmaps]
        exact LocalShapeAssembly.factor_rootMultiplicity_zero_le_one
          n hn s.factor h s.monic hfactor')
      (by
        intro a ha0
        rw [hmaps]
        by_cases ha1 : a = 1
        · subst a
          exact even_iff_two_dvd.mp hone
        · exact LocalShapeAssembly.factor_nonexceptional_multiplicity_dvd
            unramifiedRootLiftInput_of_witt 2 Nat.prime_two L n hn hpd
            s.factor h s.monic hfactor' a ha0 ha1)
  have hfield := UniversalFactorParity.even_degree_iff_eval_zero_ne_of_binary_shape
    hε hshape hH0
  have hcast : Even s.factor.natDegree ↔ (s.factor.coeff 0 : ZMod 2) ≠ 0 := by
    simpa only [G, s.monic.natDegree_map, ← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_map, Int.coe_castRingHom] using hfield
  exact hcast.trans ((not_congr ZMod.intCast_eq_zero_iff_even).trans Int.not_even_iff_odd)

end EventualIrreducibility

open Polynomial
open scoped BigOperators

namespace UniversalScalar

variable {K : Type*} [Field K]

lemma dvd_of_dvd_X_mul {g P : K[X]} (ha : g.coeff 0 ≠ 0)
    (h : g ∣ X * P) : g ∣ P := by
  obtain ⟨q, hq⟩ := h
  have hq0 : q.coeff 0 = 0 := by
    have hc := congrArg (fun Q : K[X] => Q.coeff 0) hq
    simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_left ha
  obtain ⟨r, hr⟩ := (Polynomial.X_dvd_iff.mpr hq0)
  refine ⟨r, ?_⟩
  apply mul_left_cancel₀ (Polynomial.X_ne_zero : (X : K[X]) ≠ 0)
  calc
    X * P = g * q := hq
    _ = X * (g * r) := by rw [hr]; ring

lemma quotient_degree_bound_X_pow_sub_one {g q : K[X]} {m : ℕ}
    (hg : g.Monic) (hm : 0 < m) (hq : X ^ m - 1 = g * q) :
    q.natDegree + g.natDegree ≤ m := by
  have hpoly : (X ^ m - 1 : K[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun Q : K[X] => Q.coeff m) hz
    norm_num [Polynomial.coeff_one, hm.ne'] at hc
  have hqne : q ≠ 0 := by
    intro hz
    apply hpoly
    simpa [hz] using hq
  have hupper : (g * q).natDegree ≤ m := by
    rw [← hq]
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  rw [Polynomial.natDegree_mul hg.ne_zero hqne] at hupper
  omega

lemma signed_constant_pow_eq_one_of_dvd {g : K[X]} {m : ℕ}
    (hg : g.Monic) (hm : 0 < m) (hdiv : g ∣ X ^ m - 1) :
    ((-1 : K) ^ g.natDegree * g.coeff 0) ^ m = 1 := by
  obtain ⟨q, hq⟩ := hdiv
  have hdeg := quotient_degree_bound_X_pow_sub_one hg hm hq
  have hpoly : (X ^ m : K[X]) = 1 + g * q := by rw [← hq]; ring
  have he := Polynomial.resultant_add_mul_right g 1 q g.natDegree m hdeg le_rfl
  rw [← hpoly, Polynomial.resultant_X_pow_right g g.natDegree m le_rfl] at he
  have hone : g.resultant (1 : K[X]) g.natDegree m = 1 := by

    simp [hg.coeff_natDegree]
  rw [hone] at he
  simpa only [mul_pow, ← pow_mul] using he

lemma constant_pow_eq_sign_of_signed {a : K} {d m : ℕ}
    (h : ((-1 : K) ^ d * a) ^ m = 1) :
    a ^ m = (-1 : K) ^ (d * m) := by
  have he : (-1 : K) ^ (d * m) * a ^ m = 1 := by
    simpa only [mul_pow, ← pow_mul] using h
  have hsign : ((-1 : K) ^ (d * m)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (d * m) 2, pow_mul]
    norm_num
  calc
    a ^ m = ((-1 : K) ^ (d * m)) ^ 2 * a ^ m := by rw [hsign, one_mul]
    _ = (-1 : K) ^ (d * m) *
        ((-1 : K) ^ (d * m) * a ^ m) := by ring
    _ = (-1 : K) ^ (d * m) := by rw [he, mul_one]

lemma constant_pow_eq_sign_of_dvd {g : K[X]} {m : ℕ}
    (hg : g.Monic) (hm : 0 < m) (hdiv : g ∣ X ^ m - 1) :
    (g.coeff 0) ^ m = (-1 : K) ^ (g.natDegree * m) :=
  constant_pow_eq_sign_of_signed (signed_constant_pow_eq_one_of_dvd hg hm hdiv)

lemma trinomial_dvd_X_succ_sub_one {F g : K[X]} {n : ℕ}
    (hdiv : g ∣ F)
    (hF : (X - 1) ^ 2 * F =
      X ^ (n + 1) - C ((n + 1 : ℕ) : K) * X + C (n : K))
    (hN : ((n + 1 : ℕ) : K) = 0) :
    g ∣ X ^ (n + 1) - 1 := by
  have hn : (n : K) = -1 := by
    push_cast at hN
    linear_combination hN
  obtain ⟨h, hh⟩ := hdiv
  refine ⟨(X - 1) ^ 2 * h, ?_⟩
  have he : (X - 1) ^ 2 * F = X ^ (n + 1) - 1 := by
    simpa [hN, hn, sub_eq_add_neg] using hF
  rw [← he, hh]
  ring

lemma trinomial_dvd_X_pow_sub_one {F g : K[X]} {n : ℕ}
    (hdiv : g ∣ F)
    (hF : (X - 1) ^ 2 * F =
      X ^ (n + 1) - C ((n + 1 : ℕ) : K) * X + C (n : K))
    (hn : (n : K) = 0) (ha : g.coeff 0 ≠ 0) :
    g ∣ X ^ n - 1 := by
  apply dvd_of_dvd_X_mul ha
  obtain ⟨h, hh⟩ := hdiv
  refine ⟨(X - 1) ^ 2 * h, ?_⟩
  have he : (X - 1) ^ 2 * F = X * (X ^ n - 1) := by
    calc
      (X - 1) ^ 2 * F =
          X ^ (n + 1) - C ((n + 1 : ℕ) : K) * X + C (n : K) := hF
      _ = X * (X ^ n - 1) := by simp [hn, pow_succ]; ring
  rw [← he, hh]
  ring

lemma constant_ne_zero_of_reduced_linear {a b u v n : K}
    (hc : a * b = n) (hl : a * v + b * u = n - 1) (hb : b = 0) :
    a ≠ 0 := by
  intro ha
  have hn : n = 0 := by simpa [ha, hb] using hc.symm
  have hbad : (0 : K) = -1 := by simp [ha, hb, hn] at hl
  exact one_ne_zero (by linear_combination hbad)

end UniversalScalar

namespace EventualIrreducibility

variable {K : Type*} [Field K]

lemma mapped_trinomial_identity (n : ℕ) :
    (X - 1) ^ 2 * (fInt n).map (Int.castRingHom K) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : K) * X + C (n : K) := by
  have h := congrArg (Polynomial.map (Int.castRingHom K)) (trinomial_identity n)
  simpa using h

lemma FactorSeries.mapped_divides {n : ℕ} (s : FactorSeries n) :
    s.factor.map (Int.castRingHom K) ∣ (fInt n).map (Int.castRingHom K) := by
  obtain ⟨h, hh⟩ := s.divides
  refine ⟨h.map (Int.castRingHom K), ?_⟩
  rw [← Polynomial.map_mul, ← hh]

theorem FactorSeries.constant_succ_power_mod {n : ℕ}
    (s : FactorSeries n) (hN : ((n + 1 : ℕ) : K) = 0) :
    (s.factor.coeff 0 : K) ^ (n + 1) =
      (-1 : K) ^ (s.factor.natDegree * (n + 1)) := by
  have hdiv := UniversalScalar.trinomial_dvd_X_succ_sub_one
    (s.mapped_divides (K := K)) (mapped_trinomial_identity (K := K) n) hN
  have h := UniversalScalar.constant_pow_eq_sign_of_dvd
    (s.monic.map (Int.castRingHom K)) (Nat.succ_pos n) hdiv
  simpa only [Polynomial.coeff_map, Int.coe_castRingHom,
    s.monic.natDegree_map (Int.castRingHom K)] using h

theorem FactorSeries.constant_power_mod {n : ℕ}
    (s : FactorSeries n) (hnpos : 0 < n) (hn : (n : K) = 0)
    (ha : (s.factor.coeff 0 : K) ≠ 0) :
    (s.factor.coeff 0 : K) ^ n = (-1 : K) ^ (s.factor.natDegree * n) := by
  have hconst : (s.factor.map (Int.castRingHom K)).coeff 0 ≠ 0 := by
    simpa using ha
  have hdiv := UniversalScalar.trinomial_dvd_X_pow_sub_one
    (s.mapped_divides (K := K)) (mapped_trinomial_identity (K := K) n) hn hconst
  have h := UniversalScalar.constant_pow_eq_sign_of_dvd
    (s.monic.map (Int.castRingHom K)) hnpos hdiv
  simpa only [Polynomial.coeff_map, Int.coe_castRingHom,
    s.monic.natDegree_map (Int.castRingHom K)] using h

theorem FactorSeries.constant_power_mod_complement {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) {h : ℤ[X]}
    (hh : s.factor * h = fInt n) (hb : (h.coeff 0 : K) = 0) :
    (s.factor.coeff 0 : K) ^ n = (-1 : K) ^ (s.factor.natDegree * n) := by
  have h0 : (fInt n).coeff 0 = (n : ℤ) := by simp [coeff_fInt, hn]
  obtain ⟨hc, hl⟩ := UniversalIrreducibility.polynomial_constants_and_linear
    hh h0 (coeff_fInt_linear_int hn)
  have hcK : (s.factor.coeff 0 : K) * (h.coeff 0 : K) = (n : K) := by
    simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_natCast] using
      congrArg (Int.castRingHom K) hc
  have hlK : (s.factor.coeff 0 : K) * (h.coeff 1 : K) +
      (h.coeff 0 : K) * (s.factor.coeff 1 : K) = (n : K) - 1 := by
    exact_mod_cast congrArg (Int.castRingHom K) hl
  have hnK : (n : K) = 0 := by simpa [hb] using hcK.symm
  have haK := UniversalScalar.constant_ne_zero_of_reduced_linear hcK hlK hb
  exact s.constant_power_mod hn hnK haK

end EventualIrreducibility

namespace EventualIrreducibility.UniversalConstants

structure ThreePrimeDivisors (R : ℕ) where
  p : ℕ
  q : ℕ
  r : ℕ
  hp : p.Prime
  hq : q.Prime
  hr : r.Prime
  hpq : p < q
  hqr : q < r
  dvd : p * q * r ∣ R

private lemma prime_ge_five {p : ℕ} (hp : p.Prime) (h : 3 < p) : 5 ≤ p := by
  by_contra hn
  have he : p = 4 := by omega
  norm_num [he] at hp

private lemma prime_ge_seven {p : ℕ} (hp : p.Prime) (h : 5 < p) : 7 ≤ p := by
  by_contra hn
  have he : p = 6 := by omega
  norm_num [he] at hp

private lemma prime_ge_eleven {p : ℕ} (hp : p.Prime) (h : 7 < p) : 11 ≤ p := by
  have h8 : p ≠ 8 := by rintro rfl; norm_num at hp
  have h9 : p ≠ 9 := by rintro rfl; norm_num at hp
  have h10 : p ≠ 10 := by rintro rfl; norm_num at hp
  omega

lemma thirty_le_of_three_primes {R : ℕ} (hR : 0 < R)
    (s : ThreePrimeDivisors R) : 30 ≤ R := by
  have hpq := s.hpq
  have hqr := s.hqr
  have hp2 := s.hp.two_le
  have hq3 : 3 ≤ s.q := by omega
  have hr5 : 5 ≤ s.r := prime_ge_five s.hr (by omega)
  have hmin : 30 ≤ s.p * s.q * s.r := by
    exact Nat.mul_le_mul (Nat.mul_le_mul hp2 hq3) hr5
  exact hmin.trans (Nat.le_of_dvd hR s.dvd)

private lemma small_squarefree_multiple_eq {D R : ℕ}
    (hD : D = 30 ∨ D = 42 ∨ D = 66 ∨ D = 70)
    (hR : 0 < R) (hlt : R < 76) (hfour : ¬ 4 ∣ R) (hd : D ∣ R) : R = D := by
  rcases hd with ⟨t, ht⟩
  rcases hD with rfl | rfl | rfl | rfl
  · have htpos : 0 < t := by omega
    have htlt : t ≤ 2 := by omega
    have ht1 : t = 1 := by
      by_contra hn
      have ht2 : t = 2 := by omega
      apply hfour
      refine ⟨15, ?_⟩
      omega
    omega
  · have ht1 : t = 1 := by omega
    omega
  · have ht1 : t = 1 := by omega
    omega
  · have ht1 : t = 1 := by omega
    omega

lemma three_prime_support_lt_seventysix {R : ℕ}
    (hR : 0 < R) (hlt : R < 76) (hfour : ¬ 4 ∣ R)
    (s : ThreePrimeDivisors R) :
    R = 30 ∨ R = 42 ∨ R = 66 ∨ R = 70 := by
  have hpq := s.hpq
  have hqr := s.hqr
  have hdle : s.p * s.q * s.r ≤ R := Nat.le_of_dvd hR s.dvd
  have hp2 : s.p = 2 := by
    have hpmin := s.hp.two_le
    by_contra hn
    have hp3 : 3 ≤ s.p := by omega
    have hq5 : 5 ≤ s.q := prime_ge_five s.hq (by omega)
    have hr7 : 7 ≤ s.r := prime_ge_seven s.hr (by omega)
    have hmin : 105 ≤ s.p * s.q * s.r :=
      Nat.mul_le_mul (Nat.mul_le_mul hp3 hq5) hr7
    omega
  have hq3 : 3 ≤ s.q := by omega
  have hqle : s.q ≤ 5 := by
    by_contra hn
    have hq7 : 7 ≤ s.q := prime_ge_seven s.hq (by omega)
    have hr11 : 11 ≤ s.r := prime_ge_eleven s.hr (by omega)
    have hmin : 154 ≤ s.p * s.q * s.r := by
      simpa [hp2] using Nat.mul_le_mul (Nat.mul_le_mul (show 2 ≤ s.p by omega) hq7) hr11
    omega
  have hq4 : s.q ≠ 4 := by intro h; have hh := s.hq; norm_num [h] at hh
  have hqcases : s.q = 3 ∨ s.q = 5 := by omega
  have hD : s.p * s.q * s.r = 30 ∨ s.p * s.q * s.r = 42 ∨
      s.p * s.q * s.r = 66 ∨ s.p * s.q * s.r = 70 := by
    rcases hqcases with hq | hq
    · have hr5 : 5 ≤ s.r := prime_ge_five s.hr (by omega)
      have hrle : s.r ≤ 12 := by rw [hp2, hq] at hdle; omega
      have h6 : s.r ≠ 6 := by intro h; have hh := s.hr; norm_num [h] at hh
      have h8 : s.r ≠ 8 := by intro h; have hh := s.hr; norm_num [h] at hh
      have h9 : s.r ≠ 9 := by intro h; have hh := s.hr; norm_num [h] at hh
      have h10 : s.r ≠ 10 := by intro h; have hh := s.hr; norm_num [h] at hh
      have h12 : s.r ≠ 12 := by intro h; have hh := s.hr; norm_num [h] at hh
      have hr : s.r = 5 ∨ s.r = 7 ∨ s.r = 11 := by omega
      rcases hr with hr | hr | hr <;> simp [hp2, hq, hr]
    · have hr7 : 7 ≤ s.r := prime_ge_seven s.hr (by omega)
      have hr : s.r = 7 := by rw [hp2, hq] at hdle; omega
      simp [hp2, hq, hr]
  have heq := small_squarefree_multiple_eq hD hR hlt hfour s.dvd
  simpa [← heq] using hD

lemma thirteen_le_of_radical_invariants {a R : ℕ}
    (ha : 2 ≤ a) (hR : 0 < R) (hfour : ¬ 4 ∣ R)
    (s : ThreePrimeDivisors R) (hcop : Nat.Coprime a R)
    (hbound : (R : ℝ) < (107 / 49 : ℝ) * (a : ℝ) * Real.log (a : ℝ))
    (hlog7 : Real.log (7 : ℝ) < 39 / 20) (hlog12 : Real.log (12 : ℝ) < 5 / 2)
    (h11 : a ≠ 11) : 13 ≤ a := by
  by_contra hn
  have ha12 : a ≤ 12 := by omega
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hla : Real.log (a : ℝ) < 5 / 2 :=
    (Real.log_le_log hapos (by exact_mod_cast ha12)).trans_lt hlog12
  have hrough : (R : ℝ) < (535 / 98 : ℝ) * (a : ℝ) := by
    calc
      (R : ℝ) < (107 / 49 : ℝ) * (a : ℝ) * Real.log (a : ℝ) := hbound
      _ < (107 / 49 : ℝ) * (a : ℝ) * (5 / 2) :=
        mul_lt_mul_of_pos_left hla (by positivity)
      _ = (535 / 98 : ℝ) * (a : ℝ) := by ring
  have hRlt : R < 76 := by
    have ha12' : (a : ℝ) ≤ 12 := by exact_mod_cast ha12
    exact_mod_cast (show (R : ℝ) < 76 by nlinarith)
  have hsupport := three_prime_support_lt_seventysix hR hRlt hfour s
  have ha8 : 8 ≤ a := by
    by_contra hn8
    have ha7 : a ≤ 7 := by omega
    have hla2 : Real.log (a : ℝ) < 39 / 20 :=
      (Real.log_le_log hapos (by exact_mod_cast ha7)).trans_lt hlog7
    have ha7' : (a : ℝ) ≤ 7 := by exact_mod_cast ha7
    have hR30 : (30 : ℝ) ≤ R := by exact_mod_cast thirty_le_of_three_primes hR s
    have hh := mul_lt_mul_of_pos_left hla2 (show (0 : ℝ) < (107 / 49) * a by positivity)
    nlinarith
  interval_cases a <;>
    rcases hsupport with rfl | rfl | rfl | rfl <;>
    first | omega | norm_num [Nat.Coprime] at hcop
  all_goals norm_num at hrough

lemma pow_mod_period (a m k t : ℕ) (hm : 1 < m)
    (hk : a ^ k % m = 1) :
    a ^ t % m = a ^ (t % k) % m := by
  have hperiod : (a ^ k) ^ (t / k) % m = 1 := by
    rw [Nat.pow_mod, hk, one_pow, Nat.mod_eq_of_lt hm]
  conv_lhs => rw [← Nat.mod_add_div t k, pow_add, pow_mul]
  rw [Nat.mul_mod, hperiod,
    Nat.mul_one, Nat.mod_mod]

private lemma eleven_eq_of_split {x y c : ℕ}
    (hx : 0 < x) (hy : 0 < y) (_hc : 0 < c)
    (h11 : 11 ∣ x) (hcy : c ∣ y) (hprod : x * y = 11 * c) :
    x = 11 := by
  have hxl : 11 ≤ x := Nat.le_of_dvd hx h11
  have hyl : c ≤ y := Nat.le_of_dvd hy hcy
  have hm := Nat.mul_le_mul_left x hyl
  nlinarith

private lemma not_both_same {x y c : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hc : Nat.Coprime 11 c)
    (h11 : 11 ∣ x) (hcx : c ∣ x) (hprod : x * y = 11 * c) : False := by
  have hall : 11 * c ∣ x := hc.mul_dvd_of_dvd_of_dvd h11 hcx
  rw [← hprod] at hall
  have hle : x * y ≤ x := Nat.le_of_dvd (by omega) hall
  have hm := Nat.mul_le_mul_left x (show 2 ≤ y by omega)
  nlinarith

lemma eleven_factor_of_coprime_product {x y u : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hu : 0 < u)
    (hcop : Nat.Coprime x y) (hprod : x * y = 11 * 5 ^ u) :
    x = 11 ∨ y = 11 := by
  have hp11 : Nat.Prime 11 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have hcp : IsPrimePow (5 ^ u) :=
    (isPrimePow_nat_iff _).2 ⟨5, u, hp5, hu, rfl⟩
  have hcpos : 0 < 5 ^ u := pow_pos (by norm_num) _
  have hc11 : Nat.Coprime 11 (5 ^ u) := by
    simpa using Nat.coprime_pow_primes 1 u hp11 hp5 (by norm_num : 11 ≠ 5)
  have h11dvd : 11 ∣ x * y := ⟨5 ^ u, hprod⟩
  have hcdvd : 5 ^ u ∣ x * y := ⟨11, by simpa [Nat.mul_comm] using hprod⟩
  rcases hp11.dvd_mul.mp h11dvd with h11x | h11y
  · rcases (hcop.isPrimePow_dvd_mul hcp).mp hcdvd with hcx | hcy
    · exact False.elim (not_both_same hx hy hc11 h11x hcx hprod)
    · exact Or.inl (eleven_eq_of_split (by omega) (by omega) hcpos h11x hcy hprod)
  · rcases (hcop.isPrimePow_dvd_mul hcp).mp hcdvd with hcx | hcy
    · exact Or.inr (eleven_eq_of_split (by omega) (by omega) hcpos h11y hcx
        (by simpa [Nat.mul_comm] using hprod))
    · exact False.elim (not_both_same hy hx hc11 h11y hcy
        (by simpa [Nat.mul_comm] using hprod))

lemma no_coprime_gap_two_product_eleven_five_pow {x y u : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hu : 0 < u)
    (hcop : Nat.Coprime x y) (hgap : y = x + 2)
    (hprod : x * y = 11 * 5 ^ u) : False := by
  have h5dvd : 5 ∣ 5 ^ u := dvd_pow_self 5 hu.ne'
  rcases eleven_factor_of_coprime_product hx hy hu hcop hprod with hx11 | hy11
  · have hpow : 5 ^ u = 13 := by rw [hx11, hgap, hx11] at hprod; omega
    norm_num [hpow] at h5dvd
  · have hx9 : x = 9 := by omega
    have hpow : 5 ^ u = 9 := by rw [hx9, hy11] at hprod; omega
    norm_num [hpow] at h5dvd

lemma no_eleven_power_equation {u v w : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (heq : 11 * 5 ^ u + 1 = 2 ^ v * 3 ^ w) : False := by
  have h3dvd : 3 ∣ 2 ^ v * 3 ^ w :=
    dvd_mul_of_dvd_right (dvd_pow_self 3 hw.ne') _
  have hmod3 : (11 * 5 ^ u + 1) % 3 = 0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd h3dvd
  have hp3 := pow_mod_period 5 3 2 u (by norm_num) (by norm_num)
  have hu2 : u % 2 = 0 := by
    have hub : u % 2 < 2 := Nat.mod_lt _ (by norm_num)
    by_contra hn
    have hu1 : u % 2 = 1 := by omega
    have hh : 5 ^ u % 3 = 2 := by rw [hp3, hu1]; norm_num
    norm_num [Nat.add_mod, Nat.mul_mod, hh] at hmod3
  have h58 : 5 ^ u % 8 = 1 := by
    rw [pow_mod_period 5 8 2 u (by norm_num) (by norm_num), hu2]
    norm_num
  have hright8 : (2 ^ v * 3 ^ w) % 8 = 4 := by
    rw [← heq]
    norm_num [Nat.add_mod, Nat.mul_mod, h58]
  have hvlt : v < 3 := by
    by_contra h
    have hle : 3 ≤ v := by omega
    have h8 : 8 ∣ 2 ^ v := by
      refine ⟨2 ^ (v - 3), ?_⟩
      calc
        2 ^ v = 2 ^ (3 + (v - 3)) := by congr 1; omega
        _ = 8 * 2 ^ (v - 3) := by rw [pow_add]; norm_num
    have h8' : 8 ∣ 2 ^ v * 3 ^ w := dvd_mul_of_dvd_left h8 _
    have hz := Nat.mod_eq_zero_of_dvd h8'
    omega
  have h3odd : 3 ^ w % 2 = 1 := by simp [Nat.pow_mod]
  have hv2 : v = 2 := by
    by_contra hn
    have hv1 : v = 1 := by omega
    simp only [hv1, pow_one] at hright8
    omega
  have h5u : 5 ∣ 5 ^ u := dvd_pow_self 5 hu.ne'
  have h5zero : 5 ^ u % 5 = 0 := Nat.mod_eq_zero_of_dvd h5u
  have hright5 : (4 * 3 ^ w) % 5 = 1 := by
    have hh := congrArg (fun z : ℕ => z % 5) heq
    norm_num [hv2, Nat.add_mod, Nat.mul_mod, h5zero] at hh ⊢
    exact hh.symm
  have hp5 := pow_mod_period 3 5 4 w (by norm_num) (by norm_num)
  have hwb : w % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hwcases : w % 4 = 0 ∨ w % 4 = 1 ∨ w % 4 = 2 ∨ w % 4 = 3 := by omega
  have hw4 : w % 4 = 2 := by
    rcases hwcases with hh | hh | hh | hh
    · have hh' : 3 ^ w % 5 = 1 := by rw [hp5, hh]; norm_num
      norm_num [Nat.mul_mod, hh'] at hright5
    · have hh' : 3 ^ w % 5 = 3 := by rw [hp5, hh]; norm_num
      norm_num [Nat.mul_mod, hh'] at hright5
    · exact hh
    · have hh' : 3 ^ w % 5 = 2 := by rw [hp5, hh]; norm_num
      norm_num [Nat.mul_mod, hh'] at hright5
  have hwEven : Even w := Nat.even_iff.mpr (by omega)
  obtain ⟨k, hk⟩ := hwEven
  have hkpos : 0 < k := by omega
  have h3k : 3 ≤ 3 ^ k := Nat.le_of_dvd (pow_pos (by norm_num) _)
    (dvd_pow_self 3 hkpos.ne')
  let x := 2 * 3 ^ k - 1
  let y := 2 * 3 ^ k + 1
  have hx : 1 < x := by dsimp [x]; omega
  have hy : 1 < y := by dsimp [y]; omega
  have hgap : y = x + 2 := by dsimp [x, y]; omega
  have hxodd : Odd x := by rw [Nat.odd_iff]; dsimp [x]; omega
  have hcop : Nat.Coprime x y := by
    rw [hgap, Nat.coprime_self_add_right]
    exact Nat.coprime_two_right.mpr hxodd
  have hprod : x * y = 11 * 5 ^ u := by
    rw [hv2, hk, pow_add] at heq
    dsimp [x, y]
    have hxsub : 2 * 3 ^ k - 1 + 1 = 2 * 3 ^ k := by omega
    nlinarith
  exact no_coprime_gap_two_product_eleven_five_pow hx hy hu hcop hgap hprod

end EventualIrreducibility.UniversalConstants

namespace EventualIrreducibility.UniversalConstants

lemma three_prime_divisors_of_distinct {p q r R : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpd : p ∣ R) (hqd : q ∣ R) (hrd : r ∣ R) :
    Nonempty (ThreePrimeDivisors R) := by
  have hpqc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hprc : Nat.Coprime p r := (Nat.coprime_primes hp hr).2 hpr
  have hqrc : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hqr
  have hpqd : p * q ∣ R := hpqc.mul_dvd_of_dvd_of_dvd hpd hqd
  have hprod : p * q * r ∣ R :=
    (hprc.mul_left hqrc).mul_dvd_of_dvd_of_dvd hpqd hrd
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · rcases lt_or_gt_of_ne hqr with hqr | hrq
    · exact ⟨⟨p, q, r, hp, hq, hr, hpq, hqr, hprod⟩⟩
    · rcases lt_or_gt_of_ne hpr with hpr | hrp
      · exact ⟨⟨p, r, q, hp, hr, hq, hpr, hrq,
          by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod⟩⟩
      · exact ⟨⟨r, p, q, hr, hp, hq, hrp, hpq,
          by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod⟩⟩
  · rcases lt_or_gt_of_ne hpr with hpr | hrp
    · exact ⟨⟨q, p, r, hq, hp, hr, hqp, hpr,
        by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod⟩⟩
    · rcases lt_or_gt_of_ne hqr with hqr | hrq
      · exact ⟨⟨q, r, p, hq, hr, hp, hqr, hrp,
          by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod⟩⟩
      · exact ⟨⟨r, q, p, hr, hq, hp, hrq, hqp,
          by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod⟩⟩

lemma three_prime_divisors_of_nonprimepower {b N R : ℕ}
    (hb : 2 ≤ b) (hN : 2 ≤ N) (hcop : Nat.Coprime b N)
    (hpp : ¬ IsPrimePow N)
    (hrad : ∀ p : ℕ, p.Prime → p ∣ b * N → p ∣ R) :
    Nonempty (ThreePrimeDivisors R) := by
  obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd (show b ≠ 1 by omega)
  obtain ⟨q, hq, r, hr, hqr⟩ :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hN).1 hpp
  obtain ⟨hqp, hqN, _⟩ := Nat.mem_primeFactors.mp hq
  obtain ⟨hrp, hrN, _⟩ := Nat.mem_primeFactors.mp hr
  have hgcd : Nat.gcd b N = 1 := hcop
  have hpq : p ≠ q := by
    intro he
    have hpd : p ∣ Nat.gcd b N := Nat.dvd_gcd hpb (by simpa [he] using hqN)
    rw [hgcd] at hpd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hpd
    have hp2 := hp.two_le
    omega
  have hpr : p ≠ r := by
    intro he
    have hpd : p ∣ Nat.gcd b N := Nat.dvd_gcd hpb (by simpa [he] using hrN)
    rw [hgcd] at hpd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hpd
    have hp2 := hp.two_le
    omega
  exact three_prime_divisors_of_distinct hp hqp hrp hpq hpr hqr
    (hrad p hp (dvd_mul_of_dvd_left hpb _))
    (hrad q hqp (dvd_mul_of_dvd_right hqN _))
    (hrad r hrp (dvd_mul_of_dvd_right hrN _))

lemma eleven_pow_mod_three_ne_one_of_odd {k : ℕ} (hk : Odd k) :
    11 ^ k % 3 ≠ 1 := by
  have hk2 : k % 2 = 1 := Nat.odd_iff.mp hk
  rw [pow_mod_period 11 3 2 k (by norm_num) (by norm_num), hk2]
  norm_num

lemma three_dvd_of_eleven_pow_mod_seven {k : ℕ} (hk : 11 ^ k % 7 = 1) :
    3 ∣ k := by
  have hper := pow_mod_period 11 7 3 k (by norm_num) (by norm_num)
  have hb : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hc : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  apply Nat.dvd_of_mod_eq_zero
  rcases hc with hh | hh | hh
  · exact hh
  · rw [hper, hh] at hk
    norm_num at hk
  · rw [hper, hh] at hk
    norm_num at hk

lemma no_three_or_seven_in_eleven_cofactor {n b : ℕ}
    (hn : n = 11 * b) (hnodd : Odd n)
    (hunit : ∀ p : ℕ, p.Prime → p ∣ b → 11 ^ n % p = 1) :
    (¬ 3 ∣ b) ∧ (¬ 7 ∣ b) := by
  have h3 : ¬ 3 ∣ b := by
    intro h
    exact eleven_pow_mod_three_ne_one_of_odd hnodd (hunit 3 (by norm_num) h)
  refine ⟨h3, ?_⟩
  intro h7
  have hn3 := three_dvd_of_eleven_pow_mod_seven (hunit 7 (by norm_num) h7)
  rw [hn] at hn3
  rcases Nat.prime_three.dvd_mul.mp hn3 with hbad | hgood
  · norm_num at hbad
  · exact h3 hgood

lemma exists_positive_prime_power_of_support {b p : ℕ}
    (hb : 2 ≤ b) (hp : p.Prime)
    (hs : ∀ q : ℕ, q.Prime → q ∣ b → q = p) :
    ∃ u : ℕ, 0 < u ∧ b = p ^ u := by
  obtain ⟨q, hq, hqb⟩ := Nat.exists_prime_and_dvd (show b ≠ 1 by omega)
  have hqp := hs q hq hqb
  have hpb : p ∣ b := by simpa [hqp] using hqb
  have hpp : IsPrimePow b := isPrimePow_iff_unique_prime_dvd.2
    ⟨p, ⟨hp, hpb⟩, by rintro q ⟨hq, hqb⟩; exact hs q hq hqb⟩
  obtain ⟨q, u, hq, hu, heq⟩ := (isPrimePow_nat_iff _).1 hpp
  have hqb : q ∣ b := by rw [← heq]; exact dvd_pow_self q hu.ne'
  have hqp := hs q hq hqb
  exact ⟨u, hu, by simpa [hqp] using heq.symm⟩

lemma exists_two_positive_prime_powers_of_support {N p q : ℕ}
    (hN : 2 ≤ N) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpp : ¬ IsPrimePow N)
    (hs : ∀ r : ℕ, r.Prime → r ∣ N → r = p ∨ r = q) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ N = p ^ u * q ^ v := by
  obtain ⟨r, hr, s, hs', hrs⟩ :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hN).1 hpp
  obtain ⟨hrp, hrN, _⟩ := Nat.mem_primeFactors.mp hr
  obtain ⟨hsp, hsN, _⟩ := Nat.mem_primeFactors.mp hs'
  have hrpq := hs r hrp hrN
  have hspq := hs s hsp hsN
  have hpN : p ∣ N := by
    rcases hrpq with rfl | rfl
    · exact hrN
    · rcases hspq with rfl | rfl
      · exact hsN
      · exact False.elim (hrs rfl)
  have hqN : q ∣ N := by
    rcases hspq with rfl | rfl
    · rcases hrpq with rfl | rfl
      · exact False.elim (hrs rfl)
      · exact hrN
    · exact hsN
  have hN0 : N ≠ 0 := by omega
  have hpMem : p ∈ N.primeFactors := hp.mem_primeFactors hpN hN0
  have hqMem : q ∈ N.primeFactors := hq.mem_primeFactors hqN hN0
  have hset : N.primeFactors = {p, q} := by
    ext r
    constructor
    · intro hr
      obtain ⟨hrp, hrN, _⟩ := Nat.mem_primeFactors.mp hr
      rcases hs r hrp hrN with rfl | rfl <;> simp
    · intro hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hpMem
      · exact hqMem
  refine ⟨N.factorization p, N.factorization q,
    hp.factorization_pos_of_dvd hN0 hpN,
    hq.factorization_pos_of_dvd hN0 hqN, ?_⟩
  have heq := Nat.prod_primeFactors_pow_factorization hN0
  rw [hset] at heq
  simpa [hpq] using heq

private lemma prime_dvd_three_primes {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (h : p ∣ q * r * s) : p = q ∨ p = r ∨ p = s := by
  rcases hp.dvd_mul.mp h with hqr | hps
  · rcases hp.dvd_mul.mp hqr with hpq | hpr
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 hpq)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hr).1 hpr))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hs).1 hps))

lemma prime_dvd_thirty {p : ℕ} (hp : p.Prime) (h : p ∣ 30) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  exact prime_dvd_three_primes hp (by norm_num) (by norm_num) (by norm_num)
    (by simpa using h)

lemma prime_dvd_fortytwo {p : ℕ} (hp : p.Prime) (h : p ∣ 42) :
    p = 2 ∨ p = 3 ∨ p = 7 := by
  exact prime_dvd_three_primes hp (by norm_num) (by norm_num) (by norm_num)
    (by simpa using h)

private lemma not_common_prime {p b N : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime b N) (hb : p ∣ b) : ¬ p ∣ N := by
  intro hN
  have hdiv := Nat.dvd_gcd hb hN
  have hgcd : Nat.gcd b N = 1 := hcop
  rw [hgcd] at hdiv
  have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hdiv
  have hp2 := hp.two_le
  omega

private lemma three_dvd_of_nonprimepower_support {N q : ℕ}
    (hN : 2 ≤ N) (hpp : ¬ IsPrimePow N) (h2 : ¬ 2 ∣ N)
    (hs : ∀ p : ℕ, p.Prime → p ∣ N → p = 2 ∨ p = 3 ∨ p = q) :
    3 ∣ N := by
  obtain ⟨r, hr, s, hs', hrs⟩ :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hN).1 hpp
  obtain ⟨hrp, hrN, _⟩ := Nat.mem_primeFactors.mp hr
  obtain ⟨hsp, hsN, _⟩ := Nat.mem_primeFactors.mp hs'
  rcases hs r hrp hrN with hr2 | hr3 | hrq
  · exact False.elim (h2 (by simpa [hr2] using hrN))
  · simpa [hr3] using hrN
  · rcases hs s hsp hsN with hs2 | hs3 | hsq
    · exact False.elim (h2 (by simpa [hs2] using hsN))
    · simpa [hs3] using hsN
    · exact False.elim (hrs (hrq.trans hsq.symm))

lemma eleven_impossible_of_arithmetic_invariants {n b N R : ℕ}
    (hb : 2 ≤ b) (hn : n = 11 * b) (hN : N = n + 1)
    (hcop : Nat.Coprime b N) (hpp : ¬ IsPrimePow N)
    (hR : R = 30 ∨ R = 42)
    (hrad : ∀ p : ℕ, p.Prime → p ∣ b * N → p ∣ R)
    (hunitb : ∀ p : ℕ, p.Prime → p ∣ b → 11 ^ n % p = 1)
    (hunitN : ∀ p : ℕ, p.Prime → p ∣ N → 11 ^ N % p = 1) : False := by
  have hN2 : 2 ≤ N := by omega
  have hsmall : ∀ p : ℕ, p.Prime → p ∣ b * N →
      p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    intro p hp hpd
    have hpR := hrad p hp hpd
    rcases hR with hR | hR
    · rw [hR] at hpR
      rcases prime_dvd_thirty hp hpR with h | h | h <;> simp [h]
    · rw [hR] at hpR
      rcases prime_dvd_fortytwo hp hpR with h | h | h <;> simp [h]
  by_cases hbeven : Even b
  · obtain ⟨t, ht⟩ := hbeven
    have h2b : 2 ∣ b := ⟨t, by omega⟩
    have h2N : ¬ 2 ∣ N := not_common_prime (by norm_num) hcop h2b
    have hNodd : Odd N := by
      refine ⟨11 * t, ?_⟩
      omega
    have h3N : 3 ∣ N := by
      rcases hR with hR30 | hR42
      · apply three_dvd_of_nonprimepower_support hN2 hpp h2N (q := 5)
        intro p hp hpN
        have hpR := hrad p hp (dvd_mul_of_dvd_right hpN b)
        rw [hR30] at hpR
        exact prime_dvd_thirty hp hpR
      · apply three_dvd_of_nonprimepower_support hN2 hpp h2N (q := 7)
        intro p hp hpN
        have hpR := hrad p hp (dvd_mul_of_dvd_right hpN b)
        rw [hR42] at hpR
        exact prime_dvd_fortytwo hp hpR
    exact eleven_pow_mod_three_ne_one_of_odd hNodd (hunitN 3 (by norm_num) h3N)
  · have hbodd : Odd b := by
      rw [Nat.even_iff] at hbeven
      apply Nat.odd_iff.mpr
      have hb2 := Nat.mod_lt b (by norm_num : 0 < 2)
      omega
    have hnodd : Odd n := by
      rw [hn]
      exact (show Odd (11 : ℕ) by norm_num).mul hbodd
    obtain ⟨h3b, h7b⟩ := no_three_or_seven_in_eleven_cofactor hn hnodd hunitb
    have h2b : ¬ 2 ∣ b := by
      intro h
      have hz := Nat.mod_eq_zero_of_dvd h
      have ho := Nat.odd_iff.mp hbodd
      omega
    have hbsupport : ∀ p : ℕ, p.Prime → p ∣ b → p = 5 := by
      intro p hp hpb
      rcases hsmall p hp (dvd_mul_of_dvd_left hpb N) with h2 | h3 | h5 | h7
      · exact False.elim (h2b (by simpa [h2] using hpb))
      · exact False.elim (h3b (by simpa [h3] using hpb))
      · exact h5
      · exact False.elim (h7b (by simpa [h7] using hpb))
    obtain ⟨u, hu, hbpow⟩ :=
      exists_positive_prime_power_of_support hb (by norm_num : Nat.Prime 5) hbsupport
    have h5b : 5 ∣ b := by rw [hbpow]; exact dvd_pow_self 5 hu.ne'
    have h5N : ¬ 5 ∣ N := not_common_prime (by norm_num) hcop h5b
    have hR30 : R = 30 := by
      rcases hR with h | h
      · exact h
      · have hh := hrad 5 (by norm_num) (dvd_mul_of_dvd_left h5b N)
        norm_num [h] at hh
    have hNsupport : ∀ p : ℕ, p.Prime → p ∣ N → p = 2 ∨ p = 3 := by
      intro p hp hpN
      have hpR := hrad p hp (dvd_mul_of_dvd_right hpN b)
      rw [hR30] at hpR
      rcases prime_dvd_thirty hp hpR with h2 | h3 | h5
      · exact Or.inl h2
      · exact Or.inr h3
      · exact False.elim (h5N (by simpa [h5] using hpN))
    obtain ⟨v, w, hv, hw, hNpow⟩ := exists_two_positive_prime_powers_of_support
      hN2 (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 3)
      (by norm_num : (2 : ℕ) ≠ 3) hpp hNsupport
    apply no_eleven_power_equation hu hv hw
    calc
      11 * 5 ^ u + 1 = N := by rw [hN, hn, hbpow]
      _ = 2 ^ v * 3 ^ w := hNpow

lemma thirteen_le_of_arithmetic_invariants {a b n N R : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hn : n = a * b) (hN : N = n + 1)
    (hbN : Nat.Coprime b N) (haR : Nat.Coprime a R)
    (hpp : ¬ IsPrimePow N) (hRpos : 0 < R) (hfour : ¬ 4 ∣ R)
    (hrad : ∀ p : ℕ, p.Prime → p ∣ b * N → p ∣ R)
    (hbound : (R : ℝ) < (107 / 49 : ℝ) * (a : ℝ) * Real.log (a : ℝ))
    (hlog7 : Real.log (7 : ℝ) < 39 / 20)
    (hlog12 : Real.log (12 : ℝ) < 5 / 2)
    (hunitb : ∀ p : ℕ, p.Prime → p ∣ b → a ^ n % p = 1)
    (hunitN : Odd a → ∀ p : ℕ, p.Prime → p ∣ N → a ^ N % p = 1) :
    13 ≤ a := by
  have hN2 : 2 ≤ N := by nlinarith
  obtain ⟨s⟩ := three_prime_divisors_of_nonprimepower hb hN2 hbN hpp hrad
  apply thirteen_le_of_radical_invariants ha hRpos hfour s haR hbound hlog7 hlog12
  intro ha11
  have hlog11 : Real.log (11 : ℝ) < 5 / 2 :=
    (Real.log_le_log (by norm_num) (by norm_num : (11 : ℝ) ≤ 12)).trans_lt hlog12
  have hR70 : R < 70 := by
    have hb' := hbound
    rw [ha11] at hb'
    have hR70' : (R : ℝ) < 70 := by nlinarith
    exact_mod_cast hR70'
  have hcases := three_prime_support_lt_seventysix hRpos (by omega) hfour s
  have hsmall : R = 30 ∨ R = 42 := by
    rcases hcases with h30 | h42 | h66 | h70
    · exact Or.inl h30
    · exact Or.inr h42
    · norm_num [ha11, h66] at haR
    · omega
  have hnb : n = 11 * b := by simpa [ha11] using hn
  have hunb : ∀ p : ℕ, p.Prime → p ∣ b → 11 ^ n % p = 1 := by
    simpa [ha11] using hunitb
  have hunN : ∀ p : ℕ, p.Prime → p ∣ N → 11 ^ N % p = 1 := by
    have ho : Odd a := by norm_num [ha11]
    simpa [ha11] using hunitN ho
  exact eleven_impossible_of_arithmetic_invariants hb hnb hN hbN hpp hsmall hrad hunb hunN

end EventualIrreducibility.UniversalConstants

namespace EventualIrreducibility.UniversalConstants

def supportRadical (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

private lemma prime_coprime_finset_product {p : ℕ} (hp : p.Prime)
    (s : Finset ℕ) (hs : ∀ q ∈ s, q.Prime) (hnot : p ∉ s) :
    Nat.Coprime p (∏ q ∈ s, q) := by
  classical
  revert hs hnot
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
    intro hs hnot
    have hqp : q.Prime := hs q (Finset.mem_insert_self q s)
    have hpq : p ≠ q := by
      intro heq
      apply hnot
      simp [heq]
    have hs' : ∀ r ∈ s, r.Prime := by
      intro r hr
      exact hs r (Finset.mem_insert_of_mem hr)
    have hnot' : p ∉ s := by
      intro h
      exact hnot (Finset.mem_insert_of_mem h)
    rw [Finset.prod_insert hq]
    exact ((Nat.coprime_primes hp hqp).2 hpq).mul_right (ih hs' hnot')

lemma prime_finset_product_squarefree (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    intro hs
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := by
      intro q hq
      exact hs q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp]
    exact (Nat.squarefree_mul (prime_coprime_finset_product hpp s hs' hp)).2
      ⟨hpp.squarefree, ih hs'⟩

lemma supportRadical_pos (m : ℕ) : 0 < supportRadical m := by
  unfold supportRadical
  exact Finset.prod_pos fun p hp => (Nat.mem_primeFactors.mp hp).1.pos

lemma supportRadical_dvd (m : ℕ) : supportRadical m ∣ m :=
  Nat.prod_primeFactors_dvd m

lemma prime_dvd_supportRadical {p m : ℕ} (hp : p.Prime)
    (hpm : p ∣ m) (hm : m ≠ 0) : p ∣ supportRadical m := by
  have hmem : p ∈ m.primeFactors := hp.mem_primeFactors hpm hm
  unfold supportRadical
  exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hmem

lemma four_not_dvd_supportRadical (m : ℕ) : ¬ 4 ∣ supportRadical m := by
  have hsf : Squarefree (supportRadical m) :=
    prime_finset_product_squarefree m.primeFactors
      (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  simpa using (Nat.squarefree_iff_prime_squarefree.1 hsf) 2 Nat.prime_two

lemma coprime_factor_successor (a b : ℕ) : Nat.Coprime a (a * b + 1) := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpN
  have hpn : p ∣ a * b := dvd_mul_of_dvd_left hpa b
  have hh := Nat.dvd_sub hpN hpn
  simpa using hh

theorem thirteen_le_of_norms_and_radical_bound {a b n N : ℕ} (J : ℤ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hn : n = a * b) (hN : N = n + 1)
    (hab : Nat.Coprime a b) (hpp : ¬ IsPrimePow N)
    (hJ : J ≠ 0) (hJdiv : (supportRadical (b * N) : ℤ) ∣ J)
    (hJbound : (J.natAbs : ℝ) < (107 / 49 : ℝ) * (a : ℝ) * Real.log (a : ℝ))
    (hlog7 : Real.log (7 : ℝ) < 39 / 20)
    (hlog12 : Real.log (12 : ℝ) < 5 / 2)
    (hunitb : ∀ p : ℕ, p.Prime → p ∣ b → a ^ n % p = 1)
    (hunitN : Odd a → ∀ p : ℕ, p.Prime → p ∣ N → a ^ N % p = 1) :
    13 ≤ a := by
  have hN2 : 2 ≤ N := by nlinarith
  have hbN : Nat.Coprime b N := by
    rw [hN, hn, Nat.mul_comm a b]
    exact coprime_factor_successor b a
  have haN : Nat.Coprime a N := by
    rw [hN, hn]
    exact coprime_factor_successor a b
  have haBN : Nat.Coprime a (b * N) := hab.mul_right haN
  have haR : Nat.Coprime a (supportRadical (b * N)) :=
    haBN.coprime_dvd_right (supportRadical_dvd (b * N))
  have hbn0 : b * N ≠ 0 := by positivity
  have hrad : ∀ p : ℕ, p.Prime → p ∣ b * N → p ∣ supportRadical (b * N) := by
    intro p hp hpd
    exact prime_dvd_supportRadical hp hpd hbn0
  have hle : supportRadical (b * N) ≤ J.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hJ) (Int.natCast_dvd.mp hJdiv)
  have hbound : (supportRadical (b * N) : ℝ) <
      (107 / 49 : ℝ) * (a : ℝ) * Real.log (a : ℝ) := by
    exact lt_of_le_of_lt (by exact_mod_cast hle) hJbound
  exact thirteen_le_of_arithmetic_invariants ha hb hn hN hbN haR hpp
    (supportRadical_pos (b * N)) (four_not_dvd_supportRadical (b * N)) hrad
    hbound hlog7 hlog12 hunitb hunitN

end EventualIrreducibility.UniversalConstants

namespace EventualIrreducibility.UniversalConstants

theorem prime_power_norm_one_mod
    {p a r : ℕ} (hp : p.Prime)
    (h : (a : ZMod p) ^ (p ^ r) = 1) : a % p = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have ha : (a : ZMod p) = 1 := by
    simpa only [ZMod.pow_card_pow] using h
  have hm := (ZMod.natCast_eq_natCast_iff' a 1 p).mp (by simpa using ha)
  simpa only [Nat.mod_eq_of_lt hp.one_lt] using hm

theorem prime_power_norm_neg_one_dvd
    {p b r : ℕ} (hp : p.Prime)
    (h : (b : ZMod p) ^ (p ^ r) = -1) : p ∣ b + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hb : (b : ZMod p) = -1 := by
    simpa only [ZMod.pow_card_pow] using h
  have hz : ((b + 1 : ℕ) : ZMod p) = (0 : ℕ) := by
    push_cast
    rw [hb]
    ring
  have hm := (ZMod.natCast_eq_natCast_iff' (b + 1) 0 p).mp hz
  exact Nat.dvd_of_mod_eq_zero (by simpa using hm)

theorem prime_square_residue_forces_constants
    {p a b : ℕ} (hp : 2 ≤ p) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hprod : a * b + 1 = p ^ 2)
    (ha_mod : a % p = 1) (hb_dvd : p ∣ b + 1) :
    a = p + 1 ∧ b + 1 = p := by
  have hp0 : 0 < p := by omega
  have ha_min : p + 1 ≤ a := by
    by_contra h
    have hap : a ≤ p := by omega
    rcases lt_or_eq_of_le hap with hap | rfl
    · rw [Nat.mod_eq_of_lt hap] at ha_mod
      omega
    · simp at ha_mod
  have hb_min : p ≤ b + 1 := Nat.le_of_dvd (by omega) hb_dvd
  have hb_max : b + 1 ≤ p := by
    by_contra h
    have hpb : p ≤ b := by omega
    have hmul := Nat.mul_le_mul ha_min hpb
    nlinarith
  have hb_eq : b + 1 = p := by omega
  have ha_eq : a = p + 1 := by
    nlinarith
  exact ⟨ha_eq, hb_eq⟩

theorem no_coprime_prime_square_residue_factorization
    {p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hcop : a.Coprime b)
    (hprod : a * b + 1 = p ^ 2)
    (ha_mod : a % p = 1) (hb_dvd : p ∣ b + 1) : False := by
  obtain ⟨ha_eq, hb_eq⟩ :=
    prime_square_residue_forces_constants hp.two_le ha hb hprod ha_mod hb_dvd
  have hpodd : Odd p :=
    Nat.coprime_two_right.mp ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  obtain ⟨k, hk⟩ := hpodd
  have h2a : 2 ∣ a := ⟨k + 1, by omega⟩
  have h2b : 2 ∣ b := ⟨k, by omega⟩
  have h2one : 2 ∣ 1 := by
    simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd h2a h2b
  norm_num at h2one

theorem no_coprime_prime_square_norm_factorization
    {p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hcop : a.Coprime b)
    (hprod : a * b + 1 = p ^ 2)
    (ha_norm : (a : ZMod p) ^ (p ^ 2) = 1)
    (hb_norm : (b : ZMod p) ^ (p ^ 2) = -1) : False := by
  exact no_coprime_prime_square_residue_factorization hp hp2 ha hb hcop hprod
    (prime_power_norm_one_mod hp ha_norm)
    (prime_power_norm_neg_one_dvd hp hb_norm)

end EventualIrreducibility.UniversalConstants

namespace EventualIrreducibility.UniversalConstants

theorem cyclotomic_prime_power_eval_identity
    {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    (k : ℕ) (z : R) :
    (Polynomial.cyclotomic (p ^ (k + 1)) R).eval z *
        (z ^ (p ^ k) - 1) = z ^ (p ^ (k + 1)) - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have h := congrArg (Polynomial.eval z)
    (Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one R p k)
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one] using h

theorem cyclotomic_prime_power_eval_one
    {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (Polynomial.cyclotomic (p ^ (k + 1)) R).eval 1 = (p : R) := by
  let : Fact p.Prime := ⟨hp⟩
  exact Polynomial.eval_one_cyclotomic_prime_pow k

end EventualIrreducibility.UniversalConstants

namespace EventualIrreducibility.UniversalConstants

theorem three_eighths_quotient_scalar
    {x y v w : ℝ} (hx : 4 < x) (hy : 1 < y) (hv : 0 ≤ v)
    (hxy : x = w * y) (hbound : x - 1 ≤ v * (y + 1)) :
    (3 / 8 : ℝ) * w < v := by
  have hy0 : 0 < y := by linarith
  have hfirst : (3 / 4 : ℝ) * x < v * (y + 1) := by nlinarith
  have hv0 : 0 < v := by
    by_contra h
    have hvz : v = 0 := by linarith
    rw [hvz] at hfirst
    nlinarith
  have hsecond : v * (y + 1) < 2 * (v * y) := by
    nlinarith [mul_pos hv0 (sub_pos.mpr hy)]
  by_contra h
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h) hy0.le
  nlinarith

theorem norm_gt_three_eighths_of_power_quotient
    {z v : ℂ} {m q h : ℕ}
    (hz : 1 < ‖z‖) (hq : 0 < q) (hfour : 4 < ‖z‖ ^ m)
    (hm : m = h + q)
    (hidentity : v * (z ^ q - 1) = z ^ m - 1) :
    (3 / 8 : ℝ) * ‖z‖ ^ h < ‖v‖ := by
  have hy : 1 < ‖z‖ ^ q := one_lt_pow₀ hz (by omega)
  have hprod : ‖v‖ * ‖z ^ q - 1‖ = ‖z ^ m - 1‖ := by
    simpa only [norm_mul] using congrArg norm hidentity
  have hlo : ‖z‖ ^ m - 1 ≤ ‖z ^ m - 1‖ := by
    simpa only [norm_pow, norm_one] using norm_sub_norm_le (z ^ m) (1 : ℂ)
  have hhi : ‖z ^ q - 1‖ ≤ ‖z‖ ^ q + 1 := by
    simpa only [norm_pow, norm_one] using norm_sub_le (z ^ q) (1 : ℂ)
  have hbound : ‖z‖ ^ m - 1 ≤ ‖v‖ * (‖z‖ ^ q + 1) := by
    calc
      ‖z‖ ^ m - 1 ≤ ‖z ^ m - 1‖ := hlo
      _ = ‖v‖ * ‖z ^ q - 1‖ := hprod.symm
      _ ≤ ‖v‖ * (‖z‖ ^ q + 1) := mul_le_mul_of_nonneg_left hhi (norm_nonneg v)
  exact three_eighths_quotient_scalar hfour hy (norm_nonneg v)
    (by rw [hm, pow_add]) hbound

theorem norm_cyclotomic_prime_power_gt_three_eighths
    {p : ℕ} (hp : p.Prime) (k : ℕ) {z : ℂ}
    (hz : 1 < ‖z‖) (hfour : 4 < ‖z‖ ^ (p ^ (k + 1))) :
    (3 / 8 : ℝ) * ‖z‖ ^ (p ^ k * (p - 1)) <
      ‖(Polynomial.cyclotomic (p ^ (k + 1)) ℂ).eval z‖ := by
  have hm : p ^ (k + 1) = p ^ k * (p - 1) + p ^ k := by
    rw [pow_succ]
    have hh := congrArg (fun q : ℕ => p ^ k * q) (Nat.sub_add_cancel hp.one_le)
    simpa only [Nat.mul_add, Nat.mul_one] using hh.symm
  exact norm_gt_three_eighths_of_power_quotient hz (pow_pos hp.pos k) hfour hm
    (cyclotomic_prime_power_eval_identity hp k z)

end EventualIrreducibility.UniversalConstants

namespace EventualIrreducibility.UniversalPrimePowerLocal

open Polynomial

lemma nonarch_sum_le_const {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hna : IsNonarchimedean v)
    {ι : Type*} (s : Finset ι) (u : ι → K) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ i ∈ s, v (u i) ≤ B) : v (∑ i ∈ s, u i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hna _ _).trans (max_le (hu a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))))

lemma min_leading_of_mul
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (hna : IsNonarchimedean v)
    (A B : E[X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hmin : IsMinGaussIndex (A * B) v 1 (A * B).natDegree) :
    IsMinGaussIndex A v 1 A.natDegree ∧ IsMinGaussIndex B v 1 B.natDegree := by
  obtain ⟨i, hi⟩ := A.exists_min_eq_gaussNorm v (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨j, hj⟩ := B.exists_min_eq_gaussNorm v (by norm_num : (0 : ℝ) ≤ 1)
  change IsMinGaussIndex A v 1 i at hi
  change IsMinGaussIndex B v 1 j at hj
  have hsum := assembly_min_unique (A * B) 1 (i + j) (A * B).natDegree
    (minGaussIndex_mul hna (by norm_num) A B hA hB i j hi hj) hmin
  have hi_le := UniversalSlopeDraft.gauss_attainer_le_degree A hA (by norm_num) i hi.1
  have hj_le := UniversalSlopeDraft.gauss_attainer_le_degree B hB (by norm_num) j hj.1
  rw [Polynomial.natDegree_mul hA hB] at hsum
  have hi_eq : i = A.natDegree := by omega
  have hj_eq : j = B.natDegree := by omega
  exact ⟨by simpa only [hi_eq] using hi, by simpa only [hj_eq] using hj⟩

lemma discrete_lt_one_le_exp_neg_one
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    {x : E} (hx : v x < 1) : v x ≤ Real.exp (-1) := by
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero]
    exact (Real.exp_pos _).le
  obtain ⟨z, hz⟩ := hdiscrete x hx0
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    rw [hz, ← Real.exp_zero] at hx
    have := Real.exp_lt_exp.mp hx
    linarith
  have hzposZ : 0 < z := by exact_mod_cast hzpos
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  rw [hz]
  exact Real.exp_le_exp.mpr (by linarith)

lemma lower_coeff_le_exp_neg_one_of_leading_min
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (P : E[X]) (hP : P.Monic)
    (hmin : IsMinGaussIndex P v 1 P.natDegree) :
    ∀ j < P.natDegree, v (P.coeff j) ≤ Real.exp (-1) := by
  have hnorm : P.gaussNorm v 1 = 1 := by
    simpa only [hP.coeff_natDegree, map_one, one_pow, mul_one] using hmin.1
  intro j hj
  have hlt := hmin.2 j hj
  simp only [one_pow, mul_one, hnorm] at hlt
  exact discrete_lt_one_le_exp_neg_one v hdiscrete hlt

lemma monic_eval_eq_leading_add_tail
    {K : Type*} [Field K] (P : K[X]) (hP : P.Monic) (beta : K) :
    P.eval beta = beta ^ P.natDegree +
      ∑ j ∈ P.support.erase P.natDegree, P.coeff j * beta ^ j := by
  classical
  have hdmem : P.natDegree ∈ P.support := by
    rw [Polynomial.mem_support_iff, hP.coeff_natDegree]
    exact one_ne_zero
  rw [Polynomial.eval_eq_sum, Polynomial.sum,
    ← Finset.add_sum_erase _ _ hdmem, hP.coeff_natDegree, one_mul]

theorem root_power_le_of_small_lower_coefficients
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hna : IsNonarchimedean v)
    (P : K[X]) (hP : P.Monic) (beta : K) (hroot : P.eval beta = 0)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hcoeff : ∀ j < P.natDegree, v (P.coeff j) ≤ c) :
    v beta < 1 ∧ v beta ^ P.natDegree ≤ c := by
  classical
  have hdmem : P.natDegree ∈ P.support := by
    rw [Polynomial.mem_support_iff, hP.coeff_natDegree]
    exact one_ne_zero
  have hbeta : v beta < 1 := by
    by_contra hnot
    have hb1 : 1 ≤ v beta := le_of_not_gt hnot
    have hb0 : 0 < v beta := lt_of_lt_of_le zero_lt_one hb1
    have hdom := IsNonarchimedean.apply_sum_eq_of_lt hna
      (fun x => by simp) (l := fun j => P.coeff j * beta ^ j) hdmem
      (by
        intro j hj hjne
        have hjle : j ≤ P.natDegree :=
          Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
        have hjlt : j < P.natDegree := by omega
        rw [map_mul, map_pow, hP.coeff_natDegree, one_mul, map_pow]
        calc
          v (P.coeff j) * v beta ^ j < 1 * v beta ^ j :=
            mul_lt_mul_of_pos_right (lt_of_le_of_lt (hcoeff j hjlt) hc1) (pow_pos hb0 _)
          _ ≤ v beta ^ P.natDegree := by
            simpa only [one_mul] using pow_le_pow_right₀ hb1 hjle)
    have heval : v (P.eval beta) = v beta ^ P.natDegree := by
      simpa only [Polynomial.eval_eq_sum, Polynomial.sum, map_mul, map_pow,
        hP.coeff_natDegree, map_one, one_mul] using hdom
    rw [hroot, map_zero] at heval
    linarith [pow_pos hb0 P.natDegree]
  have htail : v (∑ j ∈ P.support.erase P.natDegree, P.coeff j * beta ^ j) ≤ c := by
    apply nonarch_sum_le_const v hna _ _ hc0.le
    intro j hj
    have hjmem := (Finset.mem_erase.mp hj).2
    have hjne := (Finset.mem_erase.mp hj).1
    have hjle : j ≤ P.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hjmem)
    have hjlt : j < P.natDegree := by omega
    rw [map_mul, map_pow]
    calc
      v (P.coeff j) * v beta ^ j ≤ c * 1 :=
        mul_le_mul (hcoeff j hjlt) (pow_le_one₀ (v.nonneg beta) hbeta.le)
          (pow_nonneg (v.nonneg beta) _) hc0.le
      _ = c := mul_one _
  have heq : beta ^ P.natDegree =
      -(∑ j ∈ P.support.erase P.natDegree, P.coeff j * beta ^ j) := by
    have he := monic_eval_eq_leading_add_tail P hP beta
    rw [hroot] at he
    exact eq_neg_of_add_eq_zero_left he.symm
  have hv := congrArg v heq
  simp only [map_pow, AbsoluteValue.map_neg] at hv
  exact ⟨hbeta, hv.trans_le htail⟩

theorem eisenstein_eval_norm_at_small_root
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hna : IsNonarchimedean v)
    (Q : K[X]) (hQ : Q.Monic) (beta : K) {d : ℕ} {c : ℝ}
    (hc0 : 0 < c) (_hc1 : c < 1) (hd : d < Q.natDegree)
    (hb : v beta < 1) (hpow : v beta ^ d ≤ c)
    (hzero : v (Q.coeff 0) = c)
    (hcoeff : ∀ j < Q.natDegree, v (Q.coeff j) ≤ c) :
    v (Q.eval beta) = c := by
  classical
  have h0mem : 0 ∈ Q.support := by
    rw [Polynomial.mem_support_iff]
    intro hz
    simp only [hz, map_zero] at hzero
    linarith
  have hdom := IsNonarchimedean.apply_sum_eq_of_lt hna
    (fun x => by simp) (l := fun j => Q.coeff j * beta ^ j) h0mem
    (by
      intro j hj hj0
      have hjpos : 0 < j := by omega
      have hjle : j ≤ Q.natDegree :=
        Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
      simp only [pow_zero, mul_one, hzero]
      rw [map_mul, map_pow]
      rcases lt_or_eq_of_le hjle with hjlt | rfl
      · have hpj : v beta ^ j < 1 := pow_lt_one₀ (v.nonneg beta) hb (by omega)
        calc
          v (Q.coeff j) * v beta ^ j ≤ c * v beta ^ j :=
            mul_le_mul_of_nonneg_right (hcoeff j hjlt) (pow_nonneg (v.nonneg beta) _)
          _ < c * 1 := mul_lt_mul_of_pos_left hpj hc0
          _ = c := mul_one _
      · rw [hQ.coeff_natDegree, map_one, one_mul]
        by_cases hb0 : v beta = 0
        · simp only [hb0, zero_pow (by omega : Q.natDegree ≠ 0)]
          exact hc0
        · have hbpos : 0 < v beta := lt_of_le_of_ne (v.nonneg beta) (Ne.symm hb0)
          have hdif : Q.natDegree - d ≠ 0 := by omega
          calc
            v beta ^ Q.natDegree = v beta ^ d * v beta ^ (Q.natDegree - d) := by
              rw [← pow_add, Nat.add_sub_of_le hd.le]
            _ < v beta ^ d * 1 := mul_lt_mul_of_pos_left
              (pow_lt_one₀ (v.nonneg beta) hb hdif) (pow_pos hbpos d)
            _ ≤ c := by simpa only [mul_one] using hpow)
  simpa only [Polynomial.eval_eq_sum, Polynomial.sum, pow_zero, mul_one, hzero] using hdom

end EventualIrreducibility.UniversalPrimePowerLocal

namespace EventualIrreducibility.UniversalPrimePowerLocal

open Polynomial

noncomputable def shiftedCyclotomic (p k : ℕ) : ℤ[X] :=
  (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).comp (X + C 1)

lemma shiftedCyclotomic_monic (p k : ℕ) : (shiftedCyclotomic p k).Monic :=
  (Polynomial.cyclotomic.monic _ _).comp_X_add_C 1

lemma shiftedCyclotomic_mod_prime (p k : ℕ) (hp : p.Prime) :
    (shiftedCyclotomic p k).map (Int.castRingHom (ZMod p)) =
      X ^ (p ^ (k + 1) - p ^ k) := by
  let : Fact p.Prime := ⟨hp⟩
  have hcycl : Polynomial.cyclotomic (p ^ (k + 1)) (ZMod p) =
      (X - 1) ^ (p ^ (k + 1) - p ^ k) := by
    have h := Polynomial.cyclotomic_mul_prime_pow_eq (ZMod p) (m := 1)
      (show ¬ p ∣ 1 by simpa using hp.not_dvd_one) (k := k + 1) (by omega)
    simpa using h
  simp only [shiftedCyclotomic, Polynomial.map_comp, Polynomial.map_cyclotomic_int,
    Polynomial.map_add, Polynomial.map_X, map_one, hcycl]
  simp

lemma shiftedCyclotomic_degree (p k : ℕ) (hp : p.Prime) :
    (shiftedCyclotomic p k).natDegree = p ^ (k + 1) - p ^ k := by
  let : Fact p.Prime := ⟨hp⟩
  rw [← (shiftedCyclotomic_monic p k).natDegree_map (Int.castRingHom (ZMod p)),
    shiftedCyclotomic_mod_prime p k hp, Polynomial.natDegree_X_pow]

lemma shiftedCyclotomic_coeff_zero (p k : ℕ) (hp : p.Prime) :
    (shiftedCyclotomic p k).coeff 0 = (p : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [shiftedCyclotomic, Polynomial.eval_one_cyclotomic_prime_pow]

lemma prime_dvd_shiftedCyclotomic_lower_coeff (p k j : ℕ) (hp : p.Prime)
    (hj : j < p ^ (k + 1) - p ^ k) :
    (p : ℤ) ∣ (shiftedCyclotomic p k).coeff j := by
  have hc := congrArg (fun P : (ZMod p)[X] => P.coeff j)
    (shiftedCyclotomic_mod_prime p k hp)
  have hz : ((shiftedCyclotomic p k).coeff j : ZMod p) = 0 := by
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom,
      Polynomial.coeff_X_pow, if_neg (by omega : j ≠ p ^ (k + 1) - p ^ k)] using hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz

lemma normalized_nat_norm_le_one
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (p : ℕ)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (t : ℕ) : v (t : E) ≤ 1 := by
  by_cases ht : t = 0
  · simp [ht]
  rw [hnorm t ht, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))

lemma normalized_int_norm_le_one
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (p : ℕ)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (t : ℤ) : v (t : E) ≤ 1 := by
  cases t with
  | ofNat t =>
    change v ((t : ℤ) : E) ≤ 1
    simpa only [Int.cast_natCast] using normalized_nat_norm_le_one v p hnorm t
  | negSucc t => simpa only [Int.cast_negSucc, AbsoluteValue.map_neg,
      Nat.cast_add, Nat.cast_one] using
      normalized_nat_norm_le_one v p hnorm (t + 1)

lemma normalized_int_norm_le_exp_neg_one_of_prime_dvd
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (p : ℕ) (hp : p.Prime)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    {t : ℤ} (hpt : (p : ℤ) ∣ t) : v (t : E) ≤ Real.exp (-1) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, rfl⟩ := hpt
  have hpval : v (p : E) = Real.exp (-1) := by
    simpa using hnorm p hp.ne_zero
  push_cast
  rw [map_mul, hpval]
  exact (mul_le_mul_of_nonneg_left (normalized_int_norm_le_one v p hnorm u)
    (Real.exp_pos _).le).trans_eq (mul_one _)

theorem shiftedCyclotomic_local_coefficients
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (p k : ℕ) (hp : p.Prime)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ))) :
    let Q := (shiftedCyclotomic p k).map (Int.castRingHom E)
    Q.Monic ∧ Q.natDegree = p ^ (k + 1) - p ^ k ∧
      v (Q.coeff 0) = Real.exp (-1) ∧
      ∀ j < Q.natDegree, v (Q.coeff j) ≤ Real.exp (-1) := by
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  refine ⟨(shiftedCyclotomic_monic p k).map _, ?_, ?_, ?_⟩
  · rw [(shiftedCyclotomic_monic p k).natDegree_map, shiftedCyclotomic_degree p k hp]
  · rw [Polynomial.coeff_map, shiftedCyclotomic_coeff_zero p k hp]
    simpa using hnorm p hp.ne_zero
  · intro j hj
    rw [(shiftedCyclotomic_monic p k).natDegree_map, shiftedCyclotomic_degree p k hp] at hj
    rw [Polynomial.coeff_map]
    exact normalized_int_norm_le_exp_neg_one_of_prime_dvd v p hp hnorm
      (prime_dvd_shiftedCyclotomic_lower_coeff p k j hp hj)

end EventualIrreducibility.UniversalPrimePowerLocal

namespace EventualIrreducibility.UniversalPrimePowerLocal

open Polynomial UniversalResidueOneProfileDraft UniversalResidueOneFacesDraft

theorem actual_translated_factor_lower_coefficients
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (hna : IsNonarchimedean v)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    {n p : ℕ} (s : FactorSeries n) (hn : 0 < n) (hp : p.Prime) (k : ℕ)
    (hN : n + 1 = p ^ (k + 1))
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ))) :
    let G := (s.factor.map (Int.castRingHom E)).comp (X + C 1)
    ∀ j < G.natDegree, v (G.coeff j) ≤ Real.exp (-1) := by
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  obtain ⟨h, hfactor⟩ := s.divides
  let A : E[X] := (s.factor.map (Int.castRingHom E)).comp (X + C 1)
  let B : E[X] := (h.map (Int.castRingHom E)).comp (X + C 1)
  have hAB : A * B = (oneTranslate n : E[X]) := by
    rw [oneTranslate_eq_comp, hfactor, Polynomial.map_mul, Polynomial.mul_comp]
  have hAnonzero : A ≠ 0 := ((s.monic.map _).comp_X_add_C 1).ne_zero
  have hBnonzero : B ≠ 0 := by
    intro hz
    have hzero : (oneTranslate n : E[X]) = 0 := by rw [← hAB, hz, mul_zero]
    exact (oneTranslate_monic n hn).ne_zero hzero
  have hval : padicValNat p (n + 1) = k + 1 := by
    rw [hN, padicValNat.prime_pow]
  have hmin := (actual_residue_one_faces n p (k + 1) hn hp (by omega)
    hnorm (Or.inr hval)).2.2
  have hfull : IsMinGaussIndex (A * B) v 1 (A * B).natDegree := by
    rw [hAB, oneTranslate_natDegree n hn]
    have he : p ^ (k + 1) - 2 = n - 1 := by omega
    simpa only [he] using hmin
  have hAmin := (min_leading_of_mul v hna A B hAnonzero hBnonzero hfull).1
  exact lower_coeff_le_exp_neg_one_of_leading_min v hdiscrete A
    ((s.monic.map _).comp_X_add_C 1) hAmin

theorem actual_factor_cyclotomic_eval_norm
    {E K : Type*} [Field E] [Field K]
    (v : AbsoluteValue E ℝ) (w : AbsoluteValue K ℝ)
    (hvna : IsNonarchimedean v) (hwna : IsNonarchimedean w)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (i : E →+* K) (hrestrict : ∀ x : E, w (i x) = v x)
    {n p : ℕ} (s : FactorSeries n) (hn : 0 < n) (hp : p.Prime) (k : ℕ)
    (hN : n + 1 = p ^ (k + 1))
    (hd : s.factor.natDegree < p ^ (k + 1) - p ^ k)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (alpha : K)
    (hroot : ((s.factor.map (Int.castRingHom E)).map i).eval alpha = 0) :
    w ((((Polynomial.cyclotomic (p ^ (k + 1)) ℤ).map (Int.castRingHom E)).map i).eval alpha) =
      Real.exp (-1) := by
  let A : E[X] := (s.factor.map (Int.castRingHom E)).comp (X + C 1)
  let Q : E[X] := (shiftedCyclotomic p k).map (Int.castRingHom E)
  have hA : A.Monic := (s.monic.map _).comp_X_add_C 1
  have hAd : A.natDegree = s.factor.natDegree := by
    dsimp only [A]
    simp only [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C,
      Nat.mul_one, s.monic.natDegree_map]
  have hAdK : (A.map i).natDegree = s.factor.natDegree :=
    (hA.natDegree_map i).trans hAd
  have hbeta : (A.map i).eval (alpha - 1) = 0 := by
    simpa only [A, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_one, map_one, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, sub_add_cancel] using hroot
  have hcoeffA : ∀ j < (A.map i).natDegree,
      w ((A.map i).coeff j) ≤ Real.exp (-1) := by
    intro j hj
    rw [Polynomial.coeff_map, hrestrict]
    apply actual_translated_factor_lower_coefficients v hvna hdiscrete s hn hp k hN hnorm j
    simpa only [hA.natDegree_map] using hj
  obtain ⟨hb, hpow⟩ := root_power_le_of_small_lower_coefficients w hwna
    (A.map i) (hA.map i) (alpha - 1) hbeta
    (Real.exp_pos _) (by simp) hcoeffA
  rw [hAdK] at hpow
  obtain ⟨hQ, hQd, hQzero, hQcoeff⟩ := shiftedCyclotomic_local_coefficients v p k hp hnorm
  change Q.Monic at hQ
  change Q.natDegree = _ at hQd
  change v (Q.coeff 0) = Real.exp (-1) at hQzero
  change ∀ j < Q.natDegree, v (Q.coeff j) ≤ Real.exp (-1) at hQcoeff
  have hQdK : (Q.map i).natDegree = p ^ (k + 1) - p ^ k :=
    (hQ.natDegree_map i).trans hQd
  have heval := eisenstein_eval_norm_at_small_root w hwna (Q.map i) (hQ.map i) (alpha - 1)
    (Real.exp_pos _) (by simp)
    (show s.factor.natDegree < (Q.map i).natDegree by simpa only [hQdK] using hd)
    hb hpow
    (by simpa only [Polynomial.coeff_map, hrestrict] using hQzero)
    (by
      intro j hj
      rw [Polynomial.coeff_map, hrestrict]
      apply hQcoeff
      simpa only [hQ.natDegree_map] using hj)
  simpa only [Q, shiftedCyclotomic, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_one, map_one, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    sub_add_cancel] using heval

end EventualIrreducibility.UniversalPrimePowerLocal

namespace EventualIrreducibility.UniversalPrimePowerLocal

open Polynomial UniversalSlopeDraft

lemma absolute_multiset_prod_eq_const
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (S : Multiset K) (c : ℝ)
    (h : ∀ x ∈ S, v x = c) : v S.prod = c ^ S.card := by
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons a S ih =>
    rw [Multiset.prod_cons, map_mul, h a (Multiset.mem_cons_self _ _),
      ih (fun x hx => h x (Multiset.mem_cons_of_mem hx)), Multiset.card_cons, pow_succ]
    ring

lemma resultant_norm_eq_of_root_evaluations
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (P Q : K[X]) (hP : P.Monic) (hs : P.Splits) (c : ℝ)
    (heval : ∀ alpha : K, P.eval alpha = 0 → v (Q.eval alpha) = c) :
    v (P.resultant Q P.natDegree Q.natDegree) = c ^ P.natDegree := by
  rw [Polynomial.resultant_eq_prod_eval P Q Q.natDegree le_rfl hs,
    hP.leadingCoeff, one_pow, one_mul]
  have hprod := absolute_multiset_prod_eq_const v (P.roots.map Q.eval) c
    (by
      intro y hy
      obtain ⟨alpha, halpha, rfl⟩ := Multiset.mem_map.mp hy
      exact heval alpha ((Polynomial.mem_roots hP.ne_zero).mp halpha))
  simpa only [Multiset.card_map, ← hs.natDegree_eq_card_roots] using hprod

theorem actual_prime_power_resultant_norm
    {E : Type*} [NormedField E] [CompleteSpace E]
    (v : AbsoluteValue E ℝ) (hvna : IsNonarchimedean v)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    {n p : ℕ} (s : FactorSeries n) (hn : 0 < n) (hp : p.Prime) (k : ℕ)
    (hN : n + 1 = p ^ (k + 1))
    (hd : s.factor.natDegree < p ^ (k + 1) - p ^ k)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (S : ValuedSplittingData E v (s.factor.map (Int.castRingHom E))) :
    v ((s.factor.resultant (Polynomial.cyclotomic (p ^ (k + 1)) ℤ)
      s.factor.natDegree (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree : ℤ) : E) =
      (Real.exp (-1)) ^ s.factor.natDegree := by
  let P : E[X] := s.factor.map (Int.castRingHom E)
  let Q : E[X] := (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).map (Int.castRingHom E)
  let i : E →+* S.K := algebraMap E S.K
  have hP : P.Monic := s.monic.map _
  have hQ : Q.Monic := (Polynomial.cyclotomic.monic _ _).map _
  have hlocal := resultant_norm_eq_of_root_evaluations S.w (P.map i) (Q.map i)
    (hP.map i) S.splits (Real.exp (-1))
    (fun alpha hroot => actual_factor_cyclotomic_eval_norm v S.w hvna S.nonarchimedean
      hdiscrete i S.restrict s hn hp k hN hd hnorm alpha hroot)
  rw [hP.natDegree_map, hQ.natDegree_map, Polynomial.resultant_map_map, S.restrict] at hlocal
  have hPdeg : P.natDegree = s.factor.natDegree := s.monic.natDegree_map _
  have hQdeg : Q.natDegree = (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree :=
    (Polynomial.cyclotomic.monic _ _).natDegree_map _
  rw [hPdeg, hQdeg] at hlocal
  simpa only [P, Q, Polynomial.resultant_map_map, Int.coe_castRingHom] using hlocal

theorem exists_actual_prime_power_resultant_norm
    (hU : StandardUnramifiedInput) (hS : StandardValuedSplittingInput.{0})
    {n p : ℕ} (s : FactorSeries n) (hn : 0 < n) (hp : p.Prime) (k : ℕ)
    (hN : n + 1 = p ^ (k + 1))
    (hd : s.factor.natDegree < p ^ (k + 1) - p ^ k) :
    ∃ D : PrimeToPUnramifiedData p 1,
      D.v ((s.factor.resultant (Polynomial.cyclotomic (p ^ (k + 1)) ℤ)
        s.factor.natDegree (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree : ℤ) : D.E) =
        (Real.exp (-1)) ^ s.factor.natDegree := by
  obtain ⟨D⟩ := hU p 1 hp (by norm_num) (by simpa using hp.not_dvd_one)
  obtain ⟨S⟩ := hS D.E D.v D.nonarchimedean D.norm_eq
    (s.factor.map (Int.castRingHom D.E)) (s.monic.map _).ne_zero
  exact ⟨D, actual_prime_power_resultant_norm D.v D.nonarchimedean D.discrete
    s hn hp k hN hd D.nat_norm S⟩

end EventualIrreducibility.UniversalPrimePowerLocal

namespace EventualIrreducibility.UniversalPrimePowerLocal

open Polynomial

lemma eval_one_mul_resultant_eq_power
    {K : Type*} [Field K] (P Q : K[X]) (hP : P.Monic) (hs : P.Splits) (N : K)
    (hroot : ∀ alpha : K, P.eval alpha = 0 → (1 - alpha) * Q.eval alpha = N) :
    P.eval 1 * P.resultant Q P.natDegree Q.natDegree = N ^ P.natDegree := by
  rw [hs.eval_eq_prod_roots_of_monic hP,
    Polynomial.resultant_eq_prod_eval P Q Q.natDegree le_rfl hs,
    hP.leadingCoeff, one_pow, one_mul, ← Multiset.prod_map_mul]
  have hm : (P.roots.map (fun alpha => (1 - alpha) * Q.eval alpha)) =
      P.roots.map (fun _ => N) := by
    apply Multiset.map_congr rfl
    intro alpha halpha
    exact hroot alpha ((Polynomial.mem_roots hP.ne_zero).mp halpha)
  rw [hm]
  simp only [Multiset.map_const', Multiset.prod_replicate, ← hs.natDegree_eq_card_roots]

lemma actual_cyclotomic_root_identity
    {n p : ℕ} (hp : p.Prime) (k : ℕ) (hN : n + 1 = p ^ (k + 1))
    (alpha : ℂ)
    (hroot : (Polynomial.cyclotomic (p ^ (k + 1)) ℂ).eval alpha = 0) :
    (1 - alpha) * ((fInt n).map (Int.castRingHom ℂ)).eval alpha = ((n : ℂ) + 1) := by
  have hpow : alpha ^ (n + 1) = 1 := by
    have he := UniversalConstants.cyclotomic_prime_power_eval_identity hp k alpha
    rw [hroot, zero_mul] at he
    rw [hN]
    exact sub_eq_zero.mp he.symm
  have hne : alpha ≠ 1 := by
    intro h
    rw [h, UniversalConstants.cyclotomic_prime_power_eval_one hp k] at hroot
    have hpzero : p = 0 := by exact_mod_cast hroot
    exact hp.ne_zero hpzero
  have ht := congrArg
    (fun P : ℤ[X] => (P.map (Int.castRingHom ℂ)).eval alpha) (trinomial_identity n)
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C,
    Int.coe_castRingHom, Int.cast_natCast, Int.cast_add, Int.cast_one,
    Nat.cast_add, Nat.cast_one] at ht
  apply mul_left_cancel₀ (sub_ne_zero.mpr hne.symm)
  calc
    (1 - alpha) * ((1 - alpha) * ((fInt n).map (Int.castRingHom ℂ)).eval alpha) =
        (alpha - 1) ^ 2 * ((fInt n).map (Int.castRingHom ℂ)).eval alpha := by ring
    _ = alpha ^ (n + 1) - ((n : ℂ) + 1) * alpha + (n : ℂ) := ht
    _ = (1 - alpha) * ((n : ℂ) + 1) := by rw [hpow]; ring

theorem prime_power_total_resultant
    {n p : ℕ} (hp : p.Prime) (k : ℕ) (hN : n + 1 = p ^ (k + 1)) :
    (p : ℤ) * (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).resultant (fInt n)
      (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree (fInt n).natDegree =
        ((n + 1 : ℕ) : ℤ) ^ (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree := by
  let P : ℤ[X] := Polynomial.cyclotomic (p ^ (k + 1)) ℤ
  let PC : ℂ[X] := P.map (Int.castRingHom ℂ)
  let FC : ℂ[X] := (fInt n).map (Int.castRingHom ℂ)
  have hP : P.Monic := Polynomial.cyclotomic.monic _ _
  have hPC : PC = Polynomial.cyclotomic (p ^ (k + 1)) ℂ := by
    simp only [PC, P, Polynomial.map_cyclotomic_int]
  have hpoint : PC.eval 1 = (p : ℂ) := by
    rw [hPC]
    exact UniversalConstants.cyclotomic_prime_power_eval_one hp k
  have hres := eval_one_mul_resultant_eq_power PC FC (hP.map _) (IsAlgClosed.splits PC)
    ((n : ℂ) + 1)
    (by intro alpha ha; exact actual_cyclotomic_root_identity hp k hN alpha (hPC ▸ ha))
  rw [hpoint, hP.natDegree_map] at hres
  have hFdeg : FC.natDegree = (fInt n).natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective) (fInt n)
  rw [hFdeg] at hres
  simp only [PC, FC, Polynomial.resultant_map_map, Int.coe_castRingHom] at hres
  exact_mod_cast hres

lemma natAbs_resultant_comm (P Q : ℤ[X]) :
    (P.resultant Q P.natDegree Q.natDegree).natAbs =
      (Q.resultant P Q.natDegree P.natDegree).natAbs := by
  have h := congrArg Int.natAbs (Polynomial.resultant_comm P Q P.natDegree Q.natDegree)
  simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
    one_pow, one_mul] using h

theorem prime_power_total_resultant_natAbs
    {n p : ℕ} (hp : p.Prime) (k : ℕ) (hN : n + 1 = p ^ (k + 1)) :
    p * ((fInt n).resultant (Polynomial.cyclotomic (p ^ (k + 1)) ℤ)
      (fInt n).natDegree (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree).natAbs =
        (n + 1) ^ (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree := by
  have h := congrArg Int.natAbs (prime_power_total_resultant hp k hN)
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow] at h
  rw [natAbs_resultant_comm] at h
  exact h

end EventualIrreducibility.UniversalPrimePowerLocal

namespace EventualIrreducibility.UniversalPrimePowerLocal

open Polynomial UniversalSlopeDraft

lemma natAbs_resultant_dvd_of_monic_dvd
    (P F Q : ℤ[X]) (hP : P.Monic) (hF : F ≠ 0) (hdiv : P ∣ F) :
    (P.resultant Q P.natDegree Q.natDegree).natAbs ∣
      (F.resultant Q F.natDegree Q.natDegree).natAbs := by
  obtain ⟨H, hFH⟩ := hdiv
  have hH : H ≠ 0 := by
    intro hz
    apply hF
    simpa only [hz, mul_zero] using hFH
  have hres : F.resultant Q F.natDegree Q.natDegree =
      P.resultant Q P.natDegree Q.natDegree *
        H.resultant Q H.natDegree Q.natDegree := by
    rw [hFH, Polynomial.natDegree_mul hP.ne_zero hH]
    exact Polynomial.resultant_mul_left P H Q Q.natDegree le_rfl
  refine ⟨(H.resultant Q H.natDegree Q.natDegree).natAbs, ?_⟩
  rw [← Int.natAbs_mul, ← hres]

theorem actual_factor_resultant_dvd_prime_power
    {n p : ℕ} (s : FactorSeries n) (hp : p.Prime) (k : ℕ)
    (hN : n + 1 = p ^ (k + 1)) :
    (s.factor.resultant (Polynomial.cyclotomic (p ^ (k + 1)) ℤ)
      s.factor.natDegree (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree).natAbs ∣
        p ^ ((k + 1) * (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree) := by
  let Q : ℤ[X] := Polynomial.cyclotomic (p ^ (k + 1)) ℤ
  have hf : fInt n ≠ 0 := by
    intro hz
    have hd := s.degree_lt
    rw [hz, Polynomial.natDegree_zero] at hd
    omega
  have hdiv := natAbs_resultant_dvd_of_monic_dvd s.factor (fInt n) Q
    s.monic hf s.divides
  have htotal := prime_power_total_resultant_natAbs hp k hN
  have htotaldiv : ((fInt n).resultant Q (fInt n).natDegree Q.natDegree).natAbs ∣
      p ^ ((k + 1) * Q.natDegree) := by
    refine ⟨p, ?_⟩
    rw [pow_mul, ← hN]
    simpa only [Q, Nat.mul_comm] using htotal.symm
  exact hdiv.trans htotaldiv

lemma absolute_int_natAbs
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (z : ℤ) :
    v (z.natAbs : E) = v (z : E) := by
  cases z with
  | ofNat a =>
    change v ((a : ℕ) : E) = v ((a : ℤ) : E)
    simp only [Int.cast_natCast]
  | negSucc a => simp only [Int.natAbs_negSucc, Int.cast_negSucc, AbsoluteValue.map_neg,
      Nat.cast_succ]

lemma natAbs_eq_prime_power_of_divisibility_and_value
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ)
    {p : ℕ} (hp : p.Prime)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (z : ℤ) (d B : ℕ) (hdiv : z.natAbs ∣ p ^ B)
    (hv : v (z : E) = (Real.exp (-1)) ^ d) :
    z.natAbs = p ^ d := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, heB, he⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  have hv' : v ((p ^ e : ℕ) : E) = (Real.exp (-1)) ^ d := by
    rw [← he]
    exact (absolute_int_natAbs v z).trans hv
  have hnorm' := hnorm (p ^ e) (pow_ne_zero _ hp.ne_zero)
  rw [padicValNat.prime_pow] at hnorm'
  have heq : Real.exp (-(e : ℝ)) = Real.exp (-(d : ℝ)) := by
    calc
      Real.exp (-(e : ℝ)) = v ((p ^ e : ℕ) : E) := hnorm'.symm
      _ = (Real.exp (-1)) ^ d := hv'
      _ = Real.exp (-(d : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hed : e = d := by
    have hreal := Real.exp_injective heq
    have : (e : ℝ) = (d : ℝ) := by linarith
    exact_mod_cast this
  simpa only [hed] using he

theorem actual_prime_power_resultant_natAbs
    (hU : StandardUnramifiedInput) (hS : StandardValuedSplittingInput.{0})
    {n p : ℕ} (s : FactorSeries n) (hn : 0 < n) (hp : p.Prime) (k : ℕ)
    (hN : n + 1 = p ^ (k + 1))
    (hd : s.factor.natDegree < p ^ (k + 1) - p ^ k) :
    (s.factor.resultant (Polynomial.cyclotomic (p ^ (k + 1)) ℤ)
      s.factor.natDegree (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree).natAbs =
        p ^ s.factor.natDegree := by
  obtain ⟨D, hvalue⟩ := exists_actual_prime_power_resultant_norm hU hS
    s hn hp k hN hd
  exact natAbs_eq_prime_power_of_divisibility_and_value D.v hp D.nat_norm _ _ _
    (actual_factor_resultant_dvd_prime_power s hp k hN) hvalue

end EventualIrreducibility.UniversalPrimePowerLocal

open scoped BigOperators

namespace UniversalScalar

noncomputable def repeatedPrimeWeight (p : ℕ) : ℝ :=
  (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) ^ 2 - 1)

noncomputable def repeatedPrimeSum (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, repeatedPrimeWeight p

noncomputable def primeSplitCorrection : ℝ :=
  (17 / 30) * Real.log 2 + (11 / 40) * Real.log 3 +
    (13 / 120) * Real.log 5 + (11 / 240) * Real.log 7

lemma primeSplitCorrection_lt : primeSplitCorrection < 97 / 100 := by
  unfold primeSplitCorrection
  have h2 : Real.log (2 : ℝ) < 7 / 10 := by
    linarith [log_two_rational_bounds.2]
  nlinarith [h2, log_three_lt, log_five_lt, log_seven_lt]

lemma prime_ge_eleven_of_not_small {p : ℕ} (hp : p.Prime)
    (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) (h7 : p ≠ 7) :
    11 ≤ p := by
  by_contra h
  have hlt : p < 11 := by omega
  interval_cases p <;> norm_num at *

lemma repeatedPrimeWeight_large {p : ℕ} (hp : 11 ≤ p) :
    repeatedPrimeWeight p ≤ Real.log (p : ℝ) / 10 := by
  have hpr : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hrat : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 1 / 10 := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg ((p : ℝ) - 11)]
  have hmul := mul_le_mul_of_nonneg_right hrat hlog
  simpa only [repeatedPrimeWeight, div_mul_eq_mul_div, one_mul] using hmul

lemma repeatedPrimeWeight_split {p : ℕ} (hp : p.Prime) :
    repeatedPrimeWeight p ≤ Real.log (p : ℝ) / 10 +
      (if p = 2 then (17 / 30) * Real.log 2 else 0) +
      (if p = 3 then (11 / 40) * Real.log 3 else 0) +
      (if p = 5 then (13 / 120) * Real.log 5 else 0) +
      (if p = 7 then (11 / 240) * Real.log 7 else 0) := by
  by_cases h2 : p = 2
  · subst p
    norm_num [repeatedPrimeWeight] ; ring_nf ; simp
  by_cases h3 : p = 3
  · subst p
    norm_num [repeatedPrimeWeight] ; ring_nf ; simp
  by_cases h5 : p = 5
  · subst p
    norm_num [repeatedPrimeWeight] ; ring_nf ; simp
  by_cases h7 : p = 7
  · subst p
    norm_num [repeatedPrimeWeight] ; ring_nf ; simp
  simpa only [if_neg h2, if_neg h3, if_neg h5, if_neg h7, add_zero] using
    repeatedPrimeWeight_large (prime_ge_eleven_of_not_small hp h2 h3 h5 h7)

lemma sum_single_indicator_le (P : Finset ℕ) (q : ℕ) {c : ℝ}
    (hc : 0 ≤ c) : (∑ p ∈ P, if p = q then c else 0) ≤ c := by
  classical
  by_cases hq : q ∈ P <;> simp [hq, hc]

theorem repeatedPrimeSum_le_log_product (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    repeatedPrimeSum P <
      Real.log (∏ p ∈ P, (p : ℝ)) / 10 + 97 / 100 := by
  classical
  have hsum := Finset.sum_le_sum (fun p hp => repeatedPrimeWeight_split (hP p hp))
  have h2 := sum_single_indicator_le P 2
    (c := (17 / 30) * Real.log 2) (by positivity)
  have h3 := sum_single_indicator_le P 3
    (c := (11 / 40) * Real.log 3) (by positivity)
  have h5 := sum_single_indicator_le P 5
    (c := (13 / 120) * Real.log 5) (by positivity)
  have h7 := sum_single_indicator_le P 7
    (c := (11 / 240) * Real.log 7) (by positivity)
  simp only [Finset.sum_add_distrib] at hsum
  rw [← Finset.sum_div] at hsum
  have hlog := log_finite_positive_product P (fun p : ℕ => (p : ℝ))
    (fun p hp => by exact_mod_cast (hP p hp).pos)
  unfold repeatedPrimeSum
  rw [hlog]
  have hC := primeSplitCorrection_lt
  unfold primeSplitCorrection at hC
  linarith

lemma repeatedPrimeSum_log_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Q : ℝ}
    (hQ : (∏ p ∈ P, (p : ℝ)) = Q) :
    repeatedPrimeSum P < Real.log Q / 10 + 97 / 100 := by
  simpa only [hQ] using repeatedPrimeSum_le_log_product P hP

theorem support_global_log_bound {n Q S : ℝ}
    (hn : 0 < n) (hQpos : 0 < Q)
    (hQ : Q ≤ Real.sqrt (n * (n + 1)))
    (hS : S < Real.log Q / 10 + 97 / 100) :
    S ≤ Real.log n / 10 + 97 / 100 + 1 / (10 * n) := by
  have hp : 0 < n * (n + 1) := by positivity
  have hsqrt : 0 < Real.sqrt (n * (n + 1)) := Real.sqrt_pos.2 hp
  have hl := Real.log_le_log hQpos hQ
  have hsq : 2 * Real.log (Real.sqrt (n * (n + 1))) =
      Real.log (n * (n + 1)) := by
    have he := Real.log_pow (Real.sqrt (n * (n + 1))) 2
    rw [Real.sq_sqrt hp.le] at he
    norm_num at he
    linarith
  have hb := half_log_successive_product_le hn
  have hi : 0 ≤ 1 / (10 * n) := by positivity
  have hid : (1 / (2 * n)) / 10 = (1 / (10 * n)) / 2 := by
    field_simp
  nlinarith

theorem support_factor_log_bound {a Q J K S : ℝ}
    (ha : 1 < a) (hQpos : 0 < Q) (_hJpos : 0 < J) (hKpos : 0 < K)
    (hQ : Q ≤ Real.sqrt a * J)
    (hJ : J ≤ K * a * Real.log a)
    (hS : S < Real.log Q / 10 + 97 / 100) :
    S < 3 * Real.log a / 20 + Real.log (K * Real.log a) / 10 + 97 / 100 := by
  have hapos : 0 < a := by linarith
  have hApos : 0 < Real.log a := Real.log_pos ha
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.2 hapos
  have hmul := mul_le_mul_of_nonneg_left hJ hsqrt.le
  have hQle : Q ≤ Real.sqrt a * (K * a * Real.log a) := le_trans hQ hmul
  have hl := Real.log_le_log hQpos hQle
  have hsqrlog : Real.log (Real.sqrt a) = Real.log a / 2 := by
    have he := Real.log_pow (Real.sqrt a) 2
    rw [Real.sq_sqrt hapos.le] at he
    norm_num at he
    linarith
  have hprod : Real.sqrt a * (K * a * Real.log a) =
      Real.sqrt a * a * (K * Real.log a) := by ring
  rw [hprod, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (ne_of_gt hsqrt) (ne_of_gt hapos), hsqrlog] at hl
  linarith

theorem support_resultant_closure_inputs {n a Q J K S R : ℝ}
    (hn : 1000 ≤ n) (ha : 1 < a) (hQpos : 0 < Q)
    (hJpos : 0 < J) (hKpos : 0 < K) (hKhi : K < 201 / 100)
    (hQglobal : Q ≤ Real.sqrt (n * (n + 1)))
    (hQfactor : Q ≤ Real.sqrt a * J)
    (hJbound : J ≤ K * a * Real.log a)
    (hS : S < Real.log Q / 10 + 97 / 100)
    (hRvaluation : R ≤ (n + 1) * S) :
    S ≤ Real.log n / 10 + 97 / 100 + 1 / (10 * n) ∧
      S < 3 * Real.log a / 20 + Real.log (K * Real.log a) / 10 + 97 / 100 ∧
      Real.log (K * Real.log a) ≤ 1 + Real.log a / 3 ∧
      R ≤ (n + 1) * S := by
  refine ⟨support_global_log_bound (by linarith) hQpos hQglobal hS,
    support_factor_log_bound ha hQpos hJpos hKpos hQfactor hJbound hS, ?_, hRvaluation⟩
  exact (UniversalIrreducibility.log_support_tangent hKpos (Real.log_pos ha)
    (log_three_K_lt hKpos hKhi)).le

end UniversalScalar

open scoped BigOperators

namespace UniversalScalar

lemma prime_coprime_product_of_not_mem {p : ℕ} (hp : p.Prime)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (hnot : p ∉ P) :
    Nat.Coprime p (∏ q ∈ P, q) := by
  classical
  revert hP hnot
  induction P using Finset.induction_on with
  | empty => simp
  | @insert q P hq ih =>
    intro hP hnot
    have hqp := hP q (Finset.mem_insert_self q P)
    have hpq : p ≠ q := by
      intro heq
      apply hnot
      simp [heq]
    have hP' : ∀ r ∈ P, r.Prime := fun r hr => hP r (Finset.mem_insert_of_mem hr)
    have hnot' : p ∉ P := fun h => hnot (Finset.mem_insert_of_mem h)
    rw [Finset.prod_insert hq]
    exact ((Nat.coprime_primes hp hqp).2 hpq).mul_right (ih hP' hnot')

lemma prime_product_dvd_of_each (P : Finset ℕ) {m : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ∣ m) :
    (∏ p ∈ P, p) ∣ m := by
  classical
  revert hP hdiv
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    intro hP hdiv
    have hpp := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hdiv' : ∀ q ∈ P, q ∣ m := fun q hq => hdiv q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp]
    exact (prime_coprime_product_of_not_mem hpp P hP' hp).mul_dvd_of_dvd_of_dvd
      (hdiv p (Finset.mem_insert_self p P)) (ih hP' hdiv')

lemma prime_product_square_dvd_of_each (P : Finset ℕ) {m : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ^ 2 ∣ m) :
    (∏ p ∈ P, p) ^ 2 ∣ m := by
  classical
  revert hP hdiv
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    intro hP hdiv
    have hpp := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hdiv' : ∀ q ∈ P, q ^ 2 ∣ m := fun q hq => hdiv q (Finset.mem_insert_of_mem hq)
    have hc := prime_coprime_product_of_not_mem hpp P hP' hp
    have hc2 : Nat.Coprime (p ^ 2) ((∏ q ∈ P, q) ^ 2) := by
      simpa only [pow_two] using (hc.mul_right hc).mul_left (hc.mul_right hc)
    rw [Finset.prod_insert hp, mul_pow]
    exact hc2.mul_dvd_of_dvd_of_dvd
      (hdiv p (Finset.mem_insert_self p P)) (ih hP' hdiv')

lemma nat_le_sqrt_of_square_dvd {q m : ℕ} (hm : 0 < m) (hq : q ^ 2 ∣ m) :
    (q : ℝ) ≤ Real.sqrt (m : ℝ) := by
  have hle : q ^ 2 ≤ m := Nat.le_of_dvd hm hq
  have hleR : (q : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hle
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)
  have hnonneg := Real.sqrt_nonneg (m : ℝ)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  nlinarith

lemma prime_square_dvd_left_of_not_right {p a c : ℕ} (hp : p.Prime)
    (hsq : p ^ 2 ∣ a * c) (hnc : ¬ p ∣ c) : p ^ 2 ∣ a := by
  have hpp : p ∣ p ^ 2 := ⟨p, by ring⟩
  have hpa : p ∣ a := (hp.dvd_mul.mp (dvd_trans hpp hsq)).resolve_right hnc
  obtain ⟨u, hu⟩ := hpa
  have hpuc : p ∣ u * c := by
    obtain ⟨v, hv⟩ := hsq
    refine ⟨v, ?_⟩
    apply mul_left_cancel₀ hp.ne_zero
    rw [hu] at hv
    nlinarith only [hv]
  have hpu : p ∣ u := (hp.dvd_mul.mp hpuc).resolve_right hnc
  obtain ⟨v, hv⟩ := hpu
  refine ⟨v, ?_⟩
  rw [hu, hv]
  ring

lemma coprime_prime_not_both {a c p : ℕ} (hac : Nat.Coprime a c)
    (hp : p.Prime) (hpa : p ∣ a) : ¬ p ∣ c := by
  intro hpc
  have hd : p ∣ Nat.gcd a c := Nat.dvd_gcd hpa hpc
  have hg : Nat.gcd a c = 1 := hac
  rw [hg] at hd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hd
  have hp2 := hp.two_le
  omega

lemma product_split_filter (P : Finset ℕ) (pred : ℕ → Prop) [DecidablePred pred] :
    (∏ p ∈ P, p) =
      (∏ p ∈ P.filter pred, p) * (∏ p ∈ P.filter (fun p => ¬ pred p), p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    by_cases hpred : pred p
    · simp [Finset.filter_insert, hpred, hp, ih, mul_assoc]
    · simp [Finset.filter_insert, hpred, hp, ih, mul_left_comm]

theorem repeated_prime_product_factor_bound (P : Finset ℕ)
    {a c J : ℕ} (ha : 0 < a) (hJ : 0 < J) (hac : Nat.Coprime a c)
    (hP : ∀ p ∈ P, p.Prime) (hP2 : ∀ p ∈ P, p ^ 2 ∣ a * c)
    (hJdiv : ∀ p, p.Prime → p ∣ c → p ∣ J) :
    (((∏ p ∈ P, p) : ℕ) : ℝ) ≤ Real.sqrt (a : ℝ) * (J : ℝ) := by
  classical
  let Pa := P.filter (fun p => p ∣ a)
  let PJ := P.filter (fun p => ¬ p ∣ a)
  have hPa : ∀ p ∈ Pa, p.Prime := fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hPJ : ∀ p ∈ PJ, p.Prime := fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hPa2 : ∀ p ∈ Pa, p ^ 2 ∣ a := by
    intro p hp
    obtain ⟨hpP, hpa⟩ := Finset.mem_filter.mp hp
    exact prime_square_dvd_left_of_not_right (hP p hpP) (hP2 p hpP)
      (coprime_prime_not_both hac (hP p hpP) hpa)
  have hPJdiv : ∀ p ∈ PJ, p ∣ J := by
    intro p hp
    obtain ⟨hpP, hpa⟩ := Finset.mem_filter.mp hp
    have hpp : p ∣ p ^ 2 := ⟨p, by ring⟩
    have hpc : p ∣ c := ((hP p hpP).dvd_mul.mp (dvd_trans hpp (hP2 p hpP))).resolve_left hpa
    exact hJdiv p (hP p hpP) hpc
  have hQA := nat_le_sqrt_of_square_dvd ha (prime_product_square_dvd_of_each Pa hPa hPa2)
  have hQJNat : (∏ p ∈ PJ, p) ≤ J :=
    Nat.le_of_dvd hJ (prime_product_dvd_of_each PJ hPJ hPJdiv)
  have hQJ : (((∏ p ∈ PJ, p) : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast hQJNat
  have hsplit := product_split_filter P (fun p => p ∣ a)
  have hsplitR : (((∏ p ∈ P, p) : ℕ) : ℝ) =
      (((∏ p ∈ Pa, p) : ℕ) : ℝ) * (((∏ p ∈ PJ, p) : ℕ) : ℝ) := by
    have he := congrArg (fun k : ℕ => (k : ℝ)) hsplit
    simpa only [Nat.cast_mul, Pa, PJ] using he
  rw [hsplitR]
  exact mul_le_mul hQA hQJ (by positivity) (Real.sqrt_nonneg _)

def repeatedPrimeSupport (m : ℕ) : Finset ℕ :=
  m.primeFactors.filter (fun p => p ^ 2 ∣ m)

def repeatedPrimeProduct (m : ℕ) : ℕ :=
  ∏ p ∈ repeatedPrimeSupport m, p

lemma repeatedPrimeSupport_prime {m p : ℕ} (hp : p ∈ repeatedPrimeSupport m) :
    p.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1

lemma repeatedPrimeSupport_square {m p : ℕ} (hp : p ∈ repeatedPrimeSupport m) :
    p ^ 2 ∣ m := (Finset.mem_filter.mp hp).2

lemma repeatedPrimeProduct_pos (m : ℕ) : 0 < repeatedPrimeProduct m := by
  exact Finset.prod_pos fun p hp => (repeatedPrimeSupport_prime hp).pos

theorem repeatedPrimeProduct_le_sqrt {m : ℕ} (hm : 0 < m) :
    (repeatedPrimeProduct m : ℝ) ≤ Real.sqrt (m : ℝ) := by
  apply nat_le_sqrt_of_square_dvd hm
  exact prime_product_square_dvd_of_each (repeatedPrimeSupport m)
    (fun _ hp => repeatedPrimeSupport_prime hp)
    (fun _ hp => repeatedPrimeSupport_square hp)

theorem repeatedPrimeProduct_le_sqrt_mul {a c J : ℕ}
    (ha : 0 < a) (hJ : 0 < J) (hac : Nat.Coprime a c)
    (hJdiv : ∀ p, p.Prime → p ∣ c → p ∣ J) :
    (repeatedPrimeProduct (a * c) : ℝ) ≤ Real.sqrt (a : ℝ) * (J : ℝ) := by
  change (((∏ p ∈ repeatedPrimeSupport (a * c), p) : ℕ) : ℝ) ≤ _
  exact repeated_prime_product_factor_bound (repeatedPrimeSupport (a * c)) ha hJ hac
    (fun _ hp => repeatedPrimeSupport_prime hp)
    (fun _ hp => repeatedPrimeSupport_square hp) hJdiv

end UniversalScalar

open scoped BigOperators

namespace UniversalScalar

lemma coprime_constant_successor (a b : ℕ) : Nat.Coprime a (a * b + 1) := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpN
  have hpn : p ∣ a * b := dvd_mul_of_dvd_left hpa b
  have hh := Nat.dvd_sub hpN hpn
  simpa using hh

theorem actual_repeated_support_bounds {n a b : ℕ} (J : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hn : n = a * b)
    (hab : Nat.Coprime a b) (hJ : J ≠ 0)
    (hJprime : ∀ p, p.Prime → p ∣ b * (n + 1) → (p : ℤ) ∣ J) :
    0 < (repeatedPrimeProduct (n * (n + 1)) : ℝ) ∧
      (repeatedPrimeProduct (n * (n + 1)) : ℝ) ≤
        Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) ∧
      (repeatedPrimeProduct (n * (n + 1)) : ℝ) ≤
        Real.sqrt (a : ℝ) * (J.natAbs : ℝ) := by
  have hnpos : 0 < n := by rw [hn]; positivity
  have hglobal := repeatedPrimeProduct_le_sqrt
    (show 0 < n * (n + 1) by positivity)
  have haN : Nat.Coprime a (n + 1) := by
    rw [hn]
    exact coprime_constant_successor a b
  have hac : Nat.Coprime a (b * (n + 1)) := hab.mul_right haN
  have hJnat : 0 < J.natAbs := Int.natAbs_pos.mpr hJ
  have hJdiv : ∀ p, p.Prime → p ∣ b * (n + 1) → p ∣ J.natAbs := by
    intro p hp hpc
    exact Int.natCast_dvd.mp (hJprime p hp hpc)
  have hfactor := repeatedPrimeProduct_le_sqrt_mul ha hJnat hac hJdiv
  have hident : a * (b * (n + 1)) = n * (n + 1) := by rw [hn]; ring
  rw [hident] at hfactor
  refine ⟨by exact_mod_cast repeatedPrimeProduct_pos (n * (n + 1)), ?_, hfactor⟩
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hglobal

theorem actual_repeated_prime_sum_bound (m : ℕ) :
    repeatedPrimeSum (repeatedPrimeSupport m) <
      Real.log (repeatedPrimeProduct m : ℝ) / 10 + 97 / 100 := by
  apply repeatedPrimeSum_log_bound (repeatedPrimeSupport m)
    (fun _ hp => repeatedPrimeSupport_prime hp)
  simp only [repeatedPrimeProduct, Nat.cast_prod]

theorem actual_support_closure_inputs {n a b : ℕ} (J : ℤ) {K R : ℝ}
    (hnlarge : 1000 ≤ n) (ha : 1 < a) (hb : 0 < b) (hn : n = a * b)
    (hab : Nat.Coprime a b) (hJ : J ≠ 0)
    (hJprime : ∀ p, p.Prime → p ∣ b * (n + 1) → (p : ℤ) ∣ J)
    (hKpos : 0 < K) (hKhi : K < 201 / 100)
    (hJbound : (J.natAbs : ℝ) ≤ K * (a : ℝ) * Real.log (a : ℝ))
    (hRvaluation : R ≤ ((n : ℝ) + 1) * repeatedPrimeSum
      (repeatedPrimeSupport (n * (n + 1)))) :
    let S := repeatedPrimeSum (repeatedPrimeSupport (n * (n + 1)))
    S ≤ Real.log (n : ℝ) / 10 + 97 / 100 + 1 / (10 * (n : ℝ)) ∧
      S < 3 * Real.log (a : ℝ) / 20 +
        Real.log (K * Real.log (a : ℝ)) / 10 + 97 / 100 ∧
      Real.log (K * Real.log (a : ℝ)) ≤ 1 + Real.log (a : ℝ) / 3 ∧
      R ≤ ((n : ℝ) + 1) * S := by
  obtain ⟨hQpos, hQg, hQa⟩ := actual_repeated_support_bounds J
    (by omega : 0 < a) hb hn hab hJ hJprime
  apply support_resultant_closure_inputs
    (by exact_mod_cast hnlarge) (by exact_mod_cast ha) hQpos
    (by exact_mod_cast Int.natAbs_pos.mpr hJ) hKpos hKhi hQg hQa hJbound
    (actual_repeated_prime_sum_bound (n * (n + 1))) hRvaluation

end UniversalScalar

namespace EventualIrreducibility

theorem FactorSeries.firstDifference_quadratic_bound {n : ℕ}
    (s : FactorSeries n) (hn : 1000 ≤ n) :
    |(s.firstDifference : ℝ)| ≤
      (2 + (Real.log (2 * (n : ℝ) + 1) / (n : ℝ)) ^ 2) *
        (s.factor.coeff 0 : ℝ) * Real.log (s.factor.coeff 0 : ℝ) := by
  have hnpos : 0 < n := by omega
  obtain ⟨d, alpha, _hd, _hne, _hprod, hmod, hconst, hlog, htrace⟩ :=
    s.exists_J_root_data hnpos
  have ha := s.constant_gt_one_for_J hnpos
  have htraceR : ((s.firstDifference : ℝ) : ℂ) =
      ((s.factor.coeff 0 : ℝ) : ℂ) * ∑ i, (alpha i - (alpha i)⁻¹) := by
    simpa using htrace
  have hrad := UniversalScalar.J_radial_bound_from_complex_trace alpha
    (show 0 ≤ (s.factor.coeff 0 : ℝ) by linarith) (fun i => (hmod i).le) htraceR
  exact UniversalScalar.J_bound_from_radial_sum (fun i => ‖alpha i‖)
    (by linarith : 0 ≤ (s.factor.coeff 0 : ℝ))
    (fun i => (hmod i).le) hconst (fun i => (hlog i).le)
    (by linarith [(UniversalScalar.root_tau_large
      (show (1000 : ℝ) ≤ n by exact_mod_cast hn)).2]) hrad

theorem FactorSeries.firstDifference_kernel_data {n : ℕ}
    (s : FactorSeries n) (hn : 1000 ≤ n) :
    let K : ℝ := 2 + (Real.log (2 * (n : ℝ) + 1) / (n : ℝ)) ^ 2
    0 < K ∧ K < 201 / 100 ∧
      (s.firstDifference.natAbs : ℝ) ≤
        K * (s.factor.coeff 0 : ℝ) * Real.log (s.factor.coeff 0 : ℝ) := by
  refine ⟨by positivity, UniversalScalar.quadratic_kernel_large
    (show (1000 : ℝ) ≤ n by exact_mod_cast hn), ?_⟩
  simpa only [Nat.cast_natAbs, Int.cast_abs] using s.firstDifference_quadratic_bound hn

end EventualIrreducibility

namespace EventualIrreducibility.UniversalLocalCutAssemblyDraft

open UniversalLocalDraft

lemma colorWeight_coloredPrefix (w : ℕ → ℕ) (c : ℕ → Bool)
    (b : Bool) (r : ℕ) :
    colorWeight b (coloredPrefix w c r) =
      ∑ i ∈ Finset.range r, if c i = b then w i else 0 := by
  induction r with
  | zero => simp [coloredPrefix, colorWeight]
  | succ r ih =>
    simp only [coloredPrefix, colorWeight, ih, Finset.sum_range_succ]
    omega

lemma bool_eq_not_iff (a b : Bool) : (a = !b) ↔ a ≠ b := by
  cases a <;> cases b <;> decide

end EventualIrreducibility.UniversalLocalCutAssemblyDraft

namespace EventualIrreducibility.UniversalBinaryCrossNormDraft

lemma cross_norm_lower_bound (a b x c : ℝ)
    (hb0 : 0 ≤ b) (hx0 : 0 ≤ x) (hc : 0 < c)
    (ha : a ≤ c) (hb : b ≤ c)
    (hproduct : a * b * x ^ 2 = c ^ 4) : c ≤ x := by
  have hab : a * b ≤ c ^ 2 := by
    calc
      a * b ≤ c * c := mul_le_mul ha hb hb0 hc.le
      _ = c ^ 2 := by ring
  have hupper : c ^ 4 ≤ c ^ 2 * x ^ 2 := by
    rw [← hproduct]
    exact mul_le_mul_of_nonneg_right hab (sq_nonneg x)
  have hsq : c ^ 2 ≤ x ^ 2 := by
    have hmul : c ^ 2 * c ^ 2 ≤ c ^ 2 * x ^ 2 := by
      nlinarith only [hupper]
    exact le_of_mul_le_mul_left hmul (sq_pos_of_pos hc)
  nlinarith

theorem binary_cross_norm_ge_exp_neg_two (a b x : ℝ)
    (hb0 : 0 ≤ b) (hx0 : 0 ≤ x)
    (ha : a ≤ Real.exp (-2)) (hb : b ≤ Real.exp (-2))
    (hproduct : a * b * x ^ 2 = Real.exp (-8)) :
    Real.exp (-2) ≤ x := by
  apply cross_norm_lower_bound a b x (Real.exp (-2)) hb0 hx0
    (Real.exp_pos _) ha hb
  rw [hproduct, ← Real.exp_nat_mul]
  norm_num

end EventualIrreducibility.UniversalBinaryCrossNormDraft

open Polynomial
open scoped BigOperators

namespace EventualIrreducibility

lemma FactorSeries.coeff_one_eq_firstDifference {n : ℕ} (s : FactorSeries n) :
    s.coeff 1 = s.firstDifference := by
  have hr : s.factor.reverse.coeff 1 =
      s.factor.coeff (s.factor.natDegree - 1) := by
    rw [Polynomial.coeff_reverse]
    change s.factor.coeff
      (if 1 ≤ s.factor.natDegree then s.factor.natDegree - 1 else 1) = _
    rw [if_pos (by have := s.degree_pos; omega)]
  have h := s.quotient_identity 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.sub_zero, Nat.sub_self, Polynomial.coeff_zero_reverse,
    s.monic.leadingCoeff, one_mul, s.coeff_zero, hr] at h
  unfold FactorSeries.firstDifference
  nlinarith

theorem FactorSeries.prime_dvd_firstDifference_of_constant_unit {n : ℕ}
    (s : FactorSeries n) (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n * (n + 1))
    (hunit : ¬ (p : ℤ) ∣ s.factor.coeff 0) :
    (p : ℤ) ∣ s.firstDifference := by
  obtain ⟨r, hr, hs⟩ := localInput_proved n hn s p hp hpn
  have hr0 : r = 0 := by
    by_contra hne
    have hc := hs 0 (by simpa using Ne.symm hne)
    exact hunit (by simpa only [s.coeff_zero] using hc)
  have hmod : 1 % p ≠ r := by
    rw [hr0, Nat.mod_eq_of_lt hp.one_lt]
    omega
  simpa only [s.coeff_one_eq_firstDifference] using hs 1 hmod

noncomputable def FactorSeries.constantNat {n : ℕ} (s : FactorSeries n) : ℕ :=
  (s.factor.coeff 0).natAbs

lemma FactorSeries.constantNat_cast {n : ℕ} (s : FactorSeries n) (hn : 0 < n) :
    (s.constantNat : ℤ) = s.factor.coeff 0 := by
  simp only [FactorSeries.constantNat, Int.natCast_natAbs,
    abs_of_pos (s.constant_pos hn)]

lemma FactorSeries.constantNat_real {n : ℕ} (s : FactorSeries n) (hn : 0 < n) :
    (s.constantNat : ℝ) = (s.factor.coeff 0 : ℝ) := by
  exact_mod_cast s.constantNat_cast hn

lemma FactorSeries.two_le_constantNat {n : ℕ} (s : FactorSeries n) (hn : 0 < n) :
    2 ≤ s.constantNat := by
  have h : (1 : ℝ) < (s.constantNat : ℝ) := by
    rw [s.constantNat_real hn]
    exact s.constant_gt_one_for_J hn
  have h' : 1 < s.constantNat := by exact_mod_cast h
  omega

theorem FactorSeries.partner_constant_data {n : ℕ}
    (s t : FactorSeries n) (hn : 0 < n)
    (hprod : s.factor * t.factor = fInt n) :
    2 ≤ s.constantNat ∧ 2 ≤ t.constantNat ∧
      n = s.constantNat * t.constantNat ∧
      Nat.Coprime s.constantNat t.constantNat ∧ 6 ≤ n := by
  have ha := s.two_le_constantNat hn
  have hb := t.two_le_constantNat hn
  have hzero : (fInt n).coeff 0 = (n : ℤ) := by
    simp [coeff_fInt, hn]
  obtain ⟨hc, hl⟩ := UniversalIrreducibility.polynomial_constants_and_linear
    hprod hzero (coeff_fInt_linear_int hn)
  have hnprod : n = s.constantNat * t.constantNat := by
    have hz : (n : ℤ) = (s.constantNat : ℤ) * (t.constantNat : ℤ) := by
      rw [s.constantNat_cast hn, t.constantNat_cast hn]
      exact hc.symm
    exact_mod_cast hz
  have hcopZ := UniversalIrreducibility.polynomial_constant_coprime
    hprod hzero (coeff_fInt_linear_int hn)
  have hcop : Nat.Coprime s.constantNat t.constantNat := by
    apply Nat.coprime_of_dvd'
    intro p hp hpa hpb
    have hpaZ : (p : ℤ) ∣ s.factor.coeff 0 := by
      rw [← s.constantNat_cast hn]
      exact_mod_cast hpa
    have hpbZ : (p : ℤ) ∣ t.factor.coeff 0 := by
      rw [← t.constantNat_cast hn]
      exact_mod_cast hpb
    obtain ⟨u, v, huv⟩ := hcopZ
    have hp1 : (p : ℤ) ∣ 1 := by
      rw [← huv]
      exact dvd_add (dvd_mul_of_dvd_right hpaZ u)
        (dvd_mul_of_dvd_right hpbZ v)
    exact_mod_cast hp1
  have hn6 : 6 ≤ n := by
    by_contra hlt
    have ha2 : 2 * s.constantNat ≤ n := by
      calc
        2 * s.constantNat ≤ s.constantNat * t.constantNat := by nlinarith
        _ = n := hnprod.symm
    have hb2 : 2 * t.constantNat ≤ n := by
      calc
        2 * t.constantNat ≤ s.constantNat * t.constantNat := by nlinarith
        _ = n := hnprod.symm
    have hae : s.constantNat = 2 := by omega
    have hbe : t.constantNat = 2 := by omega
    norm_num [hae, hbe] at hcop
  exact ⟨ha, hb, hnprod, hcop, hn6⟩

theorem FactorSeries.radical_dvd_firstDifference {n : ℕ}
    (s t : FactorSeries n) (hn : 0 < n)
    (hprod : s.factor * t.factor = fInt n) :
    (UniversalConstants.supportRadical (t.constantNat * (n + 1)) : ℤ) ∣
      s.firstDifference := by
  obtain ⟨ha, hb, hnprod, hab, hn6⟩ := s.partner_constant_data t hn hprod
  have haN : Nat.Coprime s.constantNat (n + 1) := by
    have hc := UniversalConstants.coprime_factor_successor s.constantNat t.constantNat
    simpa only [← hnprod] using hc
  have haBN : Nat.Coprime s.constantNat (t.constantNat * (n + 1)) :=
    hab.mul_right haN
  change (radical (t.constantNat * (n + 1)) : ℤ) ∣ s.firstDifference
  apply radical_dvd_of_prime_dvd
  intro p hp
  obtain ⟨hpp, hpBN, hBN0⟩ := Nat.mem_primeFactors.mp hp
  have hbig : t.constantNat * (n + 1) ∣ n * (n + 1) := by
    refine ⟨s.constantNat, ?_⟩
    calc
      n * (n + 1) = (s.constantNat * t.constantNat) * (n + 1) :=
        congrArg (fun k : ℕ => k * (n + 1)) hnprod
      _ = t.constantNat * (n + 1) * s.constantNat := by ring
  apply s.prime_dvd_firstDifference_of_constant_unit (by omega) hpp
    (dvd_trans hpBN hbig)
  intro hpaZ
  have hpa : p ∣ s.constantNat := by
    have hz : (p : ℤ) ∣ (s.constantNat : ℤ) := by
      simpa only [s.constantNat_cast hn] using hpaZ
    exact_mod_cast hz
  have hp1 := Nat.dvd_gcd hpa hpBN
  rw [haBN.gcd_eq_one] at hp1
  have hp_le : p ≤ 1 := Nat.le_of_dvd (by omega) hp1
  have hp2 := hpp.two_le
  omega

private lemma nat_pow_mod_one_of_zmod {a k p : ℕ} (hp : p.Prime)
    (h : (a : ZMod p) ^ k = 1) : a ^ k % p = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hv := congrArg ZMod.val h
  simpa only [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_one,
    Nat.mod_eq_of_lt hp.one_lt] using hv

theorem FactorSeries.constantNat_norm_complement {n : ℕ}
    (s t : FactorSeries n) (hn : 0 < n)
    (hprod : s.factor * t.factor = fInt n) :
    ∀ p : ℕ, p.Prime → p ∣ t.constantNat → s.constantNat ^ n % p = 1 := by
  intro p hp hpt
  let : Fact p.Prime := ⟨hp⟩
  have ht : (t.factor.coeff 0 : ZMod p) = (t.constantNat : ZMod p) := by
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      congrArg (Int.castRingHom (ZMod p)) (t.constantNat_cast hn).symm
  have hs : (s.factor.coeff 0 : ZMod p) = (s.constantNat : ZMod p) := by
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      congrArg (Int.castRingHom (ZMod p)) (s.constantNat_cast hn).symm
  have ht0 : (t.factor.coeff 0 : ZMod p) = 0 := by
    rw [ht]
    obtain ⟨q, hq⟩ := hpt
    rw [hq]
    simp
  have hnorm := s.constant_power_mod_complement (K := ZMod p) hn hprod ht0
  have he : Even (s.factor.natDegree * n) := by
    simpa only [Nat.mul_comm] using s.even_mul_degree hn
  rw [he.neg_one_pow, hs] at hnorm
  exact nat_pow_mod_one_of_zmod hp hnorm

theorem FactorSeries.constantNat_norm_successor_of_odd {n : ℕ}
    (s : FactorSeries n) (hn : 2 ≤ n) (ha : Odd s.constantNat) :
    ∀ p : ℕ, p.Prime → p ∣ n + 1 → s.constantNat ^ (n + 1) % p = 1 := by
  intro p hp hpN
  let : Fact p.Prime := ⟨hp⟩
  have hnpos : 0 < n := by omega
  have haZ : Odd (s.factor.coeff 0) := by
    obtain ⟨k, hk⟩ := ha
    refine ⟨(k : ℤ), ?_⟩
    rw [← s.constantNat_cast hnpos]
    exact_mod_cast hk
  have hd := (s.even_degree_iff_odd_constant hn).mpr haZ
  have he : Even (s.factor.natDegree * (n + 1)) := by
    obtain ⟨k, hk⟩ := hd
    refine ⟨k * (n + 1), ?_⟩
    rw [hk]
    ring
  have hN : ((n + 1 : ℕ) : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hpN
    rw [hk]
    simp
  have hnorm := s.constant_succ_power_mod (K := ZMod p) hN
  have hs : (s.factor.coeff 0 : ZMod p) = (s.constantNat : ZMod p) := by
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      congrArg (Int.castRingHom (ZMod p)) (s.constantNat_cast hnpos).symm
  rw [he.neg_one_pow, hs] at hnorm
  exact nat_pow_mod_one_of_zmod hp hnorm

theorem FactorSeries.thirteen_le_constantNat_of_partner {n : ℕ}
    (s t : FactorSeries n) (hn : 0 < n)
    (hprod : s.factor * t.factor = fInt n)
    (hpp : ¬ IsPrimePow (n + 1)) : 13 ≤ s.constantNat := by
  obtain ⟨ha, hb, hnprod, hab, hn6⟩ := s.partner_constant_data t hn hprod
  have hJbound : (s.firstDifference.natAbs : ℝ) <
      (107 / 49 : ℝ) * (s.constantNat : ℝ) * Real.log (s.constantNat : ℝ) := by
    rw [s.constantNat_real hn]
    have h := s.firstDifference_small_bound hn6
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  exact UniversalConstants.thirteen_le_of_norms_and_radical_bound
    s.firstDifference ha hb hnprod rfl hab hpp
    (s.firstDifference_ne_zero hn) (s.radical_dvd_firstDifference t hn hprod)
    hJbound UniversalScalar.log_seven_lt_thirtynine_twentieths
    UniversalScalar.log_twelve_lt_five_halves
    (s.constantNat_norm_complement t hn hprod)
    (s.constantNat_norm_successor_of_odd (by omega))

theorem FactorSeries.both_constants_ge_thirteen {n : ℕ}
    (s t : FactorSeries n) (hn : 0 < n)
    (hprod : s.factor * t.factor = fInt n)
    (hpp : ¬ IsPrimePow (n + 1)) :
    13 ≤ s.constantNat ∧ 13 ≤ t.constantNat := by
  constructor
  · exact s.thirteen_le_constantNat_of_partner t hn hprod hpp
  · exact t.thirteen_le_constantNat_of_partner s hn
      (by simpa only [mul_comm] using hprod) hpp

theorem FactorSeries.parameter_ge_182_of_partner {n : ℕ}
    (s t : FactorSeries n) (hn : 0 < n)
    (hprod : s.factor * t.factor = fInt n)
    (hpp : ¬ IsPrimePow (n + 1)) : 182 ≤ n := by
  obtain ⟨ha, hb⟩ := s.both_constants_ge_thirteen t hn hprod hpp
  obtain ⟨_, _, hnprod, hab, _⟩ := s.partner_constant_data t hn hprod
  by_cases ha14 : 14 ≤ s.constantNat
  · nlinarith
  · have hae : s.constantNat = 13 := by omega
    have hb14 : 14 ≤ t.constantNat := by
      by_contra h
      have hbe : t.constantNat = 13 := by omega
      norm_num [hae, hbe] at hab
    nlinarith

end EventualIrreducibility

open Polynomial

namespace EventualIrreducibility

theorem FactorSeries.exists_partner {n : ℕ} (s : FactorSeries n) (hn : 0 < n) :
    ∃ t : FactorSeries n,
      s.factor * t.factor = fInt n ∧
      s.factor.natDegree + t.factor.natDegree = n - 1 := by
  obtain ⟨h, hh⟩ := s.divides
  have hh0 : h ≠ 0 := by
    intro hz
    have hf0 : fInt n = 0 := by rw [hh, hz, mul_zero]
    exact (monic_fInt n hn).ne_zero hf0
  have hmonic : h.Monic := by
    change h.leadingCoeff = 1
    have hleading : s.factor.leadingCoeff * h.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hh]
      exact (monic_fInt n hn).leadingCoeff
    simpa only [s.monic.leadingCoeff, one_mul] using hleading
  have hdegrees : s.factor.natDegree + h.natDegree = (fInt n).natDegree := by
    rw [hh, Polynomial.natDegree_mul s.monic.ne_zero hh0]
  have hhpos : 0 < h.natDegree := by
    have hslt := s.degree_lt
    omega
  have hhproper : h.natDegree < (fInt n).natDegree := by
    have hspos := s.degree_pos
    omega
  have hhdiv : h ∣ fInt n := by
    refine ⟨s.factor, ?_⟩
    simpa only [mul_comm] using hh
  let t : FactorSeries n := ⟨h, hmonic, hhdiv, hhpos, hhproper⟩
  refine ⟨t, hh.symm, ?_⟩
  simpa only [t, natDegree_fInt n hn] using hdegrees

theorem exists_small_factor_pair (n : ℕ) (hn : 2 ≤ n)
    (hred : ¬ Irreducible (fQ n)) :
    ∃ s t : FactorSeries n,
      s.factor * t.factor = fInt n ∧
      2 * s.factor.natDegree < n ∧
      s.factor.natDegree + t.factor.natDegree = n - 1 := by
  obtain ⟨s, hs⟩ := exists_small_factorSeries n hn hred
  obtain ⟨t, hprod, hdegrees⟩ := s.exists_partner (by omega)
  exact ⟨s, t, hprod, by omega, hdegrees⟩

theorem FactorSeries.constantNat_succ_power_signed {n p : ℕ}
    (s : FactorSeries n) (hn : 0 < n) (hp : p.Prime) (hpd : p ∣ n + 1) :
    (s.constantNat : ZMod p) ^ (n + 1) =
      (-1 : ZMod p) ^ (s.factor.natDegree * (n + 1)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hN : ((n + 1 : ℕ) : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hpd
    rw [hk]
    simp
  have hnorm := s.constant_succ_power_mod (K := ZMod p) hN
  have hs : (s.factor.coeff 0 : ZMod p) = (s.constantNat : ZMod p) := by
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      congrArg (Int.castRingHom (ZMod p)) (s.constantNat_cast hn).symm
  simpa only [hs] using hnorm

end EventualIrreducibility

namespace EventualIrreducibility.UniversalPrimePowerLocal

open Polynomial

lemma real_multiset_prod_pos {ι : Type*} (S : Multiset ι) (f : ι → ℝ)
    (hf : ∀ x ∈ S, 0 < f x) : 0 < (S.map f).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons x S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_pos (hf x (Multiset.mem_cons_self _ _))
      (ih (fun y hy => hf y (Multiset.mem_cons_of_mem hy)))

lemma real_multiset_prod_lt_of_positive {ι : Type*}
    (S : Multiset ι) (f g : ι → ℝ) (hS : S ≠ 0)
    (hf : ∀ x ∈ S, 0 < f x) (hfg : ∀ x ∈ S, f x < g x) :
    (S.map f).prod < (S.map g).prod := by
  induction S using Multiset.induction_on with
  | empty => exact False.elim (hS rfl)
  | @cons x S ih =>
    have hx := hfg x (Multiset.mem_cons_self _ _)
    have hxpos := hf x (Multiset.mem_cons_self _ _)
    have htpos := real_multiset_prod_pos S f
      (fun y hy => hf y (Multiset.mem_cons_of_mem hy))
    have ht : (S.map f).prod ≤ (S.map g).prod := by
      by_cases hz : S = 0
      · simpa only [hz, Multiset.map_zero, Multiset.prod_zero] using (le_refl (1 : ℝ))
      · exact (ih hz (fun y hy => hf y (Multiset.mem_cons_of_mem hy))
          (fun y hy => hfg y (Multiset.mem_cons_of_mem hy))).le
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hx htpos)
      (mul_le_mul_of_nonneg_left ht (lt_trans hxpos hx).le)

lemma multiset_prod_scale_pow {ι : Type*} (S : Multiset ι)
    (f : ι → ℝ) (c : ℝ) (D : ℕ) :
    (S.map (fun x => c * f x ^ D)).prod = c ^ S.card * (S.map f).prod ^ D := by
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons x S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih,
      pow_succ, mul_pow]
    ring

lemma norm_multiset_prod (S : Multiset ℂ) :
    ‖S.prod‖ = (S.map (fun z => ‖z‖)).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons x S ih => simp only [Multiset.prod_cons, norm_mul, ih,
      Multiset.map_cons]

lemma resultant_norm_gt_of_roots
    (P Q : ℂ[X]) (hP : P.Monic) (hd : 0 < P.natDegree)
    {c : ℝ} (hc : 0 < c) (D : ℕ)
    (hroots : ∀ z : ℂ, P.eval z = 0 →
      0 < ‖z‖ ∧ c * ‖z‖ ^ D < ‖Q.eval z‖) :
    c ^ P.natDegree * ‖P.coeff 0‖ ^ D <
      ‖P.resultant Q P.natDegree Q.natDegree‖ := by
  have hs : P.Splits := IsAlgClosed.splits P
  have hcard : P.roots.card = P.natDegree := hs.natDegree_eq_card_roots.symm
  have hne : P.roots ≠ 0 := by
    intro hz
    rw [hz, Multiset.card_zero] at hcard
    omega
  have hcomparison := real_multiset_prod_lt_of_positive P.roots
    (fun z => c * ‖z‖ ^ D) (fun z => ‖Q.eval z‖) hne
    (fun z hz => mul_pos hc (pow_pos (hroots z
      ((Polynomial.mem_roots hP.ne_zero).mp hz)).1 D))
    (fun z hz => (hroots z ((Polynomial.mem_roots hP.ne_zero).mp hz)).2)
  have hconstant : ‖P.coeff 0‖ = (P.roots.map (fun z => ‖z‖)).prod := by
    have he := congrArg norm (hs.eval_eq_prod_roots_of_monic hP (0 : ℂ))
    rw [← Polynomial.coeff_zero_eq_eval_zero, norm_multiset_prod] at he
    simpa only [Multiset.map_map, Function.comp_def, zero_sub, norm_neg] using he
  have hresultant : ‖P.resultant Q P.natDegree Q.natDegree‖ =
      (P.roots.map (fun z => ‖Q.eval z‖)).prod := by
    rw [Polynomial.resultant_eq_prod_eval P Q Q.natDegree le_rfl hs,
      hP.leadingCoeff, one_pow, one_mul, norm_multiset_prod]
    simp only [Multiset.map_map, Function.comp_def]
  rw [multiset_prod_scale_pow, hcard, ← hconstant, ← hresultant] at hcomparison
  exact hcomparison

lemma actual_factor_root_is_root {n : ℕ} (s : FactorSeries n) {z : ℂ}
    (hz : (s.factor.map (Int.castRingHom ℂ)).eval z = 0) :
    ((fInt n).map (Int.castRingHom ℂ)).eval z = 0 := by
  obtain ⟨h, hh⟩ := s.divides
  rw [hh, Polynomial.map_mul, Polynomial.eval_mul, hz, zero_mul]

lemma complex_norm_int_eq_natAbs (z : ℤ) : ‖(z : ℂ)‖ = (z.natAbs : ℝ) := by
  simp only [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]

theorem actual_prime_power_resultant_arch_lower
    {n p : ℕ} (s : FactorSeries n) (hn : 3 ≤ n) (hp : p.Prime) (k : ℕ)
    (hN : n + 1 = p ^ (k + 1)) :
    (3 / 8 : ℝ) ^ s.factor.natDegree *
      (s.factor.coeff 0 : ℝ) ^ (p ^ k * (p - 1)) <
        ((s.factor.resultant (Polynomial.cyclotomic (p ^ (k + 1)) ℤ)
          s.factor.natDegree (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree).natAbs : ℝ) := by
  let P : ℂ[X] := s.factor.map (Int.castRingHom ℂ)
  let Q : ℂ[X] := (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).map (Int.castRingHom ℂ)
  have hP : P.Monic := s.monic.map _
  have hdegree : P.natDegree = s.factor.natDegree := s.monic.natDegree_map _
  have hQdegree : Q.natDegree = (Polynomial.cyclotomic (p ^ (k + 1)) ℤ).natDegree :=
    (Polynomial.cyclotomic.monic _ _).natDegree_map _
  have ha : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by
    exact_mod_cast s.constant_pos (by omega : 0 < n)
  have hlower := resultant_norm_gt_of_roots P Q hP
    (by simpa only [hdegree] using s.degree_pos) (by norm_num : (0 : ℝ) < 3 / 8)
    (p ^ k * (p - 1)) (by
      intro z hz
      have hf := actual_factor_root_is_root s hz
      have hz1 := (RootGeometry.factor_root_annulus s (by omega : 0 < n) hz).1
      have hfour := UniversalInnerRadius.root_power_gt_four hn hf
      have hfourN : 4 < ‖z‖ ^ (p ^ (k + 1)) := by
        rw [← hN]
        exact lt_of_lt_of_le hfour (pow_le_pow_right₀ hz1.le (by omega))
      refine ⟨lt_trans zero_lt_one hz1, ?_⟩
      simpa only [Q, Polynomial.map_cyclotomic_int] using
        UniversalConstants.norm_cyclotomic_prime_power_gt_three_eighths hp k hz1 hfourN)
  have hconstant : ‖P.coeff 0‖ = (s.factor.coeff 0 : ℝ) := by
    simp only [P, Polynomial.coeff_map, Int.coe_castRingHom]
    rw [show (s.factor.coeff 0 : ℂ) = ((s.factor.coeff 0 : ℝ) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  rw [hconstant, hdegree, hQdegree] at hlower
  simpa only [P, Q, Polynomial.resultant_map_map, Int.coe_castRingHom,
    complex_norm_int_eq_natAbs] using hlower

end EventualIrreducibility.UniversalPrimePowerLocal

namespace EventualIrreducibility.UniversalPrimePowerLocal

open UniversalSlopeDraft

lemma power_resultant_metric_incompatible
    {a H c : ℝ} {d p N D : ℕ}
    (ha : 0 < a) (hH : 0 < H) (hc : 0 < c) (_hd : 0 < d) (hp : 2 ≤ p)
    (hrelation : D * p = N * (p - 1))
    (hmetric : H ^ d < a ^ N)
    (hresultant : c ^ d * a ^ D < (p : ℝ) ^ d)
    (hscalar : (p : ℝ) ^ p ≤ c ^ p * H ^ (p - 1)) : False := by
  have hm : (H ^ d) ^ (p - 1) < (a ^ N) ^ (p - 1) := by
    gcongr
    all_goals omega
  have hr : (c ^ d * a ^ D) ^ p < ((p : ℝ) ^ d) ^ p := by
    gcongr
  have hchain : (c ^ p * H ^ (p - 1)) ^ d < ((p : ℝ) ^ p) ^ d := by
    calc
      (c ^ p * H ^ (p - 1)) ^ d =
          (c ^ d) ^ p * (H ^ d) ^ (p - 1) := by
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm p d, Nat.mul_comm (p - 1) d]
      _ < (c ^ d) ^ p * (a ^ N) ^ (p - 1) :=
        mul_lt_mul_of_pos_left hm (pow_pos (pow_pos hc _) _)
      _ = (c ^ d * a ^ D) ^ p := by
        simp only [mul_pow, ← pow_mul, hrelation]
      _ < ((p : ℝ) ^ d) ^ p := hr
      _ = ((p : ℝ) ^ p) ^ d := by rw [← pow_mul, ← pow_mul, Nat.mul_comm d p]
  have hback : ((p : ℝ) ^ p) ^ d ≤ (c ^ p * H ^ (p - 1)) ^ d := by
    gcongr
  exact (not_lt_of_ge hback) hchain

lemma higher_power_of_cubic_comparison
    {H Y : ℝ} (hH : 0 < H) (hY : 1 < Y) (hbase : Y ^ 3 < H ^ 2)
    {p : ℕ} (hp : 3 ≤ p) : Y ^ p < H ^ (p - 1) := by
  have hY0 : 0 < Y := lt_trans zero_lt_one hY
  have hYH : Y < H := by
    by_contra h
    have hHY : H ≤ Y := le_of_not_gt h
    have hsq : H ^ 2 ≤ Y ^ 2 := by nlinarith
    have hcube : Y ^ 2 < Y ^ 3 := by nlinarith [mul_pos (sq_pos_of_pos hY0) (sub_pos.mpr hY)]
    linarith
  induction p, hp using Nat.le_induction with
  | base => simpa using hbase
  | @succ p hp ih =>
    have hpred : p - 1 + 1 = p := by omega
    calc
      Y ^ (p + 1) = Y ^ p * Y := pow_succ _ _
      _ < H ^ (p - 1) * Y := mul_lt_mul_of_pos_right ih hY0
      _ ≤ H ^ (p - 1) * H := mul_le_mul_of_nonneg_left hYH.le (pow_nonneg hH.le _)
      _ = H ^ ((p + 1) - 1) := by rw [← pow_succ, hpred]; congr 1

lemma odd_prime_power_metric_scalar
    {n p : ℕ} (hp : 3 ≤ p) (hN : p ^ 3 ≤ n + 1) :
    (p : ℝ) ^ p < (3 / 8 : ℝ) ^ p *
      (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) ^ (p - 1) := by
  let H : ℝ := Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))
  let Y : ℝ := (8 / 3) * (p : ℝ)
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp3 : (27 : ℝ) ≤ (p : ℝ) ^ 3 := by
    calc
      (27 : ℝ) = (3 : ℝ) ^ 3 := by norm_num
      _ ≤ (p : ℝ) ^ 3 := by gcongr
  have hNR : (p : ℝ) ^ 3 ≤ (n : ℝ) + 1 := by exact_mod_cast hN
  have hnR : (26 : ℝ) ≤ n := by linarith
  have hHpos : 0 < H := Real.sqrt_pos.2 (by positivity)
  have hHsquared : H ^ 2 = (n : ℝ) * ((n : ℝ) + 1) :=
    Real.sq_sqrt (by positivity)
  have hmul : (p : ℝ) ^ 3 * ((p : ℝ) ^ 3 - 1) ≤
      ((n : ℝ) + 1) * (n : ℝ) :=
    mul_le_mul hNR (by linarith) (by linarith) (by positivity)
  have h26 : 26 * (p : ℝ) ^ 3 ≤ H ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left (show (26 : ℝ) ≤ (p : ℝ) ^ 3 - 1 by linarith)
      (show 0 ≤ (p : ℝ) ^ 3 by positivity)
    rw [hHsquared]
    nlinarith
  have hY1 : 1 < Y := by dsimp [Y]; linarith
  have hbase : Y ^ 3 < H ^ 2 := by
    dsimp [Y]
    nlinarith [show 0 < (p : ℝ) ^ 3 by positivity]
  have hpower := higher_power_of_cubic_comparison hHpos hY1 hbase hp
  calc
    (p : ℝ) ^ p = (3 / 8 : ℝ) ^ p * Y ^ p := by
      rw [← mul_pow]
      congr 1
      dsimp [Y]
      ring
    _ < (3 / 8 : ℝ) ^ p * H ^ (p - 1) :=
      mul_lt_mul_of_pos_left hpower (pow_pos (by norm_num) _)

lemma small_degree_lt_prime_power_cyclotomic
    {n p : ℕ} (hp : p.Prime) (k d : ℕ)
    (hN : n + 1 = p ^ (k + 1)) (hsmall : 2 * d < n) :
    d < p ^ (k + 1) - p ^ k := by
  have hsplit : p ^ (k + 1) = p ^ k * (p - 1) + p ^ k := by
    rw [pow_succ]
    have h := congrArg (fun q : ℕ => p ^ k * q) (Nat.sub_add_cancel hp.one_le)
    simpa only [Nat.mul_add, Nat.mul_one] using h.symm
  have hphi : p ^ (k + 1) - p ^ k = p ^ k * (p - 1) := by omega
  have hp2 := hp.two_le
  have hpminus : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  rw [hphi]
  nlinarith

theorem no_small_factor_odd_prime_power_successor
    (hU : StandardUnramifiedInput) (hS : StandardValuedSplittingInput.{0})
    {n p : ℕ} (s : FactorSeries n) (hp : p.Prime) (hp3 : 3 ≤ p)
    (k : ℕ) (hk : 2 ≤ k) (hN : n + 1 = p ^ (k + 1))
    (hsmall : 2 * s.factor.natDegree < n) : False := by
  have hNp3 : p ^ 3 ≤ n + 1 := by
    rw [hN]
    gcongr <;> omega
  have hn3 : 3 ≤ n := by
    have hp27 : 27 ≤ p ^ 3 := by
      calc
        27 = 3 ^ 3 := by norm_num
        _ ≤ p ^ 3 := by gcongr
    omega
  have hn : 0 < n := by omega
  have hd := small_degree_lt_prime_power_cyclotomic hp k s.factor.natDegree hN hsmall
  have hlocal := actual_prime_power_resultant_natAbs hU hS s hn hp k hN hd
  have harch := actual_prime_power_resultant_arch_lower s hn3 hp k hN
  rw [hlocal, Nat.cast_pow] at harch
  have ha : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by
    exact_mod_cast s.constant_pos hn
  have hH : 0 < Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) := by
    apply Real.sqrt_pos.2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hrelation : (p ^ k * (p - 1)) * p = (n + 1) * (p - 1) := by
    rw [hN, pow_succ]
    ring
  exact power_resultant_metric_incompatible ha hH (by norm_num) s.degree_pos hp.two_le
    hrelation (s.constant_norm_metric hn) harch (odd_prime_power_metric_scalar hp3 hNp3).le

end EventualIrreducibility.UniversalPrimePowerLocal

namespace EventualIrreducibility.UniversalPrimePowerLocal

open Polynomial UniversalSlopeDraft

lemma norm_cyclotomic_two_power_gt_three_fifths
    (k : ℕ) {z : ℂ} (hz : 1 < ‖z‖)
    (hlarge : (25 / 4 : ℝ) < ‖z‖ ^ (2 ^ (k + 1))) :
    (3 / 5 : ℝ) * ‖z‖ ^ (2 ^ k) <
      ‖(Polynomial.cyclotomic (2 ^ (k + 1)) ℂ).eval z‖ := by
  have hq : 0 < 2 ^ k := by positivity
  have hqnorm : 1 < ‖z‖ ^ (2 ^ k) := one_lt_pow₀ hz (by omega)
  have hne : z ^ (2 ^ k) - 1 ≠ 0 := by
    intro h
    have heq : z ^ (2 ^ k) = 1 := sub_eq_zero.mp h
    have hn := congrArg norm heq
    simp only [norm_pow, norm_one] at hn
    linarith
  have hphi : (Polynomial.cyclotomic (2 ^ (k + 1)) ℂ).eval z = z ^ (2 ^ k) + 1 := by
    apply mul_right_cancel₀ hne
    calc
      (Polynomial.cyclotomic (2 ^ (k + 1)) ℂ).eval z * (z ^ (2 ^ k) - 1) =
          z ^ (2 ^ (k + 1)) - 1 :=
        UniversalConstants.cyclotomic_prime_power_eval_identity Nat.prime_two k z
      _ = (z ^ (2 ^ k) + 1) * (z ^ (2 ^ k) - 1) := by
        rw [show 2 ^ (k + 1) = 2 ^ k * 2 by rw [pow_succ], pow_mul]
        ring
  have hsquare : (‖z‖ ^ (2 ^ k)) ^ 2 = ‖z‖ ^ (2 ^ (k + 1)) := by
    rw [show 2 ^ (k + 1) = 2 ^ k * 2 by rw [pow_succ], pow_mul]
  have hqnorm' : (5 / 2 : ℝ) < ‖z‖ ^ (2 ^ k) := by
    nlinarith [pow_nonneg (norm_nonneg z) (2 ^ k)]
  have hlo : ‖z‖ ^ (2 ^ k) - 1 ≤ ‖z ^ (2 ^ k) + 1‖ := by
    have h := norm_sub_norm_le (z ^ (2 ^ k)) (-1 : ℂ)
    rw [Complex.norm_pow] at h
    simpa only [norm_neg, norm_one, sub_neg_eq_add] using h
  rw [hphi]
  nlinarith

theorem actual_binary_resultant_arch_lower
    {n : ℕ} (s : FactorSeries n) (hn : 8 ≤ n) (k : ℕ)
    (hN : n + 1 = 2 ^ (k + 1)) :
    (3 / 5 : ℝ) ^ s.factor.natDegree *
      (s.factor.coeff 0 : ℝ) ^ (2 ^ k) <
        ((s.factor.resultant (Polynomial.cyclotomic (2 ^ (k + 1)) ℤ)
          s.factor.natDegree (Polynomial.cyclotomic (2 ^ (k + 1)) ℤ).natDegree).natAbs : ℝ) := by
  let P : ℂ[X] := s.factor.map (Int.castRingHom ℂ)
  let Q : ℂ[X] := (Polynomial.cyclotomic (2 ^ (k + 1)) ℤ).map (Int.castRingHom ℂ)
  have hP : P.Monic := s.monic.map _
  have hdegree : P.natDegree = s.factor.natDegree := s.monic.natDegree_map _
  have hQdegree : Q.natDegree = (Polynomial.cyclotomic (2 ^ (k + 1)) ℤ).natDegree :=
    (Polynomial.cyclotomic.monic _ _).natDegree_map _
  have ha : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by
    exact_mod_cast s.constant_pos (by omega : 0 < n)
  have hlower := resultant_norm_gt_of_roots P Q hP
    (by simpa only [hdegree] using s.degree_pos) (by norm_num : (0 : ℝ) < 3 / 5)
    (2 ^ k) (by
      intro z hz
      have hf := actual_factor_root_is_root s hz
      have hz1 := (RootGeometry.factor_root_annulus s (by omega : 0 < n) hz).1
      have hpi := UniversalInnerRadius.root_power_gt_two_pi hn hf
      have hlarge : (25 / 4 : ℝ) < ‖z‖ ^ (2 ^ (k + 1)) := by
        have hlarge' : (25 / 4 : ℝ) < ‖z‖ ^ n := by
          linarith [UniversalInnerRadius.pi_rational_bounds.1]
        rw [← hN]
        exact lt_of_lt_of_le hlarge' (pow_le_pow_right₀ hz1.le (by omega))
      refine ⟨lt_trans zero_lt_one hz1, ?_⟩
      simpa only [Q, Polynomial.map_cyclotomic_int] using
        norm_cyclotomic_two_power_gt_three_fifths k hz1 hlarge)
  have hconstant : ‖P.coeff 0‖ = (s.factor.coeff 0 : ℝ) := by
    simp only [P, Polynomial.coeff_map, Int.coe_castRingHom]
    rw [show (s.factor.coeff 0 : ℂ) = ((s.factor.coeff 0 : ℝ) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  rw [hconstant, hdegree, hQdegree] at hlower
  simpa only [P, Q, Polynomial.resultant_map_map, Int.coe_castRingHom,
    complex_norm_int_eq_natAbs] using hlower

lemma binary_metric_scalar {n : ℕ} (hn : 15 ≤ n) :
    (2 : ℝ) ^ 2 ≤ (3 / 5 : ℝ) ^ 2 *
      (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) ^ (2 - 1) := by
  have hnR : (15 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) * ((n : ℝ) + 1) by positivity)
  have hs0 := Real.sqrt_nonneg ((n : ℝ) * ((n : ℝ) + 1))
  have hlarge : (100 / 9 : ℝ) < Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) := by
    nlinarith
  rw [show (2 - 1 : ℕ) = 1 by omega, pow_one]
  nlinarith

theorem no_small_factor_binary_prime_power_successor
    (hU : StandardUnramifiedInput) (hS : StandardValuedSplittingInput.{0})
    {n : ℕ} (s : FactorSeries n) (hn : 15 ≤ n) (k : ℕ)
    (hN : n + 1 = 2 ^ (k + 1)) (hsmall : 2 * s.factor.natDegree < n) : False := by
  have hn0 : 0 < n := by omega
  have hd := small_degree_lt_prime_power_cyclotomic Nat.prime_two k
    s.factor.natDegree hN hsmall
  have hlocal := actual_prime_power_resultant_natAbs hU hS s hn0 Nat.prime_two k hN hd
  have harch := actual_binary_resultant_arch_lower s (by omega) k hN
  rw [hlocal, Nat.cast_pow] at harch
  have ha : (0 : ℝ) < (s.factor.coeff 0 : ℝ) := by
    exact_mod_cast s.constant_pos hn0
  have hH : 0 < Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) := by
    apply Real.sqrt_pos.2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    positivity
  have hrelation : (2 ^ k) * 2 = (n + 1) * (2 - 1) := by
    rw [hN, pow_succ]
    norm_num
  exact power_resultant_metric_incompatible ha hH (by norm_num) s.degree_pos (by norm_num)
    hrelation (s.constant_norm_metric hn0) harch (binary_metric_scalar hn)

end EventualIrreducibility.UniversalPrimePowerLocal

open Polynomial

namespace EventualIrreducibility.UniversalPrimeSuccessor

open UniversalSlopeDraft UniversalResidueOneProfileDraft UniversalResidueOneFacesDraft

theorem no_factor_of_prime_successor_in_discrete_field
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ)
    (hna : IsNonarchimedean v)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    {n p : ℕ} (s : FactorSeries n) (hn : 2 ≤ n) (hp : p.Prime)
    (hN : n + 1 = p)
    (hnorm : ∀ t : ℕ, t ≠ 0 →
      v (t : E) = Real.exp (-(padicValNat p t : ℝ))) : False := by
  let : Fact p.Prime := ⟨hp⟩
  have hnpos : 0 < n := by omega
  have hp3 : 3 ≤ p := by omega
  have hpodd : p ≠ 2 := by omega
  have hden : 0 < p - 2 := by omega
  have hval : padicValNat p (n + 1) = 1 := by
    rw [hN]
    simpa only [pow_one] using (padicValNat.prime_pow (p := p) 1)
  have hface := (actual_residue_one_faces n p 1 hnpos hp (by omega)
    hnorm (Or.inr hval)).1 hpodd
  have hdegree : (oneTranslate n : E[X]).natDegree = p - 2 := by
    rw [oneTranslate_natDegree n hnpos]
    omega
  have hpure : PureGauss (oneTranslate n : E[X]) v
      (Real.exp (-(1 : ℝ) / ((p - 2 : ℕ) : ℝ))) := by
    refine ⟨hface.1, ?_⟩
    simpa only [hdegree] using hface.2
  obtain ⟨h, hfactor⟩ := s.divides
  let A : E[X] := (s.factor.map (Int.castRingHom E)).comp (X + C 1)
  let B : E[X] := (h.map (Int.castRingHom E)).comp (X + C 1)
  have hA : A.Monic := (s.monic.map _).comp_X_add_C 1
  have hAd : A.natDegree = s.factor.natDegree := by
    dsimp only [A]
    simp only [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C,
      Nat.mul_one, s.monic.natDegree_map]
  have hAB : A * B = (oneTranslate n : E[X]) := by
    rw [oneTranslate_eq_comp, hfactor, Polynomial.map_mul, Polynomial.mul_comp]
  have hdiv : A ∣ (oneTranslate n : E[X]) := ⟨B, hAB.symm⟩
  have hwidth := denominator_dvd_divisor_degree
    (oneTranslate n : E[X]) A (oneTranslate_monic n hnpos) hA hdiv hna
    (p - 2) hden hdiscrete hpure
  rw [hAd] at hwidth
  have hle : p - 2 ≤ s.factor.natDegree := Nat.le_of_dvd s.degree_pos hwidth
  have hlt := s.degree_lt
  rw [natDegree_fInt n hnpos] at hlt
  omega

theorem no_factor_prime_successor
    (hU : StandardUnramifiedInput) {n : ℕ} (s : FactorSeries n)
    (hn : 2 ≤ n) (hp : (n + 1).Prime) : False := by
  have hnot : ¬ (n + 1) ∣ 1 := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < (1 : ℕ)) h
    omega
  obtain ⟨D⟩ := hU (n + 1) 1 hp (by omega) hnot
  exact no_factor_of_prime_successor_in_discrete_field
    D.v D.nonarchimedean D.discrete s hn hp rfl D.nat_norm

theorem irreducible_prime_successor_rat
    (hU : StandardUnramifiedInput) {n : ℕ}
    (hn : 2 ≤ n) (hp : (n + 1).Prime) : Irreducible (fQ n) := by
  by_contra hred
  obtain ⟨s, _⟩ := exists_small_factorSeries n hn hred
  exact no_factor_prime_successor hU s hn hp

end EventualIrreducibility.UniversalPrimeSuccessor

namespace EventualIrreducibility.UniversalPrimePowerLocal

lemma no_factorization_of_prime_with_large_constants
    {n a b : ℕ} (hn : n.Prime) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hprod : n = a * b) : False := by
  have hdiv : a ∣ n ^ 1 := by
    simpa only [pow_one] using (show a ∣ n from ⟨b, hprod⟩)
  obtain ⟨j, hj, haj⟩ := (Nat.dvd_prime_pow hn).mp hdiv
  have hjcases : j = 0 ∨ j = 1 := by omega
  rcases hjcases with rfl | rfl
  · simp only [pow_zero] at haj
    omega
  · simp only [pow_one] at haj
    have hn0 := hn.pos
    rw [haj] at hprod
    nlinarith

theorem no_factor_prime_constant
    {n : ℕ} (s : FactorSeries n) (hn : n.Prime) : False := by
  obtain ⟨t, hprod, _hdegrees⟩ := s.exists_partner hn.pos
  obtain ⟨ha, hb, hab, _hcop, _hn6⟩ := s.partner_constant_data t hn.pos hprod
  exact no_factorization_of_prime_with_large_constants hn ha hb hab

theorem irreducible_prime_constant_rat
    {n : ℕ} (hn : n.Prime) : Irreducible (fQ n) := by
  by_contra hred
  obtain ⟨s, _hsmall⟩ := exists_small_factorSeries n hn.two_le hred
  exact no_factor_prime_constant s hn

theorem no_factor_odd_prime_square_successor
    {n p : ℕ} (s : FactorSeries n) (hn : 0 < n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hN : n + 1 = p ^ 2) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, hprod, hdegrees⟩ := s.exists_partner hn
  obtain ⟨ha, hb, hnprod, hcop, _hn6⟩ := s.partner_constant_data t hn hprod
  have hpodd : Odd p :=
    Nat.coprime_two_right.mp ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hpmod : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hNmod : (n + 1) % 2 = 1 := by
    rw [hN, Nat.pow_mod, hpmod]
  have hNOdd : Odd (n + 1) := Nat.odd_iff.mpr hNmod
  have hsumodd : (s.factor.natDegree + t.factor.natDegree) % 2 = 1 := by
    omega
  have hpd : p ∣ n + 1 := by
    rw [hN]
    exact dvd_pow_self p (by norm_num : 2 ≠ 0)
  have hsa := s.constantNat_succ_power_signed hn hp hpd
  have htb := t.constantNat_succ_power_signed hn hp hpd
  have hprodN : s.constantNat * t.constantNat + 1 = p ^ 2 := by
    rw [← hnprod, hN]
  rcases Nat.even_or_odd s.factor.natDegree with hdeven | hdodd
  · have hdmod := Nat.even_iff.mp hdeven
    have heodd : Odd t.factor.natDegree := Nat.odd_iff.mpr (by omega)
    have hs : (s.constantNat : ZMod p) ^ (p ^ 2) = 1 := by
      rw [← hN, hsa]
      exact (hdeven.mul_right (n + 1)).neg_one_pow
    have ht : (t.constantNat : ZMod p) ^ (p ^ 2) = -1 := by
      rw [← hN, htb]
      exact (heodd.mul hNOdd).neg_one_pow
    exact UniversalConstants.no_coprime_prime_square_norm_factorization hp hp2
      ha hb hcop hprodN hs ht
  · have hdmod := Nat.odd_iff.mp hdodd
    have heeven : Even t.factor.natDegree := Nat.even_iff.mpr (by omega)
    have ht : (t.constantNat : ZMod p) ^ (p ^ 2) = 1 := by
      rw [← hN, htb]
      exact (heeven.mul_right (n + 1)).neg_one_pow
    have hs : (s.constantNat : ZMod p) ^ (p ^ 2) = -1 := by
      rw [← hN, hsa]
      exact (hdodd.mul hNOdd).neg_one_pow
    exact UniversalConstants.no_coprime_prime_square_norm_factorization hp hp2
      hb ha hcop.symm (by simpa only [Nat.mul_comm] using hprodN) ht hs

theorem irreducible_prime_square_successor_rat
    {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hN : n + 1 = p ^ 2) :
    Irreducible (fQ n) := by
  by_cases hp2 : p = 2
  · have hn3 : n = 3 := by simp only [hp2] at hN; norm_num at hN; omega
    subst n
    exact irreducible_prime_constant_rat (by norm_num : Nat.Prime 3)
  · by_contra hred
    obtain ⟨s, _hsmall⟩ := exists_small_factorSeries n hn hred
    exact no_factor_odd_prime_square_successor s (by omega) hp hp2 hN

end EventualIrreducibility.UniversalPrimePowerLocal

namespace EventualIrreducibility.UniversalPrimePowerLocal

open UniversalSlopeDraft

theorem irreducible_prime_power_successor_rat
    (hU : StandardUnramifiedInput) (hS : StandardValuedSplittingInput.{0})
    {n p r : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hr : 0 < r)
    (hN : n + 1 = p ^ r) : Irreducible (fQ n) := by
  by_cases hr1 : r = 1
  · have hNp : n + 1 = p := by simpa only [hr1, pow_one] using hN
    have hpN : (n + 1).Prime := by rw [hNp]; exact hp
    exact UniversalPrimeSuccessor.irreducible_prime_successor_rat hU hn hpN
  by_cases hr2 : r = 2
  · exact irreducible_prime_square_successor_rat hn hp (by simpa only [hr2] using hN)
  have hr3 : 3 ≤ r := by omega
  by_contra hred
  obtain ⟨s, hs⟩ := exists_small_factorSeries n hn hred
  have hsmall : 2 * s.factor.natDegree < n := by omega
  let k := r - 1
  have hk : k + 1 = r := by dsimp [k]; omega
  have hN' : n + 1 = p ^ (k + 1) := by simpa only [hk] using hN
  by_cases hp2 : p = 2
  · by_cases hrthree : r = 3
    · have hnseven : n = 7 := by
        have h := hN
        rw [hp2, hrthree] at h
        norm_num at h
        omega
      subst n
      exact no_factor_prime_constant s (by norm_num : Nat.Prime 7)
    · have hr4 : 4 ≤ r := by omega
      have hN16 : 16 ≤ n + 1 := by
        rw [hN, hp2]
        calc
          16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ r := by gcongr ; omega
      exact no_small_factor_binary_prime_power_successor hU hS s (by omega)
        k (by simpa only [hp2] using hN') hsmall
  · have hp3 : 3 ≤ p := by have hpge := hp.two_le; omega
    exact no_small_factor_odd_prime_power_successor hU hS s hp hp3 k
      (by dsimp [k]; omega) hN' hsmall

end EventualIrreducibility.UniversalPrimePowerLocal

open scoped BigOperators

namespace EventualIrreducibility.UniversalResultantBudget

open UniversalLocalDraft

def ExactLocalResultantBound (n q : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n * (n + 1) →
    ∃ M m : ℕ, (M = n ∨ M = n + 1) ∧
      M = m * p ^ padicValNat p (n * (n + 1)) ∧
      padicValNat p q + 2 * (padicValNat p (n * (n + 1)) / 2) ≤
        m * exactCut p (padicValNat p (n * (n + 1)))

lemma log_nat_eq_sum_padic (m : ℕ) :
    Real.log (m : ℝ) = ∑ p ∈ m.primeFactors,
      (padicValNat p m : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ m.factorization.support,
      (m.factorization p : ℝ) * Real.log (p : ℝ)) = _
  rw [Nat.support_factorization]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.factorization_def m (Nat.mem_primeFactors.mp hp).1]

lemma log_nat_eq_sum_padic_on {q : ℕ} (hq : q ≠ 0) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hsub : q.primeFactors ⊆ P) :
    Real.log (q : ℝ) = ∑ p ∈ P,
      (padicValNat p q : ℝ) * Real.log (p : ℝ) := by
  rw [log_nat_eq_sum_padic]
  apply Finset.sum_subset hsub
  intro p hp hnot
  have hnd : ¬ p ∣ q := by
    intro h
    exact hnot ((hP p hp).mem_primeFactors h hq)
  simp only [padicValNat.eq_zero_of_not_dvd hnd, Nat.cast_zero, zero_mul]

lemma primeFactors_subset_of_dvd_power {q M d : ℕ}
    (hM : M ≠ 0) (hdiv : q ∣ M ^ d) : q.primeFactors ⊆ M.primeFactors := by
  intro p hp
  obtain ⟨hpp, hpq, _⟩ := Nat.mem_primeFactors.mp hp
  exact hpp.mem_primeFactors (hpp.dvd_of_dvd_pow (dvd_trans hpq hdiv)) hM

lemma layerSum_nonneg (p s : ℕ) : 0 ≤ layerSum p s := by
  unfold layerSum
  exact Finset.sum_nonneg fun _ _ => by positivity

lemma layerSum_le_geometric (p : ℕ) (hp : 2 ≤ p) (s : ℕ) :
    layerSum p s ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hid : 1 / (p : ℝ) +
      ((p : ℝ) / ((p : ℝ) ^ 2 - 1)) / (p : ℝ) ^ 2 =
      (p : ℝ) / ((p : ℝ) ^ 2 - 1) := by
    field_simp
    ring
  induction s with
  | zero => simpa only [layerSum, Finset.range_zero, Finset.sum_empty] using
      (div_nonneg (by linarith : (0 : ℝ) ≤ p) hden.le)
  | succ s ih =>
    rw [layerSum_succ_first]
    calc
      1 / (p : ℝ) + layerSum p s / (p : ℝ) ^ 2 ≤
          1 / (p : ℝ) + ((p : ℝ) / ((p : ℝ) ^ 2 - 1)) / (p : ℝ) ^ 2 :=
        add_le_add (le_refl _) (div_le_div_of_nonneg_right ih (sq_nonneg _))
      _ = (p : ℝ) / ((p : ℝ) ^ 2 - 1) := hid

lemma halfBudget_primeFactors_le (M : ℕ) :
    halfBudget M.primeFactors (fun p => padicValNat p M) ≤ Real.log (M : ℝ) / 2 := by
  have h := two_halfBudget_le M.primeFactors (fun p => padicValNat p M)
  rw [← log_nat_eq_sum_padic M] at h
  linarith

lemma local_bound_normalized {n q p : ℕ} (hloc : ExactLocalResultantBound n q)
    (hp : p.Prime) (hpd : p ∣ n * (n + 1)) :
    (padicValNat p q : ℝ) +
        2 * ((padicValNat p (n * (n + 1)) / 2 : ℕ) : ℝ) ≤
      ((n : ℝ) + 1) * layerSum p (padicValNat p (n * (n + 1)) / 2) := by
  obtain ⟨M, m, hsource, hM, hbound⟩ := hloc p hp hpd
  let r := padicValNat p (n * (n + 1))
  have hMR : (M : ℝ) = (m : ℝ) * (p : ℝ) ^ r := by
    exact_mod_cast hM
  have hMle : (M : ℝ) ≤ (n : ℝ) + 1 := by
    rcases hsource with h | h
    · rw [h]
      linarith
    · rw [h]
      push_cast
      exact le_rfl
  have hpPow : (p : ℝ) ^ r ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast hp.ne_zero
  have hnorm := normalized_exactCut_layers p hp.pos r
  have hcut : (exactCut p r : ℝ) =
      layerSum p (r / 2) * (p : ℝ) ^ r := (div_eq_iff hpPow).mp hnorm
  have hid : (m : ℝ) * (exactCut p r : ℝ) = (M : ℝ) * layerSum p (r / 2) := by
    rw [hMR, hcut]
    ring
  have hreal : (padicValNat p q : ℝ) + 2 * ((r / 2 : ℕ) : ℝ) ≤
      (m : ℝ) * (exactCut p r : ℝ) := by exact_mod_cast hbound
  rw [hid] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_right hMle (layerSum_nonneg p _))

lemma local_valuation_zero_of_not_square {n q p : ℕ}
    (hn : 0 < n) (hloc : ExactLocalResultantBound n q)
    (hp : p.Prime) (hpd : p ∣ n * (n + 1))
    (hnsq : ¬ p ^ 2 ∣ n * (n + 1)) : padicValNat p q = 0 := by
  have hr : padicValNat p (n * (n + 1)) < 2 := by
    have hM0 : n * (n + 1) ≠ 0 := by positivity
    have hh := padicValNat_dvd_iff_le_of_ne_one hp.ne_one
      (a := n * (n + 1)) (n := 2) hM0
    omega
  obtain ⟨M, m, hsource, hM, hbound⟩ := hloc p hp hpd
  have hr01 : padicValNat p (n * (n + 1)) = 0 ∨
      padicValNat p (n * (n + 1)) = 1 := by omega
  have hcut : exactCut p (padicValNat p (n * (n + 1))) = 0 := by
    rcases hr01 with hr0 | hr1
    · rw [hr0]
      rfl
    · rw [hr1]
      rfl
  have hv : padicValNat p q ≤ 0 := calc
    padicValNat p q ≤ padicValNat p q +
        2 * (padicValNat p (n * (n + 1)) / 2) := by omega
    _ ≤ m * exactCut p (padicValNat p (n * (n + 1))) := hbound
    _ = 0 := by rw [hcut, mul_zero]
  omega

theorem log_bound_by_prime_layers {n q : ℕ} (hq : q ≠ 0)
    (hsub : q.primeFactors ⊆ (n * (n + 1)).primeFactors)
    (hloc : ExactLocalResultantBound n q) :
    Real.log (q : ℝ) ≤ ((n : ℝ) + 1) *
        primeLayerBudget (n * (n + 1)).primeFactors
          (fun p => padicValNat p (n * (n + 1))) -
      2 * halfBudget (n * (n + 1)).primeFactors
        (fun p => padicValNat p (n * (n + 1))) := by
  rw [log_nat_eq_sum_padic_on hq _
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) hsub]
  have hpoint : ∀ p ∈ (n * (n + 1)).primeFactors,
      (padicValNat p q : ℝ) * Real.log (p : ℝ) ≤
        ((n : ℝ) + 1) *
          (layerSum p (padicValNat p (n * (n + 1)) / 2) * Real.log (p : ℝ)) -
        2 * (((padicValNat p (n * (n + 1)) / 2 : ℕ) : ℝ) * Real.log (p : ℝ)) := by
    intro p hp
    have hm := Nat.mem_primeFactors.mp hp
    have hb := local_bound_normalized hloc hm.1 hm.2.1
    have hh := mul_le_mul_of_nonneg_right hb (log_nat_nonneg p)
    nlinarith
  have hs := Finset.sum_le_sum hpoint
  simpa only [primeLayerBudget, halfBudget, Finset.sum_sub_distrib,
    ← Finset.mul_sum] using hs

theorem log_bound_exponent_budget8 {n q : ℕ} (hn : 15 ≤ n) (hq : q ≠ 0)
    (hsub : q.primeFactors ⊆ (n * (n + 1)).primeFactors)
    (hloc : ExactLocalResultantBound n q) :
    Real.log (q : ℝ) ≤ (((n : ℝ) + 1) / 8 - 2) *
        (Real.log ((n : ℝ) * ((n : ℝ) + 1)) / 2) + ((n : ℝ) + 1) * C8 := by
  apply exponent_budget8 (n * (n + 1)).primeFactors
    (fun p => padicValNat p (n * (n + 1)))
    (fun p hp => (Nat.mem_primeFactors.mp hp).1)
    ((n : ℝ) + 1) (Real.log ((n : ℝ) * ((n : ℝ) + 1)) / 2)
    (Real.log (q : ℝ))
  · have hnr : (15 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      halfBudget_primeFactors_le (n * (n + 1))
  · exact log_bound_by_prime_layers hq hsub hloc

theorem log_bound_repeated_prime_sum {n q : ℕ} (hn : 0 < n) (hq : q ≠ 0)
    (hsub : q.primeFactors ⊆ (n * (n + 1)).primeFactors)
    (hloc : ExactLocalResultantBound n q) :
    Real.log (q : ℝ) ≤ ((n : ℝ) + 1) *
      UniversalScalar.repeatedPrimeSum
        (UniversalScalar.repeatedPrimeSupport (n * (n + 1))) := by
  classical
  let P := (n * (n + 1)).primeFactors
  let Q := UniversalScalar.repeatedPrimeSupport (n * (n + 1))
  have hsum := log_nat_eq_sum_padic_on hq P
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) hsub
  have hrestrict : (∑ p ∈ P, (padicValNat p q : ℝ) * Real.log (p : ℝ)) =
      ∑ p ∈ Q, (padicValNat p q : ℝ) * Real.log (p : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hmem := Nat.mem_primeFactors.mp hp
    have hnsq : ¬ p ^ 2 ∣ n * (n + 1) := by
      simpa only [Q, UniversalScalar.repeatedPrimeSupport, Finset.mem_filter,
        hp, true_and] using hnot
    rw [local_valuation_zero_of_not_square hn hloc hmem.1 hmem.2.1 hnsq]
    simp
  rw [hsum, hrestrict]
  unfold UniversalScalar.repeatedPrimeSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpp := UniversalScalar.repeatedPrimeSupport_prime hp
  have hpd := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).2.1
  have hb := local_bound_normalized hloc hpp hpd
  have hgeom := layerSum_le_geometric p hpp.two_le
    (padicValNat p (n * (n + 1)) / 2)
  have hgeomN := mul_le_mul_of_nonneg_left hgeom
    (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
  have hvaluation : (padicValNat p q : ℝ) ≤
      ((n : ℝ) + 1) * ((p : ℝ) / ((p : ℝ) ^ 2 - 1)) := by
    have hh : (0 : ℝ) ≤ ((padicValNat p (n * (n + 1)) / 2 : ℕ) : ℝ) := by positivity
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hvaluation (log_nat_nonneg p)
  unfold UniversalScalar.repeatedPrimeWeight
  convert hh using 1 ; ring

end EventualIrreducibility.UniversalResultantBudget

open Polynomial
open scoped BigOperators

namespace EventualIrreducibility

open UniversalResultantBudget UniversalLocalDraft

noncomputable def FactorSeries.crossResultantNat {n : ℕ}
    (s : FactorSeries n) (h : ℤ[X]) : ℕ :=
  (s.factor.resultant h s.factor.natDegree h.natDegree).natAbs

lemma FactorSeries.log_crossResultantNat {n : ℕ}
    (s : FactorSeries n) (h : ℤ[X]) :
    Real.log (s.crossResultantNat h : ℝ) =
      Real.log |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| := by
  simp only [FactorSeries.crossResultantNat, Nat.cast_natAbs, Int.cast_abs]

theorem FactorSeries.nat_discriminant_resultant_identity {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) (h : ℤ[X])
    (hh : s.factor * h = fInt n) :
    s.factor.discr.natAbs * s.crossResultantNat h *
        (s.factor.coeff 0).natAbs * (s.factor.eval 1).natAbs =
      (n * (n + 1)) ^ s.factor.natDegree := by
  obtain ⟨d, alpha, hd, _hne, hprod, _hmod, _hconst, _hlog, _htrace⟩ :=
    s.exists_J_root_data hn
  subst d
  have htri : (X - 1) ^ 2 * (s.factor * h) =
      X ^ (n + 1) - C ((n + 1 : ℕ) : ℤ) * X + C (n : ℤ) := by
    rw [hh]
    exact trinomial_identity n
  have hid := UniversalIrreducibility.integer_discriminant_resultant_identity
    n s.factor h s.monic s.degree_pos alpha hprod htri
  have hcast : ((s.factor.discr.natAbs * s.crossResultantNat h *
        (s.factor.coeff 0).natAbs * (s.factor.eval 1).natAbs : ℕ) : ℝ) =
      (((n * (n + 1)) ^ s.factor.natDegree : ℕ) : ℝ) := by
    simpa only [FactorSeries.crossResultantNat, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_add, Nat.cast_one, Nat.cast_natAbs, Int.cast_abs] using hid
  exact_mod_cast hcast

theorem FactorSeries.crossResultantNat_positive_dvd {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) (h : ℤ[X])
    (hh : s.factor * h = fInt n) :
    0 < s.crossResultantNat h ∧
      s.crossResultantNat h ∣ (n * (n + 1)) ^ s.factor.natDegree := by
  have hid := s.nat_discriminant_resultant_identity hn h hh
  have hpow : 0 < (n * (n + 1)) ^ s.factor.natDegree := by positivity
  constructor
  · by_contra hz
    have hq0 : s.crossResultantNat h = 0 := by omega
    rw [hq0, mul_zero, zero_mul, zero_mul] at hid
    omega
  · refine ⟨s.factor.discr.natAbs * (s.factor.coeff 0).natAbs *
      (s.factor.eval 1).natAbs, ?_⟩
    rw [← hid]
    ring

theorem FactorSeries.crossResultant_prime_support {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) (h : ℤ[X])
    (hh : s.factor * h = fInt n) :
    (s.crossResultantNat h).primeFactors ⊆ (n * (n + 1)).primeFactors := by
  exact primeFactors_subset_of_dvd_power (by positivity)
    (s.crossResultantNat_positive_dvd hn h hh).2

theorem FactorSeries.resultant_log_budgets {n : ℕ}
    (s : FactorSeries n) (hn : 15 ≤ n) (h : ℤ[X])
    (hh : s.factor * h = fInt n)
    (hlocal : ExactLocalResultantBound n (s.crossResultantNat h)) :
    Real.log |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| ≤
        (((n : ℝ) + 1) / 8 - 2) *
          (Real.log ((n : ℝ) * ((n : ℝ) + 1)) / 2) + ((n : ℝ) + 1) * C8 ∧
      Real.log |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| ≤
        ((n : ℝ) + 1) * UniversalScalar.repeatedPrimeSum
          (UniversalScalar.repeatedPrimeSupport (n * (n + 1))) := by
  have hnpos : 0 < n := by omega
  have hq := (s.crossResultantNat_positive_dvd hnpos h hh).1.ne'
  have hs := s.crossResultant_prime_support hnpos h hh
  constructor
  · simpa only [s.log_crossResultantNat h] using
      log_bound_exponent_budget8 hn hq hs hlocal
  · simpa only [s.log_crossResultantNat h] using
      log_bound_repeated_prime_sum hnpos hq hs hlocal

lemma budget_C8_lt_thirteen_twentieths : C8 < (13 / 20 : ℝ) := by
  exact C8_lt_of_log_bounds
    (by linarith [UniversalScalar.log_two_rational_bounds.2])
    UniversalScalar.log_three_lt UniversalScalar.log_five_lt UniversalScalar.log_seven_lt

theorem FactorSeries.resultant_and_evaluation_closure_inputs {n : ℕ}
    (s : FactorSeries n) (hn : 15 ≤ n) (h : ℤ[X])
    (hh : s.factor * h = fInt n)
    (hlocal : ExactLocalResultantBound n (s.crossResultantNat h)) :
    C8 ≤ (13 / 20 : ℝ) ∧
      Real.log |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| ≤
        (((n : ℝ) + 1) / 8 - 2) *
          (Real.log ((n : ℝ) * ((n : ℝ) + 1)) / 2) + ((n : ℝ) + 1) * C8 ∧
      Real.log |((s.factor.eval 1 : ℤ) : ℝ)| ≤
        2 * (Real.log ((n : ℝ) * ((n : ℝ) + 1)) / 2) - Real.log 2 ∧
      Real.log |(s.factor.resultant h s.factor.natDegree h.natDegree : ℝ)| ≤
        ((n : ℝ) + 1) * UniversalScalar.repeatedPrimeSum
          (UniversalScalar.repeatedPrimeSupport (n * (n + 1))) ∧
      Real.log |((s.factor.eval 1 : ℤ) : ℝ)| ≤ 2 * Real.log (n : ℝ) := by
  obtain ⟨hR8, hRS⟩ := s.resultant_log_budgets hn h hh hlocal
  obtain ⟨hF8, hFS⟩ := s.eval_one_log_closure_bounds (by omega)
  exact ⟨budget_C8_lt_thirteen_twentieths.le, hR8, hF8, hRS, hFS.le⟩

end EventualIrreducibility

open Polynomial
open scoped BigOperators

namespace EventualIrreducibility

open UniversalResultantBudget UniversalLocalDraft

theorem FactorSeries.log_constant_degree_constraint {n : ℕ}
    (s : FactorSeries n) (hn : 0 < n) :
    Real.log (s.factor.coeff 0 : ℝ) <
      ((s.factor.natDegree : ℝ) / (n : ℝ)) * Real.log (2 * (n : ℝ) + 1) := by
  obtain ⟨d, alpha, hd, _hne, _hprod, hmod, hconst, hlog, _htrace⟩ :=
    s.exists_J_root_data hn
  subst d
  exact UniversalScalar.root_log_degree_constraint s.degree_pos
    (fun i => ‖alpha i‖) (fun i => lt_trans zero_lt_one (hmod i)) hconst hlog

theorem FactorSeries.firstDifference_prime_support {n : ℕ}
    (s t : FactorSeries n) (hn : 0 < n)
    (hprod : s.factor * t.factor = fInt n) :
    ∀ p : ℕ, p.Prime → p ∣ t.constantNat * (n + 1) →
      (p : ℤ) ∣ s.firstDifference := by
  intro p hp hpd
  have hb := t.two_le_constantNat hn
  have hM0 : t.constantNat * (n + 1) ≠ 0 := by positivity
  have hpr := UniversalConstants.prime_dvd_supportRadical hp hpd hM0
  have hprZ : (p : ℤ) ∣
      (UniversalConstants.supportRadical (t.constantNat * (n + 1)) : ℤ) := by
    exact_mod_cast hpr
  exact dvd_trans hprZ (s.radical_dvd_firstDifference t hn hprod)

theorem FactorSeries.no_small_pair_of_constants_and_local_bound {n : ℕ}
    (s t : FactorSeries n) (hn : 0 < n)
    (hprod : s.factor * t.factor = fInt n)
    (hsmall : 2 * s.factor.natDegree < n)
    (ha13 : 13 ≤ s.constantNat) (hn182 : 182 ≤ n)
    (hlocal : ExactLocalResultantBound n (s.crossResultantNat t.factor)) : False := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn182R : (182 : ℝ) ≤ n := by exact_mod_cast hn182
  have hdelta0 : (0 : ℝ) ≤ (s.factor.natDegree : ℝ) / (n : ℝ) := by positivity
  have hdelta1 : (s.factor.natDegree : ℝ) / (n : ℝ) < (1 / 2 : ℝ) := by
    have hsR : (2 : ℝ) * (s.factor.natDegree : ℝ) < n := by exact_mod_cast hsmall
    apply (div_lt_iff₀ hnR).2
    nlinarith
  have haR : (13 : ℝ) ≤ (s.factor.coeff 0 : ℝ) := by
    have h : (13 : ℝ) ≤ (s.constantNat : ℝ) := by exact_mod_cast ha13
    simpa only [s.constantNat_real hn] using h
  have hA : (51 / 20 : ℝ) ≤ Real.log (s.factor.coeff 0 : ℝ) :=
    (UniversalScalar.log_factor_constant_lower haR).le
  have hAL := s.log_constant_degree_constraint hn
  have hB := UniversalScalar.half_log_successive_product_le hnR
  obtain ⟨hC, hRbudget, hFbudget, hRsupport, hFsupport⟩ :=
    s.resultant_and_evaluation_closure_inputs (by omega : 15 ≤ n)
      t.factor hprod hlocal
  by_cases hnlarge : 1000 ≤ n
  · obtain ⟨ha, hb, hnprod, hab, _⟩ := s.partner_constant_data t hn hprod
    obtain ⟨hKpos, hKhi, hJkernel⟩ := s.firstDifference_kernel_data hnlarge
    have hJbound : (s.firstDifference.natAbs : ℝ) ≤
        (2 + (Real.log (2 * (n : ℝ) + 1) / (n : ℝ)) ^ 2) *
          (s.constantNat : ℝ) * Real.log (s.constantNat : ℝ) := by
      simpa only [s.constantNat_real hn] using hJkernel
    obtain ⟨hSglobal, hSfactor, hz, _hRsame⟩ :=
      UniversalScalar.actual_support_closure_inputs s.firstDifference hnlarge
        (by omega : 1 < s.constantNat) (by omega : 0 < t.constantNat)
        hnprod hab (s.firstDifference_ne_zero hn)
        (s.firstDifference_prime_support t hn hprod)
        hKpos hKhi hJbound hRsupport
    rw [s.constantNat_real hn] at hSfactor hz
    exact UniversalScalar.large_closure_from_resultants
      (by exact_mod_cast hnlarge) hA hdelta0 hdelta1 hAL hB hC
      hRbudget hFbudget hSglobal hSfactor hz hRsupport hFsupport
      (s.energy_outer hn t.factor hprod)
  · have hnlt : n < 1000 := by omega
    exact UniversalScalar.bridge_closure_from_resultants
      hn182R (by exact_mod_cast hnlt) hA hdelta0 hdelta1 hAL hB hC
      hRbudget hFbudget
      (s.energy_inner (by omega : 8 ≤ n) t.factor hprod)

theorem FactorSeries.no_small_pair_of_non_prime_power {n : ℕ}
    (s t : FactorSeries n) (hn : 0 < n)
    (hprod : s.factor * t.factor = fInt n)
    (hsmall : 2 * s.factor.natDegree < n)
    (hpp : ¬ IsPrimePow (n + 1))
    (hlocal : ExactLocalResultantBound n (s.crossResultantNat t.factor)) : False := by
  have ha13 := s.thirteen_le_constantNat_of_partner t hn hprod hpp
  have hn182 := s.parameter_ge_182_of_partner t hn hprod hpp
  exact s.no_small_pair_of_constants_and_local_bound t hn hprod hsmall ha13 hn182 hlocal

def UniversalPrimePowerSuccessorCase : Prop :=
  ∀ n : ℕ, 2 ≤ n → IsPrimePow (n + 1) → Irreducible (fQ n)

def UniversalActualLocalResultantCase : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ s t : FactorSeries n,
    s.factor * t.factor = fInt n →
      ExactLocalResultantBound n (s.crossResultantNat t.factor)

theorem universal_irreducible_of_prime_power_and_local_resultant
    (hprimePower : UniversalPrimePowerSuccessorCase)
    (hlocal : UniversalActualLocalResultantCase)
    (n : ℕ) (hn : 2 ≤ n) : Irreducible (fQ n) := by
  by_contra hred
  have hpp : ¬ IsPrimePow (n + 1) := fun hp => hred (hprimePower n hn hp)
  obtain ⟨s, t, hprod, hsmall, _hdegree⟩ := exists_small_factor_pair n hn hred
  exact s.no_small_pair_of_non_prime_power t (by omega) hprod hsmall hpp
    (hlocal n hn s t hprod)

end EventualIrreducibility

open Polynomial

namespace EventualIrreducibility.UniversalActualPacketBuildersDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalOrdinaryFacesDraft
  UniversalResidueOneProfileDraft UniversalResidueOneFacesDraft
  UniversalResidueOneExtractionDraft UniversalZeroPacketDraft UniversalLocalDraft FirstFace

variable {E : Type u} [NormedField E] [CompleteSpace E]
    {v : AbsoluteValue E ℝ}

def SlopeFactorData.retarget {P P' : E[X]} {c : ℝ} {i j : ℕ}
    (D : SlopeFactorData P v c i j) (h : P' = P) : SlopeFactorData P' v c i j where
  Q := D.Q
  R := D.R
  monic_Q := D.monic_Q
  monic_R := D.monic_R
  factorization := h.trans D.factorization
  degree_Q := D.degree_Q
  pure_Q := D.pure_Q
  rest_min := D.rest_min
  rest_max := D.rest_max

def actualOrdinaryPacket (n : ℕ) (hna : IsNonarchimedean v)
    (ζ : E) (hsep : v (1 - ζ) = 1) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (i j : ℕ) (D : SlopeFactorData (shiftedTrinomial n ζ) v c i j) :
    LocatedPacket ((fInt n).map (Int.castRingHom E)) v := by
  let P : E[X] := (fInt n).map (Int.castRingHom E)
  let F : E[X] := X ^ (n + 1) - C ((n + 1 : ℕ) : E) * X + C (n : E)
  have hF : F = (X - 1) ^ 2 * P := by
    symm
    simpa only [P, F, Nat.cast_add, Nat.cast_one] using
      Simplicity.mapped_trinomial_from_integer (K := E) (trinomial_identity n)
  have hcomp : F.comp (X + C ζ) = shiftedTrinomial n ζ := by
    exact (shiftedTrinomial_eq_comp n ζ).symm
  exact ordinary_packet_of_slope hna P F hF ζ hsep c hc hc1 i j
    (EventualIrreducibility.UniversalActualPacketBuildersDraft.SlopeFactorData.retarget D hcomp)

omit [CompleteSpace E] in
lemma actualOrdinaryPacket_degree (n : ℕ) (hna : IsNonarchimedean v)
    (ζ : E) (hsep : v (1 - ζ) = 1) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (i j : ℕ) (D : SlopeFactorData (shiftedTrinomial n ζ) v c i j) :
    (actualOrdinaryPacket n hna ζ hsep c hc hc1 i j D).Q.natDegree = j - i := by
  change (D.Q.comp (X - C ζ)).natDegree = j - i
  rw [unshift_natDegree, D.degree_Q]

def actualOnePacket (n : ℕ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (i j : ℕ) (D : SlopeFactorData (oneTranslate n : E[X]) v c i j) :
    LocatedPacket ((fInt n).map (Int.castRingHom E)) v :=
  packet_of_shift_slope ((fInt n).map (Int.castRingHom E)) 1 c hc hc1 i j
    (EventualIrreducibility.UniversalActualPacketBuildersDraft.SlopeFactorData.retarget D
      (oneTranslate_eq_comp n).symm)

omit [CompleteSpace E] in
lemma actualOnePacket_degree (n : ℕ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (i j : ℕ) (D : SlopeFactorData (oneTranslate n : E[X]) v c i j) :
    (actualOnePacket n c hc hc1 i j D).Q.natDegree = j - i := by
  change (D.Q.comp (X - C 1)).natDegree = j - i
  rw [unshift_natDegree, D.degree_Q]

lemma ordinaryDenom_eq_packetWeight (p i : ℕ) :
    ordinaryDenom p i = packetWeight p 0 i := by
  cases i with
  | zero => simp [ordinaryDenom, packetWeight]
  | succ i => simp [ordinaryDenom, packetWeight]

theorem actual_ordinary_odd_located
    (hstd : StandardSlopeFactorInput.{u}) (hna : IsNonarchimedean v)
    (hmetric : ∀ x : E, v x = ‖x‖)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (n p r : ℕ) (hn : 0 < n) (hp : p.Prime) (hpodd : p ≠ 2) (hr : 1 ≤ r)
    (ζ : E)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (hz : v ζ = 1) (hsep : v (1 - ζ) = 1)
    (hsource : OrdinaryRootSource n p r ζ) (i : ℕ) (hi : i < r) :
    ∃ A : LocatedPacket ((fInt n).map (Int.castRingHom E)) v,
      A.center = ζ ∧ A.radius = Real.exp (-(1 : ℝ) / (packetWeight p 0 i : ℝ)) ∧
        A.Q.natDegree = packetWeight p 0 i ∧ Irreducible A.Q := by
  obtain ⟨D, _⟩ := actual_ordinary_odd_packet hstd hna hmetric hdiscrete
    n p r hn hp hpodd hr ζ hnorm hz hsep hsource i hi
  have hepos := ordinaryDenom_pos p i hp.two_le
  let A := actualOrdinaryPacket n hna ζ hsep
    (Real.exp (-(1 : ℝ) / (ordinaryDenom p i : ℝ))) (Real.exp_pos _)
    (exp_radius_lt_one _ hepos) (ordinaryLeft p i) (ordinaryRight p i) D
  have hdegree : A.Q.natDegree = ordinaryDenom p i := by
    rw [actualOrdinaryPacket_degree, ordinary_width]
  have hirr := A.irreducible_of_degree _ hna (ordinaryDenom p i) hepos rfl hdegree hdiscrete
  refine ⟨A, rfl, ?_, ?_, hirr⟩
  · change Real.exp (-(1 : ℝ) / (ordinaryDenom p i : ℝ)) = _
    rw [ordinaryDenom_eq_packetWeight]
  · simpa only [ordinaryDenom_eq_packetWeight] using hdegree

theorem actual_one_odd_located
    (hstd : StandardSlopeFactorInput.{u}) (hna : IsNonarchimedean v)
    (hmetric : ∀ x : E, v x = ‖x‖)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (n p r : ℕ) (hn : 0 < n) (hp : p.Prime) (hpodd : p ≠ 2) (hr : 1 ≤ r)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (hsource : padicValNat p n = r ∨ padicValNat p (n + 1) = r)
    (i : ℕ) (hi : i < r) :
    ∃ A : LocatedPacket ((fInt n).map (Int.castRingHom E)) v,
      A.center = 1 ∧ A.radius = Real.exp (-(1 : ℝ) / (packetWeight p 2 i : ℝ)) ∧
        A.Q.natDegree = packetWeight p 2 i ∧ Irreducible A.Q := by
  by_cases hi0 : i = 0
  · subst i
    have hepos : 0 < p - 2 := by have := hp.two_le; omega
    obtain ⟨D, _⟩ := actual_one_odd_first_packet hstd hna hmetric hdiscrete
      n p r hn hp hpodd hr hnorm hsource
    let A := actualOnePacket n (Real.exp (-(1 : ℝ) / ((p - 2 : ℕ) : ℝ)))
      (Real.exp_pos _) (exp_radius_lt_one _ hepos) 0 (p - 2) D
    have hdegree : A.Q.natDegree = p - 2 := by
      rw [actualOnePacket_degree, Nat.sub_zero]
    have hirr := A.irreducible_of_degree _ hna (p - 2) hepos rfl hdegree hdiscrete
    exact ⟨A, rfl, rfl, hdegree, hirr⟩
  · have hi1 : 1 ≤ i := by omega
    have hepos := laterDenom_pos p i hp.two_le
    obtain ⟨D, _⟩ := actual_one_later_packet hstd hna hmetric hdiscrete
      n p r i hn hp hr hi1 hi hnorm hsource
    let A := actualOnePacket n (Real.exp (-(1 : ℝ) / (laterDenom p i : ℝ)))
      (Real.exp_pos _) (exp_radius_lt_one _ hepos) (p ^ i - 2) (p ^ (i + 1) - 2) D
    have hdegree : A.Q.natDegree = laterDenom p i := by
      rw [actualOnePacket_degree, residue_one_later_width p i hp.two_le hi1]
    have heq : laterDenom p i = packetWeight p 2 i := by
      cases i with
      | zero => omega
      | succ j => rfl
    have hirr := A.irreducible_of_degree _ hna (laterDenom p i) hepos rfl hdegree hdiscrete
    refine ⟨A, rfl, ?_, ?_, hirr⟩
    · change Real.exp (-(1 : ℝ) / (laterDenom p i : ℝ)) = _
      rw [heq]
    · exact hdegree.trans heq

omit [CompleteSpace E] in
lemma gaussNorm_one_value (c : ℝ) : (1 : E[X]).gaussNorm v c = 1 := by
  simpa only [Polynomial.C_1, map_one] using Polynomial.gaussNorm_C v c (1 : E)

def unitLocatedPacket (P : E[X]) (ζ : E) : LocatedPacket P v where
  Q := 1
  monic := Polynomial.monic_one
  divides := one_dvd P
  center := ζ
  radius := Real.exp (-1)
  radius_pos := Real.exp_pos _
  radius_lt_one := Real.exp_lt_one_iff.mpr (by norm_num)
  pure_shift := by
    rw [Polynomial.one_comp]
    constructor
    · constructor
      · simp [gaussNorm_one_value]
      · intro j hj; omega
    · constructor
      · simp [gaussNorm_one_value]
      · intro j hj
        have hj0 : j ≠ 0 := by simpa using Nat.ne_of_gt hj
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj]
        simp [gaussNorm_one_value]

theorem actual_zero_located
    (hstd : StandardSlopeFactorInput.{u}) (hna : IsNonarchimedean v)
    (hmetric : ∀ x : E, v x = ‖x‖)
    (n p r : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hr : 1 ≤ r)
    (hval : padicValNat p n = r)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ))) :
    ∃ A : LocatedPacket ((fInt n).map (Int.castRingHom E)) v,
      A.center = 0 ∧ A.radius = Real.exp (-(r : ℝ)) ∧ A.Q.natDegree = 1 := by
  obtain ⟨D, hd⟩ := actual_zero_linear_packet hstd hna hmetric n p r hn hp hr hval hnorm
  have hc1 : Real.exp (-(r : ℝ)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    linarith
  refine ⟨{
    Q := D.Q
    monic := D.monic_Q
    divides := ⟨D.R, D.factorization⟩
    center := 0
    radius := Real.exp (-(r : ℝ))
    radius_pos := Real.exp_pos _
    radius_lt_one := hc1
    pure_shift := by simpa using D.pure_Q
  }, rfl, rfl, hd⟩

end EventualIrreducibility.UniversalActualPacketBuildersDraft

open Polynomial

namespace EventualIrreducibility.UniversalOddFamilyDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalPacketAllocationDraft
  UniversalActualPacketBuildersDraft UniversalOrdinaryFacesDraft UniversalLocalDraft FirstFace

lemma packetWeight_pos (p δ i : ℕ) (hp : 2 ≤ p) (hδ : δ < p) :
    0 < packetWeight p δ i := by
  cases i with
  | zero => simp only [packetWeight]; omega
  | succ i =>
    exact mul_pos (pow_pos (by omega) _) (by omega)

lemma packetWeight_strictMono (p δ : ℕ) (hp : 3 ≤ p) (_hδ : δ ≤ p) :
    StrictMono (packetWeight p δ) := by
  apply strictMono_nat_of_lt_succ
  intro i
  cases i with
  | zero =>
    change p - δ < p ^ (0 + 1) * (p - 1)
    rw [pow_one]
    have hmul : p * 1 < p * (p - 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    exact lt_of_le_of_lt (Nat.sub_le p δ) (by simpa only [mul_one] using hmul)
  | succ i =>
    have hpos : 0 < p ^ (i + 1) * (p - 1) :=
      mul_pos (pow_pos (by omega) _) (by omega)
    change p ^ (i + 1) * (p - 1) < p ^ (i + 1 + 1) * (p - 1)
    have hmul := Nat.mul_lt_mul_of_pos_left (show 1 < p by omega) hpos
    calc
      p ^ (i + 1) * (p - 1) < p * (p ^ (i + 1) * (p - 1)) := by
        simpa only [mul_one, mul_comm p] using hmul
      _ = p ^ (i + 1 + 1) * (p - 1) := by rw [pow_succ]; ring

lemma packetRadius_injective (p δ : ℕ) (hp : 3 ≤ p) (hδ : δ < p) :
    Function.Injective (fun i => Real.exp (-(1 : ℝ) / (packetWeight p δ i : ℝ))) := by
  apply StrictMono.injective
  intro i j hij
  exact exp_radius_strict_of_denominators (packetWeight p δ i) (packetWeight p δ j)
    (packetWeight_pos p δ i (by omega) hδ) (packetWeight_strictMono p δ hp hδ.le hij)

lemma sum_packetWeight_fin (p δ r : ℕ) (hp : 1 ≤ p) (hδ : δ ≤ p) (hr : 1 ≤ r) :
    (∑ i : Fin r, packetWeight p δ i) + δ = p ^ r := by
  have h := packet_prefix p δ hp hδ (r - 1)
  rw [Nat.sub_add_cancel hr] at h
  simpa only [prefixWeight, Fin.sum_univ_eq_sum_range] using h

abbrev OddIndex (m r : ℕ) := Unit ⊕ (Fin m × Fin r)

theorem actual_odd_residue_packets
    (hstd : StandardSlopeFactorInput.{0})
    (n p r m : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hpodd : p ≠ 2) (hr : 1 ≤ r)
    (D : PrimeToPUnramifiedData p m) (one : Fin m) (hone : D.ζ one = 1)
    (hsource : (padicValNat p n = r ∧ n = p ^ r * m) ∨
      (padicValNat p (n + 1) = r ∧ n + 1 = p ^ r * m)) :
    ∃ A : Fin m → Fin r → LocatedPacket ((fInt n).map (Int.castRingHom D.E)) D.v,
      (∀ a i, (A a i).center = D.ζ a) ∧
      (∀ a i, (A a i).radius =
        Real.exp (-(1 : ℝ) / (packetWeight p (if a = one then 2 else 0) i : ℝ))) ∧
      (∀ a i, (A a i).Q.natDegree = packetWeight p (if a = one then 2 else 0) i) ∧
      (∀ a i, Irreducible (A a i).Q) := by
  classical
  have hval : padicValNat p n = r ∨ padicValNat p (n + 1) = r :=
    hsource.imp And.left And.left
  have hrootSource (a : Fin m) : OrdinaryRootSource n p r (D.ζ a) := by
    rcases hsource with ⟨hv, heq⟩ | ⟨hv, heq⟩
    · left
      refine ⟨hv, root_of_dividing_exponent (D.ζ a) m n ?_ (D.roots a)⟩
      exact ⟨p ^ r, by simpa only [Nat.mul_comm] using heq⟩
    · right
      refine ⟨hv, root_of_dividing_exponent (D.ζ a) m (n + 1) ?_ (D.roots a)⟩
      exact ⟨p ^ r, by simpa only [Nat.mul_comm] using heq⟩
  have hexists (a : Fin m) (i : Fin r) :
      ∃ A : LocatedPacket ((fInt n).map (Int.castRingHom D.E)) D.v,
        A.center = D.ζ a ∧ A.radius =
          Real.exp (-(1 : ℝ) / (packetWeight p (if a = one then 2 else 0) i : ℝ)) ∧
        A.Q.natDegree = packetWeight p (if a = one then 2 else 0) i ∧ Irreducible A.Q := by
    by_cases ha : a = one
    · subst a
      simpa only [hone, if_true] using actual_one_odd_located hstd D.nonarchimedean
        D.norm_eq D.discrete n p r (by omega) hp hpodd hr D.nat_norm hval i i.isLt
    · have hsep : D.v (1 - D.ζ a) = 1 := by
        simpa only [hone] using D.separated one a (Ne.symm ha)
      simpa only [if_neg ha] using actual_ordinary_odd_located hstd D.nonarchimedean
        D.norm_eq D.discrete n p r (by omega) hp hpodd hr (D.ζ a)
        D.nat_norm (D.units a) hsep (hrootSource a) i i.isLt
  choose A hc hr hd hi using hexists
  exact ⟨A, hc, hr, hd, hi⟩

theorem odd_residue_degree_sum
    (p r m : ℕ) (hp : 2 ≤ p) (hr : 1 ≤ r) (one : Fin m) :
    (∑ a : Fin m, ∑ i : Fin r, packetWeight p (if a = one then 2 else 0) i) + 2 =
      m * p ^ r := by
  classical
  have hrow (a : Fin m) :
      (∑ i : Fin r, packetWeight p (if a = one then 2 else 0) i) +
        (if a = one then 2 else 0) = p ^ r := by
    exact sum_packetWeight_fin p _ r (by omega) (by split_ifs <;> omega) hr
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin m))) rfl (fun a _ => hrow a)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using hsum

theorem actual_odd_common_field_product
    (hstd : StandardSlopeFactorInput.{0}) (hspl : StandardValuedSplittingInput.{0})
    (n p r m : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hpodd : p ≠ 2) (hr : 1 ≤ r)
    (D : PrimeToPUnramifiedData p m)
    (hsource : (padicValNat p n = r ∧ n = p ^ r * m) ∨
      (padicValNat p (n + 1) = r ∧ n + 1 = p ^ r * m)) :
    ∃ one : Fin m,
    ∃ B : OddIndex m r → LocatedPacket ((fInt n).map (Int.castRingHom D.E)) D.v,
      D.ζ one = 1 ∧
      (∀ a i, (B (.inr (a,i))).center = D.ζ a) ∧
      (∀ a i, (B (.inr (a,i))).radius =
        Real.exp (-(1 : ℝ) / (packetWeight p (if a = one then 2 else 0) i : ℝ))) ∧
      (∀ a i, (B (.inr (a,i))).Q.natDegree = packetWeight p (if a = one then 2 else 0) i) ∧
      (∀ a i, Irreducible (B (.inr (a,i))).Q) ∧
      (B (.inl ())).center = 0 ∧ (B (.inl ())).Q.natDegree ≤ 1 ∧
      Pairwise (fun i j =>
        ((B i).center = (B j).center ∧ (B i).radius ≠ (B j).radius) ∨
          D.v ((B i).center - (B j).center) = 1) ∧
      ((fInt n).map (Int.castRingHom D.E)) = ∏ q, (B q).Q := by
  classical
  let P : D.E[X] := (fInt n).map (Int.castRingHom D.E)
  have hP : P.Monic := (monic_fInt n (by omega)).map (Int.castRingHom D.E)
  obtain ⟨one, hone⟩ := D.one_root
  obtain ⟨A, hcenter, hradius, hdegree, hirr⟩ :=
    actual_odd_residue_packets hstd n p r m hn hp hpodd hr D one hone hsource
  have hZ : ∃ Z : LocatedPacket P D.v, Z.center = 0 ∧ Z.Q.natDegree ≤ 1 ∧
      ((∑ a : Fin m, ∑ i : Fin r, (A a i).Q.natDegree) + Z.Q.natDegree = n - 1) := by
    have hsum : (∑ a : Fin m, ∑ i : Fin r, (A a i).Q.natDegree) + 2 = m * p ^ r := by
      simpa only [hdegree] using odd_residue_degree_sum p r m hp.two_le hr one
    rcases hsource with ⟨hv, heq⟩ | ⟨hv, heq⟩
    · obtain ⟨Z, hc, _, hd⟩ := actual_zero_located hstd D.nonarchimedean
        D.norm_eq n p r hn hp hr hv D.nat_norm
      refine ⟨Z, hc, by omega, ?_⟩
      rw [hd]
      have hm : m * p ^ r = n := by nlinarith [heq]
      omega
    · refine ⟨unitLocatedPacket P 0, rfl, by simp [unitLocatedPacket], ?_⟩
      change (∑ a : Fin m, ∑ i : Fin r, (A a i).Q.natDegree) + (1 : D.E[X]).natDegree = n - 1
      have hm : m * p ^ r = n + 1 := by nlinarith [heq]
      simp only [Polynomial.natDegree_one, add_zero]
      omega
  obtain ⟨Z, hZcenter, hZsmall, hZdegree⟩ := hZ
  let B : OddIndex m r → LocatedPacket P D.v := Sum.elim (fun _ => Z) (fun q => A q.1 q.2)
  have hBdegree : ∑ q, (B q).Q.natDegree = P.natDegree := by
    simp only [B, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique,
      Sum.elim_inl, Sum.elim_inr]
    rw [Polynomial.Monic.natDegree_map (monic_fInt n (by omega)), natDegree_fInt n (by omega)]
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hBsep : Pairwise (fun i j =>
      ((B i).center = (B j).center ∧ (B i).radius ≠ (B j).radius) ∨
        D.v ((B i).center - (B j).center) = 1) := by
    intro q t hqt
    cases q with
    | inl u =>
      cases t with
      | inl v => exact False.elim (hqt (by cases u; cases v; rfl))
      | inr ai =>
        right
        simpa only [B, Sum.elim_inl, Sum.elim_inr, hZcenter, hcenter,
          zero_sub, AbsoluteValue.map_neg] using D.units ai.1
    | inr ai =>
      cases t with
      | inl u =>
        right
        simpa only [B, Sum.elim_inl, Sum.elim_inr, hZcenter, hcenter, sub_zero] using D.units ai.1
      | inr bj =>
        by_cases hab : ai.1 = bj.1
        · left
          refine ⟨by simp only [B, Sum.elim_inr, hcenter, hab], ?_⟩
          have hij : ai.2 ≠ bj.2 := by
            intro h
            apply hqt
            exact congrArg Sum.inr (Prod.ext hab h)
          have hδ : (if ai.1 = one then 2 else 0) < p := by split_ifs <;> omega
          have hinj := packetRadius_injective p (if ai.1 = one then 2 else 0) hp3 hδ
          intro heq
          apply hij
          apply Fin.ext
          apply hinj
          simpa only [B, Sum.elim_inr, hradius, hab] using heq
        · right
          simpa only [B, Sum.elim_inr, hcenter] using D.separated ai.1 bj.1 hab
  obtain ⟨S⟩ := hspl D.E D.v D.nonarchimedean D.norm_eq P hP.ne_zero
  have hproduct := located_packet_product P hP B (algebraMap D.E S.K)
    S.restrict S.nonarchimedean S.splits hBsep hBdegree
  refine ⟨one, B, hone, ?_, ?_, ?_, ?_, hZcenter, hZsmall, hBsep, hproduct⟩
  · exact hcenter
  · exact hradius
  · exact hdegree
  · exact hirr

end EventualIrreducibility.UniversalOddFamilyDraft

open Polynomial

namespace EventualIrreducibility.UniversalBinaryFamilyBuildersDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalOrdinaryFacesDraft
  UniversalActualPacketBuildersDraft UniversalBinaryQuarticDraft
  UniversalResidueOneProfileDraft UniversalResidueOneFacesDraft
  UniversalResidueOneExtractionDraft FirstFace UniversalLocalDraft

def binaryCount (r : ℕ) : ℕ := if r = 1 then 1 else r - 1
def binaryDenom (i : ℕ) : ℕ := 2 ^ (i + 1)
def mergedWeight (δ : ℕ) : ℕ → ℕ
  | 0 => 4 - δ
  | i + 1 => 2 ^ (i + 2)
def binaryWeight (δ r i : ℕ) : ℕ :=
  if r = 1 then packetWeight 2 δ i else mergedWeight δ i

lemma binaryCount_pos (r : ℕ) (hr : 1 ≤ r) : 0 < binaryCount r := by
  unfold binaryCount
  split_ifs <;> omega

lemma binaryDenom_pos (i : ℕ) : 0 < binaryDenom i := pow_pos (by omega) _

lemma binaryDenom_strictMono : StrictMono binaryDenom := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hp := binaryDenom_pos i
  unfold binaryDenom at *
  rw [pow_succ]
  omega

lemma binaryRadius_injective : Function.Injective
    (fun i => Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ))) := by
  apply StrictMono.injective
  intro i j hij
  exact exp_radius_strict_of_denominators _ _ (binaryDenom_pos i)
    (binaryDenom_strictMono hij)

lemma merged_prefix (δ s : ℕ) (hδ : δ ≤ 2) :
    (∑ i ∈ Finset.range (s + 1), mergedWeight δ i) + δ = 2 ^ (s + 2) := by
  induction s with
  | zero => simp [mergedWeight, Nat.sub_add_cancel (by omega : δ ≤ 4)]
  | succ s ih =>
    rw [Finset.sum_range_succ]
    rw [show mergedWeight δ (s + 1) = 2 ^ (s + 2) from rfl]
    have hp : 2 ^ (s + 1 + 2) = 2 ^ (s + 2) * 2 := by rw [pow_succ]
    rw [hp]
    omega

lemma binary_weight_sum (δ r : ℕ) (hδ : δ ≤ 2) (hr : 1 ≤ r) :
    (∑ i : Fin (binaryCount r), binaryWeight δ r i) + δ = 2 ^ r := by
  by_cases hr1 : r = 1
  · subst r
    change (∑ i : Fin 1, binaryWeight δ 1 i) + δ = 2 ^ 1
    rw [Fin.sum_univ_one]
    simp only [binaryWeight, if_true, packetWeight, Fin.val_zero, pow_one]
    omega
  · have hr2 : 2 ≤ r := by omega
    have h := merged_prefix δ (r - 2) hδ
    have hcount : r - 2 + 1 = r - 1 := by omega
    have hlast : r - 2 + 2 = r := by omega
    rw [show binaryCount r = r - 1 by simp only [binaryCount, if_neg hr1]]
    simp only [binaryWeight, if_neg hr1]
    rw [Fin.sum_univ_eq_sum_range]
    simpa only [hcount, hlast] using h

variable {E : Type} [NormedField E] [CompleteSpace E] {v : AbsoluteValue E ℝ}

noncomputable def unitAtBinaryRadius (P : E[X]) (ζ : E) (i : ℕ) : LocatedPacket P v where
  Q := 1
  monic := Polynomial.monic_one
  divides := one_dvd P
  center := ζ
  radius := Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ))
  radius_pos := Real.exp_pos _
  radius_lt_one := exp_radius_lt_one _ (binaryDenom_pos i)
  pure_shift := by
    rw [Polynomial.one_comp]
    constructor
    · constructor
      · simp [gaussNorm_one_value]
      · intro j hj; omega
    · constructor
      · simp [gaussNorm_one_value]
      · intro j hj
        have hj0 : j ≠ 0 := by simpa using Nat.ne_of_gt hj
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj]
        simp [gaussNorm_one_value]

theorem actual_ordinary_binary_located
    (hstd : StandardSlopeFactorInput.{0}) (hna : IsNonarchimedean v)
    (hmetric : ∀ x : E, v x = ‖x‖)
    (n r : ℕ) (hn : 0 < n) (hr : 1 ≤ r) (ζ : E)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat 2 t : ℝ)))
    (hz : v ζ = 1) (hsep : v (1 - ζ) = 1)
    (hsource : OrdinaryRootSource n 2 r ζ) (i : ℕ) (hi : i < binaryCount r) :
    ∃ A : LocatedPacket ((fInt n).map (Int.castRingHom E)) v,
      A.center = ζ ∧ A.radius = Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ)) ∧
        A.Q.natDegree = binaryWeight 0 r i := by
  have H := actual_ordinary_faces n 2 r hn Nat.prime_two hr ζ hnorm hz hsep hsource
  by_cases hi0 : i = 0
  · subst i
    obtain ⟨D⟩ := hstd E v hna hmetric (shiftedTrinomial n ζ)
      (shiftedTrinomial_monic n hn ζ) (Real.exp (-(1 : ℝ) / 2)) (Real.exp_pos _)
      0 (firstFaceLast 2 r) H.first_min H.first_max
    let A := actualOrdinaryPacket n hna ζ hsep (Real.exp (-(1 : ℝ) / 2))
      (Real.exp_pos _) (exp_radius_lt_one 2 (by omega)) 0 (firstFaceLast 2 r) D
    refine ⟨A, rfl, by rfl, ?_⟩
    rw [actualOrdinaryPacket_degree, Nat.sub_zero]
    by_cases hr1 : r = 1
    · simp [firstFaceLast, binaryWeight, packetWeight, hr1]
    · have hr2 : 2 ≤ r := by omega
      simp [firstFaceLast, binaryWeight, mergedWeight, hr1, hr2]
  · have hi1 : 1 ≤ i := by omega
    have hrne : r ≠ 1 := by intro h; subst r; simp [binaryCount] at hi; omega
    have hik : i + 1 < r := by simp only [binaryCount, if_neg hrne] at hi; omega
    have hface := H.later (i + 1) (by omega) hik (by omega)
    have hden : laterDenom 2 (i + 1) = binaryDenom i := by simp [laterDenom, binaryDenom]
    obtain ⟨D⟩ := hstd E v hna hmetric (shiftedTrinomial n ζ)
      (shiftedTrinomial_monic n hn ζ)
      (Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ))) (Real.exp_pos _)
      (2 ^ (i + 1)) (2 ^ (i + 1 + 1))
      (by simpa only [hden] using hface.1) (by simpa only [hden] using hface.2)
    let A := actualOrdinaryPacket n hna ζ hsep
      (Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ))) (Real.exp_pos _)
      (exp_radius_lt_one _ (binaryDenom_pos i)) (2 ^ (i + 1)) (2 ^ (i + 1 + 1)) D
    refine ⟨A, rfl, rfl, ?_⟩
    rw [actualOrdinaryPacket_degree, pow_succ]
    have hd : 2 ^ (i + 1) * 2 - 2 ^ (i + 1) = 2 ^ (i + 1) := by omega
    rw [hd]
    cases i with
    | zero => omega
    | succ j => simp [binaryWeight, hrne, mergedWeight]

theorem actual_one_binary_located
    (hstd : StandardSlopeFactorInput.{0}) (hna : IsNonarchimedean v)
    (hmetric : ∀ x : E, v x = ‖x‖)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (n r : ℕ) (hn : 0 < n) (hr : 1 ≤ r)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat 2 t : ℝ)))
    (hsource : padicValNat 2 n = r ∨ padicValNat 2 (n + 1) = r)
    (i : ℕ) (hi : i < binaryCount r) :
    ∃ A : LocatedPacket ((fInt n).map (Int.castRingHom E)) v,
      A.center = 1 ∧ A.radius = Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ)) ∧
        A.Q.natDegree = binaryWeight 2 r i := by
  by_cases hr1 : r = 1
  · have hi0 : i = 0 := by simp [binaryCount, hr1] at hi; omega
    subst i
    refine ⟨unitAtBinaryRadius _ 1 0, rfl, rfl, ?_⟩
    simp [unitAtBinaryRadius, binaryWeight, hr1, packetWeight]
  · have hr2 : 2 ≤ r := by omega
    have hik : i + 1 < r := by simp only [binaryCount, if_neg hr1] at hi; omega
    obtain ⟨D, _⟩ := actual_one_later_packet hstd hna hmetric hdiscrete
      n 2 r (i + 1) hn Nat.prime_two hr (by omega) hik hnorm hsource
    have hden : laterDenom 2 (i + 1) = binaryDenom i := by simp [laterDenom, binaryDenom]
    let A := actualOnePacket n (Real.exp (-(1 : ℝ) / (laterDenom 2 (i + 1) : ℝ)))
      (Real.exp_pos _) (exp_radius_lt_one _ (laterDenom_pos 2 (i + 1) (by omega)))
      (2 ^ (i + 1) - 2) (2 ^ (i + 1 + 1) - 2) D
    refine ⟨A, rfl, ?_, ?_⟩
    · change Real.exp (-(1 : ℝ) / (laterDenom 2 (i + 1) : ℝ)) = _
      rw [hden]
    · rw [actualOnePacket_degree, residue_one_later_width 2 (i + 1) (by omega) (by omega), hden]
      cases i with
      | zero => simp [binaryDenom, binaryWeight, hr1, mergedWeight]
      | succ j => simp [binaryDenom, binaryWeight, hr1, mergedWeight]

end EventualIrreducibility.UniversalBinaryFamilyBuildersDraft

open Polynomial

namespace EventualIrreducibility.UniversalBinaryFamilyDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalOrdinaryFacesDraft
  UniversalActualPacketBuildersDraft UniversalBinaryFamilyBuildersDraft UniversalOddFamilyDraft

abbrev BinaryIndex (m r : ℕ) := Unit ⊕ (Fin m × Fin (binaryCount r))

theorem actual_binary_residue_packets
    (hstd : StandardSlopeFactorInput.{0})
    (n r m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (D : PrimeToPUnramifiedData 2 m) (one : Fin m) (hone : D.ζ one = 1)
    (hsource : (padicValNat 2 n = r ∧ n = 2 ^ r * m) ∨
      (padicValNat 2 (n + 1) = r ∧ n + 1 = 2 ^ r * m)) :
    ∃ A : Fin m → Fin (binaryCount r) → LocatedPacket ((fInt n).map (Int.castRingHom D.E)) D.v,
      (∀ a i, (A a i).center = D.ζ a) ∧
      (∀ a i, (A a i).radius = Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ))) ∧
      (∀ a i, (A a i).Q.natDegree = binaryWeight (if a = one then 2 else 0) r i) := by
  classical
  have hval : padicValNat 2 n = r ∨ padicValNat 2 (n + 1) = r :=
    hsource.imp And.left And.left
  have hrootSource (a : Fin m) : OrdinaryRootSource n 2 r (D.ζ a) := by
    rcases hsource with ⟨hv, heq⟩ | ⟨hv, heq⟩
    · left
      refine ⟨hv, root_of_dividing_exponent (D.ζ a) m n ?_ (D.roots a)⟩
      exact ⟨2 ^ r, by simpa only [Nat.mul_comm] using heq⟩
    · right
      refine ⟨hv, root_of_dividing_exponent (D.ζ a) m (n + 1) ?_ (D.roots a)⟩
      exact ⟨2 ^ r, by simpa only [Nat.mul_comm] using heq⟩
  have hexists (a : Fin m) (i : Fin (binaryCount r)) :
      ∃ A : LocatedPacket ((fInt n).map (Int.castRingHom D.E)) D.v,
        A.center = D.ζ a ∧ A.radius = Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ)) ∧
        A.Q.natDegree = binaryWeight (if a = one then 2 else 0) r i := by
    by_cases ha : a = one
    · subst a
      simpa only [hone, if_true] using actual_one_binary_located hstd D.nonarchimedean
        D.norm_eq D.discrete n r (by omega) hr D.nat_norm hval i i.isLt
    · have hsep : D.v (1 - D.ζ a) = 1 := by
        simpa only [hone] using D.separated one a (Ne.symm ha)
      simpa only [if_neg ha] using actual_ordinary_binary_located hstd D.nonarchimedean
        D.norm_eq n r (by omega) hr (D.ζ a) D.nat_norm (D.units a) hsep (hrootSource a) i i.isLt
  choose A hc hr hd using hexists
  exact ⟨A, hc, hr, hd⟩

lemma binary_residue_degree_sum (r m : ℕ) (hr : 1 ≤ r) (one : Fin m) :
    (∑ a : Fin m, ∑ i : Fin (binaryCount r), binaryWeight (if a = one then 2 else 0) r i) + 2 =
      m * 2 ^ r := by
  classical
  have hrow (a : Fin m) :
      (∑ i : Fin (binaryCount r), binaryWeight (if a = one then 2 else 0) r i) +
        (if a = one then 2 else 0) = 2 ^ r :=
    binary_weight_sum _ r (by split_ifs <;> omega) hr
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin m))) rfl (fun a _ => hrow a)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using hsum

theorem actual_binary_common_field_product
    (hstd : StandardSlopeFactorInput.{0}) (hspl : StandardValuedSplittingInput.{0})
    (n r m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (D : PrimeToPUnramifiedData 2 m)
    (hsource : (padicValNat 2 n = r ∧ n = 2 ^ r * m) ∨
      (padicValNat 2 (n + 1) = r ∧ n + 1 = 2 ^ r * m)) :
    ∃ one : Fin m,
    ∃ B : BinaryIndex m r → LocatedPacket ((fInt n).map (Int.castRingHom D.E)) D.v,
      D.ζ one = 1 ∧
      (∀ a i, (B (.inr (a,i))).center = D.ζ a) ∧
      (∀ a i, (B (.inr (a,i))).radius = Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ))) ∧
      (∀ a i, (B (.inr (a,i))).Q.natDegree = binaryWeight (if a = one then 2 else 0) r i) ∧
      (B (.inl ())).center = 0 ∧ (B (.inl ())).Q.natDegree ≤ 1 ∧
      Pairwise (fun i j =>
        ((B i).center = (B j).center ∧ (B i).radius ≠ (B j).radius) ∨
          D.v ((B i).center - (B j).center) = 1) ∧
      ((fInt n).map (Int.castRingHom D.E)) = ∏ q, (B q).Q := by
  classical
  let P : D.E[X] := (fInt n).map (Int.castRingHom D.E)
  have hP : P.Monic := (monic_fInt n (by omega)).map (Int.castRingHom D.E)
  obtain ⟨one, hone⟩ := D.one_root
  obtain ⟨A, hcenter, hradius, hdegree⟩ := actual_binary_residue_packets hstd n r m hn hr D one hone hsource
  have hZ : ∃ Z : LocatedPacket P D.v, Z.center = 0 ∧ Z.Q.natDegree ≤ 1 ∧
      ((∑ a : Fin m, ∑ i : Fin (binaryCount r), (A a i).Q.natDegree) + Z.Q.natDegree = n - 1) := by
    have hsum : (∑ a : Fin m, ∑ i : Fin (binaryCount r), (A a i).Q.natDegree) + 2 = m * 2 ^ r := by
      simpa only [hdegree] using binary_residue_degree_sum r m hr one
    rcases hsource with ⟨hv, heq⟩ | ⟨hv, heq⟩
    · obtain ⟨Z, hc, _, hd⟩ := actual_zero_located hstd D.nonarchimedean
        D.norm_eq n 2 r hn Nat.prime_two hr hv D.nat_norm
      refine ⟨Z, hc, by omega, ?_⟩
      rw [hd]
      have hm : m * 2 ^ r = n := by nlinarith [heq]
      omega
    · refine ⟨unitLocatedPacket P 0, rfl, by simp [unitLocatedPacket], ?_⟩
      change (∑ a : Fin m, ∑ i : Fin (binaryCount r), (A a i).Q.natDegree) +
        (1 : D.E[X]).natDegree = n - 1
      have hm : m * 2 ^ r = n + 1 := by nlinarith [heq]
      simp only [Polynomial.natDegree_one, add_zero]
      omega
  obtain ⟨Z, hZcenter, hZsmall, hZdegree⟩ := hZ
  let B : BinaryIndex m r → LocatedPacket P D.v := Sum.elim (fun _ => Z) (fun q => A q.1 q.2)
  have hBdegree : ∑ q, (B q).Q.natDegree = P.natDegree := by
    simp only [B, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique,
      Sum.elim_inl, Sum.elim_inr]
    rw [Polynomial.Monic.natDegree_map (monic_fInt n (by omega)), natDegree_fInt n (by omega)]
    omega
  have hBsep : Pairwise (fun i j =>
      ((B i).center = (B j).center ∧ (B i).radius ≠ (B j).radius) ∨
        D.v ((B i).center - (B j).center) = 1) := by
    intro q t hqt
    cases q with
    | inl u =>
      cases t with
      | inl v => exact False.elim (hqt (by cases u; cases v; rfl))
      | inr ai =>
        right
        simpa only [B, Sum.elim_inl, Sum.elim_inr, hZcenter, hcenter,
          zero_sub, AbsoluteValue.map_neg] using D.units ai.1
    | inr ai =>
      cases t with
      | inl u =>
        right
        simpa only [B, Sum.elim_inl, Sum.elim_inr, hZcenter, hcenter, sub_zero] using D.units ai.1
      | inr bj =>
        by_cases hab : ai.1 = bj.1
        · left
          refine ⟨by simp only [B, Sum.elim_inr, hcenter, hab], ?_⟩
          have hij : ai.2 ≠ bj.2 := by
            intro h
            apply hqt
            exact congrArg Sum.inr (Prod.ext hab h)
          intro heq
          apply hij
          apply Fin.ext
          apply binaryRadius_injective
          simpa only [B, Sum.elim_inr, hradius] using heq
        · right
          simpa only [B, Sum.elim_inr, hcenter] using D.separated ai.1 bj.1 hab
  obtain ⟨S⟩ := hspl D.E D.v D.nonarchimedean D.norm_eq P hP.ne_zero
  have hproduct := located_packet_product P hP B (algebraMap D.E S.K)
    S.restrict S.nonarchimedean S.splits hBsep hBdegree
  exact ⟨one, B, hone, hcenter, hradius, hdegree, hZcenter, hZsmall, hBsep, hproduct⟩

end EventualIrreducibility.UniversalBinaryFamilyDraft

open Polynomial

@[simp] noncomputable abbrev Polynomial.localResultant
    {R : Type*} [CommRing R] (P Q : R[X]) : R :=
  Polynomial.resultant P Q P.natDegree Q.natDegree

namespace EventualIrreducibility.UniversalRootNormProductsDraft

variable {K : Type u} [Field K] (v : AbsoluteValue K ℝ)

lemma abv_multiset_prod (s : Multiset K) : v s.prod = (s.map v).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp only [Multiset.prod_cons, map_mul, Multiset.map_cons, ih]

lemma resultant_norm_eq_roots_eval (A B : K[X]) (hA : A.Monic) (hs : A.Splits) :
    v (A.localResultant B) = (A.roots.map (fun α => v (B.eval α))).prod := by
  unfold Polynomial.localResultant
  rw [Polynomial.resultant_eq_prod_eval _ _ _ le_rfl hs,
    hA.leadingCoeff, one_pow, one_mul, abv_multiset_prod]
  simp only [Multiset.map_map, Function.comp_def]

lemma resultant_norm_comm (A B : K[X]) : v (A.localResultant B) = v (B.localResultant A) := by
  unfold Polynomial.localResultant
  rw [Polynomial.resultant_comm]
  simp only [map_mul, map_pow, AbsoluteValue.map_neg, map_one, one_pow, one_mul]

lemma discr_norm_eq_roots_derivative (A : K[X]) (hA : A.Monic)
    (hd : 0 < A.natDegree) (hs : A.Splits) :
    v A.discr = (A.roots.map (fun α => v (A.derivative.eval α))).prod := by
  have hresdisc : A.resultant A.derivative A.natDegree (A.natDegree - 1) =
      (-1) ^ (A.natDegree * (A.natDegree - 1) / 2) * A.discr := by
    simpa only [hA.leadingCoeff, mul_one] using
      Polynomial.resultant_deriv (Polynomial.natDegree_pos_iff_degree_pos.mp hd)
  have heval := Polynomial.resultant_eq_prod_eval A A.derivative (A.natDegree - 1)
    (Polynomial.natDegree_derivative_le A) hs
  have hnorm := congrArg v hresdisc
  simp only [map_mul, map_pow, AbsoluteValue.map_neg, map_one, one_pow, one_mul] at hnorm
  rw [← hnorm, heval, hA.leadingCoeff, one_pow, one_mul, abv_multiset_prod]
  simp only [Multiset.map_map, Function.comp_def]

theorem discriminant_norm_mul (A B : K[X]) (hA : A.Monic) (hB : B.Monic)
    (hdA : 0 < A.natDegree) (hdB : 0 < B.natDegree)
    (hsA : A.Splits) (hsB : B.Splits) :
    v (A * B).discr = v A.discr * v B.discr * v (A.localResultant B) ^ 2 := by
  have hdeg : 0 < (A * B).natDegree := by
    rw [Polynomial.natDegree_mul hA.ne_zero hB.ne_zero]
    omega
  rw [discr_norm_eq_roots_derivative v (A * B) (hA.mul hB) hdeg (hsA.mul hsB),
    Polynomial.roots_mul (mul_ne_zero hA.ne_zero hB.ne_zero), Multiset.map_add, Multiset.prod_add]
  have hleft : (A.roots.map (fun α => v ((A * B).derivative.eval α))).prod =
      (A.roots.map (fun α => v (A.derivative.eval α))).prod *
        (A.roots.map (fun α => v (B.eval α))).prod := by
    rw [← Multiset.prod_map_mul]
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro α hα
    have hr : A.eval α = 0 := Polynomial.isRoot_of_mem_roots hα
    simp [Polynomial.derivative_mul, hr, map_mul]
  have hright : (B.roots.map (fun β => v ((A * B).derivative.eval β))).prod =
      (B.roots.map (fun β => v (A.eval β))).prod *
        (B.roots.map (fun β => v (B.derivative.eval β))).prod := by
    rw [← Multiset.prod_map_mul]
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro β hβ
    have hr : B.eval β = 0 := Polynomial.isRoot_of_mem_roots hβ
    simp [Polynomial.derivative_mul, hr, map_mul]
  rw [hleft, hright,
    ← discr_norm_eq_roots_derivative v A hA hdA hsA,
    ← discr_norm_eq_roots_derivative v B hB hdB hsB,
    ← resultant_norm_eq_roots_eval v A B hA hsA,
    ← resultant_norm_eq_roots_eval v B A hB hsB,
    resultant_norm_comm v B A]
  ring

end EventualIrreducibility.UniversalRootNormProductsDraft

open Polynomial

namespace EventualIrreducibility.UniversalLocatedNormsDraft

open UniversalPacketProductDraft UniversalRootNormProductsDraft UniversalPacketResultantDraft

section RootProducts

variable {K : Type u} [Field K] (w : AbsoluteValue K ℝ)

omit [Field K] in
lemma multiset_product_of_constant (s : Multiset K) (f : K → ℝ) (c : ℝ)
    (h : ∀ x ∈ s, f x = c) : (s.map f).prod = c ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    ring

lemma polynomial_eval_norm_of_constant_root_distance
    (B : K[X]) (hB : B.Monic) (hsB : B.Splits) (α : K) (c : ℝ)
    (hdiff : ∀ β ∈ B.roots, w (α - β) = c) :
    w (B.eval α) = c ^ B.natDegree := by
  rw [hsB.eval_eq_prod_roots_of_monic hB α, abv_multiset_prod]
  simp only [Multiset.map_map, Function.comp_def]
  rw [multiset_product_of_constant B.roots (fun β => w (α - β)) c hdiff,
    ← hsB.natDegree_eq_card_roots]

lemma resultant_norm_of_constant_root_distance
    (A B : K[X]) (hA : A.Monic) (hB : B.Monic) (hsA : A.Splits) (hsB : B.Splits)
    (c : ℝ) (hdiff : ∀ α ∈ A.roots, ∀ β ∈ B.roots, w (α - β) = c) :
    w (A.localResultant B) = c ^ (A.natDegree * B.natDegree) := by
  rw [resultant_norm_eq_roots_eval w A B hA hsA,
    multiset_product_of_constant A.roots (fun α => w (B.eval α))
      (c ^ B.natDegree) (fun α hα =>
        polynomial_eval_norm_of_constant_root_distance w B hB hsB α c (hdiff α hα)),
    ← hsA.natDegree_eq_card_roots, ← pow_mul, Nat.mul_comm]

end RootProducts

section Located

variable {E : Type u} [Field E] {K : Type u} [Field K]
  {v : AbsoluteValue E ℝ} {w : AbsoluteValue K ℝ}

lemma located_map_splits (P : E[X]) (hP : P.Monic) (A : LocatedPacket P v)
    (ι : E →+* K) (hs : (P.map ι).Splits) : (A.Q.map ι).Splits := by
  apply hs.of_dvd (hP.map ι).ne_zero
  obtain ⟨T, hT⟩ := A.divides
  exact ⟨T.map ι, by simpa only [Polynomial.map_mul] using congrArg (Polynomial.map ι) hT⟩

lemma located_pairwise_coprime {I : Type*} [Fintype I]
    (P : E[X]) (hP : P.Monic) (A : I → LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (hsep : Pairwise (fun i j =>
      ((A i).center = (A j).center ∧ (A i).radius ≠ (A j).radius) ∨
        v ((A i).center - (A j).center) = 1)) :
    Pairwise (fun i j => IsCoprime (A i).Q (A j).Q) := by
  intro i j hij
  exact coprime_of_mapped_disjoint_roots ι (A i).Q (A j).Q
    (A i).monic (A j).monic (located_map_splits P hP (A i) ι hs)
    (located_disjoint_of_centers_or_radii P (A i) (A j) ι hrestrict hna (hsep hij))

lemma resultant_norm_map (A B : E[X]) (hA : A.Monic) (hB : B.Monic)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x) :
    w ((A.map ι).localResultant (B.map ι)) = v (A.localResultant B) := by
  unfold Polynomial.localResultant
  rw [Polynomial.Monic.natDegree_map hA, Polynomial.Monic.natDegree_map hB,
    Polynomial.resultant_map_map, hrestrict]

lemma located_eval_norm_distinct_centers
    (P : E[X]) (hP : P.Monic) (A B : LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (hcenter : v (A.center - B.center) = 1)
    (α : K) (hα : (A.Q.map ι).IsRoot α) : w ((B.Q.map ι).eval α) = 1 := by
  rw [polynomial_eval_norm_of_constant_root_distance w (B.Q.map ι) (B.monic.map ι)
    (located_map_splits P hP B ι hs) α 1]
  · simp
  · intro β hβ
    exact distinct_center_difference_norm w hna α β (ι A.center) (ι B.center)
      (by rw [← map_sub, hrestrict, hcenter])
      ((A.root_radius P ι hrestrict hna α hα).trans_lt A.radius_lt_one)
      ((B.root_radius P ι hrestrict hna β (Polynomial.isRoot_of_mem_roots hβ)).trans_lt
        B.radius_lt_one)

lemma located_eval_norm_same_center
    (P : E[X]) (hP : P.Monic) (A B : LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (hcenter : A.center = B.center) (hradius : A.radius < B.radius)
    (α : K) (hα : (A.Q.map ι).IsRoot α) :
    w ((B.Q.map ι).eval α) = B.radius ^ B.Q.natDegree := by
  rw [polynomial_eval_norm_of_constant_root_distance w (B.Q.map ι) (B.monic.map ι)
    (located_map_splits P hP B ι hs) α B.radius]
  · rw [Polynomial.Monic.natDegree_map B.monic]
  · intro β hβ
    apply same_center_difference_norm w hna α β (ι A.center) A.radius B.radius
      (A.root_radius P ι hrestrict hna α hα) _ hradius
    simpa only [hcenter] using
      B.root_radius P ι hrestrict hna β (Polynomial.isRoot_of_mem_roots hβ)

lemma located_eval_norm_degree_radius
    (P : E[X]) (hP : P.Monic) (A B : LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (hcenter : A.center = B.center) (hradius : A.radius < B.radius)
    (he : 0 < B.Q.natDegree)
    (hB : B.radius = Real.exp (-(1 : ℝ) / (B.Q.natDegree : ℝ)))
    (α : K) (hα : (A.Q.map ι).IsRoot α) :
    w ((B.Q.map ι).eval α) = Real.exp (-1) := by
  rw [located_eval_norm_same_center P hP A B ι hrestrict hna hs hcenter hradius α hα,
    hB, ← Real.exp_nat_mul]
  congr 1
  have he0 : (B.Q.natDegree : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
  field_simp [he0]

lemma located_resultant_norm_distinct_centers
    (P : E[X]) (hP : P.Monic) (A B : LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (hcenter : v (A.center - B.center) = 1) : v (A.Q.localResultant B.Q) = 1 := by
  rw [← resultant_norm_map A.Q B.Q A.monic B.monic ι hrestrict]
  rw [resultant_norm_of_constant_root_distance w _ _ (A.monic.map ι) (B.monic.map ι)
    (located_map_splits P hP A ι hs) (located_map_splits P hP B ι hs) 1]
  · simp
  · intro α hα β hβ
    exact distinct_center_difference_norm w hna α β (ι A.center) (ι B.center)
      (by rw [← map_sub, hrestrict, hcenter])
      ((A.root_radius P ι hrestrict hna α (Polynomial.isRoot_of_mem_roots hα)).trans_lt
        A.radius_lt_one)
      ((B.root_radius P ι hrestrict hna β (Polynomial.isRoot_of_mem_roots hβ)).trans_lt
        B.radius_lt_one)

lemma located_resultant_norm_same_center
    (P : E[X]) (hP : P.Monic) (A B : LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (hcenter : A.center = B.center) (hradius : A.radius < B.radius) :
    v (A.Q.localResultant B.Q) = B.radius ^ (A.Q.natDegree * B.Q.natDegree) := by
  rw [← resultant_norm_map A.Q B.Q A.monic B.monic ι hrestrict]
  rw [resultant_norm_of_constant_root_distance w _ _ (A.monic.map ι) (B.monic.map ι)
    (located_map_splits P hP A ι hs) (located_map_splits P hP B ι hs) B.radius]
  · rw [Polynomial.Monic.natDegree_map A.monic, Polynomial.Monic.natDegree_map B.monic]
  · intro α hα β hβ
    apply same_center_difference_norm w hna α β (ι A.center) A.radius B.radius
      (A.root_radius P ι hrestrict hna α (Polynomial.isRoot_of_mem_roots hα)) _ hradius
    simpa only [hcenter] using
      B.root_radius P ι hrestrict hna β (Polynomial.isRoot_of_mem_roots hβ)

lemma located_resultant_norm_degree_radius
    (P : E[X]) (hP : P.Monic) (A B : LocatedPacket P v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (hcenter : A.center = B.center) (hradius : A.radius < B.radius)
    (he : 0 < B.Q.natDegree)
    (hB : B.radius = Real.exp (-(1 : ℝ) / (B.Q.natDegree : ℝ))) :
    v (A.Q.localResultant B.Q) = Real.exp (-(A.Q.natDegree : ℝ)) := by
  rw [located_resultant_norm_same_center P hP A B ι hrestrict hna hs hcenter hradius,
    hB, ← Real.exp_nat_mul]
  congr 1
  have he0 : (B.Q.natDegree : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
  push_cast
  field_simp [he0]

end Located

end EventualIrreducibility.UniversalLocatedNormsDraft

namespace EventualIrreducibility.UniversalOrientedCutDraft

open UniversalLocalDraft UniversalLocalCutAssemblyDraft

def orientedEntry (w : ℕ → ℕ) (c : ℕ → Bool) (i j : ℕ) : ℕ :=
  if c i = true ∧ c j = false then w (min i j) else 0

def orientedCut (w : ℕ → ℕ) (c : ℕ → Bool) (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, orientedEntry w c i j

lemma orientedEntry_self (w : ℕ → ℕ) (c : ℕ → Bool) (i : ℕ) :
    orientedEntry w c i i = 0 := by
  cases h : c i <;> simp [orientedEntry, h]

lemma orientedEntry_pair (w : ℕ → ℕ) (c : ℕ → Bool) (i j : ℕ) (hij : i ≤ j) :
    orientedEntry w c i j + orientedEntry w c j i =
      if c i ≠ c j then w i else 0 := by
  cases hi : c i <;> cases hj : c j <;>
    simp [orientedEntry, hi, hj, min_eq_left hij, min_eq_right hij]

lemma orientedCut_succ (w : ℕ → ℕ) (c : ℕ → Bool) (r : ℕ) :
    orientedCut w c (r + 1) = orientedCut w c r +
      ∑ i ∈ Finset.range r, if c i ≠ c r then w i else 0 := by
  unfold orientedCut
  rw [Finset.sum_range_succ]
  simp_rw [Finset.sum_range_succ]
  rw [Finset.sum_add_distrib, orientedEntry_self, add_zero]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact orientedEntry_pair w c i r (Nat.le_of_lt (Finset.mem_range.mp hi))

theorem orientedCut_eq_cutWeight (w : ℕ → ℕ) (c : ℕ → Bool) (r : ℕ) :
    orientedCut w c r = cutWeight (coloredPrefix w c r) := by
  induction r with
  | zero => simp [orientedCut, coloredPrefix, cutWeight]
  | succ r ih =>
    rw [orientedCut_succ, ih, coloredPrefix, cutWeight,
      colorWeight_coloredPrefix]
    simp_rw [bool_eq_not_iff]
    omega

lemma exp_neg_nat_sum {I : Type*} (s : Finset I) (a : I → ℕ) :
    (∏ i ∈ s, Real.exp (-(a i : ℝ))) = Real.exp (-(∑ i ∈ s, a i : ℕ)) := by
  rw [← Real.exp_sum]
  congr 1
  simp

lemma exp_neg_oriented_matrix (w : ℕ → ℕ) (c : ℕ → Bool) (r : ℕ) :
    (∏ i ∈ Finset.range r, ∏ j ∈ Finset.range r,
      Real.exp (-(orientedEntry w c i j : ℝ))) =
      Real.exp (-(cutWeight (coloredPrefix w c r) : ℝ)) := by
  simp_rw [exp_neg_nat_sum]
  rw [← orientedCut_eq_cutWeight]
  rfl

lemma exp_neg_oriented_fin_matrix (w : ℕ → ℕ) (c : ℕ → Bool) (r : ℕ) :
    (∏ i : Fin r, ∏ j : Fin r, Real.exp (-(orientedEntry w c i j : ℝ))) =
      Real.exp (-(cutWeight (coloredPrefix w c r) : ℝ)) := by
  calc
    _ = ∏ i ∈ Finset.range r, ∏ j : Fin r,
        Real.exp (-(orientedEntry w c i j : ℝ)) :=
      Fin.prod_univ_eq_prod_range
        (fun i : ℕ => ∏ j : Fin r, Real.exp (-(orientedEntry w c i j : ℝ))) r
    _ = ∏ i ∈ Finset.range r, ∏ j ∈ Finset.range r,
        Real.exp (-(orientedEntry w c i j : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact Fin.prod_univ_eq_prod_range (fun j : ℕ =>
        Real.exp (-(orientedEntry w c i j : ℝ))) r
    _ = _ := exp_neg_oriented_matrix w c r

end EventualIrreducibility.UniversalOrientedCutDraft

open Polynomial

namespace EventualIrreducibility.UniversalWholePacketMatrixDraft

open UniversalPacketAllocationDraft UniversalRootNormProductsDraft UniversalOrientedCutDraft

section Selection

variable {E : Type u} [Field E]

lemma whole_allocation_of_small_degree {I : Type*} [Fintype I]
    (Q : I → E[X]) (G H : E[X]) (A : PacketAllocation Q G H)
    (i : I) (hdegree : (Q i).natDegree ≤ 1) :
    (A.left i = Q i ∧ A.right i = 1) ∨
      (A.left i = 1 ∧ A.right i = Q i) := by
  have hd := congrArg Polynomial.natDegree (A.pair_product i)
  rw [Polynomial.natDegree_mul (A.monic_left i).ne_zero (A.monic_right i).ne_zero] at hd
  have hzero : (A.left i).natDegree = 0 ∨ (A.right i).natDegree = 0 := by omega
  rcases hzero with hl | hr
  · have hleft : A.left i = 1 := (A.monic_left i).natDegree_eq_zero.mp hl
    exact Or.inr ⟨hleft, by simpa only [hleft, one_mul] using (A.pair_product i).symm⟩
  · have hright : A.right i = 1 := (A.monic_right i).natDegree_eq_zero.mp hr
    exact Or.inl ⟨by simpa only [hright, mul_one] using (A.pair_product i).symm, hright⟩

lemma exists_whole_allocation_color {I : Type*} [Fintype I]
    (Q : I → E[X]) (G H : E[X]) (A : PacketAllocation Q G H)
    (hwhole : ∀ i, (A.left i = Q i ∧ A.right i = 1) ∨
      (A.left i = 1 ∧ A.right i = Q i)) :
    ∃ c : I → Bool,
      (∀ i, A.left i = if c i = true then Q i else 1) ∧
      (∀ i, A.right i = if c i = true then 1 else Q i) := by
  classical
  have hex (i : I) : ∃ c : Bool,
      A.left i = (if c = true then Q i else 1) ∧
      A.right i = (if c = true then 1 else Q i) := by
    rcases hwhole i with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩
  choose c hc using hex
  exact ⟨c, fun i => (hc i).1, fun i => (hc i).2⟩

lemma whole_allocation_self_norm_one {I : Type*} [Fintype I]
    (v : AbsoluteValue E ℝ) (Q : I → E[X]) (G H : E[X]) (A : PacketAllocation Q G H)
    (i : I) (hwhole : (A.left i = Q i ∧ A.right i = 1) ∨
      (A.left i = 1 ∧ A.right i = Q i)) :
    v ((A.left i).localResultant (A.right i)) = 1 := by
  rcases hwhole with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp [hl, hr]

lemma whole_allocation_unit_pair_norm {I : Type*} [Fintype I]
    (v : AbsoluteValue E ℝ) (Q : I → E[X]) (G H : E[X]) (A : PacketAllocation Q G H)
    (i j : I)
    (hi : (A.left i = Q i ∧ A.right i = 1) ∨ (A.left i = 1 ∧ A.right i = Q i))
    (hj : (A.left j = Q j ∧ A.right j = 1) ∨ (A.left j = 1 ∧ A.right j = Q j))
    (hnorm : v ((Q i).localResultant (Q j)) = 1) :
    v ((A.left i).localResultant (A.right j)) = 1 := by
  rcases hi with ⟨hli, hri⟩ | ⟨hli, hri⟩ <;>
    rcases hj with ⟨hlj, hrj⟩ | ⟨hlj, hrj⟩
  · simp [hli,hrj]
  · calc
      v ((A.left i).localResultant (A.right j)) = v ((Q i).localResultant (Q j)) :=
        congrArg v (congrArg₂ (fun L R : E[X] => L.localResultant R) hli hrj)
      _ = 1 := hnorm
  · simp [hli,hrj]
  · simp [hli,hrj]

lemma selected_resultant_norm_entry
    (v : AbsoluteValue E ℝ) (r : ℕ) (Q L R : Fin r → E[X])
    (w : ℕ → ℕ) (c : ℕ → Bool)
    (hL : ∀ i, L i = if c i = true then Q i else 1)
    (hR : ∀ i, R i = if c i = true then 1 else Q i)
    (hnorm : ∀ i j : Fin r, i < j →
      v ((Q i).localResultant (Q j)) = Real.exp (-(w i : ℝ)))
    (i j : Fin r) :
    v ((L i).localResultant (R j)) = Real.exp (-(orientedEntry w c i j : ℝ)) := by
  cases hci : c i <;> cases hcj : c j
  · simp [hL, hR, hci, hcj, orientedEntry]
  · simp [hL, hR, hci, hcj, orientedEntry]
  · simp only [hL, hR, hci, hcj, if_pos, Bool.false_eq_true, if_false]
    have hne : i ≠ j := by intro h; subst j; rw [hci] at hcj; contradiction
    rcases lt_or_gt_of_ne hne with hij | hji
    · simpa only [orientedEntry, hci, hcj, and_self, if_true,
        min_eq_left (Nat.le_of_lt hij)] using hnorm i j hij
    · rw [resultant_norm_comm v]
      simpa only [orientedEntry, hci, hcj, and_self, if_true,
        min_eq_right (Nat.le_of_lt hji)] using hnorm j i hji
  · simp [hL, hR, hci, hcj, orientedEntry]

theorem selected_resultant_norm_matrix
    (v : AbsoluteValue E ℝ) (r : ℕ) (Q L R : Fin r → E[X])
    (w : ℕ → ℕ) (c : ℕ → Bool)
    (hL : ∀ i, L i = if c i = true then Q i else 1)
    (hR : ∀ i, R i = if c i = true then 1 else Q i)
    (hnorm : ∀ i j : Fin r, i < j →
      v ((Q i).localResultant (Q j)) = Real.exp (-(w i : ℝ))) :
    (∏ i, ∏ j, v ((L i).localResultant (R j))) =
      Real.exp (-(UniversalLocalDraft.cutWeight
        (UniversalLocalDraft.coloredPrefix w c r) : ℝ)) := by
  simp_rw [selected_resultant_norm_entry v r Q L R w c hL hR hnorm]
  exact exp_neg_oriented_fin_matrix w c r

end Selection

lemma block_diagonal_product {I J : Type*} [Fintype I] [Fintype J]
    (M : (Unit ⊕ (I × J)) → (Unit ⊕ (I × J)) → ℝ)
    (hzero : ∀ q, M (.inl ()) q = 1 ∧ M q (.inl ()) = 1)
    (hoff : ∀ a b : I, a ≠ b → ∀ i j : J, M (.inr (a,i)) (.inr (b,j)) = 1) :
    (∏ q, ∏ t, M q t) = ∏ a, ∏ i, ∏ j, M (.inr (a,i)) (.inr (a,j)) := by
  classical
  rw [Fintype.prod_sum_type]
  have hrow0 : (∏ u : Unit, ∏ t, M (.inl u) t) = 1 := by
    simp only [Fintype.prod_unique]
    simp [hzero]
  rw [hrow0, one_mul, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro a ha
  apply Finset.prod_congr rfl
  intro i hi
  rw [Fintype.prod_sum_type]
  have hcol0 : (∏ u : Unit, M (.inr (a,i)) (.inl u)) = 1 := by
    simp only [Fintype.prod_unique]
    exact (hzero (.inr (a,i))).2
  rw [hcol0, one_mul, Fintype.prod_prod_type]
  apply Fintype.prod_eq_single a
  intro b hba
  apply Finset.prod_eq_one
  intro j hj
  exact hoff a b (Ne.symm hba) i j

end EventualIrreducibility.UniversalWholePacketMatrixDraft

open Polynomial

namespace EventualIrreducibility.UniversalActualOddResultantDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalPacketAllocationDraft
  UniversalOddFamilyDraft UniversalLocatedNormsDraft UniversalWholePacketMatrixDraft
  UniversalOrientedCutDraft UniversalLocalDraft UniversalRootNormProductsDraft FirstFace

lemma residue_cut_total_bound (p r m : ℕ) (hp : 2 ≤ p) (one : Fin m)
    (c : Fin m → ℕ → Bool) :
    (∑ a : Fin m, cutWeight (coloredPrefix (packetWeight p (if a = one then 2 else 0))
      (c a) r)) + 2 * (r / 2) ≤ m * exactCut p r := by
  classical
  have hrow (a : Fin m) := packet_cut_bound p (if a = one then 2 else 0) r hp
    (by split_ifs <;> omega) (c a)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun a _ => hrow a)
  have hcorrection : (∑ a : Fin m, (if a = one then 2 else 0) * (r / 2)) = 2 * (r / 2) := by
    simp only [ite_mul,zero_mul]
    simp
  simpa only [Finset.sum_add_distrib,hcorrection,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,Nat.nsmul_eq_mul] using hsum

theorem actual_odd_resultant_norm_and_cut
    (hstd : StandardSlopeFactorInput.{0}) (hspl : StandardValuedSplittingInput.{0})
    (n p r m : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hpodd : p ≠ 2) (hr : 1 ≤ r)
    (D : PrimeToPUnramifiedData p m)
    (hsource : (padicValNat p n = r ∧ n = p ^ r * m) ∨
      (padicValNat p (n + 1) = r ∧ n + 1 = p ^ r * m))
    (G H : D.E[X]) (hG : G.Monic) (hH : H.Monic)
    (hfactor : ((fInt n).map (Int.castRingHom D.E)) = G * H) :
    ∃ V : ℕ, D.v (G.localResultant H) = Real.exp (-(V : ℝ)) ∧
      V + 2 * (r / 2) ≤ m * exactCut p r := by
  classical
  let P : D.E[X] := (fInt n).map (Int.castRingHom D.E)
  have hP : P.Monic := (monic_fInt n (by omega)).map (Int.castRingHom D.E)
  obtain ⟨one, B, hone, hc, hrad, hd, hirr, hzc, hzd, hsep, hprod⟩ :=
    actual_odd_common_field_product hstd hspl n p r m hn hp hpodd hr D hsource
  obtain ⟨S⟩ := hspl D.E D.v D.nonarchimedean D.norm_eq P hP.ne_zero
  let ι : D.E →+* S.K := algebraMap D.E S.K
  have hcop := located_pairwise_coprime P hP B ι S.restrict S.nonarchimedean S.splits hsep
  obtain ⟨A⟩ := exists_packet_allocation P G H hG hH (fun q => (B q).Q)
    (fun q => (B q).monic) hcop hprod hfactor
  have hwhole (q : OddIndex m r) :
      (A.left q = (B q).Q ∧ A.right q = 1) ∨
        (A.left q = 1 ∧ A.right q = (B q).Q) := by
    cases q with
    | inl u =>
      cases u
      exact whole_allocation_of_small_degree _ G H A (.inl ()) hzd
    | inr ai => exact irreducible_packet_allocation _ G H A (.inr ai) (hirr ai.1 ai.2)
  obtain ⟨c, hleft, hright⟩ := exists_whole_allocation_color _ G H A hwhole
  let rowColor (a : Fin m) (i : ℕ) : Bool :=
    if hi : i < r then c (.inr (a, ⟨i, hi⟩)) else false
  have hrowColor (a : Fin m) (i : Fin r) : rowColor a i = c (.inr (a,i)) := by
    simp only [rowColor, dif_pos i.isLt]
  let V : ℕ := ∑ a : Fin m, cutWeight
    (coloredPrefix (packetWeight p (if a = one then 2 else 0)) (rowColor a) r)
  refine ⟨V, ?_, residue_cut_total_bound p r m hp.two_le one rowColor⟩
  have hunitpair (q t : OddIndex m r)
      (hcenters : D.v ((B q).center - (B t).center) = 1) :
      D.v ((A.left q).localResultant (A.right t)) = 1 := by
    apply whole_allocation_unit_pair_norm D.v _ G H A q t (hwhole q) (hwhole t)
    exact located_resultant_norm_distinct_centers P hP (B q) (B t)
      ι S.restrict S.nonarchimedean S.splits hcenters
  have hzero (q : OddIndex m r) :
      D.v ((A.left (.inl ())).localResultant (A.right q)) = 1 ∧
        D.v ((A.left q).localResultant (A.right (.inl ()))) = 1 := by
    cases q with
    | inl u =>
      cases u
      have h := whole_allocation_self_norm_one D.v _ G H A (.inl ()) (hwhole (.inl ()))
      exact ⟨h,h⟩
    | inr ai =>
      constructor
      · apply hunitpair
        simpa only [hzc, hc, zero_sub, AbsoluteValue.map_neg] using D.units ai.1
      · apply hunitpair
        simpa only [hzc, hc, sub_zero] using D.units ai.1
  have hoff (a b : Fin m) (hab : a ≠ b) (i j : Fin r) :
      D.v ((A.left (.inr (a,i))).localResultant (A.right (.inr (b,j)))) = 1 := by
    apply hunitpair
    simpa only [hc] using D.separated a b hab
  have hrownorm (a : Fin m) :
      (∏ i : Fin r, ∏ j : Fin r,
        D.v ((A.left (.inr (a,i))).localResultant (A.right (.inr (a,j))))) =
      Real.exp (-(cutWeight (coloredPrefix
        (packetWeight p (if a = one then 2 else 0)) (rowColor a) r) : ℝ)) := by
    apply selected_resultant_norm_matrix D.v r (fun i => (B (.inr (a,i))).Q)
      (fun i => A.left (.inr (a,i))) (fun i => A.right (.inr (a,i)))
      (packetWeight p (if a = one then 2 else 0)) (rowColor a)
      (fun i => by simpa only [hrowColor] using hleft (.inr (a,i)))
      (fun i => by simpa only [hrowColor] using hright (.inr (a,i)))
    intro i j hij
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hδ : (if a = one then 2 else 0) < p := by split_ifs <;> omega
    have hpos := packetWeight_pos p (if a = one then 2 else 0) j hp.two_le hδ
    have hijrad : (B (.inr (a,i))).radius < (B (.inr (a,j))).radius := by
      rw [hrad, hrad]
      exact exp_radius_strict_of_denominators _ _
        (packetWeight_pos p _ i hp.two_le hδ)
        (packetWeight_strictMono p _ hp3 hδ.le hij)
    have hnrm := located_resultant_norm_degree_radius P hP
      (B (.inr (a,i))) (B (.inr (a,j))) ι S.restrict S.nonarchimedean S.splits
      (by rw [hc, hc]) hijrad (by simpa only [hd] using hpos)
      (by rw [hrad, hd])
    simpa only [hd] using hnrm
  rw [resultant_norm_of_packet_allocation D.v _ G H A,
    block_diagonal_product _ hzero hoff]
  simp_rw [hrownorm]
  exact exp_neg_nat_sum Finset.univ _

end EventualIrreducibility.UniversalActualOddResultantDraft

open Polynomial

namespace EventualIrreducibility.UniversalIntegerLocalValuationDraft

open UniversalSlopeDraft UniversalLocalDraft UniversalActualOddResultantDraft

lemma integer_norm_from_nat_normalization
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (p : ℕ)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (z : ℤ) (hz : z ≠ 0) :
    v (z : E) = Real.exp (-(padicValNat p z.natAbs : ℝ)) := by
  cases z with
  | ofNat t =>
    simpa using hnorm t (by simpa using hz)
  | negSucc t =>
    simpa only [Int.cast_negSucc, AbsoluteValue.map_neg, Int.natAbs_negSucc,
      Nat.cast_add, Nat.cast_one] using hnorm (t + 1) (by omega)

lemma normalized_integer_exponent_eq
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (p : ℕ)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (z : ℤ) (V : ℕ) (hV : v (z : E) = Real.exp (-(V : ℝ))) :
    z ≠ 0 ∧ padicValNat p z.natAbs = V := by
  have hz : z ≠ 0 := by
    intro h
    have hzero : v (z : E) = 0 := by simp [h]
    rw [hzero] at hV
    exact (Real.exp_ne_zero _) hV.symm
  refine ⟨hz, ?_⟩
  rw [integer_norm_from_nat_normalization v p hnorm z hz] at hV
  have heq := Real.exp_injective hV
  have hcast : (padicValNat p z.natAbs : ℝ) = (V : ℝ) := by linarith
  exact_mod_cast hcast

theorem actual_odd_integer_resultant_valuation
    (hstd : StandardSlopeFactorInput.{0}) (hspl : StandardValuedSplittingInput.{0})
    (n p r m : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hpodd : p ≠ 2) (hr : 1 ≤ r)
    (D : PrimeToPUnramifiedData p m)
    (hsource : (padicValNat p n = r ∧ n = p ^ r * m) ∨
      (padicValNat p (n + 1) = r ∧ n + 1 = p ^ r * m))
    (g h : ℤ[X]) (hg : g.Monic) (hh : h.Monic) (hfactor : fInt n = g * h) :
    g.localResultant h ≠ 0 ∧
      padicValNat p (g.localResultant h).natAbs + 2 * (r / 2) ≤ m * exactCut p r := by
  let G : D.E[X] := g.map (Int.castRingHom D.E)
  let H : D.E[X] := h.map (Int.castRingHom D.E)
  have hG := hg.map (Int.castRingHom D.E)
  have hH := hh.map (Int.castRingHom D.E)
  have hGH : ((fInt n).map (Int.castRingHom D.E)) = G * H := by
    simpa only [G, H, Polynomial.map_mul] using congrArg
      (Polynomial.map (Int.castRingHom D.E)) hfactor
  obtain ⟨V, hV, hcut⟩ := actual_odd_resultant_norm_and_cut hstd hspl
    n p r m hn hp hpodd hr D hsource G H hG hH hGH
  have hnorm : D.v ((g.localResultant h : ℤ) : D.E) = Real.exp (-(V : ℝ)) := by
    simpa only [G, H, Polynomial.localResultant, Polynomial.Monic.natDegree_map hg,
      Polynomial.Monic.natDegree_map hh, Polynomial.resultant_map_map,
      Int.coe_castRingHom] using hV
  obtain ⟨hne, hval⟩ := normalized_integer_exponent_eq D.v p D.nat_norm
    (g.localResultant h) V hnorm
  exact ⟨hne, by simpa only [hval] using hcut⟩

end EventualIrreducibility.UniversalIntegerLocalValuationDraft

open Polynomial

namespace EventualIrreducibility.UniversalPacketDerivativeDraft

open UniversalRootNormProductsDraft UniversalLocatedNormsDraft UniversalPacketProductDraft
  UniversalOrientedCutDraft UniversalBinaryQuarticDraft UniversalBinaryCrossNormDraft

section Products

variable {K : Type u} [Field K] (w : AbsoluteValue K ℝ)

lemma derivative_product_eval_at_packet_root
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : K[X]) (Q : I → K[X]) (hproduct : P = ∏ j, Q j)
    (i : I) (α : K) (hroot : (Q i).eval α = 0) :
    P.derivative.eval α = (Q i).derivative.eval α *
      ∏ j ∈ Finset.univ.erase i, (Q j).eval α := by
  have hfactor : P = Q i * ∏ j ∈ Finset.univ.erase i, Q j :=
    hproduct.trans (Finset.mul_prod_erase Finset.univ Q (Finset.mem_univ i)).symm
  rw [hfactor, derivative_mul_eval_at_root _ _ α hroot, Polynomial.eval_prod]

lemma root_derivative_norm_from_complete_packet_product
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : K[X]) (Q : I → K[X]) (hproduct : P = ∏ j, Q j)
    (i : I) (r : ℕ) (hr : 2 ≤ r) (cost : I → ℕ)
    (hcost : ∑ j ∈ Finset.univ.erase i, cost j = r - 2)
    (α : K) (hroot : (Q i).eval α = 0)
    (hfull : w (P.derivative.eval α) = Real.exp (-(r : ℝ)))
    (hother : ∀ j, j ≠ i → w ((Q j).eval α) = Real.exp (-(cost j : ℝ))) :
    w ((Q i).derivative.eval α) = Real.exp (-2) := by
  have hrest : (∏ j ∈ Finset.univ.erase i, w ((Q j).eval α)) =
      Real.exp (-((r - 2 : ℕ) : ℝ)) := by
    calc
      _ = ∏ j ∈ Finset.univ.erase i, Real.exp (-(cost j : ℝ)) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hother j (Finset.mem_erase.mp hj).1
      _ = _ := by rw [exp_neg_nat_sum, hcost]
  have hnorm := congrArg w (derivative_product_eval_at_packet_root P Q hproduct i α hroot)
  rw [map_mul, UniversalPacketResultantDraft.abv_finset_prod, hrest, hfull] at hnorm
  apply mul_right_cancel₀ (Real.exp_ne_zero (-((r - 2 : ℕ) : ℝ)))
  rw [← hnorm, ← Real.exp_add]
  congr 1
  rw [Nat.cast_sub hr]
  norm_num
  ring

theorem quartic_discriminant_from_complete_packet_product
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : K[X]) (Q : I → K[X]) (hproduct : P = ∏ j, Q j)
    (i : I) (hQi : (Q i).Monic) (hdegree : (Q i).natDegree = 4)
    (hsplit : (Q i).Splits) (r : ℕ) (hr : 2 ≤ r) (cost : I → ℕ)
    (hcost : ∑ j ∈ Finset.univ.erase i, cost j = r - 2)
    (hfull : ∀ α ∈ (Q i).roots,
      w (P.derivative.eval α) = Real.exp (-(r : ℝ)))
    (hother : ∀ α ∈ (Q i).roots, ∀ j, j ≠ i →
      w ((Q j).eval α) = Real.exp (-(cost j : ℝ))) :
    w (Q i).discr = Real.exp (-8) := by
  rw [discr_norm_eq_roots_derivative w _ hQi (by omega) hsplit]
  have hderiv (α : K) (hα : α ∈ (Q i).roots) :
      w ((Q i).derivative.eval α) = Real.exp (-2) :=
    root_derivative_norm_from_complete_packet_product w P Q hproduct i r hr cost hcost α
      (Polynomial.isRoot_of_mem_roots hα) (hfull α hα) (hother α hα)
  rw [multiset_product_of_constant _ _ (Real.exp (-2)) hderiv,
    ← hsplit.natDegree_eq_card_roots, hdegree, ← Real.exp_nat_mul]
  norm_num

omit [Field K] in
lemma multiset_product_le_constant (s : Multiset K) (f : K → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h0 : ∀ x ∈ s, 0 ≤ f x) (h : ∀ x ∈ s, f x ≤ c) :
    (s.map f).prod ≤ c ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc
      f x * (s.map f).prod ≤ c * c ^ s.card :=
        mul_le_mul (h x (by simp))
          (ih (fun y hy => h0 y (by simp [hy])) (fun y hy => h y (by simp [hy])))
          (Multiset.prod_nonneg (fun y hy => by
            obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
            exact h0 z (by simp [hz]))) hc
      _ = _ := by ring

end Products

end EventualIrreducibility.UniversalPacketDerivativeDraft

open Polynomial

namespace EventualIrreducibility.UniversalBinaryQuarticFamilyDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalBinaryFamilyDraft
  UniversalBinaryFamilyBuildersDraft UniversalLocatedNormsDraft UniversalPacketDerivativeDraft
  UniversalBinaryQuarticDraft UniversalPacketResultantDraft UniversalOrientedCutDraft

def higherCost {m r : ℕ} (a : Fin m) : BinaryIndex m r → ℕ
  | .inl _ => 0
  | .inr (b,j) => if b = a ∧ (j : ℕ) ≠ 0 then 1 else 0

lemma sum_positive_indices (r : ℕ) :
    (∑ j ∈ Finset.range r, if j = 0 then 0 else 1) = r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

lemma higherCost_sum (m r : ℕ) (hr : 2 ≤ r) (a : Fin m) :
    (∑ q : BinaryIndex m r, higherCost a q) = r - 2 := by
  classical
  have hr1 : r ≠ 1 := by omega
  simp only [higherCost, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_unique, zero_add]
  have hrow (b : Fin m) :
      (∑ j : Fin (binaryCount r), if b = a ∧ (j : ℕ) ≠ 0 then 1 else 0) =
      if b = a then r - 2 else 0 := by
    by_cases hb : b = a
    · simp only [hb, true_and, if_true]
      calc
        _ = ∑ j ∈ Finset.range (binaryCount r), if j ≠ 0 then 1 else 0 :=
          Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≠ 0 then 1 else 0) (binaryCount r)
        _ = binaryCount r - 1 := by
          simpa only [ne_eq,ite_not] using sum_positive_indices (binaryCount r)
        _ = r - 2 := by simp only [binaryCount,if_neg hr1]; omega
    · simp [hb]
  simp_rw [hrow]
  simp

lemma higherCost_erase_sum (m r : ℕ) (hr : 2 ≤ r) (a : Fin m)
    (z : Fin (binaryCount r)) (hz : (z : ℕ) = 0) :
    (∑ q ∈ Finset.univ.erase (Sum.inr (a,z) : BinaryIndex m r), higherCost a q) = r - 2 := by
  classical
  have h := Finset.sum_erase_add Finset.univ (higherCost a)
    (Finset.mem_univ (Sum.inr (a,z) : BinaryIndex m r))
  have hzero : higherCost a (.inr (a,z)) = 0 := by simp [higherCost,hz]
  rw [hzero,add_zero] at h
  exact h.trans (higherCost_sum m r hr a)

lemma binary_higher_degree_eq_denom (r i : ℕ) (hr : 2 ≤ r) (hi : i ≠ 0) :
    binaryWeight 0 r i = binaryDenom i := by
  have hr1 : r ≠ 1 := by omega
  cases i with
  | zero => contradiction
  | succ i => simp [binaryWeight, hr1, mergedWeight, binaryDenom]

lemma f_root_derivative_norm
    {K : Type*} [Field K] (w : AbsoluteValue K ℝ)
    (n r : ℕ) (P : K[X])
    (hP : (X - 1) ^ 2 * P = shiftedTrinomial n (0 : K))
    (α : K) (hroot : P.eval α = 0)
    (hunit : w α = 1) (haway : w (α - 1) = 1)
    (hscalar : w ((n : K) * ((n + 1 : ℕ) : K)) = Real.exp (-(r : ℝ))) :
    w (P.derivative.eval α) = Real.exp (-(r : ℝ)) := by
  have hFroot : (shiftedTrinomial n (0 : K)).eval α = 0 := by
    rw [← hP]
    simp [hroot]
  have hfull := shifted_root_derivative_norm w n r 0 α hFroot
    (by simpa using hunit) (by simpa using haway) hscalar
  have hderiv : (shiftedTrinomial n (0 : K)).derivative.eval α =
      (α - 1) ^ 2 * P.derivative.eval α := by
    rw [← hP]
    simp [Polynomial.derivative_mul, hroot]
  rw [hderiv, map_mul, map_pow, haway, one_pow, one_mul] at hfull
  exact hfull

theorem binary_family_quartic_discriminant
    (n r m : ℕ) (hn : 2 ≤ n) (hr : 2 ≤ r)
    (D : PrimeToPUnramifiedData 2 m)
    (B : BinaryIndex m r → LocatedPacket ((fInt n).map (Int.castRingHom D.E)) D.v)
    (one : Fin m) (hone : D.ζ one = 1)
    (hc : ∀ a i, (B (.inr (a,i))).center = D.ζ a)
    (hrad : ∀ a i, (B (.inr (a,i))).radius = Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ)))
    (hd : ∀ a i, (B (.inr (a,i))).Q.natDegree = binaryWeight (if a = one then 2 else 0) r i)
    (hzc : (B (.inl ())).center = 0)
    (hproduct : ((fInt n).map (Int.castRingHom D.E)) = ∏ q, (B q).Q)
    (S : ValuedSplittingData D.E D.v ((fInt n).map (Int.castRingHom D.E)))
    (hscalar : D.v ((n : D.E) * ((n + 1 : ℕ) : D.E)) = Real.exp (-(r : ℝ)))
    (a : Fin m) (ha : a ≠ one) :
    let z : Fin (binaryCount r) := ⟨0, binaryCount_pos r (by omega)⟩
    S.w (((B (.inr (a,z))).Q.map (algebraMap D.E S.K)).discr) = Real.exp (-8) := by
  classical
  let P : D.E[X] := (fInt n).map (Int.castRingHom D.E)
  let ι : D.E →+* S.K := algebraMap D.E S.K
  let z : Fin (binaryCount r) := ⟨0, binaryCount_pos r (by omega)⟩
  let q0 : BinaryIndex m r := .inr (a,z)
  let Q : BinaryIndex m r → S.K[X] := fun q => (B q).Q.map ι
  have hP : P.Monic := (monic_fInt n (by omega)).map (Int.castRingHom D.E)
  have hr1 : r ≠ 1 := by omega
  have hqdegree : (Q q0).natDegree = 4 := by
    rw [Polynomial.Monic.natDegree_map (B q0).monic]
    simp only [q0, z, hd, if_neg ha, binaryWeight, if_neg hr1, mergedWeight, Nat.sub_zero]
  have hqcenter : (B q0).center = D.ζ a := hc a z
  have hqradius : (B q0).radius = Real.exp (-(1 : ℝ) / 2) := by
    simpa only [q0, z, binaryDenom, Nat.zero_add, pow_one,Nat.cast_ofNat] using hrad a z
  have hproductK : P.map ι = ∏ q, Q q := by
    simpa only [Polynomial.map_prod, Q] using congrArg (Polynomial.map ι) hproduct
  apply quartic_discriminant_from_complete_packet_product S.w (P.map ι) Q hproductK q0
    ((B q0).monic.map ι) hqdegree
    (located_map_splits P hP (B q0) ι S.splits) r hr (higherCost a)
    (higherCost_erase_sum m r hr a z rfl)
  · intro α hα
    have hroot : (Q q0).IsRoot α := Polynomial.isRoot_of_mem_roots hα
    have hαrad := (B q0).root_radius P ι S.restrict S.nonarchimedean α hroot
    have hαclose : S.w (α - ι (D.ζ a)) < 1 := by
      rw [← hqcenter, hαrad]
      exact (B q0).radius_lt_one
    have hζunit : S.w (ι (D.ζ a)) = 1 := (S.restrict _).trans (D.units a)
    have hunit : S.w α = 1 := by
      have hdiff : S.w (ι (D.ζ a) - α) = S.w (α - ι (D.ζ a)) := by
        rw [show ι (D.ζ a) - α = -(α - ι (D.ζ a)) by ring, AbsoluteValue.map_neg]
      have h := sub_norm_eq_left S.w S.nonarchimedean (ι (D.ζ a)) (ι (D.ζ a) - α)
        (by simpa only [hdiff,hζunit] using hαclose)
      simpa only [sub_sub_cancel, hζunit] using h
    have haway : S.w (α - 1) = 1 := by
      apply distinct_center_difference_norm S.w S.nonarchimedean α 1 (ι (D.ζ a)) 1
      · rw [← map_one ι, ← map_sub, S.restrict]
        simpa only [hone] using D.separated a one ha
      · exact hαclose
      · simp
    have hrootP : (P.map ι).eval α = 0 := by
      obtain ⟨T, hT⟩ := (B q0).divides
      have hmap := congrArg (Polynomial.map ι) hT
      rw [Polynomial.map_mul] at hmap
      rw [hmap]
      change ((B q0).Q.map ι).eval α = 0 at hroot
      simp only [Polynomial.eval_mul,hroot,zero_mul]
    have htrin : (X - 1) ^ 2 * P.map ι = shiftedTrinomial n (0 : S.K) := by
      have hbase := Simplicity.mapped_trinomial_from_integer (K := S.K) (trinomial_identity n)
      have hcast : ι.comp (Int.castRingHom D.E) = Int.castRingHom S.K := by
        ext z
        simp
      simpa [P, shiftedTrinomial, Polynomial.map_map,hcast] using hbase
    apply f_root_derivative_norm S.w n r (P.map ι) htrin α hrootP hunit haway
    simpa only [map_mul, map_natCast] using (S.restrict
      ((n : D.E) * ((n + 1 : ℕ) : D.E))).trans hscalar
  · intro α hα q hq
    have hroot : ((B q0).Q.map ι).IsRoot α := Polynomial.isRoot_of_mem_roots hα
    cases q with
    | inl u =>
      cases u
      change S.w (((B (.inl ())).Q.map ι).eval α) = Real.exp (-(0 : ℕ))
      rw [Nat.cast_zero, neg_zero, Real.exp_zero]
      apply located_eval_norm_distinct_centers P hP (B q0) (B (.inl ()))
        ι S.restrict S.nonarchimedean S.splits _ α hroot
      simpa only [hqcenter, hzc, sub_zero] using D.units a
    | inr bj =>
      by_cases hba : bj.1 = a
      · have hj0 : (bj.2 : ℕ) ≠ 0 := by
          intro hj
          apply hq
          apply congrArg Sum.inr
          exact Prod.ext hba (Fin.ext (hj.trans rfl))
        have hcost : higherCost a (.inr bj) = 1 := by simp [higherCost, hba, hj0]
        rw [hcost,Nat.cast_one]
        have hdegree : (B (.inr bj)).Q.natDegree = binaryDenom bj.2 := by
          rw [hd, hba, if_neg ha, binary_higher_degree_eq_denom r bj.2 hr hj0]
        apply located_eval_norm_degree_radius P hP (B q0) (B (.inr bj))
          ι S.restrict S.nonarchimedean S.splits _ _ _ _ α hroot
        · rw [hqcenter, hc, hba]
        · rw [hqradius, hrad]
          exact FirstFace.exp_radius_strict_of_denominators 2 (binaryDenom bj.2) (by omega)
            (by simpa only [binaryDenom, Nat.zero_add, pow_one] using
              binaryDenom_strictMono (show 0 < (bj.2 : ℕ) by omega))
        · rw [hdegree]; exact binaryDenom_pos _
        · rw [hrad, hdegree]
      · have hcost : higherCost a (.inr bj) = 0 := by simp [higherCost, hba]
        rw [hcost, Nat.cast_zero, neg_zero, Real.exp_zero]
        apply located_eval_norm_distinct_centers P hP (B q0) (B (.inr bj))
          ι S.restrict S.nonarchimedean S.splits _ α hroot
        simpa only [hqcenter, hc] using D.separated a bj.1 (Ne.symm hba)

end EventualIrreducibility.UniversalBinaryQuarticFamilyDraft

open Polynomial

namespace EventualIrreducibility.UniversalBinaryAllocatedCrossDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalLocatedNormsDraft
  UniversalRootNormProductsDraft UniversalPacketDerivativeDraft UniversalBinaryQuarticDraft
  UniversalBinaryCrossNormDraft

variable {E K : Type u} [Field E] [Field K]
  {v : AbsoluteValue E ℝ} {w : AbsoluteValue K ℝ}

lemma located_quadratic_discriminant_norm_le
    (P : E[X]) (hP : P.Monic) (A : LocatedPacket P v)
    (hdegree : A.Q.natDegree = 2) (hradius : A.radius = Real.exp (-(1 : ℝ) / 2))
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (htwo : v (2 : E) = Real.exp (-1))
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits) :
    w (A.Q.map ι).discr ≤ Real.exp (-2) := by
  let T : E[X] := A.Q.comp (X + C A.center)
  have hTm : T.Monic := A.monic.comp_X_add_C A.center
  have hTd : T.natDegree = 2 := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one, hdegree]
  have hTpure : PureGauss T v (Real.exp (-(1 : ℝ) / 2)) := by
    simpa only [T, hradius] using A.pure_shift
  have hlinear := pure_quadratic_linear_norm v T hTm hTd hdiscrete hTpure
  have hsQ := located_map_splits P hP A ι hs
  have hdQ : (A.Q.map ι).natDegree = 2 := by rw [Polynomial.Monic.natDegree_map A.monic, hdegree]
  have hderiv (α : K) (hα : α ∈ (A.Q.map ι).roots) :
      w ((A.Q.map ι).derivative.eval α) ≤ Real.exp (-1) := by
    have hroot := Polynomial.isRoot_of_mem_roots hα
    have hβ : w (α - ι A.center) = Real.exp (-(1 : ℝ) / 2) :=
      (A.root_radius P ι hrestrict hna α hroot).trans hradius
    have hid : (T.map ι).derivative.eval (α - ι A.center) =
        (A.Q.map ι).derivative.eval α := by
      simp [T, Polynomial.map_comp, Polynomial.derivative_comp, Polynomial.eval_comp]
    rw [← hid, monic_quadratic_derivative_eval _ (hTm.map ι)
      (by rw [Polynomial.Monic.natDegree_map hTm, hTd])]
    apply (hna _ _).trans
    apply max_le
    · have ht : w (2 : K) = Real.exp (-1) := by
        have htwoMap : ι (2 : E) = (2 : K) := by
          rw [show (2 : E) = 1 + 1 by norm_num, map_add, map_one]
          norm_num
        rw [← htwoMap]
        exact (hrestrict (2 : E)).trans htwo
      rw [map_mul, ht, hβ]
      exact mul_le_of_le_one_right (Real.exp_pos _).le
        (Real.exp_le_one_iff.mpr (by norm_num))
    · rw [Polynomial.coeff_map, hrestrict]
      exact hlinear
  rw [discr_norm_eq_roots_derivative w _ (A.monic.map ι) (by omega) hsQ]
  calc
    _ ≤ (Real.exp (-1)) ^ (A.Q.map ι).roots.card :=
      multiset_product_le_constant _ _ _ (Real.exp_pos _).le
        (fun α _ => AbsoluteValue.nonneg _ _) hderiv
    _ = Real.exp (-2) := by
      rw [← hsQ.natDegree_eq_card_roots, hdQ, ← Real.exp_nat_mul]
      norm_num

theorem allocated_quartic_cross_norm_lower
    (P : E[X]) (hP : P.Monic) (A : LocatedPacket P v)
    (hdegree : A.Q.natDegree = 4) (hradius : A.radius = Real.exp (-(1 : ℝ) / 2))
    (hnaE : IsNonarchimedean v)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (htwo : v (2 : E) = Real.exp (-1))
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (hdisc : w (A.Q.map ι).discr = Real.exp (-8))
    (L R : E[X]) (hL : L.Monic) (hR : R.Monic) (hfactor : A.Q = L * R) :
    Real.exp (-2) ≤ v (L.localResultant R) := by
  have hLd : L ∣ A.Q := ⟨R,hfactor⟩
  have hRd : R ∣ A.Q := ⟨L,by rw [hfactor, mul_comm]⟩
  have hdeg := congrArg Polynomial.natDegree hfactor
  rw [hdegree, Polynomial.natDegree_mul hL.ne_zero hR.ne_zero] at hdeg
  by_cases hl0 : L.natDegree = 0
  · have hL1 := hL.natDegree_eq_zero.mp hl0
    unfold Polynomial.localResultant
    rw [hL1]
    simp only [Polynomial.natDegree_one, Polynomial.resultant_one_left,
      zero_mul, pow_zero, one_mul, map_one]
    exact Real.exp_le_one_iff.mpr (show (-2 : ℝ) ≤ 0 by norm_num)
  by_cases hr0 : R.natDegree = 0
  · have hR1 := hR.natDegree_eq_zero.mp hr0
    unfold Polynomial.localResultant
    rw [hR1]
    simp only [Polynomial.natDegree_one, Polynomial.resultant_one_right, pow_zero, map_one]
    exact Real.exp_le_one_iff.mpr (show (-2 : ℝ) ≤ 0 by norm_num)
  have hLeven := A.denominator_dvd_divisor_degree P hnaE 2 (by omega)
    (by simpa using hradius) hdiscrete L hL hLd
  have hReven := A.denominator_dvd_divisor_degree P hnaE 2 (by omega)
    (by simpa using hradius) hdiscrete R hR hRd
  have hL2 : L.natDegree = 2 := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) hLeven
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hReven
    omega
  have hR2 : R.natDegree = 2 := by omega
  let AL := A.divisor P hnaE L hL hLd
  let AR := A.divisor P hnaE R hR hRd
  have hdL : w (L.map ι).discr ≤ Real.exp (-2) :=
    located_quadratic_discriminant_norm_le P hP AL hL2 hradius hdiscrete htwo
      ι hrestrict hna hs
  have hdR : w (R.map ι).discr ≤ Real.exp (-2) :=
    located_quadratic_discriminant_norm_le P hP AR hR2 hradius hdiscrete htwo
      ι hrestrict hna hs
  have hproduct := discriminant_norm_mul w (L.map ι) (R.map ι) (hL.map ι) (hR.map ι)
    (by rw [Polynomial.Monic.natDegree_map hL,hL2]; omega)
    (by rw [Polynomial.Monic.natDegree_map hR,hR2]; omega)
    (located_map_splits P hP AL ι hs) (located_map_splits P hP AR ι hs)
  have hmap : A.Q.map ι = L.map ι * R.map ι := by
    simpa only [Polynomial.map_mul] using congrArg (Polynomial.map ι) hfactor
  rw [← hmap, hdisc] at hproduct
  have hcross := binary_cross_norm_ge_exp_neg_two (w (L.map ι).discr) (w (R.map ι).discr)
    (w ((L.map ι).localResultant (R.map ι))) (AbsoluteValue.nonneg _ _) (AbsoluteValue.nonneg _ _)
    hdL hdR hproduct.symm
  rw [resultant_norm_map L R hL hR ι hrestrict] at hcross
  exact hcross

end EventualIrreducibility.UniversalBinaryAllocatedCrossDraft

open Polynomial

namespace EventualIrreducibility.UniversalLocatedAllocationNormsDraft

open UniversalPacketProductDraft UniversalPacketAllocationDraft UniversalLocatedNormsDraft
  UniversalRootNormProductsDraft UniversalWholePacketMatrixDraft

variable {E K : Type u} [Field E] [Field K]
  {v : AbsoluteValue E ℝ} {w : AbsoluteValue K ℝ}
  {I : Type*} [Fintype I]

def allocationLeft (P : E[X]) (B : I → LocatedPacket P v)
    (G H : E[X]) (A : PacketAllocation (fun i => (B i).Q) G H)
    (hna : IsNonarchimedean v) (i : I) : LocatedPacket P v :=
  (B i).divisor P hna (A.left i) (A.monic_left i) ⟨A.right i, A.pair_product i⟩

def allocationRight (P : E[X]) (B : I → LocatedPacket P v)
    (G H : E[X]) (A : PacketAllocation (fun i => (B i).Q) G H)
    (hna : IsNonarchimedean v) (i : I) : LocatedPacket P v :=
  (B i).divisor P hna (A.right i) (A.monic_right i)
    ⟨A.left i, by rw [A.pair_product i, mul_comm]⟩

theorem allocation_distinct_center_norm
    (P : E[X]) (hP : P.Monic) (B : I → LocatedPacket P v)
    (G H : E[X]) (A : PacketAllocation (fun i => (B i).Q) G H)
    (hnaE : IsNonarchimedean v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (i j : I) (hc : v ((B i).center - (B j).center) = 1) :
    v ((A.left i).localResultant (A.right j)) = 1 :=
  located_resultant_norm_distinct_centers P hP
    (allocationLeft P B G H A hnaE i) (allocationRight P B G H A hnaE j)
    ι hrestrict hna hs hc

theorem allocation_cross_norm_later_right
    (P : E[X]) (hP : P.Monic) (B : I → LocatedPacket P v)
    (G H : E[X]) (A : PacketAllocation (fun i => (B i).Q) G H)
    (hnaE : IsNonarchimedean v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (i j : I) (hc : (B i).center = (B j).center) (hr : (B i).radius < (B j).radius)
    (he : 0 < (B j).Q.natDegree)
    (hrad : (B j).radius = Real.exp (-(1 : ℝ) / ((B j).Q.natDegree : ℝ)))
    (hj : A.right j = (B j).Q) :
    v ((A.left i).localResultant (A.right j)) = Real.exp (-((A.left i).natDegree : ℝ)) := by
  rw [hj]
  exact located_resultant_norm_degree_radius P hP (allocationLeft P B G H A hnaE i)
    (B j) ι hrestrict hna hs hc hr he hrad

theorem allocation_cross_norm_later_left
    (P : E[X]) (hP : P.Monic) (B : I → LocatedPacket P v)
    (G H : E[X]) (A : PacketAllocation (fun i => (B i).Q) G H)
    (hnaE : IsNonarchimedean v)
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (i j : I) (hc : (B i).center = (B j).center) (hr : (B i).radius < (B j).radius)
    (he : 0 < (B j).Q.natDegree)
    (hrad : (B j).radius = Real.exp (-(1 : ℝ) / ((B j).Q.natDegree : ℝ)))
    (hj : A.left j = (B j).Q) :
    v ((A.left j).localResultant (A.right i)) = Real.exp (-((A.right i).natDegree : ℝ)) := by
  rw [hj, resultant_norm_comm v]
  exact located_resultant_norm_degree_radius P hP (allocationRight P B G H A hnaE i)
    (B j) ι hrestrict hna hs hc hr he hrad

theorem allocated_degree_sum_and_divisibility
    (P : E[X]) (B : I → LocatedPacket P v)
    (G H : E[X]) (A : PacketAllocation (fun i => (B i).Q) G H)
    (hnaE : IsNonarchimedean v)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (i : I) (b : ℕ) (hb : 0 < b)
    (hrad : (B i).radius = Real.exp (-(1 : ℝ) / (b : ℝ))) :
    (A.left i).natDegree + (A.right i).natDegree = (B i).Q.natDegree ∧
      b ∣ (A.left i).natDegree ∧ b ∣ (A.right i).natDegree := by
  refine ⟨?_, ?_, ?_⟩
  · rw [A.pair_product i, Polynomial.natDegree_mul (A.monic_left i).ne_zero (A.monic_right i).ne_zero]
  · exact (B i).denominator_dvd_divisor_degree P hnaE b hb hrad hdiscrete
      (A.left i) (A.monic_left i) ⟨A.right i, A.pair_product i⟩
  · exact (B i).denominator_dvd_divisor_degree P hnaE b hb hrad hdiscrete
      (A.right i) (A.monic_right i) ⟨A.left i, by rw [A.pair_product i,mul_comm]⟩

end EventualIrreducibility.UniversalLocatedAllocationNormsDraft

open Polynomial

namespace EventualIrreducibility.UniversalLocalSourceDraft

open UniversalSlopeDraft

lemma adjacent_not_both_divisible (n p : ℕ) (hp : p.Prime) :
    ¬ (p ∣ n ∧ p ∣ n + 1) := by
  rintro ⟨h0,h1⟩
  have h := Nat.dvd_gcd h0 h1
  have hunit : p ∣ 1 := by simpa using h
  exact hp.ne_one (Nat.eq_one_of_dvd_one hunit)

lemma adjacent_product_valuation_from_source (n p r : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hr : 1 ≤ r)
    (hsource : padicValNat p n = r ∨ padicValNat p (n + 1) = r) :
    padicValNat p (n * (n + 1)) = r := by
  let : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul (Nat.ne_of_gt hn) (by omega)]
  rcases hsource with hv | hv
  · have hd : p ∣ n := dvd_of_one_le_padicValNat (by omega)
    have hother : ¬ p ∣ n + 1 := fun h => adjacent_not_both_divisible n p hp ⟨hd,h⟩
    rw [hv, padicValNat.eq_zero_of_not_dvd hother, add_zero]
  · have hd : p ∣ n + 1 := dvd_of_one_le_padicValNat (by omega)
    have hother : ¬ p ∣ n := fun h => adjacent_not_both_divisible n p hp ⟨h,hd⟩
    rw [hv, padicValNat.eq_zero_of_not_dvd hother, zero_add]

lemma adjacent_product_norm_from_source
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ)
    (n p r : ℕ) (hn : 0 < n) (hp : p.Prime) (hr : 1 ≤ r)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (hsource : padicValNat p n = r ∨ padicValNat p (n + 1) = r) :
    v ((n : E) * ((n + 1 : ℕ) : E)) = Real.exp (-(r : ℝ)) := by
  rw [← Nat.cast_mul, hnorm _ (by positivity),
    adjacent_product_valuation_from_source n p r hn hp hr hsource]

lemma prime_power_cofactor (p M : ℕ) (hp : p.Prime) (hM : M ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ M = p ^ padicValNat p M * m := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : p ^ padicValNat p M ∣ M := (padicValNat_dvd_iff_le hM).mpr le_rfl
  obtain ⟨m,hm⟩ := hd
  refine ⟨m, ?_, ?_, hm⟩
  · by_contra h
    have hm0 : m = 0 := by omega
    simp only [hm0, mul_zero] at hm
    exact hM hm
  · rintro ⟨b,hb⟩
    apply pow_succ_padicValNat_not_dvd (p := p) hM
    refine ⟨b, ?_⟩
    calc
      M = p ^ padicValNat p M * m := hm
      _ = p ^ (padicValNat p M + 1) * b := by rw [hb,pow_succ]; ring

theorem select_local_source (n p : ℕ) (hn : 0 < n) (hp : p.Prime)
    (hdiv : p ∣ n * (n + 1)) :
    let r := padicValNat p (n * (n + 1))
    1 ≤ r ∧ ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧
      ((padicValNat p n = r ∧ n = p ^ r * m) ∨
       (padicValNat p (n + 1) = r ∧ n + 1 = p ^ r * m)) := by
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  have hr : 1 ≤ padicValNat p (n * (n + 1)) :=
    one_le_padicValNat_of_dvd (by positivity) hdiv
  refine ⟨hr, ?_⟩
  rcases hp.dvd_mul.mp hdiv with hdn | hdN
  · have hrn : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd (by omega) hdn
    have hv := adjacent_product_valuation_from_source n p (padicValNat p n) hn hp hrn (Or.inl rfl)
    obtain ⟨m,hm,hpM,hM⟩ := prime_power_cofactor p n hp (by omega)
    exact ⟨m,hm,hpM,Or.inl ⟨hv.symm,by simpa only [hv] using hM⟩⟩
  · have hrN : 1 ≤ padicValNat p (n + 1) := one_le_padicValNat_of_dvd (by omega) hdN
    have hv := adjacent_product_valuation_from_source n p (padicValNat p (n + 1)) hn hp hrN (Or.inr rfl)
    obtain ⟨m,hm,hpM,hM⟩ := prime_power_cofactor p (n + 1) hp (by omega)
    exact ⟨m,hm,hpM,Or.inr ⟨hv.symm,by simpa only [hv] using hM⟩⟩

end EventualIrreducibility.UniversalLocalSourceDraft

open Polynomial

namespace EventualIrreducibility.UniversalBinaryRowDataDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalPacketAllocationDraft
  UniversalBinaryAllocatedCrossDraft UniversalBinaryFamilyDraft UniversalBinaryFamilyBuildersDraft
  UniversalBinaryQuarticFamilyDraft UniversalLocatedAllocationNormsDraft UniversalLocalSourceDraft

theorem initial_allocation_internal_norm
    {E K : Type u} [Field E] [Field K]
    {v : AbsoluteValue E ℝ} {w : AbsoluteValue K ℝ}
    (P : E[X]) (hP : P.Monic) (A : LocatedPacket P v)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 2) (hdegree : A.Q.natDegree = 4 - δ)
    (hradius : A.radius = Real.exp (-(1 : ℝ) / 2))
    (hnaE : IsNonarchimedean v)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (htwo : v (2 : E) = Real.exp (-1))
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (hdisc : δ = 0 → w (A.Q.map ι).discr = Real.exp (-8))
    (L R : E[X]) (hL : L.Monic) (hR : R.Monic) (hfactor : A.Q = L * R) :
    Real.exp (-((if δ = 0 ∧ L.natDegree = 2 then 2 else 0 : ℕ) : ℝ)) ≤
      v (L.localResultant R) := by
  have hLd : L ∣ A.Q := ⟨R,hfactor⟩
  have hRd : R ∣ A.Q := ⟨L,by rw [hfactor,mul_comm]⟩
  have hsum := congrArg Polynomial.natDegree hfactor
  rw [hdegree, Polynomial.natDegree_mul hL.ne_zero hR.ne_zero] at hsum
  have hLeven := A.denominator_dvd_divisor_degree P hnaE 2 (by omega)
    (by simpa using hradius) hdiscrete L hL hLd
  have hReven := A.denominator_dvd_divisor_degree P hnaE 2 (by omega)
    (by simpa using hradius) hdiscrete R hR hRd
  by_cases hl0 : L.natDegree = 0
  · have hL1 := hL.natDegree_eq_zero.mp hl0
    simp [hL1]
  by_cases hr0 : R.natDegree = 0
  · have hR1 := hR.natDegree_eq_zero.mp hr0
    have hno : ¬ (δ = 0 ∧ L.natDegree = 2) := by omega
    simp [hR1,hno]
  have hl2 : 2 ≤ L.natDegree := Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) hLeven
  have hr2 : 2 ≤ R.natDegree := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hReven
  have hδ0 : δ = 0 := by rcases hδ with h | h <;> omega
  have hL2 : L.natDegree = 2 := by omega
  simp only [hδ0,hL2,and_self,if_true,Nat.cast_ofNat]
  apply allocated_quartic_cross_norm_lower P hP A (by simpa [hδ0] using hdegree)
    hradius hnaE hdiscrete htwo ι hrestrict hna hs (hdisc hδ0) L R hL hR hfactor

theorem actual_binary_higher_packet_irreducible
    (n r m : ℕ) (hr : 2 ≤ r) (D : PrimeToPUnramifiedData 2 m)
    (B : BinaryIndex m r → LocatedPacket ((fInt n).map (Int.castRingHom D.E)) D.v)
    (one : Fin m)
    (hrad : ∀ a i, (B (.inr (a,i))).radius = Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ)))
    (hd : ∀ a i, (B (.inr (a,i))).Q.natDegree = binaryWeight (if a = one then 2 else 0) r i)
    (a : Fin m) (i : Fin (binaryCount r)) (hi : (i : ℕ) ≠ 0) :
    Irreducible (B (.inr (a,i))).Q := by
  have hr1 : r ≠ 1 := by omega
  have hdegree : (B (.inr (a,i))).Q.natDegree = binaryDenom i := by
    rw [hd]
    cases hival : (i : ℕ) with
    | zero => contradiction
    | succ j => simp [binaryWeight,hr1,mergedWeight,binaryDenom]
  exact (B (.inr (a,i))).irreducible_of_degree _ D.nonarchimedean (binaryDenom i)
    (binaryDenom_pos i) (hrad a i) hdegree D.discrete

end EventualIrreducibility.UniversalBinaryRowDataDraft

namespace EventualIrreducibility.UniversalBinaryVirtualDraft

open UniversalLocalDraft UniversalOrientedCutDraft

def virtualColor (l : ℕ) (c : ℕ → Bool) : ℕ → Bool
  | 0 => decide (l = 4)
  | 1 => decide (2 ≤ l)
  | j + 2 => c (j + 1)

def initialInternalCost (δ l : ℕ) : ℕ :=
  if δ = 0 ∧ l = 2 then 2 else 0

def compressedEntry (δ l r : ℕ) (c : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, 0 => initialInternalCost δ l
  | 0, j + 1 => if c (j + 1) = false then l else 0
  | i + 1, 0 => if c (i + 1) = true then r else 0
  | i + 1, j + 1 =>
      if c (i + 1) = true ∧ c (j + 1) = false
      then packetWeight 2 δ (min (i + 1) (j + 1) + 1) else 0

def compressedCut (δ l r : ℕ) (c : ℕ → Bool) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, compressedEntry δ l r c i j

lemma initial_allocation_cases {δ l r : ℕ}
    (hδ : δ = 0 ∨ δ = 2) (hsum : l + r = 4 - δ) (hl : 2 ∣ l) :
    (δ = 0 ∧ l = 0 ∧ r = 4) ∨
    (δ = 0 ∧ l = 2 ∧ r = 2) ∨
    (δ = 0 ∧ l = 4 ∧ r = 0) ∨
    (δ = 2 ∧ l = 0 ∧ r = 2) ∨
    (δ = 2 ∧ l = 2 ∧ r = 0) := by
  obtain ⟨q, hq⟩ := hl
  omega

lemma initial_cut_exact {δ l r : ℕ}
    (hδ : δ = 0 ∨ δ = 2) (hsum : l + r = 4 - δ) (hl : 2 ∣ l)
    (c : ℕ → Bool) :
    orientedCut (packetWeight 2 δ) (virtualColor l c) 2 = initialInternalCost δ l := by
  rw [orientedCut_eq_cutWeight]
  rcases initial_allocation_cases hδ hsum hl with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    norm_num [cutWeight, colorWeight, coloredPrefix, packetWeight,
      virtualColor, initialInternalCost]

lemma compressedEntry_self_positive (δ l r : ℕ) (c : ℕ → Bool) (i : ℕ) :
    compressedEntry δ l r c (i + 1) (i + 1) = 0 := by
  cases h : c (i + 1) <;> simp [compressedEntry, h]

lemma initial_pair_entry {δ l r : ℕ}
    (hδ : δ = 0 ∨ δ = 2) (hsum : l + r = 4 - δ) (hl : 2 ∣ l)
    (c : ℕ → Bool) (j : ℕ) :
    compressedEntry δ l r c 0 (j + 1) + compressedEntry δ l r c (j + 1) 0 =
      (if virtualColor l c 0 ≠ virtualColor l c (j + 2)
        then packetWeight 2 δ 0 else 0) +
      (if virtualColor l c 1 ≠ virtualColor l c (j + 2)
        then packetWeight 2 δ 1 else 0) := by
  rcases initial_allocation_cases hδ hsum hl with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    cases hc : c (j + 1) <;>
    norm_num [compressedEntry, virtualColor, packetWeight, hc]

lemma higher_entry (δ l r : ℕ) (c : ℕ → Bool) (i j : ℕ) :
    compressedEntry δ l r c (i + 1) (j + 1) =
      orientedEntry (packetWeight 2 δ) (virtualColor l c) (i + 2) (j + 2) := by
  have hmin : min (i + 1) (j + 1) + 1 = min (i + 2) (j + 2) := by omega
  simp only [compressedEntry, orientedEntry, virtualColor, hmin]
  rfl

lemma higher_pair_entry (δ l r : ℕ) (c : ℕ → Bool) (i j : ℕ) (hij : i ≤ j) :
    compressedEntry δ l r c (i + 1) (j + 1) +
        compressedEntry δ l r c (j + 1) (i + 1) =
      if virtualColor l c (i + 2) ≠ virtualColor l c (j + 2)
        then packetWeight 2 δ (i + 2) else 0 := by
  rw [higher_entry, higher_entry]
  exact orientedEntry_pair _ _ _ _ (by omega)

lemma compressedCut_step (δ l r : ℕ) (c : ℕ → Bool) (m : ℕ) (hm : 0 < m) :
    compressedCut δ l r c (m + 1) = compressedCut δ l r c m +
      ∑ i ∈ Finset.range m,
        (compressedEntry δ l r c i m + compressedEntry δ l r c m i) := by
  have hdiag : compressedEntry δ l r c m m = 0 := by
    cases m with
    | zero => omega
    | succ m => exact compressedEntry_self_positive δ l r c m
  unfold compressedCut
  rw [Finset.sum_range_succ]
  simp_rw [Finset.sum_range_succ]
  rw [Finset.sum_add_distrib, hdiag, add_zero]
  rw [add_assoc, ← Finset.sum_add_distrib]

lemma compressedCut_succ (δ l r : ℕ) (c : ℕ → Bool) (m : ℕ) :
    compressedCut δ l r c (m + 2) = compressedCut δ l r c (m + 1) +
      ∑ i ∈ Finset.range (m + 1),
        (compressedEntry δ l r c i (m + 1) + compressedEntry δ l r c (m + 1) i) := by
  exact compressedCut_step δ l r c (m + 1) (by omega)

lemma compression_increment {δ l r : ℕ}
    (hδ : δ = 0 ∨ δ = 2) (hsum : l + r = 4 - δ) (hl : 2 ∣ l)
    (c : ℕ → Bool) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
      (compressedEntry δ l r c i (m + 1) + compressedEntry δ l r c (m + 1) i)) =
      ∑ i ∈ Finset.range (m + 2),
        if virtualColor l c i ≠ virtualColor l c (m + 2)
          then packetWeight 2 δ i else 0 := by
  have hi := initial_pair_entry hδ hsum hl c m
  have hh : (∑ i ∈ Finset.range m,
      (compressedEntry δ l r c (i + 1) (m + 1) +
        compressedEntry δ l r c (m + 1) (i + 1))) =
      ∑ i ∈ Finset.range m,
        if virtualColor l c (i + 2) ≠ virtualColor l c (m + 2)
          then packetWeight 2 δ (i + 2) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact higher_pair_entry δ l r c i m (Nat.le_of_lt (Finset.mem_range.mp hi))
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  rw [hh]
  change
    (∑ i ∈ Finset.range m,
      if virtualColor l c (i + 2) ≠ virtualColor l c (m + 2)
        then packetWeight 2 δ (i + 2) else 0) +
      (compressedEntry δ l r c 0 (m + 1) + compressedEntry δ l r c (m + 1) 0) =
    ((∑ i ∈ Finset.range m,
      if virtualColor l c (i + 2) ≠ virtualColor l c (m + 2)
        then packetWeight 2 δ (i + 2) else 0) +
      (if virtualColor l c 1 ≠ virtualColor l c (m + 2)
        then packetWeight 2 δ 1 else 0)) +
      (if virtualColor l c 0 ≠ virtualColor l c (m + 2)
        then packetWeight 2 δ 0 else 0)
  omega

theorem compressedCut_eq_virtual {δ l r : ℕ}
    (hδ : δ = 0 ∨ δ = 2) (hsum : l + r = 4 - δ) (hl : 2 ∣ l)
    (c : ℕ → Bool) (m : ℕ) :
    compressedCut δ l r c (m + 1) =
      cutWeight (coloredPrefix (packetWeight 2 δ) (virtualColor l c) (m + 2)) := by
  rw [← orientedCut_eq_cutWeight]
  induction m with
  | zero =>
    have hb := initial_cut_exact hδ hsum hl c
    simpa only [Nat.zero_add, compressedCut, Finset.sum_range_one, compressedEntry] using hb.symm
  | succ m ih =>
    rw [compressedCut_succ, ih,
      orientedCut_succ (packetWeight 2 δ) (virtualColor l c) (m + 2)]
    congr 1
    exact compression_increment hδ hsum hl c m

theorem compressedCut_bound {δ l r : ℕ}
    (hδ : δ = 0 ∨ δ = 2) (hsum : l + r = 4 - δ) (hl : 2 ∣ l)
    (c : ℕ → Bool) (m : ℕ) :
    compressedCut δ l r c (m + 1) + δ * ((m + 2) / 2) ≤ exactCut 2 (m + 2) := by
  rw [compressedCut_eq_virtual hδ hsum hl]
  exact packet_cut_bound 2 δ (m + 2) (by norm_num) (by omega) (virtualColor l c)

lemma exp_neg_compressed_matrix (δ l r : ℕ) (c : ℕ → Bool) (m : ℕ) :
    (∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
      Real.exp (-(compressedEntry δ l r c i j : ℝ))) =
        Real.exp (-(compressedCut δ l r c m : ℝ)) := by
  simp_rw [exp_neg_nat_sum]
  rfl

theorem compressed_matrix_norm_lower_exact (δ l r : ℕ)
    (c : ℕ → Bool) (m : ℕ) (B : ℕ → ℕ → ℝ)
    (hB : ∀ i < m, ∀ j < m,
      Real.exp (-(compressedEntry δ l r c i j : ℝ)) ≤ B i j) :
    Real.exp (-(compressedCut δ l r c m : ℝ)) ≤
      ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m, B i j := by
  rw [← exp_neg_compressed_matrix]
  apply Finset.prod_le_prod
  · intro i hi
    exact Finset.prod_nonneg (fun j hj => (Real.exp_pos _).le)
  · intro i hi
    apply Finset.prod_le_prod
    · intro j hj
      exact (Real.exp_pos _).le
    · intro j hj
      exact hB i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)

lemma one_exceptional_row_budget {m : ℕ} (one : Fin m)
    (cost : Fin m → ℕ) (C t : ℕ)
    (hrow : ∀ a, cost a + (if a = one then 2 else 0) * t ≤ C) :
    (∑ a, cost a) + 2 * t ≤ m * C := by
  have hs : (∑ a, (cost a + (if a = one then 2 else 0) * t)) ≤ ∑ _a : Fin m, C :=
    Finset.sum_le_sum (fun a _ha => hrow a)
  have hcorrection : (∑ a : Fin m, (if a = one then 2 else 0) * t) = 2 * t := by
    simp only [ite_mul, zero_mul]
    simp
  simpa only [Finset.sum_add_distrib, hcorrection, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using hs

lemma row_norm_product_lower {m : ℕ} (cost : Fin m → ℕ) (rowNorm : Fin m → ℝ)
    (hrow : ∀ a, Real.exp (-(cost a : ℝ)) ≤ rowNorm a) :
    Real.exp (-((∑ a, cost a : ℕ) : ℝ)) ≤ ∏ a, rowNorm a := by
  rw [← exp_neg_nat_sum (Finset.univ : Finset (Fin m)) cost]
  exact Finset.prod_le_prod (fun a _ha => (Real.exp_pos _).le) (fun a _ha => hrow a)

end EventualIrreducibility.UniversalBinaryVirtualDraft

open Polynomial

namespace EventualIrreducibility.UniversalBinaryEntryDraft

open UniversalPacketProductDraft UniversalPacketAllocationDraft UniversalLocatedAllocationNormsDraft
  UniversalBinaryRowDataDraft UniversalBinaryVirtualDraft UniversalLocalDraft
  UniversalRootNormProductsDraft

theorem allocation_compressed_entry_bound
    {E K : Type u} [Field E] [Field K]
    {v : AbsoluteValue E ℝ} {w : AbsoluteValue K ℝ}
    {I : Type*} [Fintype I]
    (P : E[X]) (hP : P.Monic) (B : I → LocatedPacket P v)
    (G H : E[X]) (A : PacketAllocation (fun i => (B i).Q) G H)
    (hnaE : IsNonarchimedean v)
    (hdiscrete : ∀ x : E, x ≠ 0 → ∃ z : ℤ, v x = Real.exp (-(z : ℝ)))
    (htwo : v (2 : E) = Real.exp (-1))
    (ι : E →+* K) (hrestrict : ∀ x : E, w (ι x) = v x)
    (hna : IsNonarchimedean w) (hs : (P.map ι).Splits)
    (δ t : ℕ) (hδ : δ = 0 ∨ δ = 2) (_ht : 0 < t)
    (q : ℕ → I) (c : ℕ → Bool)
    (hcenter : ∀ i < t, ∀ j < t, (B (q i)).center = (B (q j)).center)
    (hradius : ∀ i j, i < j → j < t → (B (q i)).radius < (B (q j)).radius)
    (hfirstdegree : (B (q 0)).Q.natDegree = 4 - δ)
    (hfirstradius : (B (q 0)).radius = Real.exp (-(1 : ℝ) / 2))
    (hdegree : ∀ j, 0 < j → j < t → (B (q j)).Q.natDegree = packetWeight 2 δ (j + 1))
    (hlater : ∀ j, 0 < j → j < t →
      0 < (B (q j)).Q.natDegree ∧
      (B (q j)).radius = Real.exp (-(1 : ℝ) / ((B (q j)).Q.natDegree : ℝ)))
    (hselectL : ∀ j, 0 < j → j < t → A.left (q j) = if c j = true then (B (q j)).Q else 1)
    (hselectR : ∀ j, 0 < j → j < t → A.right (q j) = if c j = true then 1 else (B (q j)).Q)
    (hdisc : δ = 0 → w ((B (q 0)).Q.map ι).discr = Real.exp (-8)) :
    ∀ i < t, ∀ j < t,
      Real.exp (-(compressedEntry δ (A.left (q 0)).natDegree (A.right (q 0)).natDegree c i j : ℝ)) ≤
        v ((A.left (q i)).localResultant (A.right (q j))) := by
  have hforward (i j : ℕ) (hij : i < j) (hjt : j < t) :
      v ((A.left (q i)).localResultant (A.right (q j))) =
        if c j = true then 1 else Real.exp (-((A.left (q i)).natDegree : ℝ)) := by
    have hj0 : 0 < j := by omega
    by_cases hc : c j = true
    · rw [hselectR j hj0 hjt, if_pos hc, if_pos hc]
      simp
    · rw [if_neg hc]
      apply allocation_cross_norm_later_right P hP B G H A hnaE ι hrestrict hna hs
        (q i) (q j) (hcenter i (by omega) j hjt) (hradius i j hij hjt)
        (hlater j hj0 hjt).1 (hlater j hj0 hjt).2
      rw [hselectR j hj0 hjt,if_neg hc]
  have hbackward (i j : ℕ) (hij : i < j) (hjt : j < t) :
      v ((A.left (q j)).localResultant (A.right (q i))) =
        if c j = true then Real.exp (-((A.right (q i)).natDegree : ℝ)) else 1 := by
    have hj0 : 0 < j := by omega
    by_cases hc : c j = true
    · rw [if_pos hc]
      apply allocation_cross_norm_later_left P hP B G H A hnaE ι hrestrict hna hs
        (q i) (q j) (hcenter i (by omega) j hjt) (hradius i j hij hjt)
        (hlater j hj0 hjt).1 (hlater j hj0 hjt).2
      rw [hselectL j hj0 hjt,if_pos hc]
    · rw [hselectL j hj0 hjt,if_neg hc,if_neg hc]
      simp
  intro i hit j hjt
  cases i with
  | zero =>
    cases j with
    | zero =>
      exact initial_allocation_internal_norm P hP (B (q 0)) δ hδ hfirstdegree hfirstradius
        hnaE hdiscrete htwo ι hrestrict hna hs hdisc
        (A.left (q 0)) (A.right (q 0)) (A.monic_left _) (A.monic_right _) (A.pair_product _)
    | succ j =>
      rw [hforward 0 (j + 1) (by omega) hjt]
      cases hc : c (j + 1) <;> simp [compressedEntry,hc]
  | succ i =>
    cases j with
    | zero =>
      rw [hbackward 0 (i + 1) (by omega) hit]
      cases hc : c (i + 1) <;> simp [compressedEntry,hc]
    | succ j =>
      by_cases hij : i + 1 < j + 1
      · rw [hforward (i + 1) (j + 1) hij hjt]
        rw [hselectL (i + 1) (by omega) hit]
        cases hci : c (i + 1) <;> cases hcj : c (j + 1) <;>
          simp [compressedEntry,hci,hcj,hdegree _ (by omega) hit,
            min_eq_left (Nat.le_of_lt hij)]
      · by_cases hji : j + 1 < i + 1
        · rw [hbackward (j + 1) (i + 1) hji hit]
          rw [hselectR (j + 1) (by omega) hjt]
          cases hci : c (i + 1) <;> cases hcj : c (j + 1) <;>
            simp [compressedEntry,hci,hcj,hdegree _ (by omega) hjt,
              min_eq_right (Nat.le_of_lt hji)]
        · have heq : j = i := by omega
          subst j
          rw [hselectL (i + 1) (by omega) hit, hselectR (i + 1) (by omega) hit]
          cases hc : c (i + 1) <;> simp [compressedEntry,hc]

end EventualIrreducibility.UniversalBinaryEntryDraft

open Polynomial

namespace EventualIrreducibility.UniversalActualBinaryRowsDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalPacketAllocationDraft
  UniversalBinaryFamilyDraft UniversalBinaryFamilyBuildersDraft UniversalBinaryRowDataDraft
  UniversalBinaryQuarticFamilyDraft UniversalLocatedAllocationNormsDraft UniversalLocalSourceDraft
  UniversalBinaryEntryDraft UniversalBinaryVirtualDraft UniversalLocalDraft

theorem actual_binary_row_certificate
    (n r m : ℕ) (hn : 2 ≤ n) (hr : 2 ≤ r)
    (D : PrimeToPUnramifiedData 2 m)
    (B : BinaryIndex m r → LocatedPacket ((fInt n).map (Int.castRingHom D.E)) D.v)
    (one : Fin m) (hone : D.ζ one = 1)
    (hc : ∀ a i, (B (.inr (a,i))).center = D.ζ a)
    (hrad : ∀ a i, (B (.inr (a,i))).radius = Real.exp (-(1 : ℝ) / (binaryDenom i : ℝ)))
    (hd : ∀ a i, (B (.inr (a,i))).Q.natDegree = binaryWeight (if a = one then 2 else 0) r i)
    (hzc : (B (.inl ())).center = 0)
    (hproduct : ((fInt n).map (Int.castRingHom D.E)) = ∏ q, (B q).Q)
    (S : ValuedSplittingData D.E D.v ((fInt n).map (Int.castRingHom D.E)))
    (hsource : padicValNat 2 n = r ∨ padicValNat 2 (n + 1) = r)
    (G H : D.E[X]) (A : PacketAllocation (fun q => (B q).Q) G H)
    (a : Fin m) :
    ∃ V : ℕ,
      Real.exp (-(V : ℝ)) ≤
        (∏ i : Fin (binaryCount r), ∏ j : Fin (binaryCount r),
          D.v ((A.left (.inr (a,i))).localResultant (A.right (.inr (a,j))))) ∧
      V + (if a = one then 2 else 0) * (r / 2) ≤ exactCut 2 r := by
  classical
  let P : D.E[X] := (fInt n).map (Int.castRingHom D.E)
  let ι : D.E →+* S.K := algebraMap D.E S.K
  let δ : ℕ := if a = one then 2 else 0
  have hδ : δ = 0 ∨ δ = 2 := by dsimp [δ]; split_ifs <;> omega
  have ht : 0 < binaryCount r := binaryCount_pos r (by omega)
  let idx (j : ℕ) : Fin (binaryCount r) := ⟨j % binaryCount r, Nat.mod_lt j ht⟩
  have hidx (j : ℕ) (hj : j < binaryCount r) : (idx j : ℕ) = j := Nat.mod_eq_of_lt hj
  have hidxFin (i : Fin (binaryCount r)) : idx i = i := Fin.ext (hidx i i.isLt)
  let q (j : ℕ) : BinaryIndex m r := .inr (a,idx j)
  have hex (i : Fin (binaryCount r)) : ∃ b : Bool, (0 < (i : ℕ) →
      A.left (.inr (a,i)) = (if b = true then (B (.inr (a,i))).Q else 1) ∧
      A.right (.inr (a,i)) = (if b = true then 1 else (B (.inr (a,i))).Q)) := by
    by_cases hi : (i : ℕ) = 0
    · exact ⟨false,by omega⟩
    · have hirr := actual_binary_higher_packet_irreducible n r m hr D B one hrad hd a i hi
      rcases irreducible_packet_allocation _ G H A (.inr (a,i)) hirr with h | h
      · exact ⟨true,fun _ => by simpa using h⟩
      · exact ⟨false,fun _ => by simpa using h⟩
  choose color hcolor using hex
  let c (j : ℕ) : Bool := color (idx j)
  let l := (A.left (q 0)).natDegree
  let s := (A.right (q 0)).natDegree
  have hr1 : r ≠ 1 := by omega
  have hP : P.Monic := (monic_fInt n (by omega)).map (Int.castRingHom D.E)
  have hfirstdeg : (B (q 0)).Q.natDegree = 4 - δ := by
    simp only [q,hd,δ,binaryWeight,if_neg hr1]
    rw [show idx 0 = ⟨0,ht⟩ by apply Fin.ext; exact hidx 0 ht]
    rfl
  have hfirstrad : (B (q 0)).radius = Real.exp (-(1 : ℝ) / 2) := by
    rw [hrad]
    norm_num only [binaryDenom,hidx 0 ht,Nat.zero_add,pow_one]
  have hdegs := allocated_degree_sum_and_divisibility P B G H A D.nonarchimedean D.discrete
    (q 0) 2 (by omega) (by simpa using hfirstrad)
  have hsum : l + s = 4 - δ := hdegs.1.trans hfirstdeg
  have hl : 2 ∣ l := hdegs.2.1
  let matrix (i j : ℕ) : ℝ := D.v ((A.left (q i)).localResultant (A.right (q j)))
  have hscalar := adjacent_product_norm_from_source D.v n 2 r (by omega)
    Nat.prime_two (by omega) D.nat_norm hsource
  have htwo : D.v (2 : D.E) = Real.exp (-1) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    simpa [padicValNat_self] using D.nat_norm 2 (by omega)
  have hdisc (hδ0 : δ = 0) : S.w ((B (q 0)).Q.map ι).discr = Real.exp (-8) := by
    have ha : a ≠ one := by intro h; simp [δ,h] at hδ0
    have h := binary_family_quartic_discriminant n r m hn hr D B one hone hc hrad hd hzc
      hproduct S hscalar a ha
    convert h using 1
    congr 3
  have hentry := allocation_compressed_entry_bound P hP B G H A D.nonarchimedean
    D.discrete htwo ι S.restrict S.nonarchimedean S.splits δ (binaryCount r) hδ ht q c
    (fun i hi j hj => by simp only [q,hc])
    (by
      intro i j hij hj
      simp only [q,hrad]
      apply FirstFace.exp_radius_strict_of_denominators _ _ (binaryDenom_pos _)
      apply binaryDenom_strictMono
      simpa only [hidx i (by omega),hidx j hj] using hij)
    hfirstdeg hfirstrad
    (by
      intro j hj0 hj
      rw [hd]
      simp only [binaryWeight,if_neg hr1,hidx j hj]
      cases j with
      | zero => omega
      | succ j => simp [mergedWeight,packetWeight])
    (by
      intro j hj0 hj
      have hdegree : (B (q j)).Q.natDegree = binaryDenom (idx j) := by
        rw [hd]
        simp only [binaryWeight,if_neg hr1,hidx j hj]
        cases j with
        | zero => omega
        | succ j => simp [mergedWeight,binaryDenom]
      refine ⟨by rw [hdegree]; exact binaryDenom_pos _, ?_⟩
      rw [hrad,hdegree])
    (fun j hj0 hj => (hcolor (idx j) (by rw [hidx j hj]; exact hj0)).1)
    (fun j hj0 hj => (hcolor (idx j) (by rw [hidx j hj]; exact hj0)).2) hdisc
  have hcount : binaryCount r = (r - 2) + 1 := by simp only [binaryCount,if_neg hr1]; omega
  have hlast : r - 2 + 2 = r := by omega
  let V : ℕ := compressedCut δ l s c (binaryCount r)
  refine ⟨V, ?_, ?_⟩
  · have hlow := compressed_matrix_norm_lower_exact δ l s c (binaryCount r) matrix hentry
    change Real.exp (-(V : ℝ)) ≤ _ at hlow
    have hmatrix :
        (∏ i : Fin (binaryCount r), ∏ j : Fin (binaryCount r),
          D.v ((A.left (.inr (a,i))).localResultant (A.right (.inr (a,j))))) =
        ∏ i : Fin (binaryCount r), ∏ j : Fin (binaryCount r), matrix i j := by
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro j hj
      simp only [matrix,q,hidxFin]
    have hrange : (∏ i : Fin (binaryCount r), ∏ j : Fin (binaryCount r), matrix i j) =
        ∏ i ∈ Finset.range (binaryCount r), ∏ j ∈ Finset.range (binaryCount r), matrix i j := by
      calc
        _ = ∏ i ∈ Finset.range (binaryCount r), ∏ j : Fin (binaryCount r), matrix i j :=
          Fin.prod_univ_eq_prod_range
            (fun i : ℕ => ∏ j : Fin (binaryCount r), matrix i j) (binaryCount r)
        _ = _ := by
          apply Finset.prod_congr rfl
          intro i hi
          exact Fin.prod_univ_eq_prod_range (matrix i) (binaryCount r)
    rw [hmatrix,hrange]
    exact hlow
  · have hcut := compressedCut_bound hδ hsum hl c (r - 2)
    simpa only [← hcount,hlast,δ,V] using hcut

end EventualIrreducibility.UniversalActualBinaryRowsDraft

open Polynomial

namespace EventualIrreducibility.UniversalActualBinaryResultantDraft

open UniversalSlopeDraft UniversalPacketProductDraft UniversalPacketAllocationDraft
  UniversalBinaryFamilyDraft UniversalBinaryFamilyBuildersDraft UniversalActualBinaryRowsDraft
  UniversalLocatedAllocationNormsDraft UniversalLocatedNormsDraft UniversalWholePacketMatrixDraft
  UniversalBinaryVirtualDraft UniversalLocalDraft UniversalIntegerLocalValuationDraft

theorem actual_binary_resultant_norm_and_cut_ge_two
    (hstd : StandardSlopeFactorInput.{0}) (hspl : StandardValuedSplittingInput.{0})
    (n r m : ℕ) (hn : 2 ≤ n) (hr : 2 ≤ r)
    (D : PrimeToPUnramifiedData 2 m)
    (hsource : (padicValNat 2 n = r ∧ n = 2 ^ r * m) ∨
      (padicValNat 2 (n + 1) = r ∧ n + 1 = 2 ^ r * m))
    (G H : D.E[X]) (hG : G.Monic) (hH : H.Monic)
    (hfactor : ((fInt n).map (Int.castRingHom D.E)) = G * H) :
    ∃ V : ℕ, Real.exp (-(V : ℝ)) ≤ D.v (G.localResultant H) ∧
      V + 2 * (r / 2) ≤ m * exactCut 2 r := by
  classical
  let P : D.E[X] := (fInt n).map (Int.castRingHom D.E)
  have hP : P.Monic := (monic_fInt n (by omega)).map (Int.castRingHom D.E)
  obtain ⟨one,B,hone,hc,hrad,hd,hzc,hzd,hsep,hprod⟩ :=
    actual_binary_common_field_product hstd hspl n r m hn (by omega) D hsource
  obtain ⟨S⟩ := hspl D.E D.v D.nonarchimedean D.norm_eq P hP.ne_zero
  let ι : D.E →+* S.K := algebraMap D.E S.K
  have hcop := located_pairwise_coprime P hP B ι S.restrict S.nonarchimedean S.splits hsep
  obtain ⟨A⟩ := exists_packet_allocation P G H hG hH (fun q => (B q).Q)
    (fun q => (B q).monic) hcop hprod hfactor
  have hrows (a : Fin m) := actual_binary_row_certificate n r m hn hr D B one hone hc hrad hd
    hzc hprod S (hsource.imp And.left And.left) G H A a
  choose cost hrow hcost using hrows
  let rowNorm (a : Fin m) : ℝ := ∏ i : Fin (binaryCount r), ∏ j : Fin (binaryCount r),
    D.v ((A.left (.inr (a,i))).localResultant (A.right (.inr (a,j))))
  have hcross (q t : BinaryIndex m r)
      (hcenters : D.v ((B q).center - (B t).center) = 1) :
      D.v ((A.left q).localResultant (A.right t)) = 1 :=
    allocation_distinct_center_norm P hP B G H A D.nonarchimedean
      ι S.restrict S.nonarchimedean S.splits q t hcenters
  have hzero (q : BinaryIndex m r) :
      D.v ((A.left (.inl ())).localResultant (A.right q)) = 1 ∧
        D.v ((A.left q).localResultant (A.right (.inl ()))) = 1 := by
    cases q with
    | inl u =>
      cases u
      have h := whole_allocation_self_norm_one D.v _ G H A (.inl ())
        (whole_allocation_of_small_degree _ G H A (.inl ()) hzd)
      exact ⟨h,h⟩
    | inr ai =>
      constructor
      · apply hcross
        simpa only [hzc,hc,zero_sub,AbsoluteValue.map_neg] using D.units ai.1
      · apply hcross
        simpa only [hzc,hc,sub_zero] using D.units ai.1
  have hoff (a b : Fin m) (hab : a ≠ b) (i j : Fin (binaryCount r)) :
      D.v ((A.left (.inr (a,i))).localResultant (A.right (.inr (b,j)))) = 1 := by
    apply hcross
    simpa only [hc] using D.separated a b hab
  have hresultant : D.v (G.localResultant H) = ∏ a, rowNorm a := by
    rw [resultant_norm_of_packet_allocation D.v _ G H A,
      block_diagonal_product _ hzero hoff]
  refine ⟨∑ a, cost a, ?_, ?_⟩
  · rw [hresultant]
    exact row_norm_product_lower cost rowNorm hrow
  · exact one_exceptional_row_budget one cost (exactCut 2 r) (r / 2) hcost

theorem actual_binary_resultant_norm_r_one
    (hstd : StandardSlopeFactorInput.{0}) (hspl : StandardValuedSplittingInput.{0})
    (n m : ℕ) (hn : 2 ≤ n) (D : PrimeToPUnramifiedData 2 m)
    (hsource : (padicValNat 2 n = 1 ∧ n = 2 ^ 1 * m) ∨
      (padicValNat 2 (n + 1) = 1 ∧ n + 1 = 2 ^ 1 * m))
    (G H : D.E[X]) (hG : G.Monic) (hH : H.Monic)
    (hfactor : ((fInt n).map (Int.castRingHom D.E)) = G * H) :
    D.v (G.localResultant H) = 1 := by
  classical
  let P : D.E[X] := (fInt n).map (Int.castRingHom D.E)
  have hP : P.Monic := (monic_fInt n (by omega)).map (Int.castRingHom D.E)
  obtain ⟨one,B,hone,hc,hrad,hd,hzc,hzd,hsep,hprod⟩ :=
    actual_binary_common_field_product hstd hspl n 1 m hn (by omega) D hsource
  obtain ⟨S⟩ := hspl D.E D.v D.nonarchimedean D.norm_eq P hP.ne_zero
  let ι : D.E →+* S.K := algebraMap D.E S.K
  have hcop := located_pairwise_coprime P hP B ι S.restrict S.nonarchimedean S.splits hsep
  obtain ⟨A⟩ := exists_packet_allocation P G H hG hH (fun q => (B q).Q)
    (fun q => (B q).monic) hcop hprod hfactor
  have hwhole (q : BinaryIndex m 1) :
      (A.left q = (B q).Q ∧ A.right q = 1) ∨
        (A.left q = 1 ∧ A.right q = (B q).Q) := by
    cases q with
    | inl u =>
      cases u
      exact whole_allocation_of_small_degree _ G H A (.inl ()) hzd
    | inr ai =>
      have hi0 : (ai.2 : ℕ) = 0 := by have := ai.2.isLt; change _ < 1 at this; omega
      by_cases ha : ai.1 = one
      · apply whole_allocation_of_small_degree _ G H A (.inr ai)
        simp [hd,ha,binaryWeight,hi0,packetWeight]
      · apply irreducible_packet_allocation _ G H A (.inr ai)
        apply (B (.inr ai)).irreducible_of_degree P D.nonarchimedean 2 (by omega)
          (by simpa only [hi0,binaryDenom,Nat.zero_add,pow_one] using hrad ai.1 ai.2)
          (by simp [hd,ha,binaryWeight,hi0,packetWeight]) D.discrete
  have hcross (q t : BinaryIndex m 1)
      (hcenters : D.v ((B q).center - (B t).center) = 1) :
      D.v ((A.left q).localResultant (A.right t)) = 1 :=
    allocation_distinct_center_norm P hP B G H A D.nonarchimedean
      ι S.restrict S.nonarchimedean S.splits q t hcenters
  have hzero (q : BinaryIndex m 1) :
      D.v ((A.left (.inl ())).localResultant (A.right q)) = 1 ∧
        D.v ((A.left q).localResultant (A.right (.inl ()))) = 1 := by
    cases q with
    | inl u =>
      cases u
      have h := whole_allocation_self_norm_one D.v _ G H A (.inl ()) (hwhole (.inl ()))
      exact ⟨h,h⟩
    | inr ai =>
      constructor
      · apply hcross
        simpa only [hzc,hc,zero_sub,AbsoluteValue.map_neg] using D.units ai.1
      · apply hcross
        simpa only [hzc,hc,sub_zero] using D.units ai.1
  have hoff (a b : Fin m) (hab : a ≠ b) (i j : Fin (binaryCount 1)) :
      D.v ((A.left (.inr (a,i))).localResultant (A.right (.inr (b,j)))) = 1 := by
    apply hcross
    simpa only [hc] using D.separated a b hab
  rw [resultant_norm_of_packet_allocation D.v _ G H A, block_diagonal_product _ hzero hoff]
  apply Finset.prod_eq_one
  intro a ha
  apply Finset.prod_eq_one
  intro i hi
  apply Finset.prod_eq_one
  intro j hj
  have hij : i = j := by
    apply Fin.ext
    have hi' := i.isLt
    have hj' := j.isLt
    change _ < 1 at hi' hj'
    omega
  subst j
  exact whole_allocation_self_norm_one D.v _ G H A (.inr (a,i)) (hwhole (.inr (a,i)))

theorem actual_binary_resultant_norm_and_cut
    (hstd : StandardSlopeFactorInput.{0}) (hspl : StandardValuedSplittingInput.{0})
    (n r m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (D : PrimeToPUnramifiedData 2 m)
    (hsource : (padicValNat 2 n = r ∧ n = 2 ^ r * m) ∨
      (padicValNat 2 (n + 1) = r ∧ n + 1 = 2 ^ r * m))
    (G H : D.E[X]) (hG : G.Monic) (hH : H.Monic)
    (hfactor : ((fInt n).map (Int.castRingHom D.E)) = G * H) :
    ∃ V : ℕ, Real.exp (-(V : ℝ)) ≤ D.v (G.localResultant H) ∧
      V + 2 * (r / 2) ≤ m * exactCut 2 r := by
  by_cases hr1 : r = 1
  · subst r
    refine ⟨0, ?_, by simp [exactCut]⟩
    rw [actual_binary_resultant_norm_r_one hstd hspl n m hn D hsource G H hG hH hfactor]
    simp
  · exact actual_binary_resultant_norm_and_cut_ge_two hstd hspl n r m hn (by omega)
      D hsource G H hG hH hfactor

lemma normalized_integer_exponent_le
    {E : Type*} [Field E] (v : AbsoluteValue E ℝ) (p : ℕ)
    (hnorm : ∀ t : ℕ, t ≠ 0 → v (t : E) = Real.exp (-(padicValNat p t : ℝ)))
    (z : ℤ) (V : ℕ) (hV : Real.exp (-(V : ℝ)) ≤ v (z : E)) :
    z ≠ 0 ∧ padicValNat p z.natAbs ≤ V := by
  have hz : z ≠ 0 := by
    intro hz
    simp only [hz,Int.cast_zero,map_zero] at hV
    exact (not_le_of_gt (Real.exp_pos _)) hV
  refine ⟨hz, ?_⟩
  rw [integer_norm_from_nat_normalization v p hnorm z hz] at hV
  have h := Real.exp_le_exp.mp hV
  have hcast : (padicValNat p z.natAbs : ℝ) ≤ (V : ℝ) := by linarith
  exact_mod_cast hcast

theorem actual_binary_integer_resultant_valuation
    (hstd : StandardSlopeFactorInput.{0}) (hspl : StandardValuedSplittingInput.{0})
    (n r m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (D : PrimeToPUnramifiedData 2 m)
    (hsource : (padicValNat 2 n = r ∧ n = 2 ^ r * m) ∨
      (padicValNat 2 (n + 1) = r ∧ n + 1 = 2 ^ r * m))
    (g h : ℤ[X]) (hg : g.Monic) (hh : h.Monic) (hfactor : fInt n = g * h) :
    g.localResultant h ≠ 0 ∧
      padicValNat 2 (g.localResultant h).natAbs + 2 * (r / 2) ≤ m * exactCut 2 r := by
  let G : D.E[X] := g.map (Int.castRingHom D.E)
  let H : D.E[X] := h.map (Int.castRingHom D.E)
  have hGH : ((fInt n).map (Int.castRingHom D.E)) = G * H := by
    simpa only [G,H,Polynomial.map_mul] using congrArg (Polynomial.map (Int.castRingHom D.E)) hfactor
  obtain ⟨V,hV,hcut⟩ := actual_binary_resultant_norm_and_cut hstd hspl n r m hn hr D hsource
    G H (hg.map _) (hh.map _) hGH
  have hnorm : Real.exp (-(V : ℝ)) ≤ D.v ((g.localResultant h : ℤ) : D.E) := by
    simpa only [G,H,Polynomial.localResultant,Polynomial.Monic.natDegree_map hg,Polynomial.Monic.natDegree_map hh,
      Polynomial.resultant_map_map,Int.coe_castRingHom] using hV
  obtain ⟨hne,hval⟩ := normalized_integer_exponent_le D.v 2 D.nat_norm (g.localResultant h) V hnorm
  exact ⟨hne,by omega⟩

end EventualIrreducibility.UniversalActualBinaryResultantDraft

open Polynomial

namespace EventualIrreducibility.UniversalAllPrimeLocalBoundDraft

open UniversalSlopeDraft UniversalLocalDraft UniversalLocalSourceDraft
  UniversalIntegerLocalValuationDraft UniversalActualBinaryResultantDraft

theorem actual_integer_local_resultant_bound
    (hunram : StandardUnramifiedInput)
    (hstd : StandardSlopeFactorInput.{0}) (hspl : StandardValuedSplittingInput.{0})
    (n : ℕ) (hn : 2 ≤ n)
    (g h : ℤ[X]) (hg : g.Monic) (hh : h.Monic) (hfactor : fInt n = g * h)
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ n * (n + 1)) :
    ∃ M m : ℕ, (M = n ∨ M = n + 1) ∧
      M = m * p ^ padicValNat p (n * (n + 1)) ∧
      padicValNat p (g.localResultant h).natAbs +
        2 * (padicValNat p (n * (n + 1)) / 2) ≤
          m * exactCut p (padicValNat p (n * (n + 1))) := by
  obtain ⟨hr,m,hm,hpm,hsource⟩ := select_local_source n p (by omega) hp hdiv
  obtain ⟨D⟩ := hunram p m hp hm hpm
  have hbound : padicValNat p (g.localResultant h).natAbs +
      2 * (padicValNat p (n * (n + 1)) / 2) ≤
        m * exactCut p (padicValNat p (n * (n + 1))) := by
    by_cases hp2 : p = 2
    · subst p
      exact (actual_binary_integer_resultant_valuation hstd hspl n
        (padicValNat 2 (n * (n + 1))) m hn hr D hsource g h hg hh hfactor).2
    · exact (actual_odd_integer_resultant_valuation hstd hspl n p
        (padicValNat p (n * (n + 1))) m hn hp hp2 hr D hsource g h hg hh hfactor).2
  rcases hsource with ⟨hv,hM⟩ | ⟨hv,hM⟩
  · exact ⟨n,m,Or.inl rfl,by simpa only [Nat.mul_comm] using hM,hbound⟩
  · exact ⟨n + 1,m,Or.inr rfl,by simpa only [Nat.mul_comm] using hM,hbound⟩

end EventualIrreducibility.UniversalAllPrimeLocalBoundDraft

namespace EventualIrreducibility.TrivialValuedSplittingHelpers

theorem discreteUniformity_of_norm_eq_one {K : Type u} [NormedField K]
    (htriv : ∀ x : K, x ≠ 0 → ‖x‖ = 1) : DiscreteUniformity K := by
  constructor
  apply Metric.uniformSpace_eq_bot.mpr
  refine ⟨1, zero_lt_one, ?_⟩
  intro x y hxy
  rw [dist_eq_norm, htriv (x - y) (sub_ne_zero.mpr hxy)]

theorem completeSpace_of_norm_eq_one {K : Type u} [NormedField K]
    (htriv : ∀ x : K, x ≠ 0 → ‖x‖ = 1) : CompleteSpace K := by
  let : DiscreteUniformity K := discreteUniformity_of_norm_eq_one htriv
  infer_instance

theorem trivial_isNonarchimedean (K : Type u) [Field K] [DecidableEq K] :
    IsNonarchimedean (AbsoluteValue.trivial : AbsoluteValue K ℝ) := by
  classical
  intro x y
  change (if x + y = 0 then (0 : ℝ) else 1) ≤
    max (if x = 0 then 0 else 1) (if y = 0 then 0 else 1)
  split_ifs <;> simp_all

theorem trivial_completeSpace (K : Type u) [Field K] [DecidableEq K] :
    letI : NormedField K :=
      (AbsoluteValue.trivial : AbsoluteValue K ℝ).toNormedField
    CompleteSpace K := by
  classical
  let : NormedField K :=
    (AbsoluteValue.trivial : AbsoluteValue K ℝ).toNormedField
  apply completeSpace_of_norm_eq_one
  intro x hx
  exact AbsoluteValue.trivial_apply hx

theorem trivial_restricts {E K : Type u} [NormedField E] [Field K] [DecidableEq K]
    [Algebra E K]
    (v : AbsoluteValue E ℝ) (hv : ∀ x, v x = ‖x‖)
    (htriv : ∀ x : E, x ≠ 0 → ‖x‖ = 1) (x : E) :
    (AbsoluteValue.trivial : AbsoluteValue K ℝ) (algebraMap E K x) = v x := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  · have hmap : algebraMap E K x ≠ 0 := by
      intro h
      apply hx
      apply (algebraMap E K).injective
      simpa using h
    rw [AbsoluteValue.trivial_apply hmap, hv, htriv x hx]

end EventualIrreducibility.TrivialValuedSplittingHelpers

open Polynomial

namespace EventualIrreducibility.UniversalSlopeDraft

theorem valuedSplittingData_nontrivial
    (E : Type u) [NontriviallyNormedField E] [CompleteSpace E]
    (v : AbsoluteValue E ℝ) (hna : IsNonarchimedean v)
    (hv : ∀ x : E, v x = ‖x‖) (P : E[X]) :
    Nonempty (ValuedSplittingData E v P) := by
  let : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (by
      intro x y
      simpa only [hv] using hna x y)
  let : NormedField P.SplittingField :=
    spectralNorm.normedField E P.SplittingField
  let : CompleteSpace P.SplittingField :=
    spectralNorm.completeSpace E P.SplittingField
  refine ⟨{
    K := P.SplittingField
    w := NormedField.toAbsoluteValue P.SplittingField
    nonarchimedean := ?_
    norm_eq := ?_
    restrict := ?_
    splits := Polynomial.SplittingField.splits P
  }⟩
  · change IsNonarchimedean (spectralNorm E P.SplittingField)
    exact isNonarchimedean_spectralNorm
  · intro x
    rfl
  · intro x
    change spectralNorm E P.SplittingField
      (algebraMap E P.SplittingField x) = v x
    rw [spectralNorm_extends, hv]

end EventualIrreducibility.UniversalSlopeDraft

open Polynomial

namespace EventualIrreducibility.UniversalSlopeDraft

theorem valuedSplittingData_trivial
    (E : Type u) [NormedField E]
    (v : AbsoluteValue E ℝ) (hv : ∀ x : E, v x = ‖x‖)
    (htriv : ∀ x : E, x ≠ 0 → ‖x‖ = 1) (P : E[X]) :
    Nonempty (ValuedSplittingData E v P) := by
  classical
  let : NormedField P.SplittingField :=
    (AbsoluteValue.trivial : AbsoluteValue P.SplittingField ℝ).toNormedField
  let : CompleteSpace P.SplittingField :=
    TrivialValuedSplittingHelpers.trivial_completeSpace P.SplittingField
  refine ⟨{
    K := P.SplittingField
    w := AbsoluteValue.trivial
    nonarchimedean :=
      TrivialValuedSplittingHelpers.trivial_isNonarchimedean P.SplittingField
    norm_eq := fun _ => rfl
    restrict := ?_
    splits := Polynomial.SplittingField.splits P
  }⟩
  exact TrivialValuedSplittingHelpers.trivial_restricts v hv htriv

theorem standardValuedSplittingInput_proved : StandardValuedSplittingInput.{u} := by
  classical
  intro E instNorm instComplete v hna hv P _hP
  by_cases hnt : ∃ x : E, x ≠ 0 ∧ ‖x‖ ≠ 1
  · let : NontriviallyNormedField E := NontriviallyNormedField.ofNormNeOne hnt
    exact valuedSplittingData_nontrivial E v hna hv P
  · exact valuedSplittingData_trivial E v hv (by
      intro x hx
      by_contra h
      exact hnt ⟨x, hx, h⟩) P

end EventualIrreducibility.UniversalSlopeDraft

open Polynomial

namespace EventualIrreducibility.UniversalSlopeDraft

theorem gauss_alternative_of_pure_radius
    {E : Type u} [Field E] (P : E[X]) (hP : P ≠ 0)
    (v : AbsoluteValue E ℝ) (c r : ℝ) (hc : 0 < c) (hr : 0 < r)
    (hpure : PureGauss P v r) :
    PureGauss P v c ∨ ∃ k, IsMinGaussIndex P v c k ∧ IsMaxGaussIndex P v c k := by
  obtain ⟨i, hi⟩ := P.exists_min_eq_gaussNorm v hc.le
  change IsMinGaussIndex P v c i at hi
  obtain ⟨j, hj⟩ := exists_maxGaussIndex (v := v) hc P hP
  rcases lt_trichotomy c r with hlt | heq | hgt
  · have hj0 : j = 0 := Nat.eq_zero_of_le_zero
      (gauss_attaining_index_mono hc hlt P hP j 0 hj.1 hpure.1.1)
    have hi0 : i = 0 := by
      have := minGaussIndex_le_maxGaussIndex P i j hi hj
      omega
    exact Or.inr ⟨0, by simpa only [hi0] using hi, by simpa only [hj0] using hj⟩
  · exact Or.inl (heq ▸ hpure)
  · have hid : i = P.natDegree := by
      have hlow := gauss_attaining_index_mono hr hgt P hP P.natDegree i hpure.2.1 hi.1
      have hupp := gauss_attainer_le_degree P hP hc i hi.1
      omega
    have hjd : j = P.natDegree := by
      have hlow := minGaussIndex_le_maxGaussIndex P i j hi hj
      have hupp := gauss_attainer_le_degree P hP hc j hj.1
      omega
    exact Or.inr ⟨P.natDegree, by simpa only [hid] using hi, by simpa only [hjd] using hj⟩

theorem irreducible_eq_X_of_coeff_zero
    {E : Type u} [Field E] (P : E[X]) (hP : P.Monic)
    (hI : Irreducible P) (hzero : P.coeff 0 = 0) : P = X := by
  exact (Polynomial.eq_of_monic_of_associated (monic_X : (X : E[X]).Monic) hP
    ((irreducible_X : Irreducible (X : E[X])).associated_of_dvd hI
      (Polynomial.X_dvd_iff.mpr hzero))).symm

theorem gauss_X_flat {E : Type u} [Field E]
    (v : AbsoluteValue E ℝ) (c : ℝ) (hc : 0 < c) :
    IsMinGaussIndex (X : E[X]) v c 1 ∧ IsMaxGaussIndex (X : E[X]) v c 1 := by
  have hnorm : (X : E[X]).gaussNorm v c = c := by
    simp [Polynomial.gaussNorm]
  constructor
  · constructor
    · simpa using hnorm
    · intro k hk
      have hk0 : k = 0 := by omega
      simpa [hk0, hnorm] using hc
  · constructor
    · simpa using hnorm
    · intro k hk
      have hk1 : k ≠ 1 := by omega
      simpa [Polynomial.coeff_X, hk1, Ne.symm hk1, hnorm] using hc

theorem pureGauss_of_trivial_norm
    (E : Type u) [NormedField E] (v : AbsoluteValue E ℝ)
    (hv : ∀ x : E, v x = ‖x‖) (htriv : ∀ x : E, x ≠ 0 → ‖x‖ = 1)
    (P : E[X]) (hP : P.Monic) (hzero : P.coeff 0 ≠ 0) : PureGauss P v 1 := by
  have hv1 : ∀ x : E, x ≠ 0 → v x = 1 := by
    intro x hx
    rw [hv, htriv x hx]
  have hnorm : P.gaussNorm v 1 = 1 := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := P.exists_eq_gaussNorm v (1 : ℝ)
      rw [hi, one_pow, mul_one]
      by_cases hz : P.coeff i = 0
      · simp [hz]
      · exact (hv1 _ hz).le
    · have h := P.le_gaussNorm v (show (0 : ℝ) ≤ 1 by norm_num) P.natDegree
      simpa [hP.coeff_natDegree] using h
  constructor
  · constructor
    · simp [hnorm, hv1 _ hzero]
    · intro k hk
      omega
  · constructor
    · simp [hnorm, hP.coeff_natDegree]
    · intro k hk
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hk, hnorm]

end EventualIrreducibility.UniversalSlopeDraft

open Polynomial

namespace EventualIrreducibility.UniversalSlopeDraft

theorem coeff_weight_le_pow_of_spectralValue_le
    {E : Type u} [NormedField E] (P : E[X]) (hP : P.Monic)
    (r : ℝ) (hr : 0 < r) (hs : spectralValue P ≤ r) (k : ℕ) :
    ‖P.coeff k‖ * r ^ k ≤ r ^ P.natDegree := by
  rcases lt_trichotomy k P.natDegree with hk | hk | hk
  · have ht : spectralValueTerms P k ≤ r :=
      (le_ciSup (spectralValueTerms_bddAbove P) k).trans hs
    rw [spectralValueTerms_of_lt_natDegree P hk] at ht
    have hcast : (P.natDegree : ℝ) - (k : ℝ) =
        ((P.natDegree - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk.le]
    rw [hcast, one_div] at ht
    have hdiff : 0 < ((P.natDegree - k : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hk
    have hcoeff : ‖P.coeff k‖ ≤ r ^ (P.natDegree - k) := by
      simpa only [Real.rpow_natCast] using
        (Real.rpow_inv_le_iff_of_pos (norm_nonneg _) hr.le hdiff).mp ht
    calc
      ‖P.coeff k‖ * r ^ k ≤ r ^ (P.natDegree - k) * r ^ k :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr.le _)
      _ = r ^ P.natDegree := by
        rw [← pow_add, Nat.sub_add_cancel hk.le]
  · subst k
    simp only [hP.coeff_natDegree, norm_one, one_mul, le_refl]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, norm_zero, zero_mul]
    exact pow_nonneg hr.le _

theorem pureGauss_of_spectralValue_le
    {E : Type u} [NormedField E] (v : AbsoluteValue E ℝ)
    (hv : ∀ x : E, v x = ‖x‖) (P : E[X]) (hP : P.Monic)
    (r : ℝ) (hr : 0 < r) (hs : spectralValue P ≤ r)
    (hconst : r ^ P.natDegree = ‖P.coeff 0‖) :
    PureGauss P v r := by
  have hgauss : P.gaussNorm v r = r ^ P.natDegree := by
    apply le_antisymm
    · obtain ⟨k, hk⟩ := P.exists_eq_gaussNorm v r
      rw [hk, hv]
      exact coeff_weight_le_pow_of_spectralValue_le P hP r hr hs k
    · have h := P.le_gaussNorm v hr.le P.natDegree
      simpa only [hP.coeff_natDegree, map_one, one_mul] using h
  constructor
  · constructor
    · simpa only [hgauss, hv, pow_zero, mul_one] using hconst
    · intro k hk
      omega
  · constructor
    · rw [hgauss, hP.coeff_natDegree, map_one, one_mul]
    · intro k hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, map_zero, zero_mul, hgauss]
      exact pow_pos hr _

theorem irreducible_pureGauss_nontrivial
    (E : Type u) [NontriviallyNormedField E] [CompleteSpace E]
    (v : AbsoluteValue E ℝ) (hna : IsNonarchimedean v)
    (hv : ∀ x : E, v x = ‖x‖)
    (P : E[X]) (hP : P.Monic) (hI : Irreducible P) (h0 : P.coeff 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ PureGauss P v r := by
  let : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (by
      intro x y
      simpa only [hv] using hna x y)
  let : Fact (Irreducible P) := ⟨hI⟩
  let : FiniteDimensional E (AdjoinRoot P) := hP.finite_adjoinRoot
  let : Algebra.IsAlgebraic E (AdjoinRoot P) :=
    Algebra.IsAlgebraic.of_finite E (AdjoinRoot P)
  have hmin : minpoly E (AdjoinRoot.root P) = P := by
    simpa only [show P.leadingCoeff = 1 from hP, inv_one,
      Polynomial.C_1, mul_one] using AdjoinRoot.minpoly_root hP.ne_zero
  have hspec : spectralValue P =
      ‖P.coeff 0‖ ^ (1 / (P.natDegree : ℝ)) := by
    simpa only [spectralNorm, hmin] using
      (spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow
        (K := E) (L := AdjoinRoot P) (AdjoinRoot.root P))
  have hr : 0 < spectralValue P := by
    rw [hspec]
    exact Real.rpow_pos_of_pos (norm_pos_iff.mpr h0) _
  have hd : 0 < P.natDegree := hP.natDegree_pos_of_not_isUnit hI.not_isUnit
  have hc : spectralValue P ^ P.natDegree = ‖P.coeff 0‖ := by
    rw [hspec, one_div]
    exact Real.rpow_inv_natCast_pow (norm_nonneg _) (Nat.ne_of_gt hd)
  exact ⟨spectralValue P, hr,
    pureGauss_of_spectralValue_le v hv P hP _ hr le_rfl hc⟩

end EventualIrreducibility.UniversalSlopeDraft

open Polynomial

namespace EventualIrreducibility.UniversalSlopeDraft

theorem irreducible_gauss_alternative
    (E : Type u) [NormedField E] [CompleteSpace E]
    (v : AbsoluteValue E ℝ) (hna : IsNonarchimedean v)
    (hv : ∀ x : E, v x = ‖x‖)
    (P : E[X]) (hP : P.Monic) (hI : Irreducible P) (c : ℝ) (hc : 0 < c) :
    PureGauss P v c ∨ ∃ k, IsMinGaussIndex P v c k ∧ IsMaxGaussIndex P v c k := by
  classical
  by_cases hzero : P.coeff 0 = 0
  · have hX := irreducible_eq_X_of_coeff_zero P hP hI hzero
    rw [hX]
    exact Or.inr ⟨1, gauss_X_flat v c hc⟩
  · by_cases hnt : ∃ x : E, x ≠ 0 ∧ ‖x‖ ≠ 1
    · let : NontriviallyNormedField E := NontriviallyNormedField.ofNormNeOne hnt
      obtain ⟨r, hr, hpure⟩ := irreducible_pureGauss_nontrivial E v hna hv P hP hI hzero
      exact gauss_alternative_of_pure_radius P hP.ne_zero v c r hc hr hpure
    · have htriv : ∀ x : E, x ≠ 0 → ‖x‖ = 1 := by
        intro x hx
        by_contra h
        exact hnt ⟨x, hx, h⟩
      exact gauss_alternative_of_pure_radius P hP.ne_zero v c 1 hc zero_lt_one
        (pureGauss_of_trivial_norm E v hv htriv P hP hzero)

end EventualIrreducibility.UniversalSlopeDraft

open Polynomial
open UniqueFactorizationMonoid

namespace EventualIrreducibility.UniversalSlopeDraft

section FiniteAssembly

variable {E : Type u} [Field E] {v : AbsoluteValue E ℝ} {c : ℝ}

lemma slopeAssembly_one_indices :
    IsMinGaussIndex (1 : E[X]) v c 0 ∧
      IsMaxGaussIndex (1 : E[X]) v c 0 := by
  have hnorm : (1 : E[X]).gaussNorm v c = 1 := by
    simpa only [Polynomial.C_1, map_one] using
      Polynomial.gaussNorm_C v c (1 : E)
  constructor
  · constructor
    · simp [hnorm]
    · intro k hk
      omega
  · constructor
    · simp [hnorm]
    · intro k hk
      have hk0 : k ≠ 0 := by omega
      simp [Polynomial.coeff_one, hk0, hnorm]

lemma slopeAssembly_pure_one : PureGauss (1 : E[X]) v c := by
  simpa only [PureGauss, Polynomial.natDegree_one] using
    (slopeAssembly_one_indices (E := E) (v := v) (c := c))

lemma slopeAssembly_pure_mul (hna : IsNonarchimedean v) (hc : 0 < c)
    (A B : E[X]) (hA : A.Monic) (hB : B.Monic)
    (hApure : PureGauss A v c) (hBpure : PureGauss B v c) :
    PureGauss (A * B) v c := by
  constructor
  · simpa only [Nat.zero_add] using
      minGaussIndex_mul hna hc A B hA.ne_zero hB.ne_zero 0 0
        hApure.1 hBpure.1
  · rw [hA.natDegree_mul hB]
    exact maxGaussIndex_mul hna hc A B hA.ne_zero hB.ne_zero
      A.natDegree B.natDegree hApure.2 hBpure.2

theorem slopeAssembly_list (hna : IsNonarchimedean v) (hc : 0 < c)
    (factors : List E[X])
    (hmonic : ∀ F ∈ factors, F.Monic)
    (halt : ∀ F ∈ factors,
      PureGauss F v c ∨ ∃ k, IsMinGaussIndex F v c k ∧ IsMaxGaussIndex F v c k) :
    ∃ Q R : E[X], ∃ k : ℕ,
      Q.Monic ∧ R.Monic ∧ factors.prod = Q * R ∧ PureGauss Q v c ∧
        IsMinGaussIndex R v c k ∧ IsMaxGaussIndex R v c k := by
  revert hmonic halt
  induction factors with
  | nil =>
      intro _ _
      refine ⟨1, 1, 0, Polynomial.monic_one, Polynomial.monic_one, ?_,
        slopeAssembly_pure_one, slopeAssembly_one_indices.1,
        slopeAssembly_one_indices.2⟩
      simp
  | cons F factors ih =>
      intro hmonic halt
      have hF : F.Monic := hmonic F (by simp)
      obtain ⟨Q, R, k, hQ, hR, hprod, hQpure, hRmin, hRmax⟩ := ih
        (fun G hG => hmonic G (by simp [hG]))
        (fun G hG => halt G (by simp [hG]))
      rcases halt F (by simp) with hFpure | ⟨l, hFmin, hFmax⟩
      · refine ⟨F * Q, R, k, hF.mul hQ, hR, ?_,
          slopeAssembly_pure_mul hna hc F Q hF hQ hFpure hQpure,
          hRmin, hRmax⟩
        rw [List.prod_cons, hprod, mul_assoc]
      · refine ⟨Q, F * R, l + k, hQ, hF.mul hR, ?_, hQpure,
          minGaussIndex_mul hna hc F R hF.ne_zero hR.ne_zero l k hFmin hRmin,
          maxGaussIndex_mul hna hc F R hF.ne_zero hR.ne_zero l k hFmax hRmax⟩
        calc
          (F :: factors).prod = F * (Q * R) := by rw [List.prod_cons, hprod]
          _ = Q * (F * R) := by ring

theorem slopeFactorData_of_irreducible_alternative
    (hna : IsNonarchimedean v) (hc : 0 < c)
    (halt : ∀ F : E[X], F.Monic → Irreducible F →
      PureGauss F v c ∨ ∃ k, IsMinGaussIndex F v c k ∧ IsMaxGaussIndex F v c k)
    (P : E[X]) (hP : P.Monic) (i j : ℕ)
    (hmin : IsMinGaussIndex P v c i) (hmax : IsMaxGaussIndex P v c j) :
    Nonempty (SlopeFactorData P v c i j) := by
  classical
  let factors : List E[X] := (normalizedFactors P).toList
  have hprodP : factors.prod = P := by
    dsimp only [factors]
    rw [Multiset.prod_toList]
    simpa only [hP.leadingCoeff, Polynomial.C_1, one_mul] using
      Polynomial.leadingCoeff_mul_prod_normalizedFactors P
  have hfactors : ∀ F ∈ factors, Irreducible F ∧ F.Monic := by
    intro F hF
    have hmem : F ∈ normalizedFactors P := by
      simpa only [factors, Multiset.mem_toList] using hF
    have h := (Polynomial.mem_normalizedFactors_iff hP.ne_zero).mp hmem
    exact ⟨h.1, h.2.1⟩
  obtain ⟨Q, R, k, hQ, hR, hprod, hQpure, hRmin, hRmax⟩ :=
    slopeAssembly_list hna hc factors
      (fun F hF => (hfactors F hF).2)
      (fun F hF => halt F (hfactors F hF).2 (hfactors F hF).1)
  have hPQR : P = Q * R := hprodP.symm.trans hprod
  have hPmin : IsMinGaussIndex P v c k := by
    rw [hPQR]
    simpa only [Nat.zero_add] using
      minGaussIndex_mul hna hc Q R hQ.ne_zero hR.ne_zero 0 k hQpure.1 hRmin
  have hPmax : IsMaxGaussIndex P v c (Q.natDegree + k) := by
    rw [hPQR]
    exact maxGaussIndex_mul hna hc Q R hQ.ne_zero hR.ne_zero
      Q.natDegree k hQpure.2 hRmax
  have hki : k = i := assembly_min_unique P c k i hPmin hmin
  have hdegree : Q.natDegree + k = j :=
    assembly_max_unique P c (Q.natDegree + k) j hPmax hmax
  refine ⟨{
    Q := Q
    R := R
    monic_Q := hQ
    monic_R := hR
    factorization := hPQR
    degree_Q := by omega
    pure_Q := hQpure
    rest_min := ?_
    rest_max := ?_
  }⟩
  · simpa only [hki] using hRmin
  · simpa only [hki] using hRmax

end FiniteAssembly

theorem standardSlopeFactorInput_proved : StandardSlopeFactorInput.{u} := by
  intro E instNorm instComplete v hna hv P hP c hc i j hi hj
  exact slopeFactorData_of_irreducible_alternative hna hc
    (fun F hF hFirr => irreducible_gauss_alternative E v hna hv F hF hFirr c hc)
    P hP i j hi hj

end EventualIrreducibility.UniversalSlopeDraft

noncomputable section

namespace EventualIrreducibility.FractionAbvDraft

variable {R : Type*} [CommRing R] [IsDomain R]

theorem denominatorUnits (v : AbsoluteValue R ℝ) (y : nonZeroDivisors R) :
    IsUnit (v.toMonoidWithZeroHom y) :=
  isUnit_iff_ne_zero.mpr (v.ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp y.2))

def fractionHom (v : AbsoluteValue R ℝ) : FractionRing R →*₀ ℝ :=
  (IsLocalization.toLocalizationMap (nonZeroDivisors R) (FractionRing R)).lift₀
    v.toMonoidWithZeroHom (denominatorUnits v)

@[simp]
theorem fractionHom_algebraMap (v : AbsoluteValue R ℝ) (x : R) :
    fractionHom v (algebraMap R (FractionRing R) x) = v x := by
  change (IsLocalization.toLocalizationMap (nonZeroDivisors R) (FractionRing R)).lift
    (denominatorUnits v)
    ((IsLocalization.toLocalizationMap (nonZeroDivisors R) (FractionRing R)) x) = v x
  exact (IsLocalization.toLocalizationMap (nonZeroDivisors R) (FractionRing R)).lift_eq
    (denominatorUnits v) x

theorem fractionHom_nonneg (v : AbsoluteValue R ℝ) (x : FractionRing R) :
    0 ≤ fractionHom v x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  rw [map_div₀, fractionHom_algebraMap, fractionHom_algebraMap]
  exact div_nonneg (v.nonneg _) (v.nonneg _)

theorem fractionHom_eq_zero_iff (v : AbsoluteValue R ℝ) (x : FractionRing R) :
    fractionHom v x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hx0
    have h := congrArg (fractionHom v) (mul_inv_cancel₀ hx0)
    rw [map_mul, hx, zero_mul, map_one] at h
    exact zero_ne_one h
  · rintro rfl
    exact map_zero _

theorem fractionHom_nonarchimedean (v : AbsoluteValue R ℝ)
    (hna : IsNonarchimedean v) : IsNonarchimedean (fractionHom v) := by
  intro x y
  obtain ⟨a, b, d, hx, hy⟩ :=
    IsLocalization.surj₂ (nonZeroDivisors R) (FractionRing R) x y
  have hd : 0 < v (d : R) :=
    v.pos (mem_nonZeroDivisors_iff_ne_zero.mp d.2)
  have hxv : fractionHom v x * v (d : R) = v a := by
    rw [← fractionHom_algebraMap v (d : R), ← map_mul, hx,
      fractionHom_algebraMap]
  have hyv : fractionHom v y * v (d : R) = v b := by
    rw [← fractionHom_algebraMap v (d : R), ← map_mul, hy,
      fractionHom_algebraMap]
  have hxyv : fractionHom v (x + y) * v (d : R) = v (a + b) := by
    rw [← fractionHom_algebraMap v (d : R), ← map_mul, add_mul, hx, hy,
      ← map_add, fractionHom_algebraMap]
  have h := hna a b
  rw [← hxv, ← hyv, ← hxyv, ← max_mul_of_nonneg _ _ hd.le] at h
  nlinarith

def fractionAbv (v : AbsoluteValue R ℝ) (hna : IsNonarchimedean v) :
    AbsoluteValue (FractionRing R) ℝ where
  toFun := fractionHom v
  map_mul' := map_mul (fractionHom v)
  nonneg' := fractionHom_nonneg v
  eq_zero' := fractionHom_eq_zero_iff v
  add_le' x y := (fractionHom_nonarchimedean v hna x y).trans
    (max_le (le_add_of_nonneg_right (fractionHom_nonneg v y))
      (le_add_of_nonneg_left (fractionHom_nonneg v x)))

@[simp]
theorem fractionAbv_algebraMap (v : AbsoluteValue R ℝ)
    (hna : IsNonarchimedean v) (x : R) :
    fractionAbv v hna (algebraMap R (FractionRing R) x) = v x :=
  fractionHom_algebraMap v x

theorem fractionAbv_nonarchimedean (v : AbsoluteValue R ℝ)
    (hna : IsNonarchimedean v) : IsNonarchimedean (fractionAbv v hna) :=
  fractionHom_nonarchimedean v hna

theorem fractionAbv_discrete (v : AbsoluteValue R ℝ)
    (hna : IsNonarchimedean v)
    (hdiscrete : ∀ x : R, x ≠ 0 → ∃ j : ℤ, v x = Real.exp (-(j : ℝ)))
    (x : FractionRing R) (hx : x ≠ 0) :
    ∃ j : ℤ, fractionAbv v hna x = Real.exp (-(j : ℝ)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  have ha : a ≠ 0 := by
    intro ha
    apply hx
    simp only [ha, map_zero, zero_div]
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  obtain ⟨i, hi⟩ := hdiscrete a ha
  obtain ⟨j, hj⟩ := hdiscrete b hb0
  refine ⟨i - j, ?_⟩
  rw [map_div₀, fractionAbv_algebraMap, fractionAbv_algebraMap, hi, hj,
    ← Real.exp_sub]
  congr 1
  push_cast
  ring

end EventualIrreducibility.FractionAbvDraft

namespace EventualIrreducibility.WittLift

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [CharP L p]

abbrev FractionField (p : ℕ) (L : Type*) [Fact p.Prime] [Field L] :=
  FractionRing (WittVector p L)

def fractionAbv : AbsoluteValue (FractionField p L) ℝ :=
  FractionAbvDraft.fractionAbv abv norm_nonarchimedean

@[simp]
theorem fractionAbv_witt (x : WittVector p L) :
    fractionAbv (algebraMap (WittVector p L) (FractionField p L) x) = norm x :=
  FractionAbvDraft.fractionAbv_algebraMap abv norm_nonarchimedean x

theorem fractionAbv_nonarchimedean :
    IsNonarchimedean (fractionAbv (p := p) (L := L)) :=
  FractionAbvDraft.fractionAbv_nonarchimedean abv norm_nonarchimedean

theorem fractionAbv_discrete (x : FractionField p L) (hx : x ≠ 0) :
    ∃ j : ℤ, fractionAbv x = Real.exp (-(j : ℝ)) :=
  FractionAbvDraft.fractionAbv_discrete abv norm_nonarchimedean norm_discrete x hx

theorem fractionAbv_natCast (m : ℕ) (hm : m ≠ 0) :
    fractionAbv (m : FractionField p L) = Real.exp (-(padicValNat p m : ℝ)) := by
  have h := fractionAbv_witt (p := p) (L := L) (m : WittVector p L)
  rw [map_natCast] at h
  exact h.trans (norm_natCast m hm)

theorem fractionCharZero : CharZero (FractionField p L) := by
  apply charZero_of_inj_zero
  intro m hm
  by_contra hm0
  apply natCast_ne_zero (p := p) (L := L) m hm0
  apply IsFractionRing.injective (WittVector p L) (FractionField p L)
  simpa only [map_natCast, map_zero] using hm

@[instance_reducible]
def fractionNormedField : NormedField (FractionField p L) :=
  (fractionAbv (p := p) (L := L)).toNormedField

theorem fractionAbv_eq_norm :
    letI := fractionNormedField (p := p) (L := L)
    ∀ x : FractionField p L, fractionAbv x = ‖x‖ := by
  intro x
  rfl

end EventualIrreducibility.WittLift

open UniformSpace

namespace EventualIrreducibility.DiscreteFieldCompletion

variable (F : Type u) [NormedField F]

theorem completion_completeSpace : CompleteSpace (Completion F) := inferInstance

theorem coeRingHom_norm (x : F) :
    ‖(Completion.coeRingHom : F →+* Completion F) x‖ = ‖x‖ := by
  change ‖(x : Completion F)‖ = ‖x‖
  exact Completion.norm_coe x

theorem coeRingHom_isometry :
    Isometry (Completion.coeRingHom : F →+* Completion F) := by
  change Isometry ((↑) : F → Completion F)
  exact Completion.coe_isometry

theorem completion_charZero [CharZero F] : CharZero (Completion F) := by
  refine ⟨?_⟩
  intro m n hmn
  apply (Nat.cast_injective (R := F))
  apply (Completion.coeRingHom : F →+* Completion F).injective
  simpa only [map_natCast] using hmn

theorem completion_norm_nonarchimedean
    (hna : IsNonarchimedean (norm : F → ℝ)) :
    IsNonarchimedean (norm : Completion F → ℝ) := by
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp =>
      apply isClosed_le <;> fun_prop
  | ih x y =>
      simpa only [← Completion.coe_add, Completion.norm_coe] using hna x y

theorem norm_eq_of_sub_lt {G : Type*} [SeminormedAddCommGroup G]
    (hna : IsNonarchimedean (norm : G → ℝ)) {x y : G}
    (hclose : ‖x - y‖ < ‖x‖) : ‖x‖ = ‖y‖ := by
  have hy_le : ‖y‖ ≤ ‖x‖ := by
    have h := hna x (y - x)
    have hid : x + (y - x) = y := by abel
    rw [hid, norm_sub_rev, max_eq_left hclose.le] at h
    exact h
  have hx_le : ‖x‖ ≤ ‖y‖ := by
    by_contra h
    have hy_lt : ‖y‖ < ‖x‖ := lt_of_not_ge h
    have hmax := hna y (x - y)
    have hid : y + (x - y) = x := by abel
    rw [hid] at hmax
    exact (not_lt_of_ge hmax) (max_lt hy_lt hclose)
  exact le_antisymm hx_le hy_le

theorem exists_base_norm_eq
    (hna : IsNonarchimedean (norm : F → ℝ))
    (x : Completion F) (hx : x ≠ 0) :
    ∃ y : F, y ≠ 0 ∧ ‖x‖ = ‖y‖ := by
  obtain ⟨y, hy⟩ :=
    (Completion.denseRange_coe (α := F)).exists_dist_lt x (norm_pos_iff.mpr hx)
  have hclose : ‖x - (y : Completion F)‖ < ‖x‖ := by
    simpa only [dist_eq_norm] using hy
  have hnorm : ‖x‖ = ‖y‖ :=
    (norm_eq_of_sub_lt (completion_norm_nonarchimedean F hna) hclose).trans
      (Completion.norm_coe y)
  have hy0 : y ≠ 0 := by
    intro hy0
    have hpos := norm_pos_iff.mpr hx
    rw [hnorm, hy0, norm_zero] at hpos
    exact (lt_irrefl 0) hpos
  exact ⟨y, hy0, hnorm⟩

theorem completion_norm_discrete
    (hna : IsNonarchimedean (norm : F → ℝ))
    (hdisc : ∀ x : F, x ≠ 0 → ∃ z : ℤ, ‖x‖ = Real.exp (-(z : ℝ))) :
    ∀ x : Completion F, x ≠ 0 → ∃ z : ℤ, ‖x‖ = Real.exp (-(z : ℝ)) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_base_norm_eq F hna x hx
  obtain ⟨z, hz⟩ := hdisc y hy
  exact ⟨z, hxy.trans hz⟩

noncomputable def value : AbsoluteValue (Completion F) ℝ :=
  NormedField.toAbsoluteValue (Completion F)

theorem value_eq_norm (x : Completion F) : value F x = ‖x‖ := rfl

theorem value_coeRingHom (x : F) :
    value F ((Completion.coeRingHom : F →+* Completion F) x) = ‖x‖ :=
  coeRingHom_norm F x

theorem value_nonarchimedean
    (hna : IsNonarchimedean (norm : F → ℝ)) : IsNonarchimedean (value F) :=
  completion_norm_nonarchimedean F hna

theorem value_discrete
    (hna : IsNonarchimedean (norm : F → ℝ))
    (hdisc : ∀ x : F, x ≠ 0 → ∃ z : ℤ, ‖x‖ = Real.exp (-(z : ℝ))) :
    ∀ x : Completion F, x ≠ 0 → ∃ z : ℤ, value F x = Real.exp (-(z : ℝ)) :=
  completion_norm_discrete F hna hdisc

theorem value_restrict (v : AbsoluteValue F ℝ) (hv : ∀ x : F, v x = ‖x‖)
    (x : F) :
    value F ((Completion.coeRingHom : F →+* Completion F) x) = v x := by
  rw [value_coeRingHom, hv]

theorem value_nat_norm (p : ℕ)
    (hnat : ∀ t : ℕ, t ≠ 0 → ‖(t : F)‖ = Real.exp (-(padicValNat p t : ℝ))) :
    ∀ t : ℕ, t ≠ 0 →
      value F (t : Completion F) = Real.exp (-(padicValNat p t : ℝ)) := by
  intro t ht
  have hcast : (Completion.coeRingHom : F →+* Completion F) (t : F) =
      (t : Completion F) := map_natCast _ t
  rw [← hcast, value_coeRingHom]
  exact hnat t ht

end EventualIrreducibility.DiscreteFieldCompletion

open Polynomial
open scoped BigOperators

noncomputable section

namespace EventualIrreducibility.UnramifiedRoots

universe v

theorem exists_residue_root_list
    {L : Type u} [Field L] (m : ℕ) (hm : 0 < m)
    (hmL : (m : L) ≠ 0)
    (hsplit : (X ^ m - 1 : L[X]).Splits) :
    ∃ a : Fin m → L,
      Function.Injective a ∧
      (∀ i, a i ^ m = 1) ∧
      (∀ i, a i ≠ 0) ∧
      (∃ i, a i = 1) := by
  classical
  let P : L[X] := X ^ m - 1
  have hmonic : P.Monic := by
    simpa only [P, Polynomial.C_1] using
      (Polynomial.monic_X_pow_sub_C (1 : L) (Nat.ne_of_gt hm))
  have hsep : P.Separable := by
    simpa only [P, Polynomial.C_1] using
      (Polynomial.separable_X_pow_sub_C (1 : L) hmL one_ne_zero)
  have hsplitP : P.Splits := hsplit
  have hcard : P.roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      ← hsplitP.natDegree_eq_card_roots]
    simp only [P, ← Polynomial.C_1, Polynomial.natDegree_X_pow_sub_C]
  let e : P.roots.toFinset ≃ Fin m := Finset.equivFinOfCardEq hcard
  let a : Fin m → L := fun i => (e.symm i).val
  have hinj : Function.Injective a := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  have hpow : ∀ i, a i ^ m = 1 := by
    intro i
    have hmem : a i ∈ P.roots :=
      Multiset.mem_toFinset.mp (e.symm i).property
    have hroot := (Polynomial.mem_roots hmonic.ne_zero).mp hmem
    simpa [Polynomial.IsRoot, P, sub_eq_zero] using hroot
  have hne : ∀ i, a i ≠ 0 := by
    intro i hz
    have h := hpow i
    rw [hz, zero_pow (Nat.ne_of_gt hm)] at h
    exact zero_ne_one h
  have hmemOne : (1 : L) ∈ P.roots.toFinset := by
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hmonic.ne_zero).mpr
    simp [Polynomial.IsRoot, P]
  refine ⟨a, hinj, hpow, hne, ?_⟩
  refine ⟨e ⟨1, hmemOne⟩, ?_⟩
  exact congrArg Subtype.val (e.symm_apply_apply ⟨1, hmemOne⟩)

abbrev ResidueField (p m : ℕ) [Fact p.Prime] :=
  (X ^ m - 1 : (ZMod p)[X]).SplittingField

theorem exists_residue_roots
    (p m : ℕ) [Fact p.Prime] (hm : 0 < m) (hpm : ¬ p ∣ m) :
    ∃ a : Fin m → ResidueField p m,
      Function.Injective a ∧
      (∀ i, a i ^ m = 1) ∧
      (∀ i, a i ≠ 0) ∧
      (∃ i, a i = 1) := by
  have hmL : (m : ResidueField p m) ≠ 0 := by
    intro hz
    exact hpm ((CharP.cast_eq_zero_iff (R := ResidueField p m) (p := p) m).mp hz)
  have hs : (X ^ m - 1 : (ResidueField p m)[X]).Splits := by
    have h := Polynomial.SplittingField.splits (X ^ m - 1 : (ZMod p)[X])
    change ((X ^ m - 1 : (ZMod p)[X]).map
      (algebraMap (ZMod p) (ResidueField p m))).Splits at h
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one] at h
    exact h
  exact exists_residue_root_list m hm hmL hs

theorem factorization_of_distinct_roots
    {E : Type v} [Field E] (m : ℕ) (hm : 0 < m)
    (z : Fin m → E) (hinj : Function.Injective z)
    (hroots : ∀ i, z i ^ m = 1) :
    (X ^ m - 1 : E[X]) = ∏ i, (X - C (z i)) := by
  classical
  have hP : (X ^ m - 1 : E[X]).Monic := by
    simpa only [Polynomial.C_1] using
      (Polynomial.monic_X_pow_sub_C (1 : E) (Nat.ne_of_gt hm))
  have hQ : (∏ i : Fin m, (X - C (z i) : E[X])).Monic :=
    Polynomial.monic_prod_X_sub_C z Finset.univ
  have hdvd : (∏ i : Fin m, (X - C (z i) : E[X])) ∣ X ^ m - 1 := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C hinj hij
    · intro i _
      apply Polynomial.dvd_iff_isRoot.mpr
      simp [Polynomial.IsRoot, hroots i]
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hQ hP hdvd
  simp only [← Polynomial.C_1, Polynomial.natDegree_X_pow_sub_C,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_univ, Fintype.card_fin, le_refl]

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [CharP L p]

omit [CharP L p] in
theorem norm_teichmuller_sub (a b : L) (hab : a ≠ b) :
    WittLift.norm (WittVector.teichmuller p a - WittVector.teichmuller p b) = 1 := by
  apply (WittLift.norm_residue _).mp
  rw [map_sub, WittLift.residue_teichmuller, WittLift.residue_teichmuller]
  exact sub_ne_zero.mpr hab

omit [CharP L p] in
theorem lifted_roots_of_residue_roots
    {E : Type v} [NormedField E] (m : ℕ) (hm : 0 < m)
    (φ : WittVector p L →+* E)
    (hnorm : ∀ x, ‖φ x‖ = WittLift.norm x)
    (a : Fin m → L) (hinj : Function.Injective a)
    (hroots : ∀ i, a i ^ m = 1)
    (hne : ∀ i, a i ≠ 0) (hone : ∃ i, a i = 1) :
    ∃ z : Fin m → E,
      (∀ i, z i ^ m = 1) ∧
      (∀ i, ‖z i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖z i - z j‖ = 1) ∧
      (∃ i, z i = 1) ∧
      ((X ^ m - 1 : E[X]) = ∏ i, (X - C (z i))) := by
  classical
  let z : Fin m → E := fun i => φ (WittVector.teichmuller p (a i))
  have hzpow : ∀ i, z i ^ m = 1 := by
    intro i
    change (φ (WittVector.teichmuller p (a i))) ^ m = 1
    rw [← map_pow, WittLift.teichmuller_pow_eq_one m (a i) (hroots i), map_one]
  have hunit : ∀ i, ‖z i‖ = 1 := by
    intro i
    change ‖φ (WittVector.teichmuller p (a i))‖ = 1
    rw [hnorm, WittLift.norm_teichmuller (a i) (hne i)]
  have hsep : ∀ i j, i ≠ j → ‖z i - z j‖ = 1 := by
    intro i j hij
    change ‖φ (WittVector.teichmuller p (a i)) -
      φ (WittVector.teichmuller p (a j))‖ = 1
    rw [← map_sub, hnorm]
    exact norm_teichmuller_sub (a i) (a j) (hinj.ne hij)
  have hzOne : ∃ i, z i = 1 := by
    obtain ⟨i, hi⟩ := hone
    refine ⟨i, ?_⟩
    simp only [z, hi, map_one]
  have hzinj : Function.Injective z := by
    intro i j hij
    by_contra hneij
    have h := hsep i j hneij
    rw [hij, sub_self, norm_zero] at h
    exact zero_ne_one h
  exact ⟨z, hzpow, hunit, hsep, hzOne,
    factorization_of_distinct_roots m hm z hzinj hzpow⟩

theorem lifted_residue_field_roots
    (p m : ℕ) [Fact p.Prime] (hm : 0 < m) (hpm : ¬ p ∣ m)
    {E : Type v} [NormedField E]
    (φ : WittVector p (ResidueField p m) →+* E)
    (hnorm : ∀ x, ‖φ x‖ = WittLift.norm x) :
    ∃ z : Fin m → E,
      (∀ i, z i ^ m = 1) ∧
      (∀ i, ‖z i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖z i - z j‖ = 1) ∧
      (∃ i, z i = 1) ∧
      ((X ^ m - 1 : E[X]) = ∏ i, (X - C (z i))) := by
  obtain ⟨a, hinj, hroots, hne, hone⟩ := exists_residue_roots p m hm hpm
  exact lifted_roots_of_residue_roots m hm φ hnorm a hinj hroots hne hone

end EventualIrreducibility.UnramifiedRoots

open Polynomial
open UniformSpace
noncomputable section

namespace EventualIrreducibility.UniversalSlopeDraft

theorem standardUnramifiedInput_proved : StandardUnramifiedInput := by
  intro p m hp hm hpm
  let : Fact p.Prime := ⟨hp⟩
  let L := UnramifiedRoots.ResidueField p m
  let F := WittLift.FractionField p L
  let : NormedField F := WittLift.fractionNormedField (p := p) (L := L)
  let : CharZero F := WittLift.fractionCharZero (p := p) (L := L)
  let E := Completion F
  let : CharZero E := DiscreteFieldCompletion.completion_charZero F
  have hnaF : IsNonarchimedean (norm : F → ℝ) :=
    WittLift.fractionAbv_nonarchimedean (p := p) (L := L)
  have hdiscF : ∀ x : F, x ≠ 0 → ∃ z : ℤ, ‖x‖ = Real.exp (-(z : ℝ)) :=
    WittLift.fractionAbv_discrete
  have hnatF : ∀ t : ℕ, t ≠ 0 → ‖(t : F)‖ = Real.exp (-(padicValNat p t : ℝ)) :=
    WittLift.fractionAbv_natCast
  let φ : WittVector p L →+* E :=
    (Completion.coeRingHom : F →+* Completion F).comp
      (algebraMap (WittVector p L) F)
  have hφ : ∀ x : WittVector p L, ‖φ x‖ = WittLift.norm x := by
    intro x
    change ‖(Completion.coeRingHom : F →+* Completion F)
      (algebraMap (WittVector p L) F x)‖ = WittLift.norm x
    rw [DiscreteFieldCompletion.coeRingHom_norm]
    exact WittLift.fractionAbv_witt x
  obtain ⟨ζ, hroots, hunits, hseparated, hone, hfactorization⟩ :=
    UnramifiedRoots.lifted_residue_field_roots p m hm hpm φ hφ
  exact ⟨{
    E := E
    v := DiscreteFieldCompletion.value F
    nonarchimedean := DiscreteFieldCompletion.value_nonarchimedean F hnaF
    norm_eq := DiscreteFieldCompletion.value_eq_norm F
    discrete := DiscreteFieldCompletion.value_discrete F hnaF hdiscF
    nat_norm := DiscreteFieldCompletion.value_nat_norm F p hnatF
    ζ := ζ
    roots := hroots
    units := hunits
    separated := hseparated
    one_root := hone
    factorization := hfactorization
  }⟩

end EventualIrreducibility.UniversalSlopeDraft

namespace EventualIrreducibility

open UniversalSlopeDraft UniversalPrimePowerLocal
  UniversalAllPrimeLocalBoundDraft UniversalResultantBudget

theorem universal_prime_power_case_from_standard_local
    (hU : StandardUnramifiedInput) (hS : StandardValuedSplittingInput.{0}) :
    UniversalPrimePowerSuccessorCase := by
  intro n hn hpp
  obtain ⟨p, r, hp, hr, hN⟩ := (isPrimePow_nat_iff (n + 1)).mp hpp
  exact irreducible_prime_power_successor_rat hU hS hn hp hr hN.symm

theorem universal_local_resultant_case_from_standard_local
    (hU : StandardUnramifiedInput) (hS : StandardValuedSplittingInput.{0})
    (hSlope : StandardSlopeFactorInput.{0}) : UniversalActualLocalResultantCase := by
  intro n hn s t hprod p hp hdiv
  simpa only [FactorSeries.crossResultantNat, Polynomial.localResultant] using
    actual_integer_local_resultant_bound hU hSlope hS n hn
      s.factor t.factor s.monic t.monic hprod.symm p hp hdiv

theorem universal_irreducible_rat (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (fQ n) := by
  exact universal_irreducible_of_prime_power_and_local_resultant
    (universal_prime_power_case_from_standard_local
      standardUnramifiedInput_proved standardValuedSplittingInput_proved)
    (universal_local_resultant_case_from_standard_local
      standardUnramifiedInput_proved standardValuedSplittingInput_proved
      standardSlopeFactorInput_proved) n hn

theorem universal_irreducible_int (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (fInt n) := by
  exact (irreducible_int_iff_rat n (by omega)).mpr
    (universal_irreducible_rat n hn)

#print axioms universal_irreducible_rat
#print axioms universal_irreducible_int

end EventualIrreducibility
