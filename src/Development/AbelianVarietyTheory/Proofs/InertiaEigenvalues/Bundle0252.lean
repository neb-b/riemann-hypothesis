module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeEqMulPrimitiveRootSubOnePow
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem le_pow_n0_mul (l : ℕ) [hl : Fact l.Prime] (H : ℕ) : H ≤ l ^ (n0 l H) * (l - 1) := by
  unfold n0
  apply Nat.sInf_mem (s := {n | H ≤ l ^ n * (l - 1)})
  have h2 : 2 ≤ l := hl.out.two_le
  refine ⟨H, ?_⟩
  show H ≤ l ^ H * (l - 1)
  calc H ≤ l ^ H := (Nat.lt_pow_self (by omega : 1 < l)).le
    _ ≤ l ^ H * (l - 1) := Nat.le_mul_of_pos_right _ (by omega)

theorem exists_prime_eq_mul_primitiveRoot_sub_one_pow (l : ℕ) [hl : Fact l.Prime] (H : ℕ)
    (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ (1 + n0 l H))) :
    ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hH : (H : ℝ) ≤ (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have h := le_pow_n0_mul l H
    have h1 : 1 ≤ l := hl.out.one_lt.le
    calc (H : ℝ) ≤ ((l ^ n0 l H * (l - 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by push_cast [Nat.cast_sub h1]; ring
  have hDpos : 0 < (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    positivity
  have hnorm := norm_primitiveRoot_sub_one l (1 + n0 l H) (by omega) ζ hζ
  rw [Nat.add_sub_cancel_left] at hnorm
  have hpos : 0 < ‖ζ - 1‖ := by rw [hnorm]; positivity
  have hne : ζ - 1 ≠ 0 := norm_pos_iff.mp hpos
  refine ⟨(l : PadicComplex l) / (ζ - 1) ^ H, ?_, (div_mul_cancel₀ _ (pow_ne_zero H hne)).symm⟩
  rw [norm_div, norm_pow, norm_natCast_prime_padicComplex, div_le_one (pow_pos hpos H), hnorm,
    ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le hl1.le
  rw [neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, one_mul, div_le_one hDpos]
  exact hH

end GlobalTheory.Cyc.Decomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesLimitLat
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem exists_Ainf_series_limit (l : ℕ) [Fact l.Prime] (a : ℕ → Ainf l) :
    ∃ x : Ainf l, ∀ n : ℕ, ∃ y : Ainf l,
      x - ∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i = ((l : ℕ) : Ainf l) ^ n * y := by
  have hc : IsAdicComplete (Ideal.span {((l : ℕ) : Ainf l)}) (Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  have key : ∀ (n : ℕ) (u v : Ainf l),
      u ≡ v [SMOD ((Ideal.span {((l : ℕ) : Ainf l)}) ^ n • ⊤ : Submodule (Ainf l) (Ainf l))] ↔
        ((l : ℕ) : Ainf l) ^ n ∣ u - v := by
    intro n u v
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨x, hx⟩ := hc.toIsPrecomplete.prec
    (f := fun n => ∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i) (by
      intro m n hmn
      rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
      exact Finset.dvd_sum fun i hi =>
        Dvd.dvd.mul_right (pow_dvd_pow _ (Finset.mem_Ico.mp hi).1) _)
  refine ⟨x, fun n => ?_⟩
  have := hx n
  rw [key, ← dvd_neg, neg_sub] at this
  exact this

theorem exists_series_limit_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (M : ℕ)
    (c : ℕ → P.R.BdR) (h0 : ∀ k, c k ∈ FilB P 0)
    (hc : ∀ n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, c k ∈ Lat AI M n) :
    ∃ b ∈ FilB P 0, ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀,
      b - ∑ k ∈ Finset.range R, c k ∈ Lat AI M n := by
  choose k hk using hc
  let K : ℕ → ℕ := fun n => ∑ i ∈ Finset.range (n + 1), k i
  have hK1 : ∀ n, k n ≤ K n := fun n => by
    simp only [K, Finset.sum_range_succ]
    omega
  have hK2 : ∀ n, K n ≤ K (n + 1) := fun n => by
    simp only [K, Finset.sum_range_succ k (n + 1)]
    omega
  have hblock : ∀ n R, K n ≤ R →
      ∑ j ∈ Finset.range R, c j - ∑ j ∈ Finset.range (K n), c j ∈ Lat AI M n := by
    intro n R hR
    rw [← Finset.sum_Ico_eq_sub _ hR]
    exact AddSubgroup.sum_mem _ fun j hj => hk n j ((hK1 n).trans (Finset.mem_Ico.mp hj).1)
  choose a ha using fun n => (mem_Lat AI).mp (hblock n (K (n + 1)) (hK2 n))
  have htel : ∀ n, ∑ j ∈ Finset.range (K n), c j - ∑ j ∈ Finset.range (K 0), c j -
      io AI (∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i) ∈ FilB P (M : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := add_mem ih (ha n)
      rw [Finset.sum_range_succ (fun i => ((l : ℕ) : Ainf l) ^ i * a i), map_add (f := _)]
      convert this using 1
      ring
  obtain ⟨x, hx⟩ := exists_Ainf_series_limit l a
  refine ⟨∑ j ∈ Finset.range (K 0), c j + io AI x,
    add_mem (Submodule.sum_mem _ fun j _ => h0 j) (io_mem AI x), fun n => ⟨K n, fun R hR => ?_⟩⟩
  obtain ⟨y, hy⟩ := hx n
  have h1 := io_mem_Lat AI M n y
  rw [← hy, map_sub] at h1
  have := sub_mem (sub_mem h1 (FilB_le_Lat AI (n := n) (htel n))) (hblock n R hR)
  convert this using 1
  ring

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSolFiltered
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

open PowerSeries

namespace GlobalTheory.ExpImage

noncomputable def triSol {R : Type*} [CommRing R] (M : ℕ → ℕ → R) (g : ℕ → R) (n : ℕ) : R :=
  Ring.inverse (M n n) * (g n - ∑ i : Fin n, M n i * triSol M g i)
decreasing_by exact i.2

open PowerSeries in
private lemma constantCoeff_coeff_one_one_add_X_pow {R : Type*} [CommRing R] (N : ℕ) :
    constantCoeff ((1 + X : R⟦X⟧) ^ N) = 1 ∧ coeff 1 ((1 + X : R⟦X⟧) ^ N) = N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (1 + X : R⟦X⟧) ^ (N + 1) = (1 + X) ^ N + X * (1 + X) ^ N := by ring
    have h1 : coeff 1 (X * (1 + X : R⟦X⟧) ^ N) = constantCoeff ((1 + X : R⟦X⟧) ^ N) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
    refine ⟨?_, ?_⟩
    · rw [e, map_add (f := _), ih.1, map_mul, constantCoeff_X, zero_mul, add_zero]
    · rw [e, map_add (f := _), ih.2, h1, ih.1]
      push_cast
      ring

open PowerSeries in
private lemma isUnit_padicInt_of_not_dvd' {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) (hz : ¬ (l : ℤ_[l]) ∣ z) :
    IsUnit z :=
  PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one z)
    (not_lt.1 fun h => hz ((PadicInt.norm_lt_one_iff_dvd z).1 h)))

open PowerSeries in
private lemma toZMod_eq_zero_iff_dvd {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) :
    PadicInt.toZMod z = 0 ↔ (l : ℤ_[l]) ∣ z := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

open PowerSeries in
private lemma three_le_prime_pow {l s : ℕ} (hl : l.Prime) (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s) :
    3 ≤ l ^ s := by
  rcases hl.eq_two_or_odd' with rfl | hodd
  · calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (h2 rfl)
  · have h3 : 3 ≤ l := by
      have := hl.two_le
      rcases hodd with ⟨r, hr⟩
      omega
    calc 3 ≤ l := h3
      _ = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ s := Nat.pow_le_pow_right hl.pos hs

open PowerSeries in
private lemma coeff_one_mul_one_add_X_sq_mul_pow {R : Type*} [CommRing R] (f w : R⟦X⟧) (n : ℕ) :
    coeff 1 (f * (1 + X ^ 2 * w) ^ n) = coeff 1 f := by
  obtain ⟨q, hq⟩ : X ^ 2 ∣ (1 + X ^ 2 * w) ^ n - 1 ^ n := by
    have := sub_dvd_pow_sub_pow (1 + X ^ 2 * w) 1 n
    rw [add_sub_cancel_left] at this
    exact (dvd_mul_right _ _).trans this
  have e : f * (1 + X ^ 2 * w) ^ n = f + X ^ 2 * (f * q) := by
    rw [one_pow] at hq
    linear_combination f * hq
  rw [e, map_add (f := _), X_pow_dvd_iff.1 (dvd_mul_right _ _) 1 (by norm_num), add_zero]

open PowerSeries in
private lemma sum_mul_triSol_eq {R : Type*} [CommRing R] (M : ℕ → ℕ → R)
    (g : ℕ → R) (n : ℕ) (hn : IsUnit (M n n)) :
    ∑ i ∈ Finset.range (n + 1), M n i * _root_.GlobalTheory.ExpImage.triSol M g i = g n := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range (fun i => M n i *
    _root_.GlobalTheory.ExpImage.triSol M g i) n]
  conv_lhs => rw [_root_.GlobalTheory.ExpImage.triSol]
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hn, one_mul]
  ring


open PowerSeries in
theorem _root_.GlobalTheory.ExpImage.solve_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (s : ℕ), _root_.GlobalTheory.Cyc.Lev l s →
    ∀ (m : ℕ), ¬ l ∣ m → ∀ U : ℤ_[l], (l : ℤ_[l]) ^ s ∣ U - 1 →
    ∀ (γ : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] PowerSeries ℤ_[l]) (v : PowerSeries ℤ_[l]),
    PowerSeries.X * v = (1 + PowerSeries.X) ^ (1 + l ^ s) - 1 →
    γ PowerSeries.X = PowerSeries.X * v → ∀ (k : ℕ) (F : PowerSeries ℤ_[l]),
    ∃ p F' : PowerSeries ℤ_[l], PowerSeries.C U * (1 + PowerSeries.X) ^ m * γ p - v ^ k * p =
      v ^ k * (PowerSeries.X * F - (l : PowerSeries ℤ_[l]) ^ s * F') := by
  intro l _ s hs m hm U hU γ v hv hγ k F
  obtain ⟨hs1, hs2⟩ : 1 ≤ s ∧ (l = 2 → 2 ≤ s) := by
    unfold _root_.GlobalTheory.Cyc.Lev at hs
    exact hs
  have hlp : l.Prime := Fact.out

  let T : PowerSeries ℤ_[l] →ₗ[ℤ_[l]] PowerSeries ℤ_[l] :=
    LinearMap.mulLeft ℤ_[l] (C U * (1 + X) ^ m) ∘ₗ γ.toLinearMap -
      LinearMap.mulLeft ℤ_[l] (v ^ k)
  have hT : ∀ f, T f = C U * (1 + X) ^ m * γ f - v ^ k * f := fun f => rfl
  have hTX : ∀ i : ℕ, T (X ^ i) = (C U * (1 + X) ^ m * v ^ i - v ^ k) * X ^ i := by
    intro i
    rw [hT, map_pow, hγ]
    ring

  have hloc : ∀ f g : PowerSeries ℤ_[l], ∀ j : ℕ, (∀ i < j + 1, coeff i f = coeff i g) →
      coeff j (T f) = coeff j (T g) := by
    intro f g j h
    obtain ⟨q, hq⟩ : X ^ (j + 1) ∣ f - g :=
      X_pow_dvd_iff.2 fun i hi => by rw [map_sub, h i hi, sub_self]
    have e : T f - T g = X ^ (j + 1) * (C U * (1 + X) ^ m * v ^ (j + 1) * γ q - v ^ k * q) := by
      rw [← map_sub, hq, hT, map_mul, map_pow, hγ]
      ring
    have h2 : coeff j (T f - T g) = 0 := by
      rw [e]
      exact X_pow_dvd_iff.1 (dvd_mul_right _ _) j (Nat.lt_succ_self j)
    rwa [map_sub, sub_eq_zero] at h2
  have hsum : ∀ (c : ℕ → ℤ_[l]) (j : ℕ),
      coeff j (T (mk c)) = ∑ i ∈ Finset.range (j + 1), c i * coeff j (T (X ^ i)) := by
    intro c j
    rw [hloc (mk c) (∑ i ∈ Finset.range (j + 1), c i • X ^ i) j]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [map_sum, map_smul]
    · intro i hi
      set_option synthInstance.maxHeartbeats 100000 in
        simp [coeff_mk, map_sum, coeff_X_pow, Finset.mem_range.2 hi]

  have hv0 : constantCoeff v = 1 + (l : ℤ_[l]) ^ s := by
    have h := congrArg (coeff 1) hv
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      map_sub, (constantCoeff_coeff_one_one_add_X_pow (R := ℤ_[l]) (1 + l ^ s)).2] at h
    rw [h]
    simp
  have hunitv : IsUnit v := by
    rw [isUnit_iff_constantCoeff, hv0]
    refine isUnit_padicInt_of_not_dvd' _ fun hd => ?_
    have h1 : (l : ℤ_[l]) ∣ 1 :=
      (dvd_add_left (dvd_pow_self (l : ℤ_[l]) (by omega : s ≠ 0))).1 hd
    have hn := PadicInt.isUnit_iff.1 (isUnit_of_dvd_one h1)
    have h2 := (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l])).2 dvd_rfl
    linarith

  have hdiag : ∀ i : ℕ, (l : ℤ_[l]) ^ s ∣ coeff i (T (X ^ i)) := by
    intro i
    have e := coeff_mul_X_pow (C U * (1 + X) ^ m * v ^ i - v ^ k) i 0
    rw [zero_add] at e
    rw [hTX, e, coeff_zero_eq_constantCoeff_apply]
    simp only [map_sub, map_mul, map_pow, constantCoeff_C, hv0,
      (constantCoeff_coeff_one_one_add_X_pow (R := ℤ_[l]) m).1, mul_one]
    have ha : ∀ n : ℕ, (l : ℤ_[l]) ^ s ∣ (1 + (l : ℤ_[l]) ^ s) ^ n - 1 := fun n => by
      simpa using sub_dvd_pow_sub_pow (1 + (l : ℤ_[l]) ^ s) 1 n
    have e2 : U * (1 + (l : ℤ_[l]) ^ s) ^ i - (1 + (l : ℤ_[l]) ^ s) ^ k =
        (U - 1) * (1 + (l : ℤ_[l]) ^ s) ^ i + ((1 + (l : ℤ_[l]) ^ s) ^ i - 1) -
          ((1 + (l : ℤ_[l]) ^ s) ^ k - 1) := by ring
    rw [e2]
    exact dvd_sub (dvd_add (dvd_mul_of_dvd_left hU _) (ha i)) (ha k)

  have hsub : ∀ n : ℕ, IsUnit (coeff (n + 1) (T (X ^ n))) := by
    intro n
    refine isUnit_padicInt_of_not_dvd' _ fun hd => hm ?_
    rw [← toZMod_eq_zero_iff_dvd] at hd
    haveI : CharP (PowerSeries (ZMod l)) l :=
      charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod l)) l
    obtain ⟨t, ht⟩ : ∃ t, l ^ s = t + 3 := ⟨l ^ s - 3, by have := three_le_prime_pow hlp hs1 hs2; omega⟩
    have hvb : PowerSeries.map PadicInt.toZMod v = 1 + X ^ 2 * (X ^ t * (1 + X)) := by
      apply X_mul_cancel
      have h := congrArg (PowerSeries.map (PadicInt.toZMod (p := l))) hv
      simp only [map_mul, map_sub, map_pow, map_add (f := _), map_one, PowerSeries.map_X] at h
      rw [h, pow_add, pow_one, add_pow_char_pow (1 : PowerSeries (ZMod l)) X l s, one_pow, ht]
      ring
    have hU1 : PadicInt.toZMod U = 1 := by
      have : PadicInt.toZMod (U - 1) = 0 := (toZMod_eq_zero_iff_dvd _).2
        ((dvd_pow_self (l : ℤ_[l]) (by omega : s ≠ 0)).trans hU)
      rwa [map_sub, map_one, sub_eq_zero] at this
    have hcomp : PadicInt.toZMod (coeff (n + 1) (T (X ^ n))) = (m : ZMod l) := by
      rw [← coeff_map, hTX, add_comm n 1]
      simp only [map_mul, map_sub, map_pow, map_add (f := _), map_one, PowerSeries.map_X,
        PowerSeries.map_C, hU1, one_mul]
      rw [coeff_mul_X_pow, hvb, map_sub, coeff_one_mul_one_add_X_sq_mul_pow,
        show ((1 : PowerSeries (ZMod l)) + X ^ 2 * (X ^ t * (1 + X))) ^ k =
          1 * (1 + X ^ 2 * (X ^ t * (1 + X))) ^ k by rw [one_mul],
        coeff_one_mul_one_add_X_sq_mul_pow, (constantCoeff_coeff_one_one_add_X_pow m).2]
      simp
    rw [hcomp] at hd
    exact (ZMod.natCast_eq_zero_iff m l).1 hd
  let g : ℕ → ℤ_[l] := fun j => coeff j (v ^ k * (X * F))
  let c : ℕ → ℤ_[l] := _root_.GlobalTheory.ExpImage.triSol (fun n i => coeff (n + 1) (T (X ^ i)))
    (fun n => g (n + 1))
  have hcoef : ∀ j : ℕ, (l : ℤ_[l]) ^ s ∣ coeff j (T (mk c) - v ^ k * (X * F)) := by
    intro j
    rw [map_sub, hsum]
    cases j with
    | zero =>
      have h0 : coeff 0 (v ^ k * (X * F)) = 0 := by
        simp [coeff_zero_eq_constantCoeff_apply]
      rw [h0, sub_zero, Finset.sum_range_one]
      exact dvd_mul_of_dvd_right (hdiag 0) _
    | succ n =>
      have hs' := sum_mul_triSol_eq (fun n i => coeff (n + 1) (T (X ^ i)))
        (fun n => g (n + 1)) n (hsub n)
      rw [Finset.sum_range_succ]
      convert dvd_mul_of_dvd_right (hdiag (n + 1)) (c (n + 1)) using 1
      simp only [g, c] at hs' ⊢
      rw [← hs', Finset.sum_congr rfl fun i _ => mul_comm _ _]
      ring
  let E : PowerSeries ℤ_[l] := mk fun j => (hcoef j).choose
  have hE : T (mk c) - v ^ k * (X * F) = C ((l : ℤ_[l]) ^ s) * E := by
    apply PowerSeries.ext
    intro j
    rw [coeff_C_mul, coeff_mk]
    exact (hcoef j).choose_spec
  obtain ⟨u, hu⟩ := hunitv.pow k
  refine ⟨mk c, -(↑u⁻¹ * E), ?_⟩
  have hE' : T (mk c) = v ^ k * (X * F) + C ((l : ℤ_[l]) ^ s) * E := by
    rw [← hE]; ring
  rw [← hT, hE']
  have hl : (l : PowerSeries ℤ_[l]) ^ s = C ((l : ℤ_[l]) ^ s) := by simp
  rw [hl, ← hu]
  have : (u : PowerSeries ℤ_[l]) * ↑u⁻¹ = 1 := Units.mul_inv u
  linear_combination (-(C ((l : ℤ_[l]) ^ s) * E)) * this

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableLatticeCompactGroup
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.StableLat

theorem exists_lattice : ∀ {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp LL O : Type} [Field Qp] [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O), Nonempty (Lattice (O := O) A.ρ) := by
  intro G _ _ _ Qp LL O _ _ _ _ _ _ _ hO A
  classical
  obtain ⟨⟨hDom, hDVR, hFrac⟩, -, -, hTop, hOpen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFrac; haveI := hTop
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL

  let e := Module.finBasis LL A.V
  let n := Module.finrank LL A.V
  let T₀ : Submodule O A.V := Submodule.span O (Set.range e)
  have hT₀fg : T₀.FG := Submodule.fg_span (Set.finite_range e)
  have hT₀span : Submodule.span LL (T₀ : Set A.V) = ⊤ := by
    simp only [T₀, Submodule.span_span_of_tower, e.span_eq]
  have hT₀open : IsOpen (T₀ : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hOpen T₀ hT₀fg hT₀span

  have hcov : ∀ x : A.V, ∃ b : nonZeroDivisors O, (b : O) • x ∈ T₀ := by
    intro x
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
      (fun i => e.repr x i)
    refine ⟨b, ?_⟩
    have hx : (b : O) • x = ∑ i, (b : O) • (e.repr x i • e i) := by
      rw [← Finset.smul_sum, e.sum_repr]
    rw [hx]
    refine T₀.sum_mem fun i _ => ?_
    obtain ⟨a, ha⟩ := hb i (Finset.mem_univ i)
    rw [← smul_assoc, ← ha, algebraMap_smul]
    exact T₀.smul_mem a (Submodule.subset_span ⟨i, rfl⟩)

  let C : Set A.V := ⋃ i, Set.range fun g : G => A.ρ g (e i)
  have hC : IsCompact C := isCompact_iUnion fun i => isCompact_range (A.cont (e i))
  let U : nonZeroDivisors O → Set A.V := fun b => (fun x => (b : O) • x) ⁻¹' (T₀ : Set A.V)
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    have : (fun x : A.V => (b : O) • x) = fun x => algebraMap O LL b • x := by
      funext x; rw [algebraMap_smul]
    exact hT₀open.preimage (this ▸ continuous_const_smul _)
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU (fun x _ => by
    obtain ⟨b, hb⟩ := hcov x; exact Set.mem_iUnion.2 ⟨b, hb⟩)
  let b : O := ∏ c ∈ t, (c : O)
  have hb0 : b ∈ nonZeroDivisors O := by
    simpa [b] using (∏ c ∈ t, c).2
  have hbC : ∀ y ∈ C, b • y ∈ T₀ := by
    intro y hy
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hy)
    have : b = (∏ d ∈ t.erase c, (d : O)) * c := by
      simp only [b]; rw [← Finset.prod_erase_mul _ _ hct]
    rw [this, mul_smul]
    exact T₀.smul_mem _ hc

  let T : Submodule O A.V := Submodule.span O C
  have hCT : C ⊆ T := Submodule.subset_span
  have hstable : ∀ g, ∀ x ∈ T, A.ρ g x ∈ T := by
    intro g x hx
    have hle : T ≤ T.comap ((A.ρ g).restrictScalars O) := by
      refine Submodule.span_le.2 ?_
      intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, rfl⟩ := hi
      show A.ρ g (A.ρ h (e i)) ∈ T
      rw [← Module.End.mul_apply, ← map_mul]
      exact hCT (Set.mem_iUnion.2 ⟨i, g * h, rfl⟩)
    exact hle hx

  let f : A.V →ₗ[O] A.V := b • LinearMap.id
  have hbne : algebraMap O LL b ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb0 (hinj (by rw [h, map_zero]))
  have hf : Function.Injective f := by
    intro x y hxy
    have : algebraMap O LL b • x = algebraMap O LL b • y := by
      simpa [f, algebraMap_smul] using hxy
    exact smul_right_injective A.V hbne this
  have hfT : T.map f ≤ T₀ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 fun y hy => ?_
    simpa [f] using hbC y hy
  have hTfg : T.FG := Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hT₀fg hfT)
  haveI : NoZeroSMulDivisors O A.V := ⟨fun {c x} h => by
    rw [← algebraMap_smul LL c x] at h
    rcases smul_eq_zero.1 h with h | h
    · left; exact hinj (by rw [h, map_zero])
    · right; exact h⟩
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hTfg
  have hfree : Module.Free O T := Module.free_of_finite_type_torsion_free'
  have hspan : Submodule.span LL (T : Set A.V) = ⊤ := by
    rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span (hCT (Set.mem_iUnion.2 ⟨i, 1, ?_⟩))
    simp
  exact ⟨⟨T, hstable, hTfg, hfree, hspan⟩⟩

end GlobalTheory.StableLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LocalIntegers

theorem goodO_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  fun l _ LL => (good_integers l LL).1

end GlobalTheory.LocalIntegers
end

