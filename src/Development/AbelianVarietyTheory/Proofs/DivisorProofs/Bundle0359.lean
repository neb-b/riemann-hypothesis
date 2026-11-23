module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowCountAllBounds
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LowCount

theorem v_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (z : ℤ) :
    0 ≤ v (z : C) := by
  have hn : ∀ n : ℕ, 0 ≤ v (n : C) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact le_trans (le_min ih (by simp)) (v.map_add _ _)
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · exact_mod_cast hn n
  · push_cast; rw [v.map_neg]; exact hn n

theorem low_count_first_bound : FactorialWeightedSumBound := by
  intro C _ _ v M ρ g hg P B hB
  apply AddValuation.map_le_sum
  intro α hα
  rw [v.map_mul, v.map_mul]
  have h1 := hB α hα
  have h2 := hg α
  have h3 := v_intCast_nonneg v (P.coeff α)
  have h4 : (((B + ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) + (((0 - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ)
      ≤ v ((∏ m, (α m).factorial : ℕ) : C) + v (coeff α g) := add_le_add h1 h2
  rw [← WithTop.coe_add] at h4
  have h5 : (B + ∑ m, ρ m * α m) + (0 - ∑ m, ρ m * α m) = B := by ring
  rw [h5] at h4
  calc ((B : ℝ) : WithTop ℝ) = 0 + ((B : ℝ) : WithTop ℝ) := by simp
    _ ≤ _ := by rw [add_assoc]; exact add_le_add h3 h4

end GlobalTheory.LowCount

namespace GlobalTheory.LowCount

theorem logb_two_le (p : ℕ) (hp : 3 ≤ p) : Real.logb p 2 ≤ 7 / 8 := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have h3 : Real.log 3 ≤ Real.log p := Real.log_le_log (by norm_num) hp'
  have h : 8 * Real.log 2 ≤ 7 * Real.log 3 := by
    have := Real.log_le_log (by norm_num) (show (2:ℝ) ^ 8 ≤ 3 ^ 7 by norm_num)
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  rw [Real.logb, div_le_iff₀ hlp]
  linarith

theorem low_count_third_bound : RadiusExponentInequality := by
  intro p i cr K ex hp hex hcr hK hK2
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < p := by linarith
  have hex' : (1 : ℝ) ≤ ex := by exact_mod_cast hex
  set D : ℝ := (p : ℝ) ^ 2 - 1 with hD
  have hD8 : 8 ≤ D := by nlinarith
  set q : ℝ := (p : ℝ) ^ (-(2 * (K : ℤ) + 1)) with hq
  have hq0 : 0 ≤ q := zpow_nonneg (by linarith) _
  have hqe : (ex : ℝ) * q ≤ 1 := by
    have hpos : (0 : ℝ) < (p : ℝ) ^ (2 * K + 1) := by positivity
    have : q = 1 / (p : ℝ) ^ (2 * K + 1) := by
      rw [hq, zpow_neg, one_div, show (2 * (K : ℤ) + 1) = ((2 * K + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast]
    rw [this, mul_one_div, div_le_one hpos]
    exact_mod_cast hK
  have hrK : radius p K = (1 + q) / D := rfl
  have hrm : radius p (-1) = (1 + p) / D := by
    rw [hD]; simp only [radius]; norm_num
  have hpm : 1 / ((p : ℝ) - 1) = (1 + p) / D := by
    rw [hD, div_eq_div_iff (by linarith) (by nlinarith)]; ring
  have hL : Real.logb p (ex + 1) ≤ Real.logb p ex + 7 / 8 := by
    have h2 : ((ex : ℝ) + 1) ≤ ex * 2 := by linarith
    have := Real.logb_le_logb_of_le hp1 (by linarith) h2
    rw [Real.logb_mul (by linarith) (by norm_num)] at this
    linarith [logb_two_le p hp]
  have hi : (cr : ℝ) ≤ i := by exact_mod_cast hcr
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hii : (i : ℝ) ≤ (i : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ i := by exact_mod_cast h
      nlinarith
  refine ⟨?_, ?_⟩
  · rw [hrK, hrm]
    have hdiv : (i : ℝ) * ex / ((p : ℝ) - 1) = i * ex * (1 / ((p : ℝ) - 1)) := by ring
    rw [hdiv, hpm]
    have key : ((i : ℝ) - cr) * ex * (ex * q) ≤ ((i : ℝ) - cr) * ex := by
      have := mul_le_mul_of_nonneg_left hqe (mul_nonneg (sub_nonneg.2 hi) (by positivity : (0:ℝ) ≤ ex))
      linarith
    have e : (i : ℝ) * ex * ((1 + p) / D) - (i : ℝ) ^ 2 * Real.logb p (ex + 1) - i * ex * ((1 + q) / D)
        - ex * cr * ((1 + p) / D - (1 + q) / D)
        - ((((i : ℝ) - cr) * ex * p / D) - (i : ℝ) ^ 2 * (Real.logb p ex + 1))
        = (i : ℝ) ^ 2 * (Real.logb p ex + 1 - Real.logb p (ex + 1)) - ((i : ℝ) - cr) * (ex * q) / D := by
      field_simp; ring
    have h1 : ((i : ℝ) - cr) * (ex * q) / D ≤ i / 8 := by
      rw [div_le_iff₀ (by linarith)]
      have : ((i : ℝ) - cr) * (ex * q) ≤ (i : ℝ) - cr :=
        by nlinarith [mul_le_mul_of_nonneg_left hqe (sub_nonneg.2 hi)]
      nlinarith
    have h2 : (i : ℝ) ^ 2 / 8 ≤ (i : ℝ) ^ 2 * (Real.logb p ex + 1 - Real.logb p (ex + 1)) := by
      nlinarith [sq_nonneg (i : ℝ)]
    linarith
  · rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0
      have : 0 ≤ Real.logb p ex := Real.logb_nonneg hp1 hex'
      push_cast; linarith
    · rcases hK2 with h | h
      · omega
      · have h' : ((p : ℝ) ^ (2 * K - 1) : ℝ) ≤ ex := by exact_mod_cast h.le
        have := Real.logb_le_logb_of_le hp1 (by positivity) h'
        rw [Real.logb_pow, Real.logb_self_eq_one hp1] at this
        have hc : ((2 * K - 1 : ℕ) : ℝ) = 2 * (K : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [hc] at this
        linarith

end GlobalTheory.LowCount

namespace GlobalTheory.LowCount

theorem rows_eq {i ex : ℕ} (α : Fin i × Fin i →₀ ℕ) (hdeg : Finsupp.degree α = i * ex)
    (hrow : ∀ e : Fin i, ∑ c : Fin i, α (e, c) ≤ ex) : ∀ e : Fin i, ∑ c : Fin i, α (e, c) = ex := by
  have hs : ∑ e : Fin i, ∑ c : Fin i, α (e, c) = ∑ e : Fin i, ex := by
    rw [← Fintype.sum_prod_type' (fun e c => α (e, c))]
    rw [Finsupp.degree_eq_sum] at hdeg
    simp [hdeg, mul_comm]
  intro e
  exact (Finset.sum_eq_sum_iff_of_le (fun e _ => hrow e)).1 hs e (Finset.mem_univ e)

theorem count_lt (i cr : ℕ) (hcr : cr ≤ i) (a b : ℝ) :
    ∑ e : Fin i, (if e.val < cr then a else b) = cr * a + (i - cr) * b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < cr then a else b) i, Finset.sum_ite]
  have h1 : (Finset.range i).filter (· < cr) = Finset.range cr := by
    ext k; simp; omega
  have h2 : ((Finset.range i).filter (fun k => ¬ k < cr)).card = i - cr := by
    have : (Finset.range i).filter (fun k => ¬ k < cr) = Finset.Ico cr i := by
      ext k; simp; omega
    rw [this, Nat.card_Ico]
  rw [Finset.sum_const, Finset.sum_const, h1, h2, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
  push_cast [hcr]; ring

theorem low_count_second_bound : FactorialMultiindexBound := by
  intro C _ _ v p hp hp3 hv i cr K ex hcr α hdeg hrow
  have hR := rows_eq α hdeg hrow
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨?_, ?_⟩
  · apply le_of_eq
    rw [Fintype.sum_prod_type]
    have : ∀ e : Fin i, ∑ c : Fin i, (if (e, c).1.val < cr then radius p (-1) else radius p K) * (α (e, c) : ℝ)
        = (if e.val < cr then radius p (-1) else radius p K) * ex := by
      intro e
      rw [← hR e, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun e _ => this e), ← Finset.sum_mul, count_lt i cr hcr]
    ring
  · have hN : (∏ x, (α x).factorial : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
    rw [_root_.GlobalTheory.addValuation_natCast_eq_padicValNat C v p hp hv _ hN]
    rw [WithTop.coe_le_coe]
    rw [GlobalTheory.LegendreBounds.padicValNat_prod_factorial p hp]
    have hle : ∀ x : Fin i × Fin i, α x ≤ ex := by
      intro x
      rw [← hR x.1]
      exact Finset.single_le_sum (f := fun c => α (x.1, c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ x.2)
    have hterm : ∀ x : Fin i × Fin i, (α x : ℝ) / ((p : ℝ) - 1) - Real.logb p ((ex : ℝ) + 1)
        ≤ (padicValNat p (α x).factorial : ℝ) := by
      intro x
      rw [GlobalTheory.LegendreBounds.legendre_real p hp]
      have hd := GlobalTheory.T.digits_sum_le_mul_logb p (α x) hp
      have hlog : Real.logb p ((α x : ℝ) + 1) ≤ Real.logb p ((ex : ℝ) + 1) :=
        Real.logb_le_logb_of_le hp1 (by positivity) (by have := hle x; push_cast; exact_mod_cast (by omega : α x + 1 ≤ ex + 1))
      have h0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [sub_div]
      have : (((Nat.digits p (α x)).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((ex : ℝ) + 1) := by
        rw [div_le_iff₀ h0]; nlinarith
      linarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hterm x)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul] at hsum
    have htot : (∑ x : Fin i × Fin i, (α x : ℝ)) = i * ex := by
      rw [Finsupp.degree_eq_sum] at hdeg; exact_mod_cast hdeg
    rw [htot] at hsum
    push_cast at hsum ⊢
    nlinarith [hsum]

theorem lowC_all : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality :=
  ⟨low_count_first_bound, low_count_second_bound, low_count_third_bound⟩

end GlobalTheory.LowCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPolarGaussianProbabilityComplexStatement
section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace : ∀ (n : ℕ), 0 < n → MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n))) ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  first | exact @GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb | exact GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb | (intros; apply GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOnePrimeIntegralClosureIffDvdIrreducibl
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

noncomputable section

namespace GlobalTheory.JacVal

theorem mem_iff_dvd_of_height_one : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A), Irreducible t → (∀ b : B, (b : K) = algebraMap F K t → b ∈ Q) → ∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a) := by
  intro k F K _ _ _ _ _ _ _ d u hu A _ hA B hB Q hQ hQ1 t ht htQ
  have hmem : ∀ x : K, x ∈ B ↔ x ∈ integralClosure A K := by
    intro x; rw [hB]; rfl
  let φ : A →+* B := (algebraMap A K).codRestrict B
    (fun a => (hmem _).2 (Subalgebra.algebraMap_mem _ a))
  letI : Algebra A B := φ.toAlgebra
  have hφ : ∀ a : A, ((algebraMap A B a : B) : K) = algebraMap F K (a : F) := fun a => rfl
  have hinjK : Function.Injective (algebraMap A K) := by
    intro x y h
    exact Subtype.val_injective ((algebraMap F K).injective h)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr (by
    intro x y h
    apply hinjK
    have := congrArg (fun z : B => (z : K)) h
    exact this)
  let f : B →ₐ[A] K := { (B.val : B →ₐ[k] K).toRingHom with commutes' := fun a => rfl }
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    have hb : IsIntegral A (b : K) := (hmem _).1 b.2
    exact (isIntegral_algHom_iff f Subtype.val_injective).1 hb⟩
  let e : MvPolynomial (Fin d) k ≃ₐ[k] A :=
    hu.aevalEquiv.trans (Subalgebra.equivOfEq _ _ hA.symm)
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have htp : Prime t := by
    have h1 : Irreducible (e.symm t) := (MulEquiv.irreducible_iff e.symm.toMulEquiv).2 ht
    have h2 : Prime (e.symm t) := h1.prime
    exact (MulEquiv.prime_iff e.symm.toMulEquiv).1 h2
  have ht0 : t ≠ 0 := htp.ne_zero
  haveI hsp : (Ideal.span {t} : Ideal A).IsPrime := (Ideal.span_singleton_prime ht0).2 htp
  set P : Ideal A := Q.comap (algebraMap A B) with hP
  haveI : P.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver P := ⟨rfl⟩
  have htP : t ∈ P := htQ _ (hφ t)
  have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 htP
  have hPeq : P = Ideal.span {t} := by
    by_contra hne
    have hlt : Ideal.span {t} < P := lt_of_le_of_ne hle (Ne.symm hne)
    obtain ⟨Q', hQ'Q, hQ', hQ'o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := Ideal.span {t}) (q := P) Q hlt
    haveI := hQ'
    have hQ'0 : Q' ≠ ⊥ := by
      rintro rfl
      have h := hQ'o.over
      have : t ∈ (⊥ : Ideal B).under A := h ▸ Ideal.mem_span_singleton_self t
      rw [Ideal.under, Ideal.mem_comap, Ideal.mem_bot] at this
      exact ht0 ((FaithfulSMul.algebraMap_injective A B) (by rw [this, map_zero]))
    haveI : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hQ'0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQ'Q
    have h4 : (1 : ℕ∞) ≤ Q'.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h2.trans hQ1.le)
    exact absurd h3 (by decide)
  intro a b hab
  have hb : b = algebraMap A B a := Subtype.ext (hab.trans (hφ a).symm)
  subst hb
  have : algebraMap A B a ∈ Q ↔ a ∈ P := Iff.rfl
  rw [this, hPeq, Ideal.mem_span_singleton]

end GlobalTheory.JacVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallHeightOneLocalizationIntegrallyClosed
section
namespace GlobalTheory.NormalHeightOne

theorem mem_of_forall_height_eq_one : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (z : K),
    (∀ Q : Ideal A, Q.IsPrime → Q.height = 1 → ∃ r c : A, r ∉ Q ∧ algebraMap A K r * z = algebraMap A K c) →
    ∃ c : A, z = algebraMap A K c := by
  intro A K _ _ _ _ _ _ _ z h
  have hz := ((GlobalTheory.normal_domain_height_one.{0, 0, 0} A K).2.1 z).2 (fun p _ hp => by
    obtain ⟨r, c, hr, e⟩ := h p inferInstance hp
    exact (GlobalTheory.mem_primeLocalSubalgebra_iff p z).2 ⟨r, hr, ⟨c, by rw [Algebra.smul_def, e]⟩⟩)
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, hc.symm⟩

end GlobalTheory.NormalHeightOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationChar
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD.Loc

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

theorem gen_mem (I : Finset (Fin (d + 1))) {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) :
    x j / x i ∈ rA k x I :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

theorem rA_mono {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J :=
  Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩

theorem prod_mem_single (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    ∏ j ∈ I, x j / x i ∈ rA k x {i} :=
  Subalgebra.prod_mem _ fun j _ => gen_mem {i} (Finset.mem_singleton_self i) j

theorem gen_mul_prod_mem (hne : ∀ l, x l ≠ 0) (I : Finset (Fin (d + 1))) (i : Fin (d + 1))
    {i' : Fin (d + 1)} (hi' : i' ∈ I) (j : Fin (d + 1)) :
    x j / x i' * ∏ l ∈ I, x l / x i ∈ rA k x {i} := by
  rw [← Finset.mul_prod_erase I (fun l => x l / x i) hi', ← mul_assoc]
  have e : x j / x i' * (x i' / x i) = x j / x i := by
    field_simp [hne i', hne i]
  rw [e]
  exact Subalgebra.mul_mem _ (gen_mem {i} (Finset.mem_singleton_self i) j)
    (Subalgebra.prod_mem _ fun l _ => gen_mem {i} (Finset.mem_singleton_self i) l)

end GlobalTheory.PD.Loc


open GlobalTheory.PD.Loc in
theorem GlobalTheory.PD.rA_eq_loc : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F),
    IsPd k x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ y : F,
      y ∈ rA k x I ↔ ∃ N : ℕ, y * (∏ j ∈ I, x j / x i) ^ N ∈ rA k x {i} := by
  intro k _ F _ _ d x hx I i hi y
  set P := ∏ j ∈ I, x j / x i with hP
  have hPm : P ∈ rA k x {i} := prod_mem_single I i
  constructor
  · intro hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i', hi', j, rfl⟩ := hz
      exact ⟨1, by rw [pow_one]; exact gen_mul_prod_mem hx.ne I i hi' j⟩
    | algebraMap r => exact ⟨0, by rw [pow_zero, mul_one]; exact Subalgebra.algebraMap_mem _ r⟩
    | add a b _ _ ha hb =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hb
      refine ⟨N₁ + N₂, ?_⟩
      have e : (a + b) * P ^ (N₁ + N₂) = (a * P ^ N₁) * P ^ N₂ + (b * P ^ N₂) * P ^ N₁ := by ring
      rw [e]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ h₁ (Subalgebra.pow_mem _ hPm _))
        (Subalgebra.mul_mem _ h₂ (Subalgebra.pow_mem _ hPm _))
    | mul a b _ _ ha hb =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hb
      refine ⟨N₁ + N₂, ?_⟩
      have e : (a * b) * P ^ (N₁ + N₂) = (a * P ^ N₁) * (b * P ^ N₂) := by ring
      rw [e]
      exact Subalgebra.mul_mem _ h₁ h₂
  · rintro ⟨N, hN⟩
    have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hx.ne j) (hx.ne i)
    have hPinv : P⁻¹ ∈ rA k x I := by
      rw [hP, ← Finset.prod_inv_distrib]
      exact Subalgebra.prod_mem _ fun j hj => by rw [inv_div]; exact gen_mem I hj i
    have e : y = (y * P ^ N) * P⁻¹ ^ N := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hP0, one_pow, mul_one]
    rw [e]
    exact Subalgebra.mul_mem _ (rA_mono (Finset.singleton_subset_iff.2 hi) hN) (Subalgebra.pow_mem _ hPinv _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem aic_integralClosure_algebraicClosure :
    ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  intro D _ _ p hp hd
  have hmap : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).natDegree = p.natDegree := hp.natDegree_map _
  have hdeg : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hp.map _).ne_zero, hmap]; exact_mod_cast hd.ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
  have hrDp : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) r := ⟨p, hp, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  have hrD : IsIntegral D r := isIntegral_trans r hrDp
  refine ⟨⟨r, hrD⟩, ?_⟩
  apply Subtype.val_injective
  have key := Polynomial.eval₂_at_apply (p := p) (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D))) ⟨r, hrD⟩
  rw [← Polynomial.eval_map] at key
  have hr' : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).eval r = 0 := hr
  exact key.symm.trans hr'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFreeEtaleMayerVietorisLeftMapStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mono_free_etale_mayerVietoris_left_map : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), Mono (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) := by
  first | (exact @GlobalTheory.EtC.MVLeft.left_mono) | (exact GlobalTheory.EtC.MVLeft.left_mono) | (intros; apply GlobalTheory.EtC.MVLeft.left_mono  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCechComplexExact
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.MonoCech

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

def cone (i : ι) (c : Finset ι → E) : Finset ι → E := fun t =>
  if i ∈ t then 0 else cubeSign (insert i t) i • c (insert i t)

theorem delta_cone_add (i : ι) (c : Finset ι → E) :
    GlobalTheory.DI.delta (cone i c) + cone i (GlobalTheory.DI.delta c) = c := by
  funext t
  simp only [Pi.add_apply, GlobalTheory.DI.delta, cone]
  by_cases hi : i ∈ t
  · rw [if_pos hi, add_zero, Finset.sum_eq_single i]
    · rw [if_neg (by simp), Finset.insert_erase hi, smul_smul, cubeSign_mul_self, one_smul]
    · intro j _ hji
      rw [if_pos (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩), smul_zero]
    · intro h; exact absurd hi h
  · rw [if_neg hi, Finset.sum_insert hi, Finset.erase_insert hi, smul_add, smul_smul, cubeSign_mul_self,
      one_smul, Finset.smul_sum]
    have key : ∀ j ∈ t, cubeSign t j • (if i ∈ t.erase j then (0 : E) else
        cubeSign (insert i (t.erase j)) i • c (insert i (t.erase j))) +
        cubeSign (insert i t) i • cubeSign (insert i t) j • c ((insert i t).erase j) = 0 := by
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      rw [if_neg (fun h => hi (Finset.mem_of_mem_erase h)), ← Finset.erase_insert_of_ne hij, smul_smul,
        smul_smul, ← add_smul]
      have h1 := cubeSign_mul_erase (t := insert i t) (i := i) (j := j) (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hj) hij
      rw [Finset.erase_insert hi] at h1
      have ha := cubeSign_mul_self (insert i t) i
      have he := cubeSign_mul_self ((insert i t).erase j) i
      have : cubeSign t j * cubeSign ((insert i t).erase j) i + cubeSign (insert i t) i * cubeSign (insert i t) j = 0 := by
        linear_combination (cubeSign (insert i t) i * cubeSign ((insert i t).erase j) i) * h1
          - (cubeSign t j * cubeSign ((insert i t).erase j) i) * ha
          - (cubeSign (insert i t) i * cubeSign (insert i t) j) * he
      rw [this, zero_smul]
    rw [add_left_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero key, add_zero]

theorem cone_zero (i : ι) : cone i (0 : Finset ι → E) = 0 := by
  funext t; simp [cone]

end GlobalTheory.MonoCech

namespace GlobalTheory.MonoCech

end GlobalTheory.MonoCech
end

