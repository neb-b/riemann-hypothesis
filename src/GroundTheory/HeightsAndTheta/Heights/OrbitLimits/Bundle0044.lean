module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveVerticalPointChart
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointNagata
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointResidue
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo CurveVerticalPointChart

noncomputable section

theorem CurveVertPointChart.proof (hF : CurveRingFinite.Statement) (hCP : CurveClosedPointChart.Statement) :
    CurveVertPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hy hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hv := IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι (mCoordIdeal y) s d hy hs hsP W hW
  rw [IsHorizontal, ← Ne, Submodule.ne_bot_iff] at hv
  obtain ⟨n, hn, hn0⟩ := hv
  have hmax := chartPrimeB_isMaximal y (hF K ι Ω y hy) hPW hWp hc hyc hn0 (Ideal.mem_comap.mp hn)
  rw [curvePtIdeal_eq y hPW hWp hc hyc]
  have hmp : (chartPrimeB y c W hyc).IsPrime := hmax.isPrime

  have hrat : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ locSub y _ hmp := by
    obtain ⟨c', hyc', h'⟩ := hCP K ι Ω y hy _ hmax
    have hinv : ∀ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩ ∈ locSub y _ hmp := by
      intro k
      obtain ⟨a, b, hb, hab⟩ := h' ⟨k, c k⟩
      have hab0 : (b : Ω) * (y ⟨k, c k⟩ / y ⟨k, c' k⟩) = a := hab
      have hab' : (a : Ω) * y ⟨k, c' k⟩ = b * y ⟨k, c k⟩ := by
        rw [← hab0]
        field_simp [hyc' k]
      refine mem_locSub.mpr ⟨b, a, ?_, ?_⟩
      · intro ha
        obtain ⟨e, g, hg, hgW, he⟩ := mem_chartPrimeB.mp ha
        obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
        apply hb
        refine mem_chartPrimeB.mpr ⟨f, w, hw, ?_, hbw⟩
        have h1 : X ⟨k, c k⟩ * (HilbertSamuel.SmallSectionsNonzero.chartMono c e * w) ∈ W := by
          refine mem_of_aeval_eq y hPW
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hg
              (Inter.AvoidRing.isMultiHomog_X k (c' k)))
              (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f))
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_X k (c k))
              (Inter.AvoidRing.isMultiHomog_mul
                (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hw))
            (by abel) ?_ (W.mul_mem_right _ (W.mul_mem_right _ hgW))
          simp only [map_mul, aeval_X, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
          linear_combination (-(y ⟨k, c' k⟩ * ∏ k, y ⟨k, c k⟩ ^ f k)) * he +
            (y ⟨k, c k⟩ * ∏ k, y ⟨k, c k⟩ ^ e k) * hbw +
            ((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k) * hab'
        exact mem_of_chartMono_mul hWp hc ((hWp.mem_or_mem h1).resolve_left (hc k))
      · rw [← hab0]
        field_simp [hyc' k, hyc k]
    intro p
    obtain ⟨a, b, hb, hab⟩ := h' p
    have hu : y p / y ⟨p.1, c' p.1⟩ ∈ locSub y _ hmp := mem_locSub.mpr ⟨a, b, hb, hab⟩
    have hprod := mul_mem hu (hinv p.1)
    have he : y p / y ⟨p.1, c' p.1⟩ * (y ⟨p.1, c' p.1⟩ / y ⟨p.1, c p.1⟩) = y p / y ⟨p.1, c p.1⟩ := by
      field_simp [hyc' p.1, hyc p.1]
    rwa [he] at hprod
  have hY : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  refine ⟨hmax, fun p => mem_locSub.mp (hrat p), fun e g hg => ⟨fun hgW => ?_, ?_⟩⟩
  · have hr : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ chartRingZ y c :=
      (HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).mp
        (HilbertSamuel.LiftBirationalAmple.chartLat_form hg) c hyc
    have hinv : ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) = (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [zpow_neg, zpow_natCast]
    rw [hinv] at hr
    obtain ⟨a, b, hb, hab⟩ := mem_locSub.mp (chart_le_locSub y _ hmp c hrat hr)
    have hab' : (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k := by
      rw [← hab]
      field_simp [hY e]
    refine ⟨a, b, ?_, hb, hab'⟩
    obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    refine mem_chartPrimeB.mpr ⟨f + e, w * g, Inter.AvoidRing.isMultiHomog_mul hw hg, W.mul_mem_left _ hgW, ?_⟩
    rw [prod_pow_add, map_mul]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ f k)) * hab' + (aeval y g) * hbw
  · rintro ⟨a, b, ha, hb, hab⟩
    obtain ⟨f, v, hv, hvW, hav⟩ := mem_chartPrimeB.mp ha
    obtain ⟨f', w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hwW : w ∉ W := fun h => hb (mem_chartPrimeB.mpr ⟨f', w, hw, h, hbw⟩)
    have h1 : HilbertSamuel.SmallSectionsNonzero.chartMono c f * (w * g) ∈ W := by
      refine mem_of_aeval_eq y hPW
        (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e)
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f')) hv)
        (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f)
          (Inter.AvoidRing.isMultiHomog_mul hw hg))
        (by abel) ?_ (W.mul_mem_left _ hvW)
      simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
      linear_combination (-((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f' k)) * hav +
        ((∏ k, y ⟨k, c k⟩ ^ f k) * aeval y g) * hbw -
        ((∏ k, y ⟨k, c k⟩ ^ f k) * ∏ k, y ⟨k, c k⟩ ^ f' k) * hab
    exact (hWp.mem_or_mem (mem_of_chartMono_mul hWp hc h1)).resolve_left hwW

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointMultChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CurveVerticalPointMultiplicity

variable {K : Type} {ι : K → Type}

theorem aeval_mul_of_homog [Fintype K] [∀ k, Fintype (ι k)] {S : Type*} [CommRing S] [Algebra ℤ S] (r : (Σ k, ι k) → S) (t : K → S) {f : MRing ι}
    {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) :
    aeval (fun p => r p * t p.1) f = aeval r f * ∏ k, t k ^ d k := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  dsimp only
  rw [Finset.prod_pow_eq_pow_sum, hf m hm k]

theorem map_aeval_int {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (r : (Σ k, ι k) → S)
    (f : MRing ι) : φ (aeval r f) = aeval (fun p => φ (r p)) f := by
  induction f using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end CurveVerticalPointMultiplicity


open CurveVerticalPointMultiplicity GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart in
theorem CurveVertPointMultChart.proof (hCh : CurveVertPointChart.Statement)
    (hN : CurveVertPointNagata.Statement) : CurveVertPointMultChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hP hs hsP W hW c hc a b hb hab
  obtain ⟨hmax, hrat, -⟩ := hCh K ι Ω y s d hP hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hmp : (curvePtIdeal y W).IsPrime := hmax.isPrime
  choose a' b' hb' hab' using hrat
  obtain ⟨Φ, hsurj, hker, hΦ⟩ := hN K ι Ω y s d hP hs hsP W hW c hc a' b' hb' hab'
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hunit : ∀ x : (curvePtIdeal y W).primeCompl, IsUnit ((curveRing y).subtype x) := fun x =>
    isUnit_iff_ne_zero.mpr fun h => x.2 (by
      rw [show (x : curveRing y) = 0 from Subtype.ext h]; exact zero_mem _)
  let e : Localization.AtPrime (curvePtIdeal y W) →+* Ω := IsLocalization.lift hunit
  have hinj : Function.Injective e := by
    rw [IsLocalization.lift_injective_iff]
    intro x z
    rw [(IsLocalization.injective (M := (curvePtIdeal y W).primeCompl)
      (Localization.AtPrime (curvePtIdeal y W)) (le_nonZeroDivisors_of_noZeroDivisors fun h =>
        h (zero_mem _))).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have hbc : b ∈ (curvePtIdeal y W).primeCompl := hb
  let r : (Σ k, ι k) → Localization.AtPrime (curvePtIdeal y W) := fun p =>
    IsLocalization.mk' _ (a' p) (⟨b' p, hb' p⟩ : (curvePtIdeal y W).primeCompl)
  have her : ∀ p, e (r p) = y p / y ⟨p.1, c p.1⟩ := fun p =>
    (IsLocalization.lift_mk'_spec _ _ _ _).mpr (hab' p).symm
  have hsr : aeval r s = IsLocalization.mk' _ a (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl) := by
    apply hinj
    rw [map_aeval_int, funext her]
    have key : aeval y s = aeval (fun p => y p / y ⟨p.1, c p.1⟩) s * ∏ k, y ⟨k, c k⟩ ^ d k := by
      rw [← aeval_mul_of_homog _ (fun k => y ⟨k, c k⟩) hs]
      exact congrArg (fun v => aeval v s) (funext fun p => (div_mul_cancel₀ _ (hyc p.1)).symm)
    have hpc : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
    symm
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    change (a : Ω) = (b : Ω) * _
    apply mul_right_cancel₀ hpc
    rw [mul_assoc, ← key, hab]

  have hXk : ∀ k, (X k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl := fun k h => by
    have h1 := MvPolynomial.mem_map_C_iff.mp h (Finsupp.single k 1)
    rw [MvPolynomial.coeff_X, if_pos rfl] at h1
    exact (IsLocalRing.maximalIdeal _).ne_top_iff_one.mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hprod : (∏ k, X k ^ d k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl :=
    Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hXk k) _
  have hbu : IsUnit (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
      (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl)) :=
    isUnit_iff_exists_inv.mpr ⟨algebraMap _ _ b, (IsLocalization.mk'_spec _ _ _).trans (map_one _)⟩
  have hΦs : Φ (algebraMap _ _ s) =
      algebraMap (Localization.AtPrime (curvePtIdeal y W)) (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (algebraMap (curveRing y) _ a) *
      (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) := by
    rw [hΦ s, aeval_mul_of_homog (fun p => MvPolynomial.C (r p)) X hs, ← map_aeval_int MvPolynomial.C, hsr,
      IsLocalization.mk'_eq_mul_mk'_one, map_mul, map_mul, map_mul, ← mul_assoc,
      IsScalarTower.algebraMap_apply (Localization.AtPrime (curvePtIdeal y W))
        (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), MvPolynomial.algebraMap_eq]
  have hv : IsUnit (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) :=
    ((hbu.map MvPolynomial.C).map _).mul (IsLocalization.map_units _ ⟨_, hprod⟩)

  have hJ : ((mCoordIdeal y ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).map Φ =
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a}).map
        (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    rw [Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge, bot_sup_eq,
      Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Set.image_singleton, hΦs, Ideal.span_singleton_mul_right_unit hv]

  have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) =
      IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) := by
    rw [IsScalarTower.algebraMap_eq (Localization.AtPrime (curvePtIdeal y W))
      (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), ← Ideal.map_map,
      MvPolynomial.algebraMap_eq, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : IsLocalHom (algebraMap (Localization.AtPrime (curvePtIdeal y W))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hx'
    have h1 : x ∈ IsLocalRing.maximalIdeal _ := hx'
    have h2 := Ideal.mem_map_of_mem
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) h1
    rw [hmap] at h2
    exact h2 hx
  have hfib : Module.length (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
          (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))))) = 1 := by
    rw [hmap]
    have : IsSimpleModule (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
          IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _

  rw [multAt, dite_eq_left hWp, locLen, dite_eq_left hmp]
  congr 1
  rw [length_localizedModule_quotient, length_localizedModule_quotient,
    length_quotient_of_surjective Φ hsurj _ (hker.le.trans (Ideal.map_mono le_sup_left)), hJ,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a})).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, hfib, mul_one, Ideal.map_span, Set.image_singleton]

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointSurj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.SectionBounded

noncomputable section


open CurveVerticalPointSurjective in
theorem CurveVertPointSurj.proof (hFin : CurveRingFinite.Statement) (hC : CurveClosedPointChart.Statement) :
    CurveVertPointSurj.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hP hs hsP m hm hlen
  have hfin := hFin K ι Ω y hP
  obtain ⟨c, hyc, hrat⟩ := hC K ι Ω y hP m hm
  have hrat' := hrat
  have : m.IsPrime := hm.isPrime
  have hYne : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)

  have hunit : ∀ b : m.primeCompl, IsUnit ((curveRing y).subtype (b : curveRing y)) := by
    intro b
    refine isUnit_iff_ne_zero.mpr fun h => b.2 ?_
    have hb0 : (b : curveRing y) = 0 := Subtype.ext h
    rw [hb0]
    exact m.zero_mem
  let L := Localization.AtPrime m
  let φ : L →+* Ω := IsLocalization.lift hunit
  have hinj0 : Function.Injective (algebraMap (curveRing y) L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors m)
  have hφinj : Function.Injective φ :=
    (IsLocalization.lift_injective_iff hunit).mpr fun x x' =>
      ⟨fun h => by rw [hinj0 h], fun h => by rw [Subtype.val_injective h]⟩
  have hφB : ∀ x : curveRing y, φ (algebraMap _ L x) = x := fun x => IsLocalization.lift_eq hunit x
  have hφmk : ∀ (a : curveRing y) (b : m.primeCompl) (v : Ω),
      φ (IsLocalization.mk' L a b) = v ↔ (a : Ω) = ((b : curveRing y) : Ω) * v :=
    fun a b v => IsLocalization.lift_mk'_spec hunit a v b

  choose α β hβ hαβ using hrat
  let ρ : (Σ k, ι k) → L := fun p => IsLocalization.mk' L (α p) (⟨β p, hβ p⟩ : m.primeCompl)
  have hφρ : ∀ p, φ (ρ p) = y p / y ⟨p.1, c p.1⟩ := fun p => (hφmk _ _ _).mpr (hαβ p).symm
  have hφev : ∀ {g : MRing ι} {e : K → ℕ}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      φ (aeval ρ g) = aeval y g * (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹ := by
    intro g e hg
    rw [ringHom_aeval φ ρ g, show (fun p => φ (ρ p)) = fun p => y p / y ⟨p.1, c p.1⟩ from funext hφρ]
    exact CurveVerticalPointResidue.aeval_div y c g e hg
  have hevB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → aeval ρ g = algebraMap _ L x := by
    intro g e x hg hgx
    apply hφinj
    rw [hφev hg, hφB, hgx, mul_assoc, mul_inv_cancel₀ (hYne e), mul_one]

  let r : (Σ k, ι k) → IsLocalRing.ResidueField L := fun p => IsLocalRing.residue L (ρ p)
  have hWform : ∀ {g : MRing ι} {e : K → ℕ}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      (g ∈ mCoordIdeal r ↔ aeval ρ g ∈ IsLocalRing.maximalIdeal L) := by
    intro g e hg
    rw [GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointSurjective.mem_mCoordIdeal_iff r hg, ← IsLocalRing.residue_eq_zero_iff, ringHom_aeval]
  have hWB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → (g ∈ mCoordIdeal r ↔ x ∈ m) := by
    intro g e x hg hgx
    rw [hWform hg, hevB x hg hgx]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff L m x
  have hXc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal r := by
    intro k
    have hρ1 : ρ ⟨k, c k⟩ = 1 := hφinj (by rw [hφρ, map_one, div_self (hyc k)])
    rw [hWform (homog_X ⟨k, c k⟩), aeval_X, hρ1]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hWprime : (mCoordIdeal r).IsPrime := RingHom.ker_isPrime _
  have hPW : mCoordIdeal y ≤ mCoordIdeal r := by
    obtain ⟨S, hS, hPS⟩ := CoordinateConeArithVar.isMultiHomogIdeal y
    intro f hfP
    rw [hPS] at hfP
    refine (Ideal.span_le.mpr ?_) hfP
    intro f hf
    obtain ⟨e, he⟩ := hS f hf
    have hfP' : f ∈ mCoordIdeal y := by rw [hPS]; exact Ideal.subset_span hf
    have hf0 : aeval y f = ((0 : curveRing y) : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k := by
      rw [(GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointSurjective.mem_mCoordIdeal_iff y he).mp hfP']
      simp
    exact (hWB 0 he hf0).mpr m.zero_mem

  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ s)
  dsimp only at hab
  have hbx : ((b : curveRing y) : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k := by
    have h1 := hφev hs
    rw [← hab] at h1
    rw [(hφmk a b _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne d)]
  have hlenA : locLen m (curveRing y ⧸ Ideal.span {a}) ≠ 0 := by
    rwa [← CurveSectionQuotLocal.proof K ι Ω y s d hP hs hsP m c hm.isPrime hyc hrat' a b b.2 hbx]
  have ham : a ∈ m := by
    by_contra h
    exact hlenA (locLen_quot_eq_zero m h)
  have hsW : s ∈ mCoordIdeal r := by
    rw [hWform hs, ← hab]
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a b).mpr ham
  have hJW : mCoordIdeal y ⊔ Ideal.span {s} ≤ mCoordIdeal r :=
    sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)

  have hcurve : curvePtIdeal y (mCoordIdeal r) = m := by
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro x ⟨e, g, h, hg, hh, hgW, hhW, hx⟩
      have heq : algebraMap _ L x * aeval ρ h = aeval ρ g := by
        apply hφinj
        rw [map_mul, hφB, hφev hh, hφev hg, ← hx]
        ring
      have hmem : algebraMap _ L x * aeval ρ h ∈ IsLocalRing.maximalIdeal L := by
        rw [heq]
        exact (hWform hg).mp hgW
      rcases (IsLocalRing.maximalIdeal.isMaximal L).isPrime.mem_or_mem hmem with h1 | h1
      · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L m x).mp h1
      · exact absurd ((hWform hh).mpr h1) hhW
    · intro x hx
      obtain ⟨e, g, hg, hgx⟩ := exists_form y c hyc x
      have hgW : g ∈ mCoordIdeal r := (hWB x hg hgx).mpr hx
      have hXW : chartMon c e ∉ mCoordIdeal r := chartMon_notMem hWprime hXc e
      have hval : (x : Ω) * aeval y (chartMon c e) = aeval y g := by
        rw [aeval_chartMon, hgx]
      have key : x ∈ {b : curveRing y | ∃ (d : K → ℕ) (g h : MRing ι),
          ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h d ∧ g ∈ mCoordIdeal r ∧ h ∉ mCoordIdeal r ∧
            (b : Ω) * aeval y h = aeval y g} :=
        ⟨e, g, chartMon c e, hg, homog_chartMon c e, hgW, hXW, hval⟩
      exact Ideal.subset_span key
  have ha0 : a ≠ 0 := by
    intro h0
    have hx0 : aeval y s ≠ 0 := fun h => hsP ((GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointSurjective.mem_mCoordIdeal_iff y hs).mpr h)
    have hb0 : ((b : curveRing y) : Ω) ≠ 0 := by
      intro h
      apply b.2
      rw [show (b : curveRing y) = 0 from Subtype.ext h]
      exact m.zero_mem
    have h2 := hbx
    rw [h0, ZeroMemClass.coe_zero, zero_mul] at h2
    exact mul_ne_zero hb0 hx0 h2
  have hWfrac : ∀ {f : MRing ι} {n : K → ℕ}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n → f ∈ mCoordIdeal r →
      ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧
        (b' : Ω) * aeval y f = (a' : Ω) * ∏ k, y ⟨k, c k⟩ ^ n k := by
    intro f n hf hfW
    obtain ⟨⟨a', b'⟩, hab'⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ f)
    dsimp only at hab'
    refine ⟨a', b', ?_, b'.2, ?_⟩
    · have h1 := (hWform hf).mp hfW
      rw [← hab'] at h1
      exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a' b').mp h1
    · have h1 := hφev hf
      rw [← hab'] at h1
      rw [(hφmk a' b' _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne n)]

  have hmin : ∀ Q : Ideal (MRing ι), Q.IsPrime → mCoordIdeal y ⊔ Ideal.span {s} ≤ Q →
      Q ≤ mCoordIdeal r → mCoordIdeal r ≤ Q := by
    intro Q hQ hJQ hQW
    have hPQ : mCoordIdeal y ≤ Q := le_trans le_sup_left hJQ
    have hsQ : s ∈ Q := hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    exact le_of_minimal y c hyc hfin m hm (mCoordIdeal r) Q hQ hPQ hQW hXc hWB hWfrac
      (CoordinateConeArithVar.isMultiHomogIdeal r) ha0 hs hsQ hbx
  have hmp : mCoordIdeal r ∈ (mCoordIdeal y ⊔ Ideal.span {s}).minimalPrimes :=
    ⟨⟨hWprime, hJW⟩, fun Q hQ hQW => hmin Q hQ.1 hQ.2 hQW⟩
  exact ⟨mCoordIdeal r, ⟨hmp, fun k => ⟨c k, hXc k⟩⟩, hcurve⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

