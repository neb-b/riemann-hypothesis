module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField Matrix

noncomputable section

variable {n : ℕ}

theorem HermNorm.norm_pairing_le (h : HermNorm n) (u y : Fin n → ℂ) :
    ‖∑ j, u j * y j‖ ≤ h.norm u * h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hpair : ∑ j, u j * y j = ∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i := by
    have e1 : (∑ j, u j * y j) = u ⬝ᵥ y := rfl
    have e2 : (∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i) = (h.mat *ᵥ u) ⬝ᵥ ((h.matᵀ)⁻¹ *ᵥ y) := rfl
    rw [e1, e2, dotProduct_comm (h.mat *ᵥ u), dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
      mul_nonsing_inv _ hinv, one_mulVec, dotProduct_comm]
  rw [hpair]
  calc ‖∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i‖
      ≤ ∑ i, ‖(h.mat *ᵥ u) i‖ * ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ √(∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2) * √(∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = h.norm u * h.dualNorm y := rfl

theorem HermNorm.dualNorm_pos (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  unfold HermNorm.dualNorm
  apply Real.sqrt_pos.mpr
  have hBy : (h.matᵀ)⁻¹ *ᵥ y ≠ 0 := by
    intro h0
    apply hy
    have := congrArg (fun x => h.matᵀ *ᵥ x) h0
    simp only [mulVec_mulVec, mul_nonsing_inv _ hinv, one_mulVec, mulVec_zero] at this
    exact this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hBy
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by
    have : 0 < ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := norm_pos_iff.mpr hi
    positivity⟩

theorem fsLog_le (h : HermNorm n) {u y : Fin n → ℂ} (hy : ∑ j, u j * y j ≠ 0) :
    fsLog h u y ≤ Real.log (h.norm u) := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hd := h.dualNorm_pos hy0
  have hnum : 0 < ‖∑ j, u j * y j‖ := norm_pos_iff.mpr hy
  unfold fsLog
  apply Real.log_le_log (div_pos hnum hd)
  rw [div_le_iff₀ hd]
  exact h.norm_pairing_le u y

theorem measurableSet_coneBall (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    MeasurableSet (coneBall h W) := by
  have hc : Continuous (h.pointOf) := by
    unfold HermNorm.pointOf
    fun_prop
  have hclosed : IsClosed {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} := by
    have : {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} =
        ⋂ q ∈ W, {y | eval (h.pointOf y) q = 0} := by
      ext y; simp
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq ((continuous_eval q).comp hc) continuous_const
  have hopen : MeasurableSet (Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 1) :=
    Metric.isOpen_ball.measurableSet
  have := hopen.inter hclosed.measurableSet
  convert this using 1
  ext y
  simp [coneBall, Metric.mem_ball]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMinimalPrimeComap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem MinimalPrimeComap.flat (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) :
    letI := σ.toAlgebra
    letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
    Module.Flat (MvPolynomial ι K) (MvPolynomial ι L) := by
  letI := σ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have h : Algebra.IsPushout K (MvPolynomial ι K) L (MvPolynomial ι L) := inferInstance
  exact Module.Flat.isBaseChange K (MvPolynomial ι K) L (MvPolynomial ι L) h.out

theorem MinimalPrimeComap.proof : MinimalPrimeComap.Statement := by
  intro K L _ _ σ ι I hI P hP
  letI := σ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have := MinimalPrimeComap.flat K L σ ι
  have halg : algebraMap (MvPolynomial ι K) (MvPolynomial ι L) = MvPolynomial.map σ := rfl
  have : P.IsPrime := hP.1.1
  have hle : I ≤ P.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hP.1.2
  by_contra hne
  have hlt : I < P.under (MvPolynomial ι K) := lt_of_le_of_ne hle (fun h => hne h.symm)
  have : (P.under (MvPolynomial ι K)).IsPrime := Ideal.IsPrime.under _ _
  have : P.LiesOver (P.under (MvPolynomial ι K)) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQI⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := I) P hlt
  have hIQ : I.map (MvPolynomial.map σ) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, ← halg, ← Ideal.under_def, ← hQI.over]
  exact (not_le_of_gt hQP) (hP.2 ⟨hQ, hIQ⟩ hQP.le)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjPrimeHasPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ProjPrimeHasPoint.proof : ProjPrimeHasPoint.Statement := by
  intro F _ n W hW
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.isRelevant
  by_contra hcon
  push Not at hcon
  apply hj
  have hmem : (X j : MvPolynomial (Fin n) F) ∈
      vanishingIdeal F (zeroLocus (AlgebraicClosure F) W) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · obtain ⟨q, hq, hne⟩ := hcon x hx0
      exact absurd (hx q hq) hne
  rwa [IsPrime.vanishingIdeal_zeroLocus] at hmem

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

noncomputable section

theorem RadicalBaseChange.proof : RadicalBaseChange.Statement := by
  intro K L _ _ _ σ ι I hI
  let : Algebra K L := σ.toAlgebra
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have h1 : IsReduced (L ⊗[K] (MvPolynomial ι K ⧸ I)) :=
    isReduced_tensorProduct_of_perfectField K L _
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := K) L (MvPolynomial ι K) L I
  let e2 : L ⊗[K] MvPolynomial ι K ≃ₐ[L] MvPolynomial ι L := MvPolynomial.algebraTensorAlgEquiv K L
  have hmap : I.map (MvPolynomial.map σ) =
      (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L))).map
        (e2 : L ⊗[K] MvPolynomial ι K →+* MvPolynomial ι L) := by
    rw [← Ideal.map_coe (Algebra.TensorProduct.includeRight (R := K) (A := L)), Ideal.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul, RingHom.algebraMap_toAlgebra]
    · intro i
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e3 := Ideal.quotientEquivAlg (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
    (I.map (MvPolynomial.map σ)) e2 hmap
  exact isReduced_of_injective (e1.toRingEquiv.trans e3.toRingEquiv).symm (RingEquiv.injective _)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace SectionLengthSum

theorem prime_between {A : Type*} [CommRing A] [IsNoetherianRing A] {J W Q : Ideal A} {f : A}
    (hWP : ∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    [hQ : Q.IsPrime] (hJQ : J ≤ Q) (hQW : Q ≤ W) : Q ∈ J.minimalPrimes ∨ Q = W := by
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hPp : P.IsPrime := hP.1.1
  rcases eq_or_lt_of_le hPQ with h | hlt
  · exact Or.inl (h ▸ hP)
  rcases eq_or_lt_of_le hQW with h | hlt2
  · exact Or.inr h
  exfalso
  have hW := hWP P hP (hPQ.trans hQW)
  have hWp : W.IsPrime := hW.1.1
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  set g := Ideal.Quotient.mk P
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = P := Ideal.mk_ker
  have hcm : ∀ I : Ideal A, P ≤ I → (I.map g).comap g = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective g hsurj, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hI]
  have : (Q.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ)
  have : (W.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ.trans hQW)
  have : (W.map g).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have : (Q.map g).FiniteHeight :=
    ⟨Or.inr ((Ideal.height_mono (Ideal.map_mono hQW)).trans_lt (h1.trans_lt (WithTop.coe_lt_top 1))).ne⟩
  have hbot : (⊥ : Ideal (A ⧸ P)) < Q.map g := by
    refine lt_of_le_of_ne bot_le fun h => hlt.ne ?_
    rw [← hcm Q hPQ, ← h, ← RingHom.ker_eq_comap_bot, hker]
  have hQW' : Q.map g < W.map g := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun h => hlt2.ne ?_
    rw [← hcm Q hPQ, h, hcm W (hPQ.trans hQW)]
  have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hQW'
  have h3 := Ideal.height_strict_mono_of_isPrime_of_isPrime (I := ⊥) hbot
  have h4 : (Q.map g).height < 1 := h2.trans_le h1
  rw [Order.lt_one_iff] at h4
  rw [h4] at h3
  exact absurd h3 (not_lt_of_ge bot_le)

theorem length_ne_top_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (I : Ideal B) (hI : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes) : Module.length B (B ⧸ I) ≠ ⊤ := by
  have : IsArtinianRing (B ⧸ I) := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian B (B ⧸ I) := isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

theorem proof (hLoc : LocalSectionLengthSum.Statement) : SectionLengthSum.Statement := by
  intro A _ _ J W f hJ hf hW hWP
  classical
  have hWp : W.IsPrime := hW.1.1
  let B := Localization.AtPrime W
  let φ := algebraMap A B
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing W.primeCompl B inferInstance
  have hmin : ∀ Q : Ideal B, Q ∈ (J.map φ).minimalPrimes ↔ Q.comap φ ∈ J.minimalPrimes := fun Q => by
    rw [IsLocalization.minimalPrimes_map W.primeCompl B J]
    rfl
  have hcomapW : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ ≤ W := fun Q hQ x hx => by
    by_contra hxW
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units B (⟨x, hxW⟩ : W.primeCompl)))
  have hmapcomap : ∀ Q : Ideal B, (Q.comap φ).map φ = Q := fun Q =>
    IsLocalization.map_under W.primeCompl B Q
  have hcomapmap : ∀ P : Ideal A, P.IsPrime → P ≤ W → (P.map φ).comap φ = P := fun P hP hPW =>
    IsLocalization.under_map_of_isPrime_disjoint W.primeCompl B hP
      (Set.disjoint_left.mpr fun x hx hxP => hx (hPW hxP))
  have hJ' : (J.map φ).IsRadical := by
    show (J.map φ).radical ≤ J.map φ
    rw [← IsLocalization.map_radical W.primeCompl B J, hJ.radical]
  have hf' : ∀ Q ∈ (J.map φ).minimalPrimes, φ f ∉ Q := fun Q hQ hfQ => hf _ ((hmin Q).1 hQ) hfQ
  have hdim : ∀ Q : Ideal B, Q.IsPrime → J.map φ ≤ Q →
      Q ∈ (J.map φ).minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B := by
    intro Q hQ hJQ
    have : (Q.comap φ).IsPrime := hQ.comap φ
    rcases prime_between hWP (Ideal.map_le_iff_le_comap.mp hJQ) (hcomapW Q hQ) with h | h
    · exact Or.inl ((hmin Q).2 h)
    · right
      rw [← hmapcomap Q, h]
      exact IsLocalization.AtPrime.map_eq_maximalIdeal W B
  have key := hLoc B (J.map φ) (φ f) hJ' hf' hdim
  have hsup : ∀ I : Ideal A, (I ⊔ Ideal.span {f}).map φ = I.map φ ⊔ Ideal.span {φ f} := fun I => by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hlm : ∀ I : Ideal A, localMult (I ⊔ Ideal.span {f}) W =
      (Module.length B (B ⧸ (I.map φ ⊔ Ideal.span {φ f}))).toNat := fun I => by
    unfold localMult
    rw [dite_eq_left hWp, hsup]
  have hfW : φ f ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W B]
    exact Ideal.mem_map_of_mem φ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
  have hfin : ∀ Q ∈ (J.map φ).minimalPrimes,
      Module.length B (B ⧸ (Q ⊔ Ideal.span {φ f})) ≠ ⊤ := by
    intro Q hQ
    refine length_ne_top_of_mem_minimalPrimes _ ⟨⟨(IsLocalRing.maximalIdeal.isMaximal B).isPrime,
      sup_le (IsLocalRing.le_maximalIdeal hQ.1.1.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hfW)⟩,
      fun Q₂ hQ₂ _ => ?_⟩
    rcases hdim Q₂ hQ₂.1 (hQ.1.2.trans (le_sup_left.trans hQ₂.2)) with h | h
    · exact absurd (hQ₂.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) (hf' Q₂ h)
    · exact h.ge
  rw [hlm J, key, ENat.toNat_sum (fun Q hQ => hfin Q ((Set.Finite.mem_toFinset _).mp hQ))]
  symm
  refine Finset.sum_nbij' (fun P => P.map φ) (fun Q => Q.comap φ) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    rw [Set.Finite.mem_toFinset, hmin, hcomapmap P hP.1.1.1 hP.2]
    exact hP.1
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨(hmin Q).1 hQ, hcomapW Q hQ.1.1⟩
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    exact hcomapmap P hP.1.1.1 hP.2
  · intro Q _
    exact hmapcomap Q
  · intro P _
    exact hlm P

end SectionLengthSum

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanDisc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

theorem integral_disc_radial (g : ℝ → ℝ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator g ‖z‖ = 2 * π * ∫ y in (0 : ℝ)..1, y * g y := by
  rw [integral_fun_norm_addHaar volume (fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y =
      ∫ y in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun y => y * g y) y := by
    congr 1
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  simp [nsmul_eq_mul]
  ring

theorem integrable_disc_radial (g : ℝ → ℝ) (hg : ContinuousOn (fun y => y * g y) (Icc 0 1)) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator g ‖z‖) := by
  rw [integrable_fun_norm_addHaar volume (f := fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex]
  have h1 : (fun y : ℝ => y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y) =
      (Iio (1 : ℝ)).indicator (fun y => y * g y) := by
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact (hg.integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem integral_disc_pow (m : ℕ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖ = π / (m + 1) := by
  rw [integral_disc_radial, integral_disc_weight]
  field_simp

theorem integral_disc_log_pow (m : ℕ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖ =
      π * harmonic (m + 1) / (2 * (m + 1)) := by
  rw [integral_disc_radial]
  have h : ∫ y in (0 : ℝ)..1, y * (-log y * (1 - y ^ 2) ^ m) =
      -∫ y in (0 : ℝ)..1, y * log y * (1 - y ^ 2) ^ m := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext y
    ring
  rw [h, integral_disc_log_weight]
  field_simp
  ring

theorem integrable_disc_pow (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖) :=
  integrable_disc_radial _ (by fun_prop)

theorem integrable_disc_log_pow (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖) := by
  apply integrable_disc_radial
  have : (fun y : ℝ => y * (-log y * (1 - y ^ 2) ^ m)) =
      fun y => -(y * log y) * (1 - y ^ 2) ^ m := by
    funext y; ring
  rw [this]
  exact (continuous_mul_log.neg.mul (by fun_prop)).continuousOn

end SphereMean

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowDegreeSection.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 2 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I →
        chowDegree I (e + 2) = (divCycle I u).sum fun W m => m * chowDegree W (e + 1)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def ChowFormSectionAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle (divCycle I u) e (specFirst f u)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointChartField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ClosedPointChartField.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      IsField (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1})) ∧
        Module.Finite F (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1}))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

