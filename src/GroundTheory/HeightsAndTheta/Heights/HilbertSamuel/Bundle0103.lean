module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartA
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PCharpolyRootLift
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0090
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0102
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0100
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionMixed
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0101
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ChartDimLtTorus
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Algebra

noncomputable section

namespace ChartDimLt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_dim_add_card_le {J : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hJ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal J) (p : (k : K) → ι k)
    (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime] (h𝔮 : ReciprocityTheory.AnForm.R.chartIdeal J p ≤ 𝔮) :
    ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = s ∧
      ((s + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := by
  classical
  let : CommRing (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.commRing 𝔮
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let y : (Σ k, ι k) → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    fun q => C (Ideal.Quotient.mk 𝔮 (X q))
  let θ : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    aeval (fun q => (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q)
  have hy : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), aeval y f = C (Ideal.Quotient.mk 𝔮 f) := by
    intro f
    have : (aeval y : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
        (IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
          (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).comp (Ideal.Quotient.mkₐ ℂ 𝔮) := by
      apply MvPolynomial.algHom_ext
      intro q
      simp [y, MvPolynomial.algebraMap_eq]
    rw [this]
    simp [MvPolynomial.algebraMap_eq]
  have hJθ : J ≤ RingHom.ker θ := by
    obtain ⟨S, hS, hJS⟩ := hJ
    have hle : Ideal.span S ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfJ : f ∈ J := by rw [hJS]; exact Ideal.subset_span hf
      have hf𝔮 : f ∈ 𝔮 := h𝔮 (Ideal.mem_sup_left hfJ)
      show θ f = 0
      simp only [θ]
      rw [ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha
          (X : K → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) y, hy,
        Ideal.Quotient.eq_zero_iff_mem.mpr hf𝔮, map_zero, mul_zero]
    rw [hJS]
    exact hle
  have hdimR : ringKrullDim θ.range ≤ ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := by
    let g : (MvPolynomial (Σ k, ι k) ℂ) ⧸ J →+* θ.range :=
      Ideal.Quotient.lift J (θ.rangeRestrict : (MvPolynomial (Σ k, ι k) ℂ) →+* θ.range)
        (fun a ha => Subtype.ext (by simpa using hJθ ha))
    refine ringKrullDim_le_of_surjective g ?_
    intro x
    obtain ⟨a, ha⟩ := θ.rangeRestrict_surjective x
    exact ⟨Ideal.Quotient.mk J a, ha⟩
  have : Algebra.FiniteType ℂ θ.range :=
    Algebra.FiniteType.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ 𝔮) (Ideal.Quotient.mkₐ_surjective ℂ 𝔮)
  obtain ⟨sA, hAdim, hAtr⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  obtain ⟨sR, hRdim, hRtr⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := θ.range)
  have : FaithfulSMul ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).mpr
      (algebraMap ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).injective
  have : FaithfulSMul (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
      (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr
      (MvPolynomial.C_injective K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have : FaithfulSMul ℂ θ.range :=
    (faithfulSMul_iff_algebraMap_injective ℂ θ.range).mpr (algebraMap ℂ θ.range).injective
  have : FaithfulSMul θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective θ.range
      (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr Subtype.val_injective
  have hT1 : trdeg ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) +
      trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)

  have h1 : ∀ k, Ideal.Quotient.mk 𝔮 (X ⟨k, p k⟩ : (MvPolynomial (Σ k, ι k) ℂ)) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq]
    exact h𝔮 (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
  have hXk : ∀ k, (X k : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) ∈ θ.range := by
    intro k
    refine (θ.mem_range).mpr ⟨X ⟨k, p k⟩, ?_⟩
    simp only [θ, y, aeval_X, h1, map_one, mul_one]
  have hXq : ∀ q, (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q ∈ θ.range := fun q =>
    (θ.mem_range).mpr ⟨X q, by simp only [θ, aeval_X]⟩
  let AC := Subalgebra.algebraicClosure θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have hRAC : ∀ t ∈ θ.range, t ∈ AC := fun t ht =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (isAlgebraic_algebraMap (⟨t, ht⟩ : θ.range))
  have hyAC : ∀ q, y q ∈ AC := fun q =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (IsAlgebraic.of_mul
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero q.1))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXk q.1)))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXq q))))
  have hCAC : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), C (Ideal.Quotient.mk 𝔮 f) ∈ AC := by
    intro f
    refine MvPolynomial.induction_on (motive := fun f => C (Ideal.Quotient.mk 𝔮 f) ∈ AC) f ?_ ?_ ?_
    · intro c
      apply hRAC
      refine (θ.mem_range).mpr ⟨C c, ?_⟩
      simp only [θ, aeval_C, MvPolynomial.algebraMap_apply]
      rfl
    · intro f g hf hg
      rw [map_add (f := _), map_add (f := _)]
      exact AC.add_mem hf hg
    · intro f q hf
      rw [map_mul, map_mul]
      exact AC.mul_mem hf (hyAC q)
  have hall : ∀ t : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮), t ∈ AC := by
    intro t
    refine MvPolynomial.induction_on (motive := fun t => t ∈ AC) t ?_ ?_ ?_
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact hCAC f
    · intro f g hf hg
      exact AC.add_mem hf hg
    · intro f k hf
      exact AC.mul_mem hf (hRAC _ (hXk k))
  have : Algebra.IsAlgebraic θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    ⟨fun t => (Subalgebra.mem_algebraicClosure _ _).mp (hall t)⟩
  have hT2 : trdeg ℂ θ.range + trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ θ.range
  have h0 : trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = 0 := trdeg_eq_zero
  rw [h0, add_zero] at hT2
  have hK : trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      (Fintype.card K : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [hK, hAtr, ← hT2, hRtr] at hT1
  have hnat : sA + Fintype.card K = sR := by exact_mod_cast hT1
  refine ⟨sA, hAdim, ?_⟩
  rw [hnat, ← hRdim]
  exact hdimR

end ChartDimLt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomRoots
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem FibreNormDehomRoots.full : FibreNormDehomRoots.Statement :=
  FibreNormDehomRoots.proof
    (PullFormsGeneric.proof
      (PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof))
    PullSectionIntegral.proof CharpolyRootLift.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedSectionStep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace MixedSectionInduction

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
theorem cycR_eq_finsum (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    cycR I P L s = ∑ᶠ W : Ideal (MRing ι), (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℝ) *
      (if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)) := by
  unfold cycR
  rw [finsum_mem_def]
  congr 1
  funext W
  by_cases hW : W ∈ divSupp P s
  · rw [Set.indicator_of_mem hW, GroundTheory.Heights₂.Heights.Inter.divCycle_apply_of_mem hW]
  · rw [Set.indicator_of_notMem hW, GroundTheory.Heights₂.Heights.Inter.divCycle_apply_of_not_mem hW]
    simp

end MixedSectionInduction


open MixedSectionInduction in
theorem MixedSectionStep.proof (hS : SmallSectionMixed.Statement) (hR : GroundTheory.Heights₂.Heights.Inter.RatR.Statement)
    (hI : IntegralAgainstPositive.Statement) (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg)
    (hE : ZCombExpand.Statement) : MixedSectionStep.Statement := by
  classical
  intro K _ ι _ P P0 d M H II hII hd hP hP0 hMs hMn hMc hMW hHa hHs hHb hHc hAt q p hp hpos
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  change MixedKleiman.AtDim n at hAt
  have hn : 1 ≤ n := by omega
  obtain ⟨m, f, g, hm, hfg, hdiv, hbd⟩ :=
    hS K ι P P0 (n + 1) M H p q II hII (by omega) hP hP0 hMs hMn hMc hHa hHs hHb hHc hp hpos
  have hMsm : IsSmoothHerm M := hMs.1
  have hHsm : IsSmoothHerm H := hHs.1
  let L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)
  let F : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)
  have hLsp : ∀ j, IsSemipositiveRel P0 P (L j) := fun j => by
    simp only [L]
    split_ifs
    · exact hMs
    · exact SmallSectionMixedAlt.isSemipositiveRel_zcomb hMs hHs q p
  have hFs : ∀ j, IsSmoothHerm (F j) := fun j => by
    simp only [F]
    split_ifs
    · exact hMsm
    · exact ZCombLimit.isSmoothHerm_zcomb_int hMsm hHsm _ _
  have hsnoc : ∀ X, Fin.snoc L X = Function.update F (Fin.last n) X := by
    intro X
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Function.update_self]
    · rw [Fin.snoc_castSucc, Function.update_of_ne (Fin.castSucc_lt_last i).ne]
      rfl
  have hFN : Function.update F (Fin.last n) (HermLine.zcomb M H (q : ℤ) (p : ℤ)) = F := by
    funext j
    by_cases hj : j = Fin.last n
    · subst hj
      rw [Function.update_self]
      simp only [F, Fin.val_last]
      rw [if_neg (by omega)]
    · rw [Function.update_of_ne hj]

  have hscale : II K ι P (n + 1) (Fin.snoc L (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ))) =
      (m : ℝ) * II K ι P (n + 1) F := by
    have e1 := ZCombLimit.fam_update_zcomb_int (hII K ι) hP F hFs (Fin.last n) hMsm hHsm
      ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)
    have e2 := ZCombLimit.fam_update_zcomb_int (hII K ι) hP F hFs (Fin.last n) hMsm hHsm (q : ℤ) (p : ℤ)
    rw [hFN] at e2
    rw [hsnoc, e1, e2]
    push_cast
    ring
  have hpts : ∀ {W : Ideal (MRing ι)}, P ≤ W → mcPts W ⊆ mcPts P := fun hPW z hz =>
    ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hchar : ∀ W W' : Ideal (MRing ι), W ≤ W' → charOf W ≠ 0 → charOf W' ≠ 0 := by
    intro W W' hle hW hW'
    apply hW
    unfold charOf at hW' ⊢
    rw [Int.natAbs_eq_zero, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at hW' ⊢
    exact le_bot_iff.mp (hW' ▸ Ideal.comap_mono hle)
  obtain ⟨α, β, hfα, hgβ, hfP, hgP, hαβ⟩ := hfg

  have key : ∀ W ∈ divSupp P f, 0 ≤ (if IsHorizontal W then II K ι W n L
      else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)) := by
    intro W hW
    obtain ⟨hH, hV⟩ := divSuppArith K ι P n
      (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (α k : ℤ))) f W hP ⟨α, fun _ => rfl, hfα, hfP⟩ hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    split_ifs with hWh
    ·
      have hWv := hH hWh
      rw [(hE K ι (II K ι) (hII K ι) W n M H q p hWv hMsm hHsm).2 hn]
      refine Finset.sum_nonneg fun i hi => mul_nonneg (by positivity) ?_
      have hi' := Finset.mem_range.mp hi
      exact hAt K ι W P0 M H (fun _ => 1) II hII hn hWv (hP0.trans hPW)
        ⟨hMsm, fun z hz => hMs.2 z (hpts hPW hz)⟩ (fun W' h1 h2 => hMn W' h1 (hPW.trans h2)) hMc
        (fun W' h1 h2 => hMW W' h1 (hPW.trans h2)) (by rw [hHa]; funext k; simp)
        ⟨hHsm, fun z hz => hHs.2 z (hpts hPW hz)⟩ (fun z hz => hHb z (hpts hPW hz)) hHc (n - i) (by omega)
    ·
      by_cases hc : charOf W = 0
      · simp [hc]
      have hg : 0 ≤ geoNum n W (fun j => (L j).a) := by
        refine hK K ι W n _ (hV hWh).1 hc (hV hWh).2.2 fun j => ?_
        intro W' h1 h2 h3
        have hM' : 0 ≤ geoNum 1 W' (fun _ => M.a) := hMn W' h1 (hPW.trans h2) (hchar W W' h2 hc) h3
        simp only [L]
        split_ifs
        · exact hM'
        · show 0 ≤ geoNum 1 W' (fun _ => (q : ℤ) • M.a + (p : ℤ) • H.a)
          rw [ShiftedNefBig.geoNum_one_add]
          have hH' : 0 ≤ geoNum 1 W' (fun _ => (p : ℤ) • H.a) :=
            ProjLine.nefOnFibres_of_nonneg W' _ (fun k => by rw [hHa]; simp) W' h1 le_rfl
              (hchar W W' h2 hc) h3
          exact add_nonneg (mul_nonneg (Nat.cast_nonneg q) hM') hH'
      exact mul_nonneg (by exact_mod_cast hg) (Real.log_natCast_nonneg _)

  have hcyc : cycR (II K ι) P L g ≤ cycR (II K ι) P L f := by
    rw [cycR_eq_finsum, cycR_eq_finsum]
    refine finsum_le_finsum' ?_ ?_ fun W => ?_
    · exact Set.Finite.subset (Finsupp.hasFiniteSupport (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g)) fun W hW h => hW (by simp [h])
    · exact Set.Finite.subset (Finsupp.hasFiniteSupport (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f)) fun W hW h => hW (by simp [h])
    · have hle : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g W ≤ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W := hdiv W
      by_cases hW : W ∈ divSupp P f
      · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (key W hW)
      · have h0 : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W = 0 := GroundTheory.Heights₂.Heights.Inter.divCycle_apply_of_not_mem hW
        rw [h0] at hle ⊢
        rw [Nat.le_zero.mp hle]

  have hint : ptsIntegral P (pot L)
      (logNormRat (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)) f g) ≤ 0 := by
    refine hI K ι P P0 n L _ hP0 hLsp fun z hz => ?_
    have hpos := (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)).pos z hz.1
    unfold logNormRat
    refine Real.log_nonpos (by positivity) ((div_le_one hpos).mpr ?_)
    by_cases hg0 : ‖eval z (map (Int.castRingHom ℂ) g)‖ = 0
    · rw [hg0, div_zero]
      exact hpos.le
    · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0))]
      linarith [hbd z hz]
  have hNm : IsSmoothHerm (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)) :=
    ZCombLimit.isSmoothHerm_zcomb_int hMsm hHsm _ _
  have hrec := hR K ι (II K ι) (hII K ι) P n L _ f g hP (fun j => (hLsp j).1) hNm
    ⟨α, β, hfα, hgβ, hfP, hgP, hαβ⟩
  rw [hscale] at hrec
  have hnn : 0 ≤ (m : ℝ) * II K ι P (n + 1) F := by
    rw [hrec]
    unfold recRRat
    linarith
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm : (0 : ℝ) < m)).mp hnn

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

