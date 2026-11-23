module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ArIntMul
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem arInt_mul (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) {L : Fin n → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) :
    arInt P (s * t) (A.tensor B) L = arInt P s A L + arInt P t B L := by
  obtain ⟨a, -, hsa, hsP⟩ := id hs
  obtain ⟨b, -, htb, htP⟩ := id ht
  show ptsIntegral P (pot L) _ = ptsIntegral P (pot L) _ + ptsIntegral P (pot L) _
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [← integral_add (hInt K ι P n _ L A s hP hΨg hL hA hs) (hInt K ι P n _ L B t hP hΨg hL hB ht)]
    refine integral_congr_ae ?_
    filter_upwards [ae_eval_ne_zero hP hΨg ⟨a, hsa⟩ hsP, ae_eval_ne_zero hP hΨg ⟨b, htb⟩ htP]
      with y hys hyt
    rw [← finsum_mem_add_distrib' ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)
      ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)]
    refine finsum_mem_congr rfl fun w _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hsh := hγ.choose_spec.2.self_of_nhds
      set z := hγ.choose y
      have hz : z ∈ mcPts P := hsh.2.1
      have hs0 := norm_pos_iff.mpr (hys z hz hsh.2.2)
      have ht0 := norm_pos_iff.mpr (hyt z hz hsh.2.2)
      have hA0 := A.pos z hz.1
      have hB0 := B.pos z hz.1
      rw [← add_mul]
      congr 1
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (s * t))‖ / (A.h z * B.h z)) =
        Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) +
          Real.log (‖eval z (map (Int.castRingHom ℂ) t)‖ / B.h z)
      rw [map_mul, map_mul, norm_mul, mul_div_mul_comm]
      exact Real.log_mul (div_pos hs0 hA0).ne' (div_pos ht0 hB0).ne'
    · simp
  · simp

theorem RMul.proof (hInt : PtsIntegrableStatement) : RMulStatement := by
  intro K _ ι _ I P n L A B s t hP hL hA hB hs ht
  obtain ⟨-, -, -, hsP⟩ := id hs
  obtain ⟨-, -, -, htP⟩ := id ht
  rw [recR_eq, recR_eq, recR_eq, cycR_mul I hP.2.1.1 L hsP htP, arInt_mul hInt hP hL hA hB hs ht]
  ring

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImageVarIdBotTwo
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def VerticalDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ)
    (i' : ∀ k', ι' k'),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    IsChart (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' →
    ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
      (fnDeg v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' : ℤ) = J' (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 Fin.elim0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityIntegral.proof (hC : RegularityValuationCentre.Statement) (hB : RegularityRelativeClosedPoint.Statement) :
    RegularityIntegral.Statement := by
  intro K _ ι _ P hP x
  obtain ⟨hF, hNF⟩ := RegularityFunctionFieldNumber.proof K ι P hP
  let _ := hF.toField
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (funField P)),
      v.valuation (funField P) (x : funField P) ≤ 1 := by
    intro v
    obtain ⟨n, hn0, hn⟩ := RegularityValuationCentre.exists_int_valuation_lt_one v
    obtain ⟨W, hW, hPW, hnW, hsub⟩ := hC K ι P hP.2.1 _ (v.valuation (funField P)) n hn
    have hWP : W ≠ P := by
      rintro rfl
      have h0 : n ∈ W.comap (C : ℤ →+* MRing ι) := hnW
      rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at h0
      exact hn0 h0
    exact hsub x (x.2 W (hB K ι P W hP hW hPW hWP) hPW)
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (funField P)
    (x : funField P) hv
  have hint : IsIntegral ℤ (x : funField P) := hy ▸ (Algebra.IsIntegral.isIntegral y).algebraMap
  let f : funField P →ₐ[ℤ] FractionRing (MRing ι ⧸ P) :=
    { (funField P).subtype with commutes' := fun n => by simp }
  exact hint.map f

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherMore
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

def pullbackBadImage_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ →
    volume (pullQ R v Ψ '' (pullBad R v Ψ ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0})) = 0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherTer
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def PullbackVanishingOfNullCycle.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ → IsMultiHomogIdeal J' → ¬ J' ≤ P' →
    volume {y : Fin n → ℂ | ∃ z' ∈ mcPts P', z' ∈ mcPts J' ∧
      (Ψ (segre fun p => z' (v p)) 0)⁻¹ • segre (fun p => z' (v p)) ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ y} = 0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalize.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsClosedPt W → P ≤ W → y ∈ locRing P W →
    ∃ s x : regRing P, (∃ z ∈ locRing P W, ((s : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1) ∧
      y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZIff
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionCycle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem comap_C_imageZ (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    (imageZ v W').comap (C : ℤ →+* MRing ι) = W'.comap (C : ℤ →+* MRing ι') := by
  ext c
  simp [imageZ, Ideal.mem_comap]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem isHorizontal_imageZ_iff (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    IsHorizontal (imageZ v W') ↔ IsHorizontal W' := by
  rw [IsHorizontal, IsHorizontal, comap_C_imageZ]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem charOf_imageZ (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    charOf (imageZ v W') = charOf W' := by
  simp only [charOf, comap_C_imageZ]

end ArithmeticIntersectionCycle

theorem ArithmeticIntersectionCycle.proof (hHor : ArithmeticIntersectionHorizontal.Statement) (hVert : ArithmeticIntersectionVertical.Statement) (hPush : ArithmeticIntersectionDivisorPushforward.Statement)
    (hGP : GenericPointExists.Statement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    ArithmeticIntersectionCycle.Statement := by
  intro I hI n hn K _ ι _ K' _ ι' _ κ v P' G J L L' s α hv hP' hP hJ hL hLL' hs hsP
  classical

  have hex : ∀ W' : Ideal (MRing ι'), W'.IsPrime →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' := by
    intro W' hW'
    obtain ⟨G'⟩ := hGP K ι K' ι' v W' hW'
    obtain ⟨J', hJ', -⟩ := hEU G'.Φ (FibreBlock κ) (fibreIdx ι' κ)
    exact ⟨G', J', hJ'⟩
  let E : Ideal (MRing ι') → ℤ := fun W' =>
    if h : ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' then
      h.choose_spec.choose (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ h.choose) 0 Fin.elim0 else 0
  have hE : ∀ W' : Ideal (MRing ι'), W'.IsPrime →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 Fin.elim0 := by
    intro W' hW'
    have h := hex W' hW'
    exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec, by simp only [E, dif_pos h]⟩

  let T : Ideal (MRing ι) → ℝ := fun W =>
    if IsHorizontal W then I K ι W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)
  let T' : Ideal (MRing ι') → ℝ := fun W' =>
    if IsHorizontal W' then I K' ι' W' n L' else (geoNum n W' (fun j => (L' j).a) : ℝ) * Real.log (charOf W')
  have hterm : ∀ W' ∈ divSupp P' (rename v s), T' W' = if imageZ v W' ∈ divSupp (imageZ v P') s then (E W' : ℝ) * T (imageZ v W') else 0 := by
    intro W' hW'
    obtain ⟨G', J', hJ', hEW⟩ := hE W' hW'.1.isPrime
    by_cases hh : IsHorizontal W'
    · have hh' : IsHorizontal (imageZ v W') := (ArithmeticIntersectionCycle.isHorizontal_imageZ_iff v W').2 hh
      rcases hHor I hI n hn K ι K' ι' κ v P' L L' s α W' hv hP' hP hL hLL' hs hsP hW' hh with
        ⟨hm, he⟩ | ⟨hm, h0⟩
      · simp only [T', T, if_pos hh, if_pos hm, if_pos hh', he G' J' hJ', hEW]
      · simp only [T', if_pos hh, if_neg hm, h0]
    · have hh' : ¬ IsHorizontal (imageZ v W') := fun h => hh ((ArithmeticIntersectionCycle.isHorizontal_imageZ_iff v W').1 h)
      have ha : (fun j => (L' j).a) = fun j => pullDeg κ (L j).a := funext fun j => (hLL' j).1
      rcases hVert K ι K' ι' κ v P' n (fun j => (L j).a) s α W' hv hP' hP hs hsP hW' hh with
        ⟨hm, he⟩ | ⟨hm, h0⟩
      · simp only [T', T, if_neg hh, if_pos hm, if_neg hh', ArithmeticIntersectionCycle.charOf_imageZ]
        rw [ha, he G' J' hJ', hEW]
        push_cast
        ring
      · simp only [T', if_neg hh, if_neg hm]
        rw [ha, h0]
        simp

  have hfin' : (divSupp P' (rename v s)).Finite := divSupp_finite _ _
  have hfin : (divSupp (imageZ v P') s).Finite := divSupp_finite _ _
  have key : ∀ W ∈ hfin.toFinset,
      ∑ W' ∈ hfin'.toFinset.filter (fun W' => imageZ v W' = W),
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' =
        J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0 * multAt (imageZ v P' ⊔ Ideal.span {s}) W := by
    intro W hW
    have h := hPush K ι K' ι' κ v P' n G J s α W E hv hP' hP hJ hs hsP (hfin.mem_toFinset.1 hW)
      (fun W' hW' _ => hE W' hW'.1.isPrime)
    have hfiber : {W' | W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W}.Finite :=
      hfin'.subset (fun _ hx => hx.1)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfiber] at h
    rw [← h]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext W'
    simp [Set.Finite.mem_toFinset]

  show (∑ᶠ W' ∈ divSupp P' (rename v s), (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * T' W') =
    (J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0 : ℝ) * ∑ᶠ W ∈ divSupp (imageZ v P') s, (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℝ) * T W
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc ∑ W' ∈ hfin'.toFinset, (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * T' W'
      = ∑ W' ∈ hfin'.toFinset, if imageZ v W' ∈ hfin.toFinset then
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') else 0 := by
        refine Finset.sum_congr rfl fun W' hW' => ?_
        rw [hterm W' (hfin'.mem_toFinset.1 hW')]
        simp only [Set.Finite.mem_toFinset]
        split_ifs <;> ring
    _ = ∑ W' ∈ hfin'.toFinset with imageZ v W' ∈ hfin.toFinset,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') := by
        rw [Finset.sum_filter]
    _ = ∑ W ∈ hfin.toFinset, ∑ W' ∈ hfin'.toFinset with imageZ v W' = W,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
    _ = ∑ W ∈ hfin.toFinset, ((∑ W' ∈ hfin'.toFinset with imageZ v W' = W,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' : ℤ) : ℝ) * T W := by
        refine Finset.sum_congr rfl fun W _ => ?_
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun W' hW' => ?_
        rw [(Finset.mem_filter.1 hW').2]
    _ = (J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0 : ℝ) *
          ∑ W ∈ hfin.toFinset, (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℝ) * T W := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun W hW => ?_
        rw [key W hW]
        push_cast
        ring

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]




theorem isProjVarQ_of_isArithVar {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {e : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    IsProjVarQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e := by
  obtain ⟨-, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have := hprime
  have hch : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := Ideal.mem_comap.mpr hm
    rw [show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot] at hm'
    exact hm'
  obtain ⟨hQ, hcomap, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mpr
    ⟨hQ, ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, MvPolynomial.map_X]
    exact h
  · have hd' : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
        P.map (MvPolynomial.map (Int.castRingHom ℚ))) + 1 =
        ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← hdim]
      exact hd
    show ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
      P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d at hd'
    induction d using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.bot_add] at hd'
      exact absurd hd' (WithBot.bot_ne_coe)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        have h3 : (⊤ : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast hd'
        rw [top_add] at h3
        exact absurd h3.symm (ENat.natCast_ne_top _)
      | coe n =>
        have h1 : n + 1 = e + 1 + Fintype.card K := by exact_mod_cast hd'
        have h2 : n = e + Fintype.card K := by omega
        rw [h2]
        rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PBCMult
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial IsLocalRing
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

noncomputable section

namespace BCMultProof

theorem length_quot_map_of_flat {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (φ : A →+* L) [IsLocalHom φ] (hflat : φ.Flat)
    (hmax : (maximalIdeal A).map φ = maximalIdeal L) (J : Ideal A) :
    Module.length L (L ⧸ J.map φ) = Module.length A (A ⧸ J) := by
  let _ := φ.toAlgebra
  have : Module.Flat A L := hflat
  have : IsLocalHom (algebraMap A L) := ‹IsLocalHom φ›
  have key := IsLocalRing.length_baseChange A L (A ⧸ J)
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L J).toLinearEquiv.length_eq,
    RingHom.algebraMap_toAlgebra, hmax] at key
  have h1 : Module.length L (L ⧸ maximalIdeal L) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)
  rw [h1, mul_one] at key
  exact key

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]


end BCMultProof

end

end GroundTheory.Heights₂.Heights.Inter
end

