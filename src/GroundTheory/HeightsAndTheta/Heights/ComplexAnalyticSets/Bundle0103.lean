module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0086
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceUnmixedGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceUnmixedGeneral.proof (hA : CMHeightOneGeneral.Statement) (hC : LocalDimDomain.Statement)
    (hB : SliceLocalDimGeneral.Statement) (hD : SliceCMUnmixed.Statement) :
    SliceUnmixedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hA n J W (linForm u) hJ hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hqJ : q ∈ zeroSet J := fun g hg => hq g (hW.1.2 (Ideal.mem_sup_left hg))
  obtain ⟨O, hOo, hOd, hO⟩ := hB n d J q hJ hdim hqJ
  exact ⟨O, hOo, hOd, fun L hL =>
    hD n d J L q (hf q hq hfq) (hC n (d + 1) J hJ hdim q hqJ) (hO L hL)⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeCollarMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Matrix ComplexSets

noncomputable section

theorem TubeCollarMass.proof (hC : TubeCollarCompare.Statement) (hM : ChartMassCompare.Statement)
    (hF : MassFinite.Statement) : TubeCollarMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  obtain ⟨C, hCle⟩ := hC n d J A P R hJ hdim hA hP
  have hψ : ∀ k : Fin (d + 1), SmoothNear (zeroSet J) ((fun _ => euclPot) k) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)

  have hI : Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ))
      (fun _ : Fin (d + 1) => euclPot)) := by
    obtain ⟨K, hK, hle⟩ := hM n (d + 1) J A (fun _ => euclPot) R hJ hdim hA hψ
    have hmeas := (SheetSumMeasurable.proof n (d + 1) J A
      ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) (fun _ => euclPot) hJ hdim hA
      (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hbd : Bornology.IsBounded
        (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
      (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
    obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
    have h1 := hle (fun _ => 1) measurable_const
    simp only [enorm_one, setLIntegral_one] at h1
    refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
    exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hF n (d + 1) J hJ hdim R')

  have hl : Measurable (logAbsSq P) :=
    Real.measurable_log.comp ((MvPolynomial.continuous_eval P).norm.pow 2).measurable
  refine (hI.const_mul C).mono'
    (((measurable_tubeDens hA P R _).indicator (measurableSet_le measurable_const hl)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y)]
  exact hCle y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

theorem measurable_poincareDeepWeight : Measurable poincareDeepWeight := by
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact Measurable.ite (measurableSet_lt hn.log measurable_const) (hn.mul (hn.log.pow_const 2)).inv
    measurable_const

theorem tubeDeep_term (hR : TubeDeepRankOne.Statement) {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} {P : MvPolynomial (Fin (d + 1)) ℂ} {R : ℝ} {y : Fin (d + 1) → ℂ}
    {x : Fin n → ℂ} {s : (Fin (d + 1) → ℂ) → Fin n → ℂ} (hx : x ∈ fibre J A y) (hs : IsSheetAt J A x s)
    (hy : logAbsSq P y < -Real.exp 1) :
    |(Metric.closedBall 0 R).indicator (fun x => tubeWeight P (A *ᵥ x)) x *
        ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y| =
      (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 *
          ((2 / Real.pi) ^ (d + 1) * poincareDeepWeight (deepMap P s I y 0)) := by
  obtain ⟨U, hU, hxU, hsd, -, hsec, -⟩ := hs
  have hAx : A *ᵥ x = y := hx.2
  rw [hAx] at hxU
  have hP : eval y P ≠ 0 := by
    intro h0
    simp only [logAbsSq, h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Real.log_zero] at hy
    linarith [Real.exp_pos 1]
  rw [hR n d A P U s y hU hxU hsd (fun y' hy' => (hsec y' hy').1) hP]
  have hw : ∀ I : Fin d → Fin n,
      poincareDeepWeight (deepMap P s I y 0) = (‖eval y P‖ ^ 2 * logAbsSq P y ^ 2)⁻¹ := by
    intro I
    simp only [deepMap, Matrix.cons_val_zero, poincareDeepWeight]
    exact if_pos hy
  have ht : tubeWeight P y = (logAbsSq P y ^ 2)⁻¹ :=
    if_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  simp only [hw]
  by_cases hxR : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
  · rw [Set.indicator_of_mem hxR, Set.indicator_of_mem hxR, hAx, ht, one_mul]
    have hp : 0 < ‖eval y P‖ := norm_pos_iff.2 hP
    have hl : logAbsSq P y ≠ 0 := by linarith [Real.exp_pos 1]
    rw [abs_of_nonneg (by positivity), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    field_simp
  · simp [Set.indicator_of_notMem hxR]

theorem TubeDeepMass.proof (hR : TubeDeepRankOne.Statement) (hC : TubeDeepAreaCount.Statement)
    (hW : TubeDeepWeightMass.Statement) : TubeDeepMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hc0 : 0 ≤ (2 / Real.pi) ^ (d + 1) := by positivity
  set g : (Fin (d + 1) → ℂ) → ℝ := fun z => (2 / Real.pi) ^ (d + 1) * poincareDeepWeight (z 0) with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z =>
    mul_nonneg hc0 (by unfold poincareDeepWeight; split_ifs <;> positivity)
  have hgm : Measurable g :=
    measurable_const.mul (measurable_poincareDeepWeight.comp (measurable_pi_apply 0))
  have hl : Measurable (logAbsSq P) :=
    ((continuous_norm.comp (MvPolynomial.continuous_eval P)).pow 2).measurable.log
  have hF : ∀ y, {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y =
      sheetSum J A (fun x s => (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y := by
    intro y
    by_cases hy : logAbsSq P y < -Real.exp 1
    · rw [Set.indicator_of_mem (show y ∈ {y | logAbsSq P y < -Real.exp 1} from hy), tubeDens, chartAbsDens, sheetSum, sheetSum]
      refine finsum_congr fun x => finsum_congr fun hx => ?_
      split_ifs with h
      · exact tubeDeep_term hR hx h.choose_spec hy
      · rfl
    · rw [Set.indicator_of_notMem (show y ∉ {y | logAbsSq P y < -Real.exp 1} from hy)]
      have hw0 : ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (I : Fin d → Fin n), g (deepMap P s I y) = 0 := by
        intro s I
        simp only [hg, deepMap, Matrix.cons_val_zero, poincareDeepWeight]
        exact mul_eq_zero_of_right _ (if_neg hy)
      simp [sheetSum, hw0]
  obtain ⟨N, hN⟩ := hC n d J A P R hJ hdim hA
  refine ⟨((measurable_tubeDens hA P R _).indicator (measurableSet_lt hl measurable_const)).aestronglyMeasurable,
    ?_⟩
  have hnn : ∀ y, 0 ≤ {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y :=
    fun y => Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y
  show ∫⁻ y, ‖{y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y‖ₑ < ⊤
  calc _ = ∫⁻ y, ENNReal.ofReal (sheetSum J A (fun x s =>
          (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
            ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y) :=
        lintegral_congr fun y => by rw [Real.enorm_eq_ofReal (hnn y), hF y]
    _ ≤ (N : ℝ≥0∞) * ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (g z) :=
        hN g hgm hg0
    _ = (N : ℝ≥0∞) * (ENNReal.ofReal ((2 / Real.pi) ^ (d + 1)) *
          ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R},
            ENNReal.ofReal (poincareDeepWeight (z 0))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact congrArg _ (lintegral_congr fun z => ENNReal.ofReal_mul hc0)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top N)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hW d R))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMQuotientUnmixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

def CMQuotientUnmixed.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (d : ℕ) (x : Fin d → B),
    (∀ i, x i ∈ maximalIdeal B) →
    ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B →
      ∀ p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)),
        p ∈ (Ideal.span (Set.range x)).minimalPrimes ∧
          ringKrullDim (B ⧸ p) = ringKrullDim (B ⧸ Ideal.span (Set.range x))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRegularElement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

def CMRegularElement.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (y : B), y ∈ maximalIdeal B →
    (∀ p ∈ minimalPrimes B, y ∉ p) →
      y ∈ nonZeroDivisors B ∧ IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y})

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StModelLocalizationMaximalPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def ModelLocalizationMaximalPoint.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (P : Ideal (Localization (normalModelSubmonoid M q))), P.IsMaximal →
      ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q ∧
        P.comap ((algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))).comp
            (Ideal.Quotient.mk M.ideal)) =
          RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDisc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalModelDisc.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ r : ℝ, 0 < r ∧ ∃ φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ,
        DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧
          Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧ φ 0 = w

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelProjectionLocallyInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def NormalModelProjectionLocallyInjective.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ U ∈ 𝓝 w, Set.InjOn IndefiniteRowSideFullHecke.ComplexSets.firstCoords (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdDeterminesPlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def OrdDeterminesPlace.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P P' : MaximalSpectrum (curveNormalisation I q),
        (∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
          Ring.ord (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)))) →
        P = P'

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def OrdFiniteNonZeroDivisor.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∀ P : MaximalSpectrum (curveNormalisation I q),
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) ≠ ⊤) →
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceBranchExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PlaceBranchExists.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ ν : VarBranch I 1 q, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder ν f

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceHasBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PlaceHasBranch.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ b, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder (c b) f

end

end GroundTheory.Heights₂.Heights
end

