module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CmLiftConditionOfLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open GlobalTheory.UnitFrameGen MeasureTheory
open scoped Matrix

noncomputable section

namespace GlobalTheory.LevelCusp

theorem cabs_gen_eq_one_of_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) = 1 := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU ρ ν k k' x x' y' t hmv hb hx hx'
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  obtain ⟨P, -, hp, hu, -, hA⟩ := hP k x
  obtain ⟨P', -, hp', hu', -, hA'⟩ := hP k' x'
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA' hx'
  clear hA hA' hP
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν _ _ hmv
  have hxρ : (U.un k' x').x = (U.un k x).x ≫ ρ := hb.1.symm.trans hmv.1
  obtain ⟨hxx, -, hbc⟩ := hb
  clear hmv
  generalize ik k = i at *
  generalize ik k' = i' at *
  obtain ⟨gam, hl, hg1, hg4, hex0⟩ := exists_isometry_of_sabMap F ν hp hp'
    ((congrArg (· ≫ ρ) hu).symm.trans (hxρ.symm.trans hu'))
  obtain ⟨h, hdet, hh⟩ : ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h.det ∧ ∀ z, h *ᵥ z = hl z :=
    ⟨LinearMap.toMatrix' hl.toLinearMap, by
      rw [LinearMap.det_toMatrix']; exact LinearEquiv.isUnit_det' hl,
      fun a => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hg : ∀ a, P' (gam a) = h *ᵥ P a := fun a => by rw [hh, hg4]
  have hex : ∀ z, (F.ex i' P' (h *ᵥ z)).left = (F.ex i P z).left ≫ ν.φ := fun z => by rw [hh, hex0]
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him', hg1])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have hcov2 : ∀ z, ∃ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F.ex i P z).left ≫ ν.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i' P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' z hz => by
    rw [hex]; exact ((o1 _ _ _).1 hz).1
  have tr2 : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j' := fun j j' z hz => ((o1 _ _ _).1 hz).2
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = ((U.un k x).x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i P z)).trans hu.symm
  have hw0' : ∀ z, (F.ex i' P' z).left ≫ Xo.univ.t.G.hom = ((U.un k' x').x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i' P' z)).trans hu'.symm
  have hz0 : (F.ex i P 0).left = ((U.un k x).x : Sp ℂ ⟶ Xo.X) ≫ eSec Xo.univ.t.G := by
    rw [(F.ex_ker i P hp 0).2 (zero_mem _), hu]
    rfl
  have hfr : ∀ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 →
      fr' q.1 (h *ᵥ z) = valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z :=
    frames_eq P.range hspan (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov2
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      (fun q z => valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z) (fun q z => fr' q.1 (h *ᵥ z))
      (fun q q' z => valAt' ((F.ex i P z).left ≫ ν.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
        (Xo.univ.t.PP.L.g q.1 q'.1).val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F i P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
        fun z hz => ⟨Set.mem_univ _, hz⟩).mul ((hd q.2).mono fun z hz => tr2 _ _ z hz))
      (fun q => (hd' q.1).comp dl.differentiableOn fun z hz => tr _ _ z hz)
      (fun q z hz => mul_ne_zero (o2 _ _ _ hz) (hn _ z (tr2 _ _ z hz)))
      (fun q q' z h1 h2 => by
        rw [hc q.2 q'.2 z ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ z h1, tr2 _ _ z h2⟩), ← mul_assoc,
          o3 _ _ _ _ _ h1 h2, mul_assoc])
      (fun q q' z h1 h2 => by
        have e2 := hc' q.1 q'.1 (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun q hz => by
        have t0 := tr _ _ 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 _ (tr2 _ _ 0 hz), h0' _ t0, hxρ]
        exact o4 _ _ _ _ hz0 hz)
      (fun q a haa z hz => by
        rw [hexp a haa, norm_mul, norm_mul, hm _ a haa z (tr2 _ _ z hz)]
        ring)
      (by
        rintro q _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' (gam a) q.1 (h *ᵥ z)).1
          ((ha' (gam a) q.1 (h *ᵥ z)).2 (tr _ _ z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) (U.un k' x').x y'.x
      (U.un k' x').s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hθ : ∀ z, θ z = Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h *ᵥ z) := fun z => by
    obtain ⟨q, hq⟩ := hcov2 z
    let p : Over.mk ((U.un k x).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 z _ e1 e2 (tr2 _ _ z hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex i' P' (h *ᵥ z)).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 (h *ᵥ z) pt h1 h2 (tr _ _ z hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex z)) h2 hq)
    have hval2 : valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * (θ z * fr q.2 z) =
        Formalism.L2.PjFree.toC (t none : CAt σ) * (θ' (h *ᵥ z) * fr' q.1 (h *ᵥ z)) :=
      (congrArg (valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    rw [hfr q z hq] at hval2
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hn _ z (tr2 _ _ z hq)))
    linear_combination hval2
  have ht0 : Formalism.L2.PjFree.toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  have hθp : ∀ a ∈ P.range, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + a) (z + a)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun a ha z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let p : Over.mk ((U.un k x).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv j z _ e1 e2 hj
    have v2 := hv j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    exact normSq_periodic hH _ _ _ _ z a (hn j _ hj') (v2.symm.trans v1) (hm j a ha z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hn0 : ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≠ 0 := norm_ne_zero_iff.2 ht0
  have key : ∀ z, ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' (h *ᵥ z) (h *ᵥ z)).re) =
      (‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ^ 2)⁻¹ *
        (‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) :=
    fun z => by rw [hθ, hHH, norm_mul, mul_pow]; field_simp
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun a ha z => by simp only [key, hθp a ha z])
  · simp only [key] at hmean
    rw [hI', integral_const_mul, mul_div_assoc, hI, mul_one, inv_eq_one] at hmean
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hmean
  · rintro ⟨a, ha⟩
    refine ⟨gam.symm a, hinj ?_⟩
    simp only
    rw [← hg, gam.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨gam a, hg a⟩

end GlobalTheory.LevelCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBelowOneOfHodgeTateChartForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowGerm

theorem lemmaBT_of_hodgeTate_chart : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → LemmaBT := fun h =>
  lemmaBT_of_characters GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 GlobalTheory.firstFiveLaws.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.1 (GlobalTheory.T.exists_characters_boundedMinors_of_hodgeTateChartBound h)

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DescentIdFOfLaws
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowDescent

theorem eq_famCast_of_heq {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k k' : ℕ} (e : k = k') (r : Fam Dp F k') (s : Fam Dp F k) (h : HEq r s) :
    r = famCast e s := by
  subst e
  exact eq_of_heq h

theorem descent_cast (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V))
    (P : PELUnif (maximalIdeal V) t) (hP : P.TorsionIso) :
    letI := H.starRing
    ∀ (a a' : 𝓞 E) (g g' k : ℕ) (e : 1 * g' = k), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' →
      a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1)
      (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα →
    ∀ (pb : QkPt P.D.toPre F (1 * g'))
      (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g'))))
      (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')),
      P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 →
      FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ →
      Fam.IsSmul P.D.toPre F ζb tb₀ tb →
    ∀ (p : QkPt P.D.toPre F (k * g))
      (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (k * g))))
      (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (k * g) p w ζ →
      P.ToA F (k * g) p x → x ≫ P.oA.act (star a) = 1 →
    ∀ (s₂ t₀ r : Fam P.D.toPre F (k * g)), PullAl P.D F P.oD a k g (famCast (Dp := P.D.toPre) (F := F) e tb) s₂ →
      PhiRel P.D.toPre F (k * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r →
    ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g)))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g)))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))),
      PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧
      x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧
      PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  letI := H.starRing
  intro a a' g g' k e
  subst e
  exact descent_one_generator hL hL2 hL4 hT V E H t P hP a a' g g'

theorem descentIdF_of_laws :
    Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → DescentIdF := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c n
  letI := H.starRing
  intro T io y _ C P _ g g' hg hg' hne _ _ π π' hπ hπ' _ _ _ F _ _ _ _ _ _ v ϖ _ _ Q _ D' A' G' gr cm pD pA pG U' PU
    md oD' hx hoD oA' hoA θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb p w ζ x hw hζ hf hpx hxπ
    s₂ t₀ r hs₂ hΦ hr
  obtain ⟨oA'', hoA'', t', P', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    exists_pelUnif_of_unifPow hL hL2 hL4 hT T.V E H C.I.G P n D' A' G' pD pA pG U' PU oD' hx hoD
  have hact : ∀ a, oA'.act a = oA''.act a := fun a =>
    Fan.IsLimit.hom_ext pA.lim _ _ fun i => (hoA a i).trans (hoA'' a i).symm
  have hxa : x ≫ oA''.act (star (star π)) = 1 := by
    refine Fan.IsLimit.hom_ext pA.lim _ _ fun i => ?_
    have := pA.hom i
    change (x ≫ oA''.act (star (star π))) ≫ pA.pr i = 1 ≫ pA.pr i
    rw [star_star, Category.assoc, hoA'', hxπ, MonObj.one_comp]
  have htors : P'.TorsionIso :=
    _root_.GlobalTheory.UT.torsionIso_of_pelUnif ⟨hL, hL2, hL3, hL4, hL5⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
      (twisting_statements_of_laws hL hT).1 (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H T.V (maximalIdeal T.V)
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ t' P'
  rw [hact] at hxba
  simp only [hact]
  clear hoA hact hoA'' hxπ hx hoD PU pD pA pG
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
    descent_cast hL hL2 hL4 hT T.V E H t' P' htors (star π) (star π') g g' g' (one_mul g') hg.one_le hg'.one_le
      ((Nat.coprime_primes hg hg').2 hne) (by rw [star_star, _root_.mul_comm, hπ])
      (by rw [star_star, _root_.mul_comm, hπ']) F θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
      p w ζ x hw hζ hf hpx hxa s₂ t₀ r hs₂ hΦ hr
  exact ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, eq_famCast_of_heq _ _ _ k₉⟩

end GlobalTheory.PowDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTermLe
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.SmallTranslate

theorem exists_term_le {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {I J : Type} [Fintype I] [Fintype J]
    (a : I → F) (c : J → F) (x : J → I → F) (ha : ∀ i, 0 ≤ v (a i)) (hc : ∀ j, 0 ≤ v (c j)) (r : ℚ)
    (h : v (∑ j, c j * ∑ i, a i * x j i) = (r : WithTop ℚ)) :
    ∃ (i : I) (j : J) (ρ : ℚ), v (x j i) = (ρ : WithTop ℚ) ∧ ρ ≤ r := by
  by_contra hne
  have hlt : ∀ i j, (r : WithTop ℚ) < v (x j i) := fun i j => by
    by_contra hle
    obtain ⟨ρ, hρ, hρr⟩ := WithTop.le_coe_iff.1 (not_lt.1 hle)
    exact hne ⟨i, j, ρ, hρ, hρr⟩
  have : (r : WithTop ℚ) < v (∑ j, c j * ∑ i, a i * x j i) := by
    refine AddValuation.map_lt_sum v WithTop.coe_ne_top fun j _ => ?_
    rw [v.map_mul]
    refine lt_add_of_nonneg_of_lt (hc j) (AddValuation.map_lt_sum v WithTop.coe_ne_top fun i _ => ?_)
    rw [v.map_mul]
    exact lt_add_of_nonneg_of_lt (ha i) (hlt i j)
  exact absurd h this.ne'

theorem span_pow (h1 : Laws) (h2 : Laws2) (h3 : Laws3) (h4 : Laws4) (h5 : Laws5) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [hc : IsAdicComplete (maximalIdeal V) V] [CharZero V]
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (Dw : Datum H) (ϖ : V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v)
    (I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
      (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z)))
    (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V))
    [gG : GrpObj G'] [cG : IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n)
    (U' : Unif (maximalIdeal V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) :
    letI := H.starRing
    ∀ [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) → IsUnit ((N : ℕ) : V) →
    ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ →
      PullAl D' F oD' α 1 N θ θα →
    ∀ s : Fam D'.toPre F (1 * N), NuGe D' (sumQ pD.xe Q) F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt D'.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ A'.A))
        (w : ∀ i, LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F (p i).g.b) (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam D'.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, QkToAkU U'.toUnifPre F (1 * N) (p i) (x i)) ∧
        (∀ i k, x i ≫ pA.pr k ≫ P.oA.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd D' F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam D'.toPre F (1 * N),
          PhiRel D'.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul D'.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i := by
  let _ := H.starRing
  intro md oD' hx hoD α N hN hα hcop hu θ θα hθ hθF hθα s hs
  obtain ⟨oA', hoA, t', P', hG, hgrp, hcomm, hD, hmod, hoD', hA, hoA', hU⟩ :=
    GlobalTheory.exists_pelUnif_of_unifPow h1 h2 h4 hT V E H t P n D' A' G' pD pA pG U' PU oD' hx hoD
  obtain ⟨Dw', ⟨I'⟩⟩ := GlobalTheory.exists_tateIso_of_isPowPolAV h1 h2 h4 hT E H V n P.A A' pA F P.oA.act oA'.act hoA Dw I
  have hQ' : IsQ D'.toPre ϖ (sumQ pD.xe Q) := GlobalTheory.QBox.main V ϖ hϖ n P.D D' pD Q hQ
  have hUU : UUStatement := GlobalTheory.UnitBallFree.main h1.globalFns hT
  have hP' : P'.TorsionIso := _root_.GlobalTheory.UT.torsionIso_of_pelUnif ⟨h1, h2, h3, h4, h5⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
    (GlobalTheory.twisting_statements_of_laws h1 hT).1 hUU E H V _
    ⟨inferInstance, inferInstance, inferInstance, hc⟩ t' P'
  subst hG hD hA
  cases hgrp
  cases hmod
  cases hoD'
  cases hoA'
  cases hU
  obtain ⟨m, p, x, w, ζ, tt, a, e1, e2, e3, e4, e5, e6⟩ := ReciprocityTheory.ChartRestriction.G.H1.cmLiftCondition_of_laws h1 n1c (GlobalTheory.twisting_statements_of_laws h1 hT).1 hUU E H V t' P' hP' α N hN hα hcop hu ϖ hϖ _ hQ' F v hv
    Dw' I' θ hθ hθF θα hθα s hs
  refine ⟨m, p, x, w, ζ, tt, a, e1, fun i k => ?_, e3, e4, e5, e6⟩
  have := pA.toIsPowGrp.hom k
  rw [← hoA, ← Category.assoc, e2 i]
  exact MonObj.one_comp _

theorem main : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → RPointT := by
  intro h1 h2 h3 h4 h5 hT E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hFT P hP hy ϖ hϖ Q hQ F _ _ _ _ _ _ v hv I Φ M0 r b hΦ hb hbw n D' A' G' _ _ pD pA pG U' PU _ oD' hx hoD hn
    α N Dg hα hcop hu hN hM θ θα hθ hθF hθα J _ Pi a ha hdeg f hf gm hval
  let _ := io.toAlgebra
  have hN1 : 1 ≤ 1 * N := by omega
  obtain ⟨s, σ', g, lam, hs, hσ', hg, -, ⟨ρl, hlam, hρl⟩, hjet⟩ :=
    _root_.GlobalTheory.PowJets.jets_on_copies h1 h2 h4 hT E H Dw l Xo c (fun _ => rfl) T io y hy C hFT P ϖ hϖ Q hQ Φ M0 r b hΦ hb hbw n hn D' A' G'
      pD pA pG U' PU F v hv (1 * N) Dg (by omega) (by rwa [Nat.one_mul]) f hf
  obtain ⟨m, p, x, w, ζ, t, cf, e1, e2, e3, e4, e5, e6⟩ := span_pow h1 h2 h3 h4 h5 hT T.V E H C.I.G P Dw ϖ hϖ Q hQ F v hv I
    n D' A' G' pD pA pG U' PU oD' hx hoD α N (by omega) hα hcop hu θ θα hθ hθF hθα s hs
  obtain ⟨τ, hτ, hτT, hiff⟩ := GlobalTheory.PowGerm.frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := _root_.GlobalTheory.PowGerm.univPow T.V C.I.G.G G' n _ pG C.xT (_root_.GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C)
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hz τ hτ F (1 * N)
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr h1 h2 h4 hT T.V D' A' G' U' F (1 * N) hN1).2
  choose σ hσ using fun j => (hbij (t j)).exists
  choose h hh using fun j => hex (hτT hFT) (σ j)
  have hsum : g = ∑ j, cf j • h j := by
    let σ₀ : U'.toUnifPre.SecGF F (1 * N) := GlobalTheory.ExpansionLinear.secComb
      (fun j => Out.scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj G')).left (cf j)) σ
    have k1 := GlobalTheory.GroupExpansionLinear.expandsG_sum T.V D' A' G' U' F (1 * N) m cf σ t σ₀ hσ (fun _ => rfl)
    rw [← e6] at k1
    have k2 : σ' = σ₀ := (hbij s).unique hσ' k1
    exact huniq σ' _ _ ((hiff F _ σ' g).1 hg) (hlin m cf σ h σ' hh (fun _ => by rw [k2]; rfl))
  obtain ⟨n1, n2, n3⟩ := GlobalTheory.PowGerm.nabJet _ _ _ C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) n
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
  have k1 := n1 (∑ i, a i • Pi i) _ _ (fun e he => hjet e (he.trans hdeg))
  have k2 := n2 (∑ i, a i • Pi i) Unit (fun _ => lam) (fun _ => MvPowerSeries.map (algebraMap T.Fr F) f)
  rw [Finset.univ_unique, Finset.sum_singleton, Finset.sum_singleton] at k2
  have k3 := n2 (∑ i, a i • Pi i) (Fin m) cf h
  rw [← hsum, k1, k2, Finset.sum_congr rfl fun j _ => congrArg (cf j * ·) (n3 (h j) J a Pi)] at k3
  have k4 := congrArg v k3
  rw [v.map_mul, hlam] at k4
  obtain ⟨i, j, ρ, hρ, hle⟩ := exists_term_le v a cf _ ha e5 (ρl + gm)
    (k4.symm.trans (by rw [WithTop.coe_add]; exact congrArg _ hval))
  obtain ⟨t₀, ht₀, ht⟩ := e4 j
  refine ⟨i, p j, w j, ζ j, x j, t₀, t j, σ j, h j, ρ, (e3 j).1, (e3 j).2.1, (e3 j).2.2, e1 j, e2 j, ht₀, ht, hσ j,
    (hiff F _ _ _).2 (hh j), hρ, ?_⟩
  rw [Nat.one_mul] at hρl
  have : (ρ : ℝ) ≤ ρl + gm := by exact_mod_cast hle
  linarith

end GlobalTheory.SmallTranslate
end
end

