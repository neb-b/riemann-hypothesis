module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsEtaRuleExistsUniqueMemSec
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppellHumbertMeanSquareEqOfProportionalSections
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm


open GlobalTheory.UnitFrameGen MeasureTheory in
theorem ahMean_eq_of_secBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P P' : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ) (m m' : ℝ), IsPeriod (F.Di k) ty P → IsPeriod (F.Di k) ty P' → (∀ v, P v = h₀ *ᵥ P' v) → x = F.u k P → x' = x → SecBC (RingHom.id ℂ) a x x' s s' → AHMean F k P x s m → AHMean F k P' x' s' m' → m' = ‖a‖ ^ 2 * m := by
  intro E _ _ _ H Dw l Xo σ' g ty F i P' P h x' x s' s a m' m hp' hp hg hu' hxx hbc hA' hA
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA'
  obtain ⟨hdet, huu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F i
    P P' (LinearEquiv.refl _ _) h hp hp' (fun _ _ => rfl) (fun _ _ => ⟨0, by simp⟩) (fun _ => ⟨0, by simp⟩) hg
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him'])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have tr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (F.ex i P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by rw [hex]; exact hz
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hfr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h *ᵥ z) = fr j z :=
    frames_eq P.range hspan (fun j => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      fr (fun j z => fr' j (h *ᵥ z))
      (fun j j' z => valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      hd (fun j => (hd' j).comp dl.differentiableOn fun z hz => tr j z hz) hn
      (fun j j' z h1 h2 => hc j j' z ((top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩))
      (fun j j' z h1 h2 => by
        have e2 := hc' j j' (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun j hz => by
        have t0 := tr j 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 j hz, h0' j t0, hxx])
      hm (by
        rintro j _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' a j (h *ᵥ z)).1 ((ha' a j (h *ᵥ z)).2 (tr j z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = x' := fun z => by
    rw [← hex z]
    exact (Over.w (F.ex i P' (h *ᵥ z))).trans hu'.symm
  have hθ : ∀ z, θ z = a * θ' (h *ᵥ z) := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc
      (Over.homMk (F.ex i P z).left (hw0 z)) j _ _
      (fun pt h1 h2 => hv' j (h *ᵥ z) pt (h1.trans (hex z).symm) h2 (tr j z hj))
      (fun pt h1 h2 => hv j z pt h1 h2 hj)
    rw [hfr j z hj, ← mul_assoc] at hval
    exact mul_right_cancel₀ (hn j z hj) hval
  have hθp : ∀ b ∈ P.range, ∀ z, ‖θ' (h *ᵥ (z + b))‖ ^ 2 *
      Real.exp (-Real.pi * (hermForm Hm (z + b) (z + b)).re) =
      ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun b hb z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + b)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp b hb]; exact hj
    let p : Over.mk x' ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv' j (h *ᵥ z) _ (by rw [hex]; exact e1) e2 (tr j z hj)
    have v2 := hv' j (h *ᵥ (z + b)) _ (by rw [hex, hexp b hb]; exact e1) e2 (tr j _ hj')
    rw [hfr j _ hj] at v1
    rw [hfr j _ hj'] at v2
    exact normSq_periodic hH _ _ _ _ z b (hn j _ hj') (v2.symm.trans v1) (hm j b hb z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun b hb z => by simp only [hHH, hθp b hb z])
  · rw [← hI, ← hI', ← hmean, ← mul_div_assoc, ← integral_const_mul]
    congr 2
    funext z
    rw [hθ, hHH, norm_mul, mul_pow, mul_assoc]
  · rintro ⟨b, hb⟩
    refine ⟨b, hinj ?_⟩
    simp only
    rw [← hg, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨b, hg b⟩

end GlobalTheory.FrameNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdeg
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem birSt_of_ratios_trdeg :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), ((∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) / evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j) → BIRSt h j hj hG G) ∧ (BigAt h j hj hG G → BIRSt h j hj hG G) := by
  intro D T h j hj hG ka wL wF G
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2
  have hint := GlobalTheory.Reg.intFormSt_holds D T h j hj hG wL _ G.w
  exact ⟨fun hB => birSt_of h j hj hG htr G hB hint,
    fun hBig => birSt_of_big h j hj hG htr G hBig hint⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
section
set_option autoImplicit false

noncomputable section

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.EtaForm

namespace GlobalTheory.Reg

theorem exists_even_sec_evR_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)), ∃ n : ℕ, 0 < n ∧ Even n ∧ ∃ f ∈ sec Xo c 0 n, evR Xo c f y ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ y
  have hR : Odd 3 := by decide
  have h1 : 1 < 3 := by decide
  obtain ⟨hfG, hfL, -⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw 3 h1
  letI hFin : Fintype (LatMod Dw 3) := Fintype.ofFinite _
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  obtain ⟨cf, -, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR h1
    2 0 (CAt σ) 1 (fun _ => y)
  obtain ⟨⟨f, hrule, -⟩, hsec⟩ := GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR
    (Fin 2 → LatMod Dw 3) 2 (fun j => (cf j : ℤ)) (shiftFam 3 0)
  refine ⟨2 * Nat.card (LevGrp Dw (3 ^ 4)), Nat.mul_pos two_pos Nat.card_pos, even_two_mul _, f, hsec f hrule, ?_⟩
  exact hne 0 _ (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c 3 hR _ _ _ _ f hrule (CAt σ) y (hT _ _)).1

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NotGoodConj
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.Existence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem not_good_conj (σ : c.F →+* ℂ) (h : Formalism.L2.PjFree.GoodEmb c σ) :
    ¬ Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  have h1 : (starRingEnd ℂ) H.rt0 = H.rt0 := by
    have e : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h'
    unfold Formalism.L2.PjFree.GoodEmb at h
    rwa [h] at e
  have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re] at hre
  rw [h2] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

theorem good_conj (σ : c.F →+* ℂ) (h : ¬ Formalism.L2.PjFree.GoodEmb c σ) :
    Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
  have := Formalism.L2.PjFree.goodEmb_goodOf c σ
  unfold Formalism.L2.PjFree.goodOf at this
  rwa [if_neg h] at this

theorem cabs_mul {K : Type} [Field K] {σ : K →+* ℂ} (a b : CAt σ) : cabs (a * b) = cabs a * cabs b :=
  norm_mul (show ℂ from a) (show ℂ from b)

theorem cabs_one {K : Type} [Field K] {σ : K →+* ℂ} : cabs (1 : CAt σ) = 1 :=
  norm_one (α := ℂ)

theorem cabs_unit_pos {K : Type} [Field K] {σ : K →+* ℂ} (a : (CAt σ)ˣ) : 0 < cabs (a : CAt σ) := by
  have h : cabs (a : CAt σ) * cabs ((a⁻¹ : (CAt σ)ˣ) : CAt σ) = 1 := by
    rw [← cabs_mul, Units.mul_inv, cabs_one]
  have h0 : 0 ≤ cabs (a : CAt σ) := norm_nonneg _
  refine lt_of_le_of_ne h0 fun e => ?_
  rw [← e, zero_mul] at h
  exact zero_ne_one h

theorem baseNorm_pos {x : ℝ} (hx : 0 < x) (i : Ix Dw) : 0 < baseNorm Dw x i := by
  cases i with
  | none => exact one_pos
  | some j => exact Real.sqrt_pos.mpr (by have := Real.pi_pos; positivity)

theorem cabs_eq {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {k k'} (x : (U.X k).dom) (x' : (U.X k').dom) (t t' : Ix Dw → (CAt σ)ˣ)
    (y : FrPt Xo c (CAt σ)) (hx : IsUnitFr (U.X k) x.1) (hx' : IsUnitFr (U.X k') x'.1)
    (h : FrBor t (U.un k x) y) (h' : FrBor t' (U.un k' x') y) (i : Ix Dw) :
    cabs (t i : CAt σ) = cabs (t' i : CAt σ) := by
  have hi : FrBor t'⁻¹ y (U.un k' x') :=
    (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k' x') y y).2.2.2 t' h'
  have hc : FrBor (t'⁻¹ * t) (U.un k x) (U.un k' x') :=
    (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y (U.un k' x')).2.2.1 t t'⁻¹ h hi
  have h1 : cabs ((t'⁻¹ * t) i : CAt σ) = 1 := by
    cases i with
    | none => exact _root_.GlobalTheory.UnitFrameGen.cabs_gen_eq_one E H Dw l Xo c σ r U hσ hU k k' x x' _ hx hx' hc
    | some j => exact GlobalTheory.T.cabs_frBor_eq_one_of_unitFr E H Dw l Xo c σ r U hσ hU k k' x x' _ hx hx' hc j
  have e : (t i : CAt σ) = (t' i : CAt σ) * ((t'⁻¹ * t) i : CAt σ) := by
    rw [← Units.val_mul, Pi.mul_apply, Pi.inv_apply, mul_inv_cancel_left]
  rw [e, cabs_mul, h1, mul_one]

theorem exists_good {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {xR : ℝ} (hx : 0 < xR) :
    ∃ G : FrPt Xo c (CAt σ) → Ix Dw → ℝ, (∀ y i, 0 < G y i) ∧
      ∀ k (z : (U.X k).dom), IsUnitFr (U.X k) z.1 → ∀ (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)),
        FrBor t (U.un k z) y → ∀ i, G y i = cabs (t i : CAt σ) * baseNorm Dw xR i := by
  choose k x t hu hb using (_root_.GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU).2
  refine ⟨fun y i => cabs (t y i : CAt σ) * baseNorm Dw xR i,
    fun y i => mul_pos (cabs_unit_pos _) (baseNorm_pos hx i), ?_⟩
  intro k' z hz t' y hy i
  show _ * _ = _
  rw [cabs_eq U hσ hU (x y) z (t y) t' y (hu y) hz (hb y) hy i]

theorem transport {P : (c.F →+* ℂ) → Prop} (G : ∀ σ : c.F →+* ℂ, P σ → FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    {σ τ : c.F →+* ℂ} (e : τ = σ) (hσ : P σ) (hτ : P τ) (φ : CAt σ →ₐ[c.F] CAt τ)
    (hφ : ∀ z : CAt σ, (show ℂ from φ z) = (show ℂ from z)) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt τ))
    (h : FrMap φ y y') : G τ hτ y' = G σ hσ y := by
  subst e
  have h1 : φ = AlgHom.id c.F (CAt τ) := AlgHom.ext hφ
  subst h1
  have u := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ (AlgHom.id c.F (CAt τ)) y
  rw [u.1 _ _ h u.2.1]

theorem exists_pinned : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ xR : ℝ, 0 < xR → ∃ fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ, FnPin U xR fn ∧ FnNe Xo c fn := by
  classical
  intro E _ _ _ H Dw l Xo c r U hU xR hx
  choose G hpos hpin using fun (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) =>
    exists_good (U σ) hσ (hU σ hσ) hx
  choose bc hbc using fun (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ (conjAlg σ) y
  refine ⟨fun σ y => if h : Formalism.L2.PjFree.GoodEmb c σ then G σ h y else G _ (good_conj σ h) (bc σ y), ⟨?_, ?_⟩, ?_⟩
  · intro σ hσ k z hz t y hy i
    simp only [dif_pos hσ]
    rw [abs_of_pos (hpos σ hσ y i)]
    exact hpin σ hσ k z hz t y hy i
  · intro σ y y' hy i
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · have hn := not_good_conj σ hσ
      simp only [dif_pos hσ, dif_neg hn]
      have hm : FrMap ((conjAlg ((starRingEnd ℂ).comp σ)).comp (conjAlg σ)) y (bc _ y') :=
        frMap_trans (Xo := Xo) (c := c) _ _ _ _ _ y y' _ hy (hbc _ y')
      have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ :=
        RingHom.ext fun a => Complex.conj_conj (σ a)
      rw [transport G e hσ (good_conj _ hn) _ (fun z => Complex.conj_conj (show ℂ from z)) y _ hm]
    · have hg := good_conj σ hσ
      simp only [dif_pos hg, dif_neg hσ]
      rw [(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ (conjAlg σ) y).1 _ _ hy (hbc σ y)]
  · intro σ y i
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · simp only [dif_pos hσ]
      exact (hpos σ hσ y i).ne'
    · simp only [dif_neg hσ]
      exact (hpos _ _ _ i).ne'

end GlobalTheory.FrameNorm.Existence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNormStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → FnNe Xo c fn ∧ (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ k (x : ((U σ).X k).dom) (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)), FrBor t ((U σ).un k x) y → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y = Formalism.L2.PjFree.lieFac Dw xR a * ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x.1) ∧ ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))), FrMap (conjAlg σ) y y' → ∀ a n, ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn ((starRingEnd ℂ).comp σ)) (ex Dw a n) f y' = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y := by
  first | exact @GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm | exact GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm | (intros; apply GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm <;> assumption)
end

