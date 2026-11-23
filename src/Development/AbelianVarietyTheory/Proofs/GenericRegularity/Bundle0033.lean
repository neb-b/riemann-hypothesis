module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveLocOfCountQAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

theorem curveLoc_of_countQAt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), CountQAtSt h j hj hG hT → ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w), ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧ phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a := by
  intro D T h j hj hG hT hQ ka wL wF G S g0 la hH Z r
  exact CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    (birAt_of h j hj hG hT G ((_root_.GlobalTheory.Reg.birSt_of_ratios_trdeg D T h j hj hG ka wL wF G).2 hH.2.1) Z)
    (hQ ka wL wF G S g0 la hH Z) r

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamily
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm.Hol

theorem continuousOn_form {V : Type} [TopologicalSpace V] {g : ℕ} {B : Set V} (h τ : V → Matrix (Fin g) (Fin g) ℂ)
    (hh : ∀ i j, ContinuousOn (fun b => h b i j) B) (hτ : ∀ i j, ContinuousOn (fun b => τ b i j) B)
    (hp : ∀ b ∈ B, ((τ b).map Complex.im).PosDef) :
    ContinuousOn (fun b => ((τ b).map Complex.im).det) B ∧ ∀ i j, ContinuousOn (fun b =>
      ((h b)ᵀ * (((τ b).map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * (h b).map (starRingEnd ℂ)) i j) B := by
  simp only [continuousOn_iff_continuous_restrict] at hh hτ ⊢
  have h1 : Continuous fun b : B => h b := continuous_matrix hh
  have h2 : Continuous fun b : B => (τ b).map Complex.im :=
    (continuous_matrix hτ : Continuous fun b : B => τ b).matrix_map Complex.continuous_im
  have h3 : Continuous fun b : B => ((τ b).map Complex.im)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (h2.matrix_det.inv₀ fun b => (hp b b.2).det_pos.ne').smul h2.matrix_adjugate
  refine ⟨h2.matrix_det, fun i j => ?_⟩
  exact ((h1.matrix_transpose.matrix_mul (h3.matrix_map Complex.continuous_ofReal)).matrix_mul
    (h1.matrix_map Complex.continuous_conj)).matrix_elem i j

theorem exists_continuous_form_mean {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (hty : IsTypeFn H Dw.p Dw.q ty) {A : Type} [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ}
    {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ))
    (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (hB : IsOpen B)
    (hφ : ∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) (hy : ∀ b ∈ B, FrMap (φ b) yA (y b))
    (hP : IsHolPeriods (F.Di k) ty B P) (hx : ∀ b ∈ B, (y b).x = F.u k (P b)) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (B' : Set (Fin m → ℂ)) (Hm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (μ : (Fin m → ℂ) → ℝ),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ i j, ContinuousOn (fun b => Hm b i j) B') ∧ ContinuousOn μ B' ∧
      ∀ b ∈ B', (∀ v w, (hermForm (Hm b) (P b v) (P b w)).im = (F.Di k).EF v w) ∧
        AHMean F k (P b) (y b).x (y b).s (μ b) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hB b₀ hb₀
  obtain ⟨hg, -⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨bas, hbas, -⟩ := GlobalTheory.exists_symplectic_basis_adapted_mod_eight E H (F.Di k) g hg
  obtain ⟨hR1, hR2⟩ := GlobalTheory.RiemannRel.riemann_relations E H (F.Di k) g ty bas hbas
  have hP' : IsHolPeriods (F.Di k) ty (Metric.ball b₀ ε) P :=
    ⟨fun b hb => hP.1 b (hsub hb), fun v => (hP.2 v).mono hsub⟩
  choose! h τ hn hdet hsym hpos _ using fun b hb => hR1 _ (hP'.1 b hb)
  have hhol := hR2 m _ P h τ hP' hn
  obtain ⟨c₁, c₂, hc₁, hc₂, hθ⟩ := F.theta k m _ P bas (-1) h τ Metric.isOpen_ball
    (convex_ball b₀ ε).isPreconnected hP' (fun a b => by rw [hbas]; simp) (fun b hb => ⟨hpos b hb, hn b hb⟩)
  obtain ⟨t1, t2⟩ := GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g c₁ c₂ hc₁ hc₂
  have t3 := t2 m _ h τ Metric.isOpen_ball (fun b hb => ⟨hsym b hb, hpos b hb⟩) hhol
  obtain ⟨fr, κ, hfr, hκ, hval⟩ := _root_.GlobalTheory.GenFactor.exists_holomorphic_factor E H Dw l Xo c σ σ' g ty F k A yA m _ φ y P
    (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) Metric.isOpen_ball
    (fun a => (hφ a).mono hsub) (fun b hb => hy b (hsub hb)) hP' (fun b hb => hx b (hsub hb))
    (fun z => DifferentiableOn.comp (f := fun b : Fin m → ℂ => ((b, z) : (Fin m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2))
      t3 (by fun_prop) fun b hb => ⟨hb, trivial⟩)
    (fun b hb => by
      obtain ⟨-, w, hw⟩ := t1 _ (hsym b hb) (hpos b hb)
      obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hdet b hb)) w
      exact ⟨z, by rw [hz]; exact hw⟩) hθ
  obtain ⟨c1, c2⟩ := continuousOn_form h τ (fun i j => (hhol i j).1.continuousOn)
    (fun i j => (hhol i j).2.continuousOn) hpos
  refine ⟨Metric.ball b₀ ε, _, fun b => ‖κ b‖ ^ 2 * (Real.sqrt (2 ^ g * ((τ b).map Complex.im).det))⁻¹,
    Metric.isOpen_ball, Metric.mem_ball_self hε, hsub, c2, ?_, fun b hb => ⟨?_, ?_⟩⟩
  · refine (hκ.continuousOn.norm.pow 2).mul (ContinuousOn.inv₀ (continuousOn_const.mul c1).sqrt fun b hb => ?_)
    have := (hpos b hb).det_pos
    positivity
  · obtain ⟨Hm, -, -, hH⟩ := (hP'.1 b hb).2.2.2.2
    rw [← (GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ bas _ (h b) (τ b) Hm hbas (hP'.1 b hb) (hn b hb)
      ⟨hsym b hb, hpos b hb⟩ hH).1]
    exact hH
  · exact _root_.GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar E H Dw l Xo σ' g ty F k m _ P fr bas b (h b) (τ b) c₁ c₂ _ _ (κ b) hb (hP'.1 b hb) hbas (hdet b hb)
      (hsym b hb) (hpos b hb) (hn b hb) hc₁ hc₂ hfr (hx b (hsub hb)) (hval b hb).1 (hval b hb).2

end GlobalTheory.FrameNorm.Hol

theorem GlobalTheory.FrameNorm.fn_continuousOn_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ i, ContinuousOn (fun b => |fn σ (y b) i|) B := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn _ hpin σ hσ A _ _ yA m B φ y hB hφ hy i b₀ hb₀
  obtain ⟨hr, hty, hcov, -, -, g, e, F, ik, ψ, hef, hun⟩ := hU σ hσ
  obtain ⟨B₁, k, P, hB₁, hb₁, hs₁, hP, hyP⟩ := _root_.GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨k₀, x₁, t₁, ht₁⟩ := hcov (y b₀)
  obtain ⟨P₁, hP₁, hP₁', hx₁, -⟩ := hun k₀ x₁
  obtain rfl : ik k₀ = k := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb₁) (hx₁.symm.trans (ht₁.1.symm.trans (hyP b₀ hb₁).1))
  obtain ⟨d, hd, horth⟩ := _root_.GlobalTheory.FrameNorm.period_eq_triangular_orthonormal E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ (F.sig _).1 (F.sig _).2 hr
    (hty k₀).1 (hty k₀).2 (hef k₀)
    (_root_.GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ hr (hty k₀).1 (hty k₀).2 (hef k₀) x₁.1 x₁.2 P₁ hP₁ hP₁')
  obtain ⟨B₂, Hm, μ, hB₂, hb₂, hs₂, hHm, hμ, hAH⟩ := GlobalTheory.FrameNorm.Hol.exists_continuous_form_mean F (ik k₀)
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw g e) yA φ y P hB₁ (fun a => (hφ a).mono hs₁)
    (fun b hb => hy b (hs₁ hb)) hP (fun b hb => (hyP b hb).1) hb₁
  have key : ∀ b ∈ B₂, ∃ S : Matrix (Fin g) (Fin g) ℂ, (IsUnit S.det ∧
      (∀ j j', S j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      Hm b = Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))) ∧
      (∀ j, |fn σ (y b) (some (e j))| = ‖S j j‖ * Real.sqrt (2 * Real.pi * xR)) ∧
      |fn σ (y b) none| = Real.sqrt (μ b) := by
    intro b hb
    have hp := hP.1 b (hs₂ hb)
    obtain ⟨x₀, hx₀, hunit, S, hS, hsupp, hper, hform⟩ := horth _ hp
    obtain ⟨P₀, hP₀, hP₀', hux, hud, hmean⟩ := hun k₀ ⟨x₀, hx₀⟩
    have hPS : ∀ a, P₀ a = S *ᵥ P b a := fun a => funext fun j => (hP₀ a j).trans (hper a j).symm
    obtain ⟨t, ht, htS⟩ := _root_.GlobalTheory.FrameNorm.frBor_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ S (y b) ((U σ).un k₀ ⟨x₀, hx₀⟩) hp hP₀' hPS hsupp
      (hyP b (hs₂ hb)).1 hux (hyP b (hs₂ hb)).2 hud
    have hfn := hpin.1 σ hσ k₀ ⟨x₀, hx₀⟩ hunit t (y b) ht
    refine ⟨S, ⟨hS, hsupp, ?_⟩, fun j => ?_, ?_⟩
    · refine GlobalTheory.UnitDet.eq_of_im_hermForm_eq _ hp.2.2.2.1 _ _ ?_
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← GlobalTheory.UnitDet.hermForm_mulVec, hform, (hAH b hb).1]
    · rw [hfn, ← htS j]
      rfl
    · obtain ⟨hxx, -, pm, p1, p2, p3⟩ := ht
      have hbc : SecBC (RingHom.id ℂ) (toC (t none : CAt σ)) ((U σ).un k₀ ⟨x₀, hx₀⟩).x (y b).x
          ((U σ).un k₀ ⟨x₀, hx₀⟩).s (y b).s := ⟨pm, p1, p2.trans (by rw [GlobalTheory.Frames.SecCalc.spMap_id']; exact (Category.comp_id _).symm), p3⟩
      have h1 := _root_.GlobalTheory.FrameNorm.ahMean_eq_of_secBC E H Dw l Xo _ g _ F _ P₀ (P b) S _ _ _ _ _ 1 (μ b) hP₀' hp hPS hux hxx hbc (hmean hunit)
        (hAH b hb).2
      rw [hfn, h1, mul_one, Real.sqrt_sq (norm_nonneg _)]
      exact mul_one _
  choose! S hS hlie hgen using key
  refine ContinuousAt.continuousWithinAt (ContinuousOn.continuousAt (s := B₂) ?_ (hB₂.mem_nhds hb₂))
  cases i with
  | none => exact hμ.sqrt.congr hgen
  | some s =>
    obtain ⟨j, rfl⟩ := e.surjective s
    refine ((_root_.GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt g (E →+* ℂ) _ (fun j => (e j).1) (fun j => (e j).2) d B₂ S Hm (fun j j' h1 h2 => ?_) hd hHm hS
      j).mul continuousOn_const).congr fun b hb => hlie b hb j
    exact e.injective (Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormBddAboveISupEqCuspFormSupNorm
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.SupNorm

theorem bdd_and_iSup_eq {α β : Type} (g : α → ℝ) (h : β → ℝ) (C : ℝ) (hC : 0 ≤ C) (hh : ∀ b, 0 ≤ h b)
    (h1 : ∀ a, ∃ b, g a = C * h b) (h2 : ∀ b, ∃ a, g a = C * h b)
    (hfin : (⨆ b, ENNReal.ofReal (h b)) ≠ ⊤) :
    BddAbove (Set.range g) ∧ (⨆ a, g a) = C * (⨆ b, ENNReal.ofReal (h b)).toReal := by
  have hle : ∀ b, h b ≤ (⨆ b, ENNReal.ofReal (h b)).toReal := fun b =>
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 (le_iSup (fun b => ENNReal.ofReal (h b)) b)
  have hr : Set.range g = Set.range fun b => C * h b := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := h1 a
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, rfl⟩
      exact h2 b
  refine ⟨⟨C * (⨆ b, ENNReal.ofReal (h b)).toReal, ?_⟩, ?_⟩
  · rw [hr]
    rintro _ ⟨b, rfl⟩
    exact mul_le_mul_of_nonneg_left (hle b) hC
  · rw [ENNReal.toReal_iSup (fun b => ENNReal.ofReal_ne_top), Real.mul_iSup_of_nonneg hC]
    unfold iSup
    rw [hr]
    simp only [ENNReal.toReal_ofReal (hh _)]

theorem supBdd_and_supR_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ a n, Dom a n → ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, SupBdd Xo c fn a n f ∧ ∀ σ, supR Xo c fn σ a n f = Formalism.L2.PjFree.supC Xo c U xR (Formalism.L2.PjFree.goodOf c σ) a n f := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn a n hd f hf
  obtain ⟨-, htie, hconj⟩ := GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn
  have hs : f ∈ sec Xo c a n := Formalism.L2.PjFree.cusp_le_sec Xo c U a n hf
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  let N : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → ℝ := fun σ =>
    ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f
  have hgood : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ →
      BddAbove (Set.range (N σ)) ∧ (⨆ y, N σ y) = Formalism.L2.PjFree.supC Xo c U xR σ a n f := by
    intro σ hσ
    refine bdd_and_iSup_eq (N σ)
      (fun p : Formalism.L2.PjFree.FPt (U σ).X =>
        ((U σ).X p.1).pnorm (Formalism.L2.PjFree.laU (U σ) a n p.1) (Formalism.L2.PjFree.rdU (U σ) f p.1) p.2)
      (Formalism.L2.PjFree.lieFac Dw xR a) (Formalism.L2.PjFree.lieFac_pos Dw xR a).le
      (fun p => mul_nonneg (norm_nonneg _) (Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _)) (fun y => ?_) (fun p => ?_)
      (Formalism.L2.PjFree.supE_cusp_ne_top hσ hf)
    · obtain ⟨k, x, t, ht⟩ := (hU σ hσ).2.2.1 y
      exact ⟨⟨k, x⟩, htie σ hσ k x t y ht a n hd f hs⟩
    · exact ⟨(U σ).un p.1 p.2, htie σ hσ p.1 p.2 1 _
        ((GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).1 _) a n hd f hs⟩
  have hsub : ∀ σ τ : c.F →+* ℂ, τ = (starRingEnd ℂ).comp σ → Set.range (N σ) ⊆ Set.range (N τ) := by
    rintro σ τ rfl _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ (conjAlg σ) y
    exact ⟨z, hconj σ y z hz a n f hs⟩
  have hr : ∀ σ : c.F →+* ℂ, Set.range (N σ) = Set.range (N (Formalism.L2.PjFree.goodOf c σ)) := by
    intro σ
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · have e : Formalism.L2.PjFree.goodOf c σ = σ := if_pos hσ
      exact (hsub _ _ rfl).trans (hsub _ _ (by rw [e]; ext x; simp)) |>.antisymm
        ((hsub _ _ rfl).trans (hsub _ _ (by rw [e]; ext x; simp)))
    · have e : Formalism.L2.PjFree.goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
      exact (hsub _ _ e).antisymm (hsub _ _ (by rw [e]; ext x; simp))
  refine ⟨fun σ => ?_, fun σ => ?_⟩
  · show BddAbove (Set.range (N σ))
    rw [hr σ]
    exact (hgood _ (Formalism.L2.PjFree.goodEmb_goodOf c σ)).1
  · show sSup (Set.range (N σ)) = _
    rw [hr σ]
    exact (hgood _ (Formalism.L2.PjFree.goodEmb_goodOf c σ)).2

end GlobalTheory.FrameNorm.SupNorm
end

