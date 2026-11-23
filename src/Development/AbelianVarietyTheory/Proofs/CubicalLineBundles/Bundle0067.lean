module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormValueLeSupNormAtOrthonormalFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.OrthoBound

theorem norm_diag_of_triangular {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ) (κ : ℝ) (hκ : 0 < κ)
    (hY : ∀ i j, j < i → Y i j = 0) (h : Y.conjTranspose * ((κ : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) * Y = 1)
    (i : Fin m) : ‖Y i i‖ = (Real.sqrt κ)⁻¹ := by
  have h1 : Y.conjTranspose * ((κ : ℂ) • Y) = 1 := by
    rw [← h]; simp
  have hM : ((κ : ℂ) • Y).BlockTriangular id := by
    intro a b hab
    simp [hY a b hab]
  letI : Invertible ((κ : ℂ) • Y) := invertibleOfLeftInverse _ _ h1
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hM
  rw [Matrix.inv_eq_left_inv h1] at hinv
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at h2
  · have h3 : κ * ‖Y i i‖ ^ 2 = 1 := by
      have h4 := congrArg (fun z : ℂ => ‖z‖) h2
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_star, norm_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ] at h4
      linear_combination h4
    rw [← Real.sqrt_inv]
    symm
    rw [Real.sqrt_eq_iff_mul_self_eq (inv_nonneg.2 hκ.le) (norm_nonneg _)]
    field_simp
    linear_combination -h3
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · rw [hinv (show id j < id i from hlt), zero_mul]
    · simp [hY j i hgt]
  · simp

theorem cabs_evR_le_supC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, ∀ σ, GoodEmb c σ → ∀ (y : FrPt Xo c (CAt σ)) (N : ℝ), IsMetric y N (fun _ => 1) → cabs (evR Xo c F y) ≤ Real.sqrt N ^ n * supC Xo c U ξ σ a n F := by
  intro E _ _ _ H Dw l Xo c r U ξ hU hξ hpq a n hd F hF σ hσ y N hN
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  obtain ⟨k, x, t, hx, ht⟩ := _root_.GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ r (U σ) (hU σ hσ) y
  obtain ⟨g, hg0, hgd, hchg⟩ :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) ((U σ).un k x) y y).1 t).1 ht
  have hξ0 : 0 < ξ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hξ σ hσ k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 ((U σ).X k).ξ0_ne)
  have hκ : 0 < 2 * Real.pi * ξ := by positivity
  have hm0 := _root_.GlobalTheory.OrthoMetric.isMetric_of_isOrtho E H Dw l Xo c σ r (U σ) ξ hσ (hU σ hσ) hpq k x (hξ σ hσ k) hx
  have hm1 := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c σ ((U σ).un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨hNN, hG⟩ := _root_.GlobalTheory.LamT.MetUniq.isMetric_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hnone : cabs (t none : CAt σ) = Real.sqrt N := by
    rw [hNN, _root_.mul_one, Real.sqrt_sq (norm_nonneg _)]; rfl
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ),
      cabs (t (some p) : CAt σ) = (Real.sqrt (2 * Real.pi * ξ))⁻¹ := by
    rintro ⟨τ, i⟩
    rw [← hgd τ i]
    exact norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _ hκ
      (fun i j hij => hg0 τ j i hij) (congrFun hG τ).symm i
  have hev := hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n F (cusp_le_sec Xo c U a n hF) t _ _ ht
  have hlie : ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (2 * Real.pi * ξ))⁻¹ ^ a (p.1, p.2) =
      lieFac Dw ξ a := by
    have hs : (Real.sqrt (2 * Real.pi * ξ))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hκ, ← Real.exp_neg]
      congr 1; ring
    simp only [hs, ← Real.exp_nat_mul]
    rw [← Real.exp_sum, lieFac, ← Finset.sum_mul]
    congr 1
    rw [Fintype.sum_sigma]
    ring
  have hw : cabs (wchar (ex Dw a n) t) = Real.sqrt N ^ n * lieFac Dw ξ a := by
    rw [GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, hnone, ← hlie]
    congr 1
    exact Finset.prod_congr rfl fun p _ => by rw [hsome p]; rfl
  have hrd : ‖rdU (U σ) F k x.1‖ = cabs (evR Xo c F ((U σ).un k x)) := by
    have e : rdU (U σ) F k x.1 = toC (evR Xo c F ((U σ).un k x)) := dif_pos x.2
    rw [e]; rfl
  have hle := Formalism.L2.Pj.abelian₂.pnorm_le_supN (U σ).X (laU (U σ) a n) (rdU (U σ) F) (supE_cusp_ne_top hσ hF) k x.1 x.2
  rw [PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ hx), hrd] at hle
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw, supC, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (lieFac_pos _ _ _).le)
    (pow_nonneg (Real.sqrt_nonneg _) _)

end GlobalTheory.LamT.OrthoBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointAtCmBasisFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem exists_good_cmPt_at_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), IsUnf U → 0 < r → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (Xx : FD.DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → ∀ (La : ℝ) (lam : Fin r → Fin r → E), FD.LamBasis Xx La (hX ▸ x₀.1) lam → ∃ (z : CMPt Xo c) (σ₁ : z.K →ₐ[c.F] CAt c.F.val.toRingHom), z.Good (Module.finrank ℚ E / 2) La ∧ spMap σ₁.toRingHom ≫ z.y.x = (U.un k x₀).x := by
  intro E _ _ _ H Dw l Xo c _ hstar r U hU hr k x₀ Xx hX 𝔄 h𝔄 hΛ La lam hlam
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x₀
  obtain ⟨Z, hZ⟩ := _root_.GlobalTheory.LamT.CMBasis.exists_cmLat_unfAt E H Dw l Xo c r U hU hr k x₀ W Xx hX 𝔄 h𝔄 hΛ La lam hlam
  have hfd : FiniteDimensional ℚ c.F := inferInstance
  obtain ⟨K₁, nf, hk, ρ, X, y, t₀, m, m', -, -, -, -, -, hle, hρ, hhh, hy, hpt, -⟩ :=
    GlobalTheory.CM.cmExists_holds E H Dw l Xo W.g _ W.F (W.ik k) W.Pm W.per Z c.F hfd
  letI : Algebra c.F K₁ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  obtain ⟨Φ⟩ := GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo K₁ y (by have := hU.1; omega)
  obtain ⟨n, -⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ Xo.univ.t t₀ Φ.T.t y y (𝟙 _) m Φ.m
    (Category.id_comp _).symm).1
  obtain ⟨mB⟩ : Nonempty (SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K₁) K₁))) := by
    obtain ⟨mm, -⟩ := sabComp pullCubComp E H _ _ _ X.B.t t₀ Φ.T.t _ _ m' n
    rw [Category.id_comp] at mm
    exact ⟨mm⟩
  let σ₁ : K₁ →ₐ[c.F] CAt c.F.val.toRingHom :=
    { (algebraMap K₁ ℂ : K₁ →+* ℂ) with commutes' := fun _ => rfl }
  obtain ⟨z, σ', hz, he⟩ := _root_.GlobalTheory.LamT.exists_cmPt_good_of_cmObj E H Dw l Xo c hstar K₁ ρ (algebraMap K₁ ℂ) X La y Φ mB
    (fun τ => by
      show τ (H.rt : E) = H.rt0 ↔ _
      rw [← hρ, Subtype.ext_iff]
      exact Iff.rfl)
    (fun j τ => by rw [hhh]; exact hZ j τ) hy _ σ₁
  exact ⟨z, σ', hz, he.trans (hpt.trans W.pt.symm)⟩

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorAssociatedLocalGeneratorCMLineStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGenerator_associated_localGenerator_CM_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → SecInt T M.m1 M.m2 y'.s → ∀ ca : z.K, IsLocGen p ca z.Tl.I → ∃ u : T.Vˣ, a = iK ca * algebraMap T.V T.Fr u := by
  first | exact @GlobalTheory.LamT.LocGen.integral_generator_unit | exact GlobalTheory.LamT.LocGen.integral_generator_unit | (intros; apply GlobalTheory.LamT.LocGen.integral_generator_unit <;> assumption)
end

