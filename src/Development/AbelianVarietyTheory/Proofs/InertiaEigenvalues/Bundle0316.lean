module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEnds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import GroundTheory.PAdicHodge.AxLemma
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationAtRadiusConcaveContSlope
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

lemma one_lt_natCast_of_prime : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

lemma prime_rpow_neg_mem_Ico_inv_one {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hL := one_lt_natCast_of_prime (l := l)
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

lemma logb_gaussNormAcrisRadius_convex {x : Formalism.Per.Acris l} (hx : x ≠ 0) {r₁ r₂ t : ℝ} (h1 : 0 < r₂) (h12 : r₂ ≤ r₁)
    (h2 : r₁ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.logb l (gC l ((l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂))) x) ≤
      t * Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x) + (1 - t) * Real.logb l (gC l ((l : ℝ) ^ (-r₂)) x) := by
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  obtain ⟨a1, b1⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) (by linarith : 0 < r₁) h2
  obtain ⟨a2, b2⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) h1 (by linarith)
  have hm0 : 0 < t * r₁ + (1 - t) * r₂ := by nlinarith
  have hm1 : t * r₁ + (1 - t) * r₂ ≤ 1 := by nlinarith
  obtain ⟨a0, b0⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) hm0 hm1
  have hle : (l : ℝ) ^ (-r₁) ≤ (l : ℝ) ^ (-r₂) := Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  have key := _root_.GlobalTheory.PMon.Gauss.gC_logConvex l x _ _ t a1 hle b2 ht0 ht1
  have heq : ((l : ℝ) ^ (-r₁)) ^ t * ((l : ℝ) ^ (-r₂)) ^ (1 - t) = (l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂)) := by
    rw [← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    congr 1; ring
  rw [heq] at key
  have p1 := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l x hx _ a1 b1
  have p2 := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l x hx _ a2 b2
  have p0 := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l x hx _ a0 b0
  calc Real.logb l (gC l ((l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂))) x)
      ≤ Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x ^ t * gC l ((l : ℝ) ^ (-r₂)) x ^ (1 - t)) :=
        Real.logb_le_logb_of_le hL p0 key
    _ = t * Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x) + (1 - t) * Real.logb l (gC l ((l : ℝ) ^ (-r₂)) x) := by
        rw [Real.logb_mul (Real.rpow_pos_of_pos p1 _).ne' (Real.rpow_pos_of_pos p2 _).ne',
          Real.logb_rpow_eq_mul_logb_of_pos p1, Real.logb_rpow_eq_mul_logb_of_pos p2]

theorem vr_concaveOn_Ioc {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) := by
  refine ⟨convex_Ioc 0 1, ?_⟩
  intro r₁ hr₁ r₂ hr₂ a b ha hb hab
  simp only [vr, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  rcases le_total r₂ r₁ with h | h
  · have := logb_gaussNormAcrisRadius_convex hx hr₂.1 h hr₁.2 ha (by linarith)
    linarith
  · have := logb_gaussNormAcrisRadius_convex hx hr₁.1 h hr₂.2 (t := 1 - a) (by linarith) (by linarith)
    have e : (1 - a) * r₂ + (1 - (1 - a)) * r₁ = a * r₁ + (1 - a) * r₂ := by ring
    rw [e] at this
    linarith

theorem vr_continuousOn_Ioc {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) := by
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  have hmaps : Set.MapsTo (fun r : ℝ => (l : ℝ) ^ (-r)) (Set.Ioc 0 1) (Set.Ico (l : ℝ)⁻¹ 1) :=
    fun r hr => prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2
  have hc1 : Continuous (fun r : ℝ => (l : ℝ) ^ (-r)) :=
    Continuous.rpow continuous_const continuous_neg (fun _ => Or.inl hL0.ne')
  have hc2 : ContinuousOn (fun r : ℝ => gC l ((l : ℝ) ^ (-r)) x) (Set.Ioc 0 1) :=
    (_root_.GlobalTheory.PMon.Gauss.continuousOn_gC_target l x).comp hc1.continuousOn hmaps
  have hpos : ∀ r ∈ Set.Ioc (0 : ℝ) 1, gC l ((l : ℝ) ^ (-r)) x ≠ 0 := fun r hr =>
    (_root_.GlobalTheory.PMon.Gauss.gC_pos_target l x hx _ (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).1 (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).2).ne'
  simp only [vr, Real.logb]
  exact ((hc2.log hpos).div_const _).neg

theorem vr_right_affine {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧
      ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) := by
  intro r hr
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  obtain ⟨a, b⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) hr.1 hr.2.le
  have hlt : (l : ℝ)⁻¹ < (l : ℝ) ^ (-r) := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_lt_rpow_of_exponent_lt hL (by linarith [hr.2])
  obtain ⟨c, k, ρ₁, hc, hρ₁, hρ₁r, hmon⟩ := (_root_.GlobalTheory.PMon.Gauss.gC_monomial_near l x hx _ a b).2 hlt
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le (inv_pos.mpr hL0) hρ₁
  have hsr : r < -Real.logb l ρ₁ := by
    have := Real.logb_lt_logb hL hρ₁0 hρ₁r
    rw [Real.logb_rpow hL0 hL.ne'] at this
    linarith
  have hρs : ρ₁ = (l : ℝ) ^ (-(-Real.logb l ρ₁)) := by
    rw [neg_neg, Real.rpow_logb hL0 hL.ne' hρ₁0]
  have hlogl : Real.log l ≠ 0 := (Real.log_pos hL).ne'
  have formula : ∀ t, r ≤ t → t ≤ -Real.logb l ρ₁ → vr l t x = -Real.logb l c + k * t := by
    intro t ht1 ht2
    have hmem : (l : ℝ) ^ (-t) ∈ Set.Icc ρ₁ ((l : ℝ) ^ (-r)) := by
      constructor
      · rw [hρs]; exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
      · exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
    simp only [vr]
    rw [hmon _ hmem]
    simp only [Real.logb]
    rw [Real.log_mul hc.ne' (zpow_ne_zero _ (Real.rpow_pos_of_pos hL0 _).ne'), Real.log_zpow,
      Real.log_rpow hL0]
    field_simp
    ring
  refine ⟨k, min (-Real.logb l ρ₁ - r) (1 - r), lt_min (by linarith) (by linarith [hr.2]),
    by linarith [min_le_right (-Real.logb l ρ₁ - r) (1 - r)], ?_⟩
  intro t ht
  have hs1 : r + min (-Real.logb l ρ₁ - r) (1 - r) ≤ -Real.logb l ρ₁ := by
    linarith [min_le_left (-Real.logb l ρ₁ - r) (1 - r)]
  rw [formula t ht.1 (ht.2.trans hs1), formula r le_rfl hsr.le]
  ring

theorem vr_concave_cont_rightSlope : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 →
    ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) ∧ ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) ∧
      ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧
        ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) :=
  fun _ _ _ hx => ⟨vr_concaveOn_Ioc hx, vr_continuousOn_Ioc hx, vr_right_affine hx⟩

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersOfLargeScale
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HTW

theorem admissibleParameters_of_large_scale : ∀ eps A : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → AdmissibleParameterJ.AdmPar L ∧ EmbeddingTypeJumps.ParametersPolynomiallyBounded L := by
  intro eps A heps
  obtain ⟨x0, hx0⟩ := admissible_params_large eps A heps
  refine ⟨x0, fun D L P h1 h2 h3 => ?_⟩
  obtain ⟨⟨hw, hwb, hbb, hT, ht⟩, hS⟩ := hx0 D L P h1 h2 h3
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have htt : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨⟨by linarith, by linarith, fun tt => by linarith [hT tt], ht⟩, hS⟩

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientFiltrationEveryDeclarationStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientFiltration_every_declaration : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.ambFil (D := D) i r ρ π dc := by
  first | exact @GlobalTheory.Per.AmbFil.main | exact GlobalTheory.Per.AmbFil.main | (intros; apply GlobalTheory.Per.AmbFil.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaFiniteGaloisPadic
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem norm_natCast_self_Om (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem axConstant_le_sq (l : ℕ) [hl : Fact l.Prime] : GroundTheory.PAdicHodge.axConstant l ≤ (l : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hexp : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  unfold GroundTheory.PAdicHodge.axConstant
  calc (l : ℝ) ^ ((l : ℝ) / ((l : ℝ) - 1) ^ 2) ≤ (l : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    _ = (l : ℝ) ^ 2 := by norm_cast

theorem axIn_padic : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)], AxIn ℚ_[l] L l := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  intro J x hx
  have hO := _root_.GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt l L
  let φ : L →ₐ[ℚ_[l]] Om l := IsScalarTower.toAlgHom ℚ_[l] L (Om l)
  have hφ : ∀ y : L, φ y = algebraMap L (Om l) y := fun y => rfl
  let F : IntermediateField ℚ_[l] L := IntermediateField.fixedField J
  let E : IntermediateField ℚ_[l] (Om l) := F.map φ
  have hmove : ∀ g : Gal(Om l/E), ‖g (φ x) - φ x‖ ≤ 1 := by
    intro g
    let g' : Om l ≃ₐ[ℚ_[l]] Om l := g.restrictScalars ℚ_[l]
    let τ : L ≃ₐ[ℚ_[l]] L := AlgEquiv.restrictNormalHom L g'
    have hτ : ∀ y : L, φ (τ y) = g' (φ y) := fun y => AlgEquiv.restrictNormal_commutes g' L y
    have hτJ : τ ∈ J := by
      rw [← IntermediateField.fixingSubgroup_fixedField J]
      rintro ⟨y, hy⟩
      apply φ.toRingHom.injective
      change φ (τ y) = φ y
      rw [hτ]
      have hyE : φ y ∈ E := ⟨y, hy, rfl⟩
      exact g.commutes ⟨φ y, hyE⟩
    have h1 := (hO (τ x - x)).1.1 (hx τ hτJ)
    rw [map_sub, ← hφ, ← hφ, hτ] at h1
    exact h1
  obtain ⟨Y, hYE, hY⟩ := GroundTheory.PAdicHodge.ax_lemma (K := E) (φ x) hmove
  obtain ⟨y, hyF, rfl⟩ := hYE
  refine ⟨y, fun σ hσ => (IntermediateField.mem_fixedField_iff J y).1 hyF σ hσ, ?_⟩
  rw [(hO _).1, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, norm_natCast_self_Om, ← hφ, ← hφ]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hc := axConstant_le_sq l
  rw [mul_one] at hY
  calc ((l : ℝ)⁻¹) ^ 2 * ‖φ x - φ y‖ ≤ ((l : ℝ)⁻¹) ^ 2 * (l : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (hY.trans hc) (by positivity)
    _ = 1 := by rw [inv_pow, inv_mul_cancel₀ (by positivity)]

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ExtCrysCrit

theorem cocycle_of_ext {G LL V₀ V₁ : Type} [Group G] [TopologicalSpace G] [Field LL] [TopologicalSpace LL]
    [AddCommGroup V₀] [Module LL V₀] [TopologicalSpace V₀] [ContinuousAdd V₀] [ContinuousSMul LL V₀]
    [AddCommGroup V₁] [Module LL V₁] [TopologicalSpace V₁] [IsModuleTopology LL V₁]
    (ρ₀ : Representation LL G V₀) (ρ₁ : Representation LL G V₁) (ι : V₀ →ₗ[LL] V₁)
    (hι : Function.Injective ι) (hιρ : ∀ g y, ι (ρ₀ g y) = ρ₁ g (ι y)) (x : V₁)
    (hx : Continuous fun g => ρ₁ g x) (c : G → V₀) (hc : ∀ g, ι (c g) = ρ₁ g x - x) :
    Continuous c ∧ ∀ g h, c (g * h) = c g + ρ₀ g (c h) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.2 hι)
  have hrc : ∀ g, c g = r (ρ₁ g x) + (- r x) := by
    intro g
    rw [← sub_eq_add_neg, ← map_sub, ← hc, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  refine ⟨?_, fun g h => hι ?_⟩
  · have : c = fun g => r (ρ₁ g x) + (- r x) := funext hrc
    rw [this]
    exact ((IsModuleTopology.continuous_of_linearMap r).comp hx).add continuous_const
  · rw [map_add (f := _), hιρ, hc, hc, hc, map_mul, Module.End.mul_apply, map_sub]
    abel

theorem finrank_ext {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [FiniteDimensional LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (h1 : Module.finrank LL V₂ = 1) :
    Module.finrank LL V₁ = Module.finrank LL V₀ + 1 := by
  have hk' : LinearMap.ker π = LinearMap.range ι := by
    ext z; rw [LinearMap.mem_ker, LinearMap.mem_range]; exact hk z
  have h := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.2 hπ, finrank_top, hk', LinearMap.finrank_range_of_inj hι, h1] at h
  omega

theorem not_mem_range {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (x : V₁) (hx : π x ≠ 0) :
    x ∉ LinearMap.range ι := by
  rintro ⟨y, rfl⟩
  exact hx ((hk _).2 ⟨y, rfl⟩)

theorem blochKato_ext_all : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm15 D := by
  intro D l _ K LL
  intro T Tp To ι π hses htriv hdim hcrys x hxT hπx c hc
  have key := GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Tp.V Tp.ρ ι.f ι.equiv hses.1
    (finrank_ext ι.f π.f hses.1 hses.2.1 hses.2.2.2.1 hdim) hcrys x
    (not_mem_range ι.f π.f hses.2.2.2.1 x hπx) c hc
  obtain ⟨hcont, hcoc⟩ := cocycle_of_ext T.ρ Tp.ρ ι.f hses.1 ι.equiv x (Tp.cont x) c hc
  exact ⟨fun h => key.1 h.2, fun h => ⟨⟨hcont, hcoc⟩, key.2 h⟩⟩

end GlobalTheory.ExtCrysCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfQlDimensionFormula
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

theorem isModuleTopology_of_tower (R LL V : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field LL] [Algebra R LL] [TopologicalSpace LL] [IsTopologicalRing LL] [IsModuleTopology R LL]
    [AddCommGroup V] [Module LL V] [Module R V] [IsScalarTower R LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] : IsModuleTopology R V := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let e : V ≃ₗ[LL] (Fin (finrank LL V) → LL) := (Module.finBasis LL V).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let e' : (Fin (finrank LL V) → LL) ≃L[R] V :=
    { e.symm.restrictScalars R with continuous_toFun := h2, continuous_invFun := h1 }
  exact IsModuleTopology.iso e'

section Coeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

theorem actVB_resQ (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] P.R.B) :
    actVB (P.PD K) (resQ ρ) g x = actVB (P.PD K) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem galoisInvariants_restrictScalarsToQl : H0V (resQ ρ) = (H0V ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [H0V, Submodule.mem_iInf, sub_eq_zero]

theorem FilV_resQ (a : ℤ) :
    FilV (P.PD K) (LL := ℚ_[l]) (V := V) a = (FilV (P.PD K) (LL := LL) (V := V) a).restrictScalars ℚ_[l] := by
  have h : ∀ y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  ext x
  simp only [FilV, Submodule.restrictScalars_mem, LinearMap.mem_range, h]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [ContinuousConstSMul ℚ_[l] V]

theorem mem_finiteCocycles_restrictScalars_Ql (c : ↥(GK K) → V) : c ∈ finiteCocycles (P.PD K) (resQ ρ) ↔ c ∈ finiteCocycles (P.PD K) ρ := by
  show (c ∈ continuousCocycles (resQ ρ) ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) (resQ ρ) g x - x) ↔
    (c ∈ continuousCocycles ρ ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ g x - x)
  simp only [actVB_resQ]
  exact Iff.rfl

def finiteCocyclesResEquiv : ↥(finiteCocycles (P.PD K) (resQ ρ)) ≃ₗ[ℚ_[l]] ↥(finiteCocycles (P.PD K) ρ) where
  toFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mp x.2⟩
  invFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mpr x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def h1fEquiv : FiniteCohomology (P.PD K) (resQ ρ) ≃ₗ[ℚ_[l]] FiniteCohomology (P.PD K) ρ :=
  (Submodule.Quotient.equiv _ (((B1 ρ).comap (finiteCocycles (P.PD K) ρ).subtype).restrictScalars ℚ_[l]) (finiteCocyclesResEquiv P ρ) (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    exact Iff.rfl)).trans (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _)

end Coeff

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkADim_of_dimFormula : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l),
    GlobalTheory.Published.BlochKato.DimFormula (P.PD K) → Formalism.MainNotions.LocalSituation.bkADim (P.PD K) := by
  intro l _ P K hD LL _ _ _ O _ _ hO A hdR
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  obtain ⟨-, he⟩ := hD A.V (resQ (LL := LL) A.ρ) A.cont ((isDR_resQ_iff P A.ρ).mpr hdR)
  have hH1 : finrank ℚ_[l] (FiniteCohomology (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL (FiniteCohomology (P.PD K) A.ρ) := by
    rw [(h1fEquiv P A.ρ).finrank_eq, finrank_mul_finrank]
  have hH0 : finrank ℚ_[l] ↥(H0V (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(H0V A.ρ) := by
    rw [galoisInvariants_restrictScalarsToQl, finrank_mul_finrank]
    rfl
  have hdR' : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ) := by
    rw [DdR_resQ, finrank_mul_finrank]
    rfl
  have hF : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := A.V) 0) =
      finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := LL) (V := A.V) 0) := by
    rw [DdR_resQ, FilV_resQ P (LL := LL), ← Submodule.restrictScalars_inf, finrank_mul_finrank]
    rfl
  rw [hH1, hH0, hdR', hF] at he
  push_cast at he
  have hd : (finrank ℚ_[l] LL : ℤ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ_[l]) (M := LL)).ne'
  refine mul_left_cancel₀ hd ?_
  rw [he]
  ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMem
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_mul_le_jumpSum_of_mem_upper_not_mem : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)) (v : ℝ),
    lowerRamificationGroup F L 0 = ⊤ → ∀ σ ∈ upperRamificationGroup F L v, σ ∉ B →
      (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ B v h0 σ hσ hσB
  have hσ1 : σ ≠ 1 := fun h ↦ hσB (h ▸ B.one_mem)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top (K := F) (L := L) hσ1)
  have hm1 : 1 ≤ m := by
    have : (1 : ℕ∞) ≤ lowerIndex F L σ := one_le_lowerIndex_iff.mpr (h0 ▸ Subgroup.mem_top σ)
    rw [← hm] at this
    exact_mod_cast this
  have hv := (mem_upperRamificationGroup_iff_of_lowerIndex_eq hm.symm).mp hσ
  have hcast : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm1]; simp
  rw [hcast] at hv
  obtain ⟨hanti, hbot⟩ := _root_.GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot F L
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le (L ≃ₐ[F] L) (wild F L) ⊤ B hanti hbot
  have hjs := _root_.GlobalTheory.PMon.Ram.jumpSum_eq_sum_range (L ≃ₐ[F] L) (wild F L) ⊤ B n hanti hn
  have hphi := _root_.GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified F L h0 (m - 1)
  have hle : m - 1 ≤ n := by
    by_contra hlt
    push_neg at hlt
    have hmem : σ ∈ wild F L n := by
      rw [wild, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hm]
      exact_mod_cast (by omega : n + 1 + 1 ≤ m)
    have : ¬ (⊤ ⊓ wild F L n ≤ B) := fun h ↦ hσB (h ⟨Subgroup.mem_top σ, hmem⟩)
    exact lt_irrefl n ((hn n).mpr this)
  have hcard : (0 : ℝ) ≤ (Nat.card (L ≃ₐ[F] L) : ℝ) := Nat.cast_nonneg _
  calc (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L ((m - 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hv hcard
    _ = ((∑ t ∈ Finset.range (m - 1), Nat.card ↥(wild F L t) : ℕ) : ℝ) := hphi
    _ ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
        rw [hjs]
        simp only [top_inf_eq]
        exact_mod_cast Finset.sum_le_sum_of_subset ((Finset.range_subset_range.mpr hle))

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterModPrimePowKernelGeneratorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_mod_prime_pow_kernel_generator : ∀ (G : Type) [Group G] (p r : ℕ) (a : G → ℤ), p.Prime → (∀ σ τ, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ (J : Subgroup G) (_ : J.Normal) (σ₁ : G) (c : ℤ), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ ∧ ¬ (p : ℤ) ∣ c := by
  first | exact @GlobalTheory.PMon.Ram.character_kernel_generator | exact GlobalTheory.PMon.Ram.character_kernel_generator | (intros; apply GlobalTheory.PMon.Ram.character_kernel_generator <;> assumption)
end

