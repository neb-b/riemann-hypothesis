module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodinger
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0437

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AdelicIntertwinerEqScalar
section
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
noncomputable section
namespace GlobalTheory.AdelicSchur
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.AdelicSchur
namespace GlobalTheory.AdelicSchur
theorem adelic_schur_lemma : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  intro _ F _ _ κ _ ψ hψ M hpres hcomm hiso
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  let μ : Measure (κ → AF F) := Measure.addHaar
  haveI hμH : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  have hL2 : ∀ φ ∈ schA F κ, MemLp φ 2 μ := fun φ hφ =>
    GlobalTheory.WeilM.schA_memLp_two F κ μ hμH φ hφ
  have hint : ∀ φ ∈ schA F κ, Integrable (fun x => ‖φ x‖ ^ 2) μ := fun φ hφ =>
    (hL2 φ hφ).integrable_norm_pow two_ne_zero
  have hnorm : ∀ φ ∈ schA F κ, ∫ x, ‖M φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := by
    intro φ hφ
    have h := hiso μ hμH φ hφ
    have e : ∀ g ∈ schA F κ, ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := fun g hg => by
      rw [ofReal_integral_eq_lintegral_ofReal (hint g hg) (Filter.Eventually.of_forall fun x => by positivity)]
      congr 1
      funext x
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [e _ (hpres φ hφ), e φ hφ] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity)).1 h
  have hψn : ∀ a, ‖ψ a‖ = 1 := GlobalTheory.HeisLineTheta.norm_psi hψ
  have hcy : ∀ y : κ → AF F, Continuous fun x : κ → AF F => ψ (x ⬝ᵥ y) := fun y =>
    hψ.1.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)
  have hschr0 : ∀ (y : κ → AF F) (f : (κ → AF F) → ℂ) x, schr ψ (0, y) f x = ψ (x ⬝ᵥ y) * f x := by
    intro y f x
    simp [schr]
  have hdiag : ∀ φ ∈ schA F κ, ∀ x, ‖M φ x‖ = ‖φ x‖ := by
    intro φ hφ
    have hMφ := hpres φ hφ
    set D : (κ → AF F) → ℝ := fun x => ‖M φ x‖ ^ 2 - ‖φ x‖ ^ 2 with hD
    have hDi : Integrable D μ := (hint _ hMφ).sub (hint φ hφ)
    have hDc : Continuous D :=
      ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hMφ).norm.pow 2).sub
        ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hφ).norm.pow 2)
    have hbi : ∀ (y : κ → AF F) (c : ℂ) (f : (κ → AF F) → ℂ), f ∈ schA F κ →
        Integrable (fun x => (c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2) μ := fun y c f hf =>
      (hint f hf).bdd_mul (Complex.continuous_re.comp (continuous_const.mul (hcy y))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, hψn, mul_one])
    have hre : ∀ (y : κ → AF F) (c : ℂ), ∫ x, (c * ψ (x ⬝ᵥ y)).re * D x ∂μ = 0 := by
      intro y c
      have hg : φ + c • schr ψ (0, y) φ ∈ schA F κ :=
        (schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ))
      have hMg : M (φ + c • schr ψ (0, y) φ) = M φ + c • schr ψ (0, y) (M φ) := by
        rw [map_add (f := _), map_smul, hcomm _ φ hφ]
      have h1 := hnorm _ hg
      rw [hMg] at h1
      have hpt : ∀ f : (κ → AF F) → ℂ, (fun x => ‖(f + c • schr ψ (0, y) f) x‖ ^ 2) =
          fun x => (1 + ‖c‖ ^ 2) * ‖f x‖ ^ 2 + 2 * ((c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2) := by
        intro f
        funext x
        rw [Pi.add_apply, Pi.smul_apply, hschr0, smul_eq_mul,
          show f x + c * (ψ (x ⬝ᵥ y) * f x) = (1 + c * ψ (x ⬝ᵥ y)) * f x by ring, norm_mul, mul_pow,
          norm_one_add_sq c _ (hψn _)]
        ring
      rw [hpt, hpt, integral_add ((hint _ hMφ).const_mul _) ((hbi y c _ hMφ).const_mul _),
        integral_add ((hint _ hφ).const_mul _) ((hbi y c _ hφ).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hnorm φ hφ] at h1
      have h2 : ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 ∂μ = ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2 ∂μ := by
        linarith
      have e : (fun x => (c * ψ (x ⬝ᵥ y)).re * D x) =
          fun x => (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 - (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2 := by
        funext x
        simp only [hD]
        ring
      rw [e, integral_sub (hbi y c _ hMφ) (hbi y c _ hφ), h2, sub_self]
    have hF : ∀ y : κ → AF F, ∫ x, ψ (x ⬝ᵥ y) * (D x : ℂ) ∂μ = 0 := by
      intro y
      have hI : Integrable (fun x => ψ (x ⬝ᵥ y) * (D x : ℂ)) μ :=
        hDi.ofReal.bdd_mul (hcy y).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hψn _).le)
      apply Complex.ext
      · rw [Complex.zero_re, ← RCLike.re_to_complex, ← integral_re hI]
        have e : (fun x => RCLike.re (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((1 : ℂ) * ψ (x ⬝ᵥ y)).re * D x := by
          funext x
          simp [Complex.mul_re]
        rw [e]
        exact hre y 1
      · rw [Complex.zero_im, ← RCLike.im_to_complex, ← integral_im hI]
        have e : (fun x => RCLike.im (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((-Complex.I) * ψ (x ⬝ᵥ y)).re * D x := by
          funext x
          simp [Complex.mul_re, Complex.mul_im]
        rw [e]
        exact hre y (-Complex.I)
    have hD0 := GlobalTheory.CharFourierInj.real_eq_zero (G := κ → AF F) (A := κ → AF F) (fun y x => ψ (x ⬝ᵥ y)) hcy
      (fun y x x' => by simp only [add_dotProduct, AddChar.map_add_eq_mul])
      (fun y y' x => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
      (fun x => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
      (fun y x => hψn _) (fun x hx => GlobalTheory.AdelicSchur.sep ψ hψ x hx) μ D hDc hDi hF
    intro x
    have := congrFun hD0 x
    simp only [hD, Pi.zero_apply, sub_eq_zero] at this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have htwo : ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, ∀ x a,
      star (M φ x) * M φ' (x + a) = star (φ x) * φ' (x + a) := by
    intro φ hφ φ' hφ' x a
    apply conj_mul_eq
    intro c
    have hg : φ + c • schr ψ (a, 0) φ' ∈ schA F κ :=
      (schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ' hφ'))
    have h1 := hdiag _ hg x
    rw [map_add (f := _), map_smul, hcomm _ φ' hφ'] at h1
    simpa [schr] using h1
  by_cases h0 : ∃ φ₀ ∈ schA F κ, ∃ x₀, φ₀ x₀ ≠ 0
  · obtain ⟨φ₀, hφ₀, x₀, hx₀⟩ := h0
    have hn1 : ‖M φ₀ x₀‖ = ‖φ₀ x₀‖ := hdiag φ₀ hφ₀ x₀
    have hs : star (M φ₀ x₀) ≠ 0 := by
      rw [star_ne_zero, ← norm_ne_zero_iff, hn1, norm_ne_zero_iff]
      exact hx₀
    refine ⟨star (φ₀ x₀) / star (M φ₀ x₀), fun φ hφ => funext fun x => ?_⟩
    have h2 := htwo φ₀ hφ₀ φ hφ x₀ (x - x₀)
    rw [add_sub_cancel] at h2
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs]
    exact (mul_comm _ _).trans h2
  · push_neg at h0
    refine ⟨0, fun φ hφ => ?_⟩
    have : φ = 0 := funext fun x => h0 φ hφ x
    rw [this, map_zero, smul_zero]
end GlobalTheory.AdelicSchur
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_intertwiner_eq_scalar : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  first | exact @_root_.GlobalTheory.AdelicSchur.adelic_schur_lemma | exact _root_.GlobalTheory.AdelicSchur.adelic_schur_lemma | (intros; apply _root_.GlobalTheory.AdelicSchur.adelic_schur_lemma <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AverageIsTypeAtOtherPlaceTwist
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
namespace GlobalTheory.AvgTypeOther
section SeriesClosure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.REAL MeasureTheory Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open GlobalTheory.SeriesToClosure
open scoped TensorProduct InnerProductSpace
end SeriesClosure
section ClosureSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
open GlobalTheory.ClosureSeries
end ClosureSeries
open Formalism.MainNotions.S Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum in
theorem isTypeAt_average_other_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ' (N.S τ') ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  intro D θ hθ hPr N τ τ' hne ψ hψ hty e he
  have hec : Continuous e := by
    obtain ⟨F, -, h1, h2, -⟩ := he
    exact h2 _ h1
  have hHC := hPr.harishChandraModules
  have hCW := hPr.casselmanWallach
  have hUn := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique
  have hT := hasTypeAt_of_isTypeAt θ N.V τ' (N.S τ') ψ hHC hθ hψ hty
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hU : ∀ k, (N.M.fr τ)⁻¹ * Formalism.REAL.toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => GlobalTheory.LowTypeDetermined.conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have hA := GlobalTheory.AvgOtherPlace.hasTypeAt_avgF (Formalism.REAL.muK (N.M.ε τ)) hθ hne hκ hU hec hψ.cont hT
  have hAs := GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (Formalism.REAL.KG (N.M.ε τ)) (Formalism.REAL.muK (N.M.ε τ)) _
    hκ hU e hec ψ hψ
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP', hJ', -⟩ := hty
  exact isTypeAt_of_hasTypeAt_model θ N.V τ' (N.S τ') _ hUn hHC hCW hθ H σ lam ε P hE
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS hE.1 hD) hD hP' hJ' hAs hA
end GlobalTheory.AvgTypeOther
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_isTypeAt_other_place_twist : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ' (N.S τ') ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @_root_.GlobalTheory.AvgTypeOther.isTypeAt_average_other_place | exact _root_.GlobalTheory.AvgTypeOther.isTypeAt_average_other_place | (intros; apply _root_.GlobalTheory.AvgTypeOther.isTypeAt_average_other_place <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AverageIsTypeAtSamePlaceTwist
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
namespace GlobalTheory.AvgSamePlace
theorem isTypeAt_average_same_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ (N.S τ) ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  intro D θ hθ hPr N τ ψ _ hT e he
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP, hJ, hx⟩ := hT
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE (N.M.enum τ)
  haveI : CompleteSpace H := hD.1
  have hfr : IsUnit (N.M.fr τ) := N.M.fr_unit τ
  have hfrJ := N.M.fr_gram τ
  have dfr := (isUnit_iff_isUnit_det _).1 hfr
  have dP := (isUnit_iff_isUnit_det _).1 hP
  have fr1 : (N.M.fr τ)⁻¹ * N.M.fr τ = 1 := Matrix.nonsing_inv_mul _ dfr
  have fr2 : N.M.fr τ * (N.M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ dfr
  have P1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ dP
  have P2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ dP
  set fr := N.M.fr τ with hfrdef
  set h := P * fr⁻¹ with hh
  set hi := fr * P⁻¹ with hhi
  have hih : hi * h = 1 := by
    calc hi * h = fr * (P⁻¹ * P) * fr⁻¹ := by simp only [hh, hhi, Matrix.mul_assoc]
      _ = 1 := by rw [P1, Matrix.mul_one, fr2]
  have hU : h ∈ UJset (N.M.ε τ) := by
    show hᴴ * Jm (N.M.ε τ) * h = Jm (N.M.ε τ)
    calc hᴴ * Jm (N.M.ε τ) * h = (fr⁻¹)ᴴ * (Pᴴ * Jm (N.M.ε τ) * P) * fr⁻¹ := by
          simp only [hh, conjTranspose_mul, Matrix.mul_assoc]
      _ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          rw [hJ, ← hfrJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [fr2]; simp
  have hiU : hi ∈ UJset (N.M.ε τ) := by
    show hiᴴ * Jm (N.M.ε τ) * hi = Jm (N.M.ε τ)
    calc hiᴴ * Jm (N.M.ε τ) * hi = (P⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * P⁻¹ := by
          simp only [hhi, conjTranspose_mul, Matrix.mul_assoc]
      _ = (P * P⁻¹)ᴴ * Jm (N.M.ε τ) * (P * P⁻¹) := by
          rw [hfrJ, ← hJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [P2]; simp
  set σ₂ : Mx N.V.rank → (H →L[ℂ] H) := fun y => σ (h * y * hi) with hσ₂def
  have hD₂ : IsDS (N.M.ε τ) (N.M.lam τ) σ₂ := GlobalTheory.CayleyChoice.isDS_conj hD hiU hU hih
  have hσ₂ : Std (N.M.ε τ) σ₂ := std_of_isDS hPr.harishChandraModules hD₂
  have e1 : ∀ g, σ (P * g * P⁻¹) = σ₂ (fr * g * fr⁻¹) := by
    intro g
    show σ (P * g * P⁻¹) = σ (h * (fr * g * fr⁻¹) * hi)
    congr 1
    calc P * g * P⁻¹ = P * (fr⁻¹ * fr) * g * (fr⁻¹ * fr) * P⁻¹ := by rw [fr1]; simp
      _ = _ := by simp only [hh, hhi, Matrix.mul_assoc]
  simp only [e1] at hx
  refine ⟨H, i1, i2, σ₂, N.M.lam τ, N.M.ε τ, fr, N.M.enum τ, hD₂, hfr, hfrJ, fun x => ?_⟩
  have hx' : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ₂ (GlobalTheory.SeriesToClosure.res θ N.V τ fr ψ x) :=
    hasTypeAll_transport _ H H _ σ₂ (gramAt D N.V τ) (Jm (N.M.ε τ)) fr (GlobalTheory.LowTypeDetermined.isUnit_gram hfr hfrJ)
      hfr hfrJ (LinearIsometryEquiv.refl ℂ H) (fun _ _ _ => rfl) (fun g => ψ (x * atTau θ N.V τ g))
      (hasTypeAll_iff.2 (hx x))
  obtain ⟨S, hW, hc, v, ℓ, C, hex⟩ := hx'
  have hmv := GlobalTheory.SeriesToClosure.moves_avg hθ hfr hfrJ hσ₂ he ψ x S v ℓ C hW hc hex
  have hy : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ₂
      (GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) fr e ψ) x) :=
    ⟨S, hW, hc, _, ℓ, C, hmv⟩
  have hJ' : (fr⁻¹)ᴴ * gramAt D N.V τ * fr⁻¹ = Jm (N.M.ε τ) := by
    rw [← hfrJ]
    calc (fr⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * fr⁻¹ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [fr2]; simp
  have hfri : IsUnit fr⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hfr
  have hii : fr⁻¹⁻¹ = fr := Matrix.nonsing_inv_nonsing_inv _ dfr
  have hb := hasTypeAll_transport _ H H σ₂ (fun g => σ₂ (fr * g * fr⁻¹)) (Jm (N.M.ε τ)) (gramAt D N.V τ) fr⁻¹
    (isUnit_Jm _) hfri hJ' (LinearIsometryEquiv.refl ℂ H) (fun g _ w => by
      show σ₂ g w = σ₂ (fr * (fr⁻¹ * g * fr⁻¹⁻¹) * fr⁻¹) w
      rw [hii]
      congr 2
      calc g = (fr * fr⁻¹) * g * (fr * fr⁻¹) := by rw [fr2]; simp
        _ = _ := by simp only [Matrix.mul_assoc]) _ hy
  have ef : (fun y => GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) fr e ψ) x
      (fr⁻¹⁻¹ * y * fr⁻¹)) = fun g => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) fr e ψ (x * atTau θ N.V τ g) := by
    funext y
    simp only [GlobalTheory.SeriesToClosure.res]
    congr 3
    rw [hii]
    calc fr⁻¹ * (fr * y * fr⁻¹) * fr = (fr⁻¹ * fr) * y * (fr⁻¹ * fr) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [fr1]; simp
  rw [ef] at hb
  exact hasTypeAll_iff.1 hb
end GlobalTheory.AvgSamePlace
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_isTypeAt_same_place_twist : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ (N.S τ) ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @_root_.GlobalTheory.AvgSamePlace.isTypeAt_average_same_place | exact _root_.GlobalTheory.AvgSamePlace.isTypeAt_average_same_place | (intros; apply _root_.GlobalTheory.AvgSamePlace.isTypeAt_average_same_place <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFiniteLevelFixed
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
noncomputable section
namespace GlobalTheory.BotFinLevel
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter GlobalTheory.RowVacScalar Formalism.L2.DIV
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (frG intM)
variable {D : D7}
end GlobalTheory.BotFinLevel
theorem GlobalTheory.BotFinLevel.bottom_finite_level_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T), ∀ k ∈ Lev.levA A' (Formalism.L2.DIV.St X.rA'.β), X.ω' s (k, 1) (X.f' s) = X.f' s := by
  intro _ _ _ _ _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W _ i j A A' WW X hX s k hk
  exact GlobalTheory.BotFinLevel.fix_of_unram hX.is s (fun v hv => GlobalTheory.BotFinLevel.unram_off G hμ s i j _ hv) hk
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_layer_finite_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T), ∀ k ∈ Lev.levA A' (Formalism.L2.DIV.St X.rA'.β), X.ω' s (k, 1) (X.f' s) = X.f' s := by
  first | exact @_root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed | exact _root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed | (intros; apply _root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnConvolutionIntegrableOnSlice
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ColConv
theorem columnConvolution_integrableOn_slice : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t j hj Φ hΦ φ hφ h
  obtain ⟨hν, h𝓕⟩ := measX_haar_fd hG j hj.le
  exact thetaKO_mul_cusp_integrableOn_fst hPr.cuspRapidDecay (hG.arrows.col t j hj).weil hR.inf hν h𝓕 hΦ hφ.1 hφ.2.1 h
end GlobalTheory.ColConv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnConvolution_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) := by
  first | exact @_root_.GlobalTheory.ColConv.columnConvolution_integrableOn_slice | exact _root_.GlobalTheory.ColConv.columnConvolution_integrableOn_slice | (intros; apply _root_.GlobalTheory.ColConv.columnConvolution_integrableOn_slice <;> assumption)
end
end

