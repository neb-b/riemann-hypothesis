module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaSumSiegelSetLeTorusPower
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusBound

theorem absTheta_le_torus : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ Q : Set (GA D V), IsCompact Q → ∀ Φ : schwartzA θ V.rank n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ y ∈ Q, GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n r X Y hXY c hc Q hQ Φ
  have hSB := _root_.GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨-, K, hK, hmaj⟩ := _root_.GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ V.rank n Φ.1 hSB
  obtain ⟨K', hK', hmul⟩ := _root_.GlobalTheory.MajMul.maj_mul_le D θ hθ V n Q hQ K hK
  obtain ⟨N, C₁, hC₁, hframe⟩ := _root_.GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le D θ hθ V n r X Y hXY c hc K' hK'
  obtain ⟨C₀, hC₀⟩ := hmaj N
  obtain ⟨C₂, hC₂, hmul'⟩ := hmul N
  set A : ℝ := max C₀ 0 * C₂ with hA
  have hA0 : 0 ≤ A := mul_nonneg (le_max_right _ _) hC₂
  refine ⟨A * C₁, mul_nonneg hA0 hC₁, ?_⟩
  intro t ht a ha y hy
  have hpt : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      GlobalTheory.SiegelFormula.invPt V (a * y) ξ
        = (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) (GlobalTheory.SiegelFormula.invPt V a ξ) : Mx D V.rank n) := by
    intro ξ
    have h2 : Formalism.L2.Theta.mt V (a * y)⁻¹ = Formalism.L2.Theta.mt V y⁻¹ * Formalism.L2.Theta.mt V a⁻¹ := by
      rw [mul_inv_rev]; rfl
    simp only [GlobalTheory.SiegelFormula.invPt, h2, Matrix.mul_assoc]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ
        ≤ ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := by
    intro ξ
    rw [← ENNReal.ofReal_mul hA0, ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [hpt ξ]
    set x := GlobalTheory.SiegelFormula.invPt V a ξ
    have h1 := hC₀ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    have h2 := hmul' y hy x
    have hm0 := GlobalTheory.Unf.maj_nonneg θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    calc ‖Φ.1 (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)‖
        ≤ C₀ * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := h1
      _ ≤ max C₀ 0 * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
      _ ≤ max C₀ 0 * (C₂ * GlobalTheory.Unf.maj θ K' N x) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = A * GlobalTheory.Unf.maj θ K' N x := by rw [hA, mul_assoc]
  calc GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y)
      = ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ := rfl
    _ ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal A * ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) :=
        by gcongr; exact hframe t ht a ha
    _ = ENNReal.ofReal (A * C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [← ENNReal.ofReal_mul hA0]; congr 1; ring

end GlobalTheory.TorusBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharDotMulMemAdelicSchwartzSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CharMulSchA

theorem charMul_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ b : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    (fun x => ψ (x ⬝ᵥ b) * Φ x) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ ψ hψ b Φ hΦ
  have h := GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ (0, b) Φ hΦ
  convert h using 1
  funext x
  simp [GlobalTheory.WeilM.schr]

end GlobalTheory.CharMulSchA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchroedingerSchurCommutingOperatorScalar
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.AdelicSchur

open GlobalTheory.AdelicSchur

theorem schur : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  intro F _ _ κ _ ψ hψ M hpres hcomm hiso
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

end GlobalTheory.HoweD.AdelicSchur
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensorsStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_finite_pure_tensors : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (Ψ : (κ → AF F) → ℂ), Ψ ∈ schA F κ →
    ∃ (T : Finset (Pl (F := F))) (m : ℕ) (f : Fin m → SInf F κ) (φ : Fin m → ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
      (∀ i v, φ i v ∈ SB (κ → Fv F v)) ∧
      (∀ i v, v ∉ T → φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) ∧
      Ψ = ∑ i, pure (f i) (φ i) := by
  first | exact @GlobalTheory.SchADecomp.exists_sum_pure | exact GlobalTheory.SchADecomp.exists_sum_pure | (intros; apply GlobalTheory.SchADecomp.exists_sum_pure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTrace_supportedAtSplitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z = GlobalTheory.LatVac.liftV v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ z + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) z) := by
  first | exact @GlobalTheory.SplitAdeleTrace.trace_at_split | exact GlobalTheory.SplitAdeleTrace.trace_at_split | (intros; apply GlobalTheory.SplitAdeleTrace.trace_at_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormNormEqAtConjugateEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.ConjNorm

open GlobalTheory.ConjInner

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)


set_option maxHeartbeats 1000000 in
theorem inner_reading_conj_at (he : R.models_HW) (fw : FWTie T R κ v₀) (hE : fw.Evaluates) (hT : BarTie fw) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i)
    (hB : JEvBarAt T R κ i σ hV) :
    ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
      starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ := by
  have hg : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have h1 := (hT i σ hσ hV).1 hB
  obtain ⟨v, hv, h1⟩ := h1
  have h2 := hE i ((starRingEnd ℂ).comp σ) hg hV
  have h3 : ∀ f g, evAt R i σ v (fw.jK i σ f) g =
      starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) (fw.jK i ((starRingEnd ℂ).comp σ) f) g) := fun f g =>
    (congrFun (h1 f) g).trans (congrArg (starRingEnd ℂ) (congrFun (h2 f) g).symm)
  have h4 : ∀ f f', ⟪fw.jK i σ f, fw.jK i σ f'⟫_ℂ =
      starRingEnd ℂ ⟪fw.jK i ((starRingEnd ℂ).comp σ) f, fw.jK i ((starRingEnd ℂ).comp σ) f'⟫_ℂ := fun f f' =>
    inner_conj_of_values R he i σ hv (fun τ => ((fw.hv₀ i _).1 τ).1) (h3 f) (h3 f')
  have h5 := fw.ks i
  obtain ⟨n, b, hb, -, -, -, h5⟩ := h5
  refine inner_conj_of_span σ _ _ _ h5 ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  have e : ∀ k, ∃ f, ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = b k := fun k =>
    ⟨(fw.e i).symm ⟨b k, hb k⟩, congrArg Subtype.val ((fw.e i).apply_symm_apply _)⟩
  have e1 := e k
  have e2 := e l
  obtain ⟨f, e1⟩ := e1
  obtain ⟨f', e2⟩ := e2
  rw [← e1, ← e2]
  exact h4 f f'

theorem norm_eq_of_inner_conj {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] {x : H} {y : H'} (h : ⟪x, x⟫_ℂ = starRingEnd ℂ ⟪y, y⟫_ℂ) : ‖y‖ = ‖x‖ := by
  rw [inner_conj_symm] at h
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h]


set_option maxHeartbeats 1000000 in
theorem norm_conj_of_not_good (he : R.models_HW) (fw : FWTie T R κ v₀) (hE : fw.Evaluates) (hT : BarTie fw) (hu : R.LUnif)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (x : Fin (R.nW i) → D.what₂.LL) :
    ‖(R.FW i).j ((starRingEnd ℂ).comp σ) x‖ = ‖(R.FW i).j σ x‖ := by
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := fw.laws.spaceW _ (inR i) _ (good_resC T hσ)
  by_cases hB : JEvBarAt T R κ i σ hV
  · exact norm_eq_of_inner_conj (inner_reading_conj_at T R κ v₀ he fw hE hT i σ hσ hV hB x x)
  · have h0 := (hT i σ hσ hV).2 hB
    have hx : x = 0 := by
      by_contra hx
      have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
      have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
      rw [h0] at h2
      exact h2 rfl
    subst hx
    rw [map_zero, map_zero, norm_zero, norm_zero]


omit R in
theorem not_good_conj {σ : D.what₂.LL →+* ℂ} (h : GoodEmb T.Q.c (res T σ)) :
    ¬ GoodEmb T.Q.c (res T ((starRingEnd ℂ).comp σ)) := by
  have key : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
      {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) {s : c.F →+* ℂ}, GoodEmb c s →
      ¬ GoodEmb c ((starRingEnd ℂ).comp s) := by
    intro E _ _ _ H l c s h h'
    have h2 : starRingEnd ℂ H.rt0 = H.rt0 := by
      conv_lhs => rw [← h]
      exact h'
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h2
    have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp [pow_two, him] at h3
    nlinarith [mul_self_nonneg H.rt0.re]
  exact key T.Q.c h

end GlobalTheory.ConjNorm


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ConjNorm.pConj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ fw : FWTie T R κ v₀, BarTie fw → R.LUnif → R.PConj := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ fw hT hu i σ x
  have hE := GlobalTheory.evaluates_of_unif D G Pl0 T0 A T R F κ v₀ fw hu
  have key : ∀ σ, ¬ GoodEmb T.Q.c (res T σ) → (R.FW i).nrmAt ((starRingEnd ℂ).comp σ) x = (R.FW i).nrmAt σ x :=
    fun σ hσ => GlobalTheory.ConjNorm.norm_conj_of_not_good T R κ v₀ hC.models.HW fw hE hT hu i σ hσ x
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · have h1 := key _ (GlobalTheory.ConjNorm.not_good_conj T hσ)
    have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := RingHom.ext fun a => Complex.conj_conj _
    exact h1.symm.trans (congrArg (fun s => (R.FW i).nrmAt s x) e)
  · exact key σ hσ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
section
namespace GlobalTheory

theorem automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL :=
  GlobalTheory.T.harishChandra_finiteness_automorphic_GL_of_eigen _root_.GlobalTheory.HCFGL.coreFiniteGL

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section
namespace GlobalTheory.PureMatch

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def rowB (t : T) (w : Pl D.host.E) (i j : Fin D.R.m) :
    Fin ((locGrid G t w).rank (i, j)) ≃ Fin (spW₁ G i j).rank :=
  finCongr (rank_vertex G t w (X := ((i : ℕ), (j : ℕ))) ⟨i.2.le, j.2.le⟩)

def trB (t : T) {w : Pl D.host.E} {v : Pl D.host.F} (hv : w.under (𝓞 D.host.F) = v) {i j : Fin D.R.m} (e : Num G i j)
    (Y : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)) :
    Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) :=
  Matrix.of fun r c => GlobalTheory.LFun.complMap hv (Y (rowB t w i j r) (GlobalTheory.SquareFlipReach.colE t w e c))

def blockV {i j : Fin D.R.m} (e : Num G i j) : Finset (Fin ((spW G i j).rank + (spW₁ G i j).rank)) :=
  Finset.univ.image fun k => e (Sum.inl k)

end GlobalTheory.PureMatch
end
end

