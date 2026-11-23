module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0089
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelModelsOfFunctoriality
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows

open Matrix

theorem exists_model_of_enum {D : D7} (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) {V : HSp D} (hV : V.SigOK)
    {S : D.what₂.Tau → SPar} (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hS : ∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧
      (Finset.univ.filter fun a => ε a = false).card = (V.sig (tauE D τ)).2)
    (hO : ∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) :
    ∃ M : DSModel V S, cart M = C := by
  classical
  have key : ∀ τ, ∃ σ : Equiv.Perm (Fin V.rank), ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧
      Formalism.QuantumDeterminants.IsHCParam lam ∧ ((O τ).submatrix id σ)ᴴ * gramAt D V τ * (O τ).submatrix id σ = Formalism.REAL.Jm ε ∧
      C τ * (O τ).submatrix id σ = (O τ).submatrix id σ * Formalism.REAL.Jm ε := by
    intro τ
    obtain ⟨lam, ε', hE, hH, hc⟩ := hS τ
    obtain ⟨ε, h1, h2⟩ := hO τ
    obtain ⟨σ, hσ⟩ := GlobalTheory.GridJoin.exists_perm_of_card_false ε ε' (by rw [GlobalTheory.GridJoin.card_false_of_gram hV τ h1, hc])
    have e : ε ∘ σ = ε' := funext hσ
    refine ⟨σ, lam, ε', hE, hH, ?_, ?_⟩
    · rw [GlobalTheory.GridJoin.gram_submatrix, h1, GlobalTheory.GridJoin.jm_submatrix, e]
    · rw [GlobalTheory.GridJoin.mul_submatrix_cols, h2, GlobalTheory.GridJoin.submatrix_mul_jm, e]
  choose σ lam ε hE hH h1 h2 using key
  obtain ⟨M, hM, -⟩ := _root_.GlobalTheory.dsModel_of_onb_cart D hDS V S (fun τ => (O τ).submatrix id (σ τ)) C
    (fun τ => ⟨lam τ, ε τ, hE τ, hH τ, h1 τ⟩) (fun τ => ⟨ε τ, h1 τ, h2 τ⟩)
  exact ⟨M, hM⟩

theorem isHCParam_dual_parV (D : D7) (i j : ℕ) (τ : D.what₂.Tau) {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool)
    (hn : n = rankV D i j) (hE : IsEnum (dualPar (parV D 1 i j τ)) lam ε) : Formalism.QuantumDeterminants.IsHCParam lam := by
  refine ⟨hE.1, fun a' => ?_⟩
  obtain ⟨-, q, hq, hS⟩ := hE
  have hmem : (q a', ε a') ∈ dualPar (parV D 1 i j τ) := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simp only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨y, ⟨x, hx, rfl⟩, hy1, -⟩ := hmem
  rw [← GlobalTheory.GridParDCount.grid_eq_num] at hx
  obtain ⟨z, hz⟩ := GlobalTheory.Grid.parD_entry_int D τ i j hx
  have hpar : Even (rankV D i j) ↔ Odd (i + j) := GlobalTheory.Grid.even_rkV_iff D i j
  rw [hq a', ← hy1]
  by_cases ho : Odd (i + j)
  · obtain ⟨N, hN⟩ := hpar.2 ho
    rw [if_pos ho]
    refine ⟨-z + 1 - N, ?_⟩
    have : (n : ℝ) = N + N := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring
  · have hne : ¬ Even (rankV D i j) := fun h => ho (hpar.1 h)
    obtain ⟨N, hN⟩ := Nat.not_even_iff_odd.1 hne
    rw [if_neg ho]
    refine ⟨-z - N, ?_⟩
    have : (n : ℝ) = 2 * N + 1 := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring

end GlobalTheory.SepRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviElementScalesRestrictionNormSqAbsDet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNorm

variable {D : D7}

theorem heisO_isoPart_zero (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ}
    (C' : Matrix (Fin V.rank) (Fin r) D.host.E) (F : WO V W → ℂ) :
    heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' 0) F = F := by
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' 0 = 0 := Matrix.zero_mul _
  funext w
  rw [h0]
  simp only [heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]


set_option maxHeartbeats 1000000 in
theorem norm_levi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ' = (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank * ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ' := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ μ' 𝓕' hμ' h𝓕' a g' m hC _hB h f hf
  have hstd : IsStdChar D ψ (-1) := hω.std
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.TwistDual.exists_isotropic_dual D V V' r C B hs
  obtain ⟨μ₀, 𝓕₀, h0⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V.rank
  obtain ⟨μ'', 𝓕'', h''⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V'.rank
  have hres := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hstd μ 𝓨 hμ
  have hΩf : IsThetaFunO ψ V W (ω (m, h) f) := hω.om_pres _ f hf
  have pΩ := _root_.GlobalTheory.MixParseval.parseval D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' _ _ hΩf hΩf
  have pf := _root_.GlobalTheory.MixParseval.parseval D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' f f hf hf
  obtain ⟨N₁, hN₁⟩ : ∃ N : Mx D W.rank r → ℂ, N = resNorm ψ V V' W C C' B μ 𝓨 μ'' 𝓕'' (ω (m, h) f) := ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N : Mx D W.rank r → ℂ, N = resNorm ψ V V' W C C' B μ 𝓨 μ'' 𝓕'' f := ⟨_, rfl⟩
  have hN₁c : Continuous N₁ := by rw [hN₁]; exact pΩ.1
  have hN₁i : Integrable N₁ μ := by rw [hN₁]; exact pΩ.2.1
  have hN₀c : Continuous N₀ := by rw [hN₀]; exact pf.1
  have hN₀i : Integrable N₀ μ := by rw [hN₀]; exact pf.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℂ, k = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank :=
    ⟨_, rfl⟩
  have hcov := GlobalTheory.T.integral_levi_phase_change_of_variables D ψ hstd W r μ hμ.1 h (_root_.GlobalTheory.UnitaryDetAbs.absE_det_matHom D W h) a N₀ hN₀c hN₀i
  have hph : ∀ y u : Mx D W.rank r, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) +
      symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) = phase ψ W y u :=
    fun y u => by rw [phase_apply, _root_.GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self D V W r C C' h1 u y]
  rw [← hk] at hcov
  have hφ : Continuous fun u : Mx D W.rank r => (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val : Mx D W.rank r) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : Mx D W.rank r → ℂ,
      N₂ = fun u : Mx D W.rank r => k * N₀ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) := ⟨_, rfl⟩
  have hN₂c : Continuous N₂ := by rw [hN₂]; exact continuous_const.mul (hN₀c.comp hφ)
  have hN₂i : Integrable N₂ μ := by rw [hN₂]; exact hcov.1.const_mul k
  have key : N₁ = N₂ := _root_.GlobalTheory.LeviNormInj.eq_of_phase_integral_eq D ψ hstd W r μ hμ.1 N₁ N₂ hN₁c hN₂c hN₁i hN₂i (fun y => by
    have s1 := _root_.GlobalTheory.ResNormFourier.resNorm_fourier D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' _ hΩf y
    have hz : HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y)
        (GlobalTheory.MixModel.adj (a⁻¹).val))) (GlobalTheory.MixModel.adj a.val) = y := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        ← GlobalTheory.MixModel.adj_mul, Units.mul_inv, GlobalTheory.MixModel.adj_one, Matrix.mul_one]
    have s2 := _root_.GlobalTheory.WeilCoeff.heis_coeff_eq D V W ψ χS χT ω hω m h f hf μ₀ 𝓕₀ h0.1 h0.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)))
    rw [_root_.GlobalTheory.IsoFrameAct.actO_isoPart_of_mul D V W r C a m hC h, hz] at s2
    have s3 := _root_.GlobalTheory.ResNormFourier.resNorm_fourier D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' f hf
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val))
    simp only [hph] at s1 s3
    rw [← hN₁] at s1
    rw [← hN₀] at s3
    rw [← s1, s2, s3, hcov.2 y, hN₂, ← integral_const_mul]
    congr 1
    funext u
    ring)
  have e0 := congrFun key 0
  rw [hN₁, hN₂, hN₀] at e0
  simp only [resNorm, Matrix.mul_zero, Matrix.zero_mul, heisO_isoPart_zero] at e0
  obtain ⟨p1, fin1, eq1⟩ := _root_.GlobalTheory.ThetaSqInt.thetaO_norm_fin D ψ hstd V' W μ'' 𝓕'' h'' _ (hres.1 _ hΩf).2.1
  obtain ⟨p2, fin2, eq2⟩ := _root_.GlobalTheory.ThetaSqInt.thetaO_norm_fin D ψ hstd V' W μ'' 𝓕'' h'' _ (hres.1 f hf).2.1
  rw [eq1, eq2, hk] at e0
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.Twist.NormRed.sq_norm_two_haar D V' W μ' 𝓕' hμ' h𝓕' μ'' 𝓕'' h''
  rw [hc _ (hres.1 _ hΩf).2.1.cont p1, hc _ (hres.1 f hf).2.1.cont p2]
  have eR : (∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ'').toReal =
      ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ)) ^ W.rank *
        (∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ'').toReal := by
    exact_mod_cast e0
  have eE : ∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ'' =
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank *
        ∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ'' := by
    rw [← ENNReal.toReal_eq_toReal_iff' fin1 (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) fin2),
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal]
    exact eR
  rw [eE, mul_left_comm]

end GlobalTheory.LeviNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LipschitzBoundRealUnipotentAction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.RealMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Eqv

variable {D : D7}

theorem norm_sub_three {G : Type*} (φ : G → ℂ) (a b c d : G) :
    ‖φ d - φ a‖ ≤ ‖φ d - φ c‖ + ‖φ c - φ b‖ + ‖φ b - φ a‖ := by
  have e : φ d - φ a = (φ d - φ c) + (φ c - φ b) + (φ b - φ a) := by ring
  rw [e]
  exact norm_add₃_le

theorem lip_list {ι : Type*} (θ : InfFam D) {V : HSp D} (A : Fr V) (φ : GA D V → ℂ) (c : ℝ) (hL : Lip θ A φ c)
    (τf : ι → D.what₂.Tau) (Xf Yf : ι → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : ∀ i, Xf i ∈ lieAt V (τf i)) (hY : ∀ i, Yf i ∈ lieAt V (τf i)) (l : List ι) (y : GA D V) :
    ‖φ (y * (l.map fun i => oneP θ V (τf i) (Xf i) 1 * oneP θ V (τf i) (Yf i) 1).prod) - φ y‖ ≤
      c * (l.map fun i => hsn (A.fr (τf i) * Xf i * (A.fr (τf i))⁻¹) +
        hsn (A.fr (τf i) * Yf i * (A.fr (τf i))⁻¹)).sum := by
  induction l generalizing y with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have h1 := hL y (τf i) (Xf i) (hX i) 1
    have h2 := hL (y * oneP θ V (τf i) (Xf i) 1) (τf i) (Yf i) (hY i) 1
    have h3 := ih (y * oneP θ V (τf i) (Xf i) 1 * oneP θ V (τf i) (Yf i) 1)
    rw [abs_one, mul_one] at h1 h2
    rw [← mul_assoc, ← mul_assoc]
    refine (norm_sub_three φ y (y * oneP θ V (τf i) (Xf i) 1)
      (y * oneP θ V (τf i) (Xf i) 1 * oneP θ V (τf i) (Yf i) 1) _).trans ?_
    rw [show ∀ a b s : ℝ, c * (a + b + s) = c * s + c * b + c * a from fun a b s => by ring]
    linarith

theorem list_prod_mulSingle {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Monoid (M i)] (x : ∀ i, M i)
    (l : List ι) (hl : l.Nodup) (w : ι) :
    (l.map fun i => Pi.mulSingle i (x i)).prod w = if w ∈ l then x w else 1 := by
  first
  | exact @_root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply
  | exact _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply
  | (apply _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply ..)

theorem conj_cancel {n : ℕ} {P M N : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : P * M * P⁻¹ = P * N * P⁻¹) :
    M = N := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have e := congrArg (fun Q => P⁻¹ * Q * P) h
  simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
    Matrix.mul_one] using e

theorem conj_back {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) : Q * (Q⁻¹ * M * Q⁻¹⁻¹) * Q⁻¹ = M := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hQ
  rw [Matrix.nonsing_inv_nonsing_inv Q hd]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

def expUJ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_exp X).unit, by
    have h := Formalism.REAL.exp_indefinite_unitary_holds n ε X hX 1
    show Formalism.REAL.inUJ ε (NormedSpace.exp X)
    simpa using h⟩

theorem isAtTau_unique (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (fr : UI.Frames D V) {τ : D.what₂.Tau}
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {h h' : GA D V} (hh : IsAtTau θ V τ g h) (hh' : IsAtTau θ V τ g h') :
    h = h' := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  have he : ∀ τ', infMat D.sp.cm.sig V.gram (θ τ') h = infMat D.sp.cm.sig V.gram (θ τ') h' := fun τ' => by
    by_cases e : τ' = τ
    · subst e; rw [hh.2.1, hh'.2.1]
    · rw [hh.2.2 τ' e, hh'.2.2 τ' e]
  have hx : UI.brg fr ((UI.brg fr).symm h) = h := (UI.brg fr).apply_symm_apply h
  have hx' : UI.brg fr ((UI.brg fr).symm h') = h' := (UI.brg fr).apply_symm_apply h'
  have hxx : (UI.brg fr).symm h = (UI.brg fr).symm h' := by
    refine Prod.ext (funext fun (v : InfinitePlace D.host.F) => ?_) ?_
    · have a := h2 ((UI.brg fr).symm h) ((Formalism.L2.Host.tauPl D).symm v) _ rfl
      have a' := h2 ((UI.brg fr).symm h') ((Formalism.L2.Host.tauPl D).symm v) _ rfl
      rw [Equiv.apply_symm_apply] at a a'
      rw [hx] at a
      rw [hx'] at a'
      have e2 := a.symm.trans ((he _).trans a')
      exact Subtype.ext (Units.ext (conj_cancel (fr.unit v) e2))
    · rw [(brg_mem_GinfC fr _).1 (by rw [hx]; exact hh.1), (brg_mem_GinfC fr _).1 (by rw [hx']; exact hh'.1)]
  rw [← hx, ← hx', hxx]


open Classical in
theorem isAtTau_brg (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (fr : UI.Frames D V) (v : InfinitePlace D.host.F)
    (a : Formalism.REAL.UJ (fr.ε v)) :
    IsAtTau θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Formalism.MainNotions.S.uMat a * (fr.P v)⁻¹)
      (UI.brg fr ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1)) := by
  classical
  obtain ⟨-, h2, -⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  have hs : ∀ w : InfinitePlace (UI.instV fr).F, w = v → Formalism.MainNotions.S.uMat ((Pi.mulSingle v a : (UI.instV fr).Ginf) w) = Formalism.MainNotions.S.uMat a := by
    rintro w rfl
    exact congrArg Formalism.MainNotions.S.uMat
      (Pi.mulSingle_eq_same (M := fun w : InfinitePlace (UI.instV fr).F => Formalism.REAL.UJ ((UI.instV fr).ε w)) w a)
  have hn : ∀ w : InfinitePlace (UI.instV fr).F, w ≠ v → Formalism.MainNotions.S.uMat ((Pi.mulSingle v a : (UI.instV fr).Ginf) w) = 1 := by
    intro w hw
    exact (congrArg Formalism.MainNotions.S.uMat
      (Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace (UI.instV fr).F => Formalism.REAL.UJ ((UI.instV fr).ε w)) hw a)).trans rfl
  refine ⟨(brg_mem_GinfC fr _).2 rfl, ?_, fun τ' hτ' => ?_⟩
  · have e := h2 ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1) ((Formalism.L2.Host.tauPl D).symm v) (Formalism.MainNotions.S.uMat a)
      (hs _ (Equiv.apply_symm_apply _ _)).symm
    rw [e]
    simp only [Equiv.apply_symm_apply]
  · have hw : Formalism.L2.Host.tauPl D τ' ≠ v := fun hv => hτ' (by rw [← hv, Equiv.symm_apply_apply])
    have e := h2 ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1) τ' 1 (hn _ hw).symm
    rw [e]
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit (Formalism.L2.Host.tauPl D τ'))
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]


open Classical in
theorem oneP_eq_brg (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (fr : UI.Frames D V) (v : InfinitePlace D.host.F)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (a : Formalism.REAL.UJ (fr.ε v))
    (ha : NormedSpace.exp X = fr.P v * Formalism.MainNotions.S.uMat a * (fr.P v)⁻¹) :
    oneP θ V ((Formalism.L2.Host.tauPl D).symm v) X 1 = UI.brg fr ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1) := by
  have hc := isAtTau_brg θ hθ fr v a
  rw [← ha, ← one_smul ℝ X] at hc
  have hex : ∃ x, IsAtTau θ V ((Formalism.L2.Host.tauPl D).symm v) (NormedSpace.exp ((1 : ℝ) • X)) x := ⟨_, hc⟩
  unfold oneP atTau
  rw [dite_eq_left hex]
  exact isAtTau_unique θ hθ fr hex.choose_spec hc

theorem map_prod_pairs {ι G H : Type*} [Monoid G] [Monoid H] (f : G →* H) (l : List ι) (a b : ι → G) :
    f (l.map fun i => a i * b i).prod = (l.map fun i => f (a i) * f (b i)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

theorem conj_mem_lieAt {V : HSp D} (fr : UI.Frames D V) (v : InfinitePlace D.host.F)
    {M : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hM : Formalism.REAL.inG (fr.ε v) M) :
    fr.P v * M * (fr.P v)⁻¹ ∈ lieAt V ((Formalism.L2.Host.tauPl D).symm v) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit v)
  have e1 : ((fr.P v)⁻¹)ᴴ * (fr.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  have hG : gramAt D V ((Formalism.L2.Host.tauPl D).symm v) =
      ((fr.P v)⁻¹)ᴴ * Formalism.REAL.Jm (fr.ε v) * (fr.P v)⁻¹ := by
    rw [← fr.spec v]
    calc gramAt D V ((Formalism.L2.Host.tauPl D).symm v) = V.gram.map (UI.phiV D v) := rfl
      _ = ((fr.P v)⁻¹)ᴴ * (fr.P v)ᴴ * V.gram.map (UI.phiV D v) * (fr.P v * (fr.P v)⁻¹) := by
        rw [e1, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : ∀ W : Matrix (Fin V.rank) (Fin V.rank) ℂ, (fr.P v)ᴴ * (((fr.P v)⁻¹)ᴴ * W) = W := fun W => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have e3 : ∀ W : Matrix (Fin V.rank) (Fin V.rank) ℂ, (fr.P v)⁻¹ * (fr.P v * W) = W := fun W =>
    Matrix.nonsing_inv_mul_cancel_left _ _ hd
  show _ * _ + _ * _ = 0
  rw [hG]
  have key : (fr.P v * M * (fr.P v)⁻¹)ᴴ * (((fr.P v)⁻¹)ᴴ * Formalism.REAL.Jm (fr.ε v) * (fr.P v)⁻¹) +
      ((fr.P v)⁻¹)ᴴ * Formalism.REAL.Jm (fr.ε v) * (fr.P v)⁻¹ * (fr.P v * M * (fr.P v)⁻¹) =
      ((fr.P v)⁻¹)ᴴ * (Mᴴ * Formalism.REAL.Jm (fr.ε v) + Formalism.REAL.Jm (fr.ε v) * M) * (fr.P v)⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e2, e3, Matrix.mul_add, Matrix.add_mul]
  rw [key, show Mᴴ * Formalism.REAL.Jm (fr.ε v) + Formalism.REAL.Jm (fr.ε v) * M = 0 from hM, Matrix.mul_zero, Matrix.zero_mul]


open Classical in
theorem lip_move_real : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (φ : GA D V → ℂ) (c : ℝ), 0 ≤ c → Lip θ A φ c → ∀ (u : (Formalism.IndefR.Eqv.UI.instV fr).Ginf) (Av Z : InfinitePlace D.host.F → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ v, Formalism.REAL.inG (fr.ε v) (Av v) ∧ Formalism.REAL.inG (fr.ε v) (Z v)) → (∀ v, Formalism.MainNotions.S.uMat (u v) = NormedSpace.exp (Av v) * NormedSpace.exp (Z v)) → ∀ y : GA D V, ‖φ (y * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) - φ y‖ ≤ c * ∑ v, (Real.sqrt (Formalism.REAL.hs (Av v)) + Real.sqrt (Formalism.REAL.hs (Z v))) := by
  intro D θ hθ V A fr hP φ c hc hL u Av Z hAZ hu y
  have hX : ∀ v, fr.P v * Av v * (fr.P v)⁻¹ ∈ lieAt V ((Formalism.L2.Host.tauPl D).symm v) :=
    fun v => conj_mem_lieAt fr v (hAZ v).1
  have hY : ∀ v, fr.P v * Z v * (fr.P v)⁻¹ ∈ lieAt V ((Formalism.L2.Host.tauPl D).symm v) :=
    fun v => conj_mem_lieAt fr v (hAZ v).2
  have hXe : ∀ v, oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Av v * (fr.P v)⁻¹) 1 =
      UI.brg fr ((Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf), 1) :=
    fun v => oneP_eq_brg θ hθ fr v _ _ (Matrix.exp_conj _ _ (fr.unit v))
  have hYe : ∀ v, oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Z v * (fr.P v)⁻¹) 1 =
      UI.brg fr ((Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf), 1) :=
    fun v => oneP_eq_brg θ hθ fr v _ _ (Matrix.exp_conj _ _ (fr.unit v))
  have hu' : u = ((Finset.univ : Finset (InfinitePlace D.host.F)).toList.map fun v =>
      (Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf) * (Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf)).prod := by
    have e : ∀ v : InfinitePlace D.host.F, ((Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf) *
        (Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf)) = (Pi.mulSingle v (expUJ (hAZ v).1 * expUJ (hAZ v).2) : (UI.instV fr).Ginf) :=
      fun v => (Pi.mulSingle_mul _ _ _).symm
    refine Eq.trans ?_ (congrArg List.prod (List.map_congr_left fun v _ => e v)).symm
    funext w
    refine Eq.trans ?_ (list_prod_mulSingle (M := fun w : InfinitePlace (UI.instV fr).F => Formalism.REAL.UJ ((UI.instV fr).ε w))
      (fun v => expUJ (hAZ v).1 * expUJ (hAZ v).2) _ (Finset.nodup_toList _) w).symm
    refine Eq.trans ?_ (if_pos (Finset.mem_toList.2 (Finset.mem_univ _))).symm
    exact Subtype.ext (Units.ext (hu w))
  have hfac : UI.brg fr (u, 1) = ((Finset.univ : Finset (InfinitePlace D.host.F)).toList.map fun v =>
      oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Av v * (fr.P v)⁻¹) 1 *
        oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Z v * (fr.P v)⁻¹) 1).prod := by
    have e1 : ((u, 1) : (UI.instV fr).GA) = MonoidHom.inl (UI.instV fr).Ginf (UI.instV fr).Gf u := rfl
    rw [e1, hu']
    refine (map_prod_pairs ((UI.brg fr : (UI.instV fr).GA →* GA D V).comp (MonoidHom.inl _ _)) _
      (fun v => (Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf))
      (fun v => (Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf))).trans ?_
    refine congrArg List.prod (List.map_congr_left fun v _ => ?_)
    rw [hXe v, hYe v]
    rfl
  rw [hfac]
  refine (lip_list θ A φ c hL (fun v => (Formalism.L2.Host.tauPl D).symm v) (fun v => fr.P v * Av v * (fr.P v)⁻¹)
    (fun v => fr.P v * Z v * (fr.P v)⁻¹) hX hY _ y).trans (le_of_eq ?_)
  rw [Finset.sum_map_toList]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  have hPv : fr.P v = (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹ := by
    have h := hP ((Formalism.L2.Host.tauPl D).symm v)
    rwa [Equiv.apply_symm_apply] at h
  simp only [hPv, conj_back _ _ (A.fr_unit _)]
  rfl

end GlobalTheory.RealMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevelIndicatorCoefficientTestLeDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.PoinTerm

theorem norm_coef_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ), KDecay M v → ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
  intro D θ hθ V S M K v hv b hb
  choose C hC using fun τ => (hv τ).2 (b τ) (hb τ)
  have hpos : ∀ (τ : D.what₂.Tau) (x : GA D V), 0 < (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) := fun τ x =>
    pow_pos (add_pos_of_pos_of_nonneg one_pos (Real.sqrt_nonneg _)) _
  have hle : ∀ (τ : D.what₂.Tau) (x : GA D V), ‖⟪v τ, M.rep τ (cmp θ τ x) (b τ)⟫_ℂ‖ * (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) ≤ C τ :=
    fun τ x => hC τ _ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)
  have h0 : ∀ τ, 0 ≤ C τ := fun τ => (mul_nonneg (norm_nonneg _) (hpos τ 1).le).trans (hle τ 1)
  have hP : 0 ≤ ∏ τ, C τ := Finset.prod_nonneg fun τ _ => h0 τ
  refine ⟨∏ τ, C τ, hP, fun x => ?_⟩
  unfold coef
  split_ifs
  · unfold coefR
    rw [norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) fun τ _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (hpos τ x)]
    exact hle τ x
  · rw [norm_zero]
    exact mul_nonneg hP (Finset.prod_nonneg fun τ _ => (inv_pos.2 (hpos τ x)).le)

end GlobalTheory.PoinTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialFockSpaceStableMulTracePairing
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

theorem GlobalTheory.PolMul.pol_mul_pairInf_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ (q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ M.Pol ψ τ, ∃ f₁ ∈ M.Pol ψ τ,
          ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ _ τ _ _ q f hf
  exact GlobalTheory.PolMul.model_mul M ψ hψ τ q f hf
end

