module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0700
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateIsometryStatement
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translate_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E N) (x y : Sm E N), x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → rt E N g x ∈ squareIntegrableSmoothSubmoduleGL μ ∧ ⟪l2Map μ (rt E N g x), l2Map μ (rt E N g y)⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq | exact GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

noncomputable section

namespace GlobalTheory.CompanionTheory.Godement

open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

theorem cosetConv_of_continuous_law : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  intro D n χ s₁ φ hcont hlaw hs g
  obtain ⟨H, φ₀, -, -, hH, hsec, hne⟩ :=
    GlobalTheory.StdUnn.PolesModel.hypotheses_hold D n 0 (s₁.re : ℂ)
  have hconv0 := GlobalTheory.StdUnn.PolesModel.cosetConv_stdSec hH hsec
    (s := (s₁.re : ℂ)) (by simpa using hs) g
  have hstd : GlobalTheory.StdUnn.stdSec H φ₀ (s₁.re : ℂ) (s₁.re : ℂ) = φ₀ := by
    funext x
    simp [GlobalTheory.StdUnn.stdSec, GlobalTheory.Doubling.npow]
  rw [hstd] at hconv0
  have hK : IsCompact (↑(GlobalTheory.StdUnn.K D n) : Set (G D n)) :=
    GlobalTheory.StdUnn.HeightExists.isCompact_K
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (GlobalTheory.StdUnn.K D n).one_mem)
  obtain ⟨k₀, -, hk₀⟩ := hK.exists_isMinOn ⟨1, (GlobalTheory.StdUnn.K D n).one_mem⟩
    hsec.2.1.norm.continuousOn
  have hc : 0 < ‖φ₀ k₀‖ := norm_pos_iff.mpr (hne k₀)
  have hχ : ∀ u : Circle, ‖(u : ℂ)‖ = 1 := fun u => by
    first
      | exact Circle.norm_coe u
      | exact mem_sphere_zero_iff_norm.mp u.2
      | simp [Circle.abs_coe]
  have key : ∀ x, ‖φ x‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ x‖ := by
    intro x
    obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
    rw [hlaw p hp a ha k, hsec.1 p hp a ha k]
    have hu : IsUnit (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a)) :=
      (Group.isUnit _).map _
    have hr : (0 : ℝ) < (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu.ne_zero)
    have hRR : ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          ((s₁.re : ℂ) + (n : ℂ) / 2)‖ =
        ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          (s₁ + (n : ℂ) / 2)‖ := by
      simp only [GlobalTheory.Doubling.npow]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_cpow_eq_rpow_re_of_pos hr]
      congr 1 <;> simp
    have hb : ‖φ k‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ := by
      refine le_trans (hC k hk) ?_
      calc C = C / ‖φ₀ k₀‖ * ‖φ₀ k₀‖ := (div_mul_cancel₀ C hc.ne').symm
        _ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ :=
          mul_le_mul_of_nonneg_left (isMinOn_iff.mp hk₀ k hk) (div_nonneg hC0 hc.le)
    simp only [norm_mul, hχ, hRR]
    calc 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * ‖φ k‖
        ≤ 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * (C / ‖φ₀ k₀‖ * ‖φ₀ k‖) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C / ‖φ₀ k₀‖ * (1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D
            (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ * ‖φ₀ k‖) := by ring
  unfold GlobalTheory.Eis.CosetConv at hconv0 ⊢
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (hconv0.mul_left (C / ‖φ₀ k₀‖))
  simp only [GlobalTheory.Eis.term]
  exact key _

end GlobalTheory.CompanionTheory.Godement

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOne
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem absFn_tendsto_one : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (x : GA E N) (w : ℕ → ℂ), Tendsto w atTop (𝓝 0) → Tendsto (fun k => absFn N (w k) x) atTop (𝓝 1) := by
  intro E _ _ _ N x w hw
  have hL : ∀ t : ℂ, absFn N t x =
      Complex.exp (t * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)) := by
    intro t
    exact GlobalTheory.Mem.Chr.CharModel.absHom_val E t (GeneralLinearGroup.det x)
  have h0 : Tendsto (fun k => Complex.exp (w k *
      (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ))) atTop
      (𝓝 (Complex.exp (0 * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)))) :=
    (Complex.continuous_exp.tendsto _).comp (hw.mul_const _)
  simpa [hL] using h0

end GlobalTheory.CompanionTheory.LimV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSetStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_convergence_of_siegel_set : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.WeilThetaConvergence := by
  first | exact @GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet | exact GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet | (intros; apply GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSectionContinuous
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.SiegelWeil

theorem swSection_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω →
    ∀ (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f →
    ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    Continuous (swSection A B ν 𝓖 ω f) := by
  intro D ψ A B χ ω hω f hf ν 𝓖 hν
  rw [GlobalTheory.Core.Rk.IP.swSection_eq_swSec A B ν 𝓖 ω f]
  exact (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χ ω hω ν 𝓖 hν f hf).2

end GlobalTheory.CompanionTheory.SiegelWeil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesUniformBoundCompact
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem pure_rv_zero_le {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ)
    (hGc : Continuous G) (hGs : HasCompactSupport G)
    (hg : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : (AF F)ˣ, PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a ≤ ENNReal.ofReal M := by
  obtain ⟨MG, hMG⟩ := hGc.bounded_above_of_compact_support hGs
  have hB : ∀ v : HeightOneSpectrum (𝓞 F), ∃ B : ℝ, 0 ≤ B ∧ (v ∈ S → ∀ x, |g v x| ≤ B) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨B, hB⟩ := (hg v hv).1.bounded_above_of_compact_support (hg v hv).2
      exact ⟨|B|, abs_nonneg _, fun _ x => (hB x).trans (le_abs_self B)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hv⟩
  choose B hB0 hB using hB
  refine ⟨|MG| * ∏ v ∈ S, B v, mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun v _ => hB0 v), fun a => ?_⟩
  rw [GlobalTheory.T.pure_adelic_function_formula]
  split_ifs with h
  · refine ENNReal.ofReal_le_ofReal ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul, Finset.abs_prod]
    refine mul_le_mul ((hMG _).trans (le_abs_self MG)) ?_
      (Finset.prod_nonneg fun v _ => abs_nonneg _) (abs_nonneg _)
    exact Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) fun v hv => hB v hv _
  · simp

theorem th_pure_rv_zero_bound : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r : ℝ → (AF F)ˣ, IsRay θ r →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    ∀ D : Set (AF F)ˣ, IsCompact D → ∃ C : ℝ≥0, ∀ u ∈ D, ∀ δ : ℝ, 0 < δ →
      ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ) ≤ C := by
  intro F _ _ hF θ hθ r hr S G g hGc hGs hg D hD
  obtain ⟨M, hM0, hM⟩ := pure_rv_zero_le S G g hGc hGs hg
  obtain ⟨N, hN, hden⟩ := GlobalTheory.T.bounded_denominators_compact_idele_set F D hD S (fun v => tsupport (g v)) (fun v hv => (hg v hv).2)
  let K : Set (Ainf F) :=
    (fun p : (AF F)ˣ × Ainf F => (((p.1⁻¹ : (AF F)ˣ) : AF F).1) * p.2) '' (D ×ˢ tsupport G)
  have hK : IsCompact K := by
    refine (hD.prod hGs).image ?_
    have c1 : Continuous fun a : AF F => a.1 := continuous_fst
    have c2 : Continuous fun p : (AF F)ˣ × Ainf F => ((p.1⁻¹ : (AF F)ˣ) : AF F) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    exact (c1.comp c2).mul continuous_snd
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.CompanionTheory.MassCount.countBd F hF θ hθ K hK N hN
  refine ⟨(max C₀ 0 * M).toNNReal, fun u hu δ hδ => ?_⟩
  obtain ⟨hfin, hle⟩ := hC₀ δ hδ ⊤ top_ne_bot
  set T : Set F := {x : F | x ≠ 0 ∧ (∃ y ∈ (⊤ : Ideal (𝓞 F)), (y : F) = N * x) ∧ θ δ * algebraMap F (Ainf F) x ∈ K} with hT
  have hsupp : ∀ t : Fˣ, PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * (u * r δ)) ≠ 0 → (t : F) ∈ T := by
    intro t ht
    obtain ⟨hr1, hr2⟩ := hr δ hδ
    rw [GlobalTheory.T.pure_adelic_function_formula] at ht
    have h1 : ∀ v, ((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v = algebraMap F (Fv F v) (t : F) * (u : AF F).2 v := by
      intro v
      have : ((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v
          = algebraMap F (Fv F v) (t : F) * ((u : AF F).2 v * (r δ : AF F).2 v) := rfl
      rw [this, hr2]
      simp
    have h0 : ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1 = algebraMap F (Ainf F) (t : F) * ((u : AF F).1 * θ δ) := by
      have : ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1
          = algebraMap F (Ainf F) (t : F) * ((u : AF F).1 * (r δ : AF F).1) := rfl
      rw [this, hr1]
    by_cases hint : ∀ v, v ∉ S → ((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F
    swap
    · exact absurd (if_neg hint) ht
    rw [if_pos hint] at ht
    have hne : G ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1 * ∏ v ∈ S, g v (((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v) ≠ 0 := by
      intro h
      exact ht (by rw [h]; simp)
    have hG0 := left_ne_zero_of_mul hne
    have hp0 := right_ne_zero_of_mul hne
    have hgS : ∀ v ∈ S, algebraMap F (Fv F v) (t : F) * (u : AF F).2 v ∈ tsupport (g v) := by
      intro v hv
      rw [← h1 v]
      exact subset_tsupport _ (Finset.prod_ne_zero_iff.1 hp0 v hv)
    obtain ⟨y, hy⟩ := hden u hu (t : F) hgS (fun v hv => by rw [← h1 v]; exact hint v hv)
    refine ⟨t.ne_zero, ⟨y, Submodule.mem_top, hy⟩, ?_⟩
    refine ⟨(u, ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1), ⟨hu, subset_tsupport _ hG0⟩, ?_⟩
    have hinv : (((u⁻¹ : (AF F)ˣ) : AF F).1) * (u : AF F).1 = 1 := by
      exact congrArg (fun w : (AF F)ˣ => (w : AF F).1) (inv_mul_cancel u)
    show (((u⁻¹ : (AF F)ˣ) : AF F).1) * ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1 = _
    rw [h0]
    calc _ = ((((u⁻¹ : (AF F)ˣ) : AF F).1) * (u : AF F).1) * (θ δ * algebraMap F (Ainf F) (t : F)) := by ring
      _ = _ := by rw [hinv, one_mul]
  have hfin' : {t : Fˣ | (t : F) ∈ T}.Finite :=
    hfin.preimage (Units.val_injective.injOn)
  have hth : th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ) ≤ (hfin'.toFinset.card : ℝ≥0∞) * ENNReal.ofReal M := by
    unfold th
    rw [tsum_eq_sum (s := hfin'.toFinset) (fun t ht => by
      by_contra h
      exact ht (hfin'.mem_toFinset.2 (hsupp t h)))]
    calc _ ≤ ∑ t ∈ hfin'.toFinset, ENNReal.ofReal M := Finset.sum_le_sum fun t _ => hM _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (hfin'.toFinset.card : ℝ) ≤ (T.ncard : ℝ) := by
    have h1 : hfin'.toFinset.card = {t : Fˣ | (t : F) ∈ T}.ncard := (Set.ncard_eq_toFinset_card _ hfin').symm
    rw [h1]
    exact_mod_cast Set.ncard_le_ncard_of_injOn (fun t : Fˣ => (t : F)) (fun t ht => ht) Units.val_injective.injOn hfin
  have hle' : δ ^ Module.finrank ℚ F * (T.ncard : ℝ) ≤ max C₀ 0 := by
    refine hle.trans ?_
    simp
  have hd0 : (0 : ℝ) ≤ δ ^ Module.finrank ℚ F := by positivity
  calc ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ)
      ≤ ENNReal.ofReal (δ ^ Module.finrank ℚ F) * ((hfin'.toFinset.card : ℝ≥0∞) * ENNReal.ofReal M) := by gcongr
    _ = ENNReal.ofReal (δ ^ Module.finrank ℚ F * (hfin'.toFinset.card : ℝ) * M) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hd0, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal (max C₀ 0 * M) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hM0)
        exact (mul_le_mul_of_nonneg_left hcard hd0).trans hle'
    _ = _ := by rw [ENNReal.ofReal]

end GlobalTheory.CompanionTheory.BasePsi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusElementLeviEmbedding
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.LevAt

theorem aT_eq_lev (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (t : ℝ) :
    aT E (r + s) r t = GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s (aT E r r t, 1) := by
  apply Units.ext
  have val_emb (g : GL (Fin r) (Ad E) × GL (Fin s) (Ad E)) :
      (GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s g : Matrix (Fin (r + s)) (Fin (r + s)) (Ad E)) =
        Matrix.reindex (GlobalTheory.SmGL.stdSum rfl) (GlobalTheory.SmGL.stdSum rfl)
          (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    all_goals simp [GlobalTheory.CompanionTheory.CTFin.lev, GlobalTheory.SmGL.emb₂,
      GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two,
      Matrix.blockDiagonal'_apply]
  rw [PositivityTheory.Rg.Rs.JFinTr.aT_val, val_emb]
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, PositivityTheory.Rg.Rs.JFinTr.aT_val, Matrix.diagonal_apply]
  have h1 : (fun _ : InfinitePlace E => (1 : ℂ)) = (1 : Cinf E) := rfl
  rw [h1, sub_add_cancel, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Conc.LevAt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedFirstBlockRestriction
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceL

theorem slice_typeF {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)) :
    IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W →
    ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)),
      IsOpen (K₁ : Set (GL (Fin r) (Af E))) ∧ FiniteDimensional ℂ W₁ ∧
      ∀ f ∈ typeF K W, ∀ y : GA E s,
        (fun x : GA E r => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₁ W₁ := by
  intro hK hW
  have hcf : cf (r + s) k t = finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) := by
    rw [cf, infGL_comm]
  refine ⟨Slice1.levelOne s K t,
    W.map (LinearMap.funLeft ℂ ℂ fun κ : Kinf E r => Slice1.levK E r s κ * k),
    Slice1.isOpen_levelOne hK t, inferInstance, ?_⟩
  intro f hf y
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have h := Slice1.lev_finGL_right g u y t (Unitary.toUnits k)
    have h' := hf.1 _ (Slice1.mem_levelOne.1 hu)
      (lev (Ad E) r s (g, y) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    rw [← h] at h'
    simpa only [hcf, mul_assoc] using h'
  · refine ⟨_, hf.2 (lev (Ad E) r s (g, y) * finGL E (r + s) t), ?_⟩
    funext κ
    have h := Slice1.lev_infGL_right g (Unitary.toUnits κ) y t (Unitary.toUnits k)
    have e : lev (Cinf E) r s (Unitary.toUnits κ, 1) * Unitary.toUnits k =
        Unitary.toUnits (Slice1.levK E r s κ * k) := by
      rw [map_mul, Slice1.toUnits_levK]
    rw [e] at h
    simp only [LinearMap.funLeft_apply, hcf]
    rw [← h]
    simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceL

end
end

