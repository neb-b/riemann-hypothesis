module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFormConstL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFinitenessOfReproducingPolynomialAveragin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsAUNeZero
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResAniso.ResProp
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem absAU_ne_zero {D : D7} (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h0
  have := congrArg (absA D) (mul_inv_cancel u)
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

end GlobalTheory.ResAniso.ResProp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaIntLeSetLIntegralOfCover
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover : ∀ (D : D7) (V : HSp D) (n : ℕ) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank n → ℂ, Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → GlobalTheory.SiegelFormula.absThetaInt V ν φ ≤ ∫⁻ g in S, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
  intro D V n ν hν φ hφ S hS hcov
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hScov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hleft := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have e1 : GlobalTheory.SiegelFormula.absThetaInt V ν φ =
      ∫⁻ g in GlobalTheory.AutomorphicL2Unitary.stdDom (GQ V), GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
    rw [GlobalTheory.SiegelFormula.absThetaInt, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure,
      lintegral_map (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hφ) GlobalTheory.AutomorphicL2Unitary.measurable_mk]
    exact lintegral_congr fun g => hleft.descend_mk g
  rw [e1]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν
    (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (GQ V) ν) hS hScov
    (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) (fun γ hγ g => hleft γ hγ g)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
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

noncomputable section

namespace GlobalTheory.LatVac

theorem restrict_liftV_mem_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun t : κ → Fv F v => Φ (fun i => GlobalTheory.LatVac.liftV v (t i))) ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ κ _ v Φ hΦ
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    let s : (κ → Fv F v) → (κ → Af F) := fun t i => GlobalTheory.AdelicU.singleFin v (t i)
    have hs : Continuous s := continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp (continuous_apply i)
    have hinv : Function.LeftInverse (fun x : κ → Af F => fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)) s :=
      fun t => funext fun i => GlobalTheory.AdelicU.evalV_singleFin_self v (t i)
    have hev : Continuous (fun x : κ → Af F => fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)) :=
      continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
    have hce : Topology.IsClosedEmbedding s := hinv.isClosedEmbedding hev hs
    have hmem : g ∘ s ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
      ⟨hg.1.comp_continuous hs, hg.2.comp_isClosedEmbedding hce⟩
    have e : (fun t : κ → Fv F v => GlobalTheory.WeilM.pureA F (⇑f) g (fun i => GlobalTheory.LatVac.liftV v (t i))) =
        f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F 0) • (g ∘ s) := by
      funext t
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ hmem
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end GlobalTheory.LatVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
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

namespace GlobalTheory.SchwartzTranslation

theorem schA_add_const : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : κ → AF F),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun y => Φ (y + c)) ∈ GlobalTheory.WeilM.schA F κ :=
  fun {F} _ _ {_} _ c Φ hΦ => GlobalTheory.SchwartzTranslate.schA_translate F c hΦ

end GlobalTheory.SchwartzTranslation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticCompatibilityStandardKernelDataTrueColum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ColRows.analyticTie_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.AnalyticTie (I.rec7 l Z) t.δ t.χ t.cD ∧ t.tup (I.rec7 l Z).what₂.mu0 = 1 ∧ t.m2 = (I.rec7 l Z).R.m - 2 := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t hJ hS
  obtain ⟨-, -, hDg, -⟩ := GlobalTheory.Core.Ht2.analyticTies_trueCols I hOk (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1 l Z hJ

  have hcD : t.cD = I.J.cD := (t.O_dgen B.u₀ I.mu0).symm.trans (hS.O.dgen B.u₀ I.mu0)
  refine ⟨⟨t.cc_rec ▸ t.δ_ok, t.χ_ok, hcD ▸ hDg⟩, ?_, hS.m2⟩

  obtain ⟨hX, -, -, -, -, hSS, -, htup, -⟩ := hS
  cases t
  subst hX
  subst hSS
  cases htup
  exact I.trueColumn_tuple_trivial_eq_one
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntertwinerUnique
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical
namespace GlobalTheory.ArchInvForm

theorem trace_half {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    (z : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (⅟(2 : mixedEmbedding.mixedSpace F) * z) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z / 2 := by
  have h : (2 : ℝ) • (⅟(2 : mixedEmbedding.mixedSpace F) * z) = z := by
    rw [Algebra.smul_def, map_ofNat, ← mul_assoc, mul_invOf_self, one_mul]
  have h2 := congrArg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) h
  rw [map_smul, smul_eq_mul] at h2
  linarith

theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] {κ : Type} [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w φ = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ) w φ := by
  funext x
  simp only [schr, GlobalTheory.ArchUniq.schrF, hψ]
  congr 3
  rw [map_add (f := _), trace_half]
  rfl

theorem int_phase_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @Measure V (borel V)) (hμ : @Measure.IsAddHaarMeasure V _ _ (borel V) μ)
    (u v p : V → ℂ) (hp : ∀ x, ‖p x‖ = 1) (a : V) :
    @integral V ℂ _ _ (borel V) μ (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) =
      @integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (v x)) := by
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  have e : (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) = fun x => u (x + a) * starRingEnd ℂ (v (x + a)) := by
    funext x
    have h1 : p x * starRingEnd ℂ (p x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp x]; simp
    rw [map_mul]
    linear_combination (u (x + a) * starRingEnd ℂ (v (x + a))) * h1
  rw [e]
  exact integral_add_right_eq_self (μ := μ) (fun x => u x * starRingEnd ℂ (v x)) a

theorem const_of_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  intro _ F _ _ _ κ _ ψ hψ T A hT
  have hP := GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) κ
  have hnorm : ∀ t, ‖ψ t‖ = 1 := by
    intro t
    rw [hψ, show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) t : ℝ) : ℂ) =
      ((-(2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hK : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ w (f f₁ g g₁ : SInf F κ), (f₁ : _ → ℂ) = schr ψ w f → (g₁ : _ → ℂ) = schr ψ w g →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f₁ x * starRingEnd ℂ (T g₁ x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ w f f₁ g g₁ hf hg
    have e1 := hT w f f₁ hf
    have e2 := hT w g g₁ hg
    have e : (fun x => T f₁ x * starRingEnd ℂ (T g₁ x)) = fun x =>
        (ψ (x ⬝ᵥ (A w).2 + ⅟(2 : mixedEmbedding.mixedSpace F) * ((A w).1 ⬝ᵥ (A w).2)) * T f (x + (A w).1)) *
          starRingEnd ℂ (ψ (x ⬝ᵥ (A w).2 + ⅟(2 : mixedEmbedding.mixedSpace F) * ((A w).1 ⬝ᵥ (A w).2)) *
            T g (x + (A w).1)) := by
      funext x
      rw [show T f₁ x = schr ψ (A w) (T f) x from congrFun e1 x, show T g₁ x = schr ψ (A w) (T g) x from congrFun e2 x]
      rfl
    rw [e]
    exact int_phase_shift μ hμ _ _ _ (fun x => hnorm _) _
  have hmod : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f f' g g' : SInf F κ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ L f f' g g' hf hg
    obtain ⟨b, hb⟩ := GlobalTheory.ArchUniqStd.exists_right hP ((-(1 / (2 * Real.pi))) • L)
    have hw : ∀ (u u' : SInf F κ), (∀ x, u' x = Complex.exp (Complex.I * (L x : ℂ)) * u x) →
        (u' : _ → ℂ) = schr ψ (0, b) u := by
      intro u u' hu
      rw [schr_eq_schrF ψ hψ]
      funext x
      rw [hu x]
      simp only [GlobalTheory.ArchUniq.schrF]
      rw [add_zero, hP.zero_left, zero_div, add_zero, hb, ContinuousLinearMap.smul_apply, smul_eq_mul]
      congr 2
      push_cast
      field_simp
    exact hK μ hμ (0, b) f f' g g' (hw f f' hf) (hw g g' hg)
  have htr : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ (a : κ → mixedEmbedding.mixedSpace F) (f f' g g' : SInf F κ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ a f f' g g' hf hg
    have hw : ∀ (u u' : SInf F κ), (∀ x, u' x = u (x + a)) → (u' : _ → ℂ) = schr ψ (a, 0) u := by
      intro u u' hu
      rw [schr_eq_schrF ψ hψ]
      funext x
      simp [GlobalTheory.ArchUniq.schrF, hu, hP.zero_right]
    exact hK μ hμ (a, 0) f f' g g' (hw f f' hf) (hw g g' hg)
  letI mV : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  set μ₀ : Measure (κ → mixedEmbedding.mixedSpace F) := Measure.addHaar with hμ₀
  have hμ₀H : μ₀.IsAddHaarMeasure := by rw [hμ₀]; infer_instance
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.TransConstForm.eq_const_mul_l2_of_translation_invariant _ μ₀ hμ₀H T (htr μ₀ hμ₀H) (_root_.GlobalTheory.CharMult.multiplier_symm _ μ₀ hμ₀H T (hmod μ₀ hμ₀H))
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.ArchUniqStd.exists_one (V := κ → mixedEmbedding.mixedSpace F)
  have hself : ∀ h : SInf F κ, ∫ x, h x * starRingEnd ℂ (h x) ∂μ₀ = ((∫ x, ‖h x‖ ^ 2 ∂μ₀ : ℝ) : ℂ) :=
    fun h => GlobalTheory.WrongSignGauss.ip_self μ₀ h
  have hint : Integrable (fun x => ‖Φ x‖ ^ 2) μ₀ := by
    refine (GlobalTheory.WrongSignGauss.integrable_ip μ₀ Φ Φ).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  have hn : 0 < ∫ x, ‖Φ x‖ ^ 2 ∂μ₀ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
    have ho : IsOpen (Function.support fun x => ‖Φ x‖ ^ 2) := (Φ.continuous.norm.pow 2).isOpen_support
    exact ho.measure_pos μ₀ ⟨0, by simp [hΦ]⟩
  have hm : 0 ≤ ∫ x, ‖T Φ x‖ ^ 2 ∂μ₀ := integral_nonneg fun x => sq_nonneg _
  have hcΦ := hc Φ Φ
  change ∫ x, T Φ x * starRingEnd ℂ (T Φ x) ∂μ₀ = c * ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂μ₀ at hcΦ
  rw [hself, hself] at hcΦ
  have hcc : c = (((∫ x, ‖T Φ x‖ ^ 2 ∂μ₀) / (∫ x, ‖Φ x‖ ^ 2 ∂μ₀) : ℝ) : ℂ) := by
    have hn' : ((∫ x, ‖Φ x‖ ^ 2 ∂μ₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    rw [eq_div_iff hn', hcΦ]
  refine ⟨(∫ x, ‖T Φ x‖ ^ 2 ∂μ₀) / (∫ x, ‖Φ x‖ ^ 2 ∂μ₀), div_nonneg hm hn.le, fun μ hμ f f' => ?_⟩
  haveI : μ.IsAddHaarMeasure := hμ
  have hs : μ = Measure.addHaarScalarFactor μ μ₀ • μ₀ := Measure.isAddLeftInvariant_eq_smul μ μ₀
  have hcf := hc f f'
  change ∫ x, T f x * starRingEnd ℂ (T f' x) ∂μ₀ = c * ∫ x, f x * starRingEnd ℂ (f' x) ∂μ₀ at hcf
  change ∫ x, T f x * starRingEnd ℂ (T f' x) ∂μ = _ * ∫ x, f x * starRingEnd ℂ (f' x) ∂μ
  rw [hs, integral_smul_nnreal_measure, integral_smul_nnreal_measure, hcf, ← hcc]
  simp only [NNReal.smul_def, smul_eq_mul, Complex.real_smul]
  ring

end GlobalTheory.ArchInvForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothBumpWithTrigonometricExpansionStatement
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
theorem _root_.GlobalTheory.T.archimedean_smooth_bump_with_trigonometric_expansion : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.ArchTrigBump.arch_bump_trig | exact GlobalTheory.ArchTrigBump.arch_bump_trig | (intros; apply GlobalTheory.ArchTrigBump.arch_bump_trig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingArchimedeanBoundFockNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.BrPairBound

theorem pairK_one_re_nonneg {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x : VV ℂ w) :
    0 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re := by
  by_cases h : x = 0
  · simp [h]
  · exact (Complex.lt_def.1 (GlobalTheory.CoefModel.pairK_pos w (G := fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun _ => Matrix.PosDef.one) x h)).1.le

theorem inf_bound : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N)
    (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    0 ≤ (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re ∧
    0 ≤ (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
      (GlobalTheory.CoefModel.mapVV φ _ v)).re ∧
    ‖φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v)‖ ^ 2 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
      (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re *
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
        (GlobalTheory.CoefModel.mapVV φ _ v)).re := by
  intro K ι _ _ _ φ n N hN Λ σ hI hS u v
  refine ⟨pairK_one_re_nonneg _ _, pairK_one_re_nonneg _ _, ?_⟩
  rw [_root_.GlobalTheory.BrPairF.brPairF_map_descent φ hN Λ σ u v, GlobalTheory.BrPairF.brPairF_apply]
  set u' := GlobalTheory.CoefModel.mapVV φ Λ u
  set v' := GlobalTheory.CoefModel.mapVV φ _ v
  have h1 := _root_.GlobalTheory.FockCauchySchwarz.pairBK_sq_le σ (Formalism.L2.Col.Br.brStd hN Λ σ u') ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have h2 := GlobalTheory.T.branchingMap_hermitianNorm_le_prod_bounds hN Λ σ hI hS u'
  have h3 := _root_.GlobalTheory.FunIsom.pairK_funEquiv_symm_le σ v'
  have p2 := pairK_one_re_nonneg σ ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have p3 := pairK_one_re_nonneg Λ u'
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul h2 h3 p2 (mul_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _) p3)
    _ = _ := by ring

end GlobalTheory.BrPairBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingIntegralUpToExponentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branchingPairing_integral_upToExponents : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) {n N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsFullLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    u ∈ nabAtr emb Λ L → v ∈ nabAtr emb (fun τ => (σ τ).dual) M →
    GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0 ∨
      -Formalism.DivisionValues.vw w (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≤
        Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro E K ι _ _ _ _ _ _ emb n N hN Λ σ hI hS M L hM hL w u v hu hv
  first
  | exact GlobalTheory.BrPairLocal.finLocal emb hN Λ σ hI hS M L hM hL w u v hu hv
  | exact GlobalTheory.BrPairLocal.finLocal emb hN Λ σ hI hS M L hM.toIsLattice hL w u v hu hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFinitenessOfReproducingPolynomialAveraginStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformFiniteness_of_reproducingPolynomial_averaging : GlobalTheory.PsCo.Pc3.Repro → (∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A) → GlobalTheory.PsCo.Pc3.UFin := by
  exact GlobalTheory.PsCo.Pc3.uFin_of'
end

