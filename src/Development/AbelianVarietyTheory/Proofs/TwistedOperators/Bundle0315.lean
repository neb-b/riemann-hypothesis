module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralGoodProjectorMovePetersson
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterWeilOperatorDerivative

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

variable {D : D7}

def embAt (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) (k : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  cmp θ τ (stabilizerEmbedding d (atTau θ Y τ k))

def mco {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (v₀ : M.H τ) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ℂ :=
  ⟪M.rep τ g₀ v₀, M.rep τ g (M.rep τ g₀ v₀)⟫_ℂ

def ptY {Y : HSp D} {S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S') (τ : D.what₂.Tau) (u : Formalism.REAL.UJ (M₀.ε τ)) :
    Matrix (Fin Y.rank) (Fin Y.rank) ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M₀ τ (Formalism.MainNotions.S.umat u)

structure LocOK (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S')
    (M : DSModel V S) (τ : D.what₂.Tau) (q : ℝ) (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ)
    (εB : Fin V.rank → Bool) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : M₀.H τ) (c : ℂ) : Prop where

  unitA : IsUnit A

  gramA : Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ

  unitB : IsUnit B

  gramB : Bᴴ * Formalism.REAL.Jm εB * B = gramAt D V τ

  adapted : ∀ (y : Fin Y.rank → ℂ) (a : ℂ),
    eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2

  real : g₀ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)

  kfin : v₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ

  dec : DecayAt M τ v₀ v₀ (2 * V.rank ^ 2 + 1)

  sm : w ∈ M₀.sm τ

  ne : w ≠ 0

  cne : c ≠ 0

  act : ∀ b : M₀.H τ, ∫ u, mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u)) * ⟪b, M₀.rep τ (ptY M₀ τ u) w⟫_ℂ ∂(Formalism.REAL.muG (M₀.ε τ)) =
    c * ⟪b, w⟫_ℂ

  far : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))) (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖c‖

  lip : ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤ Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹)

end GlobalTheory.PackLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicPointRationalLatticeUnitaryModelIsoEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDict
open Formalism.IndefR.Eqv.UI

theorem mem_hatL_iff (D : D7) (V : HSp D) (fr : Frames D V)
    (w : Fin V.rank → D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) :
    w ∈ Formalism.L2.Herm.hatL (F := D.host.F) fr.Λ ↔ w ∈ (instV fr).Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

theorem finE_brg (D : D7) (V : HSp D) (fr : Frames D V) (x : (instV fr).GA) :
    (Lev.finE V (brg fr x)).1 = (instV fr).fmat x.2 := by
  have hring : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E,
      Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) =
        Formalism.L2.SG.AdBridge.tauF (instV fr) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ((Lev.swapAE D).congr_arg (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    | tmul a b => exact (Formalism.L2.SG.AdBridge.tauF_tmul (instV fr) a b).symm
    | add a b ha hb =>
      have e1 := _root_.map_add (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) a b
      rw [e1, RingHom.map_add (f := _), ha, hb]
      exact (RingHom.map_add _ _ _).symm
  rw [((brg_isBridge fr) x).2]
  ext i j
  simp only [Lev.finE, finHom, matHom, Formalism.UG.bc, Formalism.L2.SG.AdBridge.hmat, Formalism.L2.SG.AdBridge.ofHAFin,
    MonoidHom.comp_apply, Units.coe_map, Matrix.map_apply]
  exact hring _

theorem latAt_brg : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  intro D V fr x
  unfold GlobalTheory.SepPer.latAt GlobalTheory.Count.lamX
  congr 1
  ext y
  rw [← map_inv (brg fr) x, finE_brg D V fr x⁻¹]
  exact mem_hatL_iff D V fr _

end GlobalTheory.LatDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointConjugateThetaLiftEqVectorValuedLift
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjAdjoint

theorem inner_eq_integral {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hH : R.models_HW)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (a b : (R.HW i σ).H) :
    inner ℂ a b = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) *
      ∫ g in R.fdW i, star ((R.HW i σ).e a (fun ρ => v ρ) g) * (R.HW i σ).e b (fun ρ => v ρ) g ∂(R.νW i) := by
  obtain ⟨-, -, hip⟩ := hH i σ
  have hc := ipM_spec (R.MW i σ) (R.νW i) (R.fdW i) _ _
    (GlobalTheory.LiftLower.IsMultIP₂ (R.HW i σ) (N := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) hip a b)
  rw [hip, ipAt, (hc (fun ρ => v ρ) (fun ρ => v ρ)).2]
  congr 1
  rw [Finset.prod_eq_one, mul_one]
  intro ρ _
  rw [inner_self_eq_norm_sq_to_K, hv ρ]
  simp

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint

theorem integrableOn_theta {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hI : GlobalTheory.LiftRows.InnerProductFormulaC R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (hL : GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io)
    (hM : IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0))
    (U : MMap (R.MW i σ)) (hU : U ∈ R.Wall i σ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (h : GA D (Vc D i))
    (Q : PolF D (Wc D i).rank (Vc D i).rank) :
    IntegrableOn (fun g => Datum.thetaKO ω h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f Q) * starRingEnd ℂ (U (fun ρ => v ρ) g))
      (R.fdW i) (R.νW i) := by
  obtain ⟨μ, 𝓧, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
  obtain ⟨⟨Fr, hFr⟩, h2⟩ := (hL.1.models.νW i).1.2.2 R.θ hL.1.models.inf
  obtain ⟨mR, hmR⟩ := (h2 Fr hFr).1
  exact (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL _ _ hM μ 𝓧 hμ Fr hFr mR hmR U hU U hU v v Q Q).1 h

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues


set_option maxHeartbeats 400000 in
theorem adjoint_eq_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (th : H.H →ₗ[ℂ] (R.HW i σ).H),
  Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP →
  GlobalTheory.GalLift.IsProjOf R i σ thP th →
  ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W),
    inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hX hS hI hF hZ hR i σ s m μ' η' ω B f₀ f c io H hL hM hy hH v hv thP th hT hP y h w

  have hC : GlobalTheory.Hk3.Core R F := hL.1
  have hω := hL.2.2.2.2.2.1
  have hpt := hL.2.2.2.2.2.2.2.2.1
  have hc : c.Is := hL.2.2.2.2.2.2.2.2.2.1
  have hio := hL.2.2.2.2.2.2.2.2.2.2
  have hKc : starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  let φ : c.W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := GlobalTheory.AdelicScalar.ptL R i σ B f (io (PiTensorProduct.tprod ℂ v))
  have hφ : ∀ w, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) (φ w) := fun w => hpt _
  have hinf : ∀ u ∈ GinfC (Vc D i), ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w) := fun u hu w => hio.1 u hu _ w
  have hlev : ∀ κ ∈ Lev.levA (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)), ∀ w,
      ω (κ, 1) (φ w) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) κ)⁻¹ • φ w :=
    fun κ hκ w => hS i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL κ hκ _
  have hWall : ∀ y' : (R.HW i σ).H, (R.HW i σ).e y' ∈ R.Wall i σ := fun y' =>
    GlobalTheory.AdelicScalar.HMod_mem (hC.models.HW i σ) y'
  have hth : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) *
      starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g)) (R.fdW i) (R.νW i) := fun y' w h =>
    integrableOn_theta R F hI i σ s m μ' η' ω B f₀ f c io hL hM _ (hWall y') v h (io (PiTensorProduct.tprod ℂ v) w)
  have hth' : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => star (Datum.thetaKO ω h g (φ w)) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := fun y' w h => by
    have h1 := hth y' w h
    have h2 : IntegrableOn (fun g => starRingEnd ℂ (Datum.thetaKO ω h g (φ w) *
        starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g))) (R.fdW i) (R.νW i) :=
      h1.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable h1.1) (Filter.Eventually.of_forall fun x => by simp)
    refine Integrable.congr h2 (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hcls : ∀ u g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j))) := by
    intro u g
    refine (hT.eq _ _ _).trans ?_
    exact GlobalTheory.AdelicScalar.theta_classSum hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev hM hy (GlobalTheory.AdelicScalar.HMod_mem hH u) g
  have hφw : ∀ w, φ w = ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w) := fun w => rfl
  clear_value φ
  have hex := GlobalTheory.AdelicScalar.exists_upVec hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev (R.νW i) (R.fdW i)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ)) (hth _)
  have hΨ := hex.choose_spec.1
  have hlaw := hex.choose_spec.2
  have hzex := GlobalTheory.AdelicScalar.HMod_onto hH (GlobalTheory.AdelicScalar.upVec_mem c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw)
  have hz := hzex.choose_spec
  have hinv : ∀ u, ∀ γ ∈ GQ (Wc D i), ∀ g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) (γ * g) =
      thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g := by
    intro u γ hγ g
    refine (hcls u (γ * g)).trans (Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hcls u g).symm)
    exact congrArg _ (_root_.GlobalTheory.ThetaLeftW.thetaKernel_leftInvariant_rationalUnitary R i _ _ ω hω _ (hφ _) _ γ hγ g)
  have eF : ∀ u (y' : (R.HW i σ).H), (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) = fun g =>
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        (star (Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j)))) * (R.HW i σ).e y' (fun ρ => v ρ) g) := by
    intro u y'
    funext g
    refine (congrArg (fun t => star t * (R.HW i σ).e y' (fun ρ => v ρ) g) (hcls u g)).trans ?_
    simp only [star_sum, Finset.sum_mul, star_mul', star_inv₀, star_natCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hintF : ∀ u (y' : (R.HW i σ).H), IntegrableOn (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u)
      (PiTensorProduct.tprod ℂ v) g) * (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := by
    intro u y'
    have hsum := integrable_finsetSum (μ := (R.νW i).restrict (R.fdW i)) Finset.univ fun j _ =>
      (hth' y' (H.e u ((R.B.L i A.μ0).pres.y j)) (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j))).const_mul
        ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹
    exact hsum.congr (Filter.Eventually.of_forall fun g => (congrFun (eF u y') g).symm)
  have hpair : ∀ u, ∫ g in R.fdW i, star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) = inner ℂ u hzex.choose := by
    intro u
    refine (congrArg (fun F => ∫ g in R.fdW i, F g ∂(R.νW i)) (eF u (GlobalTheory.LiftLower.projH R i σ y))).trans ?_
    refine (integral_finsetSum _ fun j _ => (hth' _ _ _).const_mul _).trans ?_
    refine Eq.trans ?_ (hH.2.2 u hzex.choose).symm
    refine Eq.trans ?_ (congrArg (Bridge.adInner _ _ _ (H.e u)) hz).symm
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (integral_const_mul _ _).trans (congrArg _ ?_)
    refine Eq.trans ?_ (inner_conj_symm _ _)
    refine Eq.trans ?_ (congrArg (starRingEnd ℂ) (hΨ _ _)).symm
    unfold GlobalTheory.AdelicScalar.l2 Lift.pet
    refine Eq.trans ?_ integral_conj
    refine congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) (funext fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hadj : LinearMap.adjoint th y = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hzex.choose := by
    refine ext_inner_left ℂ fun u => ?_
    have e1 : (fun g => star ((R.HW i σ).e (th u) (fun ρ => v ρ) g) * (R.HW i σ).e y (fun ρ => v ρ) g) =
        fun g => star (R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v)) g) *
          (R.HW i σ).e y (fun ρ => v ρ) g :=
      funext fun g => congrArg (fun t : GA D (Wc D i) → ℂ => star (t g) * (R.HW i σ).e y (fun ρ => v ρ) g) (hP u v)
    refine (LinearMap.adjoint_inner_right th u y).trans ?_
    refine (inner_eq_integral R hC.models.HW i σ v hv (th u) y).trans ?_
    refine Eq.trans ?_ (inner_smul_right _ _ _).symm
    refine congrArg _ (Eq.trans ?_ (hpair u))
    refine (congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) e1).trans ?_
    exact _root_.GlobalTheory.EwfMove.integral_eWf_move R F hC hX i σ v _ (hinv u) (hintF u) y
  have e3 : c.ext (H.e (LinearMap.adjoint th y)) h = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hex.choose h := by
    refine (congrArg (fun x => c.ext (H.e x) h) hadj).trans ?_
    simp only [map_smul, Pi.smul_apply]
    exact congrArg _ ((congrArg (fun x => c.ext x h) hz).trans
      (GlobalTheory.T.extend_restriction_finitePoints_eq c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw h))
  refine (congrArg (fun a => inner ℂ a w) e3).trans ?_
  refine (inner_smul_left _ _ _).trans ?_
  refine congrArg₂ (· * ·) hKc ?_
  exact (hΨ h w).trans (congrArg (fun p => GlobalTheory.AdelicScalar.l2 (R.νW i) (R.fdW i) (fun g => Datum.thetaKO ω h g p)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ))) (hφw w))

end GlobalTheory.ConjAdjoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.PairLift (adjO)
noncomputable section
namespace GlobalTheory.ExchLatPf

theorem exchLat : All fun {D} _ _ _ {G} W _ => ExchLaw D → LatExch → ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ g : WO r.sp r'.sp → ℂ, IsLatVac (heisO W.ψ r.sp r'.sp) (latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) fun _ => True) g → IsLatVac (heisO W.ψ (G.pS (.core i)) (G.pT (.core i))) (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
  intro D hOff T L μ0 hLi sc G W M hM hEx hLat i hi r r' hr hr' g hg
  have hAdj := GlobalTheory.AdjLawPf.adjLaw D W.ψ W.ψ_std (G.V (.core i)) (G.V (.core (i+1)))
  have hE := (hEx W.ψ (G.V (.core i)) (G.V (.core (i+1))) W.ψ_std).2.1
  have hL := hLat D hOff T L μ0 hLi sc G W M hM i hi r r' hr hr' (fun _ => True)
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · refine (hE _ _).trans (congrArg _ ?_)
    have h2 : adjO (G.V (.core i)) (G.V (.core (i+1))) (2 • u) = 2 • adjO (G.V (.core i)) (G.V (.core (i+1))) u := by
      rw [two_smul, two_smul, hAdj.add]
    rw [h2]
    exact hg.1 _ ((hL u).1 hu)
  · refine (hE _ _).trans (congrArg _ ?_)
    exact hg.2 (cA D e) (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isSplitIdem_cA he) _ ((hL u).1 hu) (hAdj.half e u hue)

end GlobalTheory.ExchLatPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanSupportedSmulTransposeGramFiniteSubOnStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSupported_smul_transposeGram_finite_sub_one : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∀ g ∈ GfC X, ∀ u : AF D.host.F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (kapX X e hJ g) - 1) = 0 := by
  first | exact @GlobalTheory.InfKill.smul_mat_kapX_sub_one | exact GlobalTheory.InfKill.smul_mat_kapX_sub_one | (intros; apply GlobalTheory.InfKill.smul_mat_kapX_sub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilLineIntertwinesHeisenbergLeft
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

theorem GlobalTheory.ArchLineAct.intertwine_pair_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
          ∀ (t : ℝ) (p q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (f g : SInf F (Fin n × Fin d)),
            ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) p q ⇑f →
            ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  intro F E _ _ _ _ _ σ _hcm n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hWeil γ hγ T hTact
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  have hRsh : ∀ x z, At (evI F) z → R (x + z) = R x := (hR 0).1
  let L : ℝ → Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    fun t => GlobalTheory.ArchLineAct.lmulL (k := d) (mat (γ (Multiplicative.ofAdd t)))
  have hmat : ∀ g h : UA σ X.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have hmat1 : mat (1 : UA σ X.J) = 1 := rfl
  refine ⟨fun t => GlobalTheory.ArchLineAct.archMap M.co (L t), fun w => ?_, fun s t => ?_, ?_, fun t p q f g hg => ?_⟩
  · have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t))) :=
      (Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd)))
    set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift w.1, GlobalTheory.ArchLineAct.archLift w.2) with hu
    let Ru : Matrix (Fin n) (Fin n) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
      { toFun := fun x => x * u, map_add' := fun x y => Matrix.add_mul x y u,
        map_smul' := fun c x => Matrix.smul_mul c x u }
    let K := M.co.e.toLinearMap ∘ₗ Ru
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
    have hK : Continuous K := IsModuleTopology.continuous_of_linearMap K
    have hc : Continuous fun t : ℝ => M.co.e (L t u) := hK.comp hm
    show Continuous fun t : ℝ => (GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).1,
      GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).2)
    exact Continuous.prodMk
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_fst.comp hc)))
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_snd.comp hc)))
  · show GlobalTheory.ArchLineAct.archMap M.co (L (s + t)) =
      (GlobalTheory.ArchLineAct.archMap M.co (L s)).comp (GlobalTheory.ArchLineAct.archMap M.co (L t))
    rw [GlobalTheory.ArchLineAct.archMap_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    show mat (γ (Multiplicative.ofAdd (s + t))) * x =
      mat (γ (Multiplicative.ofAdd s)) * (mat (γ (Multiplicative.ofAdd t)) * x)
    rw [ofAdd_add, map_mul, hmat, Matrix.mul_assoc]
  · show GlobalTheory.ArchLineAct.archMap M.co (L 0) = LinearMap.id
    have hL : L 0 = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show mat (γ (Multiplicative.ofAdd 0)) * x = x
      rw [ofAdd_zero, map_one, hmat1, Matrix.one_mul]
    rw [hL, GlobalTheory.ArchLineAct.archMap_id]
  · set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) with hu
    have hue : M.co.e u = (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) :=
      LinearEquiv.apply_symm_apply _ _
    have hu' : At (evI F) (L t u) := GlobalTheory.ArchLineAct.at_lin _ (GlobalTheory.ArchLineAct.at_symm _ p q)
    have hue' := GlobalTheory.ArchLineAct.coord_eq M.co hu'
    have himpl := hW.impl (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u (tens (evI F) (⇑f) R) (hR f).2
    have hact : GlobalTheory.WeilM.actAB (cA σ) (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u = L t u := by
      show (mat (γ (Multiplicative.ofAdd t))) * u * ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1ᵀ =
        mat (γ (Multiplicative.ofAdd t)) * u
      rw [show ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1 from rfl, Matrix.transpose_one, Matrix.mul_one]
    rw [hact, GlobalTheory.ArchLineAct.rho_tens hψ M.co u p q hue (⇑f) R hRsh, ← hg, hTact t g R (hR g),
      hTact t f R (hR f), GlobalTheory.ArchLineAct.rho_tens hψ M.co (L t u) _ _ hue' _ R hRsh] at himpl
    funext x
    have h := congrFun himpl (GlobalTheory.ArchLineAct.archLift x)
    rw [GlobalTheory.ArchLineAct.tens_archLift _ R hRsh, GlobalTheory.ArchLineAct.tens_archLift _ R hRsh] at h
    exact mul_right_cancel₀ hR0 h

end
end

