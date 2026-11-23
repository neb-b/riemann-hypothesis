module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Formalism.MeanHeightDescent.CombinedAverageDegreeBound
public import Formalism.MonomialMeanResidues.FilteredDegree
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0128
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScaling
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FieldPt

section Charts

variable {K : Type} [Field K] {Jx : Type} [Fintype Jx]
variable {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
variable {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop}
variable {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (Jx → Sˣ) → pts S → pts S → Prop}

theorem map_zpow_units {A B T : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing T]
    [Algebra K T] (g : A →ₐ[K] T) (g' : B →ₐ[K] T) (x : Aˣ) (x' : Bˣ) (h : g (x : A) = g' (x' : B)) (n : ℤ) :
    g ((x ^ n : Aˣ) : A) = g' ((x' ^ n : Bˣ) : B) := by
  have e : Units.map (g : A →* T) x = Units.map (g' : B →* T) x' := Units.ext h
  have e' := congrArg (fun u : Tˣ => ((u ^ n : Tˣ) : T)) e
  simp only [← map_zpow] at e'
  exact e'

theorem wtAllZ_of_borChart (h : BorChart pts mapR borR) (e : Jx → ℤ) {f : Rules pts}
    (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : Jx → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = (∏ i, ((t i ^ e i : (p.R)ˣ) : p.R)) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : Jx → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dite_eq_left hy, dite_eq_left hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  rw [Units.coe_prod, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => map_zpow_units cB (locM K m) (tB i) (t i) (e3 i) (e i)

end Charts

theorem evR_frBor_secZ_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : GlobalTheory.CompanionTheory.Ar.Rec.WZ E) (f : Rul Xo c) (L : Type) [Field L] [Algebra c.F L] (t : Ix Dw → Lˣ) (y y' : FrPt Xo c L), f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a → FrBor t y y' → evR Xo c f y' = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Lˣ) : L) * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c a f L _ _ t y y' hf hb
  obtain ⟨⟨-, -, hB, -, hA, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  exact wtAllZ_of_borChart hB (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a) hf.1 hf.2 L t y y' (hA L y) (hA L y') hb

end GlobalTheory.CompanionTheory.Ar.Rec.FieldPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombBaseChange
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.CombMap

theorem isCombAt_spMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsCombAt x v cf w → IsCombAt (spMap φ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (Formalism.L2.Pj.dualMap φ) ≫ w) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x m v cf w hc
  obtain ⟨u, hu, hw⟩ := hc
  have hcomp : (Formalism.L2.Pj.dualMap φ).comp (algebraMap S (DualNumber S)) =
      (algebraMap T (DualNumber T)).comp φ := by
    ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let f : tEps (spMap φ ≫ x) ⟶ tEps x := Over.homMk (spMap (Formalism.L2.Pj.dualMap φ)) (by
    show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap T (DualNumber T)) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hcomp,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc])
  let P : (tEps x ⟶ Xo.univ.t.G) →* (tEps (spMap φ ≫ x) ⟶ Xo.univ.t.G) :=
    { toFun := fun g => f ≫ g
      map_one' := CategoryTheory.MonObj.comp_one f
      map_mul' := CategoryTheory.MonObj.comp_mul f }
  refine ⟨fun i => f ≫ u i, fun i => ?_, ?_⟩
  · rw [Over.comp_left, hu i]
    show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (cf i)) ≫ v i =
      spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (φ (cf i))) ≫ spMap (Formalism.L2.Pj.dualMap φ) ≫ v i
    rw [← Category.assoc, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp,
      ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    congr 2
    ext y <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, smul_eq_mul, map_mul,
      TrivSqZeroExt.algebraMap_eq_inl]
  · have h1 : (List.ofFn fun i => f ≫ u i) = (List.ofFn u).map P := by
      rw [List.map_ofFn]
      rfl
    rw [h1, ← map_list_prod]
    show (f ≫ (List.ofFn u).prod).left = _
    rw [Over.comp_left, hw]
    rfl

end GlobalTheory.CompanionTheory.Ar.CombMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPoint
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.KapEquiv

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_kap_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → ∃ ψ : kap Z ≃+* Or.𝔐.Ω₀, spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ ∧ ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Z hgen
  have hb₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have hb₂ : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    have hf : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact RingHom.flat_algebraMap_iff.2 hf
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance
  have hg : IsGenericPoint (Formalism.L2.Pj.genPt Z) (Z : Set (Xo.XF c)) :=
    Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
  have hC : IsCptGen (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z ≫ Y.j) :=
    GlobalTheory.CompanionTheory.Ar.Flat.isCptGen_comp_of_flat_preimmersion Y.j (fun x => (Y.normal x).1) (Formalism.L2.Pj.genPt Z)
      (GlobalTheory.CompanionTheory.Ar.Flat.eq_genericPoint_of_specializes Z.2 hg)
  have e₁ : GlobalTheory.CompanionTheory.Ar.genPt (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z ≫ Y.j) = Y.j (Formalism.L2.Pj.genPt Z) :=
    congrArg Y.j ((Xo.XF c).fromSpecResidueField_apply (Formalism.L2.Pj.genPt Z) _)
  have e₂ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf := RegAtDom.map_genPt Or.g_over
  have e₃ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ₀ := RegAtDom.map_genPt Or.𝔐.fn_over
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.Ar.FlagPull.exists_iso hC Or.𝔐.gen₀ (e₁.trans (hgen.symm.trans (e₂.symm.trans e₃)))
  refine ⟨ψ, hψ, ?_⟩
  have hsY : Y.j ≫ Y.s = Formalism.L2.Pj.strK ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
    (Spec.map_preimage _).symm
  have hfn : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
  let i : c.F →+* RM.Ω := (Or.𝔐.fn.comp ψ.toRingHom).comp (algebraMap c.F (Formalism.L2.Pj.kap Z))
  have e0 : i.comp (algebraMap (𝓞 c.F) c.F) = Or.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hS : spMap (i.comp (algebraMap (𝓞 c.F) c.F)) = spMap (Or.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      refine Eq.trans ?_ Or.𝔐.cst_over
      have h3 : Or.𝔐.ξ ≫ Or.𝔐.f ≫ Y.s = spMap Or.𝔐.fn ≫ spMap ψ.toRingHom ≫
          (Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
        rw [← Category.assoc, hfn, ← hψ]
        simp only [Category.assoc]
        rw [hsY]
      rw [h3, h1]
      simp only [i, spMap_comp_eq, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hS)
  have e4 : i = Or.𝔐.cst := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  intro a
  exact congrArg (fun φ : c.F →+* RM.Ω => φ a) e4

end GlobalTheory.CompanionTheory.Ar.KapEquiv
end
end

