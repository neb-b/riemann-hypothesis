module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0942
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0943
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyExtAnd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0889
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoefficientsIntegralCoreForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0914

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompAtEqOneOfTameAt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.AVGood

theorem compAt_eq_one_of_tameAt {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (χ : HChar L)
    (hχ : χ.TameAt s.w) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (hξ : NG.IsCompAt χ s ξ)
    (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ)
    (hu : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) < 1) : ξ u = 1 := by
  obtain ⟨ξ', hξ', hv⟩ := _root_.GlobalTheory.HeckeSplitComp.main L s χ hχ
  have e : ξ = ξ' := _root_.GlobalTheory.CompAtUniq.main L χ s ξ ξ' hξ hξ'
  have hu1 : Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
    have h := Valuation.map_one_add_of_lt (Valued.v : Valuation (s.v.adicCompletion (maximalRealSubfield L)) _) hu
    rwa [add_sub_cancel] at h
  rw [e, hv u 1 1 (by simp) hu1 (by simpa using hu), map_one]

theorem tameAtG_of_tameAt (D : D7) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (h : ∀ (i : D.nd.Loc) (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k), (tup (D.nd.mu i) j).TameAt (D.naut.plGw k v)) :
    TameAtG D tup := by
  intro i j k v s ξ hw hξ u hu
  exact compAt_eq_one_of_tameAt s _ (hw ▸ h i j k v) ξ hξ u hu

theorem tameAtG_of_tupTied (D : D7) (cf : CharFrame D) {C : NChoice D} (tp : TupTied D cf C) : TameAtG D tp.tup :=
  tameAtG_of_tameAt D tp.tup fun i j _ _ x hx hx' => by
    change (cf.mu0 j).loc _ x * (tp.xi (D.nd.mu i)).loc _ x = 1
    rw [(cf.isMu0 j).tame _ x hx hx', tp.xi_tame _ _ x hx hx', one_mul]
end GlobalTheory.AVGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelPointRepsConjugateHalfModLattice
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.FlipReps

theorem flip_reps : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') ∧ (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ Y.card = flipIdx V W T m := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT
  obtain ⟨-, -, -, -, hSV, hSW, -⟩ := hP
  have hm0 : 0 < m := hm.pos
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hT
  set Λ := latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) with hΛ
  have hcard : Nat.card (GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m) = flipIdx V W T m := by
    have hc' : cA D eT = ∑ PP ∈ T, cA D (es PP) := by rw [hsum, map_sum]
    rw [hc', _root_.GlobalTheory.DivPtFourier.card_DQ_sum Λ (fun c hc u hu => GlobalTheory.PlaceModelSum.idem_smul_latO hc hu) T (fun PP => cA D (es PP)) ?_ ?_ m]
    · unfold flipIdx
      refine Finset.prod_congr rfl fun PP hPP => ?_
      have hi : Formalism.L2.NTheta.IsIdemAt (cA D (es PP)) (Formalism.L2.DIV.conjPl PP) :=
        GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun _ => Iff.rfl
      rw [_root_.GlobalTheory.DivPtLocal.natCard_DQ D V W ΛV ΛW hSV hSW _ _ hi m hm0, _root_.GlobalTheory.ConjNormPow.absNorm_maxPowDividing_conjPl]
    · intro i hi; rw [← map_mul, (hes i hi).1.1]
    · intro i hi j hj hij; rw [← map_mul, GlobalTheory.Tow.idemAt_orth (hes i hi) (hes j hj) hij, map_zero]
  have hfin : Finite (GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact flipIdx_ne_zero V W T hm0.ne')
  letI := Fintype.ofFinite (GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m)
  have hhalf : ∀ y : WO V W, cA D eT • y = y → IsHalf (cA D eT) y := fun y hy =>
    (GlobalTheory.PlaceModel.isHalf_iff V W).2 ((GlobalTheory.PlaceModel.mem_half V W).2 hy)
  have hhalf' : ∀ y : WO V W, IsHalf (cA D eT) y → cA D eT • y = y := fun y hy =>
    (GlobalTheory.PlaceModel.mem_half V W).1 ((GlobalTheory.PlaceModel.isHalf_iff V W).1 hy)
  refine ⟨Finset.univ.image (fun q : GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m =>
    ((GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W)), ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hhalf _ (GlobalTheory.DivPtFourier.rep q).2.1, (GlobalTheory.DivPtFourier.rep q).2.2⟩
  · intro y hy y' hy' hyy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy'
    have hqq : q' = q := by
      rw [← GlobalTheory.DivPtFourier.mk_rep q, ← GlobalTheory.DivPtFourier.mk_rep q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨?_, ?_⟩
      · have : ((-GlobalTheory.DivPtFourier.rep q' + GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) =
            ((GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) -
              ((GlobalTheory.DivPtFourier.rep q' : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) := by
          push_cast; abel
        rw [this]; exact hyy
      · exact (GlobalTheory.PlaceModel.half V W (cA D eT)).add_mem ((GlobalTheory.PlaceModel.half V W (cA D eT)).neg_mem
          ((GlobalTheory.PlaceModel.mem_half V W).2 (GlobalTheory.DivPtFourier.rep q').2.1))
          ((GlobalTheory.PlaceModel.mem_half V W).2 (GlobalTheory.DivPtFourier.rep q).2.1)
    rw [hqq]
  · intro y hy hmy
    have hyd : y ∈ GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m := ⟨hhalf' y hy, hmy⟩
    set q : GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m := QuotientAddGroup.mk (⟨y, hyd⟩ : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m))
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ q), ?_⟩
    have h := GlobalTheory.DivPtFourier.mk_rep q
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have : ((-GlobalTheory.DivPtFourier.rep q + ⟨y, hyd⟩ : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) =
        y - ((GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) := by
      push_cast; abel
    rw [← this]; exact h.1
  · rw [Finset.card_image_of_injective _ GlobalTheory.DivPtFourier.rep_injective, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]

end GlobalTheory.FlipReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalThetaSeriesOfTwistSeriesSideData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatBundles

theorem ratHyp {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) : GlobalTheory.BigOn.Exp.RatHyp X.core X.R X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O i j (X.space_eq j) :=
  have hC := X.char
  { size := X.size
    host := X.host
    std := X.std j
    laws := X.geo.fw.laws
    core := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩
    unif := X.unif
    fw := ⟨X.geo.fw⟩
    tieIn := ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
    io := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
    guard := X.guard
    fin := X.finT
    pins := X.geo.pins j
    phase := by
      convert X.geo.phase j X.unif using 2
      rename_i k
      rw [X.phs k]
      simp
    frame := hP j _
    galois := hF.galois
    small := ⟨hF.vals, hF.ray, hF.roots⟩
    inUse := hi
    low := Y.low i }

theorem levelOf {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) : Y.Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b => (Y.Z.tie i j b).U_eq, fun i j b => (Y.Z.tie i j b).psiU_eq⟩

theorem rat_of_split (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hS : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat) {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D}
    (Y : SerSide X E) (hF : FieldOk X) (hsp : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) (b : Bool) : RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  _root_.GlobalTheory.SeriesTie.RatAll.ratRow hA hA.rayClassFieldSt (GlobalTheory.SerStd.seriesRatS_of hS) D X.Γ X.Pl0 X.I0 X.T X.A3 X.core X.R X.cG Y.S Y.YS
    X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O Y.Z.ρ Y.Z.good i j b (X.space_eq j) Y.Z.pin (levelOf Y) hsp (ratHyp X Y hF hP hi j)

theorem rat_bundles : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  fun hA hS _ X _ Y hF hP _ hi j b => rat_of_split hA hS X Y hF hF.split hP hi j b

end GlobalTheory.RatBundles
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSetupCountEqZeroOffBadPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin IsAlgPos)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs.SetupPin

variable {D : D7}

theorem goodSetup_badPlaces_conj (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) :
    ∀ i, ∀ P ∈ D.ntw.S0 i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.S0 i := by
  intro i P hP P' hc
  have hP' : P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E))) := hP
  rw [T.ringSpec_excludedPlaces_eq i] at hP'
  show P' ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  rcases hP' with (((h | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Formalism.L2.placesOver_conj D _ h hc))))
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
    exact Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨k, Formalism.L2.placesOver_conj D _ hk hc⟩))))
  · exact Or.inl (Or.inl (Or.inr (Formalism.L2.placesOver_conj D _ h hc)))
  · exact Or.inl (Or.inr (Formalism.L2.placesOver_conj D _ h hc))
  · exact Or.inr (T.concreteTwistFrame_extraExcludedPlaces_conj i P P' h hc)

theorem goodSetup_placesOverTwo_subset (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (h2 : 2 ∈ low) :
    ∀ i, placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i) := by
  intro i P hP
  show P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i 2 h2 hP)

theorem q_dvd_discr (D : D7) : D.host.q ∣ (NumberField.discr D.host.E).natAbs :=
  Int.natCast_dvd.1 D.host.q_dvd_discr

theorem goodSetup_count_eq_zero_off_badPlaces (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (h2 : 2 ∈ low)
    (hd : (NumberField.discr D.host.E).natAbs.primeFactors ⊆ low) (hc : (Ideal.absNorm D.host.ccK).primeFactors ⊆ low) :
    ∀ i P, P ∉ D.ntw.S0 i → FractionalIdeal.count D.host.E P D.host.AA = 0 := by
  intro i P hP
  by_contra hA
  have hb : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    by_contra hb
    exact hA (GlobalTheory.HalfCompare.primeToAA_of_not_mem hb)
  obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under P
  have hdiv : p ∣ GlobalTheory.HalfCompare.badInt D := (hpP _).1 hb
  have hlow : p ∈ low := by
    unfold GlobalTheory.HalfCompare.badInt at hdiv
    rcases hp.dvd_mul.1 hdiv with h | h
    · exact hd (Nat.mem_primeFactors.2 ⟨hp,
        Int.natCast_dvd.1 ((D.host.dvd_discr_iff_dvd_condN hp).2 (h.mul_right D.host.d)),
        Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩)
    · exact hc (Nat.mem_primeFactors.2 ⟨hp, h, by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot⟩)
  apply hP
  show P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i p hlow ((hpP p).2 dvd_rfl))

theorem mk_fractionRing_le {R : Type} [CommRing R] [IsDomain R] (h : Cardinal.mk R ≤ Cardinal.continuum) :
    Cardinal.mk (FractionRing R) ≤ Cardinal.continuum := by
  have hs : Function.Surjective
      (fun p : R × nonZeroDivisors R => IsLocalization.mk' (FractionRing R) p.1 p.2) := fun z => by
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) z
    exact ⟨(x, y), hxy⟩
  refine (Cardinal.mk_le_of_surjective hs).trans ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc Cardinal.mk R * Cardinal.mk (nonZeroDivisors R) ≤ Cardinal.continuum * Cardinal.continuum :=
        mul_le_mul' h ((Cardinal.mk_subtype_le _).trans h)
    _ = Cardinal.continuum := Cardinal.continuum_mul_self

theorem mk_frac_Ok (F : TwFrameC D) : ∀ i k, Cardinal.mk (FractionRing (D.ntw.Ok i k)) ≤ Cardinal.continuum := by
  intro i k
  haveI := D.ntw.lPrime i
  apply mk_fractionRing_le
  have hinj : Function.Injective (fun x : D.ntw.Ok i k => ((F.eOk i k x : _) : ℂ_[D.ntw.l i])) :=
    Subtype.val_injective.comp (F.eOk i k).injective
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [(GlobalTheory.PadicCard.card_padicAlgCl_padicComplex (D.ntw.l i)).2, Cardinal.mk_complex]

theorem continuous_comp_of_isOpen_ker {Γ B Y : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group B]
    [TopologicalSpace Y] (φ : Γ →* B) (f : B → Y) (h : IsOpen (φ.ker : Set Γ)) : Continuous (f ∘ φ) := by
  have hloc : IsLocallyConstant (f ∘ φ) := by
    intro s
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun g' => g⁻¹ * g') ⁻¹' (φ.ker : Set Γ), fun g' hg' => ?_,
      h.preimage (continuous_const.mul continuous_id), ?_⟩
    · have h1 : φ (g⁻¹ * g') = 1 := hg'
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      show f (φ g') ∈ s
      rw [← h1]
      exact hg
    · show φ (g⁻¹ * g) = 1
      rw [inv_mul_cancel, map_one]
  exact hloc.continuous

theorem delAt_alg (C : CharFrame D) (l : ℕ) : IsAlgPos (C.delAt l) 0 := by
  unfold CharFrame.delAt
  split_ifs
  · obtain ⟨n, h0, h⟩ := C.isDel'.fin
    exact GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd h0 h
  · obtain ⟨n, h0, h⟩ := C.isDel.fin
    exact GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd h0 h

end GlobalTheory.TwInputs.SetupPin

namespace GlobalTheory.TwInputs.SetupPin

variable {D : D7}

theorem exists_art_gal (hA : GlobalTheory.Published.GlobalArtinReciprocity) (cf : CharFrame D) (hR : DeltaRead D cf) :
    ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧ ∀ i b,
      ∃ (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ),
        (∀ x, ι (κ ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x) ∧
        GlobalTheory.GalChar.IsGal art κ ι (cf.delAt (D.ntw.l i)) (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by
  obtain ⟨art, hart⟩ := hA D.host.E D.nd.Om
  refine ⟨art, hart, fun i b => ?_⟩
  haveI := D.ntw.lPrime i
  obtain ⟨ρ⟩ := GlobalTheory.Triple.Reading.nonempty (X := D.ntw) i b
  have hker : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have hχ : IsAlgPos (cf.delAt (D.ntw.l i)) 0 := delAt_alg cf _
  obtain ⟨r0, hr0, hL⟩ := hart.exists_isLAdicOf ρ.ι hχ
  have hc : Continuous (GlobalTheory.GalChar.inQ ρ.κ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) :=
    continuous_comp_of_isOpen_ker (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
      (Units.map (GlobalTheory.GalChar.toQ ρ.κ).toMonoidHom) hker
  have hz : ∀ v, ‖(((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)‖ = 1 := fun v => cf.delAt_unitary _ _
  have heq : GlobalTheory.GalChar.inQ ρ.κ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) = r0 := by
    refine GlobalTheory.GalChar.eq_of_frob hart hc hr0 ?_
    filter_upwards [GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (Fact.out : (D.ntw.l i).Prime).ne_zero,
      GlobalTheory.GalChar.unr_ae (cf.delAt (D.ntw.l i))] with v hv hu A hA σ hσ
    obtain ⟨x, hx, hd⟩ := hR i v hv hu A σ hA hσ
    have hx' : D.what₂.embLL (x : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
      rw [hx, Units.val_inv_eq_inv_val]
    apply Units.ext
    rw [hL.frob_unr hart (Or.inr rfl) hu hA hσ, GlobalTheory.GalChar.inQ_val]
    cases b
    · have hstar : (x : D.what₂.LL) = star ((x⁻¹ : D.LL0) : D.what₂.LL) := by
        apply D.what₂.embLL.injective
        rw [D.starLL_cx, IntermediateField.coe_inv, map_inv₀, hx', inv_inv, ← Complex.inv_eq_conj (hz v)]
      have h1 : ρ.ι (ρ.κ (D.ntw.emb0 i x)) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ) := by
        rw [← D.ntw.restX_coefficientEmbedding_conj i x⁻¹ x hstar]
        have := ρ.read x⁻¹
        simp only [GlobalTheory.Triple.embSide, Bool.false_eq_true, if_false] at this
        rw [this]
        show D.what₂.embLL ((x⁻¹ : D.LL0) : D.what₂.LL) = _
        rw [IntermediateField.coe_inv, map_inv₀, hx', inv_inv]
      show GlobalTheory.GalChar.toQ ρ.κ (((D.ntw.delta i)⁻¹ σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = _
      rw [MonoidHom.inv_apply, map_units_inv]
      congr 1
      show ρ.κ (algebraMap _ _ _) = _
      rw [hd, ← h1, ρ.ι.symm_apply_apply]
    · have h1 : ρ.ι (ρ.κ (D.ntw.emb0 i x)) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
        have := ρ.read x
        simp only [GlobalTheory.Triple.embSide, if_true] at this
        rw [this]
        exact hx'
      show ρ.κ (algebraMap _ _ ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) = _
      rw [hd, ← map_inv₀, ← h1, ρ.ι.symm_apply_apply]
  refine ⟨ρ.κ, ρ.ι, fun x => ?_, hχ, ?_, ?_⟩
  · have := ρ.read x
    cases b <;> simpa [GlobalTheory.Triple.embSide] using this
  · exact continuous_comp_of_isOpen_ker (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) Units.val hker
  · rw [heq]
    exact hL

end GlobalTheory.TwInputs.SetupPin

namespace GlobalTheory.TwInputs.SetupPin

end GlobalTheory.TwInputs.SetupPin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFormAtEvaluationVectorEqRealisationLiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftForm_at_evaluationVector_eq_realisationLift : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1),
  (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) (X.geo.v₀ j (sg0 D X.A3.A)) =
    X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) (X.geo.v₀ j (sg0 D X.A3.A)) := by
  first | exact @GlobalTheory.PlaceLift.lift_read_at | exact GlobalTheory.PlaceLift.lift_read_at | (intros; apply GlobalTheory.PlaceLift.lift_read_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralCoreSupLatticeCombination
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.XiIntCore.xi_int_core : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hAR hSR hSI D X E Y hF hFP i hi j b s h hd
  obtain ⟨u, hu, hA⟩ := _root_.GlobalTheory.XiIntSteps.xi_int_core_forms hAR hSR hSI D X E Y hF hFP hF.split i hi j b s h hd
  refine ⟨u, hu, fun P hP F hPF => ?_⟩
  obtain ⟨c, hc⟩ := hA P hP F hPF
  refine ⟨c, fun Q M hQ hs a => ?_⟩
  obtain ⟨la, hla, n, o, ψ, hψ, he⟩ := hc Q M hQ hs a (X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀)
  obtain ⟨n', o', m, hm, he'⟩ := GlobalTheory.XiIntCore.supLattice_comb_of_baseInt hAR hSR hSI D X E Y hF hFP i hi j b _ la hla n o ψ hψ
  exact ⟨n', o', m, hm, he.trans he'⟩
end
end

