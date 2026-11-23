module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Formalism.LocalRingCardinality.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.NonVanAt

theorem up_eq_setIntegral {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {χA χW : (AE D)ˣ →* Circle}
    {om : GlobalTheory.Core.Rk.IP.WRep A W} (hW : IsWeilDatumO ψ A W χA χW om) {m : Measure (GA D A)} {X : Set (GA D A)}
    (hm : m.IsHaarMeasure) (hX : IsFundamentalDomain (GQ A) X m) {f : WO A W → ℂ} (hf : IsThetaFunO ψ A W f)
    {u : GA D A → ℂ} (hu : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) u) (h : GA D W) :
    GlobalTheory.Core.Rk.IP.up om m f u h = ∫ g in X, thetaKO om g h f * u g ∂m := by
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) (fun g => thetaKO om g h f * u g) := by
    intro γ hγ g
    have e : ((γ * g, h) : GA D A × GA D W) = (γ, 1) * (g, h) := by simp
    have h1 : thetaKO om (γ * g) h f = thetaKO om g h f := by
      unfold thetaKO
      rw [e, map_mul, Module.End.mul_apply]
      exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hf)
    show thetaKO om (γ * g) h f * u (γ * g) = thetaKO om g h f * u g
    rw [h1, hu γ hγ g]
  rw [GlobalTheory.Core.Rk.IP.up, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]

theorem rcoef_zero {D : D7} {A : HSp D} (m : Measure (GA D A)) (b : GA D A) : GlobalTheory.Core.Rk.IP.rcoef m 0 0 b = 0 := by
  simp [GlobalTheory.Core.Rk.IP.rcoef, GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]


set_option maxHeartbeats 1000000 in
theorem nonVan_of_downNe : ∀ (D : D7) (_ : DownNe D) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t := by
  intro D hD G _ _ Pl0 T A Ks _ _ _ R F hG hP i t h hh s hs y hy hy0
  obtain ⟨⟨cA, a, hdef⟩, hpl, hun, hunr, hη, hsig, hrW, hr0, hrV, -, -, -⟩ := GlobalTheory.T.thetaLiftPair_definite_place_character_data D G Pl0 T A Ks R F hG hP i t
  obtain ⟨hlev, hX⟩ := hG.core.models.νV i t
  have hm : (R.νV i t).IsHaarMeasure := hlev.1
  have hW := hG.core.thP.ωP i t
  obtain ⟨l, P, hreal⟩ := _root_.GlobalTheory.Core.Rk.RealOcc.real_ne D G Pl0 T A Ks R F hG hP i t y hy0 (R.νV i t) hm
  obtain ⟨hA0, hfix⟩ := _root_.GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed D G Pl0 T A Ks R F hG hP i t cA a hdef y l
  obtain ⟨B, c, hB, hHyp⟩ := GlobalTheory.T.satake_string_gives_simple_pole_hypotheses D G Pl0 T A Ks R F hG hP i t s hs
  obtain ⟨hcart, hfock, hsph, hfixΦ⟩ := _root_.GlobalTheory.ThPFock.fock_sph_prin D G Pl0 T A Ks R F hG hP i t P
  have hu0 : (fun g => l (R.extV i t y g)) ≠ 0 := by
    intro h0
    obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
    obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D (Vc D i)
    have : LocallyCompactSpace (GinfC (Vc D i)) := i6.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : BorelSpace (GinfC (Vc D i)) := Subtype.borelSpace _
    refine hreal ν 𝓕 hν Measure.haar inferInstance ?_
    rw [h0]
    simp only [rcoef_zero, mul_zero, integral_zero]
  have hpar := _root_.GlobalTheory.LiftParams.param_of_sysParam D G Pl0 T A Ks R F hG hP i t h hh s y hy l hu0 B hB
  have hpar' : GlobalTheory.LFun.IsParamFunV (Vc D i) (under (R.Pg ∪ R.Q t)) (fun g => l (R.extV i t y g)) B :=
    hun.symm ▸ hpar
  have hHyp' : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (under (D := D) (R.Pg ∪ R.Q t) : Set (HeightOneSpectrum (𝓞 D.host.F))) (Wc D i).rank D.R.t c B
      (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
    rw [hrW, hun]; exact hHyp
  have hF : Form R.θ (Vc D i) cA (R.βV i) (R.Pg ∪ R.Q t) (chiV R i t) (Wc D i).rank D.R.t (fun g => l (R.extV i t y g)) B := by
    refine ⟨hA0, hfix, ?_, hunr, c, ?_⟩
    · exact hpar'
    · exact hHyp'
  have hO : Occ R.ψ R.θ (cart (R.MW i (sg0 D A))) (R.ωP i t) (R.νV i t) (R.βV i) (R.Pg ∪ R.Q t)
      (fun g => l (R.extV i t y g)) (R.ptP i t P) := ⟨hcart, hfock, hsph, hfixΦ, hreal⟩
  have hW' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (chiW R i t) (chiV R i t) (R.ωP i t) := hW
  have hr1 : 0 < (Wc D i).rank := by rw [hrW]; exact hr0
  have hr2 : (Vc D i).rank = (Wc D i).rank + D.R.t := by rw [hrW]; exact hrV
  have key := hD R.ψ R.θ (Vc D i) (Wc D i) D.R.t (chiW R i t) (chiV R i t) (R.ωP i t) cA a (R.βV i) (R.Pg ∪ R.Q t)
    (R.νV i t) (fun g => l (R.extV i t y g)) B (cart (R.MW i (sg0 D A))) (R.ptP i t P) hdef hsig hr1 hr2 hη hW' hpl hm hF hO
  by_contra hno
  refine key fun f hf g => ?_
  rw [up_eq_setIntegral hW hm hX hf (GlobalTheory.AutomorphicL2Unitary.leftInv_of_isAutFun (Submodule.mem_inf.1 hA0).1.1.toIsAutFun)]
  by_contra hne
  exact hno ⟨f, l, g, hf, hne⟩

end GlobalTheory.Core.Rk.NonVanAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportCorrectionCarriesColumnLatticeRowTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.TraceX

theorem mulVec_mem_ideal {R : Type} [CommRing R] {I : Ideal R} {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) {y : Fin n → R}
    (hy : ∀ i, y i ∈ I) (k : Fin m) : (A *ᵥ y) k ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (hy i)

theorem latV_iff_hatL {D : D7} (S : HSp D) (L : Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  ⟨GlobalTheory.LatVHat.latV_mem_hatL D S L P y, GlobalTheory.HatLatV.mem_latV_of_hatL D S L P y hy⟩

theorem hat_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ} (hn : m = n)
    (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin m → E ⊗[F] Formalism.L2.Herm.Af F) :
    z ∈ Formalism.L2.Herm.hatL (F := F) (L.map ((LinearEquiv.funCongrLeft E E (finCongr hn)).toLinearMap.restrictScalars (𝓞 E))) ↔
      (fun j => z (Fin.cast hn.symm j)) ∈ Formalism.L2.Herm.hatL (F := F) L := by
  subst hn
  have e : L.map ((LinearEquiv.funCongrLeft E E (finCongr (rfl : m = m))).toLinearMap.restrictScalars (𝓞 E)) = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [e]
  rfl

theorem transport (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n)
    (ιA : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hrat : ∀ x : I.E, ιA (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιE x))
    (hint : ∀ a, a ∈ IntAf I.F I.E ↔ ιA a ∈ IntAf D.host.F D.host.E)
    {n : ℕ} (q : Fin n → Fin I.n → I.E) (c : Fin n → GlobalTheory.AdForm.EF D) :
    (∑ i, ιA.symm (c i) • incl I (q i)) ∈ I.Lf ↔
      (∑ i, c i • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q i (Fin.cast hr k)))) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (latS D) := by
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hA : ∀ a, ιA a = a := GlobalTheory.Core.Mi.FinFrame.eq_self_of_rat_of_int (Formalism.L2.SG.InstExistsPf.instOf D).F
    (Formalism.L2.SG.InstExistsPf.instOf D).E ιA.toRingHom
    (fun x => (hrat x).trans (congrArg _ (hid x))) (fun a ha => (hint a).1 ha)
  have hA' : ∀ a, ιA.symm a = a := fun a => (hA _).symm.trans (ιA.apply_symm_apply a)
  simp only [hid, hA']
  have e : latS D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := GlobalTheory.ConjPlaceRed.crdLat_eq_latFrame (D.sp.Y 0)
  rw [e]
  exact (GlobalTheory.ConjPlaceRed.mem_Lf D _).symm

theorem fin_emb {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (w : Fin A.rank → AE D) :
    (fun k => toEAf D ((d.j0 *ᵥ (o.jA *ᵥ w)) k)) =
      ∑ i, toEAf D (w i) • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k i) := by
  have h2 : HMul.hMul d.j0 o.jA = (d.i₀ * o.iA).map (incA D) := (Matrix.map_mul (f := incA D)).symm
  rw [Matrix.mulVec_mulVec, h2]
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    GlobalTheory.Core.Mi.FinFrame.toEAf_incA]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem fin_mt {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (y : Fin V.rank → AE D) :
    GlobalTheory.AdForm.finM V hn g *ᵥ (fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D ((Formalism.L2.Theta.mt V g *ᵥ y) (Fin.cast hn.symm j)) := by
  subst hn
  funext i
  exact (RingHom.map_mulVec (toEAf D) (Formalism.L2.Theta.mt V g) y i).symm


set_option maxHeartbeats 1600000 in
theorem trace_iff : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (D.sp.X 0).rank → AE D), (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV (D.sp.X 0) (lat0 F) (· = v) ↔ B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y)) ∈ latV (D.sp.Y 0) (latS D) (· = v)) := by
  intro D X h u ψ F tr hK B a₀ hId hL hAd h0 v y hy
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hy' : ∀ k, (B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k ∈ idAt D (· = v) :=
    mulVec_mem_ideal _ (mulVec_mem_ideal _ (mulVec_mem_ideal _ hy))
  refine (latV_iff_hatL _ _ _ _ hy).trans
    (Iff.trans ?_ (latV_iff_hatL _ _ _ _ hy').symm)
  change (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (lat0 F) ↔
    (fun k => toEAf D ((B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (latS D)
  refine (hat_reindex hn F.cls0.lev.Lb _).trans ?_
  have H := hL.1 (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j)))
  have e1 : (tr.h0⁻¹).1.1 *ᵥ (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D (y (Fin.cast hn.symm j)) := by
    rw [Matrix.mulVec_mulVec]
    have : HMul.hMul (tr.h0⁻¹).1.1 tr.h0.1.1 = 1 := Units.inv_mul tr.h0.1
    rw [this, Matrix.one_mulVec]
  rw [e1] at H
  refine H.trans ?_
  rw [← h0.2, fin_mt, fin_emb]
  refine (transport D X.B.I X.ιE hId h (rank_eq X h) tr.ιA tr.ιA_rat tr.ιA_int
    (fun i => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt i)) _).trans ?_
  simp only [hAd _ _]
  refine iff_of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) (latS D)) ?_)
  exact (Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl).symm

end GlobalTheory.Core.Mi.LatMatch.TraceX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStableLocalLatticeShape
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

theorem GlobalTheory.LatPairStab.stable_lattice_shape : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (L : Submodule 𝒪[k] (n → k)) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x ∈ L, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → x + Pi.single b ((t : k) * x d) ∈ L) → (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∃ x ∈ L, ∃ j, x j = c) → (∀ x : n → k, x ∈ L ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∨ (∀ x : n → k, x ∈ L ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) := by
  intro k _ _ _ _ n _ _ i L c hcard hc hcl hbd hex
  obtain ⟨x₀, hx₀, j, hj⟩ := hex
  obtain ⟨a, hai, haj⟩ : ∃ a, a ≠ i ∧ a ≠ j := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset n) ⊆ {i, j} := fun b _ => by
      by_cases hbi : b = i
      · simp [hbi]
      · simp [h b hbi]
    have h1 := Finset.card_le_card hsub
    have h2 : ({i, j} : Finset n).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at h1
    omega

  have hsm : ∀ (s : 𝒪[k]) (b : n) (y : k), (s • (Pi.single b y : n → k) : n → k) = (Pi.single b ((s : k) * y) : n → k) := by
    intro s b y
    ext m
    by_cases hm : m = b
    · subst hm; simp [Subring.smul_def]
    · simp [hm, Subring.smul_def]

  have ha : ∀ t : 𝒪[k], Pi.single a ((t : k) * c) ∈ L := by
    intro t
    have h := L.sub_mem (hcl x₀ hx₀ a j t haj (Or.inl hai)) hx₀
    simpa [hj] using h
  have hca : Pi.single a c ∈ L := by simpa using ha 1

  have hsing : ∀ b, b ≠ i → ∀ t : 𝒪[k], Pi.single b ((t : k) * c) ∈ L := by
    intro b hbi t
    by_cases hba : b = a
    · subst hba; exact ha t
    · have h := L.sub_mem (hcl (Pi.single a c) hca b a t hba (Or.inl hbi)) hca
      simpa using h

  have hi : ∀ t : 𝒪[k], t ∈ IsLocalRing.maximalIdeal 𝒪[k] → Pi.single i ((t : k) * c) ∈ L := by
    intro t ht
    have h := L.sub_mem (hcl (Pi.single a c) hca i a t (Ne.symm hai) (Or.inr ht)) hca
    simpa [Ne.symm hai] using h

  have hsum : ∀ x : n → k, (∀ b, Pi.single b (x b) ∈ L) → x ∈ L := by
    intro x h
    rw [← Finset.univ_sum_single x]
    exact L.sum_mem (fun b _ => h b)
  have hoff : ∀ x : n → k, (∀ j, c⁻¹ * x j ∈ 𝒪[k]) → ∀ b, b ≠ i → Pi.single b (x b) ∈ L := by
    intro x hx b hb
    have e : x b = (c⁻¹ * x b) * c := by field_simp
    rw [e]
    exact hsing b hb ⟨_, hx b⟩
  by_cases hci : Pi.single i c ∈ L
  · left
    intro x
    refine ⟨hbd x, fun hx => hsum x fun b => ?_⟩
    by_cases hb : b = i
    · subst hb
      have e : Pi.single b (x b) = ((⟨c⁻¹ * x b, hx b⟩ : 𝒪[k]) • (Pi.single b c : n → k) : n → k) := by
        rw [hsm]; congr 1; show x b = (c⁻¹ * x b) * c; field_simp
      rw [e]; exact L.smul_mem _ hci
    · exact hoff x hx b hb
  · right
    have hm : ∀ x (hx : x ∈ L), (⟨c⁻¹ * x i, hbd x hx i⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      intro x hx
      by_contra hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hu
      obtain ⟨v, hv⟩ := hu

      have hy : x - Pi.single i (x i) ∈ L := by
        apply hsum
        intro b
        by_cases hb : b = i
        · subst hb; simp
        · have := hoff x (hbd x hx) b hb
          simpa [hb] using this
      have hxi : Pi.single i (x i) ∈ L := by
        have := L.sub_mem hx hy
        simpa using this
      apply hci
      have h1 : ((↑(v⁻¹) : 𝒪[k]) * (v : 𝒪[k])) = 1 := Units.inv_mul v
      rw [hv] at h1
      have h2 := congrArg (fun z : 𝒪[k] => (z : k)) h1
      simp only [Subring.coe_mul, OneMemClass.coe_one] at h2
      set w : k := ((↑(v⁻¹) : 𝒪[k]) : k)
      have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
      have e : Pi.single i c = ((↑(v⁻¹) : 𝒪[k]) • (Pi.single i (x i) : n → k) : n → k) := by
        rw [hsm]; congr 1
        show c = w * x i
        linear_combination -(c * h2) + (w * x i) * hcc
      rw [e]; exact L.smul_mem _ hxi
    intro x
    constructor
    · intro hx
      exact ⟨hbd x hx, ⟨c⁻¹ * x i, hbd x hx i⟩, hm x hx, rfl⟩
    · rintro ⟨hx, s, hs, hsx⟩
      refine hsum x fun b => ?_
      by_cases hb : b = i
      · subst hb
        have e : x b = (s : k) * c := by rw [hsx]; field_simp
        rw [e]; exact hi s hs
      · exact hoff x hx b hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleLevelPosOddBadPrimesPrimeToLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TupLevel

theorem odd_absNorm {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (h : (2 : 𝓞 E) ∉ P.asIdeal) :
    Odd (Ideal.absNorm P.asIdeal) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  haveI := P.isPrime
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h2
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ P.asIdeal) 2 h2
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact absurd hx (by norm_num)
  have h1 : (2 : 𝓞 E ⧸ P.asIdeal) * x = 0 := by
    have := addOrderOf_nsmul_eq_zero x
    rw [hx, two_nsmul] at this
    rw [two_mul, this]
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact h (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_ofNat]; exact h3))
  · exact h0 h3

theorem odd_levC {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    (hX : X.Ok) (hPr : Pr.Ok) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (u : Pr.Word)
    (h2 : ∀ P ∈ Formalism.L2.Col.Sall sel mu u, (2 : 𝓞 X.E) ∉ P.asIdeal) : Odd (levC sel mu cst u) := by
  have hp : Odd (∏ P : Formalism.L2.Col.rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) :=
    Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun P _ =>
      odd_absNorm P.1 (h2 P.1 (Finset.mem_union.2 (Or.inr P.2)))
  obtain ⟨P₀, hP₀⟩ : (Pr.vT u).Nonempty := Finset.card_pos.1 (hPr.vT_card u ▸ hX.f_pos)
  have hT : Odd (Pr.T u) := hPr.vT_norm u P₀ hP₀ ▸ odd_absNorm P₀ (h2 P₀ (Finset.mem_union.2 (Or.inl hP₀)))
  exact hp.pow.mul (hT.mul hp.pow)

theorem levC_pos_odd_and_off : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι), 0 < levC I.sel (I.tup a) (I.cst a) u ∧ Odd (levC I.sel (I.tup a) (I.cst a) u) ∧ (∀ Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) := by
  intro B X I hI _ u a
  obtain ⟨hXo, hPr, -⟩ := base_fields_primes_ok B X
  have hc : (B.primes X).cond = B.host.QS * B.host.q * B.host.d := rfl
  have h2 := fun Q (hQ : Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u) =>
    GlobalTheory.DatumJets.HidaSetting.notMem_Sall hPr hI.sel_ok u Nat.prime_two (hI.ram_mem 2 Nat.prime_two B.host.toHostRaw.two_dvd_condN)
      (by rw [hc]; exact B.host.toHostRaw.two_dvd_condN) hQ
  have ho : Odd (levC I.sel (I.tup a) (I.cst a) u) :=
    odd_levC hXo hPr (I.cst a) u fun Q hQ h => h2 Q hQ (by exact_mod_cast h)
  refine ⟨ho.pos, ho, fun Q hQ h => ?_⟩
  obtain ⟨l, n, -, hlP, hl, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q.asIdeal
  by_cases hd : l ∣ B.host.QS * B.host.q * B.host.d
  · exact GlobalTheory.DatumJets.HidaSetting.notMem_Sall hPr hI.sel_ok u hl (hI.ram_mem l hl hd) (by rw [hc]; exact hd) hQ hlP
  · exact UpperTheory.Ram.natCast_notMem_of_coprime Q.isPrime.ne_top hlP ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm h

end GlobalTheory.TupLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.UnrWeil

theorem natCast_mem_of_isConjPl {D : D7} (n : ℕ) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (h : Lev.IsConjPl PP' PP)
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  by_contra hn'
  obtain ⟨y, c, hc, hyc⟩ := PP'.isMaximal.exists_inv hn'
  obtain ⟨c', hc', e⟩ := h c hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have key : (1 : 𝓞 D.host.E) = RingOfIntegers.mapRingHom (starRingEnd D.host.E) y * ((n : ℕ) : 𝓞 D.host.E) + c' := by
    have h1 := congrArg (fun z : 𝓞 D.host.E => star (algebraMap (𝓞 D.host.E) D.host.E z)) hyc
    simp only [map_add (f := _), map_mul, map_natCast, map_one, star_add, star_mul', star_natCast, star_one] at h1
    have hy : algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingHom (starRingEnd D.host.E) y) =
        star (algebraMap (𝓞 D.host.E) D.host.E y) := rfl
    have hc2 : algebraMap (𝓞 D.host.E) D.host.E c' = star (algebraMap (𝓞 D.host.E) D.host.E c) := e
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    simp only [map_add (f := _), map_mul, map_natCast, map_one, hy, hc2]
    rw [← h1]
  rw [key]
  exact PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hn) hc'

theorem not_both_mem {D : D7} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime ((p : ℕ) : 𝓞 D.host.E) ((q : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left a h1) (PP.asIdeal.mul_mem_left b h2)))

end GlobalTheory.Fam.UnrWeil

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingStabilisesIffCoreStabilises
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem moves_emb0_iff_moves_of_monoAt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (γ : GA D S₀), MonoAt d L M v → (Moves S (d.emb0 γ) L L (· = v) ↔ Moves S₀ γ M M (· = v)) := by
  intro D S S₀ ρ d L M v γ hL
  have supp : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D), (∀ i, y i ∈ idAt D (· = v)) →
      ∀ i, (A *ᵥ y) i ∈ idAt D (· = v) := fun A y hy i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy k)
  have hc : ∀ {n : ℕ} (x : Matrix (Fin S.rank) (Fin n) (AE D)) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  have j0iff : ∀ w : Fin S₀.rank → AE D, d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
    intro w
    rw [hL]
    simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
      zero_mem, implies_true, true_and]
  constructor
  · intro h w hw
    have h1 := h (d.j0 *ᵥ w) (supp _ _ hw)
    rw [j0iff, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, j0iff] at h1
    exact h1
  · intro h y hy
    rw [hL y, hL (mt S (d.emb0 γ) *ᵥ y)]
    simp only [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding, d.wittDecomp_projY_anisotropicEmbedding, d.wittDecomp_projAnisotropic_anisotropicEmbedding]
    rw [← Matrix.mulVec_mulVec, ← h _ (supp _ _ hy)]

end GlobalTheory.Core.Mi.LatMatch
end

