module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0400
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscNResNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0380
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0402
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasedFlagPairLatticeContainment
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0088
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimatesStatement
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_height_bound_of_local_estimates : StepSizes → StepClassG → StepNormalsG → StepPointsG → StepHeightG → StepAnalyticGP → GenCutP := by
  first | exact @GlobalTheory.SnPos.genCutP_of_steps | exact GlobalTheory.SnPos.genCutP_of_steps | (intros; apply GlobalTheory.SnPos.genCutP_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMeanEmbeddedPairsLeMassMulPairBound
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairsRow

theorem main : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → HostC → LatticeNormalizationCondition →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    Module.finrank D.host.E W = D.R.k → GlobalTheory.Mass.PD HW.B.flip → ∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) *
          GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') := by
  intro hMax hSi hHost hLat D large₂ X Y u hStd W HW hEmb hk hpd Λ hΛ x x' hx hx'
  obtain ⟨hK, -, -, hv1, -, -, -, -, -, -, -, hg, hT⟩ := hHost D large₂ hStd
  have hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E := by
    rw [(hHost D large₂ hStd).2.2.1]; exact hv1
  obtain ⟨hTp, hTP⟩ := hT u
  obtain ⟨hI, he⟩ := hLat D large₂ X Y u hStd W HW hEmb Λ hΛ
  have hk3 : 3 ≤ Module.finrank D.host.E W := by
    rw [hk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have : FiniteDimensional D.host.E W := Module.finite_of_finrank_pos (by omega)
  have h := GlobalTheory.DegCnt.PairMean.main Formalism.MainNotions.KappaEndpoints.mk_core hMax hSi D.host.E W HW hK
    (GlobalTheory.OrthoLattice.hasOrtho D.host.E hK) hv hpd hk3 (Tu D u) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) _ hTp hTP hI he rfl
    _ rfl (gS D) D.R.rS x x' _ hg hx hx' rfl
  rw [hk] at h
  refine h.trans (le_of_eq ?_)
  unfold GlobalTheory.DegAsm.pairBd
  simp only [mul_assoc]

end GlobalTheory.PairsRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeight
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covTC_holds : CovTC := by
  intro D large₂ X Y u C hStd t N hAd μ K hμ hK
  obtain ⟨hCM, hPl, hvI, hv1, -, hcard, -, -, -, hnorm, hrk, hg2, -⟩ := _root_.GlobalTheory.TypeAsm.hostC D large₂ hStd
  have hTerm := _root_.GlobalTheory.TermRow.termC_holds D large₂ X Y u hStd t N hAd
  obtain ⟨β, n₁, g, n₂, hF⟩ := _root_.GlobalTheory.TypeAsm.frameC_holds D large₂ X Y u C hStd t N hAd
  have hι : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    exact ⟨(hPl.2 w).choose⟩
  obtain ⟨τ0⟩ := id hι

  have hμeq : ∀ τ, μ τ = (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) ∧
      SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := fun τ => by
    obtain ⟨h1, h2, hinv, hFr⟩ := hF τ
    obtain ⟨-, -, -, -, ⟨c, hc⟩, -⟩ := hFr
    have hm := hμ τ
    rw [hinv] at hm
    exact GlobalTheory.Amp.StabHaar.normalFormStabilizerMeasure_eq_any_normalForm _ _ _ N.j_le _ _ _ _ _ β c _ h1 h2 hc hm
  haveI : SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := (hμeq τ0).2

  have hrat := GlobalTheory.TypeAsm.gam_iff_nLam D large₂ X Y u hStd t N hAd
  have hGiso : ∀ n ∈ (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    fun n hn => ((hrat n).1 hn).1.1.1
  have hpts : GlobalTheory.DegVol.realPts (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = trI C '' ROinf t := by
    rw [GlobalTheory.TypeAsm.RatIsomReal.realPts_eq_image D X C _ hGiso]
    congr 1
    ext y
    constructor
    · rintro ⟨x, n, hx, rfl, hn⟩
      obtain ⟨h1, h2⟩ := (hrat n).1 hn
      exact ⟨x, n, hx, rfl, h1, h2⟩
    · rintro ⟨x, n, hx, rfl, h1, h2⟩
      exact ⟨x, n, hx, rfl, (hrat n).2 ⟨h1, h2⟩⟩
  have hfund0 := GlobalTheory.CovFund.isFund_image D X Y u C t K hK
  rw [← hpts] at hfund0
  have hRP : GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹) =
      GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => n₁ τ * g τ * n₂ τ) := by
    congr 1; funext τ; exact (hF τ).2.2.1
  rw [hRP] at hfund0

  have hunit : ∀ τ, n₁ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ n₂ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ IsUnit (g τ).det :=
    fun τ => ⟨(hF τ).1, (hF τ).2.1, GlobalTheory.Amp.StabHaar.unit_of_GG (hF τ).2.2.2.2.2.2.2.1.choose_spec.1⟩
  obtain ⟨hFund, hvol⟩ := GlobalTheory.DegVol.UnipConj.isFund_conj_and_measure D.host.E (VS D).V D.R.k D.R.rS D.what₂.Tau
    (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) n₁ g n₂ (trI C '' K)
    (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) inferInstance hunit hfund0
  have hF' : ∀ τ, GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) β
      (fun y => n₂ τ *ᵥ phiV C τ y) (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (g τ) := fun τ => by
    rw [hvI]; exact (hF τ).2.2.2
  have hle := _root_.GlobalTheory.DegVol.Cov.cov_le D.host.E (VS D).V (HV D) hCM D.R.rS N D.R.k D.what₂.Tau (embS D) β
    (fun τ y => n₂ τ *ᵥ phiV C τ y) (fun τ => zB X (C.Qi τ) u τ) (fun τ => zB X (C.Qi τ) u τ) g hPl hrk hF'
    (by rw [hAd.1, hnorm, hvI, hcard]) (by rw [hvI]; exact hv1) (gS D) t.lam _ (by omega) hTerm hFund
  have hμpi : Measure.pi μ = Measure.pi fun τ => (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) := by
    congr 1; funext τ; exact (hμeq τ).1
  rw [hμpi, hvol]
  refine hle.trans (le_of_eq ?_)
  rw [hvI, hcard]
  rfl

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermitianIsometryMatrixIffMemIsometriesStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ ↔ n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) := by
  first | exact @GlobalTheory.CovDomGrp.isUn_iff_mem_isom | exact GlobalTheory.CovDomGrp.isUn_iff_mem_isom | (intros; apply GlobalTheory.CovDomGrp.isUn_iff_mem_isom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrime
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.RowPerpMass

theorem main : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (Lat.Tu D u).Prime → Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) → ∀ Λ : Cnt.LatV D, IsRowLat D F0 Λ → mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) = Cnt.massS D D.R.k * ((((Lat.Tu D u : ℕ) : ℝ) ^ D.R.k - 1) / (((Lat.Tu D u : ℕ) : ℝ) - 1)) ^ D.R.f ∧ Cnt.massS D D.R.k * Cnt.NT D u ^ (D.R.k - 1) ≤ mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) := by
  intro D u F0 he hz hp hs Λ hΛ
  let := D.host.cmStar
  obtain ⟨⟨hPD, hrk⟩, hL⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hInt, hdisc⟩ := hL Λ hΛ
  obtain ⟨hsym, hortho, hpos, -, -⟩ := _root_.GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram D.R.k
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega

  have hf : fDeg D.host.E = D.R.f := by
    have : NumberField.IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
    have h2 := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
    have h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0 :=
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
    have h4 : fDeg D.host.E = NumberField.InfinitePlace.nrRealPlaces D.host.E +
        NumberField.InfinitePlace.nrComplexPlaces D.host.E :=
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
    show _ = 2 * D.R.ord
    omega
  have hmass := GlobalTheory.Mass.CyclicDisc.main _root_.GlobalTheory.Mass.MaxFormula.main D.host.E (D.sp.X 0).V (D.sp.X 0).hT
    D.sp.cm.cmUnram (D.sp.X 0).herm hPD (by rw [hrk]; exact hk) (Fin D.R.k → D.host.E)
    (Cnt.stdH D.host.E D.R.k) hsym (Cnt.stdLat D.host.E D.R.k) (by rw [hrk]; exact hortho)
    (Lat.Tu D u) hp hs _ hInt hdisc
  rw [hrk, hf] at hmass
  have hS : mass (Cnt.stdH D.host.E D.R.k) (Cnt.stdLat D.host.E D.R.k) = Cnt.massS D D.R.k := rfl
  rw [hS] at hmass
  refine ⟨hmass, ?_⟩
  rw [hmass]

  have hT2 : (2 : ℝ) ≤ (Lat.Tu D u : ℝ) := by exact_mod_cast hp.two_le
  have hgeom : (Lat.Tu D u : ℝ) ^ (D.R.k - 1) ≤ ((Lat.Tu D u : ℝ) ^ D.R.k - 1) / ((Lat.Tu D u : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    have e : (Lat.Tu D u : ℝ) ^ D.R.k = (Lat.Tu D u : ℝ) * (Lat.Tu D u : ℝ) ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : (1 : ℝ) ≤ (Lat.Tu D u : ℝ) ^ (D.R.k - 1) := one_le_pow₀ (by linarith)
    rw [e]; nlinarith
  have hNT : Cnt.NT D u ^ (D.R.k - 1) = ((Lat.Tu D u : ℝ) ^ (D.R.k - 1)) ^ D.R.f := by
    show (((D.mem u).A.T : ℝ) ^ D.R.f) ^ (D.R.k - 1) = _
    rw [← pow_mul, ← pow_mul, mul_comm]; rfl
  rw [hNT]
  have hm : 0 ≤ Cnt.massS D D.R.k := hpos.le
  gcongr

end GlobalTheory.Mass.RowPerpMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLatticeClassesFiniteLocalOrbits
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.ClFin

theorem classes_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite ∧ ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  have hpos := _root_.GlobalTheory.ComplPos.complement_totPos D X Y u u' F F' w hw hG
  refine ⟨_root_.GlobalTheory.StabFin.stab_finite D F F' hpos Λ₀ hΛ₀, ?_⟩
  obtain ⟨N, hN, hNs⟩ := GlobalTheory.T.orbitLattice_between_frameAndComplementParts D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  obtain ⟨d, c, hd, hc, hdc⟩ := _root_.GlobalTheory.CompScale.scale_dual D X Y u u' F F' w hw hG Z FP hB hR Λ₀ (by first | exact hΛ₀ | exact hΛ₀.toIsLattice)
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.LatClassFin.classes_fin D F F' hpos (Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F')) N d c hN hd hc
  exact ⟨S, fun Λ hΛ hloc => hS Λ hΛ (_root_.GlobalTheory.FrameSpanLat.inf_span_eq D X Y u u' F F' w hw hG Z FP hB hR Λ₀ (by first | exact hΛ₀ | exact hΛ₀.toIsLattice) Λ hΛ hloc)
    (hNs Λ hΛ hloc) (hdc Λ hΛ hloc).1 (hdc Λ hΛ hloc).2⟩

end GlobalTheory.Unfold.ClFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots
section
noncomputable section

open Matrix Formalism.MainNotions.S
open scoped Classical

namespace GlobalTheory.LoopAct

variable {n m : ℕ}

def IsMatOn (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin m → Fin n → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ b, g *ᵥ f b = ∑ c, M c b • f c

theorem isMatOn_mul {g h : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {M₁ M₂ : Matrix (Fin m) (Fin m) ℂ}
    (hg : IsMatOn g f M₁) (hh : IsMatOn h f M₂) : IsMatOn (g * h) f (M₁ * M₂) := by
  intro b
  rw [← Matrix.mulVec_mulVec, hh b, Matrix.mulVec_sum]
  have e : ∀ c, g *ᵥ (M₂ c b • f c) = ∑ d, (M₂ c b * M₁ d c) • f d := by
    intro c
    rw [Matrix.mulVec_smul, hg c, Finset.smul_sum]
    exact Finset.sum_congr rfl fun d _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem isMatOn_unique {g : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {M₁ M₂ : Matrix (Fin m) (Fin m) ℂ}
    (hf : LinearIndependent ℂ f) (hM : IsMatOn g f M₁) (hN : IsMatOn g f M₂) : M₁ = M₂ := by
  ext c b
  have h : ∑ d, (M₁ d b - M₂ d b) • f d = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← hM b, ← hN b, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hf _ h c)

theorem isMatOn_conj {g P Pi : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hg : IsMatOn g (fun j => P *ᵥ f j) A) (hP : Pi * P = 1) : IsMatOn (Pi * g * P) f A := by
  intro b
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg b, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]

variable {N : ℕ}

theorem stabU_mul {Z a b : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det) (ha : a ∈ GlobalTheory.LoopV.stabU Z)
    (hb : b ∈ GlobalTheory.LoopV.stabU Z) : a * b ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul ha.1 hb.1, ?_⟩
  have e : Z * (a * b) * Z⁻¹ = (Z * a * Z⁻¹) * (Z * b * Z⁻¹) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hZ]
  rw [e]
  exact Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_mul ha.2 hb.2

theorem stabU_inv {Z a : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det) (ha : a ∈ GlobalTheory.LoopV.stabU Z) :
    a⁻¹ ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨(Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv ha.1).1, ?_⟩
  have hai := Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv ha.1
  have e : Z * a⁻¹ * Z⁻¹ = (Z * a * Z⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hZ, Matrix.mul_assoc]
  rw [e]
  exact (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv ha.2).1

theorem stabU_map_eq_ofRoots {K : Type} [Field K] (ψ : K →+* ℂ) (p : Point K N) (x : Matrix (Fin N) (Fin N) ℂ)
    (hx : x ∈ GlobalTheory.LoopV.stabU ((ptMat p).map ψ)) :
    x = GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (fun q => x q.1.1 q.1.2) := by
  obtain ⟨σ, d, hd, hw⟩ := GlobalTheory.LoopV.Cell.ptMat_monomial p
  have hd' : ∀ i, ψ (d i) ≠ 0 := fun i => (map_ne_zero ψ).2 (hd i)
  have hw' : ∀ i j, (ptMat p).map ψ i j = if j = σ i then ψ (d i) else 0 := by
    intro i j; rw [Matrix.map_apply, hw]; split_ifs <;> simp
  ext a b
  unfold GlobalTheory.LoopV.ofRoots
  by_cases hr : (a, b) ∈ GlobalTheory.LoopV.roots (ptMat p)
  · rw [dite_eq_left hr]
  · rw [dite_eq_right hr]
    rcases lt_trichotomy a b with hab | rfl | hab
    · rw [if_neg hab.ne]
      have hσ : σ.symm a < σ.symm b := by
        rw [GlobalTheory.LoopV.Cell.mono_roots hd hw] at hr
        push_neg at hr
        rcases (hr hab).lt_or_eq with h | h
        · exact h
        · exact absurd (σ.symm.injective h) hab.ne
      have h0 := (hx.2 (σ.symm a) (σ.symm b)).1 hσ
      rw [GlobalTheory.LoopV.Cell.mono_conj hd' hw'] at h0
      simp only [Equiv.apply_symm_apply, mul_eq_zero, inv_eq_zero, hd', false_or, or_false] at h0
      exact h0
    · rw [if_pos rfl]; exact (hx.1 a a).2 rfl
    · rw [if_neg hab.ne']; exact (hx.1 a b).1 hab

end GlobalTheory.LoopAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepPinExistsAndFormNGC
section
namespace GlobalTheory

theorem stepPinExists_and_formNGC :
    Formalism.L2.SG.NGAnalytic.StepPinExists ∧ Formalism.L2.SG.NGVanish.FormNGC :=
  ⟨Formalism.L2.SG.NGPin.stepPinExists, Formalism.L2.SG.Pf.formNGC_holds⟩

end GlobalTheory
end

