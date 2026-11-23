module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralStabiliserNormalisedHaar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsTermAutomorphismsEqMovedStabilizer
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructure
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationLabelsNormalisedOfRowsTypesLevels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0059
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0011
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKF0IffGapIn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphismCovolumeEqLatticeMass
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovMass

variable {D : D7} (X : HidaSetting D)

noncomputable def realPt (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : X.B.I.Ginf :=
  (Classical.choose ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1

theorem realPt_spec {γ : Formalism.HermitianLatticesTheory.isom (VS D).hT} {x : X.B.I.GA} (h : RatLink X x γ.1) : realPt X γ = x.1 := by
  have hs := Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)
  unfold realPt
  rw [hs.2 x h]

theorem realPt_link (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : ∃ x : X.B.I.GA, RatLink X x γ.1 ∧ realPt X γ = x.1 :=
  ⟨_, (Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1, rfl⟩

noncomputable def realPtHom : Formalism.HermitianLatticesTheory.isom (VS D).hT →* X.B.I.Ginf where
  toFun := realPt X
  map_one' := by
    obtain ⟨x, hx, e⟩ := realPt_link X 1
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x x _ _ hx hx)
    have h2 := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x (x⁻¹) _ _ hx h.2.1).1
    have h3 : RatLink X (x * x⁻¹) (1 : Formalism.HermitianLatticesTheory.isom (VS D).hT).1 := by simpa using h2
    rw [realPt_spec X h3]; simp
  map_mul' := by
    intro γ δ
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    obtain ⟨y, hy, ey⟩ := realPt_link X δ
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).1
    rw [realPt_spec X (γ := γ * δ) h, ex, ey]; rfl

theorem realPtHom_injective : Function.Injective (realPtHom X) := by
  intro γ δ h
  obtain ⟨x, hx, ex⟩ := realPt_link X γ
  obtain ⟨y, hy, ey⟩ := realPt_link X δ
  have h' : x.1 = y.1 := by rw [← ex, ← ey]; exact h
  exact Subtype.ext (((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).2.2 h')

theorem realPts_eq_map (H : Subgroup ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (hH : H ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    realPts X (H : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = ((H.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (realPtHom X) : Set X.B.I.Ginf) := by
  ext y
  constructor
  · rintro ⟨x, n, hx, rfl, hn⟩
    exact ⟨⟨n, hH hn⟩, hn, realPt_spec X (γ := ⟨n, hH hn⟩) hx⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    exact ⟨x, γ.1, hx, ex, hγ⟩

theorem realPts_countable (S : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) : (realPts X S).Countable := by
  have := Formalism.L2.SG.TermOp.Vanish.countable_nf X.B.I.E
  have hsub : realPts X S ⊆ ⋃ M : Fin X.B.I.n → Fin X.B.I.n → X.B.I.E,
      {y : X.B.I.Ginf | ∀ v, uMat (y v) = (X.B.I.P v)⁻¹ * (Matrix.of M).map (X.B.I.φ v) * X.B.I.P v} := by
    rintro _ ⟨x, n, ⟨M, -, h1, -⟩, rfl, -⟩
    exact Set.mem_iUnion.2 ⟨fun i j => (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) i j, h1⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun M => Set.Subsingleton.countable ?_)
  intro y hy y' hy'
  funext v
  exact Subtype.ext (Units.ext ((hy v).trans (hy' v).symm))

end GlobalTheory.CovMass

theorem GlobalTheory.CovMass.covol_eq_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∀ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ ROinf t₀ ∧ s * y ∈ K) → (μR K).toReal = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat ρ t₀.lam) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin K hK
  obtain ⟨hKm, hKu⟩ := hK
  have hlink := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hgrp := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hterm := (_root_.GlobalTheory.HL.MovedTermPhase.main D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).1
  obtain ⟨KA, ⟨hKAm, hKAu⟩, hKA⟩ :=
    _root_.GlobalTheory.HL.Cov0.covolume_integralStabiliser_normalisedHaar_alt D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin
  have hRO := _root_.GlobalTheory.RoEq.roinf_eq_realPts D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  obtain ⟨hfin1, hfin2⟩ := GlobalTheory.T.latticeStabiliser_commensurable_integralPoints (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ _ G hk (c.lat ρ t₀.lam) (by first | exact GlobalTheory.HL.ProdStruct.full_lattice_of_term G hterm | exact hterm.1)

  let cj : ((VS D).V ≃ₗ[D.host.E] (VS D).V) →* G.GLV :=
    { toFun := c.grp ρ
      map_one' := by ext x; simp [GlobalTheory.HL.GCoord.grp]
      map_mul' := by intro m n; ext x; simp [GlobalTheory.HL.GCoord.grp] }
  have hcj : ∀ n, cj n = c.grp ρ n := fun _ => rfl
  have hcjs : Function.Surjective cj := fun x => hgrp.2.2.2.1 ρ x
  have hconj : ∀ n, c.grp (ρ * t₀.lin) (t₀.lin⁻¹ * n * t₀.lin) = c.grp ρ n := by
    intro n
    have h1 : ∀ y, t₀.lin (t₀.lin⁻¹ y) = y := fun y => by
      show (t₀.lin * t₀.lin⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    have h2 : ∀ z, t₀.lin ((ρ * t₀.lin).symm z) = ρ.symm z := fun z => by
      rw [LinearEquiv.eq_symm_apply]; exact (ρ * t₀.lin).apply_symm_apply z
    ext x
    simp only [GlobalTheory.HL.GCoord.grp, LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.symm_trans_apply, h1, h2]

  have hStN : ∀ g, g ∈ G.St → g ∈ G.N := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').1, he⟩
  have hStN' : ∀ g, g ∈ G.St → g ∈ G.N' := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').2, he⟩
  have hK0St : G.K0 ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1.1, he⟩
  have hLSt : G.stabL (c.lat ρ t₀.lam) ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1, he⟩
  have hStI : G.St.comap cj ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn =>
    ((hgrp.1 n).2 (hStN _ hn)).1
  set P := G.K0.comap cj with hP
  set Q := (G.stabL (c.lat ρ t₀.lam)).comap cj with hQ
  have hPI : P ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hK0St hn)
  have hQI : Q ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hLSt hn)
  set A := (P.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hA
  set B := (Q.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hB
  have hAset : (A : Set X.B.I.Ginf) = realPts X {σ | c.grp ρ σ ∈ G.K0} :=
    (GlobalTheory.CovMass.realPts_eq_map X P hPI).symm
  have hBset : (B : Set X.B.I.Ginf) = Formalism.L2.SG.TermOp.ROinf t₀ := by
    rw [hRO]; exact (GlobalTheory.CovMass.realPts_eq_map X Q hQI).symm
  have hAmem : ∀ y, y ∈ A ↔ y ∈ realPts X {σ | c.grp ρ σ ∈ G.K0} := fun y => by
    rw [← hAset]; rfl
  have hBmem : ∀ y, y ∈ B ↔ y ∈ Formalism.L2.SG.TermOp.ROinf t₀ := fun y => by
    rw [← hBset]; rfl

  obtain ⟨γw, s, s', μw, hγw, hs, hs', hdec, hμwH, hμwS, hμR⟩ := hPin
  have hH := Formalism.L2.SG.Pf.VolPinAsm.pinned_haar t₀ w γw s s' μw hs hs' hdec hμwH
  rw [← hμR] at hH
  have hAR : ∀ y ∈ A, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := by
    intro y hy
    obtain ⟨x, n, hx, rfl, hn⟩ := (hAmem y).1 hy
    have hnS : c.grp ρ n ∈ G.St := hK0St hn
    refine ⟨((hlink.2.2 u x n hx).1).1 ((hgrp.1 n).2 (hStN _ hnS)), ?_⟩
    have hm : t₀.lin⁻¹ * n * t₀.lin ∈ NRat (lf D (X.Fu u')) :=
      (hgrp.2.1 _).2 (by rw [hconj]; exact hStN' _ hnS)
    have hl : RatLink X (t₀.pt⁻¹ * x * t₀.pt) (t₀.lin⁻¹ * n * t₀.lin) :=
      (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ t₀.rep.2.1 t₀.rep.2.1).2.1 hx).1 t₀.rep.2.1).1
    have h2 := ((hlink.2.2 u' _ _ hl).1).1 hm
    simpa [Prod.fst_mul, Prod.fst_inv] using h2
  have hBR : ∀ y ∈ B, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := fun y hy =>
    Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset t₀ ((hBmem y).1 hy)
  haveI hCA : Countable A := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.K0}).to_subtype
    rw [← hAset] at this; exact this
  haveI hCB : Countable B := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.stabL (c.lat ρ t₀.lam)}).to_subtype
    rw [← hRO, ← hBset] at this; exact this

  have hiA : B.relIndex A = (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hPI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hiB : A.relIndex B = G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hQI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hcov := Formalism.L2.SG.Pf.CovolIdx.covol_commens μR (Formalism.L2.SG.TermOp.Vanish.Rset t₀) hH.2.2.1 A B
    (fun x hx => hH.2.2.2 x (hAR x hx)) (fun x hx => hH.2.2.2 x (hBR x hx))
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hAR x hx) hy)
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hBR x hx) hy) KA K hKAm hKm
    (fun y hy => by simpa only [hAmem] using hKAu y hy) (fun y hy => by simpa only [hBmem] using hKu y hy)
    (by rw [hiA]; exact hfin1) (by rw [hiB]; exact hfin2)
  rw [hiA, hiB, hKA] at hcov
  set a := (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 with ha
  set b := G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) with hb
  set gi : ℝ := ((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹ with hgi
  have hgi0 : 0 ≤ gi := by rw [hgi]; positivity
  have hbne : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hfin2
  have hKeq : μR K = ENNReal.ofReal gi * (a : ℝ≥0∞) / (b : ℝ≥0∞) := by
    rw [hcov, ENNReal.mul_div_cancel_right hbne (by simp)]
  rw [hKeq, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal hgi0]
  simp only [ENNReal.toReal_natCast]
  unfold GlobalTheory.HL.GFrames.mu GlobalTheory.HL.invVol
  rw [← ha, ← hb]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl Formalism.IndefR.principalLevelFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.Sat

theorem ties_at : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (F0 : ∀ u, Forms0 D u) (s : SAt R F eE F0) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r), StdPsi hF PY → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → GlobalTheory.LabPin.TypeLab D rep → GoodFTAll D → Formalism.MainNotions.S.AutTie D s.P.X.B s.P.X.pl ∧ RowDictTie s.P.X s.P.G s.S.hI.eHH ∧ GlobalTheory.LabPin.LabTie s.P.X s.S.hI.eHH := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F eE F0 s PY hF rep hP hiso hT hG
  exact ⟨s.S.autTie, s.S.rowTie,
    _root_.GlobalTheory.LabPinAt.labTie_at D s.P.X s.P.inst s.t PY hF G' Pl0 T A Ks R eE s.P.G s.S.j s.S.hI.eHH rep F hP s.P.pin s.S.rowPin s.rowJ
      s.see.levelMatchA hiso hT hG⟩

end GlobalTheory.Sat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientSmoothDecayCapelliEigen
section
open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory

theorem eigDec_of_isKFinCoefT_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  intro hH k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have hsm : PI.KFinSmooth := hH.1.1.2.2.1
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf
  obtain ⟨h1, h2⟩ := Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH.1 k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDG hgap hok hs
  refine ⟨h1, h2, fun y g hg => ?_⟩
  have hE := GlobalTheory.CapelliEigenvalue.capEig hsm GlobalTheory.capelliDiscreteSeriesInfChar k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg
  rw [(GlobalTheory.ThA.centredCapelli_forms_agree k r _ (y : ℂ) f).1, hE]
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatum
section
namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem exists_isStdOf (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hk : 1 ≤ k) (hsec : IsSection k r L.z L.z' μsec) :
    ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  obtain ⟨μG, hμG⟩ := P.unitary_group_haar_exists k r
  obtain ⟨χ, hχs, hχsupp, hχint⟩ := P.character_exists_alt
  have h1 := _root_.GlobalTheory.ThA.hcType_rep k r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  have h1' := _root_.GlobalTheory.ThA.hcType_rep k r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  have hW := _root_.GlobalTheory.ThA.haarW_twoSided_of_left k r L.z L.μW L.hz.1 L.hz.2 L.hμW.1 L.hμW.2
  have hW' := _root_.GlobalTheory.ThA.haarW_twoSided_of_left k r L.z' L.μW' L.hz'.1 L.hz'.2 L.hμW'.1 L.hμW'.2
  have hN := P.Dx2.MN.haar (k := k) r
  exact ⟨⟨L.z, L.z', L.π, L.π', μG, L.μW, D.muN k r, L.μW', μsec, χ, hk, L.hz.1, L.hz'.1, L.hz.2, L.hz'.2,
    h1.2.1, h1'.2.1, h1.2.2.2.1, h1'.2.2.2.1, h1.2.2.1, h1'.2.2.1, hμG, hW, hN, hW', hsec, hχs, hχsupp, hχint⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalAmplitudeEqLocalAmplitudesStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalAmplitude_eq_localAmplitudes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (R : ∀ p, LocNG.Reps (FP p)) (S1 : Finset (PlF D)) (Om : Finset {p // p ∈ S1}) (d : ∀ p : {p // p ∈ S1}, LocNG.Datum (FP p.1)), (∀ p, p ∉ S1 → (FP p).PrimeTo) → (∀ p, p ∈ Om ↔ ¬ (FP p.1).PrimeTo) → (∀ p : {p // p ∈ S1}, Over (FP p.1) (d p) (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1 t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u'))) → ∀ Q : Prop → Prop, ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ = ‖∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) else LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t))‖ := by
  first | exact @GlobalTheory.HL.AmpLoc.global_amp_local | exact GlobalTheory.HL.AmpLoc.global_amp_local | (intros; apply GlobalTheory.HL.AmpLoc.global_amp_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalRealDataFunctionsEquivariantContinuous
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem uh_mul {k r : ℕ} {a b : MatKR k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem b_eq_wT (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = wT C u τ (m * C.y τ) := by
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := uh_mul hm (C.y_mem τ)
  have hJ := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hmy
  have hex : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ :=
    ⟨Formalism.L2.SG.Pf.LocJEq.ujOf' _ hJ, rfl⟩
  unfold wT
  rw [dite_eq_left hex, Formalism.L2.SG.Pf.LocJEq.wloc_eq C hB u τ]
  have hc : Formalism.MainNotions.S.umat hex.choose = C.Q τ * (m * C.y τ) * C.Qi τ := hex.choose_spec
  rw [hc]
  unfold v0Of sigB
  rw [← Formalism.L2.SG.Pf.LocJEq.sig_mul τ (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hm)
    (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ (C.y_mem τ))]
  congr 2
  have e : C.Q τ * m * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ) = C.Q τ * m * (C.Qi τ * C.Q τ) * C.y τ * C.Qi τ := by
    simp only [Matrix.mul_assoc]
  rw [e, (C.isT τ).1, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem isSPsiEquiv_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {W F : MatKR k r → Wp}
    {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hW : IsSPsiEquiv z ψ π W)
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) : IsSPsiEquiv z ψ π F := by
  intro h hh n hn g hg
  have hhng : h * n * g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := uh_mul (uh_mul hh.1 hn.1) hg
  rw [hF _ hhng, hF g hg, Matrix.mul_assoc (h * n) g y, hW h hh n hn (g * y) (uh_mul hg hy), map_smul,
    smul_comm s (ψ n)]

theorem continuousOn_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {W F : MatKR k r → Wp} {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hW : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) :
    ContinuousOn F (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  have h1 : ContinuousOn (fun m : MatKR k r => s • W (m * y)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hW.comp (continuous_id.matrix_mul continuous_const).continuousOn fun m hm => uh_mul hm hy).const_smul s
  exact h1.congr hF

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), (locS hB u u' τ).Φ m = (1 : ℂ) • wT C u τ (m * C.y τ) :=
  fun m hm => by rw [one_smul]; exact b_eq_wT C hB u τ hm

theorem phi'_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      (locS hB u u' τ).Φ' m = sclOf hB u u' τ • wT C u' τ (m * C.y τ) :=
  fun m hm => by
    show sclOf hB u u' τ • bOf hB u' τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = _
    rw [b_eq_wT C hB u' τ hm]

theorem tie_of (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hc : ∀ u, ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)))
    (he : ∀ u, IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ)) :
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  ⟨isSPsiEquiv_transl 1 (C.y_mem τ) (he u) (phi_eq C hB u u' τ),
    isSPsiEquiv_transl _ (C.y_mem τ) (he u') (phi'_eq C hB u u' τ),
    continuousOn_transl 1 (C.y_mem τ) (hc u) (phi_eq C hB u u' τ),
    continuousOn_transl _ (C.y_mem τ) (hc u') (phi'_eq C hB u u' τ)⟩

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

theorem locS_phi_equiv_cont : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  fun D X θ C hB u u' τ _ =>
    tie_of C hB u u' τ (fun u => Formalism.L2.SG.Pf.LocF.local_continuity_all D X θ C u τ)
      (fun u => Formalism.L2.SG.Pf.EquivPf.local_equivalence_all D X θ C u τ)

end GlobalTheory.SlocTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtDlAlongFamilyGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.FamDlGap

theorem ptDl_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  have hA : GlobalTheory.GapIn.AmpKF0 := GlobalTheory.NoPr.Model.ampKF0_iff_gapIn.mp GlobalTheory.NoPr.Model.ampKF0_holds
  have hCC : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
  obtain ⟨C, hC⟩ := GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps hH hA hCC Cg cb Cu cT CT C0 C1
  refine ⟨C, 1000, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max m₀ 1)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, hm1, -, -, hrd, -⟩ := hx0 x hx i
  have hmm : m₀ ≤ ((Fm.D x i).R.m : ℝ) := (le_max_left _ _).trans hm1
  have hm1' : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := (le_max_right _ _).trans hm1
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hmm⟩
  intro hH0
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hH0

end GlobalTheory.FamDlGap
end

