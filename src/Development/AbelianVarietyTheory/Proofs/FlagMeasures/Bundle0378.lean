module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0209
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFromLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0369
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRowsFixedByLabelTupleOpOfSumFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabFix

theorem mem_VT_of_sum_fixed : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf), IsRedHom X red → IsSec X red sec → ∀ (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) → ∀ f ∈ HHX X, ∑ᶠ γ, serCoef t γ • X.B.R ((1, sec γ) : X.B.I.GA) f = f → f ∈ VT X t := by
  intro D X red sec hred hsec t ht f hf hsum
  classical
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  let ρ : GlobalTheory.RowLev.Red X.B.I X.B.g (G0g D.nd) :=
    { toFun := red, map_mul := hred.2.1, ker := hred.2.2.2, surj := hred.2.2.1 }
  obtain ⟨hcoef, hcent⟩ := GlobalTheory.LabIdem.ES_single_coeff_central D t ht
  have hegA : egA X (ES {t}) = ρ.lift X.B.μf (ES {t}) := by
    funext x
    rw [egA, GlobalTheory.coeff_chosenRed_eq_redHom D X red hred _ hcent x]
    by_cases hx : x ∈ X.B.I.Kset
    · rw [if_pos hx, GlobalTheory.RowLev.Red.lift_of_mem ρ _ _ hx]
    · rw [if_neg hx, GlobalTheory.RowLev.Red.lift_of_notMem ρ _ _ hx]
  obtain ⟨h1R, hm, hn, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  obtain ⟨huniq, -, -, hprod, -⟩ := GlobalTheory.WeakConv.rightConv_unique_add_smul_mul_comm X.B.I X.B.μf X.B.fund X.B.R
    X.B.fund_spec X.B.R_spec
  obtain ⟨hQ, -, -, -, -, hinfl, -, -, -⟩ := GlobalTheory.InflBasic.inflation_basic X.B.I X.B.g (G0g D.nd) ρ X.B.μf hg
  letI : Fintype (G0g D.nd) := Fintype.ofFinite _
  obtain ⟨hlint, hlloc, -⟩ := hinfl (ES {t})
  obtain ⟨Ta, hTa⟩ := (GlobalTheory.AutInst_exists_isRConvF_and_isRConv X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R
    X.B.R_spec).1 _ hlint
  have he := X.B.e_adm
  have hecont : Continuous X.B.e := he.1.continuous
  have hReRe : X.B.Re.comp X.B.Re = X.B.Re := by
    have h := hprod _ _ _ _ hecont hecont X.B.Re_spec X.B.Re_spec
    rw [he.2.1] at h
    exact huniq _ _ _ h X.B.Re_spec
  have hRT : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) (X.B.Re.comp Ta) := by
    unfold eT
    rw [hegA]
    exact hprod _ _ _ _ hecont hlloc.continuous X.B.Re_spec hTa
  have hReT : ReT X {t} = X.B.Re.comp Ta := by
    have hex : ∃ T, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) T := ⟨_, hRT⟩
    unfold ReT
    rw [dite_eq_left hex]
    exact huniq _ _ _ (Classical.choose_spec hex) hRT
  obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hf
  have hRef : X.B.Re f = f := by
    rw [← hz]
    show X.B.Re (X.B.Re (X.Rph z)) = X.B.Re (X.Rph z)
    rw [← ContinuousLinearMap.comp_apply X.B.Re X.B.Re, hReRe]
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := h1R
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b
    rw [ContinuousLinearMap.mul_def, ← hm]
    simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => hn _ v
  have hone : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
    refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, X.B.I.Lf.zero_mem, ?_⟩⟩
    have : X.B.I.fmat 1 = 1 := rfl
    simp [this]
  haveI : SecondCountableTopology X.B.I.Gf := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints X.B.I
  have hfix : ∀ k ∈ X.B.I.Kg X.B.g, X.B.R (1, k) f = f := by
    intro k hk
    have h := GlobalTheory.IdemProj.op_fixed X.B.μf (fun g => X.B.R (1, g)) p1 pm pn X.B.e X.B.Re X.B.Re_spec.2 k
      (fun x => by simpa using he.2.2.2.2.2.1 x k hk 1 hone)
    rw [← hRef, ← ContinuousLinearMap.comp_apply]
    exact DFunLike.congr_fun h f
  have hTaf : Ta f = f := by
    apply ext_inner_left ℂ
    intro v
    rw [hTa.2, GlobalTheory.LevelIdem.integral_lift ρ X.B.μf hg (ES {t}) sec hsec (fun x => ⟪v, X.B.R (1, x) f⟫_ℂ) ?_]
    · conv_rhs => rw [← hsum]
      rw [finsum_eq_sum_of_fintype, inner_sum]
      simp only [inner_smul_right, hcoef]
    · intro x k hk
      show ⟪v, X.B.R (1, x * k) f⟫_ℂ = ⟪v, X.B.R (1, x) f⟫_ℂ
      rw [show ((1 : X.B.I.Ginf), x * k) = ((1, x) : X.B.I.GA) * (1, k) by simp, hm,
        ContinuousLinearMap.comp_apply, hfix k hk]
  refine Submodule.mem_inf.2 ⟨hf, ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  show ReT X {t} f = f
  rw [hReT, ContinuousLinearMap.comp_apply, hTaf, hRef]

end GlobalTheory.LabFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PlExists
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB GlobalTheory.ThA Finset NumberField MeasureTheory Formalism.QuantumDeterminants Matrix

namespace GlobalTheory.ThA

theorem plExists : PlExists := by
  obtain ⟨Cb, -, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs ν' m₀ l0 hl1 hl2 hk hW hW' hN hF hP

  obtain ⟨T, hz, hz', hπ, hπ', hTn⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  have ez : (T.bs 0).z = Bs.z := hz
  have ez' : (T.bs 0).z' = Bs.z' := hz'
  have eπ : (T.bs 0).π = Bs.π := hπ
  have eπ' : (T.bs 0).π' = Bs.π' := hπ'

  let T' : D.LevTower P.k P.r Wp Wq :=
    { bs := fun j => Nat.rec (motive := fun j => B.RealPlaceData P.k (P.r - j) Wp Wq) Bs (fun n _ => T.bs (n + 1)) j
      z_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z_lev 0 hj
          rw [ez] at h0
          exact h0
        | succ n => exact (T.z_lev (n + 1) hj).trans ez
      z'_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z'_lev 0 hj
          rw [ez'] at h0
          exact h0
        | succ n => exact (T.z'_lev (n + 1) hj).trans ez'
      π_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π_lev 0 hj y
          rw [eπ] at h0
          exact h0
        | succ n => exact (T.π_lev (n + 1) hj y).trans (congrFun eπ _)
      π'_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π'_lev 0 hj y
          rw [eπ'] at h0
          exact h0
        | succ n => exact (T.π'_lev (n + 1) hj y).trans (congrFun eπ' _) }
  have hT'n : D.TowerNormalised T' := by
    intro j hj
    cases j with
    | zero => exact ⟨hW, hW', hN⟩
    | succ n => exact hTn (n + 1) hj

  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP
  obtain ⟨L, st, hXL, hQQ, hq, hinv, hstar, hstart⟩ :=
    Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP X l0
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k P.r Wp Wq Bs
  have hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 :=
    ⟨hP, hμ.1, hXL, hQQ, hq, hinv, hstar, hstart⟩
  obtain ⟨Θ, hΘ1, hΘ2⟩ := hTL Wp Wq P Bs X μ L st l0 hl1 hl2 hD

  obtain ⟨he1, he2, he3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts Bs ν' m₀ hF
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' (m₀ *ᵥ ν') hP he1 he2 he3
  exact ⟨⟨l0, T', ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hT'n, hF, hP, ⟨X, μ, L, st, hD, hΘ1⟩⟩, rfl, rfl, rfl, rfl, hΘ2⟩

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFunctionBlockExistsOfBesselCoef
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.WBlockExists

theorem nUnimodLoc : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  intro k r ε e f wf z0 z c hF hc hz
  exact n_unimodular_local k r ε e f wf z0 z c
    ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem realPlaceFunctionBlockExists_of_bessel_coef : BesselNVGap → CoefWeightedLoc → ∀ D : D7, GlobalTheory.St.WBlkExists D :=
  by
    intro hB hCW D hG A L Ps Rf Bu Pi Mu
    obtain ⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ := A
    exact Formalism.L2.SG.Pf.WFL.wblk_core quotient_product_compact
      Formalism.L2.SG.Pf.WFL.locHNProps_holds nUnimodLoc
      Formalism.L2.SG.Pf.WuDec.integrable_and_integral_pi_apply hB hCW
      GlobalTheory.wlocExists_real (GlobalTheory.GapAtRealPlaces.gapBigOfGapHyp D)
      hG I ιE ιE_conj ιE_F bas J_eq L_eq pl φ_eq n_eq eps_eq L Ps Rf Bu Pi Mu

end GlobalTheory.WBlockExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StMatIntIff
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StIntLat

theorem stMat_int_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ y : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ, (∃ x ∈ G.K0, y = fun v p => Formalism.L2.SG.Pf.VolPinAsm.phiV X v (GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2)) ↔ ∀ p : Formalism.L2.SG.RealObj.FreeE w, (fun v => y v p) ∈ ((((ddS D ^ (-(((p.1.2.val - p.1.1.val : ℕ)) : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup).map (Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) 1)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c y
  have hT : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u').ne'
  have hli : LinearIndependent D.host.E G.f' := by
    have h0 : LinearIndependent D.host.E (frame F'0) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F'0.fl hT
    have h1 := h0.map' (c.e : (VS D).V →ₗ[D.host.E] G.V) c.e.ker
    have e : G.f' = (c.e : (VS D).V →ₗ[D.host.E] G.V) ∘ frame F'0 := by
      funext a; exact c.f'_eq a
    rw [e]; exact h1
  have hStCo := _root_.GlobalTheory.HL.StCoord.stab_coords D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hK := _root_.GlobalTheory.HL.StabIntCoord.integralStabiliser_iff_rational_coords_alt D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hexp : ∀ a b : Fin (D.R.rS + 1), a < b →
      (-(((b.val - a.val : ℕ)) : ℤ)) = -((b : ℤ) - (a : ℤ)) := by
    intro a b hab
    have : a.val ≤ b.val := le_of_lt hab
    rw [Nat.cast_sub this]
  constructor
  · rintro ⟨x, hx, rfl⟩ p
    have hxSt : x ∈ G.St := by
      intro q
      obtain ⟨g', hg', he⟩ := hx q
      exact ⟨g', hg'.1.1, he⟩
    obtain ⟨B, -, hB, -⟩ := hStCo.1 x hxSt
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hB⟩
    have hmem := (hK x hxSt _ hspec).1 hx p.1.1 p.1.2 p.2.1
    refine ⟨GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2, ?_, ?_⟩
    · rw [hexp _ _ p.2.1]; exact hmem
    · funext v; simp [Formalism.L2.SG.NGCut.SplitEmbedding.embS]
  · intro h
    choose lam hlam hlamE using h
    let B : Formalism.L2.SG.PairVal.MatR D := fun a b =>
      if a = b then 1 else if hab : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
        then lam ⟨(a, b), hab⟩ else 0
    have hBU : IsUpUni B := by
      intro i j
      refine ⟨fun hji => ?_, fun hij => ?_⟩
      · have h1 : i ≠ j := fun h => (lt_irrefl j) (h ▸ hji)
        have h2 : ¬ (i < j ∧ Formalism.L2.SG.RealObj.blkOf w.1 i.1 = Formalism.L2.SG.RealObj.blkOf w.1 j.1) := fun h => (lt_asymm hji) h.1
        simp only [B, if_neg h1, dif_neg h2]
      · simp only [B, if_pos hij]
    have hBblk : ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 →
        B a b = 0 := by
      intro a b hne
      have h1 : a ≠ b := fun h => hne (h ▸ rfl)
      have h2 : ¬ (a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1) := fun h => hne h.2
      simp only [B, if_neg h1, dif_neg h2]
    obtain ⟨x, ⟨hxSt, hxB⟩, -⟩ := hStCo.2 B hBU hBblk
    have hxK : x ∈ G.K0 := by
      refine (hK x hxSt B hxB).2 fun a b hab => ?_
      have h1 : a ≠ b := ne_of_lt hab
      by_cases h2 : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
      · simp only [B, if_neg h1, dif_pos h2]
        have := hlam ⟨(a, b), h2⟩
        rw [hexp _ _ hab] at this
        exact this
      · simp only [B, if_neg h1, dif_neg h2]
        exact FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hxB⟩
    have hM : GlobalTheory.HL.TraceConjugationCover.stMat G x = B := by
      funext a b
      have e2 : ∑ d, (GlobalTheory.HL.TraceConjugationCover.stMat G x d b - B d b) • G.f' d = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, ← hspec b, ← hxB b, sub_self]
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ e2 a)
    refine ⟨x, hxK, ?_⟩
    funext v p
    have e1 := congrFun (hlamE p) v
    simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at e1
    rw [hM, ← e1]
    have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
    simp only [B, if_neg h1, dif_pos p.2]
    all_goals first | rfl | (congr 1)

end GlobalTheory.HL.StIntLat
end

