module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0483
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLaw
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SourceLaw
variable {D : D7}

theorem omegaG_levelDatum_zero_indep_chars (a r t : ℕ) (ha : r ≤ a) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) {b : ℕ}
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaG (Lev.datY a r t 0 ha Pg ∅ P χ ξ Lev.Frm.B) χj y = omegaG (Lev.datY a r t 0 ha Pg ∅ P χ' ξ' Lev.Frm.B) χj y := by
  unfold omegaG
  rfl


open GlobalTheory.AdjDatumMove in
theorem levelDatum_target_under_sourceLevel_element (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (r t : ℕ) (ha : r ≤ T.rank) (hb : r ≤ S.rank) (hTS : T.rank ≤ S.rank) (ea : T.rank = r + 0 * t)
    (eb : S.rank = r + (0 + 1) * t)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D)
    (g : GA D S) (sg : finE S g ∈ St βS)
    (hG : ∀ PP ∈ Pg, redFn βS PP (finE S g) ∈ blockTri (blkOf r t))
    (hP : (fun PP : ↥Pg => upperLeftBlock hb (redFn βS PP.1 (finE S g))) ∈ P.H)
    (hQ : ∀ PP ∈ Q, redFn βS PP (finE S g) ∈ blockTri (blk2 T.rank)) (x : WO S T) :
    GlobalTheory.FinZeta.levDatum S T βS βT (Lev.datY T.rank r t 0 ha Pg ∅ P (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) Q m e
                 (actO S T g⁻¹ 1⁻¹ x) =
      ((((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (0 + 1),
            m PP (dBlk (blkOf r t) (i + 1) (redFn βS PP (finE S g))))⁻¹ *
          ∏ PP ∈ Pg, m PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ) *
        ∏ PP ∈ Q, (((m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hTS (redFn βS PP (finE S g))⁻¹)))⁻¹ : ℂˣ) : ℂ)) *
      GlobalTheory.FinZeta.levDatum S T βS βT (Lev.datY T.rank r t 0 ha Pg ∅ P (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) Q m e x := by
  have sg' : finE S g⁻¹ ∈ St βS := by rw [map_inv]; exact inv_mem sg
  have s1 : finE T (1 : GA D T)⁻¹ ∈ St βT := by rw [inv_one, map_one]; exact one_mem _
  have hγ : ∀ PP, redFn βS PP (finE S g⁻¹) = (redFn βS PP (finE S g))⁻¹ := fun PP => by rw [map_inv, redFn_inv sg]
  have h1' : ∀ PP, (redFn βT PP (finE T (1 : GA D T)⁻¹))⁻¹ = 1 := fun PP => by
    rw [inv_one, map_one, redFn_one, inv_one]
  unfold GlobalTheory.FinZeta.levDatum
  by_cases hx : IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x)
  · have h1 := red_actO S T βS βT sg' s1 hx.2
    have h2 : ∀ PP, redM PP (frMapAdj S T βS βT (actO S T g⁻¹ 1⁻¹ x)) =
        ((redFn βS PP (finE S g))⁻¹).val * redM PP (frMapAdj S T βS βT x) := fun PP => by
      rw [h1.2 PP, hγ PP, h1' PP, Units.val_one, Matrix.mul_one]
    have hq := omegaQ_mul hTS Q m (fun PP => (redFn βS PP (finE S g))⁻¹) (fun _ => 1) (fun PP hP => inv_mem (hQ PP hP))
      (fun PP => redM PP (frMapAdj S T βS βT x))
    simp only [inv_one, Units.val_one, Matrix.mul_one, map_one, mul_one] at hq
    have hm := GlobalTheory.ChainOnto.omegaG_levelP_move D T.rank S.rank r t 0 ha hb ea eb Pg P (fun _ => m) (fun _ => 1)
      (fun PP => redFn βS PP (finE S g)) hG hP (fun PP => redM PP (frMapAdj S T βS βT x))
    rw [if_pos hx, if_pos ⟨isHalf_actO' _ _ hx.1, h1.1⟩, funext h2, hq,
      omegaG_levelDatum_zero_indep_chars T.rank r t ha Pg P (fun _ _ => 1) (fun _ => m) (fun _ => 1) (fun _ => 1) m
        (fun PP => ((redFn βS PP (finE S g))⁻¹).val * redM PP (frMapAdj S T βS βT x)),
      omegaG_levelDatum_zero_indep_chars T.rank r t ha Pg P (fun _ _ => 1) (fun _ => m) (fun _ => 1) (fun _ => 1) m
        (fun PP => redM PP (frMapAdj S T βS βT x)), hm]
    ring
  · rw [if_neg hx, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    have e' := GlobalTheory.AdelicLatMove.actO_actO_inv S T g (1 : GA D T) x
    have h3 := isHalf_actO' g (1 : GA D T) h1
    have h4 := (red_actO S T βS βT sg (by rw [map_one]; exact one_mem _) h2).1
    rw [e'] at h3 h4
    exact hx ⟨h3, h4⟩

end GlobalTheory.SourceLaw

namespace GlobalTheory.SourceLaw


open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues in
set_option maxHeartbeats 1000000 in
theorem om_src_law {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ) (cμ cη : (AE D)ˣ →* Circle)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (h : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io) (κ : GA D (Vc D i))
    (hκ : κ ∈ Lev.levA (Vc D i) (levV R i t P m)) :
    ω (κ, 1) f = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • f := by
  classical
  obtain ⟨hC, -, -, -, hch, hW, -, hlv, -, -, -⟩ := h
  rw [GlobalTheory.FinZeta.isLevelVec_iff] at hlv
  obtain ⟨hvac, e, he, hth⟩ := hlv
  have hL := hC.lev
  have hκG : κ ∈ GfC (Vc D i) := (Subgroup.mem_inf.1 hκ).1
  have hκL : finE (Vc D i) κ ∈ lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m) := (Subgroup.mem_inf.1 hκ).2
  have sV : finE (Vc D i) κ ∈ St (R.βV i) := parLev_St hκL.1
  have sW : finE (Wc D i) 1 ∈ St (R.βW i) := by rw [map_one]; exact one_mem _
  have dV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)
  have dW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  have fV := (hL.βV i).choose_spec.1
  have fW := (hL.βW i).choose_spec.1
  have hch' := GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification R hL i t s cμ cη m hch
  have hres : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP) :=
    fun PP hP => hch'.1 PP (Finset.mem_union.1 hP)
  have hun := hch'.2.1 ((R.datWp i P).Pg ∪ R.Q t) (fun PP h => Finset.mem_union.2 h)
  have hvac1 := GlobalTheory.StepVecLaw.om_vac hW (D.sp.V_sig _) (D.sp.W_sig _)
    (fun τ => GlobalTheory.ZetaLaw.isCartanInv_one_of_onb (hC.models.BV i τ)) (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)) dV dW
    fV fW hvac he (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) hun.1 hun.2 hκG (one_mem _) sV sW
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : (Wc D i).rank ≤ (Vc D i).rank := by omega
  have hb : D.R.r ≤ (Vc D i).rank := (datV i R.Pg (R.Q t) P m).hr
  have hQ : ∀ PP ∈ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blk2 (Wc D i).rank) := fun PP hP => by
    rw [rW]; exact parLev_q hκL.1 hP
  have hlaw := levelDatum_target_under_sourceLevel_element (Vc D i) (Wc D i) (R.βV i) (R.βW i) D.R.r D.R.t (r_le_rank_Wc i) hb hr (by rw [rW]; ring)
    (by rw [rV]; ring) R.Pg (R.Q t) P m e κ sV (fun PP hP => parLev_g hκL.1 hP) hκL.2 hQ
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hfin := _root_.GlobalTheory.ThetaMove.om_theta_eq_smul D R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hW (cA D e) _ f₀ _ f
    (_root_.GlobalTheory.SchrTheta.isTheta_placeModel D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) dV dW (cA D e) hcc hinf f₀ hvac.2.theta) hth κ 1
    (_root_.GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) dV dW fV fW κ 1 sV sW) _ _ (Units.ne_zero _)
    hvac1 hlaw
  rw [hfin]
  congr 1
  have hd : Disjoint (R.datWp i P).Pg (R.Q t) := (_root_.GlobalTheory.levCh_unramified_places D T R.toLevCh A.μ0 hL t).1
  have hQf : ∀ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ *
      (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹ =
      (m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ := fun PP hP => by
    have h1 := (GlobalTheory.VecInv.TwoBlockDet.det_blocks (kP PP) _ _ 0 hr (redFn (R.βV i) PP (finE (Vc D i) κ))).1 (hQ PP hP)
    have e1 : dBlk (blk2 (Wc D i).rank) 1 (redFn (R.βV i) PP (finE (Vc D i) κ)) =
        dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ)) := by rw [rW]
    have e2 : upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹ = (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ)))⁻¹ :=
      extendOne_inv _ (hQ PP hP)
    rw [e2, map_inv, map_inv, inv_inv, h1, e1, map_mul, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel,
      one_mul]
  have hone : ∀ PP, m PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) 1))) = 1 := fun PP => by
    rw [map_one, redFn_one, map_one, map_one]
  unfold Lev.levChi levFn
  rw [extendOne_of_mem _ hκL.2]
  have hchi : (datV i R.Pg (R.Q t) P m).P.chi ⟨rTup (R.βV i) (datV i R.Pg (R.Q t) P m) (finE (Vc D i) κ), hκL.2⟩ =
      P.chi ⟨fun PP => upperLeftBlock hb (redFn (R.βV i) PP.1 (finE (Vc D i) κ)), hκL.2⟩ := rfl
  rw [hchi]
  simp only [IndefiniteRowSideFullHecke.TwistedLevelValues.datV, hone, mul_one]
  rw [← Units.coe_prod, ← Units.val_mul, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
  congr 1
  rw [Finset.prod_union hd]
  have hX2 : (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹) *
      ∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹ =
      (∏ PP ∈ R.Q t, m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl hQf, Finset.prod_inv_distrib]
  generalize (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹) = X2 at hX2 ⊢
  generalize (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹) = Z at hX2 ⊢
  obtain rfl : X2 = (∏ PP ∈ R.Q t, m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ * Z⁻¹ := by
    rw [← hX2, mul_inv_cancel_right]
  rw [Finset.prod_inv_distrib]
  simp only [zero_add]
  rw [show (R.datWp i P).Pg = R.Pg from rfl]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.SourceLaw

namespace GlobalTheory.SourceLaw

theorem sourceLevelLaw : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → SourceLevelLawC R F := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io h κ hκ Q
  have hf := om_src_law R F i t σ s P cμ cη m ω BW f₀ f c io h κ hκ
  obtain ⟨hC, -, -, -, -, hW, -, -, hpt, -, -⟩ := h
  exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ ω hC.models.inf hW _ _ _ _ f hpt κ
    (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ hf Q

end GlobalTheory.SourceLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteLevelDatumVector_transforms_by_levelCharacter : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i P), ω (1, k) f = levChi (Wc D i) (R.βW i) (R.datWp i P) k • f := by
  first | exact @GlobalTheory.ZetaLaw.zeta_law | exact GlobalTheory.ZetaLaw.zeta_law | (intros; apply GlobalTheory.ZetaLaw.zeta_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqIntegralCombinationOfMemCompletedLatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_eq_integralCombination_of_mem_completedLattice : ∀ {D : D7} {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Y : Fin n → Formalism.L2.Theta.AE D),
    (fun i => Formalism.IndefR.Datum.toEAf D (Y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B →
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, finPart D (Y i) = finPart D (∑ p, β p * incA D (b p i)) := by
  first | exact @GlobalTheory.LatExpand.finPart_eq_int_comb_of_mem_hatL | exact GlobalTheory.LatExpand.finPart_eq_int_comb_of_mem_hatL | (intros; apply GlobalTheory.LatExpand.finPart_eq_int_comb_of_mem_hatL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationOperatorReading
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem fmR_coordX_self {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank) :
    fmR A B (Formalism.L2.Ker.coordX l) l.1 = unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  rw [Finset.sum_eq_single l.2.1, Finset.sum_eq_single l.2.2]
  · simp; rfl
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; simp [hi]
  · simp

theorem fmR_coordX_ne {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (τ' : D.what₂.Tau) (h : τ' ≠ l.1) : fmR A B (Formalism.L2.Ker.coordX l) τ' = 0 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [h]; rfl

theorem fmR_I_coordX_self {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank) :
    fmR A B (I • Formalism.L2.Ker.coordX l) l.1 =
      cplxO (A.cart l.1) (B.cart l.1) (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2) := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  rw [Finset.sum_eq_single l.2.1, Finset.sum_eq_single l.2.2]
  · simp; rfl
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; simp [hi]
  · simp

theorem fmR_I_coordX_ne {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (τ' : D.what₂.Tau) (h : τ' ≠ l.1) : fmR A B (I • Formalism.L2.Ker.coordX l) τ' = 0 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [h]; rfl

theorem gq_add_smul {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z e : VCx ι a b) (t : ℝ) :
    gq c (z + t • e) = gq c z + t * gD c z e + t ^ 2 * gq c e := by
  have key : ∀ (k : ℝ) (p q : ℂ), k * ‖p + t • q‖ ^ 2 =
      k * ‖p‖ ^ 2 + t * (2 * (k * (p * conj q).re)) + t ^ 2 * (k * ‖q‖ ^ 2) := by
    intro k p q
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  unfold gq gD
  simp only [Pi.add_apply, Pi.smul_apply, key, Finset.sum_add_distrib, Finset.mul_sum]

theorem heisO_eq_exp_rd (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D}
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (w : VCx D.what₂.Tau S.rank T.rank) :
    heisO ψ S T (fockPt σ A B w) h x = Complex.exp (-((gq (fw D) w : ℂ) / 2)) * rd ψ σ A B h x w := by
  unfold rd
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

theorem heis_dRho_fock_eval (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D)
    (hψ : IsStdChar D ψ (-1)) (hC : GlobalTheory.FockCompare.Chart θ σ) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S)
    (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (z e : VCx D.what₂.Tau S.rank T.rank) (τ : D.what₂.Tau)
    (v : Matrix (Fin T.rank) (Fin S.rank) ℂ) (hv : fmR A B e τ = v) (h0 : ∀ τ', τ' ≠ τ → fmR A B e τ' = 0)
    (hd : DifferentiableAt ℝ (rd ψ σ A B h x) z) :
    heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ v h) x =
      Complex.exp (-((gq (fw D) z : ℂ) / 2)) *
        ((-((Real.pi : ℂ) * I) * (omF A B z e : ℂ) - (gD (fw D) z e : ℂ) / 2) * rd ψ σ A B h x z +
          fderiv ℝ (rd ψ σ A B h x) z e) := by
  rw [heis_dRho_fock D ψ θ σ hψ hC S T A B h x z e τ v hv h0]
  have hfun : (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * I) * ((t * omF A B z e : ℝ) : ℂ)) *
      heisO ψ S T (fockPt σ A B (z + t • e)) h x) = fun t : ℝ =>
      Complex.exp (-((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) - ((gq (fw D) z : ℂ) +
        (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2) * rd ψ σ A B h x (z + t • e) := by
    funext t
    rw [heisO_eq_exp_rd, gq_add_smul, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfun]
  have hline : HasDerivAt (fun t : ℝ => z + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have hRd : HasDerivAt (fun t : ℝ => rd ψ σ A B h x (z + t • e)) (fderiv ℝ (rd ψ σ A B h x) z e) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact this
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hP : HasDerivAt (fun t : ℝ => -((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) - ((gq (fw D) z : ℂ) +
        (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2)
      (-((Real.pi : ℂ) * I) * (omF A B z e : ℂ) - (gD (fw D) z e : ℂ) / 2) 0 := by
    have h1 := (hid.mul_const (omF A B z e : ℂ)).const_mul (-((Real.pi : ℂ) * I))
    have h2 := ((hid.mul_const (gD (fw D) z e : ℂ)).const_add (gq (fw D) z : ℂ)).add
      ((hid.pow 2).mul_const (gq (fw D) e : ℂ))
    have h3 := h1.sub (h2.div_const 2)
    convert h3 using 1
    all_goals first | rfl | (funext t; rfl) | simp
  have hD : HasDerivAt (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) -
      ((gq (fw D) z : ℂ) + (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2) *
        rd ψ σ A B h x (z + t • e)) _ 0 := hP.cexp.mul hRd
  rw [hD.deriv]
  simp
  ring

theorem rd_aPlusAll : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank S.rank) (z : VCx D.what₂.Tau S.rank T.rank), DifferentiableAt ℝ (rd ψ σ A B h x) z → rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z = (2 / (fockScale D l.1 : ℂ)) * GlobalTheory.FockTransl.Jet.crOp A B l (rd ψ σ A B h x) z := by
  intro D ψ θ σ hψ hC S T A B h x l z hd
  have h1 := heis_dRho_fock_eval D ψ θ σ hψ hC S T A B h x z (Formalism.L2.Ker.coordX l) l.1 _
    (fmR_coordX_self A B l) (fmR_coordX_ne A B l) hd
  have h2 := heis_dRho_fock_eval D ψ θ σ hψ hC S T A B h x z (I • Formalism.L2.Ker.coordX l) l.1 _
    (fmR_I_coordX_self A B l) (fmR_I_coordX_ne A B l) hd
  have hlin : heisO ψ S T (fockPt σ A B z)
      (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x =
      (fockScale D l.1 : ℂ)⁻¹ *
        (heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ l.1
            (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2) h) x -
          I * heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ l.1
            (cplxO (A.cart l.1) (B.cart l.1) (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2)) h) x) := by
    simp only [aPlusAll, aPlus, crea, heisO, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hexp : (Real.exp (gq (fw D) z / 2) : ℂ) * Complex.exp (-((gq (fw D) z : ℂ) / 2)) = 1 := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    simp
  have hrd : rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z =
      (Real.exp (gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z)
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x := rfl
  rw [hrd, hlin, h1, h2]
  unfold crOp lamF
  linear_combination (↑(fockScale D l.1))⁻¹ *
    ((-((Real.pi : ℂ) * I) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) - (gD (fw D) z (Formalism.L2.Ker.coordX l) : ℂ) / 2) *
        rd ψ σ A B h x z + fderiv ℝ (rd ψ σ A B h x) z (Formalism.L2.Ker.coordX l) -
      I * ((-((Real.pi : ℂ) * I) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ) -
        (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ) / 2) * rd ψ σ A B h x z +
        fderiv ℝ (rd ψ σ A B h x) z (I • Formalism.L2.Ker.coordX l))) * hexp +
    (↑(fockScale D l.1))⁻¹ * (Real.pi : ℂ) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ) * rd ψ σ A B h x z * I_sq

end GlobalTheory.FockTransl.Jet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandInvariantMemIntertwinedTypeSpanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariant_mem_intertwinedTypeSpan : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ (Y₀ : Submodule ℂ (GA D V → ℂ)) (τ : D.what₂.Tau) (k : ℕ),
    ∀ f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ),
      gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ) := by
  first | exact @GlobalTheory.KTypeGelf.gelf_mem_typeSpan | exact GlobalTheory.KTypeGelf.gelf_mem_typeSpan | (intros; apply GlobalTheory.KTypeGelf.gelf_mem_typeSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandInvariantsSymmetricOfDerivativeAdjointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariants_symmetric_of_derivativeAdjoint : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (A : Submodule ℂ (GA D V → ℂ)), A ≤ GlobalTheory.Mem.AutSpace.SmFun θ V →
    (∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A) → ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
    (∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) →
    ∀ k, ∀ x ∈ A, ∀ y ∈ A, b x (gelf θ V τ k y) = b (gelf θ V τ k x) y := by
  first | exact @GlobalTheory.GelfSymm.gelf_symm | exact GlobalTheory.GelfSymm.gelf_symm | (intros; apply GlobalTheory.GelfSymm.gelf_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteDatumOfHomLatticeCosetSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFiniteDatum_of_homLatticeCoset_selfDual : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {ε : Bool} {S T : GlobalTheory.Grid.Node D} {e : AE D}
    {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (c : GlobalTheory.Grid.Coset S T I) {f₀ f : WO S.V T.V → ℂ},
    GlobalTheory.Grid.IsVac ψ θ ε S T f₀ → IsSelfDualC S.V S.Λ → IsSelfDualC T.V T.Λ → IsIdemSum e P → I ≠ ⊥ →
    GlobalTheory.Grid.IsCosetVec ψ ε S T e I c f₀ f → GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  first | exact @GlobalTheory.Grid.isFinVec_of_isCosetVec | exact GlobalTheory.Grid.isFinVec_of_isCosetVec | (intros; apply GlobalTheory.Grid.isFinVec_of_isCosetVec <;> assumption)
end

