module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0690
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0088
public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPeriod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.Separate
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0085
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0081

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PairingOfPointsExpansion
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
section
open GlobalTheory.DefStep GlobalTheory.JetsOne GlobalTheory.ExpansionInvariance
private theorem last_functional_compatible {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T} (hL : L.Is μ0) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) :
    ∃ (c : ℂ) (s : GA D (G.V (.grid D.R.m D.R.m)) →* GA D (G.V (.top D.R.m))), (∀ h, stabilizerEmbedding G.sp.topDec h = s h) ∧
      LastOK (realAct W.θ S.N.fr (.top D.R.m)) Λ (realAct W.θ S.N.fr (.grid D.R.m D.R.m)) Λ' s (finEmb G.sp.topDec)
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m D.R.m))
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hdef := GlobalTheory.TopIntegral.isDefinite_last G
  haveI : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) := isCompact_iff_compactSpace.1 (Eqv.isCompact_GinfC hdef.1 hdef.2)
  obtain ⟨κ₀, k1, k2⟩ := exists_haar _ hdef
  obtain ⟨c, hc⟩ := GlobalTheory.TopIntegral.real_average W.θ_is S.N Λ Λ' κ₀
  obtain ⟨s, h1, h2, h3⟩ := GlobalTheory.TopIntegral.exists_orthogonal_summand_embedding_hom G.sp.topDec
  refine ⟨c, s, h2, hdef, posDef_grid hL le_rfl, fun g hg => realAct_fin _ _ _ hg, fun g hg => realAct_fin _ _ _ hg, h1, h3,
    fun z => (h2 _).symm.trans (GlobalTheory.RealType.Emb_fin _ z), fun k hk => h2 k ▸ GlobalTheory.RealType.Emb_mem_inf _ hk,
    fun u u' => ?_, fun κ a1 a2 u u' => ?_⟩
  · simp only [← h2]
    exact (GlobalTheory.TopIntegral.continuous_integrand W.θ_is S.N Λ Λ' u u').comp continuous_subtype_val
  · obtain rfl : κ = κ₀ := Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ₀
    simp only [← h2]
    exact hc u u'
private theorem pairing_of_points_expansion {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (c : ℂ) (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) (X : ∀ j, FinPt G (.top j))
    (Y : ∀ i, FinPt G (.grid i D.R.m)) :
    c * pairPts S τ X Y (Ψ (X 0)) (F (Y 0)) = τ.sum fun d a => a *
      GlobalTheory.JetsOne.pairP (V := fun j => G.V (.top j)) (V' := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.top j)))
        (Mo' := fun j => VV ℂ (wt G (.grid j D.R.m))) (colComp S d) (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x))
        (rowComp S d) (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹
          (funOf (listedWt G (.grid 0 D.R.m)) (F x))) D.R.m
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) X Y := by
  rw [pairPts, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine (mul_left_comm c (τ d) _).trans (congrArg (τ d * ·) ?_)
  exact (congrArg₂ (fun a b => (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) a b)
    (ptV_eq_chainTo (V := fun j => G.V (.top j)) (Mo := fun j => VV ℂ (wt G (.top j))) (colComp S d)
      (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x)) X D.R.m)
    (ptV_eq_chainTo (V := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.grid j D.R.m))) (rowComp S d)
      (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) (F x)))
      Y D.R.m)).symm
end
theorem _root_.GlobalTheory.T.twisted_pairing_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun ch => ∀ P : PolCol ch.G × PolRow ch.G, ∃ κ : ℂ, ∀ t a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M τ, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, defTot t ch.S.toGridChoice M (Finsupp.single P 1) τ (colFn ch a) (formTop ch t y) = κ * ch.S.classSum (ch.Phi a) β τ (psiC (ch.Psi a)) (ch.S.formC t y) := by
  intro hP hS
  obtain ⟨C0, H⟩ := Big.and hS (_root_.GlobalTheory.FirstRowLaw.first_row_invariant_under_twist hP hS)
  refine ⟨C0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc P => ?_⟩
  obtain ⟨hOK, h0⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi hsc
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨Λ0, hΛ0⟩ := GlobalTheory.JetsOne.col_real ch
  obtain ⟨Λ0', hΛ0'⟩ := GlobalTheory.JetsOne.form_real ch s.core.models.cX
  obtain ⟨Λ, rfl, hΛ⟩ := GlobalTheory.JetsOne.col_chain ch.S.toGridChoice hL P Λ0
  obtain ⟨Λ', rfl, hΛ'⟩ := GlobalTheory.JetsOne.row_chain ch.S.toGridChoice hL P Λ0'
  obtain ⟨c, σ, hσ, hlast⟩ := last_functional_compatible ch.S.toGridChoice hL (Λ D.R.m) (Λ' D.R.m)
  refine ⟨c, fun t a β hβ M τ hM hτ y => ?_⟩
  have hv := (hOK t a).vec β τ hτ
  obtain ⟨v1, v2⟩ := TermVolDef.isMeasDef_of_isTermVol ch.S.toGridChoice hL t _ β M hM
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.T.normalisedKernelExpansionSum_levelInvariant ch.S.toGridChoice hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hi.guard t)
    (Set.mem_univ t) hβ hτ hv (psiC (ch.Psi a)) (ch.S.formC t y)
  have hK0 : ∀ h : 0 < D.R.m, ch.S.levTop t (ch.Phi a) β 0 h = ch.G.Kplus := fun _ => rfl
  have key := GlobalTheory.JetsOne.glue (V := fun j => ch.G.V (.top j)) (V' := fun j => ch.G.V (.grid j D.R.m)) τ
    (fun d hd => hΛ t (Set.mem_univ t) d (hv d hd).1) (hΛ0 a) (GlobalTheory.JetsOne.col_left ch a)
    (fun d hd => GlobalTheory.JetsOne.col_near _ P d (hv d hd).1 (GlobalTheory.JetsOne.col_fix ch a (v1 0 hm).2.1))
    (fun d hd => hΛ' t (Set.mem_univ t) d (hv d hd).2) (hΛ0' t y) (GlobalTheory.JetsOne.form_aut s ch t y).1
    (fun d hd => GlobalTheory.JetsOne.row_near _ P d (hv d hd).2 (GlobalTheory.JetsOne.form_aut s ch t y).2) hlast
    (fun n hn => posDef_top ch.G hn.le) (fun n hn => posDef_grid hL hn)
    (fun j => M.ν (.top j)) (fun j => M.fd (.top j)) (ch.S.levTop t (ch.Phi a) β) (fun n hn => (v1 n hn).2)
    (fun j => M.ν (.grid j D.R.m)) (fun j => M.fd (.grid j D.R.m)) (ch.S.levRow t) (fun n hn => (v2 n hn).2)
    (fun X Y => c * GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ X Y (psiC (ch.Psi a) (X 0)) (ch.S.formC t y (Y 0)))
    (pairing_of_points_expansion ch.S.toGridChoice τ c _ _)
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := i2 (GlobalTheory.JetsOne.psiC_right ch a) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i1 X Y _ j.succ_pos hj k hk))
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := h0 t a β hβ τ hτ y (psiC (ch.Psi a) (X 0)) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i3 X Y _ j.succ_pos hj k hk))
    (fun X Y k h1 hk => congrArg _ (i4 X Y k h1 hk))
  rw [defTot, Finsupp.sum_single_index (by simp)]
  simp only [one_mul, GlobalTheory.JetsOne.defPer_eq, hσ]
  refine key.trans ?_
  rw [GridChoice.classSum, mul_finsum]
  exact finsum_congr fun c' => mul_left_comm _ _ _
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealFunctionalsSeparateOfHypothesis
section
section
namespace UpperTheory.Lit
theorem real_functionals_separate_of_hypothesis
    (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent)
    (realIn : Branch.RealInputE) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  have rowModels := _root_.GlobalTheory.T.exists_models_of_separating_data P
  have rowStep := _root_.GlobalTheory.T.separating_family_extend_by_twist P (_root_.GlobalTheory.T.exists_seesaw_pair_of_theta_data P) rowModels
  have rowTower := _root_.GlobalTheory.SepRows.rowTower_of_step rowModels rowStep
  have conv := _root_.GlobalTheory.T.convergence_of_separating_family P rowTower
  have per := Branch.periodNe_of_eigen P.harishChandraModules P.casselmanWallach P.cuspRapidDecay realIn
  have onto := _root_.GlobalTheory.T.twist_core_surjective P P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover
    P.harishChandraModules P.casselmanWallach hHowe P.weilRepresentationUnitaryPair
    P.weilSiegelFormulaUnitary hSW P.doublingMethod P.unramifiedDoublingGL
  have weak := _root_.GlobalTheory.SepRows.weakSep_of_steps _root_.GlobalTheory.SepRows.sizeGap_of_sizes (_root_.GlobalTheory.T.exists_separating_models P) (_root_.GlobalTheory.T.rapid_decay_of_separating_family P rowTower) per onto
    (_root_.GlobalTheory.Asc.ascent_of_depFixed _root_.GlobalTheory.DepthFix.depFixed)
  exact _root_.UpperTheory.Lit.bessel_separate_of_step_gap P rowTower _root_.GlobalTheory.SepRows.sizeGap_of_sizes _root_.GlobalTheory.SepRows.goodRows conv weak
end UpperTheory.Lit
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareCommutesWithAll
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SquareComm
open GlobalTheory.RowClaim
end GlobalTheory.SquareComm
namespace GlobalTheory.SquareComm
open GlobalTheory.RowClaim
theorem square_commutes_with_all : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
      ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t) := by
  intro hPr hWC hK
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ t i j => ?_⟩⟩
  exact commutesWith_of_isSquareConst hWC hK hPr.cuspDecayBound s.core.lev
    (squareStanding_of_setting s s.size.2.1.eleven_le ch.G t) (hch.const i j t)
end GlobalTheory.SquareComm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_square_commutes : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t) := by
  first | exact @_root_.GlobalTheory.SquareComm.square_commutes_with_all | exact _root_.GlobalTheory.SquareComm.square_commutes_with_all | (intros; apply _root_.GlobalTheory.SquareComm.square_commutes_with_all <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralVanishesOnFiniteRelations
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ThetaFinRelDef
open GlobalTheory.SquareComm
open scoped ComplexOrder
theorem theta_integral_finite_relation_eq_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X), GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0) → ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 → ∀ Φ ∈ finRel ω (algF ψ θ false A B), thetaInt ω ν 𝓕 Φ = 0 := by
  intro _ D ψ θ hψ hθ M X A B χ χ' ω hω hsig ν 𝓕 hF
  have hω' : IsWeilDatumO ψ M X χ χ' ω := hω
  have hpd : ∀ τ, (gramAt D M τ).PosDef := fun τ => GlobalTheory.Core.CoefGram.posDef_of_hasSignature _ (hsig τ)
  have hcc : GlobalTheory.Unf.CoCpt M := (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D M).2 hpd
  have hth : ∀ Φ ∈ algF ψ θ false A B, IsThetaFunO ψ M X Φ := fun Φ hΦ =>
    GlobalTheory.SquareComm.ThetaLeft.isThetaFunO_of_mem_algF hψ hθ A B hΦ
  have hleft := GlobalTheory.SquareComm.ThetaLeft.main D ψ θ hθ M X A B χ χ' ω hω
  have hsub : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ - Ψ) = thetaKO ω g k Φ - thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_sub]
  have hadd : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ + Ψ) = thetaKO ω g k Φ + thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_add (f := _)]
  have hsmul : ∀ g k (c : ℂ) (Φ : WO M X → ℂ), thetaKO ω g k (c • Φ) = c * thetaKO ω g k Φ := by
    intros; simp [thetaKO, map_smul]
  have hzero : ∀ g k, thetaKO ω g k (0 : WO M X → ℂ) = 0 := by
    intros; simp [thetaKO]
  have hint : ∀ Φ ∈ algF ψ θ false A B, ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
    intro Φ hΦ h
    exact (GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D M hcc _
      ⟨fun γ hγ g => hleft Φ hΦ γ hγ g h, (hω'.om_cont Φ (hth Φ hΦ) 0).comp (Continuous.prodMk_left h)⟩).2.2
      ⟨ν, 𝓕, hF.1, hF.2⟩
  intro Φ hΦ
  suffices key : (∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν) ∧ thetaInt ω ν 𝓕 Φ = 0 from key.2
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, -, Ψ, hΨ, rfl⟩ := hx
    have e : ∀ g k, thetaKO ω g k (ω (u, 1) Ψ) = thetaKO ω (g * u) k Ψ := fun g k => by
      unfold thetaKO
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    have tr := fun k => integral_rightTranslate hF (f := fun g => thetaKO ω g k Ψ)
      (fun γ hγ g => hleft Ψ hΨ γ hγ g k) u
    have i1 : ∀ k, IntegrableOn (fun g => thetaKO ω g k (ω (u, 1) Ψ)) 𝓕 ν := fun k => by
      simp only [e]; exact (tr k).1.2 (hint Ψ hΨ k)
    refine ⟨fun k => ?_, ?_⟩
    · simp only [hsub]; exact (i1 k).sub (hint Ψ hΨ k)
    · funext k
      simp only [thetaInt, hsub, Pi.zero_apply]
      rw [integral_sub (i1 k) (hint Ψ hΨ k)]
      simp only [e]
      rw [(tr k).2, sub_self]
  | zero =>
    exact ⟨fun k => by simp only [hzero]; exact integrableOn_zero, by funext k; simp [thetaInt, hzero]⟩
  | add x y _ _ hx hy =>
    refine ⟨fun k => by simp only [hadd]; exact (hx.1 k).add (hy.1 k), ?_⟩
    funext k
    have := integral_add (hx.1 k) (hy.1 k)
    have ex := congrFun hx.2 k
    have ey := congrFun hy.2 k
    simp only [thetaInt, Pi.zero_apply] at ex ey
    simp only [thetaInt, hadd, Pi.zero_apply, this, ex, ey, add_zero]
  | smul c x _ hx =>
    refine ⟨fun k => by simp only [hsmul]; exact (hx.1 k).const_mul c, ?_⟩
    funext k
    have ex := congrFun hx.2 k
    simp only [thetaInt, Pi.zero_apply] at ex
    simp only [thetaInt, hsmul, Pi.zero_apply, integral_const_mul, ex, mul_zero]
end GlobalTheory.ThetaFinRelDef
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X), GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0) → ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 → ∀ Φ ∈ finRel ω (algF ψ θ false A B), thetaInt ω ν 𝓕 Φ = 0 := by
  first | exact @_root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | exact _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | (intros; apply _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero <;> assumption)
end
end

