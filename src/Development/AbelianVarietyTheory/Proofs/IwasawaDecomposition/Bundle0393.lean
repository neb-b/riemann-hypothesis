module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0182
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0111
public import Formalism.LocalRingCardinality.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionOnAdelicFunctionsEqZeroOfNoLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicLiftTypePrimeReductions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem SecondG.sAnd_of_largeBase : ∀ (KP : GroupRetwisting.BaseP) (Q Q' R : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.LargeBaseConditionG KP Q R → GroupRetwisting.SecondG KP Q Q' →
    GroupRetwisting.SecondG KP Q (sAnd Q' R) := by
  intro KP Q Q' R hK hR hS
  refine (EvG.inter hR hS).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨S₁r, P₁r, Ar, S₂r, r1, r2, hr⟩, ⟨S₁s, P₁s, As, S₂s, s1, s2, hs⟩⟩ := H
  refine ⟨fun P g F => S₁s P g F ∪ S₁r P g F, fun P g F F₀ => P₁s P g F F₀ ∪ P₁r P g F F₀, As, S₂s, ?_, s2, ?_⟩
  · intro P g F z hz
    rcases Finset.mem_union.1 hz with h | h
    exacts [s1 _ _ _ z h, r1 _ _ _ z h]
  · intro B f T hO hH hP hA hKP hT C W V S N G c hQ hX A S₂ hS₂
    have hH' : Has₂ B (S₁s B.toPre f B.KsC) (S₂s B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨B', f', T', hEnl, hf', hpl, hAv, hS', C', W', V', S', N', G', c', hQ', hTw, hQ''⟩ :=
      hs B f T hO hH' (fun x hx => hP (Finset.mem_union_left _ hx)) hA hKP hT C W V S N G c hQ hX
        (fun l => A l ∪ Ar B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂r P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
        (by
          intro P g Ξ z hz
          rcases Finset.mem_union.1 hz with h | h
          exacts [hS₂ _ _ _ z h, r2 _ _ _ _ _ z h])
    have hP' : B'.toPre = B.toPre := hEnl.1
    have cf : ∀ {α : Type} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {x : Fr P} {y : Fr P'}, P = P' → HEq x y → g P x = g P' y := by
      intro α g P P' x y h hxy
      subst h
      rw [eq_of_heq hxy]
    have hk : B'.KsC = B.KsC := hEnl.KsC_eq
    have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := hEnl.fixedCoefficientField_eq
    have hRc : R K ⟨B', C', W', V', S', N', G'⟩ f' T' c' :=
      hr B' f' T' (hP' ▸ hO)
        ⟨by rw [hk, hl, cf S₁r hP' hf']; exact fun z hz => hH.1 z (Finset.mem_union_right _ hz),
          by rw [hk, hl]; exact fun z hz => hS' z (Finset.mem_union_right _ hz)⟩
        (by rw [hk, hl, cf P₁r hP' hf', hpl]; exact fun x hx => hP (Finset.mem_union_right _ hx))
        (by
          rw [hk, hl, cf Ar hP' hf']
          exact fun w v hv h => hAv w v hv (Finset.mem_union_right _ h))
        (hK.enl B B' f f' hEnl hf' hKP) C' W' V' S' N' G' c' hQ'
    exact ⟨B', f', T', hEnl, hf', hpl, fun w v hv h => hAv w v hv (Finset.mem_union_left _ h),
      fun z hz => hS' z (Finset.mem_union_left _ hz), C', W', V', S', N', G', c', hQ', hTw, hQ'', hRc⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisRowMemDefiniteFamilyTypePartStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basisRow_mem_definiteFamily_type_part : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ (uE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, (Y.Ish.jE y).1 = PiTensorProduct.lift (R.HE.e (uE y))) → ∀ σ, ∃ p, uE (D.what₂.onb σ) ∈ R.EEp3 p ∧ ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p = ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) := by
  first | exact @GlobalTheory.Mem.RowType.row_type | exact GlobalTheory.Mem.RowType.row_type | (intros; apply GlobalTheory.Mem.RowType.row_type <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjTranslatedLevelRowEvaluationMemAllRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace


open GlobalTheory.Core.Mi GlobalTheory.Core.Mi.SeeHH in
theorem GlobalTheory.Mem.SRe.conj_ev_mem_HHX : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ MultR R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → star φ ∈ HHX X := by
  intro hDS hP hUq hRF D G' _ _ Pl0 T A Ks _ _ _ R F X h t hIdE hG hLev hinf hν hSee c v₀ hc1 hc2 S hS φ hφ
  have hθ : IsInfFam R.θ := hinf
  have hMat : Matches X h (JR R F) (chiR R F) t := ⟨hSee.fin, hSee.conj⟩
  have hCV : ConjVec X h R.θ (MP R) v₀ := ⟨c, hc1, hc2⟩
  have hL : ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v))
      (Formalism.REAL.muG (X.B.I.ε v)) := fun v => by
    have h1 := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
      (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond hG) v
    have hs : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v)) :=
      h1.mono (continuous_star.comp_aestronglyMeasurable h1.1) (ae_of_all _ fun g => le_of_eq (norm_star _))
    exact hs.const_mul ((X.dv v : ℝ) : ℂ)
  have hR := _root_.GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h R.θ hθ hIdE
  have hT : PiTensorProduct.lift S ∈ MultT R.θ (MP R) (JR R F) (chiR R F) := by
    refine (mem_multT R.θ (MP R) (JR R F) (chiR R F) _).2 ?_
    rw [LinearEquiv.symm_apply_apply]; exact hS
  obtain ⟨hRow, hMem⟩ := _root_.GlobalTheory.Core.Mi.rowFun_evS hP D X h R.θ _ (MP R) (JR R F) (chiR R F) t hθ hMat _ hT
    (PiTensorProduct.tprod ℂ v₀)
  have hfx : ∀ x, evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) x =
      S v₀ ((iotaX X h).symm x * t) := fun x => by
    delta evS
    rw [PiTensorProduct.lift.tprod]
  generalize evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) = f at hRow hMem hfx
  have hφ2 : (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f := hφ.trans (Filter.Eventually.of_forall fun x => (hfx x).symm)
  have hφ' : φ = hMem.toLp f := Lp.ext (hφ2.trans hMem.coeFn_toLp.symm)
  have hRe := re_fix_of_row X hRow hMem
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact GlobalTheory.Mem.SJ.SchurMove.castGA_mem_GFset _ _
  obtain ⟨κ, hκ⟩ := GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge (MP R) R.θ (JR R F) (chiR R F)
    (fun μ 𝓕 => GlobalTheory.MultFinite.schurMult hP μ 𝓕) hθ
    X.B.I X.B.μf X.B.fund X.B.fund_spec (iotaX X h) hι t S hS S hS
  have hv₀ : ∏ τ, ⟪(v₀ τ : (MP R).H τ), (v₀ τ : (MP R).H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    have hn : ‖(v₀ τ : (MP R).H τ)‖ = 1 := by
      rw [← (c τ).norm_map, hc2 τ]
      exact (X.low _).1
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hMem.star
  have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, star (f (γ * y)) = star (f y) := fun γ hγ y => by
    rw [hRow.left γ hγ y]
  have hnorm : (((‖hs.toLp (fun x => star (f x))‖ ^ 2 : ℝ)) : ℂ) = κ := by
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hs, ← integral_complex_ofReal]
    have e := hκ v₀ v₀
    rw [hv₀, mul_one] at e
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [norm_star, hfx x, ← starRingEnd_apply, Complex.conj_mul']
    push_cast
    ring
  have hRph : X.Rph (star (hMem.toLp f)) = star (hMem.toLp f) := by
    rw [star_toLp_eq X hMem hs]
    refine Formalism.L2.SG.EvalTRph.rph_fix_of_coef X hL _ (fun g => ?_)
    obtain ⟨a, ha, hb, w, hw, hsh⟩ := real_shift X h R.θ (MP R) (JR R F) (chiR R F) t hMat.1 hR v₀ g
    have hco := coef_eq X h R.θ (MP R) v₀ hCV g a ha hb w hw
    have hRg := Formalism.L2.SG.EvalTReg.reg_toLp_X X (fun x => star (f x)) hinv hs (g, 1)
    have hpair : ⟪hs.toLp (fun x => star (f x)), X.B.R (g, 1) (hs.toLp (fun x => star (f x)))⟫_ℂ =
        ∫ x, star (S w ((iotaX X h).symm x * t)) * S v₀ ((iotaX X h).symm x * t) ∂(muX X) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs.coeFn_toLp, hRg] with x a1 a2
      rw [a1, a2]
      simp only [RCLike.inner_apply, hfx]
      rw [hsh S hS x, starRingEnd_apply, star_star, mul_comm]
    rw [hpair, hκ w v₀, hco, hnorm]
  rw [hφ']
  refine ⟨star (hMem.toLp f), ?_⟩
  show X.B.Re (X.Rph _) = _
  rw [hRph, hRe]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAdicCompletionEquivUniformiser
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnifMap

theorem unif_to_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ ϖ : v.adicCompletion F, Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v (i ϖ) = WithZero.exp (-1 : ℤ) := by
  intro F E _ _ _ _ v w i hi ϖ hϖ
  have hle := _root_.GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous F E v w i hi
  have key : ∀ x : WithZero (Multiplicative ℤ), x ≠ 0 → x < 1 → x ≤ WithZero.exp (-1 : ℤ) := by
    intro x hx h1
    rw [← WithZero.exp_log hx] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]; omega
  have hlt : ∀ y, Valued.v (i y) < 1 ↔ Valued.v y < 1 := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have hiy : i y ≠ 0 := by simpa using hy
      have e1 := (Valued.v (R := w.adicCompletion E)).one_lt_val_iff (inv_ne_zero hiy)
      have e2 := (Valued.v (R := v.adicCompletion F)).one_lt_val_iff (inv_ne_zero hy)
      rw [inv_inv] at e1 e2
      rw [← e1, ← e2, ← not_le, ← not_le, ← map_inv₀ i, hle]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hiϖ0 : i ϖ ≠ 0 := by simpa using hϖ0
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hup : Valued.v (i ϖ) < 1 := (hlt ϖ).2 hϖ1
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  set z : w.adicCompletion E := (π : w.adicCompletion E)
  have hz : Valued.v z = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  set y := i.symm z
  have hy1 : Valued.v y < 1 := by
    rw [← hlt, RingEquiv.apply_symm_apply, hz, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy1
    have : z = 0 := by simpa [y] using h
    rw [this, map_zero] at hz; exact WithZero.exp_ne_zero hz.symm
  have hdiv : Valued.v (y / ϖ) ≤ 1 := by
    rw [map_div₀, hϖ, div_le_one₀ (by simp)]
    exact key _ (by simpa using hy0) hy1
  have h2 := (hle _).2 hdiv
  rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply, hz] at h2
  have hlow : WithZero.exp (-1 : ℤ) ≤ Valued.v (i ϖ) := by
    rwa [div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hiϖ0))] at h2
  exact le_antisymm (key _ (by simpa using hiϖ0) hup) hlow

end GlobalTheory.UnifMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoRawMulLevelIwahoriReduction
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

open Formalism.UG Formalism.MainNotions

namespace GlobalTheory.Mem.ColAd.LevGrp

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem decoRaw_mul_levelIwahori_reduction (g z : GL (Fin n) (AfE F E)) (hz : z ∈ J0 hc n ST) :
    decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 (redG hc n ST SG ⟨z, hz⟩)⁻¹ := by
  have h := decoRaw_rawSm hc ST SG 1 (⟨z, hz⟩⁻¹ : J0 hc n ST) g
  rw [map_one, map_inv] at h
  have e : Formalism.UG.bc (iA F E) ((1 : URat hc n) : GL (Fin n) E) * g *
      (((⟨z, hz⟩⁻¹ : J0 hc n ST) : J0 hc n ST) : GL (Fin n) (AfE F E))⁻¹ = g * z := by
    simp
  rw [e] at h
  exact h

end Gen

section Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) [NeZero n]

end Top

end GlobalTheory.Mem.ColAd.LevGrp

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.ColAd.LevGrp

end GlobalTheory.Mem.Col2.TC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedPointClassesBijectiveDoubleCosetsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedPointClasses_bijective_doubleCosets : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (C : Type) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (s : C → DecoF E n ST SG Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' : GL (Fin n) (AfE F E)) (y : C → UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)), U ≤ UAd hc n → k' ∈ UAd hc n → (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p')) → (∀ g ∈ UAd hc n, ∃ x ∈ U, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * k') p) → (∀ c, IsPtOf hc ((y c).1 * k') (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → Function.Bijective (fun c => (Quotient.mk'' (y c) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) (U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))))) := by
  first | exact @GlobalTheory.Mem.Col2.ClsBij.classes_bijective | exact GlobalTheory.Mem.Col2.ClsBij.classes_bijective | (intros; apply GlobalTheory.Mem.Col2.ClsBij.classes_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicPoint_finitePart_eq_realOne : ∀ {D : D7} (V : HSp D) (g : Bridge.Gf V), ∃ α ∈ GfC V, finHom V α = (g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D V g
  obtain ⟨β, hβ⟩ := g.2
  have lift (g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
      (hg : g ∈ Formalism.L2.DIV.UA D.sp.cm V.gram) :
      ∃ k ∈ GfC V, Formalism.IndefR.Lev.finE V k = g := by
    obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨g, hg⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
    obtain ⟨k, k1, k2⟩ := h2 1 b.1
    refine ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩, k1, ?_⟩
    have e := congrArg Subtype.val hb
    have e2 := GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram b
    refine Eq.trans ?_ (e2.symm.trans e)
    exact congrArg (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D)) k2
  obtain ⟨α, hα, e⟩ := lift (Formalism.IndefR.Lev.finE V β) (GlobalTheory.LevSplit.finE_mem_UA V β)
  refine ⟨α, hα, ?_⟩
  rw [← hβ]
  apply Units.ext
  ext i j
  have h := congrArg (fun x : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => x.val i j) e
  exact (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

namespace GlobalTheory.Mem.R3.LedRec


set_option maxHeartbeats 1000000 in
theorem ev_exists_sizeData : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w j, X.toD7.what₂.Aj j w = 0) →
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧
      8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) (fun w _ j _ _ => hA w j)
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  exact ⟨L, e1, M.sizes, ⟨M.params⟩, M.parT.nV_ge⟩

def bare {B : Base} {C : Cols B} (W : RowsRest B C) : RowsRest B C :=
  { GaloisStage.adapt W with Ij := fun _ _ _ => 0, jw := fun _ _ _ => 0 }

theorem exists_bare (hG : GlobalTheory.Published.GreenCuspidal) {B : Base} {C : Cols B} (a : Late B C) (f : Fr B.toPre) (η : ℝ) :
    ∃ b : Late B C, GrpTrue b.N f ∧ b.V.div.etaF = η ∧ ∀ w j, b.D.what₂.Aj j w = 0 := by
  obtain ⟨N, -, -, hN, -⟩ := exists_nStage_grpTrue hG B C (bare a.W) (GlobalTheory.MemN.shaOK_shaTrue B.toPre) (fun _ _ _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) f
  exact ⟨⟨bare a.W, { a.V with div := { a.V.div with etaF := η } }, { a.S with }, N, a.G⟩, hN, rfl, fun _ _ => rfl⟩

def sameGrp {B : Base} {C : Cols B} {a b : Late B C} {f : Fr B.toPre} (h : GrpTrue a.N f) (h' : GrpTrue b.N f) : SameGrp a b where
  e := plEquiv a.N.naut b.N.naut
  pl := TypesTrue.plGw_plEquiv h h'
  e0 := h.typeIdempotent_coeff_across_layers h'

end GlobalTheory.Mem.R3.LedRec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseLevelRowOfNonzeroGoodRowsPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.RowsAtBase

theorem exists_base_row_of_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false ≠ ⊥ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hP hH _ hG p hp
  have hC := hP.char
  have hE := hH.aux.ex
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hH.ok.ok2.irr
  have key := GlobalTheory.LevelRows.rowsOfLevel_of_models R.toRealDat F.lv2 hC.base.models.HE hC.base.models.gE false
  obtain ⟨u, huU, hu0, hup⟩ := GlobalTheory.Hk3.exists_level_vector D.what₂.embLL A3.A.X F.P0 F.ψ0 R.gE (R.EEp3 p) hX hG
    (fun g => GlobalTheory.RowsSum3.rowTypePart_map_finiteGroup_le R F hC hE p g) hp
    (fun u _ => by simpa [RealDat.eC] using GlobalTheory.ChainScalar.sum_gE hC.base.models.HE hC.base.models.gE u)
  rw [Submodule.ne_bot_iff]
  exact ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) u, ⟨huU, (key u).2 hup⟩, hu0⟩

end GlobalTheory.RowsAtBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelSmallerAtFinitePlacesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepLevel_smaller_at_finite_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (A : Subgroup (GL (Fin n) (AfE F E))) (ψ : A →* ℂˣ), A ≤ S.U → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ A, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ A) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ A}) → (∀ x : A, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1) → ∃ L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))), L.Lb = S.Lb ∧ L.U = A ∧ (∀ v, v ∉ Qv → L.Uloc v = S.Uloc v) ∧ ∀ (x : L.U) (x' : S.U) (x'' : A), x.1 = x'.1 → x.1 = x''.1 → L.chi x = S.chi x' * ψ x'' := by
  first | exact @GlobalTheory.StepLevelShrink.exists_stepLevel_shrink | exact GlobalTheory.StepLevelShrink.exists_stepLevel_shrink | (intros; apply GlobalTheory.StepLevelShrink.exists_stepLevel_shrink <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicLiftTypePrimeReductionsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelic_lift_typePrime_reductions : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (n : ℕ)
    (x : ∀ w : (B.primes X).vGs, GL (Fin n) (𝓞 B.fields.E ⧸ w.1.asIdeal)), ∃ t : GA B n,
      (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
      (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
        bc (prV (E := B.host.E) v) t = 1) ∧
      ∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((t : Matrix (Fin n) (Fin n) _) r j)) ((x w).1 r j) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.exists_unitary_lift | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.exists_unitary_lift | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.exists_unitary_lift <;> assumption)
end

