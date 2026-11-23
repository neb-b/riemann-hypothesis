module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0076

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnderMemS
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
open GlobalTheory.ChainOnto
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem under_mem_S_alt {W : _root_.GlobalTheory.MiS.RealPackAlt ex} (hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0) (k : Fin 2) (P : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : P.under (𝓞 D.host.F) ∈ (_root_.GlobalTheory.BaseChain.com_z W).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D (_root_.GlobalTheory.Fam.pk_z W).C.P k P hk with h1 | ⟨P', h1, hc⟩
  · exact ⟨P, (hL.Pg P).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨P', (hL.Pg P').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ P'.asIdeal ↔ algebraMap _ _ x ∈ P.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]
theorem stage_y_is (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (j : ℕ) (hj : j < D.R.m) :
    (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Is (_root_.GlobalTheory.BaseChain.com_z W) j := by
  have hC := hP.bot.hyp.2.2.2.1
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hC.lev
  have hM : (_root_.GlobalTheory.Fam.pk_z W).IsModels := hC.models
  have hQ := _root_.GlobalTheory.BaseChain.Q_base_eq_empty W
  have hm : min j D.R.m = j := min_eq_left hj.le
  obtain ⟨c, hc⟩ := hL.βY j hj
  have hν : ((_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) ((_root_.GlobalTheory.Fam.pk_z W).fdY W.P.A3.A.μ0 j) ((_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j) := by
    by_cases h1 : j + 1 < D.R.m
    · exact ⟨(hM.νY _ j h1).1.1, (hM.νY _ j h1).2⟩
    · have : j = D.R.m - 1 := by omega
      subst this
      exact ⟨(hM.νY' _).1.1, (hM.νY' _).2⟩
  haveI := hν.1
  refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, ?_, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1,
    ⟨_, hc, fun P hP hN => hP ?_⟩, ⟨r_le_Y j, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, ?_⟩, ?_, ?_⟩
  · show (D.sp.Y (min j D.R.m)).rank = _
    rw [D.sp.Y_rank _ (min_le_right _ _), hm]
  · show (D.sp.Y (min j D.R.m)).sig τ = _
    rw [D.Y_sigval _ (min_le_right _ _), hm]
  · show parB _ (min j D.R.m) = _
    rw [hm]
  · push_cast at hN
    have := P.isPrime.mem_of_pow_mem _ hN
    rcases P.isPrime.mem_or_mem this with h0 | h0
    · exact _root_.GlobalTheory.BaseChain.under_mem_S_alt hL 0 P h0
    · exact _root_.GlobalTheory.BaseChain.under_mem_S_alt hL 1 P h0
  · show Lev.datY _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) _ _ _ _ = _
    rw [hQ]; rfl
  · exact (MeasureTheory.Measure.IsHaarMeasure.smul _ (_root_.GlobalTheory.BaseChain.cH_ne_zero_alt W) (_root_.GlobalTheory.BaseChain.inverse_level_cardinality_ne_infinity W) :
      (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j).IsHaarMeasure)
  · exact hν.2.mono (MeasureTheory.Measure.smul_absolutelyContinuous)
end GlobalTheory.BaseChain
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnipModHalfStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lev_sub_one_pow_mem_level_multiple : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ (g : (p.F.lv2.lvl false).P) (z : (p.T.Q.Dw ((i : ℕ) + 1)).La), z ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) → (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) z ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
  first | exact @_root_.GlobalTheory.LevelUnip.unip_mod_half_alt | exact _root_.GlobalTheory.LevelUnip.unip_mod_half_alt | (intros; apply _root_.GlobalTheory.LevelUnip.unip_mod_half_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitVectorLineConjugate
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
namespace GlobalTheory.MiTop.LineV
open GlobalTheory.PiTensorInner
end GlobalTheory.MiTop.LineV
namespace GlobalTheory.MiTop.LineV
end GlobalTheory.MiTop.LineV
namespace GlobalTheory.MiTop.LineV
end GlobalTheory.MiTop.LineV
namespace GlobalTheory.MiTop
theorem unit_vector_line_conjugate_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ (v₀ v : (W.Q.Rl.MY 0).Vec), ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → (∀ τ, ‖(v₀ τ : (W.Q.Rl.MY 0).H τ)‖ = 1) → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ≠ 0 → ∀ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX W.S.X → ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB v₀ v hv hn T hTm hT0 φ hφ hst
  obtain ⟨-, hθ, -, hM, -, -⟩ := _root_.GlobalTheory.T.bottom_hypothesis_matching_central_alt W hB
  have hMt : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (show GA D (D.sp.Y 0) from W.Q.tS) := by
    have := hM 1 (one_mem _) (Subgroup.one_mem _)
    rwa [one_mul] at this
  obtain ⟨⟨j, hj, hjT⟩, -⟩ := _root_.GlobalTheory.Core.Mi.evalAll_rows hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)
    (show GA D (D.sp.Y 0) from W.Q.tS) v (by simp) hθ hB.gap hB.idE hMt hv
  obtain ⟨T', hT'⟩ := hj.2 ⟨star φ, hst⟩
  have h1 := hjT T'
  rw [hT'] at h1
  have he : evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX W.S.X]
      evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T'.1 (PiTensorProduct.tprod ℂ v)) := by
    filter_upwards [hφ, h1, Lp.coeFn_star φ] with x a1 a2 a3
    rw [← a1]
    have a4 := a3.symm.trans a2
    simpa using congrArg star a4
  exact LineV.line_of_eq hCR hθ hTm T'.2 v₀ v hn hT0 (LineV.eq_of_evS_ae W.S.X W.Q.instEq _ hTm T'.2 v₀ v he)
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilOKFamStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_of_rank_one_gram' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c), f.RowOK → f.ColOK → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t, WeilOK (t := f.t t) v := by
  first | exact @_root_.GlobalTheory.Fam.WeilTup.weilOK_fam_alt | exact _root_.GlobalTheory.Fam.WeilTup.weilOK_fam_alt | (intros; apply _root_.GlobalTheory.Fam.WeilTup.weilOK_fam_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilTupleRootStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_of_unity_theta_twist_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ (∀ j, j + 1 < D.R.m → f.g.b j ∈ GfC _ → f.g.b (j + 1) ∈ GfC _ → ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, ∀ g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → (_root_.GlobalTheory.Fam.pk_z W).ωY t j (a * f.g.b j, a' * f.g.b (j + 1)) g = ζ j • (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) g) ∧ (∀ j h g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → omT (_root_.GlobalTheory.Fam.pk_z W) t j h (f.g.b (j + 1), f.g.bT) g = ζ (j + 1) • omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) g) ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t j ^ n = (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0 j ^ n := by
  first | exact @_root_.GlobalTheory.TupRoot.weil_tuple_root_alt | exact _root_.GlobalTheory.TupRoot.weil_tuple_root_alt | (intros; apply _root_.GlobalTheory.TupRoot.weil_tuple_root_alt <;> assumption)
end
end

