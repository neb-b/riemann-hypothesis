module

public import Mathlib
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0079
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1774
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYWeilVec
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem stepY_weil_vec_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hW hf j hj
  have hC := hW.bot.hyp.2.2.2.1
  have hQ : (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 = ∅ :=
    Finset.eq_empty_of_forall_notMem fun PP => _root_.GlobalTheory.MiTop.not_mem_Q_base' W PP
  refine ⟨hC.chain.ωY W.P.A3.A.μ0 j hj, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, (_root_.GlobalTheory.Fam.pk_z W).vac j, ?_⟩
  have h := (hf.row W.P.A3.A.μ0).vP j hj
  rw [hQ] at h
  exact h
end GlobalTheory.BaseChain
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiesOfTiesB
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem ties_of_tiesB_alt : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b →
    GlobalTheory.FinalJoin2.FieldSmall D O.L → b.RealisedCondition → GlobalTheory.EX.DQ.TwAllAt D O.ex.nch O.ex.xd → b.CompatibilityConditions := by
  intro D O c b h hF hR htw
  obtain ⟨hc, hpb, -, hL, hD⟩ := _root_.GlobalTheory.PlugPt.ties_core_of_tiesB D O c b h hF
  obtain ⟨hT, hRay⟩ := h
  exact
    { real := hR, core := hc, pb := hpb, types := hT.types, series := hT.series, level := hL, data := hD,
      psiVal := hT.psiVal, ray := hT.small.ray, roots := hT.small.roots, rayQ := hRay, twist := htw }
end GlobalTheory.PlugPt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopOfMemCXP
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopLevelP
section Package
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
end Package
theorem vector_of_mem_cxp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.Fam.leadingLinearMap W t F ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t F
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  obtain ⟨⟨s, hs⟩, -⟩ := hP.lev
  exact mem_CXP_of_good (_root_.GlobalTheory.Fam.pk_z W) hC.grp.red_R hC.models.jX hC.models.cX hs.ok2.irr W.Q.F.P1 W.Q.F.ψ1 t
    (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F) ⟨F, rfl⟩ ((hP.hTop t).le ⟨_, rfl⟩)
end GlobalTheory.TopLevelP
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TuplePlaceUnderNotMemTP
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem tuplePlace_under_notMem_tP_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ PP, _root_.GlobalTheory.Fam.QAllAlt W PP → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.tP := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y m b₀ k _ _ _ _ ι v o l bas _ _ _ _ _ _ _ _ htP _ _ _ _ FY sc _ PP hQ hmem
  obtain ⟨t, ht⟩ := hQ
  apply (hP.bot.hyp.2.2.2.1.lev.Q_off t PP ht).2 u
  have h1 := (htP _).1 hmem
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast] at h1
  exact h1
end GlobalTheory
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistStOf
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.TwistBoundAtPlace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem twistSt_of_alt (hE : _root_.GlobalTheory.BigOn.ExportedStatement) (hG : _root_.GlobalTheory.BigOn.GeometricStatement')
    (hK : _root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) : _root_.GlobalTheory.BigOn.TwistStatement' := by
  obtain ⟨a, ha, H⟩ := (hE.and hG).and hK
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK'⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, E1⟩, ⟨c1, G1⟩⟩, ⟨c2, K1⟩⟩ := hK' Fm CH hc hL
  obtain ⟨x0, T0⟩ := hc.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max c1 c2, fun c hcC hb => ?_⟩
  obtain ⟨x2, G2⟩ := G1 c ((le_max_left _ _).trans hcC) hb
  obtain ⟨x3, K2⟩ := K1 c ((le_max_right _ _).trans hcC) hb
  refine ⟨max (max x0 x1) (max x2 x3), fun x hx hle i p hp hM r O hR => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have h1 : x1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  obtain ⟨-, N0, S, hTG⟩ := T0 x h0 hx i
  exact hasTwistBound_at p hR (E1 x hx h1 i p hp hM) (G2 x hx h2 i p hp hM r O hR).1 (K2 x hx h3 i p hp hM r O hR) hTG
end GlobalTheory.BigOn.TwistBoundAtPlace
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwoLogCardLevelsLeStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_log_card_Gp_le_b : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ PP A : ℝ, GlobalTheory.CovTop.HostNum D L PP A 3 → 2 * Real.log (Fintype.card p.P.Gp : ℕ) ≤ L.sc.b := by
  first | exact @_root_.GlobalTheory.CovTop.two_log_card_levels_le_alt | exact _root_.GlobalTheory.CovTop.two_log_card_levels_le_alt | (intros; apply _root_.GlobalTheory.CovTop.two_log_card_levels_le_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimesGtThreeR
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory.BigOn
theorem typePrimes_gt_three_r_alt :
    _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ k : Fin 2, 3 * (Fm.D x i).R.r < (Fm.D x i).host.g k := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  exact _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i _ _ _ k => three_r_lt_g_of_params _ _ (Fm.params x hx i) k
end GlobalTheory.BigOn
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ULowOf
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop.FromComp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem u_low_of_cover_hyps (h1 : _root_.GlobalTheory.CovTop.DeepGoodness) (h2 : _root_.GlobalTheory.CovTop.SizeCondition) (h3 : _root_.GlobalTheory.CovTop.CoverDegree) (h4 : _root_.GlobalTheory.CovTop.ShareCondition) (h5 : _root_.GlobalTheory.CovTop.HeightCondition) (h6 : _root_.GlobalTheory.CovTop.CoverHeightSum) (h7 : _root_.GlobalTheory.CovTop.SumBoundCondition) : _root_.GlobalTheory.CovTop.UniformLowerBound := by
  refine Closed.imp (Closed.and h1 (Closed.and h2 (Closed.and h3 (Closed.and h4 (Closed.and h5 (Closed.and h6 h7)))))) ?_
  rintro _ Fm _ _ ⟨⟨_, -, a1⟩, ⟨A, -, a2⟩, ⟨_, -, a3⟩, ⟨_, -, a4⟩, ⟨C1, hC1, a5⟩, ⟨C2, hC2, a6⟩, ⟨_, -, a7⟩⟩
  refine ⟨2 * (3 * C1 + C2 + 4), by positivity, ?_⟩
  obtain ⟨x0, h⟩ := a1.and (a2.and (a3.and (a4.and (a5.and (a6.and a7)))))
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h x hx hle ι p hp
  exact atPoint p i Y _ A C1 C2 hi (b1 i hi Y hY) (b2 i) (b3 i hi Y hY) (b4 i hi Y hY) (b5 i hi Y hY) (b6 i hi Y hY)
    (b7 i hi Y hY)
end GlobalTheory.CovTop.FromComp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnipModHalf
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.LevelUnip
section Res
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
end Res
variable {D : D7}
end GlobalTheory.LevelUnip
open GlobalTheory.LevelUnip in
theorem GlobalTheory.LevelUnip.unip_mod_half_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ (g : (p.F.lv2.lvl false).P) (z : (p.T.Q.Dw ((i : ℕ) + 1)).La), z ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) → (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) z ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g z hz
  obtain ⟨κ, hk, hf⟩ := (p.pins i).2.lift.lev g
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hu : p.R.eG g ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG g) ∈ (p.F.lv2.lvl false).P
    simp
  have hun : ∀ PP, p.R.eG g PP ∈ unip (kP PP.1) D.R.r := by
    rw [hlev] at hu
    exact fun PP => (Subgroup.mem_pi _).1 hu PP (Set.mem_univ _)
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hemb := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hβ := hL.βW i
  have hr := rank_Wc (D := D) i
  have hkSt := parLev_St hk.2.1
  have hred : ∀ P ∈ p.R.Pg, (((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
      Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) - 1) ^ D.R.r = 0 := by
    intro P hP
    have hb := blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)
    have e : upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) = p.R.eG g ⟨P, hP⟩ :=
      congrFun hk.2.2 ⟨P, hP⟩
    have hU := hun ⟨P, hP⟩
    rw [← e] at hU
    have hv := upper_block_val_submatrix (p.R.datWp i p.R.triv).hr hb
    have hent : ∀ a c : Fin (Wc D i).rank,
        ((upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) : GL (Fin D.R.r) (kP P)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP P)) (Fin.cast hr a) (Fin.cast hr c) =
        ((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
          Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) a c := by
      intro a c
      exact (congrFun (congrFun hv (Fin.cast hr a)) (Fin.cast hr c)).trans rfl
    rw [← hr]
    apply sub_one_pow_eq_zero'
    · intro a c hca
      rw [← hent]
      exact hU.1 (show ((Fin.cast hr c : Fin D.R.r) : ℕ) < (Fin.cast hr a : Fin D.R.r) from hca)
    · intro a
      rw [← hent]
      exact hU.2 _
  have hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := p.T.Q.l.prod
  have hp' : (∏ P ∈ p.R.Pg, P.asIdeal) * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by
    rw [← hhalf]; exact hp
  have hI : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hc : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  have hcong := fun b (hb : b ∈ Mfr p.T.Q.l) => exists_pow_cong hβ p.R.Pg hp' hkSt hred hb
  have hpow := approx_pow hemb (sub_one_mulVec_mem hβ hkSt) hf D.R.r
  have h0 : ∀ a ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La),
      ∃ w ∈ latGHat (Wc D i) 1, finVec (Wc D i) (iotaW p.T i ((0 : (p.T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] _) a)) -
        (0 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
          finVec (Wc D i) (iotaW p.T i a) = p.T.Q.l.M • w := by
    intro a _
    refine ⟨0, zero_mem _, ?_⟩
    funext j
    simp [finVec]
  have := GlobalTheory.LevelUnique.sub_mem_of_approx hemb (lt_of_lt_of_le (by norm_num) p.T.Q.l.three_le) hI hc hcong hpow h0 z
  simpa using this
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilOKFam
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.WeilTup
variable {D : D7}
theorem weilOK_fam_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c), f.RowOK → f.ColOK → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t, WeilOK (t := f.t t) v := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR hC hτ t
  have hmE : ¬ Odd D.R.m := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  have hE := GlobalTheory.WeilDatumExistence.weilDatumExists D
  have hX := hP.bot.hyp.2.2.2.1.chain.ωX t
  simp only [Formalism.IndefR.Lift.chrStep, if_neg hmE] at hX
  have hη : ∀ j' (h' : j' + 2 * 0 + 2 = D.R.m), IsHeckeChar D (_root_.GlobalTheory.Fam.pk_z W).eta ∧ ResEta D (_root_.GlobalTheory.Fam.pk_z W).eta 1 := by
    intro j' h'
    have e : j' + 1 + 1 = D.R.m := by omega
    have hk := hC.kom t (j' + 1) (by omega)
    have hμH : IsHeckeChar D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t D.R.m) := by
      have h1 : IsHeckeChar D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j' + 1 + 1)) := hk.hecS
      rw [e] at h1; exact h1
    have hμR : ResEta D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t D.R.m) (D.sp.X'.rank + 1) := by
      have h1 : ResEta D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j' + 1 + 1)) (D.sp.X (j' + 1 + 1)).rank := hk.resT
      have h2 : D.sp.X'.rank + f.c.Lz.rank = (D.sp.X (j' + 1 + 1)).rank := (f.c.oT (j' + 1 + 1) e).rank_add
      rw [← h2, (hτ j' h').1, e] at h1
      exact h1
    have hH : IsHeckeChar D (_root_.GlobalTheory.Fam.pk_z W).eta := by
      have h1 := hecke_mul (hecke_inv hX.hecT) hμH
      rwa [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right] at h1
    exact ⟨hH, resEta_of_diff hμR hX.resT⟩
  refine ⟨?_, ?_, hτ⟩
  · intro j σ h
    obtain ⟨hHη, hRη⟩ := hη (j + 2 * σ + 2) (by omega)
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j (σ + 1) h
    obtain ⟨-, -, fV, fW⟩ := (hR.row t).sFB j σ h
    have hL := (f.c.bes j (σ + 1) h).line.1
    have hL' := (f.c.bes (j + 1 + 1) σ (idx_step h)).line.1
    obtain ⟨omz, homz⟩ := hE (f.c.bes j (σ + 1) h).L (D.sp.X (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omz', homz'⟩ := hE (D.sp.X (j + 1)) (f.c.bes (j + 1 + 1) σ (idx_step h)).L (_root_.GlobalTheory.Fam.pk_z W).ψ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1))
      (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ hk1.std hk1.hecS hzH hk1.resS (by rw [hL']; exact hzR)
    refine ⟨(_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1), (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1), (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, omz, omz', bV, fW, ?_, ?_, ?_, ?_⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [fV]; exact hk1
    · rw [fV]; exact homz'
  · intro j h
    have e : j + 1 + 1 = D.R.m := by omega
    obtain ⟨hHη, hRη⟩ := hη j h
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j 0 h
    have hL := (f.c.bes j 0 h).line.1
    have hXH : IsHeckeChar D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹) := by rw [e]; exact hX.hecT
    have hXR : ResEta D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹) D.sp.X'.rank := by rw [e]; exact hX.resT
    obtain ⟨omz, homz⟩ := hE (f.c.bes j 0 h).L (D.sp.X (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omT', homT⟩ := hE (D.sp.X (j + 1)) D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ψ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹) hk1.std hk1.hecS hXH hk1.resS hXR
    obtain ⟨omz'', homz''⟩ := hE (D.sp.X (j + 1)) f.c.Lz (_root_.GlobalTheory.Fam.pk_z W).ψ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1)) (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹⁻¹
      hk1.std hk1.hecS (by rw [inv_inv]; exact hHη) hk1.resS (by rw [(hτ j h).1, inv_inv]; exact hRη)
    have hμ1 : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹⁻¹ = (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) := by
      rw [inv_inv, inv_mul_cancel_right]
    have key : ∀ n (e' : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1))
        ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹)
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX t) e') := by
      intro n e'
      subst e'
      rw [e]
      exact hX
    refine ⟨(_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1), (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1),
      (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, omz, omT', omz'', bV, ?_, ?_, ?_, homT, key (j + 1) (idx_top h), homz''⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [hμ1]; exact hk1
end GlobalTheory.Fam.WeilTup
end
end
end

