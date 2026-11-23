module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0312
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NotLargeBaseConditionDisjoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstructionAtBundlePointsOfTrueColumns
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.AtG

theorem row_aAtG_of_rowPin : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd),
    (∀ K X f T c, Q K X f T c →
      (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) →
    AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk :=
  _root_.GlobalTheory.AtG.row_atG_pinned _root_.GlobalTheory.AtG.jetSplitAmb_holds

end GlobalTheory.AtG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

namespace GlobalTheory.EtaInfType

theorem main : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (C : NChoice D) (tp : Formalism.L2.Host.TupTied D cf C), NCharTied D cf C tp → ∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)} := by
  intro D cf C tp N t
  have hI : (N.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) := by
    rw [N.etaT]
    exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
  have h1 := (N.infG _ _ hI (D.eTau t)).1
  have e0 : Formalism.L2.embT D t = embPsi D.host (D.eTau t) := rfl
  rw [e0, h1]
  push_cast
  rfl

end GlobalTheory.EtaInfType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinkedBundlePropertyAfterLargeBaseCoreProperty
section
noncomputable section

namespace GlobalTheory.NRows.AtPt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem of_is {𝒮 : Slots} {K : Ctx} {q : WPt 𝒮 K} {D : D7} {O : Obj D} (h : q.Is D O) {r : ∀ D : D7, Obj D → Prop}
    (hr : r (q.w.D q.Z) q.O) : r D O :=
  (congrArg (fun x : Σ D : D7, Obj D => r x.1 x.2) h).mpr hr

theorem linkedBundleProperty_after_largeBaseCoreProperty {KP : BaseP} {Q Q' R : V4.Slot} {Bd : BdT} {Lk : LkT Bd} {E : Par → BdP Bd} (h : LargeBaseConditionG KP Q R)
    (he : RowE (sAnd Q' R) Lk E) : Lg1 KP Q Q' fun U => RowE U Lk E :=
  ⟨_, GlobalTheory.Fc.LgModel.largeBaseProperty_conditional (R := R),
    ((EvP.of_evGd h).and he).mono fun _ _ _ t β q c b l => t.2 β ⟨q.1, q.2 t.1⟩ c b l⟩

end GlobalTheory.NRows.AtPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftFormsInternalDirectSumIsotypic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.IsotSum


set_option maxHeartbeats 2000000 in
theorem span_all : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m), (⨆ p, Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) = ⊤ := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hpt : ∀ y : Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL,
      (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (Z.jW i y)) := by
    intro y
    rw [Z.jW_read]
    have hn : (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) *
        (((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) false)).ne', Complex.ofReal_one]
    have hs : sg0 D A3.A = D.what₂.embLL := sgAt_mk _ R.toRealDat.hv0
    have h1 : (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        ∑ k, A3.A.v0.embedding (y k) • (R.toCx3 F).eW false i ((R.toCx3 F).bW false i A3.A.v0 k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]
      rfl
    apply_fun (Tw.out (s := twAt D.what₂.embLL A3.A.v0))
    case inj =>
      intro a b h
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) h
    rw [h1]
    change Tw.out (∑ k, A3.A.v0.embedding (y k) • (R.toCx3 F).eW false i ((R.toCx3 F).bW false i A3.A.v0 k)) = _
    change (∑ k, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) (A3.A.v0.embedding (y k) • (R.toCx3 F).eW false i ((R.toCx3 F).bW false i A3.A.v0 k))) =
      (R.FW i).j (sg0 D A3.A) (∑ k, y k • R.toRealDat.bL F.lv2 false i k)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
    show cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding (y k)) •
      ((((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) •
        (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 false i k))) = _
    rw [smul_smul (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)), hn, one_smul, R.toRealDat.emb0, cj_cj]
    congr 1
    exact (DFunLike.congr_fun hs (y k)).symm
  have hnP : 0 < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0 := by rw [← Y.mj.eW_norm i d, hd]; simp
    have h2 : ‖d‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hnP.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  have hw := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i

  have hUT : ∀ p, Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _)) =
      (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
    intro p
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨hy, LinearMap.mem_range_self _ _⟩
    · rw [← (R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 hR.lifts0.1 hR.ratTh
        hR.liftHyp0.h3W hR.partsW i p]
      exact (finrank_le_cpt A3.A.v0.embedding ((R.toCx3 F).w0C false i) hw (Submodule.span ℂ
        ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))) ((R.toCx3 F).WpK false i p)
        (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩)).trans (Submodule.finrank_mono inf_le_left)
  let outL : (R.toCx3 F).W i →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.HW i (sg0 D A3.A)).H :=
    { toFun := fun z => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) z
      map_add' := fun a b => Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b
      map_smul' := fun c a => Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) c a }
  set S : Submodule ℂ (D.what₂.Mj ((i : ℕ) + 1)) :=
    ⨆ p, Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) with hS

  have h5 : ∀ p, (Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))).map outL ≤
      S.map (Y.mj.eW i) := by
    intro p
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine Submodule.mem_map.2 ⟨Z.jW i y, ?_, ?_⟩
    · exact (le_iSup (fun p => Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) p)
        (Submodule.subset_span ⟨y, hy, rfl⟩)
    · show Y.mj.eW i (Z.jW i y) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)
        ((R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y))
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) (hpt y)).symm
  rw [eq_top_iff]
  intro x _
  have hWS : Y.mj.eW i x ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]
    exact LinearMap.mem_range_self _ _
  have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
      Submodule.comap (Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H)
        (LinearMap.range ((R.toCx3 F).w0C false i)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i x) ∈ LinearMap.range ((R.toCx3 F).w0C false i) := hle hWS
  rw [← (hR.partsW i).2] at h1
  have h4 : Y.mj.eW i x ∈ (⨆ p, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL :=
    Submodule.mem_map_of_mem (f := outL) h1
  rw [Submodule.map_iSup] at h4
  have h6 : (⨆ p, ((R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL) ≤ S.map (Y.mj.eW i) :=
    iSup_le fun p => (hUT p) ▸ h5 p
  obtain ⟨x', hx', hxx⟩ := h6 h4
  rw [← hinj hxx]
  exact hx'

end GlobalTheory.IsotSum

namespace GlobalTheory.IsotSum


set_option maxHeartbeats 1000000 in
theorem isotInternal_of_read : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hRk
  obtain ⟨cOf, h1, -, -⟩ := GlobalTheory.T.finiteTypes_via_full_heckeAlgebra_eigensystems hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost hRk
  show Rows.IsotInternal D.what₂
  intro j hj1 hjm
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i
  · rw [eq_top_iff, ← span_all hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i]
    refine iSup_le fun c => ?_
    rw [← (h1 i c).2]
    exact iSup_le fun σ => le_iSup (fun σ => D.what₂.isot ((i : ℕ) + 1) σ) σ.1

end GlobalTheory.IsotSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoiceGoodChartsEveryStageStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnChoice_goodCharts_every_stage : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi)), (∀ i hi, Finite (Ch i hi) ∧ I.IdY l Z u a i hi (eY i hi) ∧ ReadsOne I l Z u a i hi (chOf i hi) (Kc i hi) ∧ ∀ β, FunKilled ((Kc i hi) β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, ((Kc i hi) β).lev.chi κ ^ n = 1) ∧ Subsingleton (Ch 0 (Nat.zero_le _)) ∧ (∀ β, ((Kc 0 (Nat.zero_le _)) β).lev.Lb = F.to0.cls0.lev.Lb ∧ ((Kc 0 (Nat.zero_le _)) β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ ((Kc 0 (Nat.zero_le _)) β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : ((Kc 0 (Nat.zero_le _)) β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → ((Kc 0 (Nat.zero_le _)) β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, (((Kc 0 (Nat.zero_le _)) ((chOf 0 (Nat.zero_le _)) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.goodCharts_all | exact GlobalTheory.TwU.AtTrue.goodCharts_all | (intros; apply GlobalTheory.TwU.AtTrue.goodCharts_all <;> assumption)
end

