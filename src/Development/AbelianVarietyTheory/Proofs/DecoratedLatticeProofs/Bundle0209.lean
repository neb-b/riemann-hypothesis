module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0263
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPrimeLabelOperatorsEqChartHeckeOperators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealLastStageNormalizedOfScalarHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTwNorm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem orZero_of {X : Type} [Zero X] {p : X → Prop} {x : X} (hx : p x) : OrZero p x :=
  ⟨fun _ => hx, fun hn => absurd ⟨x, hx⟩ hn⟩

theorem baseW_of_given (hG : Given R F) : R.BaseW F := by
  obtain ⟨lev, grp, fam, models, chain, thP⟩ := hG.core
  exact ⟨lev, grp, fam, models,
    ⟨chain.ωY, chain.ωX, chain.vY, chain.vX, chain.ptY, chain.ptX, fun k hk => orZero_of fun t => chain.ItY t k hk,
      orZero_of chain.ItX, fun t k hk => orZero_of (chain.ioY t k (by omega)), fun t => orZero_of (chain.ioX t),
      fun t => orZero_of (chain.Th t)⟩,
    ⟨thP.ωP, thP.vP, thP.pt_theta, fun i => orZero_of (thP.ioP i), fun i t => orZero_of ⟨thP.thF_mem i t, thP.thF i t⟩,
      fun i t => orZero_of (thP.thG i t)⟩⟩

theorem alg_step {d I aa xy ipv P P' na : ℂ} (hna : na ≠ 0) (e1 : aa = na ^ 2) (e2 : P = P') (h1 : d * I = aa * xy)
    (h2 : I = ipv * P) : xy = d * P' / na ^ 2 * ipv := by
  subst e1 e2 h2
  field_simp
  linear_combination -h1

theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

theorem normX : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, NormX R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG h
  have hB := baseW_of_given R F hG
  have hm := hG.core.models
  obtain ⟨w0, v0, hw0⟩ : ∃ (w : R.cX.W) (v : R.MX.Vec), R.prX w (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hm.prX.1
    refine LinearMap.ext fun w => LinearMap.ext fun x => ?_
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v => simp [hc w v]
    | add x y hx hy => simp [map_add (f := _), hx, hy]
  obtain ⟨a, ha⟩ := riesz (R.prX.flip (PiTensorProduct.tprod ℂ v0))
  have ha' : ∀ w, R.prX w (PiTensorProduct.tprod ℂ v0) = ⟪a, w⟫_ℂ := fun w => ha w
  have hna : a ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [ha']; simp)
  have hv : ∀ τ, (v0 τ : R.MX.H τ) ≠ 0 := by
    intro τ h0
    apply hw0
    have : v0 τ = 0 := Subtype.ext h0
    rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ this, map_zero]
  haveI : Nontrivial R.cX.W := hm.cX.2.2.2.1
  have hd : (0 : ℝ) < Module.finrank ℂ R.cX.W := by exact_mod_cast Module.finrank_pos
  have hP : (0 : ℝ) < ∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2 :=
    Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.2 (hv τ)) 2
  have hA : (0 : ℝ) < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.2 hna) 2
  refine ⟨(Module.finrank ℂ R.cX.W : ℝ) * (∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2) / ‖a‖ ^ 2, by positivity, fun t => ⟨?_, ?_⟩⟩
  · have hi := GlobalTheory.DefiniteMult.top_injective R hm.inf hm.cX hm.prX hm.HX t
    refine ⟨fun x y e => ?_, fun z => ?_⟩
    · have e2 := (LinearEquiv.ofEq _ _ (h t)).injective e
      exact hi (congrArg Subtype.val e2)
    · obtain ⟨u, hu⟩ := (LinearMap.surjective_rangeRestrict _) ((LinearEquiv.ofEq _ _ (h t)).symm z)
      refine ⟨u, ?_⟩
      simp only [toCC, hu]
      exact (LinearEquiv.ofEq _ _ (h t)).apply_symm_apply z
  · intro ipD ip hM x y
    have hS := hM.schur (toCC R h t y) (toCC R h t x) (PiTensorProduct.tprod ℂ v0) (PiTensorProduct.tprod ℂ v0)
    have hS' := hS.trans (congrArg _ (hM.pure v0 v0))
    have hI := (_root_.GlobalTheory.Mem.SchurW.schurW D G Pl0 T A Ks R F hB t x y a a).2
    have hJ : (∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e x) g⟫_ℂ * ⟪a, R.cX.ext ((R.HX t).e y) g⟫_ℂ ∂(R.νX t)) =
        ip (toCC R h t y) (toCC R h t x) * ∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ := by
      refine Eq.trans ?_ hS'
      unfold Lift.pet
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have e3 : (((toCC R h t y : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e y) g) (PiTensorProduct.tprod ℂ v0) := rfl
      have e4 : (((toCC R h t x : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e x) g) (PiTensorProduct.tprod ℂ v0) := rfl
      simp only [e3, e4, ha', starRingEnd_apply]
      exact mul_comm _ _
    have e1 : ⟪a, a⟫_ℂ = ((‖a‖ : ℂ)) ^ 2 := inner_self_eq_norm_sq_to_K a
    have e2 : (∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ) = ∏ τ, ((‖(v0 τ : R.MX.H τ)‖ : ℂ)) ^ 2 :=
      Finset.prod_congr rfl fun τ _ => inner_self_eq_norm_sq_to_K _
    have hA' : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hna).ne'
    have H := alg_step hA' e1 e2 hI hJ
    rw [H]
    push_cast
    ring
end GlobalTheory.ChainTwNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPartHavePartParamsFirstChainMember
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw.LevelYZero
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levS_congr {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L L' : LevDat D.host.E ℂ V.rank)
    (h : ∀ x, x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L') :
    levS V β L = levS V β L' := by
  have e : Formalism.L2.DIV.lev D.sp.cm V.gram β L = Formalism.L2.DIV.lev D.sp.cm V.gram β L' := Subgroup.ext h
  unfold levS Lev.levG
  rw [e]

theorem principalRowLevelCharacter_trivial (k : GA D (Yc D 0)) : Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k = 1 := by
  unfold Lev.levChi Formalism.L2.DIV.levFn
  simp [LevCh.dat0, Lev.datY]
  exact Lev.subgroupCharExtension_one_apply _ _

theorem levS_datYt (t : T) : levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  refine levS_congr _ _ _ fun x => ?_
  show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
  unfold LevCh.datYt LevCh.dat0
  rw [Formalism.IndefR.Eqv.Act.mem_parLev_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi
    (R.xiR t) (fun _ => 1) Lev.Frm.B x]
  rfl

theorem levChi_datYt (t : T) : Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  funext k
  have h : Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k =
      Lev.levChi (Yc D 0) (R.βY 0) (Lev.flag1L (R.dat0 R.triv)) k := by
    unfold Lev.levChi
    congr 1
    have e1 : Formalism.L2.DIV.levFn (R.βY 0) (R.datYt t 0 R.triv) (Lev.finE (Yc D 0) k) =
        Formalism.L2.DIV.levFn (R.βY 0) (Lev.withP (R.datYt t 0 R.triv)
          (LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ))
          (Lev.finE (Yc D 0) k) := rfl
    rw [e1, Lev.levFn_withP]
    rw [show ext1 (LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ).H
        (⇑(LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ).chi)
        (rTup (R.βY 0) (R.datYt t 0 R.triv) (Lev.finE (Yc D 0) k)) = 1 from
          Lev.subgroupCharExtension_one_apply _ _, one_mul, Lev.levFn_flag1]
    unfold LevCh.datYt LevCh.dat0
    exact Formalism.IndefR.Eqv.Act.levFn_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le
      (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi (R.xiR t) (fun _ => 1) Lev.Frm.B _
  rw [h, principalRowLevelCharacter_trivial]
  unfold Lev.levChi Formalism.L2.DIV.levFn
  simp [LevCh.dat0, Lev.datY, Lev.flag1L, Lev.withP]
  exact Lev.subgroupCharExtension_one_apply _ _

theorem levChi_flat (t : T) (hr : D.R.r ≤ (stY R t 0).V.rank) (k : GA D (Yc D 0)) :
    Lev.levChi (flat (comR R t) (twR R t) 0 (stY R t 0) hr).V (flat (comR R t) (twR R t) 0 (stY R t 0) hr).β
      (flat (comR R t) (twR R t) 0 (stY R t 0) hr).L k = 1 := by
  unfold Lev.levChi Formalism.L2.DIV.levFn
  simp [flat, comR, twR, Lev.datY]
  exact Lev.subgroupCharExtension_one_apply _ _


open Classical in
theorem levS_flat_gen (Q : Finset (Pl D.host.E)) (hr : D.R.r ≤ (Yc D 0).rank)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    levS (Yc D 0) (R.βY 0) (Lev.datY (Yc D 0).rank D.R.r D.R.t 0 hr (R.Pg ∪ Q) ∅ ⟨trivAt R.Pg (R.Pg ∪ Q) D.R.r, 1⟩ χ ξ
      Lev.Frm.B) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  have hbt : ∀ (κ : Type) [CommRing κ] (g : GL (Fin (Yc D 0).rank) κ), g ∈ blockTri (blkOf (n := (Yc D 0).rank) D.R.r D.R.t) := by
    intro κ _ g
    show (g : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) κ).BlockTriangular _
    intro i j hij
    have hi : i.val < D.R.r := lt_of_lt_of_le i.2 Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le
    have hj : j.val < D.R.r := lt_of_lt_of_le j.2 Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le
    simp [blkOf, hi, hj] at hij
  refine levS_congr _ _ _ fun x => ?_
  show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
  simp only [LevCh.dat0, Lev.datY, eq_self_iff_true, if_true, ite_true, parLev, Subgroup.mem_inf, Subgroup.mem_iInf, mem_parah]
  constructor
  · rintro ⟨⟨⟨⟨hU, hSt⟩, hPg⟩, -⟩, hT⟩
    refine ⟨⟨⟨⟨hU, hSt⟩, fun i hi => hPg i (Finset.mem_union_left _ hi)⟩, fun i hi => absurd hi (Finset.notMem_empty _)⟩, ?_⟩
    show _ ∈ (⊥ : Subgroup (G0 R.Pg D.R.r))
    rw [Subgroup.mem_bot]
    funext PP
    exact hT ⟨PP.1, Finset.mem_union_left _ PP.2⟩ PP.2
  · rintro ⟨⟨⟨⟨hU, hSt⟩, -⟩, -⟩, hT⟩
    refine ⟨⟨⟨⟨hU, hSt⟩, fun i _ => ⟨hSt, hbt _ _⟩⟩, fun i hi => absurd hi (Finset.notMem_empty _)⟩, fun PP hP => ?_⟩
    exact congrFun (Subgroup.mem_bot.1 (show _ ∈ (⊥ : Subgroup (G0 R.Pg D.R.r)) from hT)) ⟨PP.1, hP⟩

theorem levS_flat (t : T) (hr : D.R.r ≤ (stY R t 0).V.rank) :
    levS (flat (comR R t) (twR R t) 0 (stY R t 0) hr).V (flat (comR R t) (twR R t) 0 (stY R t 0) hr).β
      (flat (comR R t) (twR R t) 0 (stY R t 0) hr).L = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) :=
  levS_flat_gen R (R.Q t) hr _ _

end GlobalTheory.ChainTw.LevelYZero

namespace GlobalTheory.ChainTw


open LevelYZero in
theorem rowPar_of_chain : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RowPar R := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F _hG hch hX t c
  obtain ⟨htw, hst, -, -, -⟩ := hch hX t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨hr, -, hflat⟩ := hst 0 hm
  have hc : (comR R t).Is := htw.com
  have hS : (comR R t).S = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
    unfold Com.S GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl comR
    congr
  have hrk : (Yc D 0).rank = D.R.r := le_antisymm Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0)
  set s' := flat (comR R t) (twR R t) 0 (stY R t 0) hr with hs'
  have hJ' : levS s'.V s'.β s'.L = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := levS_flat R t hr
  have hχ' : Lev.levChi s'.V s'.β s'.L = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) :=
    funext fun k => (levChi_flat R t hr k).trans (principalRowLevelCharacter_trivial R k).symm
  have hJ : levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := levS_datYt R t
  have hχ : Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) := levChi_datYt R t
  obtain ⟨hval, hHk, hconj⟩ := GlobalTheory.ConjVal.conj_values_hecke hP D (comR R t) hc 0 (Nat.zero_le _) s' hflat
  obtain ⟨-, hlat⟩ := GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D (comR R t) hc 0 (Nat.zero_le _) s' hflat
  obtain ⟨hsph, hsph', -⟩ := GlobalTheory.ChainOntoSph.level_spherical_off_S D (comR R t) hc 0 (Nat.zero_le _) s' hflat
  have hmem : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c,
      u ∈ partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) := by
    intro u hu
    rw [hJ', hχ', hS]
    exact (Submodule.mem_inf.1 hu).1
  have hCC : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c,
      PiTensorProduct.lift u ∈ s'.CC (comR R t) := by
    intro u hu
    refine (mem_multT _ _ _ _ _).2 ?_
    erw [LinearEquiv.symm_apply_apply]
    exact ((mem_partFull _ _ _ _ _ _ _).1 (hmem u hu)).1

  have hkey : ∀ y : s'.CC (comR R t), PiTensorProduct.lift.symm (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈
      partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) → ∀ w,
      (∀ k ∈ levS s'.V s'.β s'.L, ∀ g, (fun g => conj (PiLocalization₂.val y w g)) (g * k) =
        (fun k => conj (Lev.levChi s'.V s'.β s'.L k)) k * (fun g => conj (PiLocalization₂.val y w g)) g) ∧
      (∀ P d Rr, Hecke₂ s'.V (levS s'.V s'.β s'.L) (fun k => conj (Lev.levChi s'.V s'.β s'.L k)) (comR R t).S P d Rr →
        heckeLin s'.V Rr (fun g => conj (PiLocalization₂.val y w g)) = c P d • (fun g => conj (PiLocalization₂.val y w g))) ∧
      (fun g => conj (PiLocalization₂.val y w g)) ∈ GlobalTheory.FinZeta.bddAut s'.V := by
    intro y hy w
    obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev⟩ := hval y w
    have hb : PiLocalization₂.val y w ∈ GlobalTheory.FinZeta.bddAut s'.V := ⟨hcont, hinv, C, hC⟩
    have heig := _root_.GlobalTheory.HeckeAdjEigen.heckeLin_eq_conj_of_dualLab D s'.V _ _ (comR R t).S hsph (PiLocalization₂.val y w) hb hlev c
      (fun P d Rr hR => val_hecke_of_mem_partFull y _ hy P d Rr hR w)
    refine ⟨fun k hk g => ?_, fun P d Rr hR => ?_, ?_⟩
    · show conj (PiLocalization₂.val y w (g * k)) = _
      rw [hlev k hk g, map_mul]
    · have h1 := heig P d Rr ((hHk P d Rr).2 hR)
      have h2 := hconj Rr (PiLocalization₂.val y w)
      rw [h2, h1]
      funext g
      simp
    · refine ⟨Complex.continuous_conj.comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
      · show conj (PiLocalization₂.val y w (γ * g)) = conj (PiLocalization₂.val y w g)
        rw [hinv γ hγ g]
      · simpa using hC g

  have hiff : ∀ y : s'.CC (comR R t), PiTensorProduct.lift.symm (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈
      partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) → ∀ w B, PiLocalization₂.val y w ≠ 0 →
      (ParFun (comR R t) s' (PiLocalization₂.val y w) B ↔
        GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B) := by
    intro y hy w B h0
    obtain ⟨hl, hh, -⟩ := hkey y hy w
    have hne : (fun g => conj (PiLocalization₂.val y w g)) ≠ 0 := by
      intro h
      apply h0
      funext g
      simpa using congrFun h g
    unfold ParFun
    rw [hlat, ← hS, ← hrk]
    exact GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph' hne hl hh B
  have hy : ∀ u (hu : u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c),
      PiTensorProduct.lift.symm (((⟨PiTensorProduct.lift u, hCC u hu⟩ : s'.CC (comR R t))) :
        SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈
      partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) := by
    intro u hu
    show PiTensorProduct.lift.symm (PiTensorProduct.lift u) ∈ _
    rw [LinearEquiv.symm_apply_apply]
    exact hmem u hu
  refine ⟨fun hne => ?_, fun u hu => ?_⟩
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set y : s'.CC (comR R t) := ⟨PiTensorProduct.lift u, hCC u hu⟩ with hydef
    have hl0 : (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ≠ 0 := by
      intro h
      exact hu0 (PiTensorProduct.lift.injective (h.trans (map_zero _).symm))
    obtain ⟨w, hw⟩ : ∃ w, PiLocalization₂.val y w ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hl0 (LinearMap.ext hh)
    obtain ⟨hl, hh, hb⟩ := hkey y (hy u hu) w
    have hne' : (fun g => conj (PiLocalization₂.val y w g)) ≠ 0 := by
      intro h
      apply hw
      funext g
      simpa using congrFun h g
    obtain ⟨B, hB, -⟩ := GlobalTheory.FinZeta.ParamBound.exists_param_bounded D s'.V _ _ (comR R t).S hsph' _ hb hne' hl c hh
    refine ⟨B, (hiff y (hy u hu) w B hw).1 ?_⟩
    unfold ParFun
    rw [hlat]
    exact hB
  · have hu' : PiTensorProduct.lift u ∈ (stY R t 0).CC (comR R t) := by
      refine (mem_multT _ _ _ _ _).2 ?_
      erw [LinearEquiv.symm_apply_apply]
      show u ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv))
        (Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv))
      rw [hJ, hχ]
      exact ((mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 hu).1).1
    refine ⟨hu', fun hu0 B hB => ⟨?_, fun w hw => ?_⟩⟩
    · intro h
      apply hu0
      have h1 : PiTensorProduct.lift u = 0 := congrArg Subtype.val h
      exact PiTensorProduct.lift.injective (h1.trans (map_zero _).symm)
    · exact (hiff ⟨PiTensorProduct.lift u, hCC u hu⟩ (hy u hu) w B hw).2 hB

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurProductTypingsAgreeThetaChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.IPDictPf

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem isInnerProduct_of_isMet' (t : T) (k : ℕ) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) (x y : (stY R t k).CC (comR R t)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t k (PiTensorProduct.lift.symm x.1) (PiTensorProduct.lift.symm y.1) (ip y x) := by
  intro v v'
  have h1 := hm.integ y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  have h2 := hm.schur y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  rw [hm.pure v' v] at h2
  have e : (fun g => star ((PiTensorProduct.lift.symm x.1) v g) * (PiTensorProduct.lift.symm y.1) v' g) =
      fun g => PiLocalization₂.val y (PiTensorProduct.tprod ℂ v') g * conj (PiLocalization₂.val x (PiTensorProduct.tprod ℂ v) g) := by
    funext g; rw [mul_comm]; rfl
  refine ⟨?_, ?_⟩
  · exact (congrArg (fun F => IntegrableOn F (stY R t k).fd (stY R t k).ν) e).mpr h1
  · exact (congrArg (fun F : GA D (stY R t k).V → ℂ => ∫ g in (stY R t k).fd, F g ∂(stY R t k).ν) e).trans h2

theorem exists_tprod_ne {k : ℕ} (w : SmT (R.MY k)) (hw : w ≠ 0) : ∃ v : (R.MY k).Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra h
  push_neg at h
  have hid : (LinearMap.id : SmT (R.MY k) →ₗ[ℂ] SmT (R.MY k)) = 0 :=
    PiTensorProduct.ext (MultilinearMap.ext fun v => by simpa using h v)
  exact hw (by simpa using LinearMap.congr_fun hid w)

theorem exists_vec (hC : R.IsChain) (t : T) {k : ℕ} (hk : k < D.R.m) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) :
    ∃ v : (R.MY k).Vec, ∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ ≠ 0 := by
  have hw : ∃ w : SmT (R.MY k), w ≠ 0 := by
    by_cases hkk : k + 1 < D.R.m
    · by_contra h
      push_neg at h
      exact (hC.ItY t k hkk).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItY k φ x))
    · obtain rfl : k = D.R.m - 1 := by omega
      by_contra h
      push_neg at h
      exact (hC.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItX φ x))
  obtain ⟨w, hw⟩ := hw
  obtain ⟨v, hv⟩ := exists_tprod_ne R w hw
  refine ⟨v, fun h0 => ?_⟩
  have hp := hm.posD (PiTensorProduct.tprod ℂ v) hv
  rw [hm.pure v v] at hp
  change 0 < (∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ).re at hp
  rw [h0] at hp
  simp at hp

theorem ipDict (R : RealDat D A Ks) (F : Face D A) (hG : Given R F) : IPDict R := by
  intro t k hk ipD ip hm x y a
  obtain ⟨v, hv⟩ := exists_vec R hG.core.chain t hk hm
  exact ⟨fun h => hasPeterssonInner_unique _ _ _ _ _ v hv h (isInnerProduct_of_isMet' R t k hm x y), fun h => h ▸ isInnerProduct_of_isMet' R t k hm x y⟩

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → IPDict R := fun R F hG => ipDict R F hG

end GlobalTheory.ChainTw.IPDictPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelImageRationalStabilizerPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem toH_rat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (a : GA D (D.sp.X 0)), a ∈ GQ (D.sp.X 0) → ∃ γ : Gam X u, iotaI X u γ = (B.toH a).1 ∧ iotaF X u γ = (B.toH a).2 := by
  intro D X h u ψ B a ha
  have hrat : embA B.d B.o a ∈ GQ (D.sp.Y 0) := by
    have e : embA B.d B.o a = B.d.emb0 (B.o.emb (a, 1)) := rfl
    rw [e]
    exact B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ ha (one_mem _))
  have k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset → castGA e x ∈ I'.GFset := by
    intro I I' e x hx
    subst e
    exact hx
  have hr : iotaX X h (embA B.d B.o a) ∈ X.B.I.GFset :=
    k h.symm _ ((Formalism.IndefR.RationalEmbedding.iota_rat D _).1 hrat)
  have hH := (B.tieH (embA B.d B.o a)).1 ⟨a, rfl⟩
  exact ⟨⟨iotaX X h (embA B.d B.o a), Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_prod.2 hH⟩⟩, rfl, rfl⟩

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPrimeLabelOperatorsEqChartHeckeOperatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (opOf hyp)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_prime_label_operators_eq_chart_hecke_operators : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ Kv V v, π (embV V v k) u = u) → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ k ≤ V.rank, opOf π w (Finsupp.single (splitLab V.rank k) 1) u = heckeVec ((π.comp (embV V v)).comp e.symm.toMonoidHom) (KGL w (n := V.rank)) (fun g => Tj ℂ V.rank (Ov D.host.E w) ϖ k g⁻¹) u ∧ opOf π w (Finsupp.single (dualLab (splitLab V.rank k)) 1) u = heckeVec ((π.comp (embV V v)).comp e.symm.toMonoidHom) (KGL w (n := V.rank)) (Tj ℂ V.rank (Ov D.host.E w) ϖ k) u := by
  first | exact @GlobalTheory.ChainOnto.LabChart.split_label_ops | exact GlobalTheory.ChainOnto.LabChart.split_label_ops | (intros; apply GlobalTheory.ChainOnto.LabChart.split_label_ops <;> assumption)
end

