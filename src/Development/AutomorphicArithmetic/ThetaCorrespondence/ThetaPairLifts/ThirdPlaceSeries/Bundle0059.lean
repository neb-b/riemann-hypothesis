module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0056

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActMemMK
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TieMK
theorem act_mem_MK_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (g : p.P.Gp) f, f ∈ (p.R.toRealDat.FW i).MK → (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).MK := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p _ _ i g f hf
  exact ((GlobalTheory.RealGeoIn.mkStable_of_rhoGeo p.fw p.pins p.rhoGeo i) g f).2 hf
end GlobalTheory.TieMK
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhit
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.ShareOn.WhitBase
section SlopeTestRemainingChoices
open Formalism.L2.DIV
variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}
end SlopeTestRemainingChoices
section Comparison₂
open Formalism.L2.DIV Formalism.BasicNotions
variable {D : D7} {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G}
  {ψs : Ps →* D.what₂.LLˣ} {eG : G ≃* G0g D.nd} {Pg : Finset (Pl D.host.E)}
  {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg} {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
  {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}
end Comparison₂
end GlobalTheory.ShareOn.WhitBase
namespace GlobalTheory.ShareOn
open GlobalTheory.ShareOn.WhitBase
open Formalism.L2.DIV in
theorem isWhit_and_eq_embLL_inv_and_halfUnip : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → ∃ (lam : (p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom) →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), GlobalTheory.BadCount.IsWhit D _ lam ψ ∧ (∀ (g : p.P.P0) (h : (p.R.eG.trans p.cG) g ∈ p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom), ((lam ⟨_, h⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0⁻¹ g : D.what₂.LLˣ) : D.what₂.LL)) ∧ HalfUnip p p.P.P0 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hR
  obtain ⟨Pg, pl, res, ψ', eC, hL, -⟩ := hR.psi
  rw [p.eGtie] at hL
  unfold HalfUnip
  generalize p.R.eG.trans p.cG = e at hL ⊢
  let ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ := fun kv =>
    D.what₂.embLL.toMonoidHom.compAddChar
      ((ψ' (pl kv).1).compAddMonoidHom ((res kv).symm.toAddMonoidHom.comp (-AddMonoidHom.id _)))
  have hψ : ∀ kv c, ψ kv c = D.what₂.embLL (ψ' (pl kv).1 ((res kv).symm (-c))) := fun _ _ => rfl
  let iso := p.P.P0.equivMapOfInjective e.toMonoidHom e.injective
  have hiso : ∀ g0 : p.P.P0, ((iso g0 : p.P.P0.map e.toMonoidHom) : G0g D.nd) = e g0 := fun _ => rfl
  let lam : (p.P.P0.map e.toMonoidHom) →* ℂˣ :=
    (Units.map D.what₂.embLL.toMonoidHom).comp (p.P.ψ0⁻¹.comp iso.symm.toMonoidHom)
  have hlam : ∀ g, ((lam g : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0 (iso.symm g) : D.what₂.LLˣ) : D.what₂.LL)⁻¹ := by
    intro g
    show D.what₂.embLL (((p.P.ψ0 (iso.symm g))⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = _
    rw [Units.val_inv_eq_inv_val]
  refine ⟨lam, ψ, ⟨?_, ?_, ?_⟩, ?_, ⟨0, ?_⟩⟩
  · intro kv h1
    apply hL.gen (pl kv).1 (pl kv).2
    ext x
    have h2 : ψ kv (-(res kv x)) = 1 := by rw [h1, AddChar.one_apply]
    rw [hψ, neg_neg, RingEquiv.symm_apply_apply] at h2
    rw [AddChar.one_apply]
    apply D.what₂.embLL.injective
    rw [h2, map_one]
  · intro g
    rw [Subgroup.mem_map_equiv, mem_iff_of_lvlTie hL]
    simp only [MulEquiv.apply_symm_apply]
  · intro g
    have hg0 : e (iso.symm g) = (g : G0g D.nd) := by rw [← hiso, MulEquiv.apply_symm_apply]
    have hg : eC (iso.symm g) ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ').H := (hL.p0 _).1 (iso.symm g).2
    rw [hlam, chi_of_lvlTie hL _ hg, ← Finset.prod_inv_distrib, map_prod]
    rw [← Fintype.prod_equiv pl (fun kv => D.what₂.embLL (ψ' (pl kv).1 (edgeSum supEdge (eC (iso.symm g) (pl kv))))⁻¹)
      _ (fun _ => rfl)]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [← hg0, hL.comp _ kv]
    simp only [entN_map]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← edgeSum_supEdge_eq, hψ, ← map_neg, RingEquiv.symm_apply_apply, AddChar.map_neg_eq_inv]
  · intro g h
    have : iso.symm ⟨_, h⟩ = g := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    rw [hlam, this, ← Units.val_inv_eq_inv_val]
    rfl
  · intro g hg v
    exact (mem_iff_of_lvlTie hL g).1 hg ⟨0, v⟩
end GlobalTheory.ShareOn
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelRowsEqDimension
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR
namespace GlobalTheory.Fc.Ind
theorem base_level_rows_eq_dimension_alt : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.summandDegreeZero D O c b := by
  intro D O c b
  have h1 : D.what₂.D0 = b.P.S0.D := GlobalTheory.rowSide_card_eq_of_coord O.ex.p0.s D.what₂.onb0 b.P.I.eRR0
  have key : ∀ (Z Z' : DefSub b.P.A3.fam3.amb3) (S : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z))
      (S' : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z')), Z = Z' → HEq S S' → S.D = S'.D := by
    intro Z Z' S S' h h'
    subst h
    cases eq_of_heq h'
    rfl
  have h2 := key _ _ _ _ b.B.Q.zs b.B.Q.s0
  have h3 := b.B.Q.zs
  unfold _root_.GlobalTheory.Fc.Ind.summandDegreeZero
  rw [h1, ← h2, ← h3]
  rfl
end GlobalTheory.Fc.Ind
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatch
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
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
namespace GlobalTheory.MiTop
theorem botHyp_match_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → W.Q.Rl.toRealDat.IsModels ∧ IsInfFam W.Q.Rl.θ ∧ IsStdChar D W.Q.Rl.ψ (-1) ∧ (∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (z * (show GA D (D.sp.Y 0) from W.Q.tS))) ∧ (∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.realCharacter W k ≠ 0) ∧ ∀ e : W.Q.Rl.HE.H, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) → _root_.GlobalTheory.MiTop.rowFormOfVector W e ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W := by
  intro D L hT Gi Gl Kc Yd cX ex W hB
  have hι : W.Q.ιS = (Formalism.L2.SG.RowsJoinPinned.iotaX W.S.X W.Q.instEq).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D W.S.X W.Q.instEq W.Q.ιS).1 W.Q.ιS_eq
  have e : ∀ g, W.Q.ιS g = Formalism.L2.SG.RowsJoinPinned.iotaX W.S.X W.Q.instEq g := fun g => by rw [hι]; rfl
  have hC := (hB.pins.tSpin hB.see.1).1
  have key : ∀ k, (k ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ ((show GA D (D.sp.Y 0) from W.Q.tS)⁻¹)⁻¹ * k * (show GA D (D.sp.Y 0) from W.Q.tS)⁻¹ ∈ rowJ W.S.X W.Q.instEq) ∧
      (k ∈ _root_.GlobalTheory.MiTop.rJ_z W → rowChi W.S.X W.Q.instEq (((show GA D (D.sp.Y 0) from W.Q.tS)⁻¹)⁻¹ * k * (show GA D (D.sp.Y 0) from W.Q.tS)⁻¹) = _root_.GlobalTheory.MiTop.realCharacter W k) := by
    intro k
    obtain ⟨h1, h2⟩ := hC k
    refine ⟨h1.trans ?_, fun hk => ?_⟩
    · exact (show ∀ a b : W.S.X.B.I.GA, a = b → (a ∈ seeKS W.S.X ↔ b ∈ seeKS W.S.X) from fun a b h => h ▸ Iff.rfl) _ _ (e _)
    · exact (congrArg (seeChiS W.S.X) (e _)).symm.trans (h2 hk)
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group W.S.X
  refine ⟨W.Q.charW.base.models, W.Q.charW.base.models.inf, W.Q.stdChar, ?_, ?_, ?_⟩
  · intro z hz hzc
    have hz' := Subgroup.mem_center_iff.1 hzc
    have hconj : ∀ t k : GA D (D.sp.Y 0), ((z * t)⁻¹)⁻¹ * k * (z * t)⁻¹ = (t⁻¹)⁻¹ * k * t⁻¹ := by
      intro t k
      rw [inv_inv, inv_inv, mul_inv_rev]
      calc z * t * k * (t⁻¹ * z⁻¹) = z * (t * k * t⁻¹) * z⁻¹ := by group
        _ = t * k * t⁻¹ := by rw [← hz' (t * k * t⁻¹)]; group
    refine ⟨mul_mem hz hB.pins.tSfin, fun k => ?_⟩
    have h4 := key k
    rw [← hconj _ k] at h4
    exact h4
  · intro k hk
    have hm := (key k).1.1 hk
    rw [← (key k).2 hk]
    simp only [rowJ, Set.mem_preimage, Set.mem_setOf_eq] at hm
    simp only [rowChi]
    intro h0
    have hn := hK.2.2.2.2 _ hm.2
    rw [star_eq_zero] at h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  · intro x hx
    refine (mem_multT _ _ _ _ _).2 ?_
    simp only [_root_.GlobalTheory.MiTop.rowFormOfVector, LinearEquiv.symm_apply_apply]
    exact goodPart_le _ _ _ _ _ hx
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralIsomRamified
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
set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.Mi.CenAct in
theorem GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u) z, d.Pin z → ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ C C₀, _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → _root_.GlobalTheory.MiTop.IsColumnForm W u C₀ φ → ∀ ξ, d.B.colForm C₀.1 ξ = rTrans d.a⁻¹ (d.B.colForm C.1 ξ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB u d z hP
  have hδ : ∀ k : Hfin W.S.X u, (d.B.toH d.a).2 * k = k * (d.B.toH d.a).2 := toH_snd_comm d.B hP.cen
  have hta : d.B.toH d.a = (1, (d.B.toH d.a).2) := Prod.ext (toH_fst d.B hP.fin) rfl
  generalize (d.B.toH d.a).2 = δ at hδ hta
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)
  let col : D.what₂.Mu u →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    e.symm.toLinearMap ∘ₗ (Submodule.inclusion hram) ∘ₗ (D.eMu u).toLinearMap
  have hcol : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (col φ) =
      ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) := fun φ =>
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram (D.eMu u φ)))
  let mv : Cu W.S.X u W.S.Y.hK →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    (Formalism.L2.SG.ColDict.rtr W.S.X δ).restrict (fun T hT => rtr_mem_Cu W.S.Y.hK hδ hT)
  have hmv : ∀ T, (mv T).1 = Formalism.L2.SG.ColDict.rtr W.S.X δ T.1 := fun T => rfl
  have hmem : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) ∈ (D.mem u).A.Mram := fun φ =>
    GlobalTheory.MiTop.CenIsom.ram_rtr (W.S.tr u) W.S.Y.hK (W.S.lev u) (W.S.into u) (W.S.bij u) δ hδ (col φ) (mv (col φ)) (hmv _) (by rw [hcol]; exact (D.eMu u φ).2)
  let g0 : D.what₂.Mu u →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
    Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK ∘ₗ mv ∘ₗ col
  let fL : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := (D.eMu u).symm.toLinearMap ∘ₗ g0.codRestrict _ hmem
  have hfL : ∀ φ, ((D.eMu u (fL φ) : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) =
      Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) := fun φ => by
    have h1 : D.eMu u (fL φ) = ⟨Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)), hmem φ⟩ :=
      (D.eMu u).apply_symm_apply _
    rw [h1]
  clear_value fL g0 mv col e
  have hinner : ∀ x y, ⟪fL x, fL y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => by
    refine ((D.eMu_isom u (fL x) (fL y)).trans ?_).trans (D.eMu_isom u x y).symm
    refine (congrArg₂ ((D.fm u).ipC 0) (hfL x) (hfL y)).trans ?_
    refine (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_rtr_eq W.S hB.fin u δ hδ (col x) (col y) (mv (col x)) (mv (col y)) (hmv _) (hmv _)).trans ?_
    exact congrArg₂ ((D.fm u).ipC 0) (hcol x) (hcol y)
  let Li := fL.isometryOfInner hinner
  haveI : FiniteDimensional ℂ (D.mem u).A.Mu0 := (D.mem u).A.Mu0_fd
  haveI : FiniteDimensional ℂ (D.mem u).A.Mram := Submodule.finiteDimensional_of_le hram
  haveI : FiniteDimensional ℂ (D.what₂.Mu u) := LinearEquiv.finiteDimensional (D.eMu u).symm
  have hsurj : Function.Surjective Li := (LinearMap.injective_iff_surjective (f := Li.toLinearMap)).1 Li.injective
  refine ⟨LinearIsometryEquiv.ofSurjective Li hsurj, ?_⟩
  intro φ C C₀ hC hC₀ ξ
  have e1 : C = mv (col φ) := (W.S.bij u).1 (hC.trans (hfL φ))
  have e2 : C₀ = col φ := (W.S.bij u).1 (hC₀.trans (hcol φ).symm)
  rw [e1, e2]
  funext g
  simp only [SBes.colForm, rTrans]
  rw [hmv]
  have h4 : d.B.toH (g * d.a⁻¹) * (1, δ) = d.B.toH g :=
    (congrArg (fun y => d.B.toH (g * d.a⁻¹) * y) hta.symm).trans
      ((toH_mul d.B _ _).symm.trans (congrArg d.B.toH (inv_mul_cancel_right g d.a)))
  exact (congrArg ((col φ).1 ξ) h4).symm
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCore
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField
noncomputable section
namespace GlobalTheory.CovTop
open Formalism.L2.DIV
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem chi_mul_psi_inv_mem_core_alt (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m) : p.PointConditions' → RecTied D L →
    ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈
      Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  intro _ _ u
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hN0 : p.T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := p.T.Q.l.three_le; omega) p.T.Q.l.A_pos.ne'
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hN : ∀ PP : p.R.Pg, (p.T.Q.l.M' : kP PP.1) = 0 := by
    intro PP
    obtain ⟨k, hk⟩ := (hL.Pg PP.1).1 PP.2
    have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.1.under (𝓞 D.host.K)).asIdeal := by
      rw [hk]; exact p.R.C.P.pb_over k
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
      change _ ∈ Ideal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) PP.1.asIdeal at h2
      rwa [Ideal.mem_comap, map_natCast] at h2
    have h3 : ((D.host.g k : ℕ) : kP PP.1) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.1.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h1
    have hk' : D.host.g k ∣ p.T.Q.l.M' := by
      refine dvd_trans ?_ (Nat.dvd_lcm_left p.T.Q.l.M p.T.Q.l.A)
      rw [hM]
      fin_cases k
      exacts [dvd_mul_right _ _, dvd_mul_left _ _]
    obtain ⟨c, hc⟩ := hk'
    rw [hc, Nat.cast_mul, h3, zero_mul]
  have hu : p.R.eG u ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG u) ∈ (p.F.lv2.lvl false).P
    simp
  have key : ∀ X : LevelP p.R.Pg D.R.r ℂ, X = P0 p.R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
      (∀ PP, g PP ∈ unip (kP PP.1) D.R.r) ∧ X.chi ⟨g, hg⟩ ^ p.T.Q.l.M' = 1 := by
    rintro X rfl g hg
    exact ⟨fun PP => (Subgroup.mem_pi _).1 hg PP (Set.mem_univ _), unipotentTypeLevel_char_pow_eq_one _ _ ψ0 _ hN _⟩
  obtain ⟨hun, hpow⟩ := key _ hlev _ hu
  have e1 : (p.R.levR p.F.lv2 false).chi ⟨p.R.eG u, hu⟩ =
      Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((p.F.lv2.lvl false).ψ u) := by
    show Units.map _ ((p.F.lv2.lvl false).ψ _) = _
    congr 2
    exact Subtype.ext (by show p.R.eG.symm (p.R.eG u) = u; exact p.R.eG.symm_apply_apply _)
  have h5 : (((p.F.lv2.lvl false).ψ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    apply D.what₂.embLL.injective
    have := congrArg (fun z : ℂˣ => (z : ℂ)) (e1 ▸ hpow)
    simpa using this
  have hchi : (p.R.toRealDat.FW i).chi u = 1 := by
    apply Units.ext
    apply D.what₂.embLL.injective
    rw [hB.grp.chiW i u, Finset.prod_eq_one (fun PP _ => by rw [det_of_mem_unip (hun PP), map_one, Units.val_one]),
      Units.val_one, map_one]
  rw [hchi, one_mul]
  have hy : (((p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_pow, h5, inv_one]
  have hz : IsPrimitiveRoot (⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta p.T.Q.l.M', p.T.Q.c.zeta_mem⟩ : p.T.Q.c.F) p.T.Q.l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := p.T.Q.c.F.val) (Complex.isPrimitiveRoot_exp _ hN0) Subtype.val_injective
  have hz' := hz.map_of_injective (f := algebraMap p.T.Q.c.F D.what₂.LL) (algebraMap p.T.Q.c.F D.what₂.LL).injective
  haveI : NeZero p.T.Q.l.M' := ⟨hN0⟩
  obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hy
  exact ⟨_ ^ k, by rw [map_pow, hk]⟩
end GlobalTheory.CovTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CofiniteLabelsAt
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameAutCof
theorem cofinite_labels_at_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite :=
  fun p _ _ j _ _ _ _ w _ _ hs => cofinite_labels p j (p.R.mu w) hs.1.ne_zero
end GlobalTheory.FrameAutCof
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColCrdHolds
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
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem colC_eq_lin_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) :
    _root_.GlobalTheory.MiTop.columnOfCoordinates W u = Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1))) := by
  funext x
  exact (Fintype.linearCombination_apply ℂ _ x).symm
theorem colCrd_of_real_pack : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.ColumnCoordinateCondition W := by
  intro D L hT Gi Gl Kc Yd cX ex W u
  have hbij : Function.Bijective (Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1)))) :=
    GlobalTheory.Mem.SJ.lin_bijective_of_form D.what₂.embLL (D.jN u) (D.div.Nu u).b (W.P.I.eNu u) (D.jN_basis u)
  have hrat : ∀ x, _root_.GlobalTheory.MiTop.columnOfCoordinates W u (cpt D.what₂.embLL x) = D.jN u (W.P.I.eNu u x) := fun x => by
    rw [_root_.GlobalTheory.MiTop.colC_eq_lin_alt]
    exact GlobalTheory.Mem.SJ.lin_cpt_semilinear D.what₂.embLL ((D.jN u).comp (W.P.I.eNu u).toLinearMap) x
  refine ⟨_root_.GlobalTheory.MiTop.colC_eq_lin_alt W u ▸ hbij, hrat, 1, one_pos, fun x => ?_⟩
  rw [one_mul]
  let e : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) ≃ₗ[ℂ] D.what₂.Mu u :=
    LinearEquiv.ofBijective (Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1)))) hbij
  have hv0 : W.P.A3.A.v0 = InfinitePlace.mk D.what₂.embLL := W.Q.Rl.hv0
  have htw : ∀ a, (InfinitePlace.mk D.what₂.embLL).embedding a =
      Formalism.IndefR.Links.cj (Formalism.L2.SG.JoinSI.twQ W.P) (D.what₂.embLL a) := by
    intro a
    rw [← hv0]
    exact _root_.Formalism.L2.SG.JoinSI.embedding_eq_cj_twQ_embLL W.Q a
  have key := GlobalTheory.Mem.SJ.fnorm_cjv_eq_norm D.what₂.LL D.what₂.embLL (Formalism.L2.SG.JoinSI.twQ W.P) htw
    (GlobalTheory.Mem.SJ.colNorm_exists_im_ne_zero _) (D.div.Nu u) _ (W.P.NuC (W.P.I.wU u)) _ (W.P.I.eNu u)
    (W.P.tied.div.cols.Nu u) (D.what₂.Mu u) (D.jN u) e.symm (GlobalTheory.Mem.SJ.colNorm_normAt_column D u)
    (fun y => by
      rw [LinearEquiv.symm_symm]
      exact (congrFun (_root_.GlobalTheory.MiTop.colC_eq_lin_alt W u) _).symm.trans (hrat y)) (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x)
  have hx : e.symm (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x) = x := by
    rw [LinearEquiv.symm_apply_eq]
    exact congrFun (_root_.GlobalTheory.MiTop.colC_eq_lin_alt W u) x
  rw [hx] at key
  have hv : W.P.A3.fam3.base3.v0 = InfinitePlace.mk D.what₂.embLL := hv0
  rw [hv]
  exact key
end GlobalTheory.MiTop
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LUnifRealTBStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lUnif_of_nV_ge : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.LUnif := by
  first | exact @_root_.GlobalTheory.LocalUniformizerReal.lUnif_of_nV_ge_of_bundle | exact _root_.GlobalTheory.LocalUniformizerReal.lUnif_of_nV_ge_of_bundle | (intros; apply _root_.GlobalTheory.LocalUniformizerReal.lUnif_of_nV_ge_of_bundle <;> assumption)
end
end

