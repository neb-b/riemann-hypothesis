module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0090
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnramifiedFactorEqOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0027
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EntInSandwich
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioMap
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

abbrev GG (p : PlF D) : Type := GLp p × (GLp p)ᵐᵒᵖ

def KP (p : PlF D) : Subgroup (GG p) where
  carrier := {x | Formalism.MainNotions.S.TieN.IntLow (M p) ((x.1 : GLp p) : MP p) ∧
    Formalism.MainNotions.S.TieN.IntUp (M p) ((x.2.unop : GLp p) : MP p)}
  one_mem' := ⟨ZsVolGrp.intLow_one _, ZsVolGrp.intUp_one _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1 * y.1 : GLp p)) : MP p)
      rw [Units.val_mul]; exact ZsVolGrp.intLow_mul _ hx1 hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (((x.2 * y.2).unop : GLp p) : MP p)
      rw [MulOpposite.unop_mul, Units.val_mul]; exact ZsVolGrp.intUp_mul _ hy2 hx2
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1)⁻¹ : GLp p) : MP p)
      rw [Matrix.coe_units_inv]; exact (ZsVolGrp.intLow_inv _ hx1).1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) ((((x.2)⁻¹).unop : GLp p) : MP p)
      rw [MulOpposite.unop_inv, Matrix.coe_units_inv]; exact (ZsVolGrp.intUp_inv _ hx2).1

def StabX (p : PlF D) (X : MP p) : Subgroup (GG p) where
  carrier := {x | ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p) = X}
  one_mem' := by simp
  mul_mem' := by
    rintro x y hx hy
    show ((x.1 * y.1 : GLp p) : MP p) * X * (((x.2 * y.2).unop : GLp p) : MP p) = X
    rw [MulOpposite.unop_mul, Units.val_mul, Units.val_mul]
    calc (x.1 : MP p) * (y.1 : MP p) * X * (((y.2.unop : GLp p) : MP p) * ((x.2.unop : GLp p) : MP p))
        = (x.1 : MP p) * ((y.1 : MP p) * X * ((y.2.unop : GLp p) : MP p)) * ((x.2.unop : GLp p) : MP p) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [show (y.1 : MP p) * X * ((y.2.unop : GLp p) : MP p) = X from hy]; exact hx
  inv_mem' := by
    rintro x hx
    have hx' : ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p) = X := hx
    show (((x.1)⁻¹ : GLp p) : MP p) * X * ((((x.2)⁻¹).unop : GLp p) : MP p) = X
    rw [MulOpposite.unop_inv]
    have h1 : (((x.1)⁻¹ : GLp p) : MP p) * (x.1 : MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : ((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    conv_lhs => rw [← hx']
    calc (((x.1)⁻¹ : GLp p) : MP p) * ((x.1 : MP p) * X * ((x.2.unop : GLp p) : MP p)) *
          (((x.2.unop)⁻¹ : GLp p) : MP p)
        = ((((x.1)⁻¹ : GLp p) : MP p) * (x.1 : MP p)) * X *
            (((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p)) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

variable {p : PlF D}

def g0 (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) : GG p :=
  (⟨lOf δ M p L U, lOf δ M p L⁻¹ U⁻¹,
      (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp (lp_inv M δ hA L U hL hU), lp_inv M δ hA L U hL hU⟩,
    MulOpposite.op ⟨ρOf δ M p L U, ρOf δ M p L⁻¹ U⁻¹, up_inv M δ hA L U hL hU,
      (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp (up_inv M δ hA L U hL hU)⟩)

def XP (w : Point D.host.E (D.R.rS + 1)) (L U : Formalism.L2.SG.PairVal.MatR D) : MP p :=
  lOf δ M p L U * Y0 M δ u u' w p * ρOf δ M p L U

def Ag (w : Point D.host.E (D.R.rS + 1)) : Subgroup (GG p) := (AP M δ u u' w p).map (StP M δ u u' w p).subtype

def Cg (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) : Subgroup (GG p) :=
  (CPL M δ u u' w hA L U hL hU).map (StP M δ u u' w p).subtype

theorem idxRatio_map {G : Type} [Group G] (S : Subgroup G) (A C : Subgroup S) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A C = Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A.map S.subtype) (C.map S.subtype) := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [Subgroup.relIndex_map_map_of_injective _ _ S.subtype_injective,
    Subgroup.relIndex_map_map_of_injective _ _ S.subtype_injective]

def CShapeAt (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) : Prop :=
  Cg M δ u u' w hA L U hL hU = cj (g0 M δ hA L U hL hU) (KP M p ⊓ StabX p (XP M δ u u' w L U))

def CountAt (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) (v : ℝ) : Prop :=
  ∃ (N : Subgroup (GG p)) (π : GG p → GG p) (hR : Retr (StP M δ u u' w p) N π)
    (hHN : KP M p ⊓ StabX p (XP M δ u u' w L U) ≤ N),
    g0 M δ hA L U hL hU ∈ N ∧ img hR _ hHN ≤ Ag M δ u u' w ∧ (img hR _ hHN).relIndex (Ag M δ u u' w) ≠ 0 ∧
      v = ((img hR _ hHN).relIndex (Ag M δ u u' w) : ℝ)

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

end Formalism.L2.SG.Pf.ProdEP2Cut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalOrthogonalHolds
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}


set_option maxHeartbeats 1000000 in
theorem localOrthogonal_holds : PartialIsometryExtension Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hβ₀ hfr hW0 hOm p w hw hm hm₂
  have hStar := hB.2.2.1
  have hT2 := hStar.2.1 p
  have hId := hT2.2.2.2.1

  have hwW := OrthogonalLocalComplement.baseChange_mem_W0 Zd p γ hw
  obtain ⟨w₂, hw₂, hs1, hs2⟩ := hId.2.2.1 (baseChange₂ D p w) hwW

  have hzrep : (repF γ).zt = (repF γ).fl.z := hB.2.2.2.2.2.2.1.1.2
  have hwHp : w ∈ Hp γ.lam (lf D F0) (repF γ) := by
    have hle := BwdBetaS.UUE_le_span γ.lam (lf D F0) (repF γ) rfl hzrep
    have hspan : Submodule.span D.host.E (Set.range (Sum.elim (lf D F0).fl.fvec (repF γ).fl.fvec)) =
        F0.Xplus ⊔ (repF γ).fl.Xplus := by
      rw [Set.Sum.elim_range, Submodule.span_union, SpanOmPf.Xplus_eq, SpanOmPf.Xplus_eq]
    rw [hspan] at hle
    show w ∈ orth (VS D) (UUE γ.lam (lf D F0) (repF γ))
    rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hw ⊢
    exact fun x hx => hw x (hle hx)
  obtain ⟨w₂g, hw₂g, hd1, hd2⟩ := hW0 w hwHp

  have hu := OrthogonalLocalComplement.hu_all Zd p
  have hwperp : baseChange₂ D p w ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) :=
    baseChange_mem_perp_sup Zd p γ ((PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx =>
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw x
        (Submodule.mem_sup_left (le_sup_left (a := F0.X) (b := Submodule.span D.host.E {F0.z}) hx)))
  have hw₂perp : w₂ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) := LsDatumA.mem_perp_isotropicSpan_of_mem_framePerp _ hw₂
  have hdiff1 : baseChange₂ D p w - w₂ ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have h := hs1 ⟨baseChange₂ D p w, hwperp⟩ ⟨w₂, hw₂perp⟩ rfl rfl
    have h1 : (φ p) ((locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p w, hwperp⟩) =
        (locH Zd p).mkW (tLoc Zd p γ).f ⟨w₂, hw₂perp⟩ := by
      have := h
      simp only [one_smul] at this
      exact this
    have e' : ∀ x, (φ p) x = x := fun x => by rw [hStar.2.2 p]; rfl
    exact LsDatumA.sub_mem_X_of_mkW_eq _ ((e' _).symm.trans h1)
  have hdiff2 : baseChange₂ D p w - baseChange₂ D p w₂g ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    rw [← map_sub]
    exact bcP_X Zd p γ hu hd1
  have hdX : w₂ - baseChange₂ D p w₂g ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have := Submodule.sub_mem _ hdiff2 hdiff1
    rwa [sub_sub_sub_cancel_left] at this
  have hd0 : ∀ a, (locH Zd p).h (w₂ - baseChange₂ D p w₂g) (locF' Zd p F'₂ a) = 0 := by
    intro a
    have h1 : (locH Zd p).h w₂ (locF' Zd p F'₂ a) = 0 :=
      hw₂ _ (Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩))
    have h2 : (locH Zd p).h (baseChange₂ D p w₂g) (locF' Zd p F'₂ a) = 0 := by
      rw [h_eq, locF'_eq, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
        (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw₂g _ (OrthogonalLocalComplement.frame_mem_UUE hB.2.2.2.1.1 (lf D F0) F'₂ a),
        map_zero, mul_zero]
    rw [OmL.h_sub_left, h1, h2, sub_zero]
  have hgen := (hB.2.2.2.1.2 p).1
  have hdet : IsUnit ((locH Zd p).Zhat (locF' Zd p F'₂) (tLoc Zd p γ).f).det := by
    have h := hgen.1.2.2.2.1
    rw [OmL.dl_last] at h
    rw [LsDatumA.Zhat_swap, Matrix.det_transpose, ← RingHom.map_det]
    exact h.map _
  have hd : w₂ - baseChange₂ D p w₂g = 0 :=
    OmL.uniq_loc (locH Zd p) (locF' Zd p F'₂) (tLoc Zd p γ).f hdet
      (le_trans (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.castSucc, rfl⟩)) le_rfl hdX) hd0
  have hw₂eq : w₂ = baseChange₂ D p w₂g := sub_eq_zero.1 hd

  have hw₂perp' : w₂ ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) := LsDatumA.mem_perp_isotropicSpan_of_mem_framePerp' _ hw₂
  have h := hs2 ⟨baseChange₂ D p w, hm⟩ ⟨w₂, hw₂perp'⟩ rfl rfl
  have h' : (φ' p) ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p w, hm⟩) =
      (locH Zd p).mkW (locF' Zd p F'₂) ⟨w₂, hw₂perp'⟩ := by
    have := h
    simp only [one_smul] at this
    exact this
  rw [h']
  apply Submodule.Quotient.eq _ |>.2
  show w₂ - baseChange₂ D p (β₀ w) ∈ (locH Zd p).X (locF' Zd p F'₂)
  rw [hw₂eq, ← map_sub, show w₂g - β₀ w = -(β₀ w - w₂g) by abel, map_neg]
  exact Submodule.neg_mem _ (bcP_X' Zd p F'₂ hd2)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalPositivity
section
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.LocalPositivity

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem pos_of_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a / b) : 0 < a ∧ 0 < b := by
  rcases div_pos_iff.1 h with h' | h'
  · exact h'
  · exact absurd ha (not_le.2 h'.1)

theorem localVolumeUnit_pos_and_ZZX_pos (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hTT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) :
    0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v := by
  have hU : 0 ≤ localVolumeUnit X ψ v := ENNReal.toReal_nonneg
  have hZ : 0 ≤ ZZX X u u' ψ v := ENNReal.toReal_nonneg
  by_cases hv : TypAt X v
  · have e := volTypV_holds X u u' ψ hψ hs hTT v hv
    exact pos_of_div hU hZ (by rw [e]; exact pow_pos (by exact_mod_cast hg v hv) _)
  · have e := volOrdV_holds X u u' ψ hψ hs v hv
    exact pos_of_div hU hZ (by rw [e]; exact Real.rpow_pos_of_pos (absV_pos v (dV_ne_zero v)) _)

theorem pp_pos_ord (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) {v : PlX X} (hv : ¬ TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := hN v hv Unit
  have := hH
  have hset : (fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPOrd (E := X.B.I.E) v D.R.rS l =
      Set.univ.pi fun _ : Unit => {c | sc (E := X.B.I.E) v (alp v D.R.rS l ^ 2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [PPOrd, Set.mem_pi]
    exact ⟨fun h i => h, fun h => h ()⟩
  unfold PPX volC
  rw [if_neg hv, hset, SdW.boxScaleL_holds v Unit hfin (sdE (E := X.B.I.E) ψ v Unit)
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO]
  refine mul_pos (pow_pos (absV_pos v (dV_ne_zero v)) _) (Finset.prod_pos fun q _ => ?_)
  exact inv_pos.2 (pow_pos (absV_pos v (pow_ne_zero _ (alp_ne_zero v D.R.rS l))) 2)

theorem jac_pos (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) : 0 < jacX X v := by
  unfold jacX jacS
  refine Finset.prod_pos fun l _ => ?_
  have hx : (∏ i ∈ Finset.univ.filter (fun i : Fin (D.R.rS + 1) => (i : ℕ) ≤ (l : ℕ)), alp v D.R.rS i ^ 2) *
      (if TypAt X v then ((gAt X v : Fv X.B.I.F v)⁻¹) ^ ((l : ℕ) + 1) else 1) ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (alp_ne_zero v D.R.rS i)) ?_
    split_ifs with ht
    · refine pow_ne_zero _ (inv_ne_zero ?_)
      exact_mod_cast (hg v ht).ne'
    · exact one_ne_zero
  exact pow_pos (pow_pos (absV_pos v hx) 2) 2

end Formalism.L2.SG.Pf.LocalPositivity
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXDens
section
noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.Pf.MassDataX

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_sub_eta_nonneg (η : ℝ) (hη : η = 1 ∨ η = -1) (q i : ℕ) : 0 ≤ 1 - η ^ i / ((q : ℕ) : ℝ) ^ i := by
  have h1 : |η ^ i| = 1 := by
    rcases hη with rfl | rfl <;> simp [abs_pow]
  rcases Nat.eq_zero_or_pos (q ^ i) with h | h
  · have h' : ((q : ℕ) : ℝ) ^ i = 0 := by exact_mod_cast h
    rw [h', div_zero]
    norm_num
  · have h' : (1 : ℝ) ≤ ((q : ℕ) : ℝ) ^ i := by exact_mod_cast (show 1 ≤ q ^ i from h)
    have h2 : η ^ i / ((q : ℕ) : ℝ) ^ i ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact (le_abs_self _).trans (h1.le.trans h')
    linarith

theorem etaP_pm {D : D7} (p : PlF D) : eta₃ p = 1 ∨ eta₃ p = -1 := by
  unfold eta₃
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem aPD_nonneg {D : D7} (p : PlF D) (T : ℕ) : 0 ≤ aPD p T := by
  unfold aPD
  apply Finset.prod_nonneg
  intro i _
  exact one_sub_eta_nonneg _ (etaP_pm p) _ _

theorem alpD_nonneg {D : D7} (u u' : D.what₂.Word) (p : PlF D) : 0 ≤ alpD u u' p := by
  unfold alpD
  split_ifs
  · exact aPD_nonneg p _
  · exact mul_nonneg (aPD_nonneg p _) (aPD_nonneg p _)

theorem densP_nonneg {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (T T' : D.host.E) (Z : MatZ D) (p : PlF D) :
    0 ≤ densP L δ ϖ T T' Z p := by
  unfold densP Formalism.MainNotions.S.Loc.HermSp.dens
  positivity

theorem densNonnegAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.DensNonnegAll := by
  intro D T u u' Lsp ϖ
  apply div_nonneg
  · unfold supDens
    apply Real.sSup_nonneg
    intro d hd
    simp only [densSet, Set.mem_setOf_eq] at hd
    obtain ⟨Z, -, rfl⟩ := hd
    exact tprod_nonneg fun p => densP_nonneg _ _ _ _ _ _ _
  · exact tprod_nonneg fun p => alpD_nonneg u u' p

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAt
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section At

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

def ellP (p : PlF D) : (D.s.atP p).Fp := ((Loc.resChar p : ℕ) : (D.s.atP p).Fp)

theorem ellP_ne (p : PlF D) : ellP p ≠ 0 := by
  have := (D.s.atP p).char0
  have hp := (D.s.atP p).ellPrime.out
  exact Nat.cast_ne_zero.2 hp.ne_zero

theorem ellP_mem (p : PlF D) : ellP p ∈ 𝒪[(D.s.atP p).Fp] := natCast_mem _ _

variable {M δ}

theorem latS_R {p : PlF D} (hA : Agree δ M p) {x : (D.s.atP p).Ep} (hx : x ∈ latS (D.s.atP p) (ellP p)) :
    x ∈ (M p).R := by
  obtain ⟨y, hy, rfl⟩ := mem_latS.1 hx
  obtain ⟨-, -, -, hO, -, hsp⟩ := hA
  show _ ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R
  rcases hM : (M p).split with _ | g
  · show _ ∈ (M p).L.O
    rw [hO]
    exact (D.s.atP p).O.mul_mem (alg_mem_O (ellP_mem p)) hy
  · rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      rw [Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split]
      have hy' := (Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg y).1 hy
      have hq : ((g.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ellP p := by rw [hsp'.2]; exact sg.q_eq
      have he : g.e (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ellP p) * y) =
          (ellP p * (sg.e y).1, ellP p * (sg.e y).2) := by
        rw [map_mul, AlgEquiv.commutes, hsp'.1]; rfl
      rw [he]
      refine ⟨Subring.mul_mem _ (ellP_mem p) hy'.1, Subring.mul_mem _ (ellP_mem p) hy'.2,
        (sg.e y).1 - (sg.e y).2, Subring.sub_mem _ hy'.1 hy'.2, ?_⟩
      rw [hq]; ring

variable (M δ)

theorem ptMat_mono : ptMat w = mono (Formalism.L2.SG.Pf.fσ w) (fun a => Formalism.L2.SG.Pf.pv w.1 a) := by
  ext a b
  rw [Formalism.L2.SG.Pf.ptMat_fσ]
  rfl

theorem exists_unit_monomial_stable_of_Y0 {p : PlF D} (hA : Agree δ M p) :
    ∃ N Ni : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, N * Ni = 1 ∧ Ni * N = 1 ∧
      (∃ ν : Fin (D.R.rS + 1) → (D.s.atP p).Ep, (∀ a, IsUnit (ν a)) ∧ N = mono (Formalism.L2.SG.Pf.fσ w) ν) ∧
      ∀ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, IsLoUni l → IsUpUni ρ →
        l * ProdE.Y0 M δ u u' w p * ρ = ProdE.Y0 M δ u u' w p → l * N * ρ = N := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ a, σ (σ a) = a := Formalism.L2.SG.Pf.fσ_fσ w
  obtain ⟨ν, hν, κ, hY⟩ := zzp_mono δ M u u' hA hσ (fun a => (-1) ^ (D.R.rS - (σ a).val) * Formalism.L2.SG.Pf.pv w.1 a)
    (fun a => mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Formalism.L2.SG.Pf.pv_ne' w a))
  have hY0 : ProdE.Y0 M δ u u' w p = mono σ ν - Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS) κ := by
    rw [← hY]
    unfold ProdE.Y0
    rw [ptMat_mono, zhatOM_mono]
  refine ⟨mono σ ν, mono σ (fun a => Ring.inverse (ν (σ a))), ?_, ?_, ⟨ν, hν, rfl⟩, ?_⟩
  · ext i j
    rw [mono_mul]
    simp only [mono, Matrix.of_apply, Matrix.one_apply, hσ]
    split_ifs with h1 h2 h2
    · exact Ring.mul_inverse_cancel _ (hν i)
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  · ext i j
    rw [mul_mono hσ]
    simp only [mono, Matrix.of_apply, hσ, Matrix.one_apply]
    by_cases h : σ j = σ i
    · have hij : i = j := by rw [← hσ i, ← h, hσ]
      subst hij
      simp only [if_true]
      exact Ring.inverse_mul_cancel _ (hν _)
    · have hij : i ≠ j := fun e => h (by rw [e])
      rw [if_neg h, if_neg hij, zero_mul]
  · intro l ρ hl hρ h
    rw [hY0] at h
    exact fix_of_fix hl hρ κ h

end At

end Formalism.L2.SG.Pf.ProdEApprox
end
end

