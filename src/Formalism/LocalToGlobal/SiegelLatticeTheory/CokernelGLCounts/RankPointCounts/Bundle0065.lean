module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0062
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNH
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem coef_int (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame (lf D F0) a ∈ Λ₂) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame (lf D F0) a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) •
      (tLoc Zd p γ).f a := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, baseChangeAt_frame_eq Zd p γ (hu p), Units.smul_def, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) • (tLoc Zd p γ).f a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hbm, ← ho]
    simp only [sub_eq_zero]
    rfl
  have h3 := Fintype.linearIndependent_iff.1 hli _ hz (Fin.last D.R.rS)
  have key : ∀ {a : (D.s.atP p).Ep} (h : IsUnit a), a = 1 →
      (((h.unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) = 1 := by
    intro a h ha
    subst ha
    have : h.unit = 1 := Units.ext (IsUnit.unit_spec h)
    rw [this, inv_one, Units.val_one]
  have hone := key (hu p (Fin.last D.R.rS)) (by rw [sgnP_last, frFac_last', mul_one])
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_y (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ₂ : Submodule.IsLattice D.host.E Λ₂) (hSD₂ : BwdNA.SD (VS D) Λ₂)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (hzX : F0.z ∉ Xsp (lf D F0)) :
    ∃ y ∈ Λ₂, y ∈ orth (VS D) (Xsp (lf D F0)) ∧ (VS D).hT y F0.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f F0.z)⁻¹ • f
  have hρz : ρ F0.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp (lf D F0), ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp (lf D F0)).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame (lf D F0) i.castSucc) = 0 := fun i => by
    rw [frame_cs]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame (lf D F0) (Fin.last D.R.rS)) = 1 := by
    have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [this, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame (lf D F0)))
  have hint : ∀ m ∈ Λ₂, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_int Zd γ hprim hu c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂ hSD₂ U v hint
  have hw : ∀ a, (VS D).hT w (frame (lf D F0) a) = ρ (frame (lf D F0) a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame (lf D F0) a) w, ← h0, ← BwdNA.hsw (VS D) (frame (lf D F0) a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (F0.e i), ← frame_cs, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [← this, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfF
section
noncomputable section

open ValuativeRel

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem gdet_ne_of_ratio {r : ℕ} {f f₁ f₂ : Fin (r + 1) → V} {T T' : F} (h1G : H.Gdet f f₁ T T' ≠ 0)
    (h2u : IsUnit (H.Dl f f₂ (r + 1)))
    (hrat : H.Dl f f₁ r * H.Dl f f₂ (r + 1) = H.Dl f f₂ r * H.Dl f f₁ (r + 1)) : H.Gdet f f₂ T T' ≠ 0 := by
  intro h0
  apply h1G
  have hr' := congrArg M.L.cj hrat
  simp only [map_mul] at hr'
  have key : H.normE (H.Dl f f₁ (r + 1)) * H.Gdet f f₂ T T' =
      H.normE (H.Dl f f₂ (r + 1)) * H.Gdet f f₁ T T' := by
    unfold HermSp.Gdet HermSp.normE
    linear_combination (algebraMap F E (T * T') * (M.L.cj (H.Dl f f₁ r) * M.L.cj (H.Dl f f₂ (r + 1)))) * hrat +
      (algebraMap F E (T * T') * H.Dl f f₂ r * H.Dl f f₁ (r + 1)) * hr'
  rw [h0, mul_zero] at key
  have hu : IsUnit (H.normE (H.Dl f f₂ (r + 1))) := h2u.mul (h2u.map M.L.cj)
  exact (hu.mul_right_eq_zero).1 key.symm

end Formalism.MainNotions.S.Loc.HermSp.CohU

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gdl_full (x y : Fin (D.R.rS + 1) → (VS D).V) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl x y (D.R.rS + 1) = (Formalism.L2.SG.Pf.ScalarFramePf.GZ x y).det := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl
  rw [dite_eq_left le_rfl]
  have hc : (Fin.castLE (le_refl (D.R.rS + 1)) : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)) = id :=
    funext fun i => Fin.ext rfl
  rw [hc, Matrix.submatrix_id_id]

theorem local_discriminant_unit_of_det (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z) (hdet : Z.det ≠ 0) :
    IsUnit ((locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1)) := by
  have e : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sgnP D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (∏ i : Fin (D.R.rS + 1), (sgnP' D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (D.s.atP p).ιE (Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) :=
    Formalism.L2.SG.Pf.ScalarFramePf.dl_loc (Z := Zd) (p := p) (frame (lf D F0)) (frame F'₂)
      (fun a => sgnP D p a * frFac Zd.δ p a) (fun b => sgnP' D p b * frFac Zd.δ p b) (D.R.rS + 1) le_rfl
  rw [e]
  have hGZ : Formalism.L2.SG.Pf.ScalarFramePf.GZ (frame (lf D F0)) (frame F'₂) = Z := by
    rw [← hZ]; ext a b; rfl
  have hne : Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [gdl_full, hGZ]; exact hdet
  refine IsUnit.mul (IsUnit.mul ?_ ?_) (Formalism.L2.SG.Pf.BBTie.bt_iota_unit p hne)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map (Zd.M p).L.cj)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _)

theorem cohDG_holds : CohDG Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ' hH
  refine Set.finite_empty.subset fun p hp => ?_
  have hdet : Z.det ≠ 0 := (starMinors_holds u u' F0 what₂ γ Z hH.1).1
  have hu := local_discriminant_unit_of_det Zd p γ Z F'₂ hH.2.1 hdet
  have T1 := hH.2.2.2 p
  exact absurd ⟨hu, Formalism.MainNotions.S.Loc.HermSp.CohU.gdet_ne_of_ratio T1.1.1.2.2.2.2.1 hu T1.2.2.2.1.2.2.2.2.2⟩ hp

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FramesMem
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Term

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem frames_mem (t : TauC Y u u') :
    (∀ b, (X.Fu u).fvec b ∈ t.lam) ∧ (∀ b, t.frame.fl.fvec b ∈ t.lam) := by
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hP := t.rep.2.2.2.2
  exact ⟨Formalism.L2.SG.NGCut.PtPf.frame_mem (lf D (X.Fu u)) hrow.2.1.2.2.1.1 hrow.2.2,
    Formalism.L2.SG.NGCut.PtPf.frame_mem t.frame hP.1.1 hP.2.2.2⟩

theorem yT_mem (t : TauC Y u u') : NormalVectorPairings.yT Y u u' t ∈ t.lam := by
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨h1, h2⟩ := frames_mem Y t
  exact yv_mem hrow.2.1.2.1 (Tu D u) (X.Fu u) t.frame.fl h1 h2

theorem yT'_mem (t : TauC Y u u') : NormalVectorPairings.yT' Y u u' t ∈ t.lam' := by
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨h1, h2⟩ := frames_mem Y t
  have hv : NormalVectorPairings.yv t.frame.fl (X.Fu u) ∈ t.lam := yv_mem hrow.2.1.2.1 (Tu D u') t.frame.fl (X.Fu u) h2 h1
  have hg : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  rw [← hg] at hv
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 hv
  show t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u)) ∈ t.lam'
  rw [← hwv]
  simpa using hw

theorem yT'_orth (t : TauC Y u u') : ∀ x ∈ (X.Fu u').X, brS (VS D) (NormalVectorPairings.yT' Y u u' t) x = 0 := by
  intro x hx
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hlx : t.lin x ∈ (t.frame.fl).X := by
    have := (CorankRelation.mem_Xsp_mapLF (γ := t.lin) hiso (lf D (X.Fu u')) (t.lin x)).2 (by simpa using hx)
    exact this
  have h := yv_orth_X t.frame.fl (X.Fu u) (t.lin x) hlx
  show (VS D).hT x (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u))) = 0
  have e := hiso x (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u)))
  rw [LinearEquiv.apply_symm_apply] at e
  rw [← e]
  exact h

theorem yT'_self (t : TauC Y u u') :
    brS (VS D) (NormalVectorPairings.yT' Y u u' t) (NormalVectorPairings.yT' Y u u' t) =
      brS (VS D) (NormalVectorPairings.yv t.frame.fl (X.Fu u)) (NormalVectorPairings.yv t.frame.fl (X.Fu u)) := by
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  show (VS D).hT (t.lin.symm _) (t.lin.symm _) = _
  have e := hiso (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u))) (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u)))
  rw [LinearEquiv.apply_symm_apply] at e
  rw [← e]
  rfl

theorem lam_eq {t0 t : TauC Y u u'} (h : NormalVectorPairings.RelC Y u u' t0 t) : t.lam = t0.lam ∧ t.lam' = t0.lam' :=
  ⟨congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) h.1,
    congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) h.1⟩

end Term

theorem nmlInt_of
    (hLine : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t0 t : TauC Y u u'),
      Gt t0 ≠ 0 → Gt t ≠ 0 → NormalVectorPairings.RelC Y u u' t0 t → t.G = t0.G → 3 ≤ Tu D u → 3 ≤ Tu D u' →
        NormalVectorPairings.yT Y u u' t - NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0 ∈ (X.Fu u).X ∧
        NormalVectorPairings.yT' Y u u' t - NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0 ∈ (X.Fu u').X) :
    NormalVectorPairings.NmlInt := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hctx γ hNG t0 hGt0 hpt0 => ?_⟩
  have hT1 : (3 : ℕ) ≤ Tu D u := hctx.2.1.2.2.2.1
  have hT2 : (3 : ℕ) ≤ Tu D u' := hctx.2.1.2.2.2.2.1
  have hG := NormalVectorPairings.gval_occ Y t0 (by rw [hpt0]; exact hNG)
  rw [hpt0] at hG
  have hGeq : ∀ t : TauC Y u u', ptPN t = γ → t.G = t0.G := by
    intro t hpt
    have h1 := NormalVectorPairings.gval_occ Y t (by rw [hpt]; exact hNG)
    rw [hpt] at h1
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G Y t, Formalism.L2.SG.Pf.SatGram.gterm_G Y t0, h1, hG]
  have hGne := NormalVectorPairings.GPt_ne_of_NGPt _ _ hNG
  have hTne : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (show Tu D u ≠ 0 by omega)
  have hTne' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (show Tu D u' ≠ 0 by omega)

  have hrow := (Y.rowsOK u).1 t0.lam t0.mem
  have hun := hrow.2.1.2.1
  have hy0 := yT_mem Y t0
  obtain ⟨c0, hc0⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun hy0 hy0
  have hc0' : (c0 : D.host.E) = brS (VS D) (NormalVectorPairings.yT Y u u' t0) (NormalVectorPairings.yT Y u u' t0) := hc0
  have hval : brS (VS D) (NormalVectorPairings.yT Y u u' t0) (NormalVectorPairings.yT Y u u' t0) =
      ((Tu D u : ℕ) : D.host.E) * GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ := by
    show brS (VS D) (NormalVectorPairings.yv (X.Fu u) t0.frame.fl) (NormalVectorPairings.yv (X.Fu u) t0.frame.fl) = _
    rw [NormalVectorPairings.brS_yv_yv _ _ (by simp), ← hG]
    rfl
  have hc0ne : c0 ≠ 0 := by
    intro h
    have : (c0 : D.host.E) = 0 := by rw [h]; rfl
    rw [hc0', hval] at this
    exact mul_ne_zero hTne hGne this

  have hrow' := (Y.rowsOK u').1 t0.lam' t0.mem'
  have hun' := hrow'.2.1.2.1
  have hy1 := yT'_mem Y t0
  obtain ⟨c1, hc1⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun' hy1 hy1
  have hc1' : (c1 : D.host.E) = brS (VS D) (NormalVectorPairings.yT' Y u u' t0) (NormalVectorPairings.yT' Y u u' t0) := hc1
  have hval' : brS (VS D) (NormalVectorPairings.yT' Y u u' t0) (NormalVectorPairings.yT' Y u u' t0) =
      ((Tu D u' : ℕ) : D.host.E) * GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ := by
    rw [yT'_self, NormalVectorPairings.brS_yv_yv _ _ (by simp), NormalVectorPairings.Gflag_swap, ← hG]
    rfl
  have hc1ne : c1 ≠ 0 := by
    intro h
    have : (c1 : D.host.E) = 0 := by rw [h]; rfl
    rw [hc1', hval'] at this
    exact mul_ne_zero hTne' hGne this
  refine ⟨Jfrac t0.lam (X.Fu u).X (NormalVectorPairings.yT Y u u' t0) hun (X_iso (X.Fu u)) (yv_orth_X (X.Fu u) t0.frame.fl)
      hy0 c0 hc0' hc0ne,
    Jfrac t0.lam' (X.Fu u').X (NormalVectorPairings.yT' Y u u' t0) hun' (X_iso (X.Fu u')) (yT'_orth Y t0) hy1 c1 hc1' hc1ne,
    Jfrac_ne_zero _ _ _ _ _ _ _ _ _ _, Jfrac_ne_zero _ _ _ _ _ _ _ _ _ _, fun t hGt hpt hrel => ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨hl1, -⟩ := hLine D X Y u u' t0 t hGt0 hGt hrel (hGeq t hpt) hT1 hT2
    have hyt : NormalVectorPairings.yT Y u u' t ∈ t0.lam := (lam_eq Y hrel).1 ▸ yT_mem Y t
    show NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0 ∈ t0.lam ⊔ (X.Fu u).X.restrictScalars (𝓞 D.host.E)
    have e : NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0 =
        NormalVectorPairings.yT Y u u' t - (NormalVectorPairings.yT Y u u' t - NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0) := by
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hyt) (Submodule.mem_sup_right hl1)
  · obtain ⟨-, hl2⟩ := hLine D X Y u u' t0 t hGt0 hGt hrel (hGeq t hpt) hT1 hT2
    have hyt : NormalVectorPairings.yT' Y u u' t ∈ t0.lam' := (lam_eq Y hrel).2 ▸ yT'_mem Y t
    show NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0 ∈ t0.lam' ⊔ (X.Fu u').X.restrictScalars (𝓞 D.host.E)
    have e : NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0 =
        NormalVectorPairings.yT' Y u u' t - (NormalVectorPairings.yT' Y u u' t - NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0) := by
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hyt) (Submodule.mem_sup_right hl2)
  · have hb := norm_bound t0.lam (X.Fu u).X (NormalVectorPairings.yT Y u u' t0) hun (X_iso (X.Fu u))
      (yv_orth_X (X.Fu u) t0.frame.fl) hy0 c0 hc0' hc0ne
    rw [hc0', hval, abs_norm_TG] at hb
    unfold NormalInvariants.PG
    calc (1 : ℝ) ≤ _ := hb
      _ = _ := by ring
  · have hb := norm_bound t0.lam' (X.Fu u').X (NormalVectorPairings.yT' Y u u' t0) hun' (X_iso (X.Fu u'))
      (yT'_orth Y t0) hy1 c1 hc1' hc1ne
    rw [hc1', hval', abs_norm_TG] at hb
    unfold NormalInvariants.PG
    calc (1 : ℝ) ≤ _ := hb
      _ = _ := by ring

end Formalism.L2.SG.NGCut.NormalIntegrality
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NegOnePowSq
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem neg_one_pow_sq {R : Type*} [CommRing R] (k : ℕ) : (-1 : R) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow]; simp

theorem ρOf_eq (A B : Formalism.L2.SG.PairVal.MatR D) :
    Formalism.L2.SG.Pf.StabShape.ρOf Zd.δ Zd.M p A B =
      Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.Pf.TupGlob.locR Zd p A B * Formalism.L2.SG.LsDatumB.sgnP p := by
  unfold Formalism.L2.SG.Pf.StabShape.ρOf Formalism.L2.SG.Pf.TupGlob.locR
  cases hs : (Zd.M p).split with
  | none =>
    ext i j
    simp only [Formalism.L2.SG.Pf.StabShape.ρL, Formalism.L2.SG.LsDatumB.sgnP, Matrix.of_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.map_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, map_pow, map_neg, map_one]
    rw [frFac_cf, frFac_cf, inv_alg_cf]
    ring
  | some g =>
    ext i j
    apply g.e.injective
    simp only [Formalism.L2.SG.Pf.StabShape.ρG, glue, Formalism.L2.SG.LsDatumB.sgnP, Matrix.of_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply, Sg, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, map_pow, map_neg, map_one,
      AlgEquiv.apply_symm_apply, RingHom.comp_apply, adeleInfiniteComponent_apply, adele_ext_components, frFac_cf, AlgEquiv.commutes,
      Prod.algebraMap_apply, Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_one, Prod.snd_one, Algebra.algebraMap_self, RingHom.id_apply]
    have h2 : ∀ a, cfi Zd p a = (cf Zd p a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (cf_cfi Zd p a)
    have hs2 : ∀ k : ℕ, ((-1 : (D.s.atP p).Fp) ^ k) * (-1) ^ k = 1 := neg_one_pow_sq
    ext
    · simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_neg, Prod.fst_one, h2, div_eq_mul_inv]; ring
    · simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_neg, Prod.snd_one, h2, div_eq_mul_inv]
      linear_combination (-((g.e ((D.s.atP p).ιE (A j i))).2 * cf Zd p j * (cf Zd p i)⁻¹)) *
          hs2 (D.R.rS - i.val) +
        (-((g.e ((D.s.atP p).ιE (A j i))).2 * cf Zd p j * (cf Zd p i)⁻¹) *
          ((-1 : (D.s.atP p).Fp) ^ (D.R.rS - i.val) * (-1) ^ (D.R.rS - i.val))) * hs2 (D.R.rS - j.val)

end Formalism.L2.SG.Pf.FibD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlLineHolds
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem G_ne_of_Gt {t : TauC Y u u'} (h : Gt t ≠ 0) : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
  intro h'
  apply h
  simp only [Formalism.L2.SG.TermOp.Gt]
  rw [if_pos]
  exact (Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _).trans h'

theorem line_occ (t0 t : TauC Y u u') (h0 : Gt t0 ≠ 0) (h : Gt t ≠ 0) (hR : RelC Y u u' t0 t) (hG : t.G = t0.G)
    (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') :
    (yT Y u u' t - coefA Y u u' t0 t • yT Y u u' t0 ∈ (X.Fu u).X ∧
      coefA Y u u' t0 t * star (coefA Y u u' t0 t) = 1) ∧
    (yT' Y u u' t - coefA' Y u u' t0 t • yT' Y u u' t0 ∈ (X.Fu u').X ∧
      coefA' Y u u' t0 t * star (coefA' Y u u' t0 t) = 1) := by
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  obtain ⟨hrow, hs0⟩ := hR
  have hlam : t.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
  have hlam' : t.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
  have hlat : Submodule.IsFullLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).1.1
  have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
  have hL1 : IsLift t0.lam t0.frame := t0.rep.2.2.2.2.1
  have hL2 : IsLift t0.lam t.frame := by rw [← hlam]; exact t.rep.2.2.2.2.1
  have hG1 := G_ne_of_Gt Y h0
  have hG12 : Gval (lf D (X.Fu u)) t.frame = Gval (lf D (X.Fu u)) t0.frame := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t0, hG]
  have hs0' : Lat.s0 t0.lam (lf D (X.Fu u)) t0.frame t.frame (t.lin * t0.lin⁻¹) D.R.k = 1 := by
    have h1 : Formalism.L2.SG.TermOp.s0T t0 t = 1 := hs0
    unfold Formalism.L2.SG.TermOp.s0T at h1
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩] at h1
    exact h1
  have hTh := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t.frame _ hLF hL1 hG1).1 hs0'
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTs : star ((Tu D u : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := star_natCast _
  have hTs' : star ((Tu D u' : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E) := star_natCast _
  refine ⟨line_pair D.R.k hdim t0.lam hlat (lf D (X.Fu u)) t0.frame t.frame _ hLF hL1 hL2 hG1 hG12 hTE hTs hTh,
    line_pair' D.R.k hdim t0.lam (by first | exact hlat | exact hlat.toIsLattice) (lf D (X.Fu u)) (lf D (X.Fu u')) t0.lin t.lin t0.rep.2.2.1 t.rep.2.2.1 hLF
      hL1 hL2 hG1 hG12 hTE' hTs' hTh⟩

theorem NmlLine_holds : NmlLine := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hC γ hγ t0 t h0 h hp0 hp hR => ?_⟩
  unfold Formalism.L2.SG.NGCut.Ctx at hC
  have hT : 3 ≤ Tu D u := hC.2.1.2.2.2.1
  have hT' : 3 ≤ Tu D u' := hC.2.1.2.2.2.2.1
  have hG : t.G = t0.G := by
    have e := gval_occ Y t (by rw [hp]; exact hγ)
    have e0 := gval_occ Y t0 (by rw [hp0]; exact hγ)
    rw [hp] at e
    rw [hp0] at e0
    have e1 : t.G = Gval (lf D (X.Fu u)) t.frame :=
      Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _
    have e2 : t0.G = Gval (lf D (X.Fu u)) t0.frame :=
      Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _
    rw [e1, e2, e, e0]
  have L := line_occ Y t0 t h0 h hR hG hT hT'
  exact ⟨L.1.2, L.2.2⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

