module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0089
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0093
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0069
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0094
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0095
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0085
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIF
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem pinB_holds : PinB Zd u u' F0 what₂ :=
  pinB_of Zd (spanOm_holds D) (pinOm_holds Zd u u' F0 what₂) (localOrthogonal_holds Zd)

theorem betaInt_holds : BetaInt Zd u u' F0 what₂ :=
  betaInt_of Zd (lsetB_of Zd (pinB_holds Zd u u' F0 what₂)) (iotaB_of Zd (pinB_holds Zd u u' F0 what₂))

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobPOfInt
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem fStarC_of_int (hC : CtxP u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ :=
  fStarC_of_beta Zd hC (betaRat_holds Zd u u' F0 what₂) hInt

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameEntry
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem sum_fvec {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (w : Fin (D.R.rS + 1) → D.host.E) :
    ∑ c, w c • F0.fvec c = ∑ a : Fin D.R.rS, w (Fin.castSucc a) • F0.e a + w (Fin.last _) • F0.z := by
  rw [Fin.sum_univ_castSucc]
  simp [FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]

theorem frame_entry {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hX : XLam Λ F = XS D F.fl) (hz : F.fl.z ∈ Λ) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu)
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (c b : Fin (D.R.rS + 1)) (hcb : c < b) :
    uu c b ∈ ddS D ^ (-((((b : ℕ) - (c : ℕ) : ℕ)) : ℤ)) := by
  have hne := Formalism.L2.SG.Pf.StabIntSh.lg_ddS_ne (D := D)
  have hXS_le : XS D F.fl ≤ Λ := by rw [← hX]; exact inf_le_left
  have hXmem : ∀ y : Fin D.R.rS → D.host.E, (∑ a, y a • F.fl.e a) ∈ Λ → (∑ a, y a • F.fl.e a) ∈ XS D F.fl := by
    intro y hy
    rw [← hX]
    refine Submodule.mem_inf.2 ⟨hy, ?_⟩
    show (∑ a, y a • F.fl.e a) ∈ F.fl.X
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hc : (c : ℕ) < D.R.rS := lt_of_lt_of_le hcb (Nat.lt_succ_iff.1 b.2)
  obtain ⟨a, rfl⟩ : ∃ a : Fin D.R.rS, c = Fin.castSucc a := ⟨⟨c, hc⟩, rfl⟩
  induction b using Fin.lastCases with
  | last =>
    have hv : s F.fl.z - F.fl.z = ∑ a', uu (Fin.castSucc a') (Fin.last _) • F.fl.e a' := by
      have h := hfr (Fin.last _)
      rw [sum_fvec] at h
      simp only [FlagG.fvec, Fin.snoc_last] at h
      rw [h, (huu _ _).2 rfl, one_smul, add_sub_cancel_right]
    have hmem : s F.fl.z - F.fl.z ∈ XS D F.fl := by
      rw [hv]
      apply hXmem
      rw [← hv]
      exact Λ.sub_mem (hs _ hz) hz
    have h := coef_XS F.fl hmem _ hv a
    have e : (-((((Fin.last D.R.rS : Fin (D.R.rS + 1)) : ℕ) - ((Fin.castSucc a : Fin (D.R.rS + 1)) : ℕ) : ℕ)) : ℤ) =
        -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) := by
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [Nat.cast_sub a.2.le]
    rw [e]
    exact h
  | cast b' =>
    have hab : (a : ℕ) < b' := hcb
    have key : ∀ x ∈ ddS D ^ (-((D.R.rS : ℤ) - ((b' : ℕ) : ℤ))),
        x * uu (Fin.castSucc a) (Fin.castSucc b') ∈ ddS D ^ (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) := by
      intro x hx
      have hgen : x • F.fl.e b' ∈ XS D F.fl := Submodule.subset_span ⟨b', x, hx, rfl⟩
      have hv : s (x • F.fl.e b') = ∑ a', (x * uu (Fin.castSucc a') (Fin.castSucc b')) • F.fl.e a' := by
        have h := hfr (Fin.castSucc b')
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_castSucc] at h
        rw [LinearEquiv.map_smul, h, (huu _ _).1 (Fin.castSucc_lt_last b'), zero_smul, add_zero, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [smul_smul]
      have hmem : s (x • F.fl.e b') ∈ XS D F.fl := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact hs _ (hXS_le hgen)
      exact coef_XS F.fl hmem _ hv a
    have h := mem_of_mul (ddS D) hne _ _ _ key
    have e : (-((((Fin.castSucc b' : Fin (D.R.rS + 1)) : ℕ) - ((Fin.castSucc a : Fin (D.R.rS + 1)) : ℕ) : ℕ)) : ℤ) =
        -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) - -((D.R.rS : ℤ) - ((b' : ℕ) : ℤ)) := by
      simp only [Fin.val_castSucc]
      rw [Nat.cast_sub hab.le]
      ring
    rw [e]
    exact h

end Formalism.L2.SG.Pf.ZsVolLat

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjOfUnimod
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core Formalism.L2.SG.Pf.IndexCocycleOrbits

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxRatio_conj_of_unimod {G : Type} [Group G] (A B : Subgroup G) (s : G) (hBA : B ≤ A) (hf : B.relIndex A ≠ 0)
    (hU : IdxRatio A (cj s A) = 1) : IdxRatio A (cj s B) = (B.relIndex A : ℝ) := by
  rw [idxCocycle G A (cj s B) (cj s A) (cj_le hBA) (by rw [relIndex_cj]; exact hf), hU, relIndex_cj, mul_one]

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

def UnimodAt (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ s ∈ StP M δ u u' w p, IdxRatio (Ag M δ u u' (p := p) w) (cj s (Ag M δ u u' (p := p) w)) = 1

theorem locIdx_at' (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hL : IsLoUni L) (hU : IsUpUni U) (v : ℝ) (hN : CountAt M δ u u' w hA L U hL hU v)
    (hO : UnimodAt M δ u u' (p := p) w) :
    IdxRatio (AP M δ u u' w p) (CPL M δ u u' w hA L U hL hU) = v := by
  rw [idxRatio_map]
  obtain ⟨N, π, hR, hHN, hg, hBA, hfA, hv⟩ := hN
  have hC := cShape M δ u u' hA L U hL hU w
  have hCS : cj (g0 M δ hA L U hL hU) (KP M p ⊓ StabX p (XP M δ u u' w L U)) ≤ StP M δ u u' w p := by
    rw [← hC]
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  show IdxRatio (Ag M δ u u' w) (Cg M δ u u' w hA L U hL hU) = v
  rw [hC, cj_eq_cj_img hR hHN hg hCS, idxRatio_conj_of_unimod _ _ _ hBA hfA (hO _ (hR.mem _ hg)), hv]

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def StepsU : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D),
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) ∧
    UnimodAt M δ u u' (p := p) w

theorem locIdxC_of_count (h : StepsU M δ u u' F0 what₂) : LocIdxC M δ u u' F0 what₂ := by
  intro γ w F' L U hE p
  obtain ⟨hN, hO⟩ := h γ w F' L U hE p
  exact locIdx_at' M δ u u' w _ L U _ _ _ hN hO

end Formalism.L2.SG.Pf.ProdEP2Cut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUSubOne
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LocU

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem locU_mul (A B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A * locU Z p B = locU Z p (A * B) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, locU_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc _ = Ring.inverse (frFac Z.δ p i) * (D.s.atP p).ιE (A i k) *
        (frFac Z.δ p k * Ring.inverse (frFac Z.δ p k)) * (D.s.atP p).ιE (B k j) * frFac Z.δ p j := by ring
    _ = _ := by rw [frFac_mul_inv, mul_one]; ring

theorem locU_sub_one (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A - 1 = locU Z p (A - 1) := by
  ext i j
  simp only [Matrix.sub_apply, locU_apply, map_sub, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [map_one, mul_sub, sub_mul, mul_one, frFac_inv_mul]
  · simp only [map_zero, sub_zero]

end LocU

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTied
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol
  Formalism.L2.SG.NGAnalytic.MassDataLemmas

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nTy_holds : OnTied fun D X hb Y u u' X0 ψ =>
    Formalism.L2.SG.MassDataConc.InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
      (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro _ _ _ _ _ _ _ _ D _ X Y u u' _ hb X0 ψ hT
  exact inTypedC_loc X hb Y.hK _ _ u u' X0 ψ _ 0 0 1 _ _ _ _ _ _ _
    (fun X v => SDL.sdLocX_holds X v) (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) sTypIdx_holds
    hT.2.1 hT.2.2.1

theorem frameVolAt_of_prodConv (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) : OnTied fun D X hb Y u u' X0 ψ =>
    FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
      (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  exact frameVolAt_of X hb Y u u' X0 ψ 0 0 1 _ _ _ _ _ hT.2.1 hT.2.2.1
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT)

theorem nPos_of (hSW : PI.VolStabS.MassDataS.SWXS) (hP : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ) :
    OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX X hb (Y.FN u) (Y.FN u') u u' :=
    ⟨hT.1, hCtx.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1
    (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)
    (locHaarPosC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _)
    (covolPosC_of X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hSW hT.2.1 hT.2.2.2.1
      hT.1 hT.2.2.2.2.2.2)
    (Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of X hb Y u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _ hK2 hV)
    (recPosC_of_dv X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 _ _ Y.M Y.δ _ _ _
      (fun X v => dvPosC_holds X v) hH)
    (hP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hCtx hb X0 ψ hT) (Formalism.L2.SG.Pf.MassDataPos.cooOf_pos X u u')
    (Formalism.L2.SG.WConst.kapN_pos (D := D)) le_rfl le_rfl one_pos

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem prodConv_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConv X u u' ψ :=
  prodConvNew_holds_gen X hb ψ hψ hs hloc u u'

theorem prodConv_holds {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) : ProdConv T.X u u' T.ψ :=
  prodConv_holds_gen T.X T.hb T.ψ T.ψ_char T.ψ_std T.locCompat u u'

theorem prodConvAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.ProdConvAll :=
  fun _ T u u' _ _ => prodConv_holds T u u'

theorem prodConv_onTied :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' _ hb X0 ψ hT
  exact prodConv_holds_gen X hb ψ hT.2.1 hT.2.2.1 hT.2.2.2.2.1 u u'

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxModes
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ}

theorem smul_eq_of_cx (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cx e X = cx e Y) :
    e.symm (1, 0) • X = e.symm (1, 0) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cx, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe] at this
  ext
  · simp [this]
  · simp

theorem smul_eq_of_cy (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cy e X = cy e Y) :
    e.symm (0, 1) • X = e.symm (0, 1) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cy, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe] at this
  ext
  · simp
  · simp [this]

theorem cx_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cx e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cx, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

theorem cy_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cy e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cy, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

end Split

section Data

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp)

theorem mode_data {p : PlF D} (hA : Agree δ M p) :
    ∃ (ex ey : (D.s.atP p).Ep) (d di gg ggi : Fin (D.R.rS + 1) → (D.s.atP p).Ep),
      ex ∈ (D.s.atP p).O ∧ ey ∈ (D.s.atP p).O ∧ ex * ex = ex ∧ ey * ey = ey ∧ ex + ey = 1 ∧ ex * ey = 0 ∧
      (∀ i, d i * di i = 1) ∧ (∀ i, gg i * ggi i = 1) ∧
      ∀ a b : Formalism.L2.SG.PairVal.MatR D,
        ex • lOf δ M p a b = ex • (Matrix.diagonal d * a.map (D.s.atP p).ιE * Matrix.diagonal di) ∧
        ey • ρOf δ M p a b = ey • (Matrix.diagonal ggi * (a.map (D.s.atP p).ιE).transpose * Matrix.diagonal gg) := by
  obtain ⟨-, -, -, -, -, hsp⟩ := id hA
  cases hM : (M p).split with
  | none =>
    refine ⟨1, 0, fun i => (M p).L.cj (frFac δ p i), fun i => Ring.inverse ((M p).L.cj (frFac δ p i)),
      fun _ => 1, fun _ => 1, (D.s.atP p).O.one_mem, (D.s.atP p).O.zero_mem, mul_one 1, mul_zero 0, add_zero 1,
      mul_zero 1, fun i => Ring.mul_inverse_cancel _ ((frFac_unit δ M hA i).map _), fun _ => mul_one 1, fun a b => ⟨?_, ?_⟩⟩
    · simp only [lOf, hM, one_smul]
      exact lL_eq _ _ _ a
    · simp only [zero_smul]
  | some g =>
    rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      have hx := fun i => (split_units δ M hA g i).1
      have hy := fun i => (split_units δ M hA g i).2
      have hmemO : ∀ a b : (D.s.atP p).Fp, a ∈ 𝒪[(D.s.atP p).Fp] → b ∈ 𝒪[(D.s.atP p).Fp] →
          g.e.symm (a, b) ∈ (D.s.atP p).O := by
        intro a b ha hb
        rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1, AlgEquiv.apply_symm_apply]
        exact ⟨ha, hb⟩
      refine ⟨g.e.symm (1, 0), g.e.symm (0, 1),
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).2), fun i => algebraMap _ _ ((g.e (frFac δ p i)).2)⁻¹,
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).1), fun i => algebraMap _ _ ((g.e (frFac δ p i)).1)⁻¹,
        hmemO 1 0 (Subring.one_mem _) (Subring.zero_mem _), hmemO 0 1 (Subring.zero_mem _) (Subring.one_mem _),
        ?_, ?_, ?_, ?_, fun i => by rw [← map_mul, mul_inv_cancel₀ (hy i), map_one],
        fun i => by rw [← map_mul, mul_inv_cancel₀ (hx i), map_one], fun a b => ⟨?_, ?_⟩⟩
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · simp only [lOf, hM]
        apply smul_eq_of_cx
        rw [cx_lG, cx_mul, cx_mul, cx_diag, cx_diag]
        rfl
      · simp only [ρOf, hM]
        apply smul_eq_of_cy
        rw [cy_ρG, cy_mul, cy_mul, cy_diag, cy_diag]
        rfl

end Data

end Formalism.L2.SG.Pf.ProdEApprox
end
end

