module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameOO3FrameValTrans
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianCombinationZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.FrameZEqLinZu
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGenerators.ScalarEquivOfGen

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameSDecomp
section
noncomputable section

open Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.RowForm

namespace LocalFrameDecomposition

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem frameLoc (w : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) :
    PI.SchurPlaces.LeviLA.Frame (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR w)) (X.wfr w v) := by
  let fr := Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v
  exact
    { ee := fr.ee
      ef := fr.ef
      ff := fr.ff
      ez := fr.ez
      fz := fr.fz
      ew := fr.ew
      fw := fr.fw
      zw := fr.zw
      ww := fr.ww
      zz := fun h0 => fr.T_ne (neg_eq_zero.1 (fr.zz.symm.trans h0))
      card := by
        have h := fr.card
        omega }

end LocalFrameDecomposition

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem sDecompC_holds (w : D.what₂.Word) : SDecompC X w := by
  intro g hg
  have hgi : g⁻¹ ∈ X.SinfU w := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hg
  have hS : ∀ v, InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) (uMat (g⁻¹ v)) := hgi
  choose V hVu hVe hVf hVz _ hVN using fun v =>
    PI.SchurPlaces.LeviLA.levi_place (LocalFrameDecomposition.frameLoc X w v)
      ((g⁻¹ v : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) (g⁻¹ v).2 (hS v)
  let s0 : X.B.I.Ginf := fun v => ⟨V v, hVu v⟩
  have hs0 : ∀ v, uMat (s0 v) = (V v : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := fun v => rfl
  have hs0H : s0 ∈ HsetU X w := by
    intro v p hp
    rw [hs0]
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact hVe v a
    · exact hVf v a
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact hVz v
  have hN : s0⁻¹ * g⁻¹ ∈ X.NinfU w := fun v => by
    have e : uMat ((s0⁻¹ * g⁻¹) v) =
        (((V v)⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          uMat (g⁻¹ v) := rfl
    rw [e]
    exact hVN v
  have hN' := Formalism.L2.SG.RealObj.SpanPreservation.ninfU_inv X w hN
  rw [_root_.mul_inv_rev, inv_inv, inv_inv] at hN'
  exact ⟨g * s0, hN', s0⁻¹, Formalism.L2.SG.RealObj.InfCut.hsetU_inv X w hs0H, by group⟩

end Formalism.L2.SG.Pf.RowForm
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ScalarAgreeRatCOfScalT
section
noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowForm.ClassFrameOO2Aux
  Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition Formalism.L2.SG.Pf.RowForm.ClassFrameFirstNormalAdjugate

open scoped Matrix

namespace Formalism.L2.SG.Pf.RowForm.ClassFrameNormalVectorScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

theorem gval_ne (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hG : (Y.tO u u').G s ≠ 0) : Gval (lf D (X.Fu u)) s.frame ≠ 0 := by
  have hG' : s.G ≠ 0 := fun h => hG (by show Formalism.L2.SG.TermOp.Gt s = 0; simp [Formalism.L2.SG.TermOp.Gt, h])
  have hRL : IsRowLat D (X.Fu u) s.lam := (Y.rowsOK u).1 s.lam s.mem
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) s.lam hRL
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) s.lam hRL).1
  let x : Formalism.L2.SG.TermDef.Carrier (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u') := ⟨s.frame, s.rep.2.2.2.2⟩
  have gv : Formalism.L2.SG.TermDef.Gt s.lam (lf D (X.Fu u)) (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u')
      (Formalism.L2.SG.TermDef.mk _ _ _ x) = Gval (lf D (X.Fu u)) x.1 :=
    hGF _ _ ((hEq _ _).1 (Quot.out_eq (Formalism.L2.SG.TermDef.mk s.lam (lf D (X.Fu u))
      (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u') x)))
  intro hz
  apply hG'
  exact gv.trans (by with_unfolding_all exact hz)

variable (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))

theorem firstNormal_e (h : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) (a : Fin D.R.rS) :
    (VS D).hT ((X.Fu u).e a) (Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s))) = 0 := by
  have := firstNormal_pairing X Y u u' s h a.castSucc
  rw [if_neg (Fin.castSucc_lt_last a).ne] at this
  simpa [FlagG.fvec] using this

theorem firstNormal_z (h : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) :
    (VS D).hT (X.Fu u).z (Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s))) = 1 := by
  have := firstNormal_pairing X Y u u' s h (Fin.last _)
  rw [if_pos rfl] at this
  simpa [FlagG.fvec] using this

theorem secondNormal_e (h : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) (b : Fin D.R.rS) :
    (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s))) (s.frame.fl.e b) = 0 := by
  have := secondNormal_pairing X Y u u' s h b.castSucc
  rw [if_neg (Fin.castSucc_lt_last b).ne] at this
  simpa [FlagG.fvec] using this

theorem secondNormal_z (h : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) :
    (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s))) s.frame.fl.z = 1 := by
  have := secondNormal_pairing X Y u u' s h (Fin.last _)
  rw [if_pos rfl] at this
  simpa [FlagG.fvec] using this

theorem agree_pair (s₁ s₂ : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hG₁ : (Y.tO u u').G s₁ ≠ 0) (hG₂ : (Y.tO u u').G s₂ ≠ 0) (hl : s₁.lam = s₂.lam)
    (hs0 : Lat.s0 s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) D.R.k = 1)
    (hsc : IsScalar s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹)) :
    nu1E X u u' (Mof X Y u u' s₁) - nu1E X u u' (Mof X Y u u' s₂) ∈ WperpE X u ∧
      nu2E X u u' (Mof X Y u u' s₁) (Miof X Y u u' s₁) - nu2E X u u' (Mof X Y u u' s₂) (Miof X Y u u' s₂) ∈
        WperpE X u' ∧
      ∀ y₂, orthogonalComplementRational X u u' (Mof X Y u u' s₂) y₂ →
        ∃ y₁, orthogonalComplementRational X u u' (Mof X Y u u' s₁) y₁ ∧ y₁ - y₂ ∈ WperpE X u ∧
          Miof X Y u u' s₁ *ᵥ y₁ - Miof X Y u u' s₂ *ᵥ y₂ ∈ WperpE X u' := by
  have hRL : IsRowLat D (X.Fu u) s₁.lam := (Y.rowsOK u).1 s₁.lam s₁.mem
  obtain ⟨hgen, ⟨_, _, hlift, _⟩, _⟩ := hRL
  have hlat : Submodule.IsFullLattice D.host.E s₁.lam := hgen.1
  have hL₁ : IsLift s₁.lam s₁.frame := s₁.rep.2.2.2.2.1
  have hL₂ : IsLift s₁.lam s₂.frame := by rw [hl]; exact s₂.rep.2.2.2.2.1
  have gv₁ := gval_ne X Y u u' s₁ hG₁
  have gv₂ := gval_ne X Y u u' s₂ hG₂
  have nd₁ := PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hlat hlift hL₁ gv₁
  have nd₂ := PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hlat hlift hL₂ gv₂
  have hdim := PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace.finrank_VS D
  have hTh := PI.UnitaryGroupMassFormula.ScalEquivGen.thEqQ hdim nd₁ hs0
  have hTh'' := PI.UnitaryGroupMassFormula.ScalEquivGen.thEq''Q hlat hdim nd₁ nd₂ hs0
  have hz₁ := frame_zt X Y u u' s₁
  have hz₂ := frame_zt X Y u u' s₂
  have hT0 := PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace.tu_ne_zero D u
  have hT0' := PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace.tu_ne_zero D u'
  have hi : s₂.lin * s₁.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (lin_iso X Y u u' s₂) (Subgroup.inv_mem _ (lin_iso X Y u u' s₁))
  have hβ : ∀ x, (s₂.lin * s₁.lin⁻¹) x = s₂.lin (s₁.lin.symm x) := fun x => rfl
  have hβe : ∀ b, (s₂.lin * s₁.lin⁻¹) (s₁.frame.fl.e b) = s₂.frame.fl.e b := by
    intro b; rw [hβ, frame_e, frame_e, LinearEquiv.symm_apply_apply]
  have hβz : (s₂.lin * s₁.lin⁻¹) s₁.frame.fl.z = s₂.frame.fl.z := by
    rw [hβ, frame_z_eq_lin_zu, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply]
  have hdet : (ZE X u u' (Mof X Y u u' s₁)).det = 0 ↔ (ZE X u u' (Mof X Y u u' s₂)).det = 0 := by
    constructor
    · intro h
      obtain ⟨d, hd, hdO, hd0⟩ := ker_of_det X Y u u' s₁ gv₁ h
      obtain ⟨d₂, hd₂, hd₂O, hd₂0⟩ := ker_transport (by first | exact hlat | exact hlat.toIsLattice) rfl hz₁ hz₂ gv₁ hTh'' hsc hd hdO hd0
      exact det_of_ker X Y u u' s₂ hd₂ hd₂O hd₂0
    · intro h
      obtain ⟨d, hd, hdO, hd0⟩ := ker_of_det X Y u u' s₂ gv₂ h
      obtain ⟨d₁, hd₁, hd₁O, hd₁0⟩ := ker_transport_rev (by first | exact hlat | exact hlat.toIsLattice) rfl hz₁ hz₂ gv₂ hTh hsc hd hdO hd0
      exact det_of_ker X Y u u' s₁ hd₁ hd₁O hd₁0
  refine ⟨?_, ?_, ?_⟩
  ·
    by_cases h₁ : (ZE X u u' (Mof X Y u u' s₁)).det = 0
    · have h₂ := hdet.1 h₁
      simp [nu1E, h₁, h₂]
    have h₂ : (ZE X u u' (Mof X Y u u' s₂)).det ≠ 0 := fun h => h₁ (hdet.2 h)
    obtain ⟨ν, hνm, hνe, hνz, hνd⟩ := firstNormal_transport (by first | exact hlat | exact hlat.toIsLattice) rfl hz₁ hz₂ hT0 hTh'' hsc (firstNormal_mem_Xplus X Y u u' s₁)
      (firstNormal_e X Y u u' s₁ h₁) (firstNormal_z X Y u u' s₁ h₁)
    have hνeq : ν = Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s₂)) := by
      by_contra hne
      apply h₂
      refine det_of_ker X Y u u' s₂ (Submodule.sub_mem _ hνm (firstNormal_mem_Xplus X Y u u' s₂)) ?_ (sub_ne_zero.2 hne)
      rw [PI.ScalarPairDr.W.mem_orth_Xplus (S := VS D) (X.Fu u)]
      refine ⟨fun a => ?_, ?_⟩
      · rw [map_sub]
        have e1 := hνe a
        have e2 := firstNormal_e X Y u u' s₂ h₂ a
        simp only at e1
        rw [e1, e2, sub_zero]
      · rw [map_sub]
        have e1 := hνz
        simp only at e1
        rw [e1, firstNormal_z X Y u u' s₂ h₂, sub_self]
    apply wperp_of X u
    rw [Formalism.L2.SG.Pf.Level.toV_sub, ← hνeq]
    exact fixedX X u _ hνd
  ·
    by_cases h₁ : (ZE X u u' (Mof X Y u u' s₁)).det = 0
    · have h₂ := hdet.1 h₁
      simp [nu2E, h₁, h₂]
    have h₂ : (ZE X u u' (Mof X Y u u' s₂)).det ≠ 0 := fun h => h₁ (hdet.2 h)
    obtain ⟨x, hxm, hxe, hxz, hxd⟩ := secondNormal_transport (by first | exact hlat | exact hlat.toIsLattice) rfl hz₁ hz₂ hT0' hi hβe hβz hTh'' hsc
      (secondNormal_mem_Xplus X Y u u' s₁) (secondNormal_e X Y u u' s₁ h₁) (secondNormal_z X Y u u' s₁ h₁)
    have hxeq : x = Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s₂)) := by
      by_contra hne
      apply h₂
      refine det_of_lker X Y u u' s₂ (Submodule.sub_mem _ hxm (secondNormal_mem_Xplus X Y u u' s₂)) ?_ (sub_ne_zero.2 hne)
      intro b
      refine Fin.lastCases ?_ (fun i => ?_) b
      · simp only [FlagG.fvec, Fin.snoc_last]
        rw [map_sub, LinearMap.sub_apply, hxz, secondNormal_z X Y u u' s₂ h₂, sub_self]
      · simp only [FlagG.fvec, Fin.snoc_castSucc]
        rw [map_sub, LinearMap.sub_apply, hxe i, secondNormal_e X Y u u' s₂ h₂ i, sub_self]
    apply wperp_of X u'
    rw [Formalism.L2.SG.Pf.Level.toV_sub, secondNormal_toV, secondNormal_toV, ← hxeq]
    have key : s₂.lin.symm x = s₁.lin.symm ((s₂.lin * s₁.lin⁻¹).symm x) := by
      rw [LinearEquiv.symm_apply_eq, ← hβ, LinearEquiv.apply_symm_apply]
    rw [key, ← map_sub, ← neg_sub, map_neg]
    exact Submodule.neg_mem _ (symm_frameX X Y u u' s₁ hxd)
  ·
    intro y₂ hy₂
    have hV := orthogonal_toV (Λ := s₁.lam) X Y u u' s₂ hy₂
    obtain ⟨y₁, hy₁, hd1, hd2⟩ := orthogonal_transport hTh'' hV
    refine ⟨X.crd y₁, orthogonal_ofV X Y u u' s₁ (by first | exact hgen.1 | exact hgen.1.toIsLattice) hlift hL₁ hy₁, ?_, ?_⟩
    · apply wperp_of X u
      rw [Formalism.L2.SG.Pf.Level.toV_sub, Formalism.L2.SG.Pf.Level.toV_crd]
      exact fixedX X u _ hd1
    · apply wperp_of X u'
      rw [Formalism.L2.SG.Pf.Level.toV_sub, ← linsymm_toV, ← linsymm_toV, Formalism.L2.SG.Pf.Level.toV_crd]
      have key : s₁.lin.symm y₁ = s₂.lin.symm ((s₂.lin * s₁.lin⁻¹) y₁) := by
        rw [hβ, LinearEquiv.symm_apply_apply]
      rw [key, ← map_sub]
      exact symm_frameX X Y u u' s₂ hd2

end Formalism.L2.SG.Pf.RowForm.ClassFrameNormalVectorScalars

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.L2.SG.Pf.RowForm.ClassFrameNormalVectorScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem scalarAgreeRatC_of_scalT (hS : ScalTC X Y u u' κ) : ScalarAgreeRatC X Y u u' κ := by
  intro R ρ s₁ s₂ _ _
  obtain ⟨hG₁, hn₁, hr₁, hk₁⟩ := s₁.2
  obtain ⟨hG₂, hn₂, hr₂, hk₂⟩ := s₂.2
  have h := (hS s₁.1 s₂.1 hG₁ hG₂ hn₁ hn₂ (hr₁.trans hr₂.symm)).2 (hk₁.trans hk₂.symm)
  have h2 : Formalism.L2.SG.TermOp.scalT s₁.1 s₂.1 := h.2
  obtain ⟨⟨hl, -⟩, hs0, hsc⟩ := h2
  exact agree_pair X Y u u' s₁.1 s₂.1 hG₁ hG₂ hl hs0 hsc

theorem scalarAgreeC_of_scalT (hS : ScalTC X Y u u' κ) : ScalarAgreeC X Y u u' κ :=
  scalarAgreeC_of_rat X Y u u' κ (scalarAgreeRatC_of_scalT X Y u u' κ hS)

end Formalism.L2.SG.Pf.RowForm
end
end

