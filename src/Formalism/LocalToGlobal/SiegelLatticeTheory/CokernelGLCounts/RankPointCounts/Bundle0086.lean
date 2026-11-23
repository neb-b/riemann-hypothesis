module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsometryFixFlagAnisotropicVectorOfFixFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0082

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowLatOfMove
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}


variable (u') (F0) in
def GenXiRev : Prop :=
  ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (p : PlF D),
    IsRowLat D F0 Λ → AdmWit Λ (gS D) (lf D F0) F' 1 → IsLift Λ F' →
    (locH Zd p).IsGeneric ⟨lattice₂ D Zd.M p Λ, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f, locF' Zd p F',
      (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T'⟩ →
    (locH Zd p).IsGeneric (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u'))

theorem rowLat_of_move (hC : CtxP u u' F0 what₂) (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (himg : (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) : IsRowLat D F0 Λ₂ := by
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hg : Formalism.HermitianLatticesTheory.gmap n Λ₂ = γ.lam := gmap_eq_of_image himg
  have hni : n⁻¹ ∈ Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.G0 F0 := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hn.1, fun a => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) a
    · have h := hn.2.2.2.2
      simp only [FlagG.fvec, Fin.snoc_last]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
    · have h := hn.2.2.2.1 i
      simp only [FlagG.fvec, Fin.snoc_castSucc]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
  have h2 := Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.rowLat_gmap ⟨n⁻¹, hni⟩ hrow
  have e : Formalism.HermitianLatticesTheory.gmap (n⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) γ.lam = Λ₂ := by
    rw [← hg, ← Formalism.L2.SG.Pf.gmap_mul_sat, inv_mul_cancel, Formalism.L2.SG.Pf.gmap_one_sat]
  rw [← e]; exact h2

variable {Zd}

theorem btGen_of (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BtGen Zd u u' F0 what₂ := by
  intro hC γ Z F'₂ φ φ' Λ₂ hs
  have hLift := btLift_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hAdm := btAdm Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hG := btG_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hOKv := hOK hC γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, ⟨n, hn, himg⟩⟩ := hs
  have hR := rowLat_of_move hC γ hn himg
  have hPD : PD D Λ₂ (lf D F0) u' (liftF F'₂) := ⟨hLift, ⟨1, hAdm⟩, hOKv⟩
  refine (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 Λ₂ (liftF F'₂) hR hPD
    (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hG).2 fun p => ?_
  exact hGX Λ₂ (liftF F'₂) p hR hAdm hLift (hloc p).1

theorem bwdTerm'_of' (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BwdTerm' Zd u u' F0 what₂ :=
  bwdTerm'_of Zd (btLift_holds Zd) (btAdm Zd) (btG_holds Zd) hOK (btGen_of hOK hGX)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Th21
section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem th21 (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0) (h2 : Gt t2 ≠ 0)
    (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) :
    t1.lam = t0.lam ∧ t2.lam = t0.lam ∧
    Th t0.lam (lf D (X.Fu u)) t2.frame t1.frame (t1.lin * t2.lin⁻¹) = Hp t0.lam (lf D (X.Fu u)) t2.frame := by
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  obtain ⟨hrow1, hs01⟩ := hR1
  obtain ⟨hrow2, hs02⟩ := hR2
  have hl1 : t1.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow1
  have hl1' : t1.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow1
  have hl2 : t2.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow2
  have hl2' : t2.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow2
  have hlat : Submodule.IsFullLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).1.1
  have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
  have hL0 : IsLift t0.lam t0.frame := t0.rep.2.2.2.2.1
  have hL1 : IsLift t0.lam t1.frame := by rw [← hl1]; exact t1.rep.2.2.2.2.1
  have hL2 : IsLift t0.lam t2.frame := by rw [← hl2]; exact t2.rep.2.2.2.2.1
  have hG0 := G_ne_of_Gt Y h0
  have hG1 := G_ne_of_Gt Y h1
  have hG2 := G_ne_of_Gt Y h2
  have hTh1 : Th t0.lam (lf D (X.Fu u)) t0.frame t1.frame (t1.lin * t0.lin⁻¹) = Hp t0.lam (lf D (X.Fu u)) t0.frame := by
    have h : Formalism.L2.SG.TermOp.s0T t0 t1 = 1 := hs01
    unfold Formalism.L2.SG.TermOp.s0T at h
    rw [if_pos ⟨hl1.symm, hl1'.symm⟩] at h
    exact (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t1.frame _ hLF hL0 hG0).1 h
  have hTh2 : Th t0.lam (lf D (X.Fu u)) t0.frame t2.frame (t2.lin * t0.lin⁻¹) = Hp t0.lam (lf D (X.Fu u)) t0.frame := by
    have h : Formalism.L2.SG.TermOp.s0T t0 t2 = 1 := hs02
    unfold Formalism.L2.SG.TermOp.s0T at h
    rw [if_pos ⟨hl2.symm, hl2'.symm⟩] at h
    exact (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t2.frame _ hLF hL0 hG0).1 h
  have hsym1 := CorankRelation.Th_symm D.R.k hdim t0.lam hlat _ t0.frame t1.frame (t1.lin * t0.lin⁻¹) hLF hL0 hL1 hG0 hG1
    (CorankRelation.frame_mem_iff t0 t1) hTh1
  rw [show (t1.lin * t0.lin⁻¹)⁻¹ = t0.lin * t1.lin⁻¹ by group] at hsym1
  have htr := CorankRelation.Th_trans t0.lam _ t1.frame t0.frame t2.frame (t0.lin * t1.lin⁻¹) (t2.lin * t0.lin⁻¹)
    (fun x hx => (CorankRelation.frame_mem_iff t0 t2 x).1 hx) hsym1 hTh2
  rw [show (t2.lin * t0.lin⁻¹) * (t0.lin * t1.lin⁻¹) = t2.lin * t1.lin⁻¹ by group] at htr
  have hsym2 := CorankRelation.Th_symm D.R.k hdim t0.lam hlat _ t1.frame t2.frame (t2.lin * t1.lin⁻¹) hLF hL1 hL2 hG1 hG2
    (CorankRelation.frame_mem_iff t1 t2) htr
  rw [show (t2.lin * t1.lin⁻¹)⁻¹ = t1.lin * t2.lin⁻¹ by group] at hsym2
  exact ⟨hl1, hl2, hsym2⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TwistC
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem twistC : TwistC D := by
  intro δ M hA hodd w y
  have hm : 2 * mOdd D = gS D + 1 := by unfold mOdd; obtain ⟨k, hk⟩ := hodd; omega
  have hm' : (1 : D.host.E) - 2 * (mOdd D : D.host.E) = -((gS D : ℕ) : D.host.E) := by
    have : ((2 * mOdd D : ℕ) : D.host.E) = ((gS D + 1 : ℕ) : D.host.E) := by rw [hm]
    push_cast at this; linear_combination -this
  have hEq := E_q w y
  have hτs : ∀ q, selfP w q → τA w q y = (mOdd D : D.host.E) * cf w y q := fun q h => by simp [τA, h]
  have hτu : ∀ q, ¬ selfP w q → upperM w q →
      τA w q y = sgq w (qbar w q) * D.conjF (-(y (qbar w q)) + cf w y (qbar w q)) := fun q h1 h2 => by
    simp [τA, h1, h2]
  have hτl : ∀ q, ¬ selfP w q → ¬ upperM w q → τA w q y = 0 := fun q h1 h2 => by simp [τA, h1, h2]
  have hΛs : ∀ q, selfP w q → ∀ z, z ∈ Λq w q ↔
      z ∈ ddPow D (hgt w q) ∧ z + sgq w q * D.conjF z ∈ qdPow D (hgt w q) := fun q h z => by
    simp only [Λq, h, if_true]; rfl
  have hΛu : ∀ q, ¬ selfP w q → upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ qdPow D (hgt w q) := fun q h1 h2 z => by
    simp only [Λq, Iq, h1, h2, if_false, not_true_eq_false, or_self]; rfl
  have hΛl : ∀ q, ¬ selfP w q → ¬ upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ ddPow D (hgt w q) := fun q h1 h2 z => by
    simp only [Λq, Iq, h1, h2, if_false, not_false_eq_true, or_true, if_true]; rfl
  have hup : ∀ q, ¬ selfP w q → upperM w q →
      y q - τA w q y = (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 := by
    intro q h1 h2
    rw [hτu q h1 h2, hEq, sgq_qbar, neg_add_eq_sub]
  have hsq : ∀ q, ¬ selfP w q → ¬ selfP w (qbar w q) := fun q h1 h => h1 (by
    unfold selfP at h ⊢; rw [qbar_qbar] at h; exact h.symm)
  have hgc : ∀ q, (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) ∨
      ¬ (cf w y q ∈ ddPow D (hgt w q)) := fun q => by
    by_cases hc : cf w y q ∈ ddPow D (hgt w q)
    · left; rw [hm', neg_mul]; exact (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem (gS_mul_qd _ hc)
    · right; exact hc
  rw [condX_iff]
  constructor
  · rintro ⟨hy, hE⟩ q
    by_cases h1 : selfP w q
    · rw [hτs q h1, hΛs q h1]
      have hc := cf_mem w y q (fun p _ => hy p)
      refine ⟨(ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (hy q) (nat_mul_mem _ (mOdd D) hc), ?_⟩
      have hqq : qbar w q = q := h1
      have hEq' := hEq q
      rw [hqq] at hEq'
      rw [self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq']
      have e1 := hE q
      have e2 : sgq w q * D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2) -
          (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) :=
        (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (sg_qd w δ M hA (hgt_le w q) q e1) e1
      have e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) := by
        rcases hgc q with h | h
        · exact h
        · exact absurd hc h
      exact (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem
        ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem
          ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem e1 e2) (nat_mul_mem _ (mOdd D) e2)) e3
    · by_cases h2 : upperM w q
      · rw [hΛu q h1 h2, hup q h1 h2]; exact hE q
      · rw [hτl q h1 h2, sub_zero, hΛl q h1 h2]; exact hy q
  · intro ht
    have hy : ∀ q, y q ∈ ddPow D (hgt w q) := by
      have key : ∀ n, ∀ q, hgt w q = n → y q ∈ ddPow D (hgt w q) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro q hq
          have hlow : ∀ p, hgt w p < hgt w q → y p ∈ ddPow D (hgt w p) := fun p hp => ih _ (hq ▸ hp) p rfl
          by_cases h1 : selfP w q
          · have h3 := (hΛs q h1 _).1 (ht q)
            rw [hτs q h1] at h3
            have hc := cf_mem w y q hlow
            have := (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem h3.1 (nat_mul_mem _ (mOdd D) hc)
            rwa [sub_add_cancel] at this
          · by_cases h2 : upperM w q
            · have h3 := (hΛu q h1 h2 _).1 (ht q)
              rw [hτu q h1 h2] at h3
              obtain ⟨hp1, hp2⟩ := upper_qbar w h2
              have hyp : y (qbar w q) ∈ ddPow D (hgt w (qbar w q)) := by
                have := (hΛl _ hp1 hp2 _).1 (ht (qbar w q))
                rwa [hτl _ hp1 hp2, sub_zero] at this
              rw [hgt_qbar] at hyp
              have hcp := cf_mem w y (qbar w q) (fun p hp => hlow p (by rwa [hgt_qbar] at hp))
              rw [hgt_qbar] at hcp
              have hτ := sg_dd w δ M hA (hgt_le w q) (qbar w q)
                ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem
                  ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem hyp) hcp)
              have := (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem (qd_le_dd _ h3) hτ
              rwa [sub_add_cancel] at this
            · have := (hΛl q h1 h2 _).1 (ht q)
              rwa [hτl q h1 h2, sub_zero] at this
      exact fun q => key _ q rfl
    have hG := Xmat_grD w y hy
    refine ⟨hy, ?_⟩
    have hB2 : IsBlockDiagonalMatrix w (Xmat w y - Psi w (Xmat w y)⁻¹) := fun a c h => by
      rw [Matrix.sub_apply, Xmat_blk w y a c h,
        Psi_blk w (blk_inv w (Xmat_upU w y) (Xmat_blk w y)) a c h, sub_self]
    have key2 : ∀ n, ∀ q, hgt w q = n →
        (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro q hq
        have hU := unitCons w δ M hA (Xmat_upU w y) (Xmat_blk w y) hG q.2.1 (fun i j hij hh => by
          by_cases hb : blkOf w.1 i.val = blkOf w.1 j.val
          · exact ih _ (by rw [← hq]; exact hh) ⟨(i, j), hij, hb⟩ rfl
          · rw [hB2 i j hb]; exact FractionalIdeal.zero_mem _)
        have hPsiq : Psi w (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 = sgq w q *
            D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2) := rfl
        rw [hPsiq] at hU
        by_cases h1 : selfP w q
        · have hqq : qbar w q = q := h1
          rw [hqq] at hU
          have hT := ((hΛs q h1 _).1 (ht q)).2
          rw [hτs q h1] at hT
          have hEq' := hEq q
          rw [hqq] at hEq'
          rw [self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq'] at hT
          have hc := cf_mem w y q (fun p _ => hy p)
          have e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) := by
            rcases hgc q with h | h
            · exact h
            · exact absurd hc h
          set Ee := (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 with hEe
          have h5 := (qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem
            ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).add_mem
              ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem hT e3) (nat_mul_mem _ (mOdd D) hU)) hU
          have eq : Ee + (sgq w q * D.conjF Ee - Ee) - (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) +
              (1 - 2 * (mOdd D : D.host.E)) * cf w y q - (1 - 2 * (mOdd D : D.host.E)) * cf w y q +
              (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) - (sgq w q * D.conjF Ee - Ee) = Ee := by ring
          rw [eq] at h5
          exact h5
        · by_cases h2 : upperM w q
          · rw [← hup q h1 h2]; exact (hΛu q h1 h2 _).1 (ht q)
          · have hpu := lower_qbar w h1 h2
            have hps := hsq q h1
            have hEp : (Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2 ∈
                qdPow D (hgt w (qbar w q)) := by
              rw [← hup _ hps hpu]; exact (hΛu _ hps hpu _).1 (ht _)
            rw [hgt_qbar] at hEp
            have hs := sg_qd w δ M hA (hgt_le w q) q hEp
            have := (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem hs hU
            rwa [sub_sub_cancel] at this
    exact fun q => key2 _ q rfl

end Formalism.L2.SG.Pf.StabIntLat
end
end

