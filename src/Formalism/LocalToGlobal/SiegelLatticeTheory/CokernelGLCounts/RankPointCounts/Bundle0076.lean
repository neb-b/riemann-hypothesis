module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.KapEqParts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0074
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfD
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0031
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.InVolumesAtOfSWW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoordCovolOfCut
section
noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S

theorem coordCovol_of_cut (hL : KapLaw) (hS : KapSurj) (hN : NOfib) (hB : BlockCovol)
    (hP : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∏ p, cVal X u p = LsNc5.covolN X u / LsNc5.twoU X) :
    LsNc5.CoordCovol := by
  intro D X u FdN hF
  obtain ⟨hFm, hFex, hFu⟩ := hF
  obtain ⟨B, hBm, hBd, hB0, hlaw⟩ := hL X u
  obtain ⟨σ, hσm, hσ⟩ := hS X u
  obtain ⟨hNO, hNOmul, hNOinv, τ, hτ, hset⟩ := hN X u
  obtain ⟨-, hmulN, hinvN⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  set NO := Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u
  have hinj : Set.InjOn (blk X u) (X.NinfU u) := fun s hs s' hs' h =>
    LsNc5.kapInj D X u hs hs' (by rw [kap_eq_Φc, kap_eq_Φc, h])
  set K' := blk X u '' (FdN ∩ X.NinfU u) with hK'def
  have hK'eq : K' = σ ⁻¹' FdN := by
    ext t; constructor
    · rintro ⟨s, ⟨hsF, hsN⟩, rfl⟩
      show σ (blk X u s) ∈ FdN
      rw [hinj (hσ _).1 hsN (hσ _).2]; exact hsF
    · intro ht; exact ⟨σ t, ⟨ht, (hσ t).1⟩, (hσ t).2⟩
  have hK'm : MeasurableSet K' := by rw [hK'eq]; exact hσm hFm

  have hmulB : ∀ δ ∈ X.NinfU u, ∀ g : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
      Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B (blk X u δ) g = blk X u (δ * σ g) := by
    intro δ hδ g
    rw [hlaw δ hδ (σ g) (hσ g).1, (hσ g).2]
  have hinv : ∀ γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ p - τ p γ ∈ cLat X u p) →
      ∃ γ' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ' p - τ p γ' ∈ cLat X u p) ∧
        ∀ g, Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ' (Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ g) = g ∧ Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ (Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ' g) = g := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := (hset γ).2 hγ
    have hδN := hNO hδ
    have hδiN := hNO (hNOinv δ hδ)
    refine ⟨blk X u δ⁻¹, (hset _).1 ⟨δ⁻¹, hNOinv δ hδ, rfl⟩, fun g => ⟨?_, ?_⟩⟩
    · have hg := hσ g
      have hdg : δ * σ g ∈ X.NinfU u := (hmulN δ hδN (σ g) hg.1).1
      rw [hmulB δ hδN g, ← hlaw δ⁻¹ hδiN (δ * σ g) hdg, inv_mul_cancel_left, hg.2]
    · have hg := hσ g
      have hdg : δ⁻¹ * σ g ∈ X.NinfU u := (hmulN δ⁻¹ hδiN (σ g) hg.1).1
      rw [hmulB δ⁻¹ hδiN g, ← hlaw δ hδN (δ⁻¹ * σ g) hdg, mul_inv_cancel_left, hg.2]
  have hKd : ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, ∃! γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
      (∀ p, γ p - τ p γ ∈ cLat X u p) ∧ Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ x ∈ K' := by
    intro x
    set g := σ x
    have hg := hσ x
    obtain ⟨δ, hδ, hδF⟩ := hFex g
    have hδN := hNO hδ
    refine ⟨blk X u δ, ⟨(hset _).1 ⟨δ, hδ, rfl⟩, ?_⟩, ?_⟩
    · rw [hmulB δ hδN x]
      exact ⟨δ * g, ⟨hδF, (hmulN δ hδN g hg.1).1⟩, rfl⟩
    · rintro γ' ⟨hγ', hγ'K⟩
      obtain ⟨δ', hδ', rfl⟩ := (hset γ').2 hγ'
      have hδ'N := hNO hδ'
      rw [hmulB δ' hδ'N x] at hγ'K
      obtain ⟨s, ⟨hsF, hsN⟩, hs⟩ := hγ'K
      have hs' : s = δ' * g := hinj hsN (hmulN δ' hδ'N g hg.1).1 hs
      have h1 : δ' * δ⁻¹ = 1 := hFu (δ * g) hδF (δ' * δ⁻¹) (hNOmul δ' hδ' δ⁻¹ (hNOinv δ hδ)) (by
        rw [show δ' * δ⁻¹ * (δ * g) = δ' * g by group, ← hs']; exact hsF)
      rw [mul_inv_eq_one.1 h1]
  have hfd : ∀ p, ∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F := fun p => (hB X u p).2.1
  choose F hF hFd using hfd
  have hcount : ∀ p, Countable (cLat X u p) := fun p => (hB X u p).1
  have hmain := Formalism.L2.SG.NGCut.SplitEmbedding.triFundT (CBlk D.R.rS) (CSpc (InfinitePlace X.B.I.F) D.R.k) (cMeas (InfinitePlace X.B.I.F) D.R.k)
    cHgt B hBm hBd hB0 τ hτ (cLat X u) hinv F hF hFd K' hK'm hKd
  have hvol : ∀ p, cMeas (InfinitePlace X.B.I.F) D.R.k p (F p) = ENNReal.ofReal (cVal X u p) :=
    fun p => (hB X u p).2.2 (F p) (hF p) (hFd p)
  have hcv : ∀ p, 0 ≤ cVal X u p := by
    intro p
    rcases p with ((p | b) | (p | a)) <;> simp only [cVal]
    · exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)
    · refine mul_nonneg (mul_nonneg ?_ (pow_nonneg (by norm_num) _)) (Real.rpow_nonneg (abs_nonneg _) _)
      exact pow_nonneg (show (0 : ℝ) ≤ Formalism.L2.SG.RealObj.Tw (D := D) u from Nat.cast_nonneg _) _
    · exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)
    · exact Real.rpow_nonneg (abs_nonneg _) _

  have himg : LsNc5.kap X u '' (FdN ∩ X.NinfU u) = Ψc ⁻¹' K' := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [kap_eq_Φc, Ψc_Φc]
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, hsy⟩
      refine ⟨s, hs, ?_⟩
      rw [kap_eq_Φc, hsy, Φc_Ψc]
  rw [himg]
  refine ⟨measurable_Ψc hK'm, ?_⟩
  rw [← map_Φc, Measure.map_apply measurable_Φc (measurable_Ψc hK'm)]
  have hpre : Φc ⁻¹' (Ψc ⁻¹' K') = K' := by
    ext x; simp only [Set.mem_preimage, Ψc_Φc]
  rw [hpre, hmain, Finset.prod_congr rfl fun p _ => hvol p, ← ENNReal.ofReal_prod_of_nonneg fun p _ => hcv p, hP]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DetEqLeadMinorE
section
noncomputable section

open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cross

variable {D : D7}

theorem ld_eq_leadMinorE (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    ld Z = leadMinorE Z D.R.rS := by
  unfold ld leadMinorE
  rw [dite_eq_left (Nat.le_succ _)]
  rfl

theorem det_eq_leadMinorE (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    Z.det = leadMinorE Z (D.R.rS + 1) := by
  unfold leadMinorE
  rw [dite_eq_left le_rfl]
  rfl

theorem cross_global {w w' : Point D.host.E (D.R.rS + 1)} {Z Z' : PairVal.MatR D} (hk : kind w = kind w')
    (hZ : AtMat w Z) (hZ' : AtMat w' Z') : Cross Z Z' := by
  unfold Cross
  rw [ld_eq_leadMinorE, ld_eq_leadMinorE, det_eq_leadMinorE, det_eq_leadMinorE]
  exact cross_of_kind hk hZ hZ'

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem cross_zhatLoc (p : PlF D) {Z Z' : MatZ D} (h : Cross Z Z') :
    Cross (ZhatLoc M δ p Z) (ZhatLoc M δ p Z') := by
  have e : ∀ Y : MatZ D, ZhatLoc M δ p Y =
      Matrix.of fun a b => frFac δ p b * (M p).L.cj (frFac δ p a) * (Y.map (D.s.atP p).ιE) a b := by
    intro Y; ext a b; simp [ZhatLoc]
  rw [e, e]
  exact cross_scale (fun a => (M p).L.cj (frFac δ p a)) (frFac δ p) (cross_map _ h)

end Cross

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIC
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

namespace BetaI

theorem xi_inv_last (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (i : Fin D.R.rS) :
    (admXi D Λ F F')⁻¹ (Fin.last D.R.rS) i.castSucc = 0 := by
  obtain ⟨h1, h2⟩ := admissibility_witness_unitriangular Λ F F'
  have hbt : (admXi D Λ F F').BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : (admXi D Λ F F').det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [h2]
  haveI : Invertible (admXi D Λ F F') := Matrix.invertibleOfIsUnitDet _ (by rw [hdet]; exact isUnit_one)
  exact Matrix.blockTriangular_inv_of_blockTriangular hbt (Fin.castSucc_lt_last i)

theorem frameAct_mem {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (i : Fin D.R.rS)
    (h : ξ (Fin.last D.R.rS) i.castSucc = 0) : frameAct (frame G) ξ i.castSucc ∈ Xsp G := by
  show ∑ a, ((ξ a i.castSucc : 𝓞 D.host.E) : D.host.E) • frame G a ∈ Xsp G
  rw [Fin.sum_univ_castSucc, h]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) (by simp)
  rw [frame_csG]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem tf' (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (b : Fin (D.R.rS + 1)) :
    (tLoc Zd p γ).f' b = (TermLoc.sgnP' D p b * frFac Zd.δ p b) •
      baseChange₂ D p (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ b) := rfl

theorem bcP_perp_f' (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {m : (VS D).V}
    (hm : m ∈ orth (VS D) (Xsp (repF γ))) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') := by
  show ∀ w ∈ (locH Zd p).X (tLoc Zd p γ).f', (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [tf', LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _
        (frameAct_mem _ _ i (xi_inv_last γ.lam (lf D F0) (repF γ) i)), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

end BetaI

variable (u u' F0 what₂)

def PinB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (m : (VS D).V) (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
        (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
        m ∈ orth (VS D) (Xsp (repF γ)) →
        φ' p ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) =
          (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩

variable {u u' F0 what₂}

theorem lsetB_of (hP : PinB Zd u u' F0 what₂) : LsetB Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hm hmo
  have hloc := hB.2.2.2.1.2 p
  have hL' := hloc.2.2.2.1
  have hmp := bcP_perp_f' Zd p γ hmo
  have hXmap := BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hmo₂ : β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)) := by
    rw [← hXmap, Formalism.L2.SG.Pf.orth_map_sat β₀ hiso]
    exact Submodule.mem_map_of_mem hmo
  have hmp₂ := baseChangeAt_perp' Zd p F'₂ hmo₂
  have hin : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hmp⟩ ∈
      (locH Zd p).Lset (tLoc Zd p γ).abelian₂ (tLoc Zd p γ).f' := ⟨⟨_, hmp⟩, baseChange_mem_localLattice Zd hm p, rfl⟩
  obtain ⟨x, hxΛ, hxe⟩ := hL'.subset ⟨_, hin, rfl⟩
  rw [hP γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hmp hmp₂ hmo] at hxe
  refine ⟨(x : Vp D p), hxΛ, ?_⟩
  have := (Submodule.Quotient.eq _).1 hxe.symm
  simpa using this

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistB
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}

theorem LprExistB_equiv {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) :
    Equivalence (Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ) :=
  Formalism.L2.SG.Corank.scalarEquiv_of_G scalar_equiv_general u u' F0 Λ hΛ

theorem LprExistB_repFree : Formalism.L2.SG.Corank.ScalarRepFree D u u' :=
  scalar_rep_free D u u'

theorem scal_move {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ)
    (x1 x2 y1 y2 : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0})
    (h1 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y1.1)
    (h2 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y2.1)
    (a : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 x2) : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y1 y2 := by
  have hEq := LprExistB_equiv (u := u) (u' := u') hΛ
  have hRF := LprExistB_repFree (D := D) (u := u) (u' := u') F0 Λ hΛ
  have r2 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 y2.1).1 h2
  have a2 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 y2 := hRF x1 x2 y2 r2 a
  have r1 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 y1.1).1 h1
  have a3 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y2 y1 := hRF y2 x1 y1 r1 (hEq.symm a2)
  exact hEq.symm a3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolH
section
noncomputable section

namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.Volumes MeasureTheory MassDataVolumesW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covolH_eq_volG (hSW : PI.VolStabS.MassDataS.SWXS) {D : D7} (X : HidaSetting D)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ)
    (w : D.what₂.Word) :
    covol (X.measW w).μH = covolBy (G := HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
      X.measG.μG := by
  have hs := stepSizeW X
  obtain ⟨⟨hT1, νH, hνH, hcH⟩, -⟩ := hC.1 w
  exact covol_eq_covolBy_w (PI.VolStabS.MassDataS.volStabXS_of hSW X) (stepHerm X) (a := D.R.rS + 1 + D.R.rS)
    (by omega) (by omega) _ hT1 (stepGramH_of MassDataLevelSSteps.frameStd_holds X w hT1) hψ X.measG_norm.1 hνH
    (X.measW_norm w).1 hcH

section MassData

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem volHa'_eq (hSW : PI.VolStabS.MassDataS.SWXS) (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG :=
  covolH_eq_volG hSW X ψ hψ hC u'

end MassData

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NofibOf
section
namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting NumberField

def NOfibLat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    ∃ τ : ∀ p : CBlk D.R.rS, (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → CSpc (InfinitePlace X.B.I.F) D.R.k p,
      (∀ p (x x' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), (∀ q, cHgt q < cHgt p → x q = x' q) → τ p x = τ p x') ∧
      ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
        x ∈ blk X u '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ ∀ p, x p - τ p x ∈ cLat X u p

theorem nofib_of (hL : NOfibLat) : NOfib := by
  intro D X u
  obtain ⟨h1, h2, h3⟩ := nOinf_closed_under_mul_inv X u
  exact ⟨h1, h2, h3, hL X u⟩

end Formalism.L2.SG.Pf.NcReal.JX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OmpCoset
section
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

private theorem adjugate_last_col_sum_and_det_of_coset (Z Z' P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (v v' : Fin (r + 1) → S.V) (φ : S.V →ₗ[E] S.V) (hZ : Z' = P * Z * Q)
    (hv : ∀ b, v' b = φ (∑ c, Q c b • v c)) (hQ : Q.det = 1) (hP : P.det = 1)
    (hPl : ∀ a, P a (Fin.last r) = if a = Fin.last r then 1 else 0) :
    ∑ b, Z'.adjugate b (Fin.last r) • v' b = φ (∑ b, Z.adjugate b (Fin.last r) • v b) ∧
      Z'.det = Z.det := by
  have hQQ : Q * Q.adjugate = 1 := by rw [Matrix.mul_adjugate, hQ, one_smul]
  have hPP : P.adjugate * P = 1 := by rw [Matrix.adjugate_mul, hP, one_smul]
  have hPl' : ∀ d, P.adjugate d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    have := congrFun (congrFun hPP d) (Fin.last r)
    simpa [Matrix.mul_apply, hPl, Matrix.one_apply] using this
  have hW : ∀ c, (Q * (Q.adjugate * (Z.adjugate * P.adjugate))) c (Fin.last r) =
      Z.adjugate c (Fin.last r) := by
    intro c
    rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_apply]
    simp [hPl']
  refine ⟨?_, ?_⟩
  · rw [hZ, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hv, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, ← hW c, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [hZ, Matrix.det_mul, Matrix.det_mul, hP, hQ, one_mul, mul_one]

theorem omp_coset (F : FlagG S r T) (F0 : FlagG S r T') (σ γ1 s' : S.V ≃ₗ[E] S.V)
    (hσ : σ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hσ' : σ.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ1 : γ1 ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hγ2 : σ * γ1 * s' ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hσf : ∀ j, ∀ x ∈ F.Xa (j + 1), σ.symm x - x ∈ F.Xa j) (hσz : σ.symm F.z - F.z ∈ F.X)
    (hsf : ∀ j, ∀ x ∈ F0.Xa (j + 1), s' x - x ∈ F0.Xa j) (hsz : s' F0.z - F0.z ∈ F0.X) :
    omp F (mapFlag (σ * γ1 * s') hγ2 F0) = σ (omp F (mapFlag γ1 hγ1 F0)) ∧
    (Zhat F (mapFlag (σ * γ1 * s') hγ2 F0)).det = (Zhat F (mapFlag γ1 hγ1 F0)).det ∧
    omp (mapFlag (σ * γ1 * s') hγ2 F0) F = σ (omp (mapFlag γ1 hγ1 F0) F) ∧
    (Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F).det = (Zhat (mapFlag γ1 hγ1 F0) F).det := by
  obtain ⟨M, hM, hMd, hMl⟩ := coef_mat F0 (s' : S.V →ₗ[E] S.V) (fun j x hx => hsf j x hx) hsz
  obtain ⟨N, hN, hNd, hNl⟩ := coef_mat F (σ.symm : S.V →ₗ[E] S.V) (fun j x hx => hσf j x hx) hσz
  have hM' : ∀ b, s' (F0.fvec b) = ∑ c, M c b • F0.fvec c := hM
  have hN' : ∀ b, σ.symm (F.fvec b) = ∑ c, N c b • F.fvec c := hN
  have hs : ∀ x y, S.hT (σ x) (σ y) = S.hT x y := hσ
  have hv1 : ∀ b, (mapFlag (σ * γ1 * s') hγ2 F0).fvec b =
      σ (∑ c, M c b • (mapFlag γ1 hγ1 F0).fvec c) := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [fvec_mapFlag, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hM' b, map_sum]
    simp only [fvec_mapFlag, map_smul]
  have hv2 : ∀ b, F.fvec b = σ (∑ c, N c b • F.fvec c) := by
    intro b
    rw [← hN', LinearEquiv.apply_symm_apply]
  have hZ1 : Zhat F (mapFlag (σ * γ1 * s') hγ2 F0) = Nᴴ * Zhat F (mapFlag γ1 hγ1 F0) * M := by
    ext a b
    have e1 : Zhat F (mapFlag (σ * γ1 * s') hγ2 F0) a b =
        S.hT (F.fvec a) ((mapFlag (σ * γ1 * s') hγ2 F0).fvec b) := rfl
    rw [e1, hv1 b, hv2 a, hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Zhat, brS, starRingEnd_apply,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hZ2 : Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F = Mᴴ * Zhat (mapFlag γ1 hγ1 F0) F * N := by
    ext a b
    have e1 : Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F a b =
        S.hT ((mapFlag (σ * γ1 * s') hγ2 F0).fvec a) (F.fvec b) := rfl
    rw [e1, hv1 a, hv2 b, hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Zhat, brS, starRingEnd_apply,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨h1, h2⟩ := adjugate_last_col_sum_and_det_of_coset _ _ _ _ _ _ (σ : S.V →ₗ[E] S.V) hZ1 hv1 hMd
    (by simp [Matrix.det_conjTranspose, hNd])
    (by intro a; rw [Matrix.conjTranspose_apply, hNl]; split_ifs <;> simp)
  obtain ⟨h3, h4⟩ := adjugate_last_col_sum_and_det_of_coset _ _ _ _ _ _ (σ : S.V →ₗ[E] S.V) hZ2 hv2 hNd
    (by simp [Matrix.det_conjTranspose, hMd])
    (by intro a; rw [Matrix.conjTranspose_apply, hMl]; split_ifs <;> simp)
  exact ⟨h1, h2, h3, h4⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

