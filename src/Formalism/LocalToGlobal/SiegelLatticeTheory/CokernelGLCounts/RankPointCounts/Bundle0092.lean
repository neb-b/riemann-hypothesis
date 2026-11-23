module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0090
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerLatticeCoordinatesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartCG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LatBAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0069
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0077
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0050

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerFix
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG2

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem lmat_low {l ρ : Formalism.L2.SG.LsDatumB.MatP D p} (hl0 : ∀ a b, a < b → l a b = 0) (hl1 : ∀ a, l a a = 1)
    (hρ0 : ∀ a b, b < a → ρ a b = 0) (hρ1 : ∀ a, ρ a a = 1) :
    (∀ a b, a < b → lmat Z p g l ρ a b = 0) ∧ ∀ a, lmat Z p g l ρ a a = 1 := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · simp only [lmat, Matrix.of_apply, hl0 a b h, hρ0 b a h, map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [show ((0 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) = 0 from rfl, map_zero]
  · simp only [lmat, Matrix.of_apply, hl1 a, hρ1 a, map_one, Prod.fst_one, Prod.snd_one]
    rw [show ((1 : (D.s.atP p).Fp), (1 : (D.s.atP p).Fp)) = 1 from rfl, map_one]

theorem corner_fix {L R C : Formalism.L2.SG.LsDatumB.MatP D p} (hL0 : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1)
    (hR0 : ∀ a b, b < a → R a b = 0) (hR1 : ∀ a, R a a = 1)
    (hC : ∀ a b, ¬ (a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS) → C a b = 0) : L * C * R = C := by
  have hLl : ∀ a, L a (Fin.last D.R.rS) = if a = Fin.last D.R.rS then 1 else 0 := by
    intro a
    split_ifs with h
    · subst h; exact hL1 _
    · exact hL0 a _ (lt_of_le_of_ne (Fin.le_last a) h)
  have hRl : ∀ b, R (Fin.last D.R.rS) b = if b = Fin.last D.R.rS then 1 else 0 := by
    intro b
    split_ifs with h
    · subst h; exact hR1 _
    · exact hR0 _ b (lt_of_le_of_ne (Fin.le_last b) h)
  ext a b
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last D.R.rS) (fun d _ hd => by
      rw [Finset.sum_eq_zero (fun c _ => by rw [hC c d (fun h => hd h.2), mul_zero]), zero_mul]) (by simp),
    Finset.sum_eq_single (Fin.last D.R.rS) (fun c _ hc => by rw [hC c _ (fun h => hc h.1), mul_zero]) (by simp),
    hLl a, hRl b]
  by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS
  · subst ha; subst hb; simp
  · rw [if_neg hb, mul_zero, hC a b (fun h => hb h.2)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]

end ModeG2

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountBase
section
noncomputable section

namespace Formalism.L2.SG.Pf.CountBase

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.AtPt
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem zhatOM_sg (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    ZhatOM X * Sg D.host.E D.R.rS = X := by
  ext a b
  simp only [ZhatOM, Sg, Matrix.mul_diagonal]
  rw [mul_comm, ← mul_assoc, ← mul_pow]
  simp

theorem modMat_ord (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) (hM : (M p).split = none)
    (w : Point D.host.E (D.R.rS + 1)) :
    Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) *
        (ptMat w).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) =
      modMat δ T T' p w := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hR : (D.s.atP p).split = none := by
    have h := (hA p).2.2.2.2.2
    rw [hM] at h
    cases h' : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [h'] at h; exact h.elim
  ext a b
  rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
  by_cases hb : b = sgF w a
  · rw [if_pos hb, if_pos hb, modMat_blk Zd]
    simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul]
    subst hb
    ring
  · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]

theorem baseConj_L (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (hM : (M p).split = none) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    Formalism.L2.SG.Pf.ProdE.Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w = a.mat := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hY := Formalism.L2.SG.Pf.PCount.zzp_sgn_ord Zd u u' p hM (ZhatOM (ptMat w))
  rw [zhatOM_sg] at hY
  have hmat := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  rw [hmat]
  unfold Formalism.L2.SG.Pf.ProdE.Y0
  congr 1
  rw [show Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p =
    Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p from rfl, hY]
  exact modMat_ord hA _ _ p hM w

end Formalism.L2.SG.Pf.CountBase
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOne3CHolds
section
namespace Formalism.L2.SG.NGCut.StabilizerCovolume

theorem covolOne3C_holds : Formalism.L2.SG.Pf.VolPinAsm.CovolOne3C :=
  covolOne3C_of Formalism.L2.S.Pv.Chart.chartC_holds (stabilizerLatticeCoordinates_of Formalism.L2.SG.LatBAsm.stabilizer_lattice_twisted_prod)

end Formalism.L2.SG.NGCut.StabilizerCovolume
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIotaB
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem xi_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {x : (VS D).V}
    (hx : x ∈ XLam Λ F) : x ∈ Λ := (Submodule.mem_inf.1 hx).1

theorem g1 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (t : Loc.Term (Vp D p) (Zd.M p) D.R.rS) (hLam : t.abelian₂ = lattice₂ D Zd.M p Λ)
    (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {y y' l ξ ξ' : (VS D).V} (hy : y ∈ Λ) (hy' : y' ∈ Λ)
    (hl : l ∈ Λ) (hξ : ξ ∈ XLam Λ F) (hξ' : ξ' ∈ XLam Λ F')
    (heq : y - y' = ((gS D : ℕ) : D.host.E) • l + ξ + ξ')
    (hp1 : baseChange₂ D p (y - ξ) ∈ (locH Zd p).perp ((locH Zd p).X t.f))
    (hp2 : baseChange₂ D p (y' + ξ') ∈ (locH Zd p).perp ((locH Zd p).X t.f')) :
    ((locH Zd p).mkW t.f' ⟨baseChange₂ D p (y' + ξ'), hp2⟩, (locH Zd p).mkW t.f ⟨baseChange₂ D p (y - ξ), hp1⟩) ∈
      (locH Zd p).iotaGraph g t := by
  obtain ⟨w, hw, w', -, he, -⟩ := gS_typed Zd p g hs
  refine ⟨⟨_, hp2⟩, ⟨_, hp1⟩, ?_, ?_, ?_, rfl⟩
  · rw [hLam]; exact BwdNP.baseChange_mem_localLattice Zd (add_mem hy' (xi_mem hξ')) p
  · rw [hLam]; exact BwdNP.baseChange_mem_localLattice Zd (sub_mem hy (xi_mem hξ)) p
  · have hv : y - ξ - (y' + ξ') = ((gS D : ℕ) : D.host.E) • l := by
      rw [show y - ξ - (y' + ξ') = (y - y') - ξ - ξ' by abel, heq]; abel
    have e : baseChange₂ D p (y - ξ) - baseChange₂ D p (y' + ξ') =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • (w • baseChange₂ D p l) := by
      rw [← map_sub, hv, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, he, mul_smul]
    show baseChange₂ D p (y - ξ) - baseChange₂ D p (y' + ξ') ∈ _
    rw [e, hLam]
    exact Submodule.subset_span ⟨w • baseChange₂ D p l, Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p hw (BwdNP.baseChange_mem_localLattice Zd hl p), rfl⟩

theorem g2 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (t : Loc.Term (Vp D p) (Zd.M p) D.R.rS) (hLam : t.abelian₂ = lattice₂ D Zd.M p Λ)
    (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {y y' : (VS D).V} (hy : y ∈ Λ) (hy' : y' ∈ Λ)
    (hp1 : baseChange₂ D p y ∈ (locH Zd p).perp ((locH Zd p).X t.f))
    (hp2 : baseChange₂ D p y' ∈ (locH Zd p).perp ((locH Zd p).X t.f'))
    (hmem : ((locH Zd p).mkW t.f' ⟨baseChange₂ D p y', hp2⟩, (locH Zd p).mkW t.f ⟨baseChange₂ D p y, hp1⟩) ∈
      (locH Zd p).iotaGraph g t)
    (hA : ∀ v ∈ lattice₂ D Zd.M p Λ, v ∈ (locH Zd p).X t.f → v ∈ lattice₂ D Zd.M p (XLam Λ F))
    (hB : ∀ v ∈ lattice₂ D Zd.M p Λ, v ∈ (locH Zd p).X t.f' → v ∈ lattice₂ D Zd.M p (XLam Λ F')) :
    baseChange₂ D p (y - y') ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  obtain ⟨x'', x, hx''Λ, hxΛ, hdiff, heq⟩ := hmem
  obtain ⟨h1, h2⟩ := Prod.mk.inj heq
  rw [hLam] at hx''Λ hxΛ hdiff
  have d1 : baseChange₂ D p y' - (x'' : Vp D p) ∈ (locH Zd p).X t.f' := by
    have := (Submodule.Quotient.eq _).1 h1
    simpa using this
  have d2 : baseChange₂ D p y - (x : Vp D p) ∈ (locH Zd p).X t.f := by
    have := (Submodule.Quotient.eq _).1 h2
    simpa using this
  have hXA : XLam Λ F ≤ NgX Λ (gS D) F F' := le_sup_right.trans le_sup_left
  have hXB : XLam Λ F' ≤ NgX Λ (gS D) F F' := le_sup_right
  have a1 := localLattice_mono Zd p hXA (hA _ (sub_mem (BwdNP.baseChange_mem_localLattice Zd hy p) hxΛ) d2)
  have a2 := localLattice_mono Zd p hXB (hB _ (sub_mem (BwdNP.baseChange_mem_localLattice Zd hy' p) hx''Λ) d1)
  have a3 : (x : Vp D p) - x'' ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
    refine (Submodule.span_le.2 ?_) hdiff
    rintro _ ⟨v, hv, rfl⟩
    exact typed_q_mem Zd p g hs F F' hv
  have e : baseChange₂ D p (y - y') = (baseChange₂ D p y - x) + ((x : Vp D p) - x'') - (baseChange₂ D p y' - x'') := by
    rw [map_sub]; abel
  rw [e]
  exact sub_mem (add_mem a1 a3) a2

theorem Xle_tLoc {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (γ : TermDef.Term D u u' F0 what₂) :
    (locH Zd p).X (tLoc Zd p γ).f' ≤ (locH Zd p).X (locF' Zd p (repF γ)) := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  obtain ⟨hC0, -, -⟩ := Cm_props Zd p (admXi D γ.lam (lf D F0) (repF γ))⁻¹ hξ1 hξ2
  have hf : ∀ b, (tLoc Zd p γ).f' b = GeneratorChange.comb (Cm Zd p (admXi D γ.lam (lf D F0) (repF γ))⁻¹) (locF' Zd p (repF γ)) b :=
    fun b => (comb_Cm Zd p (repF γ) _ b).symm
  rw [Loc.HermSp.X, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only
  rw [hf, GeneratorChange.comb, Fin.sum_univ_castSucc]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) ?_
  rw [hC0 _ _ (Fin.castSucc_lt_last i), zero_smul]
  exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaF
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdBeta'_of_leaves (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) :
    BwdBeta' Zd u u' F0 what₂ :=
  bwdBeta'_of_core Zd repG_holds (betaCore_of₂ Zd (betaCore₂_of Zd hRat (scalarOf_holds Zd) hInt))

theorem fStarC_of_leaves' (hC : CtxP u u' F0 what₂) (hLP : LprPart Zd u u' F0 what₂)
    (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ :=
  fStarC_of_route2 Zd (starExists2_holds Zd u u' F0 what₂ hC)
    (fwdC_of_loc Zd hC.2.1 (omega_part_holds Zd u u' F0 what₂) (genXi_holds Zd) hLP)
    (bwdC_of''' Zd hC (bwdN_holds Zd u u' F0 what₂) (bwdTerm'_holds Zd u u' F0 what₂) (bwdBeta'_of_leaves Zd hRat hInt))
    (Uniq.uniqC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FlagOfUpUni
section
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

section Uni

variable {K : Type*} [Field K] {N : ℕ}

theorem upUni_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hA i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji (not_lt.1 hk)), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · simp

theorem loUni_iff_ct {A : Matrix (Fin N) (Fin N) K} [StarRing K] : IsLoUni A ↔ IsUpUni Aᴴ := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, fun hij => ?_⟩
    · rw [conjTranspose_apply, (h j i).1 hji, star_zero]
    · subst hij; rw [conjTranspose_apply, (h i i).2 rfl, star_one]
  · intro h i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · have := (h j i).1 hij
      rw [conjTranspose_apply] at this
      exact star_eq_zero.1 this
    · subst hij
      have := (h i i).2 rfl
      rw [conjTranspose_apply] at this
      rw [← star_star (A i i), this, star_one]

theorem upUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

theorem loUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsLoUni A) : A.det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

theorem upUni_inv {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : IsUpUni A⁻¹ := by
  have hdet : IsUnit A.det := by rw [upUni_det h]; exact isUnit_one
  have hbt : A.BlockTriangular id := fun i j hij => (h i j).1 hij
  haveI := A.invertibleOfIsUnitDet hdet
  have hbt' : A⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  intro i j
  refine ⟨fun hji => hbt' hji, fun hij => ?_⟩
  subst hij
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul] at e
  · simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [(h i k).1 hlt, zero_mul]
    · rw [hbt' hgt, mul_zero]
  · simp

theorem loUni_mul {A B : Matrix (Fin N) (Fin N) K} [StarRing K] (hA : IsLoUni A) (hB : IsLoUni B) :
    IsLoUni (A * B) := by
  rw [loUni_iff_ct, conjTranspose_mul]
  exact upUni_mul (loUni_iff_ct.1 hB) (loUni_iff_ct.1 hA)

theorem loUni_inv {A : Matrix (Fin N) (Fin N) K} [StarRing K] (h : IsLoUni A) : IsLoUni A⁻¹ := by
  rw [loUni_iff_ct, conjTranspose_nonsing_inv]
  exact upUni_inv (loUni_iff_ct.1 h)

theorem upUni_last {r : ℕ} {A : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni A) (c : Fin (r + 1)) :
    A (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  by_cases hc : c = Fin.last r
  · subst hc; rw [if_pos rfl]; exact (h _ _).2 rfl
  · rw [if_neg hc]
    exact (h _ _).1 (lt_of_le_of_ne (Fin.le_last c) hc)

end Uni

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem flag_of_upUni (F : FlagG S r T) (g : S.V →ₗ[E] S.V) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hN : IsUpUni N) (hg : ∀ b, g (F.fvec b) = ∑ c, N c b • F.fvec c) :
    (∀ j, ∀ x ∈ F.Xa (j + 1), g x - x ∈ F.Xa j) ∧ g F.z - F.z ∈ F.X := by
  have hdiff : ∀ b, g (F.fvec b) - F.fvec b = ∑ c ∈ Finset.univ.filter (· < b), N c b • F.fvec c := by
    intro b
    rw [hg b, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < b)]
    have h2 : ∑ c ∈ Finset.univ.filter (fun c => ¬ c < b), N c b • F.fvec c = F.fvec b := by
      rw [Finset.sum_eq_single b]
      · rw [(hN b b).2 rfl, one_smul]
      · intro c hc hcb
        have : b < c := lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hc).2) (Ne.symm hcb)
        rw [(hN c b).1 this, zero_smul]
      · intro hb; exfalso; apply hb; simp
    rw [h2]; abel
  have he : ∀ a : Fin r, g (F.e a) - F.e a ∈ F.Xa a := by
    intro a
    have := hdiff (Fin.castSucc a)
    simp only [FlagG.fvec, Fin.snoc_castSucc] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc' : c < Fin.castSucc a := (Finset.mem_filter.1 hc).2
    have hcl : c ≠ Fin.last r := ne_of_lt (lt_trans hc' (Fin.castSucc_lt_last a))
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', by simpa using hc', rfl⟩
  refine ⟨fun j x hx => ?_, ?_⟩
  · induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      have ha' : (a : ℕ) < j + 1 := ha
      refine Submodule.span_mono ?_ (he a)
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨i, by show (i : ℕ) < j; have : (i : ℕ) < a := hi; omega, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), add_sub_add_comm]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hx
  · have := hdiff (Fin.last r)
    simp only [FlagG.fvec, Fin.snoc_last] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hcl : c ≠ Fin.last r := ne_of_lt (Finset.mem_filter.1 hc).2
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', rfl⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GaPlusThHolds
section
namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

open Formalism.MainNotions.S.LocalSplitGroups

theorem LiftOrb_holds : LiftOrb := liftOrb_of RF.srLift_holds

theorem GaPlusTh_holds {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) : GaPlusTh M δ u u' :=
  gaPlusTh_of LiftOrb_holds M δ u u'

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end

