module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0108
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockCounting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0100
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupActB

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.XPEqZzp
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem XP_eq_ZZP {p : PlF D} (hA : Agree δ M p) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) (heq : ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U) :
    XP M δ u u' (p := p) w L U = Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') := by
  unfold XP Y0
  rw [← move δ M u u' hA L U hL hU, Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM, ← heq,
    Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM]

theorem int_zzp (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D) :
    ∀ i j, (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p) i j ∈
      (M p).R := by
  obtain ⟨hAg, hT, hrows, -, hel, ⟨hPD, hmk⟩, hadm, -⟩ := hE
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam (hrows.1 γ.lam γ.mem)
  have hGt := Formalism.L2.SG.TermDef.Gt_mk hTF.1 ⟨F', hPD⟩
  have hGen := Formalism.L2.SG.TermDef.isGen_mk (gS D) hTF.2.2.2.1 ⟨F', hPD⟩
  rw [hmk] at hGt hGen
  have hEZ : F' ∈ Formalism.L2.SG.CntLocal.EZ (Formalism.L2.SG.CntLocal.Tn u') F0 γ.lam (ZhatL (lf D F0) F') :=
    ⟨⟨hPD.1, hPD.2.1, fun h => hel.1.2 (hGt.trans h)⟩, hadm, hGen.1 hel.1.1, hPD.2.2, rfl⟩
  have hI := PI.CntNotIntW.integral_on_pairs_holds D δ M hAg u u' hT F0 what₂ hrows γ.lam γ.mem (ZhatL (lf D F0) F') F' hEZ p
  intro i j
  simp only [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal]
  exact Subring.mul_mem _ (hI i j) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolAsm
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolAsm

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolAct Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem fibreIndex_holds : FibreCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH a₁ b₁ ν₁ m₁ F₁ a₂ b₂ ν₂ m₂ F₂ x₁ x₂ hx₁ hx₂ hd₁ hd₂
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨hRep, hAdm, hL, hU, hZo⟩ := hN
  have hΛ : IsRowLat D F0 γ.lam := hR.1 γ.lam γ.mem
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hP.1.ne_zero
  have hZu : IsUnit (Zhat F0 F'.fl).det := by
    have hZ1 : Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS = L * ptMat w * U := by
      rw [← Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhatOM_eq]; exact hZo
    have hZe : Zhat F0 F'.fl = L * ptMat w * U * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS := by
      rw [← hZ1, Matrix.mul_assoc, Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq, Matrix.mul_one]
    rw [isUnit_iff_ne_zero, hZe, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL,
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hU, one_mul, mul_one]
    refine mul_ne_zero (Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w) ?_
    intro h0
    have := congrArg Matrix.det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq (K := D.host.E) (r := D.R.rS))
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hG₁ : Gval (lf D F0) F' ≠ 0 := by
    obtain ⟨Fa, ⟨pa, ea⟩, hGa, -⟩ := hE.2
    obtain ⟨p₁, e₁⟩ := hRep
    have hdca := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hΛ ⟨Fa, pa⟩ ⟨F', p₁⟩).1 (ea.trans e₁.symm)
    rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdca]
    exact hGa
  have hGr := Formalism.L2.SG.Pf.StabilizerIndexVolumes.gram_gg_unit F0 F'.fl (star_natCast _) (star_natCast _) hZu hG₁
  exact ⟨Formalism.L2.SG.Pf.ZsVolFib.fib_mp u u' F0 what₂ γ F' L hL hGr hZu a₁ b₁ ν₁ m₁ F₁ a₂ b₂ ν₂ m₂ F₂ x₁ x₂ hx₁ hx₂
      hd₁ hd₂,
    Formalism.L2.SG.Pf.ZsVolFib.fib_mpr u u' F0 what₂ γ F' L hL hT0 hZu a₁ b₁ ν₁ m₁ F₁ a₂ b₂ ν₂ m₂ F₂ x₁ x₂ hx₁ hx₂
      hd₁ hd₂⟩

end Formalism.L2.SG.Pf.ZsVolAsm

end
end

