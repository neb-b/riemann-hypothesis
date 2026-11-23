module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0082
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolPrim
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0068
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormExpSatHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataColumns
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CondXG
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ}

theorem q_ne (g : Formalism.MainNotions.S.Loc.SplitG M.L) : ((g.q : F)) ≠ 0 := by
  exact fun h => g.q_irr.ne_zero (Subtype.ext h)

theorem zzrel_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    X'.map (π1 M g) = L.map (π1 M g) * X.map (π1 M g) * P.map (π1 M g) ∧
    (X'.map (π2 M g))ᵀ = L.map (π2 M g) * (X.map (π2 M g))ᵀ * P.map (π2 M g) := by
  classical
  have hq : (g.q : F) ≠ 0 := q_ne M g
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hZ : ∀ (Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)),
      Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T' a b =
        g.e.symm ((g.e (Y a b)).1 / (g.q : F), -((g.e (Y b a)).2 / (g.q : F))) -
        (if a = Fin.last r ∧ b = Fin.last r then g.e.symm (-T / (g.q : F), T' / (g.q : F)) else 0) := by
    intro Y a b
    simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, Matrix.of_apply]
  let Ec : Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
    Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0
  have hZ1 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π1 M g) =
      (g.q : F)⁻¹ • Y.map (π1 M g) + (T / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.fst_zero, sub_zero, Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul,
        mul_zero, add_zero]
      ring
  have hZ2 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π2 M g) =
      -((g.q : F)⁻¹ • (Y.map (π2 M g))ᵀ) - (T' / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, Ec, Matrix.of_apply,
        smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.snd_zero, sub_zero, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.transpose_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_zero]
      ring
  have hE : ∀ φ : E →+* F, L.map φ * Ec * P.map φ = Ec := by
    intro φ
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Ec, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · simp only [and_self, if_true, mul_one, hL, hP]
        split_ifs <;> simp_all
      · intro k _ hk
        simp [hk]
      · simp
    · intro l _ hl
      simp [hl]
    · simp
  have hinv : (g.q : F)⁻¹ ≠ 0 := inv_ne_zero hq
  constructor
  · have hmap := congrArg (fun Z => Matrix.map Z (π1 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ1, hZ1] at hmap
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hE] at hmap
    exact smul_right_injective _ hinv (add_right_cancel hmap)
  · have hmap := congrArg (fun Z => Matrix.map Z (π2 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ2, hZ2] at hmap
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      hE] at hmap
    exact smul_right_injective _ hinv (neg_inj.1 (sub_left_inj.1 hmap))

theorem condX_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * X * uuG M g L P = X' := by
  obtain ⟨h1, h2⟩ := zzrel_G M g hs hL hP T T' h
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hcj : ∀ x : E, g.e ((M.L.cj : E →+* E) x) = (g.e x).swap := fun x => g.e_cj x
  ext i j
  apply g.e.injective
  refine Prod.ext ?_ ?_
  · have h1' := congrArg (fun A => A i j) h1
    simp only [Matrix.map_apply, Matrix.mul_apply, hπ1, Finset.sum_mul] at h1'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.fst_sum,
      Prod.fst_mul, hcj, Prod.fst_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h1']
  · have h2' := congrArg (fun A => A j i) h2
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, hπ2, Finset.sum_mul] at h2'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.snd_sum,
      Prod.snd_mul, hcj, Prod.snd_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h2', Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

theorem condM_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * cornerM c * mmG M g L P = cornerM c := by
  have hm : ∀ i, mmG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [mmG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

theorem condU_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (uuG M g L P) * cornerM c * uuG M g L P = cornerM c := by
  have hm : ∀ i, uuG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [uuG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarPinOm
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

variable (u u' F0 what₂)

theorem pinOm_cancel {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {a k d₁ d₂ : R} {A B C : W}
    (ha : IsUnit a) (hk : IsUnit k) (hd : IsUnit d₂) (h1 : (a * d₂ * k) • A = (a * d₁ * k) • B)
    (h2 : d₂ • C = d₁ • B) : A = C := by
  have key : (a * d₂ * k) • A = (a * d₂ * k) • C := by
    rw [h1]
    calc (a * d₁ * k) • B = (a * k) • (d₁ • B) := by rw [smul_smul]; congr 1; ring
      _ = (a * k) • (d₂ • C) := by rw [h2]
      _ = (a * d₂ * k) • C := by rw [smul_smul]; congr 1; ring
  obtain ⟨v, hv⟩ := (ha.mul hd).mul hk
  have := congrArg (fun w => ((v⁻¹ : Rˣ) : R) • w) key
  simp only [← hv, smul_smul, Units.inv_mul, one_smul] at this
  exact this


set_option maxHeartbeats 4000000 in
theorem pinOm_holds : PinOm Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hβ hfr hW hO p hm hm₂
  obtain ⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩ := hB
  obtain ⟨hZd, -, -⟩ := starMinors_holds u u' F0 what₂ γ Z hCtx
  have hT2 := hS.2.1 p
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  obtain ⟨K, hK⟩ : ∃ K : (D.s.atP p).Ep, K = (Zd.M p).L.cj (∏ j ∈ Finset.univ.erase (Fin.last D.R.rS), sF' Zd p j) *
      ∏ j, sF Zd p j := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : (D.s.atP p).Ep, P = (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sF Zd p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Zd p (Fin.castLE le_rfl i)) := ⟨_, rfl⟩
  have ho1 : (locH Zd p).om (tLoc Zd p γ).f (tLoc Zd p γ).f' = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame (repF γ))) := by
    have e := om_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p)
    rw [Gom_frameAct (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hK] at e
    exact e
  have ho2 : (locH Zd p).om (tLoc Zd p γ).f (locF' Zd p F'₂) = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) := by
    have e := om_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p)
    rw [← hK] at e
    exact e
  have hd1 : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [GDl_frameAct_top (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hP] at e
    exact e
  have hd2 : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [← hP] at e
    exact e
  have hid := hT2.2.2.2.1
  have hs := hid.2.2.2.2.1
  dsimp only at hs
  rw [ho1, ho2, hd1, hd2] at hs
  have hω₂ : baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) :=
    baseChangeAt_perp' Zd p F'₂ (Gom_orth (lf D F0) F'₂)
  have h1 := hs (K • ⟨_, hm⟩) (K • ⟨_, hω₂⟩) rfl rfl
  have e1 := ((locH Zd p).mkW (tLoc Zd p γ).f').map_smul K ⟨_, hm⟩
  have e2 := ((locH Zd p).mkW (locF' Zd p F'₂)).map_smul K ⟨_, hω₂⟩
  have e3 := ((φ' p).toLinearMap).map_smul K ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hm⟩)
  rw [e1, e2, e3, smul_smul, smul_smul] at h1
  have hD2 : GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [GDl_top']
    have e : GZ (frame (lf D F0)) (frame F'₂) = Z := hS.1
    rw [e]; exact hZd
  have hOp : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        baseChange₂ D p (β₀ (Gom (frame (lf D F0)) (frame (repF γ)))) -
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).X (locF' Zd p F'₂) := by
    have := bcP_X' Zd p (liftF F'₂) hO
    rw [map_sub, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂] at this
    exact this
  have hcls : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hm₂⟩ =
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hω₂⟩ := by
    rw [← LinearMap.map_smul, ← LinearMap.map_smul]
    apply (Submodule.Quotient.eq _).2
    exact hOp
  rw [map_mul, map_mul, cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)] at h1
  have hPu : IsUnit P := by
    rw [hP]
    exact (IsUnit.prod_univ_iff.2 fun i => (isUnit_sF Zd p _).map _).mul
      (IsUnit.prod_univ_iff.2 fun i => isUnit_sF' Zd p _)
  have hKu : IsUnit K := by
    rw [hK]
    exact ((IsUnit.prod_iff.2 fun j _ => isUnit_sF' Zd p j).map _).mul
      (IsUnit.prod_univ_iff.2 fun j => isUnit_sF Zd p j)
  have hDu : IsUnit ((D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)))) :=
    (isUnit_iff_ne_zero.2 (star_ne_zero.2 hD2)).map _
  exact pinOm_cancel (hPu.map _) hKu hDu h1 hcls

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfSplitMode
section
namespace Formalism.L2.SG.LsDatumA

def ModSide0G : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n true)

def ModSideUG : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n true)

theorem modSide0_mode (h0G : ModSide0G) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSide0L F E M hM r n
  · exact h0G F E M hM r n

theorem modSideU_mode (hUG : ModSideUG) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSideUL F E M hM r n
  · exact hUG F E M hM r n

theorem globalCount_of_split_mode (D : Formalism.BasicNotions.D7) (h0G : ModSide0G) (hUG : ModSideUG) : Formalism.MainNotions.ThinScalesBound.T2 D :=
  globalCount_of_module D (fun F _ _ _ E _ _ _ _ M hM => modSide0_mode h0G F E M hM _ _)
    (fun F _ _ _ E _ _ _ _ M hM => modSideU_mode hUG F E M hM _ _)

end Formalism.L2.SG.LsDatumA
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalFactorsPosTypicalGeneral
section
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem local_factors_pos_typical_general {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w)
    (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v) : 0 < MX X u u' ψ v ∧ 0 < localVolumeUnit X ψ v := by
  let p : TypX X := ⟨v, hv⟩
  have : Submodule.IsFullLattice X.B.I.E X.B.I.L :=
    { toIsLattice := Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg
      span_eq_top := X.B.I.L_span }
  have hL := locTieX_of X ψ u (hloc u) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
  have hL' := locTieX_of X ψ u' (hloc u') (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim)
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u'
  have h := locMassTyp X.B.I.cm.sig X.B.I.J ψ v (gAt X v) (frameOf X u) (frameOf X u')
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hψ, hs⟩ _ _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u) (MassDataLevelSSteps.FrameW.frameOf_isStd X u')
    (Formalism.L2.SG.Pf.MassDataX.SDL.sdLocX_holds X v) (Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v)
    ⟨X.B.I.L, inferInstance, rfl⟩ (hTF p).1
    (gAt_mem X p) (hTF p).2.1 (hTF p).2.2.1 (hTF p).2.2.2.2
    _ (hL v).1 _ (hL v).2.1 (hL v).2.2.1 _ (hL' v).2.1 (hL' v).2.2.1 (hL v).2.2.2 (hL' v).2.2.2
  have hpos := div_pos (mul_pos (gv_pos X p (kg_sub_kv X p) subset_rfl)
      (gv_pos X p (kg_sub_knat X p u) (knat_sub_kv X p u)))
      (mul_pos (sv_pos X u p (kg_sub_kv X p) subset_rfl) (sv_pos X u' p (kg_sub_kv X p) subset_rfl))
  have hR : 0 < MX X u u' ψ v / localVolumeUnit X ψ v := by
    unfold MX localVolumeUnit OmX
    rw [if_pos hv, if_pos hv]
    exact lt_of_lt_of_eq hpos h.symm
  have hU0 : 0 ≤ localVolumeUnit X ψ v := ENNReal.toReal_nonneg
  rcases div_pos_iff.1 hR with ⟨h1, h2⟩ | ⟨-, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd h2 (not_lt.2 hU0)

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

theorem normExpDegC_of_leaves (hFL : Formalism.L2.SG.Pf.FinLeviC) (hOL : Formalism.L2.SG.Pf.OOLintSumC) : NormExpDegC :=
  normExpDegC_of hilbert_schmidt_blocks (Formalism.L2.SG.Closed.FoldOKC_holds hFL) (Formalism.L2.SG.Closed.OOIntAllC_holds hOL)
    (Formalism.L2.SG.Closed.AbsConvC_holds hOL) Formalism.L2.SG.Closed.AmpWellDefC_holds Formalism.L2.SG.Closed.OOFundIndepC_holds
    (fun _ X => chi_n_bilinear X) (fun D X Y u _ => Formalism.L2.SG.NormCut.colFreeAll D X Y u)
    (fun D X Y u _ h1 h2 h3 =>
      Formalism.L2.SG.NormCut.degLeftAct_of_PD (fun D => Formalism.L2.SG.Pf.positive_definite_isomorphism D) D X Y u h1 h2 h3)
    (fun D X Y u _ h1 h2 h3 => Formalism.L2.SG.NormCut.degRightAct_holds D X Y u h1 h2 h3)

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXColumns
section
namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.L2.SG.TypedSets

theorem inColumnsAt_holds :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InColumnsAt X hb hK FdN FdN' u u' X0 L A :=
  massDataColumns_of' Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Closed.AdBridgeGF_holds
    Formalism.L2.SG.Closed.AdBridgeK_holds
    (fun X u hK => Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK))
    (fun X u hK => Formalism.L2.SG.Closed.ClassFin_holds X u hK)
    (fun I hb => ⟨Formalism.L2.SG.Pf.Meas.eFin I hb, fun _ => rfl⟩)
    (fun X => Formalism.L2.SG.Pf.level_subgroup_compact_open X)
    Formalism.L2.SG.Closed.AutKCompact_holds
    Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion
    (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)

end Formalism.L2.SG.Pf.MassDataX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartialIsometryExtension
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

variable (u u' F0 what₂)

def PartialIsometryExtension : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (w : (VS D).V), w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus) →
        BetaI.SendsB Zd p γ F'₂ (φ' p) β₀ w

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

