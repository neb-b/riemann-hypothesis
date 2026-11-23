module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0069
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.MemThPairs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0068
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0070

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DdPowConj
section
noncomputable section

open scoped Classical Matrix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem ddPow_conj (Zd : LocDat D) {k : ℕ} (hk : k ≤ D.R.rS) {y : D.host.E} (h : y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    D.conjF y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have hne := (Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)).1 k
  exact (Formalism.L2.SG.Pf.StabIntSh.locGlob _ hne _).1 fun p =>
    Formalism.L2.SG.Pf.StabIntSh.locMem_conj Zd.δ Zd.M Zd.agree p hk
      ((Formalism.L2.SG.Pf.StabIntSh.locGlob _ hne _).2 h p)

theorem mem_aaF {c b : Fin (D.R.rS + 1)} (hcb : c < b) {x y : D.host.E} (hx : x ∈ FibQ.aaF D b)
    (hy : y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D (b.val - c.val)) : x * y ∈ FibQ.aaF D c := by
  have h := FractionalIdeal.mul_mem_mul hx hy
  unfold FibQ.aaF Formalism.L2.SG.Pf.StabIntSh.ddPow at *
  rw [← zpow_add₀ (PI.NRCW.ddS_ne_zero D)] at h
  have e : -((D.R.rS : ℤ) - ((b : ℕ) : ℤ)) + -(((b.val - c.val : ℕ)) : ℤ) = -((D.R.rS : ℤ) - ((c : ℕ) : ℤ)) := by
    have : c.val ≤ b.val := le_of_lt hcb
    push_cast [this]
    ring
  rwa [e] at h

theorem sg_entry (B : Formalism.L2.SG.PairVal.MatR D) (c b : Fin (D.R.rS + 1)) :
    (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) c b =
      Formalism.L2.SG.Pf.StabIntSh.bt D B c b := by
  simp [Formalism.L2.SG.Pf.AtPt.Sg, Formalism.L2.SG.Pf.StabIntSh.bt, Matrix.mul_diagonal, Matrix.diagonal_mul]

end Formalism.L2.SG.Pf.FibD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIA
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdNP

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

section Frame

variable (p : PlF D) {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')

theorem locF'_eq (b : Fin (D.R.rS + 1)) : locF' Zd p G b = sF' Zd p b • baseChange₂ D p (frame G b) := rfl

theorem bcP_frameG (b : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame G b) = (((isUnit_sF' Zd p b).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • locF' Zd p G b := by
  rw [locF'_eq, smul_smul, (isUnit_sF' Zd p b).val_inv_mul, one_smul]

theorem frame_csG (i : Fin D.R.rS) : frame G i.castSucc = G.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_lastG : frame G (Fin.last D.R.rS) = G.fl.z := by
  simp [frame, FlagG.fvec]

theorem sF'_last : sF' Zd p (Fin.last D.R.rS) = 1 := by
  unfold sF'
  rw [frFac_last' Zd p, mul_one]
  unfold TermLoc.sgnP'
  split
  · exact sgnP_last p
  · simp

theorem locF'_last : locF' Zd p G (Fin.last D.R.rS) = baseChange₂ D p G.fl.z := by
  rw [locF'_eq, sF'_last, one_smul, frame_lastG]

theorem bcP_X' {x : (VS D).V} (hx : x ∈ Xsp G) : baseChange₂ D p x ∈ (locH Zd p).X (locF' Zd p G) := by
  change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_csG, bcP_frameG Zd p G]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChangeAt_perp' {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp G)) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p G)) := by
  show ∀ w ∈ (locH Zd p).X (locF' Zd p G), (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [locF'_eq, frame_csG, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

end Frame

theorem coef_intG {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame G a ∈ Λ) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame G a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) *
      ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) • locF' Zd p G a := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, bcP_frameG Zd p G, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (locF' Zd p G)) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) •
        locF' Zd p G a = 0 := by
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
  have hone := key (isUnit_sF' Zd p (Fin.last D.R.rS)) (sF'_last Zd p)
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_yG {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) (hSD : BwdNA.SD (VS D) Λ)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (hzX : G.fl.z ∉ Xsp G) :
    ∃ y ∈ Λ, y ∈ orth (VS D) (Xsp G) ∧ (VS D).hT y G.fl.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f G.fl.z)⁻¹ • f
  have hρz : ρ G.fl.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp G, ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp G).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame G i.castSucc) = 0 := fun i => by
    rw [frame_csG]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame G (Fin.last D.R.rS)) = 1 := by
    rw [frame_lastG, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame G))
  have hint : ∀ m ∈ Λ, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_intG Zd G hprim c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ hΛ hSD U v hint
  have hw : ∀ a, (VS D).hT w (frame G a) = ρ (frame G a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame G a) w, ← h0, ← BwdNA.hsw (VS D) (frame G a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (G.fl.e i), ← frame_csG, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · rw [← frame_lastG, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfH
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohGoodPf

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace GramNePf

theorem sign_norm {l : ℕ} (hl : l ≤ D.R.rS + 1) :
    leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l *
      star (leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l) = 1 := by
  have hsub : (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).submatrix
      (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i : Fin l => (-1 : D.host.E) ^ (D.R.rS - (Fin.castLE hl i).val)) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp [ZhatOM]
    · have h' : Fin.castLE hl i ≠ Fin.castLE hl j := fun e => h (Fin.castLE_injective hl e)
      simp [ZhatOM, Matrix.one_apply_ne h', Matrix.diagonal_apply_ne _ h]
  have hdet : Formalism.MainNotions.S.leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l =
      (-1 : D.host.E) ^ (∑ i : Fin l, (D.R.rS - (Fin.castLE hl i).val)) := by
    unfold Formalism.MainNotions.S.leadMinorE
    rw [dif_pos hl, hsub, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  rw [hdet, star_pow, star_neg, star_one, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

theorem conjF_star (x : D.host.E) : D.conjF x = star x := by
  rw [D.conjF_eq]
  exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm

private lemma submatrix_castLE_mul_of_upper {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (A B : Matrix (Fin n) (Fin n) K)
    (hB : ∀ i j, j < i → B i j = 0) :
    (A * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun k => rfl)
  intro k hk
  have hkl : l ≤ k.val := by
    by_contra h
    exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
  rw [hB k (Fin.castLE hl j) (by rw [Fin.lt_def, Fin.val_castLE]; exact lt_of_lt_of_le j.isLt hkl), mul_zero]

private lemma submatrix_castLE_mul_of_lower {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (A B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, i < j → A i j = 0) :
    (A * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun k => rfl)
  intro k hk
  have hkl : l ≤ k.val := by
    by_contra h
    exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
  rw [hA (Fin.castLE hl i) k (by rw [Fin.lt_def, Fin.val_castLE]; exact lt_of_lt_of_le i.isLt hkl), zero_mul]

private lemma det_submatrix_castLE_of_isLoUni {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (L : Matrix (Fin n) (Fin n) K)
    (hL : IsLoUni L) : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  have hb : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := by simpa using hij
    show L (Fin.castLE hl i) (Fin.castLE hl j) = 0
    exact (hL _ _).1 (by rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hij')
  rw [Matrix.det_of_lowerTriangular _ hb]
  exact Finset.prod_eq_one (fun i _ => (hL _ _).2 rfl)

private lemma det_submatrix_castLE_of_isUpUni {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (U : Matrix (Fin n) (Fin n) K)
    (hU : IsUpUni U) : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  have hb : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := by simpa using hij
    show U (Fin.castLE hl i) (Fin.castLE hl j) = 0
    exact (hU _ _).1 (by rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hij')
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one (fun i _ => (hU _ _).2 rfl)

private lemma det_submatrix_castLE_LPU_eq {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (L P U : Matrix (Fin n) (Fin n) K)
    (hL : IsLoUni L) (hU : IsUpUni U) :
    ((L * P * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  rw [submatrix_castLE_mul_of_upper hl _ _ (fun i j h => (hU i j).1 h), submatrix_castLE_mul_of_lower hl _ _ (fun i j h => (hL i j).1 h),
    Matrix.det_mul, Matrix.det_mul, det_submatrix_castLE_of_isLoUni hl L hL, det_submatrix_castLE_of_isUpUni hl U hU, one_mul, mul_one]

private lemma zhatOM_eq_mul_zhatOM_one {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM Z = Z * ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) := by
  ext a b
  simp [ZhatOM, Matrix.mul_apply, Matrix.one_apply]
  try ring

theorem gflag_ne (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hC : Ctx γ Z) (hZ : ZhatL (lf D F0) F'₂ = Z) :
    Gflag (lf D F0).fl F'₂.fl ≠ 0 := by
  obtain ⟨w, -, w', hG, -, hA⟩ := hC
  obtain ⟨L, U, hL, hU, hM⟩ := hA
  have hS : ∀ i j : Fin (D.R.rS + 1), j < i →
      ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) i j = 0 := by
    intro i j h
    simp [ZhatOM, Matrix.one_apply_ne (ne_of_gt h)]
  have hsq : ∀ l, l ≤ D.R.rS + 1 →
      Formalism.MainNotions.S.leadMinorE Z l * star (Formalism.MainNotions.S.leadMinorE Z l) = Dmin w' l * D.conjF (Dmin w' l) := by
    intro l hl
    have h1 : Dmin w' l = Formalism.MainNotions.S.leadMinorE Z l *
        Formalism.MainNotions.S.leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l := by
      unfold Dmin Formalism.MainNotions.S.leadMinorE
      simp only [dif_pos hl]
      rw [← Matrix.det_mul, ← submatrix_castLE_mul_of_upper hl _ _ hS, ← zhatOM_eq_mul_zhatOM_one, hM, det_submatrix_castLE_LPU_eq hl _ _ _ hL hU]
    rw [h1, conjF_star, star_mul']
    linear_combination (-(Formalism.MainNotions.S.leadMinorE Z l * star (Formalism.MainNotions.S.leadMinorE Z l))) * sign_norm hl
  intro h0
  apply hG
  unfold Formalism.MainNotions.S.LocalSplitGroups.Gpt
  rw [← hsq _ le_rfl, ← hsq _ (Nat.le_succ _)]
  refine Eq.trans ?_ h0
  unfold Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
  rw [show Formalism.MainNotions.S.Zhat (lf D F0).fl F'₂.fl = Z from hZ]

end GramNePf

open GramNePf

theorem globGramNe_holds : GlobGramNe u u' F0 what₂ := by
  intro _ γ Z F'₂ hC hZ hdet
  have hG := gflag_ne γ Z F'₂ hC hZ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hw : ∀ k, (VS D).hT (wG F0 F'₂ k) (∑ j, v j • wG F0 F'₂ j) = 0 := by
    intro k
    have hk := congr_fun hv k
    simp only [Matrix.mulVec, dotProduct, gramG, Matrix.of_apply, brS, Pi.zero_apply] at hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    exact (Finset.sum_congr rfl (fun j _ => mul_comm _ _)).trans hk
  obtain ⟨h1, h2⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F0 F'₂.fl (v ∘ Sum.inl) (v ∘ Sum.inr)
    (∑ j, v j • wG F0 F'₂ j) (by rw [Fintype.sum_sum_type]; rfl)
    (fun a => hw (Sum.inl a)) (fun b => hw (Sum.inr b)) hG
  apply hv0
  funext k
  rcases k with a | b
  · exact congr_fun h1 a
  · exact congr_fun h2 b

variable (Zd : LocDat D)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFstar
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem locFullC_holds : LocFullC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT p M hM
  exact Formalism.L2.SG.Pf.LocalDenominators.exists_isLattice_eq_localLattice Zd p M hM.1.1.1.1 hM.1.1.1.2.1

theorem patchC_holds : PatchC Zd u u' F0 what₂ := patchC_of_full Zd (locFullC_holds Zd u u' F0 what₂)

variable {Zd u u' F0 what₂}

theorem frGlob_of_fstar (hA : FStarC Zd u u' F0 what₂) : Formalism.L2.SG.Pf.PCount.FrGlob Zd u u' F0 what₂ :=
  frGlob_of Zd hA (patchC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClassHolds
section
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass

namespace Formalism.L2.SG.Pf

theorem liftIotaEqC_holds : LiftIotaEqC :=
  fun _ _ Y u _ s₁ s₂ _ _ _ _ hr =>
    Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ (lam_eq Y u hr) (lam'_eq Y u hr) (congrArg (fun r => r.2.2) hr)

theorem stepClassG_holds : StepClassG := stepClassG_of_liftIota liftIotaEqC_holds

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqVanish
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf.MainEqVanish

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ ν, Pinned X u u ν → ∀ t ∈ (Y.tO u u).genSet, (Y.tO u u).vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u →L[ℂ] X.Vpi u),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u w)) Set.univ (X.Wu u) (X.Wu u)
                (Formalism.L2.SG.RealObj.gamW X u u w)).comp B)

theorem stepTermVanishG_of_form (h : FormGC) : StepTermVanishG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, h2⟩ := h Cg cb Cw cT CT C0
  refine ⟨a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc ν hν t ht hJ => ?_⟩
  by_contra hv
  obtain ⟨⟨w, hw, hrep⟩, hform⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc ν hν t ht hv
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w' g :=
    ⟨w, hw, hrep⟩
  unfold J2of at hJ
  rw [dite_eq_left hex] at hJ
  have hJw : Jw Y u u ν hex.choose = 0 :=
    Formalism.L2.SG.NGVanish.hsEmb_eq_zero _ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hJ))
  obtain ⟨c, A, B, hO⟩ := hform hex.choose hex.choose_spec.1 hex.choose_spec.2
  have key : ∀ (k χ c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (Z : X.Vpi u →L[ℂ] X.Vpi u)
      (B : X.Vpi u →L[ℂ] X.Vpi u), k • Z = 0 → k • (χ • (c • A.comp (Z.comp B))) = 0 := by
    intro k χ c A Z B hZ
    have hy : ∀ y, k • Z y = 0 := fun y => by simpa using congrArg (fun T => T y) hZ
    ext x
    simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply]
    rw [smul_comm k χ, smul_comm k c, ← map_smul A k, hy]
    simp
  have hamp : ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0 := by
    unfold ampN
    rw [hO]
    unfold Jw at hJw
    exact key _ _ _ _ _ _ hJw
  apply hv
  show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
  unfold vec
  rw [hamp]
  simp
  rfl

end Formalism.L2.SG.Pf.MainEqVanish
end
end

