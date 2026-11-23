module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0047
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.FrameOKMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TrDetPfH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieLG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0029

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CntIso
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in
open PI.RepsIndep.Tr in
theorem ci_EZ_map {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {Z : MatZ D} {F' : LFlag (D.sp.Y 0) D.R.rS T'} (h : F' ∈ EZ T' F0 Λ Z) :
    mapL β hβ F' ∈ EZ T' (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z := by
  have hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0) := lflag_ext rfl rfl
  unfold EZ at h ⊢
  rw [Set.mem_setOf_eq] at h ⊢
  rw [hlf]
  obtain ⟨⟨hL, ⟨ξ, hξ⟩, hG⟩, hA, hGen, hF, hZ⟩ := h
  have hG' : Gval (mapL β hβ (lf D F0)) (mapL β hβ F') ≠ 0 := by
    show Formalism.MainNotions.S.Gflag (mapF β hβ F0) (mapF β hβ F'.fl) ≠ 0
    simp only [Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl, Zhat_mapF hβ]
    exact hG
  have hZ' : ZhatL (mapL β hβ (lf D F0)) (mapL β hβ F') = Z := by
    show Formalism.MainNotions.S.Zhat (mapF β hβ F0) (mapF β hβ F'.fl) = Z
    rw [Zhat_mapF hβ]
    exact hZ
  exact ⟨⟨IsLift_map hβ hL, ⟨ξ, AdmWit_map hβ hξ⟩, hG'⟩, AdmWit_map hβ hA, IsGeneric_map hβ hGen,
    FrameOK_map hβ hF, hZ'⟩

set_option maxHeartbeats 2000000 in
open PI.RepsIndep.Tr in
theorem ci_rel_map {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {F' F'' : LFlag (D.sp.Y 0) D.R.rS T'} (h : NilradicalFlagMoved F0 Λ F' F'') :
    NilradicalFlagMoved (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F') (mapL β hβ F'') := by
  have hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0) := lflag_ext rfl rfl
  obtain ⟨n, ⟨hnL, hne, hnz⟩, h1, h2⟩ := h
  have hN : conj β n ∈ NLam (Formalism.HermitianLatticesTheory.gmap β Λ) (lf D (mapF β hβ F0)) := by
    rw [hlf]; exact NLam_conj hβ hnL
  refine ⟨conj β n, ⟨hN, fun a => ?_, ?_⟩, fun a => ?_, ?_⟩
  · show β (n (β.symm (β (F0.e a)))) = β (F0.e a)
    rw [LinearEquiv.symm_apply_apply, hne]
  · show β (n (β.symm (β F0.z))) = β F0.z
    rw [LinearEquiv.symm_apply_apply, hnz]
  · show β (n (β.symm (β (F'.fl.e a)))) = β (F''.fl.e a)
    rw [LinearEquiv.symm_apply_apply, h1]
  · show β (n (β.symm (β F'.fl.z))) = β F''.fl.z
    rw [LinearEquiv.symm_apply_apply, h2]

open PI.RepsIndep.Tr in
theorem ci_mapF_symm {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : mapF β.symm (iso_symm hβ) (mapF β hβ F0) = F0 :=
  flag_ext (funext fun a => LinearEquiv.symm_apply_apply β (F0.e a)) (LinearEquiv.symm_apply_apply β F0.z)

open PI.RepsIndep.Tr in
theorem counting_iso_inverse : CntIsoInv := by
  intro D β hβ T T' F0 Λ Z
  have hβ' := iso_symm hβ
  have hΛ : Formalism.HermitianLatticesTheory.gmap β.symm (Formalism.HermitianLatticesTheory.gmap β Λ) = Λ := gmap_symm_gmap β Λ
  have hF : Formalism.L2.SG.Saturated.mapFlag β hβ F0 = mapF β hβ F0 := flag_ext rfl rfl
  rw [hF]
  show Formalism.MainNotions.S.Cnt.cntCl (EZ T' (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z) (NilradicalFlagMoved (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ)) =
    Formalism.MainNotions.S.Cnt.cntCl (EZ T' F0 Λ Z) (NilradicalFlagMoved F0 Λ)
  refine cntCl_equiv (mapL β hβ) (mapL β.symm hβ') (mapL_symm hβ) (mapL_symm' hβ hβ') _ _ _ _
    (fun F' => ⟨fun h => ?_, fun h => ci_EZ_map hβ h⟩) (fun F' F'' => ⟨fun h => ?_, fun h => ci_rel_map hβ h⟩)
  · have e := ci_EZ_map hβ' h
    rw [mapL_symm hβ, ci_mapF_symm hβ, hΛ] at e
    exact e
  · have e := ci_rel_map hβ' h
    rw [mapL_symm hβ, mapL_symm hβ, ci_mapF_symm hβ, hΛ] at e
    exact e

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRc
section
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

theorem trDetUnimod_holds : TrDetUnimod := TrD.trDetUnimod_of TrD.detHOne_holds

theorem rowBlockCovol_holds : RowBlockCovol := rowBlockCovol_of trDetUnimod_holds

theorem blockCovol_holds : BlockCovol := blockCovol_of rowBlockCovol_holds

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensAtD
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EtaLocAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : PlF D, (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then (-1 : ℝ) else 1) = etaF D.host.E D.host.F p.asIdeal

theorem etaLocAt_of_tied {D : Formalism.BasicNotions.D7} (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) : EtaLocAt D := fun p => Formalism.L2.SG.Pf.AlTieLG.etaLoc_of_tied hL p

def DensProdValAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D) (c : ℕ), c ≤ 2 * (D.R.rS + 1) →
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp])
                (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then -1 else 1) D.R.r (2 * (D.R.rS + 1)) c =
        alphaStd D.host.E p.asIdeal D.R.r / alphaStd D.host.E p.asIdeal (D.R.k - 1 - c)

def DensMultIntAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → Multipliable (densP L δ ϖ (Tn u) (Tn u') Z)

theorem densProdValAt_of {D : Formalism.BasicNotions.D7} (hη : EtaLocAt D) : DensProdValAt D := by
  intro δ M _ p c hc
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hq := Formalism.L2.SG.Pf.LocModel.resCard_loc (D.s.atP p)
  have hmax : p.asIdeal.IsMaximal := p.isMaximal
  have hpos := alphaStd_pos hK hF hmax (D.R.k - 1 - c)
  rw [eq_div_iff hpos.ne', alpha_split' (K := D.host.E) p.asIdeal (show D.R.k - 1 - c ≤ D.R.r by omega), mul_comm]
  congr 1
  unfold Formalism.L2.SG.DensExact.densProd
  rw [hq, hη p, show D.R.r + 1 - (2 * (D.R.rS + 1) + c) = D.R.k - 1 - c + 1 by omega]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [zpow_neg, zpow_natCast]

theorem densValAt_of (h1 : LocSelfDual) (h2 : GaPlusDiag) {D : Formalism.BasicNotions.D7} (h5 : DensProdValAt D) :
    ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∀ p : PlF D,
          densP L δ ϖ (Tn u) (Tn u') Z p =
            alphaStd D.host.E p.asIdeal D.R.r /
              alphaStd D.host.E p.asIdeal (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal) := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p
  obtain ⟨A, a, hAO, hAdet, hG, hc⟩ := h2 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p
  have hSD := h1 D δ M hA L p
  obtain ⟨-, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hz hZ hP
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hcard : Fintype.card (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ≤ Module.finrank (D.s.atP p).Ep (L.V p) := by
    rw [L.rank p, Fintype.card_sum, Fintype.card_fin]
    omega
  have hcle : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal ≤ 2 * (D.R.rS + 1) := by
    have := Formalism.L2.SG.Pf.Asm.cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal
    rw [hUr, hm] at this
    exact this
  unfold densP
  rw [hG, local_density_corank (D.s.atP p).Fp (D.s.atP p).Ep (M p) (D.s.atP p).lf (D.s.atP p).char0 (L.V p)
    (L.H p) (lattice₂ L p (VS D).L0) hSD (ϖ p) (hϖ p) _ A a hAO hAdet hcard, L.rank p, Fintype.card_sum,
    Fintype.card_fin, hc, show D.R.rS + 1 + (D.R.rS + 1) = 2 * (D.R.rS + 1) by ring]
  exact h5 δ M hA p _ hcle

theorem densMultIntAt_of (h1 : LocSelfDual) (h2 : GaPlusDiag) {D : Formalism.BasicNotions.D7} (h5 : DensProdValAt D) :
    DensMultIntAt D := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  have hval := densValAt_of h1 h2 h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  obtain ⟨-, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hz hZ hP
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : Summable (fun p : PlF D => densP L δ ϖ (Tn u) (Tn u') Z p - 1) := by
    refine Summable.of_norm_bounded_eventually ((PI.UnitaryGroupMassFormula.CntFormula.prime_zeta_two D.host.F).mul_left 6) ?_
    filter_upwards [(absNorm_small_finite D).compl_mem_cofinite] with p hp
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hp
    have hcle : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal ≤ 2 * (D.R.rS + 1) := by
      have := Formalism.L2.SG.Pf.Asm.cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal
      rw [hUr, hm] at this
      exact this
    obtain ⟨-, hup, hlow⟩ := Formalism.L2.SG.Pf.DensLoc.ratio_bounds (K := D.host.E) p.asIdeal (by linarith)
      (j := D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal) (n := D.R.r) (s := 2)
      (by omega) (by omega) (by norm_num)
    have hlow' := hlow hp
    rw [hval p, Real.norm_eq_abs]
    set x : ℝ := ((Ideal.absNorm p.asIdeal : ℝ))⁻¹ with hx
    have hx0 : 0 ≤ x := inv_nonneg.2 (by linarith)
    have hx3 : x ≤ 1 / 3 := by rw [hx, one_div]; exact inv_anti₀ (by norm_num) hp
    have hx2 : x ^ 2 ≤ 1 / 9 := by nlinarith
    have hx2n : 0 ≤ x ^ 2 := sq_nonneg x
    have h2n : (0 : ℝ) ≤ 2 * x ^ 2 := by positivity
    have h3n : (0 : ℝ) ≤ 3 * x ^ 2 := by positivity
    have e1 := Real.abs_exp_sub_one_le (x := 2 * x ^ 2) (by rw [abs_of_nonneg h2n]; linarith)
    have e2 := Real.abs_exp_sub_one_le (x := -(3 * x ^ 2)) (by rw [abs_neg, abs_of_nonneg h3n]; linarith)
    rw [abs_of_nonneg h2n] at e1
    rw [abs_neg, abs_of_nonneg h3n] at e2
    have hq : 6 * (1 / ((Ideal.absNorm p.asIdeal : ℝ) ^ 2)) = 6 * x ^ 2 := by rw [hx, inv_pow, one_div]
    rw [hq, abs_le]
    constructor
    · have := (abs_le.mp e2).1
      linarith
    · have := (abs_le.mp e1).2
      linarith
  have := Real.multipliable_one_add_of_summable hs
  simpa using this

theorem densAllAt_of_steps (h1 : LocSelfDual) (h2 : GaPlusDiag) (h3 : NotIntDens) {D : Formalism.BasicNotions.D7}
    (h5 : DensProdValAt D) (h6 : DensMultIntAt D) : Formalism.L2.SG.Pf.DensLoc.DensAllAt D := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP
  exact ⟨fun hI => ⟨densValAt_of h1 h2 h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI,
      h6 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI⟩,
    fun hI => h3 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI⟩

theorem densAllAt_of_tied {D : Formalism.BasicNotions.D7} (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) : Formalism.L2.SG.Pf.DensLoc.DensAllAt D := by
  have h1 : LocSelfDual := local_self_dual_holds
  have hF : DualityBasisChange.FrameBasisL := DualityBasisChange.frameBasisL_holds
  have h2 : GaPlusDiag := DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds
  have h5 : DensProdValAt D := densProdValAt_of (etaLocAt_of_tied hL)
  exact densAllAt_of_steps h1 h2 (DualityBasisChange.not_integral_density_of_self_dual h1 hF) h5 (densMultIntAt_of h1 h2 h5)

theorem densLocBound_of_tied {D : Formalism.BasicNotions.D7} (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) : Formalism.L2.SG.DataCut.DensLocBound D := Formalism.L2.SG.Pf.DensLoc.densLocBound_at (densAllAt_of_tied hL)

def DensInputT : Prop := ∀ D : Formalism.BasicNotions.D7, Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.SG.DataInst.DensInputAt D

theorem densInputT_holds : DensInputT := fun D hL => Formalism.L2.SG.DataCut.densInputAt_of_loc (densLocBound_of_tied hL)

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InvMulOfUnitri
section
noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem inv_mul_of_unitri {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E}
    (h0 : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (h1 : ∀ a, X0 a a = 1) : X0⁻¹ * X0 = 1 := by
  have hdet : X0.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
    simp [h1]
  exact Matrix.nonsing_inv_mul X0 (by rw [hdet]; exact isUnit_one)

theorem inW_sub {x y : (VS D).V} (hx : InW X x) (hy : InW X y) : InW X (x - y) := by
  intro c
  rw [map_sub, map_sub, (hx c).1, (hy c).1, (hx c).2, (hy c).2, sub_self]
  exact ⟨rfl, rfl⟩

theorem h_pW_left (y : (VS D).V) {w : (VS D).V} (hw : InW X w) : (VS D).hT y w = (VS D).hT (pW X y) w := by
  conv_lhs => rw [decomp X y]
  rw [LinearMap.map_add₂, LinearMap.map_add₂, h_sum_left, h_sum_left]
  simp [(hw _).1, (hw _).2]

theorem dictEx_holds : DictEx := by
  intro D X u X0 xs M hD
  obtain ⟨h0, h1, hxs, hM⟩ := hD
  have hinv := inv_mul_of_unitri h0 h1
  set n := nEq X X0 xs M hinv hxs hM with hn
  have hnx : ∀ y, n y = nL X X0 xs M y := fun y => rfl
  have hFe : (X.Fu u).e = X.eX := X.Fu_e u
  refine ⟨n, ⟨fun x y => ?_, fun j x hx => ?_, fun x hx => ?_⟩, ?_, ?_, ?_⟩
  ·
    show (VS D).hT (n x) (n y) = (VS D).hT x y
    rw [hnx, hnx]
    exact nL_isom X X0 xs M hinv hxs hM x y
  ·
    show n x - x ∈ (X.Fu u).Xa j
    have hx' : x ∈ (X.Fu u).Xa (j + 1) := hx
    unfold FlagG.Xa at hx' ⊢
    rw [hFe] at hx' ⊢
    refine Submodule.span_induction (p := fun x _ => n x - x ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < j}))
      ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨i, hi, rfl⟩
      rw [hnx, nL_e]
      unfold nE
      have e1 : ∑ b, X0 b i • X.eX b - X.eX i = ∑ b, (X0 b i - if b = i then 1 else 0) • X.eX b := by
        simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
      rw [e1]
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < j
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
      · have hbi : i ≤ b := by
          have : (i : ℕ) < j + 1 := hi
          exact Fin.le_def.2 (by omega)
        rcases hbi.lt_or_eq with hlt | heq
        · rw [h0 b i hlt, if_neg (ne_of_gt hlt), sub_zero, zero_smul]
          exact Submodule.zero_mem _
        · subst heq
          rw [h1, if_pos rfl, sub_self, zero_smul]
          exact Submodule.zero_mem _
    · simp
    · intro a b _ _ ha hb
      rw [map_add (f := _), add_sub_add_comm]
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ ha
  ·
    show n x - x ∈ (X.Fu u).X
    have horth : ∀ c, (VS D).hT (X.eX c) x = 0 := by
      intro c
      have hxo : x ∈ Lat.orth (VS D) (X.Fu u).X := hx
      unfold Lat.orth at hxo
      have := (Submodule.mem_iInf _).1 hxo (X.eX c)
      rw [Submodule.mem_iInf] at this
      have hmem : X.eX c ∈ (X.Fu u).X := by
        unfold FlagG.X
        rw [hFe]
        exact Submodule.subset_span ⟨c, rfl⟩
      exact LinearMap.mem_ker.1 (this hmem)
    unfold FlagG.X
    rw [hFe]
    have hdec := decomp X x
    simp only [horth, zero_smul, Finset.sum_const_zero, add_zero] at hdec
    have e1 : n x - x = ∑ c, (VS D).hT (X.fY c) x • (nE X X0 c - X.eX c) +
        ∑ b, (VS D).hT (xs b) (pW X x) • X.eX b := by
      calc n x - x = (∑ c, (VS D).hT (X.fY c) x • nE X X0 c +
            (pW X x + ∑ b, (VS D).hT (xs b) (pW X x) • X.eX b)) -
            (∑ c, (VS D).hT (X.fY c) x • X.eX c + pW X x) := by
            rw [← hdec, hnx, nL_apply]
            simp only [horth, zero_smul, Finset.sum_const_zero, add_zero]
        _ = _ := by
            simp only [smul_sub, Finset.sum_sub_distrib]
            abel
    rw [e1]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
    unfold nE
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      (Submodule.subset_span ⟨c, rfl⟩)
  ·
    funext b a
    show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a
    rw [hnx, nL_e]
    unfold nE
    rw [h_sum_right]
    simp [h_fe, Finset.sum_ite_eq]
  ·
    funext b
    set y := n.symm (X.fY b) with hy
    have hny : n y = X.fY b := n.apply_symm_apply _
    have hd : InW X (pW X y - xs b) := inW_sub X (inW_pW X y) (hxs b)
    have hw0 : ∀ w, InW X w → (VS D).hT (pW X y - xs b) w = 0 := by
      intro w hw
      rw [LinearMap.map_sub₂, ← h_pW_left X y hw]
      have : (VS D).hT y w = (VS D).hT (n y) (n w) := (nL_isom X X0 xs M hinv hxs hM y w).symm
      rw [this, hny, hnx, h_f_nLw X X0 xs M hxs hw, sub_self]
    show pW X y = xs b
    rw [← sub_eq_zero]
    refine (VS D).nondeg.1 _ fun v => ?_
    conv_lhs => rw [decomp X v]
    rw [map_add (f := _), map_add (f := _), h_sum_right, h_sum_right, hw0 _ (inW_pW X v)]
    simp [(inW_left X (inW_pW X y) _).1, (inW_left X (inW_pW X y) _).2, (inW_left X (hxs b) _).1,
      (inW_left X (hxs b) _).2]
  ·
    have hA : Aq X n = X0 * M := by
      funext b a
      show (VS D).hT (X.fY b) (n (X.fY a)) = (X0 * M) b a
      rw [hnx, nL_f, h_f_nF X X0 xs M hxs]
    show (Xq X n)⁻¹ * Aq X n = M
    have hXq : Xq X n = X0 := by
      funext b a
      show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a
      rw [hnx, nL_e]
      unfold nE
      rw [h_sum_right]
      simp [h_fe, Finset.sum_ite_eq]
    rw [hXq, hA, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

