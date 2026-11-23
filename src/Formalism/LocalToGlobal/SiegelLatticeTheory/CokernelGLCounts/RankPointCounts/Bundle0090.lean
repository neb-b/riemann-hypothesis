module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0076
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0060
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0065
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ReHermitianCombinationNonpos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0088

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdTermHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem bwdTerm'_holds : BwdTerm' Zd u u' F0 what₂ := bwdTerm'_of_gx (genXiRev_holds Zd)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CrossOfComp
section
noncomputable section

open Matrix ValuativeRel
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount
  Formalism.L2.SG.LsDatumB

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cross_of_comp {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ} {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (h1 : Cross (A.map (π1 M g)) (A'.map (π1 M g))) (h2 : Cross (A.map (π2 M g)) (A'.map (π2 M g))) : Cross A A' := by
  unfold Cross at h1 h2 ⊢
  have d : ∀ (f : E →+* F) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (B.map f).det = f B.det :=
    fun f B => (RingHom.map_det f B).symm
  rw [ld_map, ld_map, d, d, ← map_mul, ← map_mul] at h1 h2
  apply g.e.injective
  exact Prod.ext h1 h2

theorem gaPlusTh_of (hLO : LiftOrb) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) : GaPlusTh M δ u u' := by
  intro hA hT hPH w w' Z Z' hk hZ hZ' p hne heq
  set c := cornerSh δ (D.mem u).A.T (D.mem u').A.T p w with hc
  have hc' : cornerSh δ (D.mem u).A.T (D.mem u').A.T p w' = c := (cornerSh_of_kind δ _ _ p hk).symm
  set Y := CntLocal.ZZP (M := M) δ u u' p Z + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY
  set Y' := CntLocal.ZZP (M := M) δ u u' p Z' + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY'
  have hcm : ∀ cc : (D.s.atP p).Ep, (Matrix.of fun a b : Fin (D.R.rS + 1) =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cc else 0) = cc • Ec (K := (D.s.atP p).Ep) D.R.rS := by
    intro cc; ext a b; simp only [Ec, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  have eY : FCount.thZ M δ u u' w Z p = clsOf (M p) Y := by
    unfold FCount.thZ thL; rw [hcm]
  have eY' : FCount.thZ M δ u u' w' Z' p = clsOf (M p) Y' := by
    unfold FCount.thZ thL; rw [hcm, hc']
  rw [eY] at hne heq
  rw [eY'] at heq

  have hXc : Cross (ZhatLoc M δ p Z) (ZhatLoc M δ p Z') := cross_zhatLoc δ M p (cross_global hk hZ hZ')
  have hZc : Cross (CntLocal.ZZP (M := M) δ u u' p Z) (CntLocal.ZZP (M := M) δ u u' p Z') := by
    unfold CntLocal.ZZP
    rcases hs : (M p).split with _ | g
    · unfold Loc.HermSp.ZZplusOf; rw [hs]; exact hXc
    · refine cross_of_comp (M p) g ?_ ?_
      · rw [zzPlus_map_firstComponent (M p) g hs, zzPlus_map_firstComponent (M p) g hs]
        exact cross_shift (cross_map _ hXc) _ _
      · rw [zzPlus_map_secondComponent (M p) g hs, zzPlus_map_secondComponent (M p) g hs]
        exact cross_shift (cross_transpose (cross_map _ hXc)) _ _
  unfold clsOf at hne heq
  by_cases h1 : (∀ a b, Y a b ∈ (M p).R) ∧ IsUnit Y.det
  swap
  · exact absurd (dif_neg h1) hne
  rw [dite_eq_left h1] at heq
  by_cases h2 : (∀ a b, Y' a b ∈ (M p).R) ∧ IsUnit Y'.det
  swap
  · rw [dif_neg h2] at heq; exact absurd heq (by simp)
  rw [dite_eq_left h2] at heq
  set ZZ : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y a b, h1.1 a b⟩, h1.2⟩ with hZZ
  set ZZ' : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y' a b, h2.1 a b⟩, h2.2⟩ with hZZ'
  have hmap : ZZ.Z.map (M p).R.subtype = Y := rfl
  have hmap' : ZZ'.Z.map (M p).R.subtype = Y' := rfl
  have hiso : Nonempty ((M p).Iso ZZ ZZ') := Quotient.exact (Option.some.inj heq)
  have hκ : (ZZ.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) =
      (ZZ'.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) := by
    rw [hmap, hmap']
    exact kappa_eq hZc c h1.2 h2.2
  obtain ⟨l, ρ, hlu, hρu, hle, hρl, hrel⟩ := hLO (M p) (hA p).1 D.R.rS ZZ ZZ' hiso hκ
  set L := l.map (M p).R.subtype with hLdef
  set P := ρ.map (M p).R.subtype with hPdef
  have hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0 := by
    intro i; simp only [hLdef, Matrix.map_apply, hle i]; split_ifs <;> simp
  have hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0 := by
    intro j; simp only [hPdef, Matrix.map_apply, hρl j]; split_ifs <;> simp
  have hYrel : Y' = L * Y * P := by
    rw [← hmap, ← hmap', hrel, Matrix.map_mul, Matrix.map_mul]
  have hZrel : CntLocal.ZZP (M := M) δ u u' p Z' = L * CntLocal.ZZP (M := M) δ u u' p Z * P := by
    have e := hYrel
    rw [hY, hY', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Ec_eq_cornerM,
      corner_sandwich L P hL hP 1] at e
    exact add_right_cancel e
  have hLR : ∀ i j, L i j ∈ (M p).R := fun i j => (l i j).2
  have hPR : ∀ i j, P i j ∈ (M p).R := fun i j => (ρ i j).2
  have hLu : ∃ y ∈ (M p).R, L.det * y = 1 := by
    obtain ⟨v, hv⟩ := hlu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : L.det = ((l.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype l).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  have hPu : ∃ y ∈ (M p).R, P.det * y = 1 := by
    obtain ⟨v, hv⟩ := hρu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : P.det = ((ρ.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype ρ).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rcases hs : (M p).split with _ | g
  · have hRO : (M p).R = (M p).L.O := by unfold Loc.Model.R; rw [hs]
    have hX : ZhatLoc M δ p Z' = L * ZhatLoc M δ p Z * P := by
      have e := hZrel
      unfold CntLocal.ZZP Loc.HermSp.ZZplusOf at e
      rw [hs] at e
      exact e
    obtain ⟨yL, hyL, hLy⟩ := hLu
    obtain ⟨yP, hyP, hPy⟩ := hPu
    exact gaCong_L δ M hA p hs _ _ Z Z' L P hL hP (fun i j => hRO ▸ hLR i j) (fun i j => hRO ▸ hPR i j)
      ⟨yL, hRO ▸ hyL, hLy⟩ ⟨yP, hRO ▸ hyP, hPy⟩ hX
  · exact gaCong_G δ M hA p g hs _ _ _ _ Z Z' L P hL hP hLR hPR hLu hPu hZrel

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIotaA
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem gS_typed (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O, ∃ w' ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w ∧
        w * w' = 1 := by
  obtain ⟨sg, hsg, hq, -⟩ := typed_data Zd p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, (D.s.atP p).ιE (uP p : D.host.E),
    Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p, ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]
  · rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [mul_inv_cancel₀ h0, map_one]

theorem localLattice_mono {A B : Submodule (𝓞 D.host.E) (VS D).V} (h : A ≤ B) : lattice₂ D Zd.M p A ≤ lattice₂ D Zd.M p B :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_O_M {a : (D.s.atP p).Ep} (ha : a ∈ (D.s.atP p).O) : a ∈ (Zd.M p).L.O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.hO Zd p]; exact ha

theorem smul_gS_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [← Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    have h1 : ((gS D : ℕ) : D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • y := by
      rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) y, map_natCast]
    rw [SetLike.mem_coe, h1]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • v) = o • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
      show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hv

theorem untyped_mem (hs : (Zd.M p).split = none) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  have e := Formalism.L2.SG.Pf.StabIntSh.gS_mul_uP Zd.δ Zd.M Zd.agree p hs
  have hv' : v = (D.s.atP p).ιE (uP p : D.host.E) • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
    rw [smul_smul, mul_comm, e, one_smul]
  rw [hv']
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p) (smul_gS_mem Zd p F F' hv)

theorem typed_q_mem (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  obtain ⟨w, -, w', hw', he, hww⟩ := gS_typed Zd p g hs
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v =
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w' • v) := by
    rw [he, smul_smul, mul_assoc, hww, mul_one]
  rw [e]
  exact smul_gS_mem Zd p F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p hw' hv)

theorem l1 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')
    (f : Fin (D.R.rS + 1) → Vp D p) (s : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hs : ∀ a, s a ∈ (D.s.atP p).O)
    (hf : ∀ i : Fin D.R.rS, f i.castSucc = (s i.castSucc * frFac Zd.δ p i.castSucc) • baseChange₂ D p (G.fl.e i))
    (hprim : (locH Zd p).Prim (lattice₂ D Zd.M p Λ) f) (hXS : XLam Λ G = XS D G.fl) {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) (hvX : v ∈ (locH Zd p).X f) : v ∈ lattice₂ D Zd.M p (XLam Λ G) := by
  have hvE : v ∈ Submodule.span (D.s.atP p).Ep (Set.range f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) hvX
  have hvO := hprim.2.2 v hv hvE
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Zd.M p).L.O).1 hvO
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (D.s.atP p).Ep).1 hvX
  have key : (c (Fin.last D.R.rS) : (D.s.atP p).Ep) = 0 := by
    have h0 : ∑ a, ((c a : (D.s.atP p).Ep) - Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a) • f a = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc (f := fun a => Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a • f a)]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
      rw [he, ← hc, sub_eq_zero]
      rfl
    have := Fintype.linearIndependent_iff.1 hprim.2.1 _ h0 (Fin.last D.R.rS)
    simpa using this
  rw [← hc, Fin.sum_univ_castSucc]
  refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) ?_
  · rw [hf, hXS, Formalism.L2.SG.Pf.BBTie.bt_latP_XS Zd p (Formalism.L2.SG.Pf.locDiffC_holds D Zd) G.fl, mul_smul]
    have hm : frFac Zd.δ p i.castSucc • baseChange₂ D p (G.fl.e i) ∈ Submodule.span (Zd.M p).L.O
        (Set.range fun a : Fin D.R.rS => frFac Zd.δ p a.castSucc • baseChange₂ D p (G.fl.e a)) := Submodule.subset_span ⟨i, rfl⟩
    exact Submodule.smul_mem _ (⟨s i.castSucc, mem_O_M Zd p (hs _)⟩ : (Zd.M p).L.O) hm
  · have : c (Fin.last D.R.rS) • f (Fin.last D.R.rS) = 0 := by
      rw [Subring.smul_def, key, zero_smul]
    rw [this]; exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameMemUUE
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem localSign_sq (p : PlF D) (a : Fin (D.R.rS + 1)) : TermLoc.sgnP D p a * TermLoc.sgnP D p a = 1 := by
  unfold TermLoc.sgnP
  split
  · rename_i sg _
    rw [← map_mul, Prod.mk_mul_mk, Formalism.L2.SG.Pf.FibD.neg_one_pow_sq, one_mul]
    exact map_one sg.e.symm
  · exact one_mul 1

theorem hu_all (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) :=
  IsUnit.mul ⟨Units.mkOfMulEqOne _ _ (localSign_sq p a), rfl⟩
    (Formalism.L2.SG.Pf.StabShape.frFac_unit Zd.δ Zd.M (Zd.agree p) a)

theorem frame_mem_UUE {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (G : LFlag (D.sp.Y 0) D.R.rS T') (b : Fin (D.R.rS + 1)) :
    frame G b ∈ UUE Λ F (liftF G) := by
  induction b using Fin.lastCases with
  | last =>
    rw [frame_lastG]
    apply Submodule.subset_span
    show G.fl.z ∈ (UU Λ F (liftF G) : Set (VS D).V)
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  | cast i =>
    rw [frame_csG]
    haveI := hΛ
    obtain ⟨s, hs, hsv⟩ := Formalism.L2.SG.Pf.exists_smul_mem Λ (G.fl.e i)
    have hX : s • G.fl.e i ∈ UU Λ F (liftF G) := by
      refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hsv, ?_⟩)
      show s • G.fl.e i ∈ (Xsp (liftF G) : Set (VS D).V)
      exact Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨i, rfl⟩)
    have hs' : ((s : D.host.E)) ≠ 0 := by exact_mod_cast hs
    have e : G.fl.e i = ((s : D.host.E))⁻¹ • (s • G.fl.e i) := by
      rw [← algebraMap_smul (R := 𝓞 D.host.E) D.host.E s (G.fl.e i), smul_smul]
      show G.fl.e i = (((s : D.host.E))⁻¹ * algebraMap (𝓞 D.host.E) D.host.E s) • G.fl.e i
      rw [show algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E) from rfl, inv_mul_cancel₀ hs', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hX)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfCoefficients
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

theorem lemmaG3_of_coefficients (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0)
    (h2 : Gt t2 ≠ 0) (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) (hG1 : t1.G = t0.G) (hG2 : t2.G = t0.G)
    (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u')))
    (he : t2.lin = σ * t1.lin * s') (ha : coefA Y u u' t0 t1 = coefA Y u u' t0 t2)
    (ha' : coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2) :
    nmlOf Y u u' t1 = nmlOf Y u u' t2 := by
  obtain ⟨iω, iς, i3⟩ := lemmaG3_of_inputs Y hT hT' t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'
  have hγ1 : t1.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t1.rep.2.2.1
  have hGF1 : Gflag (X.Fu u) t1.frame.fl ≠ 0 := G_ne_of_Gt Y h1
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hσ' := SRat_inv (lf D (X.Fu u)) hσ
  have hs'' := SRat_inv (lf D (X.Fu u')) hs'
  set ς := t1.lin * s'⁻¹ * t1.lin⁻¹ with hς
  have hςx : ∀ x, ς x = t1.lin (s'.symm (t1.lin.symm x)) := fun x => rfl
  have hςf : ∀ x ∈ t1.frame.fl.X, ς x - x ∈ t1.frame.fl.X := by
    intro x hx
    refine (mem_frameX Y t1 _).2 ?_
    have hx0 := (mem_frameX Y t1 x).1 hx
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply]
    exact Submodule.sub_mem _ (X_pres (lf D (X.Fu u')) hs''.2.1 _ hx0) hx0
  have hςz : ς t1.frame.fl.z - t1.frame.fl.z ∈ t1.frame.fl.X := by
    refine (mem_frameX Y t1 _).2 ?_
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply]
    exact hs''.2.2
  obtain ⟨τ, hτi, hτA, P1, P2⟩ := tau_exists (X.Fu u) t1.frame.fl hGF1 hTE (star_natCast _) hTE' (star_natCast _)
    σ ς hσ.1 (fun x hx => Submodule.sub_mem _ (X_pres (lf D (X.Fu u)) hσ.2.1 x hx) hx)
    (fun x hx => X_pres (lf D (X.Fu u)) hσ'.2.1 x hx) hσ.2.2 hςf hςz iω iς i3
  have hτX : ∀ x ∈ (X.Fu u).X, τ x = x := fun x hx => hτA x (X_le_Asp _ _ hx)
  have hτX1 : ∀ x ∈ t1.frame.fl.X, τ x = x := fun x hx => hτA x (by rw [← Asp_symm]; exact X_le_Asp _ _ hx)
  have hτs : ∀ x ∈ (X.Fu u).X, τ.symm x = x := fun x hx => by
    conv_lhs => rw [← hτX x hx]
    simp
  set n := σ * τ⁻¹ with hn
  set n' := t1.lin⁻¹ * τ * t1.lin * s' with hn'
  have hnN : n ∈ NRat (lf D (X.Fu u)) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem hσ.1 ((Formalism.HermitianLatticesTheory.isom _).inv_mem hτi), fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u).X := Xflag_le_X (lf D (X.Fu u)) (j + 1) hx
      show σ (τ.symm x) - x ∈ _
      rw [hτs x hxX]
      exact hσ.2.1 j x hx
    · have hτi' : τ.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom _).inv_mem hτi
      have hz : τ.symm y ∈ orth (VS D) (Xsp (lf D (X.Fu u))) :=
        perp_pres (lf D (X.Fu u)) hτi' (fun x hx => by rw [LinearEquiv.symm_symm, hτX x hx]; exact hx) y hy
      have := P1 _ hz
      rw [LinearEquiv.apply_symm_apply] at this
      show σ (τ.symm y) - y ∈ _
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
  have hn'N : n' ∈ NRat (lf D (X.Fu u')) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem
      ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ1) hτi) hγ1) hs'.1, fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u').X := Xflag_le_X (lf D (X.Fu u')) (j + 1) hx
      have hsx : s' x ∈ (X.Fu u').X := X_pres (lf D (X.Fu u')) hs'.2.1 x hxX
      have h1x : t1.lin (s' x) ∈ t1.frame.fl.X := (mem_frameX Y t1 _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hsx)
      show t1.lin.symm (τ (t1.lin (s' x))) - x ∈ _
      rw [hτX1 _ h1x, LinearEquiv.symm_apply_apply]
      exact hs'.2.1 j x hx
    · have hsy : s' y ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) :=
        perp_pres (lf D (X.Fu u')) hs'.1 (fun x hx => X_pres (lf D (X.Fu u')) hs''.2.1 x hx) y hy
      have hv : t1.lin (s' y) ∈ Lat.orth (VS D) t1.frame.fl.X := by
        refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
        rw [show x = t1.lin (t1.lin.symm x) by simp, hγ1]
        exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).1 hsy _ ((mem_frameX Y t1 x).1 hx)
      have h := P2 _ hv
      rw [hςx, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
      have h' := (mem_frameX Y t1 _).1 h
      rw [map_sub, LinearEquiv.symm_apply_apply] at h'
      exact h'
  have heq : t2.lin = n * t1.lin * n' := by
    rw [he, hn, hn']
    group
  ext δ
  constructor
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n⁻¹, NRat_mul _ hm (NRat_inv _ hnN), n'⁻¹ * m', NRat_mul _ (NRat_inv _ hn'N) hm', ?_⟩
    rw [heq]
    group
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n, NRat_mul _ hm hnN, n' * m', NRat_mul _ hn'N hm', ?_⟩
    rw [heq]
    group

theorem normalsLemmaG3_holds : UnitaryNormalVectorCount := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 hσs ha ha' => ?_⟩
  obtain ⟨σ, hσ, s', hs', he⟩ := hσs
  have hT : 3 ≤ Tu D u ∧ 3 ≤ Tu D u' := by
    clear * - hc
    unfold Ctx at hc
    obtain ⟨-, -, -, h3, h3', -⟩ := hc.2.1
    exact ⟨h3, h3'⟩
  exact lemmaG3_of_coefficients Y hT.1 hT.2 t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LmatMemR
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem det_upper {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, b < a → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular id := fun i j hij => h1 i j hij
  rw [Matrix.det_of_upperTriangular hb]
  simp [h2]

theorem det_lower {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, a < b → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular OrderDual.toDual := fun i j hij => h1 i j hij
  rw [Matrix.det_of_lowerTriangular X hb]
  simp [h2]

theorem lmat_mem_R (hs : (Z.M p).split = some g) {x y : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O)
    (hy : y ∈ (Z.M p).L.O)
    (hc : ∃ o ∈ (Z.M p).L.O, x - (Z.M p).L.cj y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o) :
    g.e.symm ((g.e x).1, (g.e y).2) ∈ (Z.M p).R := by
  obtain ⟨o, ho, he⟩ := hc
  refine mem_R_of Z p g hs (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hx).1)
    (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hy).2) ⟨(g.e o).1, (comp_mem Z p g ho).1, ?_⟩
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun t => (g.e t).1) he
  simp only [map_sub, map_mul, AlgEquiv.commutes, g.e_cj, Prod.fst_sub, Prod.swap_prod_mk, Prod.fst_mul,
    Prod.fst_swap, Prod.algebraMap_apply] at h
  rw [h]
  rfl

end ModeG

end Formalism.L2.SG.Pf.FibQ
end
end

