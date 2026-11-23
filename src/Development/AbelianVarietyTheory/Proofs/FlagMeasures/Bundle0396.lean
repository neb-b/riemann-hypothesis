module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem vecOf_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X c = ∑ i, c i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_symm_apply]
  rw [← (ci X).sum_comp]
  simp

theorem crdH_vecOf (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : crdH X (vecOf X c) = c := by
  funext i
  simp only [crdH, vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, LinearEquiv.funCongrLeft_apply]
  simp

theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  conv_rhs => rw [← X.bas.equivFun.symm_apply_apply y]
  congr 1

variable {X} in
theorem n_vecOf {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E}
    (hγ : ∀ y, crdH X (n y) = γ *ᵥ crdH X y) (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    n (vecOf X c) = vecOf X (γ *ᵥ c) := by
  conv_lhs => rw [← vecOf_crdH X (n (vecOf X c)), hγ, crdH_vecOf]

theorem crdH_eq_crd (y : (VS D).V) (i : Fin (2 * D.R.rS + D.R.k + 1)) :
    crdH X y i = X.ιE (X.crd y (ci X i)) := by
  simp [crdH, HidaSetting.crd, crdOf]

theorem sig_apply (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hT_vecOf (a b : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    (VS D).hT (vecOf X a) (vecOf X b) = GlobalTheory.SgAlg.form (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) b a := by
  rw [vecOf_apply, vecOf_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, sig_apply, Jc, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem Jc_det_ne_zero : (Jc X).det ≠ 0 := by
  have h : Jc X = (X.B.I.J.map X.ιE).submatrix (ci X) (ci X) := by
    ext i j
    simp [Jc, X.J_eq]
  rw [h, Matrix.det_submatrix_equiv_self]
  intro h0
  apply X.B.I.J_det
  apply X.ιE.injective
  rw [map_zero]
  exact (RingHom.map_det X.ιE.toRingHom X.B.I.J).trans h0

def coordEquiv : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[D.host.E] (VS D).V :=
  (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).trans X.bas.equivFun.symm

theorem coordEquiv_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : coordEquiv X c = vecOf X c := rfl

theorem coordEquiv_symm_apply (y : (VS D).V) : (coordEquiv X).symm y = crdH X y := by
  apply (coordEquiv X).injective
  rw [LinearEquiv.apply_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_mat (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  refine ⟨LinearMap.toMatrix' (((coordEquiv X).symm.toLinearMap ∘ₗ n.toLinearMap) ∘ₗ (coordEquiv X).toLinearMap), fun y => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp [coordEquiv_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_equiv (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E) (hU : GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ) :
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  have hdet : IsUnit γ.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply Jc_det_ne_zero X
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have h1 : γ⁻¹ * γ = 1 := Matrix.nonsing_inv_mul γ hdet
  have h2 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hdet
  refine ⟨(coordEquiv X).symm.trans ((Matrix.toLin'OfInv h1 h2).trans (coordEquiv X)), fun y => ?_⟩
  simp only [LinearEquiv.trans_apply, coordEquiv_symm_apply, coordEquiv_apply, Matrix.toLin'OfInv_apply,
    Matrix.toLin'_apply, crdH_vecOf]
  rfl

end GlobalTheory.CovDomGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddIsotropicSpanMemLocallyStandardLattice
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.IsotropicLift

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def kerR (H : HermSp M V) (w : V) : Submodule E V where
  carrier := {v | H.h v w = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_add_left, ha, hb, add_zero]
  zero_mem' := H.h_zero_left w
  smul_mem' c v hv := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_smul_left, hv, mul_zero]

theorem h_swap_zero (H : HermSp M V) {x y : V} (h : H.h x y = 0) : H.h y x = 0 := by
  rw [H.h_herm, h]; simp

theorem X_le_perp (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  intro x hx
  have hk : H.X Fr.f ≤ kerR H (Fr.f b.castSucc) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Fr.h_iso a.castSucc b.castSucc (Or.inl (Fin.castSucc_ne_last a))
  exact h_swap_zero H (hk hx)

theorem sub_mem_X_of_mem_N (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    {v : V} (hv : v ∈ H.perp (H.X Fr.f)) : n v - v ∈ H.X Fr.f := by
  have hXP := X_le_perp H Fr
  suffices key : ∀ g ∈ Fr.N, ∀ v ∈ H.perp (H.X Fr.f), g v - v ∈ H.X Fr.f ∧ g.symm v - v ∈ H.X Fr.f from
    (key n hn v hv).1
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨hu, -, hperp⟩ := hg
    intro v hv
    refine ⟨hperp v hv, ?_⟩
    have hw : g.symm v ∈ H.perp (H.X Fr.f) := by
      intro x hx
      have hgx : g x ∈ H.X Fr.f := by
        have := hperp x (hXP hx)
        have e : g x = (g x - x) + x := by abel
        rw [e]; exact Submodule.add_mem _ this hx
      rw [← hu (g.symm v) x, LinearEquiv.apply_symm_apply]
      exact hv _ hgx
    have h1 := hperp _ hw
    rw [LinearEquiv.apply_symm_apply] at h1
    have e : g.symm v - v = -(v - g.symm v) := by abel
    rw [e]; exact Submodule.neg_mem _ h1
  | one =>
    intro v _
    exact ⟨by simp, by show v - v ∈ _; simp⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    intro v hv
    have hm : ∀ x, (g₁ * g₂) x = g₁ (g₂ x) := fun _ => rfl
    have hms : ∀ x, (g₁ * g₂).symm x = g₂.symm (g₁.symm x) := fun _ => rfl
    obtain ⟨a2, b2⟩ := ih₂ v hv
    obtain ⟨a1, b1⟩ := ih₁ v hv
    have hv2 : g₂ v ∈ H.perp (H.X Fr.f) := by
      have e : g₂ v = (g₂ v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP a2) hv
    have hv1 : g₁.symm v ∈ H.perp (H.X Fr.f) := by
      have e : g₁.symm v = (g₁.symm v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP b1) hv
    refine ⟨?_, ?_⟩
    · rw [hm]
      have e : g₁ (g₂ v) - v = (g₁ (g₂ v) - g₂ v) + (g₂ v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₁ _ hv2).1 a2
    · rw [hms]
      have e : g₂.symm (g₁.symm v) - v = (g₂.symm (g₁.symm v) - g₁.symm v) + (g₁.symm v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₂ _ hv1).2 b1
  | inv g _ ih =>
    intro v hv
    exact ⟨(ih v hv).2, (ih v hv).1⟩

theorem z_mem_LamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)}
    (hL : Fr.IsInner L) : Fr.z ∈ Fr.LamStd L := by
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  have hs : ∀ a, H.h Fr.z (Fr.es a) = 0 := fun a => h_swap_zero H (Fr.h_sz a)
  have he : ∀ a, H.h Fr.z (Fr.e a) = 0 := fun a =>
    Fr.h_iso (Fin.last r) a.castSucc (Or.inr (Fin.castSucc_ne_last a))
  refine Submodule.subset_span ⟨fun a => ?_, fun a => ?_, xz, ?_, hxzL⟩
  · rw [hs a]; exact zero_mem _
  · rw [he a]; exact zero_mem _
  · rw [hxz]
    simp [FrameD.prF, hs, he]

end Gen

variable {D : D7}

theorem exists_add_mem : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D)
    (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS),
    (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D,
    Submodule.IsLattice D.host.E Λ →
    (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) →
    ∃ x ∈ G.fl.X, G.fl.z + x ∈ Λ := by
  intro D T G Z A hA Λ hΛ hloc
  obtain ⟨π, hπX, hπmem⟩ : ∃ π : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ G.fl.X, π x = x) ∧ ∀ x, π x ∈ G.fl.X := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective G.fl.X.subtype (Submodule.ker_subtype _)
    refine ⟨G.fl.X.subtype ∘ₗ g, fun x hx => ?_, fun x => (g x).2⟩
    have := congrArg (fun f => ((f ⟨x, hx⟩ : G.fl.X) : (VS D).V)) hg
    exact this
  obtain ⟨Λ₁, hΛ₁⟩ : ∃ N : LV D, N = Λ ⊔ Submodule.span (𝓞 D.host.E) {G.fl.z} := ⟨_, rfl⟩
  obtain ⟨Λ₂, hΛ₂⟩ : ∃ N : LV D, N = Λ ⊔ Λ₁.map (π.restrictScalars (𝓞 D.host.E)) := ⟨_, rfl⟩
  have hfg : Λ₂.FG := by
    rw [hΛ₂, hΛ₁]; exact hΛ.fg.sup ((hΛ.fg.sup (Submodule.fg_span_singleton _)).map _)
  have hz : G.fl.z ∈ Λ₂ := by
    refine GlobalTheory.GenMass.GlueLoc.mem_of_bcP Z hfg fun p => ?_
    obtain ⟨n, hn, L, hL, hlat⟩ := hloc p
    have hzp : (A p).z = baseChange₂ D p G.fl.z := by
      show (A p).f (Fin.last _) = _
      rw [hA p]
      simp [frFac, frame, FlagG.fvec]
    have hperp : (A p).z ∈ (locH Z p).perp ((locH Z p).X (A p).f) := by
      obtain ⟨-, -, xz, hxz, -, -⟩ := hL
      rw [← hxz]; exact xz.2
    have hnz : n (A p).z ∈ lattice₂ D Z.M p Λ := by
      rw [hlat]
      exact Submodule.mem_map_of_mem (z_mem_LamStd _ (A p) hL)
    have hxX := sub_mem_X_of_mem_N _ (A p) hn hperp
    have hfix : (locH Z p).X (A p).f ≤ LinearMap.eqLocus (GlobalTheory.LocExt.locEnd p π) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      show (GlobalTheory.LocExt.locEnd p π) ((A p).f a.castSucc) = (A p).f a.castSucc
      rw [hA p]
      rw [map_smul, GlobalTheory.LocExt.locEnd_bcP, GlobalTheory.LocExt.frame_castSucc,
        hπX _ (Submodule.subset_span ⟨a, rfl⟩)]
      show _ = frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)
      rw [GlobalTheory.LocExt.frame_castSucc]
    have hx1 : n (A p).z - (A p).z ∈ lattice₂ D Z.M p Λ₁ := by
      rw [hΛ₁]
      refine Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz) ?_
      rw [hzp]
      exact Submodule.subset_span ⟨G.fl.z, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), rfl⟩
    have hx2 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) ∈ lattice₂ D Z.M p (Λ₁.map (π.restrictScalars (𝓞 D.host.E))) := by
      rw [GlobalTheory.FrameProj.localLattice_map Z p π (GlobalTheory.LocExt.locEnd p π) (fun x => (GlobalTheory.LocExt.locEnd_bcP p π x).symm) Λ₁]
      exact Submodule.mem_map_of_mem hx1
    have hx3 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) = n (A p).z - (A p).z := hfix hxX
    rw [hx3] at hx2
    have e : baseChange₂ D p G.fl.z = n (A p).z - (n (A p).z - (A p).z) := by rw [hzp]; abel
    rw [e, hΛ₂]
    exact Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz)
      (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_right hx2)
  rw [hΛ₂] at hz
  obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.1 hz
  obtain ⟨w, -, rfl⟩ := hy
  refine ⟨-(π w), Submodule.neg_mem _ (hπmem w), ?_⟩
  have e : G.fl.z + -(π w) = l := by
    rw [← hly]; simp
  rw [e]; exact hl

end GlobalTheory.IsotropicLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapHypothesisOfLargenessConstantGe
section
noncomputable section
namespace GlobalTheory.TypeAsm
open Formalism.BasicNotions

theorem gap_hypothesis_of_kernel_bound_large_constant {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ} (hCl : 1801 ≤ Cl)
    (h : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  obtain ⟨⟨hS, -, -⟩, -⟩ := h
  obtain ⟨-, -, hmf, hfk, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, -, -, hClm, -⟩ := hS
  have hL : 1 < large₂.sc.L := Formalism.MainNotions.S.one_lt_scL large₂
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hf16 : 16 ≤ D.R.f := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4) hmf
  have hf : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hmn : D.R.m ≤ D.R.r := by
    have h1 : 1 ≤ D.R.k := by omega
    show D.R.m ≤ D.R.k + D.R.m - 1
    omega
  have hmR : (1801 : ℝ) ≤ D.R.m := le_trans hCl hClm
  have hm1801 : 1801 ≤ D.R.m := by exact_mod_cast hmR
  refine ⟨le_trans hm1801 hmn, fun τ j hj => ?_⟩
  have g := hgap τ (j.1 + 1) (by omega) (by omega)
  rw [Formalism.MainNotions.S.bOne_succ τ (j.1 + 1) hj, Formalism.MainNotions.S.bOne_succ τ j.1 j.2] at g
  have hn0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  have h16 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have a1 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := by nlinarith
    have a2 : Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      le_mul_of_one_le_right (by positivity) (by nlinarith)
    linarith [show Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L by ring]
  have hR : ((16 * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤ (((D.hc τ).b ⟨j.1 + 1, hj⟩ - (D.hc τ).b j : ℚ) : ℝ) := by
    push_cast
    have e : ((D.hc τ).b ⟨j.1, j.2⟩ : ℝ) = ((D.hc τ).b j : ℝ) := rfl
    linarith
  exact_mod_cast hR

theorem gapC : GapC :=
  ⟨1801, fun _ _ _ _ _ _ _ _ _ _ hCl h => gap_hypothesis_of_kernel_bound_large_constant hCl h⟩

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletionsStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_unimodular_lattice_iff_local_completions : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) → ∀ Λ : LV D, Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ Submodule.IsLattice D.host.E Λ ∧ ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ) ∧ (∀ i, (locH Z p).MMfam (tm FP G G' p (lattice₂ D Z.M p Λ)) i ∈ lattice₂ D Z.M p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p (lattice₂ D Z.M p Λ)) := by
  first | exact @GlobalTheory.GenMass.GlueLoc.glue_iff_local | exact GlobalTheory.GenMass.GlueLoc.glue_iff_local | (intros; apply GlobalTheory.GenMass.GlueLoc.glue_iff_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLoUniMul
section
universe u_1

namespace GlobalTheory.LowerUnipotentMul

open Matrix

theorem isLoUni_mul {R : Type*} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (hl : Formalism.MainNotions.S.IsLoUni l) (hl' : Formalism.MainNotions.S.IsLoUni l') : Formalism.MainNotions.S.IsLoUni (l * l') := by
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hik | hki
    · rw [(hl i k).1 hik, zero_mul]
    · rw [(hl' k j).1 (lt_of_le_of_lt hki hij), mul_zero]
  · intro hij
    subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hl i i).2 rfl, (hl' i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hl' k i).1 h, mul_zero]
      · rw [(hl i k).1 h, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem main : ∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R},
    Formalism.MainNotions.S.IsLoUni l → Formalism.MainNotions.S.IsLoUni l' → Formalism.MainNotions.S.IsLoUni (l * l') :=
  fun hl hl' => isLoUni_mul hl hl'

end GlobalTheory.LowerUnipotentMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRootsPointMatrixIffSameBlock
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootsBijection

open Formalism.L2.SG.RealObj in
theorem fwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (i j a b : ℕ), Formalism.MainNotions.S.ptEntry bs i a ≠ 0 →
    Formalism.MainNotions.S.ptEntry bs j b ≠ 0 → a < b → j < i → blkOf bs a = blkOf bs b
  | [], _, _, _, _, h, _, _, _ => by simp [Formalism.MainNotions.S.ptEntry] at h
  | (t, s) :: bs, i, j, a, b, h1, h2, hab, hji => by
    rw [Formalism.MainNotions.S.ptEntry] at h1 h2
    by_cases ha : a < s
    · by_cases hb : b < s
      · simp [blkOf, ha, hb]
      · exfalso
        rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
        by_cases hj : s ≤ j
        · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1
          by_cases hi : i < s
          · omega
          · rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1; exact h1 rfl
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact h2 rfl
    · have hb : ¬ b < s := by omega
      rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1
      rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
      by_cases hi : s ≤ i
      · by_cases hj : s ≤ j
        · rw [if_pos ⟨hi, by omega⟩] at h1
          rw [if_pos ⟨hj, by omega⟩] at h2
          have := fwd bs (i - s) (j - s) (a - s) (b - s) h1 h2 (by omega) (by omega)
          simp [blkOf, ha, hb, this]
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact absurd rfl h2
      · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1; exact absurd rfl h1

open Formalism.L2.SG.RealObj in
theorem bwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ p ∈ bs, p.1 ≠ 0) → ∀ (a b : ℕ), a < b →
    b < (bs.map Prod.snd).sum → blkOf bs a = blkOf bs b →
    ∃ i j, j < i ∧ i < (bs.map Prod.snd).sum ∧ Formalism.MainNotions.S.ptEntry bs i a ≠ 0 ∧ Formalism.MainNotions.S.ptEntry bs j b ≠ 0
  | [], _, _, _, _, hb, _ => by simp at hb
  | (t, s) :: bs, hnz, a, b, hab, hbs, hbl => by
    have ht : t ≠ 0 := hnz (t, s) (by simp)
    simp only [List.map_cons, List.sum_cons] at hbs ⊢
    by_cases ha : a < s
    · have hb : b < s := by
        by_contra hb
        simp [blkOf, ha, hb] at hbl
      refine ⟨s - 1 - a, s - 1 - b, by omega, by omega, ?_, ?_⟩
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, ha⟩, if_pos (by omega)]; exact ht
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, hb⟩, if_pos (by omega)]; exact ht
    · have hb : ¬ b < s := by omega
      have hbl' : blkOf bs (a - s) = blkOf bs (b - s) := by
        simpa [blkOf, ha, hb] using hbl
      have htail :
          ∃ i j, j < i ∧ i < (bs.map Prod.snd).sum ∧
            Formalism.MainNotions.S.ptEntry bs i (a - s) ≠ 0 ∧
            Formalism.MainNotions.S.ptEntry bs j (b - s) ≠ 0 :=
        bwd bs (fun p hp => hnz p (List.mem_cons_of_mem _ hp)) (a - s) (b - s)
          (by omega) (by omega) hbl'
      rcases htail with ⟨i, j, hji, his, hi, hj⟩
      refine ⟨i + s, j + s, Nat.add_lt_add_right hji s, by omega, ?_, ?_⟩
      · simpa [Formalism.MainNotions.S.ptEntry, ha, Nat.le_of_not_gt ha] using hi
      · simpa [Formalism.MainNotions.S.ptEntry, hb, Nat.le_of_not_gt hb] using hj

end GlobalTheory.RootsBijection

theorem GlobalTheory.roots_ptMat_iff : ∀ (K : Type) [Field K] (n : ℕ) (w : Point K n) (a b : Fin n),
    (a, b) ∈ GlobalTheory.LoopV.roots (ptMat w) ↔ a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1 := by
  intro K _ n w a b
  unfold GlobalTheory.LoopV.roots
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [ptMat]
  constructor
  · rintro ⟨hab, i, j, hji, hi, hj⟩
    exact ⟨hab, GlobalTheory.RootsBijection.fwd w.1 i.1 j.1 a.1 b.1 hi hj hab hji⟩
  · rintro ⟨hab, hbl⟩
    obtain ⟨i, j, hji, hin, hi, hj⟩ := GlobalTheory.RootsBijection.bwd w.1 (fun p hp => (w.2.1 p hp).1) a.1 b.1 hab
      (by rw [w.2.2]; exact b.2) hbl
    rw [w.2.2] at hin
    exact ⟨hab, ⟨i, hin⟩, ⟨j, by omega⟩, hji, hi, hj⟩
end

