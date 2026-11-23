module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0032

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FinrankSpanLb
section
noncomputable section

open NumberField Formalism.BasicNotions
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def Wb : Submodule D.host.E (VS D).V :=
  ⨅ c, LinearMap.ker ((VS D).hT (X.eX c)) ⊓ LinearMap.ker ((VS D).hT (X.fY c))

theorem mem_Wb {y : (VS D).V} : y ∈ Wb X ↔ ∀ c, (VS D).hT (X.eX c) y = 0 ∧ (VS D).hT (X.fY c) y = 0 := by
  simp [Wb, Submodule.mem_iInf, LinearMap.mem_ker]

def phi : (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E) :=
  LinearMap.prod (LinearMap.pi fun c => (VS D).hT (X.eX c)) (LinearMap.pi fun c => (VS D).hT (X.fY c))

theorem phi_apply (y : (VS D).V) :
    phi X y = (fun c => (VS D).hT (X.eX c) y, fun c => (VS D).hT (X.fY c) y) := rfl

theorem ker_phi : LinearMap.ker (phi X) = Wb X := by
  ext y
  rw [LinearMap.mem_ker, mem_Wb, phi_apply]
  constructor
  · intro h c
    exact ⟨congrFun (congrArg Prod.fst h) c, congrFun (congrArg Prod.snd h) c⟩
  · intro h
    refine Prod.ext (funext fun c => (h c).1) (funext fun c => (h c).2)

theorem range_phi : LinearMap.range (phi X) = ⊤ := by
  rw [LinearMap.range_eq_top]
  rintro ⟨p, q⟩
  refine ⟨∑ a, p a • X.fY a + ∑ a, q a • X.eX a, ?_⟩
  rw [phi_apply]
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [map_sum, map_smul, X.ef, X.ee, Finset.sum_ite_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [map_sum, map_smul, X.ff, Ex.h_fe, Finset.sum_ite_eq]

theorem finrank_V (X : HidaSetting D) : Module.finrank D.host.E (VS D).V = 2 * D.R.rS + D.R.k + 1 := by
  rw [Module.finrank_eq_card_basis X.bas, Fintype.card_fin, nX X]

theorem finrank_Wb : Module.finrank D.host.E (Wb X) = D.R.k + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (phi X)
  rw [range_phi, ker_phi, finrank_top, Module.finrank_prod, Module.finrank_fin_fun, finrank_V X] at h
  omega

theorem span_Lb_le : Submodule.span D.host.E (X.Lb : Set (VS D).V) ≤ Wb X := by
  rw [Submodule.span_le]
  intro x hx
  exact (mem_Wb X).2 fun c => X.Lb_perp x hx c

theorem span_Lb : Submodule.span D.host.E (X.Lb : Set (VS D).V) = Wb X := by
  refine le_antisymm (span_Lb_le X) fun y hy => ?_
  have hy' := (mem_Wb X).1 hy
  have htop : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    let x : Fin X.B.I.n → X.B.I.E := fun i => X.ιE.symm (X.bas.repr y i)
    have hx : x ∈ Submodule.span X.B.I.E (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
      rw [X.B.I.L_span]; trivial
    have hm : ∀ x ∈ Submodule.span X.B.I.E (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)),
        (∑ i, X.ιE (x i) • X.bas i) ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ((X.L_eq x).1 hx)
      | zero => simp
      | add x y hx hy ihx ihy => simpa [map_add, add_smul, Finset.sum_add_distrib] using Submodule.add_mem _ ihx ihy
      | smul a x hx ih => simpa [map_mul, mul_smul, Finset.smul_sum] using Submodule.smul_mem _ (X.ιE a) ih
    have := hm x hx
    simpa only [x, RingEquiv.apply_symm_apply, X.bas.sum_repr] using this
  have hyL : y ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) := by rw [htop]; trivial
  have hle : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) ≤
      Submodule.span D.host.E (Set.range X.eX) ⊔ Submodule.span D.host.E (X.Lb : Set (VS D).V) ⊔
        Submodule.span D.host.E (Set.range X.fY) := by
    rw [Submodule.span_le]
    intro z hz
    set T := Submodule.span D.host.E (Set.range X.eX) ⊔ Submodule.span D.host.E (X.Lb : Set (VS D).V) ⊔
        Submodule.span D.host.E (Set.range X.fY) with hT
    have hL : (VS D).L0 ≤ T.restrictScalars (𝓞 D.host.E) := by
      rw [X.Lam_split]
      refine sup_le (sup_le ?_ ?_) ?_
      · unfold latSpanS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)))
      · intro l hl
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span hl))
      · unfold latSpanS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact Submodule.mem_sup_right (Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩))
    exact hL hz
  obtain ⟨y12, hy12, y3, hy3, rfl⟩ := Submodule.mem_sup.1 (hle hyL)
  obtain ⟨y1, hy1, l, hl, rfl⟩ := Submodule.mem_sup.1 hy12
  obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy1
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy3
  have hlW : ∀ c, (VS D).hT (X.eX c) l = 0 ∧ (VS D).hT (X.fY c) l = 0 := (mem_Wb X).1 (span_Lb_le X hl)
  have hα : ∀ c, α c = 0 := by
    intro c
    have := (hy' c).2
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_add (f := _), map_sum, map_smul, Ex.h_fe, X.ff, (hlW c).2, Finset.sum_ite_eq] at this
    exact this
  have hβ : ∀ c, β c = 0 := by
    intro c
    have := (hy' c).1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_add (f := _), map_sum, map_smul, X.ef, X.ee, (hlW c).1, Finset.sum_ite_eq] at this
    exact this
  simp only [hα, hβ, zero_smul, Finset.sum_const_zero, zero_add, add_zero]
  exact hl

theorem finrank_span_Lb : Module.finrank D.host.E (Submodule.span D.host.E (X.Lb : Set (VS D).V)) = D.R.k + 1 := by
  rw [span_Lb, finrank_Wb]

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsHolds
section
namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_holds : GlueExists :=
  glueExists_of_last last_unit_holds

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingProductHolds
section
namespace Formalism.L2.SG.Pf.Cnt

theorem gluing_product_holds : GlueProd :=
  glueProd_of jordan_splitting_exists jordan_invariants_holds jordan_isometry_holds local_gluing_holds

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemClosureImage
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Onto

theorem mem_closure_image {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (H : AddSubgroup A)
    (y : B) : y ∈ AddSubgroup.closure (f '' (H : Set A)) ↔ ∃ t ∈ H, f t = y := by
  rw [← AddSubgroup.coe_map, AddSubgroup.closure_eq, AddSubgroup.mem_map]

variable {D : D7} (X : HidaSetting D)

def embHom : D.host.E →+ (InfinitePlace X.B.I.F → ℂ) where
  toFun := embV X
  map_zero' := by funext v; simp [embV]
  map_add' x y := by funext v; simp [embV]

theorem mem_cl_emb (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (y : InfinitePlace X.B.I.F → ℂ) :
    y ∈ AddSubgroup.closure (embV X '' (I : Set D.host.E)) ↔ ∃ t ∈ I, embV X t = y := by
  have := mem_closure_image (embHom X) ((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) y
  exact this

theorem theta_spec (D : D7) : IsIntegral ℤ (theta D) ∧ theta D + D.host.conj (theta D) = 1 := by
  have h := thetaEx_holds D
  unfold theta
  rw [dite_eq_left h]
  exact h.choose_spec

end Onto

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PWOfInW
section
noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

def Ym : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := (X0⁻¹)ᴴ

def om (a : Fin D.R.rS) : (VS D).V := -∑ b, Ym X0 b a • xs b

def nE (a : Fin D.R.rS) : (VS D).V := ∑ b, X0 b a • X.eX b

def nF (a : Fin D.R.rS) : (VS D).V := ∑ c, Ym X0 c a • X.fY c + om X0 xs a + ∑ b, (X0 * M) b a • X.eX b

def nWL : (VS D).V →ₗ[D.host.E] (VS D).V := LinearMap.id + ∑ b, ((VS D).hT (xs b)).smulRight (X.eX b)

def pWL : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ c, ((VS D).hT (X.fY c)).smulRight (X.eX c) - ∑ c, ((VS D).hT (X.eX c)).smulRight (X.fY c)

theorem pWL_apply (y : (VS D).V) : pWL X y = pW X y := by
  simp [pWL, pW, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

def nL : (VS D).V →ₗ[D.host.E] (VS D).V :=
  ∑ c, ((VS D).hT (X.fY c)).smulRight (nE X X0 c) + ∑ c, ((VS D).hT (X.eX c)).smulRight (nF X X0 xs M c) +
    (nWL X xs).comp (pWL X)

theorem nL_apply (y : (VS D).V) : nL X X0 xs M y =
    ∑ c, (VS D).hT (X.fY c) y • nE X X0 c + ∑ c, (VS D).hT (X.eX c) y • nF X X0 xs M c +
      (pW X y + ∑ b, (VS D).hT (xs b) (pW X y) • X.eX b) := by
  simp [nL, nWL, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply, pWL_apply]

theorem pW_of_inW {w : (VS D).V} (hw : InW X w) : pW X w = w := by
  unfold pW
  simp [(hw _).1, (hw _).2]

theorem pW_e (a : Fin D.R.rS) : pW X (X.eX a) = 0 := by
  unfold pW
  simp [h_fe, X.ee, Finset.sum_ite_eq']

theorem pW_f (a : Fin D.R.rS) : pW X (X.fY a) = 0 := by
  unfold pW
  simp [X.ef, X.ff, Finset.sum_ite_eq']

theorem nL_e (a : Fin D.R.rS) : nL X X0 xs M (X.eX a) = nE X X0 a := by
  rw [nL_apply, pW_e]
  simp [h_fe, X.ee, Finset.sum_ite_eq']

theorem nL_f (a : Fin D.R.rS) : nL X X0 xs M (X.fY a) = nF X X0 xs M a := by
  rw [nL_apply, pW_f]
  simp [X.ef, X.ff, Finset.sum_ite_eq']

theorem nL_w {w : (VS D).V} (hw : InW X w) : nL X X0 xs M w = w + ∑ b, (VS D).hT (xs b) w • X.eX b := by
  rw [nL_apply, pW_of_inW X hw]
  simp [(hw _).1, (hw _).2]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowVGram
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev pV (v : InfinitePlace X.B.I.F) (p : (VS D).V) : Fin X.B.I.n → ℂ := rv X.B.I v (X.crd p)

theorem hJ_pV (v : InfinitePlace X.B.I.F) (p q : (VS D).V) :
    hJ (X.B.I.ε v) (pV X v p) (pV X v q) = embS D (X.pl v) ((VS D).hT p q) :=
  PI.SchurPlaces.hJ_psiV X v p q

theorem decompY (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → ℂ)
    (hye : ∀ a, hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.eV X v a) y = 0)
    (hyf : ∀ a, hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.fV X v a) y = 0) :
    y = ∑ c, hJ (X.B.I.ε v) (X.wfr u v c) y • X.wfr u v c +
      (-(hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) y) / ((((D.mem u).A.T : ℕ) : ℝ) : ℂ)) •
        Formalism.L2.SG.Pf.LsNc5.zV X u v := by
  have hy : y ∈ Submodule.span ℂ (Set.range (Formalism.L2.SG.Pf.LsNc5.fam X u v)) := by
    rw [Formalism.L2.SG.Pf.LsNc5.fam_span]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
  subst hc

  have pair : ∀ t : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) t (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      (∑ a, c (Sum.inl a) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.eV X v a)) +
        ((∑ a, c (Sum.inr (Sum.inl a)) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.fV X v a)) +
        ((∑ j, c (Sum.inr (Sum.inr (Sum.inl j))) * hJ (X.B.I.ε v) t (X.wfr u v j)) +
          c (Sum.inr (Sum.inr (Sum.inr ()))) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.zV X u v))) := by
    intro t
    rw [PI.SchurPlaces.hJ_sum_r]
    simp only [Fintype.sum_sum_type, Formalism.L2.SG.Pf.LsNc5.fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  have hcf : ∀ a, c (Sum.inr (Sum.inl a)) = 0 := by
    intro a
    have h := hye a
    rw [pair] at h
    simpa [Formalism.L2.SG.Pf.LsNc5.fr_ee, Formalism.L2.SG.Pf.LsNc5.fr_ef, Formalism.L2.SG.Pf.LsNc5.fr_ew,
      Formalism.L2.SG.Pf.LsNc5.fr_ez] using h
  have hce : ∀ a, c (Sum.inl a) = 0 := by
    intro a
    have h := hyf a
    rw [pair] at h
    simpa [Formalism.L2.SG.Pf.LsNc5.fr_fe, Formalism.L2.SG.Pf.LsNc5.fr_ff, Formalism.L2.SG.Pf.LsNc5.fr_fw,
      Formalism.L2.SG.Pf.LsNc5.fr_fz, hcf] using h
  have hw : ∀ j, hJ (X.B.I.ε v) (X.wfr u v j) (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      c (Sum.inr (Sum.inr (Sum.inl j))) := by
    intro j
    rw [pair]
    simp [Formalism.L2.SG.Pf.LsNc5.fr_we, Formalism.L2.SG.Pf.LsNc5.fr_wf, Formalism.L2.SG.Pf.LsNc5.fr_ww,
      Formalism.L2.SG.Pf.LsNc5.fr_wz]
  have hz : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      c (Sum.inr (Sum.inr (Sum.inr ()))) * -((((D.mem u).A.T : ℕ) : ℂ)) := by
    rw [pair]
    simp [Formalism.L2.SG.Pf.LsNc5.fr_ze, Formalism.L2.SG.Pf.LsNc5.fr_zf, Formalism.L2.SG.Pf.LsNc5.fr_zw,
      Formalism.L2.SG.Pf.LsNc5.frame_z_z_eq_neg_t]
  simp only [hw, hz]
  have hT := Formalism.L2.SG.Pf.LsNc5.T_ne u
  have hcoef : -(c (Sum.inr (Sum.inr (Sum.inr ()))) * -((((D.mem u).A.T : ℕ) : ℂ))) /
      ((((D.mem u).A.T : ℕ) : ℝ) : ℂ) = c (Sum.inr (Sum.inr (Sum.inr ()))) := by
    push_cast; field_simp
  rw [hcoef]
  simp only [Fintype.sum_sum_type, Formalism.L2.SG.Pf.LsNc5.fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
    hce, hcf, zero_smul, Finset.sum_const_zero, zero_add]

theorem decompW (v : InfinitePlace X.B.I.F) (x : (VS D).V) (hx : InW X x) :
    pV X v x = ∑ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v x) • X.wfr u v c +
      (-(hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v x)) / ((((D.mem u).A.T : ℕ) : ℝ) : ℂ)) •
        Formalism.L2.SG.Pf.LsNc5.zV X u v := by
  refine decompY X u v _ (fun a => ?_) (fun a => ?_)
  · show hJ (X.B.I.ε v) (pV X v (X.eX a)) (pV X v x) = 0
    rw [hJ_pV, (hx a).1, map_zero]
  · show hJ (X.B.I.ε v) (pV X v (X.fY a)) (pV X v x) = 0
    rw [hJ_pV, (hx a).2, map_zero]

theorem rowV_w (x : (VS D).V) (v : InfinitePlace X.B.I.F) (j : Fin D.R.k) :
    rowV X u x v (Fin.castSucc j) = hJ (X.B.I.ε v) (pV X v x) (X.wfr u v j) := by
  simp [rowV]

theorem rowV_last_eq_hJ (x : (VS D).V) (v : InfinitePlace X.B.I.F) :
    rowV X u x v (Fin.last D.R.k) = hJ (X.B.I.ε v) (pV X v x) (Formalism.L2.SG.Pf.LsNc5.zV X u v) := by
  simp [rowV]
  rfl

theorem rowV_gram (v : InfinitePlace X.B.I.F) (x y : (VS D).V) (hy : InW X y) :
    embS D (X.pl v) ((VS D).hT x y) =
      (∑ j : Fin D.R.k, rowV X u x v (Fin.castSucc j) * star (rowV X u y v (Fin.castSucc j))) -
        rowV X u x v (Fin.last D.R.k) * star (rowV X u y v (Fin.last D.R.k)) / (((D.mem u).A.T : ℕ) : ℂ) := by
  rw [← hJ_pV, decompW X u v y hy, PI.SchurPlaces.hJ_add_r, PI.SchurPlaces.hJ_sum_r, PI.SchurPlaces.hJ_smul_r]
  simp only [rowV_w, rowV_last_eq_hJ]
  have e1 : ∀ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v y) = star (hJ (X.B.I.ε v) (pV X v y) (X.wfr u v c)) :=
    fun c => hJ_conj' _ _ _
  have e2 : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v y) =
      star (hJ (X.B.I.ε v) (pV X v y) (Formalism.L2.SG.Pf.LsNc5.zV X u v)) := hJ_conj' _ _ _
  simp only [e1, e2]
  push_cast
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun c _ => by ring
  · ring

theorem rowV_inj (x : (VS D).V) (hx : InW X x) (h : rowV X u x = 0) : x = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hp : pV X v x = 0 := by
    rw [decompW X u v x hx]
    have h1 : ∀ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v x) = 0 := by
      intro c
      rw [hJ_conj', ← rowV_w, h]; simp
    have h2 : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v x) = 0 := by
      rw [hJ_conj', ← rowV_last_eq_hJ, h]; simp
    simp [h1, h2]
  refine (VS D).nondeg.1 x fun y => ?_
  apply (embS D (X.pl v)).injective
  rw [← hJ_pV, hp, map_zero]
  unfold hJ; simp

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

