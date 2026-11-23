module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0105
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolKey

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApprox
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem approxC : ProdE.ApproxC M δ u u' F0 what₂ := by
  intro γ w F' L U hE
  obtain ⟨S, hSAC, hSint⟩ := good_places M δ u u' w hE.1 L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
  exact ⟨S, hSAC, fun p => finIdx_at M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1,
    fun h => approx_core M δ u u' w hE.1 L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1 S hSint h⟩

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SecondValueMul
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

theorem first_value_mul (x y : UP p) : (((x * y : UP p) : GG p).1 : GLp p).val =
    (((x : GG p).1 : GLp p).val) * (((y : GG p).1 : GLp p).val) := rfl

theorem second_value_mul (x y : UP p) : ((((x * y : UP p) : GG p).2.unop : GLp p)).val =
    ((((y : GG p).2.unop : GLp p)).val) * ((((x : GG p).2.unop : GLp p)).val) := rfl

def fC : Quotient (CountAb.cellRel (a.mat) πa.ker (KU M p) g) → Quotient (Formalism.L2.SG.Pf.Coef.cellSetoid (M p) a) :=
  Quotient.lift (fun x => Quotient.mk _ (pairOfU a πa hker x.1 (MonoidHom.mem_ker.1 x.2.1))) (by
    intro x y hxy
    apply Quotient.sound
    have hk : (y : UP p) * (x : UP p)⁻¹ ∈ KU M p := hxy.1
    have hy : (y : UP p) = ((y : UP p) * (x : UP p)⁻¹) * (x : UP p) := by group
    refine ⟨⟨((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).1 : GLp p).val, hk.1, ?_⟩,
      ⟨((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p).val, hk.2, ?_⟩⟩
    · show (((y : UP p) : GG p).1 : GLp p).val = _
      conv_lhs => rw [hy]
      rw [first_value_mul]
      rfl
    · show ((((y : UP p) : GG p).2.unop : GLp p)).val = _
      conv_lhs => rw [hy]
      rw [second_value_mul]
      rfl)

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFib
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem act_mul (f : Fin (D.R.rS + 1) → (VS D).V) (s s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A B : MatR D)
    (hs : ∀ b, s (f b) = ∑ c, A c b • f c) (hs' : ∀ b, s' (f b) = ∑ c, B c b • f c) (b : Fin (D.R.rS + 1)) :
    (s * s') (f b) = ∑ c, (A * B) c b • f c := by
  show s (s' (f b)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs', map_sum]
  simp only [map_smul, hs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem act_inv' (f : Fin (D.R.rS + 1) → (VS D).V) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A : MatR D)
    (hA : IsUpUni A) (hs : ∀ b, s (f b) = ∑ c, A c b • f c) (b : Fin (D.R.rS + 1)) :
    s⁻¹ (f b) = ∑ c, A⁻¹ c b • f c := by
  apply s.injective
  show s (s.symm (f b)) = _
  rw [LinearEquiv.apply_symm_apply, Formalism.L2.SG.Pf.ZsVolKey.act_inv f s A (Formalism.L2.SG.Pf.ZsVolKey.up_inv_mul hA) hs b]

theorem act_one (f : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f b) = ∑ c, (1 : MatR D) c b • f c := by
  simp [Matrix.one_apply]

theorem nlam_one {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  refine ⟨(Formalism.L2.SG.Pf.isAutLam_iff Λ 1).2 ⟨fun x y => rfl, fun x => Iff.rfl⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · simp
  · simp

variable (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def stabAutG (t : Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L : MatR D)
    (hL : Formalism.MainNotions.S.IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) : Subgroup (GLR D) where
  carrier := stabAutSet D u u' F0 what₂ t F' L
  one_mem' := by
    refine ⟨1, ⟨nlam_one _ _, nlam_one _ _⟩, 1, act_one _, ?_⟩
    rw [Units.val_one, Matrix.conjTranspose_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one)]
  mul_mem' := by
    rintro x y ⟨s₁, ⟨h1F, h1F'⟩, uu₁, hu₁, hx⟩ ⟨s₂, ⟨h2F, h2F'⟩, uu₂, hu₂, hy⟩
    refine ⟨s₂ * s₁, ⟨Formalism.L2.SG.Pf.nlamPf_mul h2F h1F, Formalism.L2.SG.Pf.nlamPf_mul h2F' h1F'⟩, uu₂ * uu₁,
      act_mul _ _ _ _ _ hu₂ hu₁, ?_⟩
    have hLL : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one)
    rw [Units.val_mul, hx, hy, Matrix.conjTranspose_mul]
    calc L⁻¹ * uu₁.conjTranspose * L * (L⁻¹ * uu₂.conjTranspose * L) =
        L⁻¹ * uu₁.conjTranspose * (L * L⁻¹) * uu₂.conjTranspose * L := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hLL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨s, ⟨hF, hF'⟩, uu, hu, hx⟩

    obtain ⟨⟨⟨hiso, _⟩, hf1, hf2⟩, _⟩ := And.intro hF hF'
    obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
    have heq : uu = uu0 :=
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 hu hu0
    subst heq
    refine ⟨s⁻¹, ⟨Formalism.L2.SG.Pf.nlamPf_inv hF, Formalism.L2.SG.Pf.nlamPf_inv hF'⟩, uu⁻¹, act_inv' _ _ _ huu0 hu, ?_⟩
    have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
    have hUd : IsUnit uu.conjTranspose.det := by
      rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0)]; exact isUnit_one
    rw [Matrix.coe_units_inv, hx, Matrix.conjTranspose_nonsing_inv]
    refine Matrix.inv_eq_left_inv ?_
    calc L⁻¹ * (uu.conjTranspose)⁻¹ * L * (L⁻¹ * uu.conjTranspose * L) =
        L⁻¹ * ((uu.conjTranspose)⁻¹ * (L * L⁻¹) * uu.conjTranspose) * L := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ hLd, Matrix.mul_one, Matrix.nonsing_inv_mul _ hUd, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ hLd]

theorem mem_stabAut_iff (t : Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L : MatR D)
    (hL : Formalism.MainNotions.S.IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) (a : GLR D) :
    a ∈ stabAut D u u' F0 what₂ t F' L ↔ a ∈ stabAutSet D u u' F0 what₂ t F' L := by
  have e : stabAut D u u' F0 what₂ t F' L = stabAutG u u' F0 what₂ t F' L hL hT0 :=
    Subgroup.closure_eq (stabAutG u u' F0 what₂ t F' L hL hT0)
  rw [e]
  rfl

end Formalism.L2.SG.Pf.ZsVolFib

end
end

