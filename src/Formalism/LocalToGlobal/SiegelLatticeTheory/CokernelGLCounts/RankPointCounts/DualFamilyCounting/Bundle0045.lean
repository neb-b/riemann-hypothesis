module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BaseLatticeLe
section
noncomputable section

open NumberField Formalism.BasicNotions
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas.IntG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem base_lattice_le : X.Lb ≤ (VS D).L0 := by
  rw [X.Lam_split]
  exact le_sup_of_le_left le_sup_right

theorem Lb_le_aaLbS (b : Fin D.R.rS) : X.Lb ≤ aaLbS X b := fun l hl =>
  Submodule.subset_span ⟨1, one_mem_aaD b, l, hl, by rw [one_smul]⟩

theorem aaLbS_le_span (b : Fin D.R.rS) :
    aaLbS X b ≤ (Submodule.span D.host.E (X.Lb : Set (VS D).V)).restrictScalars (𝓞 D.host.E) := by
  unfold aaLbS
  rw [Submodule.span_le]
  rintro _ ⟨c, -, l, hl, rfl⟩
  exact Submodule.smul_mem _ c (Submodule.subset_span hl)

theorem span_aaLbS (b : Fin D.R.rS) :
    Submodule.span D.host.E (aaLbS X b : Set (VS D).V) = Submodule.span D.host.E (X.Lb : Set (VS D).V) :=
  le_antisymm (Submodule.span_le.2 (aaLbS_le_span X b)) (Submodule.span_mono (Lb_le_aaLbS X b))

theorem aaD_ne_zero' (b : Fin D.R.rS) : aaD D b ≠ 0 := by
  unfold aaD
  exact zpow_ne_zero _ ddS_ne_zero

theorem fg_aaLbS (b : Fin D.R.rS) : (aaLbS X b).FG := by
  set N : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) ^ (D.R.rS - (b : ℕ)) with hNdef
  have hN : ((N : ℕ) : D.host.E) ∈ (aaD D b)⁻¹ := mem_aaD_inv b
  have hN0 : N ≠ 0 := by
    rw [hNdef]
    refine pow_ne_zero _ ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  let f : (VS D).V →ₗ[𝓞 D.host.E] (VS D).V := (N : 𝓞 D.host.E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((N : 𝓞 D.host.E) : D.host.E) • x = ((N : 𝓞 D.host.E) : D.host.E) • y := by
      rw [algebraMap_smul, algebraMap_smul]
      exact hxy
    have h2 : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
      push_cast
      exact_mod_cast hN0
    exact smul_right_injective _ h2 h1
  have hle : (aaLbS X b).map f ≤ (VS D).L0 := by
    unfold aaLbS
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨c, hc, l, hl, rfl⟩, rfl⟩
    have hmul : ((N : ℕ) : D.host.E) * c ∈ ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Set D.host.E) := by
      have := FractionalIdeal.mul_mem_mul hN hc
      rwa [inv_mul_cancel₀ (aaD_ne_zero' b)] at this
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hmul
    have e : f (c • l) = o • l := by
      show (N : 𝓞 D.host.E) • (c • l) = o • l
      rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E), smul_smul, ← algebraMap_smul D.host.E o l, ho]
      push_cast
      rfl
    rw [e]
    exact base_lattice_le X (X.Lb.smul_mem o hl)
  haveI : IsNoetherian (𝓞 D.host.E) (VS D).L0 := isNoetherian_of_fg_of_noetherian _ (VS D).standardTuple_isLattice.fg
  have hfg : ((aaLbS X b).map f).FG := (isNoetherian_submodule.1 inferInstance) _ hle
  exact Submodule.fg_of_fg_map_injective f hf hfg

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingMassHolds
section
namespace Formalism.L2.SG.Pf.Cnt

theorem gluing_mass_holds : GlueMass :=
  glueMass_of' jordan_splitting_exists jordan_invariants_holds alpha_discriminant_holds local_gluing_holds gluing_product_holds

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HSumRight
section
noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

theorem h_sum_left (a : Fin D.R.rS → D.host.E) (x : Fin D.R.rS → (VS D).V) (y : (VS D).V) :
    (VS D).hT (∑ c, a c • x c) y = ∑ c, star (a c) * (VS D).hT (x c) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, starRingEnd_apply]

theorem h_sum_right (a : Fin D.R.rS → D.host.E) (x : Fin D.R.rS → (VS D).V) (y : (VS D).V) :
    (VS D).hT y (∑ c, a c • x c) = ∑ c, a c * (VS D).hT y (x c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul]

theorem h_e_nF (hxs : ∀ b, InW X (xs b)) (c b : Fin D.R.rS) : (VS D).hT (X.eX c) (nF X X0 xs M b) = Ym X0 c b := by
  unfold nF om
  rw [map_add (f := _), map_add (f := _), map_neg, h_sum_right, h_sum_right, h_sum_right]
  have hx1 : ∀ c d, (VS D).hT (X.eX c) (xs d) = 0 := fun c d => (hxs d c).1
  simp [X.ef, X.ee, hx1, Finset.sum_ite_eq]

theorem h_f_nF (hxs : ∀ b, InW X (xs b)) (c b : Fin D.R.rS) : (VS D).hT (X.fY c) (nF X X0 xs M b) = (X0 * M) c b := by
  unfold nF om
  rw [map_add (f := _), map_add (f := _), map_neg, h_sum_right, h_sum_right, h_sum_right]
  have hx2 : ∀ c d, (VS D).hT (X.fY c) (xs d) = 0 := fun c d => (hxs d c).2
  simp [X.ff, h_fe, hx2, Finset.sum_ite_eq]

theorem h_xs_nF (hxs : ∀ b, InW X (xs b)) (c b : Fin D.R.rS) :
    (VS D).hT (xs c) (nF X X0 xs M b) = -∑ d, Ym X0 d b * (VS D).hT (xs c) (xs d) := by
  unfold nF om
  rw [map_add (f := _), map_add (f := _), map_neg, h_sum_right, h_sum_right, h_sum_right]
  simp [(inW_left X (hxs c) _).1, (inW_left X (hxs c) _).2]

theorem h_nF_left (a : Fin D.R.rS) (y : (VS D).V) :
    (VS D).hT (nF X X0 xs M a) y = ∑ c, star (Ym X0 c a) * (VS D).hT (X.fY c) y -
      ∑ c, star (Ym X0 c a) * (VS D).hT (xs c) y + ∑ c, star ((X0 * M) c a) * (VS D).hT (X.eX c) y := by
  unfold nF om
  rw [LinearMap.map_add₂, LinearMap.map_add₂, LinearMap.map_neg₂, h_sum_left, h_sum_left, h_sum_left]
  ring

theorem h_nE_left (a : Fin D.R.rS) (y : (VS D).V) :
    (VS D).hT (nE X X0 a) y = ∑ c, star (X0 c a) * (VS D).hT (X.eX c) y := by
  unfold nE
  rw [h_sum_left]

theorem g_ee (a b : Fin D.R.rS) : (VS D).hT (nE X X0 a) (nE X X0 b) = (VS D).hT (X.eX a) (X.eX b) := by
  rw [h_nE_left, X.ee]
  unfold nE
  simp [h_sum_right, X.ee]

theorem g_ef (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (a b : Fin D.R.rS) :
    (VS D).hT (nE X X0 a) (nF X X0 xs M b) = (VS D).hT (X.eX a) (X.fY b) := by
  rw [h_nE_left, X.ef]
  simp_rw [h_e_nF X X0 xs M hxs]
  have h1 : (X0ᴴ * Ym X0) a b = ∑ c, star (X0 c a) * Ym X0 c b := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h2 : X0ᴴ * Ym X0 = 1 := by
    unfold Ym
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  rw [← h1, h2, Matrix.one_apply]

theorem g_ff (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs) (a b : Fin D.R.rS) :
    (VS D).hT (nF X X0 xs M a) (nF X X0 xs M b) = (VS D).hT (X.fY a) (X.fY b) := by
  rw [h_nF_left, X.ff]
  simp_rw [h_f_nF X X0 xs M hxs, h_xs_nF X X0 xs M hxs, h_e_nF X X0 xs M hxs]
  have hY : (Ym X0)ᴴ = X0⁻¹ := by unfold Ym; rw [Matrix.conjTranspose_conjTranspose]
  have e1 : ∑ c, star (Ym X0 c a) * (X0 * M) c b = M a b := by
    have : ((Ym X0)ᴴ * (X0 * M)) a b = ∑ c, star (Ym X0 c a) * (X0 * M) c b := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [← this, hY, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have e2 : ∑ c, star ((X0 * M) c a) * Ym X0 c b = Mᴴ a b := by
    have : ((X0 * M)ᴴ * Ym X0) a b = ∑ c, star ((X0 * M) c a) * Ym X0 c b := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [← this, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    unfold Ym
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one, Matrix.mul_one]
  have e3 : ∑ c, star (Ym X0 c a) * -∑ d, Ym X0 d b * (VS D).hT (xs c) (xs d) = -(Gp D X0 xs) a b := by
    have : ((Ym X0)ᴴ * Gq D xs * Ym X0) a b = ∑ c, star (Ym X0 c a) * ∑ d, Ym X0 d b * (VS D).hT (xs c) (xs d) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Gq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [← this, hY]
    rfl
  rw [e1, e3, e2]
  have := congrFun (congrFun hM a) b
  simp only [Matrix.add_apply, Matrix.neg_apply] at this
  rw [sub_neg_eq_add]
  linear_combination this

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OneMemZpowZero
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ddS_ne' : ddS D ≠ 0 := Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_ne

theorem star_mem_zpow (m : ℤ) {x : D.host.E} (hx : x ∈ ddS D ^ m) : star x ∈ ddS D ^ m := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_eq, ← FractionalIdeal.coeIdeal_pow] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    obtain ⟨y', hy', e⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_pow n y hy
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨y', hy', e⟩
  · rw [_root_.zpow_neg, zpow_natCast, Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_eq, ← FractionalIdeal.coeIdeal_pow] at hx ⊢
    exact Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_inv n hx

theorem iQ_eq (b a : Fin D.R.rS) :
    iQ D b a = ((ddS D ^ ((b : ℤ) - a) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
  unfold iQ aaD
  congr 1
  rw [← _root_.zpow_neg, ← zpow_add₀ ddS_ne']
  congr 1
  ring

theorem iP_eq (b a : Fin D.R.rS) :
    iP D b a = ((ddS D ^ (-((D.R.rS : ℤ) - b) - ((D.R.rS : ℤ) - a)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
  unfold iP aaD
  congr 1
  rw [← zpow_add₀ ddS_ne']
  congr 1

theorem star_mem_iQ {b a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ iQ D b a) : star x ∈ iQ D b a := by
  rw [iQ_eq] at hx ⊢; exact star_mem_zpow _ hx

theorem star_mem_iP {b a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ iP D b a) : star x ∈ iP D b a := by
  rw [iP_eq] at hx ⊢; exact star_mem_zpow _ hx

theorem iP_comm (b a : Fin D.R.rS) : iP D b a = iP D a b := by
  rw [iP_eq, iP_eq]; congr 2; ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

