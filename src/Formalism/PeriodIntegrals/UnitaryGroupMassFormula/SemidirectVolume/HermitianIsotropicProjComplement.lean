module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjGen

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

def FixEZ (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop := (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z

def Uni (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop := ∀ x y, D.h (S x) (S y) = D.h x y

variable {D : Dat A n r}

theorem h_e_pX (H : D.Hyp) (b : Fin r) (u : n → A) : D.h (D.e b) (D.pX u) = 0 := by
  have key : ∀ x y, D.h x y = D.hL x y := fun _ _ => rfl
  have H3 : ∀ a c, D.hL (D.e a) (D.e c) = 0 := fun a c => H.3 a c
  rw [key]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dat.pX.eq_1, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum,
    map_smul, H3, smul_zero, Finset.sum_const_zero]

theorem h_pX_left {y : n → A} (hy : ∀ b, D.h (D.e b) y = 0) (u : n → A) : D.h (D.pX u) y = 0 := by
  have hy' : ∀ b, ∑ x, ∑ x_1, D.σA (D.e b x) * D.JA x x_1 * y x_1 = 0 := fun b => hy b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dat.h, hform, Dat.pX.eq_1, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset (Fin r)))]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [← mul_zero (D.σA ((D.hL (D.f d)) u)), ← hy' d, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x1 _ => ?_
  ring

theorem h_pX_right (H : D.Hyp) {y : n → A} (hy : ∀ b, D.h (D.e b) y = 0) (u : n → A) :
    D.h y (D.pX u) = 0 := by
  rw [h_symm H, h_pX_left hy, map_zero]

theorem S_pX {S : (n → A) →ₗ[A] (n → A)} (hS : ∀ a, S (D.e a) = D.e a) (u : n → A) :
    S (D.pX u) = D.pX u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dat.pX.eq_1, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum,
    map_smul, hS]

theorem h_e_S {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (b : Fin r)
    (w : n → A) : D.h (D.e b) (S w) = D.h (D.e b) w := by
  have h1 := hU (D.e b) w
  rwa [(show (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z from hS).1 b] at h1

theorem h_z_S {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (w : n → A) :
    D.h D.z (S w) = D.h D.z w := by
  have h1 := hU D.z w
  rwa [(show (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z from hS).2] at h1

theorem isotropic_proj_image_complement {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) {w : n → A}
    (hw : IsW D w) : D.pU (S w) = D.pX (S w) := by
  rw [pU_apply, pXv_apply, pz_apply]
  simp [h_e_S hS hU, h_z_S hS hU, hw.1, hw.2.2]

theorem complement_proj_image {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) {w : n → A}
    (hw : IsW D w) : D.pW (S w) = S w - D.pX (S w) := by
  rw [Dat.pW.eq_1, LinearMap.sub_apply, LinearMap.id_apply, isotropic_proj_image_complement hS hU hw]

theorem Pi_comp (H : D.Hyp) {S S' : (n → A) →ₗ[A] (n → A)} (hS : ∀ a, S (D.e a) = D.e a)
    (hS' : D.FixEZ S') (hU' : D.Uni S') (v : n → A) :
    D.Pi S (D.Pi S' v) = D.Pi (S ∘ₗ S') v := by
  have h1 : D.pU (D.Pi S' v) = D.pU v := by
    rw [Pi_apply, map_add (f := _), pU_pU H, pU_of_isW (isW_pW H _), add_zero]
  have h2 : D.pW (D.Pi S' v) = D.pW (S' (D.pW v)) := by
    rw [Pi_apply, map_add (f := _), pW_pU H, pW_pW H, zero_add]
  rw [Pi_apply D S, h1, h2, complement_proj_image hS' hU' (isW_pW H v), map_sub, S_pX hS, map_sub, pW_pX H,
    sub_zero, Pi_apply]
  rfl

theorem Pi_id (H : D.Hyp) (v : n → A) : D.Pi LinearMap.id v = v := by
  rw [Pi_apply, LinearMap.id_apply, pW_pW H, pW_apply]
  abel

theorem Pi_e (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) (a : Fin r) : D.Pi S (D.e a) = D.e a := by
  rw [Pi_apply, pU_e H, pW_e H, map_zero, map_zero, add_zero]

theorem Pi_f (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) (a : Fin r) : D.Pi S (D.f a) = D.f a := by
  rw [Pi_apply, pU_f H, pW_f H, map_zero, map_zero, add_zero]

theorem unipotent_proj_fixes_normal (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) : D.Pi S D.z = D.z := by
  rw [Pi_apply, pU_z_eq H, orthogonal_proj_normal_zero H, map_zero, map_zero, add_zero]

theorem hermitian_isotropic_proj_complement (H : D.Hyp) {w : n → A} (hw : IsW D w) (x : n → A) : D.h (D.pU x) w = 0 := by
  rw [pU_apply, h_add_left, h_add_left, pX_apply, pXv_apply, pz_apply, h_sum_left, h_sum_left]
  simp [h_smul_left, hw.1, hw.2.1, hw.2.2]

theorem h_W_pU (H : D.Hyp) {w : n → A} (hw : IsW D w) (x : n → A) : D.h w (D.pU x) = 0 := by
  rw [h_symm H, hermitian_isotropic_proj_complement H hw, map_zero]

theorem h_dec (H : D.Hyp) (x y : n → A) :
    D.h x y = D.h (D.pU x) (D.pU y) + D.h (D.pW x) (D.pW y) := by
  have ex : x = D.pU x + D.pW x := by rw [pW_apply]; abel
  have ey : y = D.pU y + D.pW y := by rw [pW_apply]; abel
  conv_lhs => rw [ex, ey]
  rw [h_add_left, h_add_right, h_add_right, hermitian_isotropic_proj_complement H (isW_pW H y), h_W_pU H (isW_pW H x)]
  ring

theorem Pi_uni (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) :
    D.Uni (D.Pi S) := by
  intro x y
  have hW : ∀ w w' : n → A, IsW D w → IsW D w' →
      D.h (D.pW (S w)) (D.pW (S w')) = D.h w w' := by
    intro w w' hw hw'
    have he : ∀ {u : n → A}, IsW D u → ∀ b, D.h (D.e b) (S u) = 0 := fun hu b => by
      rw [h_e_S hS hU, hu.1 b]
    rw [complement_proj_image hS hU hw, complement_proj_image hS hU hw', h_sub_left, h_sub_right, h_sub_right,
      h_pX_left (he hw'), h_pX_left (fun b => h_e_pX H b _), h_pX_right H (he hw), hU]
    ring
  have hp : ∀ v, D.pU (D.Pi S v) = D.pU v := fun v => by
    rw [Pi_apply, map_add (f := _), pU_pU H, pU_of_isW (isW_pW H _), add_zero]
  have hq : ∀ v, D.pW (D.Pi S v) = D.pW (S (D.pW v)) := fun v => by
    rw [Pi_apply, map_add (f := _), pW_pU H, pW_pW H, zero_add]
  rw [h_dec H (D.Pi S x), hp, hp, hq, hq, hW _ _ (isW_pW H x) (isW_pW H y), ← h_dec H]

theorem pX_mem_span (u : n → A) : D.pX u ∈ Submodule.span A (Set.range D.e) := by
  simp only [Dat.pX.eq_1, LinearMap.sum_apply, LinearMap.smulRight_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Dat

end PI.VolSemiDirect.W.PG
