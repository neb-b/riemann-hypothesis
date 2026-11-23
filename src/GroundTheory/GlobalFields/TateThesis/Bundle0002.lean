module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
section
open Real Function
open scoped ContDiff Nat SchwartzMap

namespace GroundTheory.Global

noncomputable section

theorem one_add_pow_mul_exp_neg_pi_mul_sq_le {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N ^ 2 / (4 * π)) := by
  have h1 : (1 + r) ^ N ≤ Real.exp (N * r) := by
    calc (1 + r) ^ N ≤ Real.exp r ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
      _ = Real.exp (N * r) := by rw [← Real.exp_nat_mul]
  calc (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N * r) * Real.exp (-π * r ^ 2) := by
        gcongr
    _ = Real.exp (N * r - π * r ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (N ^ 2 / (4 * π)) := by
      apply Real.exp_le_exp.2
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((N : ℝ) - 2 * π * r), Real.pi_pos]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussianFun (x : E) : ℂ := ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)

theorem contDiff_gaussianFun : ContDiff ℝ ∞ (gaussianFun (E := E)) :=
  Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem norm_iteratedFDeriv_exp (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem norm_iteratedFDeriv_gaussian_le (n : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (gaussianFun (E := E)) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (-π * ‖x‖ ^ 2) := by
  set q : E → ℝ := fun x ↦ -π * ‖x‖ ^ 2 with hq_def
  have hq : q.HasTemperateGrowth := (HasTemperateGrowth.const (-π)).mul (hasTemperateGrowth_norm_sq E)
  have hqs : ContDiff ℝ ∞ q := contDiff_const.mul (contDiff_norm_sq ℝ)
  obtain ⟨k, C, hC, hb⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * max C 1 ^ n, k * n, by positivity, fun x ↦ ?_⟩
  have hx1 : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg x])
  set D := max C 1 * (1 + ‖x‖) ^ k
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hx1
  have hcomp : ‖iteratedFDeriv ℝ n (Real.exp ∘ q) x‖ ≤ n ! * Real.exp (q x) * D ^ n := by
    refine norm_iteratedFDeriv_comp_le Real.contDiff_exp hqs (by exact_mod_cast le_top) x
      (fun i _ ↦ (norm_iteratedFDeriv_exp i (q x)).le) fun i hi1 hin ↦ ?_
    calc ‖iteratedFDeriv ℝ i q x‖ ≤ C * (1 + ‖x‖) ^ k := hb i hin x
      _ ≤ D := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
  have hG : gaussianFun (E := E) = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ (Real.exp ∘ q) := rfl
  rw [hG, LinearIsometry.norm_iteratedFDeriv_comp_left _
    (Real.contDiff_exp.comp hqs).contDiffAt (by exact_mod_cast le_top)]
  refine hcomp.trans (le_of_eq ?_)
  simp only [D, mul_pow, ← pow_mul, hq_def]
  ring

def gaussianSchwartz (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : 𝓢(E, ℂ) where
  toFun := gaussianFun
  smooth' := contDiff_gaussianFun
  decay' k n := by
    obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_gaussian_le (E := E) n
    refine ⟨C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)), fun x ↦ ?_⟩
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n gaussianFun x‖
        ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ j * Real.exp (-π * ‖x‖ ^ 2)) :=
          mul_le_mul hk (hb x) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) ^ (k + j) * Real.exp (-π * ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_neg_pi_mul_sq_le (norm_nonneg x) _) hC

@[simp]
theorem gaussianSchwartz_apply (x : E) :
    gaussianSchwartz E x = ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
  rfl

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
section
namespace GroundTheory.Global

open Topology Filter

def NoSmallSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥

theorem norm_sq_sub_one_ge {z : ℂ} (hz : ‖z - 1‖ < 1 / 2) :
    3 / 2 * ‖z - 1‖ ≤ ‖z ^ 2 - 1‖ := by
  have h1 : z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
  have h2 : (3 : ℝ) / 2 ≤ ‖z + 1‖ := by
    have : z + 1 = 2 - (1 - z) := by ring
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    have h4 : ‖1 - z‖ = ‖z - 1‖ := norm_sub_rev _ _
    calc (3 : ℝ) / 2 ≤ ‖(2 : ℂ)‖ - ‖1 - z‖ := by rw [h3, h4]; linarith
      _ ≤ ‖(2 : ℂ) - (1 - z)‖ := norm_sub_norm_le _ _
      _ = ‖z + 1‖ := by rw [this]
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (z - 1)]

theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt {z : ℂ}
    (hz : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := norm_sq_sub_one_ge (hz k)
      rw [← pow_mul, ← pow_succ] at h
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = 3 / 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
        _ ≤ 3 / 2 * ‖z ^ (2 ^ k) - 1‖ := by gcongr
        _ ≤ _ := h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := lt_of_le_of_lt (key k) (hz k)
  rw [div_lt_iff₀ (by positivity)] at hk
  nlinarith

theorem eq_one_of_sq_mem {s : Set ℂ} (hsq : ∀ z ∈ s, z ^ 2 ∈ s)
    (hs : ∀ z ∈ s, ‖z - 1‖ < 1 / 2) {z : ℂ} (hz : z ∈ s) : z = 1 := by
  refine eq_one_of_forall_norm_pow_two_pow_sub_one_lt fun k ↦ hs _ ?_
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact hsq _ ih

namespace Circle

theorem subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup Circle)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← Circle.coe_eq_one]
  refine eq_one_of_sq_mem (s := (↑) '' (H : Set Circle)) ?_ ?_ ⟨z, hz, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w ^ 2, H.pow_mem hw 2, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hH w hw

theorem noSmallSubgroups : NoSmallSubgroups Circle := by
  refine ⟨{z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : Circle ↦ ‖(z : ℂ) - 1‖ :=
    (continuous_subtype_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

end Circle

namespace Complex

theorem units_subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup ℂˣ)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← Units.val_eq_one]
  refine eq_one_of_sq_mem (s := (↑) '' (H : Set ℂˣ)) ?_ ?_ ⟨z, hz, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w ^ 2, H.pow_mem hw 2, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hH w hw

theorem units_noSmallSubgroups : NoSmallSubgroups ℂˣ := by
  refine ⟨{z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    units_subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : ℂˣ ↦ ‖(z : ℂ) - 1‖ :=
    (Units.continuous_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

end Complex

section Kernel

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]

theorem isOpen_ker_of_noSmallSubgroups
    (hG : ∀ W ∈ 𝓝 (1 : G), ∃ V : OpenSubgroup G, (V : Set G) ⊆ W) (hH : NoSmallSubgroups H)
    (f : G →* H) (hf : Continuous f) : IsOpen (f.ker : Set G) := by
  obtain ⟨U, hU, hsmall⟩ := hH
  have hW : f ⁻¹' U ∈ 𝓝 (1 : G) := hf.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨V, hV⟩ := hG _ hW
  have hmap : V.toSubgroup.map f = ⊥ := by
    refine hsmall _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hV hx
  refine Subgroup.isOpen_mono (H₁ := V.toSubgroup) ?_ V.isOpen
  rwa [← Subgroup.map_eq_bot_iff]

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

end Kernel

end GroundTheory.Global
end

