module

public import Mathlib
public import Formalism.CorankShare.StatementFR

@[expose] public section

-- bundled from Formalism.CorankShare.CorankShareProofs.LayerCakeFormula
section
noncomputable section

namespace Formalism.CorankShareLayerCake.FR

open Finset MeasureTheory

namespace Pgsn2pfran

lemma ind_anti (c : ℝ) : Antitone (fun τ : ℝ => if τ < c then (1:ℝ) else 0) := by
  intro a b hab
  show (if b < c then (1:ℝ) else 0) ≤ (if a < c then (1:ℝ) else 0)
  by_cases h1 : b < c
  · have h2 : a < c := lt_of_le_of_lt hab h1
    simp [h1, h2]
  · by_cases h2 : a < c <;> simp [h1, h2]

lemma ind_int (c HH : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ HH) :
    ∫ τ in (0:ℝ)..HH, (if τ < c then (1:ℝ) else 0) = c := by
  have hi1 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1:ℝ) else 0) volume 0 c :=
    (ind_anti c).intervalIntegrable
  have hi2 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1:ℝ) else 0) volume c HH :=
    (ind_anti c).intervalIntegrable
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
    rw [ae_iff]
    simp
  have h1 : ∫ τ in (0:ℝ)..c, (if τ < c then (1:ℝ) else 0) = ∫ τ in (0:ℝ)..c, (1:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hc0] at hmem
    have hxc : x < c := lt_of_le_of_ne hmem.2 hx
    simp [hxc]
  have h2 : ∫ τ in c..HH, (if τ < c then (1:ℝ) else 0) = ∫ τ in c..HH, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    simp [not_lt.mpr hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, h1, h2]
  simp

lemma ind_lb (a xj HH : ℝ) (h : a - HH ≤ xj) (hHH : 0 ≤ HH) :
    a - xj ≤ ∫ τ in (0:ℝ)..HH, (if τ < a - xj then (1:ℝ) else 0) := by
  rcases le_total (a - xj) 0 with h0 | h0
  · have hpos : 0 ≤ ∫ τ in (0:ℝ)..HH, (if τ < a - xj then (1:ℝ) else 0) := by
      apply intervalIntegral.integral_nonneg hHH
      intro u _
      split_ifs <;> norm_num
    linarith
  · exact le_of_eq (ind_int (a - xj) HH h0 (by linarith)).symm

end Pgsn2pfran

open Pgsn2pfran

theorem layer_cake_formula : LayerCake := by
  unfold LayerCake
  intro D x a HH w hD hHH hx hw hcnt
  have hDpos : (0:ℝ) < D := by exact_mod_cast hD
  have hcount : ∀ τ : ℝ, ∑ j, (if τ < a - x j then (1:ℝ) else 0) =
      ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) := by
    intro τ
    rw [Finset.sum_boole]
    have hf : (Finset.univ.filter fun j => τ < a - x j) =
        (Finset.univ.filter fun j => x j < a - τ) :=
      Finset.filter_congr (fun j _ => by constructor <;> intro hh <;> linarith)
    rw [hf]
  have hanti : Antitone (fun τ : ℝ => ∑ j, (if τ < a - x j then (1:ℝ) else 0)) :=
    fun t1 t2 ht => Finset.sum_le_sum fun j _ => ind_anti (a - x j) ht
  have hint : ∫ τ in (0:ℝ)..HH, ∑ j, (if τ < a - x j then (1:ℝ) else 0) =
      ∑ j, ∫ τ in (0:ℝ)..HH, (if τ < a - x j then (1:ℝ) else 0) :=
    intervalIntegral.integral_finsetSum fun j _ => (ind_anti (a - x j)).intervalIntegrable
  have hsum : ∑ j, (a - x j) ≤ ∑ j, ∫ τ in (0:ℝ)..HH, (if τ < a - x j then (1:ℝ) else 0) :=
    Finset.sum_le_sum fun j _ => ind_lb a (x j) HH (hx j) hHH
  have hL : ∑ j, (a - x j) = (D:ℝ) * a - ∑ j, x j := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmono : ∫ τ in (0:ℝ)..HH, ∑ j, (if τ < a - x j then (1:ℝ) else 0) ≤
      ∫ τ in (0:ℝ)..HH, (D:ℝ) * min 1 (w τ) := by
    apply intervalIntegral.integral_mono_on hHH hanti.intervalIntegrable (hw.const_mul (D:ℝ))
    intro τ hτ
    show ∑ j, (if τ < a - x j then (1:ℝ) else 0) ≤ (D:ℝ) * min 1 (w τ)
    rw [hcount τ]
    have hc1 : (Finset.univ.filter fun j => x j < a - τ).card ≤ D := by
      calc _ ≤ (Finset.univ : Finset (Fin D)).card := Finset.card_filter_le _ _
        _ = D := by simp
    have hc1' : ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) ≤ D := by
      exact_mod_cast hc1
    have hc2 := hcnt τ hτ
    rcases le_total 1 (w τ) with hw1 | hw1
    · rw [min_eq_left hw1]
      linarith
    · rw [min_eq_right hw1]
      linarith
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [le_div_iff₀ hDpos]
  linarith

end Formalism.CorankShareLayerCake.FR
end
end

-- bundled from Formalism.CorankShare.CorankShareProofs.SumNormSqLeHilbertSchmidt
section
noncomputable section

namespace Formalism.CorankShareLayerCake.FR

namespace Pgsn2pfrla

open Finset Module LinearMap
open scoped InnerProductSpace

section gen
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

lemma norm_inner_swap (x y : E) : ‖⟪x, y⟫_ℂ‖ = ‖⟪y, x⟫_ℂ‖ := by
  exact norm_inner_symm x y

private lemma re_inner_self_eq_norm_sq_corank_share {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] (x : G) :
    (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

private lemma orthonormalBasis_sum_norm_inner_sq_eq_norm_sq {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ G) (x : G) : ∑ i, ‖⟪b i, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 :=
  b.sum_sq_norm_inner_right x

lemma sum_adj_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : E →ₗ[ℂ] F)
    (v : OrthonormalBasis ι ℂ E) (u : OrthonormalBasis κ ℂ F) :
    ∑ n, ‖adjoint A (u n)‖ ^ 2 = ∑ m, ‖A (v m)‖ ^ 2 := by
  have h1 : ∀ n, ‖adjoint A (u n)‖ ^ 2 = ∑ m, ‖⟪u n, A (v m)⟫_ℂ‖ ^ 2 := by
    intro n
    rw [← orthonormalBasis_sum_norm_inner_sq_eq_norm_sq v]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [LinearMap.adjoint_inner_right, norm_inner_swap]
  have h2 : ∀ m, ‖A (v m)‖ ^ 2 = ∑ n, ‖⟪u n, A (v m)⟫_ℂ‖ ^ 2 := fun m => (orthonormalBasis_sum_norm_inner_sq_eq_norm_sq u _).symm
  simp only [h1, h2]
  exact Finset.sum_comm

private lemma trace_eq_sum_inner_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E)
    (T : E →ₗ[ℂ] E) : trace ℂ E T = ∑ i, ⟪b i, T (b i)⟫_ℂ := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis, Matrix.trace]
  simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

lemma hilbert_schmidt_eq_basis_sum {ι : Type*} [Fintype ι] (A : E →ₗ[ℂ] F) (v : OrthonormalBasis ι ℂ E) :
    hs2 A = ∑ m, ‖A (v m)‖ ^ 2 := by
  classical
  unfold hs2
  rw [trace_eq_sum_inner_orthonormalBasis v, Complex.re_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, re_inner_self_eq_norm_sq_corank_share]

lemma sum_norm_sq_le_hilbert_schmidt {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] F) {g : κ → E} (hg : Orthonormal ℂ g) :
    ∑ l, ‖A (g l)‖ ^ 2 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E), ← sum_adj_eq A (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F)]
  have h1 : ∀ l, ‖A (g l)‖ ^ 2 = ∑ n, ‖⟪g l, adjoint A (stdOrthonormalBasis ℂ F n)⟫_ℂ‖ ^ 2 := by
    intro l
    rw [← orthonormalBasis_sum_norm_inner_sq_eq_norm_sq (stdOrthonormalBasis ℂ F)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [LinearMap.adjoint_inner_right, norm_inner_swap]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun n _ => Orthonormal.sum_inner_products_le _ hg)

lemma sum_re_inner_bound {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] E) {g : κ → E}
    (hg : Orthonormal ℂ g) :
    |∑ l, (⟪g l, A (g l)⟫_ℂ).re| ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (hs2 A) := by
  have h1 : ∀ l, |(⟪g l, A (g l)⟫_ℂ).re| ≤ ‖A (g l)‖ := by
    intro l
    calc |(⟪g l, A (g l)⟫_ℂ).re| ≤ ‖⟪g l, A (g l)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖g l‖ * ‖A (g l)‖ := norm_inner_le_norm _ _
      _ = ‖A (g l)‖ := by rw [hg.1 l, one_mul]
  have h2 : (∑ l, ‖A (g l)‖) ^ 2 ≤ (Fintype.card κ) * hs2 A := by
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun l => ‖A (g l)‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (sum_norm_sq_le_hilbert_schmidt A hg) (Nat.cast_nonneg _))
  calc |∑ l, (⟪g l, A (g l)⟫_ℂ).re| ≤ ∑ l, |(⟪g l, A (g l)⟫_ℂ).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, ‖A (g l)‖ := Finset.sum_le_sum (fun l _ => h1 l)
    _ = √((∑ l, ‖A (g l)‖) ^ 2) := (Real.sqrt_sq (Finset.sum_nonneg (fun l _ => norm_nonneg _))).symm
    _ ≤ √((Fintype.card κ) * hs2 A) := Real.sqrt_le_sqrt h2
    _ = √(Fintype.card κ) * √(hs2 A) := Real.sqrt_mul (Nat.cast_nonneg _) _

lemma fam_bound (c : ℝ) (B : E →ₗ[ℂ] F) {κ : Type*} [Fintype κ] {g : κ → E}
    (hg : Orthonormal ℂ g) :
    |c * ∑ l, ‖B (g l)‖ ^ 2 - Fintype.card κ|
      ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (hs2 (frK c B - LinearMap.id)) := by
  have h1 : ∀ l, (⟪g l, ((frK c B - LinearMap.id : E →ₗ[ℂ] E)) (g l)⟫_ℂ).re = c * ‖B (g l)‖ ^ 2 - 1 := by
    intro l
    simp only [frK, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      inner_sub_right, inner_smul_right, LinearMap.adjoint_inner_right, Complex.sub_re, Complex.re_ofReal_mul,
      re_inner_self_eq_norm_sq_corank_share, hg.1 l]
    norm_num
  have h2 : ∑ l, (⟪g l, ((frK c B - LinearMap.id : E →ₗ[ℂ] E)) (g l)⟫_ℂ).re = c * ∑ l, ‖B (g l)‖ ^ 2 - Fintype.card κ := by
    rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_sub_distrib, Finset.mul_sum]
    simp
  rw [← h2]
  exact sum_re_inner_bound _ hg

end gen

section fam
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma re_inner_Q (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x : H) :
    (⟪x, frQ c B x⟫_ℂ).re = ∑ i, c i * ‖adjoint (B i) x‖ ^ 2 := by
  simp only [frQ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_sum, inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← LinearMap.adjoint_inner_left (B i) (adjoint (B i) x) x, re_inner_self_eq_norm_sq_corank_share]

lemma Q_symm (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x y : H) :
    ⟪frQ c B x, y⟫_ℂ = ⟪x, frQ c B y⟫_ℂ := by
  simp only [frQ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_left]

lemma tQ_eq (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (trace ℂ H (frQ c B)).re = ∑ i, c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [frQ, map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← hilbert_schmidt_eq_basis_sum (B i) (stdOrthonormalBasis ℂ (V i))]
  unfold hs2
  rw [LinearMap.trace_comp_comm']

lemma trace_frame_sq_eq_sum (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (stdOrthonormalBasis ℂ H n)‖ ^ 2 := by
  have hadj : frQ c B = adjoint (frQ c B) := by
    rw [LinearMap.eq_adjoint_iff]; exact Q_symm c B
  have h := hilbert_schmidt_eq_basis_sum (frQ c B) (stdOrthonormalBasis ℂ H)
  unfold hs2 at h
  rw [← hadj] at h
  exact h

end fam

section wup
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma W_upper (B : V →ₗ[ℂ] H) (N : Submodule ℂ V) {κ : Type*} [Fintype κ] {g : κ → H}
    (hg : Orthonormal ℂ g) (hperp : ∀ l, ∀ n ∈ N, ⟪B n, g l⟫_ℂ = 0) :
    ∑ l, ‖adjoint B (g l)‖ ^ 2 ≤ ∑ m, ‖B ((stdOrthonormalBasis ℂ Nᗮ m : V))‖ ^ 2 := by
  have hmem : ∀ l, adjoint B (g l) ∈ Nᗮ := by
    intro l
    rw [Submodule.mem_orthogonal]
    intro n hn
    rw [LinearMap.adjoint_inner_right, hperp l n hn]
  have h1 : ∀ l, ‖adjoint B (g l)‖ ^ 2 = ∑ m, ‖⟪g l, B ((stdOrthonormalBasis ℂ Nᗮ m : V))⟫_ℂ‖ ^ 2 := by
    intro l
    have h := orthonormalBasis_sum_norm_inner_sq_eq_norm_sq (stdOrthonormalBasis ℂ Nᗮ) ⟨adjoint B (g l), hmem l⟩
    have hn : ‖(⟨adjoint B (g l), hmem l⟩ : Nᗮ)‖ = ‖adjoint B (g l)‖ := rfl
    rw [hn] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hi : ⟪stdOrthonormalBasis ℂ Nᗮ m, (⟨adjoint B (g l), hmem l⟩ : Nᗮ)⟫_ℂ
        = ⟪(stdOrthonormalBasis ℂ Nᗮ m : V), adjoint B (g l)⟫_ℂ := rfl
    rw [hi, LinearMap.adjoint_inner_right, norm_inner_swap]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun m _ => Orthonormal.sum_inner_products_le _ hg)

end wup

end Pgsn2pfrla

open Finset Module LinearMap Pgsn2pfrla
open scoped InnerProductSpace

end Formalism.CorankShareLayerCake.FR
end
end

