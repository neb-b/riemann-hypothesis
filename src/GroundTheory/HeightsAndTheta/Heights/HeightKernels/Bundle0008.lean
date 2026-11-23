module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShell
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

noncomputable section

namespace PGaussShell

theorem base_le (m δ : ℝ) (hm : 0 ≤ m) (hδ : 0 < δ) :
    1 + 2 * (m + 1) / δ ≤ 3 * (m + 1) * (1 + 1 / δ) := by
  have h2 : 3 * (m + 1) * (1 + 1 / δ) = 3 * (m + 1) + 3 * (m + 1) / δ := by ring
  have h1 : 2 * (m + 1) / δ ≤ 3 * (m + 1) / δ :=
    div_le_div_of_nonneg_right (by linarith) hδ.le
  linarith

end PGaussShell

theorem GaussShell.proof (hP : GaussPacking.Statement) (hT : GaussTermBound.Statement) :
    GaussShell.Statement := by
  intro n hn Λ δ hδ hmin F m
  set T := F.filter (fun μ : Λ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊ = m) with hTdef
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlow : ∀ μ ∈ T, (m : ℝ) ≤ ‖(μ : EuclideanSpace ℝ (Fin n))‖ := by
    intro μ hμ
    rw [← (Finset.mem_filter.1 hμ).2]
    exact Nat.floor_le (norm_nonneg _)
  have hup : ∀ μ ∈ T, ‖(μ : EuclideanSpace ℝ (Fin n))‖ ≤ (m : ℝ) + 1 := by
    intro μ hμ
    have h := Nat.lt_floor_add_one ‖(μ : EuclideanSpace ℝ (Fin n))‖
    rw [(Finset.mem_filter.1 hμ).2] at h
    exact h.le
  have hterm : ∀ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
      Real.exp (-π * (m : ℝ) ^ 2) := by
    intro μ hμ
    apply Real.exp_le_exp.2
    have : (m : ℝ) ^ 2 ≤ ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      pow_le_pow_left₀ hm0 (hlow μ hμ) 2
    nlinarith [Real.pi_pos]
  have hsum : ∑ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
      (T.card : ℝ) * Real.exp (-π * (m : ℝ) ^ 2) := by
    have h := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hcard : (T.card : ℝ) ≤ (1 + 2 * ((m : ℝ) + 1) / δ) ^ n := by
    have h := hP n (T.map (Function.Embedding.subtype _)) δ ((m : ℝ) + 1) hδ (by linarith) ?_ ?_
    · rwa [Finset.card_map] at h
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
      simp only [Function.Embedding.coe_subtype] at hxy ⊢
      exact hmin _ (Λ.sub_mem a.2 b.2) (sub_ne_zero.2 hxy)
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      exact hup a ha
  have hδ' : (0 : ℝ) ≤ 1 + 1 / δ := by
    have : 0 ≤ 1 / δ := le_of_lt (one_div_pos.2 hδ)
    linarith
  have hb0 : (0 : ℝ) ≤ 1 + 2 * ((m : ℝ) + 1) / δ := by
    have : 0 ≤ 2 * ((m : ℝ) + 1) / δ := div_nonneg (by linarith) hδ.le
    linarith
  have hpow : (1 + 2 * ((m : ℝ) + 1) / δ) ^ n ≤
      3 ^ n * ((m : ℝ) + 1) ^ n * (1 + 1 / δ) ^ n := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ hb0 (PGaussShell.base_le _ _ hm0 hδ) n
  calc ∑ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      ≤ (T.card : ℝ) * Real.exp (-π * (m : ℝ) ^ 2) := hsum
    _ ≤ 3 ^ n * ((m : ℝ) + 1) ^ n * (1 + 1 / δ) ^ n * Real.exp (-π * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (hcard.trans hpow) (Real.exp_pos _).le
    _ = 3 ^ n * (1 + 1 / δ) ^ n * (((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2)) := by ring
    _ ≤ 3 ^ n * (1 + 1 / δ) ^ n * (√(n : ℝ) ^ n * Real.exp √(n : ℝ) *
          Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ))) :=
        mul_le_mul_of_nonneg_left (hT n hn m) (by positivity)
    _ = gaussShellConst n * (1 + 1 / δ) ^ n * Real.exp (-(m : ℝ)) := by
        unfold gaussShellConst; ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShellSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

noncomputable section

namespace PGaussShellSum

theorem inv_one_sub_exp_neg_one_le_two : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hlt : 0 < 1 - Real.exp (-1) := by linarith
  rw [inv_le_comm₀ hlt (by norm_num)]
  linarith

theorem exp_neg_nat (m : ℕ) : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end PGaussShellSum


open PGaussShellSum in
theorem GaussShellSum.proof (hS : GaussShell.Statement) : GaussShellSum.Statement := by
  intro n hn Λ δ hδ hmin
  set K : ℝ := gaussShellConst n * (1 + 1 / δ) ^ n with hK
  let f : Λ → ℝ := fun μ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hf : 0 ≤ f := fun μ => (Real.exp_pos _).le
  have hK0 : 0 ≤ K := by
    have hc : 0 ≤ gaussShellConst n := by unfold gaussShellConst; positivity
    have : 0 ≤ 1 + 1 / δ := by positivity
    positivity
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1) < 1 := by
    exact Real.exp_lt_one_iff.2 (by norm_num)
  have hgeo : Summable fun j : ℕ => K * Real.exp (-1) ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left K
  have hbound : ∀ u : Finset Λ, ∑ μ ∈ u, f μ ≤ 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by
    intro u
    let fl : Λ → ℕ := fun μ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (g := fl) (t := u.image fl)
      (fun μ hμ => Finset.mem_image_of_mem fl hμ) f]
    calc ∑ j ∈ u.image fl, ∑ μ ∈ u with fl μ = j, f μ
        ≤ ∑ j ∈ u.image fl, K * Real.exp (-1) ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← exp_neg_nat]
          exact hS n hn Λ δ hδ hmin u j
      _ ≤ ∑' j : ℕ, K * Real.exp (-1) ^ j :=
          hgeo.sum_le_tsum _ (fun j _ => by positivity)
      _ = K * (1 - Real.exp (-1))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      _ ≤ K * 2 := mul_le_mul_of_nonneg_left inv_one_sub_exp_neg_one_le_two hK0
      _ = 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by rw [hK]; ring
  exact ⟨summable_of_sum_le hf hbound, Real.tsum_le_of_sum_le hf hbound⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussSqrt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussSqrt

theorem eq_eigenvectors_mul_diagonal {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hH : Y.IsHermitian) :
    Y = (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) * diagonal hH.eigenvalues *
      (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ)ᵀ := by
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl

end PGaussSqrt

theorem GaussSqrt.proof : GaussSqrt.Statement := by
  intro g Y hY
  classical
  set hH := hY.isHermitian
  set U : Matrix (Fin g) (Fin g) ℝ := (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) with hUdef
  refine ⟨diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ, ?_⟩
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => (hY.eigenvalues_pos i).le
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  calc U * diagonal (fun i => √(hH.eigenvalues i)) * (diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ)
      = U * (diagonal (fun i => √(hH.eigenvalues i)) * diagonal (fun i => √(hH.eigenvalues i)))
          * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = U * diagonal hH.eigenvalues * Uᵀ := by
      have hsq : (fun i => √(hH.eigenvalues i) * √(hH.eigenvalues i)) = hH.eigenvalues :=
        funext fun i => Real.mul_self_sqrt (hnn i)
      rw [diagonal_mul_diagonal, hsq]
    _ = Y := (PGaussSqrt.eq_eigenvectors_mul_diagonal hH).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussTermBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace PGaussTermBound

theorem pow_le_sqrt_pow_mul_exp (n m : ℕ) (hn : 1 ≤ n) :
    ((m : ℝ) + 1) ^ n ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) := by
  set s := √(n : ℝ) with hs_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.2 hn'
  have hss : s * s = n := Real.mul_self_sqrt hn'.le
  have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (s * ((m : ℝ) + 1)) (mul_nonneg hs.le hm) n
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hfac] at h1
  have hfac2 : (n.factorial : ℝ) ≤ s ^ n * s ^ n := by
    rw [← mul_pow, hss]
    exact_mod_cast Nat.factorial_le_pow n
  have hE : 0 ≤ Real.exp (s * ((m : ℝ) + 1)) := (Real.exp_pos _).le
  have h2 : s ^ n * ((m : ℝ) + 1) ^ n ≤ s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by
    rw [← mul_pow]
    calc (s * ((m : ℝ) + 1)) ^ n ≤ Real.exp (s * ((m : ℝ) + 1)) * (n.factorial : ℝ) := h1
      _ ≤ Real.exp (s * ((m : ℝ) + 1)) * (s ^ n * s ^ n) := mul_le_mul_of_nonneg_left hfac2 hE
      _ = s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by ring
  exact le_of_mul_le_mul_left h2 (pow_pos hs n)

theorem exponent_le (n m : ℕ) :
    √(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2 ≤ √(n : ℝ) + n / (2 * π) + -(m : ℝ) := by
  set s := √(n : ℝ) with hs_def
  have hss : s * s = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hpi : 0 < π := Real.pi_pos
  have hpi3 : 3 < π := Real.pi_gt_three

  have hA : s * m - π / 2 * (m : ℝ) ^ 2 ≤ n / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (π * m - s)]

  have hB : (m : ℝ) ≤ π / 2 * (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  nlinarith

end PGaussTermBound

theorem GaussTermBound.proof : GaussTermBound.Statement := by
  intro n hn m
  have h1 := PGaussTermBound.pow_le_sqrt_pow_mul_exp n m hn
  have h2 := PGaussTermBound.exponent_le n m
  have hE : 0 ≤ Real.exp (-π * (m : ℝ) ^ 2) := (Real.exp_pos _).le
  calc ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2)
      ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) * Real.exp (-π * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ = √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2) := by
        rw [Real.exp_add]; ring
    _ ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) + n / (2 * π) + -(m : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by positivity)
    _ = √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ)) := by
        rw [Real.exp_add, Real.exp_add]; ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

theorem GaussianSum.proof (hPD : GaussPoissonDual.Statement) (hSS : GaussShellSum.Statement)
    (hC : GaussConstant.Statement) : GaussianSum.Statement := by
  refine ⟨72 * Real.exp 4, by positivity, ?_⟩
  intro g Y ρ hY hρ hmin u
  obtain ⟨hsum, Λ, hΛ, hle⟩ := hPD g Y ρ hY hρ hmin u
  refine ⟨hsum, ?_⟩
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hq : ∀ k : Fin 0 → ℤ, qf Y (intVec k + u) = 0 := fun k => by simp [qf]
    simp only [hq, mul_zero, Real.exp_zero, tsum_const, Nat.card_unique, one_smul,
      Nat.cast_zero, zero_div, Real.rpow_zero, Matrix.det_isEmpty, Real.one_rpow, pow_zero,
      mul_one, le_refl]
  · have hdet : 0 < Y.det := hY.det_pos
    have hd : 0 ≤ Y.det ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hdet.le _
    have hS := (hSS g hg Λ ρ hρ hΛ).2
    have hc := hC g hg
    have hr : 0 ≤ (1 + 1 / ρ) ^ g := by positivity
    calc ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u))
        ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := hle
      _ ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) * (2 * gaussShellConst g * (1 + 1 / ρ) ^ g) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = √2 ^ g * (2 * gaussShellConst g) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g := by ring
      _ ≤ (72 * Real.exp 4 * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hd) hr

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutPrimeEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTransportFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutTransportFirst

end RestCutTransportFirst

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplBoxVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplBoxVolume

theorem set_eq_preimage {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      (Matrix.toLin' A) ⁻¹' (Set.pi Set.univ fun i => Set.Ioo (-a i) (a i)) := by
  ext x
  simp [abs_lt]

end PSymplBoxVolume


open PSymplBoxVolume in
theorem SymplBoxVolume.proof : SymplBoxVolume.Statement := by
  intro ι _ _ A a hA ha
  rw [set_eq_preimage, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin'])
    , Real.volume_pi_Ioo, LinearMap.det_toLin',
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [ha i]),
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, div_eq_mul_inv, mul_comm]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplCons
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplCons

theorem J_mulVec_inl {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inl i) = -v (Sum.inr i) := by
  simp [Matrix.J, fromBlocks_mulVec, neg_mulVec]

theorem J_mulVec_inr {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inr i) = v (Sum.inl i) := by
  simp [Matrix.J, fromBlocks_mulVec]

theorem symplOmega_eq_sum {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) :
    symplOmega u v = ∑ i, (u (Sum.inr i) * v (Sum.inl i) - u (Sum.inl i) * v (Sum.inr i)) := by
  unfold symplOmega dotProduct
  rw [Fintype.sum_sum_type]
  simp only [J_mulVec_inl, J_mulVec_inr, mul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_sub_distrib]
  ring

end PSymplCons


open PSymplCons in
theorem SymplCons.proof : SymplCons.Statement := by
  intro R _ n
  refine ⟨fun u => ?_, fun p q p' q' w w' => ?_⟩
  · funext x
    rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [symplCons, symplTail]
  · rw [symplOmega_eq_sum, symplOmega_eq_sum, Fin.sum_univ_succ]
    simp [symplCons]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplDetBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplDetBound

theorem step_bound (n : ℕ) (ρ : ℝ) (hle : ρ ≤ 2 * ((n : ℝ) + 1)) :
    ρ * (2 * (n : ℝ)) ^ n ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  have h0 : (0 : ℝ) ≤ (2 * (n : ℝ)) ^ n := by positivity
  calc ρ * (2 * (n : ℝ)) ^ n ≤ (2 * ((n : ℝ) + 1)) * (2 * (n : ℝ)) ^ n :=
        mul_le_mul_of_nonneg_right hle h0
    _ ≤ (2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1)) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        linarith
    _ = (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
        push_cast; ring

end PSymplDetBound

theorem SymplDetBound.proof (h1 : SymplStep.Statement) : SymplDetBound.Statement := by
  intro n
  induction n with
  | zero =>
    intro G _ _
    refine ⟨1, Submonoid.one_mem _, ?_⟩
    rw [Matrix.det_isEmpty]
    simp
  | succ n ih =>
    intro G hG hpos
    obtain ⟨ρsq, _, _, hle, P, hP, _, hdet⟩ :=
      h1 n ((2 * (n : ℝ)) ^ n) G hG hpos (fun H hH hHpos => ih H hH hHpos)
    exact ⟨P, hP, hdet.trans (PSymplDetBound.step_bound n ρsq hle)⟩

end GroundTheory.Heights₂.Heights
end

