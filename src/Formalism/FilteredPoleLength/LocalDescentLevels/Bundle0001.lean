module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.Bundle0001

@[expose] public section

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.DetMulEqSumPrincipal
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset Matrix Polynomial

theorem detPerturbNumeric : DetPerturbNumeric := by
  intro ρ hρ
  have hρ0 : (1:ℝ) ≤ ρ := by exact_mod_cast hρ
  have hpos : (0:ℝ) < ρ := by linarith
  have hx0 : 0 ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10 := by positivity
  have hρx : (ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ≤ 1 / 10 := by
    have e : (ρ:ℝ) * (ρ:ℝ) ^ (-(3:ℝ)/2) = (ρ:ℝ) ^ (-(1:ℝ)/2) := by
      rw [show (-(1:ℝ)/2) = 1 + (-(3:ℝ)/2) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    have h1 : (ρ:ℝ) ^ (-(1:ℝ)/2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hρ0 (by norm_num)
    rw [mul_div_assoc', e]
    linarith
  have h1 : (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ
      ≤ Real.exp ((ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)]) ρ
  have h2 : Real.exp ((ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)) ≤ Real.exp (1/10) :=
    Real.exp_le_exp.2 hρx
  have h3 : Real.exp (1/10) ≤ 3/2 := by
    by_contra hc
    push_neg at hc
    have h4 : (3/2:ℝ)^10 < Real.exp (1/10) ^ 10 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    rw [← Real.exp_nat_mul] at h4
    norm_num at h4
    linarith [Real.exp_one_lt_d9]
  linarith

theorem detPerturbation : DetPerturbation := by
  intro 𝕜 _ i κ _ w σ₀ ε Δmax hΔ
  classical
  have hΔ0 : 0 ≤ Δmax := (norm_nonneg _).trans (hΔ σ₀)
  have hdet : ∀ v : Fin i → Fin i → 𝕜,
      (Matrix.of fun a j => v j a).det = Matrix.detRowAlternating v := by
    intro v
    rw [← Matrix.det_transpose]
    rfl
  let c : Fin i → Option κ → 𝕜 := fun j o => Option.elim o 1 (ε j)
  let τ : Fin i → Option κ → κ := fun j o => Option.elim o (σ₀ j) id
  have hcol : (fun j => w (σ₀ j) + ∑ k, ε j k • w k) = fun j => ∑ o, c j o • w (τ j o) := by
    funext j
    rw [Fintype.sum_option]
    simp [c, τ]
  have h1 := (Matrix.detRowAlternating (n := Fin i) (R := 𝕜)).toMultilinearMap.map_sum
    (fun j o => c j o • w (τ j o))
  have h2 : ∀ r : Fin i → Option κ,
      (Matrix.detRowAlternating (n := Fin i) (R := 𝕜)).toMultilinearMap
        (fun j => c j (r j) • w (τ j (r j)))
      = (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j))) := by
    intro r
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    rfl
  have hpert : (Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det
      = ∑ r : Fin i → Option κ, (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j))) := by
    rw [hdet (fun j => w (σ₀ j) + ∑ k, ε j k • w k), hcol]
    exact h1.trans (Finset.sum_congr rfl (fun r _ => h2 r))
  have hbase : (Matrix.of fun a j => w (σ₀ j) a).det = Matrix.detRowAlternating (fun j => w (σ₀ j)) :=
    hdet _
  let r0 : Fin i → Option κ := fun _ => none
  have hr0 : (∏ j, c j (r0 j)) * Matrix.detRowAlternating (fun j => w (τ j (r0 j)))
      = Matrix.detRowAlternating (fun j => w (σ₀ j)) := by
    simp [c, τ, r0]
  rw [hpert, hbase, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hr0, add_sub_cancel_left]
  have hb : ∀ r : Fin i → Option κ,
      ‖(∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖
        ≤ (∏ j, ‖c j (r j)‖) * Δmax := by
    intro r
    rw [norm_mul, norm_prod]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    have := hΔ (fun j => τ j (r j))
    rwa [hdet] at this
  have hsum : ∏ j, (1 + ∑ k, ‖ε j k‖) = ∑ r : Fin i → Option κ, ∏ j, ‖c j (r j)‖ := by
    have e : ∀ j, (1 + ∑ k, ‖ε j k‖) = ∑ o, ‖c j o‖ := by
      intro j
      rw [Fintype.sum_option]
      simp [c]
    simp_rw [e]
    rw [Finset.prod_univ_sum]
    try rw [Fintype.piFinset_univ]
  have hr0n : ∏ j, ‖c j (r0 j)‖ = 1 := by simp [c, r0]
  calc ‖∑ r ∈ Finset.univ.erase r0, (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖
      ≤ ∑ r ∈ Finset.univ.erase r0, ‖(∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.univ.erase r0, (∏ j, ‖c j (r j)‖) * Δmax := Finset.sum_le_sum (fun r _ => hb r)
    _ = ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax := by
        rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ r0), hr0n, hsum]

lemma coeff_top_det {K : Type*} [CommRing K] {i : ℕ} (M : Matrix (Fin i) (Fin i) K) :
    (det (1 + (X : K[X]) • M.map C)).coeff i = M.det := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  · have e : (1 + (X : K[X]) • M.map C) = 1 - (X : K[X]) • (-M).map C := by
      have hm : (-M).map C = -(M.map C) := by
        ext a b
        simp
      rw [hm, smul_neg, sub_neg_eq_add]
    rw [e]
    change (Matrix.charpolyRev (-M)).coeff i = M.det
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, Polynomial.revAt_le (le_refl i), Nat.sub_self]
    have h := Matrix.det_eq_sign_charpoly_coeff (-M)
    rw [Fintype.card_fin, Matrix.det_neg, Fintype.card_fin] at h
    have hu : IsUnit ((-1 : K) ^ i) := (isUnit_one.neg).pow i
    exact (hu.mul_left_cancel h).symm

lemma det_mul_eq_sum_principal {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
      ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det := by
  rw [← coeff_top_det (A * B)]
  have h1 : (1 : Matrix (Fin i) (Fin i) K[X]) + (X : K[X]) • (A * B).map C
      = 1 + ((X : K[X]) • A.map C) * (B.map C) := by
    rw [Matrix.map_mul, Matrix.smul_mul]
  have h2 : (B.map C) * ((X : K[X]) • A.map C) = (X : K[X]) • (B * A).map C := by
    rw [Matrix.mul_smul]; congr 1; simp [Matrix.map_mul]
  rw [h1, det_one_add_mul_comm, h2, coeff_det_one_add_X_smul_eq_sum_minors]

lemma principal_minor_factor {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) (S : Finset (Fin n)) (hS : S.card = i) :
    ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det
      = (B.submatrix (S.orderEmbOfFin hS) id).det * (A.submatrix id (S.orderEmbOfFin hS)).det := by
  rw [← Matrix.det_submatrix_equiv_self (S.orderIsoOfFin hS).toEquiv]
  rw [show ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).submatrix
      (S.orderIsoOfFin hS).toEquiv (S.orderIsoOfFin hS).toEquiv
      = B.submatrix (S.orderEmbOfFin hS) id * A.submatrix id (S.orderEmbOfFin hS) from by
    ext a b
    simp [Matrix.mul_apply, Finset.coe_orderIsoOfFin_apply]]
  rw [Matrix.det_mul]

theorem cauchyBinetMax : CauchyBinetMax := by
  intro i N r M hM hNr
  classical
  let g : Finset (Fin N) → ℝ := fun S =>
    if h : S.card = i then ‖(M.submatrix id (S.orderEmbOfFin h)).det‖ ^ 2 else 0
  have h1 : (1 : ℂ) = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i,
      ((Mᴴ * M).submatrix (Subtype.val : S → Fin N) Subtype.val).det := by
    rw [← det_mul_eq_sum_principal M Mᴴ, hM, Matrix.det_one]
  have h2 : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i,
      ((Mᴴ * M).submatrix (Subtype.val : S → Fin N) Subtype.val).det = ((g S : ℝ) : ℂ) := by
    intro S hS
    have hc := (Finset.mem_powersetCard.1 hS).2
    rw [principal_minor_factor M Mᴴ S hc]
    simp only [g, dif_pos hc]
    have e : Mᴴ.submatrix (S.orderEmbOfFin hc) id = (M.submatrix id (S.orderEmbOfFin hc))ᴴ := by
      ext a b
      simp [Matrix.conjTranspose_apply]
    rw [e, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have h3 : (1 : ℝ) = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, g S := by
    have := h1.trans (Finset.sum_congr rfl h2)
    exact_mod_cast this
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, g S < (2 : ℝ) ^ (-(r : ℝ)) := by
    intro S hS
    have hc := (Finset.mem_powersetCard.1 hS).2
    simp only [g, dif_pos hc]
    have h4 := hcon _ (S.orderEmbOfFin hc).strictMono
    have h5 : ‖(M.submatrix id (S.orderEmbOfFin hc)).det‖ ^ 2 < ((2 : ℝ) ^ (-(r : ℝ) / 2)) ^ 2 :=
      pow_lt_pow_left₀ h4 (norm_nonneg _) (by norm_num)
    have h6 : ((2 : ℝ) ^ (-(r : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (-(r : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    exact h5.trans_eq h6
  by_cases hne : ((Finset.univ : Finset (Fin N)).powersetCard i).Nonempty
  · have h6 := Finset.sum_lt_sum_of_nonempty hne hlt
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin] at h6
    have h7 : ((N.choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.choose_le_two_pow N i
    have h8 : (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) ≤ 1 := by
      rw [← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : (N : ℝ) ≤ r := by exact_mod_cast hNr
      linarith
    have h9 : ((N.choose i : ℕ) : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at h3
    norm_num at h3

open MeasureTheory in
theorem packingCount : PackingCount := by
  intro n P δ R hδ hδR hR hsep
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero]
    have : P.card ≤ 1 := Finset.card_le_one.2 (fun a _ b _ => PiLp.ext (fun i => Fin.elim0 i))
    exact_mod_cast this
  · haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
    classical
    have hd2 : 0 < δ / 2 := by linarith
    have hV0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
      (Metric.measure_ball_pos volume _ one_pos).ne'
    have hVt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := measure_ball_lt_top.ne
    have hball : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 ≤ ρ →
        volume (Metric.ball x ρ) = ENNReal.ofReal (ρ ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      intro x ρ hρ
      rw [Measure.addHaar_ball _ _ hρ, finrank_euclideanSpace_fin]
    have hdisj : Set.PairwiseDisjoint (↑P : Set (EuclideanSpace ℝ (Fin n))) (fun x => Metric.ball x (δ / 2)) := by
      intro x hx y hy hxy
      exact Metric.ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
    have hsub : (⋃ x ∈ P, Metric.ball x (δ / 2)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + δ / 2) := by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨x, hx, hz⟩ := hz
      rw [Metric.mem_ball, dist_zero_right]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have := norm_le_norm_add_norm_sub' z x
      linarith [hR x hx]
    have hmeas : volume (⋃ x ∈ P, Metric.ball x (δ / 2)) = ∑ x ∈ P, volume (Metric.ball x (δ / 2)) :=
      measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)
    have key : ∑ x ∈ P, volume (Metric.ball x (δ / 2))
        ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + δ / 2)) := by
      rw [← hmeas]
      exact measure_mono hsub
    simp only [hball _ _ hd2.le, hball _ _ (by linarith : (0:ℝ) ≤ R + δ / 2), Finset.sum_const,
      nsmul_eq_mul] at key
    rw [← mul_assoc] at key
    have key2 := (ENNReal.mul_le_mul_iff_left hV0 hVt).1 key
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) n)] at key2
    have hfin : (R + δ / 2) ^ n ≤ (3 * R / δ) ^ n * (δ / 2) ^ n := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by linarith)
      have e : 3 * R / δ * (δ / 2) = 3 * R / 2 := by
        field_simp
      rw [e]
      linarith
    exact le_of_mul_le_mul_right (key2.trans hfin) (pow_pos hd2 n)

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.ExistsSumOfMemSpanImage
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset

section aux

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem exists_orth_decomp_of_finiteDimensional (K : Submodule ℝ V) [FiniteDimensional ℝ K]
    (a : V) : ∃ w ∈ K, ∃ z : V, (∀ p ∈ K, inner ℝ p z = 0) ∧ a = w + z := by
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  obtain ⟨w, hw, z, hz, h⟩ : ∃ w ∈ K, ∃ z ∈ K.orthogonal, a = w + z := by
    exact K.exists_add_mem_mem_orthogonal a
  refine ⟨w, hw, z, fun p hp => ?_, h⟩
  exact Submodule.inner_right_of_mem_orthogonal hp hz

theorem exists_orth_split {ι : Type*} (v : ι → V) (T : Finset ι) (a : V) :
    ∃ w ∈ Submodule.span ℝ (v '' (T : Set ι)), ∃ z : V,
      (∀ p ∈ Submodule.span ℝ (v '' (T : Set ι)), inner ℝ p z = 0) ∧ a = w + z ∧
        ‖z‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (v '' (T : Set ι))) :=
    FiniteDimensional.span_of_finite ℝ (T.finite_toSet.image v)
  obtain ⟨w, hw, z, hz, hwz⟩ :=
    exists_orth_decomp_of_finiteDimensional (Submodule.span ℝ (v '' (T : Set ι))) a
  refine ⟨w, hw, z, hz, hwz, ?_⟩
  rw [hwz, norm_add_sq_real, hz w hw]
  nlinarith [sq_nonneg ‖w‖]

private theorem exists_sum_repr_of_mem_span_image {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : ι → M) (T : Finset ι) (x : M) (hx : x ∈ Submodule.span R (v '' (T : Set ι))) :
    ∃ r : ι → R, x = ∑ i ∈ T, r i • v i := by
  classical
  let S : Submodule R M :=
    { carrier := {y | ∃ r : ι → R, y = ∑ i ∈ T, r i • v i}
      add_mem' := by
        rintro y₁ y₂ ⟨r₁, rfl⟩ ⟨r₂, rfl⟩
        exact ⟨r₁ + r₂, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c y ⟨r, rfl⟩
        exact ⟨c • r, by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]⟩ }
  have hle : Submodule.span R (v '' (T : Set ι)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    show ∃ r : ι → R, v j = ∑ i ∈ T, r i • v i
    refine ⟨fun i => if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro hjT
      exact absurd (Finset.mem_coe.mp hj) hjT
  exact hle hx

theorem nearestPlane_finset {ι : Type*} [DecidableEq ι] (v : ι → V) (T : Finset ι) :
    ∀ x ∈ Submodule.span ℝ (v '' (T : Set ι)),
      ∃ c : ι → ℤ, ‖x - ∑ i ∈ T, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ T, ‖v i‖ ^ 2 := by
  refine Finset.induction_on T ?_ ?_
  · intro x hx
    refine ⟨0, ?_⟩
    simp at hx
    subst hx
    simp
  · intro a s ha ih x hx
    obtain ⟨r, hr⟩ := exists_sum_repr_of_mem_span_image v (insert a s) x hx
    rw [Finset.sum_insert ha] at hr
    obtain ⟨w, hw, z, hz, hwz, hzle⟩ := exists_orth_split v s (v a)
    have hyK : (∑ i ∈ s, r i • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round (r a) := ⟨_, rfl⟩
    have hy'K : (∑ i ∈ s, r i • v i) + (r a - k) • w ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.add_mem _ hyK (Submodule.smul_mem _ _ hw)
    obtain ⟨c', hc'⟩ := ih _ hy'K
    have hSK : (∑ i ∈ s, (c' i : ℝ) • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    have heK := Submodule.sub_mem _ hy'K hSK
    refine ⟨fun i => if i = a then k else c' i, ?_⟩
    have hsum : ∑ i ∈ s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i
        = ∑ i ∈ s, (c' i : ℝ) • v i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hia : i ≠ a := fun h => ha (by rw [← h]; exact hi)
      rw [if_neg hia]
    show ‖x - ∑ i ∈ insert a s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i‖ ^ 2
      ≤ (1 / 4) * ∑ i ∈ insert a s, ‖v i‖ ^ 2
    rw [Finset.sum_insert ha, Finset.sum_insert ha, if_pos rfl, hsum]
    have hdecomp : x - ((k : ℝ) • v a + ∑ i ∈ s, (c' i : ℝ) • v i) =
        (r a - k) • z + ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) := by
      rw [hr, hwz]
      module
    have horth : inner ℝ ((r a - k) • z)
        ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) = 0 := by
      rw [real_inner_smul_left, real_inner_comm, hz _ heK, mul_zero]
    have hround : (r a - k) ^ 2 ≤ 1 / 4 := by
      have h1 : |r a - k| ≤ 1 / 2 := by
        rw [hk]
        exact abs_sub_round (r a)
      nlinarith [sq_abs (r a - k), abs_nonneg (r a - k),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg (r a - k))]
    rw [hdecomp, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 := mul_le_mul_of_nonneg_right hround (sq_nonneg ‖z‖)
    have h3 := mul_le_mul_of_nonneg_left hzle (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith

end aux

theorem nearestPlane : NearestPlane := by
  unfold NearestPlane
  intro V _ _ n v _ x hx
  have hx' : x ∈ Submodule.span ℝ (v '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) := by
    rwa [Finset.coe_univ, Set.image_univ]
  exact nearestPlane_finset v Finset.univ x hx'

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.FourTermSumBoundOfParameters
section
namespace Formalism.LatticeBaseChangeAlt

theorem four_term_sum_bound : FourTermSumBound := by
  intro d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP hD hR hκ h0 h1 h2 h3
  have e1 : PP ^ 2 * (D ^ 3 * κ / T) ≤ PP ^ 2 * D ^ 3 * C * k * f * b / T := by
    have : PP ^ 2 * D ^ 3 * C * k * f * b / T = PP ^ 2 * (D ^ 3 * (C * k * f * b) / T) := by ring
    rw [this]
    gcongr
  have e3 : PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga) ≤
      PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga := by
    have : PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga =
        PP ^ 2 * ((RR ^ 2 * c + 1 / T) * (C * k * f * b) / ga) := by ring
    rw [this]
    gcongr
  have tot : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + PP ^ 3 * T ≤
      f * m * b * δ₂ := by
    have : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) =
        PP ^ 2 * (D ^ 3 * κ / T) + PP ^ 2 * T * c + PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga) := by
      ring
    rw [this]
    linarith
  calc d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T
      = d * (PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + PP ^ 3 * T) := by
        ring
    _ ≤ d * (f * m * b * δ₂) := mul_le_mul_of_nonneg_left tot hd
    _ = d * f * m * b * δ₂ := by ring

theorem four_term_sum_bound_of_parameters : FourTermSumBoundOfParameters := by
  intro d PP D κ T c RR ga C k f b m δ₂ q DF g₀ hd hT hTga hPP hD hRR hq hC hk hf hb hm hδ
    hκ h0 hTlow hc hg₀ hTc hqlow hTPP hPP2
  have hga : 0 < ga := lt_of_lt_of_le hT hTga
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hK : 0 ≤ C * k * f * b := by positivity
  have hD0 : 0 ≤ D := by linarith
  have hPP1 : 1 ≤ PP := by nlinarith
  have hT1 : 1 ≤ T := by linarith
  have hRRc : RR ^ 2 * c ≤ 1 / PP ^ 2 := by
    have hP2 : 0 < PP ^ 2 := by positivity
    rw [hc, le_div_iff₀ hP2]
    have e : RR ^ 2 * (RR * PP * DF ^ 2 / q) * PP ^ 2 = RR ^ 3 * PP ^ 3 * DF ^ 2 / q := by ring
    rw [e, div_le_one hq]
    have h34 : RR ^ 3 ≤ RR ^ 4 := pow_le_pow_right₀ hRR (by norm_num)
    have : RR ^ 3 * (PP ^ 3 * DF ^ 2) ≤ RR ^ 4 * (PP ^ 3 * DF ^ 2) :=
      mul_le_mul_of_nonneg_right h34 (by positivity)
    nlinarith [this]
  have hmδ : 0 < m * δ₂ := mul_pos hm hδ
  have h1 : PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 4 := by
    rw [div_le_iff₀ hmδ] at hTlow
    rw [div_le_iff₀ hT]
    have := mul_le_mul_of_nonneg_right hTlow (mul_nonneg hf hb)
    nlinarith [this]
  have hPPq : PP ^ 2 ≤ f * m * b * δ₂ / 4 := by
    have a : PP ^ 2 * 1 ≤ PP ^ 2 * (PP * T) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith [a]
  have h2 : PP ^ 2 * T * c ≤ f * m * b * δ₂ / 4 := by
    have hTc0 : 0 ≤ T * c := mul_nonneg hT.le hc0
    have hTc1 : T * c ≤ 1 := by nlinarith
    have : PP ^ 2 * (T * c) ≤ PP ^ 2 * 1 := mul_le_mul_of_nonneg_left hTc1 (by positivity)
    nlinarith [this]
  have hside : 1 + PP ^ 2 / T ≤ PP ^ 2 * D ^ 3 := by
    have s1 : PP ^ 2 / T ≤ 1 := (div_le_one hT).2 hTPP
    have s2 : (1 : ℝ) ≤ D ^ 3 := one_le_pow₀ hD
    have s3 : PP ^ 2 * 1 ≤ PP ^ 2 * D ^ 3 := mul_le_mul_of_nonneg_left s2 (by positivity)
    linarith
  have h3 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 4 := by
    have a1 : PP ^ 2 * (RR ^ 2 * c + 1 / T) ≤ PP ^ 2 * D ^ 3 := by
      have : PP ^ 2 * (RR ^ 2 * c) ≤ PP ^ 2 * (1 / PP ^ 2) :=
        mul_le_mul_of_nonneg_left hRRc (by positivity)
      have e : PP ^ 2 * (1 / PP ^ 2) = 1 := by field_simp
      have e' : PP ^ 2 * (1 / T) = PP ^ 2 / T := by ring
      rw [mul_add, e']
      linarith
    have a2 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * (C * k * f * b) ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) :=
      mul_le_mul_of_nonneg_right a1 hK
    calc PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga
        = PP ^ 2 * (RR ^ 2 * c + 1 / T) * (C * k * f * b) / ga := by ring
      _ ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) / ga := by gcongr
      _ ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) / T := by gcongr
      _ = PP ^ 2 * D ^ 3 * C * k * f * b / T := by ring
      _ ≤ _ := h1
  exact four_term_sum_bound d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP.le hD0 (by positivity) hκ
    h0 h1 h2 h3

end Formalism.LatticeBaseChangeAlt
end

