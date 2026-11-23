module

public import ReciprocityTheory.ReducedBases.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReducedBases.NormGsoCompSwapRightSqMul
section
noncomputable section

namespace ReciprocityTheory.ReducedBases.T2

open Finset InnerProductSpace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

def pot (b : Fin d → E) : ℝ :=
  ∏ k, ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs b j‖ ^ 2

lemma swap_lt (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d) (hk : k ≠ j1) (l : Fin d)
    (hl : l < k) : Equiv.swap j j1 l < k := by
  by_cases h1 : l = j
  · rw [h1, Equiv.swap_apply_left]
    rw [h1] at hl
    have : k.val ≠ j1.val := fun h => hk (Fin.ext h)
    rw [Fin.lt_iff_val_lt_val] at hl ⊢
    omega
  · by_cases h2 : l = j1
    · rw [h2, Equiv.swap_apply_right]
      rw [h2] at hl
      rw [Fin.lt_iff_val_lt_val] at hl ⊢
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact hl

lemma swap_img (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d)
    (hk : k ≠ j1) : (b ∘ Equiv.swap j j1) '' Set.Iio k = b '' Set.Iio k := by
  have hs : (Equiv.swap j j1) '' Set.Iio k = Set.Iio k := by
    ext l
    simp only [Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact swap_lt j j1 hj k hk m hm
    · intro hl
      exact ⟨Equiv.swap j j1 l, swap_lt j j1 hj k hk l hl, Equiv.swap_apply_self _ _ _⟩
  rw [Set.image_comp, hs]

lemma swap_gs_other (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d)
    (hk : k ≠ j) (hk1 : k ≠ j1) : gs (b ∘ Equiv.swap j j1) k = gs b k := by
  have hkk : Equiv.swap j j1 k = k := Equiv.swap_apply_of_ne_of_ne hk hk1
  refine gs_eq_of _ _ _ ?_ ?_
  · rw [swap_img b j j1 hj k hk1]
    simp only [Function.comp_apply, hkk]
    exact b_sub_gs_mem b k
  · intro i hi
    apply inner_gs_span b k
    apply Submodule.subset_span
    exact ⟨Equiv.swap j j1 i, swap_lt j j1 hj k hk1 i hi, rfl⟩

lemma swap_gs_j (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    gs (b ∘ Equiv.swap j j1) j = gs b j1 + mu b j1 j • gs b j := by
  have hne : j ≠ j1 := fun h => by rw [Fin.ext_iff] at h; omega
  have hne' : j1 ≠ j := fun h => hne h.symm
  have hsj : Equiv.swap j j1 j = j1 := Equiv.swap_apply_left j j1
  have hI : Set.Iio j1 = insert j (Set.Iio j) := by
    ext l
    simp only [Set.mem_Iio, Set.mem_insert_iff, Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega
  have hmem := b_sub_gs_mem b j1
  rw [hI, Set.image_insert_eq, Submodule.mem_span_insert] at hmem
  obtain ⟨c, s, hs, hcs⟩ := hmem
  have hG0 : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  have hc : c = mu b j1 j := by
    have h1 : ⟪gs b j, b j1 - gs b j1⟫_ℝ = mu b j1 j * ‖gs b j‖ ^ 2 := by
      rw [inner_sub_right, gs_orth b hne, sub_zero]
      unfold mu
      rw [div_mul_cancel₀ _ hG0]
    have h2 : ⟪gs b j, b j1 - gs b j1⟫_ℝ = c * ‖gs b j‖ ^ 2 := by
      rw [hcs, inner_add_right, real_inner_smul_right, inner_gs_b_self, inner_gs_span b j hs, add_zero]
    exact mul_right_cancel₀ hG0 (h2.symm.trans h1)
  subst hc
  refine gs_eq_of _ _ _ ?_ ?_
  · rw [swap_img b j j1 hj j hne]
    simp only [Function.comp_apply, hsj]
    have he : b j1 - (gs b j1 + mu b j1 j • gs b j) = mu b j1 j • (b j - gs b j) + s := by
      rw [sub_add_eq_sub_sub, hcs, smul_sub]
      abel
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (b_sub_gs_mem b j)) hs
  · intro i hi
    have hi1 : i < j1 := lt_trans hi (by rw [Fin.lt_iff_val_lt_val]; omega)
    have hsi : Equiv.swap j j1 i = i := Equiv.swap_apply_of_ne_of_ne (ne_of_lt hi) (ne_of_lt hi1)
    simp only [Function.comp_apply, hsi]
    rw [inner_add_left, real_inner_smul_left, gs_inner_b_of_lt b hi1, gs_inner_b_of_lt b hi]
    ring

lemma norm_swap_j (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) :
    ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 = ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 := by
  have hne : j1 ≠ j := fun h => by rw [Fin.ext_iff] at h; omega
  rw [norm_add_sq_real, real_inner_smul_right, gs_orth b hne, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring

lemma norm_gso_comp_swap_right_sq_mul (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    ‖gs (b ∘ Equiv.swap j j1) j1‖ ^ 2 * ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 =
      ‖gs b j‖ ^ 2 * ‖gs b j1‖ ^ 2 := by
  have hne : j ≠ j1 := fun h => by rw [Fin.ext_iff] at h; omega
  have hjlt : j < j1 := by rw [Fin.lt_iff_val_lt_val]; omega
  have hb' : LinearIndependent ℝ (b ∘ Equiv.swap j j1) := hb.comp _ (Equiv.injective _)
  have hu := swap_gs_j b hb j j1 hj
  have hN := norm_swap_j b j j1 hj
  have hN0 : ‖gs (b ∘ Equiv.swap j j1) j‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero _ hb' j))
  have hG0 : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  have hv : gs (b ∘ Equiv.swap j j1) j1 = gs b j -
      (mu b j1 j * ‖gs b j‖ ^ 2 / ‖gs (b ∘ Equiv.swap j j1) j‖ ^ 2) • gs (b ∘ Equiv.swap j j1) j := by
    refine gs_eq_of _ _ _ ?_ ?_
    · have hmono : span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j) ≤
          span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) :=
        Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (le_of_lt hjlt)))
      have hbj : (b ∘ Equiv.swap j j1) j ∈ span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) :=
        Submodule.subset_span ⟨j, hjlt, rfl⟩
      have hgs : gs (b ∘ Equiv.swap j j1) j ∈ span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) := by
        have h := Submodule.sub_mem _ hbj (hmono (b_sub_gs_mem (b ∘ Equiv.swap j j1) j))
        rwa [sub_sub_cancel] at h
      have hB : b j - gs b j ∈ span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) := by
        apply hmono
        rw [swap_img b j j1 hj j hne]
        exact b_sub_gs_mem b j
      have hbj1 : (b ∘ Equiv.swap j j1) j1 = b j := by simp [Equiv.swap_apply_right]
      rw [hbj1]
      have he : ∀ (t : ℝ) (x : E), b j - (gs b j - t • x) = (b j - gs b j) + t • x := by
        intro t x; abel
      rw [he]
      exact Submodule.add_mem _ hB (Submodule.smul_mem _ _ hgs)
    · intro i hi
      have hij : i ≤ j := by
        rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at hi; omega
      rcases lt_or_eq_of_le hij with h | h
      · have hsi : Equiv.swap j j1 i = i :=
          Equiv.swap_apply_of_ne_of_ne (ne_of_lt h) (ne_of_lt (lt_trans h hjlt))
        rw [inner_sub_left, real_inner_smul_left, gs_inner_b_of_lt _ h]
        simp only [Function.comp_apply, hsi, gs_inner_b_of_lt b h]
        ring
      · rw [h, inner_sub_left, real_inner_smul_left, inner_gs_b_self (b ∘ Equiv.swap j j1) j]
        have hsj : (b ∘ Equiv.swap j j1) j = b j1 := by simp
        have hmu : ⟪gs b j, b j1⟫_ℝ = mu b j1 j * ‖gs b j‖ ^ 2 := by
          unfold mu
          rw [div_mul_cancel₀ _ hG0]
        rw [hsj, hmu, div_mul_cancel₀ _ hN0, sub_self]
  have hip : ⟪gs b j, gs (b ∘ Equiv.swap j j1) j⟫_ℝ = mu b j1 j * ‖gs b j‖ ^ 2 := by
    rw [hu, inner_add_right, real_inner_smul_right, gs_orth b hne, real_inner_self_eq_norm_sq]
    ring
  have hN' : ‖gs (b ∘ Equiv.swap j j1) j‖ ^ 2 = ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 := by
    rw [hu, hN]
  rw [hv, ← hu, norm_sub_sq_real, real_inner_smul_right, hip, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, hN']
  have hD : ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 ≠ 0 := hN' ▸ hN0
  have key : mu b j1 j * ‖gs b j‖ ^ 2 / (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) *
      (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) = mu b j1 j * ‖gs b j‖ ^ 2 :=
    div_mul_cancel₀ _ hD
  linear_combination (mu b j1 j * ‖gs b j‖ ^ 2 / (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) *
      (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) - mu b j1 j * ‖gs b j‖ ^ 2) * key

private lemma prod_filter_le_ite_eq_of_mul_eq_one (j j1 : Fin d) (hj : j1.val = j.val + 1) (A B : ℝ) (hAB : A * B = 1)
    (k : Fin d) :
    ∏ i ∈ univ.filter (fun i : Fin d => i ≤ k),
        ((if i = j then A else 1) * (if i = j1 then B else 1)) = if k = j then A else 1 := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_trichotomy k j with h | h | h
  · have h1 : ¬ j ≤ k := not_le.mpr h
    have h2 : ¬ j1 ≤ k := by
      rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at h; omega
    rw [if_neg h1, if_neg h2, if_neg (ne_of_lt h), one_mul]
  · have h2 : ¬ j1 ≤ j := by rw [Fin.le_iff_val_le_val]; omega
    rw [h, if_pos le_rfl, if_neg h2, if_pos rfl, mul_one]
  · have h1 : j ≤ k := le_of_lt h
    have h2 : j1 ≤ k := by
      rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at h; omega
    rw [if_pos h1, if_pos h2, if_neg (ne_of_gt h), hAB]

lemma pot_swap (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    pot (b ∘ Equiv.swap j j1) =
      pot b * (‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2) := by
  have hne : j ≠ j1 := fun h => by rw [Fin.ext_iff] at h; omega
  have hb' : LinearIndependent ℝ (b ∘ Equiv.swap j j1) := hb.comp _ (Equiv.injective _)
  have hG0 : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  have hU0 : ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 ≠ 0 := by
    rw [← swap_gs_j b hb j j1 hj]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero _ hb' j))
  have hf : ∀ i, ‖gs (b ∘ Equiv.swap j j1) i‖ ^ 2 =
      ‖gs b i‖ ^ 2 * ((if i = j then ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2 else 1) *
        (if i = j1 then ‖gs b j‖ ^ 2 / ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 else 1)) := by
    intro i
    by_cases h1 : i = j
    · rw [h1, if_pos rfl, if_neg hne, swap_gs_j b hb j j1 hj, mul_one, mul_comm,
        div_mul_cancel₀ _ hG0]
    · by_cases h2 : i = j1
      · rw [h2, if_neg (Ne.symm hne), if_pos rfl, one_mul, mul_div_assoc', eq_div_iff hU0]
        linear_combination norm_gso_comp_swap_right_sq_mul b hb j j1 hj
      · rw [if_neg h1, if_neg h2, swap_gs_other b j j1 hj i h1 h2]
        ring
  have hAB : ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2 *
      (‖gs b j‖ ^ 2 / ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2) = 1 := by
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hG0 hU0)]
    ring
  have hk : ∀ k : Fin d, ∏ i ∈ univ.filter (fun i : Fin d => i ≤ k),
      ‖gs (b ∘ Equiv.swap j j1) i‖ ^ 2 =
      (∏ i ∈ univ.filter (fun i : Fin d => i ≤ k), ‖gs b i‖ ^ 2) *
        (if k = j then ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2 else 1) := by
    intro k
    rw [← prod_filter_le_ite_eq_of_mul_eq_one j j1 hj _ _ hAB k, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hf i)
  unfold pot
  rw [Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib, Finset.prod_ite_eq' univ j,
    if_pos (Finset.mem_univ j)]

end ReciprocityTheory.ReducedBases.T2

end
end

-- bundled from ReciprocityTheory.ReducedBases.SizeReduce
section
noncomputable section

namespace ReciprocityTheory.ReducedBases.T2

open Finset InnerProductSpace Submodule

lemma span_tri {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {d : ℕ} (v : Fin d → M)
    (W : Fin d → Fin d → R) (hW : ∀ i l, i ≤ l → W i l = 0) (S : Set (Fin d))
    (hS : ∀ i ∈ S, ∀ l < i, l ∈ S) :
    span R (v '' S) = span R ((fun i => v i - ∑ l, W i l • v l) '' S) := by
  set w : Fin d → M := fun i => v i - ∑ l, W i l • v l with hw
  have key : ∀ i, i ∈ S → v i ∈ span R (w '' S) := by
    intro i
    refine WellFoundedLT.induction (motive := fun i => i ∈ S → v i ∈ span R (w '' S)) i ?_
    intro i ih hi
    have hv : v i = w i + ∑ l, W i l • v l := (sub_add_cancel _ _).symm
    rw [hv]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
      (Submodule.sum_mem _ fun l _ => ?_)
    by_cases hl : l < i
    · exact Submodule.smul_mem _ _ (ih l hl (hS i hi l hl))
    · rw [hW i l (not_lt.mp hl), zero_smul]
      exact Submodule.zero_mem _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact key i hi
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    show v i - ∑ l, W i l • v l ∈ span R (v '' S)
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
      (Submodule.sum_mem _ fun l _ => ?_)
    by_cases hl : l < i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hS i hi l hl, rfl⟩)
    · rw [hW i l (not_lt.mp hl), zero_smul]
      exact Submodule.zero_mem _

private lemma span_gs_Iio_le_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) (j : Fin d) : span ℝ (gs b '' Set.Iio j) ≤ (ℝ ∙ gs b j)ᗮ := by
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    (gramSchmidt_orthogonal (𝕜 := ℝ) (f := b) (ne_of_lt hi).symm)

private lemma sub_gs_mem_span_gs_Iio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) (j : Fin d) : b j - gs b j ∈ span ℝ (gs b '' Set.Iio j) := by
  have h := gramSchmidt_def'' (𝕜 := ℝ) (f := b) (n := j)
  nth_rewrite 1 [h]
  rw [add_sub_cancel_left]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

private lemma mu_eq_zero_of_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) {l j : Fin d} (hlj : l < j) : mu b l j = 0 := by
  have hm : b l ∈ span ℝ (gs b '' Set.Iio j) := by
    have h1 := mem_span_gramSchmidt (𝕜 := ℝ) (f := b) (le_refl l)
    refine Submodule.span_mono ?_ h1
    exact Set.image_mono (fun i hi => lt_of_le_of_lt hi hlj)
  have h0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (span_gs_Iio_le_orthogonal b j hm)
  simp only [mu]
  rw [h0, zero_div]

private lemma mu_diag_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) (hli : LinearIndependent ℝ b) (j : Fin d) : mu b j j = 1 := by
  have hne : gs b j ≠ 0 := gramSchmidt_ne_zero (𝕜 := ℝ) (n := j) hli
  have h0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (span_gs_Iio_le_orthogonal b j (sub_gs_mem_span_gs_Iio b j))
  rw [inner_sub_right] at h0
  simp only [mu]
  rw [sub_eq_zero.mp h0, real_inner_self_eq_norm_sq]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))

private lemma gs_sub_sum_lower_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) (c : Fin d → Fin d → ℝ) (hc : ∀ i l, i ≤ l → c i l = 0) :
    gs (fun i => b i - ∑ l, c i l • b l) = gs b := by
  set b' : Fin d → E := fun i => b i - ∑ l, c i l • b l with hb'
  funext n
  have hV : span ℝ (b' '' Set.Iio n) = span ℝ (b '' Set.Iio n) :=
    (span_tri b c hc (Set.Iio n) (fun i hi l hl => lt_trans hl hi)).symm
  have hV' : span ℝ (gs b' '' Set.Iio n) = span ℝ (gs b '' Set.Iio n) := by
    rw [span_gramSchmidt_Iio, span_gramSchmidt_Iio, hV]
  have hu : gs b n - gs b' n ∈ span ℝ (gs b '' Set.Iio n) := by
    have e1 : gs b n - gs b' n = (b' n - gs b' n) - (b n - gs b n) + (b n - b' n) := by abel
    rw [e1]
    refine add_mem (sub_mem ?_ (sub_gs_mem_span_gs_Iio b n)) ?_
    · rw [← hV']
      exact sub_gs_mem_span_gs_Iio b' n
    · rw [span_gramSchmidt_Iio]
      show b n - (b n - ∑ l, c n l • b l) ∈ span ℝ (b '' Set.Iio n)
      rw [sub_sub_cancel]
      refine Submodule.sum_mem _ fun l _ => ?_
      by_cases hl : l < n
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hl, rfl⟩)
      · rw [hc n l (not_lt.mp hl), zero_smul]
        exact Submodule.zero_mem _
  have hu' : gs b n - gs b' n ∈ span ℝ (gs b' '' Set.Iio n) := by
    rw [hV']
    exact hu
  have hu1 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (span_gs_Iio_le_orthogonal b n hu)
  have hu2 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (span_gs_Iio_le_orthogonal b' n hu')
  have h3 := inner_sub_left (𝕜 := ℝ) (gs b n) (gs b' n) (gs b n - gs b' n)
  rw [hu1, hu2, sub_zero] at h3
  have h4 := inner_self_eq_zero.mp h3
  exact (sub_eq_zero.mp h4).symm

private lemma exists_basis_sub_sum_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] E)
    (hli : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), LinearIndependent ℝ (fun i => f (e i)))
    (e0 : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (W : Fin d → Fin d → ℤ)
    (hW : ∀ i l, i ≤ l → W i l = 0) :
    ∃ e1 : Module.Basis (Fin d) ℤ (Fin d → ℤ), ∀ i, e1 i = e0 i - ∑ l, W i l • e0 l := by
  set v : Fin d → (Fin d → ℤ) := fun i => e0 i - ∑ l, W i l • e0 l with hv
  have hfv : (fun i => f (v i)) = fun i => f (e0 i) - ∑ l, (W i l : ℝ) • f (e0 l) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hv, map_sub, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  have hspR : span ℝ (Set.range (fun i => f (v i))) = span ℝ (Set.range (fun i => f (e0 i))) := by
    rw [hfv, ← Set.image_univ, ← Set.image_univ]
    exact (span_tri (fun i => f (e0 i)) (fun i l => (W i l : ℝ)) (fun i l h => by simp [hW i l h])
      Set.univ (fun i _ l _ => Set.mem_univ l)).symm
  have hliR : LinearIndependent ℝ (fun i => f (v i)) := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspR]
    exact linearIndependent_iff_card_eq_finrank_span.mp (hli e0)
  have hliZ : LinearIndependent ℤ v :=
    LinearIndependent.of_comp f (hliR.restrict_scalars
      (fun (a b : ℤ) (h : a • (1 : ℝ) = b • (1 : ℝ)) => by simpa using h))
  have hspZ : ⊤ ≤ span ℤ (Set.range v) := by
    have h := span_tri e0 W hW Set.univ (fun i _ l _ => Set.mem_univ l)
    rw [Set.image_univ, Set.image_univ, e0.span_eq] at h
    exact le_of_eq h
  exact ⟨Module.Basis.mk hliZ hspZ, fun i => Module.Basis.mk_apply hliZ hspZ i⟩

private lemma exists_basis_size_reduce_column {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] E)
    (hli : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), LinearIndependent ℝ (fun i => f (e i)))
    (e0 : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d) :
    ∃ e1 : Module.Basis (Fin d) ℤ (Fin d → ℤ),
      gs (fun i => f (e1 i)) = gs (fun i => f (e0 i)) ∧
      (∀ i, j < i → |mu (fun i => f (e1 i)) i j| ≤ 1 / 2) ∧
      ∀ i j', j < j' → mu (fun i => f (e1 i)) i j' = mu (fun i => f (e0 i)) i j' := by
  set b : Fin d → E := fun i => f (e0 i) with hb
  obtain ⟨e1, he1⟩ := exists_basis_sub_sum_lower f hli e0
    (fun i l => if l = j ∧ j < i then round (mu b i j) else 0)
    (fun i l h => if_neg (by rintro ⟨rfl, h2⟩; exact absurd h (not_le.mpr h2)))
  have hfe1 : (fun i => f (e1 i)) = fun i => b i -
      ∑ l, ((if l = j ∧ j < i then round (mu b i j) else 0 : ℤ) : ℝ) • b l := by
    funext i
    rw [he1 i]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_zsmul, Int.cast_smul_eq_zsmul, hb]
  have hsum : ∀ i, ∑ l, ((if l = j ∧ j < i then round (mu b i j) else 0 : ℤ) : ℝ) • b l
      = ((if j < i then round (mu b i j) else 0 : ℤ) : ℝ) • b j := by
    intro i
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hfe : ∀ i, f (e1 i) = b i - ((if j < i then round (mu b i j) else 0 : ℤ) : ℝ) • b j := by
    intro i
    have h := congrFun hfe1 i
    rw [h, hsum i]
  have hgs : gs (fun i => f (e1 i)) = gs b := by
    rw [hfe1]
    exact gs_sub_sum_lower_smul b (fun i l => ((if l = j ∧ j < i then round (mu b i j) else 0 : ℤ) : ℝ))
      (fun i l h => by
        show ((if l = j ∧ j < i then round (mu b i j) else 0 : ℤ) : ℝ) = 0
        rw [if_neg (by rintro ⟨rfl, h2⟩; exact absurd h (not_le.mpr h2)), Int.cast_zero])
  have hmu : ∀ i j', mu (fun i => f (e1 i)) i j' =
      mu b i j' - ((if j < i then round (mu b i j) else 0 : ℤ) : ℝ) * mu b j j' := by
    intro i j'
    have hfi := hfe i
    generalize ((if j < i then round (mu b i j) else 0 : ℤ) : ℝ) = r at hfi ⊢
    simp only [mu]
    rw [hgs, hfi, inner_sub_right, inner_smul_right]
    ring
  refine ⟨e1, hgs, fun i hi => ?_, fun i j' hj' => ?_⟩
  · rw [hmu, if_pos hi, mu_diag_eq_one b (hli e0) j, mul_one]
    exact abs_sub_round _
  · rw [hmu, mu_eq_zero_of_lt b hj', mul_zero, sub_zero]

lemma size_reduce {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] E)
    (hli : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), LinearIndependent ℝ (fun i => f (e i)))
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    ∃ e' : Module.Basis (Fin d) ℤ (Fin d → ℤ), gs (fun i => f (e' i)) = gs (fun i => f (e i)) ∧
      ∀ i j : Fin d, j < i → |mu (fun i => f (e' i)) i j| ≤ 1 / 2 := by
  have key : ∀ k : ℕ, ∃ e' : Module.Basis (Fin d) ℤ (Fin d → ℤ),
      gs (fun i => f (e' i)) = gs (fun i => f (e i)) ∧
      ∀ i j : Fin d, d ≤ j.val + k → j < i → |mu (fun i => f (e' i)) i j| ≤ 1 / 2 := by
    intro k
    induction k with
    | zero => exact ⟨e, rfl, fun i j h _ => absurd h (by have := j.isLt; omega)⟩
    | succ k ih =>
      obtain ⟨e', hgs', hred⟩ := ih
      by_cases hk : k < d
      · obtain ⟨e'', hgs'', hred'', hsame⟩ := exists_basis_size_reduce_column f hli e' ⟨d - k - 1, by omega⟩
        refine ⟨e'', hgs''.trans hgs', fun i j hj hji => ?_⟩
        by_cases hjv : j.val = d - k - 1
        · have hj0 : j = ⟨d - k - 1, by omega⟩ := Fin.ext hjv
          rw [hj0] at hji ⊢
          exact hred'' i hji
        · have hlt : (⟨d - k - 1, by omega⟩ : Fin d) < j := by
            rw [Fin.lt_iff_val_lt_val]
            show d - k - 1 < j.val
            omega
          rw [hsame i j hlt]
          exact hred i j (by omega) hji
      · exact ⟨e', hgs', fun i j _ hji => hred i j (by omega) hji⟩
  obtain ⟨e', hgs', hred⟩ := key d
  exact ⟨e', hgs', fun i j hji => hred i j (by omega) hji⟩

end ReciprocityTheory.ReducedBases.T2

end
end

