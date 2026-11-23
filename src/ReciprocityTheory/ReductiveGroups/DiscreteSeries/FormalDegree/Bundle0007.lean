module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.LseConvexOn
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

section LSE

variable {ι : Type*} [Fintype ι]

theorem lse_pos (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (t : ℝ) :
    0 < ∑ i, w i * Real.exp (t * y i) := by
  have hex : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have h0 : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hw0 i))
    linarith
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw0 j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

theorem lse_convexOn (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∑ i, w i * Real.exp (t * y i))) := by
  refine ⟨convex_univ, fun t1 _ t2 _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set A := ∑ i, w i * Real.exp (t1 * y i) with hA
  set B := ∑ i, w i * Real.exp (t2 * y i) with hB
  have hA0 : 0 < A := lse_pos w y hw0 hw1 t1
  have hB0 : 0 < B := lse_pos w y hw0 hw1 t2
  set E := Real.exp (a * Real.log A + b * Real.log B) with hE
  have key : ∀ i, Real.exp ((a * t1 + b * t2) * y i) ≤
      (a * (Real.exp (t1 * y i) / A) + b * (Real.exp (t2 * y i) / B)) * E := by
    intro i
    have h1 := convexOn_exp.2 (Set.mem_univ (t1 * y i - Real.log A))
      (Set.mem_univ (t2 * y i - Real.log B)) ha hb hab
    simp only [smul_eq_mul] at h1
    have e1 : Real.exp (t1 * y i - Real.log A) = Real.exp (t1 * y i) / A := by
      rw [Real.exp_sub, Real.exp_log hA0]
    have e2 : Real.exp (t2 * y i - Real.log B) = Real.exp (t2 * y i) / B := by
      rw [Real.exp_sub, Real.exp_log hB0]
    rw [e1, e2] at h1
    have e3 : Real.exp ((a * t1 + b * t2) * y i) =
        Real.exp (a * (t1 * y i - Real.log A) + b * (t2 * y i - Real.log B)) * E := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    rw [e3]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hsum : ∑ i, w i * Real.exp ((a * t1 + b * t2) * y i) ≤ E := by
    calc ∑ i, w i * Real.exp ((a * t1 + b * t2) * y i)
        ≤ ∑ i, w i * ((a * (Real.exp (t1 * y i) / A) + b * (Real.exp (t2 * y i) / B)) * E) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (key i) (hw0 i))
      _ = (a * (A / A) + b * (B / B)) * E := by
          rw [hA, hB, Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
      _ = E := by rw [div_self hA0.ne', div_self hB0.ne', mul_one, mul_one, hab, one_mul]
  have hpos := lse_pos w y hw0 hw1 (a * t1 + b * t2)
  calc Real.log (∑ i, w i * Real.exp ((a * t1 + b * t2) * y i)) ≤ Real.log E :=
        Real.log_le_log hpos hsum
    _ = a * Real.log A + b * Real.log B := Real.log_exp _

theorem lse_one_le (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hw2 : ∑ i, w i * y i = 0) : 1 ≤ ∑ i, w i * Real.exp (y i) := by
  calc (1 : ℝ) = ∑ i, w i * (1 + y i) := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero]
    _ ≤ ∑ i, w i * Real.exp (y i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (by linarith [Real.add_one_le_exp (y i)]) (hw0 i))

theorem lse_lower (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hw2 : ∑ i, w i * y i = 0) {ep : ℝ} (he0 : 0 ≤ ep) (he1 : ep ≤ 1)
    (hy : ∀ i, |y i| ≤ ep / 2) :
    (∑ i, w i * y i ^ 2) / 2 * (1 - ep) ≤ Real.log (∑ i, w i * Real.exp (y i)) := by
  set V := ∑ i, w i * y i ^ 2 with hV
  have hD : 1 ≤ ∑ i, w i * Real.exp (y i) := lse_one_le w y hw0 hw1 hw2
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (sq_nonneg _))
  have hVle : V ≤ ep ^ 2 / 4 := by
    calc V ≤ ∑ i, w i * (ep / 2) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (hw0 i))
          have := sq_abs (y i)
          have h1 := hy i
          have h2 := abs_nonneg (y i)
          nlinarith
      _ = ep ^ 2 / 4 := by rw [← Finset.sum_mul, hw1]; ring

  have hterm : ∀ i, 1 + y i + y i ^ 2 * (1 / 2 - ep / 9) ≤ Real.exp (y i) := by
    intro i
    have hyi : |y i| ≤ 1 := (hy i).trans (by linarith)
    have hb := Real.exp_bound hyi (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have hb' := (abs_le.1 hb).1
    have hc : |y i| ^ 3 ≤ ep / 2 * y i ^ 2 := by
      have : |y i| ^ 3 = |y i| * y i ^ 2 := by rw [pow_succ, sq_abs]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hy i) (sq_nonneg _)
    nlinarith
  have hlow : 1 + V * (1 / 2 - ep / 9) ≤ ∑ i, w i * Real.exp (y i) := by
    calc 1 + V * (1 / 2 - ep / 9) = ∑ i, w i * (1 + y i + y i ^ 2 * (1 / 2 - ep / 9)) := by
          simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero, hV,
            Finset.sum_mul]
          refine congrArg _ (Finset.sum_congr rfl (fun i _ => by ring))
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw0 i))
  set c := V / 2 * (1 - ep) with hc
  have hc0 : 0 ≤ c := mul_nonneg (by linarith) (by linarith)
  have hc1 : c ≤ V / 2 := by nlinarith
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; nlinarith
  have hexp : Real.exp c ≤ 1 + c + c ^ 2 := by
    have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hcabs)).2
    linarith
  have hcc : c ^ 2 ≤ V * ep ^ 2 / 8 := by nlinarith
  have hfin : 1 + c + c ^ 2 ≤ ∑ i, w i * Real.exp (y i) := by
    have : c + c ^ 2 ≤ V * (1 / 2 - ep / 9) := by
      rw [hc]
      have : V * ep ^ 2 / 8 ≤ V * ep * (7 / 18) := by nlinarith
      nlinarith
    linarith
  have hpos : 0 < ∑ i, w i * Real.exp (y i) := by linarith
  rw [← Real.exp_le_exp, Real.exp_log hpos]
  linarith

end LSE

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarInv
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem polarInv_pmat_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) : pmat (-z) = -pmat z := by
  ext a b
  simp only [pmat, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp [star_neg]

theorem polarInv_Jm_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : Jm ε * pmat z * Jm ε = -pmat z := by
  ext a b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
  by_cases hab : ε a = ε b
  · have h0 : pmat z a b = 0 := by simp [pmat, hab]
    rw [h0]; simp
  · have hs : (if ε a then (1:ℂ) else -1) * (if ε b then 1 else -1) = -1 := by
      cases ha : ε a <;> cases hb : ε b <;> simp_all
    calc (if ε a then (1:ℂ) else -1) * pmat z a b * (if ε b then 1 else -1)
        = ((if ε a then (1:ℂ) else -1) * (if ε b then 1 else -1)) * pmat z a b := by ring
      _ = -pmat z a b := by rw [hs]; ring

theorem polarInv_toMK_inv {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have hu : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := k.2.1
  exact Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.mp hu)

private theorem Jm_mul_Jm_eq_oneFormalDegree (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem conjTranspose_Jm_eq_Jm (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem polarInv_key {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    Jm ε * (polarM (k, z))ᴴ * Jm ε = polarM (k⁻¹, adK k (-z)) := by
  have hK : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := k.2.1
  have hKJ : toMK k * Jm ε = Jm ε * toMK k := k.2.2
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_Jm_eq_oneFormalDegree ε
  have hJh : (Jm ε)ᴴ = Jm ε := conjTranspose_Jm_eq_Jm ε
  have hKKh : toMK k * (toMK k)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hK
  have hKhK : (toMK k)ᴴ * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.mp hK
  have hKhJ : (toMK k)ᴴ * Jm ε = Jm ε * (toMK k)ᴴ := by
    have h := congrArg Matrix.conjTranspose hKJ
    simp only [Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hKu : IsUnit (toMK k) := ⟨⟨toMK k, (toMK k)ᴴ, hKKh, hKhK⟩, rfl⟩
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hKinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_right_inv hKKh
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJJ
  have hE : (NormedSpace.exp (pmat z))ᴴ = NormedSpace.exp (pmat z) := by
    rw [← Matrix.exp_conjTranspose, (pmat_isHermitian z).eq]
  have h1 : NormedSpace.exp (Jm ε * pmat z * (Jm ε)⁻¹) =
      Jm ε * NormedSpace.exp (pmat z) * (Jm ε)⁻¹ := Matrix.exp_conj _ _ hJu
  have h2 : NormedSpace.exp (toMK k * pmat (-z) * (toMK k)⁻¹) =
      toMK k * NormedSpace.exp (pmat (-z)) * (toMK k)⁻¹ := Matrix.exp_conj _ _ hKu
  rw [hJinv, polarInv_Jm_pmat] at h1
  rw [hKinv] at h2
  rw [show polarM (k, z) = toMK k * NormedSpace.exp (pmat z) from rfl,
    show polarM (k⁻¹, adK k (-z)) = toMK k⁻¹ * NormedSpace.exp (pmat (adK k (-z))) from rfl,
    polarInv_toMK_inv, pmat_adK, h2, Matrix.conjTranspose_mul, hE, polarInv_pmat_neg, h1]
  calc Jm ε * (NormedSpace.exp (pmat z) * (toMK k)ᴴ) * Jm ε
      = Jm ε * NormedSpace.exp (pmat z) * ((toMK k)ᴴ * Jm ε) := by simp only [Matrix.mul_assoc]
    _ = Jm ε * NormedSpace.exp (pmat z) * (Jm ε * (toMK k)ᴴ) := by rw [hKhJ]
    _ = ((toMK k)ᴴ * toMK k) * (Jm ε * NormedSpace.exp (pmat z) * Jm ε) * (toMK k)ᴴ := by
        rw [hKhK, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    _ = (toMK k)ᴴ * (toMK k * (Jm ε * NormedSpace.exp (pmat z) * Jm ε) * (toMK k)ᴴ) := by
        simp only [Matrix.mul_assoc]

theorem polarInv_apply (ε : Fin n → Bool) (S : Set (UJ ε)) (hS : MeasurableSet S) :
    muPolar ε S = ∫⁻ k, ∫⁻ z, (intMuCD_eM ε '' S).indicator (1 : (Fin n → Fin n → ℂ) → ENNReal)
      (intMuCD_pM ε (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have he : MeasurableEmbedding (intMuCD_eM ε) := (isClosedEmbedding_toM ε).measurableEmbedding
  have hT : MeasurableSet (intMuCD_eM ε '' S) := he.measurableSet_image.2 hS
  let F := (intMuCD_eM ε '' S).indicator (1 : (Fin n → Fin n → ℂ) → ENNReal)
  have hF : Measurable F := measurable_one.indicator hT
  have hpm : Measurable (intMuCD_pM ε) := (polarM_continuous ε).measurable
  have hJ : Measurable (fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) :=
    ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  change Measure.comap (intMuCD_eM ε) (muPolarMat ε) S = _
  rw [he.comap_apply, ← lintegral_indicator_one hT]
  change (∫⁻ x, F x ∂(Measure.map (intMuCD_pM ε) ((dk ε).prod (volume.withDensity _)))) = _
  rw [lintegral_map hF hpm]
  refine (lintegral_prod (F ∘ intMuCD_pM ε) (hF.comp hpm).aemeasurable).trans ?_
  refine lintegral_congr fun k => ?_
  exact (lintegral_withDensity_eq_lintegral_mul _ hJ
    (hF.comp (hpm.comp measurable_prodMk_left))).trans (lintegral_congr fun _ => mul_comm _ _)

theorem muPolar_inv (ε : Fin n → Bool) : Measure.map (fun x : UJ ε => x⁻¹) (muPolar ε) = muPolar ε := by
  have hinv : Measurable (fun x : UJ ε => x⁻¹) := continuous_inv.measurable
  have hinvK : Measurable (fun x : KG ε => x⁻¹) := continuous_inv.measurable
  have hce : Topology.IsClosedEmbedding (intMuCD_eM ε) := isClosedEmbedding_toM ε
  have he : MeasurableEmbedding (intMuCD_eM ε) := hce.measurableEmbedding
  ext S hS
  rw [Measure.map_apply hinv hS, polarInv_apply ε _ (hinv hS), polarInv_apply ε S hS]
  have hT : MeasurableSet (intMuCD_eM ε '' S) := he.measurableSet_image.2 hS
  have hpt : ∀ (k : KG ε) (z : PCoord ε → ℂ),
      (intMuCD_eM ε '' ((fun x : UJ ε => x⁻¹) ⁻¹' S)).indicator
          (1 : (Fin n → Fin n → ℂ) → ENNReal) (intMuCD_pM ε (k, z)) =
        (intMuCD_eM ε '' S).indicator 1 (intMuCD_pM ε (k⁻¹, adK k (-z))) := by
    intro k z
    obtain ⟨g, hg⟩ : polarM (k, z) ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [range_toM]; exact polarM_inUJ (k, z)
    have hg' : toM g = polarM (k, z) := hg
    have e1 : intMuCD_pM ε (k, z) = intMuCD_eM ε g := hg'.symm
    have e2 : intMuCD_pM ε (k⁻¹, adK k (-z)) = intMuCD_eM ε g⁻¹ := by
      show polarM _ = toM g⁻¹
      rw [toM_inv, hg', polarInv_key]
    rw [e1, e2]
    classical
    simp only [Set.indicator_apply, he.injective.mem_set_image, Set.mem_preimage, Pi.one_apply]
  let G : KG ε × (PCoord ε → ℂ) → ENNReal := fun kz =>
    (intMuCD_eM ε '' S).indicator 1 (intMuCD_pM ε kz) * ENNReal.ofReal (Jac kz.2)
  have hpm : Measurable (intMuCD_pM ε) := (polarM_continuous ε).measurable
  have hG : Measurable G :=
    ((measurable_one.indicator hT).comp hpm).mul
      (ENNReal.measurable_ofReal.comp ((jac_continuous ε).measurable.comp measurable_snd))
  have hH : Measurable fun k => ∫⁻ w, G (k, w) := hG.lintegral_prod_right'
  have step : ∀ k : KG ε, ∫⁻ z, (intMuCD_eM ε '' ((fun x : UJ ε => x⁻¹) ⁻¹' S)).indicator 1
      (intMuCD_pM ε (k, z)) * ENNReal.ofReal (Jac z) = ∫⁻ w, G (k⁻¹, w) := by
    intro k
    have hφ : MeasurePreserving (fun z : PCoord ε → ℂ => adK k (-z)) volume volume :=
      (adK_measurePreserving k).comp (Measure.measurePreserving_neg volume)
    have hm : Measurable (fun w => G (k⁻¹, w)) := hG.comp measurable_prodMk_left
    refine Eq.trans ?_ (hφ.lintegral_comp hm)
    refine lintegral_congr fun z => ?_
    show _ = G (k⁻¹, adK k (-z))
    simp only [G, hpt, jac_adK, jac_neg]
  calc ∫⁻ k, ∫⁻ z, (intMuCD_eM ε '' ((fun x : UJ ε => x⁻¹) ⁻¹' S)).indicator 1
        (intMuCD_pM ε (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε)
      = ∫⁻ k, (fun k => ∫⁻ w, G (k, w)) ((fun x : KG ε => x⁻¹) k) ∂(dk ε) := lintegral_congr step
    _ = ∫⁻ k, (∫⁻ w, G (k, w)) ∂(Measure.map (fun x : KG ε => x⁻¹) (dk ε)) := by
        rw [lintegral_map hH hinvK]
    _ = _ := by rw [(dk_props ε).2.2.2]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumInnerBasisSqEqAdjoint
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inner_map_of_isometry {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (f : E →L[ℂ] F) (hf : ∀ x, ‖f x‖ = ‖x‖) (x y : E) :
    ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let fi : E →ₗᵢ[ℂ] F := ⟨f.toLinearMap, hf⟩
  exact fi.inner_map_map x y

theorem toMK_mem_UJset' {ε : Fin n → Bool} (k : KG ε) : toMK k ∈ UJset ε := by
  show inUJ ε (toMK k)
  first
  | exact k.1.2
  | exact k.val.property
  | exact (k : UJ ε).2

theorem toMK_inv_mul {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ * toMK k = 1 := by
  have h : toMK k⁻¹ * toMK k = toMK (k⁻¹ * k) := rfl
  rw [h, inv_mul_cancel]
  rfl

theorem op_op_inv {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (v : T.V) :
    T.op k (T.op k⁻¹ v) = v := by
  have h : (T.τ k) * (T.τ k⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 := congrArg (fun u : unitary (T.V →L[ℂ] T.V) => (u : T.V →L[ℂ] T.V) v) h
  first
  | (rw [Submonoid.coe_mul, ContinuousLinearMap.mul_apply, OneMemClass.coe_one,
      ContinuousLinearMap.one_apply] at h2; exact h2)
  | exact h2
  | (simp only [Submonoid.coe_mul, ContinuousLinearMap.mul_apply, OneMemClass.coe_one,
      ContinuousLinearMap.one_apply] at h2; exact h2)

theorem sum_inner_basis_sq_eq_adjoint {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {T : KType ε (lowK ε lam)} {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ T.V) (k : KG ε) (y : H) :
    ∑ l, ‖⟪j (b l), σ (toMK k) y⟫_ℂ‖ ^ 2 =
      ‖(ContinuousLinearMap.adjoint j) y‖ ^ 2 := by
  have hσ1 : σ (toMK k⁻¹) (σ (toMK k) y) = y := by
    have h := hF.urep.1.2 _ (toMK_mem_UJset' k⁻¹) _ (toMK_mem_UJset' k)
    rw [← ContinuousLinearMap.comp_apply, ← h, toMK_inv_mul, hF.urep.1.1]
    rfl
  have key : ∀ l, ⟪j (b l), σ (toMK k) y⟫_ℂ = ⟪b l, T.op k (ContinuousLinearMap.adjoint j y)⟫_ℂ := by
    intro l
    rw [← inner_map_of_isometry (σ (toMK k⁻¹)) (hF.urep.2.1 _ (toMK_mem_UJset' k⁻¹)), hσ1, hF.kequiv,
      ← ContinuousLinearMap.adjoint_inner_right, ← Unitary.inner_map_map (T.τ k)]
    rw [show ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) (T.op k⁻¹ (b l)) = b l from
      op_op_inv T k (b l)]
  simp_rw [key]
  rw [b.sum_sq_norm_inner_right, Unitary.norm_map]

theorem haar_univ_eq_one (ε : Fin n → Bool) : dk ε Set.univ = 1 :=
  (CompactHaarProbability.dk_isProb ε).measure_univ

theorem hsOp_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) : 0 ≤ hsOp A := by
  unfold hsOp
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem lemma6a {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) ^ 2 / d) =
      ENNReal.ofReal (cPQ ε) * ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
  classical
  let b := stdOrthonormalBasis ℂ T.V
  let c : Fin (Module.finrank ℂ T.V) → Fin (Module.finrank ℂ T.V) → Matrix (Fin n) (Fin n) ℂ → ℝ := fun i l x => ‖⟪j (b l), σ x (j (b i))⟫_ℂ‖ ^ 2
  let f : (Fin n → Fin n → ℂ) → ENNReal := fun x => ENNReal.ofReal (∑ i, ∑ l, c i l x)
  let S : Set (Fin n → Fin n → ℂ) := UJset ε
  let F : (Fin n → Fin n → ℂ) → ENNReal := S.piecewise f 0
  have hFm : Measurable F := by
    refine ContinuousOn.measurable_piecewise ?_ continuous_const.continuousOn ?_
    · refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun l _ => ?_))
      have hc : ContinuousOn (fun x : Fin n → Fin n → ℂ => σ x (j (b i))) S := hF.urep.2.2 (j (b i))
      exact ((continuousOn_const.inner hc).norm.pow 2)
    · have hS : IsClosed S := isClosed_inUJ ε
      exact hS.measurableSet
  have hbb : ∀ i, ⟪j (b i), j (b i)⟫_ℂ = 1 := by
    intro i
    rw [inner_map_of_isometry j hF.iso, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  have hc_int : ∀ i l, Integrable (fun g : Formalism.REAL.UJ ε => c i l (Formalism.MainNotions.S.umat g)) (muCD ε) ∧
      ∫ g, c i l (Formalism.MainNotions.S.umat g) ∂(muCD ε) = 1 / d := by
    intro i l
    obtain ⟨hI, hE⟩ := (hd.2 (j (b i)) (j (b l)) (j (b i)) (j (b l)))
    have hre : ∀ g : Formalism.REAL.UJ ε, RCLike.re (Formalism.MainNotions.S.coefOn (ε := ε) σ (j (b i)) (j (b l)) g *
        star (Formalism.MainNotions.S.coefOn (ε := ε) σ (j (b i)) (j (b l)) g)) = c i l (Formalism.MainNotions.S.umat g) := by
      intro g
      simp only [c, Formalism.MainNotions.S.coefOn]
      rw [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    refine ⟨hI.re.congr (Filter.Eventually.of_forall hre), ?_⟩
    rw [← integral_congr_ae (Filter.Eventually.of_forall hre), integral_re hI, hE, hbb, hbb, one_mul]
    simp
  have hL : ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) ^ 2 / d) = ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε) := by
    have hFg : ∀ g : Formalism.REAL.UJ ε,
        F (Formalism.MainNotions.S.umat g) = ENNReal.ofReal (∑ i, ∑ l, c i l (Formalism.MainNotions.S.umat g)) := by
      intro g
      have hm : (Formalism.MainNotions.S.umat g : Fin n → Fin n → ℂ) ∈ S := by
        have h : Formalism.REAL.inUJ ε (Formalism.MainNotions.S.umat g) := g.2
        unfold Formalism.REAL.inUJ Formalism.REAL.Jm at h
        show inUJ ε _
        unfold inUJ Jm
        exact h
      exact Set.piecewise_eq_of_mem S f 0 hm
    simp_rw [hFg]
    have hsum : Integrable (fun g : Formalism.REAL.UJ ε => ∑ i, ∑ l, c i l (Formalism.MainNotions.S.umat g)) (muCD ε) :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => (hc_int i l).1))
    rw [← ofReal_integral_eq_lintegral_ofReal hsum
      (Filter.Eventually.of_forall (fun g => sum_nonneg (fun i _ => sum_nonneg (fun l _ => by positivity))))]
    congr 1
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => (hc_int i l).1))]
    have hi : ∀ i, ∫ g, ∑ l, c i l (Formalism.MainNotions.S.umat g) ∂(muCD ε) = (Module.finrank ℂ T.V : ℝ) * (1 / d) := by
      intro i
      rw [integral_finsetSum _ (fun l _ => (hc_int i l).1)]
      simp only [(hc_int _ _).2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [hi, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hval : ∀ (k : KG ε) (z : PCoord ε → ℂ), ∑ i, ∑ l, c i l (polarM (k, z)) = hsOp (fF ε lam T (pmat z)) := by
    intro k z
    have hσ : σ (polarM (k, z)) = (σ (toMK k)).comp (σ (NormedSpace.exp (pmat z))) :=
      hF.urep.1.2 _ (toMK_mem_UJset' k) _ (exp_pmat_inUJ z)
    unfold hsOp
    refine sum_congr rfl (fun i _ => ?_)
    simp only [c, hσ, ContinuousLinearMap.comp_apply]
    refine (sum_inner_basis_sq_eq_adjoint hF b k _).trans ?_
    rw [← hF.formF z, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hin : ∀ (k : KG ε) (z : PCoord ε → ℂ), F (polarM (k, z)) * ENNReal.ofReal (Jac z) =
      ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    intro k z
    have hm : (polarM (k, z) : Fin n → Fin n → ℂ) ∈ S := polarM_inUJ (k, z)
    show S.piecewise f 0 (polarM (k, z)) * _ = _
    rw [Set.piecewise_eq_of_mem S f 0 hm]
    show ENNReal.ofReal (∑ i, ∑ l, c i l (polarM (k, z))) * _ = _
    rw [hval k z, ← ENNReal.ofReal_mul (hsOp_nonneg _)]
  let e : Formalism.REAL.UJ ε → (Fin n → Fin n → ℂ) := Formalism.MainNotions.S.umat
  let p : KG ε × (PCoord ε → ℂ) → (Fin n → Fin n → ℂ) := polarM
  let J : (PCoord ε → ℂ) → ENNReal := fun z => ENNReal.ofReal (Jac z)
  let ν := volume.withDensity J
  have he : MeasurableEmbedding e := (isClosedEmbedding_toM ε).measurableEmbedding
  have hp : Measurable p := (polarM_continuous ε).measurable
  have hJ : Measurable J := ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  have hrange : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range e := by
    change ∀ᵐ x ∂(Measure.map p ((dk ε).prod ν)), x ∈ Set.range e
    refine (ae_map_iff hp.aemeasurable he.measurableSet_range).2 (ae_of_all _ fun kz => ?_)
    show polarM kz ∈ Set.range (fun g : UJ ε => toM g)
    rw [range_toM]
    exact polarM_inUJ kz
  rw [hL]
  calc
    _ = ENNReal.ofReal (cPQ ε) * ∫⁻ x, F x ∂(muPolarMat ε) := by
      rw [muCD, lintegral_smul_measure, lintegral_comap_embedding he _ hrange F, smul_eq_mul]
    _ = ENNReal.ofReal (cPQ ε) * ∫⁻ kz, F (p kz) ∂((dk ε).prod ν) := by
      change _ * (∫⁻ x, F x ∂(Measure.map p ((dk ε).prod ν))) = _
      rw [lintegral_map hFm hp]
    _ = _ := by
      congr 1
      refine (lintegral_prod (μ := dk ε) (ν := ν) (F ∘ p) (hFm.comp hp).aemeasurable).trans ?_
      let I := ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z)
      calc
        _ = ∫⁻ _ : KG ε, I ∂(dk ε) := by
          refine lintegral_congr (fun k => ?_)
          refine (lintegral_withDensity_eq_lintegral_mul volume hJ
            (hFm.comp (hp.comp measurable_prodMk_left))).trans ?_
          exact lintegral_congr (fun z => (mul_comm (J z) (F (p (k, z)))).trans (hin k z))
        _ = I * dk ε Set.univ := lintegral_const I
        _ = I := by rw [haar_univ_eq_one, mul_one]

end ReciprocityTheory.ChartRestriction.DS
end
end

