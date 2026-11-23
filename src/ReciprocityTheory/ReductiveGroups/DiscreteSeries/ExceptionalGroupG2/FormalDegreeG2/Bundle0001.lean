module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.RhoNSubNab
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdConst
section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_ncProd (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ¬ ε a = ε b), f a b =
      ∏ ab : PCoord ε, f ab.1.2 ab.1.1 := by
  have e1 : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ¬ ε a = ε b), f a b =
      ∏ x ∈ univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ¬ ε x.1 = ε x.2), f x.1 x.2 := by
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    simp_rw [Finset.prod_filter]
  rw [e1, ← Finset.prod_subtype (univ.filter (fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2))
    (fun x => by simp) (fun x : Fin n × Fin n => f x.2 x.1)]
  apply Finset.prod_nbij' Prod.swap Prod.swap
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at h ⊢
    exact ⟨h.1, fun e => h.2 e.symm⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at h ⊢
    exact ⟨h.1, fun e => h.2 e.symm⟩
  · intro x _; rfl
  · intro x _; rfl
  · intro x _; rfl

theorem fdc_vand_split (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    Vand μ = (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), (μ a - μ b)) *
      ∏ ab : PCoord ε, (μ ab.1.2 - μ ab.1.1) := by
  rw [← fdc_ncProd ε (fun a b => μ a - μ b), ← Finset.prod_mul_distrib]
  unfold Vand
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter_mul_prod_filter_not (univ.filter (fun b : Fin n => a < b)) (fun b => ε a = ε b),
    Finset.filter_filter, Finset.filter_filter]

theorem pi_weight_at_zero_eq (ε : Fin n → Bool) :
    PiW ε 0 = Real.pi ^ (pOf ε * qOf ε) / ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)) := by
  unfold PiW wab
  simp only [Pi.zero_apply, sub_zero, zero_add]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, card_PCoord]

theorem fdc_ncpos (ε : Fin n → Bool) :
    0 < ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)) := by
  refine Finset.prod_pos fun ab _ => sub_pos.2 ?_
  exact_mod_cast ab.2.1

theorem fdc_tend1 (α k m : ℝ) (hm : 0 < m) :
    Tendsto (fun t : ℕ => (α + (t : ℝ) * m + k) / (α + (t : ℝ) * m)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℕ => α + (t : ℝ) * m) atTop atTop :=
    tendsto_atTop_add_const_left _ α (tendsto_natCast_atTop_atTop.atTop_mul_const hm)
  have h2 : Tendsto (fun t : ℕ => k / (α + (t : ℝ) * m)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [h.eventually_gt_atTop 0] with t ht
  field_simp

theorem fdc_tend2 (α m : ℝ) (hm : 0 < m) :
    Tendsto (fun t : ℕ => (t : ℝ) / (α + (t : ℝ) * m)) atTop (𝓝 (1 / m)) := by
  have h : Tendsto (fun t : ℕ => α + (t : ℝ) * m) atTop atTop :=
    tendsto_atTop_add_const_left _ α (tendsto_natCast_atTop_atTop.atTop_mul_const hm)
  have h3 : Tendsto (fun t : ℕ => α / (t : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h4 := (tendsto_const_nhds (x := (1 : ℝ))).div (h3.add_const m) (by rw [zero_add]; exact hm.ne')
  rw [zero_add] at h4
  refine h4.congr' ?_
  filter_upwards [h.eventually_gt_atTop 0, eventually_gt_atTop 0] with t ht ht0
  have : (0 : ℝ) < t := by exact_mod_cast ht0
  show (1:ℝ) / (α / (t:ℝ) + m) = (t:ℝ) / (α + (t:ℝ) * m)
  rw [div_add' _ _ _ this.ne', one_div_div, mul_comm m]

theorem formal_degree_constant_eq {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (d : ℕ → ℝ)
    (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (h1 : ∀ t, d t / Vand (lamT lam t) = d 0 / Vand lam) (hd0 : 0 < d 0)
    (hup : Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / d t)) Filter.atTop ≤ ENNReal.ofReal (cPQ ε * PiW ε 0))
    (hlow : ENNReal.ofReal (cPQ ε * PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / d t)) Filter.atTop) :
    d 0 = dimVlam lam := by
  have hV := vand_pos hlam.1
  have hVt : ∀ t, 0 < Vand (lamT lam t) := fun t => vand_pos (strictAnti_lamT hlam.1 t)
  have hFp : 0 < (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) :=
    mul_pos (volU_factProd_pos _) (volU_factProd_pos _)
  have hP := fdc_ncpos ε
  have hform : ∀ t : ℕ, (t : ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) / d t =
      Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ))) *
        (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b),
          ((lamT lam t a - lamT lam t b + (nab ε a b : ℝ)) / (lamT lam t a - lamT lam t b))) *
        ∏ ab : PCoord ε, ((t : ℝ) / (lamT lam t ab.1.2 - lamT lam t ab.1.1)) := by
    intro t
    have hsplit := fdc_vand_split ε (lamT lam t)
    have hd : d t = d 0 / Vand lam * Vand (lamT lam t) := by
      have := h1 t; rw [div_eq_iff (hVt t).ne'] at this; exact this
    have hne : Vand (lamT lam t) ≠ 0 := (hVt t).ne'
    rw [hsplit] at hne
    have hQ := left_ne_zero_of_mul hne
    have hPn := right_ne_zero_of_mul hne
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, card_PCoord]
    rw [hd, lemma7 (T t), hsplit]
    field_simp
  have hR1 : Tendsto (fun t : ℕ => ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b),
      ((lamT lam t a - lamT lam t b + (nab ε a b : ℝ)) / (lamT lam t a - lamT lam t b))) atTop
      (𝓝 (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), (1 : ℝ))) := by
    refine tendsto_finsetProd _ fun a _ => tendsto_finsetProd _ fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [lamT_sub]
    refine fdc_tend1 _ _ _ (sub_pos.2 ?_)
    exact_mod_cast hb.1
  have hR2 : Tendsto (fun t : ℕ => ∏ ab : PCoord ε, ((t : ℝ) / (lamT lam t ab.1.2 - lamT lam t ab.1.1))) atTop
      (𝓝 (∏ ab : PCoord ε, 1 / (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)))) := by
    refine tendsto_finsetProd _ fun ab _ => ?_
    simp only [lamT_sub]
    refine fdc_tend2 _ _ (sub_pos.2 ?_)
    exact_mod_cast ab.2.1
  have hX := ((tendsto_const_nhds (x := Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
      ∏ i ∈ range (qOf ε), (i.factorial : ℝ))))).mul hR1).mul hR2
  have hval : Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ))) *
        (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), (1 : ℝ)) *
        (∏ ab : PCoord ε, 1 / (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ))) =
      Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
        ∏ i ∈ range (qOf ε), (i.factorial : ℝ))) * (1 / ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ))) := by
    simp only [Finset.prod_const_one, mul_one, Finset.prod_div_distrib]
  rw [hval] at hX
  have hX' := hX.congr (fun t => (hform t).symm)
  have hE := ENNReal.tendsto_ofReal hX'
  have e1 := hE.limsup_eq
  have e2 := hE.liminf_eq
  rw [e1] at hup
  rw [e2] at hlow
  have hC : 0 ≤ cPQ ε * PiW ε 0 := by
    rw [pi_weight_at_zero_eq]; unfold cPQ
    have := volU_factProd_pos n
    have := volU_factProd_pos (pOf ε)
    have := volU_factProd_pos (qOf ε)
    positivity
  have hL : 0 ≤ Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
      ∏ i ∈ range (qOf ε), (i.factorial : ℝ))) * (1 / ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ))) := by
    positivity
  have heq := (ENNReal.ofReal_eq_ofReal_iff hL hC).1 (le_antisymm hup hlow)
  rw [pi_weight_at_zero_eq] at heq
  unfold cPQ at heq
  have hpi : 0 < Real.pi ^ (pOf ε * qOf ε) := pow_pos Real.pi_pos _
  have hI := volU_factProd_pos n
  rw [dimVlam_eq_vand hlam.1]
  field_simp at heq
  field_simp
  nlinarith [heq]

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdLower
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem formal_degree_liminf_lower_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (hlim : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ))) :
    ENNReal.ofReal (PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z))
      Filter.atTop := by
  have hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z) =
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2 * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have hs : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht')
    rw [lintegral_pcoord_smul _ hs, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1 := by
      rw [inv_pow, pow_mul (Real.sqrt _) 2, Real.sq_sqrt ht'.le, mul_inv_cancel₀ (pow_ne_zero _ ht'.ne')]
    rw [e, ENNReal.ofReal_one, one_mul]
  rw [Filter.liminf_congr (Filter.eventually_atTop.2 ⟨1, hscale⟩)]
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2 * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) := by
    intro t
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    exact ((continuous_norm.comp ((fdl_inner_continuous _ (T t) _ _).comp (continuous_const_smul _))).pow 2).mul
      ((jac_continuous ε).comp (continuous_const_smul _))
  refine le_trans ?_ (lintegral_liminf_le hmeas)
  rw [← fdl_gauss ε]
  refine lintegral_mono fun y => ?_
  have h1 : Filter.Tendsto (fun t : ℕ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
      (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) Filter.atTop
      (nhds (ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)))) := by
    have h2 : Filter.Tendsto (fun t : ℕ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) Filter.atTop
        (nhds (ENNReal.ofReal (‖((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)‖ ^ 2))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)).tendsto _).comp (hlim y)
    have e : ‖((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)‖ ^ 2 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, ← Real.exp_add]
      congr 1
      ring
    rw [e] at h2
    exact h2
  rw [← h1.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun t => ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_right (sq_nonneg _) (jac_ge_one _)))

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdPointwise
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem trace_dMat_pmat {ε : Fin n → Bool} (y : PCoord ε → ℂ) : trace (Lap.Base.dMat (Dvec n) * pmat y) = 0 := by
  simp only [Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [pmat]

theorem pmat_herm_apply {ε : Fin n → Bool} (y : PCoord ε → ℂ) (a b : Fin n) :
    pmat y b a = star (pmat y a b) := by
  simp only [pmat]
  by_cases h1 : a < b ∧ ε b ≠ ε a
  · have h2 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => lt_asymm h.1 h1.1
    simp only [dif_pos h1, dif_neg h2, star_star]
  · by_cases h2 : b < a ∧ ε a ≠ ε b
    · simp only [dif_neg h1, dif_pos h2]
    · simp only [dif_neg h1, dif_neg h2, star_zero]

theorem sum_pairs_pmat_fp {ε : Fin n → Bool} (w : Fin n → Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      ∑ ab : PCoord ε, w ab.1.1 ab.1.2 * ‖z ab‖ ^ 2 := by
  classical
  have key : ∀ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      (if h : x.2 < x.1 ∧ ε x.1 ≠ ε x.2 then w x.1 x.2 * ‖z ⟨x, h⟩‖ ^ 2 else 0) := by
    rintro ⟨a, b⟩
    dsimp only
    by_cases h : b < a ∧ ε a ≠ ε b
    · rw [dif_pos h, if_pos h.1]
      have hp : pmat z a b = z ⟨(a, b), h⟩ := by
        simp only [pmat, dif_pos h]
      rw [hp]
    · rw [dif_neg h]
      split_ifs with hab
      · have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h' => lt_asymm hab h'.1
        have hp : pmat z a b = 0 := by
          simp only [pmat, dif_neg h, dif_neg h2]
        rw [hp]; simp
      · rfl
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  rw [← Finset.sum_filter_of_ne (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2)
    (fun x _ hx => by
      by_contra h
      exact hx (dif_neg h))]
  rw [Finset.sum_subtype (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2) _
    (fun x => by simp)]
  refine Finset.sum_congr rfl fun ab _ => ?_
  exact dif_pos ab.2

private theorem pmat_apply_eq_zero_of_sign_eq {ε : Fin n → Bool} (y : PCoord ε → ℂ) {a b : Fin n} (he : ε a = ε b) :
    pmat y a b = 0 := by
  simp only [pmat]
  rw [dif_neg (fun h => h.2 he), dif_neg (fun h => h.2 he.symm)]

theorem qForm_term {ε : Fin n → Bool} (y : PCoord ε → ℂ) (a b : Fin n) :
    -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) =
      (((if b < a then (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * ‖pmat y a b‖ ^ 2 else 0 : ℝ)) : ℂ) := by
  have hD : ((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ) = ((((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) : ℝ) : ℂ) := by
    simp only [Dvec]; push_cast; ring
  by_cases h : b < a ∧ ε a ≠ ε b
  · have hin : Lap.Base.InNM ε (Dvec n) b a := Or.inr h
    have hN : Lap.Base.partNM ε (Dvec n) (pmat y) b a = pmat y b a := by
      rw [Lap.Base.partNM, Matrix.of_apply, if_pos hin]
    rw [hN, if_pos h.1, hD, pmat_herm_apply y a b, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  · have h0 : pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a = 0 := by
      rw [Lap.Base.partNM, Matrix.of_apply]
      split_ifs with hin
      · rcases hin with ⟨_, he, _⟩ | h'
        · rw [pmat_apply_eq_zero_of_sign_eq y he, zero_mul]
        · exact absurd h' h
      · exact mul_zero _
    rw [h0, mul_zero, neg_zero]
    split_ifs with hba
    · have he : ε a = ε b := by
        by_contra he
        exact h ⟨hba, he⟩
      rw [pmat_apply_eq_zero_of_sign_eq y he]; simp
    · simp

theorem qForm_pmat {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Lap.Base.qForm ε (Dvec n) (pmat y) = ((Qf (0 : Fin n → ℝ) y : ℝ) : ℂ) := by
  have h1 : Lap.Base.qForm ε (Dvec n) (pmat y) = ∑ a : Fin n, ∑ b : Fin n,
      -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) *
        (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) := by
    have e : ∀ a b : Fin n, -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) *
        (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) =
        -(((Dvec n a : ℝ) : ℂ) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) +
          ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat y a b) :=
      fun a b => by ring
    simp_rw [e, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [Finset.sum_comm (f := fun a b : Fin n =>
      ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat y a b))]
    simp only [Lap.Base.qForm, Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  rw [h1]
  simp only [qForm_term]
  have e2 := sum_pairs_pmat_fp (fun a b : Fin n => ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) y
  rw [Fintype.sum_prod_type' (f := fun a b : Fin n =>
    (if b < a then (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * ‖pmat y a b‖ ^ 2 else 0 : ℝ))] at e2
  rw [← Complex.ofReal_inj] at e2
  simp only [Complex.ofReal_sum] at e2
  rw [e2, ← Complex.ofReal_sum]
  congr 1
  simp only [Qf, wab, Pi.zero_apply, sub_self, zero_add]

theorem matrix_coefficient_pointwise_limit (hB3 : Lap.Base.TangentPairingStatement) {ε : Fin n → Bool} {lam : Fin n → ℝ} (H : ℕ → Type)
    [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℂ (H t)] [∀ t, CompleteSpace (H t)]
    (σ : ∀ t : ℕ, Matrix (Fin n) (Fin n) ℂ → (H t →L[ℂ] H t)) (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (j : ∀ t : ℕ, (T t).V →L[ℂ] H t)
    (hF : ∀ᶠ t in Filter.atTop, FData ε (lamT lam t) (σ t) (T t) (j t))
    (hsm : ∀ᶠ t in Filter.atTop, ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
        ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
          ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ)
    (y : PCoord ε → ℂ) :
    Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := hB3 n ε (Dvec n) (lowK ε lam) (S7.hs (pmat y) + 1)
  have hinG : inG ε (pmat y) := by
    unfold inG Jm
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply]
    rw [pmat_herm_apply y a b, star_star]
    by_cases he : ε a = ε b
    · rw [pmat_apply_eq_zero_of_sign_eq y he]; simp
    · cases ha : ε a <;> cases hb : ε b <;> simp_all
  have hR : S7.hs (pmat y) ≤ (S7.hs (pmat y) + 1) ^ 2 := by
    nlinarith [sq_nonneg (S7.hs (pmat y) + 1 / 2)]
  have hsq : Filter.Tendsto (fun t : ℕ => Real.sqrt (t : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨⌈b ^ 2⌉₊, fun a ha => ?_⟩
    refine (le_abs_self b).trans (Real.abs_le_sqrt ?_)
    exact (Nat.le_ceil _).trans (by exact_mod_cast ha)
  have hC0 : Filter.Tendsto (fun t : ℕ => C / Real.sqrt (t : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hC0
  filter_upwards [hsm, Filter.eventually_ge_atTop 1] with t ht ht1
  obtain ⟨H', i1, i2, σ', w', hw', heq⟩ := ht
  letI := i1
  letI := i2
  have hlow : lowK ε (lamT lam t) = (t : ℝ) • Dvec n + lowK ε lam := by
    ext a
    simp only [lowK, lamT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb := hC (t : ℝ) (by exact_mod_cast ht1) H' σ' (lamT lam t) w' hw' hlow (pmat y) hinG hR
  rw [trace_dMat_pmat y, qForm_pmat y, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hb
  have hy : ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y) = ((Real.sqrt t)⁻¹ : ℝ) • y := by
    ext ab
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  have hL : (((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)) =
      Complex.exp (-((Qf (0 : Fin n → ℝ) y : ℝ) : ℂ) / 2) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [← heq, hy, adKAux_pmat_smul, hL]
  exact hb

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

