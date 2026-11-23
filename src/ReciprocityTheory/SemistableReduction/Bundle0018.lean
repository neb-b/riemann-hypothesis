module

public import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
public import ReciprocityTheory.SemistableReduction.Bundle0014
public import ReciprocityTheory.SemistableReduction.SemiContractB

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.LogNormCoeffSubLeBlockSphereLogMean
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial NumberField

theorem harmonic_pred_le_one_add_log {n : ℕ} (hn : 0 < n) : (harmonic (n - 1) : ℝ) ≤ 1 + Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := harmonic_le_one_add_log (m + 1)
  have h2 : harmonic (m + 1 - 1) ≤ harmonic (m + 1) := by
    have e : m + 1 - 1 = m := by omega
    rw [e, harmonic_succ]
    have : (0 : ℚ) ≤ (((m + 1 : ℕ) : ℚ))⁻¹ := by positivity
    linarith
  have h3 : (harmonic (m + 1 - 1) : ℝ) ≤ harmonic (m + 1) := by exact_mod_cast h2
  linarith

theorem log_norm_coeff_sub_le_blockSphereLogMean (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) {B n : ℕ}
    (hn : 0 < n) {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (s : Fin B × Fin n →₀ ℕ) (hs : g.coeff s ≠ 0) :
    Real.log ‖g.coeff s‖ - ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) ≤ blockSphereMean B n g := by
  obtain ⟨z, hz1, hzc⟩ := exists_torus_coeff_le g s
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set r : ℝ := Real.sqrt n with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hnpos
  have hr2 : r ^ 2 = n := Real.sq_sqrt hnpos.le

  have hmem : ∀ b : Fin B, (WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)) : EuclideanSpace ℂ (Fin n)) ∈
      Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1 := by
    intro b
    have hj : ∀ j, ‖z (b, j) / (r : ℂ)‖ = 1 / r := by
      intro j
      rw [norm_div, hz1, Complex.norm_of_nonneg hr.le]
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [PiLp.toLp_apply, hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_pow, one_pow, hr2, mul_one_div_cancel hnpos.ne', Real.sqrt_one]
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)), hmem b⟩
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz' : (fun p => (r : ℂ) * blockPoint u p) = z := by
    funext p
    simp only [blockPoint, spherePoint, u, PiLp.toLp_apply]
    field_simp
  have hev := eval_mul_of_isMultiHomogeneous hg (r : ℂ) (blockPoint u)
  rw [hz'] at hev
  have hcpos : 0 < ‖g.coeff s‖ := norm_pos_iff.mpr hs
  have hgz : 0 < ‖eval z g‖ := lt_of_lt_of_le hcpos hzc
  have hnorm : ‖eval z g‖ = r ^ (∑ b, a b) * ‖eval (blockPoint u) g‖ := by
    rw [hev, norm_mul, norm_pow, Complex.norm_of_nonneg hr.le]
  have hgu : eval (blockPoint u) g ≠ 0 := by
    intro h0
    rw [hnorm, h0, norm_zero, mul_zero] at hgz
    exact lt_irrefl _ hgz
  have hbb := blockSphere_logMean_bound hSJ hInt hn B a g u hg hgu
  have hH := harmonic_pred_le_one_add_log hn
  have hlogr : Real.log r = Real.log n / 2 := Real.log_sqrt hnpos.le
  have hlz : Real.log ‖eval z g‖ =
      ((∑ b, a b : ℕ) : ℝ) * Real.log r + Real.log ‖eval (blockPoint u) g‖ := by
    rw [hnorm, Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hgu), Real.log_pow]
  have hlc : Real.log ‖g.coeff s‖ ≤ Real.log ‖eval z g‖ := Real.log_le_log hcpos hzc
  set A : ℝ := ∑ b, (a b : ℝ) with hAdef
  have hsum : ((∑ b, a b : ℕ) : ℝ) = A := by rw [hAdef]; push_cast; rfl
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun b _ => Nat.cast_nonneg _)
  have hmul : A / 2 * (harmonic (n - 1) : ℝ) ≤ A / 2 * (1 + Real.log n) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hgoal : ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) = A * (Real.log n + 1 / 2) := by
    rw [hAdef, Finset.sum_mul]
  rw [hgoal]
  rw [hsum, hlogr] at hlz
  nlinarith

theorem neg_log_norm_coeff_le_finitePlaces {K : Type*} [Field K] [NumberField K] {ι : Type*} (f : MvPolynomial ι K)
    (s : ι →₀ ℕ) (hs : s ∈ f.support) :
    -Real.log |((Algebra.norm ℚ (f.coeff s) : ℚ) : ℝ)| ≤
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) := by
  classical
  have hc : f.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have hA : ∀ w : FinitePlace K, w (f.coeff s) ≤ gaussAbs w f := by
    intro w
    unfold gaussAbs
    have h1 := Finset.le_sup (f := fun t => (w (f.coeff t)).toNNReal) hs
    calc w (f.coeff s) ≤ ((w (f.coeff s)).toNNReal : ℝ) := Real.le_coe_toNNReal _
      _ ≤ _ := by exact_mod_cast h1
  have hpos : ∀ w : FinitePlace K, 0 < w (f.coeff s) := fun w => NumberField.FinitePlace.pos_iff.mpr hc
  have hU : (⋃ t ∈ f.support, Function.mulSupport (fun w : FinitePlace K => w (f.coeff t))).Finite :=
    Set.Finite.biUnion f.support.finite_toSet
      (fun t ht => NumberField.FinitePlace.hasFiniteMulSupport (MvPolynomial.mem_support_iff.mp ht))
  set T := hU.toFinset with hT
  have hsubG : Function.support (fun w : FinitePlace K => Real.log (gaussAbs w f)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    by_contra hnot
    apply hw
    simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
    have h1 : gaussAbs w f = 1 := by
      unfold gaussAbs
      have hne : f.support.Nonempty := ⟨s, hs⟩
      rw [Finset.sup_congr rfl (g := fun _ => (1 : NNReal)) (fun t ht => by simp [hnot t ht]),
        Finset.sup_const hne]
      simp
    simp [h1]
  have hsubW : Function.mulSupport (fun w : FinitePlace K => w (f.coeff s)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    exact Set.mem_biUnion hs hw
  have hprod := NumberField.FinitePlace.prod_eq_inv_abs_norm hc
  rw [finprod_eq_prod_of_mulSupport_subset _ hsubW] at hprod
  rw [finsum_eq_sum_of_support_subset _ hsubG]
  have hlog : Real.log (∏ w ∈ T, w (f.coeff s)) = ∑ w ∈ T, Real.log (w (f.coeff s)) :=
    Real.log_prod (fun w _ => (hpos w).ne')
  rw [hprod] at hlog
  have hle : ∑ w ∈ T, Real.log (w (f.coeff s)) ≤ ∑ w ∈ T, Real.log (gaussAbs w f) :=
    Finset.sum_le_sum (fun w _ => Real.log_le_log (hpos w) (hA w))
  push_cast at hlog
  rw [Real.log_inv] at hlog
  linarith

theorem sum_log_norm_embedding_eq {K : Type*} [Field K] [NumberField K] (c : K) (hc : c ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = Real.log |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
  classical
  have hne : ∀ σ : K →+* ℂ, ‖σ c‖ ≠ 0 := fun σ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hc)
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ c
  have h2 : ∏ σ : K →+* ℂ, σ c = ∏ σ : K →ₐ[ℚ] ℂ, σ c :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  have hprod : ∏ σ : K →+* ℂ, ‖σ c‖ = |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
    rw [← norm_prod, h2, ← h]
    simp [Complex.norm_ratCast]
  rw [← hprod, Real.log_prod (fun σ _ => hne σ)]

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SJCoreD
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric Set Real

theorem sphereProb_eq (n : ℕ) : sphereProb n =
    ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ]

private lemma log_norm_sum_smul_sphere_mul_exp_eq {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) (z : UnitSphereC n) (r : ℝ) (hr : 0 < r)
    (hz : ∑ i, WithLp.ofLp c i * spherePoint z i ≠ 0) :
    log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp (r • (z : EuclideanSpace ℂ (Fin n))) i‖ *
        exp (-‖r • (z : EuclideanSpace ℂ (Fin n))‖ ^ 2) =
      (log r + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) * exp (-r ^ 2) := by
  have h1 : ∑ i, WithLp.ofLp c i * WithLp.ofLp (r • (z : EuclideanSpace ℂ (Fin n))) i =
      (r : ℂ) * ∑ i, WithLp.ofLp c i * spherePoint z i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul, spherePoint]
    ring
  have h2 : ‖r • (z : EuclideanSpace ℂ (Fin n))‖ = r := by
    rw [norm_smul, norm_eq_of_mem_sphere z, mul_one, Real.norm_of_nonneg hr.le]
  rw [h1, h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
    Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hz)]

theorem polar_mean {n : ℕ} (hn : 0 < n) (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    Integrable (fun z : UnitSphereC n ↦ log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖)
        (sphereProb n) ∧
      ∫ z, log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(sphereProb n) =
        gaussLogC ‖c‖ / gaussOneC - radK (2 * n - 1) / radJ (2 * n - 1) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin n)), Complex.finrank_real_complex,
      finrank_euclideanSpace_fin]
  have hk : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1 = 2 * n - 1 := by rw [hdim]
  have hk1 : 1 ≤ 2 * n - 1 := by omega
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; omega)
  have hJ : radJ (2 * n - 1) ≠ 0 := (radJ_pos _).ne'

  have h2n : ((Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℕ) : ENNReal) ≠ 0 := by
    rw [hdim]; exact Nat.cast_ne_zero.mpr (by omega)
  have hA0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    exact mul_ne_zero h2n (measure_ball_pos _ _ one_pos).ne'
  have hAtop : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  haveI : IsFiniteMeasure (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := ⟨lt_top_iff_ne_top.mpr hAtop⟩
  have hA : ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal =
      (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) * (volume : Measure (EuclideanSpace ℂ (Fin n))).real (ball 0 1) := by
    rw [Measure.toSphere_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def]
  have hApos : 0 < ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal := ENNReal.toReal_pos hA0 hAtop

  have hIe : ∫ x : EuclideanSpace ℂ (Fin n), exp (-‖x‖ ^ 2) = ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal * radJ (2 * n - 1) := by
    have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℂ (Fin n))) (fun y : ℝ => exp (-y ^ 2))
    simp only [nsmul_eq_mul, smul_eq_mul] at h
    rw [h, hA, hk, radJ, mul_assoc]
  obtain ⟨s, hs, hGi, hIG0, hIe0⟩ := gauss_pair hn c hc
  have hae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere, ∑ i, WithLp.ofLp c i * spherePoint z i ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact sphere_linear_zero_null c hc

  have hinner : ∀ z : UnitSphereC n, ∑ i, WithLp.ofLp c i * spherePoint z i ≠ 0 →
      ∫ r : Ioi (0 : ℝ), log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp ((r : ℝ) • (z : EuclideanSpace ℂ (Fin n))) i‖ *
          exp (-‖(r : ℝ) • (z : EuclideanSpace ℂ (Fin n))‖ ^ 2)
        ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1)) =
      radK (2 * n - 1) + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * radJ (2 * n - 1) := by
    intro z hz
    calc _ = ∫ r : Ioi (0 : ℝ), (fun t : ℝ => (log t + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) * exp (-t ^ 2)) (r : ℝ)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1)) :=
          integral_congr_ae (ae_of_all _ fun r => log_norm_sum_smul_sphere_mul_exp_eq c z r.1 r.2 hz)
      _ = ∫ t in Ioi (0 : ℝ), t ^ (2 * n - 1) * ((log t + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) * exp (-t ^ 2)) := by
          rw [hk]
          exact integral_volumeIoiPow (2 * n - 1)
            (fun t : ℝ => (log t + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) * exp (-t ^ 2))
      _ = ∫ t in Ioi (0 : ℝ), (t ^ (2 * n - 1) * log t * exp (-t ^ 2) +
            log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * (t ^ (2 * n - 1) * exp (-t ^ 2))) := by
          congr 1; funext t; ring
      _ = radK (2 * n - 1) + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * radJ (2 * n - 1) := by
          rw [integral_add (integrableOn_radK hk1) (Integrable.const_mul (integrableOn_radJ _) _),
            integral_const_mul] <;> rfl
  have hΦ := integrable_polar n hGi
  have hψint : Integrable (fun z : UnitSphereC n => radK (2 * n - 1) + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * radJ (2 * n - 1))
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
    refine hΦ.integral_prod_left.congr ?_
    filter_upwards [hae] with z hz
    exact hinner z hz
  have hLσ : Integrable (fun z : UnitSphereC n => log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖) (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
    refine ((hψint.sub (integrable_const (radK (2 * n - 1)))).div_const (radJ (2 * n - 1))).congr
      (ae_of_all _ fun z => ?_)
    simp only [Pi.sub_apply]
    rw [add_sub_cancel_left, mul_div_cancel_right₀ _ hJ]
  have hIG : ∫ x : EuclideanSpace ℂ (Fin n), log ‖∑ i, WithLp.ofLp c i * WithLp.ofLp x i‖ * exp (-‖x‖ ^ 2) =
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal * radK (2 * n - 1) + (∫ z, log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere) * radJ (2 * n - 1) := by
    rw [integral_polar hn, integral_prod _ hΦ]
    calc _ = ∫ z, (radK (2 * n - 1) + log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ * radJ (2 * n - 1)) ∂(volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
            apply integral_congr_ae
            filter_upwards [hae] with z hz
            exact hinner z hz
      _ = _ := by
            rw [integral_add (integrable_const _) (hLσ.mul_const _), integral_mul_const]
            simp only [integral_const, smul_eq_mul, measureReal_def]
  have e1 := hIG.symm.trans hIG0
  have e2 := hIe.symm.trans hIe0
  have hgn : gaussOneC ^ n = gaussOneC * gaussOneC ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hg : gaussOneC ≠ 0 := by
    intro h0
    rw [hgn, h0, zero_mul, mul_zero] at e2
    exact (mul_pos hApos (radJ_pos _)).ne' e2
  rw [sphereProb_eq]
  refine ⟨hLσ.smul_measure (ENNReal.inv_ne_top.mpr hA0), ?_⟩
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  set A := ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ).toReal with hAdef
  set IL := ∫ z, log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere with hILdef
  have hA0' : A ≠ 0 := hApos.ne'
  have hIL : IL = (s * (gaussLogC ‖c‖ * gaussOneC ^ (n - 1)) - A * radK (2 * n - 1)) /
      radJ (2 * n - 1) := by
    rw [eq_div_iff hJ]
    linear_combination e1
  have hX : s * (gaussLogC ‖c‖ * gaussOneC ^ (n - 1)) / (A * radJ (2 * n - 1)) =
      gaussLogC ‖c‖ / gaussOneC := by
    rw [div_eq_div_iff (mul_ne_zero hA0' hJ) hg]
    linear_combination (-gaussLogC ‖c‖) * e2 - (gaussLogC ‖c‖ * s) * hgn
  rw [hIL, ← hX]
  field_simp <;> ring

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiContract
section
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Module

theorem semiContract_holds (hP : SemiPointStatement) (hD : DegAddStatement) :
    SemistableStatement := by
  intro K _ _ r S L hLat hSD
  obtain ⟨M, hM⟩ := hP K r S L hLat hSD
  refine ⟨M, hM, fun N hNL hN => ?_⟩
  by_contra hN0
  obtain ⟨b, hbL, hbN, hbli, hker⟩ := sc_kerfam L hLat.2 N
  obtain ⟨c, hcL, hcli⟩ := sc_imfam L hLat.2 N
  have hm := sc_rank_pos N hN0
  have hli := sc_append_li N b c hbN hbli hcli
  have hkm : finrank K (LinearMap.ker N.mulVecLin) + finrank K (LinearMap.range N.mulVecLin) = r := by
    have := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fin_fun] at this
    omega
  have hspan : Submodule.span K (Set.range (Fin.append b c)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, Module.finrank_fin_fun, hkm])
  have happL : ∀ i, Fin.append b c i ∈ L := by
    intro i
    induction i using Fin.addCases with
    | left i => rw [Fin.append_left]; exact hbL i
    | right j => rw [Fin.append_right]; exact hcL j
  have hspanL : ∀ x ∈ L, x ∈ Submodule.span K (Set.range (Fin.append b c)) := by
    intro x _; rw [hspan]; exact Submodule.mem_top

  have hdegL := hM.1 _ (Fin.append b c) ⟨happL, hli, hspanL⟩
  have hdegK := hM.2 (satSub L b) inf_le_left _ b
    ⟨fun i => ⟨hbL i, Submodule.subset_span ⟨i, rfl⟩⟩, hbli, fun x hx => hx.2⟩
  have hadd := hD K r _ _ M.H L b c M.posDef hLat.1 hbL hcL hli hspanL

  set NL := L.map (N.mulVecLin.restrictScalars (𝓞 K)) with hNLdef
  have hNLle : NL ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNL x hx
  have hNspan : ∀ y, N *ᵥ y ∈ Submodule.span K (Set.range fun j => N *ᵥ c j) := by
    intro y
    have hy : y ∈ Submodule.span K (Set.range (Fin.append b c)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction i using Fin.addCases with
      | left i => rw [Fin.append_left, hbN i]; exact Submodule.zero_mem _
      | right j => rw [Fin.append_right]; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ a hx
  have hdegN := hM.2 NL hNLle _ (fun j => N *ᵥ c j)
    ⟨fun j => ⟨c j, hcL j, rfl⟩, hcli, by rintro _ ⟨x, _, rfl⟩; exact hNspan x⟩

  have hidx := sc_index L N b c hcL hbN hker
  have hσ := fun σ => sc_gram_lt hm (M.H σ) (M.posDef σ) σ N (hN σ) b c hli hbN hcli
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramC (M.H σ) σ fun j => N *ᵥ c j).det.re <
      ∑ σ : K →+* ℂ, Real.log (quotGramC (M.H σ) σ b c).det.re :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun σ _ =>
      Real.log_lt_log (hσ σ).1 (hσ σ).2
  have hlt : quotDeg M.H L b c < latDeg M.H NL (fun j => N *ᵥ c j) := by
    rw [quotDeg, latDeg, ← hidx]
    linarith
  linarith

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegBA
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def colMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a i => σ (b i a)

theorem gramC_eq_colMat {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (colMat σ b)ᴴ * H * colMat σ b := by
  ext i j
  simp only [gramC, colMat, embVec, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem colMat_comb {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (N : Matrix (Fin k) (Fin k) K) :
    colMat σ (fun j => ∑ i, N i j • b i) = colMat σ b * N.map σ := by
  ext a j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [colMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem gramC_comb {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (N : Matrix (Fin k) (Fin k) K) :
    gramC H σ (fun j => ∑ i, N i j • b i) = (N.map σ)ᴴ * gramC H σ b * N.map σ := by
  rw [gramC_eq_colMat, gramC_eq_colMat, colMat_comb, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem det_gramC_comb {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (N : Matrix (Fin k) (Fin k) K) :
    (gramC H σ (fun j => ∑ i, N i j • b i)).det =
      ((Complex.normSq (σ N.det) : ℝ) : ℂ) * (gramC H σ b).det := by
  rw [gramC_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have h : (N.map σ).det = σ N.det := (RingHom.map_det σ N).symm
  rw [h, ← Complex.mul_conj]
  simp only [starRingEnd_apply]
  ring

theorem colMat_mulVec_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) :
    Function.Injective (colMat σ b).mulVec := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin r) (Fin k) K, B = Matrix.of fun a i => b i a := ⟨_, rfl⟩
  have hker : LinearMap.ker B.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∑ i, g i • b i = 0 := by
      funext a
      have h1 := congrFun hg a
      simp only [hB, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Pi.zero_apply] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    funext i
    exact Fintype.linearIndependent_iff.mp hb g h0 i
  obtain ⟨L, hL⟩ := B.mulVecLin.exists_leftInverse_of_injective hker
  have hLB : LinearMap.toMatrix' L * B = 1 := by
    have h2 := congrArg LinearMap.toMatrix' hL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h2
    have h4 : LinearMap.toMatrix' B.mulVecLin = B := LinearMap.toMatrix'_toLin' B
    rwa [h4] at h2
  have hc : colMat σ b = B.map σ := by
    ext a i
    rw [hB]
    rfl
  intro v w hvw
  have h3 : ((LinearMap.toMatrix' L).map σ * colMat σ b).mulVec v =
      ((LinearMap.toMatrix' L).map σ * colMat σ b).mulVec w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvw]
  rwa [hc, ← Matrix.map_mul, hLB, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.one_mulVec,
    Matrix.one_mulVec] at h3

theorem gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hH : H.PosDef) (hb : LinearIndependent K b) : (gramC H σ b).PosDef := by
  rw [gramC_eq_colMat]
  exact hH.conjTranspose_mul_mul_same (colMat_mulVec_injective σ b hb)

theorem gramC_det_re_pos {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hH : H.PosDef) (hb : LinearIndependent K b) : 0 < (gramC H σ b).det.re := by
  classical
  exact (Complex.pos_iff.mp (gramC_posDef H σ b hH hb).det_pos).1

theorem sum_log_normSq {K : Type} [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) =
      2 * Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have hprod : (∏ σ : K →+* ℂ, σ x) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
    have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
    have h2 : algebraMap ℚ ℂ (Algebra.norm ℚ x) = ((Algebra.norm ℚ x : ℚ) : ℂ) := eq_ratCast _ _
    rw [h2] at h1
    rw [h1]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  have hne : ∀ σ : K →+* ℂ, Complex.normSq (σ x) ≠ 0 := fun σ => by
    rw [Ne, Complex.normSq_eq_zero]
    exact (map_ne_zero σ).mpr hx
  have hN : ((Algebra.norm ℚ x : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  rw [← Real.log_prod (s := Finset.univ) (f := fun σ : K →+* ℂ => Complex.normSq (σ x)) (fun σ _ => hne σ),
    ← map_prod Complex.normSq (fun σ : K →+* ℂ => σ x) Finset.univ, hprod,
    ← Complex.ofReal_ratCast, Complex.normSq_ofReal, Real.log_mul hN hN,
    ← Real.log_abs ((Algebra.norm ℚ x : ℚ) : ℝ)]
  ring

end ReciprocityTheory.MultiplicativeHeights
end
end

