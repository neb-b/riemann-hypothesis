module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQA
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWR
section
noncomputable section

open Finset Matrix MeasureTheory Set Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

open ChartWRAux in
theorem chartWR_vol (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ (B : Set (UCo N)) (E : Set (TriCo N)), MeasurableSet B → MeasurableSet E →
      (∀ x ∈ B, ‖x‖ < δ) → (∀ t ∈ E, ‖t‖ < δ) →
      volume (chartWR '' (B ×ˢ E)) ≤ ENNReal.ofReal (1 + η) * (volume B * volume E) ∧
        ENNReal.ofReal (1 - η) * (volume B * volume E) ≤ volume (chartWR '' (B ×ˢ E)) := by
  have : (volume : Measure (Fin N → Fin N → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let L : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ) := (lamE : (UCo N × TriCo N) ≃L[ℝ] _)
  let g : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ) := fun z => chartWR (lamE.symm z)
  have hg : HasStrictFDerivAt g (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) 0 := by
    have hc : HasStrictFDerivAt (chartWR (N := N)) L (lamE.symm 0) := by
      rw [map_zero]; exact chartWR_strict
    have h := hc.comp (0 : Fin N → Fin N → ℂ)
      ((lamE.symm : (Fin N → Fin N → ℂ) ≃L[ℝ] (UCo N × TriCo N)) :
        (Fin N → Fin N → ℂ) →L[ℝ] (UCo N × TriCo N)).hasStrictFDerivAt
    rwa [ContinuousLinearEquiv.coe_comp_coe_symm] at h
  have hdet : ENNReal.ofReal |(ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)).det| = 1 := by
    simp [ContinuousLinearMap.det, ContinuousLinearMap.coe_id]
  have ev1 := addHaar_image_le_mul_of_det_lt (μ := (volume : Measure (Fin N → Fin N → ℂ)))
    (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) (m := (1 + η).toNNReal) (by
      rw [hdet]; exact_mod_cast (show (1 : ℝ) < (1 + η).toNNReal by
        rw [Real.coe_toNNReal _ (by linarith)]; linarith))
  have ev2 : ∀ᶠ δ in 𝓝[>] (0 : NNReal), ∀ (s : Set (Fin N → Fin N → ℂ)) (f : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ)),
      ApproximatesLinearOn f (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) s δ →
        ENNReal.ofReal (1 - η) * volume s ≤ volume (f '' s) := by
    rcases lt_or_ge η 1 with h1 | h1
    · have := mul_le_addHaar_image_of_lt_det (μ := (volume : Measure (Fin N → Fin N → ℂ)))
        (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) (m := (1 - η).toNNReal) (by
          rw [hdet]; exact_mod_cast (show ((1 - η).toNNReal : ℝ) < 1 by
            rw [Real.coe_toNNReal _ (by linarith)]; linarith))
      exact this
    · refine Filter.Eventually.of_forall fun δ s f _ => ?_
      rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]; exact bot_le
  obtain ⟨c, ⟨hc1, hc2⟩, hcpos⟩ := ((ev1.and ev2).and self_mem_nhdsWithin).exists
  obtain ⟨s, hs, hap⟩ := hg.approximates_deriv_on_nhds (Or.inr hcpos)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg _
  refine ⟨r / (‖L‖ + 1), by positivity, fun B E hB hE hBδ hEδ => ?_⟩
  have hLr : ‖L‖ * (r / (‖L‖ + 1)) < r := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hball : (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) '' (B ×ˢ E) ⊆ s := by
    rintro _ ⟨p, hp, rfl⟩
    apply hrs
    rw [Metric.mem_ball, dist_zero_right]
    have hp' : ‖p‖ < r / (‖L‖ + 1) := by
      rw [Prod.norm_def]; exact max_lt (hBδ _ hp.1) (hEδ _ hp.2)
    calc ‖lamE p‖ = ‖L p‖ := rfl
      _ ≤ ‖L‖ * ‖p‖ := L.le_opNorm p
      _ ≤ ‖L‖ * (r / (‖L‖ + 1)) := mul_le_mul_of_nonneg_left hp'.le hL0
      _ < r := hLr
  have hap' := hap.mono_set hball
  have himg : chartWR '' (B ×ˢ E) = g '' ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) := by
    rw [Set.image_image]
    refine Set.image_congr fun p _ => ?_
    simp [g]
  have hmp : MeasurePreserving (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) volume volume := by
    have e : (⇑(lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ))) = lam := funext lamE_apply
    rw [e]; exact mp_lam
  have hme : MeasurableEmbedding (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) :=
    lamE.toHomeomorph.measurableEmbedding
  have hvol : volume ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) = volume B * volume E := by
    calc volume ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E))
        = (Measure.map lamE volume) ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) := by
          rw [hmp.map_eq]
      _ = volume (lamE ⁻¹' ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E))) := hme.map_apply _ _
      _ = volume (B ×ˢ E) := by rw [Set.preimage_image_eq _ lamE.injective]
      _ = volume B * volume E := Measure.prod_prod _ _
  rw [himg]
  refine ⟨?_, ?_⟩
  · have := hc1 _ g hap'
    rw [hvol] at this
    exact this
  · have := hc2 _ g hap'
    rw [hvol] at this
    exact this

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpD
section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem gMat_add {ε : Fin n → Bool} (s t : GCo ε) : gMat (s + t) = gMat s + gMat t := by
  ext a b
  simp only [gMat, Matrix.add_apply]
  simp only [kMat, pmat, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> (try simp only [Complex.ofReal_add, star_add, mul_add, neg_add, add_zero]) <;>
    (try ring)

theorem gMat_smul {ε : Fin n → Bool} (c : ℝ) (s : GCo ε) : gMat (c • s) = (RingHom.id ℝ c) • gMat s := by
  ext a b
  simp only [gMat, RingHom.id_apply, Matrix.add_apply, Matrix.smul_apply]
  simp only [kMat, pmat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
  split_ifs <;> (try simp only [Complex.real_smul, Complex.ofReal_mul, star_mul', Complex.star_def,
    Complex.conj_ofReal, smul_add, smul_zero, smul_neg, add_zero, mul_neg]) <;>
    (try simp only [smul_eq_mul, Complex.ofReal_mul]) <;> (try ring_nf)

def gL (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' := gMat_add
  map_smul' := gMat_smul

theorem gL_injective (ε : Fin n → Bool) : Function.Injective (gL ε) := by
  intro s t h
  have h' : gMat s = gMat t := h
  rw [← gCo_gMat s, ← gCo_gMat t, h']

abbrev gV (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := LinearMap.range (gL ε)

def gE (ε : Fin n → Bool) : GCo ε ≃ₗ[ℝ] gV ε := LinearEquiv.ofInjective (gL ε) (gL_injective ε)

def ujMat (ε : Fin n → Bool) : UJ ε →* Matrix (Fin n) (Fin n) ℂ :=
  (Units.coeHom _).comp (UJ ε).subtype

theorem ujMat_apply (ε : Fin n → Bool) (g : UJ ε) : ujMat ε g = toM g := rfl

section Normed

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_inUJ_small (ε : Fin n → Bool) : ∀ᶠ Z in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ),
    inUJ ε (NormedSpace.exp Z) → inG ε Z := by
  unfold inG
  have hd : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) 0 := hasStrictFDerivAt_exp_zero
  obtain ⟨s, hs, hap⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))

  have hinj : ∀ x ∈ s, ∀ y ∈ s, NormedSpace.exp x = NormedSpace.exp y → x = y := by
    intro x hx y hy hxy
    have h := hap x hx y hy
    rw [hxy, sub_self] at h
    change ‖0 - (x - y)‖ ≤ ((1 / 2 : NNReal) : ℝ) * ‖x - y‖ at h
    rw [zero_sub, norm_neg, NNReal.coe_div, NNReal.coe_one, NNReal.coe_two] at h
    have h0 : ‖x - y‖ = 0 := le_antisymm (by linarith [norm_nonneg (x - y)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hc1 : Tendsto (fun Z : Matrix (Fin n) (Fin n) ℂ => Jm ε * Zᴴ * Jm ε) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun Z : Matrix (Fin n) (Fin n) ℂ => Jm ε * Zᴴ * Jm ε) :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    simpa using hcont.tendsto 0
  have hc2 : Tendsto (fun Z : Matrix (Fin n) (Fin n) ℂ => -Z) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : Matrix (Fin n) (Fin n) ℂ))
  filter_upwards [hc1.eventually hs, hc2.eventually hs] with Z h1 h2 hU
  unfold inUJ at hU
  have hE : NormedSpace.exp (Jm ε * Zᴴ * Jm ε) = NormedSpace.exp (-Z) := by
    have hL : Jm ε * (NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z = 1 := by
      calc Jm ε * (NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z
          = Jm ε * ((NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU, hJJ]
    rw [show Jm ε * Zᴴ * Jm ε = Jm ε * Zᴴ * (Jm ε)⁻¹ by rw [hJi], Matrix.exp_conj _ _ hJu, hJi,
      Matrix.exp_conjTranspose, Matrix.exp_neg]
    exact (Matrix.inv_eq_left_inv hL).symm
  have hZ := hinj _ h1 _ h2 hE
  calc Zᴴ * Jm ε + Jm ε * Z = Jm ε * (Jm ε * Zᴴ * Jm ε) + Jm ε * Z := by
        simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    _ = 0 := by rw [hZ, Matrix.mul_neg, neg_add_cancel]

def ujChart (ε : Fin n → Bool) : Chart (gV ε) (UJ ε) where
  mat := ujMat ε
  emb := (isClosedEmbedding_toM ε).isEmbedding
  H1 := fun X => by
    obtain ⟨s, hs⟩ := X.2
    have h : NormedSpace.exp (gMat s) ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [range_toM]
      have := exp_smul_mem_UJset (gMat_inG s) 1
      simp only [Complex.ofReal_one, one_smul] at this
      exact this
    obtain ⟨g, hg⟩ := h
    refine ⟨g, ?_⟩
    rw [ujMat_apply, ← hs]
    exact hg
  H2 := by
    filter_upwards [exp_inUJ_small ε] with Z hZ hg
    obtain ⟨g, hg⟩ := hg
    have h1 : inUJ ε (ujMat ε g) := g.2
    rw [hg] at h1
    exact ⟨gCo ε Z, gMat_gCo (hZ h1)⟩

end Normed

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.LintegralGaussTri
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussE_pow_odd (n : ℕ) : (∏ i ∈ range n, Real.pi ^ (2 * i + 1)) = Real.pi ^ (n ^ 2) := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem gaussE_volU_mul :
    volU N * (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) =
      Real.pi ^ (N ^ 2) := by
  have hX : Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N =
      ∏ i ∈ range N, (Real.pi ^ i * (i.factorial : ℝ) / 2) := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.sum_range_id, Finset.prod_const, Finset.card_range]
  rw [hX, volU, ← Finset.prod_mul_distrib, ← gaussE_pow_odd N]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hf : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
  field_simp
  ring

theorem gaussE_qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N := by
  have hcont : Continuous fun Z : Fin N → Fin N → ℂ => hs (Matrix.of Z) := by
    unfold hs
    simp only [Matrix.of_apply]
    fun_prop
  have h := hC (fun Z => ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))))
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hcont.neg).measurable)
  have hin : ∀ k : UNgrp N, (∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (Matrix.of (qrMap (k, t))))) *
      ENNReal.ofReal (qrWt t)) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
    intro k
    simp only [qrMap, Equiv.apply_symm_apply, gaussB_hs_unitary_mul]
    exact gaussD_tri
  simp only [hin, lintegral_const, measure_univ, mul_one, gaussC_mat] at h
  set X := Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]
    have : 0 < ∏ i ∈ range N, (i.factorial : ℝ) :=
      Finset.prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos i)
    positivity
  have hPpos : 0 < Real.pi ^ (N ^ 2) := pow_pos Real.pi_pos _
  have hCpos : 0 < C := by
    by_contra hc
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hc), zero_mul, ENNReal.ofReal_eq_zero] at h
    linarith
  rw [← ENNReal.ofReal_mul hCpos.le, ENNReal.ofReal_eq_ofReal_iff hPpos.le (by positivity)] at h
  have h2 := gaussE_volU_mul (N := N)
  rw [← hXdef] at h2
  exact mul_right_cancel₀ hXpos.ne' (h.symm.trans h2.symm)

theorem qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N :=
  gaussE_qr_const μ C hC

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQB
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.OmegaPQAux

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n P Q : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem Jpq_eq : Formalism.UG.Jpq P Q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext (i | i) (j | j)
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]
  · simp [Formalism.UG.Jpq, Matrix.diagonal_apply]
  · simp [Formalism.UG.Jpq, Matrix.diagonal_apply]
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]

theorem mem_lieU_iff (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ Formalism.BasicNotions.lieU P Q ↔ ∀ i j, star (X j i) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) j +
      Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i * X i j = 0 := by
  show Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔ _
  rw [Jpq_eq]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using hij
  · intro h
    ext i j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h i j

theorem mem_reindex_iff (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.reindex e.symm e.symm Y ∈ Formalism.BasicNotions.lieU P Q ↔
      ∀ a b, star (Y b a) * sg ε b + sg ε a * Y a b = 0 := by
  rw [mem_lieU_iff]
  have hs : ∀ i, Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i = sg ε (e i) := by
    rintro (i | i) <;> simp [sg, he1, he2]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, hs]
  constructor
  · intro h a b
    simpa using h (e.symm a) (e.symm b)
  · intro h i j
    exact h (e i) (e j)

theorem gMat_mem {ε : Fin n → Bool} (s : GCo ε) (a b : Fin n) :
    star (gMat s b a) * sg ε b + sg ε a * gMat s a b = 0 := by
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : ¬ b < a := lt_asymm h
    have h2 : a ≠ b := ne_of_lt h
    have h3 : b ≠ a := ne_of_gt h
    cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]
  · cases ha : ε a <;> simp [gMat, kMat, pmat, sg, ha]
  · have h1 : ¬ a < b := lt_asymm h
    have h2 : a ≠ b := ne_of_gt h
    have h3 : b ≠ a := ne_of_lt h
    cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]

theorem gMat_add {ε : Fin n → Bool} (s t : GCo ε) : gMat (s + t) = gMat s + gMat t := by
  ext a b
  simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> (try simp only [star_add, neg_add, Complex.ofReal_add]) <;> ring

theorem gMat_smul {ε : Fin n → Bool} (c : ℝ) (s : GCo ε) : gMat (c • s) = c • gMat s := by
  ext a b
  simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply]
  split_ifs <;> (try simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, star_mul',
    Complex.star_def, map_mul, Complex.conj_ofReal]) <;> ring

def coordOf {ε : Fin n → Bool} (Y : Matrix (Fin n) (Fin n) ℂ) : GCo ε :=
  ((fun a => (Y a a).im, fun k => Y k.1.1 k.1.2), fun p => Y p.1.1 p.1.2)

theorem coordOf_gMat {ε : Fin n → Bool} (s : GCo ε) : coordOf (gMat s) = s := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [coordOf, gMat, kMat, pmat]
  · funext k
    obtain ⟨⟨a, b⟩, hk⟩ := k
    have h1 : a ≠ b := ne_of_gt hk.1
    have h2 : ¬ a < b := lt_asymm hk.1
    simp [coordOf, gMat, kMat, pmat, h1, h2, hk.1, hk.2]
  · funext q
    obtain ⟨⟨a, b⟩, hq⟩ := q
    have h1 : a ≠ b := ne_of_gt hq.1
    have h2 : ¬ a < b := lt_asymm hq.1
    simp [coordOf, gMat, kMat, pmat, h1, h2, hq.1, hq.2]

theorem gMat_coordOf {ε : Fin n → Bool} (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ a b, star (Y b a) * sg ε b + sg ε a * Y a b = 0) : gMat (coordOf (ε := ε) Y) = Y := by
  ext a b
  have key := hY a b
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : ¬ b < a := lt_asymm h
    have h2 : a ≠ b := ne_of_lt h
    cases ha : ε a <;> cases hb : ε b <;>
      simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>
      first | linear_combination key | linear_combination -key
  · have hre : (Y a a).re = 0 := by
      have hk := congrArg Complex.re key
      cases ha : ε a <;> simp [sg, ha] at hk <;> linarith
    apply Complex.ext <;> simp [gMat, kMat, pmat, coordOf, hre]
  · have h1 : ¬ a < b := lt_asymm h
    have h2 : a ≠ b := ne_of_gt h
    cases ha : ε a <;> cases hb : ε b <;>
      simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>
      first | linear_combination key | linear_combination -key

end ReciprocityTheory.ChartRestriction.DS.OmegaPQAux
end
end

