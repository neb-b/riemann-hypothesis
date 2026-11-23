module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPolA
section
noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.HPol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Log

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_strict :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero.congr_fderiv (by ext; simp)


variable (n) in
def logM : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
  (exp_strict (n := n)).localInverse _ _ _

theorem logM_exp : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), logM n (NormedSpace.exp X) = X := by
  exact (exp_strict (n := n)).eventually_left_inverse

theorem exp_logM : ∀ᶠ h in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (logM n h) = h := by
  have h := (exp_strict (n := n)).eventually_right_inverse
  rw [NormedSpace.exp_zero] at h
  exact h

theorem logM_one : logM n 1 = 0 := by
  have h := (exp_strict (n := n)).localInverse_apply_image
  rw [NormedSpace.exp_zero] at h
  exact h

theorem logM_strict : HasStrictFDerivAt (logM n) (ContinuousLinearMap.id ℝ _) 1 := by
  have h := (exp_strict (n := n)).to_localInverse
  rw [NormedSpace.exp_zero] at h
  exact h

end Log

private theorem Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem Jm_inv (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε := by
  exact Matrix.inv_eq_left_inv (Jm_mul_self_eq_one' ε)

theorem Jm_isUnit (ε : Fin n → Bool) : IsUnit (Jm ε) := by
  exact ⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_one' ε, Jm_mul_self_eq_one' ε⟩, rfl⟩

theorem conjT_of_inG {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    Yᴴ = Jm ε * (-Y) * (Jm ε)⁻¹ := by
  have hJ := Jm_mul_self_eq_one' ε
  have h' : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left h'
  rw [Jm_inv]
  calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε * (-Y) * Jm ε := by rw [h1, Matrix.mul_neg]

theorem exp_inUJ {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  have hJ := Jm_mul_self_eq_one' ε
  show (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε
  rw [← Matrix.exp_conjTranspose, conjT_of_inG h, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv,
    Matrix.mul_assoc (Jm ε * NormedSpace.exp (-Y)) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem inG_of_exp {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hU : inUJ ε (NormedSpace.exp Y)) (h1 : ℓ (NormedSpace.exp Y) = Y)
    (h2 : ℓ (NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε)) = Jm ε * (-Yᴴ) * Jm ε) : inG ε Y := by
  have hJ := Jm_mul_self_eq_one' ε
  have hU' : (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε := hU
  have hEE : NormedSpace.exp Y * NormedSpace.exp (-Y) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl Y)), add_neg_cancel,
      NormedSpace.exp_zero]
  have key : NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε) = NormedSpace.exp Y := by
    have e1 : Jm ε * (-Yᴴ) * Jm ε = Jm ε * (-Y)ᴴ * (Jm ε)⁻¹ := by
      rw [Jm_inv, Matrix.conjTranspose_neg]
    rw [e1, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv, Matrix.exp_conjTranspose]
    calc Jm ε * (NormedSpace.exp (-Y))ᴴ * Jm ε
        = Jm ε * (NormedSpace.exp (-Y))ᴴ * ((NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y) := by
          rw [hU']
      _ = Jm ε * (NormedSpace.exp Y * NormedSpace.exp (-Y))ᴴ * Jm ε * NormedSpace.exp Y := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = NormedSpace.exp Y := by
          rw [hEE, Matrix.conjTranspose_one, Matrix.mul_one, hJ, Matrix.one_mul]
  have hY : Y = Jm ε * (-Yᴴ) * Jm ε := by rw [← h2, key, h1]
  have h3 : Jm ε * Y = -(Yᴴ * Jm ε) := by
    calc Jm ε * Y = Jm ε * (Jm ε * (-Yᴴ) * Jm ε) := congrArg (Jm ε * ·) hY
      _ = -(Yᴴ * Jm ε) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.neg_mul]
  show Yᴴ * Jm ε + Jm ε * Y = 0
  rw [h3, add_neg_cancel]

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem entry_of_inG {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (i j : Fin n) :
    star (Y j i) * sg ε j + sg ε i * Y i j = 0 := by
  have h' := congrFun (congrFun (show Yᴴ * Jm ε + Jm ε * Y = 0 from h) i) j
  simpa [Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h'

theorem inG_of_entry' {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, star (Y j i) * sg ε j + sg ε i * Y i j = 0) : inG ε Y := by
  show Yᴴ * Jm ε + Jm ε * Y = 0
  ext i j
  simpa [Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h i j

def cLin (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] GCo ε where
  toFun Y := ((fun a => (Y a a).im, fun ab => Y ab.1.1 ab.1.2), fun ab => Y ab.1.1 ab.1.2)
  map_add' _ _ := by
    ext <;> simp
  map_smul' _ _ := by
    ext <;> simp

theorem cLin_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cLin ε Y = ((fun a => (Y a a).im, fun ab => Y ab.1.1 ab.1.2), fun ab => Y ab.1.1 ab.1.2) := rfl

theorem cLin_gMat {ε : Fin n → Bool} (s : GCo ε) : cLin ε (gMat s) = s := by
  obtain ⟨⟨d, k⟩, p⟩ := s
  rw [cLin_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [gMat, kMat, pmat]
  · funext ab
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    have h1 : a ≠ b := ne_of_gt hab.1
    have h2 : ¬ a < b := not_lt_of_gt hab.1
    simp [gMat, kMat, pmat, h1, h2, hab.1, hab.2]
  · funext ab
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    have h1 : a ≠ b := ne_of_gt hab.1
    have h2 : ¬ a < b := not_lt_of_gt hab.1
    simp [gMat, kMat, pmat, h1, h2, hab.1, hab.2]

theorem gMat_cLin {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    gMat (cLin ε Y) = Y := by
  ext a b
  have hE := entry_of_inG h a b
  rw [cLin_apply]
  simp only [gMat, kMat, pmat, Matrix.add_apply]
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h1 : a ≠ b := ne_of_lt hab
    have h2 : ¬ b < a := not_lt_of_gt hab
    cases ha : ε a <;> cases hb : ε b <;>
      simp only [sg, ha, hb, ↓reduceIte, Bool.false_eq_true] at hE <;>
      simp [ha, hb, h1, h2, hab] <;>
      (try simp only [Complex.star_def] at hE) <;>
      first | linear_combination hE | linear_combination -hE
  · have h0 : star (Y a a) + Y a a = 0 := by
      cases ha : ε a <;> simp only [sg, ha, ↓reduceIte, Bool.false_eq_true] at hE <;>
        first | linear_combination hE | linear_combination -hE
    have hre : (Y a a).re = 0 := by
      have h4 := congrArg Complex.re h0
      simp at h4
      linarith
    apply Complex.ext <;> simp [hre]
  · have h1 : a ≠ b := ne_of_gt hab
    have h2 : ¬ a < b := not_lt_of_gt hab
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, h1, h2, hab]

theorem sg_eq {ε : Fin n → Bool} {i j : Fin n} (h : ε i = ε j) : sg ε i = sg ε j := by
  simp [sg, h]

theorem sg_ne {ε : Fin n → Bool} {i j : Fin n} (h : ¬ ε i = ε j) : sg ε i = -sg ε j := by
  unfold sg
  cases hi : ε i <;> cases hj : ε j <;> simp_all

theorem inG_gMat {ε : Fin n → Bool} (s : GCo ε) : inG ε (gMat s) := by
  apply inG_of_entry'
  intro i j
  obtain ⟨⟨d, k⟩, p⟩ := s
  simp only [gMat, kMat, pmat, Matrix.add_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have h1 : i ≠ j := ne_of_lt hij
    have h2 : ¬ j < i := not_lt_of_gt hij
    by_cases hε : ε i = ε j
    · simp [hε, h1, h1.symm, h2, hij, sg_eq hε]
      ring
    · simp [hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]
      ring
  · simp <;> ring
  · have h1 : i ≠ j := ne_of_gt hij
    have h2 : ¬ i < j := not_lt_of_gt hij
    by_cases hε : ε i = ε j
    · simp [hε, h1, h1.symm, h2, hij, sg_eq hε]
      ring
    · simp [hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]
      ring

end ReciprocityTheory.ChartRestriction.DS.HPol
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriHaar
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices

variable {N : ℕ}

theorem upMat_triCoOf_mul (t t0 : TriCo N) :
    upMat (triCoOf (upMat t * upMat t0)) = upMat t * upMat t0 ∧
      ∀ j, (triCoOf (upMat t * upMat t0)).1 j = t.1 j * t0.1 j := by
  have hU : ∀ (s : TriCo N) (a b : Fin N), upMat s a b =
      if a = b then ((s.1 a : ℝ) : ℂ) else if h : a < b then s.2 ⟨(a, b), h⟩ else 0 :=
    fun s a b => rfl
  have hz : ∀ (s : TriCo N) (a b : Fin N), b < a → upMat s a b = 0 := by
    intro s a b h
    rw [hU s a b, if_neg (ne_of_gt h), dite_eq_right (not_lt.mpr h.le)]
  have hlow : ∀ a b : Fin N, b < a → (upMat t * upMat t0) a b = 0 := by
    intro a b hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hka : k < a
    · rw [hz t a k hka, zero_mul]
    · rw [hz t0 k b (lt_of_lt_of_le hba (not_lt.mp hka)), mul_zero]
  have hdiag : ∀ a, (upMat t * upMat t0) a a = ((t.1 a * t0.1 a : ℝ) : ℂ) := by
    intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU t a a, hU t0 a a, if_pos rfl, if_pos rfl, Complex.ofReal_mul]
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · rw [hz t a k h, zero_mul]
      · rw [hz t0 k a h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  refine ⟨?_, fun j => ?_⟩
  · ext a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hU _ a b, if_neg (ne_of_lt h), dite_eq_left h]
      rfl
    · subst h
      rw [hU _ a a, if_pos rfl]
      show (((upMat t * upMat t0) a a).re : ℂ) = (upMat t * upMat t0) a a
      rw [hdiag, Complex.ofReal_re]
    · rw [hU _ a b, if_neg (ne_of_gt h), dite_eq_right (not_lt.mpr h.le), hlow a b h]
  · show ((upMat t * upMat t0) j j).re = t.1 j * t0.1 j
    rw [hdiag, Complex.ofReal_re]

theorem triMeas_map_mul_right (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    Measure.map (fun t : TriCo N => triCoOf (upMat t * upMat t0)) (triMeas N) = triMeas N := by
  classical
  have hfun : (fun t : TriCo N => triCoOf (upMat t * upMat t0)) = ⇑(rmulL (upMat t0)) := by
    funext t
    rw [rmulL_apply]
  set L : TriCo N →ₗ[ℝ] TriCo N := rmulL (upMat t0) with hL
  have hdet : LinearMap.det L = ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) := det_rmulL_upMat t0 h0
  set D : ℝ := ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) with hD
  have hDpos : 0 < D := Finset.prod_pos fun j _ => pow_pos (h0 j) _
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  haveI hC : (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)).IsAddHaarMeasure := by
    first
      | infer_instance
      | exact Measure.pi.isAddHaarMeasure _
  haveI hR : (volume : Measure (Fin N → ℝ)).IsAddHaarMeasure := by
    first
      | infer_instance
      | exact Measure.pi.isAddHaarMeasure _
  haveI hT : (volume : Measure (TriCo N)).IsAddHaarMeasure := by
    first
      | exact Measure.prod.instIsAddHaarMeasure volume volume
      | infer_instance
  have hvol : Measure.map L (volume : Measure (TriCo N)) = ENNReal.ofReal |D⁻¹| • volume := by
    rw [← hdet]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact hDpos.ne')
  have hP : MeasurableSet (triPos N) := by
    have : triPos N = ⋂ j : Fin N, {t : TriCo N | 0 < t.1 j} := by
      ext t
      simp [triPos]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)
  have hpre : ∀ S : Set (TriCo N), L ⁻¹' S ∩ triPos N = L ⁻¹' (S ∩ triPos N) := by
    intro S
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [hL, rmulL_mem_triPos t0 x h0]
  rw [hfun]
  ext s hs
  have hS : MeasurableSet (s ∩ triPos N) := hs.inter hP
  rw [Measure.map_apply hLm hs, triMeas, withDensity_apply _ (hLm hs), withDensity_apply _ hs,
    Measure.restrict_restrict (hLm hs), Measure.restrict_restrict hs, hpre s]
  have h1 : ∫⁻ x in L ⁻¹' (s ∩ triPos N), triDens x =
      ∫⁻ x in L ⁻¹' (s ∩ triPos N), ENNReal.ofReal D * triDens (L x) := by
    refine lintegral_congr fun x => ?_
    rw [hL, hD, ← triDens_rmulL t0 x h0]
  have h2 : ∫⁻ x in L ⁻¹' (s ∩ triPos N), ENNReal.ofReal D * triDens (L x) =
      ENNReal.ofReal D * ∫⁻ x, (s ∩ triPos N).indicator triDens (L x) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator (hLm hS)]
    congr 1
  have h3 : ∫⁻ x, (s ∩ triPos N).indicator triDens (L x) =
      ENNReal.ofReal |D⁻¹| * ∫⁻ y in s ∩ triPos N, triDens y := by
    rw [← lintegral_map ((triDens_measurable).indicator hS) hLm, hvol, lintegral_smul_measure,
      lintegral_indicator hS]
    rfl
  rw [h1, h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul hDpos.le, abs_of_pos (inv_pos.mpr hDpos),
    mul_inv_cancel₀ hDpos.ne', ENNReal.ofReal_one, one_mul]

theorem triMeas_compact_lt_top (K : Set (TriCo N)) (hK : IsCompact K) (hK0 : K ⊆ triPos N) :
    triMeas N K < ⊤ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold triMeas
  rw [withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_eq_left.mpr hK0]
  have hgc : ContinuousOn (fun t : TriCo N => ∏ j : Fin N, t.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1))) K := by
    refine continuousOn_finsetProd _ (fun j _ => ?_)
    exact ContinuousOn.zpow₀ (by fun_prop : Continuous fun t : TriCo N => t.1 j).continuousOn _
      (fun x hx => Or.inl (hK0 hx j).ne')
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgc
  calc ∫⁻ a in K, triDens a ≤ ∫⁻ _ in K, ENNReal.ofReal C := by
        refine setLIntegral_mono' hKm (fun x hx => ?_)
        exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC x hx))
    _ = ENNReal.ofReal C * volume K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUSetMeasurable
section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_real {V η ε a b e i : ℝ} (hV : 0 < V) (he : 0 < e) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) (hkey : (1 - ε) * (1 + η) = 1 + ε)
    (h1 : V * (i * a) ≤ (1 + ε) * (b * e)) (h2 : (1 - ε) * (b * e) ≤ V * (i * a))
    (h3 : (1 - ε) * e ≤ i) (h4 : i ≤ (1 + ε) * e) :
    a ≤ (1 + η) / V * b ∧ (1 - η) / V * b ≤ a := by
  have hε' : 0 < 1 - ε := by linarith
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hV]
    have k1 : V * a * ((1 - ε) * e) ≤ V * a * i :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hV.le ha)
    have k2 : (1 + ε) * (b * e) = (1 - ε) * (1 + η) * (b * e) := by rw [hkey]
    have k3 : (1 - ε) * e * (a * V) ≤ (1 - ε) * e * ((1 + η) * b) := by
      linarith [k1, h1, k2]
    exact le_of_mul_le_mul_left k3 (mul_pos hε' he)
  · rw [div_mul_eq_mul_div, div_le_iff₀ hV]
    have k1 : V * a * i ≤ V * a * ((1 + ε) * e) :=
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hV.le ha)
    have k2 : (1 + ε) * (1 - η) * (b * e) = (1 - ε) * (1 + η) * (1 - η) * (b * e) := by
      rw [hkey]
    have k3 : 0 ≤ (1 - ε) * η ^ 2 * (b * e) :=
      mul_nonneg (mul_nonneg hε'.le (sq_nonneg η)) (mul_nonneg hb he.le)
    have k4 : (1 + ε) * e * ((1 - η) * b) ≤ (1 + ε) * e * (a * V) := by
      linarith [k1, h2, k2, k3]
    exact le_of_mul_le_mul_left k4 (mul_pos (by linarith) he)

def volUSet (B : Set (UCo N)) : Set (UNgrp N) := {k | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)}

theorem volUSet_measurable {δ : ℝ}
    (hinj : Set.InjOn (fun x : UCo N => NormedSpace.exp (skMat x)) (Metric.ball 0 δ))
    {B : Set (UCo N)} (hB : MeasurableSet B) (hBs : B ⊆ Metric.ball 0 δ) :
    MeasurableSet (volUSet B) := by
  set F : UCo N → (Fin N → Fin N → ℂ) := fun x => Matrix.of.symm (NormedSpace.exp (skMat x)) with hF
  set G : UNgrp N → (Fin N → Fin N → ℂ) := fun k => Matrix.of.symm (toM k) with hG
  have hS : volUSet B = G ⁻¹' (F '' B) := by
    ext k
    simp only [volUSet, Set.mem_preimage, Set.mem_image, hF, hG]
    constructor
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, hx, by rw [hk]⟩
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, hx, (Matrix.of.symm.injective hk).symm⟩
  have hGc : Continuous G := continuous_toM _
  have hexp : Continuous (fun X : Matrix (Fin N) (Fin N) ℂ => NormedSpace.exp X) := by
    let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℚ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
    exact @NormedSpace.exp_continuous (Matrix (Fin N) (Fin N) ℂ) _ _
      (inferInstanceAs (CompleteSpace (Fin N → Fin N → ℂ)))
  have hFc : Continuous F := hexp.comp volU_continuous_skMat
  rw [hS]
  refine hGc.measurable ?_
  refine MeasurableSet.image_of_continuousOn_injOn hB hFc.continuousOn ?_
  intro x hx y hy hxy
  exact hinj (hBs hx) (hBs hy) (Matrix.of.symm.injective hxy)

theorem volU_image_eq (B : Set (UCo N)) (ρ : ℝ) :
    chartWR '' (B ×ˢ Metric.ball 0 ρ) = qrMap '' (volUSet B ×ˢ Metric.ball (volUOne N) ρ) := by
  ext Z
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have hmem : NormedSpace.exp (skMat x) ∈ Set.range (fun g : UNgrp N => toM g) := by
      rw [range_toM]
      exact volU_exp_inUJ x
    obtain ⟨k, hk⟩ := hmem
    have hk' : toM k = NormedSpace.exp (skMat x) := hk
    refine ⟨(k, t + volUOne N), ⟨⟨x, hx, hk'⟩, ?_⟩, ?_⟩
    · show dist (t + volUOne N) (volUOne N) < ρ
      rw [dist_eq_norm, add_sub_cancel_right, ← dist_zero_right]
      exact ht
    · simp only [qrMap, chartWR, volU_upMat_add, hk']
  · rintro ⟨⟨k, t⟩, ⟨⟨x, hx, hk⟩, ht⟩, rfl⟩
    refine ⟨(x, t - volUOne N), ⟨hx, ?_⟩, ?_⟩
    · show dist (t - volUOne N) 0 < ρ
      rw [dist_zero_right, ← dist_eq_norm]
      exact ht
    · have ht' : upMat t = 1 + upMat (t - volUOne N) := by
        rw [← volU_upMat_add, sub_add_cancel]
      have hk' : toM k = NormedSpace.exp (skMat x) := hk
      simp only [qrMap, chartWR, ht']
      rw [hk']

end ReciprocityTheory.ChartRestriction.DS
end
end

