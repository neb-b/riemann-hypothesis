module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CoordGamma
section
noncomputable section

open Complex

namespace PositivityTheory.Rg.Sw.Glob.VacE

theorem coord_gamma (c t σ co si : ℝ) (hc : 0 < c) (ht : t ^ 2 = c ^ 2) (hσ : σ ^ 2 = 1) (hco : 0 < co)
    (hs : si ^ 2 + co ^ 2 = 1) :
    (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 /
        (((-t : ℝ) : ℂ) ^ 2 * (σ : ℂ) ^ 2 / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2) - I * t * σ * ((si * co : ℝ) : ℂ)) -
      I * t * σ * ((si / co : ℝ) : ℂ) = c := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hco' : (co : ℂ) ≠ 0 := by exact_mod_cast hco.ne'
  have htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast ht
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have hden : (c : ℂ) * co - I * t * σ * si ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    rcases this with h | h
    · exact hc.ne' h
    · exact hco.ne' h
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]
  rw [neg_sq, htC, hσC]
  have e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [e1]
  field_simp
  have htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2 := by rw [htC, hσC, mul_one]
  linear_combination (-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq

theorem coord_const (c t σ co si : ℝ) (hc : 0 < c) (ht : t ^ 2 = c ^ 2) (hσ : σ ^ 2 = 1) (hco : 0 < co)
    (hs : si ^ 2 + co ^ 2 = 1) :
    ((co⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2)) *
        ((Real.pi : ℂ) / (((-t : ℝ) : ℂ) ^ 2 * (σ : ℂ) ^ 2 / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2) -
          I * t * σ * ((si * co : ℝ) : ℂ))) * (((|t| / Real.pi : ℝ) : ℂ)) ^ 2 =
      co + I * (σ * t / c) * si := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hco' : (co : ℂ) ≠ 0 := by exact_mod_cast hco.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast ht
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have habs : ((|t| : ℝ) : ℂ) ^ 2 = (c : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs]; exact_mod_cast ht
  have hden : (c : ℂ) * co - I * t * σ * si ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    rcases this with h | h
    · exact hc.ne' h
    · exact hco.ne' h
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]
  rw [neg_sq, htC, hσC, div_pow, habs]
  have e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [e1]
  have key : (co : ℂ)⁻¹ * ((Real.pi : ℂ) / ((c : ℂ) * (co : ℂ)⁻¹ ^ 2)) *
      ((Real.pi : ℂ) / (co * ((c : ℂ) * co - I * t * σ * si))) * ((c : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2) =
      (c : ℂ) / ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [key, div_eq_iff hden]
  have htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2 := by rw [htC, hσC, mul_one]
  field_simp
  linear_combination (-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq

end PositivityTheory.Rg.Sw.Glob.VacE
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneAbs
section
noncomputable section

open MeasureTheory intervalIntegral

namespace PositivityTheory.Rg.Sw.Glob.DerOneAbsH

theorem integral_deriv_zero {X Ξ : Type*} [MeasurableSpace X] [Countable Ξ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (m : Measure X) [SFinite m] (F F' : X → ℝ → Ξ → ℂ)
    (hd : ∀ x ξ, ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s => F x s ξ) (F' x t ξ) t)
    (hcont : ∀ x ξ, Continuous fun t => F' x t ξ)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod (volume.restrict (Set.Ioc 0 1))))
    (hfin : ∫⁻ p : X × ℝ, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod (volume.restrict (Set.Ioc 0 1))) ≠ ⊤)
    (hsum0 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 0 ξ‖) (hsum1 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 1 ξ‖)
    (hint0 : Integrable (fun x => ∑' ξ, F x 0 ξ) m) (hint1 : Integrable (fun x => ∑' ξ, F x 1 ξ) m)
    (hends : ∫ x, ∑' ξ, F x 1 ξ ∂m = ∫ x, ∑' ξ, F x 0 ξ ∂m)
    (hconst : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∫ x, ∑' ξ, F' x t ξ ∂m = ∫ x, ∑' ξ, F' x 0 ξ ∂m) :
    ∫ x, ∑' ξ, F' x 0 ξ ∂m = 0 := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  have hae : ∀ ξ, AEMeasurable (fun p : X × ℝ => ‖F' p.1 p.2 ξ‖ₑ) (m.prod μ) := fun ξ => (hmeas ξ).enorm
  have hle : ∀ ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≤ ∫⁻ p, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) :=
    fun ξ => lintegral_mono fun p => ENNReal.le_tsum (f := fun ξ => ‖F' p.1 p.2 ξ‖ₑ) ξ
  have hI : ∀ ξ, Integrable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod μ) := fun ξ =>
    ⟨hmeas ξ, lt_of_le_of_lt (hle ξ) hfin.lt_top⟩
  have htsum : ∑' ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≠ ⊤ := by
    rw [← lintegral_tsum hae]; exact hfin

  have hftc : ∀ x ξ, ∫ t, F' x t ξ ∂μ = F x 1 ξ - F x 0 ξ := by
    intro x ξ
    rw [hμ, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (hd x ξ) ((hcont x ξ).intervalIntegrable 0 1)

  have hswap : ∀ ξ, ∫ x, (∫ t, F' x t ξ ∂μ) ∂m = ∫ t, (∫ x, F' x t ξ ∂m) ∂μ := fun ξ =>
    integral_integral_swap (f := fun x t => F' x t ξ) (hI ξ)

  have hbx : ∑' ξ, ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≤ ∫⁻ x, ∫⁻ t, ‖F' x t ξ‖ₑ ∂μ ∂m :=
          lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod _ (hae ξ)).symm
  have hbt : ∑' ξ, ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≤ ∫⁻ t, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ :=
          lintegral_mono fun t => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod_symm _ (hae ξ)).symm
  have S1 : ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_left.aestronglyMeasurable) hbx
  have S2 : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_right.aestronglyMeasurable) hbt

  have hslice : ∀ᵐ t ∂μ, ∀ ξ, AEStronglyMeasurable (fun x => F' x t ξ) m := by
    rw [ae_all_iff]
    intro ξ
    exact ((hmeas ξ).prod_swap).prodMk_left
  have hfinT : ∀ᵐ t ∂μ, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ≠ ⊤ := by
    have hmξ : ∀ ξ, AEMeasurable (fun t => ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := fun ξ => by
      simpa using ((hae ξ).prod_swap).lintegral_prod_right'
    have hm' : AEMeasurable (fun t => ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := AEMeasurable.tsum hmξ
    have : ∫⁻ t, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ ≠ ⊤ := by
      rw [lintegral_tsum hmξ]
      refine ne_top_of_le_ne_top htsum (le_of_eq (tsum_congr fun ξ => ?_))
      exact (lintegral_prod_symm _ (hae ξ)).symm
    filter_upwards [ae_lt_top' hm' this] with t ht using ht.ne
  have S3 : ∀ᵐ t ∂μ, ∫ x, ∑' ξ, F' x t ξ ∂m = ∑' ξ, ∫ x, F' x t ξ ∂m := by
    filter_upwards [hslice, hfinT] with t h1 h2 using integral_tsum h1 h2
  have hIoc : ∀ᵐ t ∂μ, t ∈ Set.Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc

  set c := ∫ x, ∑' ξ, F' x 0 ξ ∂m with hc
  have hμ1 : μ Set.univ = 1 := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Ioc]; simp
  have key : c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := by
    have : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∫ _t, c ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [S3, hIoc] with t h1 h2
      rw [← h1, hconst t h2]
    rw [this, MeasureTheory.integral_const, Measure.real, hμ1, ENNReal.toReal_one, one_smul]
  have hsub : ∀ᵐ x ∂m, ∑' ξ, ∫ t, F' x t ξ ∂μ = ∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ := by
    filter_upwards [hsum0, hsum1] with x h0 h1
    simp only [hftc]
    exact (h1.of_norm).tsum_sub h0.of_norm
  calc c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := key
    _ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ := S2
    _ = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m := tsum_congr fun ξ => (hswap ξ).symm
    _ = ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m := S1.symm
    _ = ∫ x, (∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ) ∂m := integral_congr_ae hsub
    _ = ∫ x, ∑' ξ, F x 1 ξ ∂m - ∫ x, ∑' ξ, F x 0 ξ ∂m := integral_sub hint1 hint0
    _ = 0 := by rw [hends, sub_self]

end PositivityTheory.Rg.Sw.Glob.DerOneAbsH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ExistsCircleDetNe
section
noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacU

variable {n : ℕ}

theorem exists_circle_det_ne (W : Matrix (Fin n) (Fin n) ℂ) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ (W + lam • 1).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set p := (-W).charpoly with hp
  have hp0 : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hev : ∀ x : ℂ, p.eval x = (W + x • 1).det := by
    intro x
    rw [hp, Matrix.eval_charpoly]
    congr 1
    rw [Matrix.scalar_apply, sub_neg_eq_add, add_comm, Matrix.smul_one_eq_diagonal]
  let r : Fin (n + 1) → ℝ := fun k => (k : ℝ) / ((n : ℝ) + 1)
  let f : Fin (n + 1) → ℂ := fun k => cexp (I * (r k : ℂ))
  have hr0 : ∀ k, 0 ≤ r k := fun k => by simp only [r]; positivity
  have hr1 : ∀ k, r k < 1 := fun k => by
    simp only [r]; rw [div_lt_one (by positivity)]; exact_mod_cast k.2
  have hf : Function.Injective f := by
    intro k k' h
    obtain ⟨z, hz⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    have hre : r k = r k' + z * (2 * Real.pi) := by
      have := congrArg Complex.im hz
      simpa [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im] using this
    have hz0 : z = 0 := by
      by_contra hz0
      have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz0
      have habs : |(z : ℝ) * (2 * Real.pi)| < 1 := by
        rw [abs_lt]; constructor <;> linarith [hr0 k, hr0 k', hr1 k, hr1 k']
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
      nlinarith [Real.pi_gt_three]
    rw [hz0] at hre
    simp only [Int.cast_zero, zero_mul, add_zero, r] at hre
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : (k : ℝ) = k' := by
      field_simp at hre; linarith
    exact Fin.ext (by exact_mod_cast this)
  have hroot : ∀ k, f k ∈ p.roots.toFinset := by
    intro k
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot, hev]
    apply hcon
    simp only [f]
    rw [Complex.norm_exp]
    simp
  have hcard : (Finset.univ.image f).card ≤ p.roots.toFinset.card :=
    Finset.card_le_card (fun x hx => by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx; exact hroot k)
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at hcard
  have h1 := (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
  have h2 : p.natDegree = n := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  omega

theorem unitary_diag (W : Matrix (Fin n) (Fin n) ℂ) (hW : Wᴴ * W = 1) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ), Pᴴ * P = 1 ∧ P * Pᴴ = 1 ∧ (∀ j, ‖w j‖ = 1) ∧
      W = P * diagonal w * Pᴴ := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  obtain ⟨lam, hlam1, hdet⟩ := exists_circle_det_ne W
  have hlam0 : lam ≠ 0 := by intro h; rw [h, norm_zero] at hlam1; exact zero_ne_one hlam1
  have hconj : starRingEnd ℂ lam * lam = 1 := by
    rw [Complex.conj_mul', hlam1]; simp
  set V' := lam⁻¹ • W with hV'
  have hV'u : V'ᴴ * V' = 1 := by
    rw [hV', Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hW]
    rw [RCLike.star_def, map_inv₀]
    rw [show (starRingEnd ℂ lam)⁻¹ * lam⁻¹ = (starRingEnd ℂ lam * lam)⁻¹ by rw [mul_inv], hconj, inv_one, one_smul]
  set B := 1 + V' with hB
  set A := 1 - V' with hA
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    have : B = lam⁻¹ • (W + lam • 1) := by
      rw [hB, hV', smul_add, smul_smul, inv_mul_cancel₀ hlam0, one_smul, add_comm]
    rw [this, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hlam0)) hdet
  set H := (Complex.I • A) * B⁻¹ with hH
  have hHB : H * B = Complex.I • A := by
    rw [hH, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBdet, Matrix.mul_one]
  have hBc : IsUnit Bᴴ.det := by rw [Matrix.det_conjTranspose]; exact hBdet.star
  have hid : Bᴴ * A = -(Aᴴ * B) := by
    rw [hB, hA, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hV'u]
    abel
  have hHerm : H.IsHermitian := by
    have hk : Bᴴ * Hᴴ * B = Bᴴ * H * B := by
      have e1 : Bᴴ * Hᴴ = -(Complex.I • Aᴴ) := by
        rw [← Matrix.conjTranspose_mul, hHB, Matrix.conjTranspose_smul]
        simp [RCLike.star_def, Complex.conj_I]
      rw [e1, Matrix.mul_assoc, hHB, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, hid, smul_neg]
    have hk2 : Hᴴ = H := by
      have := congrArg (fun M => (Bᴴ)⁻¹ * M * B⁻¹) hk
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hBdet, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBdet,
        Matrix.mul_one] at this
    exact hk2
  set U : Matrix (Fin n) (Fin n) ℂ := (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℝ := hHerm.eigenvalues with hd
  have hUu : Uᴴ * U = 1 := by
    rw [hU]; exact Matrix.mem_unitaryGroup_iff'.1 hHerm.eigenvectorUnitary.2
  have hUu' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUu
  have hspec : H = U * diagonal (fun j => ((d j : ℝ) : ℂ)) * Uᴴ := by
    have := hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hdI : ∀ j, ((d j : ℝ) : ℂ) + Complex.I ≠ 0 := by
    intro j h; have := congrArg Complex.im h; simp at this
  set E : Fin n → ℂ := fun j => (Complex.I - (d j : ℂ)) / (Complex.I + (d j : ℂ)) with hE
  have hHdiag : H + Complex.I • 1 = U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ := by
    have e : diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) = diagonal (fun j => ((d j : ℝ) : ℂ)) + Complex.I • 1 := by
      rw [Matrix.smul_one_eq_diagonal, diagonal_add]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu', hspec]
  have hHI : IsUnit (H + Complex.I • 1).det := by
    rw [isUnit_iff_ne_zero, hHdiag, Matrix.det_mul, Matrix.det_mul, det_diagonal]
    have hU1 : U.det * Uᴴ.det = 1 := by rw [← Matrix.det_mul, hUu', Matrix.det_one]
    intro h0
    have : U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = 0 := by
      rw [show U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = U.det * (∏ j, (((d j : ℝ) : ℂ) + Complex.I)) * Uᴴ.det by ring]
      exact h0
    rw [hU1, one_mul] at this
    exact (Finset.prod_ne_zero_iff.2 fun j _ => hdI j) this
  have hEq1 : (H + Complex.I • 1) * V' = Complex.I • 1 - H := by
    have := hHB
    rw [hB, hA, Matrix.mul_add, Matrix.mul_one, smul_sub] at this
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at this
    rw [← this]
    abel
  have hEq2 : (H + Complex.I • 1) * (U * diagonal E * Uᴴ) = Complex.I • 1 - H := by
    rw [hHdiag]
    have e1 : U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ * (U * diagonal E * Uᴴ) =
        U * (diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * diagonal E) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUu, Matrix.one_mul]
    rw [e1, diagonal_mul_diagonal]
    have e2 : (fun j => (((d j : ℝ) : ℂ) + Complex.I) * E j) = fun j => Complex.I - ((d j : ℝ) : ℂ) := by
      funext j
      have hdI' : Complex.I + ((d j : ℝ) : ℂ) ≠ 0 := by rw [add_comm]; exact hdI j
      rw [hE]; simp only; rw [add_comm ((d j : ℝ) : ℂ) Complex.I]; field_simp
    rw [e2, hspec]
    have e3 : diagonal (fun j => Complex.I - ((d j : ℝ) : ℂ)) = Complex.I • 1 - diagonal (fun j => ((d j : ℝ) : ℂ)) := by
      rw [Matrix.smul_one_eq_diagonal, ← diagonal_sub]
    rw [e3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu']
  have hV'eq : V' = U * diagonal E * Uᴴ := by
    have h0 : (H + Complex.I • 1) * (V' - U * diagonal E * Uᴴ) = 0 := by
      rw [Matrix.mul_sub, hEq1, hEq2, sub_self]
    have := congrArg (fun M => (H + Complex.I • 1)⁻¹ * M) h0
    simp only [Matrix.mul_zero] at this
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHI, Matrix.one_mul, sub_eq_zero] at this
    exact this
  refine ⟨U, fun j => lam * E j, hUu, hUu', ?_, ?_⟩
  · intro j
    rw [norm_mul, hlam1, one_mul, hE]
    simp only
    rw [norm_div]
    have h1 : ‖Complex.I - ((d j : ℝ) : ℂ)‖ = ‖Complex.I + ((d j : ℝ) : ℂ)‖ := by
      rw [← Complex.norm_conj (Complex.I + _)]; simp [Complex.conj_I, Complex.conj_ofReal, ← neg_add']
      rw [← norm_neg]; congr 1; ring
    rw [h1, div_self]
    intro h0; rw [norm_eq_zero] at h0; exact hdI j (by rw [add_comm]; exact h0)
  · have : W = lam • V' := by rw [hV', smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    have hd2 : diagonal (fun j => lam * E j) = lam • diagonal E := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
    rw [this, hV'eq, hd2, Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.Rg.Sw.Glob.VacU
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FibFact
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositivityTheory.Rg.Sw.Glob.Fib

variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X]
  [BorelSpace X]

theorem fib_meas (μ : Measure X) [μ.IsAddRightInvariant] (π : X →+ (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) →+ X) (hπs : ∀ u, π (s u) = u) (g : X → ℝ≥0∞) (hg : Measurable g)
    (hgs : ∀ z u, g (z + s u) = g z)
    (hloc : ∀ K : Set (Fin m → Fin n → ℂ), IsCompact K → ∫⁻ z, K.indicator 1 (π z) * g z ∂μ ≠ ∞) :
    ∃ c : ℝ≥0, (μ.withDensity g).map π = c • (volume : Measure (Fin m → Fin n → ℂ)) := by
  set ν : Measure (Fin m → Fin n → ℂ) := (μ.withDensity g).map π with hν
  have hπm : Measurable π := hπ.measurable
  have hint : ∀ a : (Fin m → Fin n → ℂ) → ℝ≥0∞, Measurable a → ∫⁻ u, a u ∂ν = ∫⁻ z, a (π z) * g z ∂μ := by
    intro a ha
    rw [hν, lintegral_map ha hπm]
    have e := lintegral_withDensity_eq_lintegral_mul μ hg (ha.comp hπm)
    simp only [Function.comp_def] at e
    rw [e]
    congr 1; ext z; simp [mul_comm]
  have hinv : ν.IsAddLeftInvariant := by
    refine ⟨fun u => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add u) hA, ← lintegral_indicator_one (measurable_const_add u hA),
      ← lintegral_indicator_one hA, hint _ (measurable_one.indicator (measurable_const_add u hA)),
      hint _ (measurable_one.indicator hA)]
    have key : ∀ z, ((fun x => u + x) ⁻¹' A).indicator 1 (π z) * g z =
        (fun z => A.indicator 1 (π z) * g z) (z + s u) := by
      intro z
      simp only [map_add (f := _), hπs, hgs]
      congr 1
      by_cases h : u + π z ∈ A
      · simp [Set.indicator, h, add_comm]
      · simp [Set.indicator, h, add_comm]
    simp_rw [key]
    exact lintegral_add_right_eq_self (fun z => A.indicator 1 (π z) * g z) (s u)
  have hfc : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [← lintegral_indicator_one hK.measurableSet, hint _ (measurable_one.indicator hK.measurableSet)]
    exact (hloc K hK).lt_top
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact ⟨Measure.addHaarScalarFactor ν volume, Measure.isAddLeftInvariant_eq_smul ν volume⟩

end PositivityTheory.Rg.Sw.Glob.Fib
end
end

