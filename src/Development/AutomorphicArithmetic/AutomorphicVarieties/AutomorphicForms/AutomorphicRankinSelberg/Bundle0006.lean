module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RowRep
section
open scoped MatrixGroups

theorem UpperTheory.V.Af.Rs.rowRep :
    UpperTheory.V.Af.Rs.RowRep := by
  intro x
  set g := (x 0).gcd (x 1) with hg
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · obtain ⟨h0', h1'⟩ := Int.gcd_eq_zero_iff.mp h0
    refine ⟨0, 1, ?_⟩
    funext i
    fin_cases i <;> simp [h0', h1']
  · have hc : IsCoprime (x 0 / (g : ℤ)) (x 1 / (g : ℤ)) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
    obtain ⟨γ, -, hγ⟩ := ModularGroup.bottom_row_surj (R := ℤ)
      (show ![x 0 / (g : ℤ), x 1 / (g : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} by simpa using hc)
    refine ⟨g, γ, ?_⟩
    funext i
    have hi := congrFun hγ i
    simp only [UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hi]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left (x 0) (x 1))).symm
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right (x 0) (x 1))).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripFub
section
open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private lemma strip_meas : MeasurableSet strip := by
  have hre : Continuous fun z : ℍ => z.re := Complex.continuous_re.comp UpperHalfPlane.continuous_coe
  exact (measurableSet_le measurable_const hre.measurable).inter
    (measurableSet_lt hre.measurable measurable_const)

private lemma pt_re (x y : ℝ) (hy : 0 < y) : (pt x y).re = x := by
  rw [pt, ← UpperHalfPlane.coe_re, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  simp

private lemma vol_strip (hV : VolMap) :
    (volume : Measure ℍ).restrict strip = Measure.map (fun p : ℝ × ℝ => pt p.1 p.2)
      ((((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))).withDensity
        fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  obtain ⟨hm, hv⟩ := hV
  have hS := hm strip_meas
  have h1 : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have h2 : (fun p : ℝ × ℝ => pt p.1 p.2) ⁻¹' strip ∩ univ ×ˢ Ioi 0 = Ico 0 1 ×ˢ Ioi 0 := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_Ico, strip,
      mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [pt_re x y hy] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [pt_re x y hy]
      exact ⟨h, hy⟩
  rw [hv, Measure.restrict_map hm strip_meas, restrict_withDensity hS, h1,
    Measure.restrict_restrict hS, h2, Measure.prod_restrict]

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.stripFub :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.StripFub := by
  intro hV H hH
  have hf : Measurable fun p : ℝ × ℝ => pt p.1 p.2 := hV.1
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) := by fun_prop
  have hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))),
      ENNReal.ofReal (1 / p.2 ^ 2) < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hμ := vol_strip hV
  have hI : Integrable H ((volume : Measure ℍ).restrict strip) := hH
  rw [hμ] at hI
  have hHm := hI.1
  rw [integrable_map_measure hHm hf.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hg hlt] at hI
  have hpt : ∀ p : ℝ × ℝ, (ENNReal.ofReal (1 / p.2 ^ 2)).toReal • (H ∘ fun p : ℝ × ℝ => pt p.1 p.2) p
      = ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2) := by
    intro p
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    rfl
  have hF : Integrable (fun p : ℝ × ℝ => ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2))
      (((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))) :=
    hI.congr (Filter.Eventually.of_forall hpt)
  have hinner : ∀ y : ℝ, ∫ x, ((1 / y ^ 2 : ℝ) : ℂ) * H (pt x y) ∂(volume.restrict (Ico (0:ℝ) 1))
      = (∫ x in (0:ℝ)..1, H (pt x y)) / ((y ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
      integral_Ico_eq_integral_Ioc, one_div, Complex.ofReal_inv, div_eq_inv_mul]
  refine ⟨?_, ?_⟩
  · have := hF.integral_prod_right
    simp only [hinner] at this
    exact this
  · calc ∫ z in strip, H z
        = ∫ p, H (pt p.1 p.2) ∂((((volume : Measure ℝ).restrict (Ico 0 1)).prod
            (volume.restrict (Ioi 0))).withDensity fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
          rw [hμ, integral_map hf.aemeasurable hHm]
      _ = ∫ p, ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2) ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod
            (volume.restrict (Ioi 0))) := by
          rw [integral_withDensity_eq_integral_toReal_smul hg hlt]
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ y in Ioi 0, ∫ x, ((1 / y ^ 2 : ℝ) : ℂ) * H (pt x y) ∂(volume.restrict (Ico (0:ℝ) 1)) :=
          integral_prod_symm _ hF
      _ = _ := by simp only [hinner]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIm
section
open MeasureTheory Set
open UpperHalfPlane hiding I

private theorem pt_re_im (x y : ℝ) (hy : 0 < y) :
    (UpperTheory.V.Af.Rs.pt x y).re = x ∧ (UpperTheory.V.Af.Rs.pt x y).im = y := by
  rw [UpperTheory.V.Af.Rs.pt, ← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_im,
    UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  simp

private theorem measurableSet_strip' : MeasurableSet UpperTheory.V.Af.Rs.strip := by
  have hre : Continuous fun z : ℍ => z.re := Complex.continuous_re.comp UpperHalfPlane.continuous_coe
  exact (measurableSet_le measurable_const hre.measurable).inter
    (measurableSet_lt hre.measurable measurable_const)

private theorem volume_restrict_strip_eq_map_withDensity (hV : UpperTheory.V.Af.Rs.VolMap) :
    (volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip =
      Measure.map (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2)
      ((((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))).withDensity
        fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  obtain ⟨hf, hvol⟩ := hV
  have hs : MeasurableSet ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip) :=
    hf measurableSet_strip'
  have hset : (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip ∩ (univ ×ˢ Ioi 0)
      = Ico (0:ℝ) 1 ×ˢ Ioi 0 := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_Ico,
      UpperTheory.V.Af.Rs.strip, mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [(pt_re_im x y hy).1] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [(pt_re_im x y hy).1]
      exact ⟨h, hy⟩
  have h0 : (volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ))) =
      ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hbase : ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))).restrict
      ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip) =
      ((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0)) := by
    rw [h0, Measure.restrict_restrict hs, hset, ← Measure.prod_restrict]
  rw [hvol, Measure.restrict_map hf measurableSet_strip', restrict_withDensity hs, hbase]

theorem UpperTheory.V.Af.Rs.stripIm :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.StripIm := by
  intro hV φ hφ hint
  have hf : Measurable fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2 := hV.1
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) := by fun_prop
  have hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))),
      ENNReal.ofReal (1 / p.2 ^ 2) < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have him : Continuous fun z : ℍ => z.im := Complex.continuous_im.comp UpperHalfPlane.continuous_coe
  have hm : Measurable fun z : ℍ => φ z.im := hφ.comp him.measurable
  show Integrable (fun z : ℍ => φ z.im) ((volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip)
  rw [volume_restrict_strip_eq_map_withDensity hV, integrable_map_measure hm.aestronglyMeasurable hf.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hg hlt]
  have h1 : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ico (0:ℝ) 1)) := integrable_const 1
  have h2 : Integrable (fun y => φ y / y ^ 2) (volume.restrict (Ioi (0:ℝ))) := hint
  refine (h1.mul_prod h2).congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
    with p hp
  simp only [Function.comp_apply, (pt_re_im p.1 p.2 hp).2,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / p.2 ^ 2), smul_eq_mul, one_mul]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIntAlt
section
open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped MatrixGroups

private lemma UpperTheory.V.Af.Rs.stripInt_maj (A B s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun y : ℝ => (if y ≤ 1 then A * y ^ s else B) / y ^ 2) (Ioi 0) := by
  have hsplit : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun y : ℝ => y ^ (s - 2)) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1.mono_set
        (le_of_eq (uIoc_of_le zero_le_one).symm)
    have h1' : IntegrableOn (fun y : ℝ => A * y ^ (s - 2)) (Ioc 0 1) := h1.const_mul A
    refine h1'.congr_fun ?_ measurableSet_Ioc
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only [if_pos hy.2]
    rw [Real.rpow_sub hy0, Real.rpow_two, mul_div_assoc]
  · have h2 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    have h2' : IntegrableOn (fun y : ℝ => B * y ^ (-2 : ℝ)) (Ioi 1) := h2.const_mul B
    refine h2'.congr_fun ?_ measurableSet_Ioi
    intro y hy
    have hy1 : (1:ℝ) < y := hy
    have hy0 : 0 < y := by linarith
    simp only [if_neg (not_le.mpr hy1)]
    rw [Real.rpow_neg hy0.le, Real.rpow_two, div_eq_mul_inv]

theorem UpperTheory.V.Af.Rs.stripInt :
    UpperTheory.V.Af.Rs.StripIm → UpperTheory.V.Af.Rs.StripInt := by
  intro hIm F hF s hs
  obtain ⟨hcont, C, hC⟩ := hF
  have hbound : ∀ z : ℍ, ‖F z‖ ≤ 8 * C := by
    intro z
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    have h4 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := (g • z).im_pos
    have hw : 1 / 2 ≤ (g • z).im := by nlinarith
    have hC' := hC g⁻¹ (g • z) hw
    rw [inv_smul_smul] at hC'
    have h3 : (1 / 2 : ℝ) ^ 3 ≤ (g • z).im ^ 3 := pow_le_pow_left₀ (by norm_num) hw 3
    nlinarith [norm_nonneg (F z)]
  have hhigh : ∀ z : ℍ, 1 < z.im → ‖F z‖ * z.im ^ s ≤ C := by
    intro z hz
    have hC' := hC 1 z (by linarith)
    rw [one_smul] at hC'
    have hle : z.im ^ s ≤ z.im ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hz.le (by push_cast; linarith [hs.2])
    calc ‖F z‖ * z.im ^ s ≤ ‖F z‖ * z.im ^ 3 :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ ≤ C := hC'
  have hmeas : Measurable (fun y : ℝ => if y ≤ 1 then 8 * C * y ^ s else C) :=
    Measurable.ite measurableSet_Iic ((measurable_id.pow_const s).const_mul _) measurable_const
  have hφ := hIm _ hmeas (UpperTheory.V.Af.Rs.stripInt_maj (8 * C) C s hs.1)
  refine Integrable.mono' hφ ?_ ?_
  · have hc : Continuous fun z : ℍ => F z * ((z.im ^ s : ℝ) : ℂ) :=
      hcont.mul (Complex.continuous_ofReal.comp
        (UpperHalfPlane.continuous_im.rpow_const fun _ => Or.inr (by linarith [hs.1])))
    exact hc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    have hy := z.im_pos
    rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hy.le s)]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right (hbound z) (Real.rpow_nonneg hy.le s)
    · exact hhigh z (not_le.mp h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TEq
section
open MeasureTheory Set UpperTheory.V.Af.Rs
open UpperHalfPlane hiding I
open scoped MatrixGroups

theorem UpperTheory.V.Af.Rs.tEq :
    UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.Unfold → UpperTheory.V.Af.Rs.GcdSum → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.Swap → UpperTheory.V.Af.Rs.LBd → UpperTheory.V.Af.Rs.TEq := by
  intro hRB hSI hUnf hGcd hKer hSw hLB L _ ψ F G hG hF hGn s hs
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨hkc, hk0, hkz, hkrow, hkn, -⟩ := hKer s hs'
  obtain ⟨hint, hsum⟩ := hSw L G hGn s hs
  have hrow : ∀ x : Cop, ∃ γ : SL(2, ℤ), row γ = (x : Fin 2 → ℤ) := fun x =>
    ((hRB.2 UpperHalfPlane.I x).exists).imp fun γ h => h.1
  have hone : ∀ (γ : SL(2, ℤ)) (z : ℍ), G (cls L (row γ)) z = F (γ • z) := by
    intro γ z
    have := hG 1 γ z
    simpa using this
  have hGn' : ∀ (n : ℕ) (γ : SL(2, ℤ)) (z : ℍ),
      G (cls L ((n : ℤ) • row γ)) z = ψ n * G (cls L (row γ)) z := by
    intro n γ z
    rw [hG, hone]
  set a : (Fin 2 → ℤ) → ℂ := fun x => ∫ z in ModularGroup.fd, G (cls L x) z * (ker s x z : ℂ) with ha
  set c : ℕ → ℂ := fun n => ψ n / ((n : ℝ) ^ (2 * s) : ℝ) with hc
  have hs2 : (2 * s) ≠ 0 := by have := hs.1; linarith
  have hgcd := hGcd a c hsum.summable (hLB L ψ s hs.1.le).1
    (by simp [ha, hkz])
    (by simp [hc, Real.zero_rpow hs2])
    (by
      intro n x
      obtain ⟨γ, hγ⟩ := hrow x
      simp only [ha, hc]
      rw [← hγ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hkn]
      rw [hGn', Complex.ofReal_div]
      ring)
  have hunf := hUnf (fun z => F z * ((z.im ^ s : ℝ) : ℂ)) (fun x z => G (cls L x) z * (ker s x z : ℂ))
    (by
      have hc1 : Continuous (fun z : ℍ => z.im ^ s) :=
        UpperHalfPlane.continuous_im.rpow_const (fun _ => Or.inr (by linarith [hs.1]))
      exact hF.1.mul (Complex.continuous_ofReal.comp hc1))
    (hSI F hF s hs)
    (by intro γ z; rw [hkrow, hone])
    (fun x => hint x)
  rw [← hsum.tsum_eq, hgcd]
  congr 1
  exact hunf.tsum_eq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TailFin
section
open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped ENNReal

private lemma fd_meas : MeasurableSet ModularGroup.fd := by
  apply IsClosed.measurableSet
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (UpperHalfPlane.continuous_re.abs) continuous_const
  exact h1.inter h2

private lemma tail_fin :
    ∫⁻ y in Ioi (1 / 2 : ℝ), ENNReal.ofReal (1 / y ^ 2) < ∞ := by
  have h : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi (1 / 2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h' : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ioi (1 / 2 : ℝ)) := by
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) ≤ y := le_trans (by norm_num) (le_of_lt hy)
    simp only
    rw [Real.rpow_neg hy0, Real.rpow_two, one_div]
  exact h'.lintegral_lt_top

theorem UpperTheory.V.Af.Rs.fdFin :
    UpperTheory.V.Af.Rs.StripIm → UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdFin := by
  rintro - ⟨hm, hv⟩
  refine ⟨fd_meas, ?_⟩
  rw [hv, Measure.map_apply hm fd_meas]
  have hsub : (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' ModularGroup.fd ⊆
      (Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Ioi (1 / 2 : ℝ)) ∪ ((univ : Set ℝ) ×ˢ Iic (0 : ℝ)) := by
    rintro ⟨x, y⟩ hp
    rcases le_or_gt y 0 with hy | hy
    · exact Or.inr ⟨mem_univ _, hy⟩
    · left
      have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
      have hp' : UpperTheory.V.Af.Rs.pt x y ∈ ModularGroup.fd := hp
      have e : UpperTheory.V.Af.Rs.pt x y = ⟨_, him⟩ := ofComplex_apply_of_im_pos him
      have hre : (UpperTheory.V.Af.Rs.pt x y).re = x := by rw [e]; simp [UpperHalfPlane.re]
      have hi : (UpperTheory.V.Af.Rs.pt x y).im = y := by rw [e]; simp [UpperHalfPlane.im]
      have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hp'
      have h2 := hp'.2
      rw [hre] at h2
      rw [hi] at h3
      refine ⟨abs_le.1 h2, ?_⟩
      show (1 / 2 : ℝ) < y
      nlinarith
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
  rw [ENNReal.add_lt_top]
  constructor
  · rw [withDensity_apply _ (measurableSet_Icc.prod measurableSet_Ioi), ← Measure.prod_restrict,
      lintegral_prod _ (by fun_prop)]
    simp only [lintegral_const]
    rw [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.2 (Ioi_subset_Ioi (by norm_num))]
    exact ENNReal.mul_lt_top tail_fin (by simp)
  · rw [withDensity_absolutelyContinuous _ _ (by simp [Measure.prod_prod, Iic_inter_Ioi])]
    exact ENNReal.zero_lt_top
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.UnfMMp
section
open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal

private lemma UpperTheory.V.Af.Rs.unfM_mp (γ : SL(2, ℤ)) :
    MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
  have : (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z := rfl
  rw [this]
  exact measurePreserving_smul _ _

theorem UpperTheory.V.Af.Rs.unfM :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.FdCount → UpperTheory.V.Af.Rs.UnfM := by
  intro hFin hCount
  unfold UpperTheory.V.Af.Rs.UnfM
  unfold UpperTheory.V.Af.Rs.FdFin at hFin
  unfold UpperTheory.V.Af.Rs.FdCount at hCount
  obtain ⟨hfdm, -⟩ := hFin
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  ext s hs
  rw [Measure.sum_apply _ hs]
  have step : ∀ γ : SL(2, ℤ), Measure.map (fun z : ℍ => γ • z) (volume.restrict ModularGroup.fd) s
      = ∫⁻ z in s, ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z) := by
    intro γ
    have hm : Measurable (fun z : ℍ => γ • z) := (UpperTheory.V.Af.Rs.unfM_mp γ).measurable
    have hm' : Measurable (fun z : ℍ => γ⁻¹ • z) := (UpperTheory.V.Af.Rs.unfM_mp γ⁻¹).measurable
    have hP : MeasurableSet ((fun z : ℍ => γ⁻¹ • z) ⁻¹' ModularGroup.fd) := hm' hfdm
    rw [Measure.map_apply hm hs, Measure.restrict_apply (hm hs)]
    have hind : (fun z : ℍ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z))
        = ((fun z : ℍ => γ⁻¹ • z) ⁻¹' ModularGroup.fd).indicator 1 := by
      ext z
      by_cases h : γ⁻¹ • z ∈ ModularGroup.fd
      · rw [indicator_of_mem h, indicator_of_mem (show z ∈ _ from h)]
        rfl
      · rw [indicator_of_notMem h, indicator_of_notMem (show z ∉ _ from h)]
    rw [hind, lintegral_indicator_one hP, Measure.restrict_apply hP,
      ← (UpperTheory.V.Af.Rs.unfM_mp γ).measure_preimage (hP.inter hs).nullMeasurableSet]
    congr 1
    ext z
    simp only [mem_preimage, mem_inter_iff, inv_smul_smul]
    exact and_comm
  rw [tsum_congr step]
  have hmeas : ∀ γ : SL(2, ℤ), AEMeasurable
      (fun z : ℍ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z))
      (volume.restrict s) := fun γ =>
    ((measurable_const.indicator hfdm).comp (UpperTheory.V.Af.Rs.unfM_mp γ⁻¹).measurable).aemeasurable
  rw [← lintegral_tsum hmeas]
  have hre : ∀ z : ℍ, ∑' γ : SL(2, ℤ), ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z)
      = ∑' γ : SL(2, ℤ), ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ • z) :=
    fun z => (Equiv.inv SL(2, ℤ)).tsum_eq
      (fun γ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ • z))
  simp_rw [hre]
  rw [lintegral_congr_ae (ae_restrict_of_ae hCount), setLIntegral_const, Measure.smul_apply]
  first
    | rw [two_mul, two_nsmul]
    | rw [smul_eq_mul]
    | simp [two_mul, two_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolumeOpenPosUpperHalfPlane
section
open MeasureTheory Set UpperHalfPlane in
private theorem UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane (U : Set ℍ) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (volume : Measure ℍ) U := by
  rw [pos_iff_ne_zero]
  intro h0
  have hac : (volume.comap UpperHalfPlane.coe : Measure ℍ) ≪ (volume : Measure ℍ) := by
    rw [volume_def]
    refine withDensity_absolutelyContinuous' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine Measurable.aemeasurable (Measurable.coe_nnreal_ennreal ?_)
      refine Continuous.measurable ?_
      refine .pow (.div₀ continuous_const ?_ ?_) _
      · exact continuous_im.subtype_mk _
      · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero
    · have hz : NNReal.mk z.im z.im_pos.le ≠ 0 := NNReal.ne_iff.mp z.im_ne_zero
      exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (one_div_ne_zero hz))
  have h1 := hac h0
  rw [measurableEmbedding_coe.comap_apply] at h1
  exact ((isOpenEmbedding_coe.isOpenMap U hU).measure_pos volume (hne.image _)).ne' h1

open MeasureTheory Set UpperHalfPlane in
theorem UpperTheory.V.Af.Rs.fdPos :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdPos := by
  intro _ φ hc h0 hint z hz hpos
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hint]
  have hV : IsOpen {w : ℍ | 0 < φ w} := isOpen_lt continuous_const hc
  rw [ModularGroup.fd_eq_closure_fdo] at hz
  have hne : ({w : ℍ | 0 < φ w} ∩ ModularGroup.fdo).Nonempty :=
    mem_closure_iff.mp hz _ hV hpos
  refine (UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane _ (hV.inter ModularGroup.isOpen_fdo) hne).trans_le
    (measure_mono ?_)
  rintro w ⟨hw, hw'⟩
  exact ⟨ne_of_gt hw, ModularGroup.fdo_subset_fd hw'⟩
end

