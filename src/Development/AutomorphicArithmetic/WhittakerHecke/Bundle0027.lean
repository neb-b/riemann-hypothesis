module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0026
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0021
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0015
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0016
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0002
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0025
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0022
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0020

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAtInertPlace
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) (z : (A E)ˣ)
    (h : (z : A E) = AdeleBaseChange.adeleMap ℚ E (y : A ℚ)) : em E (aE y) = aE z := by
  apply Units.ext
  ext i j
  rw [UpperTheory.ConvolutionTheory.RankTwoDescent.em, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [aE, h]

theorem UpperTheory.exists_whittaker_heckeEigenvalues_at_inert_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
          CenN P ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ) φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∀ v : H.P ℚ, ¬ Bad N v → ∀ w : H.P E, w.under (𝓞 ℚ) = v → H.Inert D v w →
          ∃ m : ℕ → ℂ, m 0 = 1 ∧
            (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (pv v ^ k)) * g) = m k * Wo D φ g) ∧
            ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) =
              PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := by
  intro E _ _ _ D P ω χ _ _ L N φ hA hG a hIs v hv w hw hI
  obtain ⟨-, B, hsat, hEig⟩ := hG.fix w (by rw [hw]; exact hv)
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk P w B).1 hsat))
  obtain ⟨-, -, hleft, -⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hA
  have hEw := UpperTheory.eigAt_cmDatumOperator_of_eigAt E D φ w _ hA.cont hEig
  obtain ⟨χw, hχ, hχe⟩ := UpperTheory.exists_good_character_of_inert_CMDatum E D v w (hG.pl v hv) hI
  have hnl : ∀ b h, Wo D φ (H.lc w (H.nL b) * h) = χw b * Wo D φ h := fun b h => by
    obtain ⟨u, t, e1, e2⟩ := hχe b
    rw [(H.lcLaws E w).1, e1, ← e2]
    exact hleft ![u, t] h
  obtain ⟨ϖ', hϖ', hz, -⟩ := hI.unif (atFin v (unif v)) (unif_spec v)
  have hem : ∀ k : ℕ, em E (aE (pv v ^ k)) = aE (H.idl w ϖ' ^ k) := fun k => by
    refine em_aE _ _ ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, hz, Dat.mkE, map_zero, zero_mul, add_zero]
    rfl
  have hnv : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  have hqw : H.q w = (normV v : ℂ) ^ 2 := by
    have : H.q w = (normV w : ℂ) := by simp [H.q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [this, hI.norm]
    push_cast
    rfl
  have hqv : (normV v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsq : H.q w ^ (1 / 2 : ℂ) = (normV v : ℂ) := by
    rw [hqw]
    have e : ((normV v : ℂ) ^ 2) = ((((normV v : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
    rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    simp
  refine ⟨fun k => ((normV v : ℂ) ^ k)⁻¹ * ∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i), by simp,
    fun k g hg => ?_, fun _ => ?_⟩
  · have h := UpperTheory.eigenform_shintani_formula_at_place E w ϖ' hϖ' χw hχ α β _ hEw hnl g (hg w hw) k
    rw [hsq] at h
    rw [hem, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hqv), one_mul]
  · have h1 := hIs.inert v hv w hw hI.norm α β hsat
    have h2 := UpperTheory.powerSeries_completeHomogeneous_two_mul_eq_one ((α * χ.val v : ℂˣ) : ℂ) ((β * χ.val v : ℂˣ) : ℂ)
    have h3 : (PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k *
        (((normV v : ℂ) ^ k)⁻¹ * ∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i))) =
        PowerSeries.mk fun k : ℕ => ∑ i ∈ Finset.range (k + 1),
          ((α * χ.val v : ℂˣ) : ℂ) ^ i * ((β * χ.val v : ℂˣ) : ℂ) ^ (k - i) := by
      congr 1
      funext k
      rw [Nat.cast_pow, mul_comm ((normV v : ℂ) ^ k), mul_assoc, ← mul_assoc ((normV v : ℂ) ^ k),
        mul_inv_cancel₀ (pow_ne_zero k hqv), one_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
      rw [Nat.add_sub_cancel_left, Units.val_mul, Units.val_mul]
      ring
    rw [h3]
    linear_combination (PowerSeries.mk fun k : ℕ => ∑ i ∈ Finset.range (k + 1),
          ((α * χ.val v : ℂˣ) : ℂ) ^ i * ((β * χ.val v : ℂˣ) : ℂ) ^ (k - i)) * h1 -
      (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) * h2
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.MaximalCompactIntegralUnipotentNormFinite
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem row_nU (b : A ℚ) (g : G1 ℚ) (u : (A ℚ)ˣ) (j : Fin 2) :
    (gl (nU b * g) * dM u).val 1 j = (gl g * dM u).val 1 j := by
  rw [Units.val_mul, Units.val_mul, M.val_gl, M.val_gl, M.val_mul]
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem row_mD (a u : (A ℚ)ˣ) (k : G1 ℚ) (j : Fin 2) :
    (gl (mD a * cD u k) * dM u).val 1 j = ((a⁻¹ * u : (A ℚ)ˣ) : A ℚ) * G.row k j := by
  have h : gl (mD a * cD u k) = gl (mD a) * gl (cD u k) := map_mul _ _ _
  rw [h, mul_assoc, M.gl_cD, Units.val_mul, Units.val_mul, M.val_gl, M.val_gl]
  simp [mD, dM, G.row, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, Matrix.vecMul, dotProduct]

theorem UpperTheory.maximalCompact_integral_unipotent_norm_finite :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        (_root_.UpperTheory.ConvolutionTheory.R2.M.J0 M₀ fun g => ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ)) ≠ ⊤ := by
  intro E _ _ D ω φ hA M₀ Φ hΦ t u hu
  obtain ⟨B, hB⟩ := hA.bdd
  obtain ⟨hmp, hme⟩ := UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact M₀ t u hu
  obtain ⟨C, hC⟩ := UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded Φ hΦ 2 (by norm_num)
  obtain ⟨-, hiy, -, hU⟩ := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one
  haveI := M₀.prob
  have hw : ∀ g : G1 ℚ, ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ) ≤
      ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ := by
    intro g
    refine (lintegral_mono (g := fun _ => ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ)
      fun b => ?_).trans ?_
    · simp only [Un.Uu, row_nU, enorm_mul]
      refine mul_le_mul_left ?_ _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    · rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one]
  let F : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j‖ₑ * ENNReal.ofReal (ab p.1 ^ (2 : ℝ))
  have hF : Measurable F := by
    have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j :=
      (continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j =>
        (Units.continuous_val.comp continuous_fst).mul ((M.continuous_entry 1 j).comp continuous_snd))
    have h2 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => ab p.1 ^ (2 : ℝ) :=
      (M.continuous_ab.comp continuous_fst).rpow_const fun _ => Or.inr (by norm_num)
    exact h1.measurable.enorm.mul h2.measurable.ennreal_ofReal
  have hI : ∫⁻ p, F p ∂M₀.ν ≤ C := by
    rw [Meas.ν, lintegral_prod_symm _ hF.aemeasurable]
    have hae : ∀ᵐ k ∂M₀.κ, k ∈ KK ℚ := by
      rw [ae_iff]
      exact M₀.supp
    refine (lintegral_mono_ae (g := fun _ => (C : ℝ≥0∞)) (hae.mono fun k hk => hC k hk)).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  unfold M.J0
  rw [← hmp.lintegral_comp_emb hme]
  have hK : ENNReal.ofReal B * ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hK (ENNReal.coe_ne_top (r := C))) ?_
  refine le_trans ?_ (mul_le_mul_right hI _)
  rw [← lintegral_const_mul _ hF]
  refine lintegral_mono fun p => ?_
  refine (mul_le_mul_right (hw _) _).trans (le_of_eq ?_)
  have e1 : (fun j => (iy (Real.exp t) : A ℚ) * (gl (mD (Un.aa t u p.1) * cD u p.2) * dM u).val 1 j) =
      fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j := by
    funext j
    rw [row_mD, ← mul_assoc, ← Units.val_mul]
    have : (iy (Real.exp t) * ((Un.aa t u p.1)⁻¹ * u) : (A ℚ)ˣ) = p.1 := by
      have h : ∀ x y z : (A ℚ)ˣ, x * ((x * y * z⁻¹)⁻¹ * y) = z := fun x y z => by
        rw [mul_left_comm, ← mul_assoc, mul_right_comm, mul_comm x y, mul_assoc _ y x, mul_comm y x, mul_inv, inv_inv,
          mul_right_comm, inv_mul_cancel, one_mul]
      exact h _ _ _
    rw [this]
  have e2 : M.wt (Un.aa t u p.1) = ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) * ENNReal.ofReal (ab p.1 ^ (2 : ℝ)) := by
    have h : ab (Un.aa t u p.1) = Real.exp t * (ab p.1)⁻¹ := by
      have h0 : ab (Un.aa t u p.1) = ab (iy (Real.exp t)) * ab u * ab (p.1⁻¹ : (A ℚ)ˣ) := by
        rw [← M.ab_mul, ← M.ab_mul]
        rfl
      rw [h0, hiy _ (Real.exp_ne_zero t), hU u hu, M.ab_inv, abs_of_pos (Real.exp_pos t), mul_one]
    rw [M.wt, h, ← ENNReal.ofReal_mul (by positivity), Real.rpow_two, mul_inv, inv_inv, mul_pow]
  simp only [e1, e2, F]
  ring
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.UnfoldedIntegrandMeasurableIntegrableOfReGtFour
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.unfoldedIntegrand_measurable_integrable_of_re_gt_four :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ s : ℂ, 4 < s.re →
        Measurable (Un.Hh D χ φ Φ s) ∧ Integrable (Un.Hh D χ φ Φ s) ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) := by
  intro E _ _ D ω χ φ hA hU hχ M₀ Φ hΦ s hs
  haveI := M₀.prob
  have hχn : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    have h := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hχ a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one, hU a, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  have hχe : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ₑ = 1 := by
    intro a
    rw [← ofReal_norm, hχn a, ENNReal.ofReal_one]
  have hcn : ∀ (y : IdeleGroup ℚ) (w : ℂ), ‖((ab y : ℝ) : ℂ) ^ w‖ₑ = ENNReal.ofReal (ab y ^ w.re) := by
    intro y w
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos (M.ab_pos y)]
  have hW := UpperTheory.measurable_whittaker_idele_diagTorus_mul E D ω φ hA
  have hχm : Measurable fun y : IdeleGroup ℚ => ((χ.1 y : ℂˣ) : ℂ) :=
    (Units.continuous_val.comp χ.2.1).measurable
  have habm : Measurable fun y : IdeleGroup ℚ => ab y := M.continuous_ab.measurable
  have hΦc : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * row p.2 j :=
    (continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j =>
      (Units.continuous_val.comp continuous_fst).mul ((M.continuous_entry 1 j).comp continuous_snd))
  have hΦm := hΦc.measurable
  have hcp : ∀ w : ℂ, Measurable fun y : IdeleGroup ℚ => ((ab y : ℝ) : ℂ) ^ w := fun w =>
    (Complex.measurable_ofReal.comp habm).pow_const w
  have hrp : ∀ x : ℝ, Measurable fun y : IdeleGroup ℚ => ENNReal.ofReal (ab y ^ x) := fun x =>
    (habm.pow_const x).ennreal_ofReal
  have hm : Measurable (Un.Hh D χ φ Φ s) :=
    ((((hW.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
      (hχm.comp measurable_fst)).mul ((hcp _).comp measurable_fst))).mul
      ((hΦm.comp measurable_snd).mul ((hcp _).comp (measurable_fst.comp measurable_snd)))
  refine ⟨hm, hm.aestronglyMeasurable, ?_⟩
  obtain ⟨C₁, hC₁⟩ := UpperTheory.whittaker_lintegral_abs_pow_bounded_on_maximalCompact E D ω φ hA (s.re - 1) (by linarith)
  obtain ⟨C₂, hC₂⟩ := UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded Φ hΦ (2 * s.re) (by linarith)
  let Aa : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Wo D φ (em E (aE p.1 * gl p.2))‖ₑ * ENNReal.ofReal (ab p.1 ^ (s.re - 1))
  let Bb : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * row p.2 j‖ₑ * ENNReal.ofReal (ab p.1 ^ (2 * s.re))
  have hAm : Measurable Aa := hW.enorm.mul ((hrp _).comp measurable_fst)
  have hBm : Measurable Bb := hΦm.enorm.mul ((hrp _).comp measurable_fst)
  have hnorm : ∀ q, ‖Un.Hh D χ φ Φ s q‖ₑ = Aa (q.1, q.2.2) * Bb q.2 := by
    intro q
    have e1 : (s - 1).re = s.re - 1 := by simp
    have e2 : (2 * s).re = 2 * s.re := by simp
    simp only [Un.Hh, enorm_mul, hχe, mul_one, hcn, e1, e2, Aa, Bb]
  have hFm : Measurable fun q : IdeleGroup ℚ × IdeleGroup ℚ × G1 ℚ => Aa (q.1, q.2.2) * Bb q.2 :=
    (hAm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul (hBm.comp measurable_snd)
  have hae : ∀ᵐ k ∂M₀.κ, k ∈ KK ℚ := by
    rw [ae_iff]
    exact M₀.supp
  show ∫⁻ q, ‖Un.Hh D χ φ Φ s q‖ₑ ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) < ⊤
  simp_rw [hnorm]
  rw [lintegral_prod_symm _ hFm.aemeasurable, lintegral_prod_symm _ hFm.lintegral_prod_left'.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun _ => (C₁ * C₂ : ℝ≥0∞)) (hae.mono fun k hk => ?_)) ?_
  · have h1 : ∀ z : IdeleGroup ℚ, ∫⁻ y : IdeleGroup ℚ, Aa (y, k) * Bb (z, k) ∂(ideleMeasure ℚ) ≤ C₁ * Bb (z, k) := by
      intro z
      have hAk : Measurable fun y : IdeleGroup ℚ => Aa (y, k) := hAm.comp measurable_prodMk_right
      rw [lintegral_mul_const _ hAk]
      exact mul_le_mul_left (hC₁ k hk) _
    refine (lintegral_mono h1).trans ?_
    have hBk : Measurable fun z : IdeleGroup ℚ => Bb (z, k) := hBm.comp measurable_prodMk_right
    rw [lintegral_const_mul _ hBk]
    exact mul_le_mul_right (hC₂ k hk) _
  · rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerDiagTorusMulIwasawaEq
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem sc_val {R : Type} [CommRing R] (z : Rˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z).val = Matrix.diagonal fun _ => (z : R) := rfl

private theorem aE_nU (y : (A ℚ)ˣ) (b : A ℚ) :
    aE y * gl (nU b) = gl (nU ((y : A ℚ) * b)) * aE y := by
  refine Units.ext ?_
  ext i j
  rw [Units.val_mul, Units.val_mul, gl_val, gl_val]
  fin_cases i <;> fin_cases j <;> simp [aE, nU, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem aE_mD (y ζ : (A ℚ)ˣ) :
    aE y * gl (mD ζ) = Matrix.GeneralLinearGroup.scalar (Fin 2) ζ⁻¹ * aE (y * ζ ^ 2) := by
  refine Units.ext ?_
  ext i j
  rw [Units.val_mul, Units.val_mul, gl_val, sc_val]
  have hz : ((ζ⁻¹ : (A ℚ)ˣ) : A ℚ) * (ζ : A ℚ) = 1 := Units.inv_mul ζ
  fin_cases i <;> fin_cases j <;> simp [aE, mD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  linear_combination (-(y : A ℚ) * (ζ : A ℚ)) * hz

private theorem em_nU {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (x : A ℚ) :
    em E (gl (nU x)) = nE D ![x, 0] := by
  refine Units.ext ?_
  ext i j
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.em, nE, Matrix.GeneralLinearGroup.map_apply, gl_val]
  fin_cases i <;> fin_cases j <;> simp [nU, Dat.mkE]

private theorem em_sc {E : Type} [Field E] [NumberField E] (z : (A ℚ)ˣ) :
    em E (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E z) := by
  refine Units.ext ?_
  ext i j
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.em, Matrix.GeneralLinearGroup.map_apply, sc_val, coe_ideleEmbedding]
  by_cases e : i = j <;> simp [e, Matrix.diagonal]

private theorem Wo_lev {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} {N : ℕ}
    (hl : ∀ k, Lev N k → ∀ g, φ (g * em E k) = φ g) {κ : GL (Fin 2) (A ℚ)} (hκ : Lev N κ) (h : GL (Fin 2) (A E)) :
    Wo D φ (h * em E κ) = Wo D φ h := by
  unfold Wo
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only []
  rw [← mul_assoc, hl κ hκ]

theorem UpperTheory.whittaker_diagTorus_mul_iwasawa_eq :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (N : ℕ), (∀ k, Lev N k → ∀ g, φ (g * em E k) = φ g) → ∀ (y ζ : (A ℚ)ˣ) (b : A ℚ) (r κ : GL (Fin 2) (A ℚ)), Lev N κ →
          Wo D φ (em E (aE y * (gl (nU b) * gl (mD ζ) * r * κ))) = ((ω.1 ζ⁻¹ : ℂˣ) : ℂ) ^ 2 * Wo D φ (em E (aE (y * ζ ^ 2) * r)) := by
  intro E _ _ D ω φ hφ N hl y ζ b r κ hκ
  obtain ⟨-, -, hn, hz⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hφ
  have e : aE y * (gl (nU b) * gl (mD ζ) * r * κ) =
      gl (nU ((y : A ℚ) * b)) * (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ⁻¹ * (aE (y * ζ ^ 2) * r)) * κ := by
    calc aE y * (gl (nU b) * gl (mD ζ) * r * κ) = (aE y * gl (nU b)) * gl (mD ζ) * r * κ := by
          simp only [mul_assoc]
      _ = gl (nU ((y : A ℚ) * b)) * (aE y * gl (mD ζ)) * r * κ := by
          rw [aE_nU]; simp only [mul_assoc]
      _ = _ := by rw [aE_mD]; simp only [mul_assoc]
  have hN : ideleNorm ℚ E (ideleEmbedding ℚ E ζ⁻¹) = ζ⁻¹ ^ 2 := by
    rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  rw [e, map_mul, Wo_lev D hl hκ, map_mul, map_mul, em_nU D, em_sc, hn, hz, hN, map_pow]
  simp
end

