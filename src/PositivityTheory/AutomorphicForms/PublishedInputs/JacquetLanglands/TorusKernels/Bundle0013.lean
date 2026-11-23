module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.SigmaFiniteInverseAbsDensity
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle0001

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPack
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk

namespace KappaPackingLemmas

variable {F I Gf : Type} [Field F] [Group Gf]

theorem kap_smul (hb : B1b) (D : Dat F I Gf) (δ : PG F) (a b : D.Xs) (v : I) :
    kap ((δ • a : D.Xs) v) ((δ • b : D.Xs) v) = kap (a v) (b v) := by
  induction δ using QuotientGroup.induction_on with
  | H g =>
    rw [Dat.mk_smulX, Dat.mk_smulX]
    exact hb.2.2.2.1 (D.r v g) (a v) (b v)

theorem near_sixteenth (hb : B1b) (hc : B1c) (D : Dat F I Gf) (γ₁ γ : PG F) (z w : D.Xs)
    (h₁ : Near (1 / 2) (γ₁ • z : D.Xs) w) (h : Near (1 / 2) (γ • z : D.Xs) w) :
    Near (1 / 16) z ((γ₁⁻¹ * γ) • z : D.Xs) := by
  intro v
  have e : kap (z v) (((γ₁⁻¹ * γ) • z : D.Xs) v) = kap ((γ₁ • z : D.Xs) v) ((γ • z : D.Xs) v) := by
    rw [← kap_smul hb D γ₁ z ((γ₁⁻¹ * γ) • z) v, smul_smul, mul_inv_cancel_left]
  rw [e]
  have a1 := h₁ v
  have a2 := h v
  have s := (hc.1 ((γ • z : D.Xs) v) (w v)).2.2
  have t := hc.2.2.1 ((γ₁ • z : D.Xs) v) (w v) ((γ • z : D.Xs) v)
  rw [← s] at t
  nlinarith

end KappaPackingLemmas

end UpperTheory.Esk

open UpperTheory.Esk UpperTheory.Esk.KappaPackingLemmas in
theorem UpperTheory.Esk.pf_Pack : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a → UpperTheory.Esk.Pack := by
  intro hb hc hE F I Gf _ _ _ D hax
  obtain ⟨hcnt, -, -, -, -, -, -, hnear⟩ := hE F I Gf D hax
  obtain ⟨c, hc0, hcz⟩ := hnear (1 / 2) (by norm_num)
  have := hcnt
  refine ⟨c⁻¹, ?_⟩
  intro y ω' h A hh hA hfin
  set S0 : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)} with hS0
  set N : ℝ≥0∞ := (S0.ncard : ℝ≥0∞) with hN
  let Sg : {γ : PG F // γ • y.1 = ω'} → Set D.Xs := fun γ => {w | Near (1 / 2) (γ.1 • y.2 : D.Xs) w}
  have hSm : ∀ γ, MeasurableSet (Sg γ) := fun γ => (hcz (γ.1 • y.2)).1

  have one : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ A * ∫⁻ w, (Sg γ).indicator h w := by
    intro γ
    have hv : (c : ℝ≥0∞) ≤ volume (Sg γ) := (hcz (γ.1 • y.2)).2
    calc (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ h (γ.1 • y.2) * volume (Sg γ) := by
          rw [mul_comm]; gcongr
      _ = ∫⁻ _ in Sg γ, h (γ.1 • y.2) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in Sg γ, (A : ℝ≥0∞) * h w := setLIntegral_mono' (hSm γ) fun w hw => hA _ _ hw
      _ = A * ∫⁻ w in Sg γ, h w := lintegral_const_mul _ hh
      _ = A * ∫⁻ w, (Sg γ).indicator h w := by rw [lintegral_indicator (hSm γ)]

  have cnt : ∀ w : D.Xs, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ N * h w := by
    intro w
    by_cases hT : ∃ γ₁ : {γ : PG F // γ • y.1 = ω'}, w ∈ Sg γ₁
    · obtain ⟨γ₁, hγ₁⟩ := hT
      let f : {γ : PG F // γ • y.1 = ω'} → PG F := fun γ => γ₁.1⁻¹ * γ.1
      have finj : Function.Injective f := fun a b hab => Subtype.ext (mul_left_cancel hab)
      let g : PG F → ℝ≥0∞ := S0.indicator fun _ => h w
      have le1 : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ g (f γ) := by
        intro γ
        by_cases hw : w ∈ Sg γ
        · rw [Set.indicator_of_mem hw]
          have hmem : f γ ∈ S0 := by
            refine ⟨?_, near_sixteenth hb hc D γ₁.1 γ.1 y.2 w hγ₁ hw⟩
            change (γ₁.1⁻¹ * γ.1) • y.1 = y.1
            rw [mul_smul, γ.2, inv_smul_eq_iff]; exact γ₁.2.symm
          simp [g, Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem hw]; exact bot_le
      calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ ∑' γ, g (f γ) := ENNReal.tsum_le_tsum le1
        _ ≤ ∑' x, g x := ENNReal.tsum_comp_le_tsum_of_injective finj g
        _ = ∑' x : S0, h w := (tsum_subtype S0 fun _ => h w).symm
        _ = N * h w := by
          have : Fintype S0 := hfin.fintype
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN, ← Nat.card_coe_set_eq,
            Nat.card_eq_fintype_card]
    · simp only [not_exists] at hT
      have : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w = 0 := fun γ => Set.indicator_of_notMem (hT γ) _
      simp [this]

  have key : (c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2) ≤ A * (N * ∫⁻ w, h w) := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2)
        ≤ ∑' γ : {γ : PG F // γ • y.1 = ω'}, (A : ℝ≥0∞) * ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_le_tsum one
      _ = A * ∑' γ : {γ : PG F // γ • y.1 = ω'}, ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_mul_left
      _ = A * ∫⁻ w, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w := by
          rw [lintegral_tsum fun γ => (hh.indicator (hSm γ)).aemeasurable]
      _ ≤ A * ∫⁻ w, N * h w := by gcongr with w; exact cnt w
      _ = A * (N * ∫⁻ w, h w) := by rw [lintegral_const_mul _ hh]
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)
      = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)) := by
        rw [ENNReal.inv_mul_cancel_left hc' ENNReal.coe_ne_top]
    _ ≤ (c : ℝ≥0∞)⁻¹ * (A * (N * ∫⁻ w, h w)) := by gcongr
    _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * A * N * ∫⁻ w, h w := by
        rw [ENNReal.coe_inv hc0.ne']; ring
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.SplitTsum
section
open MeasureTheory

namespace UpperTheory.Esk.CentralTermsContribution

open Classical in
theorem split_tsum {G : Type} (P : G → Prop) (f : G → ℂ) (hf : Summable fun g => ‖f g‖) :
    ∑' g, f g = (∑' g, if P g then f g else 0) + ∑' g, if P g then 0 else f g := by
  have h1 : Summable fun g => if P g then f g else 0 :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  have h2 : Summable fun g => if P g then 0 else f g :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  rw [← Summable.tsum_add h1 h2]
  congr 1; funext g; split_ifs <;> simp

end UpperTheory.Esk.CentralTermsContribution

open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_TF : UpperTheory.Esk.E2 → UpperTheory.Esk.Ecut → UpperTheory.Esk.E6 → UpperTheory.Esk.Fell → UpperTheory.Esk.Fhyp → UpperTheory.Esk.TF := by
  intro hE2 hcut hE6 hFell hFhyp F I Gf _ _ _ D hAx ι _ a
  obtain ⟨S, hFam, hS⟩ := hFell F I Gf D hAx ι a
  refine ⟨S, hFam, fun k hH hfd h => ?_⟩
  obtain ⟨⟨b, hb⟩, -⟩ := hcut F I Gf D hAx
  obtain ⟨hi, htr⟩ := hE6 F I Gf ι D k a hH hfd h b hb
  obtain ⟨hie, hge⟩ := hS k hH b hb
  have hsplit : ∀ y, (∑' γ : PG F, D.kk k a γ y) = (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y :=
    fun y => CentralTermsContribution.split_tsum _ _ ((hE2 F I Gf ι D k a hH).1 y)
  have hfun : (fun y => b y • ∑' γ : PG F, D.kk k a γ y) = fun y => b y • (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y := by
    funext y; rw [hsplit y, smul_add]
  have hih : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY := by
    have := hi.sub hie
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit y, smul_add, add_sub_cancel_left]
  have h0 := hFhyp F I Gf ι D k a hH b hb hih
  rw [htr, ← hge, hfun, integral_add hie hih, h0, add_zero]
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.UnipotentIntegrandVanishesProof
section
noncomputable section
open MeasureTheory

namespace UpperTheory.Esk.UnipotentIntegrandLemmas

def large₂ {I : Type} [Fintype I] (y : I → Y1) : ℝ := ∑ v, Real.log |(y v).1|

theorem measurable_Lg {I : Type} [Fintype I] : Measurable (large₂ (I := I)) := by
  unfold large₂
  exact Finset.measurable_sum _ fun v _ =>
    Real.measurable_log.comp (continuous_abs.measurable.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))

theorem pt_congr {a a' c c' : ℝ} (h1 : a = a') (h2 : c = c') (hc : c ≠ 0) (hc' : c' ≠ 0) :
    pt a c hc = pt a' c' hc' := by
  subst h1
  subst h2
  rfl

theorem Lg_scl {I : Type} [Fintype I] (t : ℝ) (ht : 0 < t) (y : I → Y1) :
    large₂ (fun v => scl t ht.ne' (y v)) = Fintype.card I * Real.log t + large₂ y := by
  have h : ∀ v, Real.log |t * (y v).1| = Real.log t + Real.log |(y v).1| := by
    intro v
    rw [abs_mul, abs_of_pos ht, Real.log_mul ht.ne' (abs_ne_zero.mpr (y v).2)]
  unfold large₂
  simp only [scl, h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end UpperTheory.Esk.UnipotentIntegrandLemmas

open UpperTheory.Esk.UnipotentIntegrandLemmas in
theorem UpperTheory.Esk.unipotent_integrand_vanishes_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.ConstantTermVanishingAlt := by
  unfold B1a UpperHalfPlaneMeasureCoordinates ConstantTermVanishingAlt
  intro hB1 hB5
  obtain ⟨hσ, -, -⟩ := hB1
  obtain ⟨hmp, -, hcont⟩ := hB5
  have := hσ
  intro I _ _ φ hφ β hβ hβ0 hβinv A B hA hAB u hu hint
  have hval : Measurable (fun z : P => z.1) := measurable_subtype_coe
  have hgm : Measurable (fun z : P => ((z.1.re / z.1.im, (⟨z.1.im, z.2⟩ : Y1)) : ℝ × Y1)) :=
    ((Complex.measurable_re.comp hval).div (Complex.measurable_im.comp hval)).prodMk
      (Complex.measurable_im.comp hval).subtype_mk
  let eP : ℝ × Y1 ≃ᵐ P :=
    { toFun := fun p => pt p.1 p.2.1 p.2.2
      invFun := fun z => (z.1.re / z.1.im, ⟨z.1.im, z.2⟩)
      left_inv := by
        rintro ⟨x, y, hy⟩
        have h1 : ((y : ℂ) * ((x : ℂ) + Complex.I)).re = y * x := by simp
        have h2 : ((y : ℂ) * ((x : ℂ) + Complex.I)).im = y := by simp
        refine Prod.ext ?_ (Subtype.ext ?_)
        · show ((y : ℂ) * ((x : ℂ) + Complex.I)).re / ((y : ℂ) * ((x : ℂ) + Complex.I)).im = x
          rw [h1, h2]
          field_simp
        · show ((y : ℂ) * ((x : ℂ) + Complex.I)).im = y
          exact h2
      right_inv := by
        intro z
        apply Subtype.ext
        show ((z.1.im : ℂ) * (((z.1.re / z.1.im : ℝ) : ℂ) + Complex.I)) = z.1
        have hz : z.1.im ≠ 0 := z.2
        apply Complex.ext
        · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
            Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_one]
          field_simp
        · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
            Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_one]
      measurable_toFun := hcont.measurable
      measurable_invFun := hgm }
  have hmpP : MeasurePreserving eP ((volume : Measure ℝ).prod nu1) (volume : Measure P) := hmp
  have hmpX : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : I => eP)
      (Measure.pi fun _ : I => (volume : Measure ℝ).prod nu1) (Measure.pi fun _ : I => (volume : Measure P)) :=
    measurePreserving_pi _ _ fun _ => hmpP
  have hmpA : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℝ Y1 I).symm ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1))
      (Measure.pi fun _ : I => (volume : Measure ℝ).prod nu1) :=
    MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow ℝ Y1 I (fun _ => volume) (fun _ => nu1))
  let Φ : (I → ℝ) × (I → Y1) ≃ᵐ X I :=
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ Y1 I).symm.trans (MeasurableEquiv.piCongrRight fun _ : I => eP)
  have hΦ : MeasurePreserving Φ ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) (volume : Measure (X I)) := hmpX.comp hmpA
  have hΦapp : ∀ (x : I → ℝ) (y : I → Y1), Φ (x, y) = fun v => pt (x v) (y v).1 (y v).2 := fun x y => rfl
  obtain ⟨b, hbdef⟩ : ∃ b : (I → Y1) → ℝ, b = fun y => β (Φ (0, y)) := ⟨_, rfl⟩
  have hb : Measurable b := by
    rw [hbdef]
    exact hβ.comp (Φ.measurable.comp (measurable_const.prodMk measurable_id))
  have hb0 : ∀ y, 0 ≤ b y := by
    rw [hbdef]
    exact fun y => hβ0 _
  have hβΦ : ∀ (x : I → ℝ) (y : I → Y1), β (Φ (x, y)) = b y := by
    intro x y
    rw [hbdef]
    show β (Φ (x, y)) = β (Φ (0, y))
    rw [hΦapp, hΦapp]
    refine (hβinv x 0 (fun v => (y v).1) (fun v => (y v).2) 1 one_pos).trans ?_
    congr 1
    funext v
    exact pt_congr rfl (one_mul _) _ _
  have huΦ : ∀ (x : I → ℝ) (y : I → Y1), u (Φ (x, y)) = (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) := by
    intro x y
    rw [hΦapp]
    exact hu x (fun v => (y v).1) (fun v => (y v).2)
  have hint' : Integrable (fun p : (I → ℝ) × (I → Y1) => b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v, |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v, φ v (p.1 v) else 0)) ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) := by
    refine ((hΦ.integrable_comp_emb Φ.measurableEmbedding).mpr hint).congr
      (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨x, y⟩ := p
    show β (Φ (x, y)) • u (Φ (x, y)) = _
    rw [hβΦ, huΦ]
  have hI : ∫ z, β z • u z = ∫ p : (I → ℝ) × (I → Y1), b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v, |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v, φ v (p.1 v) else 0) ∂((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) := by
    refine (hΦ.integral_comp' (fun z => β z • u z)).symm.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨x, y⟩ := p
    show β (Φ (x, y)) • u (Φ (x, y)) = _
    rw [hβΦ, huΦ]
  have hcond : ∀ (x : I → ℝ) (y : I → Y1), (A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B) ↔ large₂ y ∈ Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B) := by
    intro x y
    have hp : 0 < ∏ v, |(y v).1| := Finset.prod_pos fun v _ => abs_pos.mpr (y v).2
    have hq : 0 < ∏ v, (1 + x v ^ 2) := Finset.prod_pos fun v _ => by positivity
    have hL : large₂ y = Real.log (∏ v, |(y v).1|) := by
      show ∑ v, Real.log |(y v).1| = _
      rw [Real.log_prod (s := Finset.univ) (f := fun v => |(y v).1|) fun v _ => abs_ne_zero.mpr (y v).2]
    have hM : Real.log (A / ∏ v, (1 + x v ^ 2)) = (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) := by
      rw [Real.log_div hA.ne' hq.ne',
        Real.log_prod (s := Finset.univ) (f := fun v => 1 + x v ^ 2) fun v _ => by positivity]
    rw [Set.mem_Icc, hL, ← hM, Real.log_le_log_iff (div_pos hA hq) hp,
      Real.log_le_log_iff hp (hA.trans hAB)]
  obtain ⟨m, hm⟩ : ∃ m : Measure ℝ, m = Measure.map (large₂ (I := I)) ((Measure.pi fun _ : I => nu1).withDensity fun y => ENNReal.ofReal (b y)) :=
    ⟨_, rfl⟩
  have hinner : ∀ x : I → ℝ, ∫ y, b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) ∂(Measure.pi fun _ : I => nu1) =
      (∏ v, φ v (x v)) * (((m (Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B))).toReal : ℝ) : ℂ) := by
    intro x
    have hS : MeasurableSet ((large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)) := measurable_Lg measurableSet_Icc
    have e1 : (fun y : I → Y1 => b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0)) = fun y =>
        ((((large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)).indicator b y : ℝ) : ℂ) * ∏ v, φ v (x v) := by
      funext y
      by_cases h : large₂ y ∈ Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)
      · rw [if_pos ((hcond x y).mpr h),
          Set.indicator_of_mem (show y ∈ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B) from h), Complex.real_smul]
      · rw [if_neg (fun h' => h ((hcond x y).mp h')),
          Set.indicator_of_notMem (show y ∉ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B) from h), smul_zero]
        simp
    rw [e1, integral_mul_const, integral_complex_ofReal, integral_indicator hS, mul_comm]
    congr 2
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => hb0 y) hb.aestronglyMeasurable, hm,
      Measure.map_apply measurable_Lg measurableSet_Icc, withDensity_apply _ hS]
  have hscl : ∀ (t : ℝ) (ht : 0 < t),
      MeasurePreserving (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) (Measure.pi fun _ : I => nu1) (Measure.pi fun _ : I => nu1) :=
    fun t ht => measurePreserving_pi (fun _ : I => nu1) (fun _ : I => nu1) fun _ => measurePreserving_scl t ht.ne'
  have hbscl : ∀ (t : ℝ) (ht : 0 < t) (y : I → Y1), b (fun v => scl t ht.ne' (y v)) = b y := by
    intro t ht y
    rw [hbdef]
    exact (hβinv 0 0 (fun v => (y v).1) (fun v => (y v).2) t ht).symm
  have hminv : ∀ c : ℝ, ∀ S : Set ℝ, MeasurableSet S → m ((fun x => c + x) ⁻¹' S) = m S := by
    intro c S hS
    have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hcard' : (Fintype.card I : ℝ) ≠ 0 := hcard.ne'
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = Real.exp (c / Fintype.card I) := ⟨_, rfl⟩
    have ht : 0 < t := by rw [ht_def]; exact Real.exp_pos _
    have hlog : (Fintype.card I : ℝ) * Real.log t = c := by
      rw [ht_def, Real.log_exp]
      field_simp
    have hS' : MeasurableSet ((large₂ (I := I)) ⁻¹' S) := measurable_Lg hS
    have hadd : Measurable (fun x : ℝ => c + x) := (continuous_const.add continuous_id).measurable
    have hpre : (large₂ (I := I)) ⁻¹' ((fun x => c + x) ⁻¹' S) =
        (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S) := by
      ext y
      simp only [Set.mem_preimage]
      rw [Lg_scl t ht y, hlog]
    have hpm : MeasurableSet ((fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S)) :=
      (hscl t ht).measurable hS'
    have hmi : Measurable (((large₂ (I := I)) ⁻¹' S).indicator fun y => ENNReal.ofReal (b y)) :=
      (ENNReal.measurable_ofReal.comp hb).indicator hS'
    rw [hm, Measure.map_apply measurable_Lg (hadd hS), Measure.map_apply measurable_Lg hS, hpre,
      withDensity_apply _ hpm, withDensity_apply _ hS', ← lintegral_indicator hpm, ← lintegral_indicator hS',
      ← (hscl t ht).lintegral_comp hmi]
    congr 1
    funext y
    by_cases hy : (fun v => scl t ht.ne' (y v)) ∈ (large₂ (I := I)) ⁻¹' S
    · rw [Set.indicator_of_mem (show y ∈ (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S) from hy),
        Set.indicator_of_mem hy, hbscl t ht y]
    · rw [Set.indicator_of_notMem (show y ∉ (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S) from hy),
        Set.indicator_of_notMem hy]
  have hlogAB : Real.log A < Real.log B := Real.log_lt_log hA hAB
  have hsum0 : ∀ x : I → ℝ, 0 ≤ ∑ v, Real.log (1 + x v ^ 2) := fun x =>
    Finset.sum_nonneg fun v _ => Real.log_nonneg (by linarith [sq_nonneg (x v)])
  have hlt : ∀ x : I → ℝ, (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) < Real.log B := fun x => by linarith [hsum0 x]
  have hP0 : ∀ x : I → ℝ, (∏ v, φ v (x v)) ≠ 0 := fun x =>
    Finset.prod_ne_zero_iff.mpr fun v _ => (hφ v).2.2.2.2 (x v)
  have : (ae (volume : Measure (I → ℝ))).NeBot := ae_neBot.mpr (NeZero.ne _)
  obtain ⟨x0, hx0⟩ := hint'.prod_right_ae.exists
  have hS0 : MeasurableSet ((large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)) := measurable_Lg measurableSet_Icc
  have hTint : Integrable (((large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)).indicator b) (Measure.pi fun _ : I => nu1) := by
    refine (hx0.norm.div_const ‖∏ v, φ v (x0 v)‖).congr (Filter.Eventually.of_forall fun y => ?_)
    show ‖b y • (if A / ∏ v, (1 + x0 v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x0 v) else 0)‖ / ‖∏ v, φ v (x0 v)‖ = _
    by_cases h : large₂ y ∈ Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)
    · rw [if_pos ((hcond x0 y).mpr h),
        Set.indicator_of_mem (show y ∈ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B) from h), norm_smul,
        Real.norm_of_nonneg (hb0 y), mul_div_assoc, div_self (norm_ne_zero_iff.mpr (hP0 x0)), mul_one]
    · rw [if_neg (fun h' => h ((hcond x0 y).mp h')),
        Set.indicator_of_notMem (show y ∉ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B) from h), smul_zero,
        norm_zero, zero_div]
  have hfin : m (Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)) ≠ ⊤ := by
    rw [hm, Measure.map_apply measurable_Lg measurableSet_Icc, withDensity_apply _ hS0,
      ← lintegral_indicator hS0]
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hTint.lintegral_lt_top)
    congr 1
    funext y
    by_cases hy : y ∈ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B) <;> simp [Set.indicator, hy]
  obtain ⟨R, hR⟩ := haar_Icc m hminv (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B - (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2))) (by linarith [hlt x0])
    (by rwa [show (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) + (Real.log B - (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2))) = Real.log B by ring])
  have hR' : ∀ x : I → ℝ, ∫ y, b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) ∂(Measure.pi fun _ : I => nu1) =
      (∏ v, φ v (x v)) * ((R * ((Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ) := by
    intro x
    rw [hinner x, hR _ _ (hlt x).le,
      show Real.log B - (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) = (Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2) by ring]
  rw [hI, integral_prod _ hint']
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => hR' x)).trans ?_
  exact integral_prod_log φ (fun v => ⟨(hφ v).2.1, (hφ v).2.2.1, (hφ v).2.2.2.1⟩) R (Real.log B - Real.log A)
end
end

