module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Formalism.ConjugateSelfDual.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnSqQExpansionUnitStripLow
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lintegral_sq_qs_line (b : ℕ → ℂ) (hb : PolyB b) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in Set.Ico (0 : ℝ) 1, ENNReal.ofReal (‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2)
      = ∑' n : ℕ, ENNReal.ofReal (‖b n‖ ^ 2 * Real.exp (-4 * π * n * y)) := by
  have him : ∀ x : ℝ, 0 < ((x : ℂ) + y * Complex.I).im := fun x => by simpa using hy
  have hc0 : Continuous fun x : ℝ => ofComplex ((x : ℂ) + y * Complex.I) := by
    have : (fun x : ℝ => ofComplex ((x : ℂ) + y * Complex.I))
        = fun x : ℝ => (⟨(x : ℂ) + y * Complex.I, him x⟩ : ℍ) := by
      funext x; exact ofComplex_apply_of_im_pos (him x)
    rw [this, UpperHalfPlane.isEmbedding_coe.continuous_iff]
    show Continuous fun x : ℝ => (x : ℂ) + y * Complex.I
    fun_prop
  have hc : Continuous fun x : ℝ => ‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2 :=
    ((_root_.GlobalTheory.EisM.qs_summable_continuous b hb).2.comp hc0).norm.pow 2
  have hP := _root_.GlobalTheory.EisM.parseval_line b b y hb hb hy
  have h1 : (∫ x in (0 : ℝ)..1, conj (qs b (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I)))
      = ((∫ x in (0 : ℝ)..1, ‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    funext x
    rw [Complex.conj_mul']
    push_cast
    rfl
  have h2 : (fun n : ℕ => conj (b n) * b n * (Real.exp (-4 * π * n * y) : ℝ))
      = fun n : ℕ => ((‖b n‖ ^ 2 * Real.exp (-4 * π * n * y) : ℝ) : ℂ) := by
    funext n
    rw [Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow]
  rw [h1, h2, Complex.hasSum_ofReal] at hP
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hP.summable, hP.tsum_eq,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_Ico_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal]
  · exact (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self
  · exact Eventually.of_forall fun x => by positivity

theorem lintegral_exp_rpow_le (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ y in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(c * y)))
      ≤ ENNReal.ofReal ((1 / c) ^ a * Real.Gamma a) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hc
  have hpos : 0 < (1 / c) ^ a * Real.Gamma a := mul_pos (by positivity) (Real.Gamma_pos_of_pos ha)
  have hi : Integrable (fun y : ℝ => y ^ (a - 1) * Real.exp (-(c * y))) (volume.restrict (Set.Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact hpos.ne')
  rw [← h, ofReal_integral_eq_lintegral_ofReal hi]
  · exact lintegral_mono_set Set.Ioo_subset_Ioi_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have : 0 < y := hy
    simp only [Pi.zero_apply]
    positivity

theorem tsum_lintegral_exp_rpow_lt_top (b : ℕ → ℂ) (a : ℝ) (ha0 : 0 < a)
    (hsum : Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ a) :
    ∑' n : ℕ, ENNReal.ofReal (‖b n‖ ^ 2) *
      ∫⁻ y in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) < ⊤ := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_, ?_⟩
  · have hi : IntegrableOn (fun y : ℝ => y ^ (a - 1)) (Set.Ioo 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith)).1.mono_set Set.Ioo_subset_Ioc_self
    simpa using hi.lintegral_lt_top
  · have hs1 : Summable fun n : ℕ => ‖b (n + 1)‖ ^ 2 * ((1 / (4 * π * ((n + 1 : ℕ) : ℝ))) ^ a * Real.Gamma a) := by
      refine (((summable_nat_add_iff 1).2 hsum).mul_left ((1 / (4 * π)) ^ a * Real.Gamma a)).congr fun n => ?_
      rw [show 1 / (4 * π * ((n + 1 : ℕ) : ℝ)) = (1 / (4 * π)) / ((n + 1 : ℕ) : ℝ) by field_simp,
        Real.div_rpow (x := 1 / (4 * π)) (by positivity) (by positivity)]
      ring
    have hG0 := Real.Gamma_pos_of_pos ha0
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun n : ℕ => ENNReal.ofReal
      (‖b (n + 1)‖ ^ 2 * ((1 / (4 * π * ((n + 1 : ℕ) : ℝ))) ^ a * Real.Gamma a))) fun n => ?_) ?_
    · rw [ENNReal.ofReal_mul (by positivity)]
      gcongr
      exact lintegral_exp_rpow_le a _ ha0 (by positivity)
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs1]
      exact ENNReal.ofReal_lt_top

theorem integrableOn_sq_qs_low : ∀ (e : ℕ) (b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → PolyB b →
    (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) →
    IntegrableOn (fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro e b s he hs hb hsum
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  set a : ℝ := 2 * (e : ℝ) - 1 + s with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hp : 2 * (e : ℝ) + s = a + 1 := by rw [ha]; ring
  rw [hp]
  have hcont : Continuous fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (a + 1) :=
    ((_root_.GlobalTheory.EisM.qs_summable_continuous b hb).2.norm.pow 2).mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ => Or.inr (by linarith))
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hmeas : MeasurableSet {τ : ℍ | τ.im < 1} :=
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const).measurableSet
  set G : ℍ → ENNReal := fun τ => ENNReal.ofReal (‖qs b τ‖ ^ 2 * τ.im ^ (a + 1)) with hG
  have hGm : Measurable G := ENNReal.measurable_ofReal.comp hcont.measurable
  have e1 : ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ τ.im < 1}, ‖‖qs b τ‖ ^ 2 * τ.im ^ (a + 1)‖ₑ
      = ∫⁻ τ in strip, Set.indicator {τ : ℍ | τ.im < 1} G τ := by
    rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas]
    have : {τ : ℍ | τ ∈ strip ∧ τ.im < 1} = {τ : ℍ | τ.im < 1} ∩ strip := by
      ext τ; simp [and_comm]
    rw [this]
    refine lintegral_congr fun τ => ?_
    have := τ.im_pos
    exact Real.enorm_of_nonneg (by positivity)
  rw [hasFiniteIntegral_iff_enorm, e1, _root_.GlobalTheory.EisM.strip_iterated.1 _ (hGm.indicator hmeas)]
  set T : ℕ → ℝ → ENNReal := fun n y =>
    ENNReal.ofReal (‖b n‖ ^ 2) * ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) with hT
  have hTm : ∀ n : ℕ, Measurable fun y : ℝ => ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) := fun n => by
    refine ENNReal.measurable_ofReal.comp ?_
    fun_prop
  have e2 : ∀ y ∈ Set.Ioi (0 : ℝ),
      (∫⁻ x in Set.Ico (0 : ℝ) 1, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I)))
        * ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y => ∑' n, T n y) y := by
    intro y hy
    have hy : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x : ℂ) + y * Complex.I)).im = y := fun x => by
      have h : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
      rw [ofComplex_apply_of_im_pos h]
      show ((x : ℂ) + y * Complex.I).im = y
      simp
    by_cases h1 : y < 1
    · have : ∀ x : ℝ, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I))
          = ENNReal.ofReal (‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2) * ENNReal.ofReal (y ^ (a + 1)) := fun x => by
        rw [Set.indicator_of_mem (by simpa [him x] using h1), hG]
        simp only [him x]
        rw [ENNReal.ofReal_mul (by positivity)]
      simp only [this]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_sq_qs_line b hb y hy,
        Set.indicator_of_mem (by simpa using h1), mul_assoc, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun n => ?_
      simp only [hT]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : y ^ (a + 1) = y ^ (a - 1) * y ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_add hy]; congr 1; ring
      rw [this, show -4 * π * n * y = -(4 * π * n * y) by ring]
      field_simp
    · have : ∀ x : ℝ, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I)) = 0 := fun x =>
        Set.indicator_of_notMem (by simpa [him x] using h1) _
      simp only [this]
      rw [Set.indicator_of_notMem (by simpa using h1)]
      simp
  rw [setLIntegral_congr_fun measurableSet_Ioi e2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio,
    lintegral_tsum (f := T) fun n => ((hTm n).const_mul _).aemeasurable]
  simp only [hT, lintegral_const_mul _ (hTm _)]
  exact tsum_lintegral_exp_rpow_lt_top b a ha0 hsum

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCoprimeSumUnfoldToUnitStrip
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem unfold_strip : ∀ (L : ℕ) (ρ : ℍ → ℝ) (Ψ : ℍ → ℂ) (W : ℤ × ℤ → ℍ → ℂ), Wt L ρ → IntegrableOn Ψ strip → AEStronglyMeasurable Ψ → (∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ, Ψ (γ • τ) = W (γ 1 0, γ 1 1) τ) → ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ = ∫ τ in strip, Ψ τ := by
  intro L ρ Ψ W hρ hΨ hΨm hW
  classical
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) := inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  haveI : Countable (Gamma0 L) := Subtype.countable
  have memΓ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L ↔ (L : ℤ) ∣ γ 1 0 := by
    intro γ
    rw [Gamma0_mem]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hs : MeasurableSet strip := by
    have : strip = (fun τ : ℍ => τ.re) ⁻¹' Set.Ico 0 1 := by
      ext τ; simp [strip]
    rw [this]
    exact UpperHalfPlane.continuous_re.measurable measurableSet_Ico
  set f : ℍ → ℂ := strip.indicator Ψ with hf_def
  have hfi : Integrable f := (integrable_indicator_iff hs).2 hΨ
  have hfm : AEStronglyMeasurable f := hfi.aestronglyMeasurable
  have mp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun τ : ℍ => γ • τ) volume volume := fun γ =>
    measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have me : ∀ γ : SL(2, ℤ), MeasurableEmbedding (fun τ : ℍ => γ • τ) := fun γ =>
    (MeasurableEquiv.smul ((γ : GL (Fin 2) ℝ))).measurableEmbedding
  have rowEq : ∀ (γ : SL(2, ℤ)) (a b : ℤ), γ 1 0 = a → γ 1 1 = b → UpperTheory.V.Af.Rs.row γ = ![a, b] := by
    intro γ a b ha hb
    funext i
    fin_cases i
    · simpa [UpperTheory.V.Af.Rs.row] using ha
    · simpa [UpperTheory.V.Af.Rs.row] using hb
  have step1 : ∀ τ : ℍ, ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ =
      ∑' γ : Gamma0 L, f ((γ : SL(2, ℤ)) • τ) := by
    intro τ
    have key : ∀ x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, ∃ γ : Gamma0 L,
        ((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1) = x.1 ∧ (γ : SL(2, ℤ)) • τ ∈ strip := by
      intro x
      obtain ⟨γ, ⟨hr, hst⟩, -⟩ := UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩
      have h0 : γ 1 0 = x.1.1 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 0
      have h1 : γ 1 1 = x.1.2 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 1
      refine ⟨⟨γ, (memΓ γ).2 (h0 ▸ x.2.2)⟩, ?_, hst⟩
      simp [h0, h1]
    choose g hg using key
    have ginj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      rw [← (hg x).1, ← (hg y).1, hxy]
    have hsupp : Function.support (fun γ : Gamma0 L => f ((γ : SL(2, ℤ)) • τ)) ⊆ Set.range g := by
      intro γ hγ
      have hin : (γ : SL(2, ℤ)) • τ ∈ strip := by
        by_contra h
        exact hγ (Set.indicator_of_notMem h _)
      have hL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := (memΓ γ).1 γ.2
      have hcop : IsCoprime ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := UpperTheory.V.Af.Rs.rowBij.1 γ
      refine ⟨⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩, ?_⟩
      set x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1} := ⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩
      have hx := hg x
      apply Subtype.ext
      exact (UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩).unique
        ⟨rowEq _ _ _ (congrArg Prod.fst hx.1) (congrArg Prod.snd hx.1), hx.2⟩ ⟨rowEq _ _ _ rfl rfl, hin⟩
    rw [← ginj.tsum_eq hsupp]
    refine tsum_congr fun x => ?_
    have hx := hg x
    have hL : (L : ℤ) ∣ (g x : SL(2, ℤ)) 1 0 := (memΓ _).1 (g x).2
    rw [hf_def, Set.indicator_of_mem hx.2, hW _ hL τ, hx.1]
  have hsum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ))⁻¹ • τ)) 1 := fun τ => by
    have := (Equiv.inv (Gamma0 L)).hasSum_iff.mpr (hρ.sum τ)
    simpa [Function.comp_def] using this
  set F : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ τ : ℂ) * f ((γ : SL(2, ℤ)) • τ) with hF
  set G : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℂ) * f τ with hG
  have hFG : ∀ γ, F γ = fun τ => G γ ((γ : SL(2, ℤ)) • τ) := by
    intro γ; funext τ; simp [hF, hG]
  have Gm : ∀ γ, AEStronglyMeasurable (G γ) := fun γ =>
    ((Complex.measurable_ofReal.comp (hρ.meas.comp (me ((γ : SL(2, ℤ))⁻¹)).measurable)).aestronglyMeasurable).mul hfm
  have Fm : ∀ γ, AEStronglyMeasurable (F γ) := fun γ => by
    rw [hFG γ]
    exact (Gm γ).comp_measurePreserving (mp γ)
  have tot : ∀ τ, ∑' γ : Gamma0 L, ‖G γ τ‖ₑ = ‖f τ‖ₑ := by
    intro τ
    simp only [hG, enorm_mul]
    rw [ENNReal.tsum_mul_right]
    have : ∑' γ : Gamma0 L, ‖((ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℝ) : ℂ)‖ₑ = 1 := by
      simp_rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hρ.nonneg _)]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => hρ.nonneg _) (hsum τ).summable, (hsum τ).tsum_eq,
        ENNReal.ofReal_one]
    rw [this, one_mul]
  have finG : ∑' γ, ∫⁻ τ, ‖G γ τ‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun γ => (Gm γ).enorm)]
    simp_rw [tot]
    exact hfi.hasFiniteIntegral.ne
  have finF : ∑' γ, ∫⁻ τ, ‖F γ τ‖ₑ ≠ ⊤ := by
    have : ∀ γ, ∫⁻ τ, ‖F γ τ‖ₑ = ∫⁻ τ, ‖G γ τ‖ₑ := fun γ => by
      rw [hFG γ]
      exact (mp γ).lintegral_comp_emb (me γ) (fun τ => ‖G γ τ‖ₑ)
    simp_rw [this]
    exact finG
  calc ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ
        = ∫ τ, ∑' γ, F γ τ := by
          congr 1; funext τ; rw [step1 τ, ← tsum_mul_left]
    _ = ∑' γ, ∫ τ, F γ τ := integral_tsum Fm finF
    _ = ∑' γ, ∫ τ, G γ τ := by
          refine tsum_congr fun γ => ?_
          rw [hFG γ]
          exact (mp γ).integral_comp (me γ) (G γ)
    _ = ∫ τ, ∑' γ, G γ τ := (integral_tsum Gm finG).symm
    _ = ∫ τ, f τ := by
          congr 1; funext τ
          simp only [hG]
          rw [tsum_mul_right, ← Complex.ofReal_tsum, (hsum τ).tsum_eq]
          simp
    _ = ∫ τ in strip, Ψ τ := integral_indicator hs

end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzWeightOnePeriodicMeanZero
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.LipOne

theorem block (L : ℕ) (f : ℤ → ℂ) (N : ℕ) :
    ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), f d =
      ∑ r ∈ Finset.range L, ∑ n ∈ Finset.Icc (-(N:ℤ)) N, f (r + n * L) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rw [← Finset.sum_product']
  have hL' : (0:ℤ) < L := by exact_mod_cast hL
  refine Finset.sum_nbij' (fun d => ((d % L).toNat, d / L)) (fun p => (p.1 : ℤ) + p.2 * L) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_Ico] at hd
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    have h1 := Int.emod_nonneg d hL'.ne'
    have h2 := Int.emod_lt_of_pos d hL'
    have h3 := Int.emod_add_mul_ediv d L
    refine ⟨by omega, ?_, ?_⟩
    · by_contra h
      push_neg at h
      have : (L:ℤ) * (d / L) ≤ L * (-(N:ℤ) - 1) := by
        apply mul_le_mul_of_nonneg_left (by omega) hL'.le
      nlinarith
    · by_contra h
      push_neg at h
      have : (L:ℤ) * (N + 1) ≤ L * (d / L) := by
        apply mul_le_mul_of_nonneg_left (by omega) hL'.le
      nlinarith
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp
    simp only [Finset.mem_coe, Finset.mem_Ico]
    obtain ⟨h1, h2, h3⟩ := hp
    have h1' : (p.1 : ℤ) < L := by exact_mod_cast h1
    have h0 : (0:ℤ) ≤ p.1 := by positivity
    constructor <;> nlinarith
  · intro d hd
    simp only
    have h1 := Int.emod_nonneg d hL'.ne'
    rw [Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv d L
    linarith
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp
    have h1' : (p.1 : ℤ) < L := by exact_mod_cast hp.1
    ext
    · simp only
      rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) h1']
      simp
    · simp only
      rw [Int.add_mul_ediv_right _ _ hL'.ne', Int.ediv_eq_zero_of_lt (by positivity) h1']
      simp
  · intro d hd
    simp only
    congr 1
    have h1 := Int.emod_nonneg d hL'.ne'
    rw [Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv d L
    linarith

theorem lipschitz_one : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm 1 0 (z + d)) atTop (𝓝 (-2 * π * Complex.I / L * ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  intro L φ z hL hz h0
  have hLz : (L:ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have htrm : ∀ w : ℂ, trm 1 0 w = w⁻¹ := by
    intro w
    simp [trm]
  simp only [htrm]
  have hsum0 : ∑ r ∈ Finset.range L, φ r = 0 := by simpa [hat] using h0
  set g : ℤ → ℂ := fun d => φ d * ((z + d)⁻¹ - (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) with hg
  have hs : Summable g := _root_.GlobalTheory.summable_periodic_mul_inv_sub_inv_floor L φ z hL hz
  have hsplit : ∀ s : Finset ℤ, ∑ d ∈ s, φ d * (z + d)⁻¹ =
      ∑ d ∈ s, g d + ∑ d ∈ s, φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹ := by
    intro s
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg]
    ring
  have hmonoF : Monotone (fun R : ℕ => Finset.Icc (-(R:ℤ)) R) := by
    intro a b hab
    have : (a:ℤ) ≤ b := by exact_mod_cast hab
    exact Finset.Icc_subset_Icc (by omega) (by omega)
  have hcovF : ∀ d : ℤ, ∃ R : ℕ, d ∈ Finset.Icc (-(R:ℤ)) R := by
    intro d
    exact ⟨d.natAbs, by simp only [Finset.mem_Icc]; omega⟩
  have hmonoG : Monotone (fun N : ℕ => Finset.Ico (-(N * L : ℤ)) ((N + 1) * L)) := by
    intro a b hab
    have : (a:ℤ) ≤ b := by exact_mod_cast hab
    have hL0 : (0:ℤ) ≤ L := by positivity
    exact Finset.Ico_subset_Ico (by nlinarith) (by nlinarith)
  have hcovG : ∀ d : ℤ, ∃ N : ℕ, d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L) := by
    intro d
    refine ⟨d.natAbs, ?_⟩
    have h1 : (1:ℤ) ≤ L := by exact_mod_cast hL
    have h3 : (d.natAbs : ℤ) = |d| := Int.natCast_natAbs d
    have h4 : (0:ℤ) ≤ |d| := abs_nonneg d
    simp only [Finset.mem_Ico]
    rw [h3]
    constructor
    · nlinarith [neg_abs_le d]
    · nlinarith [le_abs_self d]
  have hF := Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoF hcovF)
  have hG := Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoG hcovG)
  have hzero : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L),
      φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹ = 0 := by
    intro N
    rw [block L (fun d : ℤ => φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) N]
    calc _ = ∑ r ∈ Finset.range L, φ r * ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + ((L:ℤ) * n : ℤ))⁻¹ := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          have hr' : (r:ℤ) < L := by exact_mod_cast Finset.mem_range.mp hr
          rw [Int.add_mul_ediv_right _ _ hLz, Int.ediv_eq_zero_of_lt (by positivity) hr', zero_add]
          congr 1
          push_cast
          simp [ZMod.natCast_self]
      _ = 0 := by rw [← Finset.sum_mul, hsum0, zero_mul]
  have hb : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), φ d * (z + d)⁻¹ =
      ∑ r ∈ Finset.range L, φ r * ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹ := by
    intro N
    rw [block L (fun d : ℤ => φ d * (z + d)⁻¹) N]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    simp only [ZMod.natCast_self, mul_zero, add_zero]
    ring_nf
  have hmain := tendsto_finsetSum (Finset.range L)
    fun r (_ : r ∈ Finset.range L) => (_root_.GlobalTheory.tendsto_sum_Icc_inv_residue_cot L z r hL hz).const_mul (φ r)
  rw [_root_.GlobalTheory.CotQExp.sum_cot_eq_qexp L φ z hL hz h0] at hmain
  have hT : ∑' d, g d = -2 * ↑π * Complex.I / ↑L * ∑' (m : ℕ), hat φ ↑(m + 1) *
      cexp (2 * ↑π * Complex.I * ↑(m + 1) * z / ↑L) := by
    refine tendsto_nhds_unique ?_ hmain
    refine hG.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [← hb N, hsplit, hzero N, add_zero]
  have hlim := hF.add (T.tendsto_sum_Icc_periodic_mul_inv_floor_div L φ z hL hz h0)
  rw [add_zero, hT] at hlim
  refine hlim.congr fun R => ?_
  simp only [Function.comp_apply]
  rw [hsplit]

end GlobalTheory.EisM.LipOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastIsUnitPadicInt
section
namespace GlobalTheory.PadicInversePower

open Formalism.ConjugateSelfDual

theorem natCast_isUnit_padicInt (l : ℕ) [Fact (Nat.Prime l)] (n : ℕ) (h : ¬ l ∣ n) : IsUnit (n : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

theorem inv_pow_mem (l : ℕ) [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    (((x : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹ ∈ c.O := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (x : ZMod (l ^ 0)).val = 0 := by
      haveI : NeZero (l ^ 0) := ⟨by simp⟩
      exact Nat.lt_one_iff.mp (by simpa only [pow_zero] using ZMod.val_lt (x : ZMod (l ^ 0)))
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp only [pow_zero, inv_one]; exact c.O.one_mem
    · simp only [Nat.cast_zero, zero_pow he.ne', inv_zero]; exact c.O.zero_mem
  · let n := (x : ZMod (l ^ r)).val
    have hcop : l.Coprime n :=
      (ZMod.val_coe_unit_coprime x).symm.of_dvd_left (dvd_pow_self l hr.ne')
    have hnd : ¬ l ∣ n := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop
    obtain ⟨u, hu⟩ := (natCast_isUnit_padicInt l n hnd).pow e
    have key : ((n : Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ↑u⁻¹ := by
      rw [map_units_inv (algebraMap ℤ_[l] (Qbar l)) u, hu, map_pow, map_natCast]
    rw [key]
    exact c.O.algebraMap_mem _

end GlobalTheory.PadicInversePower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntModuleFiniteOfSeparatedOfFiniteQuotientAStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_module_finite_of_separated : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X], Finite (X ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1))) → (∀ x : X, (∀ r : ℕ, ∃ y, (l : ℤ_[l]) ^ r • y = x) → x = 0) → Module.Finite ℤ_[l] X := by
  first | exact @GlobalTheory.padicInt_module_finite_of_separated_of_finite_quotient | exact GlobalTheory.padicInt_module_finite_of_separated_of_finite_quotient | (intros; apply GlobalTheory.padicInt_module_finite_of_separated_of_finite_quotient <;> assumption)
end

