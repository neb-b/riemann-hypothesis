module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0094

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivTruncExpICompLe
section
open Filter Topology
open scoped Nat

noncomputable section

namespace GlobalTheory.GaussExpSeries

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_iteratedFDeriv_cexp (i : ℕ) (z : ℂ) : ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

theorem norm_iteratedFDeriv_id_le (j : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ j (id : V → V) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | n
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [← norm_iteratedFDeriv_fderiv,
      show fderiv ℝ (id : V → V) = fun _ => ContinuousLinearMap.id ℝ V from funext fun _ => fderiv_id]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iteratedFDeriv_diag_le (B : V →L[ℝ] V →L[ℝ] ℂ) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by
  have h := B.norm_iteratedFDeriv_le_of_bilinear (f := id) (g := id) (N := (n : WithTop ℕ∞))
    contDiff_id contDiff_id x le_rfl
  simp only [id] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => y) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : V => y) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_assoc, sq]
        gcongr
        · exact norm_iteratedFDeriv_id_le i x
        · exact norm_iteratedFDeriv_id_le (n - i) x
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

theorem norm_iteratedFDeriv_gauss_le (B : V →L[ℝ] V →L[ℝ] ℂ) (ε : ℝ)
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y => Complex.exp (B y y)) x‖ ≤
      n ! * Real.exp (-(ε * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n := by
  have hf : ContDiff ℝ ⊤ (fun y => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  refine norm_iteratedFDeriv_comp_le (g := Complex.exp) (f := fun y => B y y) hg hf
    (by exact_mod_cast le_top) x (fun i _ => ?_) (fun i hi _ => ?_)
  · rw [norm_iteratedFDeriv_cexp]; exact Real.exp_le_exp.2 (hB x)
  · refine (norm_iteratedFDeriv_diag_le B i x).trans ?_
    have h1 : 1 ≤ (1 + ‖x‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg x])
    have ha : 1 ≤ (‖B‖ + 1) * (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg B]
    have h2 := le_self_pow₀ ha (show i ≠ 0 by omega)
    rw [mul_assoc, mul_pow]
    calc ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) = 2 ^ i * (‖B‖ * (1 + ‖x‖) ^ 2) := by ring
      _ ≤ 2 ^ i * ((‖B‖ + 1) * (1 + ‖x‖) ^ 2) := by gcongr; linarith
      _ ≤ 2 ^ i * ((‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by gcongr

theorem exists_bound_poly_mul_exp (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C := by
  first
  | exact @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | (apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded ..)

end GlobalTheory.GaussExpSeries

namespace GlobalTheory

open GlobalTheory.GaussExpSeries

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqMulExpNegTraceLe
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory

theorem norm_sq_mul_exp_neg_trace_le : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : ℝ), 0 < δ →
    ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) →
      |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤
        C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) := by
  intro F _ _ _ δ hδ
  set n := 2 * Fintype.card (Emb F) with hn
  refine ⟨(n.factorial : ℝ) * (2 / δ) ^ n, fun x hx => ?_⟩
  set T := ∑ τ : Emb F, τ x with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun τ _ => (hx τ).le
  have hnorm : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ τ : Emb F, τ x := by
    have h := prod_emb x
    have h' : ((∏ τ : Emb F, τ x : ℝ) : ℂ) = (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) := by
      rw [ofReal_prod, h]; simp
    exact_mod_cast h'.symm
  have hprod : |((Algebra.norm ℚ x : ℚ) : ℝ)| ≤ T ^ Fintype.card (Emb F) := by
    rw [hnorm, abs_of_nonneg (Finset.prod_nonneg fun τ _ => (hx τ).le)]
    calc ∏ τ : Emb F, τ x ≤ ∏ _τ : Emb F, T :=
          Finset.prod_le_prod₀ (fun τ _ => (hx τ).le) (fun τ _ =>
            Finset.single_le_sum (f := fun σ : Emb F => σ x) (fun σ _ => (hx σ).le) (Finset.mem_univ τ))
      _ = T ^ Fintype.card (Emb F) := by rw [Finset.prod_const, Finset.card_univ]
  have hsq : |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ 2 ≤ T ^ n := by
    calc _ ≤ (T ^ Fintype.card (Emb F)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hprod 2
      _ = T ^ n := by rw [← pow_mul, mul_comm]
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hexp : (δ * T / 2) ^ n / n.factorial ≤ Real.exp (δ * T / 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have e2 : (δ * T / 2) ^ n ≤ Real.exp (δ * T / 2) * n.factorial := (div_le_iff₀ hf).1 hexp
  have e1 : T ^ n = (2 / δ) ^ n * (δ * T / 2) ^ n := by
    rw [← mul_pow]; congr 1; field_simp
  have hTn : T ^ n ≤ (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (δ * T / 2) := by
    rw [e1]
    calc _ ≤ (2 / δ) ^ n * (Real.exp (δ * T / 2) * n.factorial) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  calc |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ 2 * Real.exp (-δ * T)
        ≤ T ^ n * Real.exp (-δ * T) := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ ≤ (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (δ * T / 2) * Real.exp (-δ * T) :=
          mul_le_mul_of_nonneg_right hTn (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (-(δ / 2) * T) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqMulIntegralBallLeOfCircleInvariant
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory

theorem norm_sq_mul_integral_ball_le_of_circle_invariant :
    ∀ (n : ℕ) (δ : ℝ) (U : Set (V n)) (f : V n → ℂ) (W : V n → ℝ), 0 < δ → IsOpen U →
      closedBall 0 δ ⊆ U → DifferentiableOn ℂ f U → ContinuousOn W (closedBall 0 δ) →
      (∀ w, 0 ≤ W w) → (∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → W (θ • w) = W w) →
      ‖f 0‖ ^ 2 * ∫ w in ball (0 : V n) δ, W w ≤ ∫ w in ball (0 : V n) δ, ‖f w‖ ^ 2 * W w := by
  intro n δ U f W _ hU hsub hf hW hW0 hinv
  classical
  have hS : MeasurableSet (ball (0 : V n) δ) := measurableSet_ball
  have hWb : ContinuousOn W (ball (0 : V n) δ) := hW.mono ball_subset_closedBall
  set W' : V n → ℝ := (ball (0 : V n) δ).piecewise W (fun _ => 0) with hW'
  have hm : Measurable W' := hWb.measurable_piecewise continuousOn_const hS
  have heq : ∀ z ∈ ball (0 : V n) δ, W' z = W z := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  have h := enorm_pow_mul_lintegral_le_of_balanced (volume : Measure (V n)) hS balanced_ball_zero
    (φ := f) (fun z hz => hf.differentiableAt (hU.mem_nhds (hsub (ball_subset_closedBall hz))))
    (w := fun z => ENNReal.ofReal (W' z)) hm.ennreal_ofReal
    (fun c hc z hz => by
      have hz' : c • z ∈ ball (0 : V n) δ := by
        simpa [norm_smul, hc] using hz
      rw [heq _ hz', heq _ hz, hinv c z hc]) 2
  have e1 : ∫⁻ z in ball (0 : V n) δ, ENNReal.ofReal (W' z) =
      ∫⁻ z in ball (0 : V n) δ, ENNReal.ofReal (W z) :=
    setLIntegral_congr_fun hS fun z hz => by simp only [heq z hz]
  have e2 : ∫⁻ z in ball (0 : V n) δ, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (W' z) =
      ∫⁻ z in ball (0 : V n) δ, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (W z) :=
    setLIntegral_congr_fun hS fun z hz => by simp only [heq z hz]
  rw [e1, e2] at h
  have hfc : ContinuousOn f (closedBall 0 δ) := hf.continuousOn.mono hsub
  have hi : IntegrableOn W (ball (0 : V n) δ) :=
    (hW.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hi' : IntegrableOn (fun z => ‖f z‖ ^ 2 * W z) (ball (0 : V n) δ) :=
    (((hfc.norm.pow 2).mul hW).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  have h0 : ∀ z : V n, 0 ≤ ‖f z‖ ^ 2 * W z := fun z => mul_nonneg (by positivity) (hW0 z)
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg h0), ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hW0),
    ofReal_integral_eq_lintegral_ofReal hi' (Filter.Eventually.of_forall h0)]
  simpa [ENNReal.ofReal_mul, ENNReal.ofReal_pow] using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOver
section
open GlobalTheory.LKTrip NumberField

namespace GlobalTheory.HTGroupOver

theorem exists_gen {F : Type} [Field F] [NumberField F] [IsCMField F] (Kq : Subfield F)
    (hKq : Module.finrank ℚ Kq = 2 ∧ ∀ τ : F →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0) :
    ∃ y : Kq, ∃ r : ℚ, (y : F) * y = r ∧ IsCMField.complexConj F (y : F) = -(y : F) ∧
      ∀ z : Kq, ∃ a b : ℚ, (z : F) = a + b * y := by
  classical
  let σ : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨x0, hx0K, hx0⟩ := hKq.2 σ
  let x : Kq := ⟨x0, hx0K⟩
  have hσq : ∀ q : ℚ, (σ (q : F)).im = 0 := by intro q; simp [map_ratCast]
  have hdep : ¬ LinearIndependent ℚ ![(1 : Kq), x, x * x] := by
    intro h
    have := h.fintype_card_le_finrank
    simp [hKq.1] at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have hgF : (g 0 : F) + g 1 * x0 + g 2 * (x0 * x0) = 0 := by
    have := congrArg (fun w : Kq => (w : F)) hg
    simpa [Rat.smul_def, x] using this

  have hnr : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * x0 ≠ 0 := by
    intro a b hb h
    have h2 := congrArg (fun w => (σ w).im) h
    simp only [map_add (f := _), map_mul, map_ratCast, Complex.add_im, Complex.ratCast_im, Complex.mul_im,
      Complex.ratCast_re, zero_mul, add_zero, zero_add, map_zero, Complex.zero_im] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hb (by exact_mod_cast h3)
    · exact hx0 h3
  have hg2 : g 2 ≠ 0 := by
    intro h2
    rw [h2] at hgF
    simp only [Rat.cast_zero, zero_mul, add_zero] at hgF
    by_cases h1 : g 1 = 0
    · rw [h1] at hgF
      simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hgF
      fin_cases i <;> simp_all
    · exact hnr _ _ h1 hgF
  let y0 : F := 2 * g 2 * x0 + g 1
  have hy0K : y0 ∈ Kq := by
    refine add_mem (mul_mem (mul_mem (ofNat_mem Kq 2) (SubfieldClass.ratCast_mem Kq _)) hx0K)
      (SubfieldClass.ratCast_mem Kq _)
  have hy0sq : y0 * y0 = ((g 1 ^ 2 - 4 * g 0 * g 2 : ℚ) : F) := by
    push_cast
    linear_combination (4 * (g 2 : F)) * hgF
  have hy0ne : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * y0 ≠ 0 := by
    intro a b hb h
    apply hnr (a + b * g 1) (2 * b * g 2) (by simp [hb, hg2])
    push_cast
    linear_combination h

  let y : Kq := ⟨y0, hy0K⟩
  refine ⟨y, g 1 ^ 2 - 4 * g 0 * g 2, hy0sq, ?_, ?_⟩
  · have hc : (IsCMField.complexConj F y0 - y0) * (IsCMField.complexConj F y0 + y0) = 0 := by
      have h1 : IsCMField.complexConj F y0 * IsCMField.complexConj F y0 = y0 * y0 := by
        rw [← map_mul, hy0sq, map_ratCast]
      linear_combination h1
    rcases mul_eq_zero.1 hc with h | h
    · exfalso
      have h1 : IsCMField.complexConj F y0 = y0 := sub_eq_zero.1 h
      have h2 := IsCMField.complexEmbedding_complexConj F σ y0
      rw [h1] at h2
      have h3 := congrArg Complex.im h2
      simp only [Complex.conj_im] at h3
      have h4 : (σ y0).im = 0 := by linarith
      have h5 : (σ y0).im = 2 * g 2 * (σ x0).im := by
        have e : σ y0 = ((2 * g 2 : ℚ) : ℂ) * σ x0 + ((g 1 : ℚ) : ℂ) := by
          simp only [y0, map_add (f := _), map_mul, map_ratCast, map_ofNat]; push_cast; ring
        rw [e, Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.ratCast_im]
        push_cast; ring
      rw [h5] at h4
      rcases mul_eq_zero.1 h4 with h6 | h6
      · rcases mul_eq_zero.1 h6 with h7 | h7
        · norm_num at h7
        · exact hg2 (by exact_mod_cast h7)
      · exact hx0 h6
    · exact eq_neg_of_add_eq_zero_left h
  · have hli : LinearIndependent ℚ ![(1 : Kq), y] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro a ha
      have ha' := congrArg (fun w : Kq => (w : F)) ha
      simp only [Rat.smul_def, mul_one] at ha'
      apply hy0ne (-a) 1 one_ne_zero
      push_cast at ha' ⊢
      simp only [y] at ha'
      rw [← ha']
      ring
    have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hKq.1])
    intro z
    have hz : z ∈ Submodule.span ℚ (Set.range ![(1 : Kq), y]) := by rw [hsp]; trivial
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    refine ⟨a, b, ?_⟩
    rw [← hab]
    simp [Rat.smul_def, y]

theorem liesOver_or_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p),
    LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (conjQ G.F).toRingHom) := by
  intro p _ G τ
  obtain ⟨y, r, hyr, hcy, hspan⟩ := exists_gen G.Kq G.hKq
  have hyK : y * y = (r : G.Kq) := Subtype.ext (by push_cast; exact hyr)
  have hsq : τ (y : G.F) * τ (y : G.F) =
      algebraMap ℚ_[p] (PadicAlgCl p) (G.u y) * algebraMap ℚ_[p] (PadicAlgCl p) (G.u y) := by
    rw [← map_mul, ← map_mul, ← map_mul, hyK, hyr, map_ratCast, map_ratCast, map_ratCast]
  have hz : ∀ z : G.Kq, ∃ a b : ℚ, z = (a : G.Kq) + (b : G.Kq) * y := by
    intro z
    obtain ⟨a, b, h⟩ := hspan z
    exact ⟨a, b, Subtype.ext (by push_cast; exact h)⟩
  rcases mul_self_eq_mul_self_iff.1 hsq with h | h
  · left
    intro z
    obtain ⟨a, b, rfl⟩ := hz z
    simp only [Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add (f := _), map_mul, map_ratCast, h]
  · right
    intro z
    obtain ⟨a, b, rfl⟩ := hz z
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, conjQ_apply,
      Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add, map_mul, map_ratCast, hcy, map_neg, h]
    ring

end GlobalTheory.HTGroupOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorNumberFieldIsReduced
section
open GlobalTheory.LKTrip

namespace GlobalTheory

theorem padic_tensor_numberField_isReduced :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F],
      IsReduced (TensorProduct ℚ ℚ_[p] F) := by
  intro p _ F _ _
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℚ_[p] (TensorProduct ℚ ℚ_[p] F) :=
    Algebra.FormallyUnramified.base_change ℚ_[p]
  exact Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] (TensorProduct ℚ ℚ_[p] F)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariant
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.IsFam.value_mul_denom {ι : Type} {act : ι → SL(2, ℤ) → ι}
    {w : ℤ} {f : ι → ℍ → ℂ}
    (h : _root_.GlobalTheory.QFam.IsFam act w f) (i : ι) (γ : SL(2, ℤ)) (τ : ℍ) :
    f i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-w) = f (act i γ) τ := by
  have hi := congrFun (h i γ) τ
  rw [ModularForm.SL_slash_apply] at hi
  exact hi


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.IsFam.esymm_slash {ι : Type} [Fintype ι]
    {act : ι → SL(2, ℤ) → ι} {w : ℤ} {f : ι → ℍ → ℂ}
    (hb : _root_.GlobalTheory.QFam.ActBij act) (h : _root_.GlobalTheory.QFam.IsFam act w f)
    (γ : SL(2, ℤ)) (k : ℕ) :
    (fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ =
      fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ := by
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  ext τ
  rw [ModularForm.SL_slash_apply, Finset.sum_mul]
  have key : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset ι),
      (∏ i ∈ t, f i (γ • τ)) * UpperHalfPlane.denom γ τ ^ (-(k * w : ℤ)) =
        ∏ i ∈ t, f (e i) τ := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    calc (∏ i ∈ t, f i (γ • τ)) * UpperHalfPlane.denom γ τ ^ (-(k * w : ℤ))
        = ∏ i ∈ t, (f i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-w)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ht.2, ← zpow_natCast, ← zpow_mul]
          congr 2
          ring
      _ = ∏ i ∈ t, f (e i) τ := Finset.prod_congr rfl fun i _ => h.value_mul_denom i γ τ
  rw [Finset.sum_congr rfl key]
  refine Finset.sum_nbij' (fun t => t.map e.toEmbedding) (fun t => t.map e.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.card_map] at ht ⊢
    exact ht
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.card_map] at ht ⊢
    exact ht
  · intro t _
    simp [Finset.map_map]
  · intro t _
    simp [Finset.map_map]
  · intro t _
    rw [Finset.prod_map]
    rfl


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.sum_esymm_slash : ∀ (ι : Type) [Fintype ι]
    (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ),
    _root_.GlobalTheory.QFam.ActBij act → _root_.GlobalTheory.QFam.IsFam act w f → ∀ γ : SL(2, ℤ),
      ((fun τ => ∑ i, f i τ) ∣[w] γ = fun τ => ∑ i, f i τ) ∧
      ∀ k : ℕ, ((fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ =
        fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) := by
  intro ι _ act w f hb h γ
  refine ⟨?_, fun k => h.esymm_slash hb γ k⟩
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  ext τ
  rw [ModularForm.SL_slash_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => h.value_mul_denom i γ τ]
  exact e.sum_comp (fun i => f i τ)

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirected
section
open IsLocalRing GlobalTheory.Henselisation

open scoped TensorProduct

namespace GlobalTheory.Henselisation

theorem etNbhd_isDirected (R : Type) [CommRing R] [IsLocalRing R] :
    IsDirected (EtNbhd R) (· ≤ ·) := by
  refine ⟨fun i j => ?_⟩
  let C := i.A ⊗[R] j.A
  haveI : Algebra.Etale R C := Algebra.Etale.comp R i.A C
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := C)).1 inferInstance
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let P : C →ₐ[R] ResidueField R := Algebra.TensorProduct.lift i.pt j.pt (fun _ _ => Commute.all _ _)
  let k : EtNbhd R :=
    { n := n, I := RingHom.ker f, etale := Algebra.Etale.of_equiv e.symm, pt := P.comp e.toAlgHom }
  refine ⟨k, ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeLeft, ?_⟩,
    ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeRight, ?_⟩⟩
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = i.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P (a ⊗ₜ[R] (1 : j.A)) = i.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = j.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P ((1 : i.A) ⊗ₜ[R] a) = j.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefRealGramPairHermitianFormsStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_real_gram_pair_hermitian_forms : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  first | exact @GlobalTheory.HermGram.gram_posDef_pair | exact GlobalTheory.HermGram.gram_posDef_pair | (intros; apply GlobalTheory.HermGram.gram_posDef_pair <;> assumption)
end

