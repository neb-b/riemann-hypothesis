module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
section
open Complex Matrix Filter Topology
open GlobalTheory.AffinePoints
open scoped BigOperators Real GlobalTheory.AffinePoints

namespace GlobalTheory


open AffinePoints in
theorem exists_testFunctions_subset_of_mem_nhds {A : Type*} [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] {e : A →ₐ[ℂ] ℂ} {U : Set (A →ₐ[ℂ] ℂ)} (hU : U ∈ 𝓝 e) :
    ∃ (n : ℕ) (f : Fin n → A) (ε : ℝ), 0 < ε ∧
      ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → x ∈ U := by
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType ℂ A›
  rw [(isClosedEmbedding_coords (C := ℂ) p hp).isInducing.nhds_eq_comap, mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨n, fun k => p (MvPolynomial.X k), ε, hε, fun x hx => hVU (hb ?_)⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro k
  rw [dist_eq_norm]
  exact hx k


open AffinePoints in
theorem exists_holomorphic_section_of_etale :
    (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) := by
  intro g A _ _ _ _ _ e he
  let φ : MvPolynomial (Fin g) ℂ →ₐ[ℂ] A := IsScalarTower.toAlgHom ℂ _ A
  have hφ : φ.Etale := RingHom.etale_algebraMap.2 inferInstance
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin g) ℂ) inferInstance inferInstance
  obtain ⟨c, hc, hcφ, han⟩ := exists_chart_of_etale φ hφ e
  have h0 : c e = 0 := by rw [hcφ]; ext i; exact he i
  obtain ⟨n, f, ε, hε, hf⟩ := exists_testFunctions_subset_of_mem_nhds (c.open_source.mem_nhds hc)
  refine ⟨c.target, c.symm, n, f, ε, c.open_target, h0 ▸ c.map_source hc, ?_, hε,
    fun a => (han a).differentiableOn, fun w hw i => ?_, fun x hx => ?_⟩
  · rw [← h0, c.left_inv hc]
  · have := c.right_inv hw
    rw [hcφ] at this
    exact congrFun this i
  · exact ⟨c x, c.map_source (hf x hx), (c.left_inv (hf x hx)).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsThetaSeriesApplyNeZeroOfLargeForm
section
open Complex Matrix Filter Topology
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.ThetaLarge

section General

variable {E : Type*} [NormedAddCommGroup E]

theorem exists_tsum_gauss_lt_one [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [DecidableEq L] :
    ∃ a : ℝ, 0 < a ∧ ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) < 1 := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (a : ℝ) (l : L) => if l = 0 then (0 : ℝ) else Real.exp (-a * ‖(l : E)‖ ^ 2))
    (g := fun _ => 0) (summable_lattice_exp_neg_mul_norm_sq L one_pos) (fun l => ?_) ?_
  · rw [tsum_zero] at h
    obtain ⟨a, h1, h2⟩ :=
      ((eventually_gt_atTop (0 : ℝ)).and (h.eventually (gt_mem_nhds one_pos))).exists
    exact ⟨a, h1, h2⟩
  · by_cases hl : l = 0
    · simp [hl]
    · simp only [hl, if_false]
      have hn : 0 < ‖(l : E)‖ ^ 2 := pow_pos (norm_pos_iff.2 (by simpa using hl)) 2
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.atBot_mul_const hn)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha l
    split_ifs
    · simpa using (Real.exp_pos _).le
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
      nlinarith [sq_nonneg ‖(l : E)‖]

def term (L : Submodule ℤ E) (H : E → E → ℂ) (χ : L → ℂ) (z₀ : E) (l : L) (z : E) : ℂ :=
  (χ l)⁻¹ * cexp (Real.pi * H (z + l) z₀ - (Real.pi * H z l + Real.pi / 2 * H l l))

variable {L : Submodule ℤ E} {H : E → E → ℂ} {χ : L → ℂ}

theorem term_add (hl : ∀ x y w, H (x + y) w = H x w + H y w)
    (hr : ∀ x y w, H w (x + y) = H w x + H w y) (hs : ∀ x y, H y x = (starRingEnd ℂ) (H x y))
    (h1 : ∀ l, ‖χ l‖ = 1)
    (hχ : ∀ l m : L, χ (l + m) = χ l * χ m * cexp (Real.pi * I * (H l m).im))
    (z₀ : E) (l m : L) (z : E) :
    term L H χ z₀ m (z + l) =
      (χ l * cexp (Real.pi * H z l + Real.pi / 2 * H l l)) * term L H χ z₀ (l + m) z := by
  have hne : ∀ l, χ l ≠ 0 := fun l h => by simpa [h] using h1 l
  unfold term
  rw [hχ, mul_inv, mul_inv, ← Complex.exp_neg, Submodule.coe_add, ← add_assoc]
  have e : (Real.pi * H (z + l + m) z₀ - (Real.pi * H (z + l) m + Real.pi / 2 * H m m) : ℂ) =
      (Real.pi * H z l + Real.pi / 2 * H l l) + (-(Real.pi * I * (H l m).im)) +
      (Real.pi * H (z + l + m) z₀ -
        (Real.pi * H z (l + m) + Real.pi / 2 * H (l + m) (l + m))) := by
    rw [hl z l m, hr, hl l m, hr, hr, hs l m]
    have := Complex.sub_conj (H l m)
    push_cast at this
    linear_combination (-(Real.pi : ℂ) / 2) * this
  rw [e, Complex.exp_add, Complex.exp_add]
  have := hne l
  field_simp

theorem norm_term (hl : ∀ x y w, H (x + y) w = H x w + H y w)
    (hr : ∀ x y w, H w (x + y) = H w x + H w y) (hs : ∀ x y, H y x = (starRingEnd ℂ) (H x y))
    (h1 : ∀ l, ‖χ l‖ = 1) (z₀ : E) (l : L) (z : E) :
    ‖term L H χ z₀ l z‖ = Real.exp (π / 2 * ((H z z).re + (H z₀ z₀).re)) *
      Real.exp (-(π / 2) * (H (l + (z - z₀)) (l + (z - z₀))).re) := by
  unfold term
  rw [norm_mul, norm_inv, h1, inv_one, one_mul, Complex.norm_exp, ← Real.exp_add]
  congr 1
  obtain ⟨u, rfl⟩ : ∃ u, z = u + z₀ := ⟨z - z₀, by simp⟩
  rw [add_sub_cancel_right]
  have hs' : ∀ x y, (H y x).re = (H x y).re := fun x y => by rw [hs]; simp
  have e : (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  simp only [e, hl, hr, add_re, sub_re, re_ofReal_mul]
  rw [hs' u z₀, hs' u l, hs' z₀ l]
  ring

theorem exists_theta [NormedSpace ℂ E] [FiniteDimensional ℂ E] [DiscreteTopology L]
    [DecidableEq L] (hl : ∀ x y w, H (x + y) w = H x w + H y w)
    (hr : ∀ x y w, H w (x + y) = H w x + H w y) (hs : ∀ x y, H y x = (starRingEnd ℂ) (H x y))
    (hd : ∀ w, Differentiable ℂ fun z => H z w) (hc : Continuous fun z => (H z z).re)
    {a : ℝ} (ha : 0 < a) (hsum : ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) < 1)
    (hH : ∀ z, a * ‖z‖ ^ 2 ≤ π / 2 * (H z z).re) (h1 : ∀ l, ‖χ l‖ = 1)
    (hχ : ∀ l m : L, χ (l + m) = χ l * χ m * cexp (Real.pi * I * (H l m).im)) (z₀ : E) :
    ∃ θ : E → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : L) z,
      θ (z + l) = (χ l * cexp (Real.pi * H z l + Real.pi / 2 * H l l)) * θ z := by
  have hle : ∀ (l : L) z, ‖term L H χ z₀ l z‖ ≤ Real.exp (π / 2 * ((H z z).re + (H z₀ z₀).re)) *
      Real.exp (-a * ‖(l : E) + (z - z₀)‖ ^ 2) := fun l z => by
    rw [norm_term hl hr hs h1]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    linarith [hH (l + (z - z₀))]
  refine ⟨fun z => ∑' l : L, term L H χ z₀ l z, ?_, ?_, fun l z => ?_⟩
  · rw [← differentiableOn_univ]
    refine SCV.differentiableOn_tsum_of_locally_normal isOpen_univ (fun l => ?_) (fun x _ => ?_)
    · have h2 : Differentiable ℂ fun z : E => H (z + l) z₀ :=
        (hd z₀).comp (differentiable_id.add_const _)
      have h3 := hd l
      unfold term
      refine Differentiable.differentiableOn ?_
      fun_prop
    · have hx : ∀ᶠ z in 𝓝 x, (H z z).re < (H x x).re + 1 ∧ ‖z - z₀‖ < ‖x - z₀‖ + 1 :=
        (hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _))).and
          ((show Continuous fun z : E => ‖z - z₀‖ by fun_prop).continuousAt.eventually
            (gt_mem_nhds (lt_add_one _)))
      refine ⟨_, hx, _, ((summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left
        (Real.exp (a * (‖x - z₀‖ + 1) ^ 2))).mul_left
        (Real.exp (π / 2 * ((H x x).re + 1 + (H z₀ z₀).re))), fun l z hz => (hle l z).trans ?_⟩
      refine mul_le_mul ?_ (exp_neg_mul_norm_add_sq_le ha.le _ hz.2.le) (Real.exp_pos _).le
        (Real.exp_pos _).le
      gcongr
      exact hz.1.le
  · set A := Real.exp (π / 2 * ((H z₀ z₀).re + (H z₀ z₀).re)) with hA
    have hA0 : 0 < A := Real.exp_pos _
    have hle' : ∀ l : L, ‖term L H χ z₀ l z₀‖ ≤ A * Real.exp (-a * ‖(l : E)‖ ^ 2) := fun l => by
      simpa using hle l z₀
    have hg := summable_lattice_exp_neg_mul_norm_sq L ha
    have hS : Summable fun l : L => term L H χ z₀ l z₀ :=
      .of_norm_bounded (hg.mul_left A) hle'
    have h00 : H 0 0 = 0 := by simpa using hl 0 0 0
    have h0 : ‖term L H χ z₀ 0 z₀‖ = A := by
      rw [norm_term hl hr hs h1]
      simp [h00, hA]
    have hg' : Summable fun l : L => if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2) :=
      .of_nonneg_of_le (fun l => by split_ifs <;> positivity)
        (fun l => by split_ifs <;> [positivity; rfl]) hg
    have h2 : ‖∑' l : L, if l = 0 then 0 else term L H χ z₀ l z₀‖ ≤
        A * ∑' l : L, (if l = 0 then 0 else Real.exp (-a * ‖(l : E)‖ ^ 2)) := by
      refine tsum_of_norm_bounded (hg'.hasSum.mul_left A) fun l => ?_
      split_ifs
      · simp
      · exact hle' l
    intro h
    beta_reduce at h
    rw [hS.tsum_eq_add_tsum_ite 0, add_eq_zero_iff_eq_neg] at h
    rw [h, norm_neg] at h0
    nlinarith
  · beta_reduce
    rw [← (Equiv.addLeft l).tsum_eq fun m => term L H χ z₀ m z, ← tsum_mul_left]
    exact tsum_congr fun m => term_add hl hr hs h1 hχ z₀ l m z

end General

variable {g : ℕ}

theorem continuous_form (M : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z : Fin g → ℂ => (z ⬝ᵥ M.mulVec (star z)).re := by
  simp only [dotProduct, mulVec]
  fun_prop

theorem exists_coercive (M : Matrix (Fin g) (Fin g) ℂ)
    (hM : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ M.mulVec (star z)).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Fin g → ℂ, c * ‖z‖ ^ 2 ≤ (z ⬝ᵥ M.mulVec (star z)).re := by
  obtain ⟨c, hc, h⟩ := (isCompact_sphere (0 : Fin g → ℂ) 1).exists_forall_le'
    (continuous_form M).continuousOn (a := 0) fun z hz => hM z (by
      rintro rfl
      simp at hz)
  refine ⟨c, hc, fun z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨u, hu, hzu⟩ : ∃ u : Fin g → ℂ, ‖u‖ = 1 ∧ z = (‖z‖ : ℝ) • u :=
    ⟨‖z‖⁻¹ • z, by rw [norm_smul]; simp [hn.ne'], by simp [smul_smul, hn.ne']⟩
  have h2 := h u (by simpa using hu)
  generalize ‖z‖ = r at hn hzu
  subst hzu
  rw [star_smul, star_trivial, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_re, smul_re,
    smul_eq_mul, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg r)]

theorem form_symm {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) (x y : Fin g → ℂ) :
    y ⬝ᵥ M.mulVec (star x) = (starRingEnd ℂ) (x ⬝ᵥ M.mulVec (star y)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, Finset.mul_sum, map_sum, map_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hM.apply j i
  simp only [RCLike.star_def] at this ⊢
  rw [← this, Complex.conj_conj]
  ring

theorem exists_theta_apply_ne_zero :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) := by
  classical
  intro g Λ hΛ _ H₀ hH₀
  obtain ⟨a, ha, hsum⟩ := exists_tsum_gauss_lt_one Λ
  obtain ⟨c, hc, hco⟩ := exists_coercive H₀ hH₀
  refine ⟨a / c, fun Hm χ hH hρ h1 hχ z₀ => ?_⟩
  refine exists_theta (H := fun x y => x ⬝ᵥ Hm.mulVec (star y)) (fun x y w => add_dotProduct ..)
    (fun x y w => by rw [star_add, mulVec_add, dotProduct_add]) (form_symm hH) (fun w => ?_)
    (continuous_form Hm) ha hsum (fun z => ?_) h1 hχ z₀
  · simp only [dotProduct]
    fun_prop
  · have h2 : a * ‖z‖ ^ 2 ≤ (z ⬝ᵥ Hm.mulVec (star z)).re := by
      refine le_trans ?_ (hρ z)
      calc a * ‖z‖ ^ 2 = a / c * (c * ‖z‖ ^ 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hco z) (by positivity)
    have h3 : 0 ≤ a * ‖z‖ ^ 2 := by positivity
    nlinarith [Real.two_le_pi]

end GlobalTheory.ThetaLarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
section
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real

namespace GlobalTheory

theorem apply_add_intCast_vec_of_unit_periods {ι R E : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] {F : (ι → R) → E} (hF : ∀ (i : ι) x, F (x + Pi.single i 1) = F x)
    (n : ι → ℤ) (x : ι → R) : F (x + fun i => (n i : R)) = F x := by
  first
  | exact @_root_.GlobalTheory.IntegerShiftSingle.main
  | exact _root_.GlobalTheory.IntegerShiftSingle.main
  | (apply _root_.GlobalTheory.IntegerShiftSingle.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerShiftSingle.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerShiftSingle.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerShiftSingle.main ..)

theorem setIntegral_unitCube_add_right_of_periodic {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : (ι → ℝ) → E}
    (hF : ∀ (i : ι) x, F (x + Pi.single i 1) = F x) (t : ι → ℝ) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1, F (x + t) = ∫ x in Set.Icc (0 : ι → ℝ) 1, F x := by
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  haveI : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  let G : UnitAddTorus ι → E := fun y => F fun i => (AddCircle.equivIoc 1 0 (y i) : ℝ)
  have hG : ∀ x : ι → ℝ, G (fun i => (x i : UnitAddCircle)) = F x := by
    intro x
    have h : ∀ i, ∃ n : ℤ, (AddCircle.equivIoc 1 0 (x i : UnitAddCircle) : ℝ) = x i + n := by
      intro i
      have h1 : ((AddCircle.equivIoc 1 0 (x i : UnitAddCircle) : ℝ) : UnitAddCircle) = x i :=
        (AddCircle.equivIoc 1 0).symm_apply_apply _
      rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at h1
      obtain ⟨k, hk⟩ := h1
      refine ⟨k, ?_⟩
      rw [zsmul_eq_mul, mul_one] at hk
      linarith
    choose n hn using h
    have := apply_add_intCast_vec_of_unit_periods hF n x
    rw [← this]
    simp only [G, hn]
    rfl
  have hae : Set.Icc (0 : ι → ℝ) 1 =ᵐ[volume]
      {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    have h := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : ι => (volume : Measure ℝ))
      (f := (0 : ι → ℝ)) (g := 1)
    have e : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)}
        = Set.univ.pi fun i => Set.Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i) := by
      ext x
      simp [Set.mem_pi]
    rw [e]
    exact h.symm
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae]
  have h1 := UnitAddTorus.integral_preimage G 0
  have h2 := UnitAddTorus.integral_preimage (fun y => G (y + fun i => (t i : UnitAddCircle))) 0
  have h3 : ∫ y : UnitAddTorus ι, G (y + fun i => (t i : UnitAddCircle)) = ∫ y, G y :=
    integral_add_right_eq_self G _
  have h4 : ∀ x : ι → ℝ, G ((fun i => (x i : UnitAddCircle)) + fun i => (t i : UnitAddCircle))
      = F (x + t) := fun x => hG (x + t)
  simp only [hG] at h1
  simp only [h4] at h2
  rw [← h1, ← h2]
  exact h3

theorem setIntegral_unitCube_add_of_entire_periodic {g : ℕ} {f : (Fin g → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (hper : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z)
    (w : Fin g → ℂ) :
    ∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w)
      = ∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) := by
  have hd : DifferentiableOn ℂ
      (fun w => ∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w)) Set.univ := by
    refine (differentiableOn_setIntegral_of_holomorphic_of_continuousOn
      (F := fun (x : Fin g → ℝ) w => f ((fun i => (x i : ℂ)) + w)) isOpen_univ
      isCompact_Icc subset_rfl measurableSet_Icc isCompact_Icc.measure_lt_top.ne ?_ ?_).1
    · have := hf.continuous
      refine Continuous.continuousOn ?_
      unfold Function.uncurry
      fun_prop
    · intro x _
      exact (hf.comp ((differentiable_const _).add differentiable_id)).differentiableOn
  have h := SCV.eq_of_invariant_real isOpen_univ isPreconnected_univ hd
    (fun z _ t _ => by
      have := setIntegral_unitCube_add_right_of_periodic
        (F := fun x : Fin g → ℝ => f ((fun i => (x i : ℂ)) + z)) (fun i x => by
          rw [← hper i ((fun i => (x i : ℂ)) + z)]
          congr 1
          funext j
          by_cases hij : j = i
          · subst hij; simp; ring
          · simp [hij]) t
      rw [← this]
      congr 1
      funext x
      congr 1
      funext i
      simp only [Pi.add_apply, Complex.ofReal_add]
      ac_rfl) (Set.mem_univ w) (Set.mem_univ 0)
  simpa using h

theorem fourierCoeff_unitCube_translate_of_entire_periodic (g : ℕ) (f : (Fin g → ℂ) → ℂ)
    (hf : Differentiable ℂ f) (hper : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z)
    (m : Fin g → ℤ) (w : Fin g → ℂ) :
    (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) *
        cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) =
      cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) *
        (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) *
          cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) := by
  have h := setIntegral_unitCube_add_of_entire_periodic
    (f := fun z => f z * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * z i))
    (by fun_prop) (fun i z => by
      rw [hper]
      congr 1
      have e : ∑ j, (m j : ℂ) * (z + (Pi.single i 1 : Fin g → ℂ)) j
          = ∑ j, (m j : ℂ) * z j + m i := by
        simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
      rw [e, mul_add, Complex.exp_add]
      have : cexp (-(2 * Real.pi * I) * (m i : ℂ)) = 1 := by
        have := Complex.exp_int_mul_two_pi_mul_I (-m i)
        rw [← this]
        congr 1
        push_cast
        ring
      rw [this, mul_one]) w
  rw [← h, ← integral_const_mul]
  congr 1
  funext x
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

end GlobalTheory
end

