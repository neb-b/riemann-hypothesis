module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelDer
section
noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section ExpL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma mder_exp_cont (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) :=
  NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

end ExpL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open Classical in
def kcurve (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ → KG ε :=
  if h : inK ε X then Classical.choose (exists_curve ε h) else fun _ => 1

lemma kcurve_eq (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    kcurve ε X = onepCurve ε hX := by
  unfold kcurve
  rw [dite_eq_left hX]
  funext t
  apply onep_KG_ext
  rw [Classical.choose_spec (exists_curve ε hX) t, toMK_onepCurve]

lemma continuous_onepCurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    Continuous (onepCurve ε hX) := by
  apply continuous_induced_rng.2
  apply (isClosedEmbedding_toM ε).isInducing.continuous_iff.2
  have : ((fun g : UJ ε => toM g) ∘ Subtype.val ∘ onepCurve ε hX) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := by
    funext t
    exact toMK_onepCurve ε hX t
  rw [this]
  exact mder_exp_cont X

theorem kcurve_spec (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    Continuous (kcurve ε X) ∧ (∀ t, toMK (kcurve ε X t) = NormedSpace.exp ((t : ℂ) • X)) ∧
      ∀ s t, kcurve ε X (s + t) = kcurve ε X s * kcurve ε X t := by
  rw [kcurve_eq ε hX]
  refine ⟨continuous_onepCurve ε hX, toMK_onepCurve ε hX, ?_⟩
  intro s u
  apply onep_KG_ext
  show toMK (onepCurve ε hX (s + u)) = toMK (onepCurve ε hX s) * toMK (onepCurve ε hX u)
  rw [toMK_onepCurve, toMK_onepCurve, toMK_onepCurve,
    show (((s + u : ℝ) : ℂ) • X) = (s : ℂ) • X + (u : ℂ) • X by push_cast; exact add_smul _ _ _]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

theorem curve_eq_kcurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ = kcurve ε X := by
  funext t
  apply onep_KG_ext
  rw [hγ, (kcurve_spec ε hX).2.1]

theorem differentiableAt_oneParam {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (φ : ℝ → (V →L[ℂ] V)) (hc : Continuous φ) (h0 : φ 0 = 1) (hadd : ∀ s t, φ (s + t) = φ s * φ t) :
    DifferentiableAt ℝ φ 0 := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set Φ : ℝ → (V →L[ℂ] V) := fun x => ∫ s in (0:ℝ)..x, φ s with hΦ
  have hΦd : ∀ x, HasDerivAt Φ (φ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hslope : Tendsto (slope Φ 0) (𝓝[≠] 0) (𝓝 (φ 0)) := hasDerivAt_iff_tendsto_slope.1 (hΦd 0)
  rw [h0] at hslope
  have hev : ∀ᶠ h in 𝓝[≠] (0:ℝ), IsUnit (slope Φ 0 h) := hslope (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨h, hh, hne⟩ := (hev.and self_mem_nhdsWithin).exists
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  rw [slope_def_module, hΦ0, sub_zero, sub_zero] at hh
  obtain ⟨u, hu⟩ := hh
  have key : ∀ t, φ t * Φ h = Φ (t + h) - Φ t := by
    intro t
    have h1 := (ContinuousLinearMap.mul ℝ (V →L[ℂ] V) (φ t)).intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 h)
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [hΦ]
    dsimp only
    rw [← h1]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun x => φ x) t, add_zero,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hrep : φ = fun t => h⁻¹ • (Φ (t + h) - Φ t) * ((u⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V) := by
    funext t
    rw [← key, ← mul_smul_comm, ← hu, Units.mul_inv_cancel_right]
  have hD : Differentiable ℝ Φ := fun x => (hΦd x).differentiableAt
  rw [hrep]
  exact ((((hD.comp (differentiable_id.add_const h)) 0).sub (hD 0)).const_smul h⁻¹).mul_const _

section Op

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def derOp (ε : Fin n → Bool) (τ : KG ε →* unitary (V →L[ℂ] V)) (X : Matrix (Fin n) (Fin n) ℂ) : V →L[ℂ] V :=
  deriv (fun t : ℝ => ((τ (kcurve ε X t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) 0

theorem derOp_hasDeriv [FiniteDimensional ℂ V] (ε : Fin n → Bool) (τ : KG ε →* unitary (V →L[ℂ] V))
    (hcont : Continuous τ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) :
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (derOp ε τ X) 0 := by
  have hγk := curve_eq_kcurve ε hX γ hγ
  subst hγk
  obtain ⟨hc, -, hmul⟩ := kcurve_spec ε hX
  set φ : ℝ → V →L[ℂ] V := fun t => ((τ (kcurve ε X t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) with hφ
  have h0k : kcurve ε X 0 = 1 := by
    apply onep_KG_ext
    rw [(kcurve_spec ε hX).2.1]
    show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
    simp
  have hφc : Continuous φ := continuous_subtype_val.comp (hcont.comp hc)
  have hφ0 : φ 0 = 1 := by
    simp only [hφ, h0k, map_one]
    rfl
  have hφadd : ∀ s t, φ (s + t) = φ s * φ t := by
    intro s t
    simp only [hφ, hmul, map_mul]
    rfl
  exact (differentiableAt_oneParam φ hφc hφ0 hφadd).hasDerivAt

end Op

def rdc (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (f : KG ε → ℂ) (x : KG ε) : ℂ :=
  deriv (fun t : ℝ => f (x * kcurve ε (cpart1 ε (bdPart ε Z)) t)) 0 +
    Complex.I * deriv (fun t : ℝ => f (x * kcurve ε (cpart2 ε (bdPart ε Z)) t)) 0

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGenA
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section PreA

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))

abbrev preOp (k : KG ε) : V →L[ℂ] V := ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V)

theorem preOp_mul (k l : KG ε) : preOp τ (k * l) = preOp τ k * preOp τ l := by
  show ((τ (k * l) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = _
  rw [map_mul]; rfl

theorem preOp_one : preOp τ (1 : KG ε) = 1 := by
  show ((τ 1 : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = _
  rw [map_one]; rfl

theorem preOp_inv (k : KG ε) : preOp τ k⁻¹ = star (preOp τ k) := by
  show ((τ k⁻¹ : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = _
  rw [map_inv]; rfl

variable (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)

include hder in
theorem pre_op_curve {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    preOp τ (γ t) = NormedSpace.exp ((t : ℂ) • dτ X) := by
  set A := dτ X with hAdef
  set F : ℝ → V →L[ℂ] V := fun s => preOp τ (γ s) with hFdef
  have hmul : ∀ s u : ℝ, γ (s + u) = γ s * γ u := by
    intro s u
    apply onep_KG_ext
    show toMK (γ (s + u)) = toMK (γ s) * toMK (γ u)
    rw [hγ, hγ, hγ, show (((s + u : ℝ) : ℂ) • X) = (s : ℂ) • X + (u : ℂ) • X by push_cast; exact add_smul _ _ _]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have h0 : γ 0 = 1 := by
    apply onep_KG_ext
    rw [hγ]
    show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
    simp
  have hF : ∀ s u : ℝ, F (s + u) = F s * F u := by
    intro s u
    simp only [hFdef, hmul, preOp_mul]
  have hF0 : F 0 = 1 := by
    simp only [hFdef, h0, preOp_one]
  have hd0 : HasDerivAt F A 0 := hder X hX γ hγ
  have hd : ∀ s, HasDerivAt F (F s * A) s := by
    intro s
    have h1 : HasDerivAt (fun u => F s * F (u - s)) (F s * A) s := by
      have h2 := hd0.const_mul (F s)
      rw [← sub_self s] at h2
      exact HasDerivAt.comp_sub_const (f := fun y => F s * F y) s s h2
    convert h1 using 1
    funext u
    rw [← hF, add_sub_cancel]
  set E : ℝ → V →L[ℂ] V := fun u => NormedSpace.exp (u • (-A)) with hEdef
  have hE : ∀ u, HasDerivAt E (E u * (-A)) u := fun u => hasDerivAt_exp_smul_const (-A) u
  have hcomm : ∀ u, A * E u = E u * A := fun u =>
    (((Commute.refl A).neg_right.smul_right u).exp_right).eq
  have hG : ∀ u, HasDerivAt (F * E) 0 u := by
    intro u
    refine ((hd u).mul (hE u)).congr_deriv ?_
    simp only [mul_neg, mul_assoc, hcomm u, add_neg_cancel]
  have hGc : ∀ u, (F * E) u = (F * E) 0 := fun u =>
    is_const_of_deriv_eq_zero (fun v => (hG v).differentiableAt) (fun v => (hG v).deriv) u 0
  have hG0 : (F * E) 0 = 1 := by
    show F 0 * NormedSpace.exp ((0 : ℝ) • (-A)) = 1
    rw [hF0, zero_smul, NormedSpace.exp_zero, one_mul]
  show F t = _
  have hs : ((t : ℂ) • A) = t • A := by
    exact Complex.coe_smul t A
  rw [hs]
  have hc : Commute (t • (-A)) (t • A) := (((Commute.refl A).neg_left).smul_left t).smul_right t
  calc F t = F t * E t * NormedSpace.exp (t • A) := by
        rw [mul_assoc, hEdef, ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
          ((NormedSpace.expSeries_radius_eq_top ℝ (V →L[ℂ] V)).symm ▸ edist_lt_top _ _)
          ((NormedSpace.expSeries_radius_eq_top ℝ (V →L[ℂ] V)).symm ▸ edist_lt_top _ _), smul_neg, neg_add_cancel,
          NormedSpace.exp_zero, mul_one]
    _ = NormedSpace.exp (t • A) := by
        rw [show F t * E t = (F * E) t from rfl, hGc, hG0, one_mul]

include hder in
theorem pre_op_eq_exp' (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ preOp τ k = NormedSpace.exp (dτ Y) := by
  obtain ⟨Y, hY, he⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := by
    apply onep_KG_ext
    have := hγ 1
    simp only [Complex.ofReal_one, one_smul] at this
    rw [this, he]
  refine ⟨Y, hY, ?_⟩
  have := pre_op_curve τ dτ hder hY γ hγ 1
  simpa [h1] using this

include hder in
theorem pre_star_dτ {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : star (dτ X) = -dτ X := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := dτ X
  have key : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • star A) * NormedSpace.exp ((t : ℂ) • A) = 1 := by
    intro t
    have h1 := pre_op_curve τ dτ hder hX γ hγ t
    have h2 : star (preOp τ (γ t)) * preOp τ (γ t) = 1 := Unitary.coe_star_mul_self _
    rw [h1, NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal] at h2
    exact h2
  have hd0 := (hasDerivAt_exp_smul_const (star A) ((0 : ℝ) : ℂ)).mul
    (hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ))
  have hd2 := hasDerivAt_real_of_complex' hd0
  have hf : (fun y : ℝ => ((fun u : ℂ => NormedSpace.exp (u • star A)) *
      fun u : ℂ => NormedSpace.exp (u • A)) (y : ℂ)) = fun _ => 1 := funext fun t => by
    simpa using key t
  rw [hf] at hd2
  have := hd2.unique (hasDerivAt_const _ _)
  simp at this
  exact eq_neg_of_add_eq_zero_left this

include hder in
theorem pre_conj_dτ (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    preOp τ k * dτ Y * star (preOp τ k) = dτ (toMK k * Y * star (toMK k)) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have hY' := inK_conj' k hY
  set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK k) :=
    toMK_inv' k
  have hγ' : ∀ t : ℝ, toMK (k * γ t * k⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK k * Y * star (toMK k))) := by
    intro t
    have e1 : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹ := rfl
    rw [e1, toMK_inv', hγ t, ← hU]
    have e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, Matrix.exp_units_conj]
  set B := dτ Y
  set C := dτ (toMK k * Y * star (toMK k))
  have key : ∀ t : ℝ, preOp τ k * NormedSpace.exp ((t : ℂ) • B) * star (preOp τ k) =
      NormedSpace.exp ((t : ℂ) • C) := by
    intro t
    rw [← pre_op_curve τ dτ hder hY γ hγ t, ← pre_op_curve τ dτ hder hY' _ hγ' t, ← preOp_inv,
      preOp_mul, preOp_mul]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const B ((0 : ℝ) : ℂ)).const_mul (preOp τ k)).mul_const (star (preOp τ k)))
  have h2 := hasDerivAt_real_of_complex' (z := 0) (hasDerivAt_exp_smul_const C ((0 : ℝ) : ℂ))
  have hf : (fun y : ℝ => preOp τ k * NormedSpace.exp ((y : ℂ) • B) * star (preOp τ k)) =
      fun y : ℝ => NormedSpace.exp ((y : ℂ) • C) := funext key
  simp only [hf] at h1
  have := h1.unique h2
  simpa using this

section MatDerivP

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem pre_dτ_conj_hasDerivAt (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun y : ℝ => dτ (NormedSpace.exp ((y : ℂ) • X) * Y *
      NormedSpace.exp ((y : ℂ) • (-X)))) (dτ (X * Y - Y * X)) 0 := by
  have h := ((LinearMap.toContinuousLinearMap dτ).hasFDerivAt).comp_hasDerivAt _
    (mat_conj_hasDerivAt X Y)
  exact hasDerivAt_real_of_complex' (z := 0) h

end MatDerivP

include hder in
theorem pre_dτ_bracket {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    dτ X * dτ Y - dτ Y * dτ X = dτ (X * Y - Y * X) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := dτ X
  set B := dτ Y
  have hA := pre_star_dτ τ dτ hder hX
  have hXs := ((inK_iff' ε X).1 hX).1
  have key : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • A) * B * NormedSpace.exp ((s : ℂ) • (-A)) =
      dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) := by
    intro s
    have h := pre_conj_dτ τ dτ hder (γ s) hY
    rw [pre_op_curve τ dτ hder hX γ hγ s, hγ s, NormedSpace.star_exp, star_smul, hA,
      Complex.star_def, Complex.conj_ofReal] at h
    rw [h]
    congr 2
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs,
      Complex.star_def, Complex.conj_ofReal]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ)).mul_const B).mul
      (hasDerivAt_exp_smul_const (-A) ((0 : ℝ) : ℂ)))
  have h2 := pre_dτ_conj_hasDerivAt dτ X Y
  have h1' := h1.congr_of_eventuallyEq
    (f₁ := fun s : ℝ => dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))))
    (Filter.Eventually.of_forall fun s => (key s).symm)
  have := h1'.unique h2
  rw [← this]
  simp [sub_eq_add_neg]

include hder in
theorem pre_dτ_bracket_single {a b c d : Fin n} (hab : ε a = ε b) (hcd : ε c = ε d) :
    dτ (Matrix.single a b 1) * dτ (Matrix.single c d 1) -
        dτ (Matrix.single c d 1) * dτ (Matrix.single a b 1) =
      dτ (Matrix.single a b 1 * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by
  rw [single_eq_kp a b, single_eq_kp c d, brk_expand, map_add (f := _), map_add (f := _), map_smul, map_smul,
    brk_expand, map_add, map_add, map_add, map_smul, map_smul, map_smul,
    pre_dτ_bracket τ dτ hder (inK_hermitian_unit hab) (inK_hermitian_unit hcd), pre_dτ_bracket τ dτ hder (inK_hermitian_unit hab) (inK_skew_hermitian_unit hcd),
    pre_dτ_bracket τ dτ hder (inK_skew_hermitian_unit hab) (inK_hermitian_unit hcd), pre_dτ_bracket τ dτ hder (inK_skew_hermitian_unit hab) (inK_skew_hermitian_unit hcd)]

include hder in
theorem pre_star_dτ_single {a b : Fin n} (hab : ε a = ε b) :
    star (dτ (Matrix.single a b 1)) = dτ (Matrix.single b a 1) := by
  rw [single_eq_kp a b, single_eq_kp' a b, map_add (f := _), map_smul, map_add (f := _), map_smul, map_neg, star_add,
    star_smul, pre_star_dτ τ dτ hder (inK_hermitian_unit hab), pre_star_dτ τ dτ hder (inK_skew_hermitian_unit hab)]
  simp [Complex.conj_I]

end PreA

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem KType.kHighest_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KHighest ε (kunits T) Λ T.w := ⟨fun a => T.w_wt a, fun a b hab he => T.w_hw a b hab he⟩

theorem KType.w_ne_zero {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.w ≠ 0 := by
  intro h
  have h1 := T.w_norm
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem KType.kSpan_eq_top {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.kSpan ε (kunits T) T.w = ⊤ := by
  rcases KType.dτ_irred T (Formalism.REAL.kSpan ε (kunits T) T.w)
    (fun a b hab v hv => Formalism.REAL.compact_span_stable T.w a b hab v hv) with h | h
  · exfalso
    have hw := Formalism.REAL.mem_compact_span_self (ε := ε) (F := kunits T) T.w
    rw [h, Submodule.mem_bot] at hw
    exact (KType.w_ne_zero T) hw
  · exact h

theorem KType.hw_unique {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ν : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (h : IsKHWVec ε (kunits T) ν v) : ν = Λ ∧ ∃ c : ℂ, v = c • T.w := by
  have hmem : v ∈ Formalism.REAL.kSpan ε (kunits T) T.w := by rw [KType.kSpan_eq_top T]; trivial
  rcases Formalism.REAL.kHiUniq T.V n ε (kunits T) Λ ν T.w v (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) hmem h with h0 | h1
  · exact absurd h0 hv
  · exact h1

theorem wtw_eq_sum (w : List (Fin n × Fin n)) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → (b, a) ∈ w) ∧
      -Formalism.REAL.wordWeightShift w = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [Formalism.REAL.wordWeightShift]⟩
  | cons p w ih =>
    obtain ⟨c, hc, heq⟩ := ih
    refine ⟨fun a b => c a b + if a = p.2 ∧ b = p.1 then 1 else 0, ?_, ?_⟩
    · intro a b hab
      change c a b + (if a = p.2 ∧ b = p.1 then 1 else 0) ≠ 0 at hab
      by_cases h : c a b = 0
      · rw [h, zero_add] at hab
        split_ifs at hab with h2
        · obtain ⟨rfl, rfl⟩ := h2
          simp
        · exact absurd rfl hab
      · exact List.mem_cons_of_mem _ (hc a b h)
    · have hs : ∑ a, ∑ b, (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b = root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2, Finset.sum_eq_single p.1]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro b _
          simp [ha]
        · intro h
          exact absurd (Finset.mem_univ _) h
      have e : ∀ a b, (((c a b + if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b =
          (c a b : ℝ) • root a b + (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b :=
        fun a b => by rw [Nat.cast_add, add_smul]
      simp only [e, Finset.sum_add_distrib, hs, ← heq]
      simp only [Formalism.REAL.wordWeightShift, root]
      abel

theorem KType.weight_le {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {μ : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (hμ : ∀ a, T.dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
      Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  have hmem : v ∈ Formalism.REAL.lowSpan ε (kunits T) T.w := by
    rw [← Formalism.REAL.compact_span_eq_lowering (KType.kRel T) (KType.kHighest_w T), KType.kSpan_eq_top T]; trivial
  obtain ⟨w, hw, hwμ⟩ : ∃ w : List (Fin n × Fin n), (∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) ∧
      Λ + Formalism.REAL.wordWeightShift w = μ := by
    by_contra hne
    push Not at hne
    apply hv
    have horth : ∀ y ∈ Formalism.REAL.lowSpan ε (kunits T) T.w, inner ℂ v y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro z ⟨w, hw, rfl⟩
        have hwt := Formalism.REAL.word_action_weight (KType.kRel T) (KType.kHighest_w T).1 w (fun q hq => (hw q hq).1)
        exact Formalism.REAL.kWtOrth T.V n ε (kunits T) μ _ v _ (KType.kUnit T) (fun a => hμ a) hwt
          (fun h => hne w hw h.symm)
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
    exact inner_self_eq_zero.mp (horth v hmem)
  obtain ⟨c, hc, he⟩ := wtw_eq_sum (n := n) w
  refine ⟨c, fun a b hab => ?_, ?_⟩
  · have := hw _ (hc a b hab)
    exact ⟨this.2, this.1.symm⟩
  · rw [← he, ← hwμ]; abel

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

