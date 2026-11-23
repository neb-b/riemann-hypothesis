module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.CmDatumInfinitePlacesComplexSplit
section
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem mult_two (w : InfinitePlace E) : w.mult = 2 := by
  simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]

private theorem rank_eq : (Module.finrank ℚ E : ℝ) = 2 * Fintype.card (InfinitePlace E) := by
  rw [← InfinitePlace.sum_mult_eq]
  simp [mult_two, mul_comm]

private theorem mod_inf (h : GL (Fin a) (Cinf E)) :
    (Reduction.detModule E a (infGL E a h) : ℝ) = ∏ w : InfinitePlace E, ‖h.val.det w‖ ^ 2 := by
  have e1 : pInf E (infGL E a h).val.det = h.val.det := by
    rw [RingHom.map_det]
    exact congrArg (fun y : GL (Fin a) (Cinf E) => y.val.det) (pInf_infGL h)
  have e2 : pFin E (infGL E a h).val.det = 1 := by
    rw [RingHom.map_det]
    exact (congrArg (fun y : GL (Fin a) (Af E) => y.val.det) (pFin_infGL h)).trans Matrix.det_one
  have h1 : ∀ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ = ‖h.val.det v‖ := fun v => by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    exact congrArg norm (congrFun e1 v)
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (infGL E a h).val.det v‖ = 1
    rw [e2]
    exact norm_one
  change (IdeleGroup.ideleModule E (AdelicGLn.det E a (infGL E a h)) : ℝ) = _
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one, mult_two]

private theorem sect_inv (ha : 1 ≤ a) (h : GL (Fin a) (Cinf E)) :
    (Reduction.centralSection E a (Reduction.detModule E a (infGL E a h)))⁻¹ =
      splitCentre E a (Real.log (sc h.val)) := by
  rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E a, ← map_inv (Reduction.centralSection E a)]
  refine congrArg _ (Subtype.ext ?_)
  have hne : ∀ w : InfinitePlace E, ‖h.val.det w‖ ≠ 0 := fun w =>
    norm_ne_zero_iff.2 (((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).map (Pi.evalRingHom _ w)).ne_zero
  have h1 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hp := (Reduction.detModule E a (infGL E a h)).2
  change (Reduction.detModule E a (infGL E a h) : ℝ)⁻¹ = Real.exp _
  rw [← Real.exp_log hp, ← Real.exp_neg, mod_inf, Real.log_prod fun w _ => pow_ne_zero _ (hne w), sc,
    Real.log_exp, rank_eq]
  congr 1
  simp only [Real.log_pow, ← Finset.mul_sum]
  field_simp
  push_cast
  ring

private theorem pInf_split (t : ℝ) (x : Fin a → Cinf E) :
    x ᵥ* (GeneralLinearGroup.map (pInf E) (splitCentre E a t)).val = Real.exp t • x := by
  rw [splitCentre, pInf_infGL]
  change x ᵥ* Matrix.diagonal (fun _ => (fun _ : InfinitePlace E => Complex.exp (t : ℂ))) = _
  ext i w
  rw [Matrix.vecMul_diagonal]
  simp [mul_comm]

end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.cmDatum_infinitePlaces_complex_split :
    RtInf := by
  intro E _ _ _ a ha g h v
  have e : rt (g * infGL E a h) = rt g * infGL E a h * splitCentre E a (Real.log (sc h.val)) := by
    rw [← sect_inv ha h, UpperTheory.V.Lit.Geo.rt, UpperTheory.V.Lit.Geo.rt, coe_retractOne, coe_retractOne, map_mul, map_mul, _root_.mul_inv_rev,
      mul_assoc g _⁻¹, ← map_inv (Reduction.centralSection E a) (Reduction.detModule E a g),
      Reduction.centralSection_mul_comm, ← Reduction.centralSection_mul_comm _ _⁻¹]
    simp only [mul_assoc]
  rw [e]
  change vInf v ᵥ* _ = sc h.val • ((vInf v ᵥ* _) ᵥ* _)
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, pInf_split,
    pInf_infGL, Real.exp_log (show 0 < sc h.val from Real.exp_pos _)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.DerivSimilitudeCharAtOneEqTrace
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped ContDiff

private theorem der_det {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun r : ℂ => (1 + r • M).det) M.trace 0 := by
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ r : ℂ, (1 + r • M).det = 1 + M.trace * r + p.eval r * r ^ 2 :=
    ⟨_, fun r => Matrix.det_one_add_smul r M⟩
  have h1 := (((hasDerivAt_id (0 : ℂ)).const_mul M.trace).const_add 1).add
    ((p.hasDerivAt 0).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
  rw [funext hp]
  exact HasDerivAt.congr_deriv h1 (by simp)

private theorem der_log {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => Real.log ‖(1 + (t : ℂ) • M).det‖) M.trace.re 0 := by
  have h1 := (der_det M).clog (by simp)
  have h2 : HasDerivAt (fun r : ℂ => Complex.log (1 + r • M).det) M.trace ((0 : ℝ) : ℂ) := by
    simpa using h1
  have h3 := h2.real_of_complex
  simpa only [Complex.log_re] using h3

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem det_ne {y : Matrix (Fin a) (Fin a) (Cinf E)} (hy : IsUnit y) (w : InfinitePlace E) : y.det w ≠ 0 :=
  (((Matrix.isUnit_iff_isUnit_det y).1 hy).map (Pi.evalMonoidHom (fun _ : InfinitePlace E => ℂ) w)).ne_zero

private theorem sm_at {y : Lie E a} (hy : IsUnit (Matrix.of y)) :
    ContDiffAt ℝ ∞ (fun y : Lie E a => sc (Matrix.of y)) y := by
  unfold sc
  refine ((ContDiffAt.sum fun w _ => ?_).div_const _).neg.exp
  have h : ContDiff ℝ ∞ fun x : Lie E a => (Matrix.of x).det w :=
    (contDiff_apply ℝ (fun _ => ℂ) w).comp GlobalTheory.CuspRep.contDiff_det
  exact (h.contDiffAt.norm ℝ (det_ne hy w)).log (norm_ne_zero_iff.2 (det_ne hy w))

private theorem det_line (X : Lie E a) (t : ℝ) (w : InfinitePlace E) :
    (Matrix.of (oneL E a + t • X)).det w = (1 + (t : ℂ) • Matrix.of fun i j => X i j w).det := by
  have h := (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).map_det (Matrix.of (oneL E a + t • X))
  refine h.trans (congrArg _ ?_)
  ext i j
  by_cases hij : i = j <;> simp [oneL, toL, Matrix.one_apply, hij]

private theorem der_sc (X : Lie E a) :
    HasDerivAt (fun t : ℝ => sc (Matrix.of (oneL E a + t • X))) (-ell E a X) 0 := by
  unfold sc
  simp only [det_line]
  have h := ((HasDerivAt.fun_sum (u := Finset.univ) fun (w : InfinitePlace E) _ =>
    der_log (Matrix.of fun i j => X i j w)).div_const ((a : ℝ) * Fintype.card (InfinitePlace E))).neg.exp
  exact HasDerivAt.congr_deriv h (by simp [ell, Matrix.trace])

private theorem sc_mul_star {y : Matrix (Fin a) (Fin a) (Cinf E)} : sc (y * star y) = sc y ^ 2 := by
  unfold sc
  rw [← Real.exp_nat_mul]
  congr 1
  have h : ∀ w, Real.log ‖(y * star y).det w‖ = 2 * Real.log ‖y.det w‖ := fun w => by
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Pi.mul_apply, Pi.star_apply,
      norm_mul, norm_star, ← sq, Real.log_pow]
    norm_num
  simp only [h, ← Finset.mul_sum]
  push_cast
  ring

private theorem sc_one : sc (1 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 := by
  simp [sc]

theorem UpperTheory.deriv_similitudeChar_at_one_eq_trace :
    ScSm := by
  intro E _ _ a
  refine ⟨fun y hy => (sm_at hy).contDiffWithinAt, sc_one, fun X => ?_, fun h => sc_mul_star, fun k => ?_⟩
  · have h1 : IsUnit (Matrix.of (oneL E a)) := isUnit_one
    have hd := ((sm_at h1).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a)
    have h2 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd hl (by simp)
    exact h2.unique (der_sc X)
  · have h : sc k.1 ^ 2 = 1 := by
      rw [← sc_mul_star, Matrix.mem_unitaryGroup_iff.1 k.2, sc_one]
    have hp : 0 < sc k.1 := Real.exp_pos _
    exact (pow_eq_one_iff_of_nonneg hp.le two_ne_zero).1 h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideComparison
section
open UpperTheory.V.Lit.Geo

set_option maxHeartbeats 800000 in
theorem UpperTheory.geometric_side_comparison :
    MeanLow := by
  unfold MeanLow
  refine ⟨Real.exp (-Real.pi) / 16, by positivity, ?_⟩
  intro A V _ _ _ φ hinj hS hT h2
  classical
  haveI : IsAddTorsionFree V := by
    constructor
    intro n hn x y _ hxy
    have h : ((n : ℝ)) • x = ((n : ℝ)) • y := by simpa [Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective V (Nat.cast_ne_zero.mpr hn) h
  have hfin : {x : A | ‖φ x‖ < 1}.Finite := by
    have h := hS.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-Real.pi)))
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    intro x (hx : ‖φ x‖ < 1)
    simp only [Set.mem_setOf_eq, not_lt]
    apply Real.exp_le_exp.mpr
    have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
    nlinarith [Real.pi_pos]
  have hfin2 : {x : A | ‖φ x‖ < 1 / 2}.Finite :=
    hfin.subset (fun x (hx : ‖φ x‖ < 1 / 2) => show ‖φ x‖ < 1 by linarith)
  set H := hfin.toFinset with hH
  set F := hfin2.toFinset with hF
  have hFH : F ⊆ H := by
    intro x hx
    simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    linarith
  have hcd : 2 * F.card - 1 ≤ H.card := by
    have h0 : (0 : A) ∈ F := by
      simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, norm_zero]
      norm_num
    have hne : (F.image φ).Nonempty := ⟨φ 0, Finset.mem_image_of_mem _ h0⟩
    have hcdv := cauchy_davenport_of_isAddTorsionFree hne hne
    have hcard : (F.image φ).card = F.card := Finset.card_image_of_injective _ hinj
    open scoped Pointwise in
    have hsub : F.image φ + F.image φ ⊆ H.image φ := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      refine Finset.mem_image.mpr ⟨x + y, ?_, map_add φ x y⟩
      simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add (f := _)]
      calc ‖φ x + φ y‖ ≤ ‖φ x‖ + ‖φ y‖ := norm_add_le _ _
        _ < 1 := by linarith
    have hle := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hle
    rw [hcard] at hcdv
    omega
  have hsd := Finset.card_sdiff_add_card_eq_card hFH
  have hreal : (F.card : ℝ) ≤ ((H \ F).card : ℝ) + 1 := by
    have : F.card ≤ (H \ F).card + 1 := by omega
    exact_mod_cast this
  have hT2 : ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) ≤
      ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
    refine le_trans ?_ (hT.sum_le_tsum (H \ F) (fun x _ => by positivity))
    have hpt : ∀ x ∈ H \ F, Real.exp (-Real.pi) / 4 ≤ ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
      intro x hx
      simp only [Finset.mem_sdiff, hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
      obtain ⟨h1, h3⟩ := hx
      have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
      have e1 : Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have e2 : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
      have := Real.exp_pos (-Real.pi)
      nlinarith
    calc ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) = ∑ x ∈ H \ F, Real.exp (-Real.pi) / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpt
  have hS1 : ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
      4 * ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) + F.card := by
    have hg : Summable (fun x => if x ∈ F then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero (s := F) (fun x hx => if_neg hx)
    have hsum : ∑' x, (if x ∈ F then (1 : ℝ) else 0) = F.card := by
      rw [tsum_eq_sum (s := F) (fun x hx => if_neg hx)]
      simp
    have hle : ∀ x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
        4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0) := by
      intro x
      have hp := Real.exp_pos (-Real.pi * ‖φ x‖ ^ 2)
      by_cases hx : x ∈ F
      · rw [if_pos hx]
        have : Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg ‖φ x‖])
        nlinarith [sq_nonneg ‖φ x‖]
      · rw [if_neg hx]
        simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
        have : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
        nlinarith
    calc _ ≤ ∑' x, (4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0)) :=
          Summable.tsum_le_tsum hle hS ((hT.mul_left 4).add hg)
      _ = _ := by rw [Summable.tsum_add (hT.mul_left 4) hg, tsum_mul_left, hsum]
  have hE := Real.exp_pos (-Real.pi)
  have hE1 : Real.exp (-Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  have hT0 : 0 ≤ ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
    tsum_nonneg (fun x => by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hS1 hE.le, mul_le_mul_of_nonneg_left hreal hE.le,
    mul_le_mul_of_nonneg_left h2 hE.le, mul_le_mul_of_nonneg_right hE1 hT0]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideEstimate
section
open UpperTheory.V.Lit.Geo

theorem UpperTheory.geometric_side_estimate :
    ScaleFull := by
  unfold ScaleFull Scale
  intro V _ _ _ Λ _ _
  obtain ⟨hsum1, hsum2, c, hc, hP⟩ := PI.Tr.poissonGauss V Λ
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (Module.finrank ℝ V : ℝ) / 2 := ⟨_, rfl⟩
  have e1 : -(Module.finrank ℝ V : ℝ) / 2 = -α := by rw [hα]; ring
  have key : ∀ r : ℝ, 0 < r → ∑' x : Λ, Real.exp (-Real.pi * (r * ‖(x : V)‖ ^ 2)) =
      c * r ^ (-α) * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / r) := by
    intro r hr
    have h := hP r hr 0
    simp only [add_zero, inner_zero_right, mul_zero, Real.cos_zero, mul_one] at h
    rw [← e1, ← h]
    refine tsum_congr (fun x => ?_)
    congr 1
    ring
  refine ⟨fun x => sq_nonneg _, fun s t hs hst => ?_⟩
  have ht : 0 < t := lt_of_lt_of_le hs hst
  refine ⟨by simpa [mul_assoc] using hsum1 s hs 0, ?_⟩
  rw [key s hs, key t ht]
  have hD : ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / s) ≤
      ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) := by
    refine Summable.tsum_le_tsum (fun y => Real.exp_le_exp.mpr ?_) (hsum2 s hs) (hsum2 t ht)
    have h0 : 0 ≤ Real.pi * ‖(y : V)‖ ^ 2 := by positivity
    have h3 : Real.pi * ‖(y : V)‖ ^ 2 / t ≤ Real.pi * ‖(y : V)‖ ^ 2 / s :=
      div_le_div_of_nonneg_left h0 hs hst
    rw [neg_mul, neg_div, neg_div]
    linarith
  have hD0 : 0 ≤ ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) :=
    tsum_nonneg (fun y => (Real.exp_pos _).le)
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hS : s ^ α ≤ t ^ α := Real.rpow_le_rpow hs.le hst hα0
  have hSpos : 0 < s ^ α := Real.rpow_pos_of_pos hs α
  have hTpos : 0 < t ^ α := Real.rpow_pos_of_pos ht α
  have hpow : (t / s) ^ Module.finrank ℝ V = (t ^ α) ^ 2 / (s ^ α) ^ 2 := by
    rw [← div_pow, ← Real.div_rpow ht.le hs.le, ← Real.rpow_mul_natCast (div_nonneg ht.le hs.le),
      ← Real.rpow_natCast]
    congr 1
    rw [hα]
    push_cast
    ring
  have hcD : 0 ≤ c * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) :=
    mul_nonneg hc.le hD0
  have h1 : (s ^ α)⁻¹ ≤ (t ^ α) ^ 2 / (s ^ α) ^ 2 * (t ^ α)⁻¹ := by
    rw [show (t ^ α) ^ 2 / (s ^ α) ^ 2 * (t ^ α)⁻¹ = t ^ α / (s ^ α) ^ 2 by
      field_simp]
    rw [inv_eq_one_div, div_le_div_iff₀ hSpos (by positivity)]
    nlinarith
  rw [Real.rpow_neg hs.le, Real.rpow_neg ht.le, hpow]
  calc c * (s ^ α)⁻¹ * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / s)
      ≤ c * (s ^ α)⁻¹ * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg hc.le (inv_nonneg.mpr hSpos.le))
    _ = (c * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t)) * (s ^ α)⁻¹ := by ring
    _ ≤ (c * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t)) *
          ((t ^ α) ^ 2 / (s ^ α) ^ 2 * (t ^ α)⁻¹) := mul_le_mul_of_nonneg_left h1 hcD
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideLowerBound
section
open UpperTheory.V.Lit.Geo

theorem UpperTheory.geometric_side_lower_bound :
    ThetaLow := by
  classical
  intro A V _ _ _ φ hs v hv
  have ht : 0 < ‖φ v‖ := norm_pos_iff.mpr hv
  set t := ‖φ v‖ with htdef
  have hn : ∀ k : ℕ, ‖φ (k • v)‖ = k * t := by
    intro k
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
  have hinj : Function.Injective (fun k : ℕ => k • v) := by
    intro k l h
    have h1 : (k : ℝ) * t = l * t := by
      rw [← hn k, ← hn l]
      exact congrArg (fun x => ‖φ x‖) h
    exact_mod_cast mul_right_cancel₀ ht.ne' h1
  set n := ⌊1 / t⌋₊ with hndef
  have h1 : 1 / t < n + 1 := Nat.lt_floor_add_one _
  have h2 : (n : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
  have h3 : ∑ x ∈ (Finset.range (n + 1)).image (fun k : ℕ => k • v), Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
      ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
    hs.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun a _ b _ h => hinj h)] at h3
  have h4 : ∑ _k ∈ Finset.range (n + 1), Real.exp (-Real.pi) ≤
      ∑ k ∈ Finset.range (n + 1), Real.exp (-Real.pi * ‖φ (k • v)‖ ^ 2) := by
    refine Finset.sum_le_sum fun k hk => Real.exp_le_exp.mpr ?_
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h5 : (k : ℝ) * t ≤ 1 := by
      have := hk'.trans h2
      rwa [le_div_iff₀ ht] at this
    have h6 : 0 ≤ (k : ℝ) * t := by positivity
    have h7 : ((k : ℝ) * t) ^ 2 ≤ 1 := by nlinarith
    rw [hn]
    nlinarith [Real.pi_pos]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
  push_cast at h4
  have h8 : 1 ≤ t * (n + 1) := by
    rw [div_lt_iff₀ ht] at h1
    linarith
  have h9 := mul_le_mul_of_nonneg_left (h4.trans h3) ht.le
  have h10 := mul_le_mul_of_nonneg_right h8 (Real.exp_pos (-Real.pi)).le
  calc Real.exp (-Real.pi) = 1 * Real.exp (-Real.pi) := (one_mul _).symm
    _ ≤ t * (n + 1) * Real.exp (-Real.pi) := h10
    _ = t * ((n + 1) * Real.exp (-Real.pi)) := by ring
    _ ≤ _ := h9
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem quad_eq (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Fin a → Cinf E) :
    quad p x = ∑ w : InfinitePlace E, ∑ j, ∑ i, (x i w * p i j w * star (x j w)).re := by
  simp only [quad, dotProduct, vecMul, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, Complex.re_sum, Finset.sum_mul]

private theorem qf_eq (x : Fin a → Cinf E) :
    qf x = ∑ w : InfinitePlace E, ((x ⬝ᵥ star x) w).re := by
  rw [qf, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dotProduct, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem UpperTheory.geometric_side_quadraticForm_identity :
    QfFacts := by
  intro E _ _ a
  refine ⟨fun x => ?_, fun p p' c x => ⟨?_, ?_⟩, fun h x => ?_, fun c x => ?_, fun p x => ?_, fun x => ⟨?_, ?_⟩⟩
  · rw [qf_eq, quad, vecMul_one]
  · simp only [quad_eq, Matrix.add_apply, Pi.add_apply, mul_add, add_mul, Complex.add_re, Finset.sum_add_distrib]
  · simp only [quad_eq, Matrix.smul_apply, Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, Complex.smul_re, smul_eq_mul]
  · rw [qf_eq, quad, star_vecMul, dotProduct_mulVec, vecMul_vecMul]
    rfl
  · simp only [qf, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  · have hp : ∀ i j w, ‖p i j w‖ ≤ ‖toL p‖ := fun i j w =>
      ((norm_le_pi_norm (toL p i j) w).trans (norm_le_pi_norm (toL p i) j)).trans (norm_le_pi_norm (toL p) i)
    have key : ∀ w j i, |(x i w * p i j w * star (x j w)).re| ≤ ‖toL p‖ / 2 * (‖x i w‖ ^ 2 + ‖x j w‖ ^ 2) := by
      intro w j i
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, norm_star]
      have h1 := hp i j w
      have h2 := norm_nonneg (p i j w)
      have h3 := mul_nonneg (norm_nonneg (x i w)) (norm_nonneg (x j w))
      have h4 := mul_le_mul_of_nonneg_left h1 h3
      have h5 := mul_nonneg (h2.trans h1) (sq_nonneg (‖x i w‖ - ‖x j w‖))
      nlinarith
    rw [quad_eq, qf, Finset.sum_comm (f := fun i w => ‖x i w‖ ^ 2), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    calc _ ≤ ∑ j, ∑ i, ‖toL p‖ / 2 * (‖x i w‖ ^ 2 + ‖x j w‖ ^ 2) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => key w j i))
      _ = _ := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  · have h0 := qf_nonneg x
    have h : ‖x‖ ≤ √(qf x) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => Real.le_sqrt_of_sq_le ?_
      calc ‖x i w‖ ^ 2 ≤ ∑ w, ‖x i w‖ ^ 2 :=
            Finset.single_le_sum (f := fun w => ‖x i w‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w)
        _ ≤ qf x := Finset.single_le_sum (f := fun i => ∑ w, ‖x i w‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖x‖ ^ 2 ≤ √(qf x) ^ 2 := by gcongr
      _ = qf x := Real.sq_sqrt h0
  · calc qf x ≤ ∑ _i : Fin a, ∑ _w : InfinitePlace E, ‖x‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun w _ => ?_
          have := (norm_le_pi_norm (x i) w).trans (norm_le_pi_norm x i)
          gcongr
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
end

