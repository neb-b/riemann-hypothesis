module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofTorMkCIsQuotientMap
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.NormSqRiemannThetaMulExpPeriodic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEqMulCanonicalThetaOfSignMultiplier
section
noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem eC_half_char_emod_two (p q n n' : Fin g → ℤ) :
    eC (ofRealVec (fun i => (p i : ℝ) / 2) ⬝ᵥ ofIntVec n' -
      ofRealVec (fun i => (q i : ℝ) / 2) ⬝ᵥ ofIntVec n) =
    eC (ofRealVec (fun i => ((p i % 2 : ℤ) : ℝ) / 2) ⬝ᵥ ofIntVec n' -
      ofRealVec (fun i => ((q i % 2 : ℤ) : ℝ) / 2) ⬝ᵥ ofIntVec n) := by
  have split : ∀ r : Fin g → ℤ, ofRealVec (fun i => (r i : ℝ) / 2) =
      ofIntVec (fun i => r i / 2) + ofRealVec (fun i => ((r i % 2 : ℤ) : ℝ) / 2) := by
    intro r
    funext i
    simp only [ofRealVec, ofIntVec, Pi.add_apply]
    have hr : r i = 2 * (r i / 2) + r i % 2 := by omega
    conv_lhs => rw [hr]
    push_cast
    ring
  have intdot : ∀ r s : Fin g → ℤ, ofIntVec r ⬝ᵥ ofIntVec s = ((r ⬝ᵥ s : ℤ) : ℂ) := by
    intro r s
    simp [ofIntVec, dotProduct]
  have shift : ∀ (k : ℤ) (y : ℂ), eC (k + y) = eC y := by
    intro k y
    unfold eC
    rw [mul_add, Complex.exp_add]
    have hk : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * k) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * k = k * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [hk, one_mul]
  have hsub : ∀ (u v : ℤ) (A B : ℂ), eC ((u : ℂ) + A - ((v : ℂ) + B)) = eC (A - B) := by
    intro u v A B
    rw [show (u : ℂ) + A - ((v : ℂ) + B) = ((u - v : ℤ) : ℂ) + (A - B) by push_cast; ring]
    exact shift _ _
  rw [split p, split q, add_dotProduct, add_dotProduct, intdot, intdot]
  exact hsub _ _ _ _

theorem classical_law_of_canonical {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) {c : ℂ} {f : (Fin g → ℂ) → ℂ} (m n : Fin g → ℤ)
    (z : Fin g → ℂ) {l : Fin g → ℂ} (hl : l = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)))
    (h : f (z + l) = c * cexp (π * hermForm (imInv τ) z l + π / 2 * hermForm (imInv τ) l l) * f z) :
    cexp (-(π / 2 * ((z + l) ⬝ᵥ imInv τ *ᵥ (z + l)))) * f (z + l) =
      c * cexp (-(π * I * ((m ⬝ᵥ n : ℤ) : ℂ))) *
        eC (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) *
        (cexp (-(π / 2 * (z ⬝ᵥ imInv τ *ᵥ z))) * f z) := by
  set M := imInv τ with hMdef
  set nC : Fin g → ℂ := fun i => (n i : ℂ) with hnC
  set mC : Fin g → ℂ := fun i => (m i : ℂ) with hmC
  have hMsymm : Mᵀ = M := isSymm_imInv hs
  have hswap : ∀ u v : Fin g → ℂ, u ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ u := by
    intro u v
    rw [dotProduct_mulVec, ← mulVec_transpose, hMsymm, dotProduct_comm]
  have hY : M *ᵥ (((τ.map Complex.im).map fun x : ℝ => (x : ℂ)) *ᵥ nC) = nC := by
    rw [mulVec_mulVec, imInv_mul hp, one_mulVec]
  have hstar : star l = l - (2 * I) • (((τ.map Complex.im).map fun x : ℝ => (x : ℂ)) *ᵥ nC) := by
    subst hl
    funext i
    simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, Matrix.map_apply, star_add, star_sum, Finset.mul_sum]
    rw [add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    · simp [hmC]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hnC]
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hMstar : M *ᵥ star l = M *ᵥ l - (2 * I) • nC := by
    rw [hstar, mulVec_sub, mulVec_smul, hY]
  have hH1 : hermForm M z l = z ⬝ᵥ M *ᵥ l - 2 * I * (z ⬝ᵥ nC) := by
    unfold hermForm
    rw [hMstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hH2 : hermForm M l l = l ⬝ᵥ M *ᵥ l - 2 * I * (l ⬝ᵥ nC) := by
    unfold hermForm
    rw [hMstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hquad : (z + l) ⬝ᵥ M *ᵥ (z + l) = z ⬝ᵥ M *ᵥ z + 2 * (z ⬝ᵥ M *ᵥ l) + l ⬝ᵥ M *ᵥ l := by
    rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hswap l z]
    ring
  have hln : l ⬝ᵥ nC = ((m ⬝ᵥ n : ℤ) : ℂ) + ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) := by
    rw [hl, add_dotProduct]
    congr 1
    · simp [hmC, hnC, dotProduct]
    · rw [dotProduct_comm]
      rfl
  have hzn : z ⬝ᵥ nC = ofIntVec n ⬝ᵥ z := by
    rw [dotProduct_comm]
    rfl
  have E : -(π / 2 * ((z + l) ⬝ᵥ M *ᵥ (z + l))) +
      (π * hermForm M z l + π / 2 * hermForm M l l) =
      -(π * I * ((m ⬝ᵥ n : ℤ) : ℂ)) +
        2 * π * I * (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) +
        -(π / 2 * (z ⬝ᵥ M *ᵥ z)) := by
    rw [hquad, hH1, hH2, hln, hzn]
    push_cast
    ring
  rw [h]
  calc cexp (-(π / 2 * ((z + l) ⬝ᵥ M *ᵥ (z + l)))) *
        (c * cexp (π * hermForm M z l + π / 2 * hermForm M l l) * f z)
      = c * f z * cexp (-(π / 2 * ((z + l) ⬝ᵥ M *ᵥ (z + l))) +
          (π * hermForm M z l + π / 2 * hermForm M l l)) := by
        simp only [Complex.exp_add]
        ring
    _ = c * f z * cexp (-(π * I * ((m ⬝ᵥ n : ℤ) : ℂ)) +
        2 * π * I * (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) +
        -(π / 2 * (z ⬝ᵥ M *ᵥ z))) := by rw [E]
    _ = _ := by
        unfold eC
        rw [Complex.exp_add, Complex.exp_add]
        ring

end SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_eq_mul_canonical_theta_of_sign_multiplier :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (α : (Fin g → ℤ) → (Fin g → ℤ) → ℂ) (f : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → (∀ m n, α m n ^ 2 = 1) → Differentiable ℂ f → f ≠ 0 →
    (∀ (m n : Fin g → ℤ) (l z : Fin g → ℂ), l = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      f (z + l) = α m n * Complex.exp (Real.pi * hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) z l +
        Real.pi / 2 * hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) l l) * f z) →
    ∃ (a b : Fin g → ℝ) (c : ℂ), (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ c ≠ 0 ∧
      ∀ z, f z = c * (Complex.exp (Real.pi / 2 * (z ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)).mulVec z)) *
        thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) z) := by
  intro g τ α f hs hp hα2 hf hf0 hlaw
  classical
  let M : Matrix (Fin g) (Fin g) ℂ := CanTh.imInv τ
  let F : (Fin g → ℂ) → ℂ := fun z => Complex.exp (-(Real.pi / 2 * (z ⬝ᵥ M.mulVec z))) * f z
  let χ : (Fin g → ℤ) → (Fin g → ℤ) → ℂ := fun n n' =>
    α n' n * Complex.exp (-(Real.pi * Complex.I * ((n' ⬝ᵥ n : ℤ) : ℂ)))
  have hlawF : ∀ (n n' : Fin g → ℤ) (z : Fin g → ℂ),
      F (z + τ.mulVec (ReciprocityTheory.PTheta.ofIntVec n) + ReciprocityTheory.PTheta.ofIntVec n') = χ n n' *
        ReciprocityTheory.PTheta.eC (-((1 : ℕ) : ℂ) * (ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ
          (τ.mulVec (ReciprocityTheory.PTheta.ofIntVec n)) / 2 + ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * F z := by
    intro n n' z
    have hw : z + τ.mulVec (ReciprocityTheory.PTheta.ofIntVec n) + ReciprocityTheory.PTheta.ofIntVec n' =
        z + ((fun i => (n' i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) := by
      rw [add_assoc, add_comm (τ.mulVec _)]
      rfl
    have key := classical_law_of_canonical hs hp n' n z rfl (hlaw n' n _ z rfl)
    simp only [F, χ]
    rw [hw, key]
  have hF0 : F ≠ 0 := by
    intro h0
    apply hf0
    funext z
    have hz := congrFun h0 z
    simp only [F, Pi.zero_apply] at hz
    exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)
  have hquad : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ M.mulVec z) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hFd : Differentiable ℂ F := ((hquad.const_mul _).neg.cexp).mul hf
  have hone : ∀ x : ℂ, x ^ 2 = 1 → x = 1 ∨ x = -1 := by
    intro x hx
    have h' : (x - 1) * (x + 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  have hsign : ∀ n n', χ n n' = 1 ∨ χ n n' = -1 := by
    intro n n'
    apply hone
    simp only [χ]
    rw [mul_pow, hα2, _root_.one_mul, sq, ← Complex.exp_add]
    rw [show -(Real.pi * Complex.I * ((n' ⬝ᵥ n : ℤ) : ℂ)) + -(Real.pi * Complex.I * ((n' ⬝ᵥ n : ℤ) : ℂ)) =
      ((-(n' ⬝ᵥ n) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hchar := multiplier_add_of_ne_zero (N := 1) hs hF0 hlawF
  obtain ⟨p, q, hpq⟩ := exists_half_char_of_sign hchar hsign
  have hmem : F ∈ thetaLevelChar (fun i => ((p i % 2 : ℤ) : ℝ) / 2)
      (fun i => ((q i % 2 : ℤ) : ℝ) / 2) 1 τ := by
    rw [mem_thetaLevelChar]
    refine ⟨hFd, fun n n' z => ?_⟩
    rw [hlawF, hpq, eC_half_char_emod_two p q n n', Nat.cast_one, _root_.one_mul]
  rw [thetaLevelChar_one ⟨hs, hp⟩, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hF0
    rw [← hc, zero_smul]
  have hhalf : ∀ r : ℤ, ((r % 2 : ℤ) : ℝ) / 2 = 0 ∨ ((r % 2 : ℤ) : ℝ) / 2 = 1 / 2 := by
    intro r
    rcases Int.emod_two_eq_zero_or_one r with h | h <;> simp [h]
  refine ⟨fun i => ((p i % 2 : ℤ) : ℝ) / 2, fun i => ((q i % 2 : ℤ) : ℝ) / 2, c,
    fun i => hhalf (p i), fun i => hhalf (q i), hc0, fun z => ?_⟩
  show f z = c * (Complex.exp (Real.pi / 2 * (z ⬝ᵥ M.mulVec z)) * _)
  rw [CanTh.thetaChar_eq_theta]
  have hz := congrFun hc z
  simp only [Pi.smul_apply, smul_eq_mul, F] at hz
  rw [mul_left_comm, hz, ← _root_.mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
    _root_.one_mul]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
section
open Complex Matrix MeasureTheory
open scoped Real MatrixOrder

noncomputable section

namespace GlobalTheory.ThetaNorm

theorem lintegral_exp_neg_quadratic {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) :
    ∫⁻ y : Fin g → ℝ, ENNReal.ofReal (Real.exp (-2 * π * (y ⬝ᵥ Y *ᵥ y))) =
      ENNReal.ofReal (Real.sqrt (2 ^ g * Y.det))⁻¹ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg
  have hBt : Y = Bᵀ * B := by rw [hB]; rfl
  have hdet : Y.det = B.det ^ 2 := by rw [hBt, det_mul, det_transpose, sq]
  have hB0 : B.det ≠ 0 := by
    intro h
    have := hY.det_pos
    rw [hdet, h] at this
    simp at this
  set M := Matrix.toLin' B with hM
  have hMdet : LinearMap.det M ≠ 0 := by rw [hM, LinearMap.det_toLin']; exact hB0
  set F : (Fin g → ℝ) → ℝ := fun w => ∏ i, Real.exp (-(2 * π) * w i ^ 2) with hF
  have hFc : Continuous F := by rw [hF]; fun_prop
  have h1 (y : Fin g → ℝ) : Real.exp (-2 * π * (y ⬝ᵥ Y *ᵥ y)) = F (M y) := by
    rw [hBt, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hF]
    simp only [← Real.exp_sum, hM, toLin'_apply, dotProduct, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [h1]
  have hFm : Measurable fun w => ENNReal.ofReal (F w) :=
    ENNReal.measurable_ofReal.comp hFc.measurable
  have hMm : Measurable M := (LinearMap.continuous_of_finiteDimensional M).measurable
  have hint : Integrable F := by
    rw [hF, volume_pi]
    exact Integrable.fintype_prod (f := fun _ (t : ℝ) => Real.exp (-(2 * π) * t ^ 2))
      fun _ => integrable_exp_neg_mul_sq (by positivity)
  have hval : ∫ w, F w = (Real.sqrt 2)⁻¹ ^ g := by
    rw [hF, integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-(2 * π) * t ^ 2)),
      integral_gaussian, Fintype.card_fin, ← Real.sqrt_inv]
    congr 2
    field_simp
  rw [← lintegral_map hFm hMm, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hMdet,
    lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun w => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le),
    hval, smul_eq_mul, ← ENNReal.ofReal_mul (abs_nonneg _), hM, LinearMap.det_toLin', hdet,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_inv, mul_inv, mul_comm, inv_pow]
  congr 3
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
    Real.mul_self_sqrt (by norm_num)]

theorem hasSum_norm_sq_of_summable {g : ℕ} {c : (Fin g → ℤ) → ℂ} (hc : Summable fun m => ‖c m‖) :
    HasSum (fun m => ‖c m‖ ^ 2) (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      ‖∑' m, c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ)))‖ ^ 2) := by
  have hn (m : Fin g → ℤ) (x : Fin g → ℝ) :
      ‖c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ)))‖ = ‖c m‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp [dotProduct]
  have hbox : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =ᵐ[volume] Set.Icc 0 1 := by
    have e : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.univ.pi fun i => Set.Ioc ((0 : Fin g → ℝ) i) ((1 : Fin g → ℝ) i) := by
      ext; simp
    rw [e]
    exact Measure.univ_pi_Ioc_ae_eq_Icc
  have h := ReciprocityTheory.ChartRestriction.G.I2.tof_torus_parseval
    (fun x : Fin g → ℝ =>
      ∑' m, c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))))
    (continuous_tsum (fun m => by simp only [dotProduct]; fun_prop) hc fun m x => (hn m x).le)
    (fun x n => tsum_congr fun m => by
      congr 1
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨m ⬝ᵥ n, ?_⟩
      simp only [dotProduct, Pi.add_apply]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      ring)
  simp only [setIntegral_congr_set hbox] at h
  convert h using 3 with n
  rw [← integral_Icc_tsum_mul_cexp hc n]
  congr 2
  funext x
  rw [mul_comm, neg_mul]
  rfl

theorem hasSum_integral_norm_sq_riemannTheta {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (h : IsSiegel τ) (a b : Fin g → ℝ) (v : Fin g → ℂ) :
    HasSum (fun m => ‖riemannThetaTerm a b τ v m‖ ^ 2) (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      ‖riemannTheta a b τ (v + fun i => (x i : ℂ))‖ ^ 2) := by
  convert hasSum_norm_sq_of_summable (h.summable_norm_riemannThetaTerm a b v) using 4 with x
  rw [riemannTheta_add_ofReal_eq_tsum, norm_mul, Complex.norm_exp]
  simp [dotProduct]

theorem norm_sq_riemannThetaTerm_mul_exp {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (h : τ.IsSymm) (a b y : Fin g → ℝ) (n : Fin g → ℤ) :
    ‖riemannThetaTerm a b τ (τ *ᵥ fun i => (y i : ℂ)) n‖ ^ 2 *
        Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y)) =
      Real.exp (-2 * π * ((y + (fun i => (n i : ℝ)) + a) ⬝ᵥ
        τ.map Complex.im *ᵥ (y + (fun i => (n i : ℝ)) + a))) := by
  have hs : (τ.map Complex.im).IsSymm := h.map _
  have e1 : (fun i => ((τ *ᵥ fun i => (y i : ℂ)) i).im) = τ.map Complex.im *ᵥ y := by
    funext i
    simp [mulVec, dotProduct]
  have e2 : y + (fun i => (n i : ℝ)) + a = y + fun i => (n i : ℝ) + a i := by
    rw [add_assoc]; rfl
  rw [norm_riemannThetaTerm, e1, e2, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  generalize (fun i => (n i : ℝ) + a i) = u
  have e3 : y ⬝ᵥ τ.map Complex.im *ᵥ u = u ⬝ᵥ τ.map Complex.im *ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, e3]
  push_cast
  ring

theorem lintegral_lintegral_norm_sq_riemannTheta {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (h : IsSiegel τ) (a b : Fin g → ℝ) :
    ∫⁻ y in Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1,
      ∫⁻ x in Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1, ENNReal.ofReal
        (‖riemannTheta a b τ ((fun i => (x i : ℂ)) + τ *ᵥ fun i => (y i : ℂ))‖ ^ 2 *
          Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y))) =
      ENNReal.ofReal (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  have hθ : Continuous (riemannTheta a b τ) :=
    (continuousOn_riemannTheta a b).comp_continuous (f := fun v => (v, τ)) (by fun_prop)
      fun v => ⟨trivial, h⟩
  have hbox : (Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1) =ᵐ[volume] Set.Icc 0 1 :=
    Measure.univ_pi_Ico_ae_eq_Icc (f := (0 : Fin g → ℝ)) (g := 1)
  set G : (Fin g → ℝ) → ENNReal := fun y =>
    ENNReal.ofReal (Real.exp (-2 * π * ((y + a) ⬝ᵥ τ.map Complex.im *ᵥ (y + a)))) with hG
  have hGm : Measurable G := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    simp only [dotProduct, mulVec]
    fun_prop
  have hin (y : Fin g → ℝ) :
      ∫⁻ x in Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1, ENNReal.ofReal
        (‖riemannTheta a b τ ((fun i => (x i : ℂ)) + τ *ᵥ fun i => (y i : ℂ))‖ ^ 2 *
          Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y))) =
      ∑' n : Fin g → ℤ, G (y + fun i => (n i : ℝ)) := by
    have hs := (hasSum_integral_norm_sq_riemannTheta h a b (τ *ᵥ fun i => (y i : ℂ))).mul_right
      (Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y)))
    simp only [norm_sq_riemannThetaTerm_mul_exp h.isSymm] at hs
    rw [setLIntegral_congr hbox, ← ofReal_integral_eq_lintegral_ofReal
      (Continuous.integrableOn_Icc (by fun_prop))
      (Filter.Eventually.of_forall fun x => by positivity), integral_mul_const]
    simp only [add_comm _ (τ *ᵥ _)]
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hs.summable]
  simp only [hin]
  have hc : ReciprocityTheory.ChartRestriction.G.I2.cubeIco (Fin g) = Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1 := by
    ext; simp [ReciprocityTheory.ChartRestriction.G.I2.cubeIco]
  rw [lintegral_tsum (f := fun (n : Fin g → ℤ) y => G (y + fun i => (n i : ℝ)))
      fun n => (hGm.comp (measurable_add_const _)).aemeasurable, ← hc,
    ← ReciprocityTheory.ChartRestriction.G.I2.unfold_Zn G, ← lintegral_exp_neg_quadratic h.posDef]
  exact lintegral_add_right_eq_self
    (fun y => ENNReal.ofReal (Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y)))) a


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem integral_norm_sq_thetaChar :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ), τ.IsSymm →
      (τ.map Complex.im).PosDef →
      ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
        ‖thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ))
            ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))‖ ^ 2 *
          Real.exp (-2 * Real.pi *
            ((fun i => p (.inr i)) ⬝ᵥ (τ.map Complex.im).mulVec (fun i => p (.inr i)))) =
        (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ a b hs hp
  have h : IsSiegel τ := ⟨hs, hp⟩
  have hθ : Continuous (riemannTheta a b τ) :=
    (continuousOn_riemannTheta a b).comp_continuous (f := fun v => (v, τ)) (by fun_prop)
      fun v => ⟨trivial, h⟩
  simp only [← RiemannThetaModel.riemannTheta_eq_thetaChar]
  set f : (Fin g → ℝ) × (Fin g → ℝ) → ℝ := fun q =>
    ‖riemannTheta a b τ ((fun i => (q.1 i : ℂ)) + τ *ᵥ fun i => (q.2 i : ℂ))‖ ^ 2 *
      Real.exp (-2 * π * (q.2 ⬝ᵥ τ.map Complex.im *ᵥ q.2)) with hf
  have hfc : Continuous f := by
    refine Continuous.mul (((hθ.comp ?_).norm).pow 2) ?_
    · refine continuous_pi fun i => ?_
      simp only [Pi.add_apply, dotProduct, mulVec]
      fun_prop
    · simp only [dotProduct, mulVec]
      fun_prop
  have hmp := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin g ⊕ Fin g => ℝ)
  set C := Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1 with hC
  have hpre : Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1) =
      MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin g ⊕ Fin g => ℝ) ⁻¹' (C ×ˢ C) := by
    ext p
    simp [hC, MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  have key := hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) f (C ×ˢ C)
  rw [hpre]
  refine key.trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => by
      simp only [hf]; positivity) hfc.aestronglyMeasurable, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod_symm' (fun q => ENNReal.ofReal (f q))
      (ENNReal.measurable_ofReal.comp hfc.measurable)]
  simp only [hf, hC]
  rw [lintegral_lintegral_norm_sq_riemannTheta h, ENNReal.toReal_ofReal (by positivity)]

end GlobalTheory.ThetaNorm
end
end

