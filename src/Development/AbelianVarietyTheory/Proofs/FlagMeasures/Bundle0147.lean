module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0117
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentSkew
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.TwoSidedJac

open Kronecker

noncomputable def twoSided {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    Matrix (Fin a) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin b) ℂ where
  toFun T := A * T * B
  map_add' S T := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c T := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem twoSided_apply {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (T : Matrix (Fin a) (Fin b) ℂ) : twoSided A B T = A * T * B := rfl

theorem det_twoSided {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    LinearMap.det (twoSided A B) = A.det ^ b * B.det ^ a := by
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b))]
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b))
      (Matrix.stdBasis ℂ (Fin a) (Fin b)) (twoSided A B) = A ⊗ₖ Bᵀ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, twoSided_apply]
    have hr : ∀ M : Matrix (Fin a) (Fin b) ℂ,
        (Matrix.stdBasis ℂ (Fin a) (Fin b)).repr M (i, j) = M i j := by
      intro M
      simp [Matrix.stdBasis]
    rw [hr]
    simp [Matrix.mul_apply, Matrix.single, Finset.sum_mul, ite_and]
  rw [h, Matrix.det_kronecker, Matrix.det_transpose]
  simp

section Skew

variable {a : ℕ} {ι : Type} [Fintype ι]

theorem star_coe (T : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)) :
    star (T : Matrix (Fin a) (Fin a) ℂ) = -(T : Matrix (Fin a) (Fin a) ℂ) :=
  skewAdjoint.mem_iff.mp T.2

theorem linearIndependent_skew
    (e : Module.Basis ι ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))) :
    LinearIndependent ℂ (fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
  have hR : ∀ g : ι → ℝ, ∑ i, (g i : ℂ) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0 → ∀ i, g i = 0 := by
    intro g hg
    apply Fintype.linearIndependent_iff.mp e.linearIndependent g
    apply Subtype.ext
    simpa using hg
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h2 : ∑ i, (starRingEnd ℂ (g i)) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0 := by
    have := congrArg star hg
    simp only [star_sum, star_smul, star_coe, smul_neg, Finset.sum_neg_distrib, star_zero,
      neg_eq_zero] at this
    exact this
  have hre : ∀ i, 2 * (g i).re = 0 := by
    apply hR
    have : ∀ i, ((2 * (g i).re : ℝ) : ℂ) = g i + starRingEnd ℂ (g i) := fun i =>
      (Complex.add_conj _).symm
    simp only [this, add_smul, Finset.sum_add_distrib, hg, h2, add_zero]
  have him : ∀ i, 2 * (g i).im = 0 := by
    apply hR
    have : ∀ i, ((2 * (g i).im : ℝ) : ℂ) = (-Complex.I) * (g i - starRingEnd ℂ (g i)) := by
      intro i
      rw [Complex.sub_conj]
      have := Complex.I_mul_I
      linear_combination ((2 * (g i).im : ℝ) : ℂ) * this
    simp only [this, mul_smul, ← Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, hg, h2,
      sub_zero, smul_zero]
  intro i
  apply Complex.ext
  · have := hre i
    simpa using this
  · have := him i
    simpa using this

theorem span_skew
    (e : Module.Basis ι ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
  have hS : ∀ T : Matrix (Fin a) (Fin a) ℂ, star T = -T →
      T ∈ Submodule.span ℂ (Set.range fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
    intro T hT
    have h := congrArg Subtype.val (e.sum_repr ⟨T, skewAdjoint.mem_iff.mpr hT⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    rw [← h]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro T _
  have h1 := hS (T - star T) (by simp)
  have h2 := hS (Complex.I • (T + star T)) (by simp [star_smul, add_comm])
  have : T = (1 / 2 : ℂ) • ((T - star T) + (-Complex.I) • (Complex.I • (T + star T))) := by
    rw [smul_smul]
    simp only [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    module
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2))

theorem det_skew_eq
    (L : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ) →ₗ[ℝ]
      skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))
    (F : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (h : ∀ T, (L T : Matrix (Fin a) (Fin a) ℂ) = F T) :
    ((LinearMap.det L : ℝ) : ℂ) = LinearMap.det F := by
  classical
  let e := Module.finBasis ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))
  let e' := Module.Basis.mk (linearIndependent_skew e) (span_skew e)
  have he : ∀ i, e' i = (e i : Matrix (Fin a) (Fin a) ℂ) := fun i => Module.Basis.mk_apply _ _ i
  rw [← LinearMap.det_toMatrix e, ← LinearMap.det_toMatrix e']
  have hm : LinearMap.toMatrix e' e' F = (LinearMap.toMatrix e e L).map Complex.ofRealHom := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, he, ← h]
    have h1 : (L (e j) : Matrix (Fin a) (Fin a) ℂ) =
        ∑ k, ((e.repr (L (e j)) k : ℝ) : ℂ) • e' k := by
      have h := congrArg Subtype.val (e.sum_repr (L (e j)))
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      rw [← h]
      simp only [he, Complex.coe_smul]
    rw [h1, e'.repr_sum_self]
    rfl
  rw [hm]
  exact RingHom.map_det Complex.ofRealHom _

end Skew

theorem real_jacobians :
    (∀ (a b : ℕ) (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) (L : Matrix (Fin a) (Fin b) ℂ →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ), (∀ T, L T = A * T * B) → LinearMap.det L = ‖A.det‖ ^ (2 * b) * ‖B.det‖ ^ (2 * a)) ∧ ∀ (a : ℕ) (A : Matrix (Fin a) (Fin a) ℂ) (L : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ) →ₗ[ℝ] skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)), (∀ T, ((L T : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)) : Matrix (Fin a) (Fin a) ℂ) = A * (T : Matrix (Fin a) (Fin a) ℂ) * Aᴴ) → LinearMap.det L = ‖A.det‖ ^ (2 * a) := by
  refine ⟨fun a b A B L hL => ?_, fun a A L hL => ?_⟩
  · have : L = (twoSided A B).restrictScalars ℝ := LinearMap.ext hL
    rw [this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, det_twoSided,
      Complex.normSq_eq_norm_sq, norm_mul, norm_pow, norm_pow]
    ring
  · have h := det_skew_eq L (twoSided A Aᴴ) hL
    rw [det_twoSided, Matrix.det_conjTranspose, ← mul_pow] at h
    apply Complex.ofReal_injective
    rw [h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    rfl

end GlobalTheory.TwoSidedJac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagSizeDensityLeOne
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DensityIntegral

theorem integral_cube (a : ℕ) (c : Fin a → ℕ) (hc : ∀ i, 1 ≤ c i) :
    ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1), ∏ i, (c i : ℝ) * τ i ^ (c i - 1) = 1 := by
  rw [volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (i : Fin a) (t : ℝ) => (c i : ℝ) * t ^ (c i - 1))]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul, integral_pow]
  obtain ⟨m, hm⟩ : ∃ m, c i = m + 1 := ⟨c i - 1, by have := hc i; omega⟩
  rw [hm]
  simp only [Nat.add_sub_cancel, one_pow, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, sub_zero]
  push_cast
  field_simp

theorem dens_le (n f a : ℕ) (j : Fin a → ℕ) (hf : 1 ≤ f) (hj : ∀ i, 1 ≤ j i) (hn : 2 * ∑ i, j i + 1 ≤ n)
    (τ : Fin a → ℝ) (hτ : τ ∈ simplexH a) :
    FlagMeas.dens n f j τ ≤ ∏ i, ((2 * f * j i : ℕ) : ℝ) * τ i ^ (2 * f * j i - 1) := by
  have h2 := (GlobalTheory.Count.layerProd_count_mul_density_le_two n f (∑ i, j i) a j τ 0 le_rfl (by omega)
    hτ.1 hτ.2 le_rfl (by norm_num)).2
  have h3 : 0 ≤ ∏ i, 2 * (f : ℝ) * j i / τ i :=
    Finset.prod_nonneg fun i _ => by have := (hτ.2 i).1; positivity
  refine (mul_le_mul_of_nonneg_right h2 h3).trans ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => by have := (hτ.2 i).1; positivity) fun i _ => ?_
  obtain ⟨h0, h1⟩ := hτ.2 i
  have hc : 1 ≤ 2 * f * j i := Nat.mul_pos (by omega) (hj i)
  have he : 2 * f * j i ≤ 2 * j i * (n - 2 * ∑ l, j l) * f := by
    calc 2 * f * j i = 2 * j i * 1 * f := by ring
      _ ≤ _ := by gcongr; omega
  have h4 : τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f) ≤ τ i ^ (2 * f * j i - 1) * τ i := by
    rw [← pow_succ]
    exact pow_le_pow_of_le_one h0.le (by linarith) (by omega)
  calc _ ≤ τ i ^ (2 * f * j i - 1) * τ i * (2 * (f : ℝ) * j i / τ i) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = _ := by push_cast; field_simp

theorem lintegral_dens_le_one : ∀ (n f a : ℕ) (j : Fin a → ℕ), 1 ≤ f → (∀ i, 1 ≤ j i) → 2 * ∑ i, j i + 1 ≤ n → ∫⁻ τ in simplexH a, ENNReal.ofReal (dens n f j τ) ≤ 1 := by
  intro n f a j hf hj hn
  set box : Set (Fin a → ℝ) := Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1) with hbox
  have hc : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : simplexH a ⊆ box := fun τ hτ i _ => ⟨(hτ.2 i).1.le, by linarith [(hτ.2 i).2]⟩
  have hm : MeasurableSet (simplexH a) := by
    have : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : i < k, {τ : Fin a → ℝ | τ i < τ k}) ∩
        ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ : Fin a → ℝ | τ i < 1 / 2}) := by
      ext τ
      simp [simplexH, StrictMono]
    rw [this]
    refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k))
      (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
        (measurableSet_lt (measurable_pi_apply i) measurable_const))
  set g : (Fin a → ℝ) → ℝ := fun τ => ∏ i, ((2 * f * j i : ℕ) : ℝ) * τ i ^ (2 * f * j i - 1) with hg
  have hcont : Continuous g := by rw [hg]; fun_prop
  have hint : IntegrableOn g box := hcont.continuousOn.integrableOn_compact hc
  calc _ ≤ ∫⁻ τ in simplexH a, ENNReal.ofReal (g τ) :=
        setLIntegral_mono' hm fun τ hτ => ENNReal.ofReal_le_ofReal (dens_le n f a j hf hj hn τ hτ)
    _ ≤ ∫⁻ τ in box, ENNReal.ofReal (g τ) := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ τ in box, g τ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        refine (ae_restrict_iff' hc.measurableSet).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
        refine Finset.prod_nonneg fun i _ => ?_
        have := (hτ i trivial).1
        positivity
    _ = 1 := by
        rw [integral_cube a (fun i => 2 * f * j i) fun i => Nat.mul_pos (by omega) (hj i), ENNReal.ofReal_one]

end GlobalTheory.DensityIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralRpowNegChangeOfVariable
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem lintegral_rpow_neg_change_of_variable :
    ∀ (N s : ℝ), 0 < N → 0 < s → ∀ F : ℝ → ENNReal, Measurable F →
      ∫⁻ t in Set.Ioi (0 : ℝ), F ((t / s) ^ (-(1 / N))) / ENNReal.ofReal t =
        ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ENNReal.ofReal (N / τ) := by
  intro N s hN hs F _
  set a : ℝ := -(1 / N) with ha_def
  have ha : a ≠ 0 := neg_ne_zero.mpr (one_div_ne_zero hN.ne')

  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => (t / s) ^ a) (1 / s * a * (t / s) ^ (a - 1))
        (Set.Ioi 0) t := by
    intro t ht
    have h1 : HasDerivAt (fun y : ℝ => y / s) (1 / s) t := (hasDerivAt_id' t).div_const s
    exact (h1.rpow_const (Or.inl (div_pos ht hs).ne')).hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => (t / s) ^ a) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hxy' : (x / s) ^ a = (y / s) ^ a := hxy
    have hdiv : x / s = y / s := by
      rw [← Real.rpow_rpow_inv (div_pos hx hs).le ha, ← Real.rpow_rpow_inv (div_pos hy hs).le ha,
        hxy']
    exact (div_left_inj' hs.ne').mp hdiv
  have himage : (fun t : ℝ => (t / s) ^ a) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext τ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.rpow_pos_of_pos (div_pos ht hs) a
    · intro hτ
      refine ⟨s * τ ^ a⁻¹, mul_pos hs (Real.rpow_pos_of_pos hτ _), ?_⟩
      show (s * τ ^ a⁻¹ / s) ^ a = τ
      rw [mul_div_cancel_left₀ _ hs.ne', Real.rpow_inv_rpow (le_of_lt hτ) ha]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun τ => F τ * ENNReal.ofReal (N / τ))
  rw [himage] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht' : 0 < t := ht
  have hu : 0 < t / s := div_pos ht' hs
  have hua : 0 < (t / s) ^ a := Real.rpow_pos_of_pos hu a

  have hreal : |1 / s * a * (t / s) ^ (a - 1)| * (N / (t / s) ^ a) = t⁻¹ := by
    have hneg : 1 / s * a * (t / s) ^ (a - 1) = -(1 / s * (1 / N) * ((t / s) ^ a / (t / s))) := by
      rw [Real.rpow_sub hu, Real.rpow_one, ha_def]
      ring
    have hpos : 0 < 1 / s * (1 / N) * ((t / s) ^ a / (t / s)) :=
      mul_pos (mul_pos (one_div_pos.mpr hs) (one_div_pos.mpr hN)) (div_pos hua hu)
    rw [hneg, abs_neg, abs_of_pos hpos]
    field_simp
  dsimp only
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos ht', ← hreal,
    ENNReal.ofReal_mul (abs_nonneg _)]
  ring

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogUnitarySphereVolumeProductRatioLeLargeRank
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SphRatio

theorem sphV_succ (i : ℕ) :
    sphV (i + 1) = sphV i * (2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) := by
  unfold sphV
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem sphV_pos (i : ℕ) : 0 < sphV i := by
  unfold sphV
  exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity

theorem log_factor_le (n m : ℕ) (a : ℝ) (hn : 18 ≤ n) (ha : a ≤ m) (hm : (n : ℝ) / 2 ≤ m) :
    Real.log (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ)) ≤
      Real.log (2 * Real.pi) - a * Real.log (n / (2 * Real.pi * Real.exp 1)) := by
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  have hn' : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by linarith
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hc : 2 * Real.pi * Real.exp 1 ≤ n := by
    have h1 := Real.pi_lt_d2
    have h2 := Real.exp_one_lt_d9
    nlinarith
  have hL : 0 ≤ Real.log (n / (2 * Real.pi * Real.exp 1)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have h1 : (m : ℝ) ^ m / m.factorial ≤ Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp _ hm0.le m
  have h2 : 2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) ≤
      (2 * Real.pi) * ((n / (2 * Real.pi * Real.exp 1))⁻¹) ^ m := by
    have h3 : Real.pi * Real.exp 1 / m ≤ (n / (2 * Real.pi * Real.exp 1))⁻¹ := by
      rw [inv_div, div_le_div_iff₀ hm0 (by linarith)]
      have : 0 < Real.pi * Real.exp 1 := by positivity
      nlinarith
    calc 2 * Real.pi ^ (m + 1) / (m.factorial : ℝ)
        = (2 * Real.pi) * ((Real.pi / m) ^ m * ((m : ℝ) ^ m / m.factorial)) := by
          rw [div_pow, pow_succ]; field_simp
      _ ≤ (2 * Real.pi) * ((Real.pi / m) ^ m * Real.exp 1 ^ m) := by gcongr
      _ = (2 * Real.pi) * (Real.pi * Real.exp 1 / m) ^ m := by
          rw [← mul_pow]; congr 2; ring
      _ ≤ _ := by gcongr
  refine (Real.log_le_log (by positivity) h2).trans ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv]
  nlinarith

theorem log_ratio_add_le (n q : ℕ) (a : ℝ) (hn : 18 ≤ n) (ha : a ≤ q) (hq : (n : ℝ) / 2 ≤ q)
    (j : ℕ) : Real.log (sphV (q + j) / sphV q) ≤
      j * (Real.log (2 * Real.pi) - a * Real.log (n / (2 * Real.pi * Real.exp 1))) := by
  induction j with
  | zero => simp [(sphV_pos q).ne']
  | succ j ih =>
    have hpi := Real.pi_pos
    have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h := log_factor_le n (q + j) a hn (by push_cast; linarith) (by push_cast; linarith)
    have h1 := sphV_pos (q + j)
    have h2 := sphV_pos q
    rw [← add_assoc, sphV_succ, mul_div_right_comm,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    linarith

theorem log_sphV_ratio_le : ∀ (n p j : ℕ), 18 ≤ n → j ≤ p → p ≤ n → (n : ℝ) - 2 * Real.sqrt n ≤ (p : ℝ) - j → (n : ℝ) / 2 ≤ (p : ℝ) - j → Real.log (sphV p / sphV (p - j)) ≤ j * Real.log (2 * Real.pi) - j * ((n : ℝ) - 2 * Real.sqrt n) * Real.log (n / (2 * Real.pi * Real.exp 1)) := by
  intro n p j hn hj _ ha hq
  have hc : ((p - j : ℕ) : ℝ) = (p : ℝ) - j := Nat.cast_sub hj
  have h := log_ratio_add_le n (p - j) _ hn (hc ▸ ha) (hc ▸ hq) j
  rw [Nat.sub_add_cancel hj] at h
  linarith

end GlobalTheory.SphRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapFnOfEqValC
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ValueSpaceCoordinates

theorem rowAct_mem_delSq {n : ℕ} (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ delSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam := by
  have hanti : Antitone lam.natW := by
    intro i j hij
    have h := lam.anti hij
    simp only [DomWeight.natW]
    exact Int.toNat_le_toNat (by omega)
  have hw := Formalism.L2.Col.dualWeyl_eq_weyl ℂ (le_rfl : n ≤ n) lam.natW hanti
  change p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW at hp
  change Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW
  rw [← hw] at hp ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n lam.natW g p hp

theorem eval_rowAct {n : ℕ} (g x : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : Fin n × Fin n => x v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      MvPolynomial.eval (fun v : Fin n × Fin n => (g * x) v.1 v.2) p := by
  have key : (MvPolynomial.eval fun v : Fin n × Fin n => x v.1 v.2).comp
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).toRingHom =
      MvPolynomial.eval fun v : Fin n × Fin n => (g * x) v.1 v.2 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Formalism.GradedWeylDivisibility.rowAct]
    · intro v
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
  simpa using RingHom.congr_fun key p

theorem eval_ten {ι : Type} [Fintype ι] {n : ℕ} (x : ι → Matrix (Fin n) (Fin n) ℂ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : ι × Fin n × Fin n => x v.1 v.2.1 v.2.2) (ten f) =
      ∏ τ, MvPolynomial.eval (fun v : Fin n × Fin n => x τ v.1 v.2) (f τ) := by
  unfold Formalism.L2.Forms.ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.eval_rename]
  rfl

theorem fnOf_mul_ten {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (A B : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    fnOf G s (A * B) (ten f) =
      (∏ τ, (A τ).det ^ s τ) • fnOf G s B (ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ)) := by
  ext y
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [eval_ten (fun τ => (A * B) τ * y.1 τ) f,
    eval_ten (fun τ => B τ * y.1 τ) (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ))]
  simp only [eval_rowAct, Pi.mul_apply, Matrix.mul_assoc, Matrix.det_mul, mul_zpow,
    Finset.prod_mul_distrib]
  ring

theorem map_fnOf_mul_le {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (A B : ι → Matrix (Fin n) (Fin n) ℂ) :
    (CSpan lam).map (fnOf G s (A * B)) ≤ (CSpan lam).map (fnOf G s B) := by
  unfold CSpan
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨q, ⟨f, hf, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, fnOf_mul_ten]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span
    ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ), fun τ => rowAct_mem_delSq (lam τ) (A τ) (f τ) (hf τ), rfl⟩))

theorem map_fnOf_eq_ValC :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G M : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (M τ).det) → (CSpan lam).map (fnOf G (shiftOf lam) M) = ValC G lam := by
  intro ι _ n lam G M hM
  have hinv : (fun τ => (M τ)⁻¹) * M = 1 := by
    funext τ
    simp only [Pi.mul_apply, Pi.one_apply]
    exact Matrix.nonsing_inv_mul (M τ) (hM τ)
  unfold ValC
  apply le_antisymm
  · have h := map_fnOf_mul_le lam G (shiftOf lam) M 1
    rwa [mul_one] at h
  · have h := map_fnOf_mul_le lam G (shiftOf lam) (fun τ => (M τ)⁻¹) M
    rwa [hinv] at h

end GlobalTheory.ValueSpaceCoordinates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternGroupSubgroupOrderCharacterStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.patternGroup_subgroup_order_character : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ) (Φ : Fin N → Fin N → Prop), (∀ a, ¬ Φ a a) → (∀ a b c, Φ a b → Φ b c → Φ a c) → (∃ H : Subgroup (Gn g N), (∀ x, x ∈ H ↔ InPat Φ (x : Mt g N)) ∧ Nat.card H = g ^ (Finset.univ.filter fun p : Fin N × Fin N => Φ p.1 p.2).card) ∧ (∀ M : Mt g N, InPat Φ M → IsUnit M) ∧ ∀ E : Fin N → Fin N → Prop, (∀ a b c, Φ a b → Φ b c → ¬ E a c) → (∀ a, ¬ E a a) → ∀ M M' : Mt g N, InPat Φ M → InPat Φ M' → sumAt E (M * M') = sumAt E M + sumAt E M' := by
  first | exact @GlobalTheory.GLm.Pattern.pattern_group | exact GlobalTheory.GLm.Pattern.pattern_group | (intros; apply GlobalTheory.GLm.Pattern.pattern_group <;> assumption)
end

