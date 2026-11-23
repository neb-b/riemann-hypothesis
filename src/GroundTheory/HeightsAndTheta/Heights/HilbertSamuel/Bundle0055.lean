module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUniformBergmanBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights

noncomputable section

lemma gaussDiscMass_pos {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 < R) : 0 < gaussDiscMass lam R := by
  unfold gaussDiscMass
  split_ifs with h
  · positivity
  · have hl : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h)
    have : Real.exp (-lam * R ^ 2) < 1 :=
      (Real.exp_lt_exp.2 (by nlinarith [sq_pos_of_pos hR] : -lam * R ^ 2 < 0)).trans_eq Real.exp_zero
    have : 0 < 1 - Real.exp (-lam * R ^ 2) := by linarith
    positivity

theorem UniformBergmanBound.proof (hP : PolydiscSubmean.Statement)
    (hC : ChartTaylorCover.Statement) : UniformBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV _ _
  obtain ⟨r, hr, M, c, hc, hcov⟩ := hC A L W₀ W₁ dV
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hI : 0 < gaussDiscMass M' r := gaussDiscMass_pos hM'0 hr
  have hK : 0 < c * gaussDiscMass M' r ^ D := by positivity
  refine ⟨(c * gaussDiscMass M' r ^ D)⁻¹, fun n hn t ht V _ hV x => ?_⟩
  have hn0 : 0 < n := hn
  have hnD : 0 < (n : ℝ) ^ D := by positivity
  obtain ⟨j, hxj, hball, hdens, hW⟩ := hcov x
  obtain ⟨ℓ₀, h₀⟩ := hW W₀ (by simp)
  obtain ⟨ℓ₁, h₁⟩ := hW W₁ (by simp)
  set e := A.chart j
  set y := e x
  set ψ : (Fin D → ℂ) → ℝ := (W₀.lerp W₁ t).φ j ∘ e.symm with hψ
  have hψy : ψ y = (W₀.lerp W₁ t).φ j x := by simp [hψ, y, e.left_inv hxj]
  have hsub : Metric.closedBall y r ⊆ e.target ∩ e.symm ⁻¹' e.source :=
    fun w hw => ⟨hball hw, e.map_target (hball hw)⟩

  have hT : ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
      ψ (y + z) ≤ ψ y + (ℓ₀ + t • (ℓ₁ - ℓ₀)) z + M' * ∑ i, ‖z i‖ ^ 2 := by
    intro z hz
    have a₀ := h₀ z hz
    have a₁ := h₁ z hz
    have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by positivity
    have hMM : M * ∑ i, ‖z i‖ ^ 2 ≤ M' * ∑ i, ‖z i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS
    rw [hψy]
    simp only [hψ, Function.comp, Weight.lerp, FunLike.coe_add,
      FunLike.coe_smul, FunLike.coe_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    nlinarith [mul_le_mul_of_nonneg_left a₀ ht1, mul_le_mul_of_nonneg_left a₁ ht0]

  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV s.2
  have hs' : _ ∧ _ ∧ _ := hs
  set F : (Fin D → ℂ) → ℂ := (s : Fin A.n → X → ℂ) j ∘ e.symm with hF
  have hFa : AnalyticOnNhd ℂ F (Metric.closedBall y r) := ((hs'.1 j) j).mono hsub
  have hψc : ContinuousOn ψ (Metric.closedBall y r) :=
    (((W₀.lerp W₁ t).smooth j) j).continuousOn.mono hsub
  have hloc := gauss_local hP hn0 hr hM'0 hFa hψc (ℓ₀ + t • (ℓ₁ - ℓ₀)) hT
  have hρr : r / Real.sqrt n ≤ r := div_le_self hr.le (Real.one_le_sqrt.2 (by exact_mod_cast hn))
  have hBr : Metric.closedBall y (r / Real.sqrt n) ⊆ Metric.closedBall y r :=
    Metric.closedBall_subset_closedBall hρr
  have hlow := le_l2NormSq_of_chart (W₀.lerp W₁ t) dV hs j
    Metric.isClosed_closedBall.measurableSet (hBr.trans hball) hc.le
    (fun w hw => hdens w (hBr hw))
  have hpt : ptNormSq (W₀.lerp W₁ t) n s x = ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) := by
    rw [ptNormSq_eq_of_mem _ hs j hxj, hψy]
    simp [hF, y, e.left_inv hxj]
  have hmain : ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c ≤
      sectionL2NormSq (W₀.lerp W₁ t) dV n s := by
    rw [hpt]
    calc _ = c * (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ *
          gaussDiscMass M' r ^ D) := by ring
      _ ≤ c * ∫ w in Metric.closedBall y (r / Real.sqrt n), ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) :=
          mul_le_mul_of_nonneg_left hloc hc.le
      _ = _ := rfl
      _ ≤ _ := hlow
  have hl0 : 0 ≤ sectionL2NormSq (W₀.lerp W₁ t) dV n s := sectionL2NormSq_nonneg _ _ _ _
  rcases hl0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; positivity
  rw [div_le_iff₀ hpos]
  have hp0 : 0 ≤ ptNormSq (W₀.lerp W₁ t) n s x := ptNormSq_nonneg _ _ _ _
  calc ptNormSq (W₀.lerp W₁ t) n s x
      = (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D *
          (ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c) := by
        field_simp
    _ ≤ (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D * sectionL2NormSq (W₀.lerp W₁ t) dV n s :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter fwdDiff
open scoped Pointwise

noncomputable section

namespace VeroneseGenDeg

theorem finrank_homog (D n : ℕ) :
    Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ n) = (n + D).choose D := by
  have hs : {d : Fin (D + 1) →₀ ℕ | d.degree = n} =
      ((Finset.univ.finsuppAntidiag n : Finset (Fin (D + 1) →₀ ℕ)) : Set (Fin (D + 1) →₀ ℕ)) := by
    ext d; simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, hs,
    (AddMonoidAlgebra.supportedEquivFinsupp _).finrank_eq, Module.finrank_finsupp_self]
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]
  rw [show D + 1 + n - 1 = n + D by omega]
  exact Nat.choose_symm_add

theorem range_alt (D : ℕ) : Set.range (Veronese.x D) = Set.range (Veronese.t D) ^ 2 := by
  ext y
  rw [pow_two, Set.mem_mul]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    rcases le_total i j with hij | hij
    · exact ⟨⟨(), ⟨(i, j), hij⟩⟩, rfl⟩
    · exact ⟨⟨(), ⟨(j, i), hij⟩⟩, mul_comm _ _⟩

theorem aeval_t_injective (D : ℕ) :
    Function.Injective (aeval (Veronese.t D) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Veronese.Fld D) := by
  have h : (aeval (Veronese.t D) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Veronese.Fld D).toRingHom =
      (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
        (MvPolynomial.map (Int.castRingHom ℚ)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp
    · simp [Veronese.t]
  have hinj : Function.Injective ((algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) :=
    (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
      (MvPolynomial.map_injective _ (RingHom.injective_int _))
  rw [← h] at hinj
  exact hinj

theorem finrank_sec (D n : ℕ) :
    Module.finrank ℤ (sec ℤ (Veronese.x D) n) = (2 * n + D).choose D := by
  have h1 : sec ℤ (Veronese.x D) n = sec ℤ (Veronese.t D) (2 * n) := by
    rw [SectionsRank.sec_eq_span, SectionsRank.sec_eq_span, range_alt, ← pow_mul]
  rw [h1, ← finrank_homog D (2 * n)]
  exact (Submodule.equivMapOfInjective _ (aeval_t_injective D) _).finrank_eq.symm

theorem mixedDiff_const {K : Type*} (D : ℕ) (b : K → ℤ) (h : (K → ℤ) → ℤ) :
    GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff (fun _ : Fin D => b) h =
      (GroundTheory.Heights₂.Heights.NumbersDVR.diffStep b)^[D] h := by
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff
  rw [List.ofFn_const]
  induction D with
  | zero => rfl
  | succ D ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

theorem iterate_diffStep (D : ℕ) (H : (Unit → ℤ) → ℤ) (k : ℤ) :
    (GroundTheory.Heights₂.Heights.NumbersDVR.diffStep 1)^[D] H (fun _ => k) =
      (fwdDiff (1 : ℤ))^[D] (fun j : ℤ => H (fun _ => j)) (k - D) := by
  induction D generalizing H with
  | zero => simp
  | succ D ih =>
    rw [Function.iterate_succ_apply, ih]
    have hg : (fun j : ℤ => GroundTheory.Heights₂.Heights.NumbersDVR.diffStep 1 H (fun _ => j)) =
        fun j : ℤ => fwdDiff 1 (fun j : ℤ => H (fun _ => j)) (j + -1) := by
      funext j
      have e1 : (fun _ : Unit => j + -1 + 1) = fun _ => j := by funext u; ring
      have e2 : ((fun _ : Unit => j) - 1) = fun _ => j + -1 := by funext u; simp; ring
      simp only [GroundTheory.Heights₂.Heights.NumbersDVR.diffStep, fwdDiff, e1, e2]
    rw [hg, fwdDiff_iter_comp_add, ← Function.iterate_succ_apply,
      show k - (D : ℤ) + -1 = k - ((D + 1 : ℕ) : ℤ) by push_cast; ring]

def hilbPoly (D : ℕ) : Polynomial ℚ :=
  (Polynomial.preHilbertPoly ℚ D 0).comp (Polynomial.C 2 * Polynomial.X)

theorem hilbPoly_eval (D n : ℕ) : (hilbPoly D).eval (n : ℚ) = ((2 * n + D).choose D : ℚ) := by
  rw [hilbPoly, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have := Polynomial.preHilbertPoly_eq_choose_sub_add ℚ D (k := 0) (n := 2 * n) (Nat.zero_le _)
  push_cast at this
  rw [this, Nat.sub_zero]

theorem fwdDiff_hilbPoly (D : ℕ) (y : ℚ) : (fwdDiff (1 : ℚ))^[D] (hilbPoly D).eval y = 2 ^ D := by
  have hdeg : (hilbPoly D).natDegree = D := by
    rw [hilbPoly, Polynomial.natDegree_comp, Polynomial.natDegree_preHilbertPoly,
      Polynomial.natDegree_C_mul_X _ two_ne_zero, mul_one]
  have hlc : (hilbPoly D).leadingCoeff = (D.factorial : ℚ)⁻¹ * 2 ^ D := by
    rw [hilbPoly, Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_C_mul_X _ two_ne_zero]; exact one_ne_zero),
      Polynomial.leadingCoeff_preHilbertPoly, Polynomial.leadingCoeff_C_mul_X,
      Polynomial.natDegree_preHilbertPoly]
  have h := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial (hilbPoly D)) y
  rw [hdeg, hlc] at h
  rw [h]
  have hf : (D.factorial : ℚ) ≠ 0 := by positivity
  simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
  field_simp

theorem eventualValue_eq {K : Type*} (F : (K → ℤ) → ℤ) (c : ℤ)
    (h : ∀ᶠ m in atTop, F m = c) : GroundTheory.Heights₂.Heights.NumbersDVR.eventualValue F = c := by
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.eventualValue
  have hex : ∃ c, ∀ᶠ m in atTop, F m = c := ⟨c, h⟩
  rw [dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and h).exists
  rw [← h1, h2]

end VeroneseGenDeg


open VeroneseGenDeg in
theorem VeroneseGenDeg.proof : VeroneseGenDeg.Statement := by
  intro D _
  set q := (coordIdeal ℤ (Veronese.x D)).map (MvPolynomial.map (Int.castRingHom ℚ)) with hq
  set g : ℤ → ℤ := fun j => GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Veronese.Idx D)) q (fun _ => j)
    with hgdef

  have hg : ∀ j : ℤ, 0 ≤ j → (g j : ℚ) = (hilbPoly D).eval (j : ℚ) := by
    intro j hj
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    have h := SectionsRank.proof (Veronese.Fld D) (Veronese.Idx D) (Veronese.x D) n
    rw [finrank_sec] at h
    simp only [hgdef]
    rw [← hq] at h
    rw [h, Int.cast_natCast, Int.cast_natCast, hilbPoly_eval]
  have hev : ∀ᶠ m in atTop, GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff (fun _ : Fin D => (1 : Unit → ℤ))
      (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Veronese.Idx D)) q) m = 2 ^ D := by
    filter_upwards [eventually_ge_atTop (fun _ : Unit => (D : ℤ))] with m hm
    have hm' : m = fun _ => m () := funext fun u => rfl
    have hD : (D : ℤ) ≤ m () := hm ()
    rw [mixedDiff_const, hm', iterate_diffStep]
    have key : (((fwdDiff (1 : ℤ))^[D] g (m () - D) : ℤ) : ℚ) = 2 ^ D := by
      rw [← fwdDiff_hilbPoly D ((m () - D : ℤ) : ℚ), fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [nsmul_eq_mul, mul_one, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rw [hg _ (by omega)]
      push_cast
      ring
    exact_mod_cast key
  unfold genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum
  apply eventualValue_eq
  convert hev

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseSemipos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Topology

noncomputable section

theorem leviForm_comp_clm {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (L : (J → ℂ) →L[ℝ] (J → ℂ))
    (hL : ∀ w, L (Complex.I • w) = Complex.I • L w) (z : J → ℂ)
    (hφ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ φ (L y))
    (hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) (L z)) (w : J → ℂ) :
    leviForm (φ ∘ L) z w = leviForm φ (L z) (L w) := by
  set R := (ContinuousLinearMap.compL ℝ (J → ℂ) (J → ℂ) ℝ).flip L with hR
  have hev : fderiv ℝ (φ ∘ L) =ᶠ[𝓝 z] fun y => R (fderiv ℝ φ (L y)) := by
    filter_upwards [hφ] with y hy
    rw [fderiv_comp y hy L.differentiableAt, L.fderiv]
    rfl
  have hd : HasFDerivAt (fun y => R (fderiv ℝ φ (L y))) (R.comp ((fderiv ℝ (fderiv ℝ φ) (L z)).comp L)) z :=
    R.hasFDerivAt.comp z (hφ2.hasFDerivAt.comp z L.hasFDerivAt)
  have key : ∀ v, fderiv ℝ (fderiv ℝ (φ ∘ L)) z v v = fderiv ℝ (fderiv ℝ φ) (L z) (L v) (L v) := by
    intro v
    rw [hev.fderiv_eq, hd.fderiv]
    rfl
  unfold leviForm
  rw [key, key, hL]

theorem contDiffAt_log_fs {J : Type} [Fintype J] {y : J → ℂ} (hy : y ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.log ((fsMetric (ι := J)).ρ y)) y :=
  ((ProjLine.isSmoothMetric_fs (J := J) y hy).contDiffAt (isOpen_ne.mem_nhds hy)).log
    ((fsMetric (ι := J)).pos y hy).ne'

namespace Veronese

def scaleLin (D : ℕ) : (Ix (Idx D) → ℂ) →ₗ[ℂ] (Ix (Idx D) → ℂ) where
  toFun := scale D
  map_add' z z' := by
    funext q
    simp only [scale, Pi.add_apply]
    ring
  map_smul' c z := by
    funext q
    simp only [scale, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def scaleL (D : ℕ) : (Ix (Idx D) → ℂ) →L[ℝ] (Ix (Idx D) → ℂ) :=
  (LinearMap.toContinuousLinearMap (scaleLin D)).restrictScalars ℝ

theorem scaleL_I (D : ℕ) (w : Ix (Idx D) → ℂ) : scaleL D (Complex.I • w) = Complex.I • scaleL D w :=
  (scaleLin D).map_smul Complex.I w

end Veronese

open Veronese

theorem VeroneseSemipos.proof : VeroneseSemipos.Statement := by
  intro D
  refine ⟨(isSmoothMetric_metric D).mono fun z hz h0 => ?_, fun z hz w _ => ?_⟩
  · obtain ⟨i, hi⟩ := hz ()
    exact hi (congrFun h0 _)
  · have hz0 : z ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := hz.1 ()
      exact hi (congrFun h0 _)
    have e : (fun z => Real.log ((HermLine.ofCone (metric D)).h z)) =
        (fun y => Real.log ((fsMetric (ι := Ix (Idx D))).ρ y)) ∘ scaleL D := rfl
    have hφ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ (fun y => Real.log ((fsMetric (ι := Ix (Idx D))).ρ y)) (scaleL D y) := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
      exact (contDiffAt_log_fs (scale_ne_zero hy)).differentiableAt (by simp)
    have hφ2 : DifferentiableAt ℝ (fderiv ℝ fun y => Real.log ((fsMetric (ι := Ix (Idx D))).ρ y)) (scaleL D z) :=
      ((contDiffAt_log_fs (scale_ne_zero hz0)).fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt
        one_ne_zero
    rw [e, leviForm_comp_clm _ _ (scaleL_I D) z hφ hφ2 w]
    exact ProjLine.leviForm_log_fs_nonneg (scale_ne_zero hz0) (scaleL D w)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResChiIndexLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiIndex

noncomputable section

open Module

variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem basis_det_eq {N : Type*} [AddCommGroup N] [Module ℤ N] {r : ℕ} (b : Basis (Fin r) ℤ N)
    (A : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → N) (hv : ∀ k, v k = ∑ l, A k l • b l) : b.det v = A.det := by
  classical
  rw [Basis.det_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.transpose_apply, Basis.toMatrix_apply, hv i, map_sum]
  simp only [map_zsmul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem log_relIndex_sub {r : ℕ} {e e' : Fin r → Ω} (he : LinearIndependent ℤ e) (he' : LinearIndependent ℤ e')
    (T : Matrix (Fin r) (Fin r) ℚ) (hT : ∀ k, e' k = ∑ l, (T k l : Ω) * e l) (hdet : T.det ≠ 0) :
    Real.log ((Submodule.span ℤ (Set.range e)).toAddSubgroup.relIndex
        (Submodule.span ℤ (Set.range e')).toAddSubgroup) -
      Real.log ((Submodule.span ℤ (Set.range e')).toAddSubgroup.relIndex
        (Submodule.span ℤ (Set.range e)).toAddSubgroup) =
      -Real.log |(T.det : ℝ)| := by
  classical
  obtain ⟨c, hc0, hc⟩ := ChangeOfLattice.exists_clear_den T
  choose A hA using hc
  set L := Submodule.span ℤ (Set.range e) with hLdef
  set L' := Submodule.span ℤ (Set.range e') with hL'def
  set f : Fin r → Ω := fun k => (c : Ω) * e' k with hfdef
  have hAΩ : ∀ k l, (c : Ω) * (T k l : Ω) = (A k l : Ω) := fun k l => by
    have h := congrArg (fun q : ℚ => (q : Ω)) (hA k l)
    push_cast at h
    exact h
  have hf : ∀ k, f k = ∑ l, A k l • e l := by
    intro k
    simp only [hfdef, hT k, Finset.mul_sum, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, hAΩ]
  have hc0' : (c : Ω) ≠ 0 := by exact_mod_cast hc0
  have hfli : LinearIndependent ℤ f := ChangeOfLattice.linearIndependent_const_mul hc0' he'
  have hfc : ∀ k, f k = ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l • e' l := by
    intro k
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp [hfdef, zsmul_eq_mul]
  set M := Submodule.span ℤ (Set.range f) with hMdef
  have hML : M ≤ L := Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by
    rw [hf k]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hML' : M ≤ L' := Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by
    rw [hfc k]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hML₀ : M.toAddSubgroup ≤ L.toAddSubgroup := hML
  have hML'₀ : M.toAddSubgroup ≤ L'.toAddSubgroup := hML'

  have i1 : M.toAddSubgroup.relIndex L'.toAddSubgroup = (c ^ r : ℕ) := by
    rw [AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L'.toAddSubgroup hML'₀ (Basis.span hfli)
      (Basis.span he')]
    refine (congrArg Int.natAbs (basis_det_eq _ ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) _ ?_)).trans ?_
    · intro k
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [AddSubgroupClass.coe_zsmul]
      show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) =
        ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l •
          ((Basis.span he' l : Submodule.span ℤ (Set.range e')) : Ω)
      simp only [Basis.coe_span_apply]
      exact hfc k
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, Int.natAbs_pow, Int.natAbs_natCast]
  have i2 : M.toAddSubgroup.relIndex L.toAddSubgroup = (Matrix.of A).det.natAbs := by
    rw [AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L.toAddSubgroup hML₀ (Basis.span hfli)
      (Basis.span he)]
    refine congrArg Int.natAbs (basis_det_eq _ (Matrix.of A) _ fun k => ?_)
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [AddSubgroupClass.coe_zsmul, Matrix.of_apply]
    show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) =
      ∑ l, A k l • ((Basis.span he l : Submodule.span ℤ (Set.range e)) : Ω)
    simp only [Basis.coe_span_apply]
    exact hf k
  have hAdet : (((Matrix.of A).det : ℤ) : ℝ) = (c : ℝ) ^ r * (T.det : ℝ) := by
    have hmap : (Int.castRingHom ℚ).mapMatrix (Matrix.of A) = (c : ℚ) • T := by
      ext i j
      simp [← hA i j]
    have h1 : (((Matrix.of A).det : ℤ) : ℚ) = (c : ℚ) ^ r * T.det := by
      rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det, hmap, Matrix.det_smul, Fintype.card_fin]
    rw [← Rat.cast_intCast, h1, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
  have hcr : (c : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc0)
  have hTr : (T.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have h1 : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [i2]
    intro h0
    have : (((Matrix.of A).det : ℤ) : ℝ) = 0 := by
      rw [Int.natAbs_eq_zero.1 h0, Int.cast_zero]
    rw [hAdet] at this
    exact mul_ne_zero hcr hTr this
  have h2 : M.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0 := by
    rw [i1]
    exact pow_ne_zero _ hc0
  rw [ChangeOfLattice.log_relIndex_cocycle hML₀ hML'₀ h1 h2, i1, i2, Nat.cast_natAbs, Int.cast_abs, hAdet, Nat.cast_pow]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ r), Real.log_mul hcr (abs_ne_zero.2 hTr)]
  ring

end

end ResChiIndex

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

