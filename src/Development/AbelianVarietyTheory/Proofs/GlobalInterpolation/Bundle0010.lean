module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LiftInvariantsFinrankEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddHaarMapSmulOfNormEqOneStatement
section
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_smul_addHaar_of_norm_eq_one : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : K), ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ := by
  first | exact @GlobalTheory.addHaar_map_smul_of_norm_eq_one | exact GlobalTheory.addHaar_map_smul_of_norm_eq_one | (intros; apply GlobalTheory.addHaar_map_smul_of_norm_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
section
open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CharConductor

theorem eq_one_of_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterationConvergence.main
  | exact _root_.GlobalTheory.IterationConvergence.main
  | (apply _root_.GlobalTheory.IterationConvergence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IterationConvergence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IterationConvergence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IterationConvergence.main ..)

theorem exists_exponent_of_valued {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | exact _root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | (apply _root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> assumption)
  | (intros; apply _root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CharacterConductorBall.exists_conductor ..)

theorem exists_conductor_exponent : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion
  | exact _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion
  | (apply _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion ..)

end GlobalTheory.CharConductor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory


open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
theorem _root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two (K : Type) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) :
    (NumberField.classNumber K : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
  have hb := _root_.GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  rw [h] at hb
  norm_num at hb
  have hs := _root_.GlobalTheory.one_le_sqrt_abs_discr K
  set s := √|(NumberField.discr K : ℝ)| with hs_def
  have hlog : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hsq : s * s = |(NumberField.discr K : ℝ)| :=
    Real.mul_self_sqrt (abs_nonneg _)
  calc (NumberField.classNumber K : ℝ) ≤ s * (1 + Real.log s) := hb
    _ ≤ s * s := by apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    _ = |(NumberField.discr K : ℝ)| := hsq


open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
theorem _root_.GlobalTheory.classNumber_le_four_mul_abs_discr :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      (NumberField.classNumber K : ℝ) ≤ 4 * |(NumberField.discr K : ℝ)| := by
  intro K _ _ h
  have := _root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K h
  have := abs_nonneg (NumberField.discr K : ℝ)
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoeffMemOfMemMaxPow
section
noncomputable section

open MvPowerSeries IsLocalRing Formalism.BasicNotions.V1

namespace GlobalTheory.PsCNL

section Division

variable {σ : Type} {O : Type} [CommRing O]

end Division

section

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem mem_max_iff (f : MvPowerSeries (Fin a) O) :
    f ∈ maximalIdeal (MvPowerSeries (Fin a) O) ↔ constantCoeff f ∈ maximalIdeal O :=
  _root_.GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff f

theorem ps_isPrecomplete [IsPrecomplete (maximalIdeal O) O] (a : ℕ) :
    IsPrecomplete (maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) :=
  _root_.GlobalTheory.PowerSeriesIdealPowers.main a

end

theorem haus_of_noeth (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    IsHausdorff (maximalIdeal B) B :=
  _root_.GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff B

theorem psCNL : ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : TR O) (n : ℕ),
    ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) C.C)), IsCNL O (MvPowerSeries (Fin n) C.C) ∧
      ∀ x : MvPowerSeries (Fin n) C.C, x ∈ maximalIdeal (MvPowerSeries (Fin n) C.C) ↔
        MvPowerSeries.constantCoeff x ∈ maximalIdeal C.C := by
  intro O _ _ A n
  refine ⟨inferInstance, ?_, fun x => mem_max_iff x⟩
  exact
    { noeth := inferInstance
      complete :=
        { toIsHausdorff := haus_of_noeth _
          toIsPrecomplete := ps_isPrecomplete n }
      localHom := ⟨fun a ha => by
        rw [MvPowerSeries.algebraMap_apply, isUnit_iff_constantCoeff, constantCoeff_C] at ha
        exact isUnit_of_map_unit _ _ ha⟩
      resSurj := by
        intro y
        obtain ⟨f, rfl⟩ := residue_surjective y
        obtain ⟨a, ha⟩ := IsCNL.resSurj (O := O) (A := A.C) (residue A.C (constantCoeff f))
        have ha' : residue A.C (algebraMap O A.C a) = residue A.C (constantCoeff f) := ha
        refine ⟨a, ?_⟩
        show residue _ (algebraMap O (MvPowerSeries (Fin n) A.C) a) = residue _ f
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
          isUnit_iff_constantCoeff, map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C]
        show algebraMap O A.C a - constantCoeff f ∈ maximalIdeal A.C
        rw [← residue_eq_zero_iff, map_sub, ha', sub_self] }

end GlobalTheory.PsCNL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableAtFractInt
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology

namespace GlobalTheory.ZetaHalfPlane

noncomputable def fractInt (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

noncomputable def cutFract : ℝ → ℂ := (Ioi (1 : ℝ)).indicator fun t => ((Int.fract t : ℝ) : ℂ)

lemma norm_fract_le (t : ℝ) : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
  exact (Int.fract_lt_one t).le

lemma norm_cutFract_le (t : ℝ) : ‖cutFract t‖ ≤ 1 :=
  (norm_indicator_le_norm_self _ _).trans (norm_fract_le t)

lemma measurable_fract_ofReal : Measurable fun t : ℝ => ((Int.fract t : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp measurable_fract

lemma measurable_cutFract : Measurable cutFract :=
  measurable_fract_ofReal.indicator measurableSet_Ioi

lemma fractInt_eq_mellin (s : ℂ) : fractInt s = mellin cutFract (-s) := by
  unfold fractInt mellin cutFract
  have h : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • (Ioi (1 : ℝ)).indicator
      (fun t => ((Int.fract t : ℝ) : ℂ)) t = (Ioi (1 : ℝ)).indicator
      (fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul, mul_comm,
        show -s - 1 = -(s + 1) by ring]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

lemma differentiableAt_fractInt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ fractInt s := by
  have h1 : DifferentiableAt ℂ (mellin cutFract) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const (1 : ℝ)).mono measurable_cutFract.aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => by simpa using norm_cutFract_le t
    · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
      simpa using norm_cutFract_le t
    · simpa using hs
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      have : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
      filter_upwards [this] with t ht
      have ht' : t ∉ Ioi (1 : ℝ) := fun h => lt_asymm (mem_Iio.1 ht) (mem_Ioi.1 h)
      rw [cutFract, indicator_of_notMem ht', norm_zero]
      positivity
    · simp
  have h2 : fractInt = fun s => mellin cutFract (-s) := funext fractInt_eq_mellin
  rw [h2]
  exact h1.comp s differentiableAt_id.neg

lemma norm_integrand_le (s : ℂ) {t : ℝ} (ht : t ∈ Ioi (1 : ℝ)) :
    ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-(s.re + 1)) := by
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (by positivity) (norm_fract_le t)

lemma norm_fractInt_le {s : ℂ} (hs : 0 < s.re) : ‖fractInt s‖ ≤ 1 / s.re := by
  have h : -(s.re + 1) < -1 := by linarith
  calc ‖fractInt s‖ ≤ ∫ t in Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt h one_pos) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun t ht => norm_integrand_le s ht
    _ = 1 / s.re := by
        rw [integral_Ioi_rpow_of_lt h one_pos, Real.one_rpow,
          show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]

lemma integrableOn_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have h : (-(s + 1)).re < -1 := by simp; linarith
  exact (integrableOn_Ioi_cpow_of_lt h one_pos).bdd_mul (c := 1)
    measurable_fract_ofReal.aestronglyMeasurable (Eventually.of_forall norm_fract_le)

lemma zeta_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * fractInt s := by
  first
  | exact @_root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract
  | exact _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract
  | (apply _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> assumption)
  | (intros; apply _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract ..)

theorem zeta_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * fractInt s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ riemannZeta₀ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun z => 1 - z * fractInt z) {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      ((differentiableAt_const _).sub
        (differentiableAt_id.mul (differentiableAt_fractInt hz))).differentiableWithinAt) hU
  have key : ∀ z : ℂ, z ≠ 1 → z / (z - 1) = (z - 1)⁻¹ + 1 := by
    intro z hz
    have := sub_ne_zero.2 hz
    field_simp
    ring
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp) (by
      have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      have hz1 : z ≠ 1 := by
        rintro rfl
        simp at hz
      have h1 := zeta_eq_of_one_lt hz
      rw [riemannZeta_eq_inv_sub_add hz1, key z hz1] at h1
      linear_combination h1)
  have h2 : riemannZeta₀ s = 1 - s * fractInt s := heq hs
  rw [riemannZeta_eq_inv_sub_add hs1, key s hs1, h2]
  ring

theorem norm_zeta_sub_le :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s - s / (s - 1)‖ ≤ ‖s‖ / s.re := by
  intro s hs hs1
  rw [zeta_eq hs hs1, sub_sub_cancel_left, norm_neg, norm_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (norm_fractInt_le hs) (norm_nonneg s)

end GlobalTheory.ZetaHalfPlane
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DoubleCosetCount
section
namespace GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation

open GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality

theorem card_fiber_mul_card_stab {G : Type} [Group G] (Γ U K : Subgroup G) (hUK : U ≤ K)
    (hfree : ∀ x : G, stab Γ U x = ⊥) (y : G) :
    Nat.card {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y} * Nat.card (stab Γ K y) =
      U.relIndex K := by
  have hex : ∀ d : {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y},
      ∃ k : K, DoubleCoset.mk Γ U (y * k) = d.1 := by
    rintro ⟨d, hd⟩
    obtain ⟨a, ha, k, hk, h⟩ := (@DoubleCoset.eq _ _ Γ K _ _).1 hd.symm
    refine ⟨⟨k, hk⟩, ?_⟩
    refine Eq.trans ?_ (DoubleCoset.out_eq' (H := Γ) (K := U) d)
    exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨a, ha, 1, U.one_mem, by rw [h]; group⟩
  choose κ hκ using hex
  rw [← Nat.card_prod, Subgroup.relIndex, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ((⟨y⁻¹ * p.2.1 * y, ((mem_stab Γ K y _).1 p.2.2).2⟩ * κ p.1 : K) :
      K ⧸ U.subgroupOf K)) ⟨?_, ?_⟩)
  · rintro ⟨d, s, hs⟩ ⟨e, t, ht⟩ h
    have hs' := ((mem_stab Γ K y _).1 hs).1
    have ht' := ((mem_stab Γ K y _).1 ht).1
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have hde : d = e := by
      apply Subtype.ext
      rw [← hκ d, ← hκ e]
      exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨t⁻¹ * s, Γ.mul_mem (Γ.inv_mem ht') hs', _, h1, by group⟩
    subst hde
    have h2 : s⁻¹ * t ∈ stab Γ U (y * κ d) := by
      refine (mem_stab Γ U _ _).2 ⟨Γ.mul_mem (Γ.inv_mem hs') ht', ?_⟩
      convert h1 using 1
      group
    rw [hfree, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hd : DoubleCoset.mk Γ K (DoubleCoset.mk Γ U (y * k)).out = DoubleCoset.mk Γ K y := by
        obtain ⟨a, ha, u, hu, h⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1
          (DoubleCoset.out_eq' (H := Γ) (K := U) (DoubleCoset.mk Γ U (y * k))).symm
        symm
        exact (@DoubleCoset.eq _ _ Γ K _ _).2
          ⟨a, ha, k * u, K.mul_mem k.2 (hUK hu), h.trans (by group)⟩
      obtain ⟨a, ha, u, hu, h⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1 (hκ ⟨_, hd⟩)
      have hk : y⁻¹ * a * y = k * u⁻¹ * (κ ⟨_, hd⟩ : G)⁻¹ := by
        generalize (κ ⟨_, hd⟩ : G) = m at h ⊢
        rw [show (k : G) = y⁻¹ * (y * k) by group, h]
        group
      have hs : a ∈ stab Γ K y := by
        refine (mem_stab Γ K y _).2 ⟨ha, ?_⟩
        rw [hk]
        exact K.mul_mem (K.mul_mem k.2 (K.inv_mem (hUK hu))) (K.inv_mem (κ _).2)
      refine ⟨⟨⟨_, hd⟩, ⟨a, hs⟩⟩, QuotientGroup.eq.2 ?_⟩
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hk]
      convert hu using 1
      group

theorem doubleCosetCount : DoubleCosetCount := by
  intro G _ Γ U K hUK hfi _ hfin hfree rep hrep
  have hne : U.relIndex K ≠ 0 := hfi.index_ne_zero
  let π : DoubleCoset.Quotient (Γ : Set G) (U : Set G) →
      DoubleCoset.Quotient (Γ : Set G) (K : Set G) := fun d => DoubleCoset.mk Γ K d.out
  have key : ∀ c, Nat.card {d // π d = c} * Nat.card (stab Γ K (rep c)) = U.relIndex K := by
    intro c
    have := card_fiber_mul_card_stab Γ U K hUK hfree (rep c)
    rw [hrep c] at this
    exact this
  have : ∀ c, Finite {d // π d = c} := fun c =>
    Nat.finite_of_card_ne_zero fun h => hne (by rw [← key c, h, zero_mul])
  refine ⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv π), ?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv π), Nat.card_sigma, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hs : (Nat.card (stab Γ K (rep c)) : ℚ) ≠ 0 := by
    have := hfin (rep c)
    exact_mod_cast Nat.card_pos.ne'
  rw [← key c]
  push_cast
  field_simp

end GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EnormSqLeLintegralDisc
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

theorem norm_sq_le_integral_square :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (ρ : ℂ) (r : ℝ), Differentiable ℂ f → 0 < r →
      ‖f ρ‖ ^ 2 ≤ C / r ^ 2 * ∫ σ in (ρ.re - r)..(ρ.re + r), ∫ t in (ρ.im - r)..(ρ.im + r),
        ‖f (σ + t * I)‖ ^ 2 := by
  refine ⟨Real.pi⁻¹, inv_pos.mpr Real.pi_pos, fun f ρ r hf hr => ?_⟩
  set S : Set ℂ := Set.Ioc (ρ.re - r) (ρ.re + r) ×ℂ Set.Ioc (ρ.im - r) (ρ.im + r) with hS
  have hcont : Continuous fun z => ‖f z‖ ^ 2 := hf.continuous.norm.pow 2
  have hSsub : S ⊆ Metric.closedBall ρ (2 * r) := by
    intro z hz
    simp only [hS, Complex.mem_reProdIm, Set.mem_Ioc] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (z - ρ)
    simp only [Complex.sub_re, Complex.sub_im] at h
    have h1 : |z.re - ρ.re| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |z.im - ρ.im| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hint : IntegrableOn (fun z => ‖f z‖ ^ 2) S :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall ρ (2 * r))).mono_set hSsub
  have hball : Metric.ball ρ r ⊆ S := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - ρ)
    have h2 := Complex.abs_im_le_norm (z - ρ)
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
    have a1 := abs_lt.mp (lt_of_le_of_lt h1 hz)
    have a2 := abs_lt.mp (lt_of_le_of_lt h2 hz)
    simp only [hS, Complex.mem_reProdIm, Set.mem_Ioc]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hv := volume_ball_complex ρ hr
  simp only [Module.finrank_self, pow_one, mul_one, Nat.factorial_one, Nat.cast_one,
    div_one] at hv
  have hvr : volume.real (Metric.ball ρ r) = Real.pi * r ^ 2 := by
    rw [measureReal_def, hv, ENNReal.toReal_ofReal (by positivity)]
  have key := norm_pow_le_inv_measure_mul_integral_ball volume (a := ρ) hr hf.differentiableOn 2
    (integrableOn_norm_pow_ball volume (a := ρ) hf.continuous.continuousOn 2)
  rw [hvr] at key
  have hmono : ∫ z in Metric.ball ρ r, ‖f z‖ ^ 2 ≤ ∫ z in S, ‖f z‖ ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun z => by positivity)
      (Filter.Eventually.of_forall hball)
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' S =
      Set.Ioc (ρ.re - r) (ρ.re + r) ×ˢ Set.Ioc (ρ.im - r) (ρ.im + r) := by
    ext p
    simp [hS, Complex.measurableEquivRealProd_symm_apply, Complex.mem_reProdIm]
  have hint' := (hp.integrableOn_comp_preimage he).mpr hint
  rw [hpre, Measure.volume_eq_prod] at hint'
  have hiter : ∫ z in S, ‖f z‖ ^ 2 = ∫ σ in (ρ.re - r)..(ρ.re + r),
      ∫ t in (ρ.im - r)..(ρ.im + r), ‖f (σ + t * I)‖ ^ 2 := by
    rw [← hp.setIntegral_preimage_emb he (fun z => ‖f z‖ ^ 2) S, hpre, Measure.volume_eq_prod,
      setIntegral_prod (fun x => ‖f (Complex.measurableEquivRealProd.symm x)‖ ^ 2) hint', intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_congr_fun measurableSet_Ioc fun σ _ => ?_
    rw [intervalIntegral.integral_of_le (by linarith)]
    simp [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]
  calc ‖f ρ‖ ^ 2 ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in Metric.ball ρ r, ‖f z‖ ^ 2 := key
    _ ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in S, ‖f z‖ ^ 2 := by gcongr
    _ = _ := by rw [hiter, mul_inv, div_eq_mul_inv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImageStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)), (∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) → ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧ LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) = f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  first | exact @GlobalTheory.linearEquiv_descends_of_preserves_image | exact GlobalTheory.linearEquiv_descends_of_preserves_image | (intros; apply GlobalTheory.linearEquiv_descends_of_preserves_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralTsumOrbitUnfoldStatement
section
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_tsum_orbit_unfold_alt : ∀ (G G' V X : Type) [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul G'] [MulAction G V] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (μ' : Measure G') [SFinite μ'] [μ'.IsMulLeftInvariant] (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ'] (𝓕 : Set G) (𝓕' : Set G'), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ' 𝓕' μ' → ∀ (φ : G' →* G), Measurable φ → Function.Injective φ → (∀ g, φ g ∈ Γ ↔ g ∈ Γ') → ∀ (x : V), φ.range = MulAction.stabilizer G x → ∀ (c : X → V), Function.Injective c → (∀ y, y ∈ Set.range c ↔ ∃ γ ∈ Γ, γ • x = y) → ∀ (u : G → ℝ≥0∞), Measurable u → ∀ (Φ : V → ℝ≥0∞), (∀ h : G, Φ (h⁻¹ • x) = ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ') → ∫⁻ h in 𝓕, ∑' i, Φ (h⁻¹ • c i) ∂μ = μ' 𝓕' * ∫⁻ h, u h ∂μ := by
  first | exact @GlobalTheory.lintegral_tsum_orbit_unfold | exact GlobalTheory.lintegral_tsum_orbit_unfold | (intros; apply GlobalTheory.lintegral_tsum_orbit_unfold <;> assumption)
end

