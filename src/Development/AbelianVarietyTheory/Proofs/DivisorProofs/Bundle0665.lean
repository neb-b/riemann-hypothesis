module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRemainderIsBigOAndTaylorFlat
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_eq_partialSum {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) {f : (I → ℂ) → ℂ}
    {p : FormalMultilinearSeries ℂ (I → ℂ) ℂ} (hp : HasFPowerSeriesAt f p 0) (z : I → ℂ) :
    taylor N z f = p.partialSum (N + 1) z := by
  obtain ⟨r, hr⟩ := hp
  unfold taylor FormalMultilinearSeries.partialSum
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h1 := hr.factorial_smul z k
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (iteratedFDeriv ℂ k f 0 fun _ ↦ z) =
      ∑ s : Fin k → I, (∏ a, z (s a)) • iteratedFDeriv ℂ k f 0 fun a ↦ Pi.single (s a) 1 := by
    have hz : (fun _ : Fin k ↦ z) = fun _ ↦ ∑ i, z i • (Pi.single i (1 : ℂ) : I → ℂ) := by
      funext a j
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  rw [h2, nsmul_eq_mul] at h1
  rw [← inv_mul_cancel_left₀ hk (p k fun _ ↦ z), h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [smul_eq_mul]
  ring

theorem diag_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ) {f : E → ℂ}
    {p : FormalMultilinearSeries ℂ E ℂ} (hp : HasFPowerSeriesAt f p 0)
    (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) (k : ℕ) : k ≤ N → ∀ y, (p k fun _ ↦ y) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h1 := hp.isBigO_sub_partialSum_pow (k + 1)
    have hs : ∀ y, p.partialSum (k + 1) y = p k fun _ ↦ y := by
      intro y
      rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
        Finset.sum_eq_zero fun j hj ↦ ih j (Finset.mem_range.1 hj)
          (le_trans (Finset.mem_range.1 hj).le hk) y, zero_add]
    have h2 : (fun z : E ↦ ‖z‖ ^ (N + 1)) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with z hz
      rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_of_le_one (norm_nonneg _) (by simpa using hz) (by omega)
    have h3 : (fun y : E ↦ p k fun _ ↦ y) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine ((hf.trans h2).sub h1).congr_left fun y ↦ ?_
      simp [hs]
    exact h3.continuousMultilinearMap_apply_eq_zero

theorem iteratedFDeriv_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ)
    {f : E → ℂ} (ha : AnalyticAt ℂ f 0) (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) {k : ℕ} (hk : k ≤ N)
    (v : Fin k → E) : iteratedFDeriv ℂ k f 0 v = 0 := by
  obtain ⟨p, hp⟩ := ha
  have h := diag_eq_zero_of_isBigO N hp hf k hk
  obtain ⟨r, hr⟩ := hp
  rw [hr.iteratedFDeriv_eq_sum_of_completeSpace, ← (p k).iteratedFDeriv_comp_diagonal 0 v]
  simp [h]

theorem taylor_remainder_and_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  intro I _ _ N f ha
  refine ⟨?_, fun hf D _ _ t ↦ ?_⟩
  · obtain ⟨p, hp⟩ := ha
    refine (hp.isBigO_sub_partialSum_pow (N + 1)).congr_left fun z ↦ ?_
    rw [taylor_eq_partialSum N hp, zero_add]
  · unfold taylor
    refine Finset.sum_eq_zero fun k hk ↦ Finset.sum_eq_zero fun s _ ↦ ?_
    rw [iteratedFDeriv_eq_zero_of_isBigO N ha hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), mul_zero,
      zero_smul]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
section
open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory


open Filter Topology in
open Filter Topology TopologicalSpace TensorProduct in
theorem _root_.GlobalTheory.tensor_hol_ext_of_values :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (D : Type) [CommRing D] [Algebra ℂ D] (x y : D ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol W), (∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x = Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) y) → x = y := by
  intro E _ _ W D _ _ x y h
  classical
  rw [← sub_eq_zero]
  set z := x - y with hz
  have hzp : ∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D)
      ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp))
      (fun _ _ ↦ Commute.all _ _) z = 0 := fun p hp => by
    rw [hz, map_sub, h p hp, sub_self]
  let b := Module.Free.chooseBasis ℂ D
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := _root_.GlobalTheory.AnPer.Hol W) b
  have hc : ∀ i, e z i = 0 := by
    intro i
    apply _root_.GlobalTheory.AnPer.Hol.ext_fn
    intro p hp
    have hzero : (0 : _root_.GlobalTheory.AnPer.Hol W).fn p = 0 := by
      rw [← _root_.GlobalTheory.AnPer.Hol.ev_apply p hp, map_zero]
    have h0 := hzp p hp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.symm_apply_apply z, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum,
      map_sum] at h0
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
      _root_.GlobalTheory.AnPer.Hol.ev_apply, Algebra.ofId_apply] at h0
    have h1 : ∑ j ∈ (e z).support, (e z j).fn p • b j = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    by_cases hi : i ∈ (e z).support
    · rw [linearIndependent_iff'.1 b.linearIndependent (e z).support (fun j => (e z j).fn p) h1 i hi,
        hzero]
    · rw [Finsupp.notMem_support_iff.1 hi]
  exact e.injective (by rw [map_zero]; exact Finsupp.ext hc)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
section
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom
variable {F : Type} [Field F] [NumberField F]


open Classical in
def cls (I : Ideal (𝓞 F)) : ClassGroup (𝓞 F) := if h : I ∈ (Ideal (𝓞 F))⁰ then ClassGroup.mk0 ⟨I, h⟩ else 1


open Classical in
def wideInd (C : ClassGroup (𝓞 F)) : Ideal (𝓞 F) → ℚ := fun I => if cls I = C then 1 else 0

theorem cls_of_ne_bot {I : Ideal (𝓞 F)} (h : I ≠ ⊥) :
    cls I = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero h⟩ := by
  rw [cls, dite_eq_left]

theorem cls_mul {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : cls (I * J) = cls I * cls J := by
  rw [cls_of_ne_bot hI, cls_of_ne_bot hJ, cls_of_ne_bot (mul_ne_zero hI hJ), ← map_mul]
  rfl

theorem cls_span {a : 𝓞 F} (ha : a ≠ 0) : cls (Ideal.span {a}) = 1 := by
  have h : Ideal.span {a} ≠ ⊥ := by simpa using ha
  rw [cls_of_ne_bot h, ClassGroup.mk0_eq_one_iff]
  exact ⟨⟨a, rfl⟩⟩

theorem cls_span_mul {a : 𝓞 F} (ha : a ≠ 0) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : cls (Ideal.span {a} * I) = cls I := by
  rw [cls_mul (by simpa using ha) hI, cls_span ha, one_mul]

theorem isRayFun_wideInd (𝔣 : Ideal (𝓞 F)) (C : ClassGroup (𝓞 F)) : IsRayFun 𝔣 (wideInd C) := by
  intro I J hI hJ e
  obtain ⟨a, b, ha, hb, -, -, -, e⟩ := e
  have : cls I = cls J := by rw [← cls_span_mul ha hI.1, e, cls_span_mul hb hJ.1]
  unfold wideInd
  rw [this]

theorem translate_wideInd {a : 𝓞 F} (ha : a ≠ 0) (C : ClassGroup (𝓞 F)) :
    GlobalTheory.RayZeta.translate (Ideal.span {a}) (wideInd C) = wideInd C := by
  funext I
  by_cases hI : I = ⊥
  · simp [GlobalTheory.RayZeta.translate, hI]
  · simp only [GlobalTheory.RayZeta.translate, wideInd]
    rw [cls_span_mul ha hI]

end GlobalTheory.ZetaDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEstimateLhsTransfer
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lhs_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ T : ℝ) (θ : ℝ → ℝ) (F0 : U → ℂ), Continuous θ → Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - β i x * GlobalTheory.OTY.TwEst.ext0 U F0 x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖(θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x - F0 x‖ ^ 2 * (wT T (δ * psi A L s x) * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x)))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hqm hpsi δ T θ F0 hθ hF0
  have hm : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hwc : Continuous (wT T) := by
    unfold wT
    refine continuous_const.div₀ (by fun_prop) fun x => ?_
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    linarith
  have hw0 : ∀ x, 0 ≤ wT T x := by
    intro x
    unfold wT
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    positivity
  have key := htr (fun y => (θ (δ * psi A L s y) : ℂ) *
      GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y - GlobalTheory.OTY.TwEst.ext0 U F0 y)
    (fun y => wT T (δ * psi A L s y) * Real.exp (-psi A L s y))
    (((Complex.measurable_ofReal.comp (hθ.measurable.comp hm)).mul hqm).sub hF0)
    ((hwc.measurable.comp hm).mul (Real.measurable_exp.comp hpsi.neg))
    (fun y _ => mul_nonneg (hw0 _) (Real.exp_pos _).le)
  refine Eq.trans ?_ (key.trans ?_)
  · refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
    have h1 : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y
        = GlobalTheory.OTY.TwEst.quot A h β y :=
      GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
    have h2 : (θ (δ * psi A L s y) : ℂ) * h (A.pick y) y
        - β (A.pick y) y * GlobalTheory.OTY.TwEst.ext0 U F0 y
        = β (A.pick y) y * ((θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β y
          - GlobalTheory.OTY.TwEst.ext0 U F0 y) := by
      rw [hq y hy]; ring
    simp only [h1]
    congr 1
    unfold WeightedAtlas.nsq
    simp only [h2, norm_mul, mul_pow]
    ring
  · refine lintegral_congr fun x => ?_
    simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    congr 2
    rw [neg_add, Real.exp_add]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEstimateRhsLeManifold
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.rhs_le_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ δ T : ℝ, ∫⁻ x in {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1}, ENNReal.ofReal (‖GlobalTheory.OTY.TwEst.quot A h β x‖ ^ 2 * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x))) ∂vol n (fun y : U => z y) ≤ ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ T
  set S : Set Y := {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1} with hS
  have hδ : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const hδ).inter (measurableSet_le hδ measurable_const)
  have hw : Measurable (S.indicator fun y => Real.exp (-psi A L s y)) :=
    (Real.measurable_exp.comp hpsi.neg).indicator hSm
  have key := htr _ _ hm hw (fun y _ => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y)
  have hS' : MeasurableSet {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} :=
    measurable_subtype_coe hSm
  rw [← lintegral_indicator hS']
  refine le_trans (le_of_eq ?_) (le_trans key.ge ?_)
  · refine lintegral_congr fun x => ?_
    rw [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    by_cases hx : (x : Y) ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx), ← Real.exp_add]
      congr 3
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx)]
      simp
  · rw [← lintegral_indicator hSm, ← lintegral_indicator hU.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem hy]
      by_cases hx : y ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have h0 := GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
        simp only at h0
        rw [h0]
        apply le_of_eq
        congr 2
        unfold WeightedAtlas.nsq
        rw [hq y hy, norm_mul]
        ring
      · rw [Set.indicator_of_notMem hx]
        simp
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPer

theorem ex_add_lattice {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left} (u : HolUnif A L g) (l : u.Λ) (z : Fin g → ℂ) :
    u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem pre_val_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ U, IsOpen (pre u.ex U)) ∧ (∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U)) ∧ (∀ U (l : u.Λ) (z : Fin g → ℂ), z + l ∈ pre u.ex U ↔ z ∈ pre u.ex U) ∧ (∀ U b (l : u.Λ) (z : Fin g → ℂ), val u.ex U b (z + l) = val u.ex U b z) ∧ (∀ U V, pre u.ex (U ⊓ V) = pre u.ex U ∩ pre u.ex V) ∧ (∀ U V, V ≤ U → pre u.ex V ⊆ pre u.ex U) ∧ (∀ (K : Type) (W : K → A.left.Opens) z, z ∈ pre u.ex (⨆ i, W i) ↔ ∃ i, z ∈ pre u.ex (W i)) ∧ (∀ U z, z ∈ pre u.ex U → ∃ W : A.left.affineOpens, W.1 ≤ U ∧ z ∈ pre u.ex W.1) ∧ (∀ U V (h : V ≤ U) (b : Sec (str A) U), ∀ z ∈ pre u.ex V, val u.ex V (Sec.res (str A) h b) z = val u.ex U b z) ∧ (∀ U, ∀ z ∈ pre u.ex U, ∃ e : Sec (str A) U →ₐ[ℂ] ℂ, ∀ b, val u.ex U b z = e b) ∧ (∀ U b z, z ∈ pre u.ex (A.left.basicOpen b) ↔ val u.ex U b z ≠ 0) ∧ ∀ z, z ∈ pre u.ex ⊤ := by
  intro A _ g L u
  refine ⟨fun U ↦ (u.hol U 0).1, fun U b ↦ (u.hol U b).2, fun U l z ↦ ?_, fun U b l z ↦ ?_, fun U V ↦ ?_,
    fun U V h z hz ↦ top_le_preimage_mono _ h hz, fun K W z ↦ ?_, fun U z hz ↦ ?_,
    fun U V h b z hz ↦ valAt'_map (u.ex z).left (homOfLE h).op b hz, fun U z hz ↦ ?_,
    fun U b z ↦ top_le_preimage_basicOpen_iff _ U b, fun z ↦ le_top (α := (Sp ℂ).Opens)⟩
  · simp only [pre, Set.mem_setOf_eq, ex_add_lattice]
  · simp only [val, ex_add_lattice]
  · ext z
    exact top_le_preimage_inf _ U V
  · refine (top_le_preimage_iff_mem (u.ex z).left _).trans (TopologicalSpace.Opens.mem_iSup.trans ?_)
    exact exists_congr fun i ↦ (top_le_preimage_iff_mem (u.ex z).left _).symm
  · have h1 := (top_le_preimage_iff_mem (u.ex z).left _).1 hz
    obtain ⟨W, hW, h2, h3⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 A.left.isBasis_affineOpens) h1
    exact ⟨⟨W, hW⟩, h3, (top_le_preimage_iff_mem (u.ex z).left _).2 h2⟩
  · refine ⟨{ toRingHom := valAtHom (u.ex z).left U hz, commutes' := fun a ↦ ?_ }, fun b ↦ valAt'_eq_valAtHom _ hz b⟩
    refine (valAt'_eq_valAtHom (u.ex z).left hz _).symm.trans ?_
    refine valAt'_constFn (u.ex z).left (str A) ?_ U a hz
    exact (congrArg _ (Category.comp_id _)).trans (Over.w (u.ex z))

end GlobalTheory.CechPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRules
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPer

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left}

theorem holUnif_ex_left_comp_str (u : HolUnif A L g) (w : Fin g → ℂ) : (u.ex w).left ≫ str A = 𝟙 (Sp ℂ) := by
  have := Over.w (u.ex w)
  simp [str, this]

theorem holUnif_val_algebraMap (u : HolUnif A L g) (U : A.left.Opens) (w : Fin g → ℂ) (hw : w ∈ pre u.ex U) (c : ℂ) :
    val u.ex U (algebraMap ℂ (Sec (str A) U) c) w = c := by
  show valAt' (u.ex w).left U (((str A).appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c
  rw [valAt'_appLE (u.ex w).left (str A) ⊤ U le_top _ hw, holUnif_ex_left_comp_str]
  exact valAt'_id_top c

theorem holUnif_val_mul (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a * b) = fun w => val u.ex U a w * val u.ex U b w :=
  funext fun w => valAt'_mul (u.ex w).left U a b

theorem holUnif_val_add (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a + b) = fun w => val u.ex U a w + val u.ex U b w :=
  funext fun w => valAt'_add (u.ex w).left U a b

theorem holUnif_differentiableAt_val (u : HolUnif A L g) (U : A.left.Opens) (b : Sec (str A) U) {z : Fin g → ℂ}
    (hz : z ∈ pre u.ex U) : DifferentiableAt ℂ (val u.ex U b) z :=
  (u.hol U b).2.differentiableAt (((u.hol U b).1).mem_nhds hz)

theorem exists_isEv (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    ∃ E, IsEv u.ex U z E := by
  let N := (Fin g → ℂ) →L[ℂ] ℂ
  let e : Sec (str A) U →+* ℂ := valAtHom (u.ex z).left U hz
  have he : ∀ a, e a = val u.ex U a z := fun a => (valAt'_eq_valAtHom (u.ex z).left hz a).symm
  letI : Module (Sec (str A) U) N := Module.compHom N e
  haveI : IsScalarTower ℂ (Sec (str A) U) N := ⟨fun c a n => by
    show e (c • a) • n = c • (e a • n)
    rw [Algebra.smul_def, map_mul, mul_smul, he (algebraMap ℂ _ c), holUnif_val_algebraMap u U z hz]⟩
  have hc : ∀ (c : ℂ) (b : Sec (str A) U), val u.ex U (c • b) =ᶠ[nhds z] fun w => c * val u.ex U b w := by
    intro c b
    filter_upwards [((u.hol U b).1).mem_nhds hz] with w hw
    rw [Algebra.smul_def, holUnif_val_mul]
    exact congrArg (· * val u.ex U b w) (holUnif_val_algebraMap u U w hw c)
  let Dl : Sec (str A) U →ₗ[ℂ] N :=
    { toFun := fun b => fderiv ℂ (val u.ex U b) z
      map_add' := fun a b =>
        (congrArg (fun f => fderiv ℂ f z) (holUnif_val_add u U a b)).trans
          (fderiv_add (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz))
      map_smul' := fun c b =>
        (hc c b).fderiv_eq.trans (fderiv_const_mul (holUnif_differentiableAt_val u U b hz) c) }
  let D' : Derivation ℂ (Sec (str A) U) N :=
    { Dl with
      map_one_eq_zero' := by
        show fderiv ℂ (val u.ex U 1) z = 0
        have h1 : val u.ex U (1 : Sec (str A) U) =ᶠ[nhds z] fun _ => (1 : ℂ) := by
          filter_upwards [((u.hol U 1).1).mem_nhds hz] with w hw
          exact valAt'_one (u.ex w).left hw
        exact h1.fderiv_eq.trans (fderiv_const_apply 1)
      leibniz' := fun a b => by
        show fderiv ℂ (val u.ex U (a * b)) z = e a • fderiv ℂ (val u.ex U b) z + e b • fderiv ℂ (val u.ex U a) z
        rw [he, he]
        exact (congrArg (fun f => fderiv ℂ f z) (holUnif_val_mul u U a b)).trans
          (fderiv_mul (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz)) }
  refine ⟨D'.liftKaehlerDifferential.restrictScalars ℂ, fun a b => ?_⟩
  show D'.liftKaehlerDifferential (a • KaehlerDifferential.D ℂ (Sec (str A) U) b) = _
  rw [LinearMap.map_smul, Derivation.liftKaehlerDifferential_comp_D]
  show e a • fderiv ℂ (val u.ex U b) z = _
  rw [he]

theorem isEv_evForm (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    IsEv u.ex U z (evForm u.ex U z) := by
  have h := exists_isEv u U hz
  rw [evForm, dite_eq_left h]
  exact h.choose_spec

theorem evForm_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens),
    ∀ z ∈ pre u.ex U, IsEv u.ex U z (evForm u.ex U z) ∧
      (∀ (a : Sec (str A) U) ξ, evForm u.ex U z (a • ξ) = val u.ex U a z • evForm u.ex U z ξ) ∧
      ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
  intro A _ g L u U z hz
  have hE := isEv_evForm u U hz
  have hone : val u.ex U (1 : Sec (str A) U) z = 1 := valAt'_one (u.ex z).left hz
  have hD : ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
    intro b
    have := hE 1 b
    rwa [one_smul, hone, one_smul] at this
  refine ⟨hE, fun a ξ => ?_, hD⟩
  have hspan := KaehlerDifferential.span_range_derivation ℂ (Sec (str A) U)
  have hξ : ξ ∈ Submodule.span (Sec (str A) U) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U))) := by
    rw [hspan]; exact Submodule.mem_top
  revert a
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    intro a
    rw [hE a b, hD]
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | smul s x _ hx =>
    intro a
    rw [smul_smul, hx, hx, smul_smul, holUnif_val_mul]

end GlobalTheory.CechPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedL2EstimateTwistedSections
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.cutoff_quot_wint_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ : ℝ) (θ : ℝ → ℝ), Continuous θ → (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) → wint n (fun y : U => z y) (fun x : U => (θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x) (fun x : U => GlobalTheory.OTY.TwEst.wt A E β z x) ≤ ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ θ hθ hθ1
  have hma : Measurable (fun y : Y => (θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y) :=
    (Complex.measurable_ofReal.comp (hθ.measurable.comp (hpsi.const_mul δ))).mul hm
  have key := htr _ (fun _ => 1) hma measurable_const (fun _ _ => zero_le_one)
  simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe, one_mul, mul_one] at key
  unfold wint
  rw [← key]
  refine le_trans (setLIntegral_mono' hU.measurableSet ?_) (setLIntegral_le_lintegral U _)
  intro y hy
  apply ENNReal.ofReal_le_ofReal
  have e : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y = GlobalTheory.OTY.TwEst.quot A h β y :=
    GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
  rw [e]
  unfold WeightedAtlas.nsq
  rw [hq y hy, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hθ1 _).1]
  obtain ⟨h0, h1⟩ := hθ1 (δ * psi A L s y)
  have h2 : θ (δ * psi A L s y) ^ 2 ≤ 1 := by nlinarith
  set t := θ (δ * psi A L s y)
  set b := ‖β (A.pick y) y‖
  set q := ‖GlobalTheory.OTY.TwEst.quot A h β y‖
  generalize hc : Real.exp _ = c
  have hc0 : 0 ≤ c := hc ▸ (Real.exp_pos _).le
  have h3 : 0 ≤ (b * q) ^ 2 * c := by positivity
  calc b ^ 2 * c * (t * q) ^ 2 = t ^ 2 * ((b * q) ^ 2 * c) := by ring
    _ ≤ 1 * ((b * q) ^ 2 * c) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := one_mul _
end

