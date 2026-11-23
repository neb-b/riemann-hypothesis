module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0066
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionsDimZero

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def monVal (z : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) : Ω :=
  ∏ p, z p ^ m p

def blockDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ :=
  ∑ i, m ⟨k, i⟩

def rt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω :=
  fun p => y p / y ⟨p.1, c p.1⟩

theorem aeval_monomial_int (z : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (q : ℤ) :
    aeval z (monomial m q : MRing ι) = (q : Ω) * monVal z m := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), eq_intCast]
  rfl

theorem aeval_monomial_rat (z : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (q : ℚ) :
    aeval z (monomial m q : MvPolynomial (Σ k, ι k) ℚ) = q • monVal z m := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Algebra.smul_def]
  rfl

theorem monVal_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (m : (Σ k, ι k) →₀ ℕ) :
    monVal y m = monVal (rt y c) m * ∏ k, y ⟨k, c k⟩ ^ blockDeg m k := by
  have h : ∀ p : Σ k, ι k, y p ^ m p = rt y c p ^ m p * y ⟨p.1, c p.1⟩ ^ m p := fun p => by
    rw [← mul_pow, rt, div_mul_cancel₀ _ (hc p.1)]
  simp only [monVal, h, Finset.prod_mul_distrib, blockDeg]
  congr 1
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_pow_eq_pow_sum Finset.univ (fun i => m ⟨k, i⟩) (y ⟨k, c k⟩)

theorem rt_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : rt y c p ∈ chartRingQ y c :=
  Algebra.subset_adjoin ⟨p, rfl⟩

theorem monVal_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (m : (Σ k, ι k) →₀ ℕ) :
    monVal (rt y c) m ∈ chartRingQ y c :=
  prod_mem fun p _ => pow_mem (rt_mem y c p) _

theorem inv_mem_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    (y ⟨k, i⟩ / y ⟨k, c k⟩)⁻¹ ∈ chartRingQ y c :=
  Subalgebra.inv_mem_of_algebraic (A := chartRingQ y c) (x := ⟨_, rt_mem y c ⟨k, i⟩⟩)
    (CoordCurveDegree.isAlgebraic_ratio hP c hc ⟨k, i⟩)

theorem zpow_mem_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) (e : ℤ) :
    (y ⟨k, i⟩ / y ⟨k, c k⟩) ^ e ∈ chartRingQ y c := by
  rcases e with e | e
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem (rt_mem y c ⟨k, i⟩) _
  · rw [zpow_negSucc, ← inv_pow]
    exact pow_mem (inv_mem_chart hP c hc k i) _

theorem chart_le {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c c' : ∀ k, ι k)
    (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) : chartRingQ y c ≤ chartRingQ y c' := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨p, rfl⟩
  have e : y p / y ⟨p.1, c p.1⟩ = rt y c' p * (y ⟨p.1, c p.1⟩ / y ⟨p.1, c' p.1⟩)⁻¹ := by
    rw [rt, inv_div, div_mul_div_cancel₀ (hc' p.1)]
  show y p / y ⟨p.1, c p.1⟩ ∈ chartRingQ y c'
  rw [e]
  exact mul_mem (rt_mem y c' p) (inv_mem_chart hP c' hc' p.1 (c p.1))

theorem finrank_map_mulRight (L : Subalgebra ℚ Ω) {w : Ω} (hw : w ≠ 0) :
    Module.finrank ℚ ((Subalgebra.toSubmodule L).map (LinearMap.mulRight ℚ w)) = Module.finrank ℚ L := by
  have hinj : Function.Injective (LinearMap.mulRight ℚ w) := fun s t h => by
    simp only [LinearMap.mulRight_apply] at h
    exact mul_right_cancel₀ hw h
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, Subalgebra.finrank_toSubmodule]

theorem chartLatQ_eq {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) (n : ℕ) :
    chartLatQ y a n = (Subalgebra.toSubmodule (chartRingQ y c)).map
      (LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ ((n : ℤ) * a k))) := by
  have hu : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      (∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c' k⟩ ^ ((n : ℤ) * a k) = 1 := by
    intro c' hc'
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [← zpow_add₀ (hc' k), neg_add_cancel, zpow_zero]
  ext s
  constructor
  · intro hs
    refine Submodule.mem_map.mpr ⟨s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)), hs c hc, ?_⟩
    rw [LinearMap.mulRight_apply, mul_assoc, hu c hc, mul_one]
  · rintro ⟨t, ht, rfl⟩ c' hc'
    rw [LinearMap.mulRight_apply]
    have e : (∏ k, y ⟨k, c k⟩ ^ ((n : ℤ) * a k)) * ∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * a k)) =
        ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ ((n : ℤ) * a k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [div_zpow, zpow_neg, div_eq_mul_inv]
    rw [mul_assoc, e]
    exact mul_mem (chart_le hP c c' hc' ht) (prod_mem fun k _ => zpow_mem_chart hP c' hc' k (c k) _)

theorem valueSpan_le (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    valueSpan y d ≤ (Subalgebra.toSubmodule (chartRingQ y c)).map
      (LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ d k)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [SetLike.mem_coe, g.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [aeval_monomial_int, monVal_eq y c hc m]
  have hb : ∀ k, blockDeg m k = d k := fun k => hg m hm k
  simp only [hb]
  exact Submodule.mem_map.mpr ⟨((AddMonoidAlgebra.coeff g m : ℤ) : Ω) * monVal (rt y c) m,
    (mul_mem (intCast_mem _ _) (monVal_mem y c m) : _ * _ ∈ chartRingQ y c),
    by rw [LinearMap.mulRight_apply, mul_assoc]⟩

theorem mem_valueSpan (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ)
    (m : (Σ k, ι k) →₀ ℕ) (hm : ∀ k, blockDeg m k ≤ d k) :
    monVal (rt y c) m * ∏ k, y ⟨k, c k⟩ ^ d k ∈ valueSpan y d := by
  classical
  set m' : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun p => m p + if p.2 = c p.1 then d p.1 - blockDeg m p.1 else 0) with hm'_def
  have hm' : ∀ p, m' p = m p + if p.2 = c p.1 then d p.1 - blockDeg m p.1 else 0 := fun p => by
    simp [hm'_def]
  have hdeg : ∀ k, blockDeg m' k = d k := by
    intro k
    have h1 : blockDeg m' k = blockDeg m k + (d k - blockDeg m k) := by
      simp only [blockDeg, hm', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := hm k
    omega
  have hextra : ∏ p, rt y c p ^ (if p.2 = c p.1 then d p.1 - blockDeg m p.1 else 0) = 1 := by
    refine Finset.prod_eq_one fun p _ => ?_
    obtain ⟨k, i⟩ := p
    dsimp only
    split_ifs with h
    · subst h
      rw [rt, div_self (hc k), one_pow]
    · exact pow_zero _
  have hval : monVal (rt y c) m' = monVal (rt y c) m := by
    unfold monVal
    simp only [hm', pow_add, Finset.prod_mul_distrib, hextra, mul_one]
  refine Submodule.subset_span ⟨monomial m' 1, ?_, ?_⟩
  · intro e he k
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at he
    rw [he]
    exact hdeg k
  · rw [aeval_monomial_int, Int.cast_one, one_mul, monVal_eq y c hc, hval]
    simp only [hdeg]

theorem exists_le_span {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : ∃ D : ℕ, Subalgebra.toSubmodule (chartRingQ y c) ≤
      Submodule.span ℚ {x | ∃ m, (∀ k, blockDeg m k ≤ D) ∧ monVal (rt y c) m = x} := by
  set V : ℕ → Submodule ℚ Ω := fun D =>
    Submodule.span ℚ {x | ∃ m, (∀ k, blockDeg m k ≤ D) ∧ monVal (rt y c) m = x} with hV
  have hmono : Monotone V := fun D D' h => Submodule.span_mono (by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, fun k => (hm k).trans h, rfl⟩)
  have hfin : Module.Finite ℚ (chartRingQ y c) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) (by
      rintro _ ⟨p, rfl⟩
      exact (CoordCurveDegree.isAlgebraic_ratio hP c hc p).isIntegral)
  have hfg : (Subalgebra.toSubmodule (chartRingQ y c)).FG := Module.Finite.iff_fg.mp hfin
  have hcpt := (isCompactElement_iff_le_of_directed_sSup_le _).mp
    ((Submodule.fg_iff_compact _).mp hfg)
  obtain ⟨_, ⟨D, rfl⟩, hD⟩ := hcpt (Set.range V) (Set.range_nonempty V)
    (directedOn_range.mpr hmono.directed_le) (by
      intro x hx
      change x ∈ chartRingQ y c at hx
      rw [chartRingQ, Algebra.adjoin_range_eq_range_aeval] at hx
      obtain ⟨f, rfl⟩ := hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, f.as_sum, map_sum]
      refine Submodule.sum_mem _ fun m _ => ?_
      rw [aeval_monomial_rat]
      refine Submodule.smul_mem _ _ ?_
      exact (le_sSup (Set.mem_range_self (∑ k, blockDeg m k)) : V _ ≤ _) (Submodule.subset_span
        ⟨m, fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k), rfl⟩))
  exact ⟨D, hD⟩

theorem valueSpan_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (D : ℕ)
    (hD : Subalgebra.toSubmodule (chartRingQ y c) ≤
      Submodule.span ℚ {x | ∃ m, (∀ k, blockDeg m k ≤ D) ∧ monVal (rt y c) m = x})
    (d : K → ℕ) (hd : ∀ k, D ≤ d k) :
    valueSpan y d = (Subalgebra.toSubmodule (chartRingQ y c)).map
      (LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ d k)) := by
  refine le_antisymm (valueSpan_le y c hc d) ?_
  rw [Submodule.map_le_iff_le_comap]
  refine hD.trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact mem_valueSpan y c hc d m fun k => (hm k).trans (hd k)

theorem eventualValue_eq {f : (K → ℤ) → ℤ} {v : ℤ} (h : ∀ᶠ m in atTop, f m = v) :
    NumbersDVR.eventualValue f = v := by
  have hex : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨v, h⟩
  rw [NumbersDVR.eventualValue, dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and h).exists
  rw [← h1, h2]

end SectionsDimZero


open SectionsDimZero in
theorem SectionsDimZero.proof : SectionsDimZero.Statement := by
  intro K _ ι _ Ω _ _ y a n hP
  classical
  choose c hcX using hP.2.1.2.2
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k (CoordCurveDegree.X_mem_of_eq_zero h0)
  obtain ⟨D, hD⟩ := exists_le_span hP c hc
  rw [chartLatQ_eq hP c hc, finrank_map_mulRight _
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k))]
  symm
  unfold genDeg NumbersDVR.intNum
  simp only [NumbersDVR.mixedDiff, List.ofFn_zero, List.foldr_nil]
  apply eventualValue_eq
  filter_upwards [eventually_ge_atTop (fun _ : K => (D : ℤ))] with m hm
  have hm0 : ∀ k, (D : ℤ) ≤ m k := hm
  have e : m = fun k => (((m k).toNat : ℕ) : ℤ) := funext fun k => by
    have := hm0 k
    omega
  rw [e, HilbFnValueSpan.proof, valueSpan_eq y c hc D hD _ (fun k => by have := hm0 k; omega),
    finrank_map_mulRight _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftQuotientBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Mul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLatQ_add {B γ : K → ℤ} {g s : Ω} (hg : g ∈ chartLatQ y γ 1) (hs : s ∈ chartLatQ y B 1) :
    g * s ∈ chartLatQ y (B + γ) 1 := by
  intro c' hc'
  have hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (B + γ) k)) =
      y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * γ k)) * y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * B k)) := by
    intro k
    rw [← zpow_add₀ (hc' k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  have heq : g * s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (B + γ) k)) =
      (g * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * γ k))) * (s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * B k))) := by
    simp only [hk, Finset.prod_mul_distrib]
    ring
  rw [heq]
  exact Subalgebra.mul_mem _ (hg c' hc') (hs c' hc')

theorem finrank_quot_le_of_regular {B γ : K → ℤ} {g : Ω} [FiniteDimensional ℚ (chartLatQ y (B + γ) 1)]
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hg : g ∈ chartLatQ y γ 1)
    (hreg : ∀ s : Ω, s ∈ chartLatQ y B 1 → g * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (B + γ - 1) 1 →
      s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (B - 1) 1) :
    Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) ≤
      Module.finrank ℚ (chartLatQ y (B + γ) 1 ⧸ chartDivSec y c (B + γ)) := by
  let φ : chartLatQ y B 1 →ₗ[ℚ] chartLatQ y (B + γ) 1 :=
    { toFun := fun s => ⟨g * s, mul_mem_chartLatQ_add hg s.2⟩
      map_add' := fun s t => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm r g (s : Ω)) }
  have hle : chartDivSec y c B ≤ (chartDivSec y c (B + γ)).comap φ := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hs)
    refine Submodule.mem_comap.mpr (Submodule.mem_comap.mpr (Submodule.mem_map.mpr
      ⟨g * t, ?_, ?_⟩))
    · have h := mul_mem_chartLatQ_add hg ht
      rwa [show B - 1 + γ = B + γ - 1 by abel] at h
    · change (∏ k, y ⟨k, c k⟩) * (g * t) = g * (s : Ω)
      have hts' : (∏ k, y ⟨k, c k⟩) * t = (s : Ω) := hts
      rw [← hts']
      ring
  refine LinearMap.finrank_le_finrank_of_injective (f := Submodule.mapQ _ _ φ hle) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.Quotient.mk_eq_zero]
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
  have hts' : (∏ k, y ⟨k, c k⟩) * t = g * (s : Ω) := hts
  have hu := hreg s s.2 (by rwa [← hts', mul_div_cancel_left₀ _ hm0])
  refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨_, hu, ?_⟩)
  change (∏ k, y ⟨k, c k⟩) * ((s : Ω) / ∏ k, y ⟨k, c k⟩) = (s : Ω)
  exact mul_div_cancel₀ _ hm0

end Mul

theorem ShiftQuotientBound.proof (hfin : SectionLatticeFinite.Statement) (hQ : HyperplaneQuotientBound.Statement)
    (hR : HyperplaneRegularSection.Statement) : ShiftQuotientBound.Statement := by
  intro K _ ι _ Ω _ _ y D a b c hD hV hB hc
  obtain ⟨C₀, hC₀⟩ := hQ K ι Ω y D (fun _ => 1) c hD hV hB hc
  set N : ℕ := 1 + ∑ k, (a k).natAbs with hN
  set M : ℕ := ∑ k, (b k).natAbs with hM
  have hN1 : 1 ≤ N := by omega
  have ht : Tendsto (fun n : ℕ => n * N + M) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; nlinarith [Nat.zero_le n, hN1]) tendsto_id
  refine ⟨|C₀| * ((N + M : ℕ) : ℝ) ^ (D - 1),
    ((ht.eventually hC₀).and (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_⟩
  set B : K → ℤ := (n : ℤ) • a + b with hBdef
  set γ : K → ℤ := (((n * N + M : ℕ) : ℤ) • fun _ => (1 : ℤ)) - B with hγdef
  have hγ : ∀ k, 0 ≤ γ k := by
    intro k
    have ha : (a k).natAbs ≤ ∑ j, (a j).natAbs :=
      Finset.single_le_sum (f := fun j => (a j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hb : (b k).natAbs ≤ ∑ j, (b j).natAbs :=
      Finset.single_le_sum (f := fun j => (b j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have ha' : a k < (N : ℤ) :=
      calc a k ≤ (a k).natAbs := Int.le_natAbs
        _ ≤ ((∑ j, (a j).natAbs : ℕ) : ℤ) := by exact_mod_cast ha
        _ < (N : ℤ) := by rw [hN]; exact_mod_cast (by omega : ∑ j, (a j).natAbs < 1 + ∑ j, (a j).natAbs)
    have hb' : b k ≤ (M : ℤ) :=
      calc b k ≤ (b k).natAbs := Int.le_natAbs
        _ ≤ (M : ℤ) := by rw [hM]; exact_mod_cast hb
    simp only [hγdef, hBdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ha'.le (Int.natCast_nonneg n)]
  obtain ⟨g, -, hg, hreg⟩ := hR K ι Ω y c (fun k => (γ k).toNat) hc
  have he : (fun k => ((γ k).toNat : ℤ)) = γ := funext fun k => Int.toNat_of_nonneg (hγ k)
  rw [he] at hg hreg
  have := finiteDimensional_chartLatQ hfin (fun k => ⟨c k, hc k⟩) (B + γ)
  have h1 := finrank_quot_le_of_regular hc hg (hreg B)
  rw [show B + γ = ((n * N + M : ℕ) : ℤ) • fun _ => (1 : ℤ) by rw [hγdef]; abel] at h1
  have h2 : (Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) : ℝ) ≤ C₀ * ((n * N + M : ℕ) : ℝ) ^ (D - 1) :=
    le_trans (by exact_mod_cast h1) hn
  have h3 : ((n * N + M : ℕ) : ℝ) ≤ ((N + M : ℕ) : ℝ) * (n : ℝ) := by
    have : n * N + M ≤ (N + M) * n := by nlinarith
    exact_mod_cast this
  calc (Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) : ℝ)
      ≤ |C₀| * ((n * N + M : ℕ) : ℝ) ^ (D - 1) :=
        h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    _ ≤ |C₀| * (((N + M : ℕ) : ℝ) * (n : ℝ)) ^ (D - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 _) (abs_nonneg _)
    _ = |C₀| * ((N + M : ℕ) : ℝ) ^ (D - 1) * (n : ℝ) ^ (D - 1) := by rw [mul_pow, mul_assoc]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockStepLocal

theorem nonempty_of_isArithVar {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {x : Ix κ → Ω}
    (hX : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) : Nonempty κ := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : IsEmpty (Σ k : Unit, GlobalTheory κ k) := ⟨fun p => h.false p.2⟩
  have h1 : ringKrullDim (MRing (GlobalTheory κ)) = 1 := by
    rw [ringKrullDim_mvPolynomial_of_isEmpty]
    exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField
  have h2 := ringKrullDim_quotient_le (coordIdeal ℤ x : Ideal (MRing (GlobalTheory κ)))
  rw [hX.2.2.2, h1] at h2
  have h3 : ((D + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := by simpa using h2
  have h4 := WithBot.coe_le_coe.1 h3
  norm_cast at h4

theorem choose_div_factorial {D i : ℕ} (hi : i ≤ D) (u : ℝ) :
    (D.choose i : ℝ) * u / (D.factorial : ℝ) = u / ((i.factorial : ℝ) * ((D - i).factorial : ℝ)) := by
  have e : ((D.choose i : ℕ) : ℝ) * (i.factorial : ℝ) * ((D - i).factorial : ℝ) = (D.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have h0 : (D.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((D - i).factorial : ℝ) ≠ 0 := by positivity
  rw [← e]
  field_simp

end TwoBlockStepLocal


open TwoBlockStepLocal in
theorem TwoBlockStepLocal.proof (hA : TwoBlockPieceCycle.Statement) (hM : TwoBlockCycleExpand.Statement)
    (hR : TwoBlockCoeffCycle.Statement) : TwoBlockStepLocal.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm' hsp
  obtain ⟨c⟩ := nonempty_of_isArithVar hX
  obtain ⟨l, hl⟩ : ∃ l : Ix κ → ℤ, x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j := by
    have hc : x ⟨(), c⟩ ∈ Submodule.span ℤ (Set.range (matAct B x)) :=
      hsp (Submodule.subset_span ⟨⟨(), c⟩, rfl⟩)
    obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hc
    exact ⟨l, by rw [← hl]; simp [zsmul_eq_mul]⟩
  obtain ⟨a₀, C, h⟩ := hA D Ω κ x B c l hX hx hB hsp hl
  refine ⟨a₀, C, fun a b ha hb => ?_⟩
  convert h a b ha hb using 3
  rw [hM D Ω κ x B c l hX hx hB hsp hl a b, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiD : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [hR D Ω κ I x B m m' c l hI hX hx hB hm hm' hsp hl i hiD,
    show (D.choose i : ℝ) * (a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i) =
      (D.choose i : ℝ) * ((a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i)) by ring,
    choose_div_factorial hiD]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomCharpolyForms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def DehomCharpolyForms.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω),
      (∀ k, u * (l j / l k) ^ m ∈ integralClosure (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) Ω) →
      ∃ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ, c 0 = 1 ∧
        (∀ i ≤ Module.finrank P Ω, (c i).IsHomogeneous (i * m)) ∧
        (LinearMap.charpoly (Algebra.lmul P Ω u)).map (algebraMap P Ω) =
          ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
            Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) ∧
        (u ≠ 0 → c (Module.finrank P Ω) ≠ 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

