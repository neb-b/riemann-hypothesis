module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubOnePowEqPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvr
section
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem valuation_le_one_iff_isIntegral_of_complete_dvr :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field Ω] [Algebra R Ω]
      [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) →
      ∃ v : Valuation Ω ℝ≥0, ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x := by
  intro R Ω _ _ _ _ _ _ _ hinj
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).mpr hinj
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : Algebra.IsAlgebraic (FractionRing R) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R (FractionRing R))
  obtain ⟨f, hna, hnt, hball, hcomp⟩ := _root_.GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing R (FractionRing R)
  obtain ⟨v, -, hv⟩ := GlobalTheory.T.exists_spectral_valuation_algebraic_extension (FractionRing R) Ω f hna hnt hcomp
  refine ⟨v, fun x => ?_⟩
  rw [hv]
  simp only [hball]
  constructor
  · intro h
    have hl : minpoly (FractionRing R) x ∈ Polynomial.lifts (algebraMap R (FractionRing R)) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr h
    obtain ⟨q, hq, -, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl
      (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    refine ⟨q, hmon, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (FractionRing R), hq]
    exact minpoly.aeval _ _
  · intro h i
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing R) h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOne
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.ZetaNonvanishing₂

variable {Ω : Type} [Field Ω]

theorem valuation_sub_one_pow_sub_le (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (v : Valuation Ω ℝ≥0) (x : Ω) (hx : v x ≤ 1) :
    v ((x - 1) ^ p - (x ^ p - 1)) ≤ v (p : Ω) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨x, hx⟩ : v.integer) (-1)
  have hr' := congrArg Subtype.val hr
  push_cast at hr'
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [hodd.neg_one_pow] at hr'
  have e : (x - 1) ^ p - (x ^ p - 1) = (p : Ω) * (-(x * (r : Ω))) := by
    rw [sub_eq_add_neg x 1, hr']; ring
  rw [e, v.map_mul, v.map_neg, v.map_mul]
  have hr1 : v (r : Ω) ≤ 1 := r.2
  calc v (p : Ω) * (v x * v (r : Ω)) ≤ v (p : Ω) * (1 * 1) := by gcongr
    _ = v (p : Ω) := by simp

theorem valuation_zeta_sub_one : ∀ (p : ℕ) [hpf : Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), v (p : Ω) < 1 → ∀ n : ℕ, 1 ≤ n → v (T.ζ n - 1) < 1 ∧ v (p : Ω) ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by
  intro p hpf Ω _ _ hp2 T v hvp
  have hp := hpf.out

  have hvz : ∀ n, v (T.ζ n) = 1 := by
    intro n
    have h1 : v (T.ζ n) ^ (p ^ n) = 1 := by
      rw [← v.map_pow, (T.prim n).pow_eq_one, v.map_one]
    exact (pow_eq_one_iff_of_nonneg (zero_le') (pow_ne_zero _ hp.ne_zero)).1 h1

  have hlt : ∀ n, v (T.ζ n - 1) < 1 := by
    intro n
    induction n with
    | zero =>
      have : T.ζ 0 = 1 := by
        have := T.prim 0
        rw [pow_zero] at this
        exact IsPrimitiveRoot.one_right_iff.1 this
      simp [this]
    | succ n ih =>
      have hb := valuation_sub_one_pow_sub_le p hp hp2 v (T.ζ (n + 1)) (hvz _).le
      rw [T.ζpow n] at hb
      have h2 : v ((T.ζ (n + 1) - 1) ^ p) < 1 := by
        have : (T.ζ (n + 1) - 1) ^ p = ((T.ζ (n + 1) - 1) ^ p - (T.ζ n - 1)) + (T.ζ n - 1) := by ring
        rw [this]
        exact lt_of_le_of_lt (v.map_add _ _) (max_lt (lt_of_le_of_lt hb hvp) ih)
      rw [v.map_pow] at h2
      by_contra hc
      push_neg at hc
      exact absurd h2 (not_lt.2 (one_le_pow₀ hc))
  intro n hn
  refine ⟨hlt n, ?_⟩

  have hge : v (T.ζ 1 - 1) ≤ v (T.ζ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hz : ∀ k, T.ζ (k + 1) ^ (p ^ k) = T.ζ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', pow_mul, T.ζpow, ih]
    have e : T.ζ 1 - 1 = (∑ i ∈ Finset.range (p ^ m), T.ζ (m + 1) ^ i) * (T.ζ (m + 1) - 1) := by
      rw [geom_sum_mul, hz m]
    rw [e, v.map_mul]
    have hs : v (∑ i ∈ Finset.range (p ^ m), T.ζ (m + 1) ^ i) ≤ 1 :=
      v.map_sum_le fun i _ => by rw [v.map_pow, hvz, one_pow]
    calc v (∑ i ∈ Finset.range (p ^ m), T.ζ (m + 1) ^ i) * v (T.ζ (m + 1) - 1)
        ≤ 1 * v (T.ζ (m + 1) - 1) := by gcongr
      _ = v (T.ζ (m + 1) - 1) := one_mul _
  have h1 := _root_.GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime Ω v p hp (T.ζ 1) (by simpa using T.prim 1)
  have ha1 : v (T.ζ 1 - 1) ≤ 1 := (hlt 1).le
  have hp3 : 2 ≤ p - 1 := by have := hp.two_le; omega
  rw [← h1]
  calc v (T.ζ 1 - 1) ^ (p - 1) ≤ v (T.ζ 1 - 1) ^ 2 := pow_le_pow_of_le_one (zero_le') ha1 hp3
    _ = v (T.ζ 1 - 1) * v (T.ζ 1 - 1) := sq _
    _ ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by gcongr

end GlobalTheory.K5.ZetaNonvanishing₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WirtingerEichler
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerDbar

def P (s : ℂ) (G : ℂ → ℂ) (d : ℂ) : Prop :=
  ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = d

lemma wirtinger_eq_zero_of_hasDerivAt {s : ℂ} {g : ℂ → ℂ} {g' : ℂ} (hg : HasDerivAt g g' s) : P s g 0 := by
  refine ⟨_, hg.hasFDerivAt.restrictScalars ℝ, ?_⟩
  simp

lemma wirtinger_sub {s : ℂ} {G H : ℂ → ℂ} {d e : ℂ} (hG : P s G d) (hH : P s H e) :
    P s (fun z => G z - H z) (d - e) := by
  obtain ⟨L, hL, hd⟩ := hG
  obtain ⟨M, hM, he⟩ := hH
  refine ⟨L - M, hL.sub hM, ?_⟩
  simp only [ContinuousLinearMap.sub_apply]
  rw [← hd, ← he]; ring

lemma wirtinger_sum {s : ℂ} {ι : Type} (S : Finset ι) (G : ι → ℂ → ℂ) (d : ι → ℂ)
    (h : ∀ i ∈ S, P s (G i) (d i)) : P s (fun z => ∑ i ∈ S, G i z) (∑ i ∈ S, d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simpa using hasFDerivAt_const (0 : ℂ) s, by simp⟩
  | insert a S ha ih =>
    obtain ⟨L, hL, hd⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨M, hM, he⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨L + M, ?_, ?_⟩
    · refine (hL.add hM).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      simp [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha, ← hd, ← he]; simp only [ContinuousLinearMap.add_apply]; ring

lemma wirtinger_conj_mul_pow {s : ℂ} {b : ℂ → ℂ} {b' : ℂ} (hb : HasDerivAt b b' s) (j : ℕ) :
    P s (fun z => starRingEnd ℂ (b z) * z ^ j) (-2 * Complex.I * s ^ j * starRingEnd ℂ b') := by
  have h1 : HasFDerivAt (fun z => starRingEnd ℂ (b z))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) b').restrictScalars ℝ)) s :=
    Complex.conjCLE.hasFDerivAt.comp s (hb.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt (fun z : ℂ => z ^ j)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((j : ℂ) * s ^ (j - 1))).restrictScalars ℝ) s :=
    ((hasDerivAt_pow j s).hasFDerivAt.restrictScalars ℝ)
  refine ⟨_, h1.mul h2, ?_⟩
  simp
  ring

theorem wirtinger_eichler : ∀ (w : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → ∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun z : ℂ => (eichler w f (ofComplex z) - (eichler w h (ofComplex z)).map (starRingEnd ℂ) - p).eval z) L s ∧
      L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s)) := by
  intro w f h p hf hh s hs
  have he : ∀ (g : ℍ → ℂ) (z : ℂ), 0 < z.im → eichler w g (ofComplex z) =
      ∑ j ∈ Finset.range (w + 1), C ((w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w g j z) * X ^ j := by
    intro g z hz
    rw [ofComplex_apply_of_im_pos hz]
    rfl
  have hF : P s (fun z => ∑ j ∈ Finset.range (w + 1), (w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w f j z * z ^ j)
      (∑ j ∈ Finset.range (w + 1), (0 : ℂ)) :=
    wirtinger_sum _ _ _ fun j _ => wirtinger_eq_zero_of_hasDerivAt
      (((GlobalTheory.EichlerChange.hasDerivAt_ecoef w f hf j s hs).const_mul _).mul (hasDerivAt_pow j s))
  have hH : P s (fun z => ∑ j ∈ Finset.range (w + 1), starRingEnd ℂ ((w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w h j z) * z ^ j)
      (∑ j ∈ Finset.range (w + 1), -2 * Complex.I * s ^ j *
        starRingEnd ℂ ((w.choose j : ℂ) * ((h ∘ ofComplex) s * (-s) ^ (w - j)))) :=
    wirtinger_sum _ _ _ fun j _ => wirtinger_conj_mul_pow ((GlobalTheory.EichlerChange.hasDerivAt_ecoef w h hh j s hs).const_mul _) j
  obtain ⟨L, hL, hd⟩ := wirtinger_sub (wirtinger_sub hF hH) (wirtinger_eq_zero_of_hasDerivAt (Polynomial.hasDerivAt p s))
  refine ⟨L, hL.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hs] with z hz
    rw [he f z hz, he h z hz]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Polynomial.map_sum, eval_finsetSum]
  · rw [hd]
    have hb : (s - (starRingEnd ℂ) s) ^ w = ∑ j ∈ Finset.range (w + 1),
        s ^ j * (-(starRingEnd ℂ) s) ^ (w - j) * (w.choose j : ℂ) := by
      rw [sub_eq_add_neg, add_pow]
    rw [hb, Finset.mul_sum, Finset.sum_mul, Finset.sum_const_zero]
    simp only [zero_sub, sub_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, map_mul, map_natCast, map_pow, map_neg]
    ring

end GlobalTheory.EichlerDbar
end
end

