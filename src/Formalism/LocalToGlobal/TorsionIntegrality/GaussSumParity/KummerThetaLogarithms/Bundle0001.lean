module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.LetterShift
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0002
public import Formalism.FormalGroupWitt.WeightInvariance
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
public import Lemmata.GeneralBFactUpper.Imports

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExponentialSpecification
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws (constantCoeff_lgF coeff_one_lgF lgF_subst_inj lgF_funEq map_lgF
  rescale_lgF)

namespace FormalExponential

section Alg

variable {K : Type} [Field K]

theorem isUnit_coeff_one (l : ℕ) (hl : 2 ≤ l) : IsUnit (PowerSeries.coeff 1 (lgF K l)) := by
  rw [coeff_one_lgF l hl]
  exact isUnit_one

theorem expF_eq (l : ℕ) (hl : 2 ≤ l) :
    expF K l = PowerSeries.substInvOfIsUnit (lgF K l) (isUnit_coeff_one l hl) := by
  unfold expF
  rw [dite_eq_left (isUnit_coeff_one l hl)]

theorem inj (l : ℕ) (hl : 2 ≤ l) (a b : PowerSeries K) (ha : PowerSeries.constantCoeff a = 0)
    (hb : PowerSeries.constantCoeff b = 0)
    (h : PowerSeries.subst a (lgF K l) = PowerSeries.subst b (lgF K l)) : a = b :=
  lgF_subst_inj (ι := Unit) l hl a b ha hb h

theorem isMul_root {ζ : K} {l : ℕ} (hl : 2 ≤ l) (hζ : ζ ^ (l ^ 2 - 1) = 1) :
    IsMul l ζ (PowerSeries.C ζ * PowerSeries.X) := by
  refine ⟨by simp, ?_⟩
  rw [← rescale_lgF hζ hl, PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul]

theorem at_variable_C_mul_X {ι : Type} (x : ι) (ζ : K) :
    at1 x (PowerSeries.C ζ * PowerSeries.X) =
      MvPowerSeries.C ζ * (MvPowerSeries.X x : MvPowerSeries ι K) := by
  unfold at1
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X x), PowerSeries.subst_C,
    PowerSeries.subst_X (PowerSeries.HasSubst.X x)]

end Alg

section Normed

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_eq_one_of_pow {a : K} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = 1) : ‖a‖ = 1 := by
  have h1 : ‖a‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hn).1 h1

theorem norm_pow_sub_pow_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (i : ℕ) :
    ‖a ^ i - b ^ i‖ ≤ ‖a - b‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : a ^ (i + 1) - b ^ (i + 1) = a * (a ^ i - b ^ i) + (a - b) * b ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ i - b ^ i‖ ≤ 1 * ‖a - b‖ :=
            mul_le_mul ha ih (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ i ≤ ‖a - b‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _

theorem root_eq_of_norm_lt {a b : K} {N : ℕ} (hN : ‖(N : K)‖ = 1) (ha : a ^ N = 1)
    (hb : b ^ N = 1) (hab : ‖a - b‖ < 1) : a = b := by
  by_contra hne
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have na : ‖a‖ = 1 := norm_eq_one_of_pow hN0 ha
  have nb : ‖b‖ = 1 := norm_eq_one_of_pow hN0 hb
  have hS : (∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) = 0 := by
    have h := geom_sum₂_mul a b N
    rw [ha, hb, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have hT : (∑ i ∈ Finset.range N, b ^ i * b ^ (N - 1 - i)) = (N : K) * b ^ (N - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => b ^ (N - 1))]
    · simp
    · intro i hi
      have : i < N := Finset.mem_range.1 hi
      rw [← pow_add]
      congr 1
      omega
  have hD : (N : K) * b ^ (N - 1) =
      - ∑ i ∈ Finset.range N, (a ^ i - b ^ i) * b ^ (N - 1 - i) := by
    simp only [sub_mul, Finset.sum_sub_distrib, hS, hT]
    ring
  have h1 : ‖(N : K) * b ^ (N - 1)‖ = 1 := by
    rw [norm_mul, norm_pow, hN, nb, one_pow, one_mul]
  have h2 : ‖(N : K) * b ^ (N - 1)‖ ≤ ‖a - b‖ := by
    rw [hD, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul, norm_pow, nb, one_pow, mul_one]
    exact norm_pow_sub_pow_le na.le nb.le i
  rw [h1] at h2
  exact absurd hab (not_lt.2 h2)

theorem integral_X : Integral (PowerSeries.X : MvPowerSeries Unit K) := by
  intro n
  change ‖MvPowerSeries.coeff n (MvPowerSeries.X () : MvPowerSeries Unit K)‖ ≤ 1
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem ip_lgF (l : ℕ) (σ : K →+* K) (hl : 2 ≤ l) (hlK : (l : K) ≠ 0) :
    IP l σ (lgF K l : MvPowerSeries Unit K) := by
  refine ⟨constantCoeff_lgF l hl, ?_⟩
  have h1 : MvPowerSeries.map (σ.comp σ) (lgF K l : MvPowerSeries Unit K) = lgF K l :=
    map_lgF (σ.comp σ) l
  have h2 : (lgF K l : MvPowerSeries Unit K) - MvPowerSeries.C ((l : K)⁻¹) *
      frobVar (l ^ 2) (lgF K l : MvPowerSeries Unit K) = (PowerSeries.X : PowerSeries K) := by
    have h := lgF_funEq (K := K) l hl hlK
    rw [PowerSeries.smul_eq_C_mul] at h
    exact h
  rw [h1, h2]
  exact integral_X

end Normed

end FormalExponential

open FormalExponential

theorem exponential_specification : ExpSpec := by
  intro K _ l hl
  have h0 := constantCoeff_lgF (K := K) l hl
  have hc : PowerSeries.constantCoeff (expF K l) = 0 := by
    rw [expF_eq l hl]
    exact PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have h1 : PowerSeries.subst (expF K l) (lgF K l) = (PowerSeries.X : PowerSeries K) := by
    rw [expF_eq l hl]
    exact PowerSeries.subst_substInvOfIsUnit_right _ h0 _
  refine ⟨hc, h1, ?_, ?_⟩
  · rw [expF_eq l hl]
    exact PowerSeries.subst_substInvOfIsUnit_left _ h0 _
  · intro ex hex h
    exact inj l hl ex _ hex hc (h.trans h1.symm)

theorem teichmuller_sigma : TeichSigma := by
  intro K _ _ _ l d σ hU hd ζ hζ
  obtain ⟨hp, _, hnl, _, hσ⟩ := hU
  have hlt : ‖(l : K)‖ < 1 := by
    rw [hnl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hpos : 1 ≤ l ^ d := Nat.one_le_pow _ _ hp.pos
  have hnd : ¬ l ∣ l ^ d - 1 := by
    intro h
    have h1 : l ∣ l ^ d := dvd_pow_self l (by omega)
    have h2 : l ∣ 1 := by
      have := (Nat.dvd_sub h1 h)
      rwa [Nat.sub_sub_self hpos] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN : ‖((l ^ d - 1 : ℕ) : K)‖ = 1 := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hnd
  have hN0 : l ^ d - 1 ≠ 0 := by
    intro h
    rw [h] at hnd
    exact hnd (dvd_zero l)
  have nζ : ‖ζ‖ = 1 := norm_eq_one_of_pow hN0 hζ
  refine root_eq_of_norm_lt hN ?_ ?_ ?_
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  · refine lt_of_le_of_lt (hσ ζ nζ.le) ?_
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem MulSpec_of : ExpSpec → IPLemma → IPClosure → MulSpec := by
  intro hE hL hC K _ _ _ l σ hU c
  have hp : l.Prime := hU.1
  have hl : 2 ≤ l := hp.two_le
  have hlK : (l : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hc, h1, _, _⟩ := hE K l hl
  have h0 := constantCoeff_lgF (K := K) l hl
  have huniq : ∀ e e' : PowerSeries K, IsMul l c e → IsMul l c e' → e = e' := fun e e' he he' =>
    inj l hl e e' he.1 he'.1 (he.2.trans he'.2.symm)
  refine ⟨?_, huniq, ?_⟩
  · have hg0 : PowerSeries.constantCoeff (PowerSeries.C c * lgF K l) = 0 := by
      rw [map_mul, h0, mul_zero]
    refine ⟨PowerSeries.subst (PowerSeries.C c * lgF K l) (expF K l),
      PowerSeries.constantCoeff_subst_eq_zero hg0 _ hc, ?_⟩
    rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hc)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hg0), h1,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hg0)]
  · intro hc1 hσc e he n
    have hip : IP l σ (MvPowerSeries.C c * (lgF K l : MvPowerSeries Unit K)) :=
      (hC K l σ Unit).2.2 c _ hc1 hσc (ip_lgF l σ hl hlK)
    obtain ⟨h, hh0, hhI, hh⟩ := hL K l σ hU Unit _ hip
    have : e = h := huniq e h he ⟨hh0, hh⟩
    rw [this]
    exact hhI (Finsupp.single () n)

theorem BetaHypOfF_of : TeichSigma → BetaHypOfF := by
  intro hT K _ _ _ l σ hU F be0 hF1 hF2
  have hp : l.Prime := hU.1
  have hl : 2 ≤ l := hp.two_le
  refine ⟨hF1.1, hF1.2.1, hF1.2.2, ?_⟩
  intro ζ hζ
  have hN0 : l ^ 2 - 1 ≠ 0 := by
    have : 2 ^ 2 ≤ l ^ 2 := Nat.pow_le_pow_left hl 2
    omega
  have nζ : ‖ζ‖ = 1 := norm_eq_one_of_pow hN0 hζ
  have hσ : σ ζ = ζ ^ l := hT K l 2 σ hU (by norm_num) ζ hζ
  have hζl : (ζ ^ l) ^ (l ^ 2 - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσ, map_pow, hσ, ← pow_mul, ← sq]
    have : l ^ 2 = (l ^ 2 - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  have h := hF2 ζ nζ.le hσσ (PowerSeries.C ζ * PowerSeries.X)
    (PowerSeries.C (ζ ^ l) * PowerSeries.X) (isMul_root hl hζ) (by rw [hσ]; exact isMul_root hl hζl)
  rw [at_variable_C_mul_X, at_variable_C_mul_X] at h
  exact h

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IpNormPowSubPowLe
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK frobVar frobVar_eq_expand)

theorem ip_norm_pow_sub_pow_le {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  first | exact Bl.general_b_fact_upper.goal1 .. | (apply Bl.general_b_fact_upper.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y hx hy n | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y hx hy | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y hx | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› | exact @Bl.general_b_fact_upper.goal1 K ‹_› | exact @Bl.general_b_fact_upper.goal1 K

theorem frobenius_square : FrobSq := by
  intro K _ _ _ l σ h
  obtain ⟨hl, _, hn, _, hσ⟩ := h
  have hl1 : ((l : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_le)
  have hball : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := by
    intro a ha
    have h : σ a = (σ a - a ^ l) + a ^ l := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hσ a ha).trans hl1) ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha
  refine ⟨⟨hl, ⟨2, by norm_num, rfl⟩, ?_, ?_⟩, hball⟩
  · rw [hn]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  · intro a ha
    rw [hn]
    have h : (σ.comp σ) a - a ^ (l ^ 2) =
        (σ (σ a) - (σ a) ^ l) + ((σ a) ^ l - (a ^ l) ^ l) := by
      rw [RingHom.comp_apply, pow_two, pow_mul]
      ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hσ _ (hball a ha)) ?_)
    exact (ip_norm_pow_sub_pow_le (hball a ha)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha) l).trans (hσ a ha)

section Closure

variable {K : Type} [NormedField K] {τ : Type}

theorem ip_integral_add [IsUltrametricDist K] {f g : MvPowerSeries τ K} (hf : Integral f)
    (hg : Integral g) : Integral (f + g) := fun n => by
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem ip_integral_C_mul {c : K} {g : MvPowerSeries τ K} (hc : ‖c‖ ≤ 1) (hg : Integral g) :
    Integral (MvPowerSeries.C c * g) := fun n => by
  rw [MvPowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hg n)

theorem ip_op_zero (l : ℕ) (σ : K →+* K) :
    MvPowerSeries.C ((l : K)⁻¹) *
      frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (0 : MvPowerSeries τ K)) = 0 := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · have hq : l ^ 2 ≠ 0 := by positivity
    rw [frobVar_eq_expand hq, map_zero, map_zero, mul_zero]

theorem ip_op_add (l : ℕ) (σ : K →+* K) (g g' : MvPowerSeries τ K) :
    MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (g + g')) =
      MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) g) +
      MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) g') := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · have hq : l ^ 2 ≠ 0 := by positivity
    rw [frobVar_eq_expand hq, frobVar_eq_expand hq, frobVar_eq_expand hq, map_add (f := _), map_add (f := _),
      mul_add]

theorem ip_op_C_mul (l : ℕ) (σ : K →+* K) (c : K) (g : MvPowerSeries τ K) :
    MvPowerSeries.C ((l : K)⁻¹) *
        frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (MvPowerSeries.C c * g)) =
      MvPowerSeries.C (σ (σ c)) *
        (MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) g)) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · have hq : l ^ 2 ≠ 0 := by positivity
    rw [frobVar_eq_expand hq, frobVar_eq_expand hq, map_mul, MvPowerSeries.map_C, map_mul,
      MvPowerSeries.expand_C, RingHom.comp_apply]
    ring

end Closure

theorem integral_part_closure : IPClosure := by
  intro K _ _ _ l σ τ _
  refine ⟨⟨map_zero _, ?_⟩, ?_, ?_⟩
  · rw [ip_op_zero, sub_zero]
    intro n
    simp
  · rintro g g' ⟨h0, hI⟩ ⟨h0', hI'⟩
    refine ⟨by rw [map_add (f := _), h0, h0', add_zero], ?_⟩
    rw [ip_op_add, add_sub_add_comm]
    exact ip_integral_add hI hI'
  · rintro c g hc hσ ⟨h0, hI⟩
    refine ⟨by rw [map_mul, h0, mul_zero], ?_⟩
    rw [ip_op_C_mul, hσ, ← mul_sub]
    exact ip_integral_C_mul hc hI

theorem ip_map_lgF {K : Type} [Field K] (l : ℕ) (φ : K →+* K) :
    MvPowerSeries.map φ (lgF K l : MvPowerSeries Unit K) = lgF K l := by
  change PowerSeries.map φ (lgF K l) = lgF K l
  ext n
  rw [PowerSeries.coeff_map]
  unfold lgF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [map_inv₀, map_pow, map_natCast]
  · rw [map_zero]

theorem ip_expand_congr {K τ : Type} [Field K] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b)
    (f : MvPowerSeries τ K) : MvPowerSeries.expand a ha f = MvPowerSeries.expand b hb f := by
  subst h
  rfl

theorem ip_lgF_funEq {K : Type} [Field K] {l : ℕ} (hl : 2 ≤ l) (hlK : (l : K) ≠ 0)
    (hq : l ^ 2 ≠ 0) :
    (lgF K l : MvPowerSeries Unit K) -
      (l : K)⁻¹ • MvPowerSeries.expand (l ^ 2) hq (lgF K l : MvPowerSeries Unit K) =
      MvPowerSeries.X () := by
  have hl0 : l ≠ 0 := by omega
  obtain ⟨h1, h2⟩ := Formalism.InvariantFactorPaths.G7.g_zero_relation_holds K l hl hlK
  have e : ∀ f : PowerSeries K, (PowerSeries.subst (PowerSeries.X ^ l : PowerSeries K) f :
      PowerSeries K) = MvPowerSeries.expand l hl0 (f : MvPowerSeries Unit K) :=
    fun f => frobVar_eq_expand hl0 (f : MvPowerSeries Unit K)
  rw [h1, e, e] at h2
  have h3 : MvPowerSeries.expand l hl0 ((MvPowerSeries.C ((l : K)⁻¹) : MvPowerSeries Unit K) *
      MvPowerSeries.expand l hl0 (lgF K l : MvPowerSeries Unit K)) =
      (lgF K l : MvPowerSeries Unit K) - MvPowerSeries.X () := h2
  rw [map_mul, MvPowerSeries.expand_C, ← MvPowerSeries.expand_mul,
    ip_expand_congr (Nat.mul_ne_zero hl0 hl0) hq (pow_two l).symm,
    ← MvPowerSeries.smul_eq_C_mul] at h3
  rw [h3]
  ring

theorem IPLemma_of : FrobSq → IPLemma := by
  intro hF K _ _ _ l σ h τ _ g hg
  obtain ⟨hset, _⟩ := hF K l σ h
  have hl : l.Prime := h.1
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.ne_zero
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hid : Formalism.FG.IsIdMod2 (fun _ : Unit => (lgF K l : MvPowerSeries Unit K)) := by
    refine ⟨fun _ => ?_, fun j i => ?_⟩
    · by_contra hc
      have hc' : PowerSeries.coeff 0 (lgF K l) ≠ 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff]
        exact hc
      obtain ⟨j, hj⟩ := Formalism.InvariantFactorPaths.G7.coeff_lgF_ne_zero hc'
      exact (pow_ne_zero j hq) hj.symm
    · have h1 := Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl.two_le 0
      simp only [pow_zero, inv_one] at h1
      rw [if_pos (Subsingleton.elim i j)]
      exact h1
  have hf : Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (fun _ _ : Unit => (1 : K))
      (fun _ : Unit => (lgF K l : MvPowerSeries Unit K)) := by
    intro _
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    rw [ip_map_lgF, ip_lgF_funEq hl.two_le hlK hq]
    intro d
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  have hgt : Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (fun _ _ : Unit => (1 : K))
      (fun _ : Unit => g) := by
    intro _
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    rw [MvPowerSeries.smul_eq_C_mul, ← frobVar_eq_expand hq]
    exact hg.2
  obtain ⟨hh, h0, hI, hs⟩ := Formalism.FG.funEqHomV K l (l ^ 2) hq (σ.comp σ) hset Unit
    (fun _ _ => 1) (fun _ _ => by simp) (fun _ => lgF K l) hid hf τ (fun _ => g)
    (fun _ => hg.1) hgt
  exact ⟨hh (), h0 (), hI (), hs ()⟩

theorem integral_part_lemma : IPLemma := IPLemma_of frobenius_square

end Formalism.L2.Th1.D
end
end

