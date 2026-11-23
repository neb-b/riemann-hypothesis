module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitSolutionTwistedFrobeniusSquare
section
namespace GlobalTheory.Honda

theorem unitFix_subMax {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

theorem unitFix_powSub {K : Type} [NormedField K] [IsUltrametricDist K] (a b : K) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) (hab : ‖a - b‖ < 1) : ∀ n : ℕ, ‖a ^ n - b ^ n‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one
  | exact _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one
  | (apply _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one ..)

theorem unitFix_sq_apply {K : Type} [NormedField K] (σ : K →+* K) (x : K) : (σ ^ 2) x = σ (σ x) := by
  rw [pow_two]; rfl

theorem unitFix_frob2 {K : Type} [NormedField K] [IsUltrametricDist K] (l : ℕ) (σ : K →+* K) (hU : Unr K l σ)
    (x : K) (hx : ‖x‖ ≤ 1) : ‖(σ ^ 2) x - x ^ (l ^ 2)‖ < 1 := by
  obtain ⟨_, _, _, _, hiso, hfr⟩ := hU
  have hsx : ‖σ x‖ ≤ 1 := by rw [hiso]; exact hx
  have h1 := hfr (σ x) hsx
  have h2 : ‖(σ x) ^ l - (x ^ l) ^ l‖ < 1 :=
    unitFix_powSub _ _ hsx (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx) (hfr x hx) l
  have hq : x ^ (l ^ 2) = (x ^ l) ^ l := by rw [← pow_mul, sq]
  have e2 : σ (σ x) - x ^ (l ^ 2) = (σ (σ x) - σ x ^ l) + ((σ x) ^ l - (x ^ l) ^ l) := by rw [hq]; ring
  rw [unitFix_sq_apply, e2]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

theorem unitFix_root {K : Type} [NormedField K] [IsUltrametricDist K] (hR : ResAlg K) (m : ℕ) (hm : 2 ≤ m)
    (a b : K) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ∃ y : K, ‖y‖ ≤ 1 ∧ ‖y ^ m - a * y - b‖ < 1 := by
  classical
  have hdeg : (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree
      < (Polynomial.X ^ m : Polynomial K).natDegree := by
    rw [Polynomial.natDegree_X_pow]; exact lt_of_le_of_lt Polynomial.natDegree_linear_le (by omega)
  have hmon : (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).Monic :=
    (Polynomial.monic_X_pow m).sub_of_left (Polynomial.degree_lt_degree hdeg)
  have hnd : 0 < (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).natDegree := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg, Polynomial.natDegree_X_pow]; omega
  have hco : ∀ n, ‖(Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).coeff n‖ ≤ 1 := by
    intro n
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C]
    refine (unitFix_subMax _ _).trans
      (max_le ?_ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
    · split_ifs <;> simp
    · split_ifs <;> simp [ha]
    · split_ifs <;> simp [hb]
  obtain ⟨y, hy, hev⟩ := hR _ hmon hnd hco
  refine ⟨y, hy, ?_⟩
  have e : (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).eval y = y ^ m - a * y - b := by
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    ring
  rwa [e] at hev

theorem unitFix_step {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K)
    (hU : Unr K l σ) (hR : ResAlg K) (c : K) (hc : ‖c‖ = 1) (n : ℕ) (ε : K)
    (hε : ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n) :
    ∃ η : K, ‖η‖ ≤ ‖(l : K)‖ ^ n ∧ ‖(ε + η) - c * (σ ^ 2) (ε + η)‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
  have hU' := hU
  obtain ⟨hp, h2, hl1, hdisc, hiso, hfr⟩ := hU'
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hπ0 : (l : K) ^ n ≠ 0 := pow_ne_zero _ hl0
  have hπn : ‖(l : K) ^ n‖ = ‖(l : K)‖ ^ n := norm_pow _ _
  have hπpos : 0 < ‖(l : K) ^ n‖ := norm_pos_iff.mpr hπ0
  have hbn : ‖(ε - c * (σ ^ 2) ε) / (l : K) ^ n‖ ≤ 1 := by
    rw [norm_div, div_le_one hπpos, hπn]; exact hε
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hq : 2 ≤ l ^ 2 := le_trans (by omega : 2 ≤ l) (Nat.le_self_pow (by norm_num) l)
  obtain ⟨y, hy, hroot⟩ := unitFix_root hR (l ^ 2) hq c⁻¹ (c⁻¹ * ((ε - c * (σ ^ 2) ε) / (l : K) ^ n)) hci.le
    (by rw [norm_mul, hci, one_mul]; exact hbn)
  have hfy := unitFix_frob2 l σ hU y hy
  have hσπ : (σ ^ 2) ((l : K) ^ n) = (l : K) ^ n := by rw [map_pow, map_natCast]
  refine ⟨(l : K) ^ n * y, ?_, ?_⟩
  · rw [norm_mul, ← hπn]; exact mul_le_of_le_one_right (norm_nonneg _) hy
  · set b : K := (ε - c * (σ ^ 2) ε) / (l : K) ^ n with hb
    have e : (ε + (l : K) ^ n * y) - c * (σ ^ 2) (ε + (l : K) ^ n * y)
        = (l : K) ^ n * (b + y - c * y ^ (l ^ 2) + c * (y ^ (l ^ 2) - (σ ^ 2) y)) := by
      rw [map_add (f := _), map_mul, hσπ, hb]; field_simp; ring
    have e2 : b + y - c * y ^ (l ^ 2) = -c * (y ^ (l ^ 2) - c⁻¹ * y - c⁻¹ * b) := by field_simp; ring
    have hlt : ‖b + y - c * y ^ (l ^ 2) + c * (y ^ (l ^ 2) - (σ ^ 2) y)‖ < 1 := by
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [e2, norm_mul, norm_neg, hc, one_mul]; exact hroot
      · rw [norm_mul, hc, one_mul, ← norm_neg, neg_sub]; exact hfy
    rw [e, norm_mul, hπn, pow_succ]
    exact mul_le_mul_of_nonneg_left (hdisc _ hlt) (pow_nonneg (norm_nonneg _) _)

theorem unitFix_init {K : Type} [NormedField K] [IsUltrametricDist K] (l : ℕ) (σ : K →+* K)
    (hU : Unr K l σ) (hR : ResAlg K) (c : K) (hc : ‖c‖ = 1) :
    ∃ ε : K, ‖ε‖ = 1 ∧ ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ 1 := by
  have hU' := hU
  obtain ⟨hp, h2, hl1, hdisc, hiso, hfr⟩ := hU'
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hq : 4 ≤ l ^ 2 := by nlinarith
  obtain ⟨m, hm⟩ : ∃ m, l ^ 2 = m + 1 := ⟨l ^ 2 - 1, by omega⟩
  have hm2 : 2 ≤ m := by omega
  obtain ⟨x, hx, hroot⟩ := unitFix_root hR m hm2 0 c⁻¹ (by simp) hci.le
  simp only [zero_mul, sub_zero] at hroot
  have hx1 : ‖x‖ = 1 := by
    refine le_antisymm hx (not_lt.mp fun hlt => ?_)
    have hxm : ‖x ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hlt (by omega)
    have : ‖c⁻¹‖ < 1 := by
      have e : c⁻¹ = x ^ m - (x ^ m - c⁻¹) := by ring
      rw [e]; exact lt_of_le_of_lt (unitFix_subMax _ _) (max_lt hxm hroot)
    rw [hci] at this; exact lt_irrefl _ this
  refine ⟨x, hx1, ?_⟩
  have hfx := unitFix_frob2 l σ hU x hx
  have e : x - c * (σ ^ 2) x = -(c * x) * (x ^ m - c⁻¹) + c * (x ^ (l ^ 2) - (σ ^ 2) x) := by
    rw [hm, pow_succ]; field_simp; ring
  rw [pow_one]
  apply hdisc
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]; exact hroot
  · rw [norm_mul, hc, one_mul, ← norm_neg, neg_sub]; exact hfx

theorem unit_solution_twisted_frobenius : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    [CompleteSpace K] (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ c : K, ‖c‖ = 1 →
    ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * (σ ^ 2) ε := by
  intro K _ _ _ _ l σ hU hR c hc
  have hU' := hU
  obtain ⟨hp, h2, hl1, hdisc, hiso, hfr⟩ := hU'
  obtain ⟨ε0, hε0n, hε0⟩ := unitFix_init l σ hU hR c hc
  have hstep : ∀ (n : ℕ) (ε : K), ∃ η : K, ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n →
      ‖η‖ ≤ ‖(l : K)‖ ^ n ∧ ‖(ε + η) - c * (σ ^ 2) (ε + η)‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
    intro n ε
    by_cases h : ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n
    · obtain ⟨η, h1⟩ := unitFix_step l σ hU hR c hc n ε h
      exact ⟨η, fun _ => h1⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose g hg using hstep
  let e : ℕ → K := fun k => Nat.rec ε0 (fun k x => x + g (k + 1) x) k
  have he0 : e 0 = ε0 := rfl
  have hes : ∀ k, e (k + 1) = e k + g (k + 1) (e k) := fun k => rfl
  have hpow : ∀ k : ℕ, ‖(l : K)‖ ^ (k + 1) < 1 := fun k => pow_lt_one₀ (norm_nonneg _) hl1 (by omega)
  have hinv : ∀ k, ‖e k‖ = 1 ∧ ‖e k - c * (σ ^ 2) (e k)‖ ≤ ‖(l : K)‖ ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨he0 ▸ hε0n, by rw [he0]; simpa using hε0⟩
    | succ k ih =>
      obtain ⟨hη, herr⟩ := hg (k + 1) (e k) ih.2
      refine ⟨?_, by rw [hes]; exact herr⟩
      have hlt : ‖g (k + 1) (e k)‖ < ‖e k‖ := by rw [ih.1]; exact lt_of_le_of_lt hη (hpow k)
      rw [hes, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, ih.1]
  have hcs : CauchySeq e := by
    refine cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 (fun k => ?_)
    rw [dist_eq_norm, hes, sub_add_cancel_left, norm_neg, ← pow_succ']
    exact (hg (k + 1) (e k) (hinv k).2).1
  obtain ⟨ε, hlim⟩ := cauchySeq_tendsto_of_complete hcs
  have hτc : Continuous (fun x : K => (σ ^ 2) x) := AddMonoidHomClass.continuous_of_bound (σ ^ 2) 1 (fun x => by
    rw [one_mul, unitFix_sq_apply, hiso, hiso])
  have hcont : Continuous (fun x : K => x - c * (σ ^ 2) x) := continuous_id.sub (continuous_const.mul hτc)
  have h1 : Filter.Tendsto (fun k => e k - c * (σ ^ 2) (e k)) Filter.atTop (nhds (ε - c * (σ ^ 2) ε)) :=
    (hcont.tendsto ε).comp hlim
  have h0 : Filter.Tendsto (fun k => e k - c * (σ ^ 2) (e k)) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun k => (hinv k).2)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1).comp (Filter.tendsto_add_atTop_nat 1))
  have heq : ε - c * (σ ^ 2) ε = 0 := tendsto_nhds_unique h1 h0
  refine ⟨ε, ?_, sub_eq_zero.mp heq⟩
  have hn : Filter.Tendsto (fun k => ‖e k‖) Filter.atTop (nhds ‖ε‖) := (continuous_norm.tendsto ε).comp hlim
  have hfun : (fun k => ‖e k‖) = fun _ => (1 : ℝ) := funext fun k => (hinv k).1
  rw [hfun] at hn
  exact tendsto_nhds_unique hn tendsto_const_nhds

end GlobalTheory.Honda
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoHondaTypeFirstCoeffNormEqOne
section
open PowerSeries GlobalTheory.Honda

noncomputable section

namespace GlobalTheory.Honda.HeightTwo

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_natCast_coprime_eq_one (l u : ℕ) (hp : l.Prime) (hl1 : ‖(l : K)‖ < 1) (hu : ¬ l ∣ u) :
    ‖(u : K)‖ = 1 := by
  have hcop : Nat.Coprime u l := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K u) (not_lt.mp fun h => ?_)
  have hb := Nat.gcd_eq_gcd_ab u l
  rw [hcop.gcd_eq_one] at hb
  have hK := congrArg (fun z : ℤ => (z : K)) hb
  push_cast at hK
  have h1 : ‖(u : K) * (Nat.gcdA u l : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(u : K)‖ * ‖(Nat.gcdA u l : K)‖ ≤ ‖(u : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one K _) (norm_nonneg _)
      _ < 1 := by simpa using h
  have h2 : ‖(l : K) * (Nat.gcdB u l : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖(Nat.gcdB u l : K)‖ ≤ ‖(l : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one K _) (norm_nonneg _)
      _ < 1 := by simpa using hl1
  have h3 := IsUltrametricDist.norm_add_le_max ((u : K) * (Nat.gcdA u l : K)) ((l : K) * (Nat.gcdB u l : K))
  rw [← hK, norm_one] at h3
  exact absurd h3 (not_le.mpr (max_lt h1 h2))

theorem pow_le_norm_natCast (l : ℕ) (hp : l.Prime) (hl1 : ‖(l : K)‖ < 1) (k : ℕ) (hk : 1 ≤ k) :
    ‖(l : K)‖ ^ (k - 1) ≤ ‖(k : K)‖ := by
  obtain ⟨v, u, hu, hkv⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : k ≠ 0) l hp.one_lt.ne'
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero l)
  have hvk : v ≤ k - 1 := by
    have h1 : v < l ^ v := Nat.lt_pow_self hp.one_lt
    have h2 : l ^ v ≤ k := by rw [hkv]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
    omega
  have hn : ‖(k : K)‖ = ‖(l : K)‖ ^ v := by
    rw [hkv]; push_cast
    rw [norm_mul, norm_pow, norm_natCast_coprime_eq_one l u hp hl1 hu, mul_one]
  rw [hn]
  exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le hvk

theorem coeff_mul_pow_le (l : ℕ) (hp : l.Prime) (hl1 : ‖(l : K)‖ < 1) (f : K⟦X⟧)
    (hder : CoefLe 1 (derivative f)) (k : ℕ) (hk : 1 ≤ k) :
    ‖coeff k f‖ * ‖(l : K)‖ ^ k ≤ ‖(l : K)‖ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hd := hder k'
  rw [coeff_derivative, norm_mul] at hd
  have hle := pow_le_norm_natCast l hp hl1 (k' + 1) hk
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hle
  calc ‖coeff (k' + 1) f‖ * ‖(l : K)‖ ^ (k' + 1)
      = (‖coeff (k' + 1) f‖ * ‖(l : K)‖ ^ k') * ‖(l : K)‖ := by ring
    _ ≤ 1 * ‖(l : K)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (mul_le_mul_of_nonneg_left hle (norm_nonneg _)).trans hd
    _ = ‖(l : K)‖ := one_mul _

theorem norm_coeff_pow_le (g : K⟦X⟧) (r : ℝ) (m : ℕ) (hr : 0 ≤ r) (hg : ∀ j ≤ m, ‖coeff j g‖ ≤ r) :
    ∀ k j, j ≤ m → ‖coeff j (g ^ k)‖ ≤ r ^ k := by
  intro k
  induction k with
  | zero =>
    intro j _
    rw [pow_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    intro j hj
    rw [pow_succ', coeff_mul, pow_succ']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [norm_mul]
    exact mul_le_mul (hg _ (by omega)) (ih _ (by omega)) (norm_nonneg _) hr

theorem norm_coeff_succ_pow_le (g : K⟦X⟧) (hg0 : constantCoeff g = 0) (r : ℝ) (m : ℕ) (hr : 0 ≤ r)
    (hg : ∀ j ≤ m, ‖coeff j g‖ ≤ r) (k : ℕ) :
    ‖coeff (m + 1) (g ^ (k + 2))‖ ≤ r ^ (k + 2) := by
  rw [pow_succ' g (k + 1), coeff_mul, pow_succ' r (k + 1)]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases ha : p.1 = 0
  · rw [ha, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, norm_zero]; positivity
  by_cases hb : p.2 = 0
  · rw [hb, coeff_zero_eq_constantCoeff_apply, map_pow, hg0, zero_pow (by omega), mul_zero, norm_zero]
    positivity
  rw [norm_mul]
  exact mul_le_mul (hg _ (by omega)) (norm_coeff_pow_le g r m hr hg _ _ (by omega)) (norm_nonneg _) hr

theorem coeff_subst_eq_sum (f g : K⟦X⟧) (hg0 : constantCoeff g = 0) (n : ℕ) :
    coeff n (subst g f) = ∑ d ∈ Finset.range (n + 1), coeff d f * coeff n (g ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg0)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hdn
    apply hd
    obtain ⟨g', rfl⟩ := X_dvd_iff.mpr hg0
    simp only [mul_pow, coeff_X_pow_mul', if_neg (by omega : ¬ d ≤ n), smul_zero]

theorem norm_coeff_le_of_subst (f g : K⟦X⟧) (ρ : ℝ) (hρ : 0 ≤ ρ) (hf0 : coeff 0 f = 0) (hf1 : coeff 1 f = 1)
    (hf : ∀ k, 1 ≤ k → ‖coeff k f‖ * ρ ^ k ≤ ρ) (hg0 : constantCoeff g = 0) (N : ℕ)
    (hy : ∀ n ≤ N, ‖coeff n (subst g f)‖ ≤ ρ) : ∀ n ≤ N, ‖coeff n g‖ ≤ ρ := by
  have key : ∀ m, m ≤ N → ∀ j ≤ m, ‖coeff j g‖ ≤ ρ := by
    intro m
    induction m with
    | zero =>
      intro _ j hj
      rw [Nat.le_zero.mp hj, coeff_zero_eq_constantCoeff_apply, hg0, norm_zero]; exact hρ
    | succ m ih =>
      intro hm j hj
      rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
      · exact ih (by omega) j (by omega)
      obtain rfl : j = m + 1 := by omega
      have ih' := ih (by omega)
      have hs := coeff_subst_eq_sum f g hg0 (m + 1)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : 1 < m + 1 + 1)), hf1, pow_one,
        one_mul] at hs
      have hrest : ‖∑ d ∈ (Finset.range (m + 1 + 1)).erase 1, coeff d f * coeff (m + 1) (g ^ d)‖ ≤ ρ := by
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hρ fun d hd => ?_
        have hd1 := Finset.ne_of_mem_erase hd
        rcases Nat.lt_or_ge d 2 with hd2 | hd2
        · obtain rfl : d = 0 := by omega
          rw [hf0, zero_mul, norm_zero]; exact hρ
        obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
        rw [norm_mul]
        calc ‖coeff (k + 2) f‖ * ‖coeff (m + 1) (g ^ (k + 2))‖ ≤ ‖coeff (k + 2) f‖ * ρ ^ (k + 2) :=
              mul_le_mul_of_nonneg_left (norm_coeff_succ_pow_le g hg0 ρ m hρ ih' k) (norm_nonneg _)
          _ ≤ ρ := hf _ (by omega)
      have hgm : coeff (m + 1) g = coeff (m + 1) (subst g f) -
          ∑ d ∈ (Finset.range (m + 1 + 1)).erase 1, coeff d f * coeff (m + 1) (g ^ d) := by
        rw [hs]; ring
      rw [hgm, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy _ hm) ?_)
      rwa [norm_neg]
  exact fun n hn => key n hn n le_rfl

theorem norm_coeff_hondaSum_le (τ : K →+* K) (q : ℕ) (hq : 2 ≤ q) (c : ℕ → K) (f : K⟦X⟧) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hc0 : ‖c 0‖ ≤ ρ) (hf1 : coeff 1 f = 1) (n : ℕ) (hn : n ≤ q) :
    ‖coeff n (hondaSum τ q c f)‖ ≤ ρ := by
  unfold hondaSum
  rw [coeff_mk]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hρ fun j hj => ?_
  have hjn := Finset.mem_range.mp hj
  unfold frobOp
  rw [coeff_subst_X_pow (pow_ne_zero _ (by omega))]
  split_ifs with hdvd
  · have hle := Nat.le_of_dvd (by omega) hdvd
    have hqq : q < q ^ 2 := by rw [sq]; nlinarith
    have hj0 : j = 0 := by
      by_contra hj0
      have : q ^ 2 ≤ q ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    subst hj0
    have hnq : n = q := by rw [zero_add, pow_one] at hle; omega
    subst hnq
    simpa [Nat.div_self (by omega : 0 < n), coeff_map, hf1] using hc0
  · rw [mul_zero, norm_zero]; exact hρ

theorem norm_first_coeff_eq_one : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ)
    (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) →
    CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) →
    (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) → ‖c 0‖ = 1 := by
  intro K _ _ _ l σ hU f e hIL c hc hH hex
  obtain ⟨hp, hl2, hl1, hmax, -, -⟩ := hU
  obtain ⟨⟨hf0, hf1, he0, -, hef⟩, hder, -⟩ := hIL
  have hρ : 0 ≤ ‖(l : K)‖ := norm_nonneg _
  by_contra hne
  have hc0 : ‖c 0‖ ≤ ‖(l : K)‖ := hmax _ (lt_of_le_of_ne (hc 0) hne)
  have hf0' : coeff 0 f = 0 := by rw [coeff_zero_eq_constantCoeff_apply, hf0]
  have hlf0 : constantCoeff (C (l : K) * f) = 0 := by simp [hf0]
  have hg0 : constantCoeff (Formalism.L2.Th1.C.mulBy f e (l : K)) = 0 := by
    unfold Formalism.L2.Th1.C.mulBy
    exact constantCoeff_subst_eq_zero hlf0 e he0
  have hfg : subst (Formalism.L2.Th1.C.mulBy f e (l : K)) f = C (l : K) * f := by
    unfold Formalism.L2.Th1.C.mulBy
    rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' he0)
      (HasSubst.of_constantCoeff_zero' hlf0), hef, subst_X (HasSubst.of_constantCoeff_zero' hlf0)]
  have hy : ∀ n ≤ l ^ 2, ‖coeff n (subst (Formalism.L2.Th1.C.mulBy f e (l : K)) f)‖ ≤ ‖(l : K)‖ := by
    intro n hn
    rw [hfg]
    have h1 := hH n
    have h2 := norm_coeff_hondaSum_le (σ ^ 2) (l ^ 2) (by nlinarith) c f _ hρ hc0 hf1 n hn
    have : coeff n (C (l : K) * f) = coeff n (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) +
        coeff n (hondaSum (σ ^ 2) (l ^ 2) c f) := by rw [map_sub]; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  have hg := norm_coeff_le_of_subst f _ _ hρ hf0' hf1 (coeff_mul_pow_le l hp hl1 f hder) hg0 _ hy
  obtain ⟨n, hn, hn1⟩ := hex
  have := hg n hn
  linarith

end GlobalTheory.Honda.HeightTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LazardBinomialNormUltrametric
section
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda.Lazard

theorem norm_natCast_eq_one_of_not_dvd {K : Type} [NormedField K] [IsUltrametricDist K] {l m : ℕ}
    (hp : l.Prime) (hl : ‖(l : K)‖ < 1) (hm : ¬ l ∣ m) : ‖(m : K)‖ = 1 := by
  have hcop : IsCoprime (l : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (u : K) * l + v * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huv
  have hu : ‖(u : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K u
  have hv : ‖(v : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K v
  have hmle : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  refine le_antisymm hmle ?_
  by_contra hlt
  push_neg at hlt
  have h2 : ‖(1 : K)‖ ≤ max ‖(u : K) * l‖ ‖(v : K) * m‖ := by
    rw [← h1]; exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_one, norm_mul, norm_mul] at h2
  have ha : ‖(u : K)‖ * ‖(l : K)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hu) hl
  have hb : ‖(v : K)‖ * ‖(m : K)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hv) hlt
  exact absurd h2 (not_le.2 (max_lt ha hb))

theorem not_dvd_choose_pow_mul {l : ℕ} (hp : l.Prime) (m : ℕ) (hm : ¬ l ∣ m) :
    ∀ v : ℕ, ¬ l ∣ (l ^ v * m).choose (l ^ v) := by
  haveI := Fact.mk hp
  intro v
  induction v with
  | zero => simpa using hm
  | succ v ih =>
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (l ^ (v + 1) * m) (l ^ (v + 1)) l _
    have e1 : l ^ (v + 1) * m = l * (l ^ v * m) := by ring
    have e2 : l ^ (v + 1) = l * l ^ v := by ring
    rw [e1, e2, Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hp.pos, Nat.choose_zero_right, one_mul] at h
    rw [e1, e2]
    intro hd
    exact ih ((Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd))))

theorem choose_prime_pow_pred {l : ℕ} (hp : l.Prime) (i : ℕ) (hi : 0 < i) :
    ∃ m : ℕ, ¬ l ∣ m ∧ (l ^ i).choose (l ^ (i - 1)) = l * m := by
  have hle : l ^ (i - 1) ≤ l ^ i := Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)
  have h := hp.emultiplicity_choose_prime_pow_add_emultiplicity hle (pow_ne_zero _ hp.ne_zero)
  rw [emultiplicity_pow_self_of_prime hp.prime] at h
  have h1 : emultiplicity l ((l ^ i).choose (l ^ (i - 1))) = ((1 : ℕ) : ℕ∞) := by
    have : ((i : ℕ) : ℕ∞) = ((1 : ℕ) : ℕ∞) + ((i - 1 : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [this] at h
    exact WithTop.add_right_cancel (ENat.coe_ne_top _) h
  rw [emultiplicity_eq_coe] at h1
  obtain ⟨⟨m, hm⟩, hn⟩ := h1
  refine ⟨m, ?_, by simpa using hm⟩
  rintro ⟨c, rfl⟩
  apply hn
  exact ⟨c, by rw [hm]; ring⟩

theorem lazard_binomial : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (a : K) (n : ℕ), 2 ≤ n →
    (∀ k, 0 < k → k < n → ‖a * (n.choose k : K)‖ ≤ ‖(l : K)‖) →
    ‖a‖ ≤ ‖(l : K)‖ ∨ (‖a‖ ≤ 1 ∧ ∃ i : ℕ, 0 < i ∧ n = l ^ i) := by
  intro K _ _ _ l hp hl a n hn h
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) l hp.one_lt.ne'
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  by_cases hm1 : m = 1
  · subst hm1
    simp only [mul_one] at h hn ⊢
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; simp at hn
      · exact h0
    refine Or.inr ⟨?_, e, he, rfl⟩
    obtain ⟨c, hc, hch⟩ := choose_prime_pow_pred hp e he
    have hk := h (l ^ (e - 1)) (pow_pos hp.pos _) (Nat.pow_lt_pow_right hp.one_lt (by omega))
    rw [hch, Nat.cast_mul, norm_mul, norm_mul, norm_natCast_eq_one_of_not_dvd hp hl hc, mul_one] at hk
    exact le_of_mul_le_mul_right (by rwa [one_mul]) hlpos
  · left
    have hm0 : m ≠ 0 := by rintro rfl; simp at hn
    have hk := h (l ^ e) (pow_pos hp.pos e)
      (lt_mul_of_one_lt_right (pow_pos hp.pos e) (by omega))
    rwa [norm_mul, norm_natCast_eq_one_of_not_dvd hp hl (not_dvd_choose_pow_mul hp m hm e), mul_one] at hk

end GlobalTheory.Honda.Lazard
end

