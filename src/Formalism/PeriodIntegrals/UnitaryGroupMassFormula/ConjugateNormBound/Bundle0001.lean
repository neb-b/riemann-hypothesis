module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.Development

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.BeConjNormOfIntInv
section
noncomputable section

open Classical

namespace PI.BeConjNormW

open PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula

variable {p : ℕ} [Fact p.Prime]

theorem coeff_one_subst (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst a f : PowerSeries ℂ_[p]) = PowerSeries.coeff 1 f * PowerSeries.coeff 1 a := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.coeff 1 (PowerSeries.subst a f : PowerSeries ℂ_[p]) =
      ∑ᶠ k : ℕ, PowerSeries.coeff k f * PowerSeries.coeff 1 (a ^ k) :=
    (PowerSeries.coeff_subst hs f (Finsupp.single () 1)).trans (finsum_congr fun k => smul_eq_mul _ _)
  have hz : ∀ k, 2 ≤ k → PowerSeries.coeff 1 (a ^ k) = 0 := by
    intro k hk
    obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul, zero_add]
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hk (by rw [hz k (by omega), mul_zero])

private theorem coeff_zero_subst_of_constantCoeff_eq_zero (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.coeff 0 (PowerSeries.subst a f : PowerSeries ℂ_[p]) = PowerSeries.coeff 0 f := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.coeff 0 (PowerSeries.subst a f : PowerSeries ℂ_[p]) =
      ∑ᶠ k : ℕ, PowerSeries.coeff k f * PowerSeries.coeff 0 (a ^ k) :=
    (PowerSeries.coeff_subst hs f (Finsupp.single () 0)).trans (finsum_congr fun k => smul_eq_mul _ _)
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range 1)]
  · simp
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hk
    obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]

theorem linear_coeff_padic : LinCoeff := by
  intro q _ l ex hex hle c
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := coeff_zero_subst_of_constantCoeff_eq_zero ex l hex
    rw [hle, PowerSeries.coeff_zero_X, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    exact h.symm
  have hprod : PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 := by
    have h := coeff_one_subst ex l hex hl0
    rw [hle, PowerSeries.coeff_one_X] at h
    exact h.symm
  have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℂ_[q]) = 0 := PowerSeries.constantCoeff_X
  have hsX0 : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_subst_of_constantCoeff_eq_zero _ _ hX0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  have hsX1 : PowerSeries.coeff 1 (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) =
      PowerSeries.coeff 1 l := by
    rw [coeff_one_subst _ _ hX0 hl0, PowerSeries.coeff_one_X, mul_one]
  have hc0 : PowerSeries.constantCoeff
      (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) = 0 := by
    rw [map_mul, hsX0, mul_zero]
  have key := coeff_one_subst
    (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) ex hc0 hex
  rw [PowerSeries.coeff_C_mul, hsX1] at key
  show PowerSeries.coeff 1 (PowerSeries.subst
    (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) ex : PowerSeries ℂ_[q]) = c
  rw [key]
  linear_combination c * hprod

theorem core_of (hI : IntInv) (hL : LinCoeff) : StepCore := by
  intro p _ l ex ph hl0 hex0 hinv hph S hswap hadd hintS hIA hnm hdec hnorm hB
  have hE := norm_units_equivalence
  have hSub := norm_units_substitution
  have hC := norm_units_closed_form
  have hD := natCast_dense_p_adic
  have z0 := constantCoeff_var (p := p) (0 : Fin 2)
  have z1 := constantCoeff_var (p := p) (1 : Fin 2)
  have hInv : ∀ c : ℂ_[p], ‖c‖ = 1 → IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (mulBy l ex c⁻¹ (Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    intro c hc hcI
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hs0 : ∀ i : Unit, MvPowerSeries.constantCoeff
        ((fun _ => (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p])) i) = 0 :=
      fun _ => constantCoeff_formalSMul hex0 hinv _ _ (constantCoeff_var ())
    have hcomp := sb_mulBy (fun _ => (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p])) hs0 hex0 hinv c⁻¹
      (Xv ()) (constantCoeff_var ())
    rw [sb_X _ hs0] at hcomp
    rw [mulBy_mulBy hex0 hinv _ _ _ (constantCoeff_var ()), inv_mul_cancel₀ hc0, mulBy_one hex0 hinv _ (constantCoeff_var ())] at hcomp
    have key := hI p (mulBy l ex c (Xv ())) (mulBy l ex c⁻¹ (Xv ())) (constantCoeff_formalSMul hex0 hinv _ _ (constantCoeff_var ()))
      (constantCoeff_formalSMul hex0 hinv _ _ (constantCoeff_var ())) (by rw [hL p l ex hex0 hinv c]; exact hc) (fun n => hcI _) hcomp
    intro e
    have he : e = Finsupp.single () (e ()) := Finsupp.ext fun u => by cases u; simp
    unfold IsIntP
    rw [he]
    exact key (e ())
  have hU : ∀ β ∈ S, ‖β.1‖ = 1 → Simeq (be l ex ph (mulBy l ex β.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex β.2 (Xv 1))) := by
    intro β hβ h1
    obtain ⟨n, hn⟩ := hnm β hβ
    have hβ1 : β.1 ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    have hw : IntegralMv (mulBy l ex β.1⁻¹ (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) :=
      int_mulBy_of hSub hex0 hinv β.1⁻¹ (hInv β.1 h1 (hintS β hβ)) _ z1 (int_X 1)
    exact units_iv hE hSub hex0 hinv β.1 β.2 hβ1 hw
      (sTrans hE (units_i hE hSub hex0 hinv hIA _ _ (hnorm β hβ))
        (units_ii hE hSub hC hD hex0 hinv hph hIA hB _ _ n hn))
  intro α hα
  obtain ⟨β, hβ, γ, hγ, hb1, hg1, rfl⟩ := hdec α hα
  have iM : ∀ c, IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]) → ∀ i : Fin 2,
      IntegralMv (mulBy l ex c (Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) :=
    fun c hc i => int_mulBy_of hSub hex0 hinv c hc _ (constantCoeff_var i) (int_X i)
  simp only [Prod.fst_add, Prod.snd_add]
  rw [← add_mulBy hex0 hinv _ _ _ z0, ← add_mulBy hex0 hinv _ _ _ z1]
  refine sTrans hE (be_add_left hSub hex0 hinv hB _ _ _ (constantCoeff_formalSMul hex0 hinv _ _ z0) (constantCoeff_formalSMul hex0 hinv _ _ z0)
    z1 (iM _ (hintS β hβ) 0) (iM _ (hintS γ hγ) 0) (int_X 1)) ?_
  refine sTrans hE (sAdd hE (hU β hβ hb1) (hU γ hγ hg1)) ?_
  exact sSymm hE (be_add_right hSub hex0 hinv hB _ _ _ (constantCoeff_formalSMul hex0 hinv _ _ z1) (constantCoeff_formalSMul hex0 hinv _ _ z1) z0
    (iM β.2 (hintS β.swap (hswap β hβ)) 1) (iM γ.2 (hintS γ.swap (hswap γ hγ)) 1) (int_X 0))

theorem beConjNorm_of_intInv (hI : IntInv) : PI.BeConjNorm.BeConjNorm :=
  beConjNorm_of (core_of hI linear_coeff_padic)

end PI.BeConjNormW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.MemIntegerRingIffNormLeOne
section
noncomputable section

open Classical PowerSeries

namespace PI.BeConjNormW

namespace InverseCommuting

variable {p : ℕ} [Fact p.Prime]

theorem mem_integerRing_iff_norm_le_one (x : ℂ_[p]) : x ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p ↔ ‖x‖ ≤ 1 := by
  first
  | exact Iff.rfl
  | (simp only [PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing]; rfl)
  | simp [PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing]

theorem coeff_pow_int {f : PowerSeries ℂ_[p]} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (k n : ℕ) :
    ‖coeff n (f ^ k)‖ ≤ 1 := by
  have hf' : ∀ m, coeff m f ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := fun m => (mem_integerRing_iff_norm_le_one _).2 (hf m)
  rw [← mem_integerRing_iff_norm_le_one]
  induction k generalizing n with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    exact sum_mem fun x _ => mul_mem (ih _) (hf' _)

theorem coeff_pow_of_lt {f : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) {k n : ℕ} (h : n < k) :
    coeff n (f ^ k) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf0
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

theorem coeff_pow_self {f : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) (n : ℕ) :
    coeff n (f ^ n) = coeff 1 f ^ n := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf0
  have h1 : coeff 1 (X * g) = constantCoeff g := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [h1, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow]

theorem coeff_subst_fin {f g : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) (n : ℕ) :
    coeff n (subst f g) = ∑ k ∈ Finset.range (n + 1), coeff k g * coeff n (f ^ k) := by
  have hs : HasSubst f := by
    first
    | exact HasSubst.of_constantCoeff_zero' hf0
    | exact HasSubst.of_constantCoeff_zero hf0
  have h1 : coeff n (subst f g) = ∑ᶠ k : ℕ, coeff k g * coeff n (f ^ k) := by
    first
    | exact (coeff_subst hs g (Finsupp.single () n)).trans (finsum_congr fun k => smul_eq_mul _ _)
    | (rw [coeff_subst' hs]; simp only [smul_eq_mul])
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  intro k hk
  rw [Function.mem_support] at hk
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hk (by rw [coeff_pow_of_lt hf0 (by omega), mul_zero])

end InverseCommuting

open InverseCommuting in
theorem inverse_integral_padic : IntInv := by
  intro p _ f g hf0 hg0 h1 hf hfg n
  have key : ∀ m, coeff m g ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [coeff_zero_eq_constantCoeff_apply, hg0]
        exact zero_mem _
      · have hs := coeff_subst_fin (g := g) hf0 m
        rw [hfg, Finset.sum_range_succ, coeff_pow_self hf0] at hs
        have hrest : (∑ k ∈ Finset.range m, coeff k g * coeff m (f ^ k)) ∈
            PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p :=
          sum_mem fun k hk => mul_mem (ih k (Finset.mem_range.mp hk)) ((mem_integerRing_iff_norm_le_one _).2 (coeff_pow_int hf k m))
        have hX : coeff m (X : PowerSeries ℂ_[p]) ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := by
          rw [coeff_X]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        have hprod : coeff m g * coeff 1 f ^ m ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := by
          have he : coeff m g * coeff 1 f ^ m =
              coeff m (X : PowerSeries ℂ_[p]) - ∑ k ∈ Finset.range m, coeff k g * coeff m (f ^ k) := by
            rw [hs]
            ring
          rw [he]
          exact sub_mem hX hrest
        rw [mem_integerRing_iff_norm_le_one] at hprod ⊢
        rwa [norm_mul, norm_pow, h1, one_pow, mul_one] at hprod
  exact (mem_integerRing_iff_norm_le_one _).1 (key n)

end PI.BeConjNormW
end
end

