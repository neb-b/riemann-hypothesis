module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.TorsionNormIteration.LubinTateExample
public import Mathlib
public import Formalism.TorsionNormIteration.InverseIntegralClasses.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFunctionalEquationOneTermType
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.HondaFunEq

variable {K : Type} [NormedField K]

theorem sq_apply (σ : K →+* K) (a : K) : (σ ^ 2) a = σ (σ a) := by
  rw [pow_two]; rfl

theorem frobLift_sq [IsUltrametricDist K] {l : ℕ} {σ : K →+* K} (h : Unr K l σ) :
    Formalism.G.IsFrobLift l (l ^ 2) (σ ^ 2) := by
  obtain ⟨-, -, -, hmax, hiso, hfrob⟩ := h
  have key : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ l‖ ≤ ‖(l : K)‖ := fun x hx => hmax _ (hfrob x hx)
  intro a ha
  have hsa : ‖σ a‖ ≤ 1 := by rw [hiso]; exact ha
  have hal : ‖a ^ l‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have hd : (σ ^ 2) a - a ^ (l ^ 2) = (σ (σ a) - (σ a) ^ l) + ((σ a) ^ l - (a ^ l) ^ l) := by
    rw [sq_apply, ← pow_mul, sq]; ring
  rw [hd]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key _ hsa) ?_)
  rw [← (Commute.all (σ a) (a ^ l)).geom_sum₂_mul, norm_mul]
  have hs : ‖∑ i ∈ Finset.range l, σ a ^ i * (a ^ l) ^ (l - 1 - i)‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_mul, norm_pow, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hsa) (by positivity) (pow_le_one₀ (norm_nonneg _) hal)
  calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul hs (key a ha) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem setting [IsUltrametricDist K] {l : ℕ} {σ : K →+* K} (h : Unr K l σ) :
    Formalism.G.FunctionalEquationSetting K l (l ^ 2) (σ ^ 2) :=
  ⟨h.1, ⟨2, by norm_num, rfl⟩, h.2.2.1, frobLift_sq h⟩

theorem coeff_ltLog_pow (l : ℕ) (hl : 2 ≤ l) (j : ℕ) :
    coeff ((l ^ 2) ^ j) (ltLog K l) = ((l : K) ^ j)⁻¹ := by
  have h : ∃ i : ℕ, (l ^ 2) ^ j = (l ^ 2) ^ i := ⟨j, rfl⟩
  simp only [ltLog, coeff_mk, dif_pos h]
  have hq : 2 ≤ l ^ 2 := le_trans hl (Nat.le_self_pow (by norm_num) l)
  have := Nat.find_spec h
  rw [(Nat.pow_right_injective hq this).symm]

theorem coeff_ltLog_of_not (l : ℕ) {n : ℕ} (h : ¬ ∃ j : ℕ, n = (l ^ 2) ^ j) :
    coeff n (ltLog K l) = 0 := by
  simp only [ltLog, coeff_mk, dif_neg h]

theorem ltLog_funEq [CharZero K] (l : ℕ) (hl : 2 ≤ l) (τ : K →+* K) :
    ltLog K l - (l : K)⁻¹ • (PowerSeries.map τ (ltLog K l)).subst ((X : K⟦X⟧) ^ (l ^ 2)) = X := by
  have hq : l ^ 2 ≠ 0 := by positivity
  have hq2 : 2 ≤ l ^ 2 := le_trans hl (Nat.le_self_pow (by norm_num) l)
  have hmap : PowerSeries.map τ (ltLog K l) = ltLog K l := by
    ext n
    simp only [coeff_map, ltLog, coeff_mk]
    split_ifs <;> simp [map_inv₀]
  rw [hmap, ← PowerSeries.expand_apply _ hq]
  ext n
  rw [map_sub, coeff_smul, PowerSeries.coeff_expand, coeff_X, smul_eq_mul]
  by_cases hn : ∃ j : ℕ, n = (l ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    cases j with
    | zero =>
      have : ¬ l ^ 2 ∣ 1 := fun h => by
        have := Nat.le_of_dvd one_pos h; omega
      rw [coeff_ltLog_pow l hl 0, if_neg (by simpa using this), if_pos (pow_zero _)]; simp
    | succ k =>
      have h1 : (l ^ 2) ^ (k + 1) ≠ 1 := by
        exact (Nat.one_lt_pow (Nat.succ_ne_zero k) (by omega : 1 < l ^ 2)).ne'
      rw [if_pos (dvd_pow_self _ (Nat.succ_ne_zero k)), if_neg h1, pow_succ,
        Nat.mul_div_cancel _ (by omega), coeff_ltLog_pow l hl k, ← pow_succ, coeff_ltLog_pow l hl (k + 1)]
      have hl0 : (l : K) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
      field_simp
      ring
  · have h1 : n ≠ 1 := fun h => hn ⟨0, by simp [h]⟩
    rw [coeff_ltLog_of_not l hn, if_neg h1]
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      have : ¬ ∃ j : ℕ, m = (l ^ 2) ^ j := fun ⟨j, hj⟩ => hn ⟨j + 1, by rw [hj]; ring⟩
      rw [Nat.mul_div_cancel_left _ (by omega), coeff_ltLog_of_not l this]; simp
    · simp

theorem funEq_scaled [IsUltrametricDist K] {l : ℕ} {σ : K →+* K} {f : K⟦X⟧} {c ε : K} (hε : ‖ε‖ = 1)
    (hc : ε = c * (σ ^ 2) ε)
    (hH : CoefLe ‖(l : K)‖ (C (l : K) * f - C c * frobOp (σ ^ 2) (l ^ 2) 1 f)) (hl : (l : K) ≠ 0) :
    Formalism.G.IsFunEqType l (l ^ 2) (σ ^ 2) (ε⁻¹ • f) := by
  set τ := σ ^ 2 with hτdef
  have hq : l ^ 2 ≠ 0 := by
    have hl' : l ≠ 0 := by rintro rfl; simp at hl
    exact pow_ne_zero 2 hl'
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hτε : τ ε ≠ 0 := (map_ne_zero τ).2 hε0
  have hτ : τ ε⁻¹ = c * ε⁻¹ := by
    rw [map_inv₀]
    field_simp
    linear_combination hc
  have hfrob : frobOp τ (l ^ 2) 1 f = PowerSeries.expand (l ^ 2) hq (PowerSeries.map τ f) := by
    simp only [frobOp, pow_one]; rw [PowerSeries.expand_apply]
  rw [hfrob] at hH
  have hid : ε⁻¹ • f - (l : K)⁻¹ • (PowerSeries.map τ (ε⁻¹ • f)).subst ((X : K⟦X⟧) ^ (l ^ 2)) =
      (ε⁻¹ * (l : K)⁻¹) • (C (l : K) * f - C c * PowerSeries.expand (l ^ 2) hq (PowerSeries.map τ f)) := by
    rw [← PowerSeries.expand_apply _ hq, PowerSeries.smul_eq_C_mul, map_mul, map_C, map_mul,
      PowerSeries.expand_C, hτ]
    ext n
    simp only [map_sub, coeff_smul, coeff_C_mul, smul_eq_mul]
    field_simp
  intro n
  rw [hid, coeff_smul, smul_eq_mul, norm_mul, norm_mul, norm_inv, norm_inv, hε, inv_one, one_mul]
  have hlp : 0 < ‖(l : K)‖ := norm_pos_iff.2 hl
  calc ‖(l : K)‖⁻¹ * _ ≤ ‖(l : K)‖⁻¹ * ‖(l : K)‖ := mul_le_mul_of_nonneg_left (hH n) (inv_nonneg.2 hlp.le)
    _ = 1 := inv_mul_cancel₀ hlp.ne'

theorem funEqType_of_unit {p q : ℕ} (hq : q ≠ 0) {σ : K →+* K} {g : K⟦X⟧}
    (hg : Formalism.G.IsFunEqTypeMv (ι := Unit) p q hq σ (g : MvPowerSeries Unit K)) :
    Formalism.G.IsFunEqType p q σ g := by
  have hx : (PowerSeries.map σ g).subst ((X : K⟦X⟧) ^ q) =
      MvPowerSeries.expand q hq (MvPowerSeries.map σ g) := by
    rw [← PowerSeries.expand_apply q hq]
    rfl
  intro n
  have := hg (Finsupp.single () n)
  rw [← hx] at this
  exact this

theorem honda_funEq : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), Formalism.L2.Th1.C.IsLogPair f e → ∀ c ε : K, ‖ε‖ = 1 → ε = c * (σ ^ 2) ε →
    CoefLe ‖(l : K)‖ (C (l : K) * f - C c * frobOp (σ ^ 2) (l ^ 2) 1 f) →
    CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  intro K _ _ _ l σ hU f e hfe c ε hε hc hH
  have hS := setting hU
  have hl2 : 2 ≤ l := hU.2.1.le
  have hl : (l : K) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hq : l ^ 2 ≠ 0 := by positivity
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  obtain ⟨hf0, hf1, he0, hef, -⟩ := hfe
  have hg := funEq_scaled hε hc hH hl
  have hg0 : constantCoeff (ε⁻¹ • f) = 0 := by simp [hf0]
  have hαS : PowerSeries.HasSubst (ε • X : K⟦X⟧) := PowerSeries.HasSubst.smul_X' ε
  have hα0 : MvPowerSeries.constantCoeff (ε • X : K⟦X⟧) = 0 := by
    show constantCoeff (ε • X : K⟦X⟧) = 0
    simp
  have hαI : Formalism.G.IntegralMv (ε • X : K⟦X⟧) := by
    intro d
    rw [Finsupp.unique_single d]
    show ‖coeff (d ()) (ε • X : K⟦X⟧)‖ ≤ 1
    rw [coeff_smul, coeff_X, smul_eq_mul]
    split_ifs <;> simp [hε]
  have hMv := Formalism.LT.funEqSubst K l (l ^ 2) hq (σ ^ 2) hS (ε⁻¹ • f) hg0 hg Unit (ε • X : K⟦X⟧) hα0 hαI
  set ft : K⟦X⟧ := (ε⁻¹ • f).subst (ε • X : K⟦X⟧) with hft
  have hftE : Formalism.G.IsFunEqType l (l ^ 2) (σ ^ 2) ft := funEqType_of_unit hq hMv
  have hftr : ft = ε⁻¹ • rescale ε f := by
    rw [hft, PowerSeries.subst_smul hαS, PowerSeries.rescale_eq_subst]
  have hft0 : constantCoeff ft = 0 := by
    rw [hftr, ← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hf0]
    simp
  have hft1 : coeff 1 ft = 1 := by
    rw [hftr, coeff_smul, coeff_rescale, hf1, smul_eq_mul]; field_simp
  have hL0 : constantCoeff (ltLog K l) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    apply coeff_ltLog_of_not
    rintro ⟨j, hj⟩
    exact (pow_ne_zero j hq) hj.symm
  have hLE : Formalism.G.IsFunEqType l (l ^ 2) (σ ^ 2) (ltLog K l) := by
    unfold Formalism.G.IsFunEqType
    rw [ltLog_funEq l hl2]
    intro n
    rw [coeff_X]; split_ifs <;> simp
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.LT.funEqHom K l (l ^ 2) (σ ^ 2) hS ft (ltLog K l) hft0 hft1 hftE hL0 hLE
  have hhS : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hεh0 : constantCoeff (ε • h) = 0 := by simp [hh0]
  have hεhS : PowerSeries.HasSubst (ε • h) := PowerSeries.HasSubst.of_constantCoeff_zero' hεh0
  have hXh : (ε • X : K⟦X⟧).subst h = ε • h := by
    rw [PowerSeries.subst_smul hhS, PowerSeries.subst_X hhS]
  have hfεh : f.subst (ε • h) = ε • ltLog K l := by
    rw [← hh, hft, PowerSeries.subst_smul hαS, PowerSeries.subst_smul hhS,
      PowerSeries.subst_comp_subst_apply hαS hhS, hXh, smul_smul, mul_inv_cancel₀ hε0, one_smul]
  have hmain : e.subst (C ε * ltLog K l) = ε • h := by
    rw [← PowerSeries.smul_eq_C_mul, ← hfεh, ← PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf0) hεhS, hef, PowerSeries.subst_X hεhS]
  intro n
  rw [hmain, coeff_smul, smul_eq_mul, norm_mul, hε, one_mul]
  exact hhI n

end GlobalTheory.HondaFunEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicationSeriesUnitCoeffNormLe
section
noncomputable section

namespace GlobalTheory.Honda

open PowerSeries

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem htform_norm_sum_lt {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ j ∈ s, ‖f j‖ < 1) :
    ‖∑ j ∈ s, f j‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (h a (by simp)) (ih fun j hj => h j (by simp [hj])))

theorem htform_norm_sum_le {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ j ∈ s, ‖f j‖ ≤ 1) :
    ‖∑ j ∈ s, f j‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (h a (by simp)) (ih fun j hj => h j (by simp [hj])))

def HtSmallTo (N : ℕ) (f : K⟦X⟧) : Prop := CoefLe 1 f ∧ ∀ n < N, ‖coeff n f‖ < 1

theorem HtSmallTo.mul {a b : ℕ} {f g : K⟦X⟧} (hf : HtSmallTo a f) (hg : HtSmallTo b g) :
    HtSmallTo (a + b) (f * g) := by
  constructor
  · intro n
    rw [coeff_mul]
    apply htform_norm_sum_le
    rintro ⟨i, j⟩ _
    rw [norm_mul]
    exact mul_le_one₀ (hf.1 i) (norm_nonneg _) (hg.1 j)
  · intro n hn
    rw [coeff_mul]
    apply htform_norm_sum_lt
    rintro ⟨i, j⟩ hij
    have hs : i + j = n := by simpa using hij
    rw [norm_mul]
    by_cases hi : i < a
    · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hf.2 i hi) (hg.1 j)
    · have hj : j < b := by omega
      exact mul_lt_one_of_nonneg_of_lt_one_right (hf.1 i) (norm_nonneg _) (hg.2 j hj)

theorem htSmallTo_zero_iff (f : K⟦X⟧) : HtSmallTo 0 f ↔ CoefLe 1 f :=
  ⟨fun h => h.1, fun h => ⟨h, fun n hn => absurd hn (Nat.not_lt_zero _)⟩⟩

theorem htSmallTo_one : HtSmallTo 0 (1 : K⟦X⟧) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [coeff_one]
  split_ifs <;> simp

theorem htSmallTo_pow {f : K⟦X⟧} (hf : HtSmallTo 0 f) (d : ℕ) : HtSmallTo 0 (f ^ d) := by
  induction d with
  | zero => simpa using htSmallTo_one
  | succ d ih => simpa [pow_succ] using ih.mul hf

theorem htSmallTo_X_pow (k : ℕ) : HtSmallTo 0 ((X : K⟦X⟧) ^ k) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [coeff_X_pow]
  split_ifs <;> simp

theorem htSmallTo_C_mul {c : K} (hc : ‖c‖ ≤ 1) {f : K⟦X⟧} (hf : HtSmallTo 0 f) :
    HtSmallTo 0 (C c * f) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hf.1 n)

theorem htSmallTo_sum {ι : Type} (s : Finset ι) (f : ι → K⟦X⟧) (h : ∀ j ∈ s, HtSmallTo 0 (f j)) :
    HtSmallTo 0 (∑ j ∈ s, f j) := by
  rw [htSmallTo_zero_iff]
  intro n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact htform_norm_sum_le _ _ fun j hj => (h j hj).1 n

theorem htSmallTo_sub {f g : K⟦X⟧} (hf : HtSmallTo 0 f) (hg : HtSmallTo 0 g) : HtSmallTo 0 (f - g) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [map_sub, sub_eq_add_neg]
  exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (hf.1 n) (by rw [norm_neg]; exact hg.1 n))

theorem htSmallTo_inv {B : K⟦X⟧} (hB : CoefLe 1 B) (h0 : constantCoeff B = 1) : HtSmallTo 0 B⁻¹ := by
  rw [htSmallTo_zero_iff]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [coeff_inv]
  split_ifs with hn
  · simp [h0]
  · rw [h0, inv_one, neg_mul, one_mul, norm_neg]
    apply htform_norm_sum_le
    rintro ⟨i, j⟩ _
    dsimp only
    split_ifs with hj
    · rw [norm_mul]
      exact mul_le_one₀ (hB i) (norm_nonneg _) (ih j hj)
    · simp

theorem htform_coeff_vpow_eq_zero {v : K⟦X⟧} (h0 : constantCoeff v = 0) {n d : ℕ} (h : n < d) :
    coeff n (v ^ d) = 0 := by
  obtain ⟨w, rfl⟩ := X_dvd_iff.mpr h0
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

theorem htform_coeff_subst (A v : K⟦X⟧) (h0 : constantCoeff v = 0) (n : ℕ) :
    coeff n (A.subst v) = ∑ d ∈ Finset.range (n + 1), coeff d A * coeff n (v ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' h0)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [htform_coeff_vpow_eq_zero h0 (by omega), smul_zero])

theorem htSmallTo_subst {A v : K⟦X⟧} (hA : CoefLe 1 A) (hv : CoefLe 1 v) (h0 : constantCoeff v = 0) :
    HtSmallTo 0 (A.subst v) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [htform_coeff_subst A v h0]
  apply htform_norm_sum_le
  intro d _
  rw [norm_mul]
  exact mul_le_one₀ (hA d) (norm_nonneg _) ((htSmallTo_pow ((htSmallTo_zero_iff v).2 hv) d).1 n)

theorem htform_constantCoeff_subst (A v : K⟦X⟧) (h0 : constantCoeff v = 0) :
    constantCoeff (A.subst v) = constantCoeff A := by
  rw [← coeff_zero_eq_constantCoeff_apply, htform_coeff_subst A v h0]
  simp

theorem htform_unit_coeff_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A v : K⟦X⟧) (e e' : K) (M : ℕ) (Dp Np : Polynomial K), CoefLe 1 A → constantCoeff A = 1 → CoefLe 1 v → constantCoeff v = 0 → ‖e‖ ≤ 1 → ‖e'‖ ≤ 1 → Np.Monic → Np.natDegree = M + 1 → (∀ i, ‖Np.coeff i‖ ≤ 1) → Dp.natDegree ≤ M → ‖Dp.eval e'‖ = 1 → (A.subst v - C e * v ^ 2) * (∑ i ∈ Finset.range (M + 1), C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i))) * X ^ 2 = v ^ 2 * ∑ i ∈ Finset.range (M + 2), C (Np.coeff i) * A ^ i * X ^ (2 * (M + 1 - i)) → ∃ n, n ≤ M + 1 ∧ ‖coeff n v‖ = 1 := by
  intro K _ _ _ A v e e' M Dp Np hA hA0 hv hv0 he he' _ _ hNc hDdeg hDe heq
  by_contra hcon
  push_neg at hcon
  have hvs : HtSmallTo (M + 2) v := ⟨hv, fun n hn => lt_of_le_of_ne (hv n) (hcon n (by omega))⟩
  have hA' : HtSmallTo 0 A := (htSmallTo_zero_iff A).2 hA
  have hB : HtSmallTo 0 (A.subst v - C e * v ^ 2) :=
    htSmallTo_sub (htSmallTo_subst hA hv hv0) (htSmallTo_C_mul he (htSmallTo_pow ((htSmallTo_zero_iff v).2 hv) 2))
  have hB0 : constantCoeff (A.subst v - C e * v ^ 2) = 1 := by
    rw [map_sub, htform_constantCoeff_subst A v hv0, hA0, map_mul, map_pow, hv0]
    simp
  have hH : HtSmallTo 0 (∑ i ∈ Finset.range (M + 2), C (Np.coeff i) * A ^ i * X ^ (2 * (M + 1 - i))) :=
    htSmallTo_sum _ _ fun i _ => by
      simpa using (htSmallTo_C_mul (hNc i) (htSmallTo_pow hA' i)).mul (htSmallTo_X_pow (K := K) (2 * (M + 1 - i)))
  have h1 := ((hvs.mul hvs).mul hH)
  rw [← pow_two, ← heq] at h1
  set G := ∑ i ∈ Finset.range (M + 1), C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i)) with hG
  set B := A.subst v - C e * v ^ 2 with hBdef
  have h2 : HtSmallTo (M + 2 + (M + 2)) (G * X ^ 2) := by
    have := (htSmallTo_inv hB.1 hB0).mul h1
    have hBB : B⁻¹ * (B * G * X ^ 2) = G * X ^ 2 := by
      rw [mul_assoc, ← mul_assoc B⁻¹, PowerSeries.inv_mul_cancel _ (by rw [hB0]; exact one_ne_zero), one_mul]
    rw [hBB, zero_add, add_zero] at this
    exact this
  have h3 : ∀ n < 2 * M + 2, ‖coeff n G‖ < 1 := by
    intro n hn
    have := h2.2 (n + 2) (by omega)
    rwa [coeff_mul_X_pow] at this
  have hterm : ∀ k i, coeff (2 * k) (C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i))) =
      Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0) := by
    intro k i
    rw [mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  have hsmall : ∀ k, k ≤ M → ‖Dp.coeff (M - k)‖ < 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    have hc := h3 (2 * k) (by omega)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hG, map_sum] at hc
    simp_rw [hterm k] at hc
    have hmem : M - k ∈ Finset.range (M + 1) := Finset.mem_range.2 (by omega)
    rw [← Finset.add_sum_erase _ _ hmem] at hc
    have hself : Dp.coeff (M - k) * (if 2 * (M - (M - k)) ≤ 2 * k then coeff (2 * k - 2 * (M - (M - k))) (A ^ (M - k)) else 0)
        = Dp.coeff (M - k) := by
      rw [if_pos (by omega), show 2 * k - 2 * (M - (M - k)) = 0 by omega, coeff_zero_eq_constantCoeff_apply,
        map_pow, hA0, one_pow, mul_one]
    rw [hself] at hc
    have hrest : ‖∑ i ∈ (Finset.range (M + 1)).erase (M - k),
        Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0)‖ < 1 := by
      apply htform_norm_sum_lt
      intro i hi
      rw [Finset.mem_erase, Finset.mem_range] at hi
      split_ifs with hle
      · have hlt : M - i < k := by omega
        have := ih (M - i) hlt (by omega)
        rw [show M - (M - i) = i by omega] at this
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) this ((htSmallTo_pow hA' i).1 _)
      · simp
    have hd : Dp.coeff (M - k) = (Dp.coeff (M - k) + ∑ i ∈ (Finset.range (M + 1)).erase (M - k),
        Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0)) +
        -(∑ i ∈ (Finset.range (M + 1)).erase (M - k),
        Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0)) := by ring
    rw [hd]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hc (by rw [norm_neg]; exact hrest))
  have hev : ‖Dp.eval e'‖ < 1 := by
    rw [Polynomial.eval_eq_sum_range' (n := M + 1) (by omega)]
    apply htform_norm_sum_lt
    intro i hi
    rw [Finset.mem_range] at hi
    have := hsmall (M - i) (by omega)
    rw [show M - (M - i) = i by omega] at this
    rw [norm_mul, norm_pow]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) this (pow_le_one₀ (norm_nonneg _) he')
  rw [hDe] at hev
  exact lt_irrefl _ hev

end GlobalTheory.Honda
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowPrimePowSubFrobeniusTwistNormLe
section
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_add_pow_sub_pow_le (c e : K) {r : ℝ} (hc : ‖c‖ ≤ 1) (hce : ‖c + e‖ ≤ 1) (he : ‖e‖ ≤ r)
    (n : ℕ) : ‖(c + e) ^ n - c ^ n‖ ≤ r := by
  rw [← Commute.geom_sum₂_mul (Commute.all _ _), add_sub_cancel_left, norm_mul]
  have hs : ‖∑ k ∈ Finset.range n, (c + e) ^ k * c ^ (n - 1 - k)‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro k _
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hce) (by positivity) (pow_le_one₀ (norm_nonneg _) hc)
  calc _ ≤ 1 * r := mul_le_mul hs he (norm_nonneg _) zero_le_one
    _ = r := one_mul r

theorem isFrobLift_pow (l : ℕ) (σ : K →+* K) (hU : Unr K l σ) (i : ℕ) :
    Formalism.G.IsFrobLift l (l ^ i) (σ ^ i) ∧ ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := by
  obtain ⟨_, _, hl1, hmax, hiso, hfr⟩ := hU
  induction i with
  | zero => exact ⟨fun a _ => by simp, fun x => by simp⟩
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun a ha => ?_, fun x => ?_⟩
    · rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
      set b := (σ ^ i) a
      have hb : ‖b‖ ≤ 1 := (ih2 a).le.trans ha
      have h1 : ‖σ b - b ^ l‖ ≤ ‖(l : K)‖ := hmax _ (hfr b hb)
      have hc : ‖a ^ l ^ i‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
      have h2 : ‖b ^ l - (a ^ l ^ i) ^ l‖ ≤ ‖(l : K)‖ := by
        have := norm_add_pow_sub_pow_le (a ^ l ^ i) (b - a ^ l ^ i) hc (by simpa using hb) (ih1 a ha) l
        simpa using this
      have : σ b - a ^ l ^ (i + 1) = (σ b - b ^ l) + (b ^ l - (a ^ l ^ i) ^ l) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    · rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hiso, ih2]

theorem pow_frob_sub_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (s : Type) (A : MvPowerSeries s K), (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → ∀ (i : ℕ) (h : l ^ i ≠ 0) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (A ^ (l ^ i) - MvPowerSeries.expand (l ^ i) h (MvPowerSeries.map (σ ^ i) A))‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l σ hU s A hA i h m
  have hpr : l.Prime := hU.1
  have hl1 : ‖(l : K)‖ < 1 := hU.2.2.1
  have hp0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  exact Formalism.LT.FrobP.main l i hpr (σ ^ i) hp0 hl1 (isFrobLift_pow l σ hU i).1 A hA m

end GlobalTheory.Honda
end

