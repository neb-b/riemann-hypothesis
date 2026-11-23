module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormHasSumEqOfDominant
section
open Polynomial

namespace GlobalTheory

theorem norm_hasSum_eq_of_dominant : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type)
    (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by
  intro K _ _ ι f s i₀ hsum h
  classical
  have hs : Summable f := hsum.summable
  have hf : Filter.Tendsto f Filter.cofinite (nhds 0) := hs.tendsto_cofinite_zero
  rw [← hsum.tsum_eq, hs.tsum_eq_add_tsum_ite i₀]
  by_cases h0 : f i₀ = 0
  · have : ∀ i, (if i = i₀ then 0 else f i) = 0 := by
      intro i
      split_ifs with hi
      · rfl
      · have := h i hi
        rw [h0, norm_zero] at this
        exact absurd this (norm_nonneg _).not_gt
    simp [this]
  have hc : 0 < ‖f i₀‖ := norm_pos_iff.2 h0
  set g : ι → K := fun i => if i = i₀ then 0 else f i with hg
  have hglt : ∀ i, ‖g i‖ < ‖f i₀‖ := by
    intro i
    simp only [hg]
    split_ifs with hi
    · simpa using hc
    · exact h i hi
  have hfin : {i | ¬ ‖f i‖ < ‖f i₀‖ / 2}.Finite := by
    have := (NormedAddGroup.tendsto_nhds_zero.1 hf) (‖f i₀‖ / 2) (by positivity)
    exact Filter.eventually_cofinite.1 this
  obtain ⟨j, -, hj⟩ := Set.exists_max_image _ (fun i => ‖g i‖) hfin
    ⟨i₀, by simp only [Set.mem_setOf_eq]; linarith⟩
  have hb : ‖∑' i, g i‖ ≤ max (‖f i₀‖ / 2) ‖g j‖ := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
    by_cases hi : ‖f i‖ < ‖f i₀‖ / 2
    · refine le_max_of_le_left ?_
      simp only [hg]
      split_ifs
      · simp only [norm_zero]; positivity
      · exact hi.le
    · exact le_max_of_le_right (hj i hi)
  have hlt : ‖∑' i, g i‖ < ‖f i₀‖ := hb.trans_lt (max_lt (by linarith) (hglt j))
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLeMul
section
open MeasureTheory

namespace GlobalTheory

theorem norm_integral_star_mul_sq_le {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    (hff : Integrable (fun x => star (f x) * f x) μ) (hhh : Integrable (fun x => star (h x) * h x) μ) :
    ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re := by
  have key : ∀ g : X → ℂ, (fun x => star (g x) * g x) = fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
    intro g; funext x; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re_eq : ∀ g : X → ℂ, (∫ x, star (g x) * g x ∂μ).re = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    intro g; rw [key g, integral_complex_ofReal]; rfl
  have int_sq : ∀ g : X → ℂ, Integrable (fun x => star (g x) * g x) μ → Integrable (fun x => ‖g x‖ ^ 2) μ := by
    intro g hg; rw [key g] at hg; have hr := hg.re; simp only [RCLike.re_to_complex, Complex.ofReal_re] at hr; exact hr
  have mf : MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hf).mpr (int_sq f hff)
  have mh : MemLp h (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hh).mpr (int_sq h hhh)
  have hold := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) Real.HolderConjugate.two_two mf mh
  simp only [Real.rpow_two] at hold
  rw [re_eq f, re_eq h]
  have A0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have B0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have n1 : ‖∫ x, star (f x) * h x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖h x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext x; rw [norm_mul, norm_star]
  have n0 : 0 ≤ ‖∫ x, star (f x) * h x ∂μ‖ := norm_nonneg _
  have hsq : ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2
      = (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖h x‖ ^ 2 ∂μ) := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt A0, Real.sq_sqrt B0]
  calc ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2 :=
        pow_le_pow_left₀ n0 (n1.trans hold) 2
    _ = _ := hsq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormNatCastEqOneOfNotDvd
section
universe u_1

namespace GlobalTheory.NatCastUnitNorm

theorem norm_natCast_eq_one_of_not_dvd {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K]
    {l m : ℕ} (hl : Nat.Prime l) (hlt : ‖(l : K)‖ < (1 : ℝ)) (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = (1 : ℝ) := by
  have hle : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  by_contra hne
  have hmlt : ‖(m : K)‖ < 1 := lt_of_le_of_ne hle hne
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
  obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hK : (a : K) * (l : K) + (b : K) * (m : K) = 1 := by
    have h := congrArg (fun z : ℤ => (z : K)) hab
    simpa using h
  have key : ∀ (c : ℤ) (x : K), ‖x‖ < 1 → ‖(c : K) * x‖ < 1 := by
    intro c x hx
    rw [norm_mul]
    have hc : ‖(c : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K c
    calc ‖(c : K)‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ < 1 := hx
  have h1 := IsUltrametricDist.norm_add_le_max ((a : K) * (l : K)) ((b : K) * (m : K))
  rw [hK, norm_one] at h1
  exact absurd h1 (not_le.2 (max_lt (key a _ hlt) (key b _ hmlt)))

end GlobalTheory.NatCastUnitNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormOneAddEqOne
section
namespace GlobalTheory.UnitValueExistence

open Matrix

theorem norm_add_lt_one {E : Type} [NormedField E] [IsUltrametricDist E] {a b : E}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

theorem norm_one_add_eq_one {E : Type} [NormedField E] [IsUltrametricDist E] {a : E}
    (ha : ‖a‖ < 1) : ‖1 + a‖ = 1 := by
  have h : ‖(1 : E)‖ ≠ ‖a‖ := by rw [norm_one]; exact ha.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h, norm_one, max_eq_left ha.le]

theorem norm_det_lt_one {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (h : ∀ i j, ‖G i j‖ < 1) : ‖G.det‖ < 1 := by
  rw [Matrix.det_apply']
  refine Finset.sum_induction _ (fun x : E => ‖x‖ < 1) (fun a b ha hb => norm_add_lt_one ha hb)
    (by simp) ?_
  intro σ _
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [norm_mul, hs, one_mul, norm_prod]
  obtain ⟨i⟩ := ‹Nonempty n›
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h2 : ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => (h _ _).le)
  calc ‖G (σ i) i‖ * ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ ‖G (σ i) i‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact h _ _

theorem exists_unit_value {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hstar : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he : ‖e0‖ ≤ (1 : ℝ)) (htr : e0 + star e0 = 1)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (hG : Matrix.IsHermitian G) (hint : ∀ i j, ‖G i j‖ ≤ (1 : ℝ)) (hdet : ‖G.det‖ = (1 : ℝ)) :
    ∃ (i : n) (w : n → E), (∀ a, ‖w a‖ ≤ (1 : ℝ)) ∧ w i = 1 ∧
      ‖star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ) := by
  by_cases hd : ∃ i, ‖G i i‖ = 1
  · obtain ⟨i, hi⟩ := hd
    refine ⟨i, Pi.single i 1, ?_, by simp, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp
      · simp [Pi.single_eq_of_ne ha]
    · have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
        rw [Pi.star_single, star_one]
      rw [hs, single_dotProduct, Matrix.mulVec_single_one]
      simpa using hi
  · have hdiag : ∀ i, ‖G i i‖ < 1 := fun i =>
      lt_of_le_of_ne (hint i i) (fun h => hd ⟨i, h⟩)
    have hex : ∃ i j, ‖G i j‖ = 1 := by
      by_contra hne
      have := norm_det_lt_one G (fun i j => lt_of_le_of_ne (hint i j) (fun h => hne ⟨i, j, h⟩))
      exact this.ne hdet
    obtain ⟨i, j, hij⟩ := hex
    have hne : i ≠ j := by
      rintro rfl
      exact (hdiag i).ne hij
    have hg0 : G i j ≠ 0 := by
      intro h; rw [h, norm_zero] at hij; exact zero_ne_one hij
    set t : E := e0 / G i j with ht
    have htn : ‖t‖ ≤ 1 := by rw [ht, norm_div, hij, div_one]; exact he
    have htG : G i j * t = e0 := by rw [ht]; field_simp
    have hji : G j i = star (G i j) := (hG.apply j i).symm
    have htG' : star t * G j i = star e0 := by rw [hji, ← star_mul, htG]
    refine ⟨i, Pi.single i 1 + Pi.single j t, ?_, ?_, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp [Pi.single_eq_of_ne hne]
      · by_cases hb : a = j
        · subst hb; simpa [Pi.single_eq_of_ne ha] using htn
        · simp [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]
    · simp [Pi.single_eq_of_ne hne]
    · have hs : star (Pi.single i (1 : E) + Pi.single j t : n → E)
          = Pi.single i 1 + Pi.single j (star t) := by
        rw [star_add, Pi.star_single, Pi.star_single, star_one]
      have key : star (Pi.single i (1 : E) + Pi.single j t : n → E) ⬝ᵥ
          Matrix.mulVec G (Pi.single i 1 + Pi.single j t)
          = 1 + (G i i + star t * (G j j * t)) := by
        rw [hs, add_dotProduct, single_dotProduct, single_dotProduct, Matrix.mulVec_add]
        simp only [Pi.add_apply, Matrix.mulVec, dotProduct_single]
        linear_combination htG + htG' + htr
      rw [key]
      apply norm_one_add_eq_one
      apply norm_add_lt_one (hdiag i)
      rw [norm_mul, norm_mul, hstar]
      have h1 := hdiag j
      have h2 := norm_nonneg t
      have h3 := norm_nonneg (G j j)
      have h4 : ‖G j j‖ * ‖t‖ ≤ ‖G j j‖ := mul_le_of_le_one_right h3 htn
      have h5 : ‖t‖ * (‖G j j‖ * ‖t‖) ≤ ‖G j j‖ * ‖t‖ :=
        mul_le_of_le_one_left (mul_nonneg h3 h2) htn
      linarith

theorem main : (let d1 : {E : Type} → [NormedField E] → {n m : Type} → Matrix n m E → Prop := @(fun {E : Type} [NormedField E] {n m : Type} (h : Matrix n m E) ↦ ∀ (i : n) (j : m), ‖h i j‖ ≤ (1 : ℝ)); ∀ {E : Type} [inst : NormedField E] [IsUltrametricDist E] [inst_2 : StarRing E], (∀ (y : E), ‖Star.star y‖ = ‖y‖) → ∀ (e0 : E), ‖e0‖ ≤ (1 : ℝ) → e0 + Star.star e0 = (1 : E) → ∀ {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] [Nonempty n] (G : Matrix n n E), Matrix.IsHermitian G → d1 G → ‖Matrix.det G‖ = (1 : ℝ) → ∃ (i : n) (w : n → E), (∀ (a : n), ‖w a‖ ≤ (1 : ℝ)) ∧ w i = (1 : E) ∧ ‖Star.star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ)) := by
  intro d1 E _ _ _ hstar e0 he htr n _ _ _ G hG hint hdet
  exact exists_unit_value hstar e0 he htr G hG hint hdet

end GlobalTheory.UnitValueExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowPrimePowSubOne
section
namespace GlobalTheory.PadicLte

theorem norm_pow_prime_sub_one (l : ℕ) [Fact l.Prime] (u : ℤ_[l])
    (h : ‖u - 1‖ < ‖((l : ℕ) : ℤ_[l])‖) :
    ‖u ^ l - 1‖ = ‖u - 1‖ * ‖((l : ℕ) : ℤ_[l])‖ := by
  have hl1 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
    intro i
    rw [← mul_geom_sum, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
  have hsum : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, (u ^ i - 1)‖ ≤ ‖u - 1‖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      exact (PadicInt.nonarchimedean _ _).trans (max_le ih (hpow m))
  have hsplit : ∑ i ∈ Finset.range l, u ^ i
      = ((l : ℕ) : ℤ_[l]) + ∑ i ∈ Finset.range l, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hgeom : ‖∑ i ∈ Finset.range l, u ^ i‖ = ‖((l : ℕ) : ℤ_[l])‖ := by
    rw [hsplit, PadicInt.norm_add_eq_max_of_ne]
    · exact max_eq_left ((hsum l).trans h.le)
    · exact ((hsum l).trans_lt h).ne'
  rw [← mul_geom_sum, norm_mul, hgeom]

theorem norm_pow_prime_pow_sub_one (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (k : ℕ) (hk : 2 ≤ k)
    (hu : ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k) (n : ℕ) :
    ‖u ^ l ^ n - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := by
  have hl1 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : 0 ≤ ‖((l : ℕ) : ℤ_[l])‖ := norm_nonneg _
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    have hlt : ‖u ^ l ^ n - 1‖ < ‖((l : ℕ) : ℤ_[l])‖ := by
      rw [ih]
      calc ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ 2 :=
            pow_le_pow_of_le_one hl0 hl1.le (by omega)
        _ < ‖((l : ℕ) : ℤ_[l])‖ ^ 1 := by
            have hpos : 0 < ‖((l : ℕ) : ℤ_[l])‖ := by
              rw [PadicInt.norm_p]
              exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
            exact pow_lt_pow_right_of_lt_one₀ hpos hl1 (by norm_num)
        _ = ‖((l : ℕ) : ℤ_[l])‖ := pow_one _
    rw [pow_succ, pow_mul, norm_pow_prime_sub_one l _ hlt, ih, ← pow_succ, ← add_assoc]

end GlobalTheory.PadicLte
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneLe
section
namespace GlobalTheory.CloseToUnitNorm

theorem norm_eq_one_of_close {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (1 - u)
    rw [add_sub_cancel, norm_one, norm_sub_rev] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)

theorem norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (hu : ‖u‖ = 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hu, one_mul]
    exact ih

theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - (1 : C)‖ < (1 : ℝ)) (i : ℤ) : ‖u ^ i - (1 : C)‖ ≤ ‖u - (1 : C)‖ := by
  have hu : ‖u‖ = 1 := norm_eq_one_of_close u h
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le u hu n
  · rw [zpow_neg, zpow_natCast]
    have hn : u ^ n ≠ 0 := pow_ne_zero n hu0
    have e : (u ^ n)⁻¹ - 1 = -((u ^ n)⁻¹ * (u ^ n - 1)) := by
      field_simp
      ring
    rw [e, norm_neg, norm_mul, norm_inv, norm_pow, hu, one_pow, inv_one, one_mul]
    exact norm_pow_sub_one_le u hu n

end GlobalTheory.CloseToUnitNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormZpowSubOneLe
section
namespace GlobalTheory.UnitNormPowerSubOne

theorem norm_eq_one {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (-(u - 1))
    have e : u + -(u - 1) = 1 := by ring
    rw [e, norm_one, norm_neg] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)

theorem norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := IsUltrametricDist.norm_add_le_max (u ^ n * (u - 1)) (u ^ n - 1)
    have e : u ^ n * (u - 1) + (u ^ n - 1) = u ^ (n + 1) - 1 := by ring
    rw [e, norm_mul, norm_pow, norm_eq_one u h, one_pow, one_mul] at h1
    exact h1.trans (max_le le_rfl ih)

theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  have hn := norm_eq_one u h
  have hu : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le u h n
  · have hp : u ^ n ≠ 0 := pow_ne_zero n hu
    have e : u ^ (-(n : ℤ)) - 1 = -((u ^ n)⁻¹ * (u ^ n - 1)) := by
      rw [zpow_neg, zpow_natCast, mul_sub, inv_mul_cancel₀ hp, mul_one, neg_sub]
    rw [e, norm_neg, norm_mul, norm_inv, norm_pow, hn, one_pow, inv_one, one_mul]
    exact norm_pow_sub_one_le u h n

end GlobalTheory.UnitNormPowerSubOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotDvdCoeffAevalOneAddXPowSubOne
section
open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in
private theorem C_dvd_prod_pow_sub_X_pow_sum_of_C_dvd {O σ : Type} [CommRing O] [Fintype σ] (ϖ : O)
    (g : σ → Polynomial O) (k : σ → ℕ) (hg : ∀ q, Polynomial.C ϖ ∣ g q - Polynomial.X ^ k q)
    (m : σ → ℕ) :
    Polynomial.C ϖ ∣ ∏ q, g q ^ m q - Polynomial.X ^ (∑ q, m q * k q) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  rw [← Finset.prod_pow_eq_pow_sum, map_prod, map_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hq := Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hg q))
  rw [map_pow, hq, ← map_pow, ← pow_mul, mul_comm]

open scoped BigOperators in
private theorem C_dvd_one_add_X_pow_prime_pow_sub_one_sub_X_pow {O : Type} [CommRing O] (ϖ : O) (l e : ℕ)
    (hl : l.Prime) (h : ϖ ∣ (l : O)) :
    Polynomial.C ϖ ∣ (1 + Polynomial.X : Polynomial O) ^ (l ^ e) - 1 - Polynomial.X ^ (l ^ e) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  simp only [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one,
    Polynomial.coeff_X_pow]
  have hN : l ^ e ≠ 0 := (pow_pos hl.pos _).ne'
  by_cases h0 : i = 0
  · subst h0
    simp [hN.symm]
  by_cases hN' : i = l ^ e
  · subst hN'
    simp [h0, hl.ne_zero]
  · simp only [h0, hN', if_false, sub_zero]
    exact h.trans (Nat.cast_dvd_cast (hl.dvd_choose_pow h0 hN'))


open scoped BigOperators in
theorem _root_.GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (σ : Type) [Fintype σ] (l μ : ℕ), l.Prime → ϖ ∣ (l : O) → ∀ (F : MvPolynomial σ O) (e : σ → ℕ) (m₀ : σ →₀ ℕ), (∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ μ ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ F.coeff m₀ → (∀ m : σ →₀ ℕ, m ≠ m₀ → ∑ q, m q * l ^ e q ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ (μ + 1) ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F).coeff (∑ q, m₀ q * l ^ e q) := by
  intro O _ _ _ ϖ _ σ _ l μ hl hϖl F e m₀ hlow hm₀ hoth
  classical
  set W := ∑ q, m₀ q * l ^ e q with hW
  set g : σ → Polynomial O := fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1 with hgdef
  set c : (σ →₀ ℕ) → O := fun m => (∏ q, g q ^ m q).coeff W with hc
  have hexp : (MvPolynomial.aeval g F).coeff W = ∑ m ∈ F.support, F.coeff m * c m := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.algebraMap_eq, Polynomial.coeff_C_mul]
  have hcong : ∀ m : σ →₀ ℕ, ϖ ∣ c m - if W = ∑ q, m q * l ^ e q then 1 else 0 := by
    intro m
    have h := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 (C_dvd_prod_pow_sub_X_pow_sum_of_C_dvd ϖ g (fun q => l ^ e q)
      (fun q => by simpa [g] using C_dvd_one_add_X_pow_prime_pow_sub_one_sub_X_pow ϖ l (e q) hl hϖl) m) W
    simpa [Polynomial.coeff_X_pow] using h
  have hvanish : ∀ m : σ →₀ ℕ, W < m.degree → c m = 0 := by
    intro m hm
    have hX : ∀ q, Polynomial.X ∣ g q := fun q => by
      rw [Polynomial.X_dvd_iff]
      simp [g, Polynomial.coeff_one_add_X_pow]
    have hdvd : Polynomial.X ^ (∑ q, m q) ∣ ∏ q, g q ^ m q := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun q _ => pow_dvd_pow_of_dvd (hX q) _
    rw [Finsupp.degree_eq_sum] at hm
    exact (Polynomial.X_pow_dvd_iff.1 hdvd) W hm
  have hdeg : ∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m q * l ^ e q := by
    intro m
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun q _ => Nat.le_mul_of_pos_right _ (pow_pos hl.pos _)
  have hterm : ∀ m, m ≠ m₀ → ϖ ^ (μ + 1) ∣ F.coeff m * c m := by
    intro m hne
    by_cases hw : ∑ q, m q * l ^ e q ≤ W
    · exact dvd_mul_of_dvd_left (hoth m hne hw) _
    by_cases hd : m.degree ≤ W
    · have h1 := hcong m
      rw [if_neg (by omega), sub_zero] at h1
      rw [pow_succ]
      exact mul_dvd_mul (hlow m hd) h1
    · rw [hvanish m (by omega), mul_zero]
      exact dvd_zero _
  have hmain : ϖ ^ (μ + 1) ∣ F.coeff m₀ * c m₀ - F.coeff m₀ := by
    have h1 := hcong m₀
    rw [if_pos rfl] at h1
    rw [← mul_sub_one, pow_succ]
    exact mul_dvd_mul (hlow m₀ (hdeg m₀)) h1
  have hmem : m₀ ∈ F.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    exact hm₀ (h0 ▸ dvd_zero _)
  intro hdiv
  rw [hexp, ← Finset.add_sum_erase _ _ hmem] at hdiv
  have hrest : ϖ ^ (μ + 1) ∣ ∑ m ∈ F.support.erase m₀, F.coeff m * c m :=
    Finset.dvd_sum fun m hm => hterm m (Finset.ne_of_mem_erase hm)
  have h2 := (dvd_add_left hrest).1 hdiv
  exact hm₀ (by simpa using dvd_sub h2 hmain)

end GlobalTheory
end

