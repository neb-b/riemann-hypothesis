module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.ResidueQuotientHolds
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem residue_finite_holds : StatResFinite := by
  unfold StatResFinite
  intro n _ ℓ c s H hℓ hrec i m
  have hq : (0:ℝ) < ℓ - 1 := by linarith
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := hrec (i + ((m + 1 : ℕ) : ZMod n))
    have he : i + ((m + 1 : ℕ) : ZMod n) - 1 = i + (m : ZMod n) := by
      push_cast
      ring
    rw [he] at h1
    have hpow : 0 < (ℓ - 1) ^ m := pow_pos hq m
    have h2 : s (i + (m : ZMod n)) / (ℓ - 1) ^ m ≤
        (H (i + ((m + 1 : ℕ) : ZMod n)) + c + 3 + s (i + ((m + 1 : ℕ) : ZMod n)) / (ℓ - 1)) / (ℓ - 1) ^ m := by
      rw [div_eq_mul_inv, div_eq_mul_inv _ ((ℓ - 1) ^ m)]
      exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hpow.le)
    have h3 : (H (i + ((m + 1 : ℕ) : ZMod n)) + c + 3 + s (i + ((m + 1 : ℕ) : ZMod n)) / (ℓ - 1)) / (ℓ - 1) ^ m =
        (H (i + ((m + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ m + s (i + ((m + 1 : ℕ) : ZMod n)) / (ℓ - 1) ^ (m + 1) := by
      rw [pow_succ, ← div_div]
      ring
    rw [Finset.sum_range_succ]
    linarith

theorem geom_id (K L : ℝ) (hL : 1 < L) (j : ℕ) :
    (∑ a ∈ Finset.range j, K / L ^ a) + K * L / ((L - 1) * L ^ j) = K * L / (L - 1) := by
  have hL0 : L ≠ 0 := by positivity
  have hL1 : L - 1 ≠ 0 := by
    intro h
    linarith
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : L ^ n ≠ 0 := pow_ne_zero _ hL0
    have key : K / L ^ n + K * L / ((L - 1) * L ^ (n + 1)) = K * L / ((L - 1) * L ^ n) := by
      rw [pow_succ]
      field_simp <;> ring
    linarith [ih, key]

theorem residue_at_truncation : StatResCut := by
  unfold StatResCut
  intro n _ ℓ c G Hm s H i j hℓ hc hG hHm hH hrec
  have hF : StatResFinite := residue_finite_holds
  unfold StatResFinite at hF
  have hq : (1:ℝ) < ℓ - 1 := by linarith
  have hq0 : (0:ℝ) < ℓ - 1 := by linarith
  have h1 := hF n ℓ c s H (by linarith) hrec i j
  have hK0 : (0:ℝ) ≤ 2 * G + c + 3 := by linarith
  have hsum : ∑ a ∈ Finset.range j, (H (i + ((a + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ a ≤
      ∑ a ∈ Finset.range j, (2 * G + c + 3) / (ℓ - 1) ^ a := by
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.mem_range] at ha
    have hb := hH (a + 1) (by omega) (by omega)
    rw [div_eq_mul_inv, div_eq_mul_inv (2 * G + c + 3)]
    apply mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (pow_pos hq0 a).le)
    linarith
  have hg := geom_id (2 * G + c + 3) (ℓ - 1) hq j
  have htail : 0 ≤ (2 * G + c + 3) * (ℓ - 1) / ((ℓ - 1 - 1) * (ℓ - 1) ^ j) := by
    apply div_nonneg (mul_nonneg hK0 hq0.le)
    exact mul_nonneg (by linarith) (pow_pos hq0 j).le
  have hlast : s (i + (j : ZMod n)) / (ℓ - 1) ^ j ≤ Hm / (ℓ - 1) ^ j := by
    rw [div_eq_mul_inv, div_eq_mul_inv Hm]
    exact mul_le_mul_of_nonneg_right (hHm _) (inv_nonneg.mpr (pow_pos hq0 j).le)
  have hfin : (2 * G + c + 3) * (ℓ - 1) / (ℓ - 1 - 1) = (2 * G + c + 3) * (ℓ - 1) / (ℓ - 2) := by
    rw [show ℓ - 1 - 1 = ℓ - 2 by ring]
  linarith

theorem residue_always_holds : StatResAlways := by
  unfold StatResAlways
  intro ℓ s H c r hℓ hsH hr
  have hℓR : (3:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq0 : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
  have hne : (ℓ:ℝ) - 1 ≠ 0 := hq0.ne'
  have hsH' : (s:ℝ) ≤ H := by exact_mod_cast hsH
  have e1 : ((ℓ - 2 : ℕ) : ℝ) = (ℓ:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ ℓ)] <;> norm_num
  have e2 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ)] <;> norm_num
  have hd0 := Nat.cast_div_le (α := ℝ) (m := s + (ℓ - 2)) (n := ℓ - 1)
  rw [Nat.cast_add, e1, e2] at hd0
  have hA : (H:ℝ) / ((ℓ:ℝ) - 1) + 1 - ((s:ℝ) + ((ℓ:ℝ) - 2)) / ((ℓ:ℝ) - 1) =
      ((H:ℝ) - s + 1) / ((ℓ:ℝ) - 1) := by
    field_simp
    ring
  have hA0 : 0 ≤ ((H:ℝ) - s + 1) / ((ℓ:ℝ) - 1) := div_nonneg (by linarith) hq0.le
  have hB : (H:ℝ) * (2 * (ℓ:ℝ) - 1) / ((ℓ:ℝ) - 1) ^ 2 + 1 -
      (((s:ℝ) + ((ℓ:ℝ) - 2)) / ((ℓ:ℝ) - 1) + (s:ℝ) * (ℓ:ℝ) / ((ℓ:ℝ) - 1) ^ 2) =
      (((H:ℝ) - s) * (2 * (ℓ:ℝ) - 1) + ((ℓ:ℝ) - 1)) / ((ℓ:ℝ) - 1) ^ 2 := by
    field_simp
    ring
  have hB0 : 0 ≤ (((H:ℝ) - s) * (2 * (ℓ:ℝ) - 1) + ((ℓ:ℝ) - 1)) / ((ℓ:ℝ) - 1) ^ 2 := by
    apply div_nonneg ?_ (sq_nonneg _)
    have h5 : (0:ℝ) ≤ (H:ℝ) - s := by linarith
    have h6 : (0:ℝ) ≤ 2 * (ℓ:ℝ) - 1 := by linarith
    nlinarith [mul_nonneg h5 h6]
  constructor
  · linarith
  · linarith

theorem residue_quotient_holds : StatResQ := by
  unfold StatResQ
  intro A _ D _ _ N N' π₀ ℓ a r ha hr
  have hA : π₀ ^ a ∈ N'.colon N := Submodule.mem_colon.mpr ha
  have hB : (ℓ : A) ^ r ∈ N'.colon N := Submodule.mem_colon.mpr hr
  have hC := Ideal.add_pow_mem_of_pow_mem_of_le _ hA hB (show a + r ≤ a + r + 1 by omega)
  exact Submodule.mem_colon.mp hC

theorem superadditivity_holds : StatASuper := by
  unfold StatASuper
  intro ℓ _ r s
  unfold aH
  have hd : ℓ ^ (padicValNat ℓ r.factorial + padicValNat ℓ s.factorial) ∣ (r + s).factorial := by
    rw [pow_add]
    exact (Nat.mul_dvd_mul (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add r s)
  have h := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (Nat.factorial_ne_zero _)).mp hd
  omega

theorem frame_invariance_holds : StatFrameInv := by
  unfold StatFrameInv
  intro ℓ _ E _ I Cf Cf' h0 h0' hCf hconv r
  have hsup : StatASuper := superadditivity_holds
  unfold StatASuper at hsup
  have hL : ∀ k : ℕ, ((ℓ : E) ^ k) ∈ I := fun k => pow_mem (natCast_mem I ℓ) k
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [h0', mul_one]
      exact hL _
    · have hs := hconv r hr
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one,
        Finset.sum_range_succ', h0, one_mul, Nat.sub_zero] at hs
      have hCr : Cf' r = -∑ k ∈ Finset.range r, Cf (k + 1) * Cf' (r - (k + 1)) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hs
      rw [hCr, mul_neg, Finset.mul_sum]
      apply neg_mem
      apply sum_mem
      intro k hk
      rw [Finset.mem_range] at hk
      have hle : aH ℓ (k + 1) + aH ℓ (r - (k + 1)) ≤ aH ℓ r := by
        have h7 := hsup ℓ (k + 1) (r - (k + 1))
        rwa [Nat.add_sub_cancel' (by omega)] at h7
      have hcomm : Commute ((ℓ : E) ^ aH ℓ (r - (k + 1))) (Cf (k + 1)) :=
        (Nat.cast_commute ℓ (Cf (k + 1))).pow_left _
      have heq : (ℓ : E) ^ aH ℓ r * (Cf (k + 1) * Cf' (r - (k + 1))) =
          (ℓ : E) ^ (aH ℓ r - (aH ℓ (k + 1) + aH ℓ (r - (k + 1)))) *
            ((ℓ : E) ^ aH ℓ (k + 1) * Cf (k + 1)) *
            ((ℓ : E) ^ aH ℓ (r - (k + 1)) * Cf' (r - (k + 1))) := by
        conv_lhs => rw [← Nat.sub_add_cancel hle, pow_add, pow_add]
        simp only [mul_assoc]
        rw [← mul_assoc ((ℓ : E) ^ aH ℓ (r - (k + 1))) (Cf (k + 1)), hcomm.eq, mul_assoc]
      rw [heq]
      exact mul_mem (mul_mem (hL _) (hCf _)) (ih _ (by omega))

theorem sigma_j_numerical : StatSigJNum := by
  unfold StatSigJNum
  intro ℓ hℓ j y r hj
  have hℓR : (3:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
  have hP : (0:ℝ) < (ℓ:ℝ) ^ (j - 1) := pow_pos (by linarith) _
  rw [← div_div]
  set Y := (y:ℝ) / (ℓ:ℝ) ^ (j - 1) with hYdef
  have e1 : (r:ℝ) * ℓ / ((ℓ:ℝ) - 1) - Y / ((ℓ:ℝ) - 1) = ((ℓ:ℝ) * r - Y) / ((ℓ:ℝ) - 1) := by
    ring
  rcases le_total ((ℓ:ℝ) * r - Y) 0 with h | h
  · rw [max_eq_left h]
    have h8 : 0 ≤ (-((ℓ:ℝ) * r - Y)) / ((ℓ:ℝ) - 1) := div_nonneg (by linarith) hq.le
    have h9 : (-((ℓ:ℝ) * r - Y)) / ((ℓ:ℝ) - 1) = -(((ℓ:ℝ) * r - Y) / ((ℓ:ℝ) - 1)) := by ring
    linarith
  · rw [max_eq_right h]
    have h8 : ((ℓ:ℝ) * r - Y) / ((ℓ:ℝ) - 1) ≤ (ℓ:ℝ) * r - Y := div_le_self h (by linarith)
    linarith

end Formalism.RepresentationBoundsCohomology.N2
end
end

-- bundled from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SecondDescentStatementHolds
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem second_descent_statement_holds : Stat2 := by
  intro ℓ _ hℓ2 A _ D D' _ _ _ _ S Mi hi s H h1 h2 h3 h4 h5 n hn
  set t := (s + (ℓ - 2)) / (ℓ - 1) with ht
  set c := cW ℓ H with hc
  have hℓ3 : 3 ≤ ℓ := by
    have := (Fact.out : ℓ.Prime).two_le
    omega
  have hts : s ≤ (ℓ - 1) * t := by
    have e1 := Nat.div_add_mod (s + (ℓ - 2)) (ℓ - 1)
    have e2 := Nat.mod_lt (s + (ℓ - 2)) (show 0 < ℓ - 1 by omega)
    rw [← ht] at e1
    generalize (ℓ - 1) * t = X at *
    omega
  have hℓR : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ3
  have hℓ1 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have htsR : (s : ℝ) ≤ ((ℓ : ℝ) - 1) * t := by
    have := (Nat.cast_le (α := ℝ)).2 hts
    push_cast [hℓ1] at this
    rw [← hℓ1]
    exact_mod_cast hts
  have hkey : ∀ r ∈ S.R, (S.π ^ t * S.q ^ (c + 2 + t)) • r ∈ S.R' := by
    intro r hr
    rw [S.hq, add_pow, Finset.mul_sum, Finset.sum_smul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    obtain ⟨U, hU⟩ : ∃ U, c + 2 + t - i = U := ⟨_, rfl⟩
    have hU' : c + 2 + t = i + U := by omega
    rw [hU]
    have e : S.π ^ t * (((ℓ : A) * S.w) ^ i * (S.π ^ (ℓ - 1)) ^ U * ((c + 2 + t).choose i : A)) =
        (S.w ^ i * ((c + 2 + t).choose i : A)) * ((ℓ : A) ^ i * S.π ^ ((ℓ - 1) * U + t)) := by
      rw [← pow_mul, pow_add, mul_pow]
      ring
    rw [e, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hj : s ≤ (ℓ - 1) * U + t
    · rw [← Nat.sub_add_cancel hj, pow_add, ← mul_assoc, mul_smul]
      exact Submodule.smul_mem _ _ (h4 r hr)
    · refine h5 i ((ℓ - 1) * U + t) ?_ r hr
      have hU0 : (0 : ℝ) ≤ U := by positivity
      have ht0 : (0 : ℝ) ≤ t := by positivity
      have hiR : (i : ℝ) = c + 2 + t - U := by
        have := congrArg (Nat.cast : ℕ → ℝ) hU'
        push_cast at this
        linarith
      have hpos : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
      have hsl : (s : ℝ) * ℓ ≤ ((ℓ : ℝ) - 1) * t * ℓ := mul_le_mul_of_nonneg_right htsR (by linarith)
      have hcU : (0 : ℝ) ≤ U * ((ℓ : ℝ) - 1) := mul_nonneg hU0 (by linarith)
      have hj' : (((ℓ - 1) * U + t : ℕ) : ℝ) = ((ℓ : ℝ) - 1) * U + t := by
        push_cast [hℓ1]
        ring
      rw [hj', hiR]
      have hdiv : ((s : ℝ) - (((ℓ : ℝ) - 1) * U + t)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤ 2 + t - U := by
        rw [div_le_iff₀ hpos]
        nlinarith
      linarith
  have hR1 := hkey _ (h1 n hn)
  have hR2 : (S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n) ∈ S.R' := by
    rw [mul_smul]
    exact Submodule.smul_mem _ _ hR1
  have hsp := h2 _ hR2
  have hφ : S.φ (S.π ^ (Mi + hi + c + 2 + t) • n) = S.q ^ hi •
      ((S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n)) := by
    rw [S.φ_smul, map_pow, S.φπ, smul_smul, smul_smul]
    congr 1
    ring
  apply h3 _ (Submodule.smul_mem _ _ hn)
  rw [hφ]
  exact hsp

end Formalism.RepresentationBoundsCohomology.N2
end
end

-- bundled from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SumVal
section
namespace Formalism.RepresentationBoundsCohomology.N2.SumVal

open Finset

variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma sum_Ioc_add (n w : ℕ) :
    (∑ k ∈ Ioc n (n + w), padicValNat ℓ k) + padicValNat ℓ n.factorial =
      padicValNat ℓ (n + w).factorial := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) (Nat.factorial_ne_zero _), ← ih]
    ring

lemma sum_Ioc_eq (n w : ℕ) :
    (∑ k ∈ Ioc n (n + w), padicValNat ℓ k) =
      padicValNat ℓ w.factorial + padicValNat ℓ ((n + w).choose w) := by
  have h1 := sum_Ioc_add ℓ n w
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left w n)
  rw [Nat.add_sub_cancel] at h2
  rw [← h2, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.mul_ne_zero (Nat.choose_pos (Nat.le_add_left w n)).ne'
      (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.choose_pos (Nat.le_add_left w n)).ne' (Nat.factorial_ne_zero _)] at h1
  omega

lemma one_lt_cast : (1 : ℝ) < (ℓ : ℝ) := by
  exact_mod_cast (Fact.out : ℓ.Prime).one_lt

lemma val_factorial_le (w : ℕ) :
    (padicValNat ℓ w.factorial : ℝ) ≤ (w : ℝ) / ((ℓ : ℝ) - 1) := by
  have h := (Fact.out : ℓ.Prime).sub_one_mul_multiplicity_factorial (n := w)
  rw [← Nat.padicValNat_def] at h
  have h' : (ℓ - 1) * padicValNat ℓ w.factorial ≤ w := by rw [h]; exact Nat.sub_le _ _
  have hl := one_lt_cast ℓ
  rw [le_div_iff₀ (by linarith)]
  have e : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (Fact.out : ℓ.Prime).one_lt.le]; simp
  have h2 : (((ℓ - 1) * padicValNat ℓ w.factorial : ℕ) : ℝ) ≤ w := by exact_mod_cast h'
  rw [Nat.cast_mul, e] at h2
  linarith

lemma val_choose_le (N w : ℕ) :
    (padicValNat ℓ (N.choose w) : ℝ) ≤ Real.logb ℓ N := by
  have h1 : padicValNat ℓ (N.choose w) ≤ Nat.log ℓ N := by
    rw [Nat.padicValNat_def, ← Nat.factorization_def _ (Fact.out : ℓ.Prime)]
    exact Nat.factorization_choose_le_log
  calc (padicValNat ℓ (N.choose w) : ℝ) ≤ (Nat.log ℓ N : ℝ) := by exact_mod_cast h1
    _ ≤ Real.logb ℓ N := Real.natLog_le_logb N ℓ

lemma sum_nat_le (n y D : ℕ) (hD : 1 ≤ D) (T : Finset ℕ)
    (hT : ∀ k ∈ T, n < k ∧ k ≤ n + (y + 1) ∧ k ≤ D) :
    ((∑ k ∈ T, padicValNat ℓ k : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  set N' := min (n + (y + 1)) D with hN'
  have hsub : T ⊆ Ioc n N' := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := hT k hk
    exact Finset.mem_Ioc.2 ⟨h1, le_min h2 h3⟩
  have hle : (∑ k ∈ T, padicValNat ℓ k) ≤ ∑ k ∈ Ioc n N', padicValNat ℓ k :=
    Finset.sum_le_sum_of_subset hsub
  have hl := one_lt_cast ℓ
  have hD0 : (0 : ℝ) ≤ Real.logb ℓ D := Real.logb_nonneg hl (by exact_mod_cast hD)
  by_cases hnN : n ≤ N'
  · obtain ⟨w, hw⟩ : ∃ w, N' = n + w := ⟨N' - n, by omega⟩
    rw [hw, sum_Ioc_eq] at hle
    have hwle : w ≤ y + 1 := by have := min_le_left (n + (y + 1)) D; omega
    have hND : n + w ≤ D := by have := min_le_right (n + (y + 1)) D; omega
    have e1 := val_factorial_le ℓ w
    have e2 := val_choose_le ℓ (n + w) w
    have e3 : (w : ℝ) / ((ℓ : ℝ) - 1) ≤ ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hwle) (by linarith)
    have e4 : Real.logb ℓ (n + w : ℕ) ≤ Real.logb ℓ D := by
      rcases Nat.eq_zero_or_pos (n + w) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.logb_zero]; exact hD0
      · exact Real.logb_le_logb_of_le hl (by exact_mod_cast h0) (by exact_mod_cast hND)
    have e5 : ((∑ k ∈ T, padicValNat ℓ k : ℕ) : ℝ) ≤
        (padicValNat ℓ w.factorial : ℝ) + padicValNat ℓ ((n + w).choose w) := by exact_mod_cast hle
    linarith
  · have hE : Ioc n N' = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hE, Finset.sum_empty, Nat.le_zero] at hle
    rw [hle]
    have : (0 : ℝ) ≤ ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) := div_nonneg (by positivity) (by linarith)
    push_cast
    linarith

end Formalism.RepresentationBoundsCohomology.N2.SumVal

namespace Formalism.RepresentationBoundsCohomology.N2

open Finset

private theorem sum_padicValInt_sub_le_of_injective_bound (ℓ : ℕ) [Fact ℓ.Prime] (S' : Finset ℤ) (a : ℤ) (f : ℤ → ℤ)
    (n y D : ℕ) (hD : 1 ≤ D) (hf : ∀ b ∈ S', (n : ℤ) < f b ∧ f b ≤ n + (y + 1) ∧ f b ≤ D)
    (hinj : ∀ b ∈ S', ∀ b' ∈ S', f b = f b' → b = b')
    (hg : ∀ b ∈ S', padicValInt ℓ (a - b) = padicValNat ℓ (f b).toNat) :
    ((∑ b ∈ S', padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  have hsum : ∑ b ∈ S', padicValInt ℓ (a - b) =
      ∑ k ∈ S'.image (fun b => (f b).toNat), padicValNat ℓ k := by
    rw [Finset.sum_image]
    · exact Finset.sum_congr rfl hg
    · intro b hb b' hb' h
      have h' : (f b).toNat = (f b').toNat := h
      have h1 := (hf b hb).1
      have h2 := (hf b' hb').1
      exact hinj b hb b' hb' (by omega)
  rw [hsum]
  refine SumVal.sum_nat_le ℓ n y D hD _ ?_
  intro k hk
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hk
  obtain ⟨h1, h2, h3⟩ := hf b hb
  omega

private theorem sum_padicValInt_sub_le_of_lt_forall (ℓ : ℕ) [Fact ℓ.Prime] (m : ℤ) (y D : ℕ) (S' : Finset ℤ) (a : ℤ)
    (hS : S' ⊆ Finset.Icc m (m + y)) (hD : 1 ≤ D) (hSD : ∀ b ∈ S', |a - b| ≤ D)
    (hlt : ∀ b ∈ S', b < a) :
    ((∑ b ∈ S', padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  refine sum_padicValInt_sub_le_of_injective_bound ℓ S' a (fun b => a - b) (a - m - y - 1).toNat y D hD ?_ ?_ ?_
  · intro b hb
    have h1 := Finset.mem_Icc.1 (hS hb)
    have h2 := abs_le.1 (hSD b hb)
    have h3 := hlt b hb
    beta_reduce
    omega
  · intro b _ b' _ h
    have h' : a - b = a - b' := h
    omega
  · intro b hb
    have h3 := hlt b hb
    simp only [padicValInt, Nat.padicValNat_def]
    congr 1
    omega

private theorem sum_padicValInt_sub_le_of_gt_forall (ℓ : ℕ) [Fact ℓ.Prime] (m : ℤ) (y D : ℕ) (S' : Finset ℤ) (a : ℤ)
    (hS : S' ⊆ Finset.Icc m (m + y)) (hD : 1 ≤ D) (hSD : ∀ b ∈ S', |a - b| ≤ D)
    (hgt : ∀ b ∈ S', a < b) :
    ((∑ b ∈ S', padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  refine sum_padicValInt_sub_le_of_injective_bound ℓ S' a (fun b => b - a) (m - a - 1).toNat y D hD ?_ ?_ ?_
  · intro b hb
    have h1 := Finset.mem_Icc.1 (hS hb)
    have h2 := abs_le.1 (hSD b hb)
    have h3 := hgt b hb
    beta_reduce
    omega
  · intro b _ b' _ h
    have h' : b - a = b' - a := h
    omega
  · intro b hb
    have h3 := hgt b hb
    simp only [padicValInt, Nat.padicValNat_def]
    congr 1
    omega

theorem valuation_sum_at_endpoint : StatSumValEnd := by
  intro ℓ _ m y D S a hS ha hD hSD
  have hS' : S.erase a ⊆ Finset.Icc m (m + y) := (Finset.erase_subset a S).trans hS
  have hSD' : ∀ b ∈ S.erase a, |a - b| ≤ D := fun b hb => hSD b (Finset.mem_of_mem_erase hb)
  rcases ha with ha | ha
  · refine sum_padicValInt_sub_le_of_gt_forall ℓ m y D (S.erase a) a hS' hD hSD' fun b hb => ?_
    have h1 := Finset.mem_Icc.1 (hS' hb)
    have h2 := Finset.ne_of_mem_erase hb
    omega
  · refine sum_padicValInt_sub_le_of_lt_forall ℓ m y D (S.erase a) a hS' hD hSD' fun b hb => ?_
    have h1 := Finset.mem_Icc.1 (hS' hb)
    have h2 := Finset.ne_of_mem_erase hb
    omega

theorem valuation_sum_general_index : StatSumValGen := by
  intro ℓ _ m y D S a hS hD hSD
  have hS' : S.erase a ⊆ Finset.Icc m (m + y) := (Finset.erase_subset a S).trans hS
  have hSD' : ∀ b ∈ S.erase a, |a - b| ≤ D := fun b hb => hSD b (Finset.mem_of_mem_erase hb)
  rw [← Finset.sum_filter_add_sum_filter_not (S.erase a) (fun b => b < a), Nat.cast_add, two_mul]
  apply add_le_add
  · exact sum_padicValInt_sub_le_of_lt_forall ℓ m y D _ a ((Finset.filter_subset _ _).trans hS') hD
      (fun b hb => hSD' b (Finset.mem_of_mem_filter b hb)) (fun b hb => (Finset.mem_filter.1 hb).2)
  · refine sum_padicValInt_sub_le_of_gt_forall ℓ m y D _ a ((Finset.filter_subset _ _).trans hS') hD
      (fun b hb => hSD' b (Finset.mem_of_mem_filter b hb)) (fun b hb => ?_)
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    have := Finset.ne_of_mem_erase hb1
    omega

end Formalism.RepresentationBoundsCohomology.N2
end

