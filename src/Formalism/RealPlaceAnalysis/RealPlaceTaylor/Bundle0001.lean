module

public import Formalism.RealPlaceAnalysis.Bundle0001

@[expose] public section

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW
section
open Finset

noncomputable section

namespace Formalism.REAL

lemma casKHW_two_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    2 * rhoC ε a = ∑ b, ((if a < b ∧ ε b = ε a then (1:ℝ) else 0) -
      (if b < a ∧ ε b = ε a then (1:ℝ) else 0)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  unfold rhoC; ring

def casKHW_coef {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a b : Fin n) : ℝ :=
  if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0) else 0

lemma casKHW_term (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V)
    (hG : GlRel E) (hK : KHighest ε E μ w) (a b : Fin n) :
    (if ε a = ε b then E a b * E b a else 0) w = ((casKHW_coef ε μ a b : ℝ) : ℂ) • w := by
  unfold casKHW_coef
  by_cases h : ε a = ε b
  · simp only [h, if_true]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have hne : a ≠ b := ne_of_lt hab
      simp only [hne, if_false, hab, if_true]
      have h1 := congrArg (fun T : Module.End ℂ V => T w) (hG a b b a)
      simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h1
      have h0 : E a b w = 0 := hK.2 a b hab h
      rw [h0, map_zero, sub_zero, hK.1 a, hK.1 b] at h1
      rw [Module.End.mul_apply, h1]
      push_cast
      rw [sub_smul]
    · simp only [if_true, Module.End.mul_apply, hK.1 a, map_smul, smul_smul]
      push_cast; ring_nf
    · have hne : a ≠ b := ne_of_gt hab
      have hnl : ¬ a < b := not_lt_of_gt hab
      simp only [hne, if_false, hnl]
      rw [Module.End.mul_apply, hK.2 b a hab h.symm, map_zero]
      simp
  · simp [h]

lemma casKHW_arith {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    ∑ a, ∑ b, casKHW_coef ε μ a b = nsq (μ + rhoC ε) - nsq (rhoC ε) := by
  have hpt : ∀ a b, casKHW_coef ε μ a b =
      (if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a else 0) -
        (if a < b ∧ ε a = ε b then μ b else 0) := by
    intro a b
    unfold casKHW_coef
    by_cases h : ε a = ε b
    · rcases lt_trichotomy a b with hab | rfl | hab
      · simp [h, hab, ne_of_lt hab]
      · simp
      · simp [h, ne_of_gt hab, not_lt_of_gt hab]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      by_cases hab : a = b
      · exact absurd (congrArg ε hab) h
      · simp [h, h', hab]
  simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e1 : ∑ a : Fin n, ∑ b : Fin n, (if a = b then μ a ^ 2 else 0) = ∑ a, μ a ^ 2 := by
    simp
  have e2 : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε a = ε b then μ b else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) := by
    rw [Finset.sum_comm]
  have e3 : ∀ a, ∑ b : Fin n, (if a < b ∧ ε b = ε a then μ a else 0) -
      ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) = μ a * (2 * rhoC ε a) := by
    intro a
    rw [casKHW_two_rhoC, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [e1, e2, add_sub_assoc, ← Finset.sum_sub_distrib]
  simp_rw [e3]
  unfold nsq dot
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]; ring

theorem compactCasimirOnHighestWeight_holds : CasKHighest := by
  intro V _ _ n ε E μ w hG hK
  unfold CasK
  simp only [LinearMap.sum_apply]
  simp_rw [casKHW_term V n ε E μ w hG hK]
  rw [← casKHW_arith ε μ]
  simp_rw [← Finset.sum_smul]
  push_cast
  rfl

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
section
open Matrix

noncomputable section

namespace Formalism.REAL

private lemma inG_iff_star_signed_entries_eq_zero {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0 := by
  unfold inG Jm
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
      Matrix.zero_apply] using this
  · intro h
    ext i j
    simpa only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
      Matrix.zero_apply] using h i j

lemma f1auxiliary_hs_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.star_def, Complex.mul_re]

lemma continuous_hs_real_place_taylor {n : ℕ} : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp (continuous_apply i)).norm.pow 2

lemma f1auxiliary_hs_one (n : ℕ) : hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp only [hs, Matrix.one_apply]
  have key : ∀ i : Fin n, ∑ j, ‖(if i = j then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  simp [key]

theorem ball_open_holds : BallOpen := by
  intro n R hR
  refine ⟨{g | hs g < R}, isOpen_lt continuous_hs_real_place_taylor continuous_const, ?_, fun g hg => hg⟩
  show hs (1 : Matrix (Fin n) (Fin n) ℂ) < R
  rw [f1auxiliary_hs_one]
  exact hR

lemma f1auxiliary_closed {n : ℕ} (ε : Fin n → Bool) : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

lemma f1auxiliary_entry_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ hs g := by
  unfold hs
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2)
          (fun k _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem hermitian_small_ball : HSBall := by
  intro n ε
  refine ⟨fun R => ?_, fun g k hk => ⟨?_, ?_⟩⟩
  · have hcpt : IsCompact (Set.pi Set.univ fun _ : Fin n =>
        Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) (Real.sqrt R)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    refine hcpt.of_isClosed_subset ((f1auxiliary_closed ε).inter (isClosed_le continuous_hs_real_place_taylor continuous_const)) ?_
    rintro g ⟨_, hg⟩ i _ j _
    have h1 := (f1auxiliary_entry_le g i j).trans hg
    simpa using Real.abs_le_sqrt h1
  · have hk1 : k * kᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.1 hk.1
    rw [f1auxiliary_hs_eq, f1auxiliary_hs_eq, conjTranspose_mul]
    congr 1
    rw [show kᴴ * gᴴ * (g * k) = kᴴ * (gᴴ * g * k) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, Matrix.mul_assoc, hk1, Matrix.mul_one]
  · have hk2 : kᴴ * k = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.1 hk.1
    rw [f1auxiliary_hs_eq, f1auxiliary_hs_eq, conjTranspose_mul]
    congr 1
    rw [show gᴴ * kᴴ * (k * g) = gᴴ * (kᴴ * k) * g by simp only [Matrix.mul_assoc], hk2, Matrix.mul_one]

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard
section
open Finset

noncomputable section

namespace Formalism.REAL

lemma rho_card_le {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) ≤ n := by
  have h : (univ.filter p).card ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast h

lemma rho_rhoN_bound {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by
  unfold rhoN
  have h1 := rho_card_le (fun b => a < b ∧ ε b ≠ ε a)
  have h2 := rho_card_le (fun b => b < a ∧ ε b ≠ ε a)
  have h3 := Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card
  have h4 := Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card
  constructor <;> linarith

theorem half_sum_roots_standard : RhoStd := by
  intro n ε a
  unfold rhoC rhoN
  have k1 : #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} = #{b | a < b} := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h1 : a < b <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]
  have k2 : #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = #{b | b < a} := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h1 : b < a <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]
  have k3 : #{b | a < b} = n - 1 - (a : ℕ) := by
    rw [show (univ.filter fun b : Fin n => a < b) = Finset.Ioi a by ext b; simp]
    exact Fin.card_Ioi a
  have k4 : #{b | b < a} = (a : ℕ) := by
    rw [show (univ.filter fun b : Fin n => b < a) = Finset.Iio a by ext b; simp]
    exact Fin.card_Iio a
  have ha := a.isLt
  have r1 : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℝ)
      + ((a : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast (show #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} + (a : ℕ) + 1 = n by omega)
  have r2 : ((#{b | b < a ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | b < a ∧ ε b ≠ ε a} : ℕ) : ℝ)
      = ((a : ℕ) : ℝ) := by
    exact_mod_cast (show #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = (a : ℕ) by omega)
  linarith

lemma rho_nsq_root {n : ℕ} (x : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    nsq (x + root a b) = nsq x + 2 * (x a - x b) + 2 := by
  have hs : ∀ i, (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i *
        (x + (Pi.single a 1 - Pi.single b 1) : Fin n → ℝ) i
      = x i * x i + (2 * x i + 1) * (Pi.single a (1 : ℝ) : Fin n → ℝ) i +
        (1 - 2 * x i) * (Pi.single b (1 : ℝ) : Fin n → ℝ) i := by
    intro i
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [Pi.single_apply, h1, h2, hab, Ne.symm hab] <;> ring
  unfold root nsq dot
  rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [Pi.single_apply] <;> ring

theorem omega_eigenvalue_holds : OmEigen := by
  intro n ε lam a b hab
  have e : lam + rhoN ε - rhoC ε + root a b + rhoC ε = (lam + rhoN ε - rhoC ε + rhoC ε) + root a b := by
    abel
  rw [e, rho_nsq_root _ a b hab]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem unitary_spectral_gap : UGap := by
  intro n ε lam g a b _ _ hg
  obtain ⟨d1, _⟩ := rho_rhoN_bound ε a
  obtain ⟨_, d2⟩ := rho_rhoN_bound ε b
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
section
open Matrix

noncomputable section

namespace Formalism.REAL

private lemma Jm_mul_self_eq_oneRealPlaceTaylor {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private lemma Jm_conjTranspose_eq {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  rw [Pi.star_apply]
  split_ifs <;> simp

lemma f1alg_isUnit_J {n : ℕ} (ε : Fin n → Bool) : IsUnit (Jm ε) :=
  ⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_oneRealPlaceTaylor ε, Jm_mul_self_eq_oneRealPlaceTaylor ε⟩, rfl⟩

lemma f1alg_inv_J {n : ℕ} (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε :=
  Matrix.inv_eq_left_inv (Jm_mul_self_eq_oneRealPlaceTaylor ε)

lemma f1alg_JJ_left {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * A) = A := by
  rw [← Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.one_mul]

lemma f1alg_comm_iff {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * Jm ε = Jm ε * A ↔ Jm ε * A * Jm ε = A := by
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, f1alg_JJ_left]
  · intro h
    calc A * Jm ε = (Jm ε * A * Jm ε) * Jm ε := by rw [h]
      _ = Jm ε * A := by rw [Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one]

lemma f1alg_anti_iff {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * Jm ε = -(Jm ε * A) ↔ Jm ε * A * Jm ε = -A := by
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.mul_neg, f1alg_JJ_left]
  · intro h
    calc A * Jm ε = -(Jm ε * A * Jm ε) * Jm ε := by rw [h, neg_neg]
      _ = -(Jm ε * A) := by rw [Matrix.neg_mul, Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one]

lemma f1alg_inG_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ Xᴴ = -(Jm ε * X * Jm ε) := by
  unfold inG
  constructor
  · intro h
    have h' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h', Matrix.neg_mul]
  · intro h
    rw [h, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one, neg_add_cancel]

lemma f1alg_inK_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ Xᴴ = -X ∧ X * Jm ε = Jm ε * X := by
  unfold inK
  rw [f1alg_inG_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_comm_iff ε X).mp h2], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_comm_iff ε X).mp h2], h2⟩

lemma mem_cartanP_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inP ε X ↔ Xᴴ = X ∧ X * Jm ε = -(Jm ε * X) := by
  unfold inP
  rw [f1alg_inG_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_anti_iff ε X).mp h2, neg_neg], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_anti_iff ε X).mp h2, neg_neg], h2⟩

lemma f1alg_exp_inUJ {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  unfold inUJ
  have hY' : Yᴴ = Jm ε * (-Y) * Jm ε := by
    rw [(f1alg_inG_iff ε Y).mp hY, Matrix.mul_neg, Matrix.neg_mul]
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, Jm_mul_self_eq_oneRealPlaceTaylor ε, Jm_mul_self_eq_oneRealPlaceTaylor ε⟩
  have hconj : NormedSpace.exp (Jm ε * (-Y) * Jm ε) = Jm ε * NormedSpace.exp (-Y) * Jm ε :=
    Matrix.exp_units_conj U (-Y)
  have hinv : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hY', hconj]
  simp only [Matrix.mul_assoc]
  rw [f1alg_JJ_left, hinv, Matrix.mul_one]

theorem indefinite_unitary_closed : UJClosed := by
  intro n ε
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem exp_indefinite_unitary_holds : ExpUJ := by
  intro n ε X hX t
  apply f1alg_exp_inUJ
  unfold inG at hX ⊢
  have hs : ((t : ℂ) • X)ᴴ = (t : ℂ) • Xᴴ := by
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  rw [hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem indefinite_unitary_inv_closed : UJInv := by
  intro n ε g h
  have h2 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_self_eq_oneRealPlaceTaylor]
  exact ⟨mul_eq_one_comm.mp h2, h2⟩

theorem one_parameter_subgroup_holds : OneParam := by
  intro n X s t
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

theorem parabolic_character_holds : PChar := by
  intro n ε X
  exact ⟨mem_cartanP_iff ε X, fun h => (f1alg_anti_iff ε X).mp h.2⟩

lemma f1alg_unit_iff {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ gᴴ * g = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

lemma mem_unitaryGroup_iff_mul_conjTranspose {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ g * gᴴ = 1 := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]

theorem maximal_compact_facts : KFacts := by
  intro n ε

  have h1 : ∀ g ∈ Kset ε, inUJ ε g := by
    rintro g ⟨hu, hc⟩
    unfold inUJ
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, (f1alg_unit_iff g).mp hu, Matrix.one_mul]

  have h5 : ∀ g, g ∈ Kset ε ↔ (inUJ ε g ∧ g ∈ Matrix.unitaryGroup (Fin n) ℂ) := by
    intro g
    constructor
    · intro hg
      exact ⟨h1 g hg, hg.1⟩
    · rintro ⟨hJ, hu⟩
      refine ⟨hu, ?_⟩
      unfold inUJ at hJ
      calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [hJ]
        _ = (g * gᴴ) * Jm ε * g := by simp only [Matrix.mul_assoc]
        _ = Jm ε * g := by rw [(mem_unitaryGroup_iff_mul_conjTranspose g).mp hu, Matrix.one_mul]
  refine ⟨h1, ?_, ?_, ?_, h5⟩
  ·
    have hcl : IsClosed (Kset ε) := by
      have : Kset ε = {g | gᴴ * g = 1} ∩ {g | g * Jm ε = Jm ε * g} := by
        ext g
        simp only [Kset, Set.mem_setOf_eq, Set.mem_inter_iff, f1alg_unit_iff]
      rw [this]
      exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_id))
    have hsub : Kset ε ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
        (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) := by
      intro g hg i _ j _
      rw [Metric.mem_closedBall, dist_zero_right]
      exact entry_norm_bound_of_unitary hg.1 i j
    exact IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _) hcl hsub
  · refine ⟨?_, rfl⟩
    rw [f1alg_unit_iff, Jm_conjTranspose_eq, Jm_mul_self_eq_oneRealPlaceTaylor]
  · rintro X ⟨hG, hc⟩
    have hX : Xᴴ = -X := ((f1alg_inK_iff ε X).mp ⟨hG, hc⟩).1
    refine ⟨?_, ?_⟩
    · rw [f1alg_unit_iff, ← Matrix.exp_conjTranspose, hX,
        ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
        NormedSpace.exp_zero]
    · exact ((Commute.exp_right (show Commute (Jm ε) X from hc.symm)).symm).eq

end Formalism.REAL
end
end

