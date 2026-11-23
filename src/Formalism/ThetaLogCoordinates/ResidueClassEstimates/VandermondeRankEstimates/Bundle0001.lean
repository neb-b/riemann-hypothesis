module

public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.Bundle0001

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.AdmissibleSmallRatio
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

theorem geom_range_le (p m0 n : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range n, (1 / (p : ℝ) ^ (m0 + i)) ≤ 2 / (p : ℝ) ^ m0 - 2 / (p : ℝ) ^ (m0 + n) := by
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hx : (0:ℝ) < (p:ℝ)^(m0+n) := pow_pos hP0 _
    have e : (2:ℝ) / (p:ℝ)^(m0+(n+1)) ≤ 1 / (p:ℝ)^(m0+n) := by
      rw [← add_assoc, pow_succ, div_le_div_iff₀ (by positivity) hx]
      nlinarith
    have e2 : (2:ℝ) / (p:ℝ)^(m0+n) = 2 * (1 / (p:ℝ)^(m0+n)) := by ring
    linarith

theorem geometricSumDistinct : GeomDistinct := by
  intro p m0 s hp hs
  have hP0 : (0:ℝ) < p := by
    have : (2:ℝ) ≤ p := by exact_mod_cast hp
    linarith
  obtain ⟨n, hn⟩ : ∃ n, ∀ D ∈ s, D < m0 + n :=
    ⟨s.sup (fun x => x) + 1, fun D hD => by
      have := Finset.le_sup (f := fun x => x) hD
      omega⟩
  have hsub : s ⊆ (Finset.range n).image (fun i => m0 + i) := by
    intro D hD
    simp only [Finset.mem_image, Finset.mem_range]
    have h1 := hn D hD
    have h2 := hs D hD
    exact ⟨D - m0, by omega, by omega⟩
  calc ∑ D ∈ s, (1 / (p:ℝ)^D)
      ≤ ∑ D ∈ (Finset.range n).image (fun i => m0 + i), (1 / (p:ℝ)^D) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ i ∈ Finset.range n, (1 / (p:ℝ)^(m0+i)) := by
        rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
    _ ≤ 2 / (p:ℝ)^m0 - 2 / (p:ℝ)^(m0+n) := geom_range_le p m0 n hp
    _ ≤ 2 / (p:ℝ)^m0 := by
        have : (0:ℝ) ≤ 2 / (p:ℝ)^(m0+n) := by positivity
        linarith

theorem admissibleSmallRatio : AdmissibleSmallRatio := by
  intro p k Ns D1 L1 R R' a Y Qn be hp hk hNs hY ha hQn hL1 hbe h7 h8
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hNs' : (1:ℝ) ≤ Ns := by exact_mod_cast hNs
  have hY0 : (0:ℝ) < Y := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hNs0 : (0:ℝ) < Ns := by linarith
  have hR : (0:ℝ) < (p:ℝ)^R := pow_pos hP0 _
  have hR' : (0:ℝ) < (p:ℝ)^R' := pow_pos hP0 _
  have hD1 : (0:ℝ) < (p:ℝ)^D1 := pow_pos hP0 _
  have hL : (0:ℝ) < (p:ℝ)^L1 := pow_pos hP0 _
  have hT : (0:ℝ) < Qn * (p:ℝ)^R' / (p:ℝ)^R := by positivity
  have sA : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) ≤
      (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) :=
    div_le_div_of_nonneg_right hbe hT.le
  have sB : (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) =
      4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) := by
    rw [show R+D1+L1+1 = R + D1 + L1 + 1 from rfl, pow_succ, pow_add, pow_add]
    field_simp
  have ha7 : a < (p:ℝ)^R' * (8 * p * Y * (k:ℝ)^2 * Ns * ((p:ℝ)^D1 * Qn)) := by
    rwa [div_lt_iff₀ (by positivity)] at h7
  have sC : 4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) <
      32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [div_lt_div_iff₀ (by positivity) hL]
    have := mul_lt_mul_of_pos_left ha7 (show (0:ℝ) < 4 * (p:ℝ)^L1 by positivity)
    nlinarith
  have hPL : (p:ℝ)^L1 = (p:ℝ)^(L1-1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have s2 : 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 ≤ 1 / (4 * p * Y) := by
    rw [div_le_div_iff₀ hL (by positivity), hPL]
    have := mul_le_mul_of_nonneg_right h8 hP0.le
    nlinarith
  have s1 : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) < 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [sB] at sA
    exact lt_of_le_of_lt sA sC
  have s3 : 1 / (4 * p * Y) ≤ 1 / (4 * Y) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  exact ⟨s1, s2, by linarith⟩

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

-- bundled from Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LDigits
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

section Digits

variable {I1 I2 : Type}

end Digits

section Residue

def cnt (T Q r c : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin T)).filter (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card

lemma shift_iff (Q a s c : ℕ) (hQ : 1 ≤ Q) :
    (a + s) % Q = c % Q ↔ s % Q = (c + (Q - 1) * a) % Q := by
  obtain ⟨R, rfl⟩ : ∃ R, Q = R + 1 := ⟨Q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  constructor
  · intro h
    have h0 : Nat.ModEq (R + 1) (a + s) c := h
    have h1 : Nat.ModEq (R + 1) (a + s + R * a) (c + R * a) := h0.add_right (R * a)
    have h2 : a + s + R * a = s + (R + 1) * a := by ring
    rw [h2] at h1
    have h3 : (s + (R + 1) * a) % (R + 1) = (c + R * a) % (R + 1) := h1
    rw [Nat.add_mul_mod_self_left] at h3
    exact h3
  · intro h
    have h0 : Nat.ModEq (R + 1) s (c + R * a) := h
    have h1 : Nat.ModEq (R + 1) (a + s) (a + (c + R * a)) := h0.add_left a
    have h2 : a + (c + R * a) = c + (R + 1) * a := by ring
    rw [h2] at h1
    have h3 : (a + s) % (R + 1) = (c + (R + 1) * a) % (R + 1) := h1
    rw [Nat.add_mul_mod_self_left] at h3
    exact h3

lemma cnt_succ (T Q r c : ℕ) (hQ : 1 ≤ Q) :
    cnt T Q (r + 1) c = ∑ a : Fin T, cnt T Q r (c + (Q - 1) * a) := by
  have hbij : Function.Bijective
      (fun p : Fin T × (Fin r → Fin T) => (Fin.cons p.1 p.2 : Fin (r + 1) → Fin T)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => (u 0, Fin.tail u), fun p => ?_, fun u => ?_⟩
    · simp
    · simp
  simp only [cnt, Finset.card_filter]
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective _ hbij _ _ (fun p => ?_)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  exact if_congr (shift_iff _ _ _ _ hQ).symm rfl rfl

lemma cnt_one (T Q c : ℕ) (hT : T ≤ Q) : cnt T Q 1 c = if c % Q < T then 1 else 0 := by
  have hbij : Function.Bijective (fun a : Fin T => (fun _ : Fin 1 => a)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => u 0, fun a => rfl, fun u => ?_⟩
    funext i
    rw [Subsingleton.elim i 0]
  have step : (∑ u : Fin 1 → Fin T, if (∑ l, (u l : ℕ)) % Q = c % Q then 1 else 0) =
      ∑ a : Fin T, if (a : ℕ) = c % Q then 1 else 0 := by
    symm
    refine Fintype.sum_bijective _ hbij _ _ (fun a => ?_)
    simp only [Fin.sum_univ_one]
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt hT)]
  unfold cnt
  rw [Finset.card_filter, step]
  by_cases h : c % Q < T
  · rw [if_pos h, Finset.sum_eq_single (⟨c % Q, h⟩ : Fin T)]
    · simp
    · intro b _ hb
      exact if_neg (fun e => hb (Fin.ext e))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun e => h (lt_of_eq_of_lt e.symm a.isLt))

private theorem eq_of_add_pred_mul_mod_eq_of_lt (Q c a b : ℕ) (hQ : 1 ≤ Q) (ha : a < Q) (hb : b < Q)
    (h : (c + (Q - 1) * a) % Q = (c + (Q - 1) * b) % Q) : a = b := by
  have h1 : (a + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q a _ c hQ).2 (Nat.mod_mod _ _)
  have h2 : (b + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q b _ c hQ).2 (by rw [Nat.mod_mod, h])
  have h3 : Nat.ModEq Q (a + (c + (Q - 1) * a) % Q) (b + (c + (Q - 1) * a) % Q) :=
    h1.trans h2.symm
  have h4 : Nat.ModEq Q a b := Nat.ModEq.add_right_cancel' _ h3
  have h5 : a % Q = b % Q := h4
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h5

lemma cnt_two (T Q c : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) : T - (Q - T) ≤ cnt T Q 2 c := by
  have h2 : cnt T Q 2 c = ∑ a : Fin T, cnt T Q 1 (c + (Q - 1) * a) :=
    cnt_succ T Q 1 c hQ
  rw [h2]
  simp only [cnt_one T Q _ hT]
  have hsplit : (∑ a : Fin T, if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
      ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card = T := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    have hone : ∀ a : Fin T, ((if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
        (if ¬ (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) : ℕ) = 1 := by
      intro a
      by_cases h : (c + (Q - 1) * (a : ℕ)) % Q < T <;> simp [h]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hle : ((Finset.univ : Finset (Fin T)).filter
      (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ Q - T := by
    have hc : ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ (Finset.Ico T Q).card := by
      apply Finset.card_le_card_of_injOn (fun a : Fin T => (c + (Q - 1) * (a : ℕ)) % Q)
      · intro a ha
        have ha' : T ≤ (c + (Q - 1) * (a : ℕ)) % Q := by simpa using ha
        simp only [Finset.mem_coe, Finset.mem_Ico]
        exact ⟨ha', Nat.mod_lt _ (by omega)⟩
      · intro a _ b _ hab
        exact Fin.ext (eq_of_add_pred_mul_mod_eq_of_lt Q c a b hQ (lt_of_lt_of_le a.isLt hT)
          (lt_of_lt_of_le b.isLt hT) hab)
    rw [Nat.card_Ico] at hc
    exact hc
  omega

lemma cnt_ge (T Q : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) (s : ℕ) :
    ∀ c, T ^ s * (T - (Q - T)) ≤ cnt T Q (s + 2) c := by
  induction s with
  | zero =>
    intro c
    rw [pow_zero, one_mul]
    exact cnt_two T Q c hQ hT
  | succ s ih =>
    intro c
    rw [show s + 1 + 2 = (s + 2) + 1 by omega, cnt_succ T Q (s + 2) c hQ]
    calc T ^ (s + 1) * (T - (Q - T)) = ∑ _a : Fin T, T ^ s * (T - (Q - T)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
      _ ≤ ∑ a : Fin T, cnt T Q (s + 2) (c + (Q - 1) * a) :=
          Finset.sum_le_sum (fun a _ => ih _)

private theorem pow_mul_sub_natCast_add_two_mul_le_sub_pow_mul (q b : ℝ) (hb : 0 ≤ b) (hbq : b ≤ q) :
    ∀ m : ℕ, q ^ m * (q - ((m : ℝ) + 2) * b) ≤ (q - b) ^ m * (q - 2 * b) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hq : 0 ≤ q := le_trans hb hbq
    have h1 : (q - b) * (q ^ m * (q - ((m : ℝ) + 2) * b)) ≤ (q - b) * ((q - b) ^ m * (q - 2 * b)) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h2 : 0 ≤ q ^ m * (((m : ℝ) + 2) * b ^ 2) :=
      mul_nonneg (pow_nonneg hq m) (by positivity)
    calc q ^ (m + 1) * (q - (((m + 1 : ℕ) : ℝ) + 2) * b)
        = (q - b) * (q ^ m * (q - ((m : ℝ) + 2) * b)) - q ^ m * (((m : ℝ) + 2) * b ^ 2) := by
          push_cast
          ring
      _ ≤ (q - b) * ((q - b) ^ m * (q - 2 * b)) := by linarith
      _ = (q - b) ^ (m + 1) * (q - 2 * b) := by ring

theorem residueClassLowerBound : ResidueClassLowerBound := by
  intro r Q be c hr hQ
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  have key := cnt_ge (Q - 2 * be) Q (by omega) (by omega) m c
  have key' := (Nat.cast_le (α := ℝ)).mpr key
  refine le_trans ?_ key'
  have eq1 : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) =
      (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ))) := by
    have h : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) =
        (Q : ℝ) ^ m * (Q : ℝ) - (Q : ℝ) ^ m * (((m : ℝ) + 2) * (2 * (be : ℝ))) * ((Q : ℝ) / (Q : ℝ)) := by
      push_cast
      ring
    rw [h, div_self hQne, mul_one]
    ring
  rw [show m + 2 - 1 = m + 1 by omega]
  refine le_trans (le_of_eq eq1) ?_
  by_cases h4 : 2 * (2 * be) ≤ Q
  · have e1 : (Q - 2 * be) - (Q - (Q - 2 * be)) = Q - 2 * (2 * be) := by omega
    have c1 : ((Q - 2 * be : ℕ) : ℝ) = (Q : ℝ) - 2 * (be : ℝ) := by
      rw [Nat.cast_sub (show 2 * be ≤ Q by omega)] <;> push_cast <;> ring
    have c2 : ((Q - 2 * (2 * be) : ℕ) : ℝ) = (Q : ℝ) - 2 * (2 * (be : ℝ)) := by
      rw [Nat.cast_sub h4] <;> push_cast <;> ring
    rw [Nat.cast_mul, Nat.cast_pow, e1, c1, c2]
    exact pow_mul_sub_natCast_add_two_mul_le_sub_pow_mul (Q : ℝ) (2 * (be : ℝ)) (by positivity) (by exact_mod_cast hQ.le) m
  · have hneg : (Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ)) ≤ 0 := by
      have h1 : (Q : ℝ) ≤ 2 * (2 * (be : ℝ)) := by
        exact_mod_cast (show Q ≤ 2 * (2 * be) by omega)
      have h2 : (0 : ℝ) ≤ (m : ℝ) * (be : ℝ) := by positivity
      nlinarith
    have hp : (0 : ℝ) ≤ (Q : ℝ) ^ m := by positivity
    have hle : (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ))) ≤ 0 := by
      nlinarith [mul_nonneg hp (neg_nonneg.mpr hneg)]
    exact le_trans hle (Nat.cast_nonneg _)

end Residue

section Exact

end Exact

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

