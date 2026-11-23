module

public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnStepsTail
section
namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

section Pos

variable {α : Type*} [BEq α] [LawfulBEq α]

theorem cn_notMem {l1 l2 : List α} (h : (l1 ++ l2).Nodup) {x : α} (hx : x ∈ l2) : x ∉ l1 := by
  intro hx1
  first
  | exact List.disjoint_of_nodup_append h hx1 hx
  | exact (List.nodup_append.1 h).2.2 hx1 hx
  | exact (List.nodup_append.1 h).2.2 x hx1 x hx rfl
  | simp_all [List.nodup_append]

private theorem idxOf_cons_self_eq_zero (a : α) (l : List α) : (a :: l).idxOf a = 0 := by
  first
  | simp [List.idxOf_cons]
  | exact List.idxOf_cons_self l
  | simp [List.idxOf, List.findIdx_cons]

private theorem idxOf_cons_of_ne (a u : α) (h : a ≠ u) (l : List α) : (a :: l).idxOf u = l.idxOf u + 1 := by
  first
  | simp [List.idxOf_cons, h]
  | exact List.idxOf_cons_ne l h
  | simp [List.idxOf, List.findIdx_cons, h]

private theorem idxOf_append_of_not_mem_left (l1 : List α) (u : α) (hu : u ∉ l1) (l : List α) :
    (l1 ++ l).idxOf u = l1.length + l.idxOf u := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
    have hau : a ≠ u := by
      rintro rfl
      simp at hu
    have ht : u ∉ t := fun h' => hu (List.mem_cons_of_mem _ h')
    rw [List.cons_append, idxOf_cons_of_ne a u hau, ih ht, List.length_cons]
    omega

private theorem idxOf_append_of_mem_left_and_lt_length (l1 : List α) (u : α) (hu : u ∈ l1) (l : List α) :
    (l1 ++ l).idxOf u = l1.idxOf u ∧ l1.idxOf u < l1.length := by
  induction l1 with
  | nil => simp at hu
  | cons a t ih =>
    by_cases hau : a = u
    · rw [hau, List.cons_append, idxOf_cons_self_eq_zero, idxOf_cons_self_eq_zero]
      simp
    · have ht : u ∈ t := by simpa [Ne.symm hau] using hu
      obtain ⟨h1, h2⟩ := ih ht
      rw [List.cons_append, idxOf_cons_of_ne a u hau, idxOf_cons_of_ne a u hau, h1, List.length_cons]
      exact ⟨rfl, by omega⟩

theorem cn_pos_swap (l1 l2 : List α) (x y : α) (hxy : x ≠ y) (hx : x ∉ l1) (hy : y ∉ l1) (u : α) :
    (u = x ∧ (l1 ++ x :: y :: l2).idxOf u = l1.length ∧ (l1 ++ y :: x :: l2).idxOf u = l1.length + 1) ∨
    (u = y ∧ (l1 ++ x :: y :: l2).idxOf u = l1.length + 1 ∧ (l1 ++ y :: x :: l2).idxOf u = l1.length) ∨
    (u ≠ x ∧ u ≠ y ∧ (l1 ++ y :: x :: l2).idxOf u = (l1 ++ x :: y :: l2).idxOf u ∧
      ((l1 ++ x :: y :: l2).idxOf u < l1.length ∨ l1.length + 2 ≤ (l1 ++ x :: y :: l2).idxOf u)) := by
  by_cases hux : u = x
  · refine Or.inl ⟨hux, ?_, ?_⟩ <;> rw [hux] <;>
      simp only [idxOf_append_of_not_mem_left l1 x hx, idxOf_cons_self_eq_zero, idxOf_cons_of_ne y x (Ne.symm hxy)] <;> omega
  · by_cases huy : u = y
    · refine Or.inr (Or.inl ⟨huy, ?_, ?_⟩) <;> rw [huy] <;>
        simp only [idxOf_append_of_not_mem_left l1 y hy, idxOf_cons_self_eq_zero, idxOf_cons_of_ne x y hxy] <;> omega
    · refine Or.inr (Or.inr ⟨hux, huy, ?_⟩)
      by_cases hu1 : u ∈ l1
      · obtain ⟨e1, e2⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (x :: y :: l2)
        obtain ⟨e3, _⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (y :: x :: l2)
        exact ⟨by rw [e1, e3], Or.inl (by rw [e1]; exact e2)⟩
      · refine ⟨?_, Or.inr ?_⟩ <;>
          simp only [idxOf_append_of_not_mem_left l1 u hu1, idxOf_cons_of_ne x u (Ne.symm hux), idxOf_cons_of_ne y u (Ne.symm huy)] <;> omega

theorem cn_pos_braid (l1 l2 : List α) (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ l1) (hy : y ∉ l1) (hz : z ∉ l1) (u : α) :
    (u = x ∧ (l1 ++ x :: y :: z :: l2).idxOf u = l1.length ∧ (l1 ++ z :: y :: x :: l2).idxOf u = l1.length + 2) ∨
    (u = y ∧ (l1 ++ x :: y :: z :: l2).idxOf u = l1.length + 1 ∧
      (l1 ++ z :: y :: x :: l2).idxOf u = l1.length + 1) ∨
    (u = z ∧ (l1 ++ x :: y :: z :: l2).idxOf u = l1.length + 2 ∧ (l1 ++ z :: y :: x :: l2).idxOf u = l1.length) ∨
    (u ≠ x ∧ u ≠ y ∧ u ≠ z ∧ (l1 ++ z :: y :: x :: l2).idxOf u = (l1 ++ x :: y :: z :: l2).idxOf u ∧
      ((l1 ++ x :: y :: z :: l2).idxOf u < l1.length ∨ l1.length + 3 ≤ (l1 ++ x :: y :: z :: l2).idxOf u)) := by
  by_cases hux : u = x
  · refine Or.inl ⟨hux, ?_, ?_⟩ <;> rw [hux] <;>
      simp only [idxOf_append_of_not_mem_left l1 x hx, idxOf_cons_self_eq_zero, idxOf_cons_of_ne y x (Ne.symm hxy), idxOf_cons_of_ne z x (Ne.symm hxz)] <;> omega
  · by_cases huy : u = y
    · refine Or.inr (Or.inl ⟨huy, ?_, ?_⟩) <;> rw [huy] <;>
        simp only [idxOf_append_of_not_mem_left l1 y hy, idxOf_cons_self_eq_zero, idxOf_cons_of_ne x y hxy, idxOf_cons_of_ne z y (Ne.symm hyz)] <;> omega
    · by_cases huz : u = z
      · refine Or.inr (Or.inr (Or.inl ⟨huz, ?_, ?_⟩)) <;> rw [huz] <;>
          simp only [idxOf_append_of_not_mem_left l1 z hz, idxOf_cons_self_eq_zero, idxOf_cons_of_ne x z hxz, idxOf_cons_of_ne y z hyz] <;> omega
      · refine Or.inr (Or.inr (Or.inr ⟨hux, huy, huz, ?_⟩))
        by_cases hu1 : u ∈ l1
        · obtain ⟨e1, e2⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (x :: y :: z :: l2)
          obtain ⟨e3, _⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (z :: y :: x :: l2)
          exact ⟨by rw [e1, e3], Or.inl (by rw [e1]; exact e2)⟩
        · refine ⟨?_, Or.inr ?_⟩ <;>
            simp only [idxOf_append_of_not_mem_left l1 u hu1, idxOf_cons_of_ne x u (Ne.symm hux), idxOf_cons_of_ne y u (Ne.symm huy),
              idxOf_cons_of_ne z u (Ne.symm huz)] <;> omega

theorem cn_idx_rev {l : List α} (hnd : l.Nodup) {x : α} (hx : x ∈ l) :
    l.reverse.idxOf x + l.idxOf x + 1 = l.length := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hat, hnd'⟩ := hnd
    rw [List.reverse_cons, List.length_cons]
    by_cases hax : a = x
    · have hat' : x ∉ t := hax ▸ hat
      have hr : x ∉ t.reverse := by simpa using hat'
      rw [hax]
      simp only [idxOf_append_of_not_mem_left t.reverse x hr, idxOf_cons_self_eq_zero, List.length_reverse]
      all_goals omega
    · have hxt : x ∈ t := by simpa [Ne.symm hax] using hx
      have hxr : x ∈ t.reverse := by simpa using hxt
      obtain ⟨e1, _⟩ := idxOf_append_of_mem_left_and_lt_length t.reverse x hxr [a]
      rw [e1, idxOf_cons_of_ne a x hax]
      have := ih hnd' hxt
      omega

theorem cn_decomp (F : α → Prop) (l : List α) :
    (∃ lF lG, l = lF ++ lG ∧ (∀ r ∈ lF, F r) ∧ (∀ r ∈ lG, ¬ F r)) ∨
    (∃ l1 g f lF lG, l = l1 ++ g :: f :: (lF ++ lG) ∧ ¬ F g ∧ F f ∧ (∀ r ∈ lF, F r) ∧ (∀ r ∈ lG, ¬ F r)) := by
  induction l with
  | nil => exact Or.inl ⟨[], [], by simp, by simp, by simp⟩
  | cons a t ih =>
    rcases ih with ⟨lF, lG, rfl, hF, hG⟩ | ⟨l1, g, f, lF, lG, rfl, hg, hf, hF, hG⟩
    · by_cases ha : F a
      · refine Or.inl ⟨a :: lF, lG, by simp, ?_, hG⟩
        intro r hr
        rcases List.mem_cons.1 hr with h | h
        · exact h ▸ ha
        · exact hF r h
      · cases lF with
        | nil =>
          refine Or.inl ⟨[], a :: lG, by simp, by simp, ?_⟩
          intro r hr
          rcases List.mem_cons.1 hr with h | h
          · exact h ▸ ha
          · exact hG r h
        | cons f lF' =>
          exact Or.inr ⟨[], a, f, lF', lG, by simp, ha, hF f (List.mem_cons_self ..),
            fun r hr => hF r (List.mem_cons_of_mem _ hr), hG⟩
    · exact Or.inr ⟨a :: l1, g, f, lF, lG, by simp, hg, hf, hF, hG⟩

end Pos

variable {n : ℕ}

abbrev Steps (n : ℕ) := Relation.ReflTransGen (Step n)

theorem cn_step_tail {l l' : List (Fin n × Fin n)} (h : Step n l l') (R : List (Fin n × Fin n)) :
    Step n (l ++ R) (l' ++ R) := by
  cases h <;>
    (simp only [List.append_assoc, List.cons_append]
     constructor <;> assumption)

theorem cn_steps_tail {l l' : List (Fin n × Fin n)} (h : Steps n l l') (R : List (Fin n × Fin n)) :
    Steps n (l ++ R) (l' ++ R) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (cn_step_tail hs R)

theorem cn_step_rev {l l' : List (Fin n × Fin n)} (h : Step n l l') : Step n l.reverse l'.reverse := by
  cases h with
  | swap l1 l2 a b c d h1 h2 h3 h4 =>
    simpa using Step.swap l2.reverse l1.reverse c d a b h1.symm h3.symm h2.symm h4.symm
  | braid l1 l2 a b c h1 h2 => simpa using Step.braid' l2.reverse l1.reverse a b c h1 h2
  | braid' l1 l2 a b c h1 h2 => simpa using Step.braid l2.reverse l1.reverse a b c h1 h2

theorem cn_steps_rev {l l' : List (Fin n × Fin n)} (h : Steps n l l') : Steps n l.reverse l'.reverse := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (cn_step_rev hs)

end Formalism.MainNotions.G.ExtremalProjector
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CommPow
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem comm_pow {R : Type*} [Ring R] {x y z : R} (h : x * y = y * x + z) (hz : z * y = y * z) (k : ℕ) :
    x * y ^ (k + 1) = y ^ (k + 1) * x + (k + 1) • (y ^ k * z) := by
  induction k with
  | zero => simp [h]
  | succ k ih =>
    calc x * y ^ (k + 1 + 1) = (x * y ^ (k + 1)) * y := by rw [pow_succ y (k + 1), mul_assoc]
      _ = (y ^ (k + 1) * x + (k + 1) • (y ^ k * z)) * y := by rw [ih]
      _ = y ^ (k + 1) * (x * y) + (k + 1) • (y ^ k * (z * y)) := by
          simp only [add_mul, smul_mul_assoc, mul_assoc]
      _ = y ^ (k + 1) * (y * x + z) + (k + 1) • (y ^ k * (y * z)) := by rw [h, hz]
      _ = y ^ (k + 1 + 1) * x + (k + 1 + 1) • (y ^ (k + 1) * z) := by
          rw [mul_add, ← mul_assoc, ← pow_succ, ← mul_assoc (y ^ k) y z, ← pow_succ,
            succ_nsmul (y ^ (k + 1) * z) (k + 1)]
          first
          | abel
          | rw [add_assoc, add_comm (y ^ (k + 1) * z)]

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cA (K : Type*) [Field K] (s k : ℕ) : K :=
  (-1 : K) ^ k / ((Nat.choose (s + k) k : ℕ) : K) * (((k.factorial : K)⁻¹) * ((k.factorial : K)⁻¹))

theorem pf_eq (E : GLOps n K V) (a b : Fin n) (s T : ℕ) :
    pf E a b s T = ∑ k ∈ Finset.range (T + 1), cA K s k • ((E b a) ^ k * (E a b) ^ k) := by
  first
  | simp only [pf, cA]
  | unfold pf cA
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold divPowE
  first
  | rw [smul_mul_smul_comm, smul_smul]
  | simp only [smul_mul_smul_comm, smul_smul]
  | simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  | simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]

theorem cA_succ [CharZero K] (s k : ℕ) :
    ((k + 1 : ℕ) : K) * cA K s (k + 1) = - ((s : K) + 1)⁻¹ * cA K (s + 1) k := by
  have hk : ((k : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hs : ((s : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero s
  have hf : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h2 : ((Nat.choose (s + 1 + k) k : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'

  have hc : ((Nat.choose (s + (k + 1)) (k + 1) : ℕ) : K)
      = ((Nat.choose (s + 1 + k) k : ℕ) : K) * ((s : K) + 1) / ((k : K) + 1) := by
    rw [eq_div_iff hk]
    have h := Nat.choose_succ_right_eq (s + k + 1) k
    have e3 : s + k + 1 - k = s + 1 := by omega
    rw [e3] at h
    have e1 : s + (k + 1) = s + k + 1 := by omega
    have e2 : s + 1 + k = s + k + 1 := by omega
    rw [e1, e2]
    exact_mod_cast h
  unfold cA
  rw [hc, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem cross_ab [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (s T : ℕ) (hnil : (E a b) ^ T = 0) :
    E b c * pf E a b s T = pf E a b s T * E b c + ((s : K) + 1)⁻¹ • (E b a * pf E a b (s + 1) T * E a c) := by
  have hrel := hE.1
  have hYF : E b c * E b a = E b a * E b c := by
    have h := hrel b c b a
    rw [if_neg (Ne.symm hbc), if_neg hab, sub_zero, sub_eq_zero] at h
    exact h
  have hYX : E b c * E a b = E a b * E b c + -(E a c) := by
    have h := hrel b c a b
    rw [if_neg (Ne.symm hac), if_pos rfl, zero_sub] at h
    rw [← h]; abel
  have hZX : -(E a c) * E a b = E a b * -(E a c) := by
    have h := hrel a c a b
    rw [if_neg (Ne.symm hac), if_neg (Ne.symm hab), sub_zero, sub_eq_zero] at h
    rw [neg_mul, mul_neg, h]
  have hFc : ∀ k : ℕ, E b c * E b a ^ k = E b a ^ k * E b c := fun k =>
    (Commute.pow_right (hYF : Commute (E b c) (E b a)) k).eq
  have hpow : ∀ j : ℕ, E b c * E a b ^ (j + 1) =
      E a b ^ (j + 1) * E b c - ((j + 1 : ℕ) : K) • (E a b ^ j * E a c) := by
    intro j
    rw [comm_pow hYX hZX j, Nat.cast_smul_eq_nsmul, mul_neg, smul_neg, sub_eq_add_neg]
  have hT : ∀ j : ℕ, E b c * (E b a ^ (j + 1) * E a b ^ (j + 1)) =
      (E b a ^ (j + 1) * E a b ^ (j + 1)) * E b c -
        ((j + 1 : ℕ) : K) • (E b a ^ (j + 1) * E a b ^ j * E a c) := by
    intro j
    rw [← mul_assoc, hFc, mul_assoc (E b a ^ (j + 1)) (E b c), hpow j, mul_sub, mul_smul_comm]
    simp only [mul_assoc]
  rw [pf_eq, pf_eq]
  have hL : E b c * (∑ k ∈ Finset.range (T + 1), cA K s k • (E b a ^ k * E a b ^ k)) -
      (∑ k ∈ Finset.range (T + 1), cA K s k • (E b a ^ k * E a b ^ k)) * E b c =
        -∑ j ∈ Finset.range T, (cA K s (j + 1) * ((j + 1 : ℕ) : K)) •
          (E b a ^ (j + 1) * E a b ^ j * E a c) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_range_succ',
      ← Finset.sum_neg_distrib]
    have h0 : E b c * (cA K s 0 • (E b a ^ 0 * E a b ^ 0)) - cA K s 0 • (E b a ^ 0 * E a b ^ 0) * E b c = 0 := by
      simp only [pow_zero, mul_one, mul_smul_comm, smul_mul_assoc, one_mul, sub_self]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, hT j, smul_sub, sub_sub_cancel_left, smul_smul]
  have hR : ((s : K) + 1)⁻¹ • (E b a * (∑ k ∈ Finset.range (T + 1), cA K (s + 1) k • (E b a ^ k * E a b ^ k)) *
      E a c) = ∑ j ∈ Finset.range T, (((s : K) + 1)⁻¹ * cA K (s + 1) j) •
        (E b a ^ (j + 1) * E a b ^ j * E a c) := by
    rw [Finset.sum_range_succ, hnil, mul_zero, smul_zero, add_zero, Finset.mul_sum, Finset.sum_mul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, ← mul_assoc, ← pow_succ']
  rw [← sub_eq_iff_eq_add', hL, hR, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul]
  congr 1
  rw [mul_comm (cA K s (j + 1)), cA_succ, neg_mul, neg_neg]

theorem cross_ac [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (u T : ℕ) (hnil : (E a c) ^ T = 0) :
    E b c * pf E a c u T = pf E a c u T * E b c - ((u : K) + 1)⁻¹ • (E b a * pf E a c (u + 1) T * E a c) := by
  have hrel := hE.1
  have hYX : E b c * E a c = E a c * E b c := by
    have h := hrel b c a c
    rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), sub_zero, sub_eq_zero] at h
    exact h
  have hYF : E b c * E c a = E c a * E b c + E b a := by
    have h := hrel b c c a
    rw [if_pos rfl, if_neg hab, sub_zero] at h
    rw [← h]; abel
  have hEF : E b a * E c a = E c a * E b a := by
    have h := hrel b a c a
    rw [if_neg hac, if_neg hab, sub_zero, sub_eq_zero] at h
    exact h
  have hXc : ∀ k : ℕ, E b c * E a c ^ k = E a c ^ k * E b c := fun k =>
    (Commute.pow_right (hYX : Commute (E b c) (E a c)) k).eq
  have hEFk : ∀ k : ℕ, E b a * E c a ^ k = E c a ^ k * E b a := fun k =>
    (Commute.pow_right (hEF : Commute (E b a) (E c a)) k).eq
  have hEF' : ∀ (k : ℕ) (M : Module.End K V), E b a * (E c a ^ k * M) = E c a ^ k * (E b a * M) := by
    intro k M
    rw [← mul_assoc, hEFk k, mul_assoc]
  have hpow : ∀ j : ℕ, E b c * E c a ^ (j + 1) =
      E c a ^ (j + 1) * E b c + ((j + 1 : ℕ) : K) • (E c a ^ j * E b a) := by
    intro j
    rw [comm_pow hYF hEF j, Nat.cast_smul_eq_nsmul]
  have hT : ∀ j : ℕ, E b c * (E c a ^ (j + 1) * E a c ^ (j + 1)) =
      (E c a ^ (j + 1) * E a c ^ (j + 1)) * E b c +
        ((j + 1 : ℕ) : K) • (E c a ^ j * E b a * E a c ^ (j + 1)) := by
    intro j
    rw [← mul_assoc, hpow j, add_mul, smul_mul_assoc]
    simp only [mul_assoc, hXc]
  rw [pf_eq, pf_eq]
  have hL : E b c * (∑ k ∈ Finset.range (T + 1), cA K u k • (E c a ^ k * E a c ^ k)) -
      (∑ k ∈ Finset.range (T + 1), cA K u k • (E c a ^ k * E a c ^ k)) * E b c =
        ∑ j ∈ Finset.range T, (cA K u (j + 1) * ((j + 1 : ℕ) : K)) •
          (E c a ^ j * E b a * E a c ^ (j + 1)) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
    have h0 : E b c * (cA K u 0 • (E c a ^ 0 * E a c ^ 0)) - cA K u 0 • (E c a ^ 0 * E a c ^ 0) * E b c = 0 := by
      simp only [pow_zero, mul_one, mul_smul_comm, smul_mul_assoc, one_mul, sub_self]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, hT j, smul_add, add_sub_cancel_left, smul_smul]
  have hR : ((u : K) + 1)⁻¹ • (E b a * (∑ k ∈ Finset.range (T + 1), cA K (u + 1) k • (E c a ^ k * E a c ^ k)) *
      E a c) = ∑ j ∈ Finset.range T, (((u : K) + 1)⁻¹ * cA K (u + 1) j) •
        (E c a ^ j * E b a * E a c ^ (j + 1)) := by
    rw [Finset.sum_range_succ, hnil, mul_zero, smul_zero, add_zero, Finset.mul_sum, Finset.sum_mul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, ← mul_assoc, hEFk j, mul_assoc (E c a ^ j * E b a),
      ← pow_succ]
  rw [sub_eq_add_neg, ← sub_eq_iff_eq_add', hL, hR, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul]
  congr 1
  rw [mul_comm (cA K u (j + 1)), cA_succ, neg_mul]

end

end Formalism.MainNotions.G.ExtremalProjector
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.PfTrunc
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem restNil : RestNil := by
  intro K V _ _ _ _ _ n E hE a b hab k hk
  have hs := gl_rep_shifts_weights hE
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  have h1 : (E a b) ^ (2 * m + 1) = 0 := by
    have hle : (⊤ : Submodule K V) ≤ LinearMap.ker ((E a b) ^ (2 * m + 1)) := by
      rw [← hE.2.2]
      refine iSup_le fun ν x hx => ?_
      rw [LinearMap.mem_ker]
      by_contra h0
      have hx0 : weightSp E ν ≠ ⊥ := by
        intro hb
        rw [hb, Submodule.mem_bot] at hx
        exact h0 (by rw [hx, map_zero])
      have hw := operator_pow_shifts_weight hs a b ν (2 * m + 1) x hx
      have hw0 : weightSp E (ν + ((2 * m + 1 : ℕ) : ℤ) • rootW a b) ≠ ⊥ := by
        intro hb
        rw [hb, Submodule.mem_bot] at hw
        exact h0 hw
      have b1 := hm _ hx0 a
      have b2 := hm _ hw0 a
      rw [Pi.add_apply, root_multiple_apply_first a b hab] at b2
      rw [abs_le] at b1 b2
      push_cast at b2
      omega
    exact LinearMap.ker_eq_top.1 (top_le_iff.1 hle)
  have h2 : LinearMap.ker ((E a b) ^ k) = ⊤ := by
    rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hk,
      ← Module.End.ker_pow_eq_ker_pow_finrank_of_le (le_max_left (Module.finrank K V) (2 * m + 1)),
      pow_eq_zero_of_le (le_max_right _ _) h1]
    exact LinearMap.ker_zero
  exact LinearMap.ker_eq_top.1 h2

theorem pf_trunc {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ}
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (hab : a ≠ b) (c T T' : ℕ)
    (hT : Module.finrank K V ≤ T) (hT' : Module.finrank K V ≤ T') : pf E a b c T = pf E a b c T' := by
  have hz : ∀ k, Module.finrank K V ≤ k → divPowE E a b k = 0 := by
    intro k hk
    unfold divPowE
    rw [restNil K V n E hE a b hab k hk, smul_zero]
  have hsum : ∀ S : ℕ, Module.finrank K V ≤ S → pf E a b c S = pf E a b c (Module.finrank K V) := by
    intro S hS
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hS
    unfold pf
    rw [show Module.finrank K V + m + 1 = (Module.finrank K V + 1) + m by ring, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range m, ((-1 : K) ^ (Module.finrank K V + 1 + x) /
        ((Nat.choose (c + (Module.finrank K V + 1 + x)) (Module.finrank K V + 1 + x) : ℕ) : K)) •
        (divPowE E b a (Module.finrank K V + 1 + x) * divPowE E a b (Module.finrank K V + 1 + x)) = 0 :=
      Finset.sum_eq_zero (fun x _ => by rw [hz _ (by omega), mul_zero, smul_zero])
    rw [h0, add_zero]
  rw [hsum T hT, hsum T' hT']

end Formalism.MainNotions.G.ExtremalProjector
end
end

