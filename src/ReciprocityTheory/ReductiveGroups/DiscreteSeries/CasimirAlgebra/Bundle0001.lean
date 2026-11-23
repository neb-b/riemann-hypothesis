module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def hwTerm (μ : Fin n → ℝ) (a b : Fin n) : ℝ :=
  if a = b then μ a * μ a else if a < b then μ a - μ b else 0

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem pair_apply_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (hd : ∀ a, E a a v = (μ a : ℂ) • v) {a b : Fin n}
    (hab : a < b → E a b v = 0) (hba : b < a → E b a v = 0) :
    (E a b * E b a) v = ((hwTerm μ a b : ℝ) : ℂ) • v := by
  rcases lt_trichotomy a b with h | rfl | h
  ·
    have hc := congrArg (fun f : Module.End ℂ M => f v) (hE a b b a)
    simp only [if_pos rfl, if_true, ite_true, LinearMap.sub_apply, Module.End.mul_apply, hab h, map_zero,
      sub_zero] at hc
    rw [Module.End.mul_apply, hc, hd, hd]
    simp [hwTerm, h, h.ne, sub_smul]
  · rw [Module.End.mul_apply, hd, map_smul, hd, smul_smul]
    simp [hwTerm]
  · rw [Module.End.mul_apply, hba h, map_zero]
    simp [hwTerm, h.ne', not_lt.2 h.le]

theorem sum_pair_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (S : Fin n → Fin n → Prop) [DecidableRel S] (hS : ∀ a b, S a b → S b a)
    (hd : ∀ a, E a a v = (μ a : ℂ) • v) (hv : ∀ a b, a < b → S a b → E a b v = 0) :
    (∑ a, ∑ b ∈ univ.filter (fun b => S a b), E a b * E b a) v =
      ((∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b : ℝ) : ℂ) • v := by
  simp only [LinearMap.sum_apply, Complex.ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : S a b := (Finset.mem_filter.1 hb).2
  exact pair_apply_hw hE hd (fun h => hv a b h hab) (fun h => hv b a h (hS a b hab))

end Alg

theorem sum_hwTerm (S : Fin n → Fin n → Prop) [DecidableRel S] (hrefl : ∀ a, S a a)
    (hS : ∀ a b, S a b → S b a) (μ r : Fin n → ℝ)
    (hr : ∀ a, 2 * r a = ((univ.filter fun b => a < b ∧ S a b).card : ℝ) -
      ((univ.filter fun b => b < a ∧ S a b).card : ℝ)) :
    ∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b = nsq (μ + r) - nsq r := by
  classical
  have hpt : ∀ a b, (if S a b then hwTerm μ a b else 0) =
      (if a = b then μ a * μ a else 0) +
        ((if a < b ∧ S a b then μ a else 0) - (if a < b ∧ S a b then μ b else 0)) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · by_cases hs : S a b <;> simp [hwTerm, h, h.ne, hs]
    · simp [hwTerm, hrefl]
    · by_cases hs : S a b <;> simp [hwTerm, h.ne', not_lt.2 h.le, hs]

  have hL : ∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b =
      ∑ a, μ a * μ a + ∑ a, ∑ b, ((if a < b ∧ S a b then μ a else 0) -
        (if a < b ∧ S a b then μ b else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    simp only [hpt a, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  have hR : nsq (μ + r) - nsq r = ∑ a, μ a * μ a + ∑ a, ∑ b, ((if a < b ∧ S a b then μ a else 0) -
        (if b < a ∧ S a b then μ a else 0)) := by
    rw [← Finset.sum_add_distrib]
    unfold nsq dot
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : ∑ b, ((if a < b ∧ S a b then μ a else 0) - (if b < a ∧ S a b then μ a else 0)) =
        μ a * (2 * r a) := by
      rw [hr a, Finset.natCast_card_filter, Finset.natCast_card_filter, mul_sub, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [mul_ite, mul_one, mul_zero]
    rw [h2, Pi.add_apply]
    ring
  rw [hL, hR]
  congr 1
  simp only [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b < a ∧ S a b
  · rw [if_pos h, if_pos ⟨h.1, hS a b h.2⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1, hS b a h'.2⟩]

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem casimir_hwVec {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (hv : IsHWVec E μ v) :
    casimir E v = ((nsq (μ + rho n) - nsq (rho n) : ℝ) : ℂ) • v := by
  classical
  have hc : casimir E = ∑ a, ∑ b ∈ univ.filter (fun _ => True), E a b * E b a := by
    simp [casimir]
  have hsum := sum_pair_hw hE (fun _ _ => True) (fun _ _ h => h) hv.1 (fun a b h _ => hv.2 a b h)
  rw [hc, hsum, sum_hwTerm (fun _ _ => True) (fun _ => trivial) (fun _ _ h => h) μ (rho n)]
  intro a
  have ha : 1 + (a : ℕ) ≤ n := by have := a.isLt; omega
  simp only [and_true, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi,
    Fin.card_Iio, rho]
  rw [Nat.sub_sub, Nat.cast_sub ha]
  push_cast
  ring

theorem casimirK_khwVec (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    {μ : Fin n → ℝ} {v : M} (hv : IsKHWVec ε E μ v) :
    casimirK ε E v = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • v := by
  classical
  have hsum := sum_pair_hw hE (fun a b => ε b = ε a) (fun _ _ h => h.symm) hv.1
    (fun a b h hs => hv.2 a b h hs.symm)
  rw [casimirK, hsum, sum_hwTerm (fun a b => ε b = ε a) (fun _ => rfl) (fun _ _ h => h.symm) μ
    (rhoC ε)]
  intro a
  simp only [rhoC]
  ring

end Alg

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem mul_mul_sub_mul_mul_eq_add {R : Type*} [Ring R] (X Y Z : R) :
    X * Y * Z - Z * (X * Y) = (X * Z - Z * X) * Y + X * (Y * Z - Z * Y) := by
  noncomm_ring

theorem ite_mul_sub_mul_ite {R : Type*} [Ring R] (p : Prop) [Decidable p] (X Z : R) :
    (if p then X else 0) * Z - Z * (if p then X else 0) = if p then X * Z - Z * X else 0 := by
  split_ifs <;> simp

theorem ite_sub_add_sub_eq {R : Type*} [AddCommGroup R] (p : Prop) [Decidable p] (A B C D : R) :
    (if p then (A - B) + (C - D) else 0) =
      ((if p then A else 0) - (if p then B else 0)) + ((if p then C else 0) - (if p then D else 0)) := by
  split_ifs <;> simp

theorem casimir_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (c d : Fin n) :
    casimir E * E c d = E c d * casimir E := by
  unfold IsGlRep at hE
  rw [← sub_eq_zero]
  unfold casimir
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_mul_sub_mul_mul_eq_add, hE]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  abel

theorem casimirK_comm (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (c d : Fin n) (hcd : ε c = ε d) :
    casimirK ε E * E c d = E c d * casimirK ε E := by
  unfold IsGlRep at hE
  rw [← sub_eq_zero]
  unfold casimirK
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ite_mul_sub_mul_ite, mul_mul_sub_mul_mul_eq_add, hE]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [ite_sub_add_sub_eq, ← ite_and, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [and_comm (b := _ = c), and_comm (b := d = _), Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [hcd]
  abel

end Alg

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.RhoEqRhoCAddRhoN
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem casimir_split {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (P : Fin n → Fin n → Prop) [DecidableRel P] (hirr : ∀ a, ¬ P a a)
    (hP : ∀ a b, a ≠ b → (P a b ↔ ¬ P b a)) :
    casimir E = ∑ a, E a a * E a a +
      ∑ a, ∑ b ∈ univ.filter (fun b => P a b), (E a a - E b b + 2 • (E b a * E a b)) := by
  classical

  have h1 : casimir E = ∑ a, ∑ b, ((if a = b then E a a * E a a else 0) +
      (if P a b then E a b * E b a else 0) + (if P b a then E a b * E b a else 0)) := by
    unfold casimir
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b
    · subst hab
      simp [hirr]
    · by_cases h : P a b
      · have h' : ¬ P b a := (hP a b hab).1 h
        simp [hab, h, h']
      · have h' : P b a := by
          by_contra h''
          exact h ((hP a b hab).2 h'')
        simp [hab, h, h']

  have comm : ∀ a b, E a b * E b a + E b a * E a b = E a a - E b b + 2 • (E b a * E a b) := by
    intro a b
    have h := hE a b b a
    rw [if_pos rfl, if_pos rfl, sub_eq_iff_eq_add] at h
    rw [h]
    abel
  have h3 : ∑ a, ∑ b, (if P b a then E a b * E b a else 0) =
      ∑ a, ∑ b, (if P a b then E b a * E a b else 0) := Finset.sum_comm
  have h4 : ∑ a, ∑ b, (if a = b then E a a * E a a else 0) = ∑ a, E a a * E a a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  rw [h1]
  simp only [Finset.sum_add_distrib]
  rw [h3, h4, add_assoc]
  congr 1
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact comm a b
  · simp

end Alg

theorem rho_eq_rhoC_add_rhoN (ε : Fin n → Bool) : rho n = rhoC ε + rhoN ε := by
  classical
  funext a
  simp only [rho, rhoC, rhoN, Pi.add_apply]

  have hgt : (univ.filter fun b : Fin n => a < b ∧ ε b = ε a).card +
      (univ.filter fun b : Fin n => a < b ∧ ε b ≠ ε a).card = n - 1 - (a : ℕ) := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.Ioi a)
      (fun b => ε b = ε a)
    rw [Fin.card_Ioi] at h
    rw [← h]
    congr 2 <;> ext b <;> simp

  have hlt : (univ.filter fun b : Fin n => b < a ∧ ε b = ε a).card +
      (univ.filter fun b : Fin n => b < a ∧ ε b ≠ ε a).card = (a : ℕ) := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.Iio a)
      (fun b => ε b = ε a)
    rw [Fin.card_Iio] at h
    rw [← h]
    congr 2 <;> ext b <;> simp
  have ha := a.isLt
  have hc : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have c1 := congrArg (Nat.cast : ℕ → ℝ) hgt
  have c2 := congrArg (Nat.cast : ℕ → ℝ) hlt
  push_cast at c1 c2
  rw [hc] at c1
  linarith

end ReciprocityTheory.ChartRestriction.DS
end
end

