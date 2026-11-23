module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.CountCross
section
open Finset

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}

private theorem isWH_coeff_one_polynomial (hT : IsTab col b) (N : ℝ) (c : C) (x : Q)
    (hx : ∃ y ∈ S, col y = c ∧ b y = b x) :
    ∑ y ∈ S.filter (fun y => col y = c), (if b y = b x then N else 0) = N := by
  obtain ⟨y, hyS, hyc, hyb⟩ := hx
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_filter]
  have e : (S.filter fun z => col z = c ∧ b z = b x) = {y} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hzc, hzb⟩
      exact hT.1 z y (hzc.trans hyc.symm) (hzb.trans hyb.symm)
    · rintro rfl
      exact ⟨hyS, hyc, hyb⟩
  rw [e, Finset.card_singleton, one_smul]

private theorem sum_filter_col_le_sum_ite_of_bound (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S))
    (R : Q → Q → ℝ) (N : ℝ) (hsymm : ∀ p q, R p q = R q p)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N)
    (c d : C) (hcd : c ≠ d) :
    ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d), R p q ≤
      ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d),
        (if b q = b p then N else 0) := by
  by_cases h : ∀ p ∈ S, col p = c → ∃ q ∈ S, col q = d ∧ b q = b p
  · refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [isWH_coeff_one_polynomial hT N d p (h p hp.1 hp.2)]
    exact hcross p hp.1 d (by rw [hp.2]; exact Ne.symm hcd)
  · push_neg at h
    obtain ⟨p0, hp0S, hp0c, hp0⟩ := h
    have h' : ∀ q ∈ S, col q = d → ∃ p ∈ S, col p = c ∧ b p = b q := by
      intro q hqS hqd
      rcases lt_trichotomy (b p0) (b q) with hl | he | hg
      · obtain ⟨p, hpc, hpb⟩ := hT.2 p0 (b q) hl
        exact ⟨p, (hS p p0 hpc).2 hp0S, hpc.trans hp0c, hpb⟩
      · exact absurd he.symm (hp0 q hqS hqd)
      · obtain ⟨q', hq'c, hq'b⟩ := hT.2 q (b p0) hg
        exact absurd hq'b (hp0 q' ((hS q' q hq'c).2 hqS) (hq'c.trans hqd))
    rw [Finset.sum_comm, Finset.sum_comm (s := S.filter (fun p => col p = c))]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Finset.mem_filter] at hq
    have e : ∑ p ∈ S.filter (fun p => col p = c), (if b q = b p then N else 0) = N :=
      (Finset.sum_congr rfl fun p _ => if_congr eq_comm rfl rfl).trans
        (isWH_coeff_one_polynomial hT N c q (h' q hq.1 hq.2))
    rw [e, Finset.sum_congr rfl fun p _ => hsymm p q]
    exact hcross q hq.1 c (by rw [hq.2]; exact hcd)

private theorem sum_sum_ite_col_ne_eq_sum_by_col (F : Q → Q → ℝ) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then F p q else 0) =
      ∑ c ∈ S.image col, ∑ d ∈ S.image col, (if d ≠ c then
        ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d), F p q else 0) := by
  symm
  calc ∑ c ∈ S.image col, ∑ d ∈ S.image col, (if d ≠ c then
        ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d), F p q else 0)
      = ∑ c ∈ S.image col, ∑ d ∈ S.image col, ∑ p ∈ S.filter (fun p => col p = c),
          ∑ q ∈ S.filter (fun q => col q = d), (if col q ≠ col p then F p q else 0) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        split_ifs with h
        · refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
          rw [Finset.mem_filter] at hp hq
          rw [if_pos (by rw [hp.2, hq.2]; exact h)]
        · symm
          refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
          rw [Finset.mem_filter] at hp hq
          rw [if_neg (by rw [hp.2, hq.2]; exact h)]
    _ = ∑ c ∈ S.image col, ∑ p ∈ S.filter (fun p => col p = c), ∑ d ∈ S.image col,
          ∑ q ∈ S.filter (fun q => col q = d), (if col q ≠ col p then F p q else 0) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then F p q else 0) := by
        rw [Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem col hp)]
        refine Finset.sum_congr rfl fun p _ => ?_
        exact Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem col hq) _

theorem count_cross (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) (R : Q → Q → ℝ) (N : ℝ)
    (hsymm : ∀ p q, R p q = R q p)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then R p q else 0) ≤
      ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then N else 0) := by
  rw [sum_sum_ite_col_ne_eq_sum_by_col (S := S) (col := col) R]
  have hR : ∀ p q, (if col q ≠ col p ∧ b q = b p then N else 0) =
      (if col q ≠ col p then (if b q = b p then N else 0) else 0) := by
    intro p q
    by_cases h1 : col q ≠ col p <;> by_cases h2 : b q = b p <;> simp [h1, h2]
  simp_rw [hR]
  have e2 := sum_sum_ite_col_ne_eq_sum_by_col (S := S) (col := col) (fun p q => if b q = b p then N else 0)
  beta_reduce at e2
  rw [e2]
  refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
  split_ifs with h
  · exact sum_filter_col_le_sum_ite_of_bound hT hS R N hsymm hcross c d (Ne.symm h)
  · exact le_rfl

theorem cas_count (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S))
    (R : Q → Q → ℝ) (N : ℝ) (hsymm : ∀ p q, R p q = R q p)
    (hsame : ∀ p q, col p = col q → p ≠ q → R p q = -N)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N) :
    ((n * S.card : ℕ) : ℝ) * N + ∑ p ∈ S, ∑ q ∈ S.erase p, R p q ≤
      (∑ i : Fin n, ((S.filter fun p => b p = i).card : ℝ) *
        (((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)) * N := by
  rw [count_rhs, Finset.sum_mul]
  have hsplit : ∀ p, ∑ q ∈ S.erase p, R p q =
      (∑ q ∈ S, (if col q = col p ∧ q ≠ p then (1:ℝ) else 0)) * (-N) +
        ∑ q ∈ S, (if col q ≠ col p then R p q else 0) := by
    intro p
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    rw [← Finset.filter_ne' S p, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q = p
    · subst hq
      simp
    · by_cases hc : col q = col p
      · simp [hq, hc, hsame p q hc.symm (Ne.symm hq)]
      · simp [hq, hc]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, count_same hT]
  have hup : ∑ p ∈ S, ∑ q ∈ S, (if col q = col p ∧ b p < b q then (1:ℝ) else 0) =
      ∑ p ∈ S, ((n:ℝ) - 1 - (b p : ℕ)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_boole]
    exact count_up hT hS p hp
  have heq : ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then N else 0) =
      ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) - 1) * N := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [count_eqb hT p hp, add_sub_cancel_left, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  have hc := count_cross hT hS R N hsymm hcross
  rw [heq] at hc
  rw [hup]
  have hcard : ((n * S.card : ℕ) : ℝ) = ∑ p ∈ S, (n : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  rw [hcard]
  have e3 : ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) + 2 * (b p : ℕ) + 1 - n) * N =
      (∑ p ∈ S, (n:ℝ)) * N + (2 * ∑ p ∈ S, ((n:ℝ) - 1 - (b p : ℕ))) * (-N) +
        ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) - 1) * N := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e3]
  linarith

end

end PositivityTheory.Rg.Cz
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.Expand
section
open Finset

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

theorem eAt_applyC (p : Q) (a c : Fin n) (f : TV n ℂ Q) (I : Q → Fin n) :
    (eAt p a c : Module.End ℂ (TV n ℂ Q)) f I = if I p = a then f (Function.update I p c) else 0 := by
  simp only [eAt, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem tE_zero_apply (S : Finset Q) (a c : Fin n) (f : TV n ℂ Q) (I : Q → Fin n) :
    (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c : Module.End ℂ (TV n ℂ Q)) f I =
      ∑ p ∈ S, (eAt p a c : Module.End ℂ (TV n ℂ Q)) f I := by
  simp [tE, lift, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply]

theorem sum4 {α β : Type} (s : Finset α) (t : Finset β) (F : Fin n → Fin n → α → β → ℂ) :
    ∑ a, ∑ c, ∑ p ∈ s, ∑ q ∈ t, F a c p q = ∑ p ∈ s, ∑ q ∈ t, ∑ a, ∑ c, F a c p q := by
  calc _ = ∑ a, ∑ p ∈ s, ∑ c, ∑ q ∈ t, F a c p q := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p ∈ s, ∑ a, ∑ c, ∑ q ∈ t, F a c p q := Finset.sum_comm
    _ = ∑ p ∈ s, ∑ a, ∑ q ∈ t, ∑ c, F a c p q := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_comm

theorem pair_apply (p q : Q) (f : TV n ℂ Q) (I : Q → Fin n) :
    ∑ a, ∑ c, (eAt p a c : Module.End ℂ (TV n ℂ Q)) ((eAt q c a : Module.End ℂ (TV n ℂ Q)) f) I =
      if p = q then (n : ℂ) * f I else f (I ∘ Equiv.swap p q) := by
  simp only [eAt_applyC]
  rw [Finset.sum_eq_single (I p)]
  · by_cases hpq : p = q
    · subst hpq
      simp [Function.update_idem, Finset.card_univ]
    · have hqp : q ≠ p := Ne.symm hpq
      simp only [if_true, Function.update_of_ne hqp, hpq, if_false]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      congr 1
      funext x
      by_cases hx : x = q
      · subst hx
        simp [Equiv.swap_apply_right]
      · by_cases hx' : x = p
        · subst hx'
          simp [Function.update_apply, hx, Equiv.swap_apply_left]
        · simp [Function.update_apply, hx, hx', Equiv.swap_apply_of_ne_of_ne hx' hx]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

private theorem tE_zero_eq_sum_eAt (S : Finset Q) (a c : Fin n) :
    (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c : Module.End ℂ (TV n ℂ Q)) =
      ∑ p ∈ S, (eAt p a c : Module.End ℂ (TV n ℂ Q)) := by
  apply LinearMap.ext
  intro f
  funext I
  rw [tE_zero_apply]
  simp [LinearMap.sum_apply, Finset.sum_apply]

theorem cas_expand' (S : Finset Q) :
    (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a : Module.End ℂ (TV n ℂ Q)) =
      ((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) +
        ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) := by
  simp_rw [tE_zero_eq_sum_eAt, Finset.sum_mul_sum]
  apply LinearMap.ext
  intro f
  funext I
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, Module.End.one_apply]
  rw [sum4]
  simp_rw [pair_apply]
  have hpm : ∀ p q : Q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ Equiv.swap p q) := by
    intro p q
    simp [pm]
  simp_rw [hpm]
  have hsplit : ∀ p ∈ S, (∑ q ∈ S, if p = q then (n : ℂ) * f I else f (I ∘ Equiv.swap p q)) =
      (n : ℂ) * f I + ∑ q ∈ S.erase p, f (I ∘ Equiv.swap p q) := by
    intro p hp
    rw [← Finset.add_sum_erase S _ hp]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_neg (Finset.ne_of_mem_erase hq).symm]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  simp [Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
  ring

end

end PositivityTheory.Rg.Cz
end

