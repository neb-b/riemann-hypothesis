module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.KTypeData

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.CountSame
section
open Finset

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}

theorem count_rhs :
    (∑ i : Fin n, ((S.filter fun p => b p = i).card : ℝ) *
        (((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)) =
      ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) + 2 * (b p : ℕ) + 1 - n) := by
  rw [← Finset.sum_fiberwise S b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => ((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)]
  · rw [Finset.sum_const, nsmul_eq_mul]
  · intro p hp
    rw [(Finset.mem_filter.mp hp).2]

theorem count_up (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) (p : Q) (hp : p ∈ S) :
    ((S.filter fun q => col q = col p ∧ b p < b q).card : ℝ) = n - 1 - (b p : ℕ) := by
  have hc : (S.filter fun q => col q = col p ∧ b p < b q).card = (Finset.Ioi (b p)).card := by
    apply Finset.card_bij (fun q _ => b q)
    · intro q hq
      simp only [Finset.mem_filter] at hq
      exact Finset.mem_Ioi.mpr hq.2.2
    · intro q₁ h₁ q₂ h₂ h
      simp only [Finset.mem_filter] at h₁ h₂
      exact hT.1 q₁ q₂ (h₁.2.1.trans h₂.2.1.symm) h
    · intro i hi
      rw [Finset.mem_Ioi] at hi
      obtain ⟨q, hq1, hq2⟩ := hT.2 p i hi
      refine ⟨q, ?_, hq2⟩
      simp only [Finset.mem_filter]
      refine ⟨(hS q p hq1).2 hp, hq1, ?_⟩
      rw [hq2]
      exact hi
  rw [hc, Fin.card_Ioi]
  have h : (b p : ℕ) + 1 ≤ n := (b p).isLt
  rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + (b p : ℕ) ≤ n)]
  push_cast
  ring

theorem count_eqb (hT : IsTab col b) (p : Q) (hp : p ∈ S) :
    ((S.filter fun q => b q = b p).card : ℝ) =
      1 + ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole]
  have h1 : (S.filter fun q => b q = b p).filter (fun q => col q = col p) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact hT.1 q p h3 h2
    · rintro rfl
      exact ⟨⟨hp, rfl⟩, rfl⟩
  have h2 : (S.filter fun q => b q = b p).filter (fun q => ¬ col q = col p) =
      S.filter (fun q => col q ≠ col p ∧ b q = b p) := by
    ext q
    simp only [Finset.mem_filter]
    tauto
  have h3 := Finset.card_filter_add_card_filter_not (s := S.filter fun q => b q = b p)
    (fun q => col q = col p)
  beta_reduce at h3
  rw [h1, h2, Finset.card_singleton] at h3
  rw [← h3]
  push_cast
  ring

theorem count_same (hT : IsTab col b) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q = col p ∧ q ≠ p then (1 : ℝ) else 0) =
      2 * ∑ p ∈ S, ∑ q ∈ S, (if col q = col p ∧ b p < b q then (1 : ℝ) else 0) := by
  have hpt : ∀ p q : Q, (if col q = col p ∧ q ≠ p then (1 : ℝ) else 0) =
      (if col q = col p ∧ b p < b q then 1 else 0) + (if col p = col q ∧ b q < b p then 1 else 0) := by
    intro p q
    by_cases hc : col q = col p
    · by_cases hq : q = p
      · subst hq; simp
      · have hb : b q ≠ b p := fun hb => hq (hT.1 q p hc hb)
        rcases lt_or_gt_of_ne hb with h | h
        · simp [hc, hq, h, not_lt.mpr h.le]
        · simp [hc, hq, h, not_lt.mpr h.le]
    · have hc' : col p ≠ col q := fun h => hc h.symm
      simp [hc, hc']
  simp_rw [hpt, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun p q => if col p = col q ∧ b q < b p then (1 : ℝ) else 0)]
  ring

end

end PositivityTheory.Rg.Cz
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.ReSwapSumLe
section
open Finset Matrix

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

theorem pm_apply' (σ : Equiv.Perm Q) (f : TV n ℂ Q) (I : Q → Fin n) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ σ) := rfl

theorem pm_pm (σ τ : Equiv.Perm Q) (f : TV n ℂ Q) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) (pm τ f) = pm (σ * τ) f := rfl

theorem dot_pm_swap (a c : Q) (u v : TV n ℂ Q) :
    star u ⬝ᵥ (pm (Equiv.swap a c) : Module.End ℂ (TV n ℂ Q)) v =
      star ((pm (Equiv.swap a c) : Module.End ℂ (TV n ℂ Q)) u) ⬝ᵥ v := by
  let e : (Q → Fin n) ≃ (Q → Fin n) :=
    { toFun := fun I => I ∘ Equiv.swap a c, invFun := fun I => I ∘ Equiv.swap a c,
      left_inv := fun I => by funext x; simp, right_inv := fun I => by funext x; simp }
  simp only [dotProduct, Pi.star_apply, pm_apply']
  refine Fintype.sum_equiv e _ _ fun I => ?_
  have : (I ∘ Equiv.swap a c) ∘ Equiv.swap a c = I := by funext x; simp
  simp [e, this]

theorem re_swapSum_le' (f : TV n ℂ Q) (B : Finset Q) (p : Q)
    (hp : p ∉ B) (hf : ∀ q ∈ B, ∀ q' ∈ B, q ≠ q' → pm (Equiv.swap q q') f = -f) :
    (∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f).re ≤ (star f ⬝ᵥ f).re := by
  set Y : Module.End ℂ (TV n ℂ Q) := ∑ q ∈ B, pm (Equiv.swap p q) with hY
  have hYf : Y f = ∑ q ∈ B, pm (Equiv.swap p q) f := by simp [hY, LinearMap.sum_apply]
  have hsa : ∀ u v : TV n ℂ Q, star u ⬝ᵥ Y v = star (Y u) ⬝ᵥ v := by
    intro u v
    simp only [hY, LinearMap.sum_apply, dotProduct_sum, star_sum, sum_dotProduct, dot_pm_swap]
  have hq : ∀ q ∈ B, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (Y f) =
      f - Y f + pm (Equiv.swap p q) f := by
    intro q hqB
    have hpq : p ≠ q := fun h => hp (h ▸ hqB)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hYf, ← Finset.add_sum_erase B _ hqB, map_add (f := _), map_sum, pm_pm, Equiv.swap_mul_self]
    have : ∀ q' ∈ B.erase q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (pm (Equiv.swap p q') f) =
        -(pm (Equiv.swap p q') f) := by
      intro q' hq'
      obtain ⟨hne, hq'B⟩ := Finset.mem_erase.mp hq'
      have hpq' : p ≠ q' := fun h => hp (h ▸ hq'B)
      have hperm : Equiv.swap p q * Equiv.swap p q' = Equiv.swap p q' * Equiv.swap q q' := by
        ext x
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
        split_ifs <;> simp_all
      rw [pm_pm, hperm, ← pm_pm, hf q hqB q' hq'B (Ne.symm hne), map_neg]
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
    have h1 : (pm 1 : Module.End ℂ (TV n ℂ Q)) f = f := rfl
    rw [h1]
    abel
  have hYY : Y (Y f) = (B.card : ℂ) • f - (B.card : ℂ) • Y f + Y f := by
    conv_lhs => rw [hY, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl hq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_const, ← hYf]
    simp [Nat.cast_smul_eq_nsmul]
  set g := f - Y f with hg
  have hYg : Y g = -((B.card : ℂ) • g) := by
    rw [hg, map_sub, hYY, smul_sub]
    abel
  have hgg : star g ⬝ᵥ g = (1 + (B.card : ℂ)) * (star f ⬝ᵥ g) := by
    conv_lhs => rw [hg]
    rw [star_sub, sub_dotProduct, ← hsa, ← hg, hYg, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    ring
  have hnn : 0 ≤ (star g ⬝ᵥ g).re := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_nonneg fun I _ => ?_
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (g I).re, sq_nonneg (g I).im]
  have hre : (star g ⬝ᵥ g).re = (1 + (B.card : ℝ)) * (star f ⬝ᵥ g).re := by
    rw [hgg]
    simp [Complex.mul_re]
  have hpos : 0 ≤ (star f ⬝ᵥ g).re := by
    have h1 : (0 : ℝ) < 1 + (B.card : ℝ) := by positivity
    nlinarith
  have hfg : star f ⬝ᵥ g = star f ⬝ᵥ f - ∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f := by
    rw [hg, dotProduct_sub, hYf, dotProduct_sum]
  rw [hfg, Complex.sub_re] at hpos
  linarith

end

end PositivityTheory.Rg.Cz
end

