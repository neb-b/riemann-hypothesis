module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0007

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MatExtBvec
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

def sg (k r i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i

theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = sg k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  unfold Hpk sg
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    rcases h1 with h1 | h1
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_pos ⟨h1, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_neg (by omega), if_pos ⟨by omega, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1]
    push Not at h1
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h2 : i = j
    · subst h2; rw [if_pos ⟨h1.1, h1.2, rfl⟩, if_pos rfl]
    · rw [if_neg (fun h => h2 h.2.2), if_neg (fun h => h2 (Fin.ext h.symm))]

theorem hpk_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Hpk k r j i = Hpk k r i j := by
  rw [hpk_apply, hpk_apply]; unfold sg
  split_ifs <;> first | rfl | omega

theorem hpk_conjT (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hpk_symm, hpk_apply]
  split_ifs <;> simp

theorem sg_lt {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i < 2 * r + k + 1 := by
  unfold sg; split_ifs <;> omega

theorem sg_sg {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r (sg k r i) = i := by
  unfold sg; split_ifs <;> omega

theorem sg_rk {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i = r + k ↔ i = r + k := by
  unfold sg; split_ifs <;> omega

theorem hpk_apply' (k r i : ℕ) (hi : i < 2 * r + k + 1) (j : Fin (2 * r + k + 1)) :
    Hpk k r ⟨i, hi⟩ j = if j.val = sg k r i then (if i = r + k then -1 else 1) else 0 :=
  hpk_apply k r ⟨i, hi⟩ j

theorem hpk_mul (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨sg k r i.val, sg_lt i.2⟩ : Fin _)]
  · rw [hpk_apply k r i ⟨sg k r i.val, sg_lt i.2⟩, hpk_apply' k r _ (sg_lt i.2) j, sg_sg i.2, Matrix.one_apply,
      if_pos (show ((⟨sg k r i.val, sg_lt i.2⟩ : Fin (2 * r + k + 1)).val = sg k r i.val) from rfl)]
    have hs := sg_rk (k := k) (r := r) i.2
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
      by_cases h : i.val = r + k
      · rw [if_pos h, if_pos (hs.2 h)]; norm_num
      · rw [if_neg h, if_neg (fun h' => h (hs.1 h'))]; norm_num
    · rw [if_neg hij, if_neg (fun h : j.val = i.val => hij (Fin.ext h.symm)), mul_zero]
  · intro b _ hb; rw [hpk_apply k r i b, if_neg (fun h => hb (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_mid {n N : ℕ} (h : N = n + 2) (f : Fin N → ℂ) (h0 : ∀ q : Fin N, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin N, q.val = n + 1 → f q = 0) : ∑ q, f q = ∑ q : Fin n, f ⟨q.val + 1, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, h0 0 rfl, h1 (Fin.last n).succ (by simp)]
  simp only [zero_add, add_zero]; rfl

theorem mv_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (q p : Fin n) : (M *ᵥ bvec q) p = M p q := by
  unfold bvec; simp [mulVec, dotProduct, Pi.single_apply]

theorem mat_ext_bvec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : ∀ q, A *ᵥ bvec q = B *ᵥ bvec q) : A = B := by
  ext i j; have := congrFun (h j) i; rwa [mv_bvec, mv_bvec] at this

section Lev
variable {k r' : ℕ}

def sh (q : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := ⟨q.val + 1, by have := q.2; omega⟩

theorem sh_val (q : Fin (2 * r' + k + 1)) : (sh q).val = q.val + 1 := rfl

theorem exists_sh (p : Fin (2 * (1 + r') + k + 1)) (hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) :
    ∃ q : Fin (2 * r' + k + 1), p = sh q :=
  ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp [sh]; omega)⟩

theorem sum_sh (f : Fin (2 * (1 + r') + k + 1) → ℂ) (h0 : ∀ q : Fin _, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin _, q.val = 2 * (1 + r') + k → f q = 0) : ∑ q, f q = ∑ q : Fin (2 * r' + k + 1), f (sh q) :=
  sum_mid (n := 2 * r' + k + 1) (by omega) f h0 (fun q hq => h1 q (by omega))

theorem lv_in (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) : liftVec k 1 r' v (sh q) = v q := by
  unfold liftVec; rw [dite_eq_left (show 1 ≤ (sh q).val ∧ (sh q).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := q.2; simp [sh]; omega⟩)]
  congr 1

theorem lv_out (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : liftVec k 1 r' v p = 0 := by
  unfold liftVec; rw [dite_eq_right (by omega)]

theorem io_in (g : Mat k r') (p q : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (sh p) (sh q) = g p q := by
  unfold ιLev
  rw [dite_eq_left (show 1 ≤ (sh p).val ∧ (sh p).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := p.2; simp [sh]; omega⟩),
    dite_eq_left (show 1 ≤ (sh q).val ∧ (sh q).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := q.2; simp [sh]; omega⟩)]
  congr 1

theorem io_out (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · rw [dite_eq_left hp, dite_eq_right (by omega), if_neg (fun h => by subst h; omega)]
  · rw [dite_eq_right hp]

theorem io_out' (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  unfold ιLev; rw [dite_eq_right (by omega)]

theorem io_lv (g : Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' v = liftVec k 1 r' (g *ᵥ v) := by
  funext p
  simp only [mulVec, dotProduct]
  rw [sum_sh _ (fun q hq => by rw [lv_out v q (by omega), mul_zero]) (fun q hq => by rw [lv_out v q (by omega), mul_zero])]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · obtain ⟨p', rfl⟩ := exists_sh p hp
    rw [lv_in]; simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun q _ => by rw [io_in, lv_in]
  · rw [lv_out _ p (by omega)]
    exact Finset.sum_eq_zero fun q _ => by
      rw [io_out' g p _ (by omega), if_neg (fun h => by rw [h, sh_val] at hp; omega), zero_mul]

theorem io_bvec_out (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) :
    ιLev k 1 r' g *ᵥ bvec q = bvec q := by
  funext p; rw [mv_bvec, io_out g p q hq]; unfold bvec; simp only [Pi.single_apply]

theorem bvec_lv (q : Fin (2 * r' + k + 1)) : (bvec (sh q) : Fin (2 * (1 + r') + k + 1) → ℂ) = liftVec k 1 r' (bvec q) := by
  funext p
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · obtain ⟨p', rfl⟩ := exists_sh p hp
    rw [lv_in]; unfold bvec; simp only [Pi.single_apply, Fin.ext_iff, sh_val]; simp
  · rw [lv_out _ p (by omega)]; unfold bvec; rw [Pi.single_apply, if_neg (fun h => by rw [h, sh_val] at hp; omega)]

theorem io_bvec_sh (g : Mat k r') (q : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g *ᵥ bvec (sh q) = liftVec k 1 r' (g *ᵥ bvec q) := by
  rw [bvec_lv, io_lv]

theorem io_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply mat_ext_bvec; intro q
  rw [← Matrix.mulVec_mulVec]
  by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · obtain ⟨q', rfl⟩ := exists_sh q hq
    rw [io_bvec_sh, io_bvec_sh, io_lv, Matrix.mulVec_mulVec]
  · rw [io_bvec_out _ _ (by omega), io_bvec_out _ _ (by omega), io_bvec_out _ _ (by omega)]

theorem io_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext_bvec; intro q
  rw [Matrix.one_mulVec]
  by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · obtain ⟨q', rfl⟩ := exists_sh q hq
    rw [io_bvec_sh, Matrix.one_mulVec, bvec_lv]
  · rw [io_bvec_out _ _ (by omega)]

theorem io_conjT (g : Mat k r') : ιLev k 1 r' gᴴ = (ιLev k 1 r' g)ᴴ := by
  ext p q
  rw [conjTranspose_apply]; unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 <;>
    by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · rw [dite_eq_left hp, dite_eq_left hq, dite_eq_left hq, dite_eq_left hp, conjTranspose_apply]
  · rw [dite_eq_left hp, dite_eq_right hq, dite_eq_right hq, if_neg (fun h => by subst h; exact hq hp), star_zero]
  · rw [dite_eq_right hp, dite_eq_left hq, dite_eq_right hp, if_neg (fun h => by subst h; exact hp hq), star_zero]
  · rw [dite_eq_right hp, dite_eq_right hq]; by_cases h : p = q
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]

end Lev

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExists2
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem aAll_of (hb : AStepBase) (hs : AStepSucc) : ∀ k r : ℕ, 1 ≤ k → AAt k r := by
  intro k r hk
  induction r with
  | zero => exact hb k hk
  | succ r' ih => exact hs k (r' + 1) r' (by omega) hk ih

theorem bAll_of (hb : BStepBase) (hs : BStepSucc) :
    ∀ k r : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r δ := by
  intro k r hk
  induction r with
  | zero => intro δ hδ _; exact hb k hk δ hδ
  | succ r' ih =>
    intro δ hδ hδ'
    exact hs k (r' + 1) r' (by omega) hk δ hδ hδ' (ih (δ / 4) (by positivity) (by linarith))

theorem xiExists_of (hA : ∀ k r : ℕ, 1 ≤ k → AAt k r) (hB : ∀ k r : ℕ, 1 ≤ k → BAt k r (1 / 2))
    (hC : CoefStep) (hX : XiIntStep) : XiExists := by
  intro k r Wp Wq _ _ _ _ _ _ D A hA'
  obtain ⟨eS, heS, hBs⟩ := hB k r D.k_pos
  have he0 : 0 < min eS (1 / 10 : ℝ) := lt_min heS (by norm_num)
  have adm : SAdm k r (fun l => s0 k r l - min eS (1 / 10)) := fun l => by
    simp only [sub_sub_cancel]; exact ⟨he0, min_le_right _ _⟩
  have adm' : ∀ l, 0 < s0 k r l - (s0 k r l - min eS (1 / 10)) ∧ s0 k r l - (s0 k r l - min eS (1 / 10)) ≤ eS :=
    fun l => by simp only [sub_sub_cancel]; exact ⟨he0, min_le_left _ _⟩
  exact ⟨xiN k r _, hC k r Wp Wq D A _ adm hA' (hA k r D.k_pos _ adm D.μG D.haarG A hA'),
    hX k r Wp Wq D _ adm (hBs _ adm' D.z D.z_mem D.T_pos D.μN D.haarN)
      (hBs _ adm' D.z' D.z'_mem D.T'_pos D.μN D.haarN)⟩

theorem xiExists_of_induction_steps (hAb : AStepBase) (hAs : AStepSucc) (hBb : BStepBase) (hBs : BStepSucc)
    (hC : CoefStep) (hX : XiIntStep) : XiExists :=
  xiExists_of (aAll_of hAb hAs) (fun k r hk => bAll_of hBb hBs k r hk (1 / 2) (by norm_num) le_rfl) hC hX

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

