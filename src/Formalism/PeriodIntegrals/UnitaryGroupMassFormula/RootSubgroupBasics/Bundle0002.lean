module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower
section
open Matrix

noncomputable section

namespace PI.AmpRootCommon

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

def hτ (k r : ℕ) (i : ℕ) : ℕ := if r ≤ i ∧ i ≤ r + k then i else 2 * r + k - i

def hs (k r : ℕ) (i : ℕ) : ℂ := if i = r + k then -1 else 1

theorem Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = hτ k r i.val then hs k r i.val else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, hτ, hs, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hτ_lt (i : ℕ) (hi : i < 2 * r + k + 1) : hτ k r i < 2 * r + k + 1 := by
  unfold hτ
  split_ifs <;> omega

theorem hτ_hτ (i : ℕ) (hi : i < 2 * r + k + 1) : hτ k r (hτ k r i) = i := by
  unfold hτ
  split_ifs <;> omega

theorem hs_hτ (i : ℕ) (hi : i < 2 * r + k + 1) : hs k r (hτ k r i) = hs k r i := by
  unfold hs hτ
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hs_sq (i : ℕ) : hs k r i * hs k r i = 1 := by
  unfold hs
  split_ifs <;> norm_num

theorem Hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨hτ k r i.val, hτ_lt i.val hi⟩ : Fin (2 * r + k + 1))]
  · rw [Hpk_apply, Hpk_apply, Matrix.one_apply]
    show (if hτ k r i.val = hτ k r i.val then hs k r i.val else 0) *
      (if j.val = hτ k r (hτ k r i.val) then hs k r (hτ k r i.val) else 0) = if i = j then 1 else 0
    rw [if_pos rfl, hτ_hτ i.val hi, hs_hτ i.val hi]
    by_cases hij : i = j
    · rw [if_pos (congrArg Fin.val hij).symm, if_pos hij, hs_sq]
    · rw [if_neg (fun h => hij (Fin.ext h.symm)), if_neg hij, mul_zero]
  · intro l _ hl
    rw [Hpk_apply, if_neg (fun h => hl (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem uh_left {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Hpk_mul_self]

theorem uh_inv_mul {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (Matrix.isUnit_det_of_left_inverse (uh_left hg))

theorem uh_mul_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (uh_left hg))

def Fm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i b => fvec k r z b i

theorem zhat_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Zhat k r z z' g = (Fm k r z)ᴴ * (Hpk k r * g) * Fm k r z' := by
  ext a b
  simp only [Zhat, herm, Fm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Finset.sum_comm

theorem flagMat_lower {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) (i j : Fin (r + 1)) (hji : j ≤ i) : flagMat k r z a i j = if i = j then 1 else 0 := by
  have hji' : j.val ≤ i.val := hji
  have hcol : ∀ (c d : Fin (2 * r + k + 1)), (a *ᵥ Pi.single c (1 : ℂ)) d = a d c := by
    intro c d
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [flagMat]
  by_cases hi : i.val < r
  · rw [dite_eq_left hi]
    have hj : j.val < r := lt_of_le_of_lt hji' hi
    have hf : fvec k r z j = bvec (eI k r ⟨j.val, hj⟩) := by
      unfold fvec
      rw [dite_eq_left hj]
    rw [hf]
    unfold bvec
    rw [hcol, ha.2.1 ⟨j.val, hj⟩ (eI k r ⟨i.val, hi⟩) hji']
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg hij, if_neg]
      intro h
      apply hij
      have h' := congrArg Fin.val h
      exact Fin.ext h'
  · rw [dite_eq_right hi]

theorem flagMat_upper {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) : (flagMat k r z a).BlockTriangular id := by
  intro i j hij
  have hij' : j < i := hij
  rw [flagMat_lower ha i j (le_of_lt hij'), if_neg (ne_of_gt hij')]

theorem flagMat_diag {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) (i : Fin (r + 1)) : flagMat k r z a i i = 1 := by
  rw [flagMat_lower ha i i le_rfl, if_pos rfl]

theorem mul_Fm {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r) :
    a * Fm k r z = Fm k r z * flagMat k r z a := by
  ext i b
  have hF1 : ∀ c : Fin r, fvec k r z (Fin.castSucc c) = bvec (eI k r c) := by
    intro c
    unfold fvec
    rw [dite_eq_left (show (Fin.castSucc c).val < r from c.isLt)]
    rfl
  have hF2 : fvec k r z (Fin.last r) = z := by
    unfold fvec
    rw [dite_eq_right (show ¬ (Fin.last r).val < r from lt_irrefl r)]
  have hM1 : ∀ c : Fin r, flagMat k r z a (Fin.castSucc c) b = (a *ᵥ fvec k r z b) (eI k r c) := by
    intro c
    simp only [flagMat]
    rw [dite_eq_left (show (Fin.castSucc c).val < r from c.isLt)]
    rfl
  have hM2 : flagMat k r z a (Fin.last r) b = if Fin.last r = b then 1 else 0 := by
    simp only [flagMat]
    rw [dite_eq_right (show ¬ (Fin.last r).val < r from lt_irrefl r)]
  have hL : (a * Fm k r z) i b = (a *ᵥ fvec k r z b) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fm, Matrix.of_apply]
  rw [hL, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [Fm, Matrix.of_apply, hF1, hF2, hM1, hM2, bvec]
  by_cases hi : i.val < r
  · have hei : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
    rw [Finset.sum_eq_single ⟨i.val, hi⟩, hei, hz i (Or.inl hi), Pi.single_eq_same, one_mul, zero_mul,
      add_zero]
    · intro c _ hc
      rw [Pi.single_eq_of_ne, zero_mul]
      intro h
      apply hc
      have h' := congrArg Fin.val h
      have hv : (eI k r c).val = c.val := rfl
      exact Fin.ext (by rw [← hv, ← h'])
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hsum : ∑ c : Fin r, (Pi.single (eI k r c) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i * (a *ᵥ fvec k r z b) (eI k r c) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [Pi.single_eq_of_ne, zero_mul]
      intro h
      have h' := congrArg Fin.val h
      have hv : (eI k r c).val = c.val := rfl
      have hc := c.isLt
      omega
    rw [hsum, zero_add]
    by_cases hb : Fin.last r = b
    · subst hb
      rw [if_pos rfl, mul_one, hF2]
      have hterm : ∀ j, a i j * z j = if j = i then z i else 0 := by
        intro j
        by_cases hjW : r ≤ j.val ∧ j.val ≤ r + k
        · rw [ha.2.2 i j hjW.1 hjW.2 (by omega)]
          by_cases hij : i = j
          · subst hij
            simp
          · rw [if_neg hij, if_neg (Ne.symm hij), zero_mul]
        · rw [hz j (by omega), mul_zero]
          split_ifs with hij
          · subst hij
            exact (hz _ (by omega)).symm
          · rfl
      simp [Matrix.mulVec, dotProduct, hterm]
    · rw [if_neg hb, mul_zero]
      have hbr : b.val < r := by
        have := b.isLt
        have : b.val ≠ r := fun h => hb (Fin.ext h.symm)
        omega
      have hfb : fvec k r z b = bvec (eI k r ⟨b.val, hbr⟩) := by
        unfold fvec
        rw [dite_eq_left hbr]
      rw [hfb]
      unfold bvec
      have hcol : (a *ᵥ Pi.single (eI k r ⟨b.val, hbr⟩) (1 : ℂ)) i = a i (eI k r ⟨b.val, hbr⟩) := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hcol, ha.2.1 ⟨b.val, hbr⟩ i (by show b.val ≤ i.val; omega), if_neg]
      intro h
      have h' := congrArg Fin.val h
      have hv : (eI k r ⟨b.val, hbr⟩).val = b.val := rfl
      omega

theorem flag_rel {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (ha : a ∈ RStab k r g) :
    (flagMat k r z a)ᴴ * Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) = Zhat k r z z' g := by
  have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
  have ha1 : a ∈ Nset k r := ha.1
  have hU : aᴴ * Hpk k r * a = Hpk k r := ha1.1
  have h1 := mul_Fm hz ha1
  have h2 := mul_Fm hz' hx
  have hgg : g * g⁻¹ = 1 := uh_mul_inv hg
  rw [zhat_eq]
  calc (flagMat k r z a)ᴴ * ((Fm k r z)ᴴ * (Hpk k r * g) * Fm k r z') * flagMat k r z' (g⁻¹ * a * g)
      = (Fm k r z * flagMat k r z a)ᴴ * (Hpk k r * g) *
          (Fm k r z' * flagMat k r z' (g⁻¹ * a * g)) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = (a * Fm k r z)ᴴ * (Hpk k r * g) * (g⁻¹ * a * g * Fm k r z') := by rw [← h1, ← h2]
    _ = (Fm k r z)ᴴ * (aᴴ * Hpk k r * (g * g⁻¹) * a) * g * Fm k r z' := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = (Fm k r z)ᴴ * (Hpk k r * g) * Fm k r z' := by
        rw [hgg, Matrix.mul_one, hU]
        simp only [Matrix.mul_assoc]

end PI.AmpRootCommon
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.PtEntryNeZeroImp
section
noncomputable section

namespace PI.AmpRootCommon

open Formalism.MainNotions.S

def pv : List (ℂ × ℕ) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < s then s - 1 - i else s + pv bs (i - s)

theorem ptEntry_ne_zero_imp : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), ptEntry bs i j ≠ 0 → j = pv bs i := by
  intro bs
  induction bs with
  | nil => intro i j h; simp [ptEntry] at h
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro i j h
    unfold ptEntry at h
    unfold pv
    by_cases h1 : i < s ∧ j < s
    · rw [ite_eq_left h1] at h
      by_cases h2 : i + j + 1 = s
      · rw [ite_eq_left h1.1]; omega
      · rw [ite_eq_right h2] at h; exact absurd rfl h
    · rw [ite_eq_right h1] at h
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [ite_eq_left h3] at h
        have hj := ih (i - s) (j - s) h
        rw [ite_eq_right (by omega)]; omega
      · rw [ite_eq_right h3] at h; exact absurd rfl h

theorem pv_spec : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i < (bs.map Prod.snd).sum →
    pv bs i < (bs.map Prod.snd).sum ∧ pv bs (pv bs i) = i ∧ ptEntry bs i (pv bs i) ≠ 0 := by
  intro bs
  induction bs with
  | nil => intro _ i hi; simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro hb i hi
    have ht : t ≠ 0 := (hb (t, s) (by simp)).1
    have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    by_cases h1 : i < s
    · have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, h1]
      have e2 : pv ((t, s) :: bs) (s - 1 - i) = i := by
        simp only [pv]; rw [ite_eq_left (by omega)]; omega
      refine ⟨by omega, by rw [e1, e2], ?_⟩
      rw [e1]; unfold ptEntry
      rw [ite_eq_left ⟨h1, by omega⟩, ite_eq_left (by omega)]; exact ht
    · obtain ⟨ih1, ih2, ih3⟩ := ih hb' (i - s) (by omega)
      have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, h1]
      have e2 : pv ((t, s) :: bs) (s + pv bs (i - s)) = i := by
        simp only [pv]; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ih2]; omega
      refine ⟨by omega, by rw [e1, e2], ?_⟩
      rw [e1]; unfold ptEntry
      rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]; exact ih3

theorem pv_adj : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i + 1 < (bs.map Prod.snd).sum →
    (pv bs (i + 1) + 1 = pv bs i ∧ ptEntry bs (pv bs (i + 1)) (i + 1) = ptEntry bs (pv bs i) i) ∨
      pv bs i < pv bs (i + 1) := by
  intro bs
  induction bs with
  | nil => intro _ i hi; simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro hb i hi
    have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
    simp only [List.map_cons, List.sum_cons] at hi
    by_cases h1 : i + 1 < s
    · left
      have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
      have e2 : pv ((t, s) :: bs) (i + 1) = s - 1 - (i + 1) := by simp [pv, h1]
      rw [e1, e2]
      refine ⟨by omega, ?_⟩
      unfold ptEntry
      rw [ite_eq_left ⟨by omega, h1⟩, ite_eq_left (by omega),
        ite_eq_left ⟨by omega, by omega⟩, ite_eq_left (by omega)]
    · by_cases h2 : i + 1 = s
      · right
        have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
        have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i + 1 - s) := by simp [pv, h1]
        rw [e1, e2]; omega
      · have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, show ¬ i < s by omega]
        have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i - s + 1) := by
          simp only [pv]; rw [ite_eq_right h1, show i + 1 - s = i - s + 1 by omega]
        rw [e1, e2]
        rcases ih hb' (i - s) (by omega) with ⟨h3, h4⟩ | h3
        · left
          refine ⟨by omega, ?_⟩
          have hA : ¬ (s + pv bs (i - s + 1) < s ∧ i + 1 < s) := by omega
          have hB : s ≤ s + pv bs (i - s + 1) ∧ s ≤ i + 1 := by omega
          have hC : ¬ (s + pv bs (i - s) < s ∧ i < s) := by omega
          have hD : s ≤ s + pv bs (i - s) ∧ s ≤ i := by omega
          unfold ptEntry
          rw [ite_eq_right hA, ite_eq_left hB, ite_eq_right hC, ite_eq_left hD,
            Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, show i + 1 - s = i - s + 1 by omega]
          exact h4
        · right; omega

end PI.AmpRootCommon
end
end

