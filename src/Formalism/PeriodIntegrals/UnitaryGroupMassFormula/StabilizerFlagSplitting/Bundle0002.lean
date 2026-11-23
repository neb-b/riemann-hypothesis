module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.SubFlag
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.FixFlag
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.StabSplit

private lemma mem_flagSpan_of_eq_zero_of_le {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1))
    (w : Fin (2 * r + k + 1) → ℂ) (hw : ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → w i = 0) :
    w ∈ flagSpan k r z a := by
  have hw' : w = ∑ i : Fin (2 * r + k + 1), w i • bvec i := by
    ext j
    simp [bvec, Pi.single_apply, Finset.sum_apply]
  rw [hw']
  refine Submodule.sum_mem _ (fun i _ => ?_)
  by_cases hi : a.val ≤ i.val
  · simp [hw i hi]
  · push_neg at hi
    have hr : i.val < r := by omega
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨i.val, by omega⟩, Fin.lt_def.mpr hi⟩, ?_⟩)
    have hr' : (⟨i.val, by omega⟩ : Fin (r + 1)).val < r := hr
    simp only [fvec, dif_pos hr']
    congr 1

private lemma mulVec_mem_flagSpan_of_fixes_fvec {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1))
    (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hf : ∀ b, h *ᵥ fvec k r z b = fvec k r z b) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : w ∈ flagSpan k r z a) : h *ᵥ w ∈ flagSpan k r z a := by
  unfold flagSpan at *
  have hle : Submodule.span ℂ (Set.range fun b : {b : Fin (r + 1) // b < a} => fvec k r z b.1) ≤
      (Submodule.span ℂ (Set.range fun b : {b : Fin (r + 1) // b < a} => fvec k r z b.1)).comap
        (Matrix.mulVecLin h) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    rw [hf]
    exact Submodule.subset_span ⟨b, rfl⟩
  exact hle hw

theorem stabilizer_subgroup_flag : SubFlag := by
  unfold SubFlag
  intro k r z hz s hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨hhU, hhe, hhz⟩ := hh
  obtain ⟨hmU, hmc, hmd⟩ := hm
  have hhU' : hᴴ * Hpk k r * h = Hpk k r := hhU
  have hmU' : mᴴ * Hpk k r * m = Hpk k r := hmU
  have hfix : ∀ b, h *ᵥ fvec k r z b = fvec k r z b := by
    intro b
    unfold fvec
    split_ifs with hb
    · exact (hhe ⟨b.val, hb⟩).1
    · exact hhz
  refine ⟨?_, fun a => ?_⟩
  · show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc mᴴ * hᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hhU']; exact hmU'
  · have hm1 : m *ᵥ fvec k r z a - fvec k r z a ∈ flagSpan k r z a := by
      apply mem_flagSpan_of_eq_zero_of_le
      intro i hi
      rw [Pi.sub_apply, sub_eq_zero]
      unfold fvec
      split_ifs with ha
      · simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact hmc ⟨a.val, ha⟩ i hi
      · have hri : r ≤ i.val := by omega
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single i]
        · by_cases hzi : z i = 0
          · simp [hzi]
          · have hik : i.val ≤ r + k := by
              by_contra hc
              exact hzi (hz i (Or.inr (by omega)))
            rw [hmd i i hri hik hri, if_pos rfl, one_mul]
        · intro j _ hji
          by_cases hzj : z j = 0
          · simp [hzj]
          · have h1 : r ≤ j.val := by
              by_contra hc
              exact hzj (hz j (Or.inl (by omega)))
            have h2 : j.val ≤ r + k := by
              by_contra hc
              exact hzj (hz j (Or.inr (by omega)))
            rw [hmd i j h1 h2 hri, if_neg (Ne.symm hji), zero_mul]
        · intro hi'
          exact absurd (Finset.mem_univ i) hi'
    have heq : (h * m) *ᵥ fvec k r z a - fvec k r z a =
        h *ᵥ (m *ᵥ fvec k r z a - fvec k r z a) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hfix]
    rw [heq]
    exact mulVec_mem_flagSpan_of_fixes_fvec z a h hfix _ hm1

end PI.StabSplit
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.FixSub
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic

noncomputable section

namespace PI.StabSplit.FixW

def uOf (k r : ℕ) (g : B.Mat k r) : B.Mat k r :=
  Matrix.of fun i j =>
    if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then g i j
    else if i = j then 1 else 0

lemma uOf_out_col {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hj : j.val < r ∨ r + k < j.val) : uOf k r g i j = if i = j then 1 else 0 := by
  simp only [uOf, of_apply]
  rw [if_neg (by omega)]

lemma uOf_out_row {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi : i.val < r ∨ r + k < i.val) : uOf k r g i j = if i = j then 1 else 0 := by
  simp only [uOf, of_apply]
  rw [if_neg (by omega)]

lemma uOf_in {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi1 : r ≤ i.val) (hi2 : i.val ≤ r + k) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    uOf k r g i j = g i j := by
  simp only [uOf, of_apply]
  rw [if_pos ⟨⟨hi1, hi2⟩, hj1, hj2⟩]

lemma uOf_W_out {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi1 : r ≤ i.val) (hi2 : i.val ≤ r + k) (hj : j.val < r ∨ r + k < j.val) :
    uOf k r g i j = 0 := by
  rw [uOf_out_col g i j hj, if_neg]
  intro h; subst h; omega

lemma herm_entry {k r : ℕ} (A C : B.Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Aᴴ * Hpk k r * C) i j = ∑ p, star (A p i) * sgn k r p * C (sig k r p) j := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, conjTranspose_apply, Hpk_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [mul_ite, ite_mul, Finset.sum_ite_eq']

lemma mulVec_bvec {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    A *ᵥ bvec j = fun i => A i j := by
  ext i; simp [bvec, mulVec, dotProduct, Pi.single_apply]

lemma fix_col {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (j : Fin (2 * r + k + 1)) (hj : j.val < r) (i : Fin (2 * r + k + 1)) :
    g i j = if i = j then 1 else 0 := by
  have h := congrFun (hg.2 ⟨j.val, by omega⟩) i
  have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
  simp only [fvec, dif_pos hj, e, mulVec_bvec] at h
  rw [h]; simp [bvec, Pi.single_apply]

lemma isometry_fix_flagAnisotropicVector_of_fix_frame {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z) :
    g *ᵥ z = z := by
  have h := hg.2 (Fin.last r)
  simpa [fvec] using h

lemma fix_zero {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (i j : Fin (2 * r + k + 1)) (hi : r + k < i.val) (hj2 : j.val ≤ r + k) : g i j = 0 := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  set a := sig k r i with ha
  have har : a.val < r := by rw [ha, sig_hi k r i hi]; have := i.isLt; omega
  have e := congrFun (congrFun hU a) j
  rw [herm_entry, Finset.sum_eq_single a] at e
  · rw [fix_col hg a har a, if_pos rfl, ha, sig_sig] at e
    have hs : sgn k r (sig k r i) = 1 := by
      unfold sgn; rw [if_neg]; rw [sig_hi k r i hi]; have := i.isLt; omega
    rw [hs, star_one, one_mul, one_mul, Hpk_eq, if_neg] at e
    · exact e
    · rw [← ha, sig_sig]; intro h; subst h; omega
  · intro p _ hp
    rw [fix_col hg a har p, if_neg hp, star_zero, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma uOf_mem {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z) :
    uOf k r g ∈ UH (Hpk k r) := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  show (uOf k r g)ᴴ * Hpk k r * uOf k r g = Hpk k r
  ext i j
  rw [herm_entry]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [← congrFun (congrFun hU i) j, herm_entry]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [sig_mid k r p hp.1 hp.2, uOf_in g p i hp.1 hp.2 hi.1 hi.2, uOf_in g p j hp.1 hp.2 hj.1 hj.2]
      · rw [uOf_out_row g p i (by omega), if_neg (by intro h; subst h; omega), star_zero, zero_mul,
          zero_mul]
        rcases (show p.val < r ∨ r + k < p.val by omega) with hp' | hp'
        · rw [fix_zero hg (sig k r p) j (by rw [sig_lo k r p hp']; omega) hj.2, mul_zero]
        · rw [fix_zero hg p i hp' hi.2, star_zero, zero_mul, zero_mul]
    · rw [Finset.sum_eq_single (sig k r j)]
      · rw [sig_sig, uOf_out_col g j j (by omega), if_pos rfl, mul_one]
        have hsj : (sig k r j).val < r ∨ r + k < (sig k r j).val := by
          have := j.isLt; rw [sig_val]; split_ifs <;> omega
        rw [uOf_out_row g (sig k r j) i hsj, if_neg (by intro h; rw [← h] at hi; omega), star_zero,
          zero_mul, Hpk_eq, if_neg]
        rw [sig_mid k r i hi.1 hi.2]; intro h; subst h; omega
      · intro p _ hp
        rw [uOf_out_col g _ j (by omega), if_neg (by intro h; apply hp; rw [← h, sig_sig]), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single i]
    · rw [uOf_out_col g i i (by omega), if_pos rfl, star_one, one_mul]
      have hsi : (sig k r i).val < r ∨ r + k < (sig k r i).val := by
        have := i.isLt; rw [sig_val]; split_ifs <;> omega
      rw [uOf_out_row g (sig k r i) j hsi, Hpk_eq]
      by_cases h : sig k r i = j
      · rw [if_pos h, if_pos h.symm, mul_one]
      · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
    · intro p _ hp
      rw [uOf_out_col g p i (by omega), if_neg hp, star_zero, zero_mul, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma uOf_fix_out {k r : ℕ} (g : B.Mat k r) (c : Fin (2 * r + k + 1))
    (hc : c.val < r ∨ r + k < c.val) : uOf k r g *ᵥ bvec c = bvec c := by
  rw [mulVec_bvec]; ext i
  rw [uOf_out_col g i c hc]; simp [bvec, Pi.single_apply]

lemma unipotent_part_fixes_vector {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : B.Mat k r}
    (hg : g ∈ FixSet k r z) : uOf k r g *ᵥ z = z := by
  ext i
  have hgz := congrFun (isometry_fix_flagAnisotropicVector_of_fix_frame hg) i
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · rw [← hgz]
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
    · rw [uOf_in g i l hi.1 hi.2 hl.1 hl.2]
    · rw [hz l (by omega), mul_zero, mul_zero]
  · simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · rw [uOf_out_row g i i (by omega), if_pos rfl, one_mul]
    · intro l _ hl
      rw [uOf_out_row g i l (by omega), if_neg (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma uOf_UW {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : B.Mat k r}
    (hg : g ∈ FixSet k r z) : uOf k r g ∈ UWset k r z := by
  refine ⟨uOf_mem hg, fun a => ⟨?_, ?_⟩, unipotent_part_fixes_vector hz hg⟩
  · exact uOf_fix_out g _ (Or.inl (by simp [eI]))
  · exact uOf_fix_out g _ (Or.inr (by simp [esI]; omega))

def yv (k r : ℕ) (g : B.Mat k r) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if i.val < r then g i j else if i = j then 1 else 0

lemma uOf_yv {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (j : Fin (2 * r + k + 1)) (hj : j.val ≤ r + k) : uOf k r g *ᵥ yv k r g j = fun i => g i j := by
  ext i
  simp only [mulVec, dotProduct]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · have key : ∀ l, uOf k r g i l * yv k r g j l =
        if l = j then (if r ≤ j.val then g i j else 0) else 0 := by
      intro l
      by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
      · rw [uOf_in g i l hi.1 hi.2 hl.1 hl.2]
        simp only [yv, if_neg (show ¬ l.val < r by omega)]
        by_cases hlj : l = j
        · subst hlj; rw [if_pos rfl, if_pos rfl, if_pos hl.1, mul_one]
        · rw [if_neg hlj, if_neg hlj, mul_zero]
      · rw [uOf_W_out g i l hi.1 hi.2 (by omega), zero_mul]
        by_cases hlj : l = j
        · subst hlj; rw [if_pos rfl, if_neg (by omega)]
        · rw [if_neg hlj]
    rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ _)]
    by_cases hjr : r ≤ j.val
    · rw [if_pos hjr]
    · rw [if_neg hjr, fix_col hg j (by omega) i, if_neg]; intro h; subst h; omega
  · rw [Finset.sum_eq_single i]
    · rw [uOf_out_row g i i (by omega), if_pos rfl, one_mul]
      simp only [yv]
      by_cases hir : i.val < r
      · rw [if_pos hir]
      · rw [if_neg hir, if_neg (by intro h; subst h; omega)]
        by_cases hjr : j.val < r
        · rw [fix_col hg j hjr i, if_neg (by intro h; subst h; omega)]
        · rw [fix_zero hg i j (by omega) hj]
    · intro l _ hl
      rw [uOf_out_row g i l (by omega), if_neg (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem fixed_point_subgroup : FixSub := by
  intro k r z hz g hg
  have hu := uOf_UW hz hg
  have hH : (Hpk k r).det ≠ 0 := by
    have h2 := congrArg Matrix.det (Hpk_sq k r)
    rw [det_mul, det_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have hdet : IsUnit (uOf k r g).det := by
    have h := congrArg Matrix.det hu.1
    rw [det_mul, det_mul, det_conjTranspose] at h
    refine isUnit_iff_ne_zero.mpr (fun h0 => hH ?_)
    rw [← h, h0, mul_zero]
  refine ⟨uOf k r g, hu, (uOf k r g)⁻¹ * g, ?_, ?_⟩
  · have hm : (uOf k r g)⁻¹ * g ∈ UH (Hpk k r) := by
      have hinv := (uHGroup (2 * r + k + 1) (Hpk k r) (isUnit_iff_ne_zero.mpr hH)).2
      exact hinv.1 _ (hinv.2 _ hu.1).2 _ hg.1
    refine ⟨hm, fun a i hi => ?_, fun i j h1 h2 h3 => ?_⟩
    · have e : (eI k r a).val < r := by simp [eI]
      have hy := congrFun (uOf_yv hg (eI k r a) (by omega)) i
      have hc : ((uOf k r g)⁻¹ * g) i (eI k r a) = yv k r g (eI k r a) i := by
        rw [← congrFun (mulVec_bvec ((uOf k r g)⁻¹ * g) (eI k r a)) i, ← mulVec_mulVec,
          mulVec_bvec g, ← uOf_yv hg (eI k r a) (by omega), mulVec_mulVec,
          nonsing_inv_mul _ hdet, one_mulVec]
      rw [hc]; simp only [yv]
      by_cases hir : i.val < r
      · rw [if_pos hir, fix_col hg _ e i]
      · rw [if_neg hir]
    · have hc : ((uOf k r g)⁻¹ * g) i j = yv k r g j i := by
        rw [← congrFun (mulVec_bvec ((uOf k r g)⁻¹ * g) j) i, ← mulVec_mulVec,
          mulVec_bvec g, ← uOf_yv hg j h2, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
      rw [hc]; simp only [yv, if_neg (show ¬ i.val < r by omega)]
  · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul]

end PI.StabSplit.FixW

namespace PI.StabSplit

theorem fixed_point_subgroup : FixSub := FixW.fixed_point_subgroup

end PI.StabSplit
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.MulVecColOfMul
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.StabSplit

def Ym (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun i j => gramVec k r z z' γ j i

def Pm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : B.Mat k r :=
  Proj.prj (Hpk k r) (Ym k r z z' γ)

lemma Ym_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (c) :
    Ym k r z z' γ *ᵥ c = ∑ j, c j • gramVec k r z z' γ j := by
  ext i
  simp [Ym, mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma L_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v) (j) :
    (((Ym k r z z' γ)ᴴ * Hpk k r) *ᵥ v) j = herm (Hpk k r) v (gramVec k r z z' γ j) := by
  simp only [herm, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, Ym, of_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma gram_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    gramM k r z z' γ = (Ym k r z z' γ)ᴴ * Hpk k r * Ym k r z z' γ := by
  ext i j
  rw [gramM, ← L_mulVec]
  simp only [mulVec, dotProduct, Matrix.mul_apply, Ym, of_apply]

lemma mem_U_iff (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v) :
    v ∈ Uperp k r z z' γ ↔ ((Ym k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
  have : (Matrix.of fun i j => star (gramVec k r z z' γ i j)) = (Ym k r z z' γ)ᴴ := by
    ext i j; simp [Ym, conjTranspose_apply]
  rw [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, this]

lemma hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h := congrArg Matrix.det (GBasic.Hpk_sq k r)
  rw [det_mul, det_one] at h
  exact isUnit_iff_ne_zero.2 (by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h)

lemma GV_one (k r : ℕ) : (1 : B.Mat k r) ∈ B.GV k r := (uHGroup _ _ (hpk_unit k r)).1

lemma GV_mul (k r : ℕ) {g h : B.Mat k r} (hg : g ∈ B.GV k r) (hh : h ∈ B.GV k r) :
    g * h ∈ B.GV k r := (uHGroup _ _ (hpk_unit k r)).2.1 g hg h hh

lemma GV_unit (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) : IsUnit g.det :=
  ((uHGroup _ _ (hpk_unit k r)).2.2 g hg).1

lemma GV_inv (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ ∈ B.GV k r :=
  ((uHGroup _ _ (hpk_unit k r)).2.2 g hg).2

lemma GV_eq (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) : gᴴ * Hpk k r * g = Hpk k r := hg

lemma gram_unit (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hs : Std k r z z')
    (hp : PosPt k r z z' γ) : IsUnit ((Ym k r z z' γ)ᴴ * Hpk k r * Ym k r z z' γ).det := by
  rw [← gram_eq]
  have h := gGram k r z z' hs.2.1.1 hs.2.2.1 γ hp.1
  have hne : (gramM k r z z' γ).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    have := hp.2
    have h1 : (Gf k r z z' γ : ℝ) = 0 := by exact_mod_cast h
    linarith
  exact isUnit_iff_ne_zero.2 hne

lemma herm_unit (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rw [GV_eq k r hg]

lemma mul_eq_of_cols {m : Type*} [Fintype m] (k r : ℕ) (A : B.Mat k r)
    (C : Matrix (Fin (2 * r + k + 1)) m ℂ) (h : ∀ j, A *ᵥ (fun i => C i j) = fun i => C i j) :
    A * C = C := by
  ext i j
  have := congrFun (h j) i
  simpa [mulVec, dotProduct, Matrix.mul_apply] using this

lemma mulVec_col_of_mul {m : Type*} [Fintype m] (k r : ℕ) (A : B.Mat k r)
    (C : Matrix (Fin (2 * r + k + 1)) m ℂ) (h : A * C = C) (j : m) :
    A *ᵥ (fun i => C i j) = fun i => C i j := by
  ext i
  have := congrFun (congrFun h i) j
  simpa [mulVec, dotProduct, Matrix.mul_apply] using this

lemma flag_nilp {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ (a.val + 1)) *ᵥ v a = 0 := by
  intro a
  induction' ht : a.val using Nat.strong_induction_on with t ih generalizing a
  have hsp : Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1) ≤
      LinearMap.ker (Matrix.mulVecLin ((g - 1) ^ t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hb : b.1.val < t := by rw [← ht]; exact b.2
    have := ih b.1.val hb b.1 rfl
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have e : t = (t - (b.1.val + 1)) + (b.1.val + 1) := by omega
    rw [e, pow_add, ← mulVec_mulVec, this, mulVec_zero]
  have h1 := hsp (hv a)
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h1
  rw [pow_succ, ← mulVec_mulVec, sub_mulVec, one_mulVec]
  exact h1

lemma flag_nilp_all {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ m) *ᵥ v a = 0 := by
  intro a
  have e : m = (m - (a.val + 1)) + (a.val + 1) := by omega
  rw [e, pow_add, ← mulVec_mulVec, flag_nilp g v hv a, mulVec_zero]

lemma conj_pow {N : ℕ} (A G Gi : Matrix (Fin N) (Fin N) ℂ) (h1 : Gi * G = 1) (h2 : G * Gi = 1) :
    ∀ p : ℕ, (Gi * A * G) ^ p = Gi * A ^ p * G := by
  intro p
  induction p with
  | zero => simp [h1]
  | succ p ih =>
    rw [pow_succ, ih, pow_succ]
    calc
      Gi * A ^ p * G * (Gi * A * G) = Gi * A ^ p * (G * Gi) * A * G := by
        simp only [Matrix.mul_assoc]
      _ = Gi * (A ^ p * A) * G := by
        rw [h2]
        simp only [Matrix.mul_one, Matrix.mul_assoc]

lemma fvec_lt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    fvec k r z ⟨a.val, by omega⟩ = bvec (eI k r a) := by
  unfold fvec; rw [dite_eq_left a.isLt]

end PI.StabSplit
end
end

