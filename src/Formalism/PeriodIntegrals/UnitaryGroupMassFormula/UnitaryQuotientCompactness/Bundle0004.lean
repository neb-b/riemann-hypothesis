module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnipotentRadicalContracting
section
open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

lemma uw_conj_N {h n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : h * n * h⁻¹ ∈ Nset k r := by
  rw [mem_Nset_iff] at hn ⊢
  obtain ⟨hnU, hnc⟩ := hn
  have hU : h ∈ UH (Hpk k r) := hh.1
  have hhi := inv_mem_UW hh
  refine ⟨mul_mem_UH (mul_mem_UH hU hnU) (inv_mem_UH hU), fun i j hj hi => ?_⟩
  by_cases hjW : r ≤ j.val
  · have hir : r ≤ i.val := by
      have := min_eq_right hjW
      omega
    have hA : ∀ b, inW k r b → (h * n) i b = h i b := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · rw [hnc b b hb2 (by rw [min_eq_right hb1]; exact hb1), if_pos rfl, mul_one]
      · intro a _ hab
        by_cases har : r ≤ a.val
        · rw [hnc a b hb2 (by rw [min_eq_right hb1]; exact har), if_neg hab, mul_zero]
        · rw [uw_block hh i a (fun h' => har h'.2.1),
            if_neg (fun e => har (by rw [← e]; exact hir)), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ b) h'
    have hone : (h * h⁻¹) i j = if i = j then 1 else 0 := by
      rw [mul_inv_UH hU, Matrix.one_apply]
    rw [← hone, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : inW k r b
    · rw [hA b hb]
    · rw [uw_block hhi b j (fun h' => hb h'.1),
        if_neg (fun e => hb (by rw [e]; exact ⟨hjW, hj⟩)), mul_zero, mul_zero]
  · push Not at hjW
    have hmin : min j.val r = j.val := min_eq_left hjW.le
    have hij : j.val ≤ i.val := by omega
    have hjn : ¬ inW k r j := fun h' => absurd h'.1 (by omega)
    have hcol : (h * n * h⁻¹) i j = (h * n) i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [uw_col_out hhi j hjn j, if_pos rfl, mul_one]
      · intro b _ hb
        rw [uw_col_out hhi j hjn b, if_neg hb, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ j) h'
    rw [hcol, Matrix.mul_apply]
    by_cases hiW : inW k r i
    · have hi1 := hiW.1
      rw [if_neg (fun e => by rw [e] at hi1; omega)]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases haW : inW k r a
      · have ha1 := haW.1
        rw [hnc a j (by omega) (by rw [hmin]; omega), if_neg (fun e => by rw [e] at ha1; omega),
          mul_zero]
      · rw [uw_block hh i a (fun h' => haW h'.2), if_neg (fun e => haW (by rw [← e]; exact hiW)),
          zero_mul]
    · rw [Finset.sum_eq_single i]
      · rw [uw_block hh i i (fun h' => hiW h'.1), if_pos rfl, one_mul,
          hnc i j (by omega) (by rw [hmin]; exact hij)]
      · intro a _ hai
        rw [uw_block hh i a (fun h' => hiW h'.1), if_neg (Ne.symm hai), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ i) h'

def fexp (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then (r : ℤ) - i.val else if i.val ≤ r + k then 0 else (r : ℤ) + k - i.val

lemma fexp_piI (i : Fin (2 * r + k + 1)) : fexp k r (piI k r i) = - fexp k r i := by
  have hi := i.isLt
  have hv := piI_val (k := k) (r := r) i
  simp only [fexp]
  split_ifs at hv ⊢ <;> omega

lemma fexp_inW {i : Fin (2 * r + k + 1)} (hi : inW k r i) : fexp k r i = 0 := by
  obtain ⟨h1, h2⟩ := hi
  simp only [fexp]
  split_ifs <;> omega

lemma fexp_gap {i j : Fin (2 * r + k + 1)} (hij : i.val < j.val) (hW : ¬ (inW k r i ∧ inW k r j)) :
    1 ≤ fexp k r i - fexp k r j := by
  simp only [inW] at hW
  simp only [fexp]
  split_ifs <;> omega

def dS (k r : ℕ) (s : ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  diagonal fun i => ((s : ℂ)) ^ (fexp k r i)

lemma dS_mul_dS_inv {s : ℝ} (hs : s ≠ 0) : dS k r s * dS k r s⁻¹ = 1 := by
  rw [dS, dS, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← mul_zpow, Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs), _root_.one_zpow]

lemma dS_conj_apply (s : ℝ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (dS k r s * g * dS k r s⁻¹) i j = (s : ℂ) ^ (fexp k r i) * g i j * ((s⁻¹ : ℝ) : ℂ) ^ (fexp k r j) := by
  rw [dS, dS, Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma dS_mem_UH {s : ℝ} (hs : s ≠ 0) : dS k r s ∈ UH (Hpk k r) := by
  show (dS k r s)ᴴ * Hpk k r * dS k r s = Hpk k r
  ext i j
  rw [dS, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Hpk_apply]
  split_ifs with h
  · subst h
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    rw [fexp_piI, Pi.star_apply, star_zpow₀, Complex.star_def, Complex.conj_ofReal, _root_.zpow_neg]
    field_simp
  · simp

lemma dS_conj_fix {s : ℝ} (hs : s ≠ 0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (i j : Fin (2 * r + k + 1)) (hg : g i j = if i = j then 1 else 0) :
    (dS k r s * g * dS k r s⁻¹) i j = if i = j then 1 else 0 := by
  rw [dS_conj_apply, hg]
  split_ifs with h
  · subst h
    rw [mul_one, ← mul_zpow, Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs),
      _root_.one_zpow]
  · simp

lemma dS_conj_UW {s : ℝ} (hs : s ≠ 0) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : dS k r s * h * dS k r s⁻¹ = h := by
  ext i j
  by_cases hij : inW k r i ∧ inW k r j
  · rw [dS_conj_apply, fexp_inW hij.1, fexp_inW hij.2, zpow_zero, zpow_zero, one_mul, mul_one]
  · rw [dS_conj_fix hs i j (uw_block hh i j hij), uw_block hh i j hij]

lemma dS_conj_N {s : ℝ} (hs : s ≠ 0) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : dS k r s * n * dS k r s⁻¹ ∈ Nset k r := by
  rw [mem_Nset_iff] at hn ⊢
  exact ⟨mul_mem_UH (mul_mem_UH (dS_mem_UH hs) hn.1) (dS_mem_UH (inv_ne_zero hs)),
    fun i j hj hi => dS_conj_fix hs i j (hn.2 i j hj hi)⟩

lemma dS_conj_S {s : ℝ} (hs : s ≠ 0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Sset k r z) : dS k r s * g * dS k r s⁻¹ ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  have h1 : dS k r s⁻¹ * dS k r s = 1 := by
    have := dS_mul_dS_inv (k := k) (r := r) (inv_ne_zero hs)
    rwa [inv_inv] at this
  have e : dS k r s * (h * m) * dS k r s⁻¹ =
      (dS k r s * h * dS k r s⁻¹) * (dS k r s * m * dS k r s⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (dS k r s⁻¹) (dS k r s), h1, Matrix.one_mul]
  exact ⟨h, hh, _, dS_conj_N hs hm, by rw [e, dS_conj_UW hs hh]⟩

lemma dS_inv_eq {s : ℝ} (hs : s ≠ 0) : (dS k r s)⁻¹ = dS k r s⁻¹ :=
  Matrix.inv_eq_right_inv (dS_mul_dS_inv hs)

lemma dS_conj_S_iff {s : ℝ} (hs : s ≠ 0) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    dS k r s * g * (dS k r s)⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z := by
  rw [dS_inv_eq hs]
  have h1 : dS k r s⁻¹ * dS k r s = 1 := by
    have := dS_mul_dS_inv (k := k) (r := r) (inv_ne_zero hs)
    rwa [inv_inv] at this
  constructor
  · intro hg
    have h2 := dS_conj_S (inv_ne_zero hs) hg
    rw [inv_inv] at h2
    have e : dS k r s⁻¹ * (dS k r s * g * dS k r s⁻¹) * dS k r s = g := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    rwa [e] at h2
  · exact dS_conj_S hs

lemma norm_dS_conj_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) (i j) :
    ‖(dS k r s * n * (dS k r s)⁻¹ - 1) i j‖ ≤ s * ‖n i j‖ := by
  have hs := hs0.ne'
  rw [dS_inv_eq hs, Matrix.sub_apply]
  by_cases hfix : n i j = if i = j then 1 else 0
  · rw [dS_conj_fix hs i j hfix, Matrix.one_apply, sub_self, norm_zero]
    positivity
  · have hlt : i.val < j.val := by
      by_contra hle
      exact hfix (n_ut hn i j (by omega))
    have hne : i ≠ j := fun e => by rw [e] at hlt; omega
    have hW : ¬ (inW k r i ∧ inW k r j) := by
      rintro ⟨⟨hi1, -⟩, -, hj2⟩
      exact hfix (((mem_Nset_iff n).mp hn).2 i j hj2 (by omega))
    have hd := fexp_gap hlt hW
    rw [dS_conj_apply, Matrix.one_apply_ne hne, sub_zero, norm_mul, norm_mul, norm_zpow, norm_zpow,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs0.le,
      Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]
    have key : s ^ fexp k r i * s⁻¹ ^ fexp k r j = s ^ (fexp k r i - fexp k r j) := by
      rw [_root_.inv_zpow, ← _root_.zpow_neg, ← zpow_add₀ hs, sub_eq_add_neg]
    have hle : s ^ (fexp k r i - fexp k r j) ≤ s := by
      calc s ^ (fexp k r i - fexp k r j) ≤ s ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hs0 hs1 hd
        _ = s := zpow_one s
    calc s ^ fexp k r i * ‖n i j‖ * s⁻¹ ^ fexp k r j = s ^ (fexp k r i - fexp k r j) * ‖n i j‖ := by
          rw [← key]; ring
      _ ≤ s * ‖n i j‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)

theorem unipotent_radical_contracting : NContract := by
  intro k r z _ n hn ε hε
  have hM : 0 ≤ ∑ i, ∑ j, ‖n i j‖ := by positivity
  have hs0 : 0 < min 1 (ε / (∑ i, ∑ j, ‖n i j‖ + 1)) := lt_min one_pos (div_pos hε (by linarith))
  have hs1 : min 1 (ε / (∑ i, ∑ j, ‖n i j‖ + 1)) ≤ 1 := min_le_left _ _
  refine ⟨dS k r (min 1 (ε / (∑ i, ∑ j, ‖n i j‖ + 1))),
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse (dS_mul_dS_inv hs0.ne')),
    fun g => dS_conj_S_iff hs0.ne' g, fun i j => ?_⟩
  have hentry : ‖n i j‖ ≤ ∑ i, ∑ j, ‖n i j‖ :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (n i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖n i j‖)
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
  calc ‖(dS k r _ * n * (dS k r _)⁻¹ - 1) i j‖ ≤ _ * ‖n i j‖ := norm_dS_conj_le hs0 hs1 hn i j
    _ ≤ (ε / (∑ i, ∑ j, ‖n i j‖ + 1)) * ∑ i, ∑ j, ‖n i j‖ :=
        mul_le_mul (min_le_right _ _) hentry (norm_nonneg _) (div_pos hε (by linarith)).le
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

end PI.QuotSetU.UnitaryGroupMassFormula.SW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
section
open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.UWC

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW

variable {k r : ℕ}

def lI (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

def Wp (k r : ℕ) : Finset (Fin (2 * r + k + 1)) :=
  Finset.univ.filter fun i => r ≤ i.val ∧ i.val < r + k

lemma star_dotProduct_Hpk_mulVec_eq_sum_sub (v w : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i, ¬ inW k r i → v i = 0) :
    star w ⬝ᵥ (Hpk k r *ᵥ v) =
      (∑ i ∈ Wp k r, star (w i) * v i) - star (w (lI k r)) * v (lI k r) := by
  have hterm : ∀ i, star (w i) * (Hpk k r *ᵥ v) i =
      (if r ≤ i.val ∧ i.val < r + k then star (w i) * v i else 0) -
        (if lI k r = i then star (w (lI k r)) * v (lI k r) else 0) := by
    intro i
    rw [Hpk_mulVec_apply]
    have hi := i.isLt
    by_cases hW : inW k r i
    · have hp : piI k r i = i := by
        have hW' := hW
        unfold inW at hW'
        unfold piI
        rw [if_pos hW']
      rw [hp]
      unfold inW at hW
      by_cases hl : i.val = r + k
      · have h1 : lI k r = i := Fin.ext hl.symm
        rw [if_neg (by omega), if_pos h1, h1]
        unfold epsI; rw [if_pos hl]; ring
      · have h1 : lI k r ≠ i := fun h => hl (by rw [← h]; rfl)
        rw [if_pos ⟨hW.1, by omega⟩, if_neg h1]
        unfold epsI; rw [if_neg hl]; ring
    · have h0 : v (piI k r i) = 0 := hv _ (piI_not_inW hW)
      have h1 : lI k r ≠ i := fun h => hW (by rw [← h]; unfold inW lI; simp)
      unfold inW at hW
      rw [h0, if_neg (by omega), if_neg h1]; ring
  simp only [dotProduct, Pi.star_apply, hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Wp, Finset.sum_filter]

lemma star_mul_self_eq (x : ℂ) : star x * x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

lemma tz_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    Tz k r z = ‖z (lI k r)‖ ^ 2 - ∑ i ∈ Wp k r, ‖z i‖ ^ 2 := by
  have hv : ∀ i, ¬ inW k r i → z i = 0 := fun i hi => hz i (by unfold inW at hi; omega)
  unfold Tz herm
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub z z hv]
  simp only [star_mul_self_eq]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]
  ring

lemma herm_invariant {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) :
    star (h *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ (h *ᵥ v)) = star u ⬝ᵥ (Hpk k r *ᵥ v) := by
  have hh' : hᴴ * (Hpk k r * h) = Hpk k r := by rw [← Matrix.mul_assoc]; exact hh
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, hh']

lemma norm_epsI (i : Fin (2 * r + k + 1)) : ‖epsI k r i‖ = 1 := by
  unfold epsI; split_ifs <;> simp

lemma norm_bvec_le (j i : Fin (2 * r + k + 1)) : ‖bvec j i‖ ≤ 1 := by
  rw [bvec_apply]; split_ifs <;> simp

lemma norm_H_bvec_le (j i : Fin (2 * r + k + 1)) : ‖(Hpk k r *ᵥ bvec j) i‖ ≤ 1 := by
  rw [Hpk_mulVec_apply, norm_mul, norm_epsI, one_mul]
  exact norm_bvec_le _ _

def Bd (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  ((2 * r + k + 1 : ℕ) : ℝ) +
    (Real.sqrt (∑ i ∈ Wp k r, ‖z i‖ ^ 2) * ((2 * r + k + 1 : ℕ) : ℝ) + ∑ i, ‖z i‖) /
      (‖z (lI k r)‖ - Real.sqrt (∑ i ∈ Wp k r, ‖z i‖ ^ 2))

lemma uw_entry_bound {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (i j : Fin (2 * r + k + 1)) : ‖h i j‖ ≤ Bd k r z := by
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  set A := ∑ i ∈ Wp k r, ‖z i‖ ^ 2 with hAdef
  set a := Real.sqrt A with hadef
  set b := ‖z (lI k r)‖ with hbdef
  set Z := ∑ i, ‖z i‖ with hZdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have haa : a ^ 2 = A := Real.sq_sqrt hA0
  have hTab : Tz k r z = b ^ 2 - a ^ 2 := by rw [tz_eq hz, haa]
  have hab : a < b := by
    by_contra hc
    push Not at hc
    nlinarith [mul_self_le_mul_self hb0 hc]
  have hba : 0 < b - a := by linarith
  have hq0 : 0 ≤ (a * n + Z) / (b - a) := div_nonneg (by positivity) hba.le
  have hBd : Bd k r z = n + (a * n + Z) / (b - a) := rfl
  rw [hBd]
  have hδ : ∀ x : ℂ, (x = if i = j then 1 else 0) → ‖x‖ ≤ n + (a * n + Z) / (b - a) := by
    intro x hx
    have : ‖x‖ ≤ 1 := by rw [hx]; split_ifs <;> simp
    linarith
  by_cases hij : inW k r i ∧ inW k r j
  swap
  · exact hδ _ (uw_block hh i j hij)
  obtain ⟨hiW, hjW⟩ := hij

  set c : Fin (2 * r + k + 1) → ℂ := fun x => h x j with hcdef
  have hc : c = h *ᵥ bvec j := funext fun x => (mulVec_bvec_apply h x j).symm
  have hcW : ∀ x, ¬ inW k r x → c x = 0 := by
    intro x hx
    have hne : x ≠ j := by rintro rfl; exact hx hjW
    have := uw_block hh x j (fun h' => hx h'.1)
    simp only [hcdef, this, if_neg hne]
  have hEA : star c ⬝ᵥ (Hpk k r *ᵥ c) = star (bvec j) ⬝ᵥ (Hpk k r *ᵥ bvec j) := by
    rw [hc]; exact herm_invariant hh.1 _ _
  have hEK : star z ⬝ᵥ (Hpk k r *ᵥ c) = star z ⬝ᵥ (Hpk k r *ᵥ bvec j) := by
    have := herm_invariant hh.1 z (bvec j)
    rw [hh.2.2] at this
    rw [hc]; exact this
  have hnA : ‖star (bvec j) ⬝ᵥ (Hpk k r *ᵥ bvec j)‖ ≤ n := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ x ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))),
        ‖(star (bvec j)) x * (Hpk k r *ᵥ bvec j) x‖ ≤ 1 := by
      intro x _
      rw [norm_mul, Pi.star_apply, norm_star]
      exact mul_le_one₀ (norm_bvec_le _ _) (norm_nonneg _) (norm_H_bvec_le _ _)
    refine (Finset.sum_le_sum this).trans ?_
    simp [hn]
  have hnK : ‖star z ⬝ᵥ (Hpk k r *ᵥ bvec j)‖ ≤ Z := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, Pi.star_apply, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_H_bvec_le _ _)
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub c c hcW] at hEA
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub c z hcW] at hEK
  set X2 := ∑ x ∈ Wp k r, ‖c x‖ ^ 2 with hX2
  set Y := ‖c (lI k r)‖ with hY
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hX20 : 0 ≤ X2 := Finset.sum_nonneg fun _ _ => sq_nonneg _

  have h1 : X2 - Y ^ 2 ≤ n := by
    have e := congrArg Complex.re hEA
    simp only [star_mul_self_eq] at e
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re] at e
    rw [e]
    exact (Complex.re_le_norm _).trans hnA

  have h2 : b * Y ≤ (∑ x ∈ Wp k r, ‖z x‖ * ‖c x‖) + Z := by
    have e : star (z (lI k r)) * c (lI k r) =
        (∑ x ∈ Wp k r, star (z x) * c x) - star z ⬝ᵥ (Hpk k r *ᵥ bvec j) := by
      rw [← hEK]; ring
    have e2 := congrArg norm e
    rw [norm_mul, norm_star] at e2
    rw [hbdef, hY, e2]
    refine (norm_sub_le _ _).trans (add_le_add ?_ hnK)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, norm_star]
  have hCS : (∑ x ∈ Wp k r, ‖z x‖ * ‖c x‖) ≤ a * Real.sqrt X2 :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hsX : Real.sqrt X2 ≤ n + Y := by
    have : X2 ≤ (n + Y) ^ 2 := by nlinarith
    calc Real.sqrt X2 ≤ Real.sqrt ((n + Y) ^ 2) := Real.sqrt_le_sqrt this
      _ = n + Y := Real.sqrt_sq (by linarith)
  have hYb : Y ≤ (a * n + Z) / (b - a) := by
    rw [le_div_iff₀ hba]
    nlinarith
  by_cases hil : i = lI k r
  · have : ‖h i j‖ = Y := by rw [hY, hil]
    rw [this]; linarith
  · have hiWp : i ∈ Wp k r := by
      unfold Wp inW at *
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hiW.1, ?_⟩
      rcases Nat.lt_or_ge i.val (r + k) with h' | h'
      · exact h'
      · exact absurd (Fin.ext (by simp [lI]; omega)) hil
    have hci : ‖c i‖ ^ 2 ≤ X2 :=
      Finset.single_le_sum (f := fun x => ‖c x‖ ^ 2) (fun _ _ => sq_nonneg _) hiWp
    have hci' : ‖c i‖ ≤ n + Y := by
      have h0 : 0 ≤ ‖c i‖ := norm_nonneg _
      nlinarith
    have : ‖h i j‖ = ‖c i‖ := rfl
    rw [this]; linarith

end PI.QuotSetU.UnitaryGroupMassFormula.UWC

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.UWC

theorem unitary_weyl_compact : UWCompact := by
  intro k r z hz hT
  have hcont : ∀ v : Fin (2 * r + k + 1) → ℂ,
      Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g *ᵥ v :=
    fun v => Continuous.matrix_mulVec continuous_id continuous_const
  have hcl : IsClosed (UWset k r z) := by
    have e : UWset k r z = UH (Hpk k r) ∩ ((⋂ a : Fin r,
        ({g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g | g *ᵥ z = z}) := by
      ext g
      simp only [UWset, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [e]
    refine (unitary_hermitian_group k r).1.inter (IsClosed.inter (isClosed_iInter fun a => ?_) ?_)
    · exact (isClosed_eq (hcont _) continuous_const).inter (isClosed_eq (hcont _) continuous_const)
    · exact isClosed_eq (hcont _) continuous_const
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Metric.closedBall (0 : ℂ) (Bd k r z)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset hcl ?_
  intro g hg i _ j _
  simpa using uw_entry_bound hz hT hg i j

end PI.QuotSetU.UnitaryGroupMassFormula

end
end

