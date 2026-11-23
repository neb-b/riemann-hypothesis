module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0011

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.OldestLetterInSegment
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Rows

variable {n' r : ℕ} [NeZero n'] [NeZero r]


open Classical in
def evL (F : Frames n' r) (j x : ℤ) : List ℤ := ((F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)

theorem row_eq (X : Dat n' r) (j x : ℤ) (i : Fin r) :
    X.row j x i = (evL X.F j x).getD ((evL X.F j x).length - r + i.val) 0 := rfl

theorem oldest_eq (F : Frames n' r) (j x : ℤ) : F.oldest j x = (evL F j x).getD ((evL F j x).length - r) 0 := rfl

theorem mem_evL (F : Frames n' r) (j x z : ℤ) : z ∈ evL F j x ↔ z ∈ F.letters j ∧ Even z ∧ z < x := by
  classical
  unfold evL
  rw [Finset.mem_sort, Finset.mem_filter]

theorem bk_fr_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) :
    ∀ i', i < i' → i' < r → F.fr j i < F.fr j i' := by
  intro i' hi hi'
  induction i', hi using Nat.le_induction with
  | base => exact hV.2.2.1 j i hi'
  | succ k hik ih =>
    exact lt_trans (ih (by omega)) (hV.2.2.1 j k hi')

theorem bk_fr_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i i' : ℕ) (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  rcases Nat.lt_or_eq_of_le h with h1 | h1
  · exact le_of_lt (bk_fr_lt hV j i i' h1 h')
  · rw [h1]

theorem r_le_length {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ F.letters j)
    (hW : ¬ F.IsW j x) : r ≤ (evL F j x).length := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hW' : F.fr (j - 1) (r - 1) < x := lt_of_not_ge hW
  have h4 : F.fr (j - 1) (r - 1) < F.fr j 0 := by
    have := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at this
  have hj0 : F.fr j 0 ≤ F.fr j (r - 1) := bk_fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)
  have hsub : (Finset.range r).image (fun i => F.fr (j - 1) i) ⊆
      (F.letters j).filter (fun z => Even z ∧ z < x) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    have hle : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1) := bk_fr_le hV (j - 1) i (r - 1) (by omega) (by omega)
    have hge : F.fr (j - 1) 0 ≤ F.fr (j - 1) i := bk_fr_le hV (j - 1) 0 i (Nat.zero_le _) hi
    have h5 := hV.2.2.2.2.1 (j - 1) i hi
    rw [Finset.mem_filter]
    refine ⟨?_, h5.2, lt_of_le_of_lt hle hW'⟩
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hge, by linarith⟩, h5.1⟩
  have hinj : Set.InjOn (fun i => F.fr (j - 1) i) (Finset.range r : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · exact absurd hab (ne_of_lt (bk_fr_lt hV (j - 1) a b h1 hb))
    · exact absurd hab (ne_of_gt (bk_fr_lt hV (j - 1) b a h1 ha))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hc
  unfold evL
  rw [Finset.length_sort]
  exact hc

theorem evL_nodup (F : Frames n' r) (j x : ℤ) : (evL F j x).Nodup := by
  classical
  unfold evL
  exact Finset.sort_nodup _ _

theorem evL_mono (F : Frames n' r) (j x : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < (evL F j x).length) :
    (evL F j x)[a]'(lt_of_le_of_lt hab hb) ≤ (evL F j x)[b]'hb := by
  have hp : (evL F j x).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  rcases Nat.lt_or_eq_of_le hab with h1 | h1
  · exact List.pairwise_iff_getElem.mp hp a b _ hb h1
  · subst h1
    exact le_refl _

end Rows

theorem late_row_injective : LateIndexInjective := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hlen := r_le_length hX.valid j x hx.1 hx.2
  have hidx : ∀ i : Fin r, (evL X.F j x).length - r + i.val < (evL X.F j x).length := by
    intro i
    have := i.isLt
    omega
  have hrow : ∀ i : Fin r, X.row j x i = (evL X.F j x)[(evL X.F j x).length - r + i.val]'(hidx i) := by
    intro i
    rw [row_eq, List.getD_eq_getElem]
  refine ⟨?_, ?_⟩
  · intro a b h
    rw [hrow, hrow] at h
    have := (evL_nodup X.F j x).getElem_inj_iff.mp h
    exact Fin.ext (by omega)
  · intro i
    rw [hrow]
    exact (mem_evL X.F j x _).mp (List.getElem_mem _)

theorem oldest_letter_in_segment : OldestLetterInSegment := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hV := hX.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hlen := r_le_length hV j x hx.1 hx.2
  have hk : (evL X.F j x).length - r < (evL X.F j x).length := by omega
  have hold : X.F.oldest j x = (evL X.F j x)[(evL X.F j x).length - r]'hk := by
    rw [oldest_eq, List.getD_eq_getElem]
  have hmem := (mem_evL X.F j x _).mp (List.getElem_mem hk)
  rw [hold]
  refine ⟨hmem.1, ?_⟩
  intro hnW
  have hlet := hmem.1
  unfold Frames.letters at hlet
  rw [Finset.mem_filter, Finset.mem_Icc] at hlet
  unfold Frames.LLset
  rw [Finset.mem_filter, Finset.mem_Ioo]
  refine ⟨⟨lt_of_not_ge hnW, ?_⟩, hlet.2⟩
  by_contra hge
  push_neg at hge
  have frame : ∀ y ∈ X.F.letters j, X.F.fr j 0 ≤ y → ∃ i < r, X.F.fr j i = y := by
    intro y hy hy0
    unfold Frames.letters at hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    by_contra hne
    push_neg at hne
    have hall : ∀ i, i < r → X.F.fr j i < y := by
      intro i
      induction i with
      | zero => intro h0; exact lt_of_le_of_ne hy0 (hne 0 h0)
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        by_contra h2
        push_neg at h2
        rcases lt_or_eq_of_le h2 with h3 | h3
        · exact hV.2.2.2.2.2.1 j m y hm h1 h3 hy.2
        · exact hne (m + 1) hm h3.symm
    have := hall (r - 1) (by omega)
    linarith [hy.1.2]
  set l := evL X.F j x with hl
  set k := l.length - r with hkdef
  have hdl : (l.drop k).length = r := by
    rw [List.length_drop]
    omega
  have hnd : (l.drop k).Nodup := (evL_nodup X.F j x).sublist (List.drop_sublist _ _)
  have hxn : x ∉ (l.drop k).toFinset := by
    intro h
    rw [List.mem_toFinset] at h
    have := ((mem_evL X.F j x x).mp (List.mem_of_mem_drop h)).2.2
    exact lt_irrefl _ this
  have hsub : insert x (l.drop k).toFinset ⊆ (Finset.range r).image (fun i => X.F.fr j i) := by
    intro y hy
    rw [Finset.mem_image]
    rw [Finset.mem_insert, List.mem_toFinset] at hy
    rcases hy with rfl | hy
    · obtain ⟨i, hi, he⟩ := frame y hx.1 (le_trans hge (le_of_lt hmem.2.2))
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
    · have hyl := (mem_evL X.F j x y).mp (List.mem_of_mem_drop hy)
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hy
      have hm' : k + m < l.length := by
        rw [hdl] at hm
        omega
      have hge2 : l[k]'hk ≤ (l.drop k)[m] := by
        rw [List.getElem_drop]
        exact evL_mono X.F j x (Nat.le_add_right k m) hm'
      obtain ⟨i, hi, he⟩ := frame _ hyl.1 (le_trans hge hge2)
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxn, List.toFinset_card_of_nodup hnd, hdl] at hc
  have hc2 := Finset.card_image_le (s := Finset.range r) (f := fun i => X.F.fr j i)
  rw [Finset.card_range] at hc2
  omega

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ProdIccOneEqProdRange
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

variable {N r K : ℕ}

theorem entry_eq_of_lt (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s m : ℕ)
    (hs : s < N + 1) (hm : m < r + K) :
    BranchingDimensions.Letters.ent (D := toL r K LL B) μ s m = μ ⟨s, hs⟩ ⟨m, hm⟩ :=
  dif_pos (⟨hs, hm⟩ : s < N + 1 ∧ m < r + K)

theorem entry_eq_zero_of_ge (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s m : ℕ)
    (hm : ¬ m < r + K) : BranchingDimensions.Letters.ent (D := toL r K LL B) μ s m = 0 :=
  dif_neg (fun h : s < N + 1 ∧ m < r + K => hm h.2)

theorem sum_Icc_one_eq_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ m ∈ Finset.range n, f (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem prod_Icc_one_eq_prod_range {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, f i = ∏ m ∈ Finset.range n, f (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem prod_fin_ite_lt_eq {M : Type} [CommMonoid M] (n j : ℕ) (hj : j ≤ n) (h : ℕ → M) :
    ∏ i : Fin n, (if i.val < j then h i.val else 1) = ∏ i ∈ Finset.range j, h i := by
  rw [Fin.prod_univ_eq_prod_range (fun m => if m < j then h m else 1) n]
  rw [← Finset.prod_subset (Finset.range_subset_range.mpr hj)]
  · refine Finset.prod_congr rfl fun m hm => ?_
    rw [if_pos (Finset.mem_range.mp hm)]
  · intro m _ hm
    rw [if_neg (by simpa using hm)]

theorem sum_fin_ite_lt_eq {M : Type} [AddCommMonoid M] (n j : ℕ) (hj : j ≤ n) (h : ℕ → M) :
    ∑ i : Fin n, (if i.val < j then h i.val else 0) = ∑ i ∈ Finset.range j, h i := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < j then h m else 0) n]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hj)]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos (Finset.mem_range.mp hm)]
  · intro m _ hm
    rw [if_neg (by simpa using hm)]

theorem beta_eq_sum_thresholds (LL : Letters (Fin N)) (B : Fin N → ℕ) (n0 : ℕ) (hn : n0 ≤ N) :
    ∑ i ∈ Finset.Icc 1 n0, (toL r K LL B).B i = beA n0 B := by
  unfold beA
  rw [sum_Icc_one_eq_sum_range, ← sum_fin_ite_lt_eq N n0 hn (fun m => (toL r K LL B).B (m + 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.val < n0
  · rw [if_pos hi, if_pos hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]
    congr 1
  · rw [if_neg hi, if_neg hi]

theorem rank_eq_prod_choose (LL : Letters (Fin N)) (B : Fin N → ℕ) (n0 : ℕ) (hn : n0 ≤ N) :
    ∏ i ∈ Finset.Icc 1 n0, ((toL r K LL B).B i + (r + K) - 1).choose (r + K - 1) = rkA r K n0 B := by
  unfold rkA
  rw [prod_Icc_one_eq_prod_range, ← prod_fin_ite_lt_eq N n0 hn (fun m => ((toL r K LL B).B (m + 1) + (r + K) - 1).choose (r + K - 1))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i.val < n0
  · rw [if_pos hi, if_pos hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]
    congr 3
  · rw [if_neg hi, if_neg hi]

theorem entry_weight_eq_sum (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s : ℕ) (hs : s < N + 1) :
    BranchingDimensions.wsize (r + K) (BranchingDimensions.Letters.ent (D := toL r K LL B) μ s) = ∑ m : Fin (r + K), μ ⟨s, hs⟩ m := by
  unfold BranchingDimensions.wsize
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun m _ => entry_eq_of_lt LL B μ s m.val hs m.2

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem toL_IsPATH (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) : (toL r K LL B).IsPATH P.mu := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    by_cases hm : m < r + K
    · rw [entry_eq_of_lt LL B P.mu 0 m (by omega) hm]
      have h0 : (⟨0, by omega⟩ : Fin (N + 1)) = 0 := rfl
      rw [h0, P.zero]; rfl
    · exact entry_eq_zero_of_ge LL B P.mu 0 m hm
  · intro i hi m hm
    have hi' : i ≤ N := hi
    have hm' : m + 1 < r + K := hm
    rw [entry_eq_of_lt LL B P.mu i (m + 1) (by omega) hm', entry_eq_of_lt LL B P.mu i m (by omega) (by omega)]
    exact P.dom _ (by rw [Fin.le_def]; simp)
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have h2' : i0 + 1 ≤ N := h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, h2'⟩] at hv
    have hs := step_vec P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have hm' : m < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']
      exact hs.1 ⟨m, hm'⟩
    · have hm' : m + 1 < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) (by omega), entry_eq_of_lt LL B P.mu (i0 + 1) (m + 1) (by omega) hm']
      exact hs.2.1 ⟨m, by omega⟩ hm'
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have h2' : i0 + 1 ≤ N := h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, h2'⟩] at hv
    have hs := step_cov P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have hm' : m < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']
      exact hs.1 ⟨m, hm'⟩
    · have hm' : m + 1 < r + K := hm
      rw [entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) (by omega), entry_eq_of_lt LL B P.mu i0 (m + 1) (by omega) hm']
      exact hs.2.1 ⟨m, by omega⟩ hm'
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    rw [hn0] at h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, by omega⟩] at hv
    have hs := step_vec P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]
    show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _
    rw [entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]
    have := hs.2.2
    rw [hP.degs ⟨i0, by omega⟩ (by simp only; omega)] at this
    exact this
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    rw [hn0] at h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, by omega⟩] at hv
    have hs := step_cov P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]
    show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _
    rw [entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]
    have := hs.2.2
    rw [hP.degs ⟨i0, by omega⟩ (by simp only; omega)] at this
    exact this
  · intro i' h1 h2 m hm
    have h2' : i' ≤ r := h2
    rw [hn0, entry_eq_of_lt LL B P.mu (n0 + i') m (by omega) (by omega)]
    have := hP.head ⟨n0 + i' - 1, by omega⟩ ⟨m, by omega⟩ (by simp only; omega) (by simp only; omega)
    have he : (⟨n0 + i' - 1, by omega⟩ : Fin N).succ = (⟨n0 + i', by omega⟩ : Fin (N + 1)) :=
      Fin.ext (by simp; omega)
    rw [he] at this
    rw [this]
    congr 1
    show beA n0 B = ∑ i ∈ Finset.Icc 1 (toL r K LL B).n0, (toL r K LL B).B i
    rw [hn0, beta_eq_sum_thresholds LL B n0 (by omega)]

theorem toL_wt (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (μ : Fin (N + 1) → Fin (r + K) → ℤ)
    (hd : Dominant (pEnd (tanPart μ))) :
    (({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).ncard : ℝ) = BranchingDimensions.Letters.wt (D := toL r K LL B) μ := by
  have h1 := h3 K N (tanPart μ) hd
  rw [← Nat.card_coe_set_eq]
  have h2 : ((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℝ) =
      (((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℚ) : ℝ) := by push_cast; rfl
  refine Eq.trans h2 ?_
  rw [h1]
  unfold BranchingDimensions.Letters.wt BranchingDimensions.weylDim
  push_cast
  rw [Finset.prod_comm, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hka : ∀ x : Fin K, BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N x.val = pEnd (tanPart μ) x := by
    intro x
    unfold BranchingDimensions.Letters.kaRows
    show BranchingDimensions.Letters.ent (D := toL r K LL B) μ N (r + x.val) = _
    rw [entry_eq_of_lt LL B μ N (r + x.val) (by omega) (by have := x.2; omega)]
    rfl
  refine Eq.trans ?_ (prod_fin_ite_lt_eq K j.val j.2.le (fun i =>
    (((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N i : ℤ) : ℝ) - ((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N j.val : ℤ) : ℝ) +
      (((j.val : ℕ) : ℝ) - (i : ℝ))) / (((j.val : ℕ) : ℝ) - (i : ℝ))))
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hij : i < j
  · have hij' : i.val < j.val := hij
    rw [if_pos hij, if_pos hij', hka i, hka j]
    push_cast
    ring
  · have hij' : ¬ i.val < j.val := hij
    rw [if_neg hij, if_neg hij']
    simp

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

