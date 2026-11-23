module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0008

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamImgApply
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

structure LamGeo {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) : Prop where
  U1 : ∀ j j' : Fin X.F.J, ∀ x ∈ X.toLate (j.val : ℤ), ∀ x' ∈ X.toLate (j'.val : ℤ), posOf n' x = posOf n' x' →
    j = j' ∧ x = x'
  U2 : ∀ j j' : Fin X.F.J, ∀ x ∈ X.F.letters (j.val : ℤ), X.F.IsW (j.val : ℤ) x → ∀ x' ∈ X.F.letters (j'.val : ℤ),
    X.F.IsW (j'.val : ℤ) x' → posOf n' x = posOf n' x' → j = j' ∧ x = x'
  LK : ∀ j j' : Fin X.F.J, ∀ x ∈ X.F.letters (j.val : ℤ), X.F.IsW (j.val : ℤ) x → ∀ x' ∈ X.toLate (j'.val : ℤ),
    posOf n' x = posOf n' x' → (∃ i < r, x' = X.F.fr (j'.val : ℤ) i) ∧
      X.Pz p K (j.val : ℤ) x = X.Pz p K (j'.val : ℤ) x' * X.Qc p K (j'.val : ℤ)
  EX : ∀ t ∈ X.F.TT, ∃ j : Fin X.F.J, ∃ x ∈ X.toLate (j.val : ℤ), posOf n' x = t

def RestLamGeo (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    LamGeo X p K

def RestLamTau : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K →
    ∀ (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) (i : Fin r),
      X.bfam p K la e (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val) = e j i

theorem lam_digit {P la la' A A' : ℕ} (h1 : la < P) (h2 : la' < P) (h : la + P * A = la' + P * A') :
    la = la' ∧ A = A' := by
  have hP : 0 < P := lt_of_le_of_lt (Nat.zero_le _) h1
  have e1 : (la + P * A) % P = la := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have e2 : (la' + P * A') % P = la' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  have hla : la = la' := by rw [← e1, ← e2, h]
  refine ⟨hla, ?_⟩
  subst hla
  have h3 : P * A = P * A' := by omega
  exact Nat.eq_of_mul_eq_mul_left hP h3

section Eval

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

theorem lam_img_apply (j : Fin X.F.J) (m : ℤ × Fin (r + K) →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) (t : Fin n') (c : Fin (r + K)) :
    imgMon (X.lamG K j) (X.lamE p K j) m (t, c) =
      ∑ x ∈ X.F.letters (j.val : ℤ), if posOf n' x = t then X.Pz p K (j.val : ℤ) x * m (x, c) else 0 := by
  classical
  unfold imgMon
  rw [Finsupp.sum_apply]
  have hsub : m.support ⊆ X.F.letters (j.val : ℤ) ×ˢ (Finset.univ : Finset (Fin (r + K))) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨(hm v (Finsupp.mem_support_iff.mp hv)).1, Finset.mem_univ _⟩
  rw [Finsupp.sum_of_support_subset m hsub _ (by intro v _; simp), Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finsupp.single_apply, Dat.lamG, Prod.mk.injEq]
  by_cases h : posOf n' x = t
  · simp [h, Dat.lamE, Dat.Pz]
  · simp [h]


open Classical in
def segmentWeightExponent (m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ)) (t : Fin n') (c : Fin (r + K)) : ℕ :=
  ∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
    if posOf n' x = t then m j (x, c) else 0

theorem lam_eval (hG : LamGeo X p K) (m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ))
    (hm : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) (j0 : Fin X.F.J) (x0 : ℤ) (hx0 : x0 ∈ X.toLate (j0.val : ℤ))
    (c : Fin (r + K)) :
    (∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (posOf n' x0, c) =
      X.Pz p K (j0.val : ℤ) x0 * (m j0 (x0, c) + X.Qc p K (j0.val : ℤ) * segmentWeightExponent X K m (posOf n' x0) c) := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_congr rfl fun j _ => lam_img_apply X p K j (m j) (hm j) _ c]
  have hsplit : ∀ j : Fin X.F.J,
      (∑ x ∈ X.F.letters (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      (∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
        if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) +
      ∑ x ∈ X.toLate (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0 := by
    intro j
    unfold Dat.toLate
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
  have hlate : (∑ j : Fin X.F.J, ∑ x ∈ X.toLate (j.val : ℤ),
      if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      X.Pz p K (j0.val : ℤ) x0 * m j0 (x0, c) := by
    rw [Finset.sum_eq_single j0]
    · rw [Finset.sum_eq_single x0]
      · rw [if_pos rfl]
      · intro x hx hne
        rw [if_neg]
        intro h
        exact hne (hG.U1 j0 j0 x hx x0 hx0 h).2
      · intro h; exact absurd hx0 h
    · intro j _ hne
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [if_neg]
      intro h
      exact hne (hG.U1 j j0 x hx x0 hx0 h).1
    · intro h; exact absurd (Finset.mem_univ _) h
  have hW : (∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
      if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      X.Pz p K (j0.val : ℤ) x0 * (X.Qc p K (j0.val : ℤ) * segmentWeightExponent X K m (posOf n' x0) c) := by
    unfold segmentWeightExponent
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
    split_ifs with h
    · rw [(hG.LK j j0 x hxl hxW x0 hx0 h).2]; ring
    · simp
  rw [hlate, hW]; ring

end Eval

theorem restLamInj_of (C₀ : ℝ) (hGeo : RestLamGeo C₀) (hTau : RestLamTau) : RestLamInj C₀ := by
  intro p n' r K _ _ _ X hX hLa hk la hla e he la' hla' e' he' m m' hm hm' heq
  classical
  have hG := hGeo p n' r K X hX hLa hk
  have hok : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ) := fun j => (hm j).1
  have hok' : ∀ j v, m' j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ) := fun j => (hm' j).1
  have hlaS := Fintype.mem_piFinset.mp hla
  have hlaS' := Fintype.mem_piFinset.mp hla'

  have hdec : ∀ (j0 : Fin X.F.J) (x0 : ℤ), x0 ∈ X.toLate (j0.val : ℤ) → ∀ c : Fin (r + K),
      la (posOf n' x0) c = la' (posOf n' x0) c ∧ m j0 (x0, c) = m' j0 (x0, c) ∧
        segmentWeightExponent X K m (posOf n' x0) c = segmentWeightExponent X K m' (posOf n' x0) c := by
    intro j0 x0 hx0 c
    have h1 := congrArg (fun f => f (posOf n' x0, c)) heq
    simp only [Finsupp.add_apply] at h1
    rw [lam_eval X p K hG m hok j0 x0 hx0 c, lam_eval X p K hG m' hok' j0 x0 hx0 c] at h1
    have hl1 : la (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0 :=
      ((Finset.mem_filter.mp (hlaS (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c
    have hl2 : la' (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0 :=
      ((Finset.mem_filter.mp (hlaS' (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c
    obtain ⟨g1, g2⟩ := lam_digit hl1 hl2 h1
    refine ⟨g1, ?_⟩
    by_cases hfc : (∃ i < r, x0 = X.F.fr (j0.val : ℤ) i) ∧ c.val < r
    · obtain ⟨⟨i, hi, rfl⟩, hc⟩ := hfc
      have hcc : c = Fin.castAdd K ⟨c.val, hc⟩ := Fin.ext rfl
      have a1 : m j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ) := by
        rw [hcc]; exact (hm j0).2.2 i hi ⟨c.val, hc⟩
      have a2 : m' j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ) := by
        rw [hcc]; exact (hm' j0).2.2 i hi ⟨c.val, hc⟩
      exact lam_digit a1 a2 g2
    · have hw0 : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j v, mm j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) →
          segmentWeightExponent X K mm (posOf n' x0) c = 0 := by
        intro mm hmm
        unfold segmentWeightExponent
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x hx => ?_
        obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
        split_ifs with h
        · by_contra hne
          apply hfc
          refine ⟨(hG.LK j j0 x hxl hxW x0 hx0 h).1, ?_⟩
          by_contra hc
          exact (hmm j (x, c) hne).2 (not_lt.mp hc) hxW
        · rfl
      rw [hw0 m hok, hw0 m' hok'] at g2 ⊢
      simp only [mul_zero, add_zero] at g2
      exact ⟨g2, rfl⟩
  have hlaeq : la = la' := by
    funext t c
    by_cases ht : t ∈ X.F.TT
    · obtain ⟨j0, x0, hx0, rfl⟩ := hG.EX t ht
      exact (hdec j0 x0 hx0 c).1
    · have ha : X.a' p K t = 0 := by
        unfold Dat.a' Dat.d
        rw [if_neg ht]; simp
      have b1 := (Finset.mem_filter.mp (hlaS t)).2.1
      have b2 := (Finset.mem_filter.mp (hlaS' t)).2.1
      rw [ha] at b1 b2
      have c1 := Finset.single_le_sum (f := fun c => la t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      have c2 := Finset.single_le_sum (f := fun c => la' t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
  have hmeq : m = m' := by
    funext j
    ext v
    obtain ⟨x, c⟩ := v
    by_cases hv : (x, c) ∈ okVars X.F K (j.val : ℤ)
    · by_cases hW : X.F.IsW (j.val : ℤ) x
      · have hTT : posOf n' x ∈ X.F.TT := by
          have := hv.1
          unfold Frames.letters at this
          exact (Finset.mem_filter.mp this).2
        obtain ⟨j0, x0, hx0, hpos⟩ := hG.EX _ hTT
        have h3 := (hdec j0 x0 hx0 c).2.2
        have hwv : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), segmentWeightExponent X K mm (posOf n' x0) c = mm j (x, c) := by
          intro mm
          unfold segmentWeightExponent
          rw [Finset.sum_eq_single j]
          · rw [Finset.sum_eq_single x]
            · rw [if_pos hpos.symm]
            · intro y hy hne
              obtain ⟨hyl, hyW⟩ := Finset.mem_filter.mp hy
              rw [if_neg]
              intro h
              exact hne (hG.U2 j j y hyl hyW x hv.1 hW (h.trans hpos)).2
            · intro h; exact absurd (Finset.mem_filter.mpr ⟨hv.1, hW⟩) h
          · intro j' _ hne
            refine Finset.sum_eq_zero fun y hy => ?_
            obtain ⟨hyl, hyW⟩ := Finset.mem_filter.mp hy
            rw [if_neg]
            intro h
            exact hne (hG.U2 j' j y hyl hyW x hv.1 hW (h.trans hpos)).1
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hwv m, hwv m'] at h3
        exact h3
      · exact (hdec j x (Finset.mem_filter.mpr ⟨hv.1, hW⟩) c).2.1
    · have z1 : m j (x, c) = 0 := by
        by_contra h; exact hv (hok j _ h)
      have z2 : m' j (x, c) = 0 := by
        by_contra h; exact hv (hok' j _ h)
      rw [z1, z2]
  refine ⟨⟨hlaeq, ?_⟩, hmeq⟩
  funext j i
  have d1 := (hm j).2.1 (X.F.fr (j.val : ℤ) i.val)
  have d2 := (hm' j).2.1 (X.F.fr (j.val : ℤ) i.val)
  rw [hTau p n' r K X hX] at d1 d2
  rw [← d1, ← d2, hmeq]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ReflectionMemGlevCastSucc
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def OldestLetterInSegment : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    X.F.oldest j x ∈ X.F.letters j ∧ (¬ X.F.IsW j (X.F.oldest j x) → X.F.oldest j x ∈ X.F.LLset j)

def OrderNumericBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j, ∀ x ∈ X.toLate j,
      ((p ^ X.Rj p K j : ℕ) : ℝ) * X.oc p K j x + Dat.k (r := r) K * ((p ^ X.Rj p K j : ℕ) : ℝ) ≤ X.o p K j x

section Num

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem frame_zero_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih => intro h; exact (ih (by omega)).trans (hV.2.2.1 j i h).le

theorem reflection_mem_Glev_castSucc {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr (j - 1) 0 ∈ F.letters j := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := frame_zero_le hV (j - 1) (r - 1) (by omega)
  have h2 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h2
  have h3 := frame_zero_le hV j (r - 1) (by omega)
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨le_rfl, by omega⟩, (hV.2.2.2.2.1 (j - 1) 0 hr).1⟩

theorem mem_letters_bounds {F : Frames n' r} {j x : ℤ} (hx : x ∈ F.letters j) :
    F.fr (j - 1) 0 ≤ x ∧ x ≤ F.fr j (r - 1) ∧ posOf n' x ∈ F.TT := by
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

structure Basics (X : Dat n' r) (p K : ℕ) : Prop where
  p1 : (1 : ℝ) < p
  Ns1 : (1 : ℝ) ≤ X.Ns
  k5 : (5 : ℝ) ≤ Dat.k (r := r) K
  rk : (r : ℝ) ≤ Dat.k (r := r) K
  Q1 : (1 : ℝ) ≤ X.Q
  Y1 : (1 : ℝ) ≤ X.Y

theorem basics (hX : X.Hyp p K) : Basics X p K := by
  have hV := hX.valid
  have hw := reflection_mem_Glev_castSucc hV 0
  have hp : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hc : 1 ≤ (X.F.letters 0).card := Finset.card_pos.mpr ⟨_, hw⟩
  have hNs : 1 ≤ X.Ns := hc.trans (hX.card 0)
  have hK := hX.NsK
  have hr := hX.r2
  have hQ := hX.twist 0 _ hw
  refine ⟨by linarith, by exact_mod_cast hNs, ?_, ?_, ?_, hX.Y1⟩
  · unfold Dat.k
    exact_mod_cast (by omega : 5 ≤ r + K)
  · unfold Dat.k
    exact_mod_cast (by omega : r ≤ r + K)
  · exact le_trans (one_le_pow₀ (by linarith : (1 : ℝ) ≤ p)) hQ

def Tj (X : Dat n' r) (p K : ℕ) (j : ℤ) : ℝ :=
  X.a / (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))

theorem den_pos (hX : X.Hyp p K) (j : ℤ) :
    0 < 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by
  have B := basics hX
  have h1 : (0 : ℝ) < p := by linarith [B.p1]
  have h2 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have h3 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
  have h4 : (0 : ℝ) < X.Ns := by linarith [B.Ns1]
  positivity

theorem Tj_ge (hX : X.Hyp p K) (j : ℤ) : 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) ≤ Tj X p K j := by
  have b := basics hX
  have hd := den_pos hX j
  have hw := reflection_mem_Glev_castSucc hX.valid j
  have hQ := hX.twist j _ hw
  have P3 := hX.P3
  have hY : 0 ≤ X.Y := by linarith [b.Y1]
  have hp0 : (0 : ℝ) ≤ p := by linarith [b.p1]
  have hdQ : (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) ≤ X.Q ^ 2 := hQ.trans (by nlinarith [b.Q1])
  have hk : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hc : 0 ≤ (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hp0 hY) (sq_nonneg _)) (Nat.cast_nonneg _))
      (by positivity)
  have hm := mul_le_mul_of_nonneg_left hdQ hc
  unfold Tj
  rw [le_div_iff₀ hd, hk]
  calc 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))
        = 32 * ((p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := by ring
    _ ≤ 32 * ((p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * X.Q ^ 2) := by linarith
    _ = 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by ring
    _ ≤ X.a := P3

theorem pow_Rj_le (hX : X.Hyp p K) (j : ℤ) : ((p : ℝ) ^ X.Rj p K j) ≤ Tj X p K j := by
  have B := basics hX
  have hT := Tj_ge hX j
  have hT1 : (1 : ℝ) ≤ Tj X p K j := by
    have h0 : (0 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar := by positivity
    nlinarith [B.p1]
  have hfl : ⌊Tj X p K j⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊Tj X p K j⌋₊ := Nat.le_floor (by simpa using hT1)
    omega
  have h1 : p ^ X.Rj p K j ≤ ⌊Tj X p K j⌋₊ := Nat.pow_log_le_self p hfl
  have h2 : ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) ≤ Tj X p K j := Nat.floor_le (by linarith)
  have h3 : ((p ^ X.Rj p K j : ℕ) : ℝ) ≤ ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem lt_pow_Rj (hX : X.Hyp p K) (j : ℤ) : Tj X p K j < (p : ℝ) ^ (X.Rj p K j + 1) := by
  have h1 : ⌊Tj X p K j⌋₊ < p ^ (X.Rj p K j + 1) := Nat.lt_pow_succ_log_self hX.prime.one_lt _
  have h2 : Tj X p K j < (⌊Tj X p K j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) + 1 ≤ ((p ^ (X.Rj p K j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem power_exceeds_max_multiplicity (C₀ : ℝ) : PowerExceedsMaxMultiplicity C₀ := by
  intro p n' r K _ _ _ X hX _ _ j
  have B := basics hX
  have h1 := Tj_ge hX j
  have h2 := lt_pow_Rj hX j
  rw [pow_succ] at h2
  have hp : (0 : ℝ) < p := by linarith [B.p1]
  have hE : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
  have h3 : 4 * ((X.E₀ : ℝ) + X.mStar + 1) < (p : ℝ) ^ X.Rj p K j := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_right hcon hp.le
    nlinarith
  have h4 : (X.mStar : ℝ) < ((p ^ X.Rj p K j : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast h4

theorem l42b (hX : X.Hyp p K) (j y : ℤ) (hy : y ∈ X.F.letters j) :
    8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤ X.a := by
  have b := basics hX
  have hd := den_pos hX j
  have hy' := mem_letters_bounds hy
  have hdist : X.F.dist j y ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    exact Int.toNat_le_toNat (by linarith [hy'.1])
  have hp1 : (1 : ℝ) ≤ p := b.p1.le
  have hpow : (p : ℝ) ^ X.F.dist j y ≤ (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := pow_le_pow_right₀ hp1 hdist
  have hR := pow_Rj_le hX j
  have hY : 0 ≤ X.Y := by linarith [b.Y1]
  have hTa : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j = X.a := by
    unfold Tj
    exact mul_div_cancel₀ _ hd.ne'
  have hc0 : 0 ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hY) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul hpow hR (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)) hc0
  rw [pow_add]
  calc 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j y * (p : ℝ) ^ X.Rj p K j)
      ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j) := hm
    _ = X.a := by rw [← hTa]; ring

end Num

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

