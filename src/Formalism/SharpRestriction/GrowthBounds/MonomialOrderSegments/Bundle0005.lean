module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyBlock

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MlabNotMemYset
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section

variable {K : Type} [Field K]

theorem linMap_eq_sum {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) (Y : MvPolynomial σ K) :
    T Y = ∑ ζ ∈ Y.support, Y.coeff ζ • T (monomial ζ 1) := by
  conv_lhs => rw [Y.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]

end

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

theorem Good.dg {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (f : D.EM → K) :
    D.Good p (Formalism.MainNotions.PlaneGram.dg f Z) := fun ζ hζ => hZ ζ (support_dg_subset f Z hζ)

theorem mlab_notMem_Yset (j : Fin D.J) (m : Fin D.r) (t : D.Tau) : D.mlab t ∉ D.Yset j m := by
  rw [mem_Yset]
  rintro (⟨m', h⟩ | ⟨b, -, h⟩ | ⟨m', -, h⟩) <;> simp [mb, mw, mlab, mtp] at h

end TwistData

section Main

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem cge_Pj_monomial (hD : DVRHyp v p) (D : TwistData K) (hr : 1 ≤ D.r)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (ζ : D.EM) (hζ : D.GoodE p ζ) :
    cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (monomial ζ 1)) := by
  intro ζ'
  by_cases h : ζ' ∈ (Pj (monomial ζ 1)).support
  · have hb : D.SameBlockAlt ζ ζ' := hP1 ζ ζ' h
    have h1 := D.blk_fact hD hr hζ hb
    exact vge_mono v (by linarith) (hP2 ζ hζ ζ')
  · rw [notMem_support_iff.mp h]; exact vge_zero v _

theorem good_Pj (D : TwistData K)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    {Y : MvPolynomial (D.ML × Fin D.r) K} (hY : D.Good p Y) : D.Good p (Pj Y) := by
  rw [linMap_eq_sum Pj Y]
  refine TwistData.Good.sum D _ _ fun ζ hζ => TwistData.Good.smul D ?_ _
  intro ζ' hζ'
  exact TwistData.GoodE.good_exponent_same_block D (hY ζ hζ) (hP1 ζ ζ' hζ')

theorem omega_clauses (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hPj : (∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a))) ∧
      (∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1))) ∧
      (∀ Z (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) (Pj Z)) ∧
      (∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1)) ∧
      (∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ) Z, vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) θ (Pj Z)))
    (gp gm : D.EM → K) (hgp : ∀ ζ, 0 ≤ v (gp ζ)) (hgm : ∀ ζ, 0 ≤ v (gm ζ))
    (hcost : ∀ S : Finset D.ML, (∀ t, D.mlab t ∉ S) → ∀ (θ : ℝ) (Z : MvPolynomial (D.ML × Fin D.r) K),
        vala D.msg S θ Z → vala D.msg S (θ - 12 * D.c) (dg gp Z) ∧ vala D.msg S (θ - 12 * D.c) (dg gm Z)) :
    ((⌈D.Dm p C0 + D.kapD p / 2⌉₊ : ℕ) : ℝ) ≤ D.Dm p C0 + D.kapD p / 2 + 1 ∧
    (∀ Z, Integral v Z → D.Good p Z →
      Integral v (((p : K) ^ ⌈D.Dm p C0 + D.kapD p / 2⌉₊) • dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → D.Good p (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (i : Fin (D.nch j)),
      vala D.msg (D.chainSet j i) (D.th j i - D.sl j i - 12 * D.c) (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
      vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) (θ - 24 * D.c) (dg gm (Pj (dg gp Z)))) := by
  obtain ⟨hP1, hP2, hP3, -, hP5⟩ := hPj
  have hp : 2 ≤ p := two_le_p hD
  have hr : 1 ≤ D.r := hV.1
  have hJ : 1 ≤ D.J := hV.2.1
  have hkap := D.kapD_ge_one hp hr hJ
  have hDm := D.Dm_nonneg hp hr h1
  have hpos : 0 ≤ D.Dm p C0 + D.kapD p / 2 := by linarith
  refine ⟨(Nat.ceil_lt_add_one hpos).le, ?_, ?_, ?_, ?_⟩
  · intro Z hZi hZg
    rw [← cge_zero_iff_Integral]
    have hY : cge v 0 (dg gp Z) := by
      have := cge_dg v (a := 0) (b := 0) (f := gp) (fun ζ => (vge_zero_iff v _).mpr (hgp ζ))
        ((cge_zero_iff_Integral v Z).mpr hZi)
      simpa using this
    have hYg : D.Good p (dg gp Z) := TwistData.Good.dg D hZg gp
    have hPY : cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (dg gp Z)) := by
      rw [linMap_eq_sum Pj (dg gp Z)]
      refine cge_sum v _ _ fun ζ hζ => ?_
      have := cge_smul v (hY ζ) (cge_Pj_monomial hD D hr Pj hP1 hP2 ζ (hYg ζ hζ))
      simpa using this
    have hG : cge v (-(D.Dm p C0 + D.kapD p / 2)) (dg gm (Pj (dg gp Z))) := by
      have := cge_dg v (a := 0) (f := gm) (fun ζ => (vge_zero_iff v _).mpr (hgm ζ)) hPY
      simpa using this
    have := cge_smul v (vge_p_pow hD ⌈D.Dm p C0 + D.kapD p / 2⌉₊) hG
    refine cge_mono v ?_ this
    have := Nat.le_ceil (D.Dm p C0 + D.kapD p / 2)
    linarith
  · intro Z hZg
    exact TwistData.Good.dg D (good_Pj D Pj hP1 (TwistData.Good.dg D hZg gp)) gm
  · intro Z _ j i
    exact (hcost (D.chainSet j i) (D.mlab_notMem_chainSet j i) _ _ (hP3 (dg gp Z) j i)).2
  · intro Z _ j m θ _ hZ
    have a1 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) θ Z hZ).1
    have a2 := hP5 j m _ _ a1
    have a3 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) _ _ a2).2
    exact vala_mono (by linarith) a3

end Main

end Formalism.MainNotions.PlaneGram
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SecondEmbeddingTangentIndex
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def Marked (o : Finset (Fin (D.nB j + D.r))) : Prop := ∃ l ∈ o, l.val < D.nB j


open Classical in
def fk (o : Finset (Fin (D.nB j + D.r))) : Fin (D.nB j + D.r) → D.ML :=
  @ite _ (D.Marked j o) (by unfold Marked; infer_instance) (D.e1 j) (D.e0 j)

theorem fk_inj (o : Finset (Fin (D.nB j + D.r))) : Function.Injective (D.fk j o) := by
  unfold fk; split_ifs
  · exact D.second_embedding_injective j
  · exact D.index_embedding_injective j

theorem segL_fk (o : Finset (Fin (D.nB j + D.r))) (l : Fin (D.nB j + D.r)) :
    D.SegL j (D.fk j o l) := by
  unfold fk; split_ifs
  · exact D.segment_letter_second_embedding j l
  · exact D.segment_letter_first_embedding j l

theorem fk_castAdd (o : Finset (Fin (D.nB j + D.r))) (a : Fin (D.nB j)) :
    D.fk j o (Fin.castAdd D.r a) = D.mb (D.eB j a) := by
  unfold fk; split_ifs <;> simp

def cnt (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) : ℕ :=
  ∑ l, if D.fk j o l = i then (if l ∈ o then 1 else 0) else 0

theorem cnt_eq (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (l0 : Fin (D.nB j + D.r))
    (h : D.fk j o l0 = i) : D.cnt j o i = if l0 ∈ o then 1 else 0 := by
  unfold cnt
  rw [Finset.sum_eq_single l0]
  · rw [if_pos h]
  · intro l _ hl
    rw [if_neg]
    intro h2
    exact hl (D.fk_inj j o (h2.trans h.symm))
  · intro h2; exact absurd (Finset.mem_univ _) h2

theorem cnt_zero (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (h : ∀ l, D.fk j o l ≠ i) :
    D.cnt j o i = 0 := by
  unfold cnt
  exact Finset.sum_eq_zero fun l _ => if_neg (h l)

theorem cnt_le_one (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) : D.cnt j o i ≤ 1 := by
  by_cases h : ∃ l, D.fk j o l = i
  · obtain ⟨l0, h0⟩ := h
    rw [D.cnt_eq j o i l0 h0]
    split_ifs <;> simp
  · push_neg at h
    rw [D.cnt_zero j o i h]; exact Nat.zero_le _

theorem first_embedding_ne_tangent (l : Fin (D.nB j + D.r)) (t : D.Tau) : D.e0 j l ≠ D.mtp t := by
  refine Fin.addCases (fun a => ?_) (fun m => ?_) l <;> simp [mb, mlab, mtp]

theorem second_embedding_tangent_index (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mtp (j, m)) :
    m.val ≠ 0 ∧ l = Fin.natAdd (D.nB j) (Fin.rev m) := by
  revert h
  refine Fin.addCases (fun a => ?_) (fun m0 => ?_) l
  · simp [mb, mtp]
  · rw [second_embedding_natAdd]
    split_ifs with h0
    · simp [mlab, mtp]
    · intro h
      simp only [mtp, Sum.inr.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact ⟨h0, by rw [Fin.rev_rev]⟩

theorem second_embedding_label_index_zero (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mlab (j, m)) :
    m.val = 0 := by
  revert h
  refine Fin.addCases (fun a => ?_) (fun m0 => ?_) l
  · simp [mb, mlab]
  · rw [second_embedding_natAdd]
    split_ifs with h0
    · intro h
      simp only [mlab, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact h0
    · simp [mlab, mtp]

theorem cnt_mb (o : Finset (Fin (D.nB j + D.r))) (a : Fin (D.nB j)) :
    D.cnt j o (D.mb (D.eB j a)) = if Fin.castAdd D.r a ∈ o then 1 else 0 :=
  D.cnt_eq j o _ _ (D.fk_castAdd j o a)

theorem cnt_lab_add_tp (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) :
    D.cnt j o (D.mlab (j, m)) + D.cnt j o (D.mtp (j, m)) =
      if Fin.natAdd (D.nB j) (Fin.rev m) ∈ o then 1 else 0 := by
  by_cases hM : D.Marked j o
  · have hf : D.fk j o = D.e1 j := by unfold fk; rw [if_pos hM]
    by_cases h0 : m.val = 0
    · rw [D.cnt_eq j o (D.mlab (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, second_embedding_natAdd, Fin.rev_rev, if_pos h0]),
        D.cnt_zero j o (D.mtp (j, m)) (by
          intro l hl; rw [hf] at hl; exact (D.second_embedding_tangent_index j l m hl).1 h0), add_zero]
    · rw [D.cnt_eq j o (D.mtp (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, second_embedding_natAdd, Fin.rev_rev, if_neg h0]),
        D.cnt_zero j o (D.mlab (j, m)) (by
          intro l hl; rw [hf] at hl; exact h0 (D.second_embedding_label_index_zero j l m hl)), zero_add]
  · have hf : D.fk j o = D.e0 j := by unfold fk; rw [if_neg hM]
    rw [D.cnt_eq j o (D.mlab (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, first_embedding_natAdd, Fin.rev_rev]),
        D.cnt_zero j o (D.mtp (j, m)) (by
          intro l hl; rw [hf] at hl; exact D.first_embedding_ne_tangent j l _ hl), add_zero]

theorem cnt_tp_zero (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) (h0 : m.val = 0) :
    D.cnt j o (D.mtp (j, m)) = 0 := by
  apply D.cnt_zero
  intro l hl
  unfold fk at hl
  split_ifs at hl
  · exact (D.second_embedding_tangent_index j l m hl).1 h0
  · exact D.first_embedding_ne_tangent j l _ hl

theorem cnt_tp_le (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) :
    D.cnt j o (D.mtp (j, m)) ≤ ∑ a : Fin (D.nB j), if Fin.castAdd D.r a ∈ o then 1 else 0 := by
  by_cases hM : D.Marked j o
  · obtain ⟨l, hl, hln⟩ := hM
    refine le_trans (D.cnt_le_one j o _) ?_
    have : (if Fin.castAdd D.r (⟨l.val, hln⟩ : Fin (D.nB j)) ∈ o then 1 else 0 : ℕ) = 1 := by
      rw [if_pos]
      have : Fin.castAdd D.r (⟨l.val, hln⟩ : Fin (D.nB j)) = l := by ext; simp
      rw [this]; exact hl
    have h2 := Finset.single_le_sum (f := fun a : Fin (D.nB j) => if Fin.castAdd D.r a ∈ o then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨l.val, hln⟩ : Fin (D.nB j)))
    simp only [this] at h2
    exact h2
  · rw [D.cnt_zero j o]
    · exact Nat.zero_le _
    · intro l hl
      unfold fk at hl
      rw [if_neg hM] at hl
      exact D.first_embedding_ne_tangent j l _ hl

theorem cnt_not_segL (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (hi : ¬ D.SegL j i) :
    D.cnt j o i = 0 := by
  apply D.cnt_zero
  intro l hl
  exact hi (hl ▸ D.segL_fk j o l)

def PsiP {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) : MvPolynomial (D.ML × Fin D.r) K :=
  ∏ k, rename (Prod.map (D.fk j (occ k)) id) (col k)

theorem PsiP_HomD {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0)) :
    HomD (fun i => ∑ k, D.cnt j (occ k) i) (D.PsiP j col occ) := by
  unfold PsiP
  refine HomD_prod _ _ _ fun k _ => ?_
  exact HomD_rename (D.fk j (occ k)) (D.fk_inj j _) _ _ ((mem_PolK_iff _ _).mp (hcol k))

theorem PsiP_support {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0))
    (hcount : ∀ i, (univ.filter fun k => i ∈ occ k).card = D.dO (D.eA j i))
    (ξ : D.EM) (hξ : ξ ∈ (D.PsiP j col occ).support) :
    D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0 := by
  have hd := D.PsiP_HomD j col occ hcol ξ hξ
  have hc : ∀ i, (∑ k, if i ∈ occ k then 1 else 0) = D.dO (D.eA j i) := by
    intro i; rw [← hcount i, Finset.card_filter]
  have hz : ∀ i, ldeg ξ i = 0 → ∀ a, ξ (i, a) = 0 := by
    intro i h a
    unfold ldeg at h
    exact (Finset.sum_eq_zero_iff.mp h) a (Finset.mem_univ a)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨a, rfl⟩ := D.eB_surj j b hb
    rw [hd]
    simp only [cnt_mb]
    rw [hc, eA_castAdd]; rfl
  · intro m
    rw [hd, hd, ← Finset.sum_add_distrib]
    simp only [cnt_lab_add_tp]
    rw [hc, eA_natAdd, Fin.rev_rev]; rfl
  · intro m
    rw [hd]
    refine le_trans (Finset.sum_le_sum fun k _ => D.cnt_tp_le j (occ k) m) ?_
    rw [Finset.sum_comm, dLL_eq_sum]
    refine le_of_eq (Finset.sum_congr rfl fun a _ => ?_)
    rw [hc, eA_castAdd]; rfl
  · intro m h0
    apply hz
    rw [hd]
    exact Finset.sum_eq_zero fun k _ => D.cnt_tp_zero j _ m h0
  · intro i hi
    apply hz
    rw [hd]
    exact Finset.sum_eq_zero fun k _ => D.cnt_not_segL j _ i hi

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

