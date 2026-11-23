module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CorePair
section
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem exists_blk {p q r s : ℕ} (a b c d : List ℤ) (hd : PI.FJM.ShapeData p q r s a b c d) (u v : ℚ)
    (hu : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = u)
    (hv : ∀ j : Fin q, (pad c (q - c.length - d.length) d).getD j 0 = v) :
    ∃ (x : Pol p q r s) (dx : ℕ), x ≠ 0 ∧ x ∈ homog (Ix p q × Ix r s) dx ∧ x ∈ Jset p q r s ∧
      ∀ a' b', sameBlock a' b' → fockAct1 p q r s (Eab a' b') x =
        (if a' = b' then (((Sum.elim (fun _ => u + cPair r s) (fun _ => v - cPair r s) a' : ℚ)) : ℂ) else 0) • x := by
  let μ : Ix p q → ℚ := Sum.elim (fun _ => u + cPair r s) (fun _ => v - cPair r s)
  have hS : JointShape p q r s μ (PI.FJM.wtOf2 p q r s a b c d) := by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := hd
    refine ⟨a, b, c, d, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, ?_, ?_⟩
    · funext i
      cases i with
      | inl i => simp only [shiftNu, ofBlocks, μ, Sum.elim_inl, hu]; ring
      | inr i => simp only [shiftNu, ofBlocks, μ, Sum.elim_inr, hv]; ring
    · funext i
      cases i with
      | inl i => simp only [shiftNu, PI.FJM.wtOf2, PI.FJM.sh2, Sum.elim_inl]; ring
      | inr i => simp only [shiftNu, PI.FJM.wtOf2, PI.FJM.sh2, Sum.elim_inr]; ring
  have h1 := (fock_joint_multiplicity p q r s μ _).1 hS
  have hne : hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) (PI.FJM.wtOf2 p q r s a b c d) ⊓
      Submodule.span ℂ (Jset p q r s) ≠ ⊥ := by
    intro h0
    rw [h0] at h1
    simp at h1
  obtain ⟨P, hP, hP0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hPJ : P ∈ Jset p q r s := PI.FJMF.span_jset P (Submodule.mem_inf.1 hP).2
  have hP1 : P ∈ hwSub (fockAct1 p q r s) μ := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hP).1).1
  have hex : ∃ e, homogeneousComponent e P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hP0
    rw [← sum_homogeneousComponent P]
    exact Finset.sum_eq_zero fun e _ => hcon e
  obtain ⟨e, he⟩ := hex
  refine ⟨homogeneousComponent e P, e, he, homogeneousComponent_mem e P, PI.FJMF.jset_hc P hPJ e, ?_⟩
  intro a' b' hab
  refine scalar_of_hw (μ := μ) ?_ (PI.FJMF.hc_mem_hwSub1 μ P hP1 e) a' b' hab
  intro x y hxy
  cases x <;> cases y <;> simp_all [μ, sameBlock]

theorem fockAct1_Eab_inr_inl_eq_zero_of_mem_Jset {p q r : ℕ} {x : Pol p q r 0} (hx : x ∈ Jset p q r 0) (i : Fin p) (j : Fin q) :
    fockAct1 p q r 0 (Eab (.inr j) (.inl i)) x = 0 := by
  have h := ((PI.FJM.jointHarmonicsIffLaplacians p q r 0 x).1 hx).2.1 i j
  rw [PI.FJM.leftOffDiagonalActionFormula p q r 0 _ _ (by simp)]
  simp only [PI.FJM.rai1, PI.FJM.lapB, PI.FJM.dd, LinearMap.sum_apply, Fintype.sum_sum_type,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, Module.End.mul_apply, raiB, lowB, linePos] at h ⊢
  simp only [Bool.false_eq_true, if_false, if_true, LinearMap.neg_apply, Finset.sum_neg_distrib, neg_eq_zero]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => PI.FockOneDegW.Core.pd_comm _ _ _

theorem cross_y {p q s : ℕ} {y : Pol p q 0 s} (hy : y ∈ Jset p q 0 s) (i : Fin p) (j : Fin q) :
    fockAct1 p q 0 s (Eab (.inl i) (.inr j)) y = 0 := by
  have h := ((PI.FJM.jointHarmonicsIffLaplacians p q 0 s y).1 hy).1 i j
  rw [PI.FJM.leftOffDiagonalActionFormula p q 0 s _ _ (by simp)]
  simp only [PI.FJM.rai1, PI.FJM.lapA, PI.FJM.dd, LinearMap.sum_apply, Fintype.sum_sum_type,
    Finset.univ_eq_empty, Finset.sum_empty, zero_add, Module.End.mul_apply, raiB, lowB, linePos] at h ⊢
  simp only [Bool.false_eq_true, if_false, if_true, LinearMap.neg_apply, Finset.sum_neg_distrib, neg_eq_zero]
  exact h

theorem pair_of {p q r s : ℕ} (c0 u v u' v' : ℚ) (h1 : u' + cPair 0 s = c0 - (u + cPair r 0))
    (h2 : v' - cPair 0 s = c0 - (v - cPair r 0))
    (hx : ∃ (x : Pol p q r 0) (dx : ℕ), x ≠ 0 ∧ x ∈ homog (Ix p q × Ix r 0) dx ∧ x ∈ Jset p q r 0 ∧
      ∀ a' b', sameBlock a' b' → fockAct1 p q r 0 (Eab a' b') x =
        (if a' = b' then (((Sum.elim (fun _ => u + cPair r 0) (fun _ => v - cPair r 0) a' : ℚ)) : ℂ) else 0) • x)
    (hy : ∃ (x : Pol p q 0 s) (dx : ℕ), x ≠ 0 ∧ x ∈ homog (Ix p q × Ix 0 s) dx ∧ x ∈ Jset p q 0 s ∧
      ∀ a' b', sameBlock a' b' → fockAct1 p q 0 s (Eab a' b') x =
        (if a' = b' then (((Sum.elim (fun _ => u' + cPair 0 s) (fun _ => v' - cPair 0 s) a' : ℚ)) : ℂ) else 0) • x) :
    PairData p q r s (c0 : ℂ) := by
  obtain ⟨x, dx, x0, xh, xJ, xK⟩ := hx
  obtain ⟨y, dy, y0, -, yJ, yK⟩ := hy
  refine ⟨fun a => (((Sum.elim (fun _ => u + cPair r 0) (fun _ => v - cPair r 0) a : ℚ)) : ℂ), x, y, dx,
    x0, y0, xh, xK, fockAct1_Eab_inr_inl_eq_zero_of_mem_Jset xJ, fun a b hab => ?_, cross_y yJ⟩
  rw [yK a b hab, h1, h2]
  cases a <;> simp only [Sum.elim_inl, Sum.elim_inr, Rat.cast_sub]

theorem pad_l (k : ℕ) (z : ℤ) (i : Fin k) :
    (pad (List.replicate k z) (k - (List.replicate k z).length - ([] : List ℤ).length) []).getD i 0 = (z : ℚ) := by
  simp [pad, List.getD_eq_getElem?_getD]

theorem pad_r (k : ℕ) (z : ℤ) (i : Fin k) :
    (pad [] (k - ([] : List ℤ).length - (List.replicate k z).length) (List.replicate k z)).getD i 0 = (z : ℚ) := by
  simp [pad, List.getD_eq_getElem?_getD]

theorem pad_nil_getD_zero (k : ℕ) (i : Fin k) :
    (pad [] (k - ([] : List ℤ).length - ([] : List ℤ).length) []).getD i 0 = (0 : ℚ) := by
  simp [pad, List.getD_eq_getElem?_getD]

theorem pw_rep (k : ℕ) (z : ℤ) : (List.replicate k z).Pairwise (· ≥ ·) := by
  rw [List.pairwise_replicate]
  exact Or.inr le_rfl

theorem pair_pos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = n + cPair r s) (h2 : c0 = m - cPair r s) : PairData p q r s (c0 : ℂ) := by
  refine pair_of c0 ((n : ℤ) : ℚ) 0 0 ((m : ℤ) : ℚ) ?_ ?_
    (exists_blk (List.replicate p (n : ℤ)) [] [] [] ?_ _ _ (pad_l p _) (pad_nil_getD_zero q))
    (exists_blk [] [] (List.replicate q (m : ℤ)) [] ?_ _ _ (pad_nil_getD_zero p) (pad_l q _))
  · simp only [cPair] at *; push_cast at *; linarith
  · simp only [cPair] at *; push_cast at *; linarith
  · refine ⟨?_, by simp, by simp, by simp, pw_rep _ _, by simp, by simp, by simp, by simp, by simp,
      by simpa using hp, by simp⟩
    intro v hv; rw [List.eq_of_mem_replicate hv]; exact_mod_cast hn
  · refine ⟨by simp, ?_, by simp, by simp, by simp, by simp, pw_rep _ _, by simp, by simp, by simp,
      by simp, by simpa using hq⟩
    intro v hv; rw [List.eq_of_mem_replicate hv]; exact_mod_cast hm

theorem pair_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s) : PairData p q r s (c0 : ℂ) := by
  refine pair_of c0 0 ((-(n : ℤ) : ℤ) : ℚ) ((-(m : ℤ) : ℤ) : ℚ) 0 ?_ ?_
    (exists_blk [] [] [] (List.replicate q (-(n : ℤ))) ?_ _ _ (pad_nil_getD_zero p) (pad_r q _))
    (exists_blk [] (List.replicate p (-(m : ℤ))) [] [] ?_ _ _ (pad_r p _) (pad_nil_getD_zero q))
  · simp only [cPair] at *; push_cast at *; linarith
  · simp only [cPair] at *; push_cast at *; linarith
  · refine ⟨by simp, by simp, by simp, ?_, by simp, by simp, by simp, pw_rep _ _, by simp, by simp,
      by simpa using hq, by simp⟩
    intro v hv; rw [List.eq_of_mem_replicate hv]; omega
  · refine ⟨by simp, by simp, ?_, by simp, by simp, pw_rep _ _, by simp, by simp, by simp, by simp,
      by simp, by simpa using hp⟩
    intro v hv; rw [List.eq_of_mem_replicate hv]; omega

end PositivityTheory.KReal

end
end

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreProj
section
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem graded_orth {σ : Type} [Fintype σ] (L : Submodule ℂ (MvPolynomial σ ℂ))
    (hL : ∀ d, ∀ z ∈ L, homogeneousComponent d z ∈ L) (u : MvPolynomial σ ℂ) :
    ∃ y ∈ L, ∀ z ∈ L, fockInner z (u - y) = 0 := by
  have key : ∀ d, ∀ u ∈ homog σ d, ∃ y ∈ L, ∀ z ∈ L, fockInner z (u - y) = 0 := by
    intro d u hu
    obtain ⟨y, hy, h⟩ := PI.FHS.exists_orth (L ⊓ homog σ d) d inf_le_right u
    refine ⟨y, hy.1, fun z hz => ?_⟩
    rw [← PI.FHS.fockInner_hc_left z (u - y) (Submodule.sub_mem _ hu hy.2)]
    exact h _ ⟨hL d z hz, homogeneousComponent_mem d z⟩
  choose! f hf using fun d => key d (homogeneousComponent d u) (homogeneousComponent_mem d u)
  refine ⟨∑ i ∈ Finset.range (u.totalDegree + 1), f i, Submodule.sum_mem _ fun i _ => (hf i).1, fun z hz => ?_⟩
  have e : u - ∑ i ∈ Finset.range (u.totalDegree + 1), f i =
      ∑ i ∈ Finset.range (u.totalDegree + 1), (homogeneousComponent i u - f i) := by
    rw [Finset.sum_sub_distrib, sum_homogeneousComponent]
  rw [e, PI.FHS.fockInner_sum_right]
  exact Finset.sum_eq_zero fun i _ => (hf i).2 z hz

theorem unit_homog {p q r : ℕ} (a b : Ix p q) (i : ℕ) (P : Pol p q r 0) (hP : P ∈ homog (Ix p q × Ix r 0) i) :
    ∃ e, fockAct1 p q r 0 (Eab a b) P ∈ homog (Ix p q × Ix r 0) e := by
  by_cases hab : sameBlock a b
  · exact ⟨i, (gradedOscillatorProperty p q r 0).1 _ (PI.FockOneDegW.isKC_Eab hab) i P hP⟩
  have hP' : P.IsHomogeneous i := hP
  rw [PI.FockOneDegW.fockAct1_Eab_apply]
  rcases a with a | a <;> rcases b with b | b
  · exact absurd trivial hab
  · refine ⟨1 + (1 + i), Submodule.sum_mem _ fun c _ => ?_⟩
    rcases c with c | c
    · rw [PI.FHS.omE_apply_of_ne (by simp)]
      simp only [raiB, lowB, linePos, if_true, Bool.false_eq_true, if_false, LinearMap.mulLeft_apply]
      exact (isHomogeneous_X ℂ _).mul ((isHomogeneous_X ℂ _).mul hP')
    · exact c.elim0
  · refine ⟨i - 1 - 1, Submodule.sum_mem _ fun c _ => ?_⟩
    rcases c with c | c
    · rw [PI.FHS.omE_apply_of_ne (by simp)]
      simp only [raiB, lowB, linePos, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply]
      exact Submodule.neg_mem _ (hP'.pderiv.pderiv)
    · exact c.elim0
  · exact absurd trivial hab

theorem gen_graded {p q r : ℕ} (x : Pol p q r 0) (dx : ℕ) (hx : x ∈ homog (Ix p q × Ix r 0) dx) :
    ∀ d, ∀ z ∈ genG (fockAct1 p q r 0) (Submodule.span ℂ {x}),
      homogeneousComponent d z ∈ genG (fockAct1 p q r 0) (Submodule.span ℂ {x}) := by
  set L := genG (fockAct1 p q r 0) (Submodule.span ℂ {x}) with hLdef
  have hxL : x ∈ L := by
    rw [hLdef, genG, Submodule.mem_sInf]
    exact fun N hN => hN.1 (Submodule.mem_span_singleton_self x)
  have hst : ∀ W, ∀ z ∈ L, fockAct1 p q r 0 W z ∈ L := by
    intro W z hz
    rw [hLdef, genG, Submodule.mem_sInf] at hz ⊢
    exact fun N hN => hN.2 W z (hz N hN)
  have hhom : ∀ e d, ∀ w ∈ homog (Ix p q × Ix r 0) e, w ∈ L → homogeneousComponent d w ∈ L := by
    intro e d w hw hwL
    rw [homogeneousComponent_of_mem hw]
    split_ifs
    · exact hwL
    · exact L.zero_mem
  let L' : Submodule ℂ (Pol p q r 0) := ⨅ d, L.comap (homogeneousComponent d)
  have mem' : ∀ z, z ∈ L' ↔ ∀ d, homogeneousComponent d z ∈ L := fun z => by
    simp only [L', Submodule.mem_iInf, Submodule.mem_comap]
  have hle : L ≤ L' := by
    rw [hLdef, genG]
    refine sInf_le ⟨?_, ?_⟩
    · rw [Submodule.span_singleton_le_iff_mem, mem']
      exact fun d => hhom dx d x hx hxL
    · intro W z hz
      rw [act_eq_sum]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_homogeneousComponent z, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨e, he⟩ := unit_homog a b i _ (homogeneousComponent_mem i z)
      rw [mem']
      exact fun d => hhom e d _ he (hst _ _ ((mem' z).1 hz i))
  exact fun d z hz => (mem' z).1 (hle hz) d

theorem proj_gen {p q r : ℕ} (x : FV p q r 0) (dx : ℕ) (hx : (x : Pol p q r 0) ∈ homog (Ix p q × Ix r 0) dx) :
    genG (fvAct1 p q r 0) (Submodule.span ℂ {x}) ⊔ (genG (fvAct1 p q r 0) (Submodule.span ℂ {x}))ᗮ = ⊤ := by
  rw [eq_top_iff]
  intro u _
  obtain ⟨y, hy, h⟩ := graded_orth (σ := Ix p q × Ix r 0) _ (gen_graded (p := p) (q := q) (r := r) x dx hx) u
  let y' : FV p q r 0 := y
  have h1 : y' ∈ genG (fvAct1 p q r 0) (Submodule.span ℂ {x}) := hy
  have h2 : u - y' ∈ (genG (fvAct1 p q r 0) (Submodule.span ℂ {x}))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact h z hz
  have := Submodule.add_mem_sup h1 h2
  rwa [add_sub_cancel] at this

end PositivityTheory.KReal

end
end

