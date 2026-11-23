module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0014
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0013
public import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestLjjFinProved
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.CountingStatementReduction

section Lvl

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem mem_xiMons_of (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ)
    (hsupp : ∀ v ∈ m.support, ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c)
    (hsum : ∑ c, m (Formalism.GM.M.xiVar N r G.T.t c) = n) : m ∈ xiMons (r := r) G n := by
  classical
  unfold xiMons
  rw [Finset.mem_image]
  refine ⟨fun c => m (Formalism.GM.M.xiVar N r G.T.t c), (CountingStatementReduction.mem_Ev _).2 hsum, ?_⟩
  ext v
  rw [Finsupp.finsetSum_apply]
  by_cases hv : ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c
  · obtain ⟨c, rfl⟩ := hv
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  · have h0 : m v = 0 := by
      by_contra hne
      exact hv (hsupp v (Finsupp.mem_support_iff.2 hne))
    rw [h0]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hv ⟨c, h.symm⟩

theorem xi_mem_spanZ (n : ℕ) (g : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ Formalism.GM.M.XiPolZ p N r G.T.t n) :
    g ∈ Submodule.span ℤ_[p] ((fun m => (monomial m (1 : ℚ_[p]))) '' (xiMons (r := r) G n : Set _)) := by
  classical
  obtain ⟨hs, hint⟩ := Submodule.mem_inf.1 hg
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hs
  obtain ⟨g0, hg0⟩ := hint
  have hc : ∀ m, AddMonoidAlgebra.coeff g m = algebraMap ℤ_[p] ℚ_[p] (AddMonoidAlgebra.coeff g0 m) := by
    intro m
    rw [← hg0]
    simp [MvPolynomial.coeff_map]
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨hsupp, hsum⟩ := hs hm
  have hmono : monomial m (AddMonoidAlgebra.coeff g m) = (AddMonoidAlgebra.coeff g0 m) • monomial m (1 : ℚ_[p]) := by
    rw [hc m, smul_monomial, Algebra.smul_def, mul_one]
  rw [hmono]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, mem_xiMons_of G n m hsupp hsum, rfl⟩)

theorem Ljj_fg (j : Fin G.T.t → ℕ) (jp : ℕ) : (Ljj p (r := r) G j jp).FG := by
  classical
  obtain ⟨A, hA⟩ := Formalism.GM.TM.yZ_fg (p := p) (r := r) (G.lettersAt j jp) G.T.J G.T.thr
  let S : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :=
    (fun am : _ × _ => rename (Formalism.GM.M.chainEmb N r G.T.t) am.1 * monomial am.2 (1 : ℚ_[p])) ''
      ((A : Set _) ×ˢ (xiMons (r := r) G (G.B - jp) : Set _))
  have hS : S.Finite := (A.finite_toSet.prod (xiMons (r := r) G (G.B - jp)).finite_toSet).image _
  have hle : Ljj p (r := r) G j jp ≤ Submodule.span ℤ_[p] S := by
    unfold Ljj
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, g, hg, rfl⟩
    have hy' : y ∈ Submodule.span ℤ_[p] (A : Set _) := by rw [hA]; exact hy
    have hg' := xi_mem_spanZ G (G.B - jp) g hg
    clear hy hg
    induction hy' using Submodule.span_induction with
    | mem a ha =>
      induction hg' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, hm, rfl⟩ := hx
        exact Submodule.subset_span ⟨(a, m), ⟨ha, hm⟩, rfl⟩
      | zero => simp
      | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ c hu
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), add_mul]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu =>
      have : rename (Formalism.GM.M.chainEmb N r G.T.t) (c • u) = c • rename (Formalism.GM.M.chainEmb N r G.T.t) u := by
        rw [← algebraMap_smul ℚ_[p] c u, ← algebraMap_smul ℚ_[p] c (rename (Formalism.GM.M.chainEmb N r G.T.t) u)]
        exact map_smul (rename (Formalism.GM.M.chainEmb N r G.T.t)) _ _
      rw [this, smul_mul_assoc]
      exact Submodule.smul_mem _ c hu
  exact Submodule.FG.of_le (Submodule.fg_span hS) hle

end Lvl

section Lvl2

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem ljjFin_gen (j : Fin G.T.t → ℕ) (jp : ℕ) :
    (Ljj p (r := r) G j jp).FG ∧
    ∃ W : Submodule ℚ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]),
      FiniteDimensional ℚ_[p] W ∧ ∀ u ∈ Ljj p (r := r) G j jp, u ∈ W :=
  ⟨Ljj_fg G j jp, _, Ljj_span_fd G j jp, fun _ hu => Submodule.subset_span hu⟩

end Lvl2

theorem restLjjFin_proved (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestLjjFin C0 CE1 CE2 X :=
  fun _ _ aTop _ x _ => ljjFin_gen (p := X.p) (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.UTopVal
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section SI

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

private theorem lLL_deg_mul_segP_le_two_mul_a_of_kept (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA))
    (b : SegBlock X.s X.r) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) ≠ 2 * X.s) :
    ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) (topOf q hq) : ℝ) ≤ 2 * X.L.a := by
  have hF := hS.hF
  have h1 := lLL_deg_le_chain hS a b x q
  obtain ⟨-, hK1, hK2, -⟩ := hK
  set v := topOf q hq with hv
  set P := SegData.P X.p (X.S C0 CE1 CE2) v with hPdef
  have hc : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ (X.S C0 CE1 CE2).bTop v / P ∨
      (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ a v / P := by
    have hA : coarseA X.p (X.S C0 CE1 CE2) b v ≤ (X.S C0 CE1 CE2).bTop v / P :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    have hC : coarseC X.p (X.S C0 CE1 CE2) a b v ≤ a v / P :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    simp only [segChain, dif_neg hq]
    rw [← hv]
    split_ifs with h2 h3 h3
    · exact Or.inl ((hK2 v h3).2.1.trans hA)
    · exact Or.inl (((hK1 v (not_lt.mp h3)).1).trans hA)
    · exact Or.inr ((Nat.sub_le _ _).trans hC)
    · exact Or.inr hC
  have hbT : ((X.S C0 CE1 CE2).bTop v : ℝ) ≤ 2 * X.L.a := by
    have h5 := hS.bTop v
    have hb0 := hF.b0
    have hlt := hF.b_lt
    have hpm := hF.p_ge
    have hm := hF.m4
    have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hm
    have hp25 : (25 : ℝ) ≤ X.L.p := by nlinarith
    nlinarith
  have haT : (a v : ℝ) ≤ 2 * X.L.a := by
    have hmem := Fintype.mem_piFinset.mp hT v
    simp only [flipOneThree.Inst.winA, Finset.mem_Icc] at hmem
    have h2 := Nat.floor_le hF.win0
    have h3 : (a v : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) := by exact_mod_cast hmem.2
    linarith [hF.win_le]
  have hfin : ∀ N : ℕ, (N : ℝ) ≤ 2 * X.L.a → (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ N / P →
      ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) * (P : ℝ) ≤ 2 * X.L.a := by
    intro N hN hd
    have h4 : (lLL C0 CE1 CE2 X a b x).deg q * P ≤ N :=
      (Nat.mul_le_mul_right P (h1.trans hd)).trans (Nat.div_mul_le_self N P)
    have h5 : (((lLL C0 CE1 CE2 X a b x).deg q * P : ℕ) : ℝ) ≤ N := by exact_mod_cast h4
    push_cast at h5
    linarith
  rcases hc with hc | hc
  · exact hfin _ hbT hc
  · exact hfin _ haT hc

theorem S_bound (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) :
    ((gT C0 CE1 CE2 X b).S (lLL C0 CE1 CE2 X a b x) i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
  have hF := hS.hF
  have hK' := hK
  obtain ⟨-, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hus : (u : ℕ) < X.s := u.2
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  have hSdef : (gT C0 CE1 CE2 X b).S (lLL C0 CE1 CE2 X a b x) i =
      ∑ q : Fin (2 * X.s + 1), if (q : ℕ) ≤ 2 * (u : ℕ) then (lLL C0 CE1 CE2 X a b x).deg q else 0 := rfl
  rw [hSdef]
  push_cast
  rw [Finset.sum_mul]
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hpm := hF.p_ge
  have hp : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have hb0 := hF.b0
  have hB : (0 : ℝ) ≤ 2 * X.L.a / X.p := by positivity
  have key : ∀ q : Fin (2 * X.s + 1),
      (if (q : ℕ) ≤ 2 * (u : ℕ) then ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) else 0) *
          (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤
        (if (q : ℕ) = 2 * (u : ℕ) then 5 / 2 * X.L.b' else 0) + 2 * X.L.a / X.p := by
    intro q
    by_cases h : (q : ℕ) ≤ 2 * (u : ℕ)
    · rw [if_pos h]
      by_cases he : (q : ℕ) = 2 * (u : ℕ)
      · rw [if_pos he]
        have h1 := lLL_deg_le_chain hS a b x q
        rw [segChain_deg_even (X.S C0 CE1 CE2) a b q u he hσu] at h1
        have hA : coarseA X.p (X.S C0 CE1 CE2) b u ≤
            (X.S C0 CE1 CE2).bTop u / SegData.P X.p (X.S C0 CE1 CE2) u :=
          Nat.div_le_div_right (Nat.sub_le _ _)
        have h4 : (lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u ≤
            (X.S C0 CE1 CE2).bTop u :=
          (Nat.mul_le_mul_right _ ((h1.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
        have h5 : (((lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u : ℕ) : ℝ) ≤
            (X.S C0 CE1 CE2).bTop u := by exact_mod_cast h4
        push_cast at h5
        linarith [hS.bTop u]
      · rw [if_neg he, zero_add]
        have hq : (q : ℕ) ≠ 2 * X.s := by omega
        have h2 := lLL_deg_mul_segP_le_two_mul_a_of_kept hS a hT b hK x q hq
        have hvu : topOf q hq < u := by
          rw [Fin.lt_iff_val_lt_val]
          simp only [topOf]
          omega
        have h3 := P_step (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) _ _ hvu
        have h3' : ((X.p : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤
            (SegData.P X.p (X.S C0 CE1 CE2) (topOf q hq) : ℝ) := by exact_mod_cast h3
        rw [le_div_iff₀ hp]
        have hd0 : (0 : ℝ) ≤ ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) := Nat.cast_nonneg _
        nlinarith
    · rw [if_neg h, zero_mul]
      split_ifs <;> positivity
  calc _ ≤ ∑ q : Fin (2 * X.s + 1),
        ((if (q : ℕ) = 2 * (u : ℕ) then 5 / 2 * X.L.b' else 0) + 2 * X.L.a / X.p) :=
        Finset.sum_le_sum (fun q _ => key q)
    _ = 5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.sum_eq_single (⟨2 * (u : ℕ), by omega⟩ : Fin (2 * X.s + 1))]
        · simp
        · intro c _ hc
          rw [if_neg]
          intro hc'
          exact hc (Fin.ext hc')
        · intro hc
          exact absurd (Finset.mem_univ _) hc

end SI

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

