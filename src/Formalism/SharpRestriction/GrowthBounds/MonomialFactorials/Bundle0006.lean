module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfLatticeInclusion
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Gen

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem le_expM (l : (Fin G.T.t → ℕ) × ℕ) (hl : l ∈ levels G) :
    padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) ≤ expM p (r := r) G :=
  Finset.le_sup (f := fun l : (Fin G.T.t → ℕ) × ℕ => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2)) hl

theorem levels_nonempty : (levels G).Nonempty := by
  classical
  refine ⟨(fun _ => 0, 0), ?_⟩
  unfold levels
  rw [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]
  exact ⟨⟨fun _ => Finset.mem_range.2 (Nat.succ_pos _), Finset.mem_range.2 (Nat.succ_pos _)⟩,
    fun _ => ⟨Nat.zero_le _, Nat.zero_le _⟩, Nat.zero_le _⟩

theorem exists_expM : ∃ l ∈ levels G, expM p (r := r) G = padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) :=
  Finset.exists_mem_eq_sup (levels G) (levels_nonempty G)
    (fun l : (Fin G.T.t → ℕ) × ℕ => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2))

end Gen

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def aBig : ℕ := (3 * X.s + 2) * X.L.a

def RestLL : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∀ x ∈ (gB C0 CE1 CE2 X aTop aPlus b).PSZ X.p (r := X.r),
        ((X.p : ℚ_[X.p]) ^ (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X))) • x ∈
          (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r)

def RestVal : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∀ l ∈ levels (gB C0 CE1 CE2 X aTop aPlus b),
        ∀ z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r), ∀ μ ∈ z.support,
          (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
              degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) +
            2 * (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
          (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + levelPassageLoss X

theorem lv_eq (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) :
    lv C0 CE1 CE2 X aTop b = levels (gB C0 CE1 CE2 X aTop aPlus b) := rfl

theorem gB_blockOK (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) :
    (gB C0 CE1 CE2 X aTop aPlus b).BlockOK := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i i' h
    have h' : (i : ℕ) < (i' : ℕ) := h
    show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) < 2 * ((X.S C0 CE1 CE2).sigma + (i' : ℕ))
    omega
  · intro i
    have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := (uTop (X.S C0 CE1 CE2) i).2
    refine ⟨?_, ?_, ?_⟩
    · show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 < 2 * X.s + 1
      omega
    · show decide ((2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ))) % 2 = 0) = true
      simp
    · show decide ((2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) % 2 = 0) = false
      rw [decide_eq_false_iff_not]
      omega
  · intro i
    have hi : (i : ℕ) < (X.S C0 CE1 CE2).t := i.2
    refine ⟨(⟨(i : ℕ), Nat.lt_succ_of_lt hi⟩ : Fin ((X.S C0 CE1 CE2).t + 1)), ?_⟩
    show (if h : (i : ℕ) < (X.S C0 CE1 CE2).t then 2 * (uTop (X.S C0 CE1 CE2) ⟨(i : ℕ), h⟩ : ℕ) + 1 else 2 * X.s + 1) =
      2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1
    rw [dite_eq_left hi]
    rfl
  · intro i
    have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := (uTop (X.S C0 CE1 CE2) i).2
    show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 < 2 * X.s
    omega
  · show decide ((2 * X.s) % 2 = 0) = true
    simp
  · rfl

theorem block_valuation_Zp_of_lattice_inclusion (hr : 1 ≤ X.r) (hLL : RestLL C0 CE1 CE2 X) (hV : RestVal C0 CE1 CE2 X) :
    BlockBoundIntegers C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hK D _
  obtain ⟨n, x, y, hx, hy, hxy, hsum⟩ := blkZ_gen X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)
    (gB_blockOK C0 CE1 CE2 X aTop aPlus b) hr (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X))
    (expM X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)) (hLL aTop hT aPlus hP b hK)
    (fun l hl => le_expM X.p _ l hl) D
  refine ⟨n, x, y, _, hx, hy, hxy, ?_, hsum⟩
  intro z hz μ hμ
  obtain ⟨l, hl, hl'⟩ := exists_expM X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)
  have h := hV aTop hT aPlus hP b hK l hl z hz μ hμ
  rw [← hl'] at h
  push_cast
  linarith

theorem gB_deg_le {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (aTop : Fin X.s → ℕ)
    (haTop : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (aPlus : ℕ) (haPlus : aPlus ∈ X.winA)
    (b : SegBlock X.s X.r) (hK : Kept X.p X.r (X.S C0 CE1 CE2) aTop b) :
    1 ≤ aBig X ∧ (∀ x, (gB C0 CE1 CE2 X aTop aPlus b).LL.deg x ≤ 2 * aBig X) ∧
      (gB C0 CE1 CE2 X aTop aPlus b).B ≤ 2 * aBig X ∧
      (∀ i, (gB C0 CE1 CE2 X aTop aPlus b).T.z i ≤ 2 * aBig X) ∧
      (gB C0 CE1 CE2 X aTop aPlus b).zPlus ≤ 2 * aBig X := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hmR : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
  have hp25 : (25 : ℝ) ≤ (X.L.p : ℝ) := by nlinarith [hF.p_ge]
  have hp1 : 1 ≤ X.p := by
    have : (1 : ℝ) ≤ (X.L.p : ℝ) := by linarith
    exact_mod_cast this
  have ha0 : (0 : ℝ) ≤ (X.L.a : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
  have hb10 : 5 / 2 * X.L.b' ≤ (X.L.a : ℝ) / 10 := by nlinarith [hF.b_lt, hF.b0]
  have hE0 : 0 ≤ (X.S C0 CE1 CE2).E0 := by
    show 0 ≤ errorTermBound CE1 CE2 X.L.p X.L.k X.L.N1 X.L.Q X.L.c X.L.a X.L.b' (X.L.La C0)
    unfold errorTermBound
    have h1 := hF.La0
    have h2 := hF.b0.le
    have h3 : (0 : ℝ) ≤ X.L.k := by show (0 : ℝ) ≤ (X.L.m : ℝ) + 1; positivity
    have h4 : (0 : ℝ) ≤ X.L.Q := by show (0 : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'; positivity
    positivity
  have hLa : (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 := by
    show X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2 ≤ 1
    have h1 : X.L.La C0 / ((X.L.m : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [hF.La_lt]
    have h2 : 4 / (X.L.p : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hbig : ((2 * aBig X : ℕ) : ℝ) = 2 * ((3 * (X.s : ℝ) + 2) * (X.L.a : ℝ)) := by
    unfold aBig; push_cast; ring
  have hsa : 0 ≤ (X.s : ℝ) * (X.L.a : ℝ) := mul_nonneg hs0 ha0
  have hwin : ∀ x ∈ X.winA, (x : ℝ) ≤ 2 * (X.L.a : ℝ) := by
    intro x hx
    have h2 := (Finset.mem_Icc.1 hx).2
    have h3 : (x : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h2
    exact (h3.trans (Nat.floor_le hF.win0)).trans hF.win_le
  have hbT : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ (X.L.a : ℝ) / 10 := fun i =>
    (hF.bT_le _ (segPos_mem X.L.TT X.j i)).trans hb10
  have hbP : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ (X.L.a : ℝ) / 10 := (hF.bT_le _ (segNext_mem X.L.TT X.j)).trans hb10
  refine ⟨?_, fun x => ?_, ?_, fun i => ?_, ?_⟩
  · have h1 : 1 ≤ X.L.a := by exact_mod_cast hF.a1
    unfold aBig
    exact Nat.mul_pos (by omega) h1
  · have h1 := segChain_deg_le (X.S C0 CE1 CE2) aTop b hK hp1 hE0 hF.La0 hLa (2 * (X.L.a : ℝ)) ((X.L.a : ℝ) / 10)
      hbT hbP (fun i => hwin _ (Fintype.mem_piFinset.1 haTop i))
      (show (X.L.a : ℝ) ≤ 2 * (X.L.a : ℝ) by linarith) x
    have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).LL.deg x : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans h1 ?_
      nlinarith
    exact_mod_cast h2
  · have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).B : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans hbP ?_
      nlinarith
    exact_mod_cast h2
  · have h0 : (gB C0 CE1 CE2 X aTop aPlus b).T.z i ≤ (X.S C0 CE1 CE2).bTop (uTop (X.S C0 CE1 CE2) i) :=
      (Nat.sub_le _ _).trans (coarseA_le (X.S C0 CE1 CE2) b _)
    have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).T.z i : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans (Nat.cast_le.2 h0) (le_trans (hbT _) ?_)
      nlinarith
    exact_mod_cast h2
  · have h0 : (gB C0 CE1 CE2 X aTop aPlus b).zPlus ≤ aPlus := Nat.sub_le _ _
    have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).zPlus : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans (Nat.cast_le.2 h0) (le_trans (hwin _ haPlus) ?_)
      nlinarith
    exact_mod_cast h2

theorem restLL_of {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hTU : ∀ (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r),
      Formalism.InvariantFactorPaths.KP.LL.HypJoin X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) ∧
      Formalism.InvariantFactorPaths.KP.LL.HypU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)) : RestLL C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hK
  obtain ⟨h1, h2, h3, h4, h5⟩ := gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop hT aPlus hP b hK
  have hr : 1 ≤ X.r := by have := r_ge C0 CYb Cde Ck CD Cb Cc X hH; omega
  exact (Formalism.InvariantFactorPaths.KP.Top.levelLattice X.p (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b) (aBig X)
    (gB_blockOK C0 CE1 CE2 X aTop aPlus b) hr h1 h2 h3 h4 h5 (hTU aTop aPlus b).1 (hTU aTop aPlus b).2).2.2

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DigitsOKOfCompat
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Chain

variable {s : ℕ} {p r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r)

theorem segChain_deg_even (x : Fin (2 * s + 1)) (u : Fin s) (hx : (x : ℕ) = 2 * (u : ℕ)) (hu : S.sigma ≤ (u : ℕ)) :
    (segChain p S aTop b).deg x = b.o u := by
  have hu' := u.isLt
  have hne : (x : ℕ) ≠ 2 * s := by omega
  have ht : topOf x hne = u := Fin.ext (by simp [topOf]; omega)
  simp only [segChain]
  rw [dite_eq_right hne, if_pos (by omega), ht, if_neg (by omega)]

theorem segChain_deg_odd (x : Fin (2 * s + 1)) (u : Fin s) (hx : (x : ℕ) = 2 * (u : ℕ) + 1)
    (hu : S.sigma ≤ (u : ℕ)) : (segChain p S aTop b).deg x = coarseC p S aTop b u := by
  have hu' := u.isLt
  have hne : (x : ℕ) ≠ 2 * s := by omega
  have ht : topOf x hne = u := Fin.ext (by simp [topOf]; omega)
  simp only [segChain]
  rw [dite_eq_right hne, if_neg (by omega), ht, if_neg (by omega)]

theorem segChain_deg_last (x : Fin (2 * s + 1)) (hx : (x : ℕ) = 2 * s) : (segChain p S aTop b).deg x = b.oPlus := by
  simp only [segChain]
  rw [dite_eq_left hx]

end Chain

theorem mem_levels_iff {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) :
    x ∈ levels G ↔ G.LevelOK x.1 x.2 := by
  simp only [levels, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (h.1 i).1.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact h.2.trans (min_le_right _ _)

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem uTop_ge (i : Fin (X.S C0 CE1 CE2).t) : (X.S C0 CE1 CE2).sigma ≤ ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) := by
  simp only [uTop]
  omega

theorem levelOK_gB (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    (gB C0 CE1 CE2 X aTop aPlus b).LevelOK x.1 x.2 ↔
      (∀ i : Fin (X.S C0 CE1 CE2).t, x.1 i ≤ b.o (uTop (X.S C0 CE1 CE2) i) ∧
        x.1 i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i)) ∧
      x.2 ≤ min b.oPlus (X.S C0 CE1 CE2).bPlus := by
  simp only [Formalism.GM.M.BlockData.LevelOK, gB, gmB, blockData, BlockData.withMargin, blockBase, gmL, gmT, segTies]
  refine and_congr (forall_congr' fun i => ?_) ?_
  · have hi := (uTop (X.S C0 CE1 CE2) i).isLt
    rw [segChain_deg_even (X.S C0 CE1 CE2) aTop b
        ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ)) (2 * X.s + 1 - 1), by omega⟩ (uTop _ i)
        (by simp only; omega) (uTop_ge i),
      segChain_deg_odd (X.S C0 CE1 CE2) aTop b
        ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) + 1) (2 * X.s + 1 - 1), by omega⟩ (uTop _ i)
        (by simp only; omega) (uTop_ge i)]
  · rw [segChain_deg_last (X.S C0 CE1 CE2) aTop b ⟨2 * X.s, by omega⟩ rfl]

theorem mem_lv (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    x ∈ lv C0 CE1 CE2 X aTop b ↔
      (∀ i : Fin (X.S C0 CE1 CE2).t, x.1 i ≤ b.o (uTop (X.S C0 CE1 CE2) i) ∧
        x.1 i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i)) ∧
      x.2 ≤ min b.oPlus (X.S C0 CE1 CE2).bPlus :=
  (mem_levels_iff (gB C0 CE1 CE2 X aTop 0 b) x).trans (levelOK_gB aTop 0 b x)

theorem digitsOK_of_compat {dl : DCl X} {aTop : Fin X.s → ℕ} (hc : Compat C0 CE1 CE2 X dl aTop)
    (b : SegBlock X.s X.r) (hb : (b.rz, b.ry) = dl) : DigitsOK X.p (X.S C0 CE1 CE2) aTop b := by
  subst hb
  simpa only [Compat, DigitsOK, ColumnSystems.digitBlock] using hc

theorem mem_cbox' {dl : DCl X} {aTop : Fin X.s → ℕ} (ha : aTop ∈ cbox C0 CE1 CE2 X dl) :
    aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl aTop := by
  simp only [cbox, Finset.mem_filter] at ha
  exact ha

theorem idx_sub (hS : SegFacts C0 CE1 CE2 X) (dl : DCl X) (aTop aTop' : Fin X.s → ℕ)
    (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (ha' : aTop' ∈ cbox C0 CE1 CE2 X dl) :
    idx C0 CE1 CE2 X dl aTop ⊆ idx C0 CE1 CE2 X dl aTop' := by
  haveI : NeZero X.r := ⟨X.hm⟩
  have hF := hS.hF
  have hwin : ∀ i, X.L.a ≤ aTop' i := fun i =>
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (mem_cbox' ha').1 i)).1
  have hp : (25:ℝ) ≤ X.L.p := by
    have h1 := hF.p_ge
    have h2 : (4:ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
    nlinarith
  have hb0 := hF.b0
  have hblt := hF.b_lt
  have h25 : 25 * X.L.b' < X.L.a := by nlinarith
  rintro ⟨b, x⟩ hbx
  simp only [idx, Finset.mem_sigma, Finset.mem_filter] at hbx ⊢
  obtain ⟨⟨hk, hdl⟩, hx⟩ := hbx
  rw [mem_keptSet] at hk ⊢
  have hD' := digitsOK_of_compat (mem_cbox' ha').2 b hdl
  have hsum : ∀ i, ((∑ c, b.ry i c : ℕ) : ℝ) < X.L.b' := by
    intro i
    have h1 : ∑ c, b.ry i c < ∑ _c : Fin (X.r + 1), SegData.P X.p (X.S C0 CE1 CE2) i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => (hD'.1 i c).2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 := hS.kP i
    have h3 : ((∑ c, b.ry i c : ℕ) : ℝ) < (((X.r + 1) * SegData.P X.p (X.S C0 CE1 CE2) i : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h3 ⊢
    linarith
  have hC : ∀ i, (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) =
      (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
    intro i
    have h1 := Nat.div_mul_cancel (hD'.2.2 i).2
    have h2 := (hD'.2.2 i).1
    unfold coarseC
    rw [← Nat.cast_sub h2, ← Nat.cast_mul, h1]
  have hAC : ∀ i, coarseA X.p (X.S C0 CE1 CE2) b i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i := by
    intro i
    have h1 := hS.bTop i
    have h2 := hsum i
    have h3 : (X.L.a : ℝ) ≤ aTop' i := by exact_mod_cast hwin i
    have h4 : (((X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c : ℕ) : ℝ) < aTop' i := by
      push_cast at h2 ⊢
      linarith
    have h5 : (X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c < aTop' i := by exact_mod_cast h4
    unfold coarseA coarseC
    exact Nat.div_le_div_right (by omega)
  have hSG : ∀ i, ((b.sg i : ℕ) : ℝ) ≤ 2 * (X.S C0 CE1 CE2).La *
      ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) →
      b.sg i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i := by
    intro i h
    have hP1 : (1:ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by exact_mod_cast hS.P1 i
    have hPQ : (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
      exact_mod_cast hS.PQ i
    have hQ : (0:ℝ) < (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by linarith
    have hA : ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
      have h1 := Int.floor_le ((((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) /
        (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ))
      have h2 := hS.E0
      have h3 : (((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) ≤
          (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hQ.le
        show (X.L.a : ℝ) - (X.S C0 CE1 CE2).E0 ≤ X.L.a
        linarith
      exact h1.trans h3
    have hLa0 : 0 ≤ (X.S C0 CE1 CE2).La := hF.La0
    have hLa4 : 4 * (X.S C0 CE1 CE2).La < (X.r : ℝ) + 1 := hS.La4
    have hr : (0:ℝ) < (X.r : ℝ) + 1 := by positivity
    have hq0 : 0 ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by positivity
    have e1 : 2 * (X.S C0 CE1 CE2).La * ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) ≤
        2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by linarith)) hr.le
    have e2 : 2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1) ≤
        ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 := by
      rw [div_le_div_iff₀ hr (by norm_num)]
      nlinarith
    have e3 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (X.L.a : ℝ) / 2 := by
      have h0 : ((b.sg i : ℕ) : ℝ) ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 :=
        h.trans (e1.trans e2)
      calc ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
          ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 * (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) :=
            mul_le_mul h0 hPQ (by linarith) (by positivity)
        _ = (X.L.a : ℝ) / 2 := by field_simp
    have e4 : (X.L.a : ℝ) - X.L.b' < (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
      have h1 := hsum i
      have h2 : (X.L.a : ℝ) ≤ aTop' i := by exact_mod_cast hwin i
      linarith
    have e5 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) <
        (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
      rw [hC i]
      linarith
    have e6 : ((b.sg i : ℕ) : ℝ) < (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) :=
      lt_of_mul_lt_mul_right e5 (by linarith)
    exact_mod_cast e6.le
  refine ⟨⟨⟨hD', hk.2.1, fun i hi => ?_, hk.2.2.2⟩, hdl⟩, ?_⟩
  · obtain ⟨h1, h2, _, h4, h5⟩ := hk.2.2.1 i hi
    exact ⟨h1, h2, hSG i h5, h4, h5⟩
  · have hx' := (mem_lv aTop b x).mp hx
    refine (mem_lv aTop' b x).mpr ⟨fun i => ⟨(hx'.1 i).1, ?_⟩, hx'.2⟩
    exact (hx'.1 i).1.trans (((hk.2.1 _ (uTop_ge i)).1).trans (hAC _))

theorem restFree_proved (hS : SegFacts C0 CE1 CE2 X) : RestFree C0 CE1 CE2 X := fun dl _ aTop ha aTop' ha' =>
  Finset.Subset.antisymm (idx_sub hS dl aTop aTop' ha ha') (idx_sub hS dl aTop' aTop ha' ha)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusAOf
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def RestPlusAW (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : Prop :=
  Formalism.GM.M.goodCount p (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
            (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D * dXi r (G.B - jp) ≤
    Formalism.GM.M.goodCount p (bePhi p (r := r) G j jp) (Ljj p (r := r) G j jp) D

theorem plusA_of (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) (h : RestPlusAW p (r := r) G j jp D) :
    Formalism.GM.M.bad p (bePhi p (r := r) G j jp) (Ljj p (r := r) G j jp) D ≤ badY p (r := r) G j jp D * dXi r (G.B - jp) := by
  have h1 := finrank_Ljj_le p (r := r) G j jp
  have hY : Module.finrank ℤ_[p] (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) = dimY p (r := r) G j jp :=
    Formalism.CountingSumsFrames.finrank_lattice _ _ inf_le_left
  unfold badY
  simp only [Formalism.GM.M.bad]
  rw [hY, Nat.sub_mul]
  unfold RestPlusAW at h
  omega

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestPlusAWI (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    RestPlusAW X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 ⌊D1r C0 CE1 CE2 X CM⌋

theorem restPlusA_of (CM : ℝ) (h : RestPlusAWI C0 CE1 CE2 X CM) : RestPlusA C0 CE1 CE2 X CM := by
  intro dl hdl aTop ha x hx
  exact plusA_of X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 _ (h dl hdl aTop ha x hx)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

