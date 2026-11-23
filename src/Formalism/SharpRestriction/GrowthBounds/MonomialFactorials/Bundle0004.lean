module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CoarseCLower
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

structure SegFacts (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : Prop where
  hF : HIFacts C0 X
  kP : ∀ i, ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.b'
  P1 : ∀ i, 1 ≤ (X.S C0 CE1 CE2).P X.p i
  PQ : ∀ i, (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).Qj X.p
  La4 : 4 * X.L.La C0 < (X.r : ℝ) + 1
  E0 : 0 ≤ (X.S C0 CE1 CE2).E0
  bTop : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ 5 / 2 * X.L.b'
  kb : ((X.r : ℝ) + 1) * X.L.b' ≤ (X.L.a : ℝ) / 4
  Y1 : 1 ≤ X.L.Y
  xa0 : 0 ≤ X.xa
  xa : X.xa ≤ 2 * X.L.J0 C0

theorem segFacts {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hCb : 1 ≤ Cb) (hCD : 0 ≤ CD) (hCE1 : 0 ≤ CE1)
    (hCE2 : 0 ≤ CE2) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : SegFacts C0 CE1 CE2 X := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X (by linarith) hH
  obtain ⟨h0, -, hxa0, hxa, -, -, -, -, -, -⟩ := hH
  obtain ⟨hY, hpk, ⟨s0, hs0, -⟩, -, hseg, hN1, hm, hLa8, hb0, hbl, hbh, h12, hbw, hYb, hk2, hlog, hde, hpa, hCk,
    hband, hccl0, hccl1, hDLP, hcs, hbig⟩ := h0
  have hk : X.L.k = (X.L.m : ℝ) + 1 := rfl
  have hp25 := p25 hF
  have hp1 : 1 ≤ X.L.p := by
    have : (1 : ℝ) ≤ (X.L.p : ℝ) := by linarith
    exact_mod_cast this
  have hN : (1 : ℝ) ≤ X.L.N := by
    have : 1 ≤ X.L.TT.card := Finset.card_pos.2 ⟨s0, hs0⟩
    show (1 : ℝ) ≤ (X.L.TT.card : ℝ)
    exact_mod_cast this
  have hQ1 : (1 : ℝ) ≤ X.L.Q := by
    show (1 : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'
    exact one_le_pow₀ (by linarith)
  have hk1 : (1 : ℝ) ≤ X.L.k := by rw [hk]; have : (0 : ℝ) ≤ X.L.m := Nat.cast_nonneg _; linarith
  have hlogb : 0 ≤ Real.logb X.L.p X.L.a := Real.logb_nonneg (by linarith) hF.a1
  have hDLP0 : 0 ≤ X.L.DLP := by
    refine le_trans ?_ hDLP
    have : (0 : ℝ) ≤ (X.L.N1 : ℝ) ^ 5 + X.L.k ^ 3 := by positivity
    have : 0 ≤ X.L.N := by linarith
    positivity
  have hM : (1 : ℝ) ≤ X.L.cs + X.L.N * X.L.ccl + X.L.n' * X.L.ccl := by
    have h1 : 0 ≤ X.L.N * X.L.ccl := mul_nonneg (by linarith) hccl0
    have h2 : 0 ≤ (X.L.n' : ℝ) * X.L.ccl := mul_nonneg (Nat.cast_nonneg _) hccl0
    linarith
  have hkQ : X.L.k * X.L.Q ≤ X.L.b' := by
    refine le_trans ?_ hbig
    have e1 : X.L.k ≤ X.L.k ^ 3 := le_self_pow₀ hk1 (by norm_num)
    have e2 : X.L.Q ≤ X.L.Q ^ 4 := le_self_pow₀ hQ1 (by norm_num)
    calc X.L.k * X.L.Q = 1 * X.L.k * 1 * X.L.Q * 1 * 1 := by ring
      _ ≤ Cb * X.L.k ^ 3 * X.L.N * X.L.Q ^ 4 * (X.L.cs + X.L.N * X.L.ccl + X.L.n' * X.L.ccl) * X.L.Y := by
          gcongr
  have hPQ : ∀ i, (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).Qj X.p := fun i =>
    Nat.pow_le_pow_right (lt_of_lt_of_le zero_lt_one hp1) (Nat.sub_le _ _)
  have hQj : ((X.S C0 CE1 CE2).Qj X.p : ℝ) ≤ X.L.Q := by
    show ((X.L.p ^ segG X.L.TT X.j : ℕ) : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'
    push_cast
    exact pow_le_pow_right₀ (by exact_mod_cast hp1) (hseg X.j).1
  have hE0 : 0 ≤ (X.S C0 CE1 CE2).E0 := by
    show 0 ≤ errorTermBound CE1 CE2 X.L.p X.L.k X.L.N1 X.L.Q X.L.c X.L.a X.L.b' (X.L.La C0)
    unfold errorTermBound
    have h1 := hF.La0
    have h2 := hF.b0.le
    have h3 : (0 : ℝ) ≤ X.L.k := by linarith
    have h4 : (0 : ℝ) ≤ X.L.Q := by linarith
    positivity
  refine ⟨hF, fun i => ?_, fun i => Nat.one_le_pow _ _ (lt_of_lt_of_le zero_lt_one hp1), hPQ, ?_, hE0, fun i => ?_, ?_, hY, hxa0, hxa⟩
  · have h1 : ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.Q :=
      le_trans (by exact_mod_cast hPQ i) hQj
    have h2 : X.L.k * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.b' :=
      le_trans (mul_le_mul_of_nonneg_left h1 (by linarith)) hkQ
    exact h2
  · have hYb2 : 2 ≤ X.L.Yb := le_trans hCYb hYb
    have : 4 * X.L.La C0 ≤ 2 * X.L.Yb * X.L.N * X.L.La C0 := by
      have h0 := hF.La0
      have hYN : 2 ≤ X.L.Yb * X.L.N := by nlinarith only [hYb2, hN]
      have := mul_le_mul_of_nonneg_right hYN h0
      linarith only [this]
    have h2 : 4 * X.L.La C0 < X.L.k := by linarith
    exact h2
  · exact hF.bT_le _ (segPos_mem X.L.TT X.j i)
  · have h1 := hF.b_lt
    have h2 : ((X.r : ℝ) + 1) ^ 2 ≤ (X.L.p : ℝ) := hF.p_ge
    have hm4 : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
    have hb := hF.b0
    have h4 : 4 * ((X.L.m : ℝ) + 1) ≤ (X.L.p : ℝ) := by nlinarith only [h2, hm4]
    have h5 := mul_le_mul_of_nonneg_right h4 hb.le
    have h3 : ((X.L.m : ℝ) + 1) * X.L.b' ≤ (X.L.a : ℝ) / 4 := by linarith only [h5, h1]
    exact h3

section Coarse

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem coarseC_lower (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (hD : DigitsOK X.p (X.S C0 CE1 CE2) aTop b)
    (i : Fin X.s) :
    (aTop i : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤
      (coarseC X.p (X.S C0 CE1 CE2) aTop b i : ℝ) * ((X.S C0 CE1 CE2).P X.p i : ℝ) := by
  set P := (X.S C0 CE1 CE2).P X.p i
  have hP : 1 ≤ P := hS.P1 i
  obtain ⟨h1, -, h3⟩ := hD
  obtain ⟨hle, hdvd⟩ := h3 i
  have e : coarseC X.p (X.S C0 CE1 CE2) aTop b i * P = aTop i - ∑ c, b.ry i c := Nat.div_mul_cancel hdvd
  have hρ : ∑ c, b.ry i c ≤ (X.r + 1) * P := by
    calc ∑ c, b.ry i c ≤ ∑ _c : Fin (X.r + 1), P := Finset.sum_le_sum fun c _ => (h1 i c).2.le
      _ = (X.r + 1) * P := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have e2 : ((coarseC X.p (X.S C0 CE1 CE2) aTop b i : ℕ) : ℝ) * (P : ℝ) = (aTop i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, e, Nat.cast_sub hle]
  rw [e2]
  have : ((∑ c, b.ry i c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by exact_mod_cast hρ
  linarith

theorem coarseA_upper (b : SegBlock X.s X.r) (i : Fin X.s) :
    (coarseA X.p (X.S C0 CE1 CE2) b i : ℝ) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ 5 / 2 * X.L.b' := by
  have h1 : coarseA X.p (X.S C0 CE1 CE2) b i * (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).bTop i :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have h2 : ((coarseA X.p (X.S C0 CE1 CE2) b i * (X.S C0 CE1 CE2).P X.p i : ℕ) : ℝ) ≤ ((X.S C0 CE1 CE2).bTop i : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  exact h2.trans (hS.bTop i)

theorem win_ge (aTop : Fin X.s → ℕ) (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (i : Fin X.s) :
    (X.L.a : ℝ) ≤ aTop i := by
  have := (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hT i)).1
  exact_mod_cast this

end Coarse

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DegFactNeZero
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.ProjS

theorem exists_scal (p : ℕ) [hp : Fact p.Prime] (m Mx : ℕ) (hm : m ≠ 0) (h : padicValNat p m ≤ Mx) :
    ∃ c : ℤ_[p], (c : ℚ_[p]) * (m : ℚ_[p]) = (p : ℚ_[p]) ^ Mx := by
  have hm' : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm
  have hn : ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hm', Padic.valuation_natCast, Nat.padicValNat_def]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  refine ⟨Padic.lift ((p : ℚ_[p]) ^ Mx / m) ?_, ?_⟩
  · rw [norm_div, norm_pow, Padic.norm_p, hn, div_le_one (zpow_pos hp0 _), inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hp1 (by omega)
  · show (p : ℚ_[p]) ^ Mx / m * m = _
    field_simp

section Block

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def expU (a : ℕ) : ℕ := (G.T.t + 1) * ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊

def expM : ℕ := (levels G).sup fun l => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2)

theorem lvC_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : lvC (r := r) G j jp ≠ 0 := by
  unfold lvC
  refine mul_ne_zero (pow_ne_zero 2 (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _)
    (Nat.factorial_ne_zero _))) (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero ?_
      (Nat.factorial_ne_zero _)) (mul_ne_zero ?_ (Nat.factorial_ne_zero _)))
  · exact (Nat.choose_pos (by omega)).ne'
  · exact (Nat.choose_pos (by omega)).ne'

theorem degFact_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : degFact G j jp ≠ 0 := by
  unfold degFact
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)

def nLv (D : ℤ) (l : (Fin G.T.t → ℕ) × ℕ) : ℕ :=
  goodCount p (bejj p (r := r) G l.1 l.2) (Ljj p (r := r) G l.1 l.2) D

theorem nLv_mem (D : ℤ) (l : (Fin G.T.t → ℕ) × ℕ) :
    ∃ x y : Fin (nLv p (r := r) G D l) → MvPolynomial (M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G l.1 l.2) ∧ (∀ i, y i ∈ Ljj p (r := r) G l.1 l.2) ∧
      ∀ i j, fockK (G.phiAll p (r := r) l.1 l.2 (x i)) (y j) =
        (if i = j then (p : ℚ_[p]) ^ D else 0) * (degFact G l.1 l.2 : ℚ_[p]) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p (bejj p (r := r) G l.1 l.2) (Ljj p (r := r) G l.1 l.2) D
  refine ⟨x, y, hx, hy, fun i j => ?_⟩
  have hd : (degFact G l.1 l.2 : ℚ_[p]) ≠ 0 := by exact_mod_cast degFact_ne_zero G _ _
  have h := hxy i j
  unfold bejj at h
  rw [div_eq_iff hd] at h
  exact h

theorem blkZ_gen (hB : G.BlockOK) (hr : 1 ≤ r) (U Mx : ℕ)
    (hLL : ∀ x ∈ G.PSZ p (r := r), ((p : ℚ_[p]) ^ U) • x ∈ G.SSZ p (r := r))
    (hM : ∀ l ∈ levels G, padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) ≤ Mx) (D : ℤ) :
    ∃ (n : ℕ) (x y : Fin n → MvPolynomial (M.BVar N r G.T.t) ℚ_[p]),
      (∀ i, x i ∈ G.SSZ p (r := r)) ∧ (∀ i, y i ∈ G.SSZ p (r := r)) ∧
      (∀ i j, fockK (x i) (y j) =
        if i = j then (p : ℚ_[p]) ^ (D + 2 * (U : ℤ) + (Mx : ℤ)) else 0) ∧
      ∑ l ∈ levels G, Module.finrank ℤ_[p] (Ljj p (r := r) G l.1 l.2) ≤
        n + ∑ l ∈ levels G, badLvl p (r := r) G l.1 l.2 D := by
  classical
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hw := fun l : (Fin G.T.t → ℕ) × ℕ => nLv_mem p (r := r) G D l
  choose u v hu hv huv using hw
  have hsc : ∀ l : ↥(levels G), ∃ c : ℤ_[p],
      (c : ℚ_[p]) * ((lvC (r := r) G l.1.1 l.1.2 * degFact G l.1.1 l.1.2 : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ Mx := by
    intro l
    exact exists_scal p _ Mx (mul_ne_zero (lvC_ne_zero G _ _) (degFact_ne_zero G _ _)) (hM l.1 l.2)
  choose sc hsc' using hsc
  have hok : ∀ l : ↥(levels G), G.LevelOK l.1.1 l.1.2 := fun l => (Finset.mem_filter.1 l.2).2
  let I := Σ l : ↥(levels G), Fin (nLv p (r := r) G D l.1)
  let Xf : I → MvPolynomial (M.BVar N r G.T.t) ℚ_[p] := fun a => ((p : ℚ_[p]) ^ U) • Th p G a.1.1.1 a.1.1.2 (v a.1.1 a.2)
  let Yf : I → MvPolynomial (M.BVar N r G.T.t) ℚ_[p] := fun a =>
    sc a.1 • (((p : ℚ_[p]) ^ U) • Th p G a.1.1.1 a.1.1.2 (u a.1.1 a.2))
  have hX : ∀ a, Xf a ∈ G.SSZ p (r := r) := fun a => hLL _ (Th_mem_PSZ p G _ _ (hok a.1) _ (hv _ _))
  have hY : ∀ a, Yf a ∈ G.SSZ p (r := r) := fun a =>
    Submodule.smul_mem _ _ (hLL _ (Th_mem_PSZ p G _ _ (hok a.1) _ (hu _ _)))
  have hXY : ∀ a b : I, fockK (Xf a) (Yf b) = if a = b then (p : ℚ_[p]) ^ (D + 2 * (U : ℤ) + (Mx : ℤ)) else 0 := by
    rintro ⟨l, i⟩ ⟨l', k⟩
    simp only [Xf, Yf]
    rw [zsmul_eq, fockK_smul_left, fockK_smul_right, fockK_smul_right]
    by_cases hll : l = l'
    · subst hll
      rw [Th_fock p G hB hr _ _ (hok l) _ _ (hv _ _) (hu _ _), fockK_symm]
      have h1 := huv l.1 k i
      have h2 := hsc' l
      push_cast at h2
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl] at h1
        rw [h1, if_pos rfl]
        rw [zpow_add₀ hp0, zpow_add₀ hp0, zpow_natCast, ← h2, two_mul, zpow_add₀ hp0, zpow_natCast]
        ring
      · rw [if_neg (fun h => hik h.symm)] at h1
        rw [h1, if_neg]
        · ring
        · intro h
          rw [Sigma.mk.inj_iff] at h
          exact hik (eq_of_heq h.2)
    · have hne : (l.1.1, l.1.2) ≠ (l'.1.1, l'.1.2) := by
        intro h
        exact hll (Subtype.ext h)
      rw [Th_orth p G hB hr _ _ _ _ (hok l) (hok l') hne _ _ (hv _ _) (hu _ _), if_neg]
      · ring
      · intro h
        rw [Sigma.mk.inj_iff] at h
        exact hll h.1
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => Xf (e.symm i), fun i => Yf (e.symm i), fun i => hX _, fun i => hY _, ?_, ?_⟩
  · intro i j
    rw [hXY]
    simp only [e.symm.injective.eq_iff]
  · have hc : Fintype.card I = ∑ l ∈ levels G, nLv p (r := r) G D l := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact Finset.sum_coe_sort (levels G) (nLv p (r := r) G D)
    rw [hc, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun l _ => ?_
    unfold badLvl bad nLv
    exact le_add_tsub

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LettersExt
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Letters

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem letters_ext {N : ℕ} (L L' : Formalism.GM.M.Letters N) (h1 : L.vec = L'.vec) (h2 : L.deg = L'.deg) : L = L' := by
  cases L; cases L'; simp_all

theorem uTop_inj : Function.Injective (uTop (X.S C0 CE1 CE2)) := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [uTop] at h'
  exact Fin.ext (by omega)

abbrev lLL (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) : Formalism.GM.M.Letters (2 * X.s + 1) :=
  (gB C0 CE1 CE2 X aTop 0 b).lettersAt x.1 x.2

abbrev gT (b : SegBlock X.s X.r) : Formalism.GM.M.TieData := (gB C0 CE1 CE2 X (fun _ => 0) 0 b).T

theorem deg_eta (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) :
    (lLL C0 CE1 CE2 X aTop b x).deg q = coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i) - x.1 i := by
  have hi := i.2
  simp only [SegData.t] at hi
  simp only [lLL, Formalism.GM.M.BlockData.lettersAt, gB, gmB, gmL, gmT, blockData, BlockData.withMargin, blockBase, segChain, segTies]
  have h1 : (q : ℕ) ≠ 2 * X.s := by omega
  have hodd : ¬ (q : ℕ) % 2 = 0 := by omega
  have htop : topOf q h1 = uTop (X.S C0 CE1 CE2) i := Fin.ext (by simp only [topOf, uTop]; omega)
  have hnl : ¬ ((uTop (X.S C0 CE1 CE2) i : ℕ) < (X.S C0 CE1 CE2).sigma) := by simp only [uTop]; omega
  have hu : ¬ q = ⟨2 * X.s, by omega⟩ := by
    intro h
    exact h1 (by rw [h])
  rw [dif_neg h1, if_neg hodd, htop, if_neg hnl]
  simp only [hu, if_false, Nat.sub_zero]
  congr 1
  simp only [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  apply Eq.trans (Finset.sum_eq_single i ?_ ?_)
  · exact if_pos (Or.inr (show (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 from hq))
  · intro j _ hj
    have hj' : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
    apply if_neg
    show ¬ ((q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (j : ℕ)) ∨ (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (j : ℕ)) + 1)
    omega
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem deg_other (aTop aTop' : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X)
    (hag : ∀ l : Fin X.s, (l : ℕ) < (X.S C0 CE1 CE2).sigma → aTop l = aTop' l)
    (q : Fin (2 * X.s + 1)) (hq : ¬ ∃ i : Fin (X.S C0 CE1 CE2).t, 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 = (q : ℕ)) :
    (lLL C0 CE1 CE2 X aTop b x).deg q = (lLL C0 CE1 CE2 X aTop' b x).deg q := by
  have hLL : (gB C0 CE1 CE2 X aTop 0 b).LL.deg q = (gB C0 CE1 CE2 X aTop' 0 b).LL.deg q := by
    simp only [gB, gmB, gmL, blockData, BlockData.withMargin, blockBase, segChain]
    by_cases h : (q : ℕ) = 2 * X.s
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h]
      have hv : ((topOf q h : Fin X.s) : ℕ) = (q : ℕ) / 2 := rfl
      have hlt : (q : ℕ) / 2 < X.s := by
        have := (topOf q h).2
        omega
      split_ifs with h2 h3 h3
      · rfl
      · rfl
      · simp only [coarseC]
        rw [hag _ h3]
      · exfalso
        apply hq
        refine ⟨⟨(q : ℕ) / 2 - (X.S C0 CE1 CE2).sigma, ?_⟩, ?_⟩
        · simp only [SegData.t]
          omega
        · simp only
          omega
  simp only [lLL, Formalism.GM.M.BlockData.lettersAt]
  rw [hLL]
  rfl

theorem lLL_ovr (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    lLL C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x =
      (lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b)
        (fun i : Fin (X.S C0 CE1 CE2).t =>
          (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
  apply letters_ext
  · rfl
  · funext q
    simp only [Formalism.GM.M.Letters.setTies]
    split_ifs with h
    · have hc := Classical.choose_spec h
      have hp : (gT C0 CE1 CE2 X b).pos (Classical.choose h) = 2 * ((X.S C0 CE1 CE2).sigma + ((Classical.choose h : Fin (X.S C0 CE1 CE2).t) : ℕ)) := rfl
      have hjq : (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + ((Classical.choose h : Fin (X.S C0 CE1 CE2).t) : ℕ)) + 1 := by
        omega
      rw [deg_eta C0 CE1 CE2 X _ b x _ q hjq]
      have he : ∃ i, uTop (X.S C0 CE1 CE2) i = uTop (X.S C0 CE1 CE2) (Classical.choose h) := ⟨_, rfl⟩
      have hov : ovr (uTop (X.S C0 CE1 CE2)) a n (uTop (X.S C0 CE1 CE2) (Classical.choose h)) = n (Classical.choose h) := by
        simp only [ovr, dif_pos he]
        rw [uTop_inj C0 CE1 CE2 X (Classical.choose_spec he)]
      simp only [coarseC, hov]
      rfl
    · rw [deg_other C0 CE1 CE2 X _ a b x ?_ q ?_]
      · intro l hl
        have hne : ¬ ∃ i, uTop (X.S C0 CE1 CE2) i = l := by
          rintro ⟨i, rfl⟩
          simp only [uTop] at hl
          omega
        simp only [ovr, dif_neg hne]
      · rintro ⟨i, hi⟩
        exact h ⟨i, hi⟩

end Letters

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

