module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
public import Formalism.MahlerMeasure.MahlerMeasureProofs.FockBlocks
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.FinalLL

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BoxOfFibres
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Comb

variable {s t : ℕ} (u : Fin t → Fin s)


open Classical in
def ovr (a : Fin s → ℕ) (n : Fin t → ℕ) : Fin s → ℕ :=
  fun l => if h : ∃ i, u i = l then n (Classical.choose h) else a l

theorem ovr_u (hu : Function.Injective u) (a : Fin s → ℕ) (n : Fin t → ℕ) (i : Fin t) : ovr u a n (u i) = n i := by
  unfold ovr
  have h : ∃ i', u i' = u i := ⟨i, rfl⟩
  rw [dite_eq_left h]
  exact congrArg n (hu (Classical.choose_spec h))

theorem ovr_not (a : Fin s → ℕ) (n : Fin t → ℕ) (l : Fin s) (h : ¬ ∃ i, u i = l) : ovr u a n l = a l := dif_neg h

theorem ovr_ovr (hu : Function.Injective u) (a : Fin s → ℕ) (n : Fin t → ℕ) :
    ovr u (ovr u a n) (fun i => a (u i)) = a := by
  funext l
  by_cases h : ∃ i, u i = l
  · obtain ⟨i, rfl⟩ := h
    exact ovr_u u hu _ _ i
  · rw [ovr_not u _ _ l h, ovr_not u _ _ l h]

theorem ovr_mem (hu : Function.Injective u) (W : Fin s → Finset ℕ) (a : Fin s → ℕ) (n : Fin t → ℕ)
    (ha : a ∈ Fintype.piFinset W) (hn : n ∈ Fintype.piFinset (fun i => W (u i))) :
    ovr u a n ∈ Fintype.piFinset W := by
  rw [Fintype.mem_piFinset] at ha hn ⊢
  intro l
  by_cases h : ∃ i, u i = l
  · obtain ⟨i, rfl⟩ := h
    rw [ovr_u u hu]
    exact hn i
  · rw [ovr_not u _ _ _ h]
    exact ha l

theorem ovr_update (hu : Function.Injective u) (a : Fin s → ℕ) (n : Fin t → ℕ) (i : Fin t) (v : ℕ) :
    Function.update (ovr u a n) (u i) v = ovr u a (Function.update n i v) := by
  funext l
  by_cases h : ∃ j, u j = l
  · obtain ⟨j, rfl⟩ := h
    by_cases hj : j = i
    · subst hj
      simp [ovr_u u hu]
    · rw [Function.update_of_ne (hu.ne hj), ovr_u u hu, ovr_u u hu, Function.update_of_ne hj]
  · have hl : l ≠ u i := fun e => h ⟨i, e.symm⟩
    rw [Function.update_of_ne hl, ovr_not u _ _ l h, ovr_not u _ _ l h]

theorem sum_ovr (hu : Function.Injective u) (W : Fin s → Finset ℕ) (F : (Fin s → ℕ) → ℝ) :
    ∑ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), F (ovr u a n) =
      ((Fintype.piFinset (fun i => W (u i))).card : ℝ) * ∑ a ∈ Fintype.piFinset W, F a := by
  calc ∑ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), F (ovr u a n)
      = ∑ q ∈ Fintype.piFinset W ×ˢ Fintype.piFinset (fun i => W (u i)), F (ovr u q.1 q.2) := by
        rw [Finset.sum_product]
    _ = ∑ q ∈ Fintype.piFinset W ×ˢ Fintype.piFinset (fun i => W (u i)), F q.1 := by
        refine Finset.sum_nbij' (fun q => (ovr u q.1 q.2, fun i => q.1 (u i)))
          (fun q => (ovr u q.1 q.2, fun i => q.1 (u i))) ?_ ?_ ?_ ?_ ?_
        · rintro ⟨a, n⟩ hq
          rw [Finset.mem_product] at hq ⊢
          refine ⟨ovr_mem u hu W a n hq.1 hq.2, ?_⟩
          have ha := hq.1
          rw [Fintype.mem_piFinset] at ha ⊢
          exact fun i => ha (u i)
        · rintro ⟨a, n⟩ hq
          rw [Finset.mem_product] at hq ⊢
          refine ⟨ovr_mem u hu W a n hq.1 hq.2, ?_⟩
          have ha := hq.1
          rw [Fintype.mem_piFinset] at ha ⊢
          exact fun i => ha (u i)
        · rintro ⟨a, n⟩ _
          exact Prod.ext (ovr_ovr u hu a n) (funext fun i => ovr_u u hu a n i)
        · rintro ⟨a, n⟩ _
          exact Prod.ext (ovr_ovr u hu a n) (funext fun i => ovr_u u hu a n i)
        · rintro ⟨a, n⟩ _
          rfl
    _ = _ := by
        rw [Finset.sum_product, Finset.mul_sum]
        simp [Finset.sum_const, nsmul_eq_mul]

theorem box_of_fibres (hu : Function.Injective u) (W : Fin s → Finset ℕ) (F : (Fin s → ℕ) → ℝ)
    (G : Fin t → (Fin s → ℕ) → ℝ) (ε : ℝ) (hne : (Fintype.piFinset W).Nonempty)
    (h : ∀ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), F (ovr u a n) ≤
      ε * ∑ i, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), G i (ovr u a n)) :
    ∑ a ∈ Fintype.piFinset W, F a ≤ ε * ∑ i, ∑ a ∈ Fintype.piFinset W, G i a := by
  obtain ⟨a0, ha0⟩ := hne
  have hmem : (fun i => a0 (u i)) ∈ Fintype.piFinset (fun i => W (u i)) := by
    rw [Fintype.mem_piFinset] at ha0 ⊢
    exact fun i => ha0 (u i)
  have hpos : (0 : ℝ) < ((Fintype.piFinset (fun i => W (u i))).card : ℝ) :=
    Nat.cast_pos.2 (Finset.card_pos.2 ⟨_, hmem⟩)
  have hG : ∀ i, ∑ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), G i (ovr u a n) =
      ((Fintype.piFinset (fun i => W (u i))).card : ℝ) * ∑ a ∈ Fintype.piFinset W, G i a :=
    fun i => sum_ovr u hu W (G i)
  have hsum := Finset.sum_le_sum h
  rw [sum_ovr u hu W F, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun i _ => hG i,
    ← Finset.mul_sum, mul_left_comm] at hsum
  exact le_of_mul_le_mul_left hsum hpos

theorem interval_eq (A : Finset ℕ) (hne : A.Nonempty) (hc : ∀ x ∈ A, ∀ y ∈ A, ∀ z, x ≤ z → z ≤ y → z ∈ A) :
    A = (Finset.range (A.sup id - sInf (A : Set ℕ) + 1)).image (fun k => sInf (A : Set ℕ) + 1 * k) := by
  have hmA : sInf (A : Set ℕ) ∈ A := Finset.mem_coe.1 (Nat.sInf_mem (Finset.coe_nonempty.2 hne))
  obtain ⟨M, hM, hMe⟩ := Finset.exists_mem_eq_sup A hne id
  have hle : ∀ x ∈ A, sInf (A : Set ℕ) ≤ x := fun x hx => Nat.sInf_le (Finset.mem_coe.2 hx)
  have hge : ∀ x ∈ A, x ≤ A.sup id := fun x hx => show x ≤ A.sup id from Finset.le_sup (f := id) hx
  ext x
  simp only [Finset.mem_image, Finset.mem_range, one_mul]
  constructor
  · intro hx
    have h1 := hle x hx
    have h2 := hge x hx
    exact ⟨x - sInf (A : Set ℕ), by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    refine hc _ hmA M hM _ (Nat.le_add_right _ _) ?_
    have h3 : A.sup id = M := hMe
    have h4 := hle M hM
    omega

end Comb

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.GoodCountMem
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.ProjS

theorem goodCount_mem (p : ℕ) [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℤ_[p] Vs]
    (be : Vs → Vs → ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ) :
    ∃ x y : Fin (goodCount p be L D) → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0 := by
  set S : Set ℕ := {n | ∃ x y : Fin n → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
    ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0} with hS
  have h0 : (0 : ℕ) ∈ S := ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hmem : sSup S ∈ S := by
    by_cases hb : BddAbove S
    · exact Nat.sSup_mem ⟨0, h0⟩ hb
    · rw [Nat.sSup_of_not_bddAbove hb]; exact h0
  exact hmem

section Lin

variable {k σ : Type} [Field k] {r : ℕ}

theorem harmonicProjection_add (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (y y' : MvPolynomial σ k) :
    tieP w e zv sv o n z (y + y') = tieP w e zv sv o n z y + tieP w e zv sv o n z y' := by
  unfold tieP
  simp only [mul_add, map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem harmonicProjection_smul (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (c : k) (y : MvPolynomial σ k) :
    tieP w e zv sv o n z (c • y) = c • tieP w e zv sv o n z y := by
  unfold tieP
  simp only [mul_smul_comm, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _

end Lin

section Block

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem Pall_add (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    G.Pall p (r := r) j jp (u + v) = G.Pall p (r := r) j jp u + G.Pall p (r := r) j jp v := by
  unfold M.BlockData.Pall
  rw [← harmonicProjection_add]
  congr 1
  induction (List.finRange G.T.t) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons]; rw [ih, harmonicProjection_add]

theorem Pall_smul (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    G.Pall p (r := r) j jp (c • u) = c • G.Pall p (r := r) j jp u := by
  unfold M.BlockData.Pall
  rw [← harmonicProjection_smul]
  congr 1
  induction (List.finRange G.T.t) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons]; rw [ih, harmonicProjection_smul]

def Th (j : Fin G.T.t → ℕ) (jp : ℕ) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p] :=
  (∏ i, G.Ehat p (r := r) i ^ j i) * G.Eplus p (r := r) ^ jp * G.Pall p (r := r) j jp u

theorem Th_add (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    Th p G j jp (u + v) = Th p G j jp u + Th p G j jp v := by
  unfold Th; rw [Pall_add, mul_add]

theorem Th_smul (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    Th p G j jp (c • u) = c • Th p G j jp u := by
  unfold Th; rw [Pall_smul, mul_smul_comm]

theorem Th_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : Th p (r := r) G j jp (0 : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) = 0 := by
  have := Th_smul p (r := r) G j jp 0 0
  simpa using this

theorem zsmul_eq (c : ℤ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) : c • u = (c : ℚ_[p]) • u :=
  (algebraMap_smul ℚ_[p] c u).symm

theorem Th_mem_PSZ (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hu : u ∈ Ljj p (r := r) G j jp) : Th p G j jp u ∈ G.PSZ p (r := r) := by
  unfold Ljj at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, g, hg, rfl⟩ := hx
    apply Submodule.subset_span
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hl, y, hy, g, hg, rfl⟩
  | zero => rw [Th_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Th_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [zsmul_eq, Th_smul, ← zsmul_eq]; exact Submodule.smul_mem _ c hx

def lvC (j : Fin G.T.t → ℕ) (jp : ℕ) : ℕ :=
  ((∏ i, (j i).factorial) * jp.factorial) ^ 2 *
    ((∏ i, (((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
        (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1).choose (j i) *
      (G.T.z i).factorial)) *
    (((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1).choose jp * G.zPlus.factorial))

theorem Th_fock (hB : G.BlockOK) (hr : 1 ≤ r) (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp)
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j jp) :
    fockK (Th p G j jp u) (Th p G j jp v) = (lvC (r := r) G j jp : ℚ_[p]) * fockK u (G.phiAll p (r := r) j jp v) := by
  unfold Ljj at hu hv
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      obtain ⟨y', hy', g', hg', rfl⟩ := hx'
      have h := (fock_block_decomposition p N r G hB hr).2 j jp hl y hy.1 y' hy'.1 g hg g' hg'
      rw [fockK_smul_left, fockK_smul_right] at h
      have hf : ((∏ i, ((j i).factorial : ℚ_[p])) * (jp.factorial : ℚ_[p])) ≠ 0 :=
        mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      unfold Th lvC
      push_cast
      push_cast at h
      have hf2 : (∏ i, ((j i).factorial : ℚ_[p])) ^ 2 * (jp.factorial : ℚ_[p]) ^ 2 ≠ 0 := by
        rw [← mul_pow]; exact pow_ne_zero 2 hf
      field_simp at h
      rw [div_eq_iff hf2] at h
      rw [h]
      ring
    | zero => rw [Th_zero, fockK_zero_right, map_zero, fockK_zero_right, mul_zero]
    | add a b _ _ ha hb => rw [Th_add, fockK_add_right, ha, hb, map_add (f := _), fockK_add_right, mul_add]
    | smul c a _ ha =>
      rw [zsmul_eq, Th_smul, fockK_smul_right, ha, map_smul, fockK_smul_right]; ring
  | zero => rw [Th_zero, fockK_zero_left, fockK_zero_left, mul_zero]
  | add a b _ _ ha hb => rw [Th_add, fockK_add_left, ha, hb, fockK_add_left, mul_add]
  | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_left, ha, fockK_smul_left]; ring

theorem Th_orth (hB : G.BlockOK) (hr : 1 ≤ r) (j j' : Fin G.T.t → ℕ) (jp jp' : ℕ) (hl : G.LevelOK j jp)
    (hl' : G.LevelOK j' jp') (hne : (j, jp) ≠ (j', jp'))
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j' jp') :
    fockK (Th p G j jp u) (Th p G j' jp' v) = 0 := by
  unfold Ljj at hu hv
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      obtain ⟨y', hy', g', hg', rfl⟩ := hx'
      exact (fock_block_decomposition p N r G hB hr).1 j j' jp jp' hl hl' hne y hy.1 y' hy'.1 g hg g' hg'
    | zero => rw [Th_zero, fockK_zero_right]
    | add a b _ _ ha hb => rw [Th_add, fockK_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_right, ha, mul_zero]
  | zero => rw [Th_zero, fockK_zero_left]
  | add a b _ _ ha hb => rw [Th_add, fockK_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_left, ha, mul_zero]

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.KappaZeroNonneg
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem depth_num (Y N s t r L CM C : ℝ) (hY : 1 ≤ Y) (hN : 1 ≤ N) (hs0 : 0 ≤ s) (hs : s ≤ N) (ht0 : 0 ≤ t)
    (ht : t ≤ s) (hr : 0 ≤ r) (hL : 0 ≤ L) (hCM : 0 ≤ CM) (hC : 18 * (1 + CM) + 20 ≤ C) :
    Y * (t * (Y * (3 * (s + 2) * r ^ 2 * L) + CM * (3 * (s + 2) * r ^ 2 * L)) + CM * (3 * (s + 2) * r ^ 2 * L)) +
      10 * (s + 1) * (r + 1) * L ≤ C * Y ^ 2 * N ^ 2 * (r + 1) ^ 2 * L := by
  have hA0 : 0 ≤ 3 * (s + 2) * r ^ 2 * L := by positivity
  have hB0 : 0 ≤ N * (r + 1) ^ 2 * L := by
    have : 0 ≤ N := by linarith
    positivity
  have hA : 3 * (s + 2) * r ^ 2 * L ≤ 9 * (N * (r + 1) ^ 2 * L) := by
    have h1 : s + 2 ≤ 3 * N := by linarith
    have h2 : r ^ 2 ≤ (r + 1) ^ 2 := by nlinarith
    have h3 : (s + 2) * r ^ 2 ≤ (3 * N) * (r + 1) ^ 2 := mul_le_mul h1 h2 (by positivity) (by linarith)
    have h4 := mul_le_mul_of_nonneg_right h3 hL
    linarith
  have htA : t * (3 * (s + 2) * r ^ 2 * L) ≤ N * (9 * (N * (r + 1) ^ 2 * L)) :=
    mul_le_mul (by linarith) hA hA0 (by linarith)
  have k1 := mul_le_mul_of_nonneg_left htA (sq_nonneg Y)
  have hYCM : 0 ≤ Y * CM := mul_nonneg (by linarith) hCM
  have k2 := mul_le_mul_of_nonneg_left htA hYCM
  have k3 := mul_le_mul_of_nonneg_left hA hYCM
  have k4 : 10 * (s + 1) * (r + 1) * L ≤ 20 * (N * (r + 1) ^ 2 * L) := by
    have h1 : s + 1 ≤ 2 * N := by linarith
    have h2 : r + 1 ≤ (r + 1) ^ 2 := by nlinarith
    have h3 : (s + 1) * (r + 1) ≤ (2 * N) * (r + 1) ^ 2 := mul_le_mul h1 h2 (by linarith) (by linarith)
    have h4 := mul_le_mul_of_nonneg_right h3 hL
    linarith
  have hY2 : Y ≤ Y ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left hN (sq_nonneg Y)
  have hYN : Y * N ≤ Y ^ 2 * N := mul_le_mul_of_nonneg_right hY2 (by linarith)
  have hY1 : Y ≤ Y ^ 2 * N := by linarith
  have h1P : 1 ≤ Y ^ 2 * N := by nlinarith
  have hc0 : 0 ≤ CM * (9 * (N * (r + 1) ^ 2 * L)) := mul_nonneg hCM (by linarith)
  have m1 := mul_le_mul_of_nonneg_left hYN hc0
  have m2 := mul_le_mul_of_nonneg_left hY1 hc0
  have m3 := mul_le_mul_of_nonneg_left h1P (by linarith : (0:ℝ) ≤ 20 * (N * (r + 1) ^ 2 * L))
  have hP0 : 0 ≤ Y ^ 2 * N * (N * (r + 1) ^ 2 * L) := mul_nonneg (by linarith) hB0
  have m4 := mul_le_mul_of_nonneg_right (by linarith : 29 + 18 * CM ≤ C) hP0
  linarith [k1, k2, k3, k4, m1, m2, m3, m4]

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem p25 (hF : HIFacts C0 X) : (25 : ℝ) ≤ (X.L.p : ℝ) := by
  have hmR : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
  nlinarith [hF.p_ge]

theorem lgA_ge_one_facts (hF : HIFacts C0 X) : 1 ≤ lgA X.p X.L.a X.r := by
  unfold lgA
  have h : 0 ≤ Real.logb (X.p : ℝ) (8 * (X.L.a : ℝ) + X.r) := by
    unfold Real.logb
    apply div_nonneg
    · have h' := Real.log_natCast_nonneg (8 * X.L.a + X.r)
      push_cast at h'
      exact h'
    · exact Real.log_natCast_nonneg _
  linarith

theorem kap0A_nonneg_of_hiFacts (hF : HIFacts C0 X) : 0 ≤ kappaZeroExponent X.p X.L.a X.Nt X.r := by
  unfold kappaZeroExponent
  have h : 0 ≤ Real.logb (X.p : ℝ) (X.L.a : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  exact mul_nonneg (by positivity) h

theorem restDepth_proved {CYb Cde Ck CD Cb Cc : ℝ} (CM C : ℝ) (hCYb : 1 ≤ CYb) (hCM : 0 ≤ CM)
    (hC : 18 * (1 + CM) + 20 ≤ C) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestDepth C0 CE1 CE2 X CM C := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hN : (1 : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hH.1.2.2.2.2.2.1
  have hs : (X.s : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast (hH.1.2.2.2.2.1 X.j).2
  have ht : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ) := by
    have : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
    exact_mod_cast this
  have hL := lgA_ge_one_facts hF
  have hL0 : 0 ≤ lgA X.p X.L.a X.r := by linarith
  have hk := kap0A_nonneg_of_hiFacts hF
  constructor
  · unfold D1r kapS
    positivity
  · have h := depth_num X.L.Y X.N₁ X.s ((X.S C0 CE1 CE2).t : ℝ) X.r (lgA X.p X.L.a X.r) CM C hY hN (Nat.cast_nonneg _) hs
      (Nat.cast_nonneg _) ht (Nat.cast_nonneg _) hL0 hCM hC
    unfold D1r kapS levelPassageLoss depthD
    linarith

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PadicIntegersEmbeddingMapPrime
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Formalism.MainNotions.G

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem castPow_zero (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) :
    ((p ^ n : ℕ) : O ⧸ (IsLocalRing.maximalIdeal O) ^ n) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ n)) (p ^ n), Nat.cast_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hpm n

def iotaN (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) :
    ℤ_[p] →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ n :=
  RingHom.comp (ZMod.castHom (ringChar.dvd (castPow_zero p O hpm n)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ n))
    (PadicInt.toZModPow n)

theorem iotaN_compat (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp (iotaN p O hpm n) = iotaN p O hpm m := by
  have hz := PadicInt.zmod_cast_comp_toZModPow (p := p) m n hle
  have key : ∀ (f g : ZMod (p ^ n) →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ m), f = g :=
    fun f g => RingHom.ext_zmod f g
  unfold iotaN
  rw [← hz]
  ext x
  simp only [RingHom.comp_apply]
  exact congrArg (fun f => f (PadicInt.toZModPow n x))
    (key ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp
      (ZMod.castHom (ringChar.dvd (castPow_zero p O hpm n)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ n)))
      ((ZMod.castHom (ringChar.dvd (castPow_zero p O hpm m)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ m)).comp
        (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ m)))))

def iota0 (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : ℤ_[p] →+* O :=
  ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal O)).symm : AdicCompletion (IsLocalRing.maximalIdeal O) O →+* O).comp
    (AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal O) (iotaN p O hpm) (fun hle => iotaN_compat p O hpm hle))

theorem padic_integers_embedding_map_prime (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    iota0 p O hpm (p : ℤ_[p]) = (p : O) :=
  map_natCast (iota0 p O hpm) p

theorem padic_integers_embedding_injective (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : Function.Injective (iota0 p O hpm) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hspec := PadicInt.unitCoeff_spec hne
  have h2 := congrArg (iota0 p O hpm) hspec
  rw [hx, map_mul, map_pow, padic_integers_embedding_map_prime] at h2
  have hu : IsUnit (iota0 p O hpm (PadicInt.unitCoeff hne : ℤ_[p])) := (Units.isUnit _).map _
  rcases mul_eq_zero.mp h2.symm with h3 | h3
  · exact hu.ne_zero h3
  · exact hp0 (pow_eq_zero_iff'.mp h3).1

def iotaQ (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : ℚ_[p] →+* KK O :=
  IsFractionRing.lift (A := ℤ_[p]) (K := ℚ_[p]) (g := (algebraMap O (KK O)).comp (iota0 p O hpm))
    ((IsFractionRing.injective O (KK O)).comp (padic_integers_embedding_injective p O hpm hp0))

theorem iotaQ_int (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : ℤ_[p]) :
    iotaQ p O hpm hp0 (x : ℚ_[p]) = algebraMap O (KK O) (iota0 p O hpm x) := by
  unfold iotaQ
  exact IsFractionRing.lift_algebraMap _ x

def iotaX (X : flipOneThree.Inst) : ℚ_[X.p] →+* KK X.O :=
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal X.O) X.O := X.setting.complete
  iotaQ X.p X.O X.setting.p_mem X.setting.p_ne

theorem iotaX_int (X : flipOneThree.Inst) (x : ℤ_[X.p]) :
    ∃ y : X.O, iotaX X (x : ℚ_[X.p]) = algebraMap X.O (KK X.O) y := by
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal X.O) X.O := X.setting.complete
  exact ⟨_, iotaQ_int X.p X.O X.setting.p_mem X.setting.p_ne x⟩

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

