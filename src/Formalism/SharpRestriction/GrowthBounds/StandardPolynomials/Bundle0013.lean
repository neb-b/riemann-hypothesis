module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0010
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoDChain
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXNum
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXPH
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXSum
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0012

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColTop
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.ColumnSystems.Pf.Col Formalism.MainNotions.ColumnSystems.Pf.ColF Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

theorem col_lamS_vec {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X} (L : LvDat C0 CE1 CE2 mu X β)
    (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1)) : (lamS X j a.succ).2 = (L.LL j).vec a := by
  show _ = decide ((a : ℕ) % 2 = 0)
  by_cases h : (a : ℕ) < 2 * segS X.TT j
  · rw [lamS_succ_lt X j a h]
  · rw [lamS_succ_ge X j a h]
    have : (a : ℕ) = 2 * segS X.TT j := by have := a.2; omega
    simp [this]

theorem column_kappa_nonneg (X : Loc) : 0 ≤ ka1 X := by
  unfold ka1 Loc.k Loc.Q
  positivity

theorem colsAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hNum : ColumnNumericsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hS hD hH hC mm hmm n hn1 hnc β hβ L j y hy
  obtain ⟨hnum1, hnum2⟩ := hNum X hD hH hC mm hmm n hn1 hnc j (β j) (hβ j)
  have h2 : 2 ≤ numSeg X.TT := hH.1.2.2.2.1
  have hG : segG X.TT j ≤ X.G' := (hH.1.2.2.2.2.1 j).1
  have hs : segS X.TT j ≤ X.N1 := (hH.1.2.2.2.2.1 j).2
  have hN : 2 * X.N1 + 2 ≤ X.m := hH.1.2.2.2.2.2.2.1
  have hm : 2 * segS X.TT j + 1 < X.m := by omega
  have hn' : 1 ≤ X.n' := by have := hD.2.2.1; omega
  have hp : 0 < X.p := hD.1.pos
  have h := ph_seg L j y hy (hβ j) hnum1 hnum2 hm
  have hvec := col_lamS_vec L j
  have hmu : 0 ≤ mm + (n : ℝ) * ka1 X := by
    have h1 : 0 ≤ mm := by
      rcases hmm with h | h
      · rw [h]
      · rw [h]; positivity
    have h3 := column_kappa_nonneg X
    positivity
  exact ⟨{
    ι := ↥(colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
    fin := inferInstance
    Kc := fun c => Kcol (KK O) y.1.1.mu c.1 (2 * segS X.TT j + 1) (y.1.2 c.1)
    dK := fun c => dKS X j y.1.1.mu c.1
    pl := fun c => plS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j c.1
    fC := fun c => fCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu O y.1.2 c.1
    oC := fun c => oCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu c.1
    dgC := fun c => dgCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu c.1
    a0 := (a0Z C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).toNat
    KInt := fun c => colKInt y.1.1.mu c.1 _
    KPol := fun c => colKPol j y.1.1.mu c.1 _
    digit_le_one := fun c i => by unfold dKS; split_ifs <;> omega
    dKsum := fun i => by
      rw [Finset.sum_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu) (fun c => dKS X j y.1.1.mu c i)]
      exact dKsum_seg L j y h i
    Kprod := by
      rw [Finset.prod_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
        (fun c => Kcol (KK O) y.1.1.mu c (2 * segS X.TT j + 1) (y.1.2 c))]
      exact Kprod_seg L j y (KK O)
    facC := fun c => colFac j y.1.1.mu y.1.2 S hS hn' h2 h hvec c.1
    homC := fun c => colHomC j y.1.1.mu h (fun a => (hvec a).symm) c.1 _
    fPol := fun c => colFPol j y.1.1.mu h2 y.1.2 c.1
    polC := fun c => colPolC j y.1.1.mu h c.1 _
    plQ := fun c l => colPlQ j hp h2 hG c.1 l
    dgCQ := fun c l => colDgQ j y.1.1.mu hp h2 hG c.1 l
    dgCY := fun c j' => colDgY j y.1.1.mu c.1 j'
    a0le := by
      have h0 : 0 ≤ a0Z C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j := sub_nonneg.2 hnum1
      rw [Int.toNat_of_nonneg h0]
      unfold a0Z
      rw [sub_add_cancel]
      have h1 : ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋ ≤
          ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ)⌋ := Int.floor_le_floor (by linarith)
      rwa [Int.floor_intCast] at h1
    plSum := by
      rw [Finset.sum_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
        (fun c => plS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j c)]
      exact plSum_seg L j y h
    oSum := by
      rw [Finset.sum_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
        (fun c => oCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu c)]
      exact oSum_seg L j y h }⟩

theorem restCols : RestCols :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => colsAt_of h) column_numerics_holds

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoDScalLast
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Io

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O] (β : GlobalTheory X) (j : Fin (numSeg X.TT))

theorem ioD_X (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioD ioA
  exact aeval_X _ _

theorem ioD_scal (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.castSucc l, bb))) =
      MvPolynomial.X ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !bb), 0) ^
        (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  rw [ioD_X]
  have hl : ((Fin.castSucc l : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) < (X.seg C0 CE1 CE2 j).t := l.2
  simp only [symVar, symLev]
  rw [dite_eq_left hl, dite_eq_left hl]
  rfl

theorem ioD_scalLast (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t, bb))) =
      MvPolynomial.X ((topEnd X j, !bb), 0) := by
  rw [ioD_X]
  have hl : ¬ ((Fin.last (BDk C0 CE1 CE2 mu X β j).T.t : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) <
      (X.seg C0 CE1 CE2 j).t := lt_irrefl _
  simp only [symVar, symLev]
  rw [dite_eq_right hl, dite_eq_right hl, pow_one]

theorem ioD_odd (i : Fin (segS X.TT j)) (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * i + e)
    (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topOdd X j i, decide (e = 0)), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i := by
  rw [ioD_X]
  have hi := i.2
  have hl : (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dite_eq_left hl, dite_eq_left hl]
  have e1 : (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by simp only; omega)
  have e2 : decide ((a : ℕ) % 2 = 0) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e1, e2]

theorem ioD_end (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * segS X.TT j + e) (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topEnd X j, decide (e = 0)), c.succ) := by
  rw [ioD_X]
  have hl : ¬ (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dite_eq_right hl, dite_eq_right hl, pow_one]
  have e2 : decide ((a : ℕ) = 2 * segS X.TT j) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e2]

theorem ioD_Ehat (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) l) =
      EhatT O X (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l)) ((X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l)) := by
  unfold BlockData.Ehat EhatT scalZ scalS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_mul, map_sum, ioD_scal, ioD_scal]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have hu := (uTop (X.seg C0 CE1 CE2 j) l).2
  rw [map_mul, ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 0 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ)) (2 * segS X.TT j + 1) = _
      omega),
    ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 1 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ) + 1) (2 * segS X.TT j + 1) = _
      omega)]
  rfl

theorem ioD_Eplus :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) = hTop O X (topEnd X j) := by
  unfold hTop hKey
  rw [Fin.sum_univ_succ]
  unfold BlockData.Eplus scalZ scalS xiVar
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_mul, map_sum, ioD_scalLast, ioD_scalLast]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, ioD_end β j 0 (by omega) _ (by rfl), ioD_end β j 1 (by omega) _ (by rfl)]
  rfl

end Io

theorem uTop_sum {s : ℕ} {M : Type} [AddCommMonoid M] (S : SegData s) (F : Fin s → M) :
    ∑ l : Fin S.t, F (uTop S l) = ∑ i : Fin s, if (i : ℕ) < S.sigma then 0 else F i := by
  classical
  have h1 : ∑ i : Fin s, (if (i : ℕ) < S.sigma then 0 else F i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin s => ¬ (i : ℕ) < S.sigma), F i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < S.sigma <;> simp [h]
  rw [h1]
  refine Finset.sum_bij (fun l _ => uTop S l) ?_ ?_ ?_ ?_
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uTop]
    omega
  · intro l _ l' _ h
    have := congrArg Fin.val h
    simp only [uTop] at this
    exact Fin.ext (by omega)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨(i : ℕ) - S.sigma, ?_⟩, Finset.mem_univ _, ?_⟩
    · have := i.2
      unfold SegData.t
      omega
    · apply Fin.ext
      simp only [uTop]
      omega
  · intro l _
    rfl

end Formalism.MainNotions.ColumnSystems.Pf
end
end

