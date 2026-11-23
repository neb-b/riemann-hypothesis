module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix

section pts

theorem toStd_size' (r : ℕ) (g : ℝ) : ∀ (p : C.LPt) (b : ℕ), D.ptSize (D.toStd r g b p) = D.ptSize p := by
  intro p
  induction p with
  | nil => intro b; rfl
  | cons head rest ih =>
    rcases head with ⟨s, t⟩
    intro b
    change s + D.ptSize (D.toStd r g (b + s) rest) = s + D.ptSize rest
    rw [ih]

theorem toStd_ok_iff (r : ℕ) (g : ℝ) (hg : 0 < g) : ∀ (p : C.LPt) (b : ℕ),
    (∀ x ∈ D.toStd r g b p, 1 ≤ x.1 ∧ x.2 ≠ 0) ↔ ∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ≠ 0 := by
  intro p
  induction p with
  | nil => intro b; simp [D.toStd]
  | cons head rest ih =>
    rcases head with ⟨s, t⟩
    intro b
    have hne : ((((g / (2 * Real.pi)) ^ S6.nuBlock r b s : ℝ) : ℂ) * Complex.I ^ (s - 1)) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ Complex.I_ne_zero)
      have : 0 < (g / (2 * Real.pi)) ^ S6.nuBlock r b s := zpow_pos (by positivity) _
      exact_mod_cast this.ne'
    simp only [D.toStd, List.forall_mem_cons, ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, fun ht => h2 (by rw [ht, mul_zero])⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, mul_ne_zero hne h2⟩, h3⟩

theorem isLocPt_toStd_iff (r : ℕ) (g : ℝ) (hg : 0 < g) (p : C.LPt) (b i : ℕ) :
    D.IsLocPt (D.toStd r g b p) i ↔ D.IsLocPt p i := by
  unfold D.IsLocPt
  rw [toStd_ok_iff r g hg p b, toStd_size']

theorem bSt_append_one (κ : ℝ) (h : C.LPt) (c : ℂ) : D.bSt κ (h ++ [(1, c)]) = D.bSt κ h := by
  simp [D.bSt]

theorem bSt_pos' (κ : ℝ) (hκ : 0 < κ) (p : C.LPt) : 0 < D.bSt κ p := by
  unfold D.bSt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
  exact Finset.prod_pos fun m _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _

theorem rd_pos' (E : Type) [Field E] [NumberField E] : 0 < S6.rd E := by
  unfold S6.rd
  refine Real.rpow_pos_of_pos ?_ _
  exact_mod_cast abs_pos.2 (discr_ne_zero E)

end pts

section weights

theorem weight_product_append (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (x : ℕ × ℂ) : ∀ (h : C.LPt) (b : ℕ),
    C.nAux k r GG fr b (h ++ [x]) = C.nAux k r GG fr b h * C.nAux k r GG fr (b + D.ptSize h) [x] := by
  intro h
  induction h with
  | nil => intro b; simp [C.nAux, D.ptSize]
  | cons head rest ih =>
    rcases head with ⟨s, t⟩
    intro b
    simp only [List.cons_append, C.nAux, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc, mul_assoc]

theorem weight_product_indep_of_real_parameter (k r : ℕ) (GG GG' : ℝ) (fr : ℕ → ℕ → ℝ) : ∀ (h : C.LPt) (b : ℕ), 1 ≤ b →
    b + D.ptSize h ≤ r + 1 → C.nAux k r GG fr b h = C.nAux k r GG' fr b h := by
  intro h
  induction h with
  | nil => intro b hb hs; simp [C.nAux]
  | cons head rest ih =>
    rcases head with ⟨s, t⟩
    intro b hb hs
    change b + (s + D.ptSize rest) ≤ r + 1 at hs
    have hrest := ih (b + s) (by omega) (by omega)
    simp only [C.nAux, hrest]
    congr 1
    have : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by
      rintro ⟨h1, h2⟩
      omega
    simp only [ite_eq_right this]

end weights

section det

theorem ptEntry_app_lt (c : ℂ) : ∀ (H : C.LPt) (a b : ℕ), a < D.ptSize H → b < D.ptSize H →
    D.ptEntry (H ++ [(1, c)]) a b = D.ptEntry H a b
  | [], a, b, ha, _ => by simp [D.ptSize] at ha
  | (s, t) :: rest, a, b, ha, hb => by
    simp only [D.ptSize, List.map_cons, List.sum_cons] at ha hb
    simp only [List.cons_append, D.ptEntry]
    by_cases h1 : a < s ∧ b < s
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : s ≤ a ∧ s ≤ b
      · rw [if_pos h2, if_pos h2]
        exact ptEntry_app_lt c rest (a - s) (b - s) (by simp only [D.ptSize]; omega) (by simp only [D.ptSize]; omega)
      · rw [if_neg h2, if_neg h2]

theorem ptEntry_app_last (c : ℂ) : ∀ (H : C.LPt), D.ptEntry (H ++ [(1, c)]) (D.ptSize H) (D.ptSize H) = c := by
  intro H
  induction H with
  | nil => simp [D.ptSize, D.ptEntry]
  | cons head rest ih =>
    rcases head with ⟨s, t⟩
    have hle := Nat.le_add_right s (rest.map Prod.fst).sum
    simpa only [List.cons_append, D.ptEntry, D.ptSize, List.map_cons, List.sum_cons,
      not_lt_of_ge hle, false_and, ite_false, hle, and_self, ite_true, Nat.add_sub_cancel_left] using ih

theorem ptEntry_app_row (c : ℂ) : ∀ (H : C.LPt) (b : ℕ), b < D.ptSize H →
    D.ptEntry (H ++ [(1, c)]) (D.ptSize H) b = 0 := by
  intro H
  induction H with
  | nil => intro b hb; simp [D.ptSize] at hb
  | cons head rest ih =>
    rcases head with ⟨s, t⟩
    intro b hb
    change b < s + D.ptSize rest at hb
    have hle := Nat.le_add_right s (rest.map Prod.fst).sum
    simp only [List.cons_append, D.ptEntry, D.ptSize, List.map_cons, List.sum_cons,
      not_lt_of_ge hle, false_and, ite_false, hle, true_and, Nat.add_sub_cancel_left]
    by_cases hsb : s ≤ b
    · rw [ite_eq_left hsb]
      exact ih (b - s) (by omega)
    · rw [ite_eq_right hsb]

theorem det_ptMatN_app (c : ℂ) (H : C.LPt) (n : ℕ) (hn : D.ptSize H = n) :
    (D.ptMatN (H ++ [(1, c)]) (n + 1)).det = c * (D.ptMatN H n).det ∧
      D.ptMatN (H ++ [(1, c)]) n = D.ptMatN H n := by
  subst hn
  have hsub : (D.ptMatN (H ++ [(1, c)]) (D.ptSize H + 1)).submatrix Fin.castSucc Fin.castSucc =
      D.ptMatN H (D.ptSize H) := by
    ext a b
    simp only [Matrix.submatrix_apply, D.ptMatN, Fin.coe_castSucc]
    exact ptEntry_app_lt c H a b a.isLt b.isLt
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_succ_row _ (Fin.last _), Finset.sum_eq_single (Fin.last _)]
    · simp only [Fin.val_last, Fin.succAbove_last]
      rw [hsub]
      simp only [D.ptMatN, Fin.val_last, ptEntry_app_last]
      simp
    · intro j _ hj
      have hj' : (j : ℕ) < D.ptSize H := by
        have := j.isLt
        have : (j : ℕ) ≠ D.ptSize H := fun h => hj (Fin.ext (by simp [h]))
        omega
      simp [D.ptMatN, ptEntry_app_row c H j hj']
    · simp
  · ext a b
    simp only [D.ptMatN]
    exact ptEntry_app_lt c H a b a.isLt b.isLt

theorem ptG_app (TT : ℝ) (c : ℂ) (H : C.LPt) (n : ℕ) (hn : D.ptSize H = n) :
    D.ptG TT n (H ++ [(1, c)]) = Complex.normSq (D.ptMatN H n).det * (Complex.normSq c - TT) := by
  obtain ⟨h1, h2⟩ := det_ptMatN_app c H n hn
  unfold D.ptG
  rw [h1, h2, Complex.normSq_mul]
  ring

end det

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem lpt_value_nonneg_of_pos_of_size_le (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 < fr b s) :
    ∀ (p : C.LPt) (b : ℕ), 1 ≤ b → b + D.ptSize p ≤ r + 1 → 0 ≤ C.nAux k r GG fr b p := by
  intro p
  induction p with
  | nil => intro b hb hs; simp [C.nAux]
  | cons head rest ih =>
    rcases head with ⟨s, t⟩
    intro b hb hs
    change b + (s + D.ptSize rest) ≤ r + 1 at hs
    simp only [C.nAux]
    refine mul_nonneg ?_ (ih (b + s) (by omega) (by omega))
    have : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by
      rintro ⟨h1, h2⟩
      omega
    rw [ite_eq_right this]
    exact zpow_nonneg (mul_nonneg (hfr b s).le (norm_nonneg _)) _

theorem cutWord_of_adm (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (hC : KB.CutInside S) (w : S.W) (v : Fin S.f) :
    KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := by
  have hA := w.2.1
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have h1 := hA.1 v a a.isLt
    have hnode := (hG v).2.2.2.2.2
    apply hC v
    set x := (w.1 v)[(a : ℕ)]'a.isLt with hx
    have hget : (w.1 v).get a = x := by simp [hx]
    rw [hget]
    have hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
      intro Y hY
      simp only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY
      simp only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]
      constructor <;> linarith [hY.1, hY.2]
    by_cases hp : x.1
    · rw [if_pos hp] at h1
      have hy : (∃ a, x.2 ∈ S.grid v a) ∨ x.2 ∈ S.grid1 v := by
        rcases Finset.mem_union.1 h1 with h | h
        · exact Or.inl ⟨_, h⟩
        · exact Or.inr h
      exact hcut _ (hnode _ hy).1
    · rw [if_neg hp] at h1
      have hy : (∃ a, x.2 - 1 ∈ S.grid v a) ∨ x.2 - 1 ∈ S.grid1 v := by
        rcases Finset.mem_union.1 h1 with h | h
        · exact Or.inl ⟨_, h⟩
        · exact Or.inr h
      have := hcut _ (hnode _ hy).2.1
      simpa using this
  · have h2 := hA.2 v a b a.isLt b.isLt (fun h => hab (Fin.ext h)) 0 (by norm_num) (by norm_num)
    simpa using h2

theorem scal_id (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (ν e : ℤ) :
    (B ^ (-ν) / ((A * B)⁻¹ ^ ν)) ^ (2 * e) / ((A * B)⁻¹ ^ ν) ^ 2 = B ^ (2 * ν) * A ^ (2 * ν * (e + 1)) := by
  have h1 : B ^ (-ν) / ((A * B)⁻¹ ^ ν) = A ^ ν := by
    rw [inv_zpow, div_inv_eq_mul, mul_zpow, zpow_neg]
    field_simp
  have h2 : ((A * B)⁻¹ ^ ν) ^ 2 = A ^ (-(2 * ν)) * B ^ (-(2 * ν)) := by
    rw [← zpow_natCast, ← zpow_mul, mul_inv, mul_zpow, ← zpow_neg_one, ← zpow_neg_one B, ← zpow_mul, ← zpow_mul]
    congr 2 <;> push_cast <;> ring
  rw [h1, h2, ← zpow_mul]
  rw [div_eq_mul_inv, mul_inv, ← zpow_neg, ← zpow_neg]
  simp only [neg_neg]
  rw [show 2 * ν * (e + 1) = ν * (2 * e) + 2 * ν by ring, zpow_add₀ hA.ne']
  ring

theorem gamLev_succ (k r : ℕ) (κ de : ℝ) (j : ℕ) (hj : j ≤ r) :
    D.GamLev k r κ de j =
      κ ^ (-(4 * ((r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev k r (j + 1) - 1))) / de * D.GamLev k r κ de (j + 1) := by
  unfold D.GamLev
  have : Finset.Ioc j (r + 1) = insert (j + 1) (Finset.Ioc (j + 1) (r + 1)) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
  rw [this, Finset.prod_insert (by simp)]

theorem gamLev_pos (k r : ℕ) (κ de : ℝ) (hκ : 0 < κ) (hde : 0 < de) (i : ℕ) : 0 < D.GamLev k r κ de i := by
  unfold D.GamLev
  exact Finset.prod_pos fun l _ => div_pos (zpow_pos hκ _) hde

theorem hsInner_zero_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) A = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) => (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
    simp; rfl
  rw [this, inner_zero_right]

theorem rrTop_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (l0 : ℕ)
    (T : D.LevTower P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (Θ : Top.TopLift P.k P.r Wp Wq) (TP : Top.TypeProj P T.base.π T.base.z (m₀ *ᵥ ν')) (s : ℂ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (H H' : C.LPt) (c : ℂ) (hH : D.ptSize H = P.r)
    (hc : Complex.normSq c ≤ Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') :
    D.RRplace T s ν' m₀ (Top.topOf P l0 T ν' m₀ Θ TP) F (P.r + 1) w (H ++ [(1, c)]) H' = 0 := by
  have hv : ∀ F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp), D.vecV T.base ν' m₀ F' (H ++ [(1, c)]) = 0 := by
    intro F'
    unfold D.vecV
    rw [dite_eq_right]
    rintro ⟨-, hG⟩
    rw [ptG_app _ c H P.r hH] at hG
    have : Complex.normSq (D.ptMatN H P.r).det * (Complex.normSq c - Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (by linarith)
    linarith
  unfold D.RRplace
  split_ifs with h1 h2 h3 h4
  · omega
  · rw [hv, hsInner_zero_left]
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    rw [hv, ContinuousLinearMap.comp_zero, hsInner_zero_left, mul_zero]
  · rfl
  · rfl

end main

end Formalism.FourierDecayAlt.P.PBD
