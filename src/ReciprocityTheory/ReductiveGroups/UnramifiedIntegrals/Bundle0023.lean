module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorDefs
public import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.NonsingularNorm
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0006
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorBasic
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem good_norm_two (h : GoodPair l g2 g3) : ‖(2 : ℂ_[l])‖ = 1 := by
  have hl : ¬ (l ∣ 2) := by
    intro hd
    have h1 := Nat.le_of_dvd (by norm_num) hd
    have h2 := h.five
    omega
  have hQ : ‖(2 : ℚ_[l])‖ = 1 := by
    have e2 := Padic.eq_padicNorm (p := l) (2 : ℚ)
    push_cast at e2
    rw [e2]
    exact_mod_cast (padicNorm.nat_eq_one_iff 2).mpr hl
  have e : (2 : ℂ_[l]) = (((2 : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by
    rw [map_ofNat]
    first
    | exact (map_ofNat (UniformSpace.Completion.coeRingHom (α := PadicAlgCl l)) 2).symm
    | exact (UniformSpace.Completion.coe_ofNat 2).symm
    | exact (map_ofNat (algebraMap (PadicAlgCl l) ℂ_[l]) 2).symm
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, hQ]

theorem good_norm_four (h : GoodPair l g2 g3) : ‖(4 : ℂ_[l])‖ = 1 := by
  rw [show (4 : ℂ_[l]) = 2 * 2 by norm_num, norm_mul, good_norm_two h, mul_one]

theorem good_model (h : GoodPair l g2 g3) : IntegralModel (shortW g2 g3) ∧ ‖(shortW g2 g3).Δ‖ = 1 := by
  have h4 := good_norm_four h
  refine ⟨?_, ?_⟩
  · unfold IntegralModel shortW
    simp only [norm_zero, zero_le_one, norm_neg, norm_div, h4, div_one, true_and, h.norm2, h.norm3,
      and_self]
  · have hΔ : (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
      simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [hΔ, h.disc]

theorem good_int (h : GoodPair l g2 g3) : IntCurve (shortW g2 g3) := by
  have h4 := good_norm_four h
  have hΔ := (good_model h).2
  unfold IntCurve
  simp only [shortW] at hΔ ⊢
  simp only [norm_zero, zero_le_one, norm_neg, norm_div, h4, div_one, true_and, h.norm2,
    h.norm3, and_self, hΔ]

theorem good_coeff (h : GoodPair l g2 g3) : CoeffSub (MaximalUnramifiedExtension l) (shortW g2 g3) := by
  have h4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    first
    | exact ofNat_mem (MaximalUnramifiedExtension l) 4
    | (have h4' := natCast_mem (MaximalUnramifiedExtension l) 4
       exact_mod_cast h4')
  unfold CoeffSub shortW
  exact ⟨zero_mem _, zero_mem _, zero_mem _, div_mem (neg_mem h.mem2) h4,
    div_mem (neg_mem h.mem3) h4⟩

theorem integral_of_not_mem_formalGroup (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP : ¬ InFormalGroupPoints P) :
    P ≠ 0 ∧ ‖px _ P‖ ≤ 1 ∧ ‖py _ P‖ ≤ 1 := by
  unfold InFormalGroupPoints at hP
  cases P with
  | zero => exact absurd trivial hP
  | some x y hxy =>
    have hx : ‖x‖ ≤ 1 := not_lt.mp hP
    have h4 := good_norm_four h
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp hxy.1
    simp only [shortW, zero_mul, mul_zero, add_zero] at heq
    have hb1 : ‖x ^ 3‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hx
    have hb2 : ‖-g2 / 4 * x‖ ≤ 1 := by
      rw [norm_mul, norm_div, norm_neg, h4, div_one]
      exact mul_le_one₀ h.norm2 (norm_nonneg _) hx
    have hb3 : ‖-g3 / 4‖ ≤ 1 := by
      rw [norm_div, norm_neg, h4, div_one]
      exact h.norm3
    have hsum : ‖x ^ 3 + -g2 / 4 * x + -g3 / 4‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb1 hb2)) hb3)
    have hy2 : ‖y‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, heq]
      exact hsum
    refine ⟨by rintro (_ | _), ?_, ?_⟩
    · exact hx
    · show ‖y‖ ≤ 1
      nlinarith [norm_nonneg y]

theorem torsion_not_mem_formalGroup (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN : ¬ l ∣ N)
    (hNP : N • P = 0) (hP0 : P ≠ 0) : ¬ InFormalGroupPoints P := fun hE => by
  have hn := norm_natCast_Cl_of_not_dvd (l := l) hN
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
  have hmul := (FormalGroupPointsTorsion.mulz (good_model h).1 P hE hP0 m).2
  rw [hNP, Affine.Point.zero_def] at hmul
  simp only [FormalGroupPointsTorsion.zf, zero_sub, norm_neg, norm_mul, hn, one_mul] at hmul
  exact lt_irrefl _ hmul

theorem not_mem_formalGroup_sub (h : GoodPair l g2 g3) (P D : (shortW g2 g3).toAffine.Point) (hP : ¬ InFormalGroupPoints P)
    (hD : InFormalGroupPoints D) : ¬ InFormalGroupPoints (P - D) := fun hE => by
  have hadd : InFormalGroupPoints (P - D + D) := by
    generalize P - D = E at hE ⊢
    cases E with
    | zero =>
      change InFormalGroupPoints (0 + D)
      rwa [zero_add]
    | some x₁ y₁ h₁ =>
      cases D with
      | zero =>
        change InFormalGroupPoints (Affine.Point.some x₁ y₁ h₁ + 0)
        rwa [add_zero]
      | some x₂ y₂ h₂ =>
        by_cases hxy : x₁ = x₂ ∧ y₁ = (shortW g2 g3).toAffine.negY x₂ y₂
        · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
          trivial
        · rw [Affine.Point.add_some hxy]
          exact FormalGroupPointsSubgroup.addX_norm _ (good_model h).1 h₁.1 h₂.1 hxy hE hD
  exact hP (by simpa only [sub_add_cancel] using hadd)

theorem tor_y_unit (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN : ¬ l ∣ N)
    (hNP : N • P = 0) (h2 : P + P ≠ 0) : ‖py _ P‖ = 1 := by
  have hP0 : P ≠ 0 := fun h0 => h2 (by rw [h0, add_zero])
  obtain ⟨-, hx, hy⟩ := integral_of_not_mem_formalGroup h P (torsion_not_mem_formalGroup h P N hN hNP hP0)
  have hN2 : N • (P + P) = 0 := by rw [smul_add, hNP, add_zero]
  obtain ⟨-, hx2, -⟩ := integral_of_not_mem_formalGroup h (P + P) (torsion_not_mem_formalGroup h (P + P) N hN hN2 h2)
  have hu := Formalism.L2.Th1.E.UnitPsi2_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] _ (good_int h) P hP0 h2 hx hy hx2
  have he : Formalism.L2.Th1.E.psi2 (shortW g2 g3) P = 2 * py _ P := by
    simp [Formalism.L2.Th1.E.psi2, shortW]
  rw [he, norm_mul, good_norm_two h, one_mul] at hu
  exact hu

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorChord
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem chord_norm_add {a b : C} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem chord_norm_y_sq (W : WeierstrassCurve C) (hW : IntegralModel W) {x y : C}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  rw [Affine.equation_iff] at h
  have hx0 : 0 < ‖x‖ := lt_trans one_pos hx
  have e2 : ‖W.a₂ * x ^ 2‖ < ‖x ^ 3‖ := by
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖W.a₂‖ * ‖x‖ ^ 2 ≤ 1 * ‖x‖ ^ 2 := by gcongr
      _ < ‖x‖ ^ 3 := by nlinarith [pow_pos hx0 2]
  have e4 : ‖W.a₄ * x‖ < ‖x ^ 3‖ := by
    rw [norm_mul, norm_pow]
    calc ‖W.a₄‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
      _ < ‖x‖ ^ 3 := by nlinarith [pow_pos hx0 2, mul_pos hx0 hx0]
  have e6 : ‖W.a₆‖ < ‖x ^ 3‖ := by
    rw [norm_pow]
    calc ‖W.a₆‖ ≤ 1 := h6
      _ < ‖x‖ ^ 3 := one_lt_pow₀ hx (by norm_num)
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ = ‖x‖ ^ 3 := by
    have s1 := chord_norm_add e2
    have s2 : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x‖ = ‖x ^ 3‖ := by
      rw [chord_norm_add (by rw [s1]; exact e4), s1]
    rw [chord_norm_add (by rw [s2]; exact e6), s2, norm_pow]
  have hL : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y * (y + (W.a₁ * x + W.a₃)) := by ring
  rw [← h, hL, norm_mul] at hR
  have hc : ‖W.a₁ * x + W.a₃‖ ≤ ‖x‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h3.trans hx.le))
    rw [norm_mul]
    calc ‖W.a₁‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  have hyx : ‖x‖ < ‖y‖ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hs : ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcon hc)
    have : ‖y‖ * ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul hcon hs (norm_nonneg _) hx0.le
    nlinarith [mul_pos hx0 hx0]
  rw [chord_norm_add (lt_of_le_of_lt hc hyx)] at hR
  rw [← hR]; ring

theorem chord_norm_u_sq (W : WeierstrassCurve C) (hW : IntegralModel W) {x y : C}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖-x / y‖ ^ 2 * ‖x‖ = 1 := by
  have hy := chord_norm_y_sq W hW h hx
  have hx0 : 0 < ‖x‖ := by linarith
  have hx0' := hx0.ne'
  rw [norm_div, norm_neg, div_pow, hy]
  field_simp

theorem formalGroup_param_norm_lt_one (W : WeierstrassCurve C) (hW : IntegralModel W) (P : W.toAffine.Point) (hP : InFormalGroupPoints P) :
    ‖uOf P‖ < 1 := by
  rcases P with _ | @⟨x, y, h⟩
  · simp [uOf]
  · have hx : 1 < ‖x‖ := hP
    have hu := chord_norm_u_sq W hW h.1 hx
    show ‖-x / y‖ < 1
    by_contra hcon
    rw [not_lt] at hcon
    have : 1 ≤ ‖-x / y‖ ^ 2 := one_le_pow₀ hcon
    nlinarith

theorem chord_adjoin_le (W : WeierstrassCurve C) (hW : IntegralModel W) {c : C}
    (hc : c ∈ Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set C)) : ‖c‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  | algebraMap n =>
    rw [eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one C n
  | add x y _ _ hx hy =>
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | mul x y _ _ hx hy =>
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

theorem chord_eval_est [CompleteSpace C] {F : MvPowerSeries (Fin 2) C} (hF : Formalism.G.IntegralMv F)
    (h00 : MvPowerSeries.constantCoeff F = 0)
    (h10 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1)
    (h01 : MvPowerSeries.coeff (Finsupp.single 1 1) F = 1) {a b : C} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖evalMv2 F a b - a - b‖ ≤ (max ‖a‖ ‖b‖) ^ 2 := by
  set r := max ‖a‖ ‖b‖ with hr
  have hr0 : 0 ≤ r := le_trans (norm_nonneg a) (le_max_left _ _)
  have hr1 : r < 1 := max_lt ha hb
  set G : MvPowerSeries (Fin 2) C := F - MvPowerSeries.X 0 - MvPowerSeries.X 1 with hG
  have hI1 : Formalism.G.IntegralMv (F - MvPowerSeries.X 0) :=
    (FormalGroupPointsHom.IL C).sub_mem hF (FormalGroupPointsHom.integral_X 0)
  have hIG : Formalism.G.IntegralMv G := (FormalGroupPointsHom.IL C).sub_mem hI1 (FormalGroupPointsHom.integral_X 1)
  have hev : evalMv2 G a b = evalMv2 F a b - a - b := by
    rw [hG, FormalGroupPointsHom.evalMv2_sub hI1 (FormalGroupPointsHom.integral_X 1) ha hb,
      FormalGroupPointsHom.evalMv2_sub hF (FormalGroupPointsHom.integral_X 0) ha hb, FormalGroupPointsHom.evalMv2_X0,
      FormalGroupPointsHom.evalMv2_X1]
  rw [← hev, FormalGroupPointsHom.evalMv2_eq]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (pow_nonneg hr0 2)
  intro d
  by_cases hd : 2 ≤ d.degree
  · exact (FormalGroupPointsHom.norm_term_le hIG (le_max_left _ _) (le_max_right _ _) d).trans
      (pow_le_pow_of_le_one hr0 hr1.le hd)
  · have hz : MvPowerSeries.coeff d G = 0 := by
      rw [FormalGroupPointsHom.degree_fin_two_eq_add_of_ne] at hd
      have hcases : d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
        have h3 : (d 0 = 0 ∧ d 1 = 0) ∨ (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
        rcases h3 with ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩
        · left; ext i; fin_cases i <;> simp [u, v]
        · right; left; ext i; fin_cases i <;> simp [u, v]
        · right; right; ext i; fin_cases i <;> simp [u, v]
      have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
        intro he
        have := DFunLike.congr_fun he 0
        simp at this
      rcases hcases with rfl | rfl | rfl
      · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG]
        simp [h00]
      · rw [hG, map_sub, map_sub, h10, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl,
          if_neg hne]
        ring
      · rw [hG, map_sub, map_sub, h01, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl,
          if_neg hne.symm]
        ring
    rw [FormalGroupPointsHom.term, hz, zero_mul, norm_zero]
    exact pow_nonneg hr0 2

theorem formalGroup_add_estimate [CompleteSpace C] (W : WeierstrassCurve C) (hW : IntegralModel W)
    (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P) (hQ : InFormalGroupPoints Q) :
    ‖uOf (P + Q) - uOf P - uOf Q‖ ≤ (max ‖uOf P‖ ‖uOf Q‖) ^ 2 := by
  obtain ⟨w, hw, -⟩ := wSeriesUnique.{0} C W
  obtain ⟨F, hFc, hch⟩ := wFormalGroup.{0} C W w hw
  have hF : Formalism.G.IntegralMv F.toPowerSeries := fun d => chord_adjoin_le W hW (hFc d)
  have hadd : uOf (P + Q) = evalMv2 F.toPowerSeries (uOf P) (uOf Q) :=
    FormalGroupPointsHom.e1hom_main wSubstUnique wChordSubst formal_group_points_param
      hW hw F hF hch P Q hP hQ
  rw [hadd]
  exact chord_eval_est hF F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y
    (formalGroup_param_norm_lt_one W hW P hP) (formalGroup_param_norm_lt_one W hW Q hQ)

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorRes
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation

open Polynomial Finset

variable (l : ℕ) [Fact l.Prime]

theorem monic_X_pow_add_sum {R : Type*} [CommRing R] [Nontrivial R] (d : ℕ) (a : ℕ → R) :
    (X ^ d + ∑ i ∈ range d, C (a i) * X ^ i).Monic := by
  refine monic_X_pow_add
    (lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).2 ?_))
  intro i hi
  exact (degree_C_mul_X_pow_le i (a i)).trans_lt (WithBot.coe_lt_coe.2 (mem_range.1 hi))

theorem exists_nat_near (a : ℚ_[l]) (ha : ‖a‖ ≤ 1) : ∃ n : ℕ, ‖a - n‖ < 1 := by
  set x : ℤ_[l] := ⟨a, ha⟩ with hxdef
  obtain ⟨n, hn⟩ := PadicInt.denseRange_natCast.exists_dist_lt x one_pos
  have hxa : (x : ℚ_[l]) = a := rfl
  refine ⟨n, ?_⟩
  rw [dist_eq_norm, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, hxa] at hn
  exact hn

theorem exists_nat_poly_near (y : PadicAlgCl l) (hy : ‖y‖ ≤ 1) :
    ∃ d : ℕ, ∃ c : ℕ → ℕ, ‖((X ^ d + ∑ i ∈ range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval
      (y : ℂ_[l]))‖ < 1 := by
  set P := minpoly ℚ_[l] y with hPdef
  have hint : IsIntegral ℚ_[l] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hmon : P.Monic := minpoly.monic hint
  have hcoef : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    have h1 : spectralValue P ≤ 1 := by
      have : spectralNorm ℚ_[l] (PadicAlgCl l) y = ‖y‖ := PadicAlgCl.spectralNorm_eq l y
      rw [spectralNorm] at this
      rw [hPdef, this]; exact hy
    exact (spectralValue_le_one_iff hmon).1 h1
  choose c hc using fun i => exists_nat_near l (P.coeff i) (hcoef i)
  refine ⟨P.natDegree, c, ?_⟩
  set z : ℂ_[l] := (y : ℂ_[l]) with hz
  have hP0 : aeval z P = 0 := by
    rw [hz, PadicComplex.coe_eq, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hPsum : aeval z P = z ^ P.natDegree +
      ∑ i ∈ range P.natDegree, algebraMap ℚ_[l] ℂ_[l] (P.coeff i) * z ^ i := by
    conv_lhs => rw [hmon.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_add (f := _), map_sum, aeval_X, aeval_C]
  have he : (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z =
      ∑ i ∈ range P.natDegree, algebraMap ℚ_[l] ℂ_[l] ((c i : ℚ_[l]) - P.coeff i) * z ^ i := by
    have : (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z =
        (X ^ P.natDegree + ∑ i ∈ range P.natDegree, C ((c i : ℕ) : ℂ_[l]) * X ^ i).eval z -
          aeval z P := by rw [hP0, sub_zero]
    rw [this, hPsum]
    simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_natCast, map_sub,
      map_natCast, sub_mul, sum_sub_distrib]
    ring
  have hz1 : ‖z‖ ≤ 1 := by rw [hz, PadicComplex.norm_extends]; exact hy
  rw [he]
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le (range P.natDegree)
    (fun i => algebraMap ℚ_[l] ℂ_[l] ((c i : ℚ_[l]) - P.coeff i) * z ^ i)
  refine lt_of_le_of_lt hle ?_
  rw [norm_mul, norm_algebraMap', norm_pow, norm_sub_rev]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz1))
    (hc i)

end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve Polynomial
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable (l : ℕ) [Fact l.Prime]

theorem res_full (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) : ∃ ξ ∈ Tch l, ‖x - ξ‖ < 1 := by
  obtain ⟨y, hy⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x one_pos
  rw [dist_eq_norm] at hy
  have hy1 : ‖y‖ ≤ 1 := by
    rw [← PadicComplex.norm_extends]
    calc ‖(y : ℂ_[l])‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ max ‖x‖ ‖x - y‖ := by
        have := IsUltrametricDist.norm_add_le_max x (-(x - (y : ℂ_[l])))
        rwa [← sub_eq_add_neg, norm_neg] at this
      _ ≤ 1 := max_le hx hy.le
  obtain ⟨d, c, hQ⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_nat_poly_near l y hy1
  set Q' : (Rmu l)[X] := X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : Rmu l) * X ^ i with hQ'
  have hmon : Q'.Monic := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.monic_X_pow_add_sum d (fun i => ((c i : ℕ) : Rmu l))
  have hmap : Q'.map (algebraMap (Rmu l) ℂ_[l]) =
      X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hQ', Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_natCast]
  obtain ⟨α, hroot, hα⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near l
    (X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i)
    (by rw [← hmap]; exact hmon.map _) (y : ℂ_[l]) hQ
  have hint : IsIntegral (Rmu l) α := ⟨Q', hmon, by rw [eval₂_eq_eval_map, hmap]; exact hroot⟩
  obtain ⟨ξ, hξ, hξα⟩ := tch_of_integral l α hint
  refine ⟨ξ, hξ, ?_⟩
  have e : x - ξ = (x - y) + ((y - α) + (α - ξ)) := by ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hy ?_)
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hα hξα)

end ReciprocityTheory.ChartRestriction.L1
end
end

