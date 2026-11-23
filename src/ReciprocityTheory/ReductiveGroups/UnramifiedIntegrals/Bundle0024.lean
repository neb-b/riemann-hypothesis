module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0023
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorClose
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

theorem chord_identity {C : Type} [Field C] (W : WeierstrassCurve C) (h1 : W.a₁ = 0) (h2 : W.a₂ = 0)
    (h3 : W.a₃ = 0) (A B : W.toAffine.Point) (hA : A ≠ 0) (hB : B ≠ 0) (hs : A + B ≠ 0)
    (hd : A - B ≠ 0) :
    (px W A - px W B) ^ 2 * (px W (A + B) - px W (A - B)) = -4 * py W A * py W B := by
  rw [sub_eq_add_neg A B]
  rcases A with _ | ⟨xA, yA, hA'⟩
  · exact absurd rfl hA
  rcases B with _ | ⟨xB, yB, hB'⟩
  · exact absurd rfl hB
  by_cases hx : xA = xB
  · exfalso
    subst hx
    have e1 := (WeierstrassCurve.Affine.equation_iff _ _).1 hA'.1
    have e2 := (WeierstrassCurve.Affine.equation_iff _ _).1 hB'.1
    have hm : (yA - yB) * (yA + yB) = 0 := by
      linear_combination e1 - e2 - xA * (yA - yB) * h1 - (yA - yB) * h3
    rcases mul_eq_zero.1 hm with h | h
    · have hy : yA = yB := sub_eq_zero.1 h
      subst hy
      exact hd (sub_self _)
    · have hy : yA = W.toAffine.negY xA yB := by
        rw [WeierstrassCurve.Affine.negY]
        linear_combination h + xA * h1 + h3
      exact hs (WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hy)
  · have hx' : xA - xB ≠ 0 := sub_ne_zero.2 hx
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.add_of_X_ne hx,
      WeierstrassCurve.Affine.Point.add_of_X_ne hx]
    simp only [px, py, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_X_ne hx,
      WeierstrassCurve.Affine.negY, h1, h2, h3]
    field_simp
    ring

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_x_sub_le_of_formalGroup (W : WeierstrassCurve C) (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0)
    (hW : IntegralModel W) (A B : W.toAffine.Point) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAy : ‖py W A‖ ≤ 1) (hBy : ‖py W B‖ ≤ 1) (hs : A + B ≠ 0) (hsx : ‖px W (A + B)‖ ≤ 1)
    (hd : A - B ≠ 0) (hdx : InFormalGroupPoints (A - B)) : ‖px W A - px W B‖ ≤ ‖uOf (A - B)‖ := by
  obtain ⟨-, -, -, h4, h6⟩ := hW
  have hc := chord_identity W h1 h2 h3 A B hA hB hs hd
  generalize A - B = D at hc hd hdx ⊢
  rcases D with _ | ⟨xd, yd, hdn⟩
  · exact absurd rfl hd
  have hX : 1 < ‖xd‖ := hdx
  have hX0 : 0 < ‖xd‖ := by linarith
  have hXne : ‖xd‖ ≠ 0 := hX0.ne'
  have hc' : (px W A - px W B) ^ 2 * (px W (A + B) - xd) = -4 * py W A * py W B := hc
  have eqd := (WeierstrassCurve.Affine.equation_iff _ _).1 hdn.1
  have e : yd ^ 2 = xd ^ 3 + (W.a₄ * xd + W.a₆) := by
    linear_combination eqd - xd * yd * h1 - yd * h3 + xd ^ 2 * h2
  have hr : ‖W.a₄ * xd + W.a₆‖ ≤ ‖xd‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) h4
    · linarith
  have hX2 : 1 < ‖xd‖ ^ 2 := by nlinarith
  have hX3 : ‖xd‖ < ‖xd‖ ^ 3 := by
    have hm := mul_lt_mul_of_pos_left hX2 hX0
    nlinarith
  have hne2 : ‖xd ^ 3‖ ≠ ‖W.a₄ * xd + W.a₆‖ := by
    rw [norm_pow]
    exact ne_of_gt (lt_of_le_of_lt hr hX3)
  have hY : ‖yd‖ ^ 2 = ‖xd‖ ^ 3 := by
    rw [← norm_pow, e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne2, norm_pow,
      max_eq_left (by linarith)]
  have hYpos : 0 < ‖yd‖ := by
    by_contra hneg
    have h0 : ‖yd‖ = 0 := le_antisymm (not_lt.1 hneg) (norm_nonneg _)
    rw [h0] at hY
    have := pow_pos hX0 3
    nlinarith
  have hne1 : ‖px W (A + B)‖ ≠ ‖-xd‖ := ne_of_lt (by rw [norm_neg]; linarith)
  have hxs : ‖px W (A + B) - xd‖ = ‖xd‖ := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne1, norm_neg,
      max_eq_right (by linarith)]
  have h2n : ‖(2 : C)‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (1 : C) 1
    rw [one_add_one_eq_two, norm_one, max_self] at h
    exact h
  have h4n : ‖(4 : C)‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (2 : C) 2
    rw [show (2 : C) + 2 = 4 by norm_num] at h
    exact h.trans (max_le h2n h2n)
  have hn := congrArg norm hc'
  rw [norm_mul, norm_pow, hxs, norm_mul, norm_mul, norm_neg] at hn
  have ha0 := norm_nonneg (py W A)
  have hb0 := norm_nonneg (py W B)
  have h40 := norm_nonneg (4 : C)
  have hab : ‖(4 : C)‖ * ‖py W A‖ ≤ 1 := by nlinarith
  have habc : ‖(4 : C)‖ * ‖py W A‖ * ‖py W B‖ ≤ 1 := by nlinarith [mul_nonneg h40 ha0]
  have hbound : ‖px W A - px W B‖ ^ 2 * ‖xd‖ ≤ 1 := by rw [hn]; exact habc
  show ‖px W A - px W B‖ ≤ ‖-xd / yd‖
  rw [norm_div, norm_neg]
  have hq : (‖xd‖ / ‖yd‖) ^ 2 * ‖xd‖ = 1 := by
    rw [div_pow, hY]
    first
      | (field_simp; ring)
      | field_simp
  have hs0 := norm_nonneg (px W A - px W B)
  have hq0 : 0 ≤ ‖xd‖ / ‖yd‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  by_contra hlt
  push_neg at hlt
  have hsq : (‖xd‖ / ‖yd‖) ^ 2 < ‖px W A - px W B‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < ‖px W A - px W B‖ + ‖xd‖ / ‖yd‖)]
  nlinarith

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorContr
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]

theorem formalGroup_nsmul_estimate (W : WeierstrassCurve C) (hW : IntegralModel W) (hΔ : ‖W.Δ‖ = 1)
    (D : W.toAffine.Point) (hD : InFormalGroupPoints D) (n : ℕ) :
    InFormalGroupPoints (n • D) ∧ ‖uOf (n • D) - (n : C) * uOf D‖ ≤ ‖uOf D‖ ^ 2 := by
  have hu : ‖uOf D‖ < 1 := formalGroup_param_norm_lt_one W hW D hD
  have hsq : ‖uOf D‖ ^ 2 ≤ ‖uOf D‖ := by
    have h0 := norm_nonneg (uOf D)
    nlinarith
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [zero_smul]; exact (trivial : InFormalGroupPoints (Affine.Point.zero : W.toAffine.Point))
    · rw [zero_smul]
      have : uOf (0 : W.toAffine.Point) = 0 := rfl
      rw [this]; simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hin : InFormalGroupPoints (n • D + D) := (formal_group_points_subgroup C W hW hΔ (n • D) D h1 hD).1
    have hn : ‖(n : C)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one C n
    have hnu : ‖(n : C) * uOf D‖ ≤ ‖uOf D‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hn
    have hb : ‖uOf (n • D)‖ ≤ ‖uOf D‖ := by
      have e : uOf (n • D) = (uOf (n • D) - (n : C) * uOf D) + (n : C) * uOf D := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h2.trans hsq) hnu)
    have hadd := formalGroup_add_estimate W hW (n • D) D h1 hD
    rw [max_eq_right hb] at hadd
    rw [succ_nsmul]
    refine ⟨hin, ?_⟩
    have e : uOf (n • D + D) - ((n + 1 : ℕ) : C) * uOf D
        = (uOf (n • D + D) - uOf (n • D) - uOf D) + (uOf (n • D) - (n : C) * uOf D) := by
      push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hadd h2)

theorem formalGroup_pow_tendsto_zero (W : WeierstrassCurve C) (hW : IntegralModel W) (hΔ : ‖W.Δ‖ = 1)
    (D : W.toAffine.Point) (hD : InFormalGroupPoints D) (M : ℕ) (hM : ‖(M : C)‖ < 1) :
    Filter.Tendsto (fun k : ℕ => ‖uOf (M ^ k • D)‖) Filter.atTop (nhds 0) := by
  have hu : ‖uOf D‖ < 1 := formalGroup_param_norm_lt_one W hW D hD
  set c : ℝ := max ‖(M : C)‖ ‖uOf D‖ with hc
  have hc0 : 0 ≤ c := le_max_of_le_left (norm_nonneg _)
  have hc1 : c < 1 := max_lt hM hu
  have key : ∀ k : ℕ, ‖uOf (M ^ k • D)‖ ≤ c ^ k * ‖uOf D‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : InFormalGroupPoints (M ^ k • D) := (formalGroup_nsmul_estimate W hW hΔ D hD (M ^ k)).1
      have hest := (formalGroup_nsmul_estimate W hW hΔ (M ^ k • D) hk M).2
      have hle : ‖uOf (M ^ k • D)‖ ≤ ‖uOf D‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hc0 hc1.le))
      have hr0 := norm_nonneg (uOf (M ^ k • D))
      have e0 : M ^ (k + 1) • D = M • (M ^ k • D) := by
        rw [smul_smul, pow_succ, mul_comm]
      have h1 : ‖uOf (M • (M ^ k • D))‖ ≤ c * ‖uOf (M ^ k • D)‖ := by
        have e : uOf (M • (M ^ k • D)) = (uOf (M • (M ^ k • D)) - (M : C) * uOf (M ^ k • D))
            + (M : C) * uOf (M ^ k • D) := by ring
        rw [e]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hest.trans ?_) ?_)
        · rw [sq]
          exact mul_le_mul_of_nonneg_right (hle.trans (le_max_right _ _)) hr0
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
      rw [e0, pow_succ, mul_comm (c ^ k) c, mul_assoc]
      exact h1.trans (mul_le_mul_of_nonneg_left ih hc0)
  have hlim : Filter.Tendsto (fun k : ℕ => c ^ k * ‖uOf D‖) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const ‖uOf D‖
  exact squeeze_zero (fun _ => norm_nonneg _) key hlim

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorHensel
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable (l : ℕ) [Fact l.Prime]

theorem hensel_mem (P : Polynomial ℂ_[l]) (hK : ∀ i, P.coeff i ∈ MaximalUnramifiedExtension l) (hP : ∀ i, ‖P.coeff i‖ ≤ 1)
    (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (h0 : P.eval x = 0) (h1 : ‖P.derivative.eval x‖ = 1) : x ∈ MaximalUnramifiedExtension l := by
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial (MaximalUnramifiedExtension l), Q.map (MaximalUnramifiedExtension l).subtype = P := by
    have : P ∈ Polynomial.lifts (MaximalUnramifiedExtension l).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      exact ⟨⟨P.coeff i, hK i⟩, rfl⟩
    exact (Polynomial.mem_lifts P).mp this
  obtain ⟨ξ, hξ, hd⟩ := res_full l x hx
  have hξ1 : ‖ξ‖ ≤ 1 := tch_norm_le l hξ
  let a : MaximalUnramifiedExtension l := ⟨ξ, tch_mem_kur l hξ⟩
  have hev : ∀ b : MaximalUnramifiedExtension l, ((Q.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.eval (b : ℂ_[l]) := fun b => by
    rw [← hQ]
    exact (Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm
  have hdev : ∀ b : MaximalUnramifiedExtension l, ((Q.derivative.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.derivative.eval (b : ℂ_[l]) :=
    fun b => by
      rw [← hQ, Polynomial.derivative_map]
      exact (Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm
  have hQc : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i => by
    have := hP i
    rw [← hQ, Polynomial.coeff_map] at this
    exact this
  have e0 : ‖P.eval ξ‖ < 1 := by
    have := newton_lipschitz P hP ξ x hξ1 hx
    rw [h0, sub_zero, norm_sub_rev] at this
    exact lt_of_le_of_lt this hd
  have e1 : ‖P.derivative.eval ξ‖ = 1 := by
    have h2 := newton_lipschitz P.derivative (newton_derivative_coeff P hP) ξ x hξ1 hx
    rw [norm_sub_rev ξ x] at h2
    have h3 : ‖P.derivative.eval ξ - P.derivative.eval x‖ < ‖P.derivative.eval x‖ := by
      rw [h1]; exact lt_of_le_of_lt h2 hd
    have h4 : P.derivative.eval ξ = (P.derivative.eval ξ - P.derivative.eval x) + P.derivative.eval x := by
      ring
    rw [h4, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h3.ne, max_eq_right h3.le, h1]
  obtain ⟨x', hx'0, hx'd⟩ := newton_root Q hQc a hξ1
    (show ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1 by rw [hev]; exact e0)
    (show ‖((Q.derivative.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 by rw [hdev]; exact e1)
  have hx'd' : ‖(x' : ℂ_[l]) - ξ‖ < 1 := by
    have h5 : ‖((x' - a : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ := hx'd
    rw [hev] at h5
    exact lt_of_le_of_lt h5 e0
  have hP0 : P.eval (x' : ℂ_[l]) = 0 := by
    rw [← hev, hx'0]; rfl
  set y : ℂ_[l] := (x' : ℂ_[l]) - x with hy
  have hy1 : ‖y‖ < 1 := by
    have : y = ((x' : ℂ_[l]) - ξ) + (ξ - x) := by rw [hy]; ring
    rw [this]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx'd' ?_)
    rwa [norm_sub_rev]
  obtain ⟨k, hk, hexp⟩ := newton_expansion P hP x y hx hy1.le
  have hxy : x + y = (x' : ℂ_[l]) := by rw [hy]; ring
  rw [hxy, hP0, h0, zero_add] at hexp
  have hfac : y * (P.derivative.eval x + k * y) = 0 := by
    rw [hexp]; ring
  have hne : P.derivative.eval x + k * y ≠ 0 := by
    intro h
    have h6 : P.derivative.eval x = -(k * y) := eq_neg_of_add_eq_zero_left h
    rw [h6, norm_neg, norm_mul] at h1
    have : ‖k‖ * ‖y‖ < 1 := by
      calc ‖k‖ * ‖y‖ ≤ 1 * ‖y‖ := by gcongr
        _ < 1 := by rwa [one_mul]
    exact absurd h1 this.ne
  have hy0 : y = 0 := (mul_eq_zero.mp hfac).resolve_right hne
  have : x = (x' : ℂ_[l]) := by rw [← hxy, hy0, add_zero]
  rw [this]
  exact x'.2

theorem sqrt_mem (hl : l ≠ 2) (c y : ℂ_[l]) (hc : c ∈ MaximalUnramifiedExtension l) (hy : ‖y‖ = 1) (h : y ^ 2 = c) : y ∈ MaximalUnramifiedExtension l := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hle : ‖(2 : ℂ_[l])‖ ≤ 1 := by
      have := IsUltrametricDist.norm_natCast_le_one ℂ_[l] 2
      exact_mod_cast this
    refine le_antisymm hle ?_
    by_contra hlt
    push_neg at hlt
    have hcop : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two (Fact.out)).2 (Ne.symm hl)
    have hg : Int.gcd 2 (l : ℤ) = 1 := by
      have := Int.gcd_natCast_natCast 2 l
      simpa [Nat.Coprime.gcd_eq_one hcop] using this
    have hz' : (1 : ℤ) = 2 * Int.gcdA 2 l + l * Int.gcdB 2 l := by
      rw [← Int.gcd_eq_gcd_ab, hg]
      rfl
    have h1 := congrArg (Int.cast : ℤ → ℂ_[l]) hz'
    push_cast at h1
    have hm := IsUltrametricDist.norm_add_le_max (2 * ((Int.gcdA 2 l : ℤ) : ℂ_[l]))
      ((l : ℂ_[l]) * ((Int.gcdB 2 l : ℤ) : ℂ_[l]))
    rw [← h1, norm_one, norm_mul, norm_mul] at hm
    have ha := IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdA 2 l)
    have hb := IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdB 2 l)
    have hl1 := norm_prime_lt_one_complexPadic (l := l)
    rcases le_max_iff.1 hm with h | h
    · nlinarith [norm_nonneg ((Int.gcdA 2 l : ℤ) : ℂ_[l]), norm_nonneg (2 : ℂ_[l])]
    · nlinarith [norm_nonneg ((Int.gcdB 2 l : ℤ) : ℂ_[l]), norm_nonneg (l : ℂ_[l])]
  have hc1 : ‖c‖ = 1 := by rw [← h, norm_pow, hy, one_pow]
  refine hensel_mem l (Polynomial.X ^ 2 - Polynomial.C c) (fun i => ?_) (fun i => ?_) y hy.le ?_ ?_
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem hc
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem (MaximalUnramifiedExtension l).zero_mem
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem hc
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem (MaximalUnramifiedExtension l).zero_mem
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs <;> first | (exfalso; omega) | simp [hc1]
  · simp [h]
  · simp [Polynomial.derivative_X_pow, norm_mul, hy]
    rw [one_add_one_eq_two]
    exact h2

theorem exists_sqrt (hl : l ≠ 2) (c : ℂ_[l]) (hc : c ∈ MaximalUnramifiedExtension l) (h1 : ‖c‖ = 1) :
    ∃ b ∈ MaximalUnramifiedExtension l, b ^ 2 = c ∧ ‖b‖ = 1 := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  have hb1 : ‖b‖ = 1 := by
    have : ‖b‖ ^ 2 = 1 := by rw [← norm_pow, hb, h1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg b) two_ne_zero).1 this
  exact ⟨b, sqrt_mem l hl c b hc hb1 hb, hb, hb1⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

