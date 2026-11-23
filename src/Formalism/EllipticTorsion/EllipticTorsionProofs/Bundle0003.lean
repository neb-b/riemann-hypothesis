module

public import Mathlib
public import Formalism.EllipticTorsion.Bundle0003
public import Formalism.EllipticTorsion.EllipticTorsionProofs.Bundle0002
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
public import Formalism.EllipticTorsion.EllipticTorsionProofs.IntegralPSBserSubOne

@[expose] public section

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.Change
section
open Formalism.ELL Formalism.G

namespace Formalism.ELL.RootExponentBounds

universe u

section
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma addle {x y : K} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x + y‖ ≤ B :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

lemma tb {a r : K} (k n : ℕ) (ha : ‖a‖ ≤ 1) (hr : 1 ≤ ‖r‖) (hk : k ≤ n) :
    ‖a * r ^ k‖ ≤ ‖r‖ ^ n := by
  rw [norm_mul, norm_pow]
  calc ‖a‖ * ‖r‖ ^ k ≤ 1 * ‖r‖ ^ n :=
        mul_le_mul ha (pow_le_pow_right₀ hr hk) (by positivity) zero_le_one
    _ = _ := one_mul _

lemma root2 {a b r : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (h : r ^ 2 + a * r + b = 0) :
    ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e : r ^ 2 = -(a * r ^ 1 + b * r ^ 0) := by linear_combination h
  have hb' : ‖a * r ^ 1 + b * r ^ 0‖ ≤ ‖r‖ ^ 1 :=
    addle (tb 1 1 ha hr.le le_rfl) (tb 0 1 hb hr.le (by norm_num))
  rw [← norm_neg, ← e, norm_pow] at hb'
  have : ‖r‖ ^ 1 < ‖r‖ ^ 2 := pow_lt_pow_right₀ hr (by norm_num)
  linarith

lemma root3 {c a b d r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (h : c * r ^ 3 + a * r ^ 2 + b * r + d = 0) : ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e : c * r ^ 3 = -(a * r ^ 2 + b * r ^ 1 + d * r ^ 0) := by linear_combination h
  have hb' : ‖a * r ^ 2 + b * r ^ 1 + d * r ^ 0‖ ≤ ‖r‖ ^ 2 :=
    addle (addle (tb 2 2 ha hr.le le_rfl) (tb 1 2 hb hr.le (by norm_num)))
      (tb 0 2 hd hr.le (by norm_num))
  rw [← norm_neg, ← e, norm_mul, norm_pow, hc, one_mul] at hb'
  have : ‖r‖ ^ 2 < ‖r‖ ^ 3 := pow_lt_pow_right₀ hr (by norm_num)
  linarith

lemma root4 {c a b d e r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (he : ‖e‖ ≤ 1) (h : c * r ^ 4 + a * r ^ 3 + b * r ^ 2 + d * r + e = 0) : ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e' : c * r ^ 4 = -(a * r ^ 3 + b * r ^ 2 + d * r ^ 1 + e * r ^ 0) := by
    linear_combination h
  have hb' : ‖a * r ^ 3 + b * r ^ 2 + d * r ^ 1 + e * r ^ 0‖ ≤ ‖r‖ ^ 3 :=
    addle (addle (addle (tb 3 3 ha hr.le le_rfl) (tb 2 3 hb hr.le (by norm_num)))
      (tb 1 3 hd hr.le (by norm_num))) (tb 0 3 he hr.le (by norm_num))
  rw [← norm_neg, ← e', norm_mul, norm_pow, hc, one_mul] at hb'
  have : ‖r‖ ^ 3 < ‖r‖ ^ 4 := pow_lt_pow_right₀ hr (by norm_num)
  linarith

lemma memB {x : K} : x ∈ unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

lemma natB (n : ℕ) : (n : K) ∈ unitBall K := memB.2 (IsUltrametricDist.norm_natCast_le_one K n)

lemma ofNatB (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : K) ∈ unitBall K := by
  have := natB (K := K) n
  exact this

end

lemma bmem {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (h1 : W.a₁ ∈ unitBall K) (h2 : W.a₂ ∈ unitBall K) (h3 : W.a₃ ∈ unitBall K)
    (h4 : W.a₄ ∈ unitBall K) (h6 : W.a₆ ∈ unitBall K) :
    W.b₂ ∈ unitBall K ∧ W.b₄ ∈ unitBall K ∧ W.b₆ ∈ unitBall K ∧ W.b₈ ∈ unitBall K := by
  let S := unitBall K
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.b₂]
    exact S.add_mem (S.pow_mem h1 2) (S.mul_mem (ofNatB 4) h2)
  · rw [WeierstrassCurve.b₄]
    exact S.add_mem (S.mul_mem (ofNatB 2) h4) (S.mul_mem h1 h3)
  · rw [WeierstrassCurve.b₆]
    exact S.add_mem (S.pow_mem h3 2) (S.mul_mem (ofNatB 4) h6)
  · rw [WeierstrassCurve.b₈]
    exact S.sub_mem
      (S.add_mem
        (S.sub_mem
          (S.add_mem (S.mul_mem (S.pow_mem h1 2) h6) (S.mul_mem (S.mul_mem (ofNatB 4) h2) h6))
          (S.mul_mem (S.mul_mem h1 h3) h4))
        (S.mul_mem h2 (S.pow_mem h3 2)))
      (S.pow_mem h4 2)

theorem change_of_variables_integral_of : ChangeIntegral.{u} := by
  intro K _ _ W C hW hW' hΔ0 hΔ
  set W' := C • W with hW'def
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  obtain ⟨h1', h2', h3', h4', h6'⟩ := hW'

  have hv : ‖((C.u⁻¹ : Kˣ) : K)‖ = 1 := by
    have e := WeierstrassCurve.variableChange_Δ W C
    rw [← hW'def] at e
    rw [e, norm_mul, norm_pow] at hΔ
    have hn : ‖W.Δ‖ ≠ 0 := norm_ne_zero_iff.2 hΔ0
    have : ‖((C.u⁻¹ : Kˣ) : K)‖ ^ 12 = 1 := by
      have := mul_right_cancel₀ hn (hΔ.trans (one_mul _).symm); exact this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  have hu : ‖(C.u : K)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_eq_one] at hv; exact hv
  set u : K := (C.u : K)
  set v : K := ((C.u⁻¹ : Kˣ) : K)
  have hvu : v * u = 1 := by simp [u, v]
  have hvu2 : v ^ 2 * u ^ 2 = 1 := by rw [← mul_pow, hvu, one_pow]
  have hvu6 : v ^ 6 * u ^ 6 = 1 := by rw [← mul_pow, hvu, one_pow]
  have hvu8 : v ^ 8 * u ^ 8 = 1 := by rw [← mul_pow, hvu, one_pow]
  rw [← memB] at h1 h2 h3 h4 h6 h1' h2' h3' h4' h6'
  have hu' : u ∈ unitBall K := by rw [memB, hu]
  obtain ⟨hb2, hb4, hb6, hb8⟩ := bmem W h1 h2 h3 h4 h6
  obtain ⟨-, -, hb6', hb8'⟩ := bmem W' h1' h2' h3' h4' h6'

  let S := unitBall K
  have hr : C.r ∈ unitBall K := by
    rw [memB]
    rcases (IsUltrametricDist.norm_natCast_le_one K 2).lt_or_eq with h2lt | h2eq
    ·
      have h3n : ‖(3 : K)‖ = 1 := by
        have h3le : ‖(3 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 3
        have : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
          have := IsUltrametricDist.norm_add_le_max (3 : K) (-2)
          rw [norm_neg] at this
          have e : (3 : K) + -2 = 1 := by norm_num
          rwa [e] at this
        rw [norm_one] at this
        push_cast at h2lt
        rcases le_max_iff.1 this with h | h
        · exact le_antisymm h3le h
        · linarith
      have e8 := WeierstrassCurve.variableChange_b₈ W C
      rw [← hW'def] at e8
      have key : (3 : K) * C.r ^ 4 + W.b₂ * C.r ^ 3 + (3 * W.b₄) * C.r ^ 2 + (3 * W.b₆) * C.r
          + (W.b₈ - u ^ 8 * W'.b₈) = 0 := by
        linear_combination (-u ^ 8) * e8 - (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄
          + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) * hvu8
      exact root4 h3n (memB.1 hb2) (memB.1 (S.mul_mem (ofNatB 3) hb4))
        (memB.1 (S.mul_mem (ofNatB 3) hb6))
        (memB.1 (S.sub_mem hb8 (S.mul_mem (S.pow_mem hu' 8) hb8'))) key
    ·
      have h4n : ‖(4 : K)‖ = 1 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this, norm_mul]; push_cast at h2eq; rw [h2eq]; norm_num
      have e6 := WeierstrassCurve.variableChange_b₆ W C
      rw [← hW'def] at e6
      have key : (4 : K) * C.r ^ 3 + W.b₂ * C.r ^ 2 + (2 * W.b₄) * C.r
          + (W.b₆ - u ^ 6 * W'.b₆) = 0 := by
        linear_combination (-u ^ 6) * e6 - (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂
          + 4 * C.r ^ 3) * hvu6
      exact root3 h4n (memB.1 hb2) (memB.1 (S.mul_mem (ofNatB 2) hb4))
        (memB.1 (S.sub_mem hb6 (S.mul_mem (S.pow_mem hu' 6) hb6'))) key

  have hs : C.s ∈ unitBall K := by
    have e2 : W'.a₂ = v ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := rfl
    have key : C.s ^ 2 + W.a₁ * C.s + (-W.a₂ - 3 * C.r + u ^ 2 * W'.a₂) = 0 := by
      linear_combination u ^ 2 * e2 + (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * hvu2
    have hconst : -W.a₂ - 3 * C.r + u ^ 2 * W'.a₂ ∈ S :=
      S.add_mem (S.sub_mem (S.neg_mem h2) (S.mul_mem (ofNatB 3) hr))
        (S.mul_mem (S.pow_mem hu' 2) h2')
    exact memB.2 (root2 (memB.1 h1) (memB.1 hconst) key)

  have ht : C.t ∈ unitBall K := by
    have e6 : W'.a₆ = v ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
        - C.t ^ 2 - C.r * C.t * W.a₁) := rfl
    have key : C.t ^ 2 + (W.a₃ + C.r * W.a₁) * C.t
        + (-(W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3) + u ^ 6 * W'.a₆) = 0 := by
      linear_combination u ^ 6 * e6 + (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
        - C.t ^ 2 - C.r * C.t * W.a₁) * hvu6
    have hsum : W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 ∈ S :=
      S.add_mem (S.add_mem (S.add_mem h6 (S.mul_mem hr h4)) (S.mul_mem (S.pow_mem hr 2) h2))
        (S.pow_mem hr 3)
    exact memB.2 (root2 (memB.1 (S.add_mem h3 (S.mul_mem hr h1)))
      (memB.1 (S.add_mem (S.neg_mem hsum) (S.mul_mem (S.pow_mem hu' 6) h6'))) key)
  exact ⟨hu, memB.1 hr, memB.1 hs, memB.1 ht⟩

end Formalism.ELL.RootExponentBounds

namespace Formalism.ELL

universe v

theorem change_of_variables_integral : ChangeIntegral.{v} := Formalism.ELL.RootExponentBounds.change_of_variables_integral_of

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.CompExp
section
open PowerSeries IsUltrametricDist

universe u

namespace Formalism.ELL.MultiplicativeWeight

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)

def W (w : ℤ) (f : MvPowerSeries σ K) : Prop :=
  ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e f‖ ≤ c ^ (w - (e.degree : ℤ))

variable {c}

theorem W_one (hc : 0 < c) (_hc1 : c ≤ 1) : W c 0 (1 : MvPowerSeries σ K) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp only [norm_zero]; positivity

theorem W_mul (hc : 0 < c) {w₁ w₂ : ℤ} {f g : MvPowerSeries σ K} (hf : W c w₁ f) (hg : W c w₂ g) :
    W c (w₁ + w₂) (f * g) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
  have hp : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 f‖ * ‖MvPowerSeries.coeff p.2 g‖
      ≤ c ^ (w₁ - (p.1.degree : ℤ)) * c ^ (w₂ - (p.2.degree : ℤ)) :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
    _ = c ^ (w₁ + w₂ - (e.degree : ℤ)) := by
        rw [← zpow_add₀ hc.ne', ← hp, map_add (f := _)]; push_cast; ring_nf

theorem W_pow (hc : 0 < c) (hc1 : c ≤ 1) {w : ℤ} {f : MvPowerSeries σ K} (hf : W c w f) (n : ℕ) :
    W c (n * w) (f ^ n) := by
  induction n with
  | zero => simpa using W_one hc hc1
  | succ n ih => rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact W_mul hc ih hf

theorem W_E (E : PowerSeries K) (hE : constantCoeff E = 0)
    (hb : ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) (hc : 0 < c) (i : σ) :
    W c 1 (E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0, coeff_zero_eq_constantCoeff_apply, hE, norm_zero]; positivity
    · conv_rhs => rw [h, Finsupp.degree_single]
      exact hb _ h0
  · rw [norm_zero]; positivity

theorem W_prod (hc : 0 < c) (hc1 : c ≤ 1) (a : σ → MvPowerSeries σ K) (ha : ∀ i, W c 1 (a i))
    (d : σ →₀ ℕ) : W c (d.degree : ℤ) (d.prod fun s n => a s ^ n) := by
  classical
  unfold Finsupp.prod
  have hdeg : (d.degree : ℤ) = ∑ s ∈ d.support, ((d s : ℕ) : ℤ) := by
    show (((∑ i ∈ d.support, d i : ℕ)) : ℤ) = _
    push_cast; rfl
  rw [hdeg]
  induction d.support using Finset.induction_on with
  | empty => simpa using W_one hc hc1
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs]
    have := W_pow hc hc1 (ha s) (d s)
    rw [mul_one] at this
    exact W_mul hc this ih

theorem comp_exp_coeff_weight_of : CompExpWeight.{u} := by
  intro K _ _ σ _ c hc hc1 E hE hb G hG α
  classical
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := σ) (S := K)
    (a := fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K))
    fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE
  rw [MvPowerSeries.coeff_subst ha]
  have hfin := MvPowerSeries.coeff_subst_finite ha G α
  rw [finsum_eq_sum _ hfin]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d _ => ?_
  rw [smul_eq_mul, norm_mul]
  have h1 := W_prod hc hc1 _ (W_E E hE hb hc) d α
  calc ‖MvPowerSeries.coeff d G‖ * ‖MvPowerSeries.coeff α
          (d.prod fun s e => (E.subst (MvPowerSeries.X s : MvPowerSeries σ K)) ^ e)‖
      ≤ 1 * c ^ ((d.degree : ℤ) - (α.degree : ℤ)) :=
        mul_le_mul (hG d) h1 (norm_nonneg _) zero_le_one
    _ ≤ c ^ (-(α.degree : ℤ)) := by
        rw [one_mul]; exact zpow_le_zpow_right_of_le_one₀ hc hc1 (by omega)

end Formalism.ELL.MultiplicativeWeight

namespace Formalism.ELL

theorem comp_exp_coeff_weight : Formalism.ELL.CompExpWeight := Formalism.ELL.MultiplicativeWeight.comp_exp_coeff_weight_of

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
section
namespace Formalism.ELL

namespace DeuringModel

open Polynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma norm_add_eq_left {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_nat_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

lemma exists_root_deuring [IsAlgClosed K] (j : K) :
    ∃ a : K, a ^ 3 * (a ^ 3 - 24) ^ 3 = j * (a ^ 3 - 27) := by
  let P : K[X] := X ^ 3 * (X ^ 3 - C 24) ^ 3 - C j * (X ^ 3 - C 27)
  have hdeg : P.degree = 12 := by
    simp only [P]
    compute_degree!
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P (by rw [hdeg]; norm_num)
  refine ⟨a, ?_⟩
  simp only [P, IsRoot, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at ha
  exact sub_eq_zero.mp ha

end DeuringModel

open DeuringModel in
theorem deuring_model : ModelDeuring := by
  intro K _ _ _ h3 j hj
  obtain ⟨a, ha⟩ := exists_root_deuring j
  have hc4 : (deuring a).c₄ = a * (a ^ 3 - 24) := by
    simp [deuring, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hΔ : (deuring a).Δ = a ^ 3 - 27 := by
    simp [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have h27 : ‖(27 : K)‖ = 1 := by
    have e : (27 : K) = 3 ^ 3 := by norm_num
    rw [e, norm_pow, h3, one_pow]
  have ha1 : ‖a‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hA3 : ‖a ^ 3‖ = ‖a‖ ^ 3 := norm_pow a 3
    have hbig : 1 < ‖a‖ ^ 3 := one_lt_pow₀ hlt (by norm_num)
    have h24 : ‖(24 : K)‖ ≤ 1 := by exact_mod_cast norm_nat_le_one (K := K) 24
    have hn1 : ‖a ^ 3 - 24‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hn2 : ‖a ^ 3 - 27‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = ‖a‖ ^ 12 := by
      rw [norm_mul, hA3, norm_pow, hn1]
      ring
    have hR : ‖j * (a ^ 3 - 27)‖ ≤ ‖a‖ ^ 3 := by
      rw [norm_mul, hn2]
      calc ‖j‖ * ‖a‖ ^ 3 ≤ 1 * ‖a‖ ^ 3 := by gcongr
        _ = ‖a‖ ^ 3 := one_mul _
    rw [ha] at hL
    have hlt2 : ‖a‖ ^ 3 < ‖a‖ ^ 12 := pow_lt_pow_right₀ hlt (by norm_num)
    linarith
  have hA3le : ‖a ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha1
  have hΔle : ‖a ^ 3 - 27‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA3le (by rw [norm_neg, h27]))
  have hΔ1 : ‖a ^ 3 - 27‖ = 1 := by
    by_contra hne
    have hlt : ‖a ^ 3 - 27‖ < 1 := lt_of_le_of_ne hΔle hne
    have e1 : a ^ 3 = 27 + (a ^ 3 - 27) := by ring
    have hA : ‖a ^ 3‖ = 1 := by
      rw [e1, norm_add_eq_left (by rw [h27]; exact hlt), h27]
    have e2 : a ^ 3 - 24 = 3 + (a ^ 3 - 27) := by ring
    have hB : ‖a ^ 3 - 24‖ = 1 := by
      rw [e2, norm_add_eq_left (by rw [h3]; exact hlt), h3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = 1 := by
      rw [norm_mul, hA, norm_pow, hB]
      norm_num
    rw [ha, norm_mul] at hL
    have h4 : ‖j‖ * ‖a ^ 3 - 27‖ < 1 := by
      calc ‖j‖ * ‖a ^ 3 - 27‖ ≤ 1 * ‖a ^ 3 - 27‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hlt
    linarith
  refine ⟨a, ha1, ?_, ?_⟩
  · rw [hc4, hΔ, ← ha]
    ring
  · rw [hΔ, hΔ1]

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.JetsTwo
section
universe u

noncomputable section

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type*} [CommRing K]

def ccd (i : Fin 2) (H : MvPowerSeries (Fin 2) K) : K :=
  MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := K) i H)

theorem hv {x y : MvPowerSeries (Fin 2) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    ∀ j, MvPowerSeries.constantCoeff (![x, y] j) = 0 := by
  intro j
  fin_cases j <;> simp [hx, hy]

theorem ccd_F (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (i : Fin 2) :
    ccd i (F.subst ![x, y]) = ccd 0 F * ccd i x + ccd 1 F * ccd i y := by
  unfold ccd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pderiv_subst (hv hx hy), map_sum, Fin.sum_univ_two]
  simp only [map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy), Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

theorem ccd_single (F : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    ccd i F = MvPowerSeries.coeff (Finsupp.single i 1) F := by
  unfold ccd
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL

open Formalism.G Formalism.ELL.FormalGroupQuadraticJets Formalism.G.LogCR

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.UnitCancel
section
universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

theorem unit_cancellation : Formalism.ELL.UnitCancel.{u} := by
  intro p _ K _ _ _ _ σ G b hb h
  obtain ⟨u, rfl⟩ := hb
  have := Formalism.ELL.N_padic_integer_smul p K σ _ h ((u⁻¹ : (ℤ_[p])ˣ) : ℤ_[p])
  convert this using 1
  rw [smul_smul, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, inv_mul_cancel]
  simp

end Formalism.ELL
end
end

