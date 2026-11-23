module

public import Formalism.IncomingBounds.IncomingBound
public import Formalism.IncomingBounds.Bundle0001

@[expose] public section

-- bundled from Formalism.IncomingBounds.FlowDegreeBounds.BaseTermLeTopTerm
section
noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

end Formalism.IncomingBounds
end
end

-- bundled from Formalism.IncomingBounds.FlowDegreeBounds.LemmaF
section
noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

section Helpers

variable {l d : ℕ} [NeZero d]

private lemma oddLevels_one_le {d i : ℕ} (hi : i ∈ oddLevels d) : 1 ≤ i := by
  unfold oddLevels at hi
  have h := (Finset.mem_filter.1 hi).2.pos
  omega

private lemma one_mem_oddLevels {d : ℕ} (hd : 2 ≤ d) : 1 ∈ oddLevels d := by
  unfold oddLevels
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), odd_one⟩

private lemma gam_sub_inv (hl : 2 ≤ l) : gam l - 1 / ((l : ℝ) + 1) = rho l := by
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < (l : ℝ) ^ 2 - 1).ne'
  have h3 : (l : ℝ) + 1 ≠ 0 := (by linarith : (0 : ℝ) < (l : ℝ) + 1).ne'
  unfold gam rho
  rw [div_sub_div _ _ h1 h3, div_eq_div_iff (mul_ne_zero h1 h3) h1]
  ring

private theorem one_le_pow_of_one_le_real {a : ℝ} (ha : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith

private theorem pow_le_pow_right_of_one_le_real {a : ℝ} (ha : 1 ≤ a) {m n : ℕ} (h : m ≤ n) : a ^ m ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have h1 := one_le_pow_of_one_le_real ha k
  have h2 : 0 ≤ a ^ m := pow_nonneg (by linarith) m
  nlinarith

private theorem self_le_pow_of_one_le_of_one_le_exp {a : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : 1 ≤ n) : a ≤ a ^ n := by
  have h := pow_le_pow_right_of_one_le_real ha hn
  rwa [pow_one] at h

private lemma sum_incoming (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := by
  calc ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i
      = ∑ i ∈ oddLevels d, ∑ s : ZMod d, x (s - (i : ZMod d)) i := Finset.sum_comm
    _ = ∑ i ∈ oddLevels d, ∑ s : ZMod d, x s i :=
        Finset.sum_congr rfl fun i _ =>
          Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => rfl)
    _ = ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := Finset.sum_comm

private lemma flowVal_mul_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    ((l : ℝ) + 1) * flowVal d x ≤ ∑ s, D s := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : ∑ s : ZMod d, ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
      (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i)) ≤ ∑ s, D s :=
    Finset.sum_le_sum fun s _ => hx.2 s
  rw [Finset.sum_add_distrib, sum_incoming x] at h1
  have h2 : (l : ℝ) * flowVal d x ≤ ∑ s : ZMod d, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
    unfold flowVal
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (self_le_pow_of_one_le_of_one_le_exp hl1 (oddLevels_one_le hi)) (hx.1 s i)
  have h3 : flowVal d x = ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := rfl
  rw [add_mul, one_mul]
  linarith

private theorem le_div_of_mul_le_of_pos_flow_degree_bounds {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  have h2 := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc.le)
  rwa [mul_inv_cancel_right₀ hc.ne', ← div_eq_mul_inv] at h2

private lemma maxFlow_le (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    maxFlow l d D ≤ (∑ s, D s) / ((l : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  unfold maxFlow
  apply Real.sSup_le
  · rintro t ⟨x, hx, rfl⟩
    exact le_div_of_mul_le_of_pos_flow_degree_bounds hpos (by rw [mul_comm]; exact flowVal_mul_le hl hx)
  · exact div_nonneg (Finset.sum_nonneg fun s _ => hD s) hpos.le

private lemma le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  unfold maxFlow
  refine le_csSup ⟨(∑ s, D s) / ((l : ℝ) + 1), ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨y, hy, rfl⟩
  exact le_div_of_mul_le_of_pos_flow_degree_bounds hpos (by rw [mul_comm]; exact flowVal_mul_le hl hy)

private def altNum (l d : ℕ) (D : ZMod d → ℝ) (s : ZMod d) : ℝ :=
  ∑ r ∈ Finset.range d, (-1 : ℝ) ^ r * ((l : ℝ) ^ (r + 1))⁻¹ * D (s - (r : ZMod d))

private lemma altNum_rec (hl : 1 ≤ l) (hev : Even d) (D : ZMod d → ℝ) (s : ZMod d) :
    (l : ℝ) * altNum l d D s + altNum l d D (s - 1) = (1 - ((l : ℝ) ^ d)⁻¹) * D s := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hinv : (l : ℝ) * (l : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hl0.ne'
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, ∀ r, f r = (-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d)) :=
    ⟨_, fun _ => rfl⟩
  have h1 : (l : ℝ) * altNum l d D s = ∑ r ∈ Finset.range d, f r := by
    unfold altNum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hf, pow_succ, mul_inv]
    linear_combination ((-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d))) * hinv
  have h2 : altNum l d D (s - 1) = ∑ r ∈ Finset.range d, -f (r + 1) := by
    unfold altNum
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hf]
    have e : s - 1 - (r : ZMod d) = s - ((r + 1 : ℕ) : ZMod d) := by push_cast; ring
    rw [e]
    ring
  have e0 : ((0 : ℕ) : ZMod d) = 0 := Nat.cast_zero
  have ed : ((d : ℕ) : ZMod d) = 0 := ZMod.natCast_self d
  have eneg : ((-1 : ℝ)) ^ d = 1 := hev.neg_one_pow
  calc (l : ℝ) * altNum l d D s + altNum l d D (s - 1)
      = ∑ r ∈ Finset.range d, (f r - f (r + 1)) := by
        rw [h1, h2, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun r _ => (sub_eq_add_neg _ _).symm
    _ = f 0 - f d := Finset.sum_range_sub' f d
    _ = (1 - ((l : ℝ) ^ d)⁻¹) * D s := by
        rw [hf, hf, e0, ed, sub_zero, eneg]
        ring

private lemma sum_range_two_mul (f : ℕ → ℝ) (m : ℕ) :
    ∑ r ∈ Finset.range (2 * m), f r = ∑ u ∈ Finset.range m, (f (2 * u) + f (2 * u + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    simp only [Finset.sum_range_succ, ih]
    ring

private theorem sum_deficit_le_Fnum_of_isDual (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D sig : ZMod d → ℝ} (hD : 0 ≤ D) (hsig : IsDual l d sig) :
    ∑ s, D s * (gam l - sig s) ≤ Fnum l d D := by
  have h := (hA l d hl hd hev D hD).2
  exact h.2 ⟨sig, hsig, rfl⟩

private theorem exists_isDual_Fnum_eq_sum_deficit (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    ∃ sig, IsDual l d sig ∧ Fnum l d D = ∑ s, D s * (gam l - sig s) :=
  (hA l d hl hd hev D hD).2.1

private theorem sum_add_apply_mul (D E f : ZMod d → ℝ) :
    ∑ s, (D + E) s * f s = ∑ s, D s * f s + ∑ s, E s * f s := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.add_apply, add_mul]

private lemma altNum_nonneg (hl : 1 ≤ l) (hev : Even d) {D : ZMod d → ℝ}
    (hr : ∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s) (s : ZMod d) : 0 ≤ altNum l d D s := by
  obtain ⟨m, hm⟩ := hev
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hli : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 hl0
  have hinv : (l : ℝ) * (l : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hl0.ne'
  have hrange : Finset.range d = Finset.range (2 * m) := congrArg Finset.range (by omega)
  unfold altNum
  rw [hrange, sum_range_two_mul]
  refine Finset.sum_nonneg fun u _ => ?_
  have e1 : ((-1 : ℝ)) ^ (2 * u) = 1 := Even.neg_one_pow ⟨u, two_mul u⟩
  have e2 : ((-1 : ℝ)) ^ (2 * u + 1) = -1 := Odd.neg_one_pow ⟨u, rfl⟩
  have e3 : ((l : ℝ) ^ (2 * u + 1 + 1))⁻¹ = ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ := by
    rw [pow_succ (l : ℝ) (2 * u + 1), mul_inv]
  have hp : (0 : ℝ) < ((l : ℝ) ^ (2 * u + 1))⁻¹ := inv_pos.2 (pow_pos hl0 _)
  have hab := hr (s - ((2 * u : ℕ) : ZMod d)) (s - ((2 * u + 1 : ℕ) : ZMod d))
  have hint_r := mul_nonneg (mul_nonneg hp.le hli.le) (sub_nonneg.2 hab)
  have key : (1 : ℝ) * ((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)) +
      -1 * (((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹) * D (s - ((2 * u + 1 : ℕ) : ZMod d)) =
      ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ *
        ((l : ℝ) * D (s - ((2 * u : ℕ) : ZMod d)) - D (s - ((2 * u + 1 : ℕ) : ZMod d))) := by
    linear_combination (-(((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)))) * hinv
  simp only [e1, e2, e3]
  linarith

end Helpers

theorem lemmaFc_of (hF : FlowAttained) (hA : LemmaFa) : LemmaFc := by
  intro l d _ hl hd hev D E sig hD hE hopt
  have hDE : 0 ≤ D + E := add_nonneg hD hE
  obtain ⟨hsig, hdef⟩ := hopt
  constructor
  · have h1 := sum_deficit_le_Fnum_of_isDual hA hl hd hev hDE hsig
    rw [sum_add_apply_mul, ← hdef] at h1
    have h2 : -(∑ s, E s * max (sig s - gam l) 0) ≤ ∑ s, E s * (gam l - sig s) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      have hEs : 0 ≤ E s := hE s
      have hm := le_max_left (sig s - gam l) 0
      nlinarith
    linarith
  · obtain ⟨sg, hsg, e⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hDE
    have h3 := sum_deficit_le_Fnum_of_isDual hA hl hd hev hD hsg
    have h4 : ∑ s, E s * (gam l - sg s) ≤ gam l * ∑ s, E s := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hEs : 0 ≤ E s := hE s
      have hs0 : 0 ≤ sg s := (hsg.1 s).1
      nlinarith
    rw [e, sum_add_apply_mul]
    linarith

end Formalism.IncomingBounds
end
end

-- bundled from Formalism.IncomingBounds.FlowDegreeBounds.PadicValFactorialRatioProd
section
noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

private theorem one_add_mul_le_one_add_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : 1 + k * x ≤ (1 + x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg hx hx),
      mul_le_mul_of_nonneg_right ih (by linarith : (0:ℝ) ≤ 1 + x)]

theorem padicValuationGain : ValGain := by
  intro l hl
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hB : 0 < (l : ℝ) - 1 := by linarith
  refine ⟨?_, ?_⟩
  · intro n hn
    have hle : l ^ padicValNat l n ≤ n := Nat.le_of_dvd (by omega) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have hleR : (l : ℝ) ^ padicValNat l n ≤ n := by exact_mod_cast hle
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) - 1) hB.le (padicValNat l n)
    rw [show (1 : ℝ) + ((l : ℝ) - 1) = l by ring] at hb
    rw [le_sub_iff_add_le, div_add' _ _ _ hB.ne', div_le_div_iff_of_pos_right hB]
    linarith
  · intro e
    unfold rho
    have hA : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
    have hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1 := mul_one_div_cancel hA.ne'
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) ^ 2 - 1) hA.le e
    rw [show (1 : ℝ) + ((l : ℝ) ^ 2 - 1) = (l : ℝ) ^ 2 by ring] at hb
    have hm := mul_le_mul_of_nonneg_right hb (one_div_pos.2 hA).le
    have he : (1 + (e : ℝ) * ((l : ℝ) ^ 2 - 1)) * (1 / ((l : ℝ) ^ 2 - 1)) =
        1 / ((l : ℝ) ^ 2 - 1) + e := by
      linear_combination (e : ℝ) * hq
    linarith

end Formalism.IncomingBounds
end
end

