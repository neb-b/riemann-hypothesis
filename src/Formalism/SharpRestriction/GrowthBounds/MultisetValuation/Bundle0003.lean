module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaNuTwoLeOne
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section Shape

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ}

def ea_colH (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (J : ℕ) (s : Fin n') (c : ℕ) : ℕ :=
  ((Icc 1 (NN k1 t J)).filter fun i => (c : ℤ) < nu t lam0 w J s i).card

theorem ea_lamI_anti (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') {i i' : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ i')
    (h3 : i' ≤ k1 + 1) : lamI lam0 s i' ≤ lamI lam0 s i := by
  unfold lamI
  rw [dite_eq_left (show 1 ≤ i' ∧ i' ≤ k1 + 1 by omega), dite_eq_left (show 1 ≤ i ∧ i ≤ k1 + 1 by omega)]
  exact h.dom s (Fin.mk_le_mk.2 (by omega))

theorem ea_block_le {J i : ℕ} (h1 : k1 + 1 < i) (h2 : i ≤ NN k1 t J) : (i - (k1 + 2)) / (t + 1) + 1 ≤ J := by
  unfold NN at h2
  have h3 : i - (k1 + 2) < J * (t + 1) := by omega
  have h4 := (Nat.div_lt_iff_lt_mul (by omega : 0 < t + 1)).2 h3
  omega

theorem ea_nu_head (J : ℕ) (s : Fin n') {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k1 + 1) :
    nu t lam0 w J s i = lamI lam0 s i + w J s := by
  unfold nu
  rw [if_pos ⟨h1, h2⟩]

theorem ea_nu_tail (J : ℕ) (s : Fin n') {i : ℕ} (h1 : k1 + 1 < i) (h2 : i ≤ NN k1 t J) :
    nu t lam0 w J s i = -w ((i - (k1 + 2)) / (t + 1) + 1) s + w J s := by
  unfold nu
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

private theorem std_w_le_w_of_le (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') {l l' : ℕ} (hl : 1 ≤ l)
    (hll : l ≤ l') (hl' : l' ≤ m) : w l s ≤ w l' s := by
  induction l', hll using Nat.le_induction with
  | base => exact le_refl _
  | succ k hk ih => exact (ih (by omega)).trans (h.w_mono s k (by omega) (by omega))

theorem ea_nu_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m) (s : Fin n') (i : ℕ) :
    0 ≤ nu t lam0 w J s i := by
  have hk : 1 ≤ k1 := by have := h.r_pos; have := h.two_r; omega
  unfold nu
  split_ifs with h1 h2
  · have hw := std_w_le_w_of_le h s (le_refl 1) hJ1 hJ
    have hlow := (h.w_low s).2
    have hla : lam0 s (Fin.last k1) ≤ lamI lam0 s i := by
      unfold lamI
      rw [dite_eq_left h1]
      exact h.dom s (Fin.le_last _)
    omega
  · have hb := ea_block_le (k1 := k1) (t := t) h2.1 h2.2
    have hw := std_w_le_w_of_le h s (l := (i - (k1 + 2)) / (t + 1) + 1) (Nat.le_add_left 1 _) hb hJ
    omega
  · exact le_refl 0

theorem ea_nu_le_two (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ : J ≤ m) (s : Fin n') {i : ℕ}
    (h2 : 2 ≤ i) (h3 : i ≤ NN k1 t J) : nu t lam0 w J s i ≤ nu t lam0 w J s 2 := by
  have hk : 1 ≤ k1 := by have := h.r_pos; have := h.two_r; omega
  have e2 := ea_nu_head (t := t) (lam0 := lam0) (w := w) J s (i := 2) (by norm_num) (by omega)
  rw [e2]
  by_cases hi : i ≤ k1 + 1
  · rw [ea_nu_head J s (by omega) hi]
    have := ea_lamI_anti h s (i := 2) (i' := i) (by norm_num) h2 hi
    omega
  · rw [ea_nu_tail J s (by omega) h3]
    have hb := ea_block_le (k1 := k1) (t := t) (J := J) (i := i) (by omega) h3
    have hw := std_w_le_w_of_le h s (l := 1) (l' := (i - (k1 + 2)) / (t + 1) + 1) (le_refl 1) (Nat.le_add_left 1 _) (by omega)
    have hlow := (h.w_low s).2
    have hla : lam0 s (Fin.last k1) ≤ lamI lam0 s 2 := by
      unfold lamI
      rw [dite_eq_left (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 by omega)]
      exact h.dom s (Fin.le_last _)
    omega

theorem ea_nu_two_le_one (h : Std p n' k1 t m c r TT a b lam0 w) (J : ℕ) (s : Fin n') :
    nu t lam0 w J s 2 ≤ nu t lam0 w J s 1 := by
  have hk : 1 ≤ k1 := by have := h.r_pos; have := h.two_r; omega
  rw [ea_nu_head J s (i := 2) (by norm_num) (by omega), ea_nu_head J s (i := 1) (le_refl 1) (by omega)]
  have := ea_lamI_anti h s (i := 1) (i' := 2) (le_refl 1) (by norm_num) (by omega)
  omega

theorem ea_nu_le_one (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ : J ≤ m) (s : Fin n') {i : ℕ}
    (h1 : 1 ≤ i) (h3 : i ≤ NN k1 t J) : nu t lam0 w J s i ≤ nu t lam0 w J s 1 := by
  rcases Nat.lt_or_ge i 2 with hi | hi
  · have e : i = 1 := by omega
    subst e
    exact le_refl _
  · exact (ea_nu_le_two h hJ s hi h3).trans (ea_nu_two_le_one h J s)

theorem ea_nu_last (J : ℕ) (s : Fin n') {i : ℕ} (h1 : NN k1 t J < i) (h2 : i ≤ NN k1 t (J + 1)) :
    nu t lam0 w (J + 1) s i = 0 := by
  unfold NN at h1 h2
  unfold nu
  have e : (J + 1) * (t + 1) = J * (t + 1) + (t + 1) := by ring
  rw [if_neg (by omega), if_pos ⟨by omega, by unfold NN; omega⟩]
  have hq : (i - (k1 + 2)) / (t + 1) = J := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hq]
  ring

theorem ea_colH_le (J : ℕ) (s : Fin n') (x : ℕ) : ea_colH t lam0 w (J + 1) s x ≤ NN k1 t J := by
  unfold ea_colH
  calc _ ≤ (Icc 1 (NN k1 t J)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
        refine ⟨hi.1.1, ?_⟩
        by_contra hc
        push_neg at hc
        have e := ea_nu_last (t := t) (lam0 := lam0) (w := w) J s hc hi.1.2
        rw [e] at hi
        omega
    _ = NN k1 t J := by simp

theorem ea_NN_two (h : Std p n' k1 t m c r TT a b lam0 w) (J : ℕ) : 2 ≤ NN k1 t J := by
  have := h.r_pos
  have := h.two_r
  unfold NN
  omega

theorem ea_colH_eq_one (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ : J ≤ m) (s : Fin n') (x : ℕ)
    (hx : (x : ℤ) < nu t lam0 w J s 1) : ea_colH t lam0 w J s x = 1 ↔ nu t lam0 w J s 2 ≤ x := by
  unfold ea_colH
  have hN := ea_NN_two h J
  constructor
  · intro h1
    by_contra h2
    push_neg at h2
    have hsub : ({1, 2} : Finset ℕ) ⊆ (Icc 1 (NN k1 t J)).filter fun i => (x : ℤ) < nu t lam0 w J s i := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_refl 1, by omega⟩, hx⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by norm_num, hN⟩, h2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair (by norm_num)] at hc
    omega
  · intro h2
    rw [Finset.card_eq_one]
    refine ⟨1, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hi1, hi2⟩, hlt⟩
      by_contra hne
      have := ea_nu_le_two h hJ s (i := i) (by omega) hi2
      omega
    · rintro rfl
      exact ⟨⟨le_refl _, by omega⟩, hx⟩

theorem ea_card_one (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m) (s : Fin n') :
    (((range (nu t lam0 w J s 1).toNat).filter fun x => ea_colH t lam0 w J s x = 1).card : ℤ) =
      lamI lam0 s 1 - lamI lam0 s 2 := by
  have hk : 1 ≤ k1 := by have := h.r_pos; have := h.two_r; omega
  have h0 := ea_nu_nonneg h hJ1 hJ s 2
  have h21 := ea_nu_two_le_one h J s
  have hfil : ((range (nu t lam0 w J s 1).toNat).filter fun x => ea_colH t lam0 w J s x = 1) =
      Ico (nu t lam0 w J s 2).toNat (nu t lam0 w J s 1).toNat := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hx, h1⟩
      have hx' : (x : ℤ) < nu t lam0 w J s 1 := by omega
      have := (ea_colH_eq_one h hJ s x hx').1 h1
      exact ⟨by omega, hx⟩
    · rintro ⟨h2, hx⟩
      have hx' : (x : ℤ) < nu t lam0 w J s 1 := by omega
      exact ⟨hx, (ea_colH_eq_one h hJ s x hx').2 (by omega)⟩
  rw [hfil, Nat.card_Ico]
  have e1 := ea_nu_head (t := t) (lam0 := lam0) (w := w) J s (i := 1) (le_refl 1) (by omega)
  have e2 := ea_nu_head (t := t) (lam0 := lam0) (w := w) J s (i := 2) (by norm_num) (by omega)
  omega

theorem ea_sum_colH (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m) (s : Fin n') :
    ((∑ x ∈ range (nu t lam0 w J s 1).toNat, ea_colH t lam0 w J s x : ℕ) : ℤ) =
      ∑ i ∈ Icc 1 (NN k1 t J), nu t lam0 w J s i := by
  have key : ∑ x ∈ range (nu t lam0 w J s 1).toNat, ea_colH t lam0 w J s x =
      ∑ i ∈ Icc 1 (NN k1 t J), (nu t lam0 w J s i).toNat := by
    unfold ea_colH
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    have hn := ea_nu_nonneg h hJ1 hJ s i
    have hl := ea_nu_le_one h hJ s hi.1 hi.2
    rw [← Finset.card_filter]
    have hf : (range (nu t lam0 w J s 1).toNat).filter (fun x : ℕ => (x : ℤ) < nu t lam0 w J s i) =
        range (nu t lam0 w J s i).toNat := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hf, Finset.card_range]
  rw [key, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Int.toNat_of_nonneg (ea_nu_nonneg h hJ1 hJ s i)

end Shape

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem prime_cast_ne_zero : ((p : ℕ) : K0 p) ≠ 0 := by
  have h1 : ((p : ℕ) : WW p) ≠ 0 := WittVector.p_nonzero p (kb p)
  have h2 : algebraMap (WW p) (K0 p) ((p : ℕ) : WW p) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).2 h1
  simpa using h2

theorem pKf_ne (Y : Pend X) : ((p : ℕ) : X.G.Kf) ≠ 0 := by
  intro h
  have h1 : algebraMap X.G.Kf Y.Kc ((p : ℕ) : X.G.Kf) = 0 := by rw [h, map_zero]
  have h2 : algebraMap (K0 p) Y.Kc ((p : ℕ) : K0 p) = 0 := by
    rw [map_natCast] at h1 ⊢
    exact h1
  exact prime_cast_ne_zero ((map_eq_zero _).1 h2)

theorem algebraMap_inj (Y : Pend X) (he : 0 < X.eO) : Function.Injective (algebraMap X.G.O X.G.Kf) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 X.unif
  obtain ⟨u, hu⟩ := hn

  have h1 : algebraMap X.G.O X.G.Kf (X.vp ^ n) = 0 := by rw [← hu, map_mul, ha, zero_mul]
  have h2 : algebraMap X.G.O X.G.Kf X.vp = 0 := by
    rw [map_pow] at h1
    by_contra h
    exact pow_ne_zero n h h1
  obtain ⟨u', hu'⟩ := X.eO_spec
  have h3 : algebraMap X.G.O X.G.Kf ((p : X.G.O) * u') = 0 := by
    rw [hu', map_pow, h2, zero_pow (by omega)]
  rw [map_mul, map_natCast] at h3
  rcases mul_eq_zero.1 h3 with h | h
  · exact pKf_ne Y h
  · have : algebraMap X.G.O X.G.Kf ((u' : X.G.O) * ((u'⁻¹ : X.G.Oˣ) : X.G.O)) = 0 := by rw [map_mul, h, zero_mul]
    simp at this

theorem isFractionRing_of_pos_eO (Y : Pend X) (he : 0 < X.eO) : IsFractionRing X.G.O X.G.Kf := by
  have : FaithfulSMul X.G.O X.G.Kf := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_inj Y he)
  apply IsFractionRing.of_field
  intro z
  rcases Y.Oc_val (algebraMap X.G.Kf Y.Kc z) with h | h
  · obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z).1 h)
    exact ⟨a, 1, by simp [ha]⟩
  · rw [← map_inv₀] at h
    obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z⁻¹).1 h)
    exact ⟨1, a, by simp [ha]⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RelativePresentationOfD7
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

variable {p n' k1 t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ} {lam0 : Fin n' → Fin (k1 + 1) → ℤ}
  {w : ℕ → Fin n' → ℤ}

theorem w_one_le (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') :
    ∀ j, 1 ≤ j → j ≤ m → w 1 s ≤ w j s := by
  intro j hj hm
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj0 | hj'
    · subst hj0
      exact le_rfl
    · exact (ih hj' (by omega)).trans (h.w_mono s j hj' (by omega))

theorem lamI_ge_last (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k1 + 1) :
    lam0 s (Fin.last k1) ≤ lamI lam0 s i := by
  unfold lamI
  rw [dite_eq_left ⟨h1, h2⟩]
  exact h.dom s (Fin.le_last _)

theorem lamI_add_w_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (i j : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ k1 + 1) (hj : 1 ≤ j) (hm : j ≤ m) : 0 ≤ lamI lam0 s i + w j s := by
  have h3 := lamI_ge_last h s i h1 h2
  have h4 := w_one_le h s j hj hm
  have h5 := (h.w_low s).2
  linarith

theorem al_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') : 0 ≤ al TT lam0 s := by
  have hk : 2 ≤ k1 + 1 := by have := h.two_r; have := h.r_pos; omega
  unfold al
  split_ifs
  · unfold lamI
    rw [dite_eq_left (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 by omega), dite_eq_left (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 by omega)]
    exact sub_nonneg.mpr (h.dom s (Fin.mk_le_mk.mpr (by omega)))
  · exact le_rfl

theorem cap_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    0 ≤ cap t TT lam0 w j s := by
  have hk : 2 ≤ k1 + 1 := by have := h.two_r; have := h.r_pos; omega
  unfold cap nu
  split_ifs <;> first
    | omega
    | exact lamI_add_w_nonneg h s _ j (by omega) (by omega) hj hm

theorem gam_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) : 0 ≤ gam p := by
  unfold gam
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five_le
  apply div_nonneg
  · positivity
  · nlinarith

theorem Pr_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    0 ≤ Pr t r lam0 w j := by
  unfold Pr
  have hk := h.two_r
  have hr := h.r_pos
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro s _
    have hcard : (Icc (k1 + 2 - r) (k1 + 1)).card = r := by
      rw [Nat.card_Icc]
      omega
    have key : ∀ a ∈ Icc (k1 + 2 - r) (k1 + 1), (0 : ℝ) ≤ (w j s : ℝ) + (lamI lam0 s a : ℝ) := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have h0 := lamI_add_w_nonneg h s a j (by omega) ha.2 hj hm
      have h0' : (0 : ℤ) ≤ w j s + lamI lam0 s a := by linarith
      exact_mod_cast h0'
    have hsum := Finset.sum_nonneg key
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at hsum
    linarith
  · positivity

theorem gA_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) :
    -de p t TT lam0 w j ≤ gA p t TT lam0 w j := by
  unfold gA
  have key : ∀ X Y : ℝ, 0 ≤ X → -Y ≤ X - Y := fun X Y hX => by linarith
  apply key
  apply Finset.sum_nonneg
  intro s _
  apply tsum_nonneg
  intro e
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem gB_le (h : Std p n' k1 t m c r TT a b lam0 w) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    gB p t TT lam0 w j ≤ gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) - de p t TT lam0 w j := by
  unfold gB
  have key : ∀ A X Y : ℝ, 0 ≤ X → A - X - Y ≤ A - Y := fun A X Y hX => by linarith
  apply key
  apply Finset.sum_nonneg
  intro s _
  apply tsum_nonneg
  intro e
  apply le_min
  · apply div_nonneg
    · exact_mod_cast al_nonneg h s
    · positivity
  · exact_mod_cast cap_nonneg h _ j hj hm

theorem relative_presentation_of_d7 (D : Formalism.BasicNotions.D7) : RelativePresentationLiterature D := by
  intro p n' k1 t m c r TT a b lam0 w h
  unfold Sv
  have hA : 0 ≤ gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) :=
    mul_nonneg (gam_nonneg h) (Finset.sum_nonneg fun s _ => by exact_mod_cast al_nonneg h s)
  calc ∑ j ∈ Icc 1 m, max (gB p t TT lam0 w j - Pr t r lam0 w j - gA p t TT lam0 w j) 0
      ≤ ∑ j ∈ Icc 1 m, gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Icc] at hj
        have e1 := gB_le h j hj.1 hj.2
        have e2 := Pr_nonneg h j hj.1 hj.2
        have e3 := gA_ge p t TT lam0 w j
        exact max_le (by linarith) hA
    _ = (m : ℝ) * gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

