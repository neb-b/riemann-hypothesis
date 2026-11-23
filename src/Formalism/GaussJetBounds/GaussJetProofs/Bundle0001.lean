module

public import Formalism.GaussJetBounds.Bundle0001
public import Formalism.GaussJetBounds.StatementH

@[expose] public section

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.MinorProductSupportTop
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial

section ShapeSec

variable {σ : Type}

lemma shape_prod_eq {R : Type u} [CommRing R] {ι : Type*} (g : (σ →₀ ℕ) → ℕ) (hg0 : g 0 = 0)
    (hgadd : ∀ a b, g (a + b) = g a + g b) (f : ι → MvPolynomial σ R) (a : ι → ℕ) (s : Finset ι)
    (h : ∀ c ∈ s, ∀ mono ∈ (f c).support, g mono = a c) :
    ∀ mono ∈ (∏ c ∈ s, f c).support, g mono = ∑ c ∈ s, a c := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ mono hm
    rw [Finset.prod_empty, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h0
    · rw [← h0, hg0, Finset.sum_empty]
    · exact absurd rfl hm
  | insert c s hc ih =>
    intro h mono hm
    rw [Finset.prod_insert hc] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [hgadd, Finset.sum_insert hc, h c (Finset.mem_insert_self c s) m1 hm1,
      ih (fun c' hc' => h c' (Finset.mem_insert_of_mem hc')) m2 hm2]

lemma shape_prod_le {R : Type u} [CommRing R] {ι : Type*} (g : (σ →₀ ℕ) → ℕ) (hg0 : g 0 = 0)
    (hgadd : ∀ a b, g (a + b) = g a + g b) (f : ι → MvPolynomial σ R) (a : ι → ℕ) (s : Finset ι)
    (h : ∀ c ∈ s, ∀ mono ∈ (f c).support, g mono ≤ a c) :
    ∀ mono ∈ (∏ c ∈ s, f c).support, g mono ≤ ∑ c ∈ s, a c := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ mono hm
    rw [Finset.prod_empty, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h0
    · rw [← h0, hg0, Finset.sum_empty]
    · exact absurd rfl hm
  | insert c s hc ih =>
    intro h mono hm
    rw [Finset.prod_insert hc] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [hgadd, Finset.sum_insert hc]
    exact Nat.add_le_add (h c (Finset.mem_insert_self c s) m1 hm1)
      (ih (fun c' hc' => h c' (Finset.mem_insert_of_mem hc')) m2 hm2)

end ShapeSec

lemma shape_count_total {J : Type} [Fintype J] [DecidableEq J] {p : ℕ} (τ : Fin p → J) :
    (∑ j, (Finset.univ.filter (fun i => τ i = j)).card) = p := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin p)))
    (t := Finset.univ) (f := τ) (fun i _ => Finset.mem_coe.mpr (Finset.mem_univ (τ i)))
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

lemma shape_count_le_one {J : Type} [DecidableEq J] {p : ℕ} (τ : Fin p → J)
    (hτ : Function.Injective τ) (j : J) :
    (Finset.univ.filter (fun i => τ i = j)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hτ (ha.trans hb.symm)

def shapeSet {R : Type u} [CommRing R] {J : Type} {N1 p : ℕ} (A : Fin p → J → R)
    (I : Fin p → Fin N1) : Set (J × Fin N1 →₀ ℕ) :=
  {mono | ∃ τ : Fin p → J, Function.Injective τ ∧
    (∃ π : Equiv.Perm (Fin p), ∀ i, A (π i) (τ i) ≠ 0) ∧ mono = ∑ i, Finsupp.single (τ i, I i) 1}

lemma shape_minor {R : Type u} [CommRing R] {J : Type} [Fintype J] [DecidableEq J] {N1 p : ℕ}
    (A : Fin p → J → R) (I : Fin p → Fin N1) :
    (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (J × Fin N1) R)).det ∈
        restrictSupport R (shapeSet A I) := by
  classical
  have hτ : ∀ τ : Fin p → J, ∑ π : Equiv.Perm (Fin p), Equiv.Perm.sign π •
      ∏ i, (C (A (π i) (τ i)) * X (τ i, I i) : MvPolynomial (J × Fin N1) R) =
      C (Matrix.of fun (r i : Fin p) => A r (τ i)).det * ∏ i, X (τ i, I i) := by
    intro τ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.det_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Units.smul_def, map_zsmul, smul_mul_assoc, Finset.prod_mul_distrib, map_prod,
      Matrix.of_apply]
  rw [Matrix.det_apply]
  simp only [Matrix.of_apply]
  simp_rw [Finset.prod_univ_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun τ _ => ?_
  have hX : ∏ i, (X (τ i, I i) : MvPolynomial (J × Fin N1) R) =
      monomial (∑ i, Finsupp.single (τ i, I i) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [hτ τ, hX, C_mul_monomial, mul_one, monomial_mem_restrictSupport]
  by_cases hinj : Function.Injective τ
  · by_cases hd : (Matrix.of fun (r i : Fin p) => A r (τ i)).det = 0
    · exact Or.inr hd
    · left
      refine ⟨τ, hinj, ?_, rfl⟩
      by_contra hno
      push_neg at hno
      apply hd
      rw [Matrix.det_apply]
      refine Finset.sum_eq_zero fun π _ => ?_
      obtain ⟨i, hi⟩ := hno π
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), smul_zero]
  · right
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, i', hii, hne⟩ := hinj
    exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hii])

lemma shape_minor_mem {R : Type u} [CommRing R] {J : Type} [Fintype J] [DecidableEq J]
    {N1 p : ℕ} (A : Fin p → J → R) (I : Fin p → Fin N1) (mono : J × Fin N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (J × Fin N1) R)).det.support) :
    mono ∈ shapeSet A I := by
  have h := shape_minor A I
  rw [mem_restrictSupport_iff] at h
  exact h hm

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

theorem oddExponentCount : JCount := by
  intro l a hl ha
  set L := Nat.log l a with hLdef
  have hsub : (Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a) ⊆
      Finset.Icc (-(L : ℤ)) L := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    have h1 : j.natAbs ≤ L := Nat.le_log_of_pow_le (by omega) hj.2.2
    rcases Int.natAbs_eq j with h | h <;> omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have h2 : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
  rw [h2] at hcard
  have hL : (L : ℝ) ≤ Real.logb l a := Real.natLog_le_logb a l
  have h3 : ((((Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a)).card : ℕ) : ℝ)
      ≤ ((2 * L + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  push_cast at h3
  linarith

section DegProdSec

variable {σ κ : Type} [DecidableEq κ] (blk : σ → Option κ)

end DegProdSec

section BasisSec

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_det_le_one_of_entries {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro p _
  have hp : ‖∏ i, M (p i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => h _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs <;> rw [hs]
  · rw [one_smul]; exact hp
  · rw [Units.neg_smul, one_smul, norm_neg]; exact hp

lemma norm_inv_entry_le_one {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (h : ∀ i j, ‖M i j‖ ≤ 1) (hd : ‖M.det‖ = 1) (i j : n) : ‖M⁻¹ i j‖ ≤ 1 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    hd, inv_one, one_mul, Matrix.adjugate_apply]
  apply norm_det_le_one_of_entries
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact h _ _

end BasisSec

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.OneLetterRadiusIdentity
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem lw_cast_succ (l d : ℕ) (s : ZMod d) : ((lw l s : ℤ) : ZMod (l + 1)) = 1 := by
  unfold lw
  have hl : ((l : ℤ) : ZMod (l + 1)) = -1 := by
    rw [Int.cast_natCast]
    have h : ((l + 1 : ℕ) : ZMod (l + 1)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  split_ifs with h
  · rw [Int.cast_mul, Int.cast_one, one_mul, Int.cast_pow, hl]
    exact Even.neg_one_pow (Nat.even_iff.mpr h)
  · rw [Int.cast_mul, Int.cast_neg, Int.cast_one, Int.cast_pow, hl,
      Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]
    ring

theorem succ_dvd_total {l d : ℕ} (hl : 1 ≤ l) (hd : Even d) {ι : Type*} (n : ι →₀ ℕ)
    (f : ι → ZMod d)
    (h : ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l (f x)) :
    ((l + 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) := by
  have hl' : ((l : ℕ) : ZMod (l + 1)) = -1 := by
    have h : ((l + 1 : ℕ) : ZMod (l + 1)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  have h1 : ((l ^ d - 1 : ℕ) : ZMod (l + 1)) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, hl', hd.neg_one_pow, Nat.cast_one,
      sub_self]
  obtain ⟨c, hc⟩ := h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 := congrArg (fun z : ℤ => (z : ZMod (l + 1))) hc
  simp only [Int.cast_mul, Int.cast_sum, Int.cast_natCast, lw_cast_succ, mul_one, h1, zero_mul] at h2
  rw [Int.cast_sum]
  simpa only [Int.cast_natCast] using h2

theorem dot_const_wt {ι : Type*} (n : ι →₀ ℕ) (c : ℝ) :
    dot n (fun _ => c) = (∑ x ∈ n.support, (n x : ℝ)) * c := by
  simp only [dot, Finsupp.sum, Finset.sum_mul]

theorem weightQuantization : Quant.{u} := by
  unfold Quant
  intro K _ l d _ hl hd2 hd hl1 hl0 K0 hK0 c hc n hdiv hmono
  have hl2 : 2 ≤ l := hl.two_le
  obtain ⟨m, hm⟩ := succ_dvd_total (f := fun x : V2 d => x.2) (by omega) hd n hdiv
  unfold MonoWtGe at hmono ⊢
  rw [dot_const_wt] at hmono ⊢
  have hL : (2 : ℝ) ≤ l := by exact_mod_cast hl2
  have hNm : (∑ x ∈ n.support, (n x : ℝ)) = ((l : ℝ) + 1) * m := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hm
    push_cast at h
    exact h
  rw [hNm] at hmono ⊢
  by_cases hc0 : c = 0
  · rw [hc0, norm_zero]
    exact Real.rpow_nonneg hl0.le _
  obtain ⟨k, hk⟩ := hK0 c hc hc0
  rw [hk, ← Real.rpow_intCast] at hmono ⊢
  rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hl0 hl1] at hmono ⊢
  unfold rho at hmono ⊢
  have hL2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hL1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  set ρ := 1 / ((l : ℝ) ^ 2 - 1) with hρ
  set q := 1 / ((l : ℝ) - 1) with hq
  have hρ1 : ρ * ((l : ℝ) ^ 2 - 1) = 1 := by rw [hρ]; exact one_div_mul_cancel hL2.ne'
  have hq1 : q * ((l : ℝ) - 1) = 1 := by rw [hq]; exact one_div_mul_cancel hL1.ne'
  have hq0 : 0 < q := by rw [hq]; exact one_div_pos.mpr hL1
  have e1 : ((l : ℝ) + 1) * ρ = q := by
    rw [hρ, hq, mul_one_div, div_eq_div_iff hL2.ne' hL1.ne']
    ring
  have h1 : 1 - ((l : ℝ) + 1) * m ≤ k * ((l : ℝ) ^ 2 - 1) := by
    have h := mul_le_mul_of_nonneg_right hmono hL2.le
    have e : (ρ - ((l : ℝ) + 1) * m * ρ) * ((l : ℝ) ^ 2 - 1) = 1 - ((l : ℝ) + 1) * m := by
      linear_combination (1 - ((l : ℝ) + 1) * m) * hρ1
    linarith
  have h2 : (1 : ℝ) ≤ ((l : ℝ) + 1) * (k * ((l : ℝ) - 1) + m) := by nlinarith
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = k * ((l : ℤ) - 1) + m := ⟨_, rfl⟩
  have h3 : (1 : ℤ) ≤ ((l : ℤ) + 1) * z := by
    rw [hz]
    exact_mod_cast h2
  have h4 : 1 ≤ z := by
    by_contra hz1
    have hz0 : z ≤ 0 := by omega
    nlinarith
  have h5 : (1 : ℝ) ≤ k * ((l : ℝ) - 1) + m := by
    have h := h4
    rw [hz] at h
    exact_mod_cast h
  have h6 := mul_le_mul_of_nonneg_left h5 hq0.le
  have e2 : q * (k * ((l : ℝ) - 1) + m) = k + q * m := by linear_combination k * hq1
  have e3 : ((l : ℝ) + 1) * m * ρ = q * m := by linear_combination m * e1
  linarith

private theorem cancel_lemma {d : ℕ} {s s' : ZMod d} {a i : ℕ}
    (h : s + ((a + i : ℕ) : ZMod d) = s' + (a : ZMod d)) : s + (i : ZMod d) = s' := by
  rw [Nat.cast_add] at h
  linear_combination h

private theorem odd_of_odd_add_add_self {a i : ℕ} (h : Odd (a + i + a)) : Odd i := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k - a, by omega⟩

private theorem odd_of_odd_self_add_add {a i : ℕ} (h : Odd (a + (a + i))) : Odd i := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k - a, by omega⟩

private theorem exists_dTop_eq_le_of_odd_of_mem {d : ℕ} [NeZero d] {TT : Finset (ZMod d)} {s : ZMod d} {i : ℕ} (hi : Odd i)
    (hm : s + (i : ZMod d) ∈ TT) : ∃ e : ℕ, dTop d TT s = e ∧ e ≤ i := by
  have hle : dTop d TT s ≤ (i : ℕ∞) := by
    unfold dTop
    exact iInf₂_le i ⟨hi, hm⟩
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top i) hle)
  refine ⟨e, he.symm, ?_⟩
  rw [← he] at hle
  exact_mod_cast hle

theorem dualRadiiInequalities : ThmARadii := by
  unfold ThmARadii
  intro l d _ hl hd2 hd TT sig eps hdual hsig heps hT
  unfold IsDualAll at hdual
  have hL : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hL0 : (0 : ℝ) < l := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s s' α β τ τ' hτ hτ' hodd heq
    rcases le_total β α with h | h
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_add_add_self hodd
      have hs := cancel_lemma heq
      have hD := hdual s i hi
      rw [hs] at hD
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL
      calc (1 : ℝ) ≤ (l : ℝ) ^ β := hb
        _ = (l : ℝ) ^ β * 1 := (mul_one _).symm
        _ ≤ (l : ℝ) ^ β * ((l : ℝ) ^ i * sig s + sig s') := mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (l : ℝ) ^ β * (l : ℝ) ^ i * sig s + (l : ℝ) ^ β * sig s' := by ring
        _ ≤ (l : ℝ) ^ β * (l : ℝ) ^ i * τ + (l : ℝ) ^ β * τ' :=
          add_le_add (mul_le_mul_of_nonneg_left hτ (by positivity))
            (mul_le_mul_of_nonneg_left hτ' (by positivity))
        _ = (l : ℝ) ^ (β + i) * τ + (l : ℝ) ^ β * τ' := by rw [pow_add]
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_self_add_add hodd
      have hs := cancel_lemma heq.symm
      have hD := hdual s' i hi
      rw [hs] at hD
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ α := one_le_pow₀ hL
      calc (1 : ℝ) ≤ (l : ℝ) ^ α := hb
        _ = (l : ℝ) ^ α * 1 := (mul_one _).symm
        _ ≤ (l : ℝ) ^ α * ((l : ℝ) ^ i * sig s' + sig s) := mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (l : ℝ) ^ α * sig s + (l : ℝ) ^ α * (l : ℝ) ^ i * sig s' := by ring
        _ ≤ (l : ℝ) ^ α * τ + (l : ℝ) ^ α * (l : ℝ) ^ i * τ' :=
          add_le_add (mul_le_mul_of_nonneg_left hτ (by positivity))
            (mul_le_mul_of_nonneg_left hτ' (by positivity))
        _ = (l : ℝ) ^ α * τ + (l : ℝ) ^ (α + i) * τ' := by rw [pow_add]
  · intro s β j τ _ hτ
    have hb : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL
    have h1 := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ β)
    rw [pow_add]
    nlinarith
  · intro s α j τ _ hτ
    have hb : (1 : ℝ) ≤ (l : ℝ) ^ α := one_le_pow₀ hL
    have hj0 : (0 : ℝ) < (l : ℝ) ^ j := by positivity
    have h1 := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ α * (l : ℝ) ^ j)
    have e : (l : ℝ) ^ α * (l : ℝ) ^ j * ((l : ℝ) ^ j)⁻¹ = (l : ℝ) ^ α := by
      rw [mul_assoc, mul_inv_cancel₀ hj0.ne', mul_one]
    have h2 : 0 ≤ (l : ℝ) ^ α * eps s := mul_nonneg (by positivity) (heps s)
    rw [pow_add]
    linarith
  · intro s hs s' hs' α β hodd heq
    rcases le_total β α with h | h
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_add_add_self hodd
      have hss := cancel_lemma heq
      obtain ⟨e, he, hei⟩ := exists_dTop_eq_le_of_odd_of_mem (TT := TT) hi (hss ▸ hs')
      have hε := hT s hs e he
      have hpe : (0 : ℝ) < (l : ℝ) ^ e := by positivity
      have hei' : (l : ℝ) ^ e ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hL hei
      have h1 : (l : ℝ) ^ (β + i) * ((l : ℝ) ^ e)⁻¹ ≤ (l : ℝ) ^ (β + i) * eps s :=
        mul_le_mul_of_nonneg_left hε (by positivity)
      have h2 : (l : ℝ) ^ β ≤ (l : ℝ) ^ (β + i) * ((l : ℝ) ^ e)⁻¹ := by
        rw [pow_add, mul_assoc, le_mul_iff_one_le_right (by positivity), le_mul_inv_iff₀ hpe, one_mul]
        exact hei'
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL
      have h3 : 0 ≤ (l : ℝ) ^ β * eps s' := mul_nonneg (by positivity) (heps s')
      linarith
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hi := odd_of_odd_self_add_add hodd
      have hss := cancel_lemma heq.symm
      obtain ⟨e, he, hei⟩ := exists_dTop_eq_le_of_odd_of_mem (TT := TT) hi (hss ▸ hs)
      have hε := hT s' hs' e he
      have hpe : (0 : ℝ) < (l : ℝ) ^ e := by positivity
      have hei' : (l : ℝ) ^ e ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hL hei
      have h1 : (l : ℝ) ^ (α + i) * ((l : ℝ) ^ e)⁻¹ ≤ (l : ℝ) ^ (α + i) * eps s' :=
        mul_le_mul_of_nonneg_left hε (by positivity)
      have h2 : (l : ℝ) ^ α ≤ (l : ℝ) ^ (α + i) * ((l : ℝ) ^ e)⁻¹ := by
        rw [pow_add, mul_assoc, le_mul_iff_one_le_right (by positivity), le_mul_inv_iff₀ hpe, one_mul]
        exact hei'
      have hb : (1 : ℝ) ≤ (l : ℝ) ^ α := one_le_pow₀ hL
      have h3 : 0 ≤ (l : ℝ) ^ α * eps s := mul_nonneg (by positivity) (heps s)
      linarith

theorem oneLetterRadiusIdentity : OneLetterRadius := by
  unfold OneLetterRadius
  intro l hl
  have hL : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hL1 : (1 : ℝ) ≤ l := by linarith
  refine ⟨fun α β hodd => ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity), one_mul]
    rcases Nat.eq_zero_or_pos α with ha | ha
    · subst ha
      have hb : 1 ≤ β := by
        rcases hodd with ⟨k, hk⟩
        omega
      have h1 : (l : ℝ) ^ 1 ≤ (l : ℝ) ^ β := pow_le_pow_right₀ hL1 hb
      rw [pow_zero]
      rw [pow_one] at h1
      linarith
    · have h1 : (l : ℝ) ^ 1 ≤ (l : ℝ) ^ α := pow_le_pow_right₀ hL1 ha
      have h2 : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL1
      rw [pow_one] at h1
      linarith
  · unfold gam rho
    have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h2 : (l : ℝ) + 1 ≠ 0 := by linarith
    rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h1]
    ring

end Formalism.DworkPowerSeriesWeights
end
end

