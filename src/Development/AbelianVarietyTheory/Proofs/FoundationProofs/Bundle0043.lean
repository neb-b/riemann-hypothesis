module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImage
section
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_adjoin_mem_span : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] (s : Set S) (D : S → M), IsDerOn (Algebra.adjoin A s) D →
    ∀ x ∈ Algebra.adjoin A s, D x ∈ Submodule.span S (D '' s) := by
  intro A S M _ _ _ _ _ s D hD x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | algebraMap r => rw [hD.alg]; exact zero_mem _
  | add x y hx hy ihx ihy => rw [hD.add x hx y hy]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [hD.mul x hx y hy]
    exact add_mem (Submodule.smul_mem _ _ ihy) (Submodule.smul_mem _ _ ihx)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnVanishingOnSubalgebraKilledSq
section
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_killed_sq : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → (∀ β ∈ B, D β = 0) →
      ∀ x ∈ C, (e * e) • D x = 0 := by
  intro A S M _ _ _ _ _ B C tr n a b e h D hD hB x hx
  have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → S), (∀ i, f i ∈ C) →
      D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hD.alg 0
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        hD.add _ (hf j) _ (Subalgebra.sum_mem _ (fun i _ => hf i)), ih]
  have key : ∀ y ∈ C, e • D y = ∑ j, tr (b j * y) • D (a j) := by
    intro y hy
    have heC : e ∈ C := h.le h.e_mem
    have h1 : D (e * y) = e • D y := by
      rw [hD.mul e heC y hy, hB e h.e_mem, smul_zero, add_zero]
    rw [← h1, ← h.left y hy, hsum _ _ (fun j => C.mul_mem (h.a_mem j)
      (h.le (h.tr_mem _ (C.mul_mem (h.b_mem j) hy))))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have ht : tr (b j * y) ∈ B := h.tr_mem _ (C.mul_mem (h.b_mem j) hy)
    rw [hD.mul _ (h.a_mem j) _ (h.le ht), hB _ ht, smul_zero, zero_add]
  have L : ∑ i, b i • (e • D (x * a i)) = ∑ j, (e * x * b j) • D (a j) := by
    simp_rw [key _ (C.mul_mem hx (h.a_mem _)), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_smul]
    congr 1
    have hr := h.right (b j * x) (C.mul_mem (h.b_mem j) hx)
    calc ∑ i, b i * tr (b j * (x * a i)) = ∑ i, b i * tr (a i * (b j * x)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show b j * (x * a i) = a i * (b j * x) by ring]
      _ = e * (b j * x) := hr
      _ = e * x * b j := by ring
  have R : ∑ i, b i • (e • D (x * a i)) = ∑ j, (e * x * b j) • D (a j) + (e * e) • D x := by
    simp_rw [hD.mul x hx _ (h.a_mem _), smul_add, smul_smul, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1; ring
    · congr 1
      rw [show e * e = e * ∑ i, a i * b i by rw [h.sum], Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
  have := R.symm.trans L
  simpa using this

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCongr
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem dia_congr : ∀ (N l : ℕ) (k d : ℤ) (σ τ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    GlobalTheory.Hk.IsDia N l d τ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.dia k σ ⇑f = GlobalTheory.Hk.dia k τ ⇑f := by
  intro N l k d σ τ hN hσ hτ f
  have h := _root_.GlobalTheory.Hk.dia_mul_inv_mem_lev N l d σ τ hN hσ hτ
  have hτ' : τ = (τ * σ⁻¹) * σ := by group
  have hinv : ⇑f ∣[k] (τ * σ⁻¹) = ⇑f :=
    SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ h)
  unfold GlobalTheory.Hk.dia
  rw [hτ', SlashAction.slash_mul, hinv]

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivLeRpowThreeQuarters
section
open Finset

namespace GlobalTheory

theorem card_class_in_dyadic_le (Y : ℝ) (hY : 0 ≤ Y) (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y)
    (hc : ∀ g ∈ T, ∀ g' ∈ T, g ≡ g' [MOD M]) : (T.card : ℝ) ≤ Y / M + 1 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hne
  · have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    rw [Finset.card_empty, Nat.cast_zero]
    have := div_nonneg hY hMr.le
    linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have ha := T.min'_mem hne
  have key : ∀ g ∈ T, T.min' hne ≤ g ∧ M ∣ g - T.min' hne := fun g hg =>
    ⟨T.min'_le g hg, (Nat.modEq_iff_dvd' (T.min'_le g hg)).1 (hc _ ha g hg)⟩
  have hmaps : ∀ g ∈ T, (g - T.min' hne) / M ∈ Finset.range (⌊Y / M⌋₊ + 1) := by
    intro g hg
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    rw [le_div_iff₀ hMr]
    have h1 : (g - T.min' hne) / M * M ≤ g - T.min' hne := Nat.div_mul_le_self _ _
    have h2 : ((g - T.min' hne : ℕ) : ℝ) = g - T.min' hne := Nat.cast_sub (key g hg).1
    have h3 := (hT g hg).2
    have h4 := (hT _ ha).1
    calc (((g - T.min' hne) / M : ℕ) : ℝ) * M = (((g - T.min' hne) / M * M : ℕ) : ℝ) := by
          rw [Nat.cast_mul]
      _ ≤ ((g - T.min' hne : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ Y := by rw [h2]; linarith
  have hinj : Set.InjOn (fun g => (g - T.min' hne) / M) T := by
    intro g hg g' hg' h
    have h' : (g - T.min' hne) / M = (g' - T.min' hne) / M := h
    have e1 := Nat.div_mul_cancel (key g hg).2
    have e2 := Nat.div_mul_cancel (key g' hg').2
    have e3 : g - T.min' hne = g' - T.min' hne := by rw [← e1, ← e2, h']
    have := (key g hg).1
    have := (key g' hg').1
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  calc (T.card : ℝ) ≤ ((⌊Y / M⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ Y / M + 1 := by
        push_cast
        linarith [Nat.floor_le (div_nonneg hY hMr.le)]

theorem div_le_rpow_three_quarters (Y M : ℝ) (hY : 0 < Y) (hM : 0 < M) (h : Y < M ^ 4) :
    Y / M ≤ Y ^ ((3 : ℝ) / 4) := by
  have hq : 0 < Y ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hY _
  have h4 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le]
    norm_num
  have hlt : Y ^ ((1 : ℝ) / 4) < M := by
    have : (Y ^ ((1 : ℝ) / 4)) ^ 4 < M ^ 4 := by rw [h4]; exact h
    exact lt_of_pow_lt_pow_left₀ 4 hM.le this
  have e : Y ^ ((3 : ℝ) / 4) = Y / Y ^ ((1 : ℝ) / 4) := by
    rw [show (3 : ℝ) / 4 = 1 - 1 / 4 by norm_num, Real.rpow_sub hY, Real.rpow_one]
  rw [e]
  exact div_le_div_of_nonneg_left hY.le hq hlt.le

theorem card_exc_fixed_le (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) (Y : ℝ) (hY : 2 ≤ Y) (ℓ d : ℕ)
    (hd : 1 ≤ d) (T : Finset ℕ)
    (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ Formalism.CyclotomicNorms.Exc g d ℓ) :
    (T.card : ℝ) ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  have hY0 : 0 ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  rcases T.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity) (by linarith)
  obtain ⟨g0, hg0, hmin⟩ := T.exists_min_image (fun g => padicValNat ℓ (g ^ d - 1)) hne
  obtain ⟨w, hw⟩ : ∃ w, w = padicValNat ℓ (g0 ^ d - 1) := ⟨_, rfl⟩
  have hmin' : ∀ g ∈ T, w ≤ padicValNat ℓ (g ^ d - 1) := by
    intro g hg
    rw [hw]
    exact hmin g hg
  have hg1 : ∀ g ∈ T, 1 ≤ g := fun g hg => by
    have h := (hT g hg).1
    have : (1 : ℝ) ≤ g := by linarith
    exact_mod_cast this
  have hgd : ∀ g ∈ T, 1 ≤ g ^ d := fun g hg => Nat.one_le_pow _ _ (hg1 g hg)
  obtain ⟨hℓ, hlt0⟩ := (hT g0 hg0).2.2
  rw [← hw] at hlt0
  have hw1 : 1 ≤ w := by
    by_contra h0
    have h00 : w = 0 := by omega
    rw [h00, mul_zero, pow_zero] at hlt0
    have := hgd g0 hg0
    omega
  have hM0 : 0 < ℓ ^ w := pow_pos hℓ.pos _
  have : NeZero (ℓ ^ w) := ⟨hM0.ne'⟩
  have hroot : ∀ g ∈ T, ((g : ZMod (ℓ ^ w))) ^ d = 1 := by
    intro g hg
    have h1 : ℓ ^ w ∣ g ^ d - 1 := (pow_dvd_pow ℓ (hmin' g hg)).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have h2 : 1 ≡ g ^ d [MOD ℓ ^ w] := (Nat.modEq_iff_dvd' (hgd g hg)).2 h1
    have h3 := (ZMod.natCast_eq_natCast_iff 1 (g ^ d) (ℓ ^ w)).2 h2
    push_cast at h3
    exact h3.symm
  have hYM : Y < ((ℓ ^ w : ℕ) : ℝ) ^ 4 := by
    have h1 : (g0 : ℝ) ≤ ((g0 ^ d : ℕ) : ℝ) := by exact_mod_cast Nat.le_self_pow (by omega) g0
    have h2 : g0 ^ d < (ℓ ^ w) ^ 4 := by rw [← pow_mul, mul_comm]; exact hlt0
    have h3 : ((g0 ^ d : ℕ) : ℝ) < (((ℓ ^ w) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h2
    rw [Nat.cast_pow (ℓ ^ w) 4] at h3
    linarith [(hT g0 hg0).1]
  have hfib : ∀ a ∈ T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))),
      ((T.filter fun g : ℕ => (g : ZMod (ℓ ^ w)) = a).card : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    intro a _
    have h1 := card_class_in_dyadic_le Y (by linarith) (ℓ ^ w) hM0
      (T.filter fun g : ℕ => (g : ZMod (ℓ ^ w)) = a)
      (fun g hg => ⟨(hT g (Finset.mem_filter.1 hg).1).1, (hT g (Finset.mem_filter.1 hg).1).2.1⟩)
      (fun g hg g' hg' => (ZMod.natCast_eq_natCast_iff g g' (ℓ ^ w)).1
        ((Finset.mem_filter.1 hg).2.trans (Finset.mem_filter.1 hg').2.symm))
    have h2 := div_le_rpow_three_quarters Y ((ℓ ^ w : ℕ) : ℝ) (by linarith)
      (by exact_mod_cast hM0) hYM
    linarith
  have himg : (T.image fun g : ℕ => (g : ZMod (ℓ ^ w))).card ≤ 2 * d := by
    have hsub : T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))) ⊆
        Finset.univ.filter (fun x : ZMod (ℓ ^ w) => x ^ d = 1) := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hroot g hg⟩
    refine (Finset.card_le_card hsub).trans ?_
    have h1 := (hR ℓ w d hℓ hw1 hd).2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    exact h1
  rw [Finset.card_eq_sum_card_image (fun g : ℕ => (g : ZMod (ℓ ^ w))) T]
  push_cast
  calc ∑ a ∈ T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))),
        ((T.filter fun g : ℕ => (g : ZMod (ℓ ^ w)) = a).card : ℝ)
      ≤ ∑ a ∈ T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))), (Y ^ ((3 : ℝ) / 4) + 1) :=
        Finset.sum_le_sum hfib
    _ = ((T.image fun g : ℕ => (g : ZMod (ℓ ^ w))).card : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact_mod_cast himg

theorem card_mem_BB_fixed_le (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) (Y : ℝ) (hY : 2 ≤ Y) (ℓ N : ℕ)
    (T : Finset ℕ) (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ ℓ ∈ Formalism.CyclotomicNorms.BB N g) :
    (T.card : ℝ) ≤ 1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  have hY0 : 0 ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  have hsub : T ⊆ T.filter (fun g => g = ℓ) ∪
      (Finset.Icc 1 N).biUnion (fun d => T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)) := by
    intro g hg
    have h := (hT g hg).2.2
    simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at h
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
    rcases h with h | ⟨d, hd1, hdN, hex⟩
    · exact Or.inl ⟨hg, h.symm⟩
    · exact Or.inr ⟨d, Finset.mem_Icc.2 ⟨hd1, hdN⟩, Finset.mem_filter.2 ⟨hg, hex⟩⟩
  have h0 : (T.filter (fun g => g = ℓ)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]
  have hd : ∀ d ∈ Finset.Icc 1 N, ((T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card : ℝ) ≤
      2 * N * (Y ^ ((3 : ℝ) / 4) + 1) := by
    intro d hdm
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.1 hdm
    have h1 := card_exc_fixed_le hR Y hY ℓ d hd1 (T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ))
      (fun g hg => ⟨(hT g (Finset.mem_filter.1 hg).1).1, (hT g (Finset.mem_filter.1 hg).1).2.1,
        (Finset.mem_filter.1 hg).2⟩)
    have hdN' : (d : ℝ) ≤ N := by exact_mod_cast hdN
    have h2 := mul_le_mul_of_nonneg_right hdN' (by linarith : (0 : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1)
    linarith
  have hc1 : T.card ≤ (T.filter (fun g => g = ℓ)).card +
      ∑ d ∈ Finset.Icc 1 N, (T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hc2 : (T.card : ℝ) ≤
      1 + ∑ d ∈ Finset.Icc 1 N, ((T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card : ℝ) := by
    have h1 := (Nat.cast_le (α := ℝ)).2 hc1
    push_cast at h1
    have h0' : ((T.filter (fun g => g = ℓ)).card : ℝ) ≤ 1 := by exact_mod_cast h0
    linarith
  have hc3 : ∑ d ∈ Finset.Icc 1 N, ((T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card : ℝ) ≤
      N * (2 * N * (Y ^ ((3 : ℝ) / 4) + 1)) := by
    calc _ ≤ ∑ d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := Finset.sum_le_sum hd
      _ = N * (2 * N * (Y ^ ((3 : ℝ) / 4) + 1)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have e : (N : ℝ) * (2 * N * (Y ^ ((3 : ℝ) / 4) + 1)) = 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := by
    ring
  linarith

theorem choiceCount_of (hB : Formalism.CyclotomicNorms.BBCount) (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) :
    Formalism.CyclotomicNorms.ChoiceCount := by
  intro Y N g₁ hY hN hg₁ hg₁' S hS
  classical
  have h2 : 2 ≤ g₁ := by
    have : (2 : ℝ) ≤ g₁ := by linarith
    exact_mod_cast this
  obtain ⟨hfin, hcard⟩ := (hB g₁ h2).2 N
  have hsub : S ⊆ hfin.toFinset.biUnion (fun ℓ => S.filter (fun g => ℓ ∈ Formalism.CyclotomicNorms.BB N g)) := by
    intro g hg
    obtain ⟨ℓ, hℓ1, hℓ2⟩ := (hS g hg).2.2
    exact Finset.mem_biUnion.2 ⟨ℓ, hfin.mem_toFinset.2 hℓ2, Finset.mem_filter.2 ⟨hg, hℓ1⟩⟩
  have hbound : ∀ ℓ ∈ hfin.toFinset, ((S.filter (fun g => ℓ ∈ Formalism.CyclotomicNorms.BB N g)).card : ℝ) ≤
      1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := fun ℓ _ =>
    card_mem_BB_fixed_le hR Y hY ℓ N _ (fun g hg => ⟨(hS g (Finset.mem_filter.1 hg).1).1,
      (hS g (Finset.mem_filter.1 hg).1).2.1, (Finset.mem_filter.1 hg).2⟩)
  have hFc : (hfin.toFinset.card : ℝ) ≤ 3 * N + 1 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast hcard
  have hc : (S.card : ℝ) ≤
      ∑ ℓ ∈ hfin.toFinset, ((S.filter (fun g => ℓ ∈ Formalism.CyclotomicNorms.BB N g)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hY0 : 0 ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  calc (S.card : ℝ) ≤ _ := hc
    _ ≤ ∑ ℓ ∈ hfin.toFinset, (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) :=
        Finset.sum_le_sum hbound
    _ = hfin.toFinset.card * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * N + 1) * (1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) :=
        mul_le_mul_of_nonneg_right hFc
          (add_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith)))

theorem choice_count : Formalism.CyclotomicNorms.ChoiceCount := choiceCount_of exceptional_set_count rootsOfUnityCount

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralChangeOfVariablesIntMatrixSlash
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerChangeGL
open GlobalTheory.EichlerChange

lemma toGL_entry (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) (i j : Fin 2) :
    (toGL g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  unfold toGL; rw [dite_eq_right h]; rfl

lemma toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) :
    (toGL g).det.val = ((g.det : ℤ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two,
    toGL_entry g h, toGL_entry g h, toGL_entry g h, toGL_entry g h]
  push_cast
  ring

lemma toGL_det_pos (g : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < g.det) : 0 < (toGL g).det.val := by
  rw [toGL_det g h.ne']
  exact_mod_cast h

lemma denom_toGL (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) (z : ℂ) :
    denom (toGL g) z = ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) := by
  rw [denom, toGL_entry g h, toGL_entry g h]
  simp

lemma coe_toGL_smul (g : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < g.det) (τ : ℍ) :
    ((toGL g • τ : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * τ + ((g 0 1 : ℤ) : ℂ)) /
      (((g 1 0 : ℤ) : ℂ) * τ + ((g 1 1 : ℤ) : ℂ)) := by
  rw [coe_smul_of_det_pos (toGL_det_pos g h), denom_toGL g h.ne', num, toGL_entry g h.ne',
    toGL_entry g h.ne']
  simp

lemma slash_toGL (k : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < g.det) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toGL g) τ = f (toGL g • τ) * ((g.det : ℤ) : ℂ) ^ (k - 1) *
      (((g 1 0 : ℤ) : ℂ) * τ + ((g 1 1 : ℤ) : ℂ)) ^ (-k) := by
  have hpos := toGL_det_pos g h
  rw [ModularForm.slash_apply, σ, if_pos hpos, abs_of_pos hpos, toGL_det g h.ne', denom_toGL g h.ne']
  simp

lemma eichler_I (w : ℕ) (h : ℍ → ℂ) : eichler w h UpperHalfPlane.I = 0 := by
  simp [eichler]

theorem polySlash_eichler_toGL_smul : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
    ∀ (β : Matrix (Fin 2) (Fin 2) ℤ), 0 < β.det → ∀ τ : ℍ,
      slP (k - 2) β (eichler (k - 2) f (toGL β • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] toGL β) τ +
        slP (k - 2) β (eichler (k - 2) f (toGL β • UpperHalfPlane.I)) := by
  intro k hk f hf β hβ τ
  obtain ⟨w, rfl⟩ : ∃ w, k = w + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set h : ℍ → ℂ := f ∣[((w + 2 : ℕ) : ℤ)] toGL β with hdef
  have hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := hf.slash _ _
  set a : ℂ := ((β 0 0 : ℤ) : ℂ) with ha
  set b : ℂ := ((β 0 1 : ℤ) : ℂ) with hb
  set c : ℂ := ((β 1 0 : ℤ) : ℂ) with hc
  set d : ℂ := ((β 1 1 : ℤ) : ℂ) with hd
  set D : ℂ := ((β.det : ℤ) : ℂ) with hD
  have hdet : a * d - b * c = D := by
    rw [ha, hb, hc, hd, hD, Matrix.det_fin_two]
    push_cast
    ring
  ext n
  set q : ℕ → ℂ := fun i => ((C a * X + C b) ^ i * (C c * X + C d) ^ (w - i)).coeff n with hq
  have hslP : ∀ p : ℂ[X], (slP w β p).coeff n = ∑ i ∈ Finset.range (w + 1), p.coeff i * q i := by
    intro p
    rw [polySlash_apply, finsetSum_coeff]
    simp only [Polynomial.coeff_smul, smul_eq_mul]
    rfl
  set Φ : ℂ → ℂ := fun v => ∑ i ∈ Finset.range (w + 1),
      (w.choose i : ℂ) * ecoef w f i ((a * v + b) / (c * v + d)) * q i -
    (w.choose n : ℂ) * ecoef w h n v with hΦ
  have hΦ1 : ∀ τ : ℍ, Φ τ =
      (slP w β (eichler w f (toGL β • τ))).coeff n - (eichler w h τ).coeff n := by
    intro τ
    simp only [hΦ, hslP, coeff_eichler, coe_toGL_smul β hβ]
    rfl
  have hder : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt Φ 0 z := by
    intro z hz
    obtain ⟨τ, rfl⟩ : ∃ τ : ℍ, (τ : ℂ) = z := ⟨⟨z, hz⟩, rfl⟩
    have hj : c * τ + d ≠ 0 := by
      rw [hc, hd, ← denom_toGL β hβ.ne']
      exact denom_ne_zero _ _
    have hs : ((toGL β • τ : ℍ) : ℂ) = (a * τ + b) / (c * τ + d) := coe_toGL_smul β hβ τ
    have hm : HasDerivAt (fun v : ℂ => (a * v + b) / (c * v + d)) (D * (c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      have h1 : HasDerivAt (fun v : ℂ => a * v + b) a (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
      have h2 : HasDerivAt (fun v : ℂ => c * v + d) c (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
      refine (h1.fun_div h2 hj).congr_deriv ?_
      rw [inv_pow, div_eq_mul_inv]
      linear_combination ((c * τ + d) ^ 2)⁻¹ * hdet
    have hA : ∀ i, HasDerivAt (fun v : ℂ => ecoef w f i ((a * v + b) / (c * v + d)))
        (f (toGL β • τ) * (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (D * (c * τ + d)⁻¹ ^ 2)) (τ : ℂ) := by
      intro i
      have := hasDerivAt_ecoef w f hf i _ (toGL β • τ).im_pos
      simp only [Function.comp_apply, ofComplex_apply] at this
      exact HasDerivAt.comp (τ : ℂ) (h₂ := ecoef w f i) (by rw [← hs]; exact this) hm
    have hB := hasDerivAt_ecoef w h hh n _ τ.im_pos
    simp only [Function.comp_apply, ofComplex_apply] at hB
    have hP := congrArg (fun p : ℂ[X] => p.coeff n)
      (polySlash_pow w β ((toGL β • τ : ℍ) : ℂ) τ (D * (c * τ + d)⁻¹)
        (by rw [hs, ← ha, ← hc]; rw [div_eq_mul_inv]
            linear_combination (-a) * mul_inv_cancel₀ hj + (c * τ + d)⁻¹ * hdet)
        (by rw [hs, ← hb, ← hd]; rw [div_eq_mul_inv]
            linear_combination (-b) * mul_inv_cancel₀ hj - (c * τ + d)⁻¹ * τ * hdet))
    simp only [hslP, coeff_C_mul, coeff_X_add_C_pow] at hP
    have hv : h τ = f (toGL β • τ) * D ^ (w + 1) * (c * τ + d)⁻¹ ^ (w + 2) := by
      have e : ((w + 2 : ℕ) : ℤ) - 1 = ((w + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hdef, slash_toGL _ β hβ, e, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
    refine ((HasDerivAt.fun_sum (u := Finset.range (w + 1)) fun i _ =>
      ((hA i).const_mul (w.choose i : ℂ)).mul_const (q i)).fun_sub
        (hB.const_mul (w.choose n : ℂ))).congr_deriv ?_
    have : ∑ i ∈ Finset.range (w + 1), (w.choose i : ℂ) *
        (f (toGL β • τ) * (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (D * (c * τ + d)⁻¹ ^ 2)) * q i =
        f (toGL β • τ) * (D * (c * τ + d)⁻¹ ^ 2) * ∑ i ∈ Finset.range (w + 1),
          (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (w.choose i : ℂ) * q i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hP, hv]
    ring
  have hconst : Φ τ = Φ (I : ℍ) :=
    isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hder z hz).deriv) τ.im_pos (I : ℍ).im_pos
  rw [hΦ1, hΦ1, eichler_I, coeff_zero] at hconst
  rw [coeff_add]
  linear_combination hconst

end GlobalTheory.EichlerChangeGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromIFinsetSumStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerIntegralFromI_finset_sum : ∀ (w : ℕ) {ι : Type} [Fintype ι] (g : ι → ℍ → ℂ), (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) → ∀ τ : ℍ, eichler w (∑ i, g i) τ = ∑ i, eichler w (g i) τ := by
  first | exact @GlobalTheory.EichlerSum.eichler_finset_sum | exact GlobalTheory.EichlerSum.eichler_finset_sum | (intros; apply GlobalTheory.EichlerSum.eichler_finset_sum <;> assumption)
end

