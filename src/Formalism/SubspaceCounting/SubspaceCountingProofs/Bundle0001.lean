module

public import Formalism.SubspaceCounting.Bundle0001

@[expose] public section

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.LengthLayers
section
noncomputable section

open scoped BigOperators

namespace Formalism.G0

namespace LengthLayersP

section General

variable {O : Type} [CommRing O]

theorem length_eq_add_of_le {X : Type} [AddCommGroup X] [Module O X] {U V : Submodule O X}
    (h : U ≤ V) :
    Module.length O ↥V = Module.length O ↥U + Module.length O (↥V ⧸ U.comap V.subtype) := by
  rw [Module.length_eq_add_of_exact (U.comap V.subtype).subtype (U.comap V.subtype).mkQ
    Subtype.val_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
    (Submodule.comapSubtypeEquivOfLe h).length_eq]

theorem length_quot_eq_add {X : Type} [AddCommGroup X] [Module O X] {U V : Submodule O X}
    (h : U ≤ V) :
    Module.length O (X ⧸ U) = Module.length O ↥(V.map U.mkQ) + Module.length O (X ⧸ V) := by
  refine Module.length_eq_add_of_exact (V.map U.mkQ).subtype (U.mapQ V LinearMap.id (fun x hx => h hx))
    Subtype.val_injective ?_ ?_
  · intro y
    obtain ⟨x, rfl⟩ := V.mkQ_surjective y
    exact ⟨U.mkQ x, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := U.mkQ_surjective y
    constructor
    · intro hx
      have hxV : x ∈ V := (Submodule.Quotient.mk_eq_zero V).mp hx
      exact ⟨⟨U.mkQ x, Submodule.mem_map_of_mem hxV⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, hzx⟩
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
      have h1 : U.mkQ w = U.mkQ x := hzx
      have h2 : w - x ∈ U := (Submodule.Quotient.eq U).mp h1
      have h3 : x ∈ V := by simpa using V.sub_mem hw (h h2)
      exact (Submodule.Quotient.mk_eq_zero V).mpr h3

end General

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem length_residue (π : O) (hπ : Irreducible π) :
    Module.length O (O ⧸ Ideal.span {π}) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
  exact (PrincipalIdealRing.isMaximal_of_irreducible hπ).out

private theorem length_sup_span_le_add_one_of_smul_mem (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (W : Submodule O X) (z : X) (hz : π • z ∈ W) :
    Module.length O ↥(W ⊔ O ∙ z) ≤ Module.length O ↥W + 1 := by
  have hWT : W ≤ W ⊔ O ∙ z := le_sup_left
  rw [length_eq_add_of_le hWT]
  refine add_le_add le_rfl ?_
  set T := W ⊔ O ∙ z with hT
  set K := W.comap T.subtype with hK
  have hzT : z ∈ T := Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  set q : ↥T ⧸ K := K.mkQ ⟨z, hzT⟩ with hq
  have hπq : π • q = 0 := by
    rw [hq, ← map_smul]
    exact (Submodule.Quotient.mk_eq_zero K).mpr hz
  let f : O →ₗ[O] ↥T ⧸ K := LinearMap.toSpanSingleton O _ q
  have hker : Ideal.span {π} ≤ LinearMap.ker f := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    exact hπq
  have hsurj : Function.Surjective ((Ideal.span {π}).liftQ f hker) := by
    intro y
    obtain ⟨⟨t, ht⟩, rfl⟩ := K.mkQ_surjective y
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp ht
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    refine ⟨Submodule.Quotient.mk r, ?_⟩
    rw [Submodule.liftQ_apply]
    show r • q = K.mkQ ⟨w + r • z, ht⟩
    rw [hq, ← map_smul]
    simp only [Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq, hK, Submodule.mem_comap]
    have e : T.subtype (r • ⟨z, hzT⟩ - ⟨w + r • z, ht⟩) = -w := by
      show r • z - (w + r • z) = -w
      abel
    rw [e]
    exact W.neg_mem hw
  exact (Module.length_le_of_surjective _ hsurj).trans (length_residue π hπ).le

private theorem length_sup_span_le_add_of_pow_smul_mem (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] : ∀ (s : ℕ) (W : Submodule O X) (z : X), π ^ s • z ∈ W →
      Module.length O ↥(W ⊔ O ∙ z) ≤ Module.length O ↥W + (s : ℕ∞) := by
  intro s
  induction s with
  | zero =>
    intro W z hz
    rw [pow_zero, one_smul] at hz
    have e : W ⊔ O ∙ z = W := sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hz)
    rw [e]
    simp
  | succ s ih =>
    intro W z hz
    have h1 : π ^ s • (π • z) ∈ W := by rw [smul_smul, ← pow_succ]; exact hz
    have h2 := ih W (π • z) h1
    have h3 := length_sup_span_le_add_one_of_smul_mem π hπ (W ⊔ O ∙ (π • z)) z
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    have h4 : W ⊔ O ∙ (π • z) ⊔ O ∙ z = W ⊔ O ∙ z := by
      apply le_antisymm
      · refine sup_le (sup_le le_sup_left ?_) le_sup_right
        exact le_trans ((Submodule.span_singleton_le_iff_mem _ _).mpr
          (Submodule.smul_mem _ π (Submodule.mem_span_singleton_self z))) le_sup_right
      · exact sup_le (le_trans le_sup_left le_sup_left) le_sup_right
    rw [h4] at h3
    calc Module.length O ↥(W ⊔ O ∙ z) ≤ Module.length O ↥(W ⊔ O ∙ (π • z)) + 1 := h3
      _ ≤ Module.length O ↥W + (s : ℕ∞) + 1 := add_le_add h2 le_rfl
      _ = Module.length O ↥W + ((s + 1 : ℕ) : ℕ∞) := by push_cast; ring

theorem length_span_singleton_le (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] : ∀ (s : ℕ) (x : X), π ^ s • x = 0 → Module.length O ↥(O ∙ x) ≤ s := by
  intro s x hx
  have h := length_sup_span_le_add_of_pow_smul_mem π hπ s ⊥ x (by rw [hx]; exact Submodule.zero_mem _)
  have h0 : Module.length O ↥(⊥ : Submodule O X) = 0 := Module.length_eq_zero
  rw [bot_sup_eq, h0, zero_add] at h
  exact h

end DVR

section Main

variable {O : Type} [CommRing O]

end Main

end LengthLayersP

end Formalism.G0
end
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.QVandermonde
section
namespace Formalism.G0

namespace QVandermondeP

theorem gb_zero_right (q n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

theorem gb_zero_succ (q k : ℕ) : gaussBinom q 0 (k + 1) = 0 := rfl

theorem gb_succ_succ (q n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) :=
  rfl

theorem gb_eq_zero (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [gb_succ_succ, gb_eq_zero q n k (by omega), gb_eq_zero q n (k + 1) (by omega)]
    simp

theorem form2 (q m : ℕ) : ∀ g n : ℕ, gaussBinom q (m + g) n =
    ∑ l ∈ Finset.range (n + 1),
      q ^ ((n - l) * (g - l)) * gaussBinom q m (n - l) * gaussBinom q g l := by
  intro g
  induction g with
  | zero =>
    intro n
    rw [Finset.sum_range_succ']
    simp [gb_zero_succ, gb_zero_right]
  | succ g ih =>
    intro n
    cases n with
    | zero => simp [gb_zero_right]
    | succ k =>
      show gaussBinom q ((m + g) + 1) (k + 1) = _
      rw [gb_succ_succ, ih k, ih (k + 1)]
      rw [Finset.sum_range_succ' _ (k + 1), Finset.sum_range_succ' _ (k + 1)]
      have h1 : ∀ l ∈ Finset.range (k + 1),
          q ^ ((k + 1 - (l + 1)) * (g + 1 - (l + 1))) * gaussBinom q m (k + 1 - (l + 1)) *
              gaussBinom q (g + 1) (l + 1) =
            q ^ ((k - l) * (g - l)) * gaussBinom q m (k - l) * gaussBinom q g l +
              q ^ (k + 1) * (q ^ ((k + 1 - (l + 1)) * (g - (l + 1))) *
                gaussBinom q m (k + 1 - (l + 1)) * gaussBinom q g (l + 1)) := by
        intro l hl
        have hl' : l ≤ k := by
          have := Finset.mem_range.mp hl
          omega
        rw [gb_succ_succ]
        simp only [Nat.add_sub_add_right]
        rcases Nat.lt_or_ge g (l + 1) with h | h
        · rw [gb_eq_zero q g (l + 1) h]
          ring
        · obtain ⟨a, rfl⟩ : ∃ a, k = l + a := ⟨k - l, by omega⟩
          obtain ⟨b, rfl⟩ : ∃ b, g = l + 1 + b := ⟨g - (l + 1), by omega⟩
          have e1 : l + a - l = a := by omega
          have e2 : l + 1 + b - l = b + 1 := by omega
          have e3 : l + 1 + b - (l + 1) = b := by omega
          rw [e1, e2, e3]
          ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
      simp only [Nat.sub_zero, gb_zero_right]
      ring

end QVandermondeP

end Formalism.G0
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.SubspaceCount
section
noncomputable section

open scoped BigOperators
open Module

namespace Formalism.G0

namespace SubspaceCountP

theorem gb_zero_right (q n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

theorem gb_succ_succ (q n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) :=
  rfl

theorem gb_eq_zero (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [gb_succ_succ, gb_eq_zero q n k (by omega), gb_eq_zero q n (k + 1) (by omega)]
    simp

def P (q : ℤ) (m k : ℕ) : ℤ := ∏ i ∈ Finset.range k, (q ^ m - q ^ i)

theorem P_succ_right (q : ℤ) (m k : ℕ) : P q m (k + 1) = P q m k * (q ^ m - q ^ k) := by
  unfold P; rw [Finset.prod_range_succ]

theorem P_succ_succ (q : ℤ) (m k : ℕ) :
    P q (m + 1) (k + 1) = (q ^ (m + 1) - 1) * (q ^ k * P q m k) := by
  unfold P
  rw [Finset.prod_range_succ', pow_zero, mul_comm]
  congr 1
  rw [← Finset.card_range k, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem gb_mul_P (q : ℤ) (qn : ℕ) (hq : (qn : ℤ) = q) :
    ∀ n k : ℕ, (gaussBinom qn n k : ℤ) * P q k k = P q n k := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => simp [P, gb_zero_right]
    | succ k =>
      have : P q 0 (k + 1) = 0 := by
        unfold P
        exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos k)) (by simp)
      rw [this]; simp [gaussBinom]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp [P, gb_zero_right]
    | succ k =>
      rw [gb_succ_succ]
      push_cast
      rw [hq]
      have h1 := ih k
      have h2 := ih (k + 1)
      rw [P_succ_succ q k k, P_succ_succ q n k]
      rw [P_succ_succ q k k, P_succ_right] at h2
      linear_combination (q ^ (k + 1) - 1) * q ^ k * h1 + q ^ (k + 1) * h2

end SubspaceCountP

namespace SubspaceCountP

abbrev LI (F V : Type) [Field F] [AddCommGroup V] [Module F V] (k : ℕ) :=
  {s : Fin k → V // LinearIndependent F s}

abbrev Gr (F W : Type) [Field F] [AddCommGroup W] [Module F W] (k : ℕ) :=
  {U : Submodule F W // finrank F U = k}

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W]

def spanMap (k : ℕ) (s : LI F W k) : Gr F W k :=
  ⟨Submodule.span F (Set.range s.1), (finrank_span_eq_card s.2).trans (Fintype.card_fin k)⟩

variable [Finite W]

def fiberEquiv (k : ℕ) (U : Gr F W k) : {s : LI F W k // spanMap k s = U} ≃ LI F U.1 k where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      have h := congrArg Subtype.val s.2
      simp only [spanMap] at h
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩⟩, by
      apply LinearIndependent.of_comp U.1.subtype
      exact s.1.2⟩
  invFun t := ⟨⟨U.1.subtype ∘ t.1, t.2.map' _ (Submodule.ker_subtype _)⟩, by
      apply Subtype.ext
      apply Submodule.eq_of_le_of_finrank_eq
      · show Submodule.span F (Set.range (U.1.subtype ∘ t.1)) ≤ U.1
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (t.1 i).2
      · rw [(spanMap k _).2, U.2]⟩
  left_inv s := rfl
  right_inv t := rfl

end SubspaceCountP

namespace SubspaceCountP

variable {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W]

theorem card_LI_eq (k : ℕ) :
    Nat.card (LI F W k) =
      Nat.card (Gr F W k) * ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
  classical
  let _ := Fintype.ofFinite (Gr F W k)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (spanMap (F := F) (W := W) k)), Nat.card_sigma]
  have h : ∀ U : Gr F W k, Nat.card {s // spanMap k s = U} =
      ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
    intro U
    rw [Nat.card_congr (fiberEquiv k U), card_linearIndependent (by rw [U.2]), U.2]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem cast_prod_eq_P (q m k : ℕ) (hq : 1 ≤ q) (hm : k ≤ m) :
    ((∏ i : Fin k, (q ^ m - q ^ i.val) : ℕ) : ℤ) = P (q : ℤ) m k := by
  rw [Nat.cast_prod, P, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  rfl

end SubspaceCountP

open SubspaceCountP in
theorem countSubspacesEq : SubspaceCount := by
  intro F W _ _ _ _ _ k
  classical
  have hcount : countBelow (⊤ : Submodule F W) k = Nat.card (Gr F W k) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by simp))
  rw [hcount]
  rcases lt_or_ge (finrank F W) k with hnk | hkn
  · rw [gb_eq_zero _ _ _ hnk, Nat.card_eq_zero]
    left
    constructor
    rintro ⟨U, hU⟩
    have := Submodule.finrank_le U
    omega
  · have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have h1 := card_LI_eq (F := F) (W := W) k
    rw [card_linearIndependent hkn] at h1
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, cast_prod_eq_P _ _ _ hq.le hkn, cast_prod_eq_P _ _ _ hq.le le_rfl] at h2
    have h3 := gb_mul_P (Fintype.card F : ℤ) (Fintype.card F) rfl (finrank F W) k
    have hP : P (Fintype.card F : ℤ) k k ≠ 0 := by
      unfold P
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have : (Fintype.card F : ℤ) ^ i < (Fintype.card F : ℤ) ^ k :=
        pow_lt_pow_right₀ (by exact_mod_cast hq) (Finset.mem_range.mp hi)
      omega
    have : (Nat.card (Gr F W k) : ℤ) = gaussBinom (Fintype.card F) (finrank F W) k :=
      mul_right_cancel₀ hP (h2.symm.trans h3.symm)
    exact_mod_cast this

end Formalism.G0
end
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.TopsChoicePartA
section
noncomputable section

open Finset

namespace Formalism.G0

namespace TopsConditionalProbabilityWindows


open Classical in
def P (U : Finset ℕ) (δ : ℝ) (A : Finset ℕ → Prop) : ℝ :=
  by classical exact ∑ t ∈ U.powerset, if A t then δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0

theorem key (n L K : ℕ) (t : Finset ℕ) (h0t : 0 ∉ t) (h : ¬ CondA n (insert 0 t) L K) :
    ∃ i ∈ range n, ∃ S ∈ powersetCard (if 0 ∈ window n i L then K else K + 1)
      ((window n i L).erase 0), S ⊆ t := by
  classical
  unfold CondA at h
  push Not at h
  obtain ⟨i, hi, hK⟩ := h
  refine ⟨i, mem_range.2 hi, ?_⟩
  set W := window n i L
  set s := t ∩ W.erase 0 with hs_def
  have hm : (if 0 ∈ W then K else K + 1) ≤ s.card := by
    by_cases hw : 0 ∈ W
    · rw [if_pos hw]
      have hsub : insert 0 t ∩ W ⊆ insert 0 s := by
        intro x hx
        rcases mem_inter.1 hx with ⟨hx1, hx2⟩
        rcases mem_insert.1 hx1 with rfl | hxt
        · exact mem_insert_self _ _
        · refine mem_insert_of_mem (mem_inter.2 ⟨hxt, mem_erase.2 ⟨?_, hx2⟩⟩)
          rintro rfl
          exact h0t hxt
      have := (card_le_card hsub).trans (card_insert_le 0 s)
      omega
    · rw [if_neg hw]
      have hsub : insert 0 t ∩ W ⊆ s := by
        intro x hx
        rcases mem_inter.1 hx with ⟨hx1, hx2⟩
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hw hx2
        rcases mem_insert.1 hx1 with hx | hxt
        · exact absurd hx hx0
        · exact mem_inter.2 ⟨hxt, mem_erase.2 ⟨hx0, hx2⟩⟩
      have := card_le_card hsub
      omega
  obtain ⟨S, hSs, hSc⟩ := exists_subset_card_eq hm
  refine ⟨S, mem_powersetCard.2 ⟨?_, hSc⟩, ?_⟩
  · exact fun x hx => (mem_inter.1 (hSs hx)).2
  · exact fun x hx => (mem_inter.1 (hSs hx)).1

end TopsConditionalProbabilityWindows


end Formalism.G0
end
end

