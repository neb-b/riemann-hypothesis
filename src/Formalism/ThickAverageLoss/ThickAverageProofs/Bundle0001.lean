module

public import Formalism.ThickAverageLoss.PartnersToFactorsAt
public import Formalism.JacobiWeightFamilies.Statement
public import Formalism.Bundle0002

@[expose] public section

-- bundled from Formalism.ThickAverageLoss.ThickAverageProofs.Balance
section
open Finset ArithmeticFunction

noncomputable section

namespace Formalism.D5

open Formalism Formalism.WT

namespace Bal

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma zmod_two_ne_zero_iff_eq_one (e : ZMod 2) : ¬ e = 0 ↔ e = 1 := by
  revert e
  decide

private lemma prod_add_fst_fst (x y : E0 × H) : (x + y).1.1 = x.1.1 + y.1.1 := rfl

private lemma topPl_fst_fst_eq_zero (t : H) : (topPl t).1.1 = 0 := rfl

lemma inPhi_add_topPl (g : E0 × H) (t : H) : InPhi (g + topPl t) ↔ InPhi g := by
  show (g + topPl t).1.1 = 0 ↔ g.1.1 = 0
  rw [prod_add_fst_fst, topPl_fst_fst_eq_zero, add_zero]

private lemma cconj_fst_fst_eq_one : (cconj : E0 × H).1.1 = 1 := rfl

private lemma prod_sub_fst_fst (x y : E0 × H) : (x - y).1.1 = x.1.1 - y.1.1 := rfl

lemma sum_S_rho {β : Type*} [AddCommMonoid β] (t : H) (F : E0 × H → β) :
    ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), F (cconj + g + topPl t)
      = ∑ ρ ∈ PhiSet (H := H), F ρ := by
  refine Finset.sum_nbij' (fun g => cconj + g + topPl t) (fun ρ => ρ - cconj - topPl t) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    have hg' : ¬ InPhi (g + topPl t) := (Finset.mem_filter.mp hg).2
    have h1 : ¬ g.1.1 = 0 := fun h => hg' ((inPhi_add_topPl g t).mpr h)
    show cconj + g + topPl t ∈ PhiSet (H := H)
    rw [PhiSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show (cconj + g + topPl t).1.1 = 0
    rw [prod_add_fst_fst, prod_add_fst_fst, cconj_fst_fst_eq_one, topPl_fst_fst_eq_zero]
    revert h1
    generalize g.1.1 = e
    revert e
    decide
  · intro ρ hρ
    rw [PhiSet, Finset.mem_filter] at hρ
    have h1 : ρ.1.1 = 0 := hρ.2
    show ρ - cconj - topPl t ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t))
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [inPhi_add_topPl]
    show ¬ (ρ - cconj - topPl t).1.1 = 0
    rw [prod_sub_fst_fst, prod_sub_fst_fst, cconj_fst_fst_eq_one, topPl_fst_fst_eq_zero]
    revert h1
    generalize ρ.1.1 = e
    revert e
    decide
  · intro g _
    show cconj + g + topPl t - cconj - topPl t = g
    abel
  · intro ρ _
    show cconj + (ρ - cconj - topPl t) + topPl t = ρ
    abel
  · intro g _
    rfl

lemma card_S (t : H) :
    (univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t))).card = (PhiSet (H := H)).card := by
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
  exact sum_S_rho t (fun _ => (1 : ℕ))

lemma card_G_eq : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H := H)).card : ℂ) := by
  have h1 : (univ.filter (fun g : E0 × H => InPhi g)).card
      + (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = Fintype.card (E0 × H) := by
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, ← Finset.card_univ, Finset.card_eq_sum_ones]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have h2 : (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = (PhiSet (H := H)).card := by
    rw [← card_S (H := H) 0]
    congr 1
    apply Finset.filter_congr
    intro g _
    rw [inPhi_add_topPl]
  have h3 : univ.filter (fun g : E0 × H => InPhi g) = PhiSet (H := H) := PhiSet.eq_1.symm
  rw [← h1, h2, h3]
  push_cast
  ring

lemma phiSet_card_ne_zero : ((PhiSet (H := H)).card : ℂ) ≠ 0 := by
  have hmem : (0 : E0 × H) ∈ PhiSet (H := H) := by
    rw [PhiSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  exact Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨_, hmem⟩).ne'

end

end Bal


end Formalism.D5
end
end

-- bundled from Formalism.ThickAverageLoss.ThickAverageProofs.ThickAverage
section
open Finset

noncomputable section

namespace Formalism.D5

open Formalism Formalism.WT

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma zmod_two_cases_bis (x : ZMod 2) : x = 0 ∨ x = 1 := by
  first
    | (revert x; decide)
    | (fin_cases x <;> simp)

lemma zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  decide

lemma zmod_two_one_ne_zero : (1 : ZMod 2) ≠ 0 := by
  decide

lemma phiSet_card : (PhiSet (H := H)).card = 2 * Fintype.card H := by
  have h1 : PhiSet (H := H) =
      (Finset.univ.filter (fun e : E0 => e.1 = 0)) ×ˢ (Finset.univ : Finset H) := by
    ext ⟨⟨a, b⟩, h⟩
    simp [PhiSet, InPhi]
  have h2 : (Finset.univ.filter (fun e : E0 => e.1 = 0)).card = 2 := by
    first
      | decide
      | rfl
  rw [h1, Finset.card_product, h2, Finset.card_univ]



lemma thick_filter (T2 : Finset H) (u0 t : H) :
    univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t) ∧ IsThickAt T2 u0 (cconj + g + topPl t))
      = T2.image (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  ext ⟨⟨a, b⟩, h⟩
  rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl <;>
    simp [InPhi, IsThickAt, topPl, cconj, thickPl, zmod_two_one_add_one, zmod_two_one_ne_zero,
      zmod_two_one_ne_zero.symm, h2, sub_eq_iff_eq_add]

lemma thick_inj (u0 t : H) :
    Set.InjOn (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) Set.univ := by
  intro x _ y _ hxy
  simpa using hxy


end

end Formalism.D5
end
end

