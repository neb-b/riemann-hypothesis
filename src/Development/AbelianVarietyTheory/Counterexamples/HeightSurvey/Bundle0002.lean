module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Matrix

namespace GlobalTheory.SignedParTest

theorem isEnum_unique {n : ℕ} {S : SPar} {l l' : Fin n → ℝ} {e e' : Fin n → Bool}
    (h : IsEnum S l e) (h' : IsEnum S l' e') : l = l' ∧ e = e' := by
  obtain ⟨ha, q, hq, hS⟩ := h
  obtain ⟨ha', q', hq', hS'⟩ := h'
  have key : ∀ a, ∃ b, q' b = q a ∧ e' b = e a := by
    intro a
    have : (q a, e a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS'] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, congrArg Prod.fst hb, congrArg Prod.snd hb⟩
  have key' : ∀ a, ∃ b, q b = q' a := by
    intro a
    have : (q' a, e' a) ∈ S := by rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, congrArg Prod.fst hb⟩
  have hr : Set.range l = Set.range l' := by
    ext x; constructor
    · rintro ⟨a, rfl⟩; obtain ⟨b, hb, -⟩ := key a; exact ⟨b, by rw [hq, hq', hb]⟩
    · rintro ⟨a, rfl⟩; obtain ⟨b, hb⟩ := key' a; exact ⟨b, by rw [hq, hq', hb]⟩
  have hl : l = l' := (ha.range_inj ha').1 hr
  refine ⟨hl, funext fun a => ?_⟩
  obtain ⟨b, hb, he⟩ := key a
  have : l' b = l' a := by rw [hq' b, hb, ← hq a, hl]
  rw [ha'.injective this] at he
  exact he.symm

theorem blattner_add_rho2C {p q : ℕ} {lam : Ix p q → ℚ} (h : IsParam lam) (a : Ix p q) :
    blattner lam a + rhoOfIndex a = lam a +
      (((Finset.univ.filter fun b => lam b < lam a).card : ℚ) -
        ((Finset.univ.filter fun b => lam a < lam b).card : ℚ)) / 2 := by
  classical
  have pos : ∀ a b : Ix p q, posC a b ↔ sameBlock a b ∧ lam b < lam a := by
    intro a b
    refine ⟨fun hh => ⟨by cases a <;> cases b <;> simp_all [posC, sameBlock], h.2.1 a b hh⟩, fun ⟨h1, h2⟩ => ?_⟩
    by_contra hn
    rcases a with a | a <;> rcases b with b | b
    · rcases (not_lt.1 hn).lt_or_eq with e | e
      · exact lt_asymm h2 (h.2.1 (.inl b) (.inl a) e)
      · subst e; exact lt_irrefl _ h2
    · exact h1
    · exact h1
    · rcases (not_lt.1 hn).lt_or_eq with e | e
      · exact lt_asymm h2 (h.2.1 (.inr b) (.inr a) e)
      · subst e; exact lt_irrefl _ h2
  have sym : ∀ a b : Ix p q, sameBlock a b ↔ sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  simp only [blattner, rhoNC, rhoOfIndex, Finset.card_filter, pos, sym _ a]
  push_cast
  simp only [← Finset.sum_sub_distrib, Finset.sum_div, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : sameBlock a b <;> by_cases h2 : lam b < lam a <;> by_cases h3 : lam a < lam b <;>
    simp [h1, h2, h3] <;> norm_num

theorem blattner_inj {p q : ℕ} {l l' : Ix p q → ℚ} (h : IsParam l) (h' : IsParam l') (e : blattner l = blattner l') :
    l = l' := by
  classical
  have mono : ∀ {m : Ix p q → ℚ}, IsParam m → ∀ a b, m b < m a → blattner m b + rhoOfIndex b < blattner m a + rhoOfIndex a := by
    intro m hm a b hab
    rw [blattner_add_rho2C hm, blattner_add_rho2C hm]
    have h1 : ((Finset.univ.filter fun c => m c < m b).card : ℚ) ≤ (Finset.univ.filter fun c => m c < m a).card := by
      exact_mod_cast Finset.card_le_card fun c hc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; linarith
    have h2 : ((Finset.univ.filter fun c => m a < m c).card : ℚ) ≤ (Finset.univ.filter fun c => m b < m c).card := by
      exact_mod_cast Finset.card_le_card fun c hc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; linarith
    linarith
  have one : ∀ {m m' : Ix p q → ℚ}, IsParam m → IsParam m' → blattner m = blattner m' →
      ∀ a b, m b < m a → m' b < m' a := by
    intro m m' hm hm' e a b hab
    by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with x | x
    · have := mono hm a b hab
      have := mono hm' b a x
      rw [e] at *; linarith
    · rw [hm'.1 x] at hab; exact lt_irrefl _ hab
  have ord : ∀ a b, l b < l a ↔ l' b < l' a := fun a b => ⟨one h h' e a b, one h' h e.symm a b⟩
  funext a
  have x := blattner_add_rho2C h a
  have y := blattner_add_rho2C h' a
  simp only [ord] at x
  rw [e] at x
  linarith

theorem hasParam_zero {T : GrpData 0 0} (R : DSRep T) (lam : Ix 0 0 → ℚ) : HasParam R lam := by
  refine ⟨?_, fun μ v _ => by simp [vogan]⟩
  haveI := R.nontriv
  obtain ⟨x, hx⟩ := exists_ne (0 : R.U.H)
  have hfin : Finite T.G := by
    have hinj : Function.Injective fun g : T.G => ((T.sq g : ℂˣ) : ℂ) := by
      intro g h e
      refine T.emb.injective (Prod.ext (Units.ext (Subsingleton.elim _ _)) (Units.ext e))
    have hsub : Set.range (fun g : T.G => ((T.sq g : ℂˣ) : ℂ)) ⊆ {1, -1} := by
      rintro _ ⟨g, rfl⟩
      have := T.sq_sq g
      rw [Matrix.det_isEmpty] at this
      simpa using this
    have := (Set.toFinite _).subset hsub
    exact Set.finite_univ_iff.1 (Set.Finite.of_finite_image (by rwa [Set.image_univ]) hinj.injOn)
  obtain ⟨v, hv⟩ := (R.ι_range x).2 (by
    unfold KFin
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _))
  refine ⟨v, fun h => hx (by rw [← hv, h, map_zero]), ?_⟩
  simp [hwSub, wtSub]

end GlobalTheory.SignedParTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.NotHasInfExpThird
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.VolHeckeCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isWittLower_self (D : D7) (V : HSp D) : IsWittLower V V 0 := by
  refine ⟨rfl, LinearMap.id, fun _ _ => rfl, 0, ⟨linearIndependent_empty_type, ?_⟩, ?_⟩
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

end GlobalTheory.VolHeckeCheck

end
end

