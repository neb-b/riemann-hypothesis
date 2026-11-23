module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariants
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.KatoNOfKato

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameOfShCoc
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZ

theorem tame_of_shCoc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (P u : Qbar l) (b : Fin 2 → Qbar l), ShCoc (mat W) ψ Y → (∀ x i, Continuous fun s => Y s x i) → (∀ s x i, Y s x i ∈ c.O) → P ∈ c.O → ‖u‖ = 1 → (∀ i, b i ∈ c.O) → (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b - b)) → (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det)) → (∀ q : Pl, q ≠ w → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ t : Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l, (∀ x i, t x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, ∀ x, Y s x = mat W s *ᵥ t x - t x) → Tame c W y n w ψ := by
  intro l _ Ω _ _ c W y n w ψ Y P u b hY hcont hint hP hu hb hsum hfrob hunr
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : l.Prime).ne_zero⟩
  refine ⟨fun s a => Y s (Multiplicative.ofAdd (-a)), P, u, b, ?_, fun s a i => hint s _ i, hP, hu, hb, ?_, ?_, hfrob, ?_⟩
  · exact continuous_pi fun a => continuous_pi fun i => hcont _ i
  · intro s t a
    simp only
    rw [hY s t (Multiplicative.ofAdd (-a))]
    congr 3
    rw [neg_sub, sub_eq_neg_add]
    rfl
  · intro s
    rw [finsum_eq_sum_of_fintype, ← hsum s]
    exact Fintype.sum_equiv ((Equiv.neg (ZMod (l ^ n))).trans Multiplicative.ofAdd) _ _ (fun a => rfl)
  · intro q hq hl
    obtain ⟨B, hB, t, ht, hts⟩ := hunr q hq hl
    exact ⟨B, hB, fun a => t (Multiplicative.ofAdd (-a)), fun a i => ht _ i, fun s hs a => hts s hs _⟩

end GlobalTheory.KZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariantsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_h1_card_invariants : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (hρ : ContAction ρ), IsPlaceOver A v → Nat.card (H1ur ρ ((Ine (F := F) A).subgroupOf (Dec (F := F) A))) = Nat.card (H0 ρ) := by
  first | exact @GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 | exact GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 | (intros; apply GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedOfLevelAwayInertiaCharactersStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_of_levelAway_inertia_characters : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (M : ℕ), 1 ≤ M → LevelAway l M W → ∃ S : Finset Pl, ContainsAbove S l ∧ ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker := by
  first | exact @GlobalTheory.Ord2.unramified_of_levelAway | exact GlobalTheory.Ord2.unramified_of_levelAway | (intros; apply GlobalTheory.Ord2.unramified_of_levelAway <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdOfKatoUseN
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.VanishNarrow

open Polynomial

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]


omit [Fact l.Prime] in
theorem valuation_lt_one {A : ValuationSubring Ω} (h : OverL l A) : A.valuation (l : Ω) < 1 := by
  obtain ⟨v, hv, hl⟩ := h
  have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
  simpa using h1

end GlobalTheory.Ord2.VanishNarrow

namespace GlobalTheory.Ord2

end GlobalTheory.Ord2

end
end

