module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0004

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AutomorphismGroupTopologies

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm
open scoped TensorProduct

section Quot

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

@[reducible] def topU (A : Type) [CommRing A] [Algebra F A] [t : TopologicalSpace A] (V : HSpace E r) :
    TopologicalSpace (UA F A V) :=
  ⨅ (a : Fin r) (b : Fin r) (φ : E →ₗ[F] F),
    t.induced fun g => TensorProduct.rid F A (LinearMap.lTensor A φ (g.1.val a b))

@[reducible] def topG (V : HSpace E r) : TopologicalSpace (GA F V) :=
  (topU F (Ai F) V).induced Prod.fst ⊓ (topU F (Af F) V).induced Prod.snd

def ratG (V : HSpace E r) : Subgroup (GA F V) where
  carrier := {g | ∃ γ, IsRat F V γ g}
  one_mem' := ⟨1, by simp [IsRat, Matrix.map_one]⟩
  mul_mem' := by
    rintro g h ⟨γ, g1, g2⟩ ⟨δ, h1, h2⟩
    refine ⟨γ * δ, ?_, ?_⟩
    · rw [Units.val_mul, Matrix.map_mul, ← g1, ← h1]; rfl
    · rw [Units.val_mul, Matrix.map_mul, ← g2, ← h2]; rfl
  inv_mem' := by
    rintro g ⟨γ, g1, g2⟩
    have e1 : g.1.1 = Matrix.GeneralLinearGroup.map (incl F (Ai F)) γ := Units.ext g1
    have e2 : g.2.1 = Matrix.GeneralLinearGroup.map (incl F (Af F)) γ := Units.ext g2
    refine ⟨γ⁻¹, ?_, ?_⟩
    · change (g.1.1⁻¹).val = _
      rw [e1, ← map_inv]; rfl
    · change (g.2.1⁻¹).val = _
      rw [e2, ← map_inv]; rfl

def AutQ (V : HSpace E r) : Type := Quotient (QuotientGroup.rightRel (ratG F V))

def autMk (V : HSpace E r) (g : GA F V) : AutQ F V := Quotient.mk _ g

instance (V : HSpace E r) : MeasurableSpace (AutQ F V) := (@borel _ (topG F V)).map (autMk F V)

def autRt (V : HSpace E r) (h : GA F V) : AutQ F V → AutQ F V :=
  Quotient.map' (· * h) fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab

def IsAutProb (V : HSpace E r) (ν : Measure (AutQ F V)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ h s, MeasurableSet s → ν (autRt F V h ⁻¹' s) = ν s

def FinVol (V : HSpace E r) : Prop := ∃ ν, IsAutProb F V ν

end Quot

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [Algebra F E] {R : Nums E} (Q : CorePar F R)

variable {Q}

end GlobalTheory.IndefiniteRowSideFullHecke.AutomorphismGroupTopologies
