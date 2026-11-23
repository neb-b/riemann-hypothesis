module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (k := w.adicCompletion E) → WD h}

def FieldG {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h') : Prop :=
  ∀ (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'),
    (∀ z, φ z ∈ A' ↔ z ∈ A) → (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → Continuous i →
    (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) →
    ∀ (n : ℕ) (π : IrrRep (GL (Fin n) (w.adicCompletion E))) (π' : IrrRep (GL (Fin n) (w'.adicCompletion E')))
      (e : π.V ≃ₗ[ℂ] π'.V), (∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) → Good (cls π) →
      ∃ (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = rc (cls π) ∧ WD.mk b' = rc' (cls π') ∧
        b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)) → b.ρ σ = b'.ρ σ'

def FieldGT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω')
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w')
    (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h'),
    IsRecT h rc → IsRecT h' rc' → FieldG rc rc'

namespace Old

theorem twist (H : Laws a ha ε rc) : ∀ x χ hχ, Good x → rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ)) :=
  fun x χ hχ _ => H.twist x χ hχ

end Old

namespace New

end New

end UpperTheory.One.M
