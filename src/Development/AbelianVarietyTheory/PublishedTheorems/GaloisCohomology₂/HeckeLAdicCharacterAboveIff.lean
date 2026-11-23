module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal

namespace GlobalTheory.Published

def HeckeLAdicCharacterAbove : Prop := GlobalTheory.TripleGal.CharAbove

theorem heckeLAdicCharacterAbove_iff : HeckeLAdicCharacterAbove ↔
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
      (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Qbar l ≃+* ℂ)
      (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
      ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
      IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O),
        GlobalTheory.Pst.Induces Bw →
        IsdRAt P Bw ((rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
        IsPotCrysAt P Bw ((rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
        (χ.UnrAt w → IsCrysAt P Bw ((rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw ((rk1 μ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ {-n (ι.toRingHom.comp τ)} :=
  Iff.rfl

end GlobalTheory.Published

namespace GlobalTheory.HeckeGal

end GlobalTheory.HeckeGal

end
