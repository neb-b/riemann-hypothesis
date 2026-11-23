module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.SameUpToScalars

@[expose] public section

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def SDHerm (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y)

def SDTrace (ξ : E) (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, EFf ξ G x y = k) ∧ ∀ φ : L →+ ℤ, ∃ x ∈ L, ∀ y : L, (φ y : ℚ) = EFf ξ G x y

end defs

def DualTransport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E) (a : GL (Fin r) E)
    (L' : Submodule (𝓞 E) (Fin r → E)),
    (a : Matrix (Fin r) (Fin r) E)ᵀ * G * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = G' → IsLat L' →
    ∃ aL' : Submodule (𝓞 E) (Fin r → E), IsLat aL' ∧ (∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ aL') ∧
      (SDHerm G' L' → SDHerm G aL') ∧ ∀ ξ, SDTrace ξ G' L' → SDTrace ξ G aL'

def LocalToAdelic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (L L' : Submodule (𝓞 E) (Fin r → E)), IsLat L → IsLat L' →
    (∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (GlobalTheory.SelfDualGenus.LocAlg v),
      (∀ v, GlobalTheory.SelfDualGenus.IsLocalIsometry v G L' G L (γ v)) ∧ {v | γ v ≠ 1}.Finite) →
    AdGenus (IsCMField.complexConj E) G L L'

end PositivityTheory.EqVol
