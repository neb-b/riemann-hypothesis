module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

section Local

variable {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

def AbW (x : WD h) : Prop :=
  ∀ g g' : Weil h, x.charPol (g * g' * g⁻¹ * g'⁻¹) = (Polynomial.X - 1) ^ x.lpDim

structure Near (x y : WD h) : Prop where
  mono : x.mono0 ↔ y.mono0
  size : ∀ σ : Weil h, (x.eig σ).map (fun z => ‖z‖) = (y.eig σ).map (fun z => ‖z‖)
  eq : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IneTriv (y.lpTwist χ hχ) → x = y
  tame : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IsTameWD (y.lpTwist χ hχ) →
    ∀ τ : Ine (F := K) A, x.charPol (ineIncl h τ) = y.charPol (ineIncl h τ)

end Local

def SolvDisj {K Ω : Type} (M : Type) [Field K] [Field M] [Field Ω] [Algebra K Ω] [Algebra M Ω] [Algebra K M] [IsScalarTower K M Ω]
    (N : Subgroup (G K Ω)) : Prop :=
  IsGalois K M ∧ IsSolvable (M ≃ₐ[K] M) ∧
    ∀ g : G K Ω, ∃ (x : G M Ω) (n : G K Ω), n ∈ N ∧ g = AlgEquiv.restrictScalarsHom K x * n

section API

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

variable {K M : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] {a : ℕ}

end API

end GlobalTheory.AboveL

end
