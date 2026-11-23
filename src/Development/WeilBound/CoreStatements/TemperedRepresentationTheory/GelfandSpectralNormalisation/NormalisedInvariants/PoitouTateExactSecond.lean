module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.PoitouTateConclusion

section Loc

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {r : ℕ}

def InvNormalised (ζ : Ω) (inv : InvFam F Ω l r) : Prop :=
  ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
    Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A)

end Loc

section Glob

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (inv : InvFam F Ω l r)
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

def PoitouTateExactSecond : Prop :=
  Function.Exact (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ)

end Glob

def VanishAll : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (r : ℕ), (l ≠ 2 ∨ IsTotallyComplex F) → 0 < r →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    ContAction ρ → ∀ n, 3 ≤ n → Subsingleton (Hn ρ n)

end PositivityTheory.PoitouTateConclusion
