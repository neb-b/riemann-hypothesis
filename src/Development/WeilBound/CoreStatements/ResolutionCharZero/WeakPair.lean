module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIntegralBlowupOfSmooth
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

def ResW : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (M D : ℕ) (X : Scheme.{0}) (i : X ⟶ PSpace K M) (U : X.Opens),
    IsResInput M i U D →
    ∃ (X₁ : Scheme.{0}) (s : X₁ ⟶ X),
      IsProjOver (s ≫ i ≫ PSpace.str K M) ∧ Smooth (s ≫ i ≫ PSpace.str K M) ∧ IsIso (s ∣_ U) ∧
        Dense ((s ⁻¹ᵁ U : X₁.Opens) : Set X₁)

def PrincW : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp K),
    SmoothOfRelativeDimension d g → IsProjOver g → ∀ U : X.Opens, Dense (U : Set X) →
    ∃ (X' : Scheme.{0}) (s : X' ⟶ X),
      IsProjOver (s ≫ g) ∧ Smooth (s ≫ g) ∧ IsIso (s ∣_ U) ∧ FinalTheorems.Snc (preRed s (U : Set X)ᶜ U.isOpen.isClosed_compl)

theorem resK_of_weak (H₁ : ResW) (H₂ : PrincW) : ResKStatement := by
  intro K _ _ M D X i U hin
  obtain ⟨X₁, s, hproj₁, hsm₁, hiso₁, hd₁⟩ := H₁ K M D X i U hin
  obtain ⟨hi, hred, hdense, hU⟩ := hin
  have hD₁ : SmoothOfRelativeDimension D (s ≫ i ≫ PSpace.str K M) :=
    relDim_of_dense _ _ hd₁ (relDim_preimage s _ U hU)
  obtain ⟨X₂, t, hproj₂, hsm₂, hiso₂, hsnc₂⟩ := H₂ K D X₁ (s ≫ i ≫ PSpace.str K M) hD₁ hproj₁ (s ⁻¹ᵁ U) hd₁
  have hiso : IsIso ((t ≫ s) ∣_ U) := by
    rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso₂ hiso₁
  have hT : IsClosed ((t ≫ s).base ⁻¹' (U : Set X)ᶜ) :=
    U.isOpen.isClosed_compl.preimage (t ≫ s).base.hom.continuous
  have hsncT : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨_, hT⟩) := hsnc₂
  have hd₂ : Dense (((t ≫ s) ⁻¹ᵁ U : X₂.Opens) : Set X₂) := by
    exact Dense.mono (fun x hx => by simpa using hx) (dense_compl_of_snc _ hsncT)
  have hproj₂' : IsProjOver (t ≫ s ≫ i ≫ PSpace.str K M) := hproj₂
  have : CompactSpace X₂ := by
    have hP₂ := isProper_of_isProjOver hproj₂'
    exact QuasiCompact.compactSpace_of_compactSpace (t ≫ s ≫ i ≫ PSpace.str K M)
  have hsm : Smooth ((t ≫ s) ≫ i ≫ PSpace.str K M) := by simpa using hsm₂
  obtain ⟨hDim, hC⟩ := _root_.GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side K D X₂ ((t ≫ s) ≫ i ≫ PSpace.str K M) ((t ≫ s) ⁻¹ᵁ U) _ hT inferInstance hsm hd₂
    (relDim_preimage (t ≫ s) _ U hU) hsncT
  obtain ⟨r, j, hj, e⟩ := exists_closed_in_prod ((t ≫ s) ≫ i) (by simpa using hproj₂')
  exact ⟨r, X₂, j, t ≫ s, hj, e, hDim, hiso, hd₂, hC⟩

end PositivityTheory.ResPlug
