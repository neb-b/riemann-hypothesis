module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothSubordinateFan

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement

theorem exists_smooth_refinement : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone bar φ' γ → ψ.LinearOn γ := by
  intro O _ _ _ _ bar w0 hb q ψ hD hψ hT
  obtain ⟨φ, lab, hφ, hφT, hlT, hSL, hsub⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement.exists_simpLab_refinement O bar w0 hb q ψ hD hψ hT
  obtain ⟨φ', h1, h2, h3, hsub'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.FanResolution.resolution O bar w0 hb q φ lab hD hφ hφT hlT hSL
  exact ⟨φ', h1, h2, h3, fun X _ _ _ _ hX m γ hγ => (hsub'.trans hsub).linearOn hX hγ.isCell⟩

end GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement
