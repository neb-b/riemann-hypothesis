module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0007

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSimplicialLabelledRefinement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement

theorem exists_simpLab_refinement : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ φ lab : InvFun O, IsPolyFan bar q φ ∧ IsTwG w0 φ ∧ IsTwG w0 lab ∧ SimpLab bar q φ lab ∧ Subordinate bar q φ ψ := by
  intro O _ _ _ _ bar w0 hb q ψ hD hψ hT
  obtain ⟨lab, hlT, hlab⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim O bar w0 hb q ψ hD hψ hT
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity.carrierDim_bounded O bar hb q ψ lab hlab
  have key : ∀ d : ℕ, ∃ φ : InvFun O, IsTwG w0 φ ∧ IsBaryStage bar q ψ lab φ (N - d) := by
    intro d
    induction d with
    | zero => exact ⟨ψ, hT, isBaryStage_start hψ hN⟩
    | succ d ih =>
      obtain ⟨φ, hφT, hφ⟩ := ih
      rcases Nat.eq_zero_or_pos (N - d) with h | h
      · exact ⟨φ, hφT, by rw [show N - (d + 1) = N - d by omega]; exact hφ⟩
      · have e : N - d = (N - (d + 1)) + 1 := by omega
        rw [e] at hφ
        exact _root_.GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision.baryStep O bar w0 hb q ψ lab φ _ hD hψ hT hlT hlab hφT hφ
  obtain ⟨φ, hφT, hφ⟩ := key N
  rw [Nat.sub_self] at hφ
  exact ⟨φ, lab, hφ.1, hφT, hlT, GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero _ bar q ψ lab φ hlab hφ, hφ.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionDropsMultCells
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells

theorem exists_star_drop_multCells : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∀ M n : ℕ, 2 ≤ M →
    maxMult bar q φ ≤ M → MultCellsAmong bar q φ M (n + 1) →
    ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧
      Subordinate bar q φ' φ ∧ maxMult bar q φ' ≤ M ∧ MultCellsAmong bar q φ' M n := by
  intro O _ _ _ _ bar w0 hb q φ lab hDom hφ hφtw hlabtw hsl M n hM hmax hcells
  obtain ⟨R, hR⟩ := hcells
  obtain ⟨w, hwtw, hwc, hcov, hdrop⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.TwistedOrbitCentres.centres_exists O bar w0 hb q φ lab hDom hφ hφtw hlabtw hsl M hM hmax (R 0)
  obtain ⟨ψ', hψ', hψ'tw, hsub, hstar⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision.exists_starSubdivision O bar w0 hb q φ w hDom hφ hφtw hwtw hwc
  obtain ⟨lab', hlab'tw, hsl'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling.exists_isTwG_simpLab_star O bar w0 hb q φ lab w ψ' hDom hφ hlabtw hsl hwtw hwc hψ' hsub hstar
  obtain ⟨hmax', hc'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity.starMult O bar hb q φ lab w ψ' hDom hφ hsl hwc hdrop hψ' hsub hstar M hmax
  refine ⟨ψ', lab', hψ', hψ'tw, hlab'tw, hsl', hsub, hmax', fun k => R k.succ, ?_⟩
  intro X _ _ _ _ hX m δ hδ
  obtain ⟨hδφ, hnoc⟩ := hc' X hX m δ hδ
  obtain ⟨k, hk⟩ := hR X hX m δ hδφ
  induction k using Fin.cases with
  | zero =>
    obtain ⟨β, hβ, hp, hw1, hin⟩ := hcov X hX m δ hδφ hk
    exact absurd hw1 (hnoc β hβ hp hin)
  | succ k => exact ⟨k, hk⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFanIsPolyhedral
section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem vorFun_isPolyFan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ),
    (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) →
    Module.finrank ℤ O * q ≤ g → IsPolyFan bar q (vorFun O g) := by
  intro O _ _ _ _ bar g q hred hg X _ _ _ _ hX
  obtain ⟨hhom, hsup⟩ := vorFun_homog_superadd O bar g X
  obtain ⟨hint, hpos⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.vorFun_int_pos O bar g q X hg hX
  exact
    { homog := hhom
      superadd := hsup
      integral := fun β _ h => hint β h
      pos := fun β hβ h h0 => hpos β hβ.1 h h0
      finite := GlobalTheory.T.psd_cone_finitely_many_orbits O bar g hred X }

end GlobalTheory.CompanionTheory.Ar.Fan
end

