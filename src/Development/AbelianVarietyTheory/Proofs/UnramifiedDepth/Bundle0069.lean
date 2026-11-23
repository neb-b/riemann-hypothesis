module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceLinearDataStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colength_bound_split_place_linear_data : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, ∃ W' : Fin rm → Fin d → O, EigB ρG τ W') → ∃ xs : Fin w.n → NNReal, (∀ j, HasLen v O ((Fin rp → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) (xs j)) ∧ v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j := by
  first | exact @GlobalTheory.ChF.colength_bound_linDat | exact GlobalTheory.ChF.colength_bound_linDat | (intros; apply GlobalTheory.ChF.colength_bound_linDat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SmoothOfRelativeDimensionOfGrpPullbackLocalRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftDim

private theorem connectedSpace_primeSpectrum (R : Type) [CommRing R] [IsLocalRing R] :
    ConnectedSpace (PrimeSpectrum R) := by
  have : PreconnectedSpace (PrimeSpectrum R) :=
    ⟨isPreconnected_of_forall (IsLocalRing.closedPoint R) fun y _ =>
      ⟨closure {y}, Set.subset_univ _, (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl,
        isPreconnected_singleton.closure⟩⟩
  exact ⟨inferInstance⟩

theorem smoothOfRelativeDimension_of_isGrpPullback : ∀ (R' O : Type) [CommRing R'] [IsLocalRing R'] [CommRing O] [Nontrivial O] (π : R' →+* O) (G : Over (Spec (CommRingCat.of R'))) [GrpObj G] (G' : Over (Spec (CommRingCat.of O))) [GrpObj G'] (ψ : G'.left ⟶ G.left) (g : ℕ), IsAbelianScheme G → Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom π)) ψ → SmoothOfRelativeDimension g G'.hom → SmoothOfRelativeDimension g G.hom := by
  intro R' O _ _ _ _ π G _ G' _ ψ g hG hp hg
  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Spec (CommRingCat.of R')) := connectedSpace_primeSpectrum R'
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨n, hn⟩ := Geo.Tor.exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hn' : SmoothOfRelativeDimension n G'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback hp.1 hn
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum O) := inferInstance
  have e : n = g := H1.dim_unique _ hn' hg ((η[G']).left p)
  exact e ▸ hn

end GlobalTheory.LiftDim
end

