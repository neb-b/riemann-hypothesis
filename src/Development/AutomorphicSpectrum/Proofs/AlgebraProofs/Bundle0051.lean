module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FieldExtensionIntersectionInvarianceStatement
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSPullback
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.TraceIntegralOfCodifferent
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FreeQuotProof

def HasAffineChart {P X : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) : Prop :=
  a ⁻¹ᵁ V = b ⁻¹ᵁ V ∧
    ∃ (Y : Scheme.{0}) (q : V.toScheme ⟶ Y) (a' : (b ⁻¹ᵁ V).toScheme ⟶ V.toScheme),
      IsAffine Y ∧ IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
        a' ≫ V.ι = (b ⁻¹ᵁ V).ι ≫ a ∧ IsPullback a' (b ∣_ V) q q

end GlobalTheory.CompanionTheory.FreeQuotProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateDatumReduceScalars
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem htd_restrict_coefficients : ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R), HodgeTateSetting p v R Oe σ cp → ∀ H : HodgeTateDatum p g v R Oe σ cp, HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp ∧ ∃ H' : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp, H'.AA = H.AA ∧ H'.Ht = H.Ht ∧ H'.Bt = H.Bt ∧ H'.E = H.E := by
  intro p _ g C _ v R _ _ _ Oe _ _ σ cp hS H
  refine ⟨⟨hS.integers, hS.p_lt, hS.p_ne, hS.cp_val, fun _ => rfl⟩,
    { ρ := H.ρ.comp (Algebra.ofId _ _)
      ρL := H.ρL.comp (algebraMap _ _)
      P := H.P
      PL := H.PL
      E := H.E
      E_alternating := H.E_alternating
      isUnit_det_E := H.isUnit_det_E
      E_equivariant := fun a => ?_
      projectors := ⟨H.projectors.1, H.projectors.2.1, H.projectors.2.2.1, fun a => H.projectors.2.2.2.1 _, fun a => H.projectors.2.2.2.2 _⟩
      Ht := H.Ht
      Bt := H.Bt
      Ht_equivariant := ⟨fun a => ?_, H.Ht_equivariant.2⟩
      form_eq_alt := H.form_eq_alt
      AA := H.AA
      h3 := fun a => H.h3 _
      h4 := H.h4
      h5 := H.h5
      φ := H.φ
      cotangent_surjective := H.cotangent_surjective
      cotangent_ker_eq := H.cotangent_ker_eq
      cotangent_linear := fun a => H.cotangent_linear _ }, rfl, rfl, rfl, rfl⟩
  · have := H.E_equivariant (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this
  · have := H.Ht_equivariant.1 (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullback
section
namespace GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberPullback.Statement :=
  PositivityTheory.Xgn.t_s_pullback

end GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem unimodularity_sesq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ y, (∀ x, sesq D x y = 0) → y = 0) ∧ ∀ f : D.La →ₗ[𝓞 E] E, (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x, ∃ b : 𝓞 E, (δ : E) * f x = b) → ∃ y, ∀ x, f x = sesq D x y :=
  PositivityTheory.Xgf.sesq_unimodular_dual

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupQuotient
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) := by
  first | exact @PositivityTheory.HtPt.Rfin.a_nonunit | exact PositivityTheory.HtPt.Rfin.a_nonunit
end

