module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSBlowupfibre
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0035
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BetaEquivariantFrobenius
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv

theorem beta_rhoH_eq : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O]
    [StarRing O] (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)),
    beta B p (rhoH B a y) = ((rho B (star a)).transpose.map (· ^ p)).mulVec (beta B p y) := by
  intro R _ p _ _ d O _ _ B a y
  refine dotProduct_eq _ _ fun u => ?_
  have hadj := (_root_.GlobalTheory.CompanionTheory.Ar.Conj.rhoH_hom_adjoint R d O B).2.2 (star a) (alpha B p u) y
  rw [star_star] at hadj
  have htw := _root_.GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act R p d O B (star a) u
  rw [dotProduct_comm, dotProduct_beta, ← hadj, ← htw, ← dotProduct_beta, dotProduct_comm _ (beta B p y),
    Matrix.dotProduct_mulVec, Matrix.transpose_map, Matrix.mulVec_transpose]

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlowUpFibreSemilocal
section
namespace GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} :=
  PositivityTheory.Xgn.t_s_blowupfibre

end GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPairBaseExtensionStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_base_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ) (f g : Fin N → MRing ι O), IsFlagPair ϖ x E E' w w' b b' f g → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → IsFlagPair ϖ (joinCoord x z) EB E'B w w' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ w₁' : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → (∀ i, w₁' i = bc (w' i)) → ∀ EB E'B : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsPullBC O x z bc E' E'B → IsFlagPair ϖ (bcCoord x z) EB E'B w₁ w₁' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair.main | exact GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalDataBaseChange
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem map_mats_baseChange : ∀ (R R₂ : Type) [CommRing R] [CommRing R₂] (f : R →+* R₂) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R₂ d O), IsMapOf f B B₂ → (∀ a, rho B₂ a = (rho B a).map f ∧ bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f) ∧ bil B₂.sy 1 1 = (bil B.sy 1 1).map f ∧ ∀ p, hw B₂ p = (hw B p).map f ∧ am B₂ p = (am B p).map f :=
  PositivityTheory.HtPt.Cc.map_mats

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupActionRingHom
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem rho_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  intro R _ d O _ _ B
  obtain ⟨ρ, h⟩ := GlobalTheory.ChF.linPart_act_ringHom R d B.G O B.A R (RingHom.id R)
  refine ⟨ρ, fun a => ?_⟩
  rw [(h a).2]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProductStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_ideal_frobenius_product : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → ∀ n, (∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈ sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p}) ∧ (∃ δ : R, c n ^ p = δ * c (n + 1)) ∧ ∀ δ : R, c n ^ p = δ * c (n + 1) → HasLen v R (OmType AA.carrier (σ ^ p ^ (n + 1))) (v (algebraMap R C δ)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_product | exact GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_product | (intros; apply GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_product <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusValuationStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_ideal_frobenius_valuation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → AA.carrier = Submodule.span R (Set.range fun (d : Fin f → Fin p) (a : F) => ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) ∧ ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = (∏ n : Fin f, v (algebraMap R C (c n))) ^ (p ^ f * (p - 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation | exact GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation | (intros; apply GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureCharacter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hChar_of_eigSp_ranks : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [CharZero K] (d r : ℕ) (B : Germ.FB K d (𝓞 E)) (ρ : 𝓞 E →+* Module.End K (Fin d → K)), (∀ a v, ρ a v = (rho B a).mulVec v) → Nat.card (E →+* K) = Module.finrank ℚ E → (∀ s s' : E →+* K, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) → Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ s') = r) → HChar B r :=
  @PositivityTheory.Xgn.hodge_character_generic

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NonFundamentalEigenLeSquareAugmentationStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_fundamental_eigen_le_square_augmentation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, ¬ IsFund p χ → eig AA.carrier χ ≤ sqIdeal (augIdeal AA.carrier) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation | exact GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation | (intros; apply GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NumericalSegreClosed
section
namespace GlobalTheory.CompanionTheory.Segre

theorem numericalSegre_closed : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.full

end GlobalTheory.CompanionTheory.Segre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.FieldNumbers

open GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.NumbersDVR

theorem projectionFormulaDegree :
    GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} :=
  ProjectionFormulaDegree.of_divPushForward
    (DivPushForward.proof ContractRelDimLe.proof DivPushForwardLocalZero)

end GlobalTheory.CompanionTheory.FieldNumbers
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientZarhinHodgeTateSubquotientStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_zarhin_hodge_tate_subquotient : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement → SubquotientStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate | exact GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate <;> assumption)
end

