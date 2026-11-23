module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0762
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0560
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0571
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0722
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LawOfOrbitMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainProperty
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0604
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0564
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0717
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0715
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemUpperHalf

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnipotentRadicalConjScalingStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_unipotent_radical_conj_scaling : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)], ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d, νN.map (fun n : radN d => MulAut.conjNormal m n) = ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | exact GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | (intros; apply GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsLast
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem main : IdemEx → LatBound → QK → IkSch → ThetaSideMeasure := by
  intro _ hLat hQK hIk D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx
  have hdx := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ D W b₀ hb x₀ hx
  have hDom := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.dom
  have hOF := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound hLat
  have hZ := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.zp_eq
  have hA := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq
  have hJ := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds
  have hB := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.jnBl
  have hE := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action
  have hS := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.shift
  have hL := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.ikLint
  have hF := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds
  refine ⟨nuT hn I μ x₀, ⟨_root_.GlobalTheory.CompanionTheory.ColumnSplitting.isFiniteMeasureOnCompacts_nuT D n t B W d hn I μ hμ b₀ hb x₀ hx, _root_.GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp hZ hA D n t B W d hn I μ hμ b₀ hb x₀ hx,
    fun h _ => GlobalTheory.T.orbit_measure_unitary_group_invariant hQK _root_.GlobalTheory.CompanionTheory.ColumnSplitting.LawPf.law D n t B W d hn I μ hμ x₀ h,
    fun y _ => _root_.GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant D n t B W d hn I μ hμ x₀ y,
    fun g _ => _root_.GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov D n t B W d hn I μ hμ x₀ g⟩,
    _root_.GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero D n t B W d hn I μ hμ x₀, fun Φ hΦ η hη => ?_⟩
  have hc := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.integrable_core hIk hDom hOF hS hL hF hB D n t B W d hn I θ hθ μ hμ x₀ hdx Φ hΦ η hη
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hc
  exact ⟨h1, _root_.GlobalTheory.CompanionTheory.ColumnSplitting.continuous_orb_shear hIk hDom hOF hS hB hE D n t B W d hn I θ hθ x₀ hdx Φ hΦ, h2⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExists
section
noncomputable section

open scoped NNReal Matrix TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.StdChart

theorem bdet_Psi (D : D7) {n : ℕ} (χ : (AE D)ˣ →* Circle) (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D))
    (h : GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1) :
    bdet (Sum.inl '' (Set.univ : Set (Fin n))) (Psi D χ n g).1 = Matrix.GeneralLinearGroup.det a := by
  rw [Psi_val]
  exact bdet_eq D _ a h

theorem tStd : TStd := by
  intro hD hI D χ n
  refine ⟨Psi D χ n, ?_, ?_, ?_, ?_⟩
  · exact mem_GF D χ
  · exact mem_P D χ
  · exact mem_K D χ hD hI
  · exact bdet_Psi D χ

end GlobalTheory.CompanionTheory.StdChart

end
end

