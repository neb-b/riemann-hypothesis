module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.StableBlock
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTwistedConstantTermMatches
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import GroundTheory.GlobalFields.TateThesis.LocalConductor

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.matchSplit : UpperTheory.V.Z.Tf.GlobalTraceComparison.MatchSplit := by
  intro E _ _ _ w hw n a b h μ f ⟨K', hKo, hKl, hf⟩
  obtain rfl : b = n - a := by omega
  have ha : a ≤ n := by omega
  have hL : IsLevel (MonoidHom.id _) (KL n w) K' := ⟨hKo, hKl, fun k hk => hk⟩
  have hμ : IsOpen {x | μ.loc w x = 1} :=
    GroundTheory.Global.isOpen_ker_of_continuous w GroundTheory.Global.Complex.units_noSmallSubgroups (μ.loc w)
      (μ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele w))
  obtain ⟨K₁, K₂, -, h₁, h₂, -, -, -, -, -, -, hH⟩ := GlobalTheory.T.exists_block_levels_twistedConstantTerm_split_place E n a ha w hw (μ.loc w) hμ K' hL
  exact ⟨⟨K₁.prod K₂, h₁.1.prod h₂.1, Subgroup.prod_mono h₁.2.1 h₂.2.1, hH f hf⟩, _root_.GlobalTheory.BCT.SplitCtMatch.match_ctMu_of_isSplitAt E n a ha w hw (μ.loc w) K' hL f hf⟩
