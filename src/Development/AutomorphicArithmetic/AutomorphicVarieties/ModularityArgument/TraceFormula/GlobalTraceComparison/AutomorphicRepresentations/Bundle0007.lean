module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPiAdm
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField GlobalTheory.CuspRep PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open PositivityTheory.Rg.BcB.E.E3.fintype in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.piAdm_pf :
    PiAdm := by
  intro E _ _ _ n _ π _ K W hK hW
  have hs : ∀ (τ : E →+* ℂ) (z : ℂ), ∃ c : ℂ, ∀ φ ∈ π.V, cap τ z φ = c • φ := fun τ z =>
    π.exists_scalar (Algebra.subset_adjoin ⟨τ, z, rfl⟩) (by
      rintro (k | k | X)
      exacts [commute_cap_finRep τ z k, GlobalTheory.CapAdInv.cap_commute_rt_infGL E n τ z _, commute_cap_lie τ z X])
  choose c hc using hs
  haveI := wl_fin W
  haveI hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E n K hK _ (sig W) (sig_cont W) c
  refine ⟨π.V ⊓ Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (sig W) c), inf_le_left,
    Submodule.finiteDimensional_inf_right _ _, fun ψ hψ ht => ⟨hψ, Submodule.subset_span
      ⟨(π.cusp ψ hψ).1, fun k hk => Subtype.ext (funext fun g => ht.1 k hk g),
        coeff_mem W ψ ht.2, fun τ z => hc τ z ψ hψ⟩⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.WtExPf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.wtEx_pf :
    WtEx := by
  intro E _ _ _ n π hreg
  have h : ∀ φ : E →+* ℂ, ∃ lam : DomWeight n, π.HasInfChar φ (infOfWeight lam) := fun φ => by
    have hm : π.HasInfChar φ ((CG.mk π).infChar φ) :=
      GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E n (fun τ u o => GlobalTheory.SpehInfChar.cap_commute_act τ u o) (CG.mk π) φ
    obtain ⟨lam, hl⟩ := DiscreteGroups.T1.G.reg_of hreg hm
    exact ⟨lam, hl ▸ hm⟩
  choose lamE hlam using h
  exact ⟨lamE, hlam⟩
end

