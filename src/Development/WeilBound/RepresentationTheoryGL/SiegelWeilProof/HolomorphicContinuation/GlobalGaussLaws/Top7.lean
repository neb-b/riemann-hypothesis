module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Top6
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FTfact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0048
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0034

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem top7 (hG : GenA) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top6 fTfact hG schDeriv (derivOne wtc) hId hC

end PositivityTheory.Rg.Sw.Glob
