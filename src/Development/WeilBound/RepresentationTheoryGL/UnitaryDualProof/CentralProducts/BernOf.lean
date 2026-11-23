module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.LeviScalars.EmbScalarMemLevi
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.EigenInjectivity.SubInjective
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.PositiveProducts.PosProdOf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.SubquotientBounds.LeOfSubsingletonSubQuot
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.UnitarisableHypotheses.NormEqOneOfUnitarisable
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.CentralSub

@[expose] public section

noncomputable section

namespace PositivityTheory.RgUd.Prod.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bern_of (hT : DerivTop k) (hP : DerivPos k) (hL : GlobalTheory.RgGu.Leib.LeibnizOrd k) : BernAt k :=
  Asm.bern_of_parts k hT
    (Pos.posProd_of k hT hP hL (LF.lfDeriv k) (CSel.centralSub k) (Eig.eigProd k) (Eig.eigFilt k))
    (Pos2.topProd_of k hT hP hL (LF.lfDeriv k) (CSel.centralSub k) (Eig.eigProd k) (Eig.eigFilt k))

end PositivityTheory.RgUd.Prod.Final
