module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.LocStep
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceFormAlt
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.ThmA
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerivPos
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.BernOf
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.HighestDerivProd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.BernAll
section
namespace PositivityTheory.RgUd.All

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmT : ThmT k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with h | rfl
  · haveI : Fact p.Prime := ⟨h⟩
    exact TP.Final.thmT k p
  · haveI : CharZero k := CharP.charP_to_charZero k
    exact T.Final.thmT k

theorem thmB : ThmB k := AB.Final.thmB k (AB.Final.thmA k (thmT k))

theorem bernAt : BernAt k :=
  Prod.Final.bern_of k (Form.U.Final.derivTop k (thmB k)) (Form.U.Final.derivPos k (thmB k))
    (GlobalTheory.RgGu.Leib.Hand.leibnizOrd k)

theorem bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible := fun k _ _ _ _ => bernAt k

end PositivityTheory.RgUd.All
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ThmBChar0
section
namespace PositivityTheory.RgUd

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

theorem thmB_char0 : ThmB k := AB.Final.thmB k (AB.Final.thmA k (T.Final.thmT k))

theorem bern : BernAt k :=
  Prod.Final.bern_of k (Form.U.Final.derivTop k (thmB_char0 k)) (Form.U.Final.derivPos k (thmB_char0 k))
    (GlobalTheory.RgGu.Leib.Hand.leibnizOrd k)

end PositivityTheory.RgUd
end

