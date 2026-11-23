module

public import Development.EtaleCohomology.CyclotomicDiscriminants.Bundle0001
public import Development.EtaleCohomology.CyclotomicDiscriminants.Bundle0002

@[expose] public section

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.FinSDetect
section
namespace LateralTheory.Fin.SDetect
theorem detection_statement_holds : UpperTheory.V.ZK.SDetect := by
  apply LateralTheory.Q.SDetectCut.goal
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SDetect := detection_statement_holds
end LateralTheory.Fin.SDetect
end

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.FinSFewOf
section
namespace LateralTheory.Fin.SFewOf
theorem few_of_statement_holds : UpperTheory.V.ZK.SFewOf := by
  apply LateralTheory.Q.SFewOfCut.sFewOf
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SFewOf := few_of_statement_holds
end LateralTheory.Fin.SFewOf
end

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.FinSStein
section
namespace LateralTheory.Fin.SStein
theorem stein_statement_holds : UpperTheory.V.ZK.SStein := by
  apply LateralTheory.Q.SSteinT.SStein_of
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SStein := stein_statement_holds
end LateralTheory.Fin.SStein
end

