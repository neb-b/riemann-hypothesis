module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PLocGood
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PFactorField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PStruct
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PInertBase

@[expose] public section

namespace PositivityTheory.Rg.BcB.G3

theorem param : Param :=
  param_pf skewEx_pf (struct_pf factorField_pf) quadField_pf
    (locDict_pf clsNorm_pf clsOnto_pf clsEq_pf baseFrame_pf (inertBase_pf tensorCompl_pf) (splitSq_pf tensorCompl_pf)
      tensorCompl_pf) clsNorm_pf clsOnto_pf clsEq_pf locGood_pf

theorem count1 : Count1 := count1_pf param

theorem g3 : G8.G3 :=
  twisted_trace_formula_elliptic_expansion absSum_pf finCl2_pf invar2_pf (unit_pair_of_support locGood_pf genUnit_pf supp_pf) (count2_pf count1) supp_pf finPol2_pf

end PositivityTheory.Rg.BcB.G3
