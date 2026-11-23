module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassGlEqClass
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleLeft
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MulClassBasisRight
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleFold
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleCast
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.Bundle0002
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.Bundle0001
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.TriSupportedLe

@[expose] public section

namespace CompanionTheory.Groth

theorem groth_of_cls (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Cls k) :
    GlobalTheory.Published.GrothendieckRingPolynomial := by
  refine groth_of_steps (fun k _ _ _ _ => ?_) triAut uniTri
  have hm : MulCls k := by apply mulCls
  have ha : Assoc k := by apply assoc; exact hm
  have hc : Comm k := comm k
  have h1 : One k := by apply one
  have hl : ProdList k := by apply prodList; exact hm
  refine ⟨H k, hm, ha, hc, h1, hl, tri k (H k), ?_, by apply jCls, by apply jSeg, altSum k⟩
  apply multOne <;> first | exact H k | assumption

end CompanionTheory.Groth
