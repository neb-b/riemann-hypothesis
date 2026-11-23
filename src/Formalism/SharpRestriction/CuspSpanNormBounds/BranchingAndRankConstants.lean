module

public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusBranching

export Formalism.MainNotions.S.UnitaryVolumeMass (volU ForAmpH)

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

section admitted

variable (D : D7) (large₂ : SizeData₂ D)

def adm1 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm2 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTDl D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm3 (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  UnitaryVolumeMass.stMOM D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def adm5 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

def adm9 (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  UnitaryVolumeMass.PieriNormDegreeFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1

def adm10 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.FormalDegreeUnitStepRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

end admitted

section Adm2

variable (D : D7) (large₂ : SizeData₂ D)

def adm11 (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stSchur D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

def adm12 : Prop :=
  UnitaryVolumeMass.stWeyl D

end Adm2

def adm6 : Prop :=
  UnitaryVolumeMass.stBRmult

def adm7 : Prop :=
  UnitaryVolumeMass.stBRhad

section Conclusion₂

variable (D : D7) (large₂ : SizeData₂ D)

def Conclusion1 (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

def Conclusion2 (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.L2PointwiseLoss D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def PointsLemma (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  UnitaryVolumeMass.stL2prod D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def Conclusion4 (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stABS D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def PrimeSumLogBound (C' Cl Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  UnitaryVolumeMass.stABSconv D large₂ C' Cl Cg cb Cu cT CT C0 A C1

def Conclusion5 (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  UnitaryVolumeMass.stABSprod D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def Conclusion6 (C' Cl Cg cb Cu cT CT C0 A C1 C δ : ℝ) : Prop :=
  UnitaryVolumeMass.stMIN D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ

def division_rows_rational_lattice (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ : ℝ) : Prop :=
  UnitaryVolumeMass.stDEC D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ

def aux₃ (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ : ℝ) : Prop :=
  Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 C ∧ Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧
  PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch ∧ Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧
  PrimeSumLogBound D large₂ C' Cl Cg cb Cu cT CT C0 A C1 ∧
  Conclusion5 D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch ∧ Conclusion6 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ ∧
  division_rows_rational_lattice D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ

def admitted (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CPT CDl CMo hilbertNinetyConstant CS : ℝ) : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl ∧
  adm3 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CMo ∧ adm5 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm6 ∧ adm7 ∧
  adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 ∧ adm10 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant ∧
  adm11 D large₂ C' Cl Cg cb Cu cT CT C0 C1 CS ∧ adm12 D

def IntegralityFromMetric (C' Cl Cg cb Cu cT CT C0 C1 CS C : ℝ) : Prop :=
  adm11 D large₂ C' Cl Cg cb Cu cT CT C0 C1 CS → adm12 D → Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

def HodgeTateFromSandwich (C' Cl Cg cb Cu cT CT C0 A Cn C1 CPT Cc C : ℝ) : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT → Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 Cc →
    Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def TowerRallisLemma (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop := PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def GGFromIrreducibility (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop := Conclusion5 D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def ShareFromInputs (C' Cl Cg cb Cu cT CT C0 A C1 Ca C δ : ℝ) : Prop :=
  adm5 D large₂ C' Cl Cg cb Cu cT CT C0 → Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Ca →
    Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Ca → Conclusion6 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ

end Conclusion₂

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF5 (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm5 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def admF9 (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cn, OwnEv Fm fun C' Cl x i => adm9 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1

def FamilyTwelfthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm12 (Fm.D x i)

end Family

end Formalism.MainNotions.VanishingOnXAndXPlusBranching
