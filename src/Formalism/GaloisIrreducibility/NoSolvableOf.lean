module

public import Formalism.GaloisIrreducibility.Statement

@[expose] public section

namespace Formalism.GaloisIrreducibility

def LemmaAOf : Prop := OrbitSubSum → RestrictRoots → LemmaA

def IrredOf : Prop := LemmaA → Irred

def NoSolvableOf : Prop :=
  PowerPCycle → PrimitiveOfPCycle → JordanPrime → AltNotSolvable → NoSolvableTransitive

end Formalism.GaloisIrreducibility
