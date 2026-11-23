module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace UpperTheory.Et

variable {R : Type} [CommRing R]

def prGen (R : Type) [CommRing R] (X : Scheme.{0}) : sec ((GlobalTheory.Et.freeOn R).obj X).obj X :=
  ap (toSheafify Scheme.proetaleTopology
    (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))).obj (uliftYoneda.{1}.obj X)))
    (ModuleCat.freeMk (ULift.up (𝟙 X)))

section Cont
variable (R) (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T]

def cPre : PMod R where
  obj U := ModuleCat.of (ULift.{1} R) (ULift.{1} C(U.unop, T))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ⟨g.down.comp f.unop.base.hom⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def cSh : GlobalTheory.Et.Shv R := (presheafToSheaf _ _).obj (cPre R T)

def cSec {U : Scheme.{0}} (g : C(U, T)) : sec (cSh R T).obj U :=
  ap (toSheafify Scheme.proetaleTopology (cPre R T)) (ULift.up g)

variable {R T} {T' : Type} [AddCommGroup T'] [Module R T'] [TopologicalSpace T'] [IsTopologicalAddGroup T']
  [ContinuousConstSMul R T']

def cPreMap (u : T →L[R] T') : cPre R T ⟶ cPre R T' where
  app U := ModuleCat.ofHom
    { toFun := fun g => ⟨(⟨u, u.continuous⟩ : C(T, T')).comp g.down⟩
      map_add' := fun a b => congrArg ULift.up (ContinuousMap.ext fun x => map_add u _ _)
      map_smul' := fun r a => congrArg ULift.up (ContinuousMap.ext fun x => map_smul u r.down _) }
  naturality _ _ _ := rfl

def cMap (u : T →L[R] T') : cSh R T ⟶ cSh R T' := (presheafToSheaf _ _).map (cPreMap u)

end Cont

section Adic
variable (l : ℕ) [Fact l.Prime]

end Adic

end UpperTheory.Et

end
