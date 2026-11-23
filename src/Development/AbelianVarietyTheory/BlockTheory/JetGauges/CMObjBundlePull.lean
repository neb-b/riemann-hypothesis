module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.LamCM

section Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R]

abbrev epsAt (t : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ t)

def IsTan {G : Over S} [GrpObj G] (t : Sp R ⟶ S) (v : epsAt t ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left

def IsMultiple {G : Over S} {t : Sp R ⟶ S} (x : R) (v w : epsAt t ⟶ G) : Prop :=
  w.left = spMap (epsScaleR x) ≫ v.left

end Lie

section Line

variable {K : Type} [Field K] [NumberField K]

abbrev genPt (K : Type) [Field K] [NumberField K] : Sp K ⟶ Sp (𝓞 K) := spMap (algebraMap (𝓞 K) K)

end Line

section Pol

variable {K : Type} [Field K] [NumberField K]

end Pol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

def psi (H : Host E) : Set (E →+* ℂ) := {τ | τ (H.rt : E) = H.rt0}

def psiBar (H : Host E) : Set (E →+* ℂ) := {τ | τ (H.rt : E) = -H.rt0}

structure CMObj (c : Coeff l) (p q : ℕ) : Type 1 where

  K : Type
  [field : Field K]
  [numberField : NumberField K]
  [alg : Algebra c.F K]

  B : Out.PolAV (Sp (𝓞 K))

  AP : Out.PolAV (Sp (𝓞 K))

  AC : Out.PolAV (Sp (𝓞 K))
  ιB : Out.RingAct B.A (𝓞 E)
  ιP : Out.RingAct AP.A (𝓞 E)
  ιC : Out.RingAct AC.A (𝓞 E)

  φP : Fin p → (AP.A ⟶ B.A)
  φP_hom : ∀ j, IsMonHom (φP j)
  φP_lin : ∀ j a, ιP.act a ≫ φP j = φP j ≫ ιB.act a

  φC : Fin q → (AC.A ⟶ B.A)
  φC_hom : ∀ j, IsMonHom (φC j)
  φC_lin : ∀ j a, ιC.act a ≫ φC j = φC j ≫ ιB.act a

  hP : Fin p → 𝓞 E

  hC : Fin q → 𝓞 E

  ηP : psi H → (epsAt (genPt K) ⟶ AP.A)

  ηC : psiBar H → (epsAt (genPt K) ⟶ AC.A)

  ℓP : psi H → MLine K

  ℓC : psiBar H → MLine K

attribute [instance] CMObj.field CMObj.numberField CMObj.alg

namespace CMObj

variable {c : Coeff l} {p q : ℕ} (o : CMObj c p q)

end CMObj

end GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull
