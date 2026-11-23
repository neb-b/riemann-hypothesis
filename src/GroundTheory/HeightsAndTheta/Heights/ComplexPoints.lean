module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import GroundTheory.HeightsAndTheta.Heights.ComplexProjective

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

structure ProjScheme (A : Type u) [CommRing A] (N : ℕ) where

  X : Scheme.{u}

  ι : X ⟶ projectiveSpace A N

  isClosedImmersion : IsClosedImmersion ι

attribute [instance] ProjScheme.isClosedImmersion

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

variable (X : ProjScheme A N)

end ProjScheme

end

end GroundTheory.Heights₂.Heights
