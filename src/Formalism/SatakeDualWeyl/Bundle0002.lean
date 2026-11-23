module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.SatakeDualWeyl.Bundle0001

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.NablaRepApply
section
noncomputable section

open Matrix TensorProduct

namespace Formalism.UG

def nablaRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (nabla O n k) where
  toFun g := (polyAct O n g).toLinearMap.restrict (fun P hP => Formalism.UG.P.nabla_subspace_stable O n k g P hP)
  map_one' := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n 1 (P : MvPolynomial n O) = (P : MvPolynomial n O)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n (g * h) (P : MvPolynomial n O) = polyAct O n g (polyAct O n h P)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n g h).1]
    rfl

def ratEquiv {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n]
    [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] : UJ (σ : E →+* E) J ≃* ratPts σ J R :=
  Subgroup.equivMapOfInjective (UJ (σ : E →+* E) J) (bc (inclE (F := F) R))
    (Formalism.UG.P.UG_inclusion_injective F E n R inferInstance)

end Formalism.UG
end
end

-- bundled from Formalism.SatakeDualWeyl.StatementG
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace Formalism.UG

def IsInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal

end Formalism.UG
end
end

