module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.AdelicCompactOpens.HermDefONFamily
section
namespace Formalism.L2.Props

open Matrix
open scoped ComplexOrder

def HermDefON : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.PosDef → ∃ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y.det ∧ yᴴ * G * y = 1

end Formalism.L2.Props
end

-- bundled from Formalism.LocalToGlobal.AdelicCompactOpens.IntAdelesCompactOpen
section
namespace Formalism.L2.Props

open Filter Topology IsDedekindDomain NumberField

def IntAdelesCompactOpen : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} ∧
    IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

end Formalism.L2.Props
end

