module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabfin
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

@[expose] public section

noncomputable section
namespace Formalism.MainNotions.Gaps.LevGap
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section DefCong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

end DefCong

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable [TopologicalSpace R] [IsTopologicalRing R]

variable [FiniteDimensional F E]

end Gen

section GLc

variable {M : Type} [CommRing M] [TopologicalSpace M] [IsTopologicalRing M] [T2Space M]
  {n : Type} [Fintype n] [DecidableEq n]

end GLc

section Dec

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
variable {R : Type} [CommRing R] [Algebra F R] (O : Subring R)

variable [NumberField F]

variable {n : Type} [Fintype n] [DecidableEq n]

end Dec

section Adele

variable {F : Type} [Field F] [NumberField F]

theorem compact_Ov (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) := by
  have h1 : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have h2 : IsClosed ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Valued.isClosed_valuationSubring _
  have h3 : CompleteSpace (v.adicCompletionIntegers F) := h2.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
    ⟨h3, (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F)), h1⟩

theorem isCompact_intAd : IsCompact (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) := compact_Ov
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_intAd : IsOpen (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

open scoped RestrictedProduct in
theorem t2Space_adeleRing_numberField : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Adele

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

end Main

section Bridge

open Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

section Loc

variable (v : HeightOneSpectrum (𝓞 F))

end Loc

section ParSec

variable {k : ℕ} (P : Par F E k) (v : HeightOneSpectrum (𝓞 F))

end ParSec

end Bridge

section Facts

open Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

end Facts

end Formalism.MainNotions.Gaps.LevGap
