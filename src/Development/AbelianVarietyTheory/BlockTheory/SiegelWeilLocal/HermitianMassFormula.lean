module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg
open scoped TensorProduct ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianLocalData

variable {F : Type} [Field F] [NumberField F]


variable {E : Type} [Field E] [NumberField E] [Algebra F E]

section Loc

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
  (r : ℕ) (T T' : 𝓞 F) {v : HeightOneSpectrum (𝓞 F)} (δ : Fv F v) (g : ℕ)

end Loc



section Meas

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

end Meas

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianLocalData
