module

public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SatakeDualWeyl.DefsCS

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure SplitAt (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E) where
  φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  sig : ∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)
  alg : ∀ c : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] c) = (c, c)
  int : ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F
  ori : Valued.v (φ (a ⊗ₜ[F] (1 : v.adicCompletion F))).1 < 1

structure Par (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) where
  σ : E →ₐ[F] E
  J : Matrix (Fin k) (Fin k) E
  gp : Fin 2 → ℕ
  T : ℕ
  pz : 𝓞 E
  a : Fin 2 → E

namespace Par

variable {k : ℕ} (P : Par F E k)


end Par

end Gen

section HostPar

variable {R : Ranks} (H : Host R)

end HostPar

end Formalism.MainNotions.Gaps.LG

end
