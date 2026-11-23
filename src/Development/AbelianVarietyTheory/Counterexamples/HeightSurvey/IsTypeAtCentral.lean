module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.TypeAtTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rep
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Rep

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem isTypeAt_zero {τ : D.what₂.Tau} {S : SPar} : IsTypeAt θ V τ S 0 ↔
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsEnum S lam ε ∧ IsDS ε lam σ ∧ IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ := by
  constructor
  · rintro ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, -⟩
    exact ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4⟩
  · rintro ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4⟩
    refine ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, fun x => ⟨fun _ => 0, fun i => ?_, fun _ => 0,
      fun i => ?_, ⟨[], fun _ => 0, by simp, fun i w _ => by simp, fun S' _ => by simp,
        ⟨fun _ => 0, continuous_const, fun g _ w _ => by simp⟩⟩, fun g _ => by simpa using hasSum_zero⟩⟩
    · intro k Xs _
      simp only [map_zero]
      exact contDiff_const
    · exact ⟨[], 0, by simp, fun w _ => by simp⟩

end GlobalTheory.TypeAtTest
end
