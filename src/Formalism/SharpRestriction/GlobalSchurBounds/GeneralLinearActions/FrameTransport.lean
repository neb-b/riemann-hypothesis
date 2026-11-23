module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

structure GaugeFam (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) where

  μ : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), Measure (HA (AF F) σ J)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

def FrameRel {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E)
    (B : Matrix (Fin M) (Fin M') E) (g : HA (AF F) σ J) (g' : HA (AF F) σ J') : Prop :=
  ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      B.map (inclR (AF F)) =
    B.map (inclR (AF F)) *
      ((HA.mat (AF F) σ J' g' : GL (Fin M') (AF F ⊗[F] E)) : Matrix (Fin M') (Fin M') (AF F ⊗[F] E))

namespace GaugeFam

variable (G : GaugeFam F E σ)

def IsHaar : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHaarH F E σ M J (G.μ M J)

def BasisInv : Prop :=
  ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J →
    J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) →
    AllSome (fun e : HA (AF F) σ J ≃* HA (AF F) σ J' =>
      ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) fun e =>
      (G.μ M J).map e = G.μ M J'

def StepCompat : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    3 ≤ M + 1 → IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) →
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B → IsHermND σ J' →
    AllSome (IsCharAF F) fun ψ =>
    AllSome (IsXbetaMeasure F E σ (M + 1) J ψ β) fun νX =>
    AllSome (fun e : Hstab (AF F) σ J x ≃* HA (AF F) σ J' =>
      ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) fun e =>
      IsCompatible F E σ (M + 1) J x (G.μ (M + 1) J) ((G.μ M J').map e.symm) νX

def IsGauge : Prop := G.IsHaar ∧ G.BasisInv ∧ G.StepCompat

end GaugeFam

def volHE (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) : ENNReal :=
  covolume (HFinIn (AF F) σ J) (HA (AF F) σ J) (G.μ M J)

def volH (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) : ℝ := (volHE G M J).toReal

end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
