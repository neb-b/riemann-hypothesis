module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def mono4 {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (a : (AE D)ˣ) (e : Fin 4 → ℤ) : ℂ :=
  chrPow s₁.χV a (e 0) * chrPow s₁.χW a (e 1) * chrPow s₂.χV a (e 2) * chrPow s₂.χW a (e 3)

def LinExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k)
    (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    ∃ lS lT : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ (CharUnramAt D χS p.v → IsUnram lT) ∧
      (lS q.unit : ℂ) = (((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2) : ℝ) : ℂ) * chrPow χT (p.idele q.unit) (-1) ∧
      (lT q.unit : ℂ) = (((resCard k : ℝ) ^ ((S.rank : ℝ) / 2) : ℝ) : ℂ) * chrPow χS (p.idele q.unit) 1 ∧
      ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) (LS : Lat S)
        (LT : Lat T) (f₀ : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ) (f : WO S T → ℂ), Over ψ α β LS LT f₀ Ψ f →
        ∀ (g : GL n' k) (h : GL n k), Over ψ α β LS LT f₀ (fun x => (lS (Matrix.GeneralLinearGroup.det g) : ℂ) *
          (lT (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ ((h⁻¹ : GL n k).val * x * g.val)) (om (α.gl g, β.gl h) f)

def SourceExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1), ∃ (r : ℝ) (e : ℤ), 0 < r ∧
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ →
    CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS p.v → CharUnramAt D χT p.v →
    ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ →
    ∀ (P : Pair k n') (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsFullLattice k] (LS : Lat S) (LT : Lat T) (f₀ Ξ : WO S T → ℂ)
      (Ξ' : Pair k n → WO S T → ℂ), Over ψ α₀ β LS LT f₀ (latInd (gluedS q 1 P.ker P.vec) Λ) Ξ →
      (∀ Q ∈ withLat Λ, Over ψ α₀ β LS LT f₀ (tensCol (phiOne P Q) (charInd (resChar χ hχ q) Q)) (Ξ' Q)) →
      ∀ φ, IsRam α φ → liftA o om vA (φ P) Ξ =
        ((r : ℂ) * chrPow χT (p.idele q.unit) e) • ∑ Q ∈ withLat Λ, liftA o om vA (FFStar q (resChar χ hχ q) φ P) (Ξ' Q)

def VertexExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ →
    ∃ ε : 𝓀[k]ˣ, (ε = 1 ∨ ε = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''],
      ∃ (r : ℝ) (e : ℤ), 0 < r ∧ ∀ (P : Pair k n') (Q : Pair k n) (R : Pair k n'')
        (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
        (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), UnrAt s₁ p.v → UnrAt s₂ p.v →
      ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
        (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
      ∀ (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
          (f₁ Ξ₁ Ξ₁' : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ Ξ₂' : WO J.W₀ B'.V₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Ξ₁ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q) (vecInd Q.lat)) Ξ₁' →
          Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (gluedS q 1 R.ker R.vec)) Ξ₂ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow (phiOne Q R) (dualInd Q.lat)) Ξ₂' →
          ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ =
            ((r : ℂ) * chrPow s₁.χW (p.idele q.unit) e) •
              hand0 s₁ s₂ l vL (dia ε (FFStar q (resChar χ hχ q) φ) P) Ξ₁' Ξ₂'

def HandInv (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ),
    IsThetaFunO ψ B.V J.W Φ₁ → IsThetaFunO ψ J.W B'.V Φ₂ → ∀ φ, IsContAut B.A φ → ∀ g h₁ h₂,
      (∀ r ∈ jacGrp J.d, Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g (r * h₁) h₂ = Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) ∧
      ∀ G, IsContAut B'.V G → ∀ r ∈ besGrp B'.d B'.o,
        B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (r * h₂)) (rTrans (r * h₂) G) =
          B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) (rTrans h₂ G)

end GlobalTheory.FinPl

end
