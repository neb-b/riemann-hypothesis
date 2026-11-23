module

public import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.TieRad
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.StatementTL

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.NumberFieldModels.ModelPt
section
namespace Formalism.MainStatements.NFTie

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

def NFModelPt : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), P.OK → MA.IsModelLevel P (MA.DQ P) L →
    ∀ l0 : ℕ, 1 ≤ l0 → l0 ≤ P.k → ∀ w : List C.Letter, KB.CutWord P l0 w → ∀ (a : Wd.Ix (Fin w.length)) (s : ℕ),
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (u : Fin m → List (MA.A P (MA.DQ P))) (C : ℝ), 0 ≤ C ∧
        (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧
        (∀ j, (u j).length = w.length ∧ ∀ x ∈ u j, x ∈ MA.hatSet P L) ∧
        ∀ f g : M.Ty P → MA.SmQ P.r P.TT,
          (∀ ρ q, MA.evQ P (g ρ) q = ((MA.Gq P q ^ s : ℝ) : ℂ) * MA.evQ P (f ρ) q) → ∀ q : MA.Qp P.r P.TT,
          ∑ ρ, ‖MA.evQ P (MA.actA P (Formalism.FourierDecayAlt.P.NormalFormRelations.gM P l0 L (D.positionted w) a) g ρ) q‖ ^ 2 ≤
            C * MA.Gq P q ^ (2 * s) * (Complex.normSq ((∏ l, q.1.1 l) * q.1.2))⁻¹ ^ w.length *
              ∑ j, ∑ ρ, ‖MA.evQ P (MA.actA P (b j * (u j).prod) f ρ) q‖ ^ 2

end

end Formalism.MainStatements.NFTie
end

-- bundled from CompanionTheory.AutomorphicTheory.NumberFieldModels.NFTieProv
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP.Gauge

namespace Formalism.MainStatements.NFTie

noncomputable section

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def GaugeQQ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def tr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)

end defs

end

end Formalism.MainStatements.NFTie
end

