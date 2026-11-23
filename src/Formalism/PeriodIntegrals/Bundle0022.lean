module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.AmpOrbQ
section
open MeasureTheory
open scoped ENNReal

noncomputable section

namespace PI.AmpOrbQ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def OrbQuotEx : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μR : Measure (Mt k r)), IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ → IsHaarOn (RStab k r g₀) μR →
    ∃ ν : Measure (PairSp k r), IsOrbQuot L g₀ μR ν

def HaarLieN : Prop :=
  ∀ (k r : ℕ) (κ : ℝ≥0∞), κ ≠ 0 → κ ≠ ⊤ →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) (Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) κ)

end PI.AmpOrbQ
end
end

-- bundled from Formalism.PeriodIntegrals.AmpRoot
section
open MeasureTheory
open scoped ENNReal

noncomputable section

namespace PI.AmpRoot

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def RootJac : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μ₀ : Measure (Mt k r)), IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ →
    μ₀ {x | Matrix.of x ∉ Rset k r g₀} = 0 →
    μ₀.map (rootCoords k r L.z' p) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) • volume →
    IsRootMeas L p g₀ (μ₀.map (fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j))

def RelAtPt : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    star L.c = L.c → IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ → IsRelStab L g₀

end PI.AmpRoot
end
end

-- bundled from Formalism.PeriodIntegrals.AmpRootH
section
open MeasureTheory
open scoped ENNReal

noncomputable section

namespace PI.AmpRootH

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def RootHaar : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μ₀ : Measure (Mt k r)), L.c ≠ 0 → IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ →
    μ₀ {x | Matrix.of x ∉ Rset k r g₀} = 0 →
    μ₀.map (rootCoords k r L.z' p) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) • volume →
    IsHaarOn (RStab k r g₀) (μ₀.map (fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j))

end PI.AmpRootH
end
end

-- bundled from Formalism.PeriodIntegrals.BetaLUniq
section
noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PI.BetaLUniq

abbrev Lt (D : D7) : Type := Submodule (𝓞 D.host.E) (hS D).V

abbrev Fl (D : D7) (T : ℕ) : Type := LFlag (hS D) D.R.rS ((T : ℕ) : D.host.E)

end PI.BetaLUniq

namespace PI


open PI.BetaLUniq in
def BetaLUniq : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word),
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' F'' : Fl D (Tu D u')) (β₁ β₂ : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' → IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    IsPair Λ F F' F'' β₁ (gS D) → IsPair Λ F F' F'' β₂ (gS D) →
    Lat.s0 Λ F F' F'' β₁ D.R.k = 1 → Lat.s0 Λ F F' F'' β₂ D.R.k = 1 →
      ∀ x ∈ orth (hS D) (Xsp F'), β₂ x - β₁ x ∈ Xsp F''

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.HwFixedLine
section
noncomputable section

namespace PI.HwFix

open Formalism.BasicNotions Formalism.L2.DIV MvPolynomial
open scoped Matrix

section Stab

variable {n : ℕ} {ι : Type} [Fintype ι]

def MtwStable (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)) : Prop :=
  ∀ g : ι → GL (Fin n) ℂ, ∀ x ∈ S, rhoK lam g x ∈ S

def mtwHw (lam : ι → DomWeight n) : VV ℂ lam :=
  ⟨ten fun τ => extremal ℂ n (lam τ), Submodule.subset_span ⟨fun τ => extremal ℂ n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (PI.WGB.natW_anti_A (lam τ)), rfl⟩⟩

end Stab

def MtwUni {n : ℕ} {ι : Type} (g : ι → GL (Fin n) ℂ) : Prop :=
  ∀ τ, (∀ i j, j < i → ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
    ∀ i, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1

def HwFixedEx : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)), S ≠ ⊥ → MtwStable lam S →
    ∃ v ∈ S, v ≠ 0 ∧ ∀ g : ι → GL (Fin n) ℂ, MtwUni g → rhoK lam g v = v

def HwFixedLine : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (v : VV ℂ lam),
    (∀ g : ι → GL (Fin n) ℂ, MtwUni g → rhoK lam g v = v) → ∃ c : ℂ, v = c • mtwHw lam

end PI.HwFix
end
end

-- bundled from Formalism.PeriodIntegrals.PairCorankPos
section
noncomputable section

open scoped Classical

namespace PI.PairCorankPos

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

def CorankPosG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r k : ℕ),
    finrank E S.V = k + 2 * r + 1 →
    ∀ Λ : Submodule (𝓞 E) S.V, Submodule.IsFullLattice E Λ →
    ∀ (T T' : E) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V),
      IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → 1 ≤ Formalism.MainNotions.S.Lat.s0 Λ F F' F'' β k

end PI.PairCorankPos
end
end

