module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
public import ReciprocityTheory.Hypotheses.GalCoh
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0004
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0008
public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardH1EqCardH0MulCardH2
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousCompOfIsOpenKer

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.Imports
section
namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity :=
  CompanionTheory.FamInh.globalArtin

end GlobalTheory.CompanionTheory.Hypotheses₂
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def mnorm (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖

def wt (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := (gᴴ * g).trace.re

def IsSmoothVec (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ F : (Fin n → Fin n → ℂ) → H, ContDiff ℝ ∞ F ∧ ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z

def WordBound (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ HCSS.lieOf G) →
    ‖l.foldr (dRep π) v‖ ≤ C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod

def AlmostIsom (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ (Q : H → H → ℂ) (m M a : ℝ), 0 < m ∧ 0 ≤ M ∧ 0 ≤ a ∧
    (∀ x y z, Q x (y + z) = Q x y + Q x z) ∧ (∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) ∧
    (∀ x y, Q y x = star (Q x y)) ∧ (∀ x, m * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, ‖Q x y‖ ≤ M * ‖x‖ * ‖y‖) ∧
    ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H),
      (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤
        Real.exp (a * |t| * mnorm X) * (Q x x).re

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NSEqFixingSubgroup
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem NS_eq_fixingSubgroup (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S = (maxUnramifiedOutside F Ω S).fixingSubgroup :=
  le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (_root_.GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS F Ω S)

end GlobalTheory.CompanionTheory.Hypotheses₂
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnramifiedOrthogonality
section
namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem unramifiedOrthogonality : ReciprocityTheory.Gal.UnramifiedOrthogonality :=
  UnrOrth.unramifiedOrthogonality_of localFiniteness localTateDuality
    LocalEuler.localEulerChar_holds

end GlobalTheory.CompanionTheory.Hypotheses₂
end

