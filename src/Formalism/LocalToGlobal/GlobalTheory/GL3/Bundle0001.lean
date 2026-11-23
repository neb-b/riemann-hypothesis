module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.LambdaConjLatticeUniform
public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.ThetaTranslationOperatorApply
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Th0TranslateProduct
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.ExistsTorsionPointOfLattice
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical Formalism.MainNotions
open Formalism.L2.Th1 (F2.IsLat F2.HasCM)

theorem sgStar_spec (L : PeriodPair) :
    Differentiable ℂ (Formalism.L2.Th1.F.sgStar L) ∧ deriv (Formalism.L2.Th1.F.sgStar L) 0 = 1 ∧
      (∀ z, Formalism.L2.Th1.F.sgStar L (-z) = -Formalism.L2.Th1.F.sgStar L z) ∧
      ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω (Formalism.L2.Th1.F.sgStar L) z =
        (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * Formalism.L2.Th1.F.sgStar L z := by
  obtain ⟨h1, h2, -, h4, -⟩ := Formalism.L2.Th1.F.sgStarBasic L
  refine ⟨h1, h4, h2, fun ω hω z => ?_⟩
  rw [Formalism.L2.GlobalTheoryTheory.taylorLogMetric_U1_eq_U1, Formalism.L2.Th1.F2.thetaTranslationOperator_apply]
  have hfix := Formalism.L2.Th1.F.sgStarFixed L ω z hω
  by_cases h : ω / 2 ∈ L.lattice
  · have hs : Formalism.L2.Th1.F.semiChar L ω = 1 := by unfold Formalism.L2.Th1.F.semiChar; simp [h]
    have h' : ω / 2 ∈ L.lattice.toAddSubgroup := h
    rw [if_pos h', one_mul, ← hfix, hs, one_mul]
  · have hs : Formalism.L2.Th1.F.semiChar L ω = -1 := by unfold Formalism.L2.Th1.F.semiChar; simp [h]
    have h' : ω / 2 ∉ L.lattice.toAddSubgroup := h
    rw [if_neg h', ← hfix, hs]
    ring

theorem sgStar_eq (L : PeriodPair) : Formalism.MainNotions.TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  have hlat : L.lattice.toAddSubgroup = PI.lat2 L.ω₁ L.ω₂ := Submodule.span_int_eq_addSubgroupClosure _
  have hIm : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
    have := Formalism.L2.Th1.F.areaPos L
    unfold Formalism.L2.Th1.F.area at this
    exact abs_pos.mp this
  have hF := sgStar_spec L
  have hE := Classical.epsilon_spec (p := fun G : ℂ → ℂ => Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
    ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G z =
      (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G z) ⟨_, hF⟩
  have huniq : ∀ G G' : ℂ → ℂ,
      (Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
        ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G z =
          (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G z) →
      (Differentiable ℂ G' ∧ deriv G' 0 = 1 ∧ (∀ z, G' (-z) = -G' z) ∧
        ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G' z =
          (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G' z) → G = G' := by
    intro G G' hG hG'
    rw [hlat] at hG hG'
    exact sigma_star_unique L.ω₁ L.ω₂ hIm G G' hG hG'
  unfold Formalism.MainNotions.TaylorLogMetric.sgStar
  exact huniq _ _ hE hF





end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.IntegralityIffAwayAtD
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

def OneAt (D : D7) (p : ℕ) (𝔞 : IdE D) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ 𝔞, (s : D.host.E) * x ∈ (1 : IdE D)) ∧ (s : D.host.E) ∈ 𝔞

def LemmaU (D : D7) : Prop :=
  ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (𝔞 : IdE D),
    N1 D 𝔞 → OneAt D p 𝔞 → χ 𝔞 ∈ Qbar ∧ ‖lamC lam (χ 𝔞)‖ = 1

def DetOneAt (D : D7) : Prop :=
  ∀ (p N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L → OneAt D p (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L)

def ChiFacUnit (D : D7) : Prop :=
  ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') L' →
      Base.chiFac χ N N' L L' ∈ Qbar ∧ ‖lamC lam (Base.chiFac χ N N' L L')‖ = 1

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
end
end

