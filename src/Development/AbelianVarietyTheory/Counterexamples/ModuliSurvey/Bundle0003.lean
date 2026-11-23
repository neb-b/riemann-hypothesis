module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.RealCase
open ReciprocityTheory.ChartRestriction.G.Out Classical
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

variable {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem exists_chart (χ : u.D.toPre.X) : ∃ j : PUnit → u.D.toPre.P.L.ι,
    ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U (j PUnit.unit) := by
  obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart u.D.toPre.P.isLB
    ((u.D.toPre.c χ).left (IsLocalRing.closedPoint u.V))
  refine ⟨fun _ => i, fun x _ => ?_⟩
  rw [Scheme.Hom.mem_preimage]
  exact ((IsLocalRing.specializes_closedPoint (R := u.V) x).map
    (u.D.toPre.c χ).left.continuous).mem_open (u.D.toPre.P.L.U i).isOpen hi

theorem psiNorm_unique (χ : u.D.toPre.X) {r r' : ℝ} (h : u.PsiNorm χ r) (h' : u.PsiNorm χ r') : r = r' := by
  obtain ⟨j, hj⟩ := exists_chart u χ
  exact (h j hj).symm.trans (h' j hj)

end GlobalTheory.ZH.RealCase
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.FinExtHomInjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.RelTests

section Ext
variable {V W : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]

end Ext

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem isNsmul_b {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, hl⟩ := H
  have key : ∀ (n : ℕ) (hn : n < k + 1), (gs ⟨n, hn⟩).b = g.b ^ n := by
    intro n
    induction n with
    | zero => intro hn; rw [pow_zero]; exact h0.1
    | succ n ih =>
      intro hn
      have e := (hs ⟨n, by omega⟩).1
      rw [pow_succ, ← ih (by omega)]
      exact e
  rw [← hl]
  exact key k (Nat.lt_succ_self k)

end Tors

end GlobalTheory.UU.RelTests
end
end

