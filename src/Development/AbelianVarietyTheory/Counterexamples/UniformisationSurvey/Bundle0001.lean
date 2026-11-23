module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.BoxCubicalUnconditional
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerExamples

variable {S : Scheme.{0}}

theorem hom_ext {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) {T : Over S}
    {x y : T ⟶ G'} (h : ∀ i, x ≫ p.pr i = y ≫ p.pr i) : x = y :=
  p.lim.hom_ext fun ⟨i⟩ => h i

theorem comm_of_pow {G' G : Over S} [GrpObj G'] [GrpObj G] [IsCommMonObj G] {j : ℕ}
    (p : IsPowGrp G' G j) : IsCommMonObj G' where
  mul_comm := hom_ext p fun i => by
    have := p.hom i
    rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]

theorem pow_unique {G₁ G₂ G : Over S} [GrpObj G₁] [GrpObj G₂] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G₁ G j) (q : IsPowGrp G₂ G j) :
    ∃ e : G₁ ≅ G₂, IsMonHom e.hom ∧ ∀ i, e.hom ≫ q.pr i = p.pr i := by
  have he : ∀ i, (p.lim.conePointUniqueUpToIso q.lim).hom ≫ q.pr i = p.pr i := fun i =>
    p.lim.conePointUniqueUpToIso_hom_comp q.lim ⟨i⟩
  refine ⟨p.lim.conePointUniqueUpToIso q.lim, ⟨hom_ext q fun i => ?_, hom_ext q fun i => ?_⟩, he⟩
  · have := p.hom i; have := q.hom i
    erw [Category.assoc, he i, IsMonHom.one_hom, IsMonHom.one_hom]
  · have := p.hom i; have := q.hom i
    erw [Category.assoc, he i, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom (q.pr i),
      ← Category.assoc, tensorHom_comp_tensorHom, he i]

end GlobalTheory.PowerExamples
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.EquivIffOfIsEmpty
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPairTest

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem ext_val {T : Over (Spec (CommRingCat.of R))} {g g' : GtPt D T} (hb : g.b = g'.b)
    (hs : ∀ χ y J, Geo.Tor.Good D.P.L y J → Geo.Tor.val (g.s χ) (𝟙 _) y J = Geo.Tor.val (g'.s χ) (𝟙 _) y J) :
    g = g' := by
  obtain ⟨b, s, h, _, _⟩ := g
  obtain ⟨b', s', h', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ =>
    GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ) (Geo.Tor.corr_of_val D.P.isLB (hs χ))
  rfl

theorem isPull_unique {T T' : Over (Spec (CommRingCat.of R))} {h : T'.left ⟶ T.left} {g : GtPt D T}
    {a a' : GtPt D T'} (H : GtPt.IsPull h g a) (H' : GtPt.IsPull h g a') : a = a' :=
  ext_val (Over.OverMorphism.ext (H.1.trans H'.1.symm)) fun χ _ _ hJ =>
    (Geo.Tor.val_corr hJ (H.2 χ) (𝟙 _)).trans (Geo.Tor.val_corr hJ (H'.2 χ) (𝟙 _)).symm

section Empty

variable {T : Over (Spec (CommRingCat.of R))} [IsEmpty T.left]

end Empty

variable {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) [IsEmpty T.left]

end GlobalTheory.TorsionPairTest
end
end

