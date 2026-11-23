module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFiniteStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.abelianVariety_lineBundle_sections_finite : (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M)) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0 := by
  first | exact @GlobalTheory.AbLaw.sections_finite_of_perf | exact GlobalTheory.AbLaw.sections_finite_of_perf | (intros; apply GlobalTheory.AbLaw.sections_finite_of_perf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeConclusionIff
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext exists_chart gm_cocycle gm_self)

namespace GlobalTheory.GtCubeCompare

section General

variable {X Y Z : Scheme.{0}}

variable {A B : LB X}

def gw (w : LB.Iso A B) (f : Y ⟶ X) (y : Y) (p : B.ι) (q : A.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y (B.U p ⊓ A.U q) (w.s (p, q))

theorem gm_linCombIso (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : K → B.ι) (q : K → A.ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ LB.wchart B φ p ⊓ LB.wchart A φ q) :
    gm r z (LB.wchart B φ p ⊓ LB.wchart A φ q) ((LB.linCombIso w φ ε).s (p, q)) =
      ∏ a, gw w (r ≫ φ a) z (p a) (q a) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ B.U (p a) ⊓ A.U (q a) :=
    ⟨LB.wchart_le B φ p a hz.1, LB.wchart_le A φ q a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z (B.U (p a) ⊓ A.U (q a)) hm _)

def PM (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb A φ ε)) (b : LB.Gen (LB.LinComb B φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → B.ι) (q : K → A.ι),
    r z ∈ LB.wchart B φ p → r z ∈ LB.wchart A φ q →
    gm r z (LB.wchart B φ p) (b.s p) =
      (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart A φ q) (a.s q)

theorem maps_iff_pm (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb A φ ε)) (b : LB.Gen (LB.LinComb B φ ε)) :
    LB.Gen.Maps (LB.linCombIso w φ ε) a b ↔ PM w φ ε a b := by
  constructor
  · intro H Z r z p q hp hq
    have hm : r z ∈ LB.wchart B φ p ⊓ LB.wchart A φ q := ⟨hp, hq⟩
    have := congrArg (gm r z (LB.wchart B φ p ⊓ LB.wchart A φ q)) (H (p, q))
    rw [← gm_linCombIso w φ ε p q r z hm]
    exact (gm_res r z _ hm _).symm.trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res r z _ hm _))))
  · rintro H ⟨p, q⟩
    apply unit_ext
    intro x hx
    have := H _ (𝟙 Y) x p q hx.1 hx.2
    rw [← gm_linCombIso w φ ε p q (𝟙 Y) x hx] at this
    exact (gm_res _ x _ hx _).trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

variable {w : LB.Iso A B} {K K' : Type} [Fintype K] [Fintype K']

end General

section Group

variable {S S' : Scheme.{0}}

end Group

end GlobalTheory.GtCubeCompare

end
end

