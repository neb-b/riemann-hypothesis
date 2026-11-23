module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionBoxProductDivGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exists_section_boxProduct_div_generator : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ : K₁ → (Y ⟶ X)) (ψ : K₂ → (Y ⟶ X)) (e : ℤ) (th : L.Sec) (w : LB.Gen (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim φ ψ) (Sum.elim (fun _ => 1) (fun _ => -e)))), w.IsGen → ∃ s : LB.Sec (LB.LinComb L ψ (fun _ => e)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, Good L z J → ∏ k, gs (r ≫ φ k) z (L.U (J (r ≫ φ k))) (th.f (J (r ≫ φ k))) = (val w r z J).val * sval s r z J := by
  first | exact @GlobalTheory.KeyQuot.exists_sec_quot | exact GlobalTheory.KeyQuot.exists_sec_quot | (intros; apply GlobalTheory.KeyQuot.exists_sec_quot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LbIsoDescendsToSubfieldContainingFinset
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

namespace GlobalTheory

theorem lbIso_descends_to_subfield_containing_finset :
    ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X₀ : Over (Sp k)) (X : Over (Sp K)) (φ : X.left ⟶ X₀.left) (M N : LB X₀.left), IsPullback φ X.hom X₀.hom (spMap σ) → QuasiCompact X₀.hom → QuasiSeparated X₀.hom → M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ : Over (Sp k₁)) (χ : X₁.left ⟶ X₀.left), IsPullback χ X₁.hom X₀.hom (spMap α) → LBIso (M.pull χ) (N.pull χ) := by
  intro k K _ _ σ X₀ X φ M N hφ hqc hqs hM hN H
  letI := σ.toAlgebra
  have same : ∀ {Y Y' : Scheme.{0}} (a : Y ⟶ X₀.left) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀.left), a' = j ≫ a →
      LBIso (M.pull a) (N.pull a) → LBIso (M.pull a') (N.pull a') := fun a j a' e h =>
    LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h
  have hφ' : IsPullback φ X.hom X₀.hom (spMap (algebraMap k K)) := hφ
  have H₁ := same φ hφ'.isoPullback.inv (pullback.fst X₀.hom (spMap (algebraMap k K)))
    (IsPullback.isoPullback_inv_fst hφ').symm H
  obtain ⟨R, hR₀, ⟨s, rfl⟩, hiso⟩ := exists_fg_lbIso (C := K) (R₀ := ⊥) X₀.hom Subalgebra.fg_bot
    (M.pull (pullback.fst _ _)) (N.pull (pullback.fst _ _)) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.chartPull
      (chartPullOut M _ _ _ _ fun _ => (baseChangeMap_fst X₀.hom _).symm)
      (chartPullOut N _ _ _ _ fun _ => (baseChangeMap_fst X₀.hom _).symm) H₁)
  have H₂ := LBIso.chartPull (chartPullIn M _ _ _) (chartPullIn N _ _ _) hiso
  refine ⟨s, ?_⟩
  intro k₁ _ α β hαβ hs X₁ χ hχ
  have hR : ∀ x : Algebra.adjoin k (s : Set K), ∃ y, β y = x := by
    rintro ⟨x, hx⟩
    change x ∈ β.range
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact ⟨α r, RingHom.congr_fun hαβ r⟩
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  choose ρ₀ hρ₀ using hR
  let ρ : Algebra.adjoin k (s : Set K) →+* k₁ :=
    { toFun := ρ₀
      map_one' := β.injective (by simp [hρ₀])
      map_mul' := fun x y ↦ β.injective (by simp [hρ₀])
      map_zero' := β.injective (by simp [hρ₀])
      map_add' := fun x y ↦ β.injective (by simp [hρ₀]) }
  have hρ₂ : ρ.comp (algebraMap k _) = α := RingHom.ext fun r ↦ β.injective
    ((hρ₀ _).trans (RingHom.congr_fun hαβ r).symm)
  let j : X₁.left ⟶ pullback X₀.hom (spMap (algebraMap k (Algebra.adjoin k (s : Set K)))) :=
    pullback.lift χ (X₁.hom ≫ spMap ρ) (by rw [Category.assoc, spMap_comp_ring, hρ₂, hχ.w])
  have hj₁ : j ≫ pullback.fst _ _ = χ := pullback.lift_fst _ _ _
  refine same _ j χ ?_ H₂
  rw [baseChangeMap_fst, hj₁]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem exists_finset_lbIso_adjoin {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    {B : Scheme.{0}} (pB : B ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] (M N : LB B)
    (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (pullback.fst pB (spMap (algebraMap k A))))
      (N.pull (pullback.fst pB (spMap (algebraMap k A))))) :
    ∃ s : Finset A,
      LBIso (M.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))))
        (N.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A)))))) := by
  classical
  obtain ⟨t, f, h⟩ := exists_lbIso_of_isLimit (Spread.bcDiagram pB A)
    (X := pullback pB (spMap (algebraMap k A)))
    (fun s => Spread.bcMap pB (Algebra.adjoin k (s.unop : Set A)).val)
    (fun f => (Spread.bcCone pB A).w f) (Spread.isLimitBcCone pB A) (i := .op ∅)
    (M.pull (pullback.fst _ _)) (N.pull (pullback.fst _ _)) (LB.isLB_pull hM _) (LB.isLB_pull hN _)
    (LBIso.chartPull
      (chartPullOut M _ _ _ _ fun _ => (Spread.bcMap_fst pB _).symm)
      (chartPullOut N _ _ _ _ fun _ => (Spread.bcMap_fst pB _).symm) H)
  have H₂ := LBIso.chartPull (chartPullIn M _ _ _) (chartPullIn N _ _ _) h
  refine ⟨t.unop, ?_⟩
  exact LBIso.chartPull (chartPullSame M _ _ _ (𝟙 _) fun _ =>
      ((Category.id_comp _).trans (Spread.bcMap_fst pB _)).symm)
    (chartPullSame N _ _ _ (𝟙 _) fun _ =>
      ((Category.id_comp _).trans (Spread.bcMap_fst pB _)).symm) H₂

theorem lbIso_descends_to_subring_containing_finset :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (M N : LB X₀), IsPullback π f f₀ (spMap R₀.subtype) → M.IsLB → N.IsLB → LBIso (M.pull π) (N.pull π) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → LBIso (M.pull π₁) (N.pull π₁) := by
  intro S _ R₀ X X₀ f f₀ π _ _ M N hp hM hN H
  have same : ∀ {Y Y' : Scheme.{0}} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀), a' = j ≫ a →
      LBIso (M.pull a) (N.pull a) → LBIso (M.pull a') (N.pull a') := fun a j a' e h =>
    LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h
  have hp' : IsPullback π f f₀ (spMap (algebraMap R₀ S)) := hp
  have H₁ := same π hp'.isoPullback.inv (pullback.fst f₀ (spMap (algebraMap R₀ S)))
    (IsPullback.isoPullback_inv_fst hp').symm H
  obtain ⟨s, H₂⟩ := exists_finset_lbIso_adjoin f₀ M N hM hN H₁
  refine ⟨s, fun R₁ h hs X₁ f₁ π₁ hp₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let g : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hg : spMap g ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let m : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S)))) :=
    pullback.lift π₁ (f₁ ≫ spMap g) (by rw [Category.assoc, hg, hp₁.w])
  exact same _ m π₁ (pullback.lift_fst _ _ _).symm H₂

end GlobalTheory
end

