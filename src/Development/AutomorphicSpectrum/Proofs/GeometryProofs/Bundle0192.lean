module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0187
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0188

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieModelsAgree
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtDvr

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem spMap_genMap_fromSpecStalk (p : Cpt ξ) : spMap (genMap ξ p) ≫ X.fromSpecStalk p.1 = ξ := by
  have h : spMap (genMap ξ p) = Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes p.2) := by
    rw [← Spec.map_comp]
    rfl
  have h₁ : Spec.map (X.presheaf.stalkSpecializes p.2) ≫ X.fromSpecStalk p.1 = X.fromSpecStalk (genPt ξ) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk p.2
  rw [h, Category.assoc]
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) h₁).trans
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (k : R →+* R') :
    (dualMap k).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp k := by
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spec_dualMap_comp {R R' : Type} [CommRing R] [CommRing R'] (k : R →+* R') :
    Spec.map (CommRingCat.ofHom (dualMap k)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫ Spec.map (CommRingCat.ofHom k) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_comp_algebraMap]

theorem isFractionRing_stalk (h : IsCptGen ξ) (p : Cpt ξ) :
    letI := (genMap ξ p).toAlgebra
    IsFractionRing (X.presheaf.stalk p.1) Ω := by
  letI := (genMap ξ p).toAlgebra
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (h.inj p)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩, e⟩ := RegAtRing.exists_div h p z
  exact ⟨a, b, e⟩

section Move

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {k : R →+* Ω} {G G' : Over X} [GrpObj G] [GrpObj G']
  {GΩ : Over (Sp Ω)} [GrpObj GΩ] {φ : GΩ.left ⟶ G.left} {φ' : GΩ.left ⟶ G'.left}
  {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} {ψ' : G₀.left ⟶ G'.left} {κ : GΩ.left ⟶ G₀.left}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem isHTFormOver_move (hψ : IsGrpPullback G₀ G x ψ) (hψ' : IsGrpPullback G₀ G' x ψ')
    (hκ : κ ≫ G₀.hom = GΩ.hom ≫ spMap k) (e₁ : κ ≫ ψ = φ) (e₂ : κ ≫ ψ' = φ')
    (M : LieModel G ξ E) (M' : LieModel G' ξ E)
    (tie : ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left)
    (N : ℕ) (w : Module.Dual Ω E) (h : M.IsHTFormOver N x k w) : M'.IsHTFormOver N x k w := by
  obtain ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, ht, hj, hHT, hw⟩ := h
  obtain ⟨i₀, hi₀, ht₀⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.torsionAlong_iff_pullback_torsion R T Γ X x G G₀ ψ N hψ).1 i ht
  have ht' := (_root_.GlobalTheory.CompanionTheory.Ar.torsionAlong_iff_pullback_torsion R T Γ X x G' G₀ ψ' N hψ').2 i₀ ht₀
  obtain ⟨M₀₀, hM₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main R X x G G₀ ψ L hψ).1 M₀
  obtain ⟨M₀', hM₀'⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main R X x G' G₀ ψ' L hψ').2 M₀₀
  refine ⟨hd, T, _, Γ, i₀ ≫ ψ', L, _, _, M₀', j, χ, w₀, ht', ?_, ?_, hw⟩
  · intro e
    obtain ⟨v, hv, hv'⟩ := tie (j e)
    have key : Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀₀.pt e).left = v.left ≫ κ := by
      refine hψ.1.hom_ext ?_ ?_
      · rw [Category.assoc, hM₀, ← hj e, Category.assoc, e₁, hv]
      · have a := Over.w (M₀₀.pt e)
        have b := Over.w v
        dsimp at a b
        rw [Category.assoc, Category.assoc, a, hκ, ← Category.assoc (Over.Hom.left v), b]
        simp only [Category.comp_id]
        exact spec_dualMap_comp k
    rw [← hM₀' e, ← Category.assoc, key, Category.assoc, e₂, hv']
  · obtain ⟨s, hs, hsv⟩ := hHT
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, h₁, h₂, h₃⟩ := hsv e
    refine ⟨v, h₁, ?_, h₃⟩
    have key : v ≫ i₀ = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
        (M₀₀.pt e).left := by
      refine hψ.1.hom_ext ?_ ?_
      · rw [Category.assoc, hi₀, h₂, Category.assoc, hM₀]
      · have a := Over.w (M₀₀.pt e)
        have b := ht₀.isOver
        dsimp at a b
        rw [Category.assoc, Category.assoc, a, b, ← Category.assoc v, h₁]
        simp only [Category.comp_id]
        rw [spec_dualMap_comp, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [← Category.assoc, key, Category.assoc, hM₀']

theorem isHTFormOver_of_dvr [IsDomain R] [IsDiscreteValuationRing R]
    (hk : letI := k.toAlgebra; IsFractionRing R Ω) (hx : spMap k ≫ x = ξ) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback GΩ G ξ φ) (hφ' : IsGrpPullback GΩ G' ξ φ')
    (M : LieModel G ξ E) (M' : LieModel G' ξ E)
    (tie : ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left)
    (N : ℕ) (w : Module.Dual Ω E) (h : M.IsHTFormOver N x k w) : M'.IsHTFormOver N x k w := by
  subst hx
  letI := k.toAlgebra
  haveI : IsFractionRing R Ω := hk
  obtain ⟨G₀, _, ψ, ψ', κ, hψ, hψ', hκ, e₁, e₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.semiAbelian_commonModel R Ω X X x x G G' GΩ φ φ' hG hG' hφ hφ'
  exact isHTFormOver_move hψ hψ' hκ.1.w e₁ e₂ M M' tie N w h

theorem isHTFormAt_move (hξ : IsCptGen ξ) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback GΩ G ξ φ) (hφ' : IsGrpPullback GΩ G' ξ φ')
    (M : LieModel G ξ E) (M' : LieModel G' ξ E)
    (tie : ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left)
    (N : ℕ) (p : Cpt ξ) [IsDomain (X.presheaf.stalk p.1)] [IsDiscreteValuationRing (X.presheaf.stalk p.1)]
    (w : Module.Dual Ω E) (h : M.IsHTFormAt N p w) : M'.IsHTFormAt N p w := by
  exact isHTFormOver_of_dvr (isFractionRing_stalk hξ p) (spMap_genMap_fromSpecStalk p) hG hG' hφ hφ' M M' tie N w h

end Move

theorem main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (M' : LieModel G' ξ V), (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left) → ∀ (N : ℕ) (p : Cpt ξ), (∃ _ : IsDomain (X.presheaf.stalk p.1), IsDiscreteValuationRing (X.presheaf.stalk p.1)) → M.htLat N p = M'.htLat N p := by
  intro X Ω _ ξ hξ G G' _ _ GΩ _ φ φ' hG hG' hφ hφ' V _ _ M M' tie N p hp
  obtain ⟨_, _⟩ := hp
  have e : {w | M.IsHTFormAt N p w} = {w | M'.IsHTFormAt N p w} := Set.ext fun w =>
    ⟨isHTFormAt_move hξ hG hG' hφ hφ' M M' tie N p w,
      isHTFormAt_move hξ hG' hG hφ' hφ M' M (fun e => by
        obtain ⟨v, a, b⟩ := tie e
        exact ⟨v, b, a⟩) N p w⟩
  simp only [LieModel.htLat]
  rw [e]

end GlobalTheory.CompanionTheory.Ar.HtDvr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTwoTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_two_torsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenTors.exists_finite_ext_torusExtension_two_torsion | exact GlobalTheory.CompanionTheory.Ar.GenTors.exists_finite_ext_torusExtension_two_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.GenTors.exists_finite_ext_torusExtension_two_torsion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionCardBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_torsion_card_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RankBound.rank_bound_of_points_of_order_two | exact GlobalTheory.CompanionTheory.Ar.RankBound.rank_bound_of_points_of_order_two | (intros; apply GlobalTheory.CompanionTheory.Ar.RankBound.rank_bound_of_points_of_order_two <;> assumption)
end

