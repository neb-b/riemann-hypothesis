module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePointsOfIsOpenImmersion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

namespace GlobalTheory.AbelianSubgroupFinite

theorem finite_points_of_isOpenImmersion {k : Type} [Field k] [IsAlgClosed k]
    (N : Over (Sp k)) [GrpObj N] [LocallyOfFiniteType N.hom] [NoetherianSpace N.left]
    {N₀ : Over (Sp k)} (ν : N₀ ⟶ N) [IsOpenImmersion ν.left] (e : 𝟙_ (Over (Sp k)) ⟶ N₀)
    (he : e ≫ ν = η[N]) [Finite (𝟙_ (Over (Sp k)) ⟶ N₀)] : Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  let pt : Sp k := IsLocalRing.closedPoint k
  let F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left := fun x => x.left pt
  let φ : (𝟙_ (Over (Sp k)) ⟶ N) → (N₀ ⟶ N) := fun x => ν ≫ (GrpObj.mulRight x).hom
  have hφ : ∀ x, IsOpenImmersion (φ x).left := fun x => by
    have : IsIso (GrpObj.mulRight x).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))
    simp only [φ, Over.comp_left]
    infer_instance
  have hx : ∀ x, e ≫ φ x = x := fun x => by
    simp only [φ]
    rw [← Category.assoc, he]
    simpa [comp_lift_assoc] using lift_comp_one_left (𝟙 _) x
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (Set.range F)).elim_finite_subcover
    (fun x => Set.range (φ x).left) (fun x => (φ x).left.isOpenEmbedding.isOpen_range) (by
      rintro _ ⟨x, rfl⟩
      refine Set.mem_iUnion.2 ⟨x, e.left pt, ?_⟩
      simp only [F]
      conv_rhs => rw [← hx x]
      simp only [Over.comp_left, Scheme.Hom.comp_apply])
  refine Finite.of_surjective
    (fun p : t × (𝟙_ (Over (Sp k)) ⟶ N₀) => p.2 ≫ φ p.1.1) fun y => ?_
  obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.1 (ht ⟨y, rfl⟩)
  have hsub : Set.range y.left ⊆ Set.range (φ x).left := by
    rintro _ ⟨a, rfl⟩
    have : Subsingleton (Sp k) := inferInstance
    rw [show a = pt from this.elim _ _]
    exact hy
  refine ⟨⟨⟨x, hxt⟩, Over.homMk (IsOpenImmersion.lift (φ x).left y.left hsub) ?_⟩, ?_⟩
  · rw [← (φ x).w, IsOpenImmersion.lift_fac_assoc, y.w]
  · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac (φ x).left y.left hsub)

theorem finite_of_torsionFree : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) := by
  intro k _ _ B _ n hB hn hnk C Z hZ hC htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have hfin₀ : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine _root_.GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion k N₀ hA n hn.two_le hnk fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  have := finite_points_of_isOpenImmersion N ν₀ η[N₀] (IsMonHom.one_hom ν₀)
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  obtain ⟨l, hl⟩ := exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)
  refine ⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩
  rw [← ν.w, ← Category.assoc, hl, x.w]

end GlobalTheory.AbelianSubgroupFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralLatticeStructureUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_sabMap_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} (T : CDVR) {x x' : Sp T.Fr ⟶ Xo.X} (hx : x' = x) (G G₂ : SAB H (Sp T.V))
    (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t₂ Xo.univ.t x') (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) :
    ∃ (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), k.φ ≫ n₁.φ = m₁.φ ∧ m₂.φ ≫ n.φ = k.φ ≫ n₂.φ := by
  subst hx
  exact _root_.GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr x' G G₂ t t₂ m₁ m₂ n₁ n₂

theorem intLatU_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntLatU Xo c := by
  intro E _ _ _ H Dw l Xo c T io y y'
  let := io.toAlgebra
  intro hx
  obtain ⟨G, t, m₁, m₂, ⟨ub, hub⟩, θ, hθ⟩ := y.2.2
  obtain ⟨G₂, t₂, n₁, n₂, ⟨ub₂, hub₂⟩, θ₂, hθ₂⟩ := y'.2.2
  obtain ⟨k, n, hk, hn⟩ := exists_sabMap_of_eq T hx G G₂ t t₂ m₁ m₂ n₁ n₂
  refine ⟨GlobalTheory.T.integral_frames_differ_by_unit' E H Dw l Xo c T io y.1 y'.1 G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn ub ub₂ hub hub₂, ?_⟩
  intro a pm h1 h2 h3
  refine GlobalTheory.T.valV_eq_one_integral_generators E H Dw l Xo c T io y.1 y'.1 G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn θ θ₂ hθ hθ₂ a
    ⟨pm, h1, ?_, h3⟩
  have hid : spMap (RingHom.id T.Fr) = 𝟙 (Sp T.Fr) := Spec.map_id _
  rw [h2, hid]
  exact (Category.comp_id _).symm

end GlobalTheory.Frames
end

