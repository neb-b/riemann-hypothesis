module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CoordinateMapFiniteType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.CoordinateMapFiniteType

theorem finiteType_of_range {A Ω R : Type} [CommRing A] [Field Ω] [CommRing R] (φ : A →+* Ω)
    (hφ : Function.Injective φ) (s : Set Ω) (hs : s.Finite)
    (h : ∀ a : Ω, a ∈ Algebra.adjoin ℤ s ↔ a ∈ φ.range) (ψ : R →+* A) : ψ.FiniteType := by
  have h1 : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have hr : φ.toIntAlgHom.range = Algebra.adjoin ℤ s := by
    ext a
    rw [h a]
    rfl
  have h2 : Algebra.FiniteType ℤ A :=
    Algebra.FiniteType.equiv h1
      ((AlgEquiv.ofInjective φ.toIntAlgHom hφ).trans (Subalgebra.equivOfEq _ _ hr)).symm
  have h3 : (ψ.comp (algebraMap ℤ R)).FiniteType := by
    rw [Subsingleton.elim (ψ.comp (algebraMap ℤ R)) (algebraMap ℤ A)]
    exact RingHom.finiteType_algebraMap.2 h2
  exact RingHom.FiniteType.of_comp_finiteType h3

theorem main {X Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ Y) {Ω : Type} [Field Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hq : ∀ q : X, genPt ξ ⤳ q) (hT : CoordTie ℤ ξ x) :
    LocallyOfFiniteType f ∧ QuasiCompact f := by
  choose U h hU hUq _ hinj hran using fun c : {c // x c ≠ 0} => TieFrame.exists_chart hT c.2
  have hcov : ∀ q : X, ∃ c, q ∈ U c := fun q => by
    obtain ⟨c, hc⟩ := hT.cover ⟨q, hq q⟩
    exact ⟨⟨c, hc.1⟩, (hUq ⟨c, hc.1⟩ ⟨q, hq q⟩).2 hc⟩
  constructor
  · have htop : ⨆ c, ((⟨U c, hU c⟩ : X.affineOpens) : X.Opens) = ⊤ := by
      refine top_le_iff.1 fun q _ => ?_
      obtain ⟨c, hc⟩ := hcov q
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, hc⟩
    refine (HasRingHomProperty.iff_of_iSup_eq_top (P := @LocallyOfFiniteType)
      (fun c => (⟨U c, hU c⟩ : X.affineOpens)) htop).2 fun c => ?_
    exact finiteType_of_range _ (hinj c) _ (Set.finite_range _) (hran c) _
  · have : CompactSpace X := by
      refine ⟨?_⟩
      have e : (Set.univ : Set X) = ⋃ c, (U c : Set X) :=
        (Set.eq_univ_of_forall fun q => Set.mem_iUnion.2 (hcov q)).symm
      rw [e]
      exact isCompact_iUnion fun c => (hU c).isCompact
    exact (quasiCompact_iff_compactSpace f).2 this

end PositivityTheory.Xgn.CoordinateMapFiniteType

theorem PositivityTheory.Xgn.coordinate_map_finite_type : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) := by
  intro X Ω _ K _ J _ y ξ hq hT
  exact PositivityTheory.Xgn.CoordinateMapFiniteType.main (toZ X) hq hT
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsIntegralClosedSubscheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.IntegralClosedSubscheme

theorem reduced_sub {S : Scheme.{0}} (Z : TopologicalSpace.Closeds S) :
    AlgebraicGeometry.IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have hU : ∀ U : S.affineOpens, IsReduced
      (Spec (CommRingCat.of (Γ(S, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U))) := by
    intro U
    have h : ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).IsRadical := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    haveI : _root_.IsReduced (Γ(S, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp h
    infer_instance
  haveI : ∀ i, IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X i) := hU
  exact IsReduced.of_openCover _ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover

theorem le_ker {S Y : Scheme.{0}} (Z : TopologicalSpace.Closeds S) (g : Y ⟶ S) [QuasiCompact g]
    [AlgebraicGeometry.IsReduced Y] (h : Set.range g ⊆ Z) :
    Scheme.IdealSheafData.vanishingIdeal Z ≤ g.ker := by
  have h1 : g.ker.support ≤ Z := by
    intro x hx
    have hx' : x ∈ (g.ker.support : Set S) := hx
    rw [Scheme.Hom.support_ker] at hx'
    exact closure_minimal h Z.isClosed hx'
  refine (Scheme.IdealSheafData.vanishingIdeal_antimono h1).trans ?_
  rw [Scheme.IdealSheafData.vanishingIdeal_support]
  intro U s hs
  rw [Scheme.IdealSheafData.radical_ideal] at hs
  rw [Scheme.Hom.ker_apply] at hs ⊢
  obtain ⟨n, hn⟩ := hs
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsNilpotent.eq_zero ⟨n, hn⟩

end PositivityTheory.Xgn.IntegralClosedSubscheme

theorem PositivityTheory.Xgn.exists_integral_closed_subscheme_of_irreducible : ∀ (S : Scheme.{0}) (F : Set S), IsClosed F → IsIrreducible F →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ S), IsClosedImmersion i ∧ Set.range i = F ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S), x (IsLocalRing.closedPoint k) ∈ F → ∃ x' : Sp k ⟶ Z, x' ≫ i = x := by
  intro S F hF hirr
  let Zc : TopologicalSpace.Closeds S := ⟨F, hF⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Zc
  have hrange : Set.range I.subschemeι = F := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  haveI : IsReduced I.subscheme := IntegralClosedSubscheme.reduced_sub Zc
  haveI : IrreducibleSpace I.subscheme := by
    haveI : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [← isIrreducible_iff_irreducibleSpace, hrange]
      exact hirr
    exact I.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this
  haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  refine ⟨I.subscheme, inferInstance, I.subschemeι, inferInstance, hrange, ?_⟩
  intro k _ x hx
  have hsub : Set.range x ⊆ Zc := by
    rintro _ ⟨y, rfl⟩
    have hy : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hy]
    exact hx
  refine ⟨IsClosedImmersion.lift I.subschemeι x ?_, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact IntegralClosedSubscheme.le_ker Zc x hsub
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsSplitTorusExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.SplitTorusExtension

theorem one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    change ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h₁ : (e * e).left = e.left := by
    rw [h.2 T 1 1 e e rfl rfl, _root_.mul_one]
    rfl
  have h₂ : e * e = e := Over.OverMorphism.ext h₁
  have h₃ : e = 1 := by simpa using h₂
  rw [← h₃]
  rfl

theorem eq_one {S S' : Scheme.{0}} {G' H' : Over S'} [GrpObj G'] [GrpObj H'] {G H : Over S} [GrpObj G] [GrpObj H]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ)
    (hψ : IsGrpPullback H' H f ψ) (i : G' ⟶ H') [IsMonHom i] [Mono i] (u : G ⟶ H)
    (hu : i.left ≫ ψ = φ ≫ u.left) (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ G) (ht : t ≫ u = 1) : t = 1 := by
  have hw : t.left ≫ G.hom = T.hom ≫ f := Over.w t
  let s : T.left ⟶ G'.left := hφ.1.lift t.left T.hom hw
  have hs : s ≫ φ = t.left := hφ.1.lift_fst _ _ _
  let s' : T ⟶ G' := Over.homMk s (hφ.1.lift_snd _ _ _)
  have h1 : s' ≫ i = 1 := by
    apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · rw [← one_left hψ T, Over.comp_left, Category.assoc, hu, ← Category.assoc]
      change (s ≫ φ) ≫ u.left = _
      rw [hs, ← Over.comp_left, ht]
    · rw [Over.w, Over.w]
  have h2 : s' = 1 := by
    have h3 : (1 : T ⟶ G') ≫ i = 1 := by simp [Hom.one_def]
    rw [← h3] at h1
    exact (cancel_mono i).mp h1
  apply Over.OverMorphism.ext
  rw [one_left hφ T, ← h2]
  exact hs.symm

end PositivityTheory.Xgn.SplitTorusExtension

theorem PositivityTheory.Xgn.exists_split_torus_extension : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 := by
  intro hext Z' _ _ hnorm G _ hG L' _ j hj τ
  letI := τ.addCommGroup
  haveI := τ.free
  haveI := τ.finite
  haveI := τ.i_hom
  haveI : Mono τ.i := τ.isKernel.mono_fst_of_mono
  have hT : IsSemiAbelian (splitTorus Z' τ.X) :=
    ((GlobalTheory.splitTorus_properties Z').1 τ.X).2.2.2.2.2.2.2.2.1
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange Z' (Sp L') j τ.X
  haveI := he
  have hφ : IsGrpPullback (splitTorus (Sp L') τ.X) (splitTorus Z' τ.X) j
      (e.hom.left ≫ pullback.fst (splitTorus Z' τ.X).hom j) := by
    have h0 := (isGrpPullback_of_iso e).comp (isGrpPullback_pullback (splitTorus Z' τ.X) j)
    rwa [Category.id_comp] at h0
  have hψ := isGrpPullback_pullback G j
  obtain ⟨F, ⟨hF, hu⟩, -⟩ :=
    GlobalTheory.Published.SemiAbelianHomExtension.generic_of_isGrpPullback hext hnorm hj hT hG hφ hψ τ.i
  refine ⟨F, hF, fun A _ g t ht => ?_⟩
  haveI := hF
  exact SplitTorusExtension.eq_one hφ hψ τ.i F hu (Over.mk (spMap g)) t ht
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FiniteSurjectiveImageOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem PositivityTheory.Xgn.finite_surjective_image_open : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V := by
  intro Z Z' _ _ π hπ _ V hV
  haveI : IsFinite π := hπ
  have hCc : IsClosed ((V : Set Z')ᶜ) := V.isOpen.isClosed_compl
  refine ⟨⟨(π '' (V : Set Z')ᶜ)ᶜ, (π.isClosedMap _ hCc).isOpen_compl⟩, ⟨genericPoint Z, ?_⟩, ?_⟩
  · show genericPoint Z ∉ π '' (V : Set Z')ᶜ
    rintro ⟨x, hxC, hx⟩
    have h1 : genericPoint Z' ⤳ x := (genericPoint_spec Z').specializes (Set.mem_univ x)
    have h2 : π (genericPoint Z') = genericPoint Z := by
      have a : π (genericPoint Z') ⤳ π x := h1.map π.continuous
      rw [hx] at a
      exact (a.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ _))).eq
    haveI hd := (π.isDiscrete_preimage_singleton (genericPoint Z)).to_subtype
    have m2 : genericPoint Z' ∈ (π ⁻¹' {genericPoint Z} : Set Z') := h2
    have mx : x ∈ (π ⁻¹' {genericPoint Z} : Set Z') := hx
    have h3 : (⟨genericPoint Z', m2⟩ : (π ⁻¹' {genericPoint Z} : Set Z')) ⤳ ⟨x, mx⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp h1
    have h4 : genericPoint Z' = x := congrArg Subtype.val (specializes_iff_eq.mp h3)
    apply hxC
    rw [← h4]
    exact ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FiniteSurjectivePointLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.FiniteSurjectivePointLift

theorem exists_ringHom (L A : Type) [Field L] [CommRing A] [Nontrivial A] (φ : L →+* A) (hφ : φ.Finite) :
    ∃ ψ : A →+* AlgebraicClosure L, ψ.comp φ = algebraMap L (AlgebraicClosure L) := by
  letI := φ.toAlgebra
  haveI : Module.Finite L A := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  haveI : Module.Finite L (A ⧸ m) := inferInstance
  haveI : Algebra.IsAlgebraic L (A ⧸ m) := inferInstance
  let j : (A ⧸ m) →ₐ[L] AlgebraicClosure L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(j.comp (Ideal.Quotient.mkₐ L m)).toRingHom, ?_⟩
  ext x
  exact (j.comp (Ideal.Quotient.mkₐ L m)).commutes x

theorem exists_point (L : Type) [Field L] (P : Scheme.{0}) [Nonempty P] (g : P ⟶ Spec (CommRingCat.of L))
    [IsFinite g] : ∃ x : Spec (CommRingCat.of (AlgebraicClosure L)) ⟶ P,
      x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) := by
  haveI hA : IsAffine P := isAffine_of_isAffineHom g
  have hfin : (g.appTop).hom.Finite := g.finite_app ⊤ (isAffineOpen_top _)
  let φ : L →+* Γ(P, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ g.appTop).hom
  have hφ : φ.Finite := by
    refine RingHom.Finite.comp hfin ?_
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).2
  haveI : Nonempty (⊤ : P.Opens) := ⟨⟨Classical.arbitrary P, trivial⟩⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom L Γ(P, ⊤) φ hφ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ P.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv]
  simp only [← Spec.map_comp]
  congr 1
  ext x
  exact congrArg (fun f => f x) hψ

end PositivityTheory.Xgn.FiniteSurjectivePointLift

theorem PositivityTheory.Xgn.finite_surjective_point_lift : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ := by
  intro Z' Z π hfin hsurj L _ zZ
  haveI : Surjective (pullback.snd π zZ) := inferInstance
  obtain ⟨p, -⟩ := (pullback.snd π zZ).surjective (IsLocalRing.closedPoint L)
  haveI : Nonempty ↥(pullback π zZ) := ⟨p⟩
  obtain ⟨x, hx⟩ := FiniteSurjectivePointLift.exists_point L (pullback π zZ) (pullback.snd π zZ)
  refine ⟨x ≫ pullback.fst π zZ, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HermitianNormSquareFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.HermitianNormSquare

theorem core_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) {n : ℕ}
    (e : Fin n → V) (w : Fin n → ℂ) :
    c.inner (∑ a, w a • e a) (∑ a, w a • e a)
      = star w ⬝ᵥ ((Matrix.of fun a b => c.inner (e a) (e b)) *ᵥ w) := by
  letI : PreInnerProductSpace.Core ℂ V := c.toCore
  have hl : ∀ (s : Finset (Fin n)) (f : Fin n → V) (y : V),
      c.inner (∑ a ∈ s, f a) y = ∑ a ∈ s, c.inner (f a) y := by
    intro s f y
    induction s using Finset.induction_on with
    | empty => simpa using InnerProductSpace.Core.inner_zero_left (𝕜 := ℂ) y
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      exact InnerProductSpace.Core.inner_add_left (𝕜 := ℂ) _ _ _
  have hr : ∀ (s : Finset (Fin n)) (f : Fin n → V) (x : V),
      c.inner x (∑ a ∈ s, f a) = ∑ a ∈ s, c.inner x (f a) := by
    intro s f x
    induction s using Finset.induction_on with
    | empty => simpa using InnerProductSpace.Core.inner_zero_right (𝕜 := ℂ) x
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      exact InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) _ _ _
  rw [hl]
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ), hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
  simp only [RCLike.star_def, Complex.star_def]
  ring

end PositivityTheory.Xgn.HermitianNormSquare

theorem PositivityTheory.Xgn.hermitian_norm_square_formula : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re := by
  intro L _ _ B σ n ε Γ hΓ w
  have hx : (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a :
      GroundTheory.Heights₂.Heights.Fibre σ B.carrier)
      = ∑ a, w a • ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul']
    congr 1
    change w a = w a * 1
    rw [_root_.mul_one]
  have hM : Γ = Matrix.of fun a b => (B.metric.form σ).inner
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b) := by
    ext a b
    exact hΓ a b
  unfold sqAt
  rw [hx, hM, ← PositivityTheory.Xgn.HermitianNormSquare.core_sum]
end

