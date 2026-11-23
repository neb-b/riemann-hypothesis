module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ExistsFgSmoothOfRelativeDimension
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

def dimLocus {X S : Scheme.{0}} (p : X ⟶ S) (g : ℕ) : X.Opens :=
  ⨆ U : {U : X.Opens // SmoothOfRelativeDimension g (U.ι ≫ p)}, U.1

theorem smoothOfRelativeDimension_snd {X S T : Scheme.{0}} (p : X ⟶ S) (b : T ⟶ S) (g : ℕ)
    (h : pullback.fst p b ⁻¹ᵁ dimLocus p g = ⊤) : SmoothOfRelativeDimension g (pullback.snd p b) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g)
    (fun U : {U : X.Opens // SmoothOfRelativeDimension g (U.ι ≫ p)} => pullback.fst p b ⁻¹ᵁ U.1)
    (top_le_iff.1 fun y _ => ?_) fun U => ?_
  · have hy : pullback.fst p b y ∈ dimLocus p g := h.ge (Set.mem_univ y)
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      ((isPullback_morphismRestrict _ U.1).paste_vert (IsPullback.of_hasPullback _ _)) U.2

theorem preimage_dimLocus_eq_top {X S T : Scheme.{0}} (p : X ⟶ S) [Smooth p] (b : T ⟶ S) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd p b)) :
    pullback.fst p b ⁻¹ᵁ dimLocus p g = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨n, W, hW, d⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim p (pullback.fst p b y)
  obtain rfl : n = g := ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback p b) d h y hW
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, d⟩, hW⟩


open GlobalTheory.Spread in
theorem exists_fg_smoothOfRelativeDimension : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k]
    [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k) (g : ℕ), Smooth p → QuasiCompact p →
    SmoothOfRelativeDimension g (pullback.snd p (spMap (algebraMap k V))) →
    ∃ R : Subalgebra k V, R.FG ∧ SmoothOfRelativeDimension g (pullback.snd p (spMap (algebraMap k R))) := by
  intro k V _ _ _ _ X p g hs hq h
  classical
  have : QuasiCompact p := hq
  let s : (Finset V)ᵒᵖ := .op ∅
  let π : (GlobalTheory.Spread.bcDiagram p V).obj s ⟶ X := pullback.fst p _
  have hπ : (GlobalTheory.Spread.bcCone p V).π.app s ≫ π = pullback.fst p _ :=
    GlobalTheory.Spread.bcMap_fst _ _
  obtain ⟨j, f, hj⟩ := exists_map_eq_top (GlobalTheory.Spread.bcDiagram p V)
    (GlobalTheory.Spread.bcCone p V) (GlobalTheory.Spread.isLimitBcCone p V)
    (π ⁻¹ᵁ dimLocus p g) (by
      rw [← Scheme.Hom.comp_preimage, hπ]
      exact preimage_dimLocus_eq_top p _ g h)
  refine ⟨Algebra.adjoin k (j.unop : Set V), Subalgebra.fg_adjoin_finset _,
    smoothOfRelativeDimension_snd p _ g ?_⟩
  have e : (GlobalTheory.Spread.bcDiagram p V).map f ≫ π = pullback.fst p _ :=
    GlobalTheory.Spread.bcMap_fst _ _
  rwa [← Scheme.Hom.comp_preimage, e] at hj

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.LineBundleSpreadsOut
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem lb_descends_fg : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp k) (p : X ⟶ Sp V) (φ : X ⟶ X₀), QuasiCompact p₀ → IsSeparated p₀ → IsPullback φ p p₀ (spMap (algebraMap k V)) → ∀ L : LB X, L.IsLB → ∃ R : Subalgebra k V, R.FG ∧ ∃ M : LB (pullback p₀ (spMap (algebraMap k R))), M.IsLB ∧ ∀ σ : X ⟶ pullback p₀ (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = φ → σ ≫ pullback.snd _ _ = p ≫ spMap R.val.toRingHom → LBIso L (M.pull σ) := by
  intro k V _ _ _ X₀ X p₀ p φ hqc hsep hpb L hL
  haveI := hqc
  haveI := hsep
  have hcompS : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
      (g : B →+* C), spMap (g.comp f) = spMap g ≫ spMap f := by
    intro A B C _ _ _ f g
    simp only [spMap, CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp]
  obtain ⟨R₀, ι₀, hι₀c, hR₀⟩ : ∃ (R₀ : Subring V) (ι₀ : k →+* R₀),
      R₀.subtype.comp ι₀ = algebraMap k V ∧ ∀ x ∈ R₀, ∃ a, algebraMap k V a = x :=
    ⟨(algebraMap k V).range, (algebraMap k V).rangeRestrict, by ext a; rfl,
      fun x hx => RingHom.mem_range.mp hx⟩
  haveI : QuasiSeparated p₀ := inferInstance
  haveI : QuasiCompact (pullback.snd p₀ (spMap ι₀)) := inferInstance
  haveI : QuasiSeparated (pullback.snd p₀ (spMap ι₀)) := inferInstance
  have hw0 : φ ≫ p₀ = (p ≫ spMap R₀.subtype) ≫ spMap ι₀ := by
    rw [Category.assoc, ← hcompS, hι₀c]; exact hpb.w
  obtain ⟨π, hπ1, hπ2⟩ : ∃ π : X ⟶ pullback p₀ (spMap ι₀),
      π ≫ pullback.fst _ _ = φ ∧ π ≫ pullback.snd _ _ = p ≫ spMap R₀.subtype :=
    ⟨pullback.lift φ _ hw0, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hright : IsPullback (pullback.fst p₀ (spMap ι₀)) (pullback.snd p₀ (spMap ι₀)) p₀
      (spMap ι₀) := IsPullback.of_hasPullback _ _
  have hleft : IsPullback π p (pullback.snd p₀ (spMap ι₀)) (spMap R₀.subtype) := by
    refine IsPullback.of_right ?_ hπ2 hright
    rw [hπ1, ← hcompS, hι₀c]; exact hpb
  obtain ⟨S, hS⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring V R₀ X (pullback p₀ (spMap ι₀)) p
    (pullback.snd p₀ (spMap ι₀)) π L hleft hL
  obtain ⟨R, hRfg, hSR⟩ : ∃ R : Subalgebra k V, R.FG ∧ (S : Set V) ⊆ R :=
    ⟨_, Subalgebra.fg_adjoin_finset S, Algebra.subset_adjoin⟩
  refine ⟨R, hRfg, ?_⟩
  have h : R₀ ≤ R.toSubring := by
    intro x hx
    obtain ⟨a, rfl⟩ := hR₀ x hx
    exact R.algebraMap_mem a
  have hcR : R.val.toRingHom.comp (algebraMap k R) = algebraMap k V := by
    ext a; rfl
  have hw1 : φ ≫ p₀ = (p ≫ spMap R.val.toRingHom) ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, ← hcompS, hcR]; exact hpb.w
  have hinc : (Subring.inclusion h).comp ι₀ = (algebraMap k R : k →+* R) := by
    ext a
    have := RingHom.congr_fun hι₀c a
    simpa using this
  have hw2 : pullback.fst p₀ (spMap (algebraMap k R)) ≫ p₀ =
      (pullback.snd p₀ (spMap (algebraMap k R)) ≫ spMap (Subring.inclusion h)) ≫
        spMap ι₀ := by
    rw [Category.assoc, ← hcompS, hinc]; exact pullback.condition
  obtain ⟨π₁, hπ₁1, hπ₁2⟩ : ∃ π₁ : pullback p₀ (spMap (algebraMap k R)) ⟶ pullback p₀ (spMap ι₀),
      π₁ ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      π₁ ≫ pullback.snd _ _ =
        pullback.snd p₀ (spMap (algebraMap k R)) ≫ spMap (Subring.inclusion h) :=
    ⟨pullback.lift _ _ hw2, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hpb1 : IsPullback π₁ (pullback.snd p₀ (spMap (algebraMap k R)))
      (pullback.snd p₀ (spMap ι₀)) (spMap (Subring.inclusion h)) := by
    refine IsPullback.of_right ?_ hπ₁2 hright
    rw [hπ₁1, ← hcompS, hinc]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨σ₀, hσ₀1, hσ₀2⟩ : ∃ σ₀ : X ⟶ pullback p₀ (spMap (algebraMap k R)),
      σ₀ ≫ pullback.fst _ _ = φ ∧ σ₀ ≫ pullback.snd _ _ = p ≫ spMap R.val.toRingHom :=
    ⟨pullback.lift φ _ hw1, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsub : spMap R.val.toRingHom ≫ spMap (Subring.inclusion h) = spMap R₀.subtype := by
    rw [← hcompS]
    exact congrArg spMap (RingHom.ext fun x => rfl)
  have hj1 : σ₀ ≫ π₁ = π := by
    apply pullback.hom_ext
    · rw [Category.assoc, hπ₁1, hσ₀1, hπ1]
    · rw [Category.assoc, hπ₁2, ← Category.assoc, hσ₀2, Category.assoc, hsub, hπ2]
  obtain ⟨M, hM, hLM⟩ := hS R.toSubring h hSR _ _ π₁ σ₀ hpb1 hj1 hσ₀2
  refine ⟨M, hM, fun σ h1 h2 => ?_⟩
  have hσ : σ = σ₀ := pullback.hom_ext (h1.trans hσ₀1.symm) (h2.trans hσ₀2.symm)
  subst hσ
  exact hLM

end GlobalTheory.CompanionTheory.Ar.Approx
end
end

