module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductFormulaPlacesFunctionField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductFormulaPlacesOfFgField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS

def Places.sigma {k K : Type} [Field k] [Field K] [Algebra k K] {J : Type} [Finite J]
    (F : J → IntermediateField k K) (P : ∀ j, Places (F j) K) : Places k K where
  I := Σ j, (P j).I
  O := fun i => (P i.1).O i.2
  v := fun i => (P i.1).v i.2
  v_mul := fun i => (P i.1).v_mul i.2
  mem := fun i => (P i.1).mem i.2
  const := fun i c => (P i.1).const i.2 (algebraMap k (F i.1) c)
  fin := fun x => by
    refine (Set.finite_iUnion fun j => ((P j).fin x).image (Sigma.mk (β := fun j => (P j).I) j)).subset ?_
    rintro ⟨j, i⟩ hi
    exact Set.mem_iUnion.2 ⟨j, i, hi, rfl⟩
  sum := fun x => by
    classical
    have := Fintype.ofFinite J
    rw [finsum_eq_sum_of_support_subset (s := Finset.univ.sigma fun j => ((P j).fin x).toFinset),
      Finset.sum_sigma]
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [← (P j).sum x, finsum_eq_sum _ ((P j).fin x)]
    · rintro ⟨j, i⟩ hi
      simpa using hi

theorem isAlgebraic_of_forall_erase {k K : Type} [Field k] [Field K] [Algebra k K] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K)) {x : K}
    (h : ∀ t : s, IsAlgebraic (IntermediateField.adjoin k (s \ {(t : K)})) x) : IsAlgebraic k x := by
  have key : x ∈ (AlgebraicIndependent.matroid k K).closure ∅ := by
    have hB := AlgebraicIndependent.matroid_isBase_iff.2 hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · rw [hB.closure_eq]; trivial
    · have := hne.coe_sort
      have e : (⋂ t : s, s \ {(t : K)}) = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun y hy => ?_
        rw [Set.mem_iInter] at hy
        exact (hy ⟨y, (hy this.some).1⟩).2 rfl
      rw [← e, hB.indep.closure_iInter_eq_biInter_closure_of_forall_subset fun _ => Set.diff_subset]
      refine Set.mem_iInter.2 fun t => ?_
      rw [AlgebraicIndependent.matroid_closure_eq]
      exact IntermediateField.isAlgebraic_adjoin_iff.1 (h t)
  rw [AlgebraicIndependent.matroid_closure_eq] at key
  have h2 : IsAlgebraic (IntermediateField.adjoin k (∅ : Set K)) x :=
    IntermediateField.isAlgebraic_adjoin_iff.2 key
  have : Algebra.IsAlgebraic k (IntermediateField.adjoin k (∅ : Set K)) :=
    (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic k K).2 (by simp)
  exact h2.restrictScalars k

theorem transcendental_erase {k K : Type} [Field k] [Field K] [Algebra k K] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K)) (t : s) :
    Transcendental (IntermediateField.adjoin k (s \ {(t : K)})) (t : K) := by
  have hB := AlgebraicIndependent.matroid_isBase_iff.2 hs
  intro h
  refine hB.indep.notMem_closure_diff_of_mem t.2 ?_
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact IntermediateField.isAlgebraic_adjoin_iff.1 h

theorem exists_places_of_fg (k : Type) [Field k] [IsAlgClosed k] (K : Type) [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → x ∈ Set.range (algebraMap k K) := by
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have : Algebra.EssFiniteType (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.EssFiniteType.of_comp k _ K
  have hfin : FiniteDimensional (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have H : ∀ t : (s : Set K), ∃ Pl : Places (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) K,
      ∀ x : K, (∀ i, x ∈ Pl.O i) →
        IsAlgebraic (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) x := by
    intro t
    have e : IntermediateField.adjoin k (s : Set K) = (IntermediateField.adjoin
        (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) {(t : K)}).restrictScalars k := by
      rw [IntermediateField.adjoin_adjoin_left, Set.diff_union_of_subset (by simpa using t.2)]
    rw [e] at hsep hfin
    exact _root_.GlobalTheory.SS.PlacesExt.exists_places _ K t (transcendental_erase hs t) hfin hsep
  choose P hP using H
  refine ⟨Places.sigma _ P, fun x hx => ?_⟩
  have hx' : IsAlgebraic k x := isAlgebraic_of_forall_erase hs fun t => hP t x fun i => hx ⟨t, i⟩
  exact minpoly.mem_range_of_degree_eq_one k x
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx'.isIntegral))

end GlobalTheory.SS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GlueModels

set_option backward.isDefEq.respectTransparency false

theorem exists_glue {X U V W Y : Scheme.{0}} {u : U ⟶ X} {v : V ⟶ X} {p : W ⟶ U} {q : W ⟶ V}
    [IsOpenImmersion u] [IsOpenImmersion v] (h : IsPullback p q u v)
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (a : U ⟶ Y) (b : V ⟶ Y) (hab : p ≫ a = q ≫ b) :
    ∃ φ : X ⟶ Y, u ≫ φ = a ∧ v ≫ φ = b := by
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) u v i
  let m : ∀ i, T i ⟶ Y := fun i => Bool.rec (motive := fun i => T i ⟶ Y) a b i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  suffices hm : _ from ⟨𝒰.glueMorphisms m hm, 𝒰.ι_glueMorphisms m hm false, 𝒰.ι_glueMorphisms m hm true⟩
  · rintro (_ | _) (_ | _)
    · change pullback.fst u u ≫ a = pullback.snd u u ≫ a
      rw [fst_eq_snd_of_mono_eq]
    · change pullback.fst u v ≫ a = pullback.snd u v ≫ b
      rw [← h.isoPullback_inv_fst, ← h.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]
    · change pullback.fst v u ≫ b = pullback.snd v u ≫ a
      rw [← h.flip.isoPullback_inv_fst, ← h.flip.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]
    · change pullback.fst v v ≫ b = pullback.snd v v ≫ b
      rw [fst_eq_snd_of_mono_eq]

theorem isPullback_of_two {W X Y Z U V U' V' : Scheme.{0}} {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {u : U ⟶ X} {v : V ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    {u' : U' ⟶ W} {v' : V' ⟶ W} {aU : U' ⟶ U} {aV : V' ⟶ V}
    (hU : IsPullback aU u' u a) (hV : IsPullback aV v' v a)
    (hU' : IsPullback aU (u' ≫ b) (u ≫ f) g) (hV' : IsPullback aV (v' ≫ b) (v ≫ f) g) :
    IsPullback a b f g := by
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec u v i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  refine Scheme.isPullback_of_openCover _ _ _ _ 𝒰 ?_
  rintro (_ | _)
  · change IsPullback (pullback.snd a u) (pullback.fst a u ≫ b) (u ≫ f) g
    refine hU'.of_iso hU.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  · change IsPullback (pullback.snd a v) (pullback.fst a v ≫ b) (v ≫ f) g
    refine hV'.of_iso hV.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp

theorem isOpenImmersion_inl {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] : IsOpenImmersion (pushout.inl p q) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.left))

theorem isOpenImmersion_inr {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] : IsOpenImmersion (pushout.inr p q) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.right))

theorem pushout_cover {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] (z : (pushout p q : Scheme.{0})) :
    z ∈ Set.range (pushout.inl p q) ∨ z ∈ Set.range (pushout.inr p q) := by
  obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span p q) z
  rcases i with _ | _ | _
  · refine Or.inl ⟨p x, Eq.trans ?_ hx⟩
    exact congrArg (fun g => g x) (colimit.w (span p q) WalkingSpan.Hom.fst)
  · exact Or.inl ⟨x, hx⟩
  · exact Or.inr ⟨x, hx⟩

theorem exists_of_inl_eq_inr {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] {x : U} {y : V} (h : pushout.inl p q x = pushout.inr p q y) :
    ∃ w : W, p w = x ∧ q w = y := by
  obtain ⟨k, fi, fj, w, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span p q)
    (i := WalkingSpan.left) (j := WalkingSpan.right)).1 h
  rcases fi with _ | _
  · rcases fj with _ | _
  · rcases fj with _ | _
    exact ⟨w, h1, h2⟩

theorem model_open {k K : Type} [Field k] [Field K] (β : k →+* K) {U W : Over (Sp K)} (p : W ⟶ U)
    [IsOpenImmersion p.left] {U₀ W₀ : Over (Sp k)} {φU : U.left ⟶ U₀.left} {φW : W.left ⟶ W₀.left}
    (hU : IsPullback φU U.hom U₀.hom (spMap β)) (hW : IsPullback φW W.hom W₀.hom (spMap β))
    (p₀ : W₀ ⟶ U₀) (hp : φW ≫ p₀.left = p.left ≫ φU) :
    IsPullback φW p.left p₀.left φU ∧ IsOpenImmersion p₀.left := by
  have H : IsPullback φW p.left p₀.left φU := by
    refine IsPullback.of_bot ?_ hp hU
    rwa [Over.w p, Over.w p₀]
  refine ⟨H, ?_⟩
  have hβ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap β) := by
    refine ⟨⟨⟨fun x => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩, ?_⟩,
      inferInstanceAs (QuasiCompact (spMap β))⟩
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [β]
    exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat k K))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip (MorphismProperty.of_isPullback hU.flip hβ) ‹_›

theorem glue_models : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (X U V W : Over (Sp K)) (u : U ⟶ X) (v : V ⟶ X) (p : W ⟶ U) (q : W ⟶ V), IsOpenImmersion u.left → IsOpenImmersion v.left → IsPullback p.left q.left u.left v.left → (∀ x : X.left, x ∈ Set.range u.left ∨ x ∈ Set.range v.left) → ∀ (U₀ V₀ W₀ : Over (Sp k)) (φU : U.left ⟶ U₀.left) (φV : V.left ⟶ V₀.left) (φW : W.left ⟶ W₀.left), IsPullback φU U.hom U₀.hom (spMap β) → IsPullback φV V.hom V₀.hom (spMap β) → IsPullback φW W.hom W₀.hom (spMap β) → ∀ (p₀ : W₀ ⟶ U₀) (q₀ : W₀ ⟶ V₀), φW ≫ p₀.left = p.left ≫ φU → φW ≫ q₀.left = q.left ≫ φV → ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β) := by
  intro k K _ _ β X U V W u v p q hu hv h hc U₀ V₀ W₀ φU φV φW hU hV hW p₀ q₀ hp hq
  have : IsOpenImmersion p.left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip hv
  have : IsOpenImmersion q.left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h hu
  obtain ⟨Hp, _⟩ := model_open β p hU hW p₀ hp
  obtain ⟨Hq, _⟩ := model_open β q hV hW q₀ hq
  have := isOpenImmersion_inl p₀.left q₀.left
  have := isOpenImmersion_inr p₀.left q₀.left
  obtain ⟨φ, h1, h2⟩ := exists_glue h hc (φU ≫ pushout.inl p₀.left q₀.left) (φV ≫ pushout.inr p₀.left q₀.left) (by
    rw [← Category.assoc, ← Category.assoc, ← hp, ← hq, Category.assoc, Category.assoc, pushout.condition])
  have e1 (x : U.left) : φ (u.left x) = pushout.inl p₀.left q₀.left (φU x) := congrArg (fun g => g x) h1
  have e2 (x : V.left) : φ (v.left x) = pushout.inr p₀.left q₀.left (φV x) := congrArg (fun g => g x) h2
  have e3 (w : W.left) : u.left (p.left w) = v.left (q.left w) := congrArg (fun g => g w) h.w
  refine ⟨Over.mk (pushout.desc U₀.hom V₀.hom ((Over.w p₀).trans (Over.w q₀).symm)), φ, ?_⟩
  refine isPullback_of_two (pushout_cover p₀.left q₀.left) (u' := u.left) (v' := v.left) (aU := φU) (aV := φV)
    ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hq w x hw
        exact ⟨p.left z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨φU y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hp w x hw
        exact ⟨q.left z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨φV y, (e2 y).symm⟩
  · simpa only [Over.w u, Over.mk_hom, pushout.inl_desc] using hU
  · simpa only [Over.w v, Over.mk_hom, pushout.inr_desc] using hV

end GlobalTheory.GlueModels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpSchemePointsModelOverField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.ModelPoints

theorem exists_push_equiv {S S' : Scheme.{0}} (f : S' ⟶ S) (H : Over S) [GrpObj H] (T : Over S')
    (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ π : (T ⟶ (Over.pullback f).obj H) ≃* (Over.mk s ⟶ H),
      ∀ x, (π x).left = x.left ≫ pullback.fst H.hom f := by
  subst hs
  have h := isGrpPullback_pullback H f
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y => ?_⟩, fun x => rfl⟩
  exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_comp_equiv {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (e : G ≅ H) [IsMonHom e.hom]
    (T : Over S) : ∃ π : (T ⟶ G) ≃* (T ⟶ H), ∀ y, π.symm y = y ≫ e.inv :=
  ⟨{ toFun := fun x => x ≫ e.hom
     invFun := fun y => y ≫ e.inv
     left_inv := fun x => by simp
     right_inv := fun x => by simp
     map_mul' := fun x y => MonObj.mul_comp x y e.hom }, fun _ => rfl⟩

theorem exists_equiv {S₁ S₂ S : Scheme.{0}} (f : S ⟶ S₁) (g : S ⟶ S₂) (A : Over S₁) [GrpObj A]
    (G : Over S₂) [GrpObj G] (e : (Over.pullback g).obj G ≅ (Over.pullback f).obj A) [IsMonHom e.hom]
    {T : Scheme.{0}} (t : T ⟶ S) (s₁ : T ⟶ S₁) (s₂ : T ⟶ S₂) (h₁ : s₁ = t ≫ f) (h₂ : s₂ = t ≫ g) :
    ∃ θ : (Over.mk s₁ ⟶ A) ≃* (Over.mk s₂ ⟶ G), ∀ (x : Over.mk s₁ ⟶ A) (z : T ⟶ pullback A.hom f),
      z ≫ pullback.fst A.hom f = x.left → z ≫ pullback.snd A.hom f = t →
      (θ x).left = z ≫ e.inv.left ≫ pullback.fst G.hom g := by
  obtain ⟨π₁, p₁⟩ := exists_push_equiv f A (Over.mk t) s₁ h₁
  obtain ⟨π₂, p₂⟩ := exists_push_equiv g G (Over.mk t) s₂ h₂
  obtain ⟨π, p⟩ := exists_comp_equiv e (Over.mk t)
  refine ⟨π₁.symm.trans (π.symm.trans π₂), fun x z hz hz' => ?_⟩
  have hx : π₁.symm x = Over.homMk z hz' := by
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hz.symm.trans (p₁ (Over.homMk z hz')).symm)
  show (π₂ (π.symm (π₁.symm x))).left = _
  rw [p₂, p, hx, Over.comp_left, Category.assoc]
  rfl

theorem spMap_comp_of_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap h = spMap g ≫ spMap f := by
  subst e
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem spMap_cancel {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {g : B →+* C}
    (hg : Function.Injective g) {a b : Sp B ⟶ Sp A} (e : spMap g ≫ a = spMap g ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at e
  congr 1
  ext x
  exact hg (congrArg (fun q => q.hom x) e)

theorem points_model : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], IsModel (L := L) A G → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra W Ω] (j : L →+* Ω), j.comp (algebraMap K L) = algebraMap K Ω → j.comp (algebraMap W L) = algebraMap W Ω → ∃ θ : (Over.mk (spMap (algebraMap K Ω)) ⟶ A) ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G), (∀ τ : Ω →+* Ω, τ.comp j = j → ∀ x x', x'.left = spMap τ ≫ x.left → (θ x').left = spMap τ ≫ (θ x).left) ∧ ∀ (K' : Type) [Field K'] (i : L →+* K') (j' : K' →+* Ω), j'.comp i = j → ∀ (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) (y : Sp K' ⟶ A.left), spMap j' ≫ y = x.left → ∀ ρ : W →+* K', ρ = i.comp (algebraMap W L) → ∃ y' : Over.mk (spMap ρ) ⟶ G, ∀ c : ℕ, spMap j' ≫ (y' ^ c).left = (θ (x ^ c)).left := by
  intro K W L _ _ _ _ _ A _ G _ ⟨e, he⟩ Ω _ _ _ j hK hW
  obtain ⟨θ, hθ⟩ := exists_equiv (spMap (algebraMap K L)) (spMap (algebraMap W L)) A G e (spMap j)
    _ _ (spMap_comp_of_eq hK) (spMap_comp_of_eq hW)
  refine ⟨θ, fun τ hτ x x' hx => ?_, fun K' _ i j' hj x y hy ρ hρ => ?_⟩
  · have w : x.left ≫ A.hom = spMap j ≫ spMap (algebraMap K L) :=
      (Over.w x).trans (spMap_comp_of_eq hK)
    rw [hθ x (pullback.lift x.left (spMap j) w) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
      hθ x' (spMap τ ≫ pullback.lift x.left (spMap j) w)
        (by rw [Category.assoc, pullback.lift_fst, hx])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hτ]), Category.assoc]
  · have w : y ≫ A.hom = spMap i ≫ spMap (algebraMap K L) := by
      apply spMap_cancel j'.injective
      rw [← Category.assoc, hy, ← Category.assoc, ← spMap_comp_of_eq hj]
      exact (Over.w x).trans (spMap_comp_of_eq hK)
    have w' : (pullback.lift y (spMap i) w ≫ e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap W L))) ≫ G.hom
        = spMap ρ := by
      have h₁ : e.inv.left ≫ pullback.snd G.hom (spMap (algebraMap W L))
          = pullback.snd A.hom (spMap (algebraMap K L)) := Over.w e.inv
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% h₁, pullback.lift_snd_assoc]
      exact (spMap_comp_of_eq hρ.symm).symm
    have hU : spMap j' ≫ spMap ρ = spMap (algebraMap W Ω) :=
      (spMap_comp_of_eq (by rw [hρ, ← RingHom.comp_assoc, hj, hW])).symm
    let U : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap ρ) := Over.homMk (spMap j') hU
    let y' : Over.mk (spMap ρ) ⟶ G := Over.homMk _ w'
    have hxy : θ x = U ≫ y' := by
      apply Over.OverMorphism.ext
      rw [hθ x (spMap j' ≫ pullback.lift y (spMap i) w)
        (by rw [Category.assoc, pullback.lift_fst, hy])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hj]), Category.assoc]
      rfl
    refine ⟨y', fun c => ?_⟩
    rw [map_pow, hxy, ← MonObj.comp_pow]
    rfl

end GlobalTheory.SS.ModelPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsOpenImmersionOfExtendsIdOfEtale
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord

namespace GlobalTheory.SS.Ord

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma model_isPullback_genericFibre_spMap (M : _root_.GlobalTheory.SS.Model R A) :
    IsPullback M.j A.hom M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  have h := IsPullback.of_hasPullback M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K))
  refine IsPullback.of_iso h ((Over.forget _).mapIso M.e) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [_root_.GlobalTheory.SS.Model.j, ← Over.comp_left_assoc]
  · have := Over.w M.e.hom
    simpa using this.symm


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] in
theorem _root_.GlobalTheory.SS.Ord.isOpenImmersion_of_extends_id_of_etale :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (M N : _root_.GlobalTheory.SS.Model R A)
      (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left),
      _root_.GlobalTheory.SS.Extends M N (𝟙 A) U g → Etale g → IsOpenImmersion g := by
  intro R K _ _ _ _ _ _ A M N U g hE _
  haveI := M.smooth
  haveI := M.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  haveI : IsSeparated (g ≫ N.Y.hom) := by rw [hE.1]; infer_instance
  haveI : IsSeparated g := IsSeparated.of_comp g N.Y.hom
  haveI := FormallyUnramified.isOpenImmersion_diagonal g
  let ψ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)
  let q := pullback.fst g g ≫ U.ι ≫ M.Y.hom
  let φ := pullback.fst q ψ
  haveI : IsSchemeTheoreticallyDominant φ :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback q ψ).flip
  have hU := ((isPullback_morphismRestrict M.j U).paste_vert
    (model_isPullback_genericFibre_spMap M))
  have hN := model_isPullback_genericFibre_spMap N
  have hs : (φ ≫ pullback.fst g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [Category.assoc]
    exact pullback.condition
  have hs' : (φ ≫ pullback.snd g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [← hs, ← hE.1]
    simp only [Category.assoc, pullback.condition_assoc]
  have key : ∀ (c : pullback q ψ ⟶ U) (hc : c ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ),
      (hU.lift c _ hc ≫ (M.j ⁻¹ᵁ U).ι) ≫ N.j = c ≫ g := by
    intro c hc
    have h2 := hE.2
    conv_rhs => rw [← hU.lift_fst c _ hc]
    rw [Category.assoc (hU.lift c _ hc) (M.j ∣_ U) g, h2]
    simp
  have hl : hU.lift _ _ hs ≫ (M.j ⁻¹ᵁ U).ι =
      hU.lift _ _ hs' ≫ (M.j ⁻¹ᵁ U).ι := by
    apply hN.hom_ext
    · rw [key _ hs, key _ hs']
      simp only [Category.assoc, pullback.condition]
    · have e1 := hU.lift_snd _ _ hs
      have e2 := hU.lift_snd _ _ hs'
      simp only [Category.assoc] at e1 e2 ⊢
      rw [e1, e2]
  have hab : φ ≫ pullback.fst g g = φ ≫ pullback.snd g g := by
    rw [← hU.lift_fst _ _ hs, ← hU.lift_fst _ _ hs', (cancel_mono _).1 hl]
  have hφ : φ = (φ ≫ pullback.fst g g) ≫ pullback.diagonal g := by
    apply pullback.hom_ext <;> simp [hab]
  have hrange : Set.range φ ⊆ Set.range (pullback.diagonal g) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(φ ≫ pullback.fst g g) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hφ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) :=
    (pullback.diagonal g).isClosedEmbedding.isClosed_range
  have huniv : Set.range (pullback.diagonal g) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (IsDominant.denseRange (f := φ)).closure_eq]
    exact closure_minimal hrange hclosed
  haveI : IsIso (pullback.diagonal g) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext (by simpa using huniv))
  haveI : Mono g := (pullback.isIso_diagonal_iff g).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono g

end GlobalTheory.SS.Ord
end

