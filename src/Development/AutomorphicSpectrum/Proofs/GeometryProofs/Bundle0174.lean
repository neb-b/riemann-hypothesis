module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0169
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    {U : X.Opens} (hpU : p.1 ∈ U) (heU : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ p ((X.presheaf.germ U p.1 hpU).hom s) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) heU).hom s) := by
  have e : (X.presheaf.stalkSpecializes p.2).hom ((X.presheaf.germ U p.1 hpU).hom s) =
      (X.presheaf.germ U (genPt ξ) heU).hom s :=
    ConcreteCategory.congr_hom (X.presheaf.germ_stalkSpecializes hpU p.2) s
  exact congrArg (fun t : X.presheaf.stalk (genPt ξ) => (Scheme.stalkClosedPointTo ξ).hom t) e

theorem exists_eq_div_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ u v : X.presheaf.stalk p.1, genMap ξ p v ≠ 0 ∧ a = genMap ξ p u / genMap ξ p v := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have heU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  obtain ⟨g, hg⟩ : ∃ g : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom g = a := hξ.bij.2 a
  letI alg : Algebra Γ(X, U) (X.presheaf.stalk (genPt ξ)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, heU⟩ : U)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, heU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨genPt ξ, heU⟩
  obtain ⟨⟨f, h⟩, hfh⟩ := IsLocalization.surj (hU.primeIdealOf ⟨genPt ξ, heU⟩).asIdeal.primeCompl g
  have hunit := IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) h
  let ψ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
  have germ_val : ∀ s : Γ(X, U), genMap ξ p ((X.presheaf.germ U p.1 hpU).hom s) =
      (Scheme.stalkClosedPointTo ξ).hom (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) s) :=
    fun s => genMap_germ p hpU heU s
  have hv : (Scheme.stalkClosedPointTo ξ).hom
      (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) (h : Γ(X, U))) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨(X.presheaf.germ U p.1 hpU).hom f, (X.presheaf.germ U p.1 hpU).hom h, ?_, ?_⟩
  · rw [germ_val]
    exact hv
  · rw [germ_val, germ_val, eq_div_iff hv, ← hg]
    exact (map_mul ψ _ _).symm.trans (congrArg ψ hfh)

theorem normalCpt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : Flat.NormalCpt ξ := by
  intro p a ha
  obtain ⟨hd, hc⟩ := hX p.1
  letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk p.1) Ω) := hξ.inj p
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨u, v, -, e⟩ := exists_eq_div_genMap hξ p z
    exact ⟨u, v, e⟩
  letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
    Algebra.IsIntegral.of_surjective (R := X.presheaf.stalk p.1) (A := X.presheaf.stalk p.1)
      (Algebra.ofId _ _) (genMap ξ p).rangeRestrict_surjective
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk p.1) (K := Ω)).1
    (isIntegral_trans (R := X.presheaf.stalk p.1) (A := regAt ξ p) a ha)
  exact ⟨b, hb⟩

theorem exists_cpt_of_genericPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), ∀ e ∈ genericPoints Y.X, ∃ (K : Type) (_ : Field K) (_ : CharZero K) (n : ℕ) (x : Fin n → K) (y : Sp K ⟶ Xo.XF c), CoordTie ℤ (y ≫ Y.j) x ∧ Flat.NormalCpt (y ≫ Y.j) ∧ GlobalTheory.CompanionTheory.Ar.genPt (y ≫ Y.j) = e := by
  intro E _ _ _ H D l Xo c Y e he
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hfrac : (letI := (algebraMap (𝓞 c.F) c.F).toAlgebra; IsFractionRing (𝓞 c.F) c.F) := by
    have : (algebraMap (𝓞 c.F) c.F).toAlgebra = (inferInstance : Algebra (𝓞 c.F) c.F) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [this]
    infer_instance
  have hmax : ∀ y : Y.X, y ⤳ e → y = e := by
    intro y hy
    have h1 : closure {e} = closure {y} :=
      (show Maximal IsIrreducible (closure {e}) from he).eq_of_le isIrreducible_singleton.closure
        (specializes_iff_closure_subset.1 hy)
    exact (inseparable_iff_closure_eq.2 h1.symm).eq
  have hgen : IsCptGen (Ω := Y.X.residueField e) (Y.X.fromSpecResidueField e) :=
    isCptGen_of_maximal Y.X (fun x => (Y.normal x).1) e hmax
  have hj : e ∈ Set.range Y.j :=
    GlobalTheory.T.generic_points_in_generic_fibre E H D l Xo c (𝓞 c.F) _ Y inferInstance hfrac he
  have hr : Set.range (Y.X.fromSpecResidueField e) ⊆ Set.range Y.j := by
    rw [Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.2 hj
  obtain ⟨y, hy⟩ := GlobalTheory.T.field_point_lifts_generic_fibre E H D l Xo c (𝓞 c.F) _ Y hfrac (Y.X.residueField e)
    (Y.X.fromSpecResidueField e) hr
  have hch : CharZero (Y.X.residueField e) := by
    let φ : c.F →+* Y.X.residueField e :=
      (Spec.preimage (y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))).hom
    exact charZero_of_injective_ringHom φ.injective
  have hover : Y.X.fromSpecResidueField e ≫ Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)) =
      spMap (algebraMap ℤ (Y.X.residueField e)) := by
    rw [← Spec.map_preimage (Y.X.fromSpecResidueField e ≫ Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)))]
    congr 1
    ext1
    exact Subsingleton.elim (α := ℤ →+* Y.X.residueField e) _ _
  obtain ⟨n, x, hx⟩ := _root_.GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist ℤ Y.X (Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)))
    (_root_.GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int (𝓞 c.F) Y.X Y.s Y.proj) (Y.X.residueField e) (Y.X.fromSpecResidueField e) hgen hover
  refine ⟨Y.X.residueField e, inferInstance, hch, n, x, y, ?_, ?_, ?_⟩
  · rw [hy]; exact hx
  · rw [hy]; exact normalCpt_of_isCptGen hgen Y.normal
  · rw [hy]; exact Y.X.fromSpecResidueField_apply e _

end GlobalTheory.CompanionTheory.Ar.XR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfCommGroupNsmulSurjective
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_section_of_nonempty {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Sp K) [LocallyOfFiniteType f] [Nonempty X] : ∃ s : Sp K ⟶ X, s ≫ f = 𝟙 _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hc⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X))
    isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint (K := K) f x hc, pointOfClosedPoint_comp (K := K) f x hc⟩

theorem exists_comp_eq_of_surjective {K : Type} [Field K] [IsAlgClosed K] (H : Over (Sp K))
    [LocallyOfFiniteType H.hom] (m : H ⟶ H) [Surjective m.left] (x : 𝟙_ (Over (Sp K)) ⟶ H) :
    ∃ y : 𝟙_ (Over (Sp K)) ⟶ H, y ≫ m = x := by
  have h1 : LocallyOfFiniteType (m.left ≫ H.hom) := by rw [Over.w m]; infer_instance
  have h2 : LocallyOfFiniteType m.left := locallyOfFiniteType_of_comp m.left H.hom
  let q : pullback m.left x.left ⟶ Sp K := pullback.snd m.left x.left
  have h3 : LocallyOfFiniteType q := inferInstanceAs (LocallyOfFiniteType (pullback.snd m.left x.left))
  have h4 : Surjective q := inferInstanceAs (Surjective (pullback.snd m.left x.left))
  have h5 : Nonempty ↥(pullback m.left x.left) := by
    obtain ⟨w, -⟩ := q.surjective (default : PrimeSpectrum K)
    exact ⟨w⟩
  obtain ⟨s, hs⟩ := exists_section_of_nonempty q
  refine ⟨Over.homMk (s ≫ pullback.fst m.left x.left) ?_, ?_⟩
  · have hx : x.left ≫ H.hom = 𝟙 _ := Over.w x
    have hm := Over.w m
    calc (s ≫ pullback.fst m.left x.left) ≫ H.hom
        = s ≫ pullback.fst m.left x.left ≫ m.left ≫ H.hom := by rw [hm]; simp
      _ = s ≫ q ≫ x.left ≫ H.hom := by
          rw [← Category.assoc (pullback.fst m.left x.left), pullback.condition]; simp [q]
      _ = 𝟙 _ := by
          rw [hx]
          change s ≫ q ≫ 𝟙 (Sp K) = _
          rw [Category.comp_id]; exact hs
  · ext1
    change (s ≫ pullback.fst m.left x.left) ≫ m.left = x.left
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (s ≫ q) ≫ x.left = x.left
    rw [hs]
    exact Category.id_comp _

theorem geometricallyConnected_of_surjective_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 G) ^ n : G ⟶ G).left) → GeometricallyConnected G.hom := by
  intro S G _ _ hl hq hn
  refine ⟨fun k _ y Z a b hZ => ?_⟩
  let L := AlgebraicClosure k
  let j : Sp L ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let t : Sp L ⟶ S := j ≫ y
  let H : Over (Sp L) := (Over.pullback t).obj G
  have hlH : LocallyOfFiniteType H.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))
  have hqH : QuasiCompact H.hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom t))
  have hconn : ConnectedSpace H.left := by
    refine GlobalTheory.CompanionTheory.Ar.Approx.connectedSpace_of_divisible L H hlH hqH fun n hn0 x => ?_
    have e : (Over.pullback t).map ((𝟙 G) ^ n) = (𝟙 H) ^ n := by
      have := map_pow (Over.pullback t).homMonoidHom (𝟙 G) n
      simpa using this
    have hs : Surjective ((𝟙 H) ^ n : H ⟶ H).left := by
      have hG := hn n hn0
      have sq : IsPullback ((Over.pullback t).map ((𝟙 G) ^ n)).left (pullback.fst G.hom t)
          (pullback.fst G.hom t) ((𝟙 G) ^ n : G ⟶ G).left := by
        have hA : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.fst G.hom t =
            pullback.fst G.hom t ≫ ((𝟙 G) ^ n : G ⟶ G).left := pullback.lift_fst _ _ _
        have hB : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t =
            pullback.snd G.hom t := Over.w ((Over.pullback t).map ((𝟙 G) ^ n))
        have rect : IsPullback (((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t)
            (pullback.fst G.hom t) t (((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom) := by
          rw [hB, Over.w ((𝟙 G) ^ n : G ⟶ G)]
          exact (IsPullback.of_hasPullback _ _).flip
        exact IsPullback.of_right rect hA (IsPullback.of_hasPullback _ _).flip
      rw [← e]
      exact MorphismProperty.of_isPullback (P := @Surjective) sq.flip hG
    obtain ⟨w, hw⟩ := exists_comp_eq_of_surjective H ((𝟙 H) ^ n) x
    refine ⟨w, ?_⟩
    rw [← hw, MonObj.comp_pow, Category.comp_id]
  have hj : Surjective j := ⟨fun z => ⟨default, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have big : IsPullback (pullback.fst b j ≫ a) (pullback.snd b j) G.hom t :=
    (IsPullback.of_hasPullback b j).paste_horiz hZ
  have hc' : ConnectedSpace ↥(pullback G.hom t) := hconn
  have hsurj : Surjective (big.isoPullback.inv ≫ pullback.fst b j) := inferInstance
  exact (big.isoPullback.inv ≫ pullback.fst b j).surjective.connectedSpace
    (big.isoPullback.inv ≫ pullback.fst b j).continuous

end GlobalTheory.CompanionTheory.Ar.Approx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyIntegralFibre
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

open IsLocalRing GlobalTheory.ProperFunctions

theorem isClosed_germ_ne_zero (X : Scheme.{0}) (f : Γ(X, ⊤)) :
    IsClosed {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hx
  have hx' : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ ⊤ x trivial 0 := by
    rw [hx, map_zero]
  obtain ⟨W, hxW, iU, iV, h⟩ := TopCat.Presheaf.germ_eq X.presheaf (U := ⊤) (V := ⊤) x trivial trivial f 0 hx'
  refine Filter.mem_of_superset (W.2.mem_nhds hxW) fun y hy ↦ ?_
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  rw [← X.presheaf.germ_res_apply iU y hy, h, map_zero, map_zero]

theorem germ_mem_maximalIdeal {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}}
    (p : X ⟶ Sp A) (x : X) (hx : p x = closedPoint A) {a : A} (ha : a ∈ maximalIdeal A) :
    X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) ∈
      maximalIdeal (X.presheaf.stalk x) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := (X.mem_basicOpen (U := ⊤) _ x trivial).mpr hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := by
    rw [Scheme.preimage_basicOpen]
    exact h1
  have h3 : p x ∈ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact h3 ha

theorem eq_zero_of_mem_pow {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{0}} (p : X ⟶ Sp A) [UniversallyClosed p] [LocallyOfFiniteType p]
    (f : Γ(X, ⊤))
    (h : ∀ (n : ℕ) (U : X.affineOpens), X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op f ∈
      (((maximalIdeal A) ^ (n + 1)).map (Scheme.ΓSpecIso (.of A)).inv.hom).map
        (p.appLE ⊤ U.1 (le_preimage_top p _)).hom) : f = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_contra hf
  have hne : ∃ z : X, X.presheaf.germ ⊤ z trivial f ≠ 0 := by
    by_contra hall
    push_neg at hall
    refine hf (TopCat.Presheaf.section_ext X.sheaf ⊤ f 0 fun x _ ↦ ?_)
    rw [map_zero]
    exact hall x
  obtain ⟨z, hz⟩ := hne
  have hcl := p.isClosedMap _ (isClosed_germ_ne_zero X f)
  have hmem : closedPoint A ∈ p '' {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0} :=
    (specializes_closedPoint (p z)).mem_closed hcl ⟨z, hz, rfl⟩
  obtain ⟨x, hxZ, hx⟩ := hmem
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine hxZ ?_
  have hθ : ∀ a : A, X.presheaf.germ U x hxU
      (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) =
      X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := by
    intro a
    have e1 : p.appLE ⊤ U (le_preimage_top p _) =
        p.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := rfl
    rw [e1, CommRingCat.comp_apply]
    exact X.presheaf.germ_res_apply _ x hxU _
  have hpow : ∀ n : ℕ, X.presheaf.germ ⊤ x trivial f ∈
      maximalIdeal (X.presheaf.stalk x) ^ (n + 1) := by
    intro n
    have h1 := Ideal.mem_map_of_mem (X.presheaf.germ U x hxU).hom (h n ⟨U, hU⟩)
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_pow] at h1
    have h2 : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ U x hxU
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f) :=
      (X.presheaf.germ_res_apply _ x hxU f).symm
    rw [h2]
    refine Ideal.pow_right_mono ?_ _ h1
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    change X.presheaf.germ U x hxU
      (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) ∈ _
    rw [hθ]
    exact germ_mem_maximalIdeal p x hx ha
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (X.presheaf.stalk x))
    Ideal.IsPrime.ne_top'
  have : X.presheaf.germ ⊤ x trivial f ∈ (⊥ : Ideal (X.presheaf.stalk x)) := by
    rw [← hbot, Ideal.mem_iInf]
    intro i
    exact Ideal.pow_le_pow_right (Nat.le_succ i) (hpow i)
  simpa using this

theorem geometricallyIntegral_fibre {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (π : A →+* B) (hπ : Function.Surjective π) [IsLocalHom π] {X : Scheme.{0}}
    (p : X ⟶ Sp A) (hG : GeometricallyIntegral (pullback.snd p (spMap (residue A)))) :
    GeometricallyIntegral
      (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B))) := by
  let φ : ResidueField A →+* ResidueField B := ResidueField.map π
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hπ b
    exact ⟨residue A a, ResidueField.map_residue π a⟩
  have : IsIso (CommRingCat.ofHom φ) := (ConcreteCategory.isIso_iff_bijective _).mpr hφ
  have : IsIso (spMap φ) := inferInstanceAs (IsIso (Spec.map _))
  have e1 : φ.comp (residue A) = (residue B).comp π := by
    ext a
    exact ResidueField.map_residue π a
  have hw : spMap (residue B) ≫ spMap π = spMap φ ≫ spMap (residue A) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1]
  have H := (IsPullback.of_hasPullback (pullback.snd p (spMap π)) (spMap (residue B))).paste_horiz
    (IsPullback.of_hasPullback p (spMap π))
  rw [hw] at H
  have R := IsPullback.of_hasPullback p (spMap (residue A))
  have w : (pullback.fst (pullback.snd p (spMap π)) (spMap (residue B)) ≫
      pullback.fst p (spMap π)) ≫ p =
      (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B)) ≫ spMap φ) ≫
        spMap (residue A) := H.w.trans (Category.assoc _ _ _).symm
  have H2 : IsPullback (R.lift _ _ w) (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B)))
      (pullback.snd p (spMap (residue A))) (spMap φ) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (spMap (residue A))) (v₁₃ := p)
      (h₂₂ := spMap (residue A)) ?_ (R.lift_snd _ _ w) R
    rw [R.lift_fst]
    exact H
  exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H2 hG

theorem appTop_fst_eq_zero {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [IsArtinianRing B] (π : A →+* B) (hπ : Function.Surjective π) [IsLocalHom π]
    {X : Scheme.{0}} (p : X ⟶ Sp A) (e : Sp A ⟶ X) (he : e ≫ p = 𝟙 _) (hF : Flat p)
    (hP : IsProper p) (hG : GeometricallyIntegral (pullback.snd p (spMap (residue A))))
    (f : Γ(X, ⊤)) (hf : e.appTop f = 0) : (pullback.fst p (spMap π)).appTop f = 0 := by
  have H := IsPullback.of_hasPullback p (spMap π)
  have hqF : Flat (pullback.snd p (spMap π)) := MorphismProperty.of_isPullback H hF
  have hqP : IsProper (pullback.snd p (spMap π)) := MorphismProperty.of_isPullback H hP
  have hiso := isIso_appTop_of_artinian B _ (pullback.snd p (spMap π)) hqF hqP
    (geometricallyIntegral_fibre π hπ p hG)
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (pullback.snd p (spMap π)).appTop).2
    ((pullback.fst p (spMap π)).appTop f)
  let e' : Sp B ⟶ pullback p (spMap π) :=
    pullback.lift (spMap π ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h1 : e'.appTop ((pullback.snd p (spMap π)).appTop c) = c := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd,
      Scheme.Hom.id_appTop]
    rfl
  have h2 : e'.appTop ((pullback.fst p (spMap π)).appTop f) = 0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf, map_zero]
  have hc0 : c = 0 := by
    rw [hc, h2] at h1
    exact h1.symm
  rw [← hc, hc0, map_zero]

theorem ker_appTop_le {A : Type} [CommRing A] (I : Ideal A) :
    RingHom.ker (spMap (Ideal.Quotient.mk I)).appTop.hom ≤
      I.map (Scheme.ΓSpecIso (.of A)).inv.hom := by
  intro r hr
  obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (.of A)).inv a = r :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2 r
  refine Ideal.mem_map_of_mem _ ?_
  have h1 := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))) a)
  simp only [CommRingCat.comp_apply] at h1
  have h2 : (Scheme.ΓSpecIso (.of (A ⧸ I))).inv (Ideal.Quotient.mk I a) = 0 :=
    h1.trans hr
  have h3 : Ideal.Quotient.mk I a = 0 :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).1
      (h2.trans (map_zero _).symm)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3

theorem quotient_pow_facts (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    ∃ (_ : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)))
      (_ : IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1))),
      IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
  have hle : maximalIdeal A ^ (n + 1) ≤ maximalIdeal A := Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hI : maximalIdeal A ^ (n + 1) ≠ ⊤ := fun h ↦
    Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))
  have : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hL : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hH : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have ham : a ∈ maximalIdeal A := (mem_maximalIdeal a).mpr hna
    have h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)
    have := (ha.pow (n + 1))
    rw [h0] at this
    exact not_isUnit_zero this
  have hK : Ring.KrullDimLE 0 (A ⧸ maximalIdeal A ^ (n + 1)) := by
    refine Ring.krullDimLE_zero_iff.mpr fun Q hQ ↦ ?_
    have : Q = maximalIdeal _ := by
      refine le_antisymm (le_maximalIdeal hQ.ne_top) fun b hb ↦ ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      have ham : a ∈ maximalIdeal A := by
        rw [mem_maximalIdeal] at hb ⊢
        exact fun hu ↦ hb (hu.map _)
      have h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) ∈ Q := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)]
        exact Q.zero_mem
      exact hQ.mem_of_pow_mem _ h0
    rw [this]
    exact maximalIdeal.isMaximal _
  exact ⟨hL, IsNoetherianRing.isArtinianRing_of_krullDimLE_zero, hH⟩

theorem isIso_appTop_of_closedFibre : ∀ (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (X : Scheme.{0}) (p : X ⟶ Sp A) (e : Sp A ⟶ X), e ≫ p = 𝟙 _ → Flat p →
    IsProper p → GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A))) →
    IsIso p.appTop := by
  intro A _ _ _ X p e he hF hP hG
  have h1 : p.appTop ≫ e.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have h2 : Function.Injective e.appTop := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    refine eq_zero_of_mem_pow p f fun n U ↦ ?_
    obtain ⟨_, _, _⟩ := quotient_pow_facts A n
    have h0 := appTop_fst_eq_zero (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))
      Ideal.Quotient.mk_surjective p e he hF hP hG f hf
    have h3 := mem_map_ker_of_app_eq_zero
      (IsPullback.of_hasPullback p (spMap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))))) U.2
      (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op f) (by
        rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
        erw [h0]
        exact map_zero _)
    exact Ideal.map_mono (ker_appTop_le _) h3
  have : Mono e.appTop := ConcreteCategory.mono_of_injective _ h2
  exact ⟨e.appTop, h1, by rw [← cancel_mono e.appTop, Category.assoc, h1]; simp⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperOfProperCoverStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_of_proper_cover : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0}) (π : ∀ i, Y i ⟶ X), IsSeparated p → LocallyOfFiniteType p → (∀ i, IsProper (π i ≫ p)) → (∀ x : X, ∃ i, x ∈ Set.range (π i)) → IsProper p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover | exact GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PureTypeProjectionIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem tyPart_pure_family_bases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsTypeFn H p q ty → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → IsPure hP x → LinearIndependent (𝓞 E) x → (LinearIndependent ℂ (fun a => tyPart ty τ (P (x (.inl a)))) ∧ ∀ w : Fin g → ℂ, w ∈ Submodule.span ℂ (Set.range fun a => tyPart ty τ (P (x (.inl a)))) ↔ tyPart ty τ w = w) ∧ LinearIndependent ℂ (fun a => tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr a)))) ∧ ∀ w : Fin g → ℂ, w ∈ Submodule.span ℂ (Set.range fun a => tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr a)))) ↔ tyPart ty (ComplexEmbedding.conjugate τ) w = w := by
  exact @PositivityTheory.Xgf.pure_type_projection_independent

end GlobalTheory.CompanionTheory.Ar.Fl
end

