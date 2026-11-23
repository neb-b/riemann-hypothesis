module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTrdegEqDimension
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptTrdeg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem trdeg_residueField_of_isIntegral {K B : Type} [Field K] [CharZero K] [CommRing B] [Algebra K B]
    [Algebra.IsIntegral K B] (q : Ideal B) [q.IsPrime] :
    Algebra.trdeg ℤ q.ResidueField = Algebra.trdeg ℤ K := by
  have hcm : (Ideal.comap (algebraMap K B) q).IsMaximal :=
    Ideal.IsPrime.isMaximal' (Ideal.comap_isPrime _ _)
  have hmax : q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := K) q hcm
  have hs : Function.Surjective (IsScalarTower.toAlgHom K B q.ResidueField) :=
    Ideal.algebraMap_residueField_surjective q
  have : Algebra.IsIntegral K q.ResidueField := Algebra.IsIntegral.of_surjective _ hs
  have : CharZero q.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K q.ResidueField).injective
  have h0 : Algebra.trdeg K q.ResidueField = 0 := trdeg_eq_zero
  rw [← trdeg_add_eq ℤ K (A := q.ResidueField), h0, add_zero]

theorem trdeg_int_eq_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (e : A ≃+* B) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ B :=
  (AlgEquiv.ofRingEquiv (f := e) (fun n => by simp [eq_intCast (algebraMap ℤ A), eq_intCast (algebraMap ℤ B)])).trdeg_eq

theorem residueFieldMap_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Bijective (f.residueFieldMap x).hom := by
  refine ⟨RingHom.injective _, fun b => ?_⟩
  obtain ⟨c, rfl⟩ := X.residue_surjective x b
  obtain ⟨d, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective f x c
  exact ⟨Y.residue (f x) d, congr($(Scheme.residue_residueFieldMap f x).hom d)⟩

theorem trdeg_residueField_of_fst {X : Scheme.{0}} {O F Ω₀ : Type} [CommRing O] [Field F] [Field Ω₀] [CharZero Ω₀]
    (s : X ⟶ Sp O) (β : O →+* F) (g₀ : O →+* Ω₀) (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (hs : ξ₀ ≫ s = spMap g₀)
    (hγ : Function.Injective g₀)
    (hF : letI := β.toAlgebra; ∀ u : F, ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u))
    {y : ↥(pullback s (spMap β))} (hy : pullback.fst s (spMap β) y = genPt ξ₀) :
    Algebra.trdeg ℤ ((pullback s (spMap β)).residueField y) = Algebra.trdeg ℤ Ω₀ := by
  letI := β.toAlgebra
  letI := g₀.toAlgebra
  have hsurj : SurjectiveOnStalks ξ₀ := by
    have : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀]
    infer_instance
  obtain ⟨z, rfl, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y
    (IsLocalRing.closedPoint Ω₀) hy
  have sq : IsPullback (pullback.snd (pullback.fst s (spMap β)) ξ₀)
      (pullback.fst (pullback.fst s (spMap β)) ξ₀ ≫ pullback.snd s (spMap β)) (spMap g₀) (spMap β) := by
    rw [← hs]
    exact (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip.paste_vert
      (IsPullback.of_hasPullback s (spMap β))
  let e := sq.isoPullback ≪≫ pullbackSpecIso O Ω₀ F
  have hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := HodgeBasic.isIntegral_tensor hγ hF
  let p : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z
  have h1 : Algebra.trdeg ℤ p.asIdeal.ResidueField = Algebra.trdeg ℤ Ω₀ :=
    trdeg_residueField_of_isIntegral (K := Ω₀) p.asIdeal
  have hst : SurjectiveOnStalks (pullback.fst (pullback.fst s (spMap β)) ξ₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip hsurj
  have h2 := trdeg_int_eq_of_ringEquiv (RingEquiv.ofBijective _ (residueFieldMap_bijective
    (pullback.fst (pullback.fst s (spMap β)) ξ₀) z))
  have h3 := trdeg_int_eq_of_ringEquiv (asIso (e.hom.residueFieldMap z)).commRingCatIsoToRingEquiv
  have h4 : Algebra.trdeg ℤ ((Spec (.of (Ω₀ ⊗[O] F))).residueField p) = Algebra.trdeg ℤ p.asIdeal.ResidueField :=
    trdeg_int_eq_of_ringEquiv (B := p.asIdeal.ResidueField)
      (Scheme.Spec.residueFieldIso (.of (Ω₀ ⊗[O] F)) p).commRingCatIsoToRingEquiv
  exact h2.trans (h3.symm.trans (h4.trans h1))

theorem trdeg_eq_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Function.Injective β → IsCptGen ξ₀ → x ≫ Y.j = Spec.map (CommRingCat.ofHom i) ≫ ξ₀ → Algebra.trdeg ℤ Ω₀ = ((D.dim : ℕ) : Cardinal) := by
  intro E _ _ _ H D l Xo c O _ β Y Ω₀ _ ξ₀ Ω _ x i hβ h₀ hx
  have := c.fin
  have := Y.jQ_open

  let g₀ : O →+* Ω₀ := (Spec.preimage (ξ₀ ≫ Y.s)).hom
  have hs : ξ₀ ≫ Y.s = spMap g₀ := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (ξ₀ ≫ Y.s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let str := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let cst : c.F →+* Ω := (Spec.preimage (x ≫ str)).hom
  have hc : x ≫ str = spMap cst := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (x ≫ str)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hj : Y.j ≫ Y.s = str ≫ spMap β := by
    simp only [Model.j, Category.assoc, pullback.condition]
    rw [← Category.assoc, Y.jQ_over]
  have hcomp : i.comp g₀ = cst.comp β := by
    have h1 : spMap (i.comp g₀) = spMap (cst.comp β) := by
      have h2 : spMap i ≫ ξ₀ ≫ Y.s = x ≫ str ≫ spMap β := by
        rw [← hj, ← Category.assoc, ← Category.assoc, ← hx]
      rw [hs, ← Category.assoc, hc] at h2
      simpa only [spMap, CommRingCat.ofHom_comp, Spec.map_comp] using h2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hg : Function.Injective g₀ := by
    refine Function.Injective.of_comp (f := i) ?_
    have h3 : (i ∘ g₀) = cst ∘ β := congrArg DFunLike.coe hcomp
    rw [h3]
    exact cst.injective.comp hβ
  have hΩ : CharZero Ω := charZero_of_injective_ringHom cst.injective
  have hΩ₀ : CharZero Ω₀ := (RingHom.charZero_iff i.injective).2 hΩ

  let w : Xo.XF c := x (IsLocalRing.closedPoint Ω)
  have hy : pullback.fst Y.s (spMap β) (Y.jQ w) = genPt ξ₀ := by
    have h4 : pullback.fst Y.s (spMap β) (Y.jQ w) = (x ≫ Y.j) (IsLocalRing.closedPoint Ω) := rfl
    have h6 : (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) (IsLocalRing.closedPoint Ω) =
        ξ₀ ((Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint Ω)) := rfl
    have h5 : (Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint Ω₀ :=
      Subsingleton.elim (α := PrimeSpectrum _) _ _
    rw [h4, hx, h6, h5]
    rfl
  have hF := HodgeBasic.exists_integral_multiple_of_injective β hβ
  have hw : ∀ w' : Xo.XF c, w' ⤳ w → w' = w := fun w' h =>
    Y.jQ.isOpenEmbedding.injective
      (HodgeBasic.eq_of_specializes_of_fst Y.s β g₀ ξ₀ h₀ hs hg hF hy (h.map Y.jQ.continuous))

  have hsm : SmoothOfRelativeDimension D.dim str :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  obtain ⟨-, htr⟩ := GlobalTheory.residueField_fg_trdeg_of_smoothOfRelativeDimension str D.dim hsm w hw
  letI : Algebra c.F ((Xo.XF c).residueField w) :=
    (Spec.preimage ((Xo.XF c).fromSpecResidueField w ≫ str)).hom.toAlgebra
  have : CharZero ((Xo.XF c).residueField w) :=
    charZero_of_injective_algebraMap (algebraMap c.F ((Xo.XF c).residueField w)).injective
  have h6 : Algebra.trdeg ℤ ((Xo.XF c).residueField w) = (D.dim : Cardinal) := by
    have hal : Algebra.IsAlgebraic ℤ c.F :=
      ⟨fun u => (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic u)⟩
    have h0 : Algebra.trdeg ℤ c.F = 0 := trdeg_eq_zero
    rw [← trdeg_add_eq ℤ c.F (A := (Xo.XF c).residueField w), h0, zero_add]
    exact htr
  have h7 := trdeg_int_eq_of_ringEquiv (asIso (Y.jQ.residueFieldMap w)).commRingCatIsoToRingEquiv
  have h8 := trdeg_residueField_of_fst Y.s β g₀ ξ₀ h₀ hs hg hF hy
  rw [← h8, h7, h6]

end GlobalTheory.CompanionTheory.Ar.CptTrdeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistFrameCompat
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem genPt_specializes_of_injective {Ω : Type} [Field Ω] {R : CommRingCat.{0}} [IsDomain R]
    (φ : R ⟶ CommRingCat.of Ω) (hφ : Function.Injective φ.hom) (q : Spec R) :
    genPt (Spec.map φ) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes (genPt (Spec.map φ) : PrimeSpectrum R) q).1 ?_
  intro a ha
  have hm : φ.hom a ∈ IsLocalRing.maximalIdeal Ω := ha
  have h0 : φ.hom a = 0 := by
    by_contra hne
    exact hm (isUnit_iff_ne_zero.2 hne)
  have : a = 0 := hφ (h0.trans (map_zero φ.hom).symm)
  rw [this]
  exact zero_mem _

theorem lift_transfer {X X' W W' V : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    (e : X' ≅ X) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (hξ : ξ' ≫ e.hom = ξ)
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) (hdom : ∀ p : X', IsDomain (X'.presheaf.stalk p))
    (sW : W ⟶ Sp R) (hproj : IsProjOver sW)
    (f : X ⟶ W) (f' : X' ⟶ W') (j : V ⟶ W) (j' : V ⟶ W') [Mono j'] (Ψ : V ≅ V) (x x' : Sp Ω ⟶ V)
    (hx : x' ≫ Ψ.inv = x) (hf : ξ ≫ f = x ≫ j) (hf' : ξ' ≫ f' = x' ≫ j') (p : X')
    (hu : ∃ u' : Spec (X'.presheaf.stalk p) ⟶ V, u' ≫ j' = X'.fromSpecStalk p ≫ f') :
    ∃ u : Spec (X.presheaf.stalk (e.hom p)) ⟶ V, u ≫ j = X.fromSpecStalk (e.hom p) ≫ f := by
  obtain ⟨u', hu'⟩ := hu
  haveI := hdom p
  have h' : ξ' (IsLocalRing.closedPoint Ω) ⤳ p := hall p
  let φ : X'.presheaf.stalk p ⟶ CommRingCat.of Ω := X'.presheaf.stalkSpecializes h' ≫ Scheme.stalkClosedPointTo ξ'
  let ξp : Sp Ω ⟶ Spec (X'.presheaf.stalk p) := Spec.map φ
  have hξp : ξp ≫ X'.fromSpecStalk p = ξ' := by
    simp only [ξp, φ]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have hgp : ∀ q, genPt ξp ⤳ q := genPt_specializes_of_injective φ (hgen.inj ⟨p, hall p⟩)
  have hxu : ξp ≫ u' = x' := by
    rw [← cancel_mono j', Category.assoc, hu', ← Category.assoc, hξp, hf']
  have heq : u' ≫ Ψ.inv ≫ j = X'.fromSpecStalk p ≫ e.hom ≫ f := by
    refine _root_.GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic R (Spec (X'.presheaf.stalk p)) W sW Ω ξp _ _ hproj hgp ?_
    have h1 : ξp ≫ u' ≫ Ψ.inv ≫ j = x ≫ j := by rw [reassoc_of% hxu, reassoc_of% hx]
    have h2 : ξp ≫ X'.fromSpecStalk p ≫ e.hom ≫ f = x ≫ j := by rw [reassoc_of% hξp, reassoc_of% hξ, hf]
    rw [h1, h2]
  haveI : IsIso (e.hom.stalkMap p) := inferInstance
  refine ⟨inv (Spec.map (e.hom.stalkMap p)) ≫ u' ≫ Ψ.inv, ?_⟩
  rw [Category.assoc, Category.assoc, heq, ← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, IsIso.inv_hom_id_assoc]

end GlobalTheory.CompanionTheory.Ar.TwistInterior

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem interior_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z ↔ A.Interior (z ≫ e.hom) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hf hf' hfst hsnd _ _ _ z
  have hΦ' : Φ.inv ≫ Xo.s = Xo.s := (Iso.inv_comp_eq Φ).2 hΦ.symm
  let ΦF : Xo.XF c ≅ Xo.XF c :=
    { hom := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.hom)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ, pullback.condition])
      inv := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.inv)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ', pullback.condition])
      hom_inv_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.hom_inv_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp])
      inv_hom_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.inv_hom_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp]) }
  have hxx : x ≫ ΦF.hom = x' := by
    apply pullback.hom_ext
    · simp only [ΦF, Category.assoc, pullback.lift_fst, hfst]
    · simp only [ΦF, Category.assoc, pullback.lift_snd, hsnd]
  obtain ⟨hjY, hA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.IntOpen.interior_iff_factor E H D l Xo c O β Y S Ω K J y A (z ≫ e.hom) hβ
  obtain ⟨hjY', hA'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.IntOpen.interior_iff_factor E H D l Xo c O' β' Y' S Ω K J y A' z hβ'
  have hc : centre (z ≫ e.hom) = e.hom (centre z) := rfl
  rw [hA, hA', hc]
  constructor
  · exact lift_transfer e A.ξ A'.ξ hξ A'.tie.gen A'.all (fun p => (A'.normal p).1) Y.s Y.proj A.f A'.f Y.j Y'.j
      ΦF x x' (by rw [← hxx, Category.assoc, Iso.hom_inv_id, Category.comp_id]) hf hf' (centre z)
  · intro hu
    have key := lift_transfer e.symm A'.ξ A.ξ (by rw [← hξ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])
      A.tie.gen A.all (fun p => (A.normal p).1) Y'.s Y'.proj A'.f A.f Y'.j Y.j ΦF.symm x' x
      (by rw [Iso.symm_inv, hxx]) hf' hf (e.hom (centre z)) hu
    have hp : e.symm.hom (e.hom (centre z)) = centre z := by
      rw [Iso.symm_hom, ← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    rwa [hp] at key

end GlobalTheory.CompanionTheory.Ar.TwistInterior
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGermEigen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame

section Abstract

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {E : Type} [Field E] [NumberField E]
  {A : Subring K}

theorem mem_of_isFreeOn {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) (i : Fin N) : t i ∈ L := by
  have e : t i = ρ 1 (t i) := by simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h.2.2, e, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_zsmul, LinearMap.smul_apply]
  exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _

theorem exists_lift_basis {R Y : Type} [CommRing R] [AddCommGroup Y] [Module R Y] (f : R →+* K)
    (hf : Function.Injective f) (hA : ∀ a, a ∈ A ↔ ∃ c, f c = a) (Φ : Y →+ V)
    (hsmul : ∀ (c : R) y, Φ (c • y) = f c • Φ y) (hinj : Function.Injective Φ)
    {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} (hrange : ∀ v, v ∈ L ↔ ∃ y, Φ y = v)
    (rB : 𝓞 E → Y → Y) (hact : ∀ a y, Φ (rB a y) = ρ a (Φ y)) {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) :
    ∃ x : Fin N → Y, (∀ j, Φ (x j) = t j) ∧
      LinearIndependent R (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) ∧
      Submodule.span R (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  choose x hx using fun i => (hrange (t i)).1 (mem_of_isFreeOn h i)
  have hΦ : ∀ c : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R,
      Φ (∑ q, c q • rB (RingOfIntegers.basis E q.2) (x q.1)) =
        ∑ q, f (c q) • ρ (RingOfIntegers.basis E q.2) (t q.1) := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hsmul, hact, hx]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := Fintype.linearIndependent_iff.1 h.1 (fun q => f (c q)) (by rw [← hΦ, hc, map_zero])
    exact hf ((h1 q).trans (map_zero f).symm)
  · rw [eq_top_iff]
    rintro y -
    have hy : Φ y ∈ L := (hrange _).2 ⟨y, rfl⟩
    rw [h.2.2] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
    choose c' hc' using fun q => (hA (c q : K)).1 (c q).2
    have e : y = ∑ q, c' q • rB (RingOfIntegers.basis E q.2) (x q.1) := hinj (by
      rw [hΦ, ← hc]
      exact Finset.sum_congr rfl fun q _ => by rw [hc']; rfl)
    rw [e]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

end Abstract

theorem exists_of_mem_stdLat {Ω : Type} [Field Ω] {A : Subring Ω} {d : ℕ}
    {T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)} {w : (Fin d → Ω) × (Fin d → Ω)}
    (h : w ∈ stdLat A T) : ∃ y₀ : (Fin d → Ω) × (Fin d → Ω), (∀ i, y₀.1 i ∈ A ∧ y₀.2 i ∈ A) ∧ w = T y₀ := by
  induction h using Submodule.span_induction with
  | mem w hw => exact hw
  | zero => exact ⟨0, fun i => ⟨A.zero_mem, A.zero_mem⟩, (map_zero T).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, rfl⟩ := ha
    obtain ⟨z, hz, rfl⟩ := hb
    exact ⟨y + z, fun i => ⟨A.add_mem (hy i).1 (hz i).1, A.add_mem (hy i).2 (hz i).2⟩, (map_add T y z).symm⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, rfl⟩ := ha
    exact ⟨(c : Ω) • y, fun i => ⟨A.mul_mem c.2 (hy i).1, A.mul_mem c.2 (hy i).2⟩, (map_smul T (c : Ω) y).symm⟩

theorem toVec_injective (Ω : Type) [Field Ω] (d : ℕ) : Function.Injective (toVec Ω d) := by
  intro y y' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 ((dotProductEquiv Ω (Fin d)).injective h2)

theorem toVec_surjective (Ω : Type) [Field Ω] (d : ℕ) : Function.Surjective (toVec Ω d) := by
  rintro ⟨a, φ⟩
  obtain ⟨b, rfl⟩ := (dotProductEquiv Ω (Fin d)).surjective φ
  exact ⟨(a, b), rfl⟩

section Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω] {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d r : ℕ}
  {M : LieModel t.G ξ (Fin d → Ω)} {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)}

theorem vmap_injective {R S : Type} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (vmap (d := d) f) := fun _ _ h =>
  Prod.ext (funext fun i => hf (congrFun (congrArg Prod.fst h) i))
    (funext fun i => hf (congrFun (congrArg Prod.snd h) i))

theorem toH_injective (hξ : IsCptGen ξ) (S : GermSys t ξ M) (p : Cpt ξ) : Function.Injective (toH S p) :=
  fun _ _ h => vmap_injective (hξ.inj p)
    ((_root_.GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing _ _ _ _ _ _ _ _ (S.iso p)).2.2.1.1 (toVec_injective Ω d h))

theorem toH_mem_iff (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ)
    (v : (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) : v ∈ 𝓗.HL p ↔ ∃ y, toH S p y = v := by
  constructor
  · intro hv
    obtain ⟨w, rfl⟩ := toVec_surjective Ω d v
    obtain ⟨y₀, hy₀, rfl⟩ := exists_of_mem_stdLat ((hG.2 p w).1 hv)
    choose a ha using fun i => (hy₀ i).1
    choose b hb using fun i => (hy₀ i).2
    refine ⟨(a, b), ?_⟩
    have e : vmap (genMap ξ p) (a, b) = y₀ := Prod.ext (funext ha) (funext hb)
    rw [toH, e]
  · rintro ⟨y, rfl⟩
    exact (hG.2 p _).2 (Submodule.subset_span ⟨vmap (genMap ξ p) y,
      fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩)

theorem toH_rhoH (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ) (a : 𝓞 E)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (rhoH (S.g p).B a y) = 𝓗.ρH a (toH S p y) := by
  have h1 := vmap_rhoH (S.mapK p) a y
  have h2 := LinearMap.congr_fun ((_root_.GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a) (vmap (genMap ξ p) y)
  have h3 := hG.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))
  have e1 := congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h1
  have e2 := congrArg (toVec Ω d) h2.symm
  exact (e1.trans e2).trans h3.symm

end Germ

theorem exists_basis_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (σ : E →+* Ω) (u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)), IsCptGen ξ → S.Gives 𝓗 → (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → ∀ p : Cpt ξ, ∃ (x : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) (A : Matrix (Fin r) (Fin r) Ω), IsHBasis (S.g p).B x ∧ (𝓗.quot σ).IsFrameAt (fun j => ∑ l, A j l • u l) p ∧ ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (x j)) = ∑ l, A j l • u l := by
  intro E _ _ _ H _ X t Ω _ _ ξ d r M S ρ 𝓗 σ u hξ hG hσ _ hu p
  obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
  have hfree := hx p hU
  obtain ⟨x', h1, h2, h3⟩ := exists_lift_basis (genMap ξ p) (hξ.inj p) (A := regAt ξ p) (fun _ => Iff.rfl)
    (AddMonoidHom.mk' (toH S p) (toH_add S p)) (toH_smul S p) (toH_injective hξ S p)
    (toH_mem_iff S hG p) (fun a y => rhoH (S.g p).B a y) (toH_rhoH S hG p) hfree
  have hA : ∀ i, ∃ c : Fin r → Ω, ∑ l, c l • u l = HT.eigProj 𝓗.ρH σ (x i) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hu ▸ HT.LatBasic.eigProj_mem _ _ _)
  choose A hA using hA
  refine ⟨x', Matrix.of A, ⟨h2, h3⟩, ?_, fun j => ?_⟩
  · have e : (fun j => ∑ l, Matrix.of A j l • u l) = fun j => HT.eigProj 𝓗.ρH σ (x j) := funext hA
    rw [e]
    exact ⟨HodgeDeterminantLattice.linearIndependent_eigProj σ hfree,
      HodgeDeterminantLattice.eigQuot_eq_span σ hfree fun a => ⟨⟨_, hσ p a⟩, rfl⟩⟩
  · have := h1 j
    change toH S p (x' j) = x j at this
    rw [this]
    exact (hA j).symm

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem top_le_spMap_comp_iff {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  have hsub : ∀ a b : Sp ℂ, a = b := fun a b => Subsingleton.elim (α := PrimeSpectrum ℂ) a b
  constructor
  · intro h p _
    have hq : x.base ((spMap σ).base p) ∈ U := h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    rwa [hsub ((spMap σ).base p) p] at hq
  · intro h p _
    exact h (show (spMap σ).base p ∈ (⊤ : (Sp ℂ).Opens) from trivial)

private theorem gammaSpecIso_appLE_spMap_apply (z : Γ(Sp ℂ, ⊤)) (σ : ℂ →+* ℂ)
    (e : (⊤ : (Sp ℂ).Opens) ≤ (spMap σ) ⁻¹ᵁ ⊤) :
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
      ((CommRingCat.Hom.hom (Scheme.Hom.appLE (spMap σ) ⊤ ⊤ e)) z) =
    σ ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) z) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
  exact congrArg (fun φ => CommRingCat.Hom.hom φ z) h

theorem valAt'_spMap_comp {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (spMap σ ≫ x) U f = σ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ U
  · have hc : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := (top_le_spMap_comp_iff σ x U).2 hx
    rw [dite_eq_left hc, dite_eq_left hx]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
    rw [← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ hx (by simp)]
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact gammaSpecIso_appLE_spMap_apply _ σ _
  · have hc : ¬ ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun h => hx ((top_le_spMap_comp_iff σ x U).1 h)
    rw [dite_eq_right hc, dite_eq_right hx, map_zero]

private theorem differentiableOn_conj_comp_star {m : ℕ} {g : (Fin m → ℂ) → ℂ} {S : Set (Fin m → ℂ)}
    (hg : DifferentiableOn ℂ g S) :
    DifferentiableOn ℂ (fun b => starRingEnd ℂ (g (star b))) (star ⁻¹' S) := by
  intro b hb
  obtain ⟨L, hL⟩ := hg (star b) hb
  have h1 : HasFDerivWithinAt (star : (Fin m → ℂ) → (Fin m → ℂ))
      ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) (star ⁻¹' S) b :=
    ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt g (L.restrictScalars ℝ) S (star b) := hL.restrictScalars ℝ
  have h3 := h2.comp b h1 (fun y hy => hy)
  have hR := ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasFDerivWithinAt b h3
  let L' : (Fin m → ℂ) →L[ℂ] ℂ :=
    { toFun := fun v => star (L (star v))
      map_add' := fun v w => by simp [star_add, map_add (f := _)]
      map_smul' := fun c v => by simp [star_smul, map_smul]
      cont := continuous_star.comp (L.continuous.comp continuous_star) }
  exact ⟨L', HasFDerivWithinAt.of_restrictScalars (𝕜 := ℝ) hR (by ext v; rfl)⟩

theorem isHolTo_conj (X : Scheme.{0}) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (hy : IsHolTo B y) :
    IsHolTo (star ⁻¹' B) (fun b => spMap (starRingEnd ℂ) ≫ y (star b)) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo at hy ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hset : {b | b ∈ star ⁻¹' B ∧
        ⊤ ≤ (TopologicalSpace.Opens.map (spMap (starRingEnd ℂ) ≫ y (star b)).base).obj U}
      = star ⁻¹' {b | b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (y b).base).obj U} := by
    ext b
    exact and_congr_right fun _ => top_le_spMap_comp_iff (starRingEnd ℂ) (y (star b)) U
  rw [hset]
  refine ⟨ho.preimage continuous_star, ?_⟩
  refine (differentiableOn_conj_comp_star hd).congr ?_
  intro b _
  exact valAt'_spMap_comp (starRingEnd ℂ) (y (star b)) U f

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

