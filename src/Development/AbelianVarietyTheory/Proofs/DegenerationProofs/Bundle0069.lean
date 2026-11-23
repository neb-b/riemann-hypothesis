module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClosedImmersionDensePoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ToImm
open GlobalTheory.ZH.CrdCalc GlobalTheory.ZH.ImmSep

theorem ext_local {T X : Scheme.{0}} (f g : T ⟶ X)
    (h : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ T), y ≫ f = y ≫ g) : f = g :=
  ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk f g fun t =>
    @h (T.presheaf.stalk t) _ (T.toLocallyRingedSpace.isLocalRing t) (T.fromSpecStalk t)

theorem exists_hom_of_ringHom {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (V : Y.Opens)
    (φ : Γ(X, U) →+* Γ(Y, V)) : ∃ g : V.toScheme ⟶ X, ∀ (R : Type) [CommRing R] (y : Sp R ⟶ V.toScheme)
      (h : ⊤ ≤ (y ≫ V.ι) ⁻¹ᵁ V), ∃ h' : ⊤ ≤ (y ≫ g) ⁻¹ᵁ U,
        ∀ f, valHom (y ≫ g) U h' f = valHom (y ≫ V.ι) V h (φ f) := by
  refine ⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, fun R _ y h => ?_⟩
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h' : ⊤ ≤ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ ((y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) z))
  refine ⟨h', fun f => ?_⟩
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.appLE_comp_appLE (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) hU.fromSpec
      U ⊤ ⊤ h0 le_rfl).symm
  have h3 : (y ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ y.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE y V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]
    erw [Scheme.Opens.ι_appLE]
    simp only [Scheme.Opens.topIso_inv]
    congr 1
  have h4 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      CommRingCat.ofHom φ ≫ (y ≫ V.ι).appLE V ⊤ h := by
    rw [h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc]
    exact Iso.inv_hom_id_assoc _ _
  unfold valHom
  rw [h4]
  rfl

def constHom {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem constHom_apply {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) (a : k) :
    constHom p U a = constFn p U a := rfl

theorem eq_zero_of_dense {Y : Scheme.{0}} [IsReduced Y] {K : Type} [Field K] {A : Type}
    (x : A → (Sp K ⟶ Y)) (hd : Dense (⋃ a, Set.range (x a))) (V : Y.Opens) (f : Γ(Y, V))
    (hf : ∀ a (h : ⊤ ≤ x a ⁻¹ᵁ V), valHom (x a) V h f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro z hz
  obtain ⟨w, hw, hw'⟩ := hd.inter_open_nonempty _ (Y.basicOpen f).isOpen ⟨z, hz⟩
  obtain ⟨a, t, rfl⟩ := Set.mem_iUnion.1 hw'
  have h1 : ⊤ ≤ x a ⁻¹ᵁ Y.basicOpen f := fun t' _ => by
    have : t' = t := Subsingleton.elim (α := PrimeSpectrum K) _ _
    subst this
    exact hw
  have h2 : ⊤ ≤ x a ⁻¹ᵁ V := h1.trans ((x a).preimage_mono (Y.basicOpen_le f))
  have := (isUnit_valR_iff (x a) V h2 f).2 h1
  rw [valR_eq _ _ h2, hf a h2] at this
  exact (not_isUnit_zero this).elim

theorem comp_eq_of_const {k R : Type} [CommRing k] [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp k)
    (p' : Y ⟶ Sp k) (x : Sp R ⟶ X) (y : Sp R ⟶ Y) {U : X.Opens} {V : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ V) (e : ∀ a, valHom x U h (constFn p U a) = valHom y V h' (constFn p' V a)) :
    x ≫ p = y ≫ p' := by
  refine eq_of_valHom_eq _ _ ⊤ (isAffineOpen_top _) le_top le_top (RingHom.ext fun f => ?_)
  obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective f
  have := e a
  rw [valHom_constFn, valHom_constFn] at this
  exact this

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {H : LB X} {H' : LB Y}
  {J : Type} {s : J → H.Sec} {s' : J → H'.Sec}

theorem exists_chart [IsReduced Y] (hH : H.IsLB) (hH' : H'.IsLB) (hI : ImmBy p H s Set.univ)
    {K : Type} [Field K] {A : Type} (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X))
    (hd : Dense (⋃ a, Set.range (x a)))
    (hx : ∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) (i : J) :
    ∃ g : (nonzeroLocus (s' i)).toScheme ⟶ X, ∀ (R : Type) [CommRing R] [IsLocalRing R]
      (y : Sp R ⟶ (nonzeroLocus (s' i)).toScheme),
      (y ≫ g) ≫ p = (y ≫ (nonzeroLocus (s' i)).ι) ≫ p' ∧
        ∀ v, Crd H' s' (y ≫ (nonzeroLocus (s' i)).ι) v → Crd H s (y ≫ g) v := by
  obtain ⟨hA, r, hr, hc⟩ := hI.2 i (Set.mem_univ i)
  choose r' hr' using fun j =>
    (GlobalTheory.SecRatio.existsUnique_isRatio hH' (s' j) (s' i) (nonzeroLocus (s' i)) le_rfl).exists
  let ev := MvPolynomial.eval₂Hom (constHom p (nonzeroLocus (s i))) r
  let ev' := MvPolynomial.eval₂Hom (constHom p' (nonzeroLocus (s' i))) r'
  have hs : Function.Surjective ev := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hc, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  have hk : RingHom.ker ev ≤ RingHom.ker ev' := by
    intro f hf
    refine eq_zero_of_dense x hd _ _ fun a h => ?_
    obtain ⟨e, v, hv', hv⟩ := hx a
    have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
    have h' := (crd_isUnit_iff i hv).1 hu
    have : (valHom (x a) _ h).comp ev' = (valHom (x' a) _ h').comp ev := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) fun j => ?_
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_C, constHom_apply,
          valHom_constFn, e]
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        have e := (crd_ratio hv' (hr' j) h).symm.trans (crd_ratio hv (hr j) h')
        rw [valR_eq _ _ h, valR_eq _ _ h'] at e
        exact hu.mul_right_cancel e
    have := congrArg (fun q => q f) this
    simp only [RingHom.comp_apply] at this
    rw [this, (RingHom.mem_ker).1 hf, map_zero]
  let φ := RingHom.liftOfSurjective ev hs ⟨ev', hk⟩
  have hφ : ∀ f, φ (ev f) = ev' f := fun f => RingHom.liftOfSurjective_comp_apply ev hs ⟨ev', hk⟩ f
  have hφc : ∀ a, φ (constFn p _ a) = constFn p' _ a := fun a => by
    have := hφ (MvPolynomial.C a)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_C, constHom_apply] using this
  have hφr : ∀ j, φ (r j) = r' j := fun j => by
    have := hφ (MvPolynomial.X j)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_X'] using this
  obtain ⟨g, hg⟩ := exists_hom_of_ringHom hA _ φ
  refine ⟨g, fun R _ _ y => ?_⟩
  have h : ⊤ ≤ (y ≫ (nonzeroLocus (s' i)).ι) ⁻¹ᵁ nonzeroLocus (s' i) := fun z _ => (y z).2
  obtain ⟨h', hv⟩ := hg R y h
  refine ⟨comp_eq_of_const p p' _ _ h' h fun a => by rw [hv, hφc], fun v hv' => ?_⟩
  obtain ⟨w, hw⟩ := crd_exists hH s (y ≫ g)
  have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
  have hu' : IsUnit (w i) := (crd_isUnit_iff i hw).2 h'
  have := crd_smul (hu.unit * hu'.unit⁻¹) hw
  convert this using 2 with j
  rw [crd_ratio hv' (hr' j) h, crd_ratio hw (hr j) h', valR_eq _ _ h, valR_eq _ _ h', hv, hφr,
    mul_left_comm, Units.val_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one, IsUnit.unit_spec]

theorem exists_factor : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsReduced Y] (p : X ⟶ Sp k) (p' : Y ⟶ Sp k) (H : LB X) (H' : LB Y) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy p H s Set.univ → ⨆ j, nonzeroLocus (s' j) = ⊤ → ∀ (K : Type) [Field K] (A : Type) (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X)), Dense (⋃ a, Set.range (x a)) → (∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) → ∃ g : Y ⟶ X, g ≫ p = p' ∧ (∀ a, x a ≫ g = x' a) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y) (v : J → R), Crd H' s' y v → Crd H s (y ≫ g) v := by
  intro k _ X Y _ p p' H H' J _ s s' hH hH' hI hc K _ A x x' hd hx
  choose g hg using exists_chart hH hH' hI x x' hd hx
  let 𝒰 := Y.openCoverOfIsOpenCover (fun j => nonzeroLocus (s' j)) hc
  have hcomp : ∀ i j : J, pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g i =
      pullback.snd (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g j := by
    intro i j
    refine ext_local _ _ fun R _ _ y => ?_
    have e : (y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι =
        (y ≫ pullback.snd _ _) ≫ (nonzeroLocus (s' j)).ι := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨a₁, b₁⟩ := hg i R (y ≫ pullback.fst _ _)
    obtain ⟨a₂, b₂⟩ := hg j R (y ≫ pullback.snd _ _)
    obtain ⟨v, hv⟩ := crd_exists hH' s' ((y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι)
    rw [← Category.assoc, ← Category.assoc]
    exact eq_of_crd_eq k X p H J s _ hH hI R _ _ v (by rw [a₁, a₂, e]) (b₁ v hv) (b₂ v (e ▸ hv))
  have hG : ∀ i, (nonzeroLocus (s' i)).ι ≫ 𝒰.glueMorphisms g hcomp = g i :=
    fun i => 𝒰.ι_glueMorphisms g hcomp i
  have key : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y),
      (y ≫ 𝒰.glueMorphisms g hcomp) ≫ p = y ≫ p' ∧
        ∀ v, Crd H' s' y v → Crd H s (y ≫ 𝒰.glueMorphisms g hcomp) v := by
    intro R _ _ y
    have : y (IsLocalRing.closedPoint R) ∈ ⨆ j, nonzeroLocus (s' j) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    have h := (top_le_iff y _).2 hi
    have hr : Set.range y ⊆ Set.range (nonzeroLocus (s' i)).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact h (Set.mem_univ z)
    have e := IsOpenImmersion.lift_fac (nonzeroLocus (s' i)).ι y hr
    have := hg i R (IsOpenImmersion.lift (nonzeroLocus (s' i)).ι y hr)
    rwa [← hG i, ← Category.assoc, e] at this
  refine ⟨𝒰.glueMorphisms g hcomp, ext_local _ _ fun R _ _ y => ?_, fun a => ?_,
    fun R _ _ y => (key R y).2⟩
  · rw [← Category.assoc, (key R y).1]
  · obtain ⟨e, v, hv', hv⟩ := hx a
    exact eq_of_crd_eq k X p H J s _ hH hI K _ _ v (by rw [(key K (x a)).1, e]) ((key K (x a)).2 v hv') hv

end GlobalTheory.ZH.ToImm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumBaseChangeMaps
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section

namespace GlobalTheory


open GtBaseChange in
theorem exists_gtDatum_baseChange_maps :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G] (d : E.GtDatum G), ∃ (E' : SplitExt S') (xe : E'.X ≃+ E.X) (d' : E'.GtDatum ((Over.pullback f).obj G)) (π : E'.B.left ⟶ E.B.left), IsGrpPullback E'.B E.B f π ∧ d'.q.left ≫ π = pullback.fst G.hom f ≫ d.q.left ∧ (∀ χ, LBIso (E'.O χ).L ((E.O (xe χ)).L.pull π)) ∧ ∀ (Z : Over S') (τ : Z ⟶ splitTorus S' E'.X), ∃ τ₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S E.X, (τ₀ ≫ d.i).left = (τ ≫ d'.i).left ≫ pullback.fst G.hom f ∧ ∀ (χ : E'.X) (z : Z.left), gm (Y := Z.left) τ₀.left z ⊤ (charUnit S E.X (xe χ)) = gm τ.left z ⊤ (charUnit S' E'.X χ) := by
  intro S S' f E G _ d
  have := d.q_hom
  have := d.i_hom
  have : IsMonHom (Iso.refl ((Over.pullback f).obj G)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have : IsMonHom (Iso.refl ((Over.pullback f).obj E.B)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨eT, mT, hT⟩ := splitTorus_baseChange S S' f E.X
  obtain ⟨q, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := TorusExtBaseChange.exists_extension f eT
    (Iso.refl ((Over.pullback f).obj G)) (Iso.refl ((Over.pullback f).obj E.B)) d.i d.q d.q_flat d.q_surjective
    d.q_affine d.isKernel
  have hq : q.left ≫ pullback.fst E.B.hom f = pullback.fst G.hom f ≫ d.q.left := by simpa using h7
  have hi : i.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst _ f) ≫ d.i.left := by simpa using h8
  have le : ∀ j : (extBC f E).ChartIdx, q.left ⁻¹ᵁ (extBC f E).chart j ≤
      pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) := fun j y hy => by
    change (pullback.fst G.hom f ≫ d.q.left) y ∈ E.chart (fun k => j k PUnit.unit)
    rw [← hq]
    exact chart_le_preimage f E j hy
  let u : ∀ (j : (extBC f E).ChartIdx) (_ : Module.Free.ChooseBasisIndex ℤ E.X),
      Γ(((Over.pullback f).obj G).left, q.left ⁻¹ᵁ (extBC f E).chart j)ˣ := fun j k =>
    res (le j) (pullU (pullback.fst G.hom f) _ (d.u (fun k => j k PUnit.unit) k))
  have hw : ∀ j k, HasWeight i _ (u j k) (E.basis k) := fun j k =>
    HasWeight.baseChange f ((hasWeight_iff d.i _ _ _ (d.act_le _) _).2 (d.equiv _ k)) i _ (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)) hi (hT _) (le j)
      fun Z t g z hz => translate_mem q i h6 t g _ z hz
  refine ⟨extBC f E, AddEquiv.refl _,
    { q := q
      i := i
      q_hom := h1
      i_hom := h5
      q_flat := h2
      q_surjective := h3
      q_affine := h4
      isKernel := h6
      u := u
      coord := fun j V hV h => coord_of_hasWeight E.basis q i h2 h3 h4 h6 _ (u j) (hw j) V hV h
      trans := fun j j' k => unit_ext fun y hy => ?_
      act_le := fun j y hy => translate_mem q i h6 (fst _ _) (snd _ _) ((extBC f E).chart j) y hy
      equiv := fun j k => (hasWeight_iff i _ _ _ _ _).1 (hw j k)
      unit_norm := fun j k => unit_ext fun y hy => ?_ }, pullback.fst E.B.hom f,
    isGrpPullback_pullback E.B f, hq, fun χ => GtBaseChange.lbIso_refl (pull_isLB (E.O χ).isLB _),
    fun Z τ => ?_⟩
  · have hm : pullback.fst G.hom f y ∈ d.q.left ⁻¹ᵁ
        (E.chart (fun k => j k PUnit.unit) ⊓ E.chart (fun k => j' k PUnit.unit)) := ⟨le j hy.1, le j' hy.2⟩
    have e := congrArg (gm (pullback.fst G.hom f) y _)
      (d.trans (fun k => j k PUnit.unit) (fun k => j' k PUnit.unit) k)
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_pull _ d.q.left y _ hm _).trans (gm_res (pullback.fst G.hom f ≫ d.q.left) y _ hm _))
      (gm_res _ y _ hm _))))
    refine ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j') hy.2 _)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j) hy.1 _)))
    refine ((gm_pull (𝟙 _) q.left y _ hy _).trans (gm_res (𝟙 _ ≫ q.left) y _ hy _)).trans ?_
    refine (gm_pull_g (E.O (E.basis k)).L (pullback.fst E.B.hom f) (𝟙 _ ≫ q.left) y (j k) (j' k)
      ((extBC f E).chart_le j k hy.1) ((extBC f E).chart_le j' k hy.2)).trans ?_
    rw [Category.id_comp, hq]
  · have hs := eSec_fst f G
    have h₁ : (eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f) y ∈
        d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit) := le j hy.1
    rw [hs] at h₁
    have h₂ := (rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k) hy.2
    let f' : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left := f
    have hm : f' y ∈ eSec G ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) ⊓
        ((E.O (E.basis k)).L.pull (eSec E.B)).U (fun _ => j k PUnit.unit) := ⟨h₁, h₂⟩
    have e := congrArg (gm f' y _) (d.unit_norm (fun k => j k PUnit.unit) k)
    have e' := ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res_pullU f' _ y _ hm _) (gm_res f' y _ hm _))).symm.trans (e.trans (map_one _))
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)).trans (e'.trans (map_one _).symm)
    · refine (gm_res_pullU' _ y _ hy _).trans ((gm_res_pullU _ _ y (le j) hy.1 _).trans ?_)
      rw [hs]
    · exact (gm_res (𝟙 _) y _ hy _).trans
        (gm_res_pullU' f' y ((rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k)) hy.2 _)
  · have hτ : (eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ≫ (splitTorus S E.X).hom =
        (splitTorus S' E.X).hom ≫ f := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)
    refine ⟨pushPt hτ τ, ?_, fun χ z => ?_⟩
    · change (τ.left ≫ eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ≫ d.i.left =
        (τ.left ≫ i.left) ≫ pullback.fst G.hom f
      exact (Category.assoc _ _ _).trans
        ((congrArg (τ.left ≫ ·) hi.symm).trans (Category.assoc _ _ _).symm)
    · have e₂ : charUnit S' E.X χ =
          pullU (eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ⊤ (charUnit S E.X χ) :=
        Units.ext (hT χ).symm
      refine Eq.trans ?_ (congrArg (gm τ.left z ⊤) e₂).symm
      exact (gm_pull τ.left _ z ⊤ trivial _).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumOfTorusCoords
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib
open GlobalTheory.CoordToExt

section
variable {S : Scheme.{0}}

theorem exists_gtDatum_of_units (E : SplitExt S) {G : Over S} [GrpObj G] (q : G ⟶ E.B) (i : splitTorus S E.X ⟶ G)
    (hq : IsMonHom q) (hi : IsMonHom i) (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q (η[E.B]))
    (s : ∀ (χ : E.X) (a : (E.O χ).L.ι), Γ(G.left, q.left ⁻¹ᵁ (E.O χ).L.U a)ˣ)
    (h₁ : ∀ (χ : E.X) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (a a' : (E.O χ).L.ι), q.left (r z) ∈ (E.O χ).L.U a →
      q.left (r z) ∈ (E.O χ).L.U a' →
      gm r z _ (s χ a') = gm (r ≫ q.left) z _ ((E.O χ).L.g a a') * gm r z _ (s χ a))
    (h₂ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (Z : Over S) (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (g.left z) ∈ (E.O χ).L.U a →
      gm ((t ≫ i) * g).left z _ (s χ a) = gm t.left z ⊤ (charUnit S E.X χ) * gm g.left z _ (s χ a))
    (h₃ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (y : (𝟙_ (Over S)).left), q.left (eSec G y) ∈ (E.O χ).L.U a →
      gm (eSec G) y _ (s χ a) * gm (𝟙 _) y _ ((E.O χ).rig.s fun _ => a) = 1) :
    ∃ d : E.GtDatum G, d.q = q ∧ d.i = i := by
  have hact : ∀ {Z : Over S} (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (((t ≫ i) * g).left z) = q.left (g.left z) := by
    intro Z t g z
    have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
      rw [MonObj.mul_comp, Category.assoc, hk.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
    exact congrArg (fun f => f.left z) e
  let u : ∀ (j : E.ChartIdx) (_k : Module.Free.ChooseBasisIndex ℤ E.X), Γ(G.left, q.left ⁻¹ᵁ E.chart j)ˣ :=
    fun j k => res (Scheme.Hom.preimage_mono q.left (E.chart_le j k)) (s _ (j k))
  have hu : ∀ (j : E.ChartIdx) k {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ E.chart j →
      gm r z (q.left ⁻¹ᵁ E.chart j) (u j k) = gm r z _ (s _ (j k)) := fun j k Z r z hz => gm_res r z _ hz _
  refine ⟨{
    q := q, i := i, q_hom := hq, i_hom := hi, q_flat := hf, q_surjective := hs, q_affine := ha, isKernel := hk
    u := u
    coord := fun j V hV h => ?_
    trans := fun j j' k => unit_ext fun y hy => ?_
    act_le := fun j y hy => (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    equiv := fun j k => unit_ext fun y hy => ?_
    unit_norm := fun j k => unit_ext fun y hy => ?_ }, rfl, rfl⟩
  · refine bijective_of_basis E.basis q i hq hi hf hs ha hk V hV _ fun k Z t g z hz => ?_
    have hz' : q.left (((t ≫ i) * g).left z) ∈ V := by rw [hact]; exact hz
    rw [gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz', gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz, hu j k _ z (h hz'), hu j k _ z (h hz)]
    exact h₂ _ _ Z t g z (E.chart_le j k (h hz))
  · refine ((gm_res _ y _ hy _).trans ((hu j' k _ y hy.2).trans
      (h₁ _ _ (𝟙 _) y (j k) (j' k) (E.chart_le j k hy.1) (E.chart_le j' k hy.2)))).trans (Eq.symm ?_)
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull (𝟙 _) q.left y (E.chart j ⊓ E.chart j') hy _).trans
      (gm_res _ y (V := E.chart j ⊓ E.chart j') _ hy _)) ((gm_res _ y _ hy _).trans (hu j k _ y hy.1)))
  · have hy' : q.left (((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y) ∈ E.chart j :=
      (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    have e := h₂ _ (j k) _ (fst _ _) (snd _ _) y (E.chart_le j k hy)
    rw [← hu j k _ y hy, ← hu j k _ y hy'] at e
    refine ((gm_res _ y _ hy _).trans ((gm_pull (𝟙 _) ((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y
      (q.left ⁻¹ᵁ E.chart j) hy' _).trans ?_)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res (𝟙 _) y _ hy _).trans
        (gm_pull (𝟙 _) (fst (splitTorus S E.X) G).left y ⊤ trivial _))
        (gm_pull (𝟙 _) (snd (splitTorus S E.X) G).left y (q.left ⁻¹ᵁ E.chart j) hy _))).symm
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
    exact e
  · refine Eq.trans ?_ ((h₃ _ (j k) y (E.chart_le j k hy.1)).trans (map_one _).symm)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ hy _).trans
      ((gm_pull (𝟙 _) (eSec G) y (q.left ⁻¹ᵁ E.chart j) hy.1 _).trans ?_)) (gm_res _ y _ hy _))
    rw [Category.id_comp]
    exact hu j k _ y hy.1

end

theorem exists_gtDatum_of_gtCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G), ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (xe : E.X ≃+ D.X) (d : E.GtDatum (thickObj R I e G)) (π : E.B.left ⟶ D.P.A.left), IsGrpPullback E.B D.P.A (thick R I e) π ∧ d.q.left ≫ π = g.pG.left ∧ (∀ χ, LBIso (E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) ∧ ∀ χ, UFib.GenWt (G := thickObj R I e G) d.i (g.t (xe χ)) χ := by
  intro R _ _ I D e G _ _ g
  have := g.q_hom
  have he : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (fun f => f.left) (IsMonHom.one_hom g.q)
  choose ρ hρ hρ' using fun χ => exists_rig g.q.left _ _ he (bundle I D e χ) (coordUnit g χ) (coordUnit_trans g χ)
  let E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    { B := thickObj R I e D.P.A
      isAbelian := isAbelianScheme_thick I D e
      X := D.X
      O := fun χ => ⟨bundle I D e χ, ρ χ, DVR.linComb_isLB _ D.P.isLB _ _, hρ χ⟩
      addIso := bundle_add I D e
      zeroTriv := bundle_zero I D e
      primitive := bundle_primitive I D e }
  obtain ⟨d, hq, hi⟩ := exists_gtDatum_of_units E g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj g.q_affine g.isKernel
    (coordUnit g) (coordUnit_trans g) (coordUnit_weight g) hρ'
  refine ⟨E, AddEquiv.refl _, d, (D.prBe I e).left, isGrpPullback_pullback D.P.A (thick R I e), ?_, fun χ => ?_,
    fun χ => ?_⟩
  · rw [hq]
    rfl
  · refine exists_iso D.P.isLB (funext fun k => ?_) Oε
    refine Eq.trans ?_ (WeightPf.Oφ_comp (D.prBe I e) (𝟙 _) χ k).symm
    rw [Category.comp_id]
  · rw [hi]
    intro Z t y z J hJ
    have v := TorusCoord.val_t_act g t y χ (𝟙 _) z J hJ
    have c : splitTorusPointsEquiv _ D.X Z t (Multiplicative.ofAdd χ) = pullU t.left ⊤ (charUnit _ D.X χ) :=
      Units.ext (splitTorusPointsEquiv_val _ _ _ t χ)
    have c' := gm_pull (𝟙 _) t.left z ⊤ trivial (charUnit _ D.X χ)
    rw [Category.id_comp] at c'
    rw [Category.id_comp, Category.id_comp, c] at v
    exact v.trans (congrArg (· * _) c')

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfComparison
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory.PsiRing

theorem exists_isPullDeg_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D.TauBimult → ∃ hD : IsPullDeg φ D D', hD.e.hom.left ≫ pullback.fst _ _ = β ∧ HEq hD.w v ∧ hD.xe = xe := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hr gam hgam hψ hB
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨W, hW, ⟨ψW⟩⟩ := PsiSpread.exists_psiOn D hB
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW W).left, gW ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem y W ⟨_, hW⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ W) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  refine ⟨⟨e, me, v, hv, hE, ?_, xe, hc, W, ψW, gam ≫ gW,
    (Category.assoc _ _ _).trans ((congrArg (gam ≫ ·) hgW).trans hgam), fun x => ?_⟩, rfl, HEq.rfl, rfl⟩
  · exact (maps_iff v _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 hr
  · obtain ⟨b, -, vb⟩ := exists_up ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (D'.psi x) (D'.psi_gen x)
    have hx : D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = gam ≫ D.xK (xe x) :=
      (Category.assoc _ _ _).trans ((congrArg (jK V ≫ ·) (hc x)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (D.c (xe x)).left) hgam.symm).trans (Category.assoc _ _ _))))
    refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · have e₁ := vb _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
      rw [pw, Fintype.prod_unique] at e₁
      refine (gm_res _ y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _)))))
      exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ y _ hy _))
    · obtain ⟨q, hq⟩ := exists_chart D'.P.isLB (D'.xK x y)
      obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
      have mp : (e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.xK x y) ∈ D.P.L.U p := hp ▸ hJ _
      have e₁ := vb _ (𝟙 _) y (fun _ => p) (fun _ => q) (Set.mem_iInter.2 fun _ => mp) (Set.mem_iInter.2 fun _ => hq)
      have e₂ := hψ x _ (𝟙 _) y (fun _ => p) (fun _ => q) (fun _ => mp) (fun _ => hq)
      have w₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) (gam ≫ lam)).trans (val_pull hJ _ _ _))
      rw [Category.assoc, Category.assoc, l₁, l₂, Category.comp_id] at w₁
      refine (val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp])).trans (e₁.trans (e₂.symm.trans
        (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
      rw [Category.id_comp, Category.id_comp]
      exact (val_of (D.psi (xe x)) gam y J (fun _ => p) (fun _ => by rw [hp, hx])).symm.trans w₁.symm

end GlobalTheory.PsiRing

end
end

