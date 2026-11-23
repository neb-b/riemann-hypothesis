module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0027
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0025

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRepPtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Thom
namespace RepPt

def specEq (U : Scheme.{0}) (B : Type) [CommRing B] : (CommRingCat.of B ⟶ Γ(U, ⊤)) ≃ (U ⟶ Spec (CommRingCat.of B)) where
  toFun φ := ΓSpec.adjunction.homEquiv U (op (CommRingCat.of B)) φ.op
  invFun f := (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f.appTop
  left_inv φ := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ
  right_inv f := by
    refine ext_to_Spec ?_
    simp only [Scheme.Γ_map, Quiver.Hom.unop_op]
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

theorem specEq_symm_apply (U : Scheme.{0}) (B : Type) [CommRing B] (f : U ⟶ Spec (CommRingCat.of B)) :
    (specEq U B).symm f = (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f.appTop := rfl

theorem appTop_specEq (U : Scheme.{0}) (B : Type) [CommRing B] (φ : CommRingCat.of B ⟶ Γ(U, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specEq U B φ).appTop = φ :=
  (specEq U B).left_inv φ

theorem symm_comp {V U : Scheme.{0}} (B : Type) [CommRing B] (f : V ⟶ U) (g : U ⟶ Spec (CommRingCat.of B)) :
    (specEq V B).symm (f ≫ g) = (specEq U B).symm g ≫ f.appTop := by
  simp only [specEq_symm_apply, Scheme.Hom.comp_appTop, Category.assoc]

theorem comp_specEq {V U : Scheme.{0}} (B : Type) [CommRing B] (f : V ⟶ U) (φ : CommRingCat.of B ⟶ Γ(U, ⊤)) :
    f ≫ specEq U B φ = specEq V B (φ ≫ f.appTop) := by
  apply (specEq V B).symm.injective
  rw [symm_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem specEq_comp_Spec (U : Scheme.{0}) {B C : Type} [CommRing B] [CommRing C]
    (ψ : CommRingCat.of B ⟶ CommRingCat.of C) (φ : CommRingCat.of C ⟶ Γ(U, ⊤)) :
    specEq U C φ ≫ Spec.map ψ = specEq U B (ψ ≫ φ) := by
  apply (specEq U B).symm.injective
  rw [Equiv.symm_apply_apply, specEq_symm_apply, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, appTop_specEq]

theorem mem_basicOpen_specEq (U : Scheme.{0}) (B : Type) [CommRing B] (φ : CommRingCat.of B ⟶ Γ(U, ⊤)) (b : B)
    (x : U) : (specEq U B φ x : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen b ↔ x ∈ U.basicOpen (φ b) := by
  have h := Scheme.preimage_basicOpen_top (specEq U B φ) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
  rw [basicOpen_eq_of_affine] at h
  have h2 : (specEq U B φ).appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) = φ b := by
    calc _ = ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specEq U B φ).appTop) b := rfl
      _ = φ b := by rw [appTop_specEq]
  rw [h2] at h
  rw [← h]
  rfl

theorem mem_off_iff {B : Type} [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B) (hJ : J = Ideal.span (Set.range S))
    (x : PrimeSpectrum B) : x ∈ off B J ↔ ∃ i, x ∈ PrimeSpectrum.basicOpen (S i) := by
  subst hJ
  change x ∉ PrimeSpectrum.zeroLocus _ ↔ _
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le, Set.range_subset_iff,
    PrimeSpectrum.mem_basicOpen, SetLike.mem_coe, not_forall]

theorem range_sub (U : Scheme.{0}) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S))
    (φ : {φ : CommRingCat.of B ⟶ Γ(U, ⊤) // ∀ p : U, ∃ i, p ∈ U.basicOpen (φ (S i))}) :
    Set.range (specEq U B φ.1) ⊆ Set.range (off B J).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨p, rfl⟩
  obtain ⟨i, hi⟩ := φ.2 p
  exact (mem_off_iff S J hJ _).2 ⟨i, (mem_basicOpen_specEq U B φ.1 _ p).2 hi⟩

def offEq (U : Scheme.{0}) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S)) :
    (U ⟶ (off B J).toScheme) ≃ {φ : CommRingCat.of B ⟶ Γ(U, ⊤) // ∀ p : U, ∃ i, p ∈ U.basicOpen (φ (S i))} where
  toFun h := ⟨(specEq U B).symm (h ≫ (off B J).ι), fun p => by
    have hp' : (h ≫ (off B J).ι) p ∈ Set.range (off B J).ι := ⟨h p, rfl⟩
    have hp : (h ≫ (off B J).ι) p ∈ off B J := by rwa [Scheme.Opens.range_ι] at hp'
    obtain ⟨i, hi⟩ := (mem_off_iff S J hJ _).1 hp
    refine ⟨i, ?_⟩
    rw [← mem_basicOpen_specEq, Equiv.apply_symm_apply]
    exact hi⟩
  invFun φ := IsOpenImmersion.lift (off B J).ι (specEq U B φ.1) (range_sub U B S J hJ φ)
  left_inv h := by
    apply (cancel_mono (off B J).ι).1
    dsimp only
    rw [IsOpenImmersion.lift_fac, Equiv.apply_symm_apply]
  right_inv φ := Subtype.ext (by
    dsimp only
    rw [IsOpenImmersion.lift_fac (off B J).ι (specEq U B φ.1) (range_sub U B S J hJ φ), Equiv.symm_apply_apply])

theorem offEq_symm_ι (U : Scheme.{0}) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S)) φ :
    (offEq U B S J hJ).symm φ ≫ (off B J).ι = specEq U B φ.1 := IsOpenImmersion.lift_fac _ _ _

theorem comp_offEq_symm {V U : Scheme.{0}} (f : V ⟶ U) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S)) φ ψ (h : ψ.1 = φ.1 ≫ f.appTop) :
    f ≫ (offEq U B S J hJ).symm φ = (offEq V B S J hJ).symm ψ := by
  rw [← cancel_mono (off B J).ι, Category.assoc, offEq_symm_ι, offEq_symm_ι, comp_specEq, h]


open MvPolynomial in
def e₂ (d : ℕ) (R : Type) [CommRing R] (U : Scheme.{0}) : Vec d 0 U × (U ⟶ Spec (CommRingCat.of R)) ≃
    {φ : CommRingCat.of (MvPolynomial (Fin d) R) ⟶ Γ(U, ⊤) // ∀ p : U, ∃ i, p ∈ U.basicOpen (φ (X i))} where
  toFun vg := ⟨CommRingCat.ofHom (eval₂Hom ((specEq U R).symm vg.2).hom vg.1.1), fun p => by
    obtain ⟨i, -, hi⟩ := vg.1.2 p
    exact ⟨i, by simpa using hi⟩⟩
  invFun φ := (⟨fun i => φ.1 (X i), fun p => (φ.2 p).imp fun _ h => ⟨Nat.zero_le _, h⟩⟩,
    specEq U R (CommRingCat.ofHom C ≫ φ.1))
  left_inv vg := by
    obtain ⟨v, g⟩ := vg
    refine Prod.ext (Subtype.ext (funext fun i => by simp)) ?_
    dsimp only
    conv_rhs => rw [← (specEq U R).apply_symm_apply g]
    congr 1
    ext r
    simp
  right_inv φ := by
    apply Subtype.ext
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp


open MvPolynomial in
def e₁ (d : ℕ) (R : Type) [CommRing R] (U : Scheme.{0}) : Vec (d + 1) 1 U × (U ⟶ Spec (CommRingCat.of R)) ≃
    {φ : CommRingCat.of (Polynomial (MvPolynomial (Fin d) R)) ⟶ Γ(U, ⊤) //
      ∀ p : U, ∃ j, p ∈ U.basicOpen (φ (Polynomial.C (X j)))} where
  toFun vg := ⟨CommRingCat.ofHom (Polynomial.eval₂RingHom
      (eval₂Hom ((specEq U R).symm vg.2).hom (fun j => vg.1.1 j.succ)) (vg.1.1 0)), fun p => by
    obtain ⟨i, hi, hp⟩ := vg.1.2 p
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (show i ≠ 0 by rintro rfl; simp at hi)
    exact ⟨j, by simpa using hp⟩⟩
  invFun φ := (⟨(Fin.cons (φ.1 Polynomial.X) (fun j => φ.1 (Polynomial.C (X j))) : Fin (d + 1) → Γ(U, ⊤)),
      fun p => by
        obtain ⟨j, hj⟩ := φ.2 p
        exact ⟨j.succ, by simp, by simpa using hj⟩⟩,
    specEq U R (CommRingCat.ofHom (Polynomial.C.comp C) ≫ φ.1))
  left_inv vg := by
    obtain ⟨v, g⟩ := vg
    refine Prod.ext (Subtype.ext (funext fun i => Fin.cases (by simp) (fun j => by simp) i)) ?_
    dsimp only
    conv_rhs => rw [← (specEq U R).apply_symm_apply g]
    congr 1
    ext r
    simp
  right_inv φ := by
    apply Subtype.ext
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i; simp
    · simp

theorem hJ (d : ℕ) (R : Type) [CommRing R] :
    (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map Polynomial.C =
      Ideal.span (Set.range fun j => (Polynomial.C (MvPolynomial.X j) : Polynomial (MvPolynomial (Fin d) R))) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

end RepPt


open RepPt in
theorem LeafRepPt_of : LeafRepPt := by
  intro d R _
  refine ⟨MvPolynomial (Fin d) R, inferInstance, Ideal.span (Set.range MvPolynomial.X), MvPolynomial.C,
    Submodule.fg_span (Set.finite_range _), off_le_C _ _,
    fun U => (e₁ d R U).trans (offEq U _ _ _ (hJ d R)).symm,
    fun U => (e₂ d R U).trans (offEq U _ _ _ rfl).symm, ?_, ?_, ?_⟩
  · intro V U f v g
    refine (comp_offEq_symm f _ _ _ (hJ d R) _ _ ?_).symm
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [e₁, symm_comp]
      · intro i; simp [e₁, Vec.map]
    · simp [e₁, Vec.map]
  · intro V U f v g
    refine (comp_offEq_symm f _ _ _ rfl _ _ ?_).symm
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp [e₂, symm_comp]
    · intro i; simp [e₂, Vec.map]
  · intro U v g
    rw [← cancel_mono (off _ _).ι, Category.assoc, Scheme.Hom.resLE_comp_ι]
    simp only [Equiv.trans_apply]
    rw [offEq_symm_ι, ← Category.assoc, offEq_symm_ι, specEq_comp_Spec]
    congr 1
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp [e₁, e₂]
    · intro i; simp [e₁, e₂, Vec.tail]

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafWLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem prod_elt_bij (A B : Spc) (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) :
    Function.Bijective (fun z : ((A ⨯ B).obj n).obj X =>
      (((prod.fst : A ⨯ B ⟶ A).app n).app X z, ((prod.snd : A ⨯ B ⟶ B).app n).app X z)) := by
  let G : Spc ⥤ Type := (evaluation _ _).obj n ⋙ (evaluation _ _).obj X
  let f := (PreservesLimitPair.iso G A B).hom ≫ (Types.binaryProductIso _ _).hom
  have hf : Function.Bijective f := (isIso_iff_bijective f).1 inferInstance
  have h1 : f ≫ TypeCat.ofHom (Prod.fst : G.obj A × G.obj B → G.obj A) = G.map prod.fst := by
    simp [f, PreservesLimitPair.iso_hom]
  have h2 : f ≫ TypeCat.ofHom (Prod.snd : G.obj A × G.obj B → G.obj B) = G.map prod.snd := by
    simp [f, PreservesLimitPair.iso_hom]
  have e : (fun z : ((A ⨯ B).obj n).obj X =>
      (((prod.fst : A ⨯ B ⟶ A).app n).app X z, ((prod.snd : A ⨯ B ⟶ B).app n).app X z)) = ⇑(ConcreteCategory.hom f) := by
    funext z
    refine Prod.ext ?_ ?_
    · exact (congrArg (fun φ => φ z) h1).symm
    · exact (congrArg (fun φ => φ z) h2).symm
  rw [e]; exact hf

def liftW {C : Type} [Category C] {d : ℕ} {U : Scheme.{0}} (F : C ⥤ Vec (d + 1) 0 U)
    (h : ∀ c, IsUnit ((F.obj c).1 0)) : C ⥤ WVec d U where
  obj c := ⟨F.obj c, h c⟩
  map f := F.map f
  map_id c := F.map_id c
  map_comp f g := F.map_comp f g

def lift1 {C : Type} [Category C] {N : ℕ} {U : Scheme.{0}} (F : C ⥤ Vec N 0 U)
    (h : ∀ c (p : U), ∃ i : Fin N, 1 ≤ i.val ∧ p ∈ U.basicOpen ((F.obj c).1 i)) : C ⥤ Vec N 1 U where
  obj c := ⟨(F.obj c).1, h c⟩
  map f := F.map f
  map_id c := F.map_id c
  map_comp f g := F.map_comp f g

theorem bo_hom {N k : ℕ} {U : Scheme.{0}} {v w : Vec N k U} (u : v ⟶ w) (i : Fin N) :
    U.basicOpen (v.1 i) = U.basicOpen (w.1 i) := by
  obtain ⟨u, hu⟩ := u
  rw [hu i, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ u.isUnit, top_inf_eq]

theorem bo_chain {N k m : ℕ} {U : Scheme.{0}} (c : ComposableArrows (Vec N k U) m) (a : Fin (m + 1)) (i : Fin N) :
    U.basicOpen ((c.obj a).1 i) = U.basicOpen ((c.obj 0).1 i) :=
  (bo_hom (c.map (homOfLE (Fin.zero_le a))) i).symm

theorem mem_bo_map {N k : ℕ} {X : Scheme.{0}} (O : X.Opens) (v : Vec N k X) (i : Fin N) (p : (O : Scheme.{0})) :
    p ∈ (O : Scheme.{0}).basicOpen (((Vec.map N k O.ι).obj v).1 i) ↔ p.val ∈ X.basicOpen (v.1 i) := by
  change p ∈ (O : Scheme.{0}).basicOpen (O.ι.appTop.hom (v.1 i)) ↔ _
  rw [← Scheme.preimage_basicOpen_top]
  rfl

theorem isUnit_of_bo {Y : Scheme.{0}} (f : Γ(Y, ⊤)) (h : ∀ p : Y, p ∈ Y.basicOpen f) : IsUnit f :=
  Y.toRingedSpace.isUnit_of_isUnit_germ ⊤ f fun x _ => (Y.mem_basicOpen_top f x).1 (h x)

theorem fst_map {A B : Spc} (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (f : X ⟶ Y) (z : ((A ⨯ B).obj n).obj X) :
    ((prod.fst : A ⨯ B ⟶ A).app n).app Y (((A ⨯ B).obj n).map f z) =
      (A.obj n).map f (((prod.fst : A ⨯ B ⟶ A).app n).app X z) :=
  NatTrans.naturality_apply ((prod.fst : A ⨯ B ⟶ A).app n) f z

theorem snd_map {A B : Spc} (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (f : X ⟶ Y) (z : ((A ⨯ B).obj n).obj X) :
    ((prod.snd : A ⨯ B ⟶ B).app n).app Y (((A ⨯ B).obj n).map f z) =
      (B.obj n).map f (((prod.snd : A ⨯ B ⟶ B).app n).app X z) :=
  NatTrans.naturality_apply ((prod.snd : A ⨯ B ⟶ B).app n) f z

theorem map_fst_app {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ)
    (z : ((A ⨯ B).obj n).obj X) :
    ((prod.fst : A' ⨯ B' ⟶ A').app n).app X (((prod.map f g).app n).app X z) =
      (f.app n).app X (((prod.fst : A ⨯ B ⟶ A).app n).app X z) := by
  have := congrArg (fun φ => (φ.app n).app X z) (prod.map_fst f g)
  simp only [NatTrans.comp_app] at this
  exact this

theorem map_snd_app {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ)
    (z : ((A ⨯ B).obj n).obj X) :
    ((prod.snd : A' ⨯ B' ⟶ B').app n).app X (((prod.map f g).app n).app X z) =
      (g.app n).app X (((prod.snd : A ⨯ B ⟶ B).app n).app X z) := by
  have := congrArg (fun φ => (φ.app n).app X z) (prod.map_snd f g)
  simp only [NatTrans.comp_app] at this
  exact this

theorem prod_ext_app {A B : Spc} (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) (z w : ((A ⨯ B).obj n).obj X)
    (h1 : ((prod.fst : A ⨯ B ⟶ A).app n).app X z = ((prod.fst : A ⨯ B ⟶ A).app n).app X w)
    (h2 : ((prod.snd : A ⨯ B ⟶ B).app n).app X z = ((prod.snd : A ⨯ B ⟶ B).app n).app X w) : z = w :=
  (prod_elt_bij A B n X).1 (Prod.ext h1 h2)

theorem LeafWLoc_of : LeafWLoc := by
  intro d R _ n X x
  let c : ComposableArrows (Vec (d + 1) 0 X) n.unop.len :=
    ((prod.fst : PR (d + 1) 0 R ⟶ Pj (d + 1) 0).app n).app (op X) x
  let s := ((prod.snd : PR (d + 1) 0 R ⟶ sp R).app n).app (op X) x
  refine ⟨Fin (d + 1), fun j => X.basicOpen ((c.obj 0).1 j), ?_, fun j => ?_⟩
  · refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨j, -, hj⟩ := (c.obj 0).2 p
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  · let O := X.basicOpen ((c.obj 0).1 j)
    let cr : ComposableArrows (Vec (d + 1) 0 O) n.unop.len := c ⋙ Vec.map (d + 1) 0 O.ι
    let sr := ((sp R).obj n).map O.ι.op s
    have hbo : ∀ a i (p : (O : Scheme.{0})), p ∈ (O : Scheme.{0}).basicOpen ((cr.obj a).1 i) ↔
        p.val ∈ X.basicOpen ((c.obj 0).1 i) := fun a i p => by
      rw [← bo_chain c a i]; exact mem_bo_map O (c.obj a) i p
    by_cases hj : j = 0
    · left
      obtain ⟨y, hy⟩ := (prod_elt_bij (Wsp d) (sp R) n (op (O : Scheme.{0}))).2
        (liftW cr (fun a => isUnit_of_bo _ fun p => (hbo a 0 p).2 (hj ▸ p.2)), sr)
      refine ⟨y, prod_ext_app _ _ _ _ ?_ ?_⟩
      · change ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app _ (((prod.map (Wincl d) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_fst_app, fst_map]
        refine (congrArg (fun w => ((Wincl d).app n).app _ w) (congrArg Prod.fst hy)).trans ?_
        rfl
      · change ((prod.snd : PR (d + 1) 0 R ⟶ _).app n).app _ (((prod.map (Wincl d) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_snd_app, snd_map]
        refine (congrArg (fun w => ((𝟙 (sp R) : sp R ⟶ sp R).app n).app _ w) (congrArg Prod.snd hy)).trans ?_
        rfl
    · right
      have hj1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.2 fun h => hj (Fin.ext h)
      obtain ⟨y, hy⟩ := (prod_elt_bij (Pj (d + 1) 1) (sp R) n (op (O : Scheme.{0}))).2
        (lift1 cr (fun a p => ⟨j, hj1, (hbo a j p).2 p.2⟩), sr)
      refine ⟨y, prod_ext_app _ _ _ _ ?_ ?_⟩
      · change ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app _
          (((prod.map (Pj.incl (d + 1)) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_fst_app, fst_map]
        refine (congrArg (fun w => ((Pj.incl (d + 1)).app n).app _ w) (congrArg Prod.fst hy)).trans ?_
        rfl
      · change ((prod.snd : PR (d + 1) 0 R ⟶ _).app n).app _
          (((prod.map (Pj.incl (d + 1)) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_snd_app, snd_map]
        refine (congrArg (fun w => ((𝟙 (sp R) : sp R ⟶ sp R).app n).app _ w) (congrArg Prod.snd hy)).trans ?_
        rfl

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.OffContLocKnxPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem span_range_mul_span_singleton {A : Type} [CommRing A] {r : ℕ} (x : Fin r → A) (f : A) :
    Ideal.span (Set.range x) * Ideal.span {f} = Ideal.span (Set.range (fun k => x k * f)) := by
  rw [Ideal.span_mul_span', Set.mul_singleton, ← Set.range_comp]
  rfl

theorem OffContLoc_of : OffContLoc := by
  intro _ r hN q A B _ _ φ x f hq J _ _ D s t hc he n i
  rw [span_range_mul_span_singleton]
  exact hN q φ (fun k => x k * f) hq J D s t hc he n i

end LateralTheory.CohomologicalPurity
end
end

