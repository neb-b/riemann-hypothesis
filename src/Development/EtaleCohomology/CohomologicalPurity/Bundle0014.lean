module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0006
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0010
public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafGenKerPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

theorem ker_specMap_mk_appTop {R : CommRingCat.{0}} (I : Ideal R) :
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom =
      I.comap (Scheme.ΓSpecIso R).hom.hom := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  calc RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom
      = RingHom.ker ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).hom).hom := by
        rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv]; rfl
    _ = RingHom.ker ((Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom := by rw [h]; rfl
    _ = _ := by rw [CommRingCat.hom_comp, ← RingHom.comap_ker, CommRingCat.hom_ofHom, Ideal.mk_ker]

theorem comap_iso_inv {A B : CommRingCat.{0}} (e : A ≅ B) (J : Ideal A) :
    J.comap e.inv.hom = J.map e.hom.hom := by
  have h := Ideal.comap_symm (I := J) e.commRingCatIsoToRingEquiv
  exact h

theorem ker_specMap_mk_top {B : CommRingCat.{0}} (IB : Ideal B) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk IB))).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      IB.comap (Scheme.ΓSpecIso B).hom.hom := by
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, ← ker_specMap_mk_appTop]
  convert Ideal.map_id _
  rw [show (homOfLE (X := (Spec (CommRingCat.of B)).Opens) (le_top (a := ⊤))).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

theorem comap_ideal_top {X : Scheme.{0}} {B : CommRingCat.{0}} (I : X.IdealSheafData) (w : Spec B ⟶ X)
    [IsOpenImmersion w] (V : X.affineOpens) (ψ : Γ(X, V.1) ⟶ B) (hle : w ''ᵁ ⊤ ≤ V.1)
    (key : X.presheaf.map (homOfLE hle).op ≫ (w.appIso ⊤).hom = ψ ≫ (Scheme.ΓSpecIso B).inv) :
    (I.comap w).ideal ⟨⊤, isAffineOpen_top _⟩ = (I.ideal V).map (ψ ≫ (Scheme.ΓSpecIso B).inv).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  rw [← Scheme.IdealSheafData.map_ideal I (U := ⟨w ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion w⟩) (V := V) hle]
  rw [comap_iso_inv, Ideal.map_map, ← CommRingCat.hom_comp]
  exact congrArg (fun f => Ideal.map (CommRingCat.Hom.hom f) (I.ideal V)) key

theorem key_gen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec)]
    (hle : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ''ᵁ ⊤ ≤ U) :
    X.presheaf.map (homOfLE hle).op ≫
      (Scheme.Hom.appIso (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ⊤).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)) ≫ (Scheme.ΓSpecIso _).inv := by
  have e : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro x _
    exact hle ⟨x, trivial, rfl⟩
  have e1 := Scheme.Hom.appLE_appIso_inv
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) e
  have h1 : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h2 : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ⁻¹ᵁ ⊤ := le_top
  have a1 : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rw [show ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h1).op : Opposite.op (⊤ : (Spec Γ(X, U)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ from Subsingleton.elim _ _]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have a2 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appLE ⊤ ⊤ h2 =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  calc _ = (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec).appLE U ⊤ e := by
        rw [← e1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ h1 h2, a1, a2, Scheme.ΓSpecIso_inv_naturality]
      rfl

theorem hle_loc {X : Scheme.{0}} (V : X.affineOpens) (r : Γ(X, V.1))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)] :
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ''ᵁ ⊤ ≤ V.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  rintro _ ⟨y, rfl⟩
  show V.2.fromSpec _ ∈ (V.1 : Set X)
  rw [← V.2.range_fromSpec]; exact ⟨_, rfl⟩

theorem LeafGenKer_of : LeafGenKer := by
  intro X Z ι _ V r
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) := by
    have h1 := Scheme.isOpenImmersion_SpecMap_localizationAway (R := Γ(X, V.1)) r
    have h2 := V.2.isOpenImmersion_fromSpec
    infer_instance
  have hle := hle_loc V r
  apply Scheme.IdealSheafData.ext_of_isAffine
  have hL := ker_specMap_mk_top (B := CommRingCat.of (Localization.Away r))
    ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))
  have hR := comap_ideal_top ι.ker _ V _ hle (key_gen V.2 r hle)
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hc := comap_iso_inv (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away r))).symm
    ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))
  simp only [Iso.symm_inv, Iso.symm_hom] at hc
  rw [hc, Ideal.map_map]
  rfl

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafGeoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.GeoPf

theorem vec_map_comp {N k : ℕ} {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (v : Vec N k X) :
    (Vec.map N k (g ≫ f)).obj v = (Vec.map N k g).obj ((Vec.map N k f).obj v) := by
  apply Subtype.ext
  funext i
  change (g ≫ f).appTop.hom (v.1 i) = g.appTop.hom (f.appTop.hom (v.1 i))
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem sch_map_pt {N k : ℕ} {Y X : Scheme.{0}} (f : Y ⟶ X) (v : Vec N k X) :
    sch.map f ≫ Pj.pt v = Pj.pt ((Vec.map N k f).obj v) := by
  ext n U g
  change (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k (g ≫ f)).obj v) =
    (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k g).obj ((Vec.map N k f).obj v))
  exact congrArg (Functor.const (Fin (n.unop.len + 1))).obj (vec_map_comp (show U.unop ⟶ Y from g) f v)

theorem part3 (d : ℕ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Fin d → A) :
    spMap φ ≫ Pj.pt (vec1 x) = Pj.pt (vec1 (φ ∘ x)) := by
  change sch.map _ ≫ _ = _
  rw [sch_map_pt]
  congr 1
  apply Subtype.ext
  funext i
  change (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) i)) =
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Fin.cons 1 (φ ∘ x) : Fin (d + 1) → B) i)
  have key := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have := congrArg (fun g => g.hom ((Fin.cons 1 x : Fin (d + 1) → A) i)) key
  refine this.symm.trans ?_
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (φ ((Fin.cons 1 x : Fin (d + 1) → A) i)) = _
  congr 1
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem part2 (q N k : ℕ) (R : Type) [CommRing R] (hq : IsUnit (q : R)) : Inv q (PR N k R) := by
  intro U ⟨y⟩
  let f : U ⟶ Spec (CommRingCat.of R) := ((prod.snd : PR N k R ⟶ sp R).app _).app (op U) y
  have h := (hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map f.appTop.hom
  rwa [map_natCast, map_natCast] at h

theorem comp_val {N k : ℕ} {U : Scheme.{0}} {a b c : Vec N k U} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = g.1 * f.1 := rfl

theorem eqToHom_val {N k : ℕ} {U : Scheme.{0}} {a b : Vec N k U} (e : a = b) : (eqToHom e).1 = 1 := by
  subst e; rfl

theorem incl_map_val {N : ℕ} {U : Scheme.{0}} {a b : Vec N 1 U} (u : a ⟶ b) : ((Vec.incl N U).map u).1 = u.1 := rfl

theorem incl_cancel {N : ℕ} {U : Scheme.{0}} {J : Type} [Category J] (F G : J ⥤ Vec N 1 U)
    (h : F ⋙ Vec.incl N U = G ⋙ Vec.incl N U) : F = G := by
  have hobj : ∀ j, F.obj j = G.obj j := fun j => Subtype.ext (by have := congrArg Subtype.val (Functor.congr_obj h j); exact this)
  refine CategoryTheory.Functor.ext hobj (fun a b f => ?_)
  apply Subtype.ext
  have h2 := congrArg Subtype.val (Functor.congr_hom h f)
  simp only [Functor.comp_map, comp_val, eqToHom_val, incl_map_val, mul_one, one_mul] at h2 ⊢
  exact h2

theorem incl_mono (N : ℕ) : Mono (Pj.incl N) := by
  have : ∀ n, Mono ((Pj.incl N).app n) := fun n => by
    have : ∀ U, Mono (((Pj.incl N).app n).app U) := fun U => by
      rw [mono_iff_injective]
      intro F G h
      exact incl_cancel (U := U.unop) F G h
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

theorem part1 (d : ℕ) (R : Type) [CommRing R] : Mono (pr d R).hom := by
  have := incl_mono (d + 1)
  change Mono (prod.map _ _)
  infer_instance

theorem pt_incl {N : ℕ} {X : Scheme.{0}} (v : Vec N 1 X) :
    Pj.pt v ≫ Pj.incl N = Pj.pt ((Vec.incl N X).obj v) := rfl

theorem part4 (d : ℕ) (A : Type) [CommRing A] (I : Ideal A) (x : Fin d → A) (hI : Ideal.span (Set.range x) = I) :
    ∃ Φ : opn (off A I) ⟶ pr d A, Φ.right = chart x := by
  let w : Vec (d + 1) 1 (off A I).toScheme := ⟨((Vec.map (d + 1) 0 (off A I).ι).obj (vec1 x)).1, fun p => by
    have hp : ¬ (Ideal.span (Set.range x) ≤ ((off A I).ι p).asIdeal) := by rw [hI]; exact p.2
    rw [Ideal.span_le] at hp
    obtain ⟨j, hj⟩ : ∃ j, x j ∉ ((off A I).ι p).asIdeal := by
      by_contra hc
      push Not at hc
      exact hp (by rintro _ ⟨j, rfl⟩; exact hc j)
    refine ⟨j.succ, by simp, ?_⟩
    change p ∈ (off A I).toScheme.basicOpen ((off A I).ι.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) j.succ)))
    rw [← Scheme.preimage_basicOpen_top]
    change (off A I).ι p ∈ (Spec (CommRingCat.of A)).basicOpen _
    rw [basicOpen_eq_of_affine]
    simp only [Fin.cons_succ]
    exact hj⟩
  refine ⟨Arrow.homMk (prod.lift (Pj.pt w) (sch.map (off A I).ι)) (chart x) ?_, rfl⟩
  apply prod.hom_ext
  · change prod.lift (Pj.pt w) (sch.map (off A I).ι) ≫ prod.map (Pj.incl (d + 1)) (𝟙 _) ≫ prod.fst =
      sch.map (off A I).ι ≫ chart x ≫ prod.fst
    rw [prod.map_fst, prod.lift_fst_assoc, chart, prod.lift_fst, pt_incl, sch_map_pt]
    rfl
  · change prod.lift (Pj.pt w) (sch.map (off A I).ι) ≫ prod.map (Pj.incl (d + 1)) (𝟙 _) ≫ prod.snd =
      sch.map (off A I).ι ≫ chart x ≫ prod.snd
    rw [prod.map_snd, prod.lift_snd_assoc, chart, prod.lift_snd]

end LateralTheory.CohomologicalPurity.Thom.GeoPf

namespace LateralTheory.CohomologicalPurity.Thom

theorem LeafGeo_of : LeafGeo :=
  ⟨GeoPf.part1, GeoPf.part2, GeoPf.part3, GeoPf.part4⟩

end LateralTheory.CohomologicalPurity.Thom

namespace LateralTheory.CohomologicalPurity.Thom.GeoPf

end LateralTheory.CohomologicalPurity.Thom.GeoPf
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHsContPfFive
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem opnMap_tri {X'' X' X : Scheme.{0}} {g : X'' ⟶ X} (a : X'' ⟶ X') (b : X' ⟶ X) (e : g = a ≫ b)
    (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens) (h : U'' ≤ g ⁻¹ᵁ U) (h1 : U'' ≤ a ⁻¹ᵁ U') (h2 : U' ≤ b ⁻¹ᵁ U) :
    opnMap g U'' U h = opnMap a U'' U' h1 ≫ opnMap b U' U h2 := by
  subst e; exact opnMap_comp _ _ _ _ _ h1 h2 h

theorem fgt_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right (tw q i) n (Hs.fgt q P n i x) := by
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp, dbl.inl_map']

theorem res_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (y : Ht q P.right n i) :
    pull _ P'.hom (tw q i) n (pull _ φ.right (tw q i) n y) = pull _ φ.left (tw q i) n (pull _ P.hom (tw q i) n y) := by
  rw [← pull_comp, ← pull_comp, ← Arrow.w φ]

theorem pull_left_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (y : Ht q P.left n i) :
    pull _ (φ ≫ ψ).left (tw q i) n y = pull _ φ.left (tw q i) n (pull _ ψ.left (tw q i) n y) := by
  rw [Arrow.comp_left, pull_comp]

theorem pull_right_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (y : Ht q P.right n i) :
    pull _ (φ ≫ ψ).right (tw q i) n y = pull _ φ.right (tw q i) n (pull _ ψ.right (tw q i) n y) := by
  rw [Arrow.comp_right, pull_comp]

theorem leafHsFive : LeafHsFive := by
  intro a1 b1 hBd q A B _ _ φ I hq J _ _ D s t hc he i hO n
  obtain ⟨δ, hδ⟩ := hBd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hqB : IsUnit (q : B) := by simpa using hq.map φ
  have hqj : ∀ j, IsUnit (q : D.obj j) := fun j => by simpa using hq.map (s.app j).hom
  have hsn : ∀ {j k : J} (f : j ⟶ k), s.app k = s.app j ≫ D.map f := fun f => by simpa using s.naturality f
  have htn : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ t.app k = t.app j := fun f => by simpa using t.naturality f
  have hD : ∀ {j k : J} (f : j ⟶ k), off (D.obj k) (I.map (s.app k).hom) ≤
      Spec.map (D.map f) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := by
    intro j k f
    have e1 := off_map (s.app k).hom I
    have e2 := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e1 e2
    rw [e1, e2, hsn f, Spec.map_comp]
    intro x hx; exact hx
  have hT : ∀ j, off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := by
    intro j
    have e1 := off_map φ I
    have e2 := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e2
    rw [e1, e2, ← he j, Spec.map_comp]
    intro x hx; exact hx
  have eT : ∀ {j k : J} (f : j ⟶ k), Spec.map (t.app j) = Spec.map (t.app k) ≫ Spec.map (D.map f) := fun f => by
    rw [← Spec.map_comp, htn f]
  have eD : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), Spec.map (D.map (f ≫ g)) = Spec.map (D.map g) ≫ Spec.map (D.map f) :=
    fun f g => by rw [← Spec.map_comp, ← Functor.map_comp]
  have sc : ∀ k : ℤ, (∀ x : Ht q (opn (off B (I.map φ))).right k i, ∃ j, ∃ y : Ht q (opn (off (D.obj j) (I.map (s.app j).hom))).right k i,
      pull _ (opnMap (Spec.map (t.app j)) _ _ (hT j)).right (tw q i) k y = x) ∧
      ∀ j (y : Ht q (opn (off (D.obj j) (I.map (s.app j).hom))).right k i),
        pull _ (opnMap (Spec.map (t.app j)) _ _ (hT j)).right (tw q i) k y = 0 →
        ∃ (l : J) (f : j ⟶ l), pull _ (opnMap (Spec.map (D.map f)) _ _ (hD f)).right (tw q i) k y = 0 :=
    fun k => spec_cont b1 q D t hc hqB hqj k i
  have ex := fun {X : Scheme.{0}} (V : X.Opens) (k : ℤ) => hδ.1 q (opn V) (opn_mono V) k i
  constructor
  · intro x
    obtain ⟨j1, y1, hy1'⟩ := (sc (m + 1)).1 (Hs.fgt q _ (m + 1) i x)
    have h2 : pull _ (opnMap (Spec.map (t.app j1)) _ _ (hT j1)).left (tw q i) (m + 1)
        (pull _ (opn (off (D.obj j1) (I.map (s.app j1).hom))).hom (tw q i) (m + 1) y1) = 0 := by
      rw [← res_pull, hy1']
      exact (ex _ (m + 1)).1.apply_apply_eq_zero x
    obtain ⟨k, f, h', hk⟩ := (hO (m + 1)).2 j1 (hT j1) _ h2
    have h3 : pull _ (opn (off (D.obj k) (I.map (s.app k).hom))).hom (tw q i) (m + 1)
        (pull _ (opnMap (Spec.map (D.map f)) _ _ h').right (tw q i) (m + 1) y1) = 0 := by
      rw [res_pull]; exact hk
    obtain ⟨z, hz⟩ := ((ex (off (D.obj k) (I.map (s.app k).hom)) (m + 1)).1 _).1 h3
    have h4 : Hs.fgt q _ (m + 1) i (x - Hs.pull q (opnMap (Spec.map (t.app k)) _ _ (hT k)) (m + 1) i z) = 0 := by
      rw [map_sub, fgt_pull, hz, ← pull_right_comp,
        ← opnMap_tri (Spec.map (t.app k)) (Spec.map (D.map f)) (eT f) _ _ _ (hT j1) (hT k) h', hy1', sub_self]
    obtain ⟨w, hw⟩ := ((ex (off B (I.map φ)) m).2.2 _).1 h4
    obtain ⟨j2, h2', w2, hw2⟩ := (hO m).1 w
    refine ⟨IsFiltered.max k j2, hT _,
      Hs.pull q (opnMap (Spec.map (D.map (IsFiltered.leftToMax k j2))) _ _ (hD _)) (m + 1) i z +
      δ q _ m i (pull _ (opnMap (Spec.map (D.map (IsFiltered.rightToMax k j2))) _ _ (hD _)).left (tw q i) m w2), ?_⟩
    rw [map_add (f := _), ← Hs.pull_comp',
      ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.leftToMax k j2))) (eT _) _ _ _ (hT k) (hT _) (hD _),
      hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), ← pull_left_comp,
      ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.rightToMax k j2))) (eT _) _ _ _ h2' (hT _) (hD _),
      hw2, hw]
    abel
  · intro j h y hy
    have hf : pull _ (opnMap (Spec.map (t.app j)) _ _ h).right (tw q i) (m + 1) (Hs.fgt q _ (m + 1) i y) = 0 := by
      rw [← fgt_pull, hy, map_zero]
    obtain ⟨k, f, hk⟩ := (sc (m + 1)).2 j _ (by exact hf)
    have h5 : Hs.fgt q _ (m + 1) i (Hs.pull q (opnMap (Spec.map (D.map f)) _ _ (hD f)) (m + 1) i y) = 0 := by
      rw [fgt_pull]; exact hk
    obtain ⟨w, hw⟩ := ((ex (off (D.obj k) (I.map (s.app k).hom)) m).2.2 _).1 h5
    have h6 : δ q _ m i (pull _ (opnMap (Spec.map (t.app k)) _ _ (hT k)).left (tw q i) m w) = 0 := by
      rw [← hδ.2.1 q _ _ (opnMap (Spec.map (t.app k)) _ _ (hT k)) (opn_mono _) (opn_mono _), hw, ← Hs.pull_comp',
        ← opnMap_tri (Spec.map (t.app k)) (Spec.map (D.map f)) (eT f) _ _ _ h (hT k) (hD f), hy]
    obtain ⟨v, hv⟩ := ((ex (off B (I.map φ)) m).2.1 _).1 h6
    obtain ⟨j3, v3, hv3'⟩ := (sc m).1 v
    have h7 : pull _ (opnMap (Spec.map (t.app (IsFiltered.max k j3))) _ _ (hT _)).left (tw q i) m
        (pull _ (opnMap (Spec.map (D.map (IsFiltered.leftToMax k j3))) _ _ (hD _)).left (tw q i) m w -
          pull _ (opn (off (D.obj (IsFiltered.max k j3)) (I.map (s.app _).hom))).hom (tw q i) m
            (pull _ (opnMap (Spec.map (D.map (IsFiltered.rightToMax k j3))) _ _ (hD _)).right (tw q i) m v3)) = 0 := by
      rw [map_sub, sub_eq_zero, ← pull_left_comp,
        ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.leftToMax k j3))) (eT _) _ _ _ (hT k) (hT _) (hD _),
        ← res_pull, ← pull_right_comp,
        ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.rightToMax k j3))) (eT _) _ _ _ (hT j3) (hT _) (hD _),
        hv3', hv]
    obtain ⟨r, g, h8, hr⟩ := (hO m).2 _ (hT _) _ h7
    refine ⟨r, f ≫ IsFiltered.leftToMax k j3 ≫ g, hD _, ?_⟩
    rw [map_sub, sub_eq_zero] at hr
    rw [opnMap_tri (Spec.map (D.map (IsFiltered.leftToMax k j3 ≫ g))) (Spec.map (D.map f)) (eD _ _) _ _ _ _ (hD _) (hD f),
      Hs.pull_comp', ← hw,
      opnMap_tri (Spec.map (D.map g)) (Spec.map (D.map (IsFiltered.leftToMax k j3))) (eD _ _) _ _ _ _ h8 (hD _),
      Hs.pull_comp', hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), hr,
      ← res_pull]
    exact (ex _ m).2.1.apply_apply_eq_zero _

theorem leafHsCont_of' (hB : LeafBd) (hE : LeafExc) (hO : LeafOffCont) : LeafHsCont :=
  leafHsCont_of hB hE hO leafHsFive

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHsSumPfR
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafDblSum : Prop := ∀ (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)),
  Nonempty (IsColimit (Cofan.mk (dbl (abv U (E := disc.obj c.pt) (disc.map π)))
    fun a => dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))))

def LeafDiscSumH : Prop := ∀ (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk (disc.obj c.pt) fun a => disc.map (c.inj a)))

theorem leafDiscSumH : LeafDiscSumH := fun A E c hc =>
  ⟨isColimitCofanMkObjOfIsColimit disc E (fun a => c.inj a)
    (hc.some.ofIsoColimit (Cofan.ext (Iso.refl _) (fun _ => by simp)))⟩

def LeafPbSum : Prop := ∀ (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)),
  Nonempty (IsColimit (Cofan.mk (abv U (E := disc.obj c.pt) (disc.map π)).left
    fun a => (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left))

theorem dbl_inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem dbl_inl_map_assoc {P' P : Arrow Spc} (φ : P' ⟶ P) {Z : Spc} (h : dbl P ⟶ Z) :
    dbl.inl P' ≫ dbl.map φ ≫ h = φ.right ≫ dbl.inl P ≫ h := by
  rw [← Category.assoc, dbl_inl_map, Category.assoc]

theorem dbl_inr_map_assoc {P' P : Arrow Spc} (φ : P' ⟶ P) {Z : Spc} (h : dbl P ⟶ Z) :
    dbl.inr P' ≫ dbl.map φ ≫ h = φ.right ≫ dbl.inr P ≫ h := by
  rw [← Category.assoc, dbl.inr_map, Category.assoc]

def dbl_cofan {A : Type} {P : Arrow Spc} (Q : A → Arrow Spc) (φ : ∀ a, Q a ⟶ P)
    (hl : IsColimit (Cofan.mk P.left fun a => (φ a).left)) (hr : IsColimit (Cofan.mk P.right fun a => (φ a).right)) :
    IsColimit (Cofan.mk (dbl P) fun a => dbl.map (φ a)) := by
  refine Cofan.IsColimit.mk _ (fun s => pushout.desc (Cofan.IsColimit.desc hr fun a => dbl.inl (Q a) ≫ s.inj a)
      (Cofan.IsColimit.desc hr fun a => dbl.inr (Q a) ≫ s.inj a) ?_) ?_ ?_
  · refine Cofan.IsColimit.hom_ext hl _ _ fun a => ?_
    have w := Arrow.w (φ a)
    have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a :=
      Cofan.IsColimit.fac hr _ a
    have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a :=
      Cofan.IsColimit.fac hr _ a
    change ((φ a).left ≫ P.hom) ≫ _ = ((φ a).left ≫ P.hom) ≫ _
    rw [w, Category.assoc, Category.assoc, f1, f2, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ s.inj a) (pushout.condition (f := (Q a).hom) (g := (Q a).hom))
  · intro s a
    have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a := by
      simpa using Cofan.IsColimit.fac hr (fun a => dbl.inl (Q a) ≫ s.inj a) a
    have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a := by
      simpa using Cofan.IsColimit.fac hr (fun a => dbl.inr (Q a) ≫ s.inj a) a
    apply pushout.hom_ext (f := (Q a).hom) (g := (Q a).hom)
    · exact (dbl_inl_map_assoc (φ a) _).trans ((congrArg _ (pushout.inl_desc _ _ _)).trans f1)
    · exact (dbl_inr_map_assoc (φ a) _).trans ((congrArg _ (pushout.inr_desc _ _ _)).trans f2)
  · intro s m hm
    apply pushout.hom_ext
    · refine Eq.trans ?_ (pushout.inl_desc _ _ _).symm
      refine Cofan.IsColimit.hom_ext hr _ _ fun a => ?_
      have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a := by
        simpa using Cofan.IsColimit.fac hr (fun a => dbl.inl (Q a) ≫ s.inj a) a
      refine Eq.trans ?_ f1.symm
      exact (dbl_inl_map_assoc (φ a) m).symm.trans (congrArg _ (hm a))
    · refine Eq.trans ?_ (pushout.inr_desc _ _ _).symm
      refine Cofan.IsColimit.hom_ext hr _ _ fun a => ?_
      have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a := by
        simpa using Cofan.IsColimit.fac hr (fun a => dbl.inr (Q a) ≫ s.inj a) a
      refine Eq.trans ?_ f2.symm
      exact (dbl_inr_map_assoc (φ a) m).symm.trans (congrArg _ (hm a))

theorem leafDblSum_of (hP : LeafPbSum) : LeafDblSum := fun X U A E c hc π π' h =>
  ⟨dbl_cofan _ _ (hP X U A E c hc π π' h).some (leafDiscSumH A E c hc).some⟩

theorem LeafHsSum_of_dbl (hS : LeafSum) (hD : LeafDblSum) (hd : LeafDiscSumH) : LeafHsSum := by
  intro q X U A E c hc π π' h n i
  have S1 := hS (ZMod q) (tw q i) A _ _ (hD X U A E c hc π π' h) n
  have S2 := hS (ZMod q) (tw q i) A _ _ (hd A E c hc) n
  constructor
  · intro x y e
    apply Subtype.ext
    apply S1.1
    funext a
    exact congrArg Subtype.val (congrFun e a)
  · intro y
    obtain ⟨x, hx⟩ := S1.2 (fun a => (y a).1)
    have hx' : ∀ a, pull _ (dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))) (tw q i) n x
        = (y a).1 := fun a => congrFun hx a
    have m : x ∈ Hs q (abv U (E := disc.obj c.pt) (disc.map π)) n i := by
      refine AddMonoidHom.mem_ker.mpr ?_
      apply S2.1
      funext a
      have e := dbl.inr_map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))
      have y0 : pull _ (dbl.inr _) (tw q i) n (y a).1 = 0 := (y a).2
      have e2 : disc.map (c.inj a) ≫ dbl.inr (abv U (E := disc.obj c.pt) (disc.map π)) =
          dbl.inr _ ≫ dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)) := e.symm
      have key : pull _ (disc.map (c.inj a) ≫ dbl.inr (abv U (E := disc.obj c.pt) (disc.map π))) (tw q i) n x = 0 := by
        exact (congrArg (fun f => pull (ZMod q) f (tw q i) n x) e2).trans ((pull_comp _ _ _ _ _ _).trans
          ((congrArg (pull (ZMod q) (dbl.inr _) (tw q i) n) (hx' a)).trans y0))
      exact ((pull_comp _ _ _ _ _ _).symm.trans key).trans (map_zero _).symm
    exact ⟨⟨x, m⟩, funext fun a => Subtype.ext (hx' a)⟩

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafSumPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut

def LeafChainsSum : Prop := ∀ (R : Type) [CommRing R] (A : Type) (E : A → Spc) (c : Cofan E), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj c.pt) fun a => (chains R).map (c.inj a)))

def LeafHKSum : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) (K : A → Cx R) (c : Cofan K),
  Nonempty (IsColimit c) → ∀ n : ℤ, Function.Bijective fun (x : HK R c.pt F n) (a : A) => HK.pull R (c.inj a) F n x

end LateralTheory.CohomologicalPurity.TubeCut.SumCut

namespace LateralTheory.CohomologicalPurity.TubeCut
open SumCut

theorem LeafSum_of (hc : LeafChainsSum) (hk : LeafHKSum) : LeafSum := by
  intro R _ F A E c hc' n
  exact hk R F A (fun a => (chains R).obj (E a)) _ (hc R A E c hc') n

end LateralTheory.CohomologicalPurity.TubeCut
end
end

