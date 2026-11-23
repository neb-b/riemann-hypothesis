module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0004
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
section
set_option maxSynthPendingDepth 1

open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization

namespace GroundTheory.Arith.SchemeCoh
universe u
noncomputable section

namespace ProjHom

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}

lemma corr_apply (g : X ⟶ Proj 𝒜) (r : A) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 r)
    (y : Away 𝒜 r) :
    corr 𝒜 g r V h y = V.topIso.inv (g.appLE _ V h (Proj.awayToSection 𝒜 r y)) := by
  rw [corr, ConcreteCategory.comp_apply, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
  have hB := congr($(Proj.basicOpenToSpec_app_top 𝒜 r) ((Scheme.ΓSpecIso _).inv y))
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hB
  have hR := congr($(Scheme.Hom.resLE_app_top g h)
    ((Proj.basicOpen 𝒜 r).topIso.inv (Proj.awayToSection 𝒜 r y)))
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hR
  erw [hB]
  exact hR


set_option backward.isDefEq.respectTransparency false in
lemma ι_appTop_eq (V : X.Opens) (z : Γ(X, ⊤)) :
    V.ι.appTop z = V.topIso.inv (X.presheaf.map (homOfLE le_top).op z) := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  congr

lemma basicOpen_awayToSection_isLocalizationElem {f g : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (he : 0 < e) :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  set U := Proj.basicOpen 𝒜 f
  have h1 : (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (Proj 𝒜).basicOpen
        (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg))) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr ((Proj 𝒜).basicOpen_le _)]
  have h2 : U.ι ⁻¹ᵁ (Proj 𝒜).basicOpen
      (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) = U.ι ⁻¹ᵁ Proj.basicOpen 𝒜 g := by
    rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen, ← SpecMap_preimage_basicOpen]
    change Proj.basicOpenToSpec 𝒜 f ⁻¹ᵁ
      (PrimeSpectrum.basicOpen (Away.isLocalizationElem hf hg) : (Spec (.of (Away 𝒜 f))).Opens) = _
    rw [← Proj.awayι_preimage_basicOpen 𝒜 hf hd hg he, ← Proj.basicOpenIsoSpec_inv_ι 𝒜 f hf hd,
      ← Scheme.Hom.comp_preimage, ← Proj.basicOpenIsoSpec_hom 𝒜 f hf hd, Iso.hom_inv_id_assoc]
  rw [h1, h2, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

end ProjHom

namespace ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

variable {A : Type u} [CommRing A] {n : ℕ}

def chartHom (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) A →+* Γ(projectiveSpace A n, Proj.basicOpen (grading A n) (X i)) :=
  (Proj.awayToSection (grading A n) (X i)).hom.comp ((polyToChart A i).comp (dehom A i))

lemma polyToChart_dehom_of_mem (i : Fin (n + 1)) {m : ℕ} {a : MvPolynomial (Fin (n + 1)) A}
    (ha : a ∈ grading A n m) :
    polyToChart A i (dehom A i a) =
      Away.mk (grading A n) (X_mem i) m a (by rwa [smul_eq_mul, mul_one]) := by
  apply HomogeneousLocalization.val_injective
  have h1 := congr($(scaleMap_eq A i) a)
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply] at h1
  rw [h1, Away.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  exact scaleMap_homog A i ha

lemma chartHom_of_mem (i : Fin (n + 1)) {m : ℕ} {a : MvPolynomial (Fin (n + 1)) A}
    (ha : a ∈ grading A n m) :
    chartHom i a = Proj.awayToSection (grading A n) (X i)
      (Away.mk (grading A n) (X_mem i) m a (by rwa [smul_eq_mul, mul_one])) := by
  rw [chartHom, RingHom.comp_apply, RingHom.comp_apply, polyToChart_dehom_of_mem i ha]

lemma chartHom_X (i j : Fin (n + 1)) :
    chartHom i (X j : MvPolynomial (Fin (n + 1)) A) = Proj.awayToSection (grading A n) (X i)
      (Away.isLocalizationElem (X_mem i) (X_mem j)) := by
  rw [chartHom_of_mem i (X_mem j)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp [Away.val_mk]

lemma chartHom_X_self (i : Fin (n + 1)) : chartHom i (X i : MvPolynomial (Fin (n + 1)) A) = 1 := by
  rw [chartHom, RingHom.comp_apply, RingHom.comp_apply, dehom_X_self, map_one, map_one]

lemma basicOpen_chartHom_X (i j : Fin (n + 1)) :
    (projectiveSpace A n).basicOpen (chartHom i (X j : MvPolynomial (Fin (n + 1)) A)) =
      Proj.basicOpen (grading A n) (X i) ⊓ Proj.basicOpen (grading A n) (X j) := by
  rw [chartHom_X]
  exact ProjHom.basicOpen_awayToSection_isLocalizationElem _ (X_mem i) one_pos (X_mem j) one_pos

lemma basicOpen_mul_le_left (j k : Fin (n + 1)) :
    Proj.basicOpen (grading A n) (X k * X j : MvPolynomial (Fin (n + 1)) A) ≤
      Proj.basicOpen (grading A n) (X k) :=
  Proj.basicOpen_mono _ _ _ ⟨_, rfl⟩

lemma basicOpen_mul_le_right (j k : Fin (n + 1)) :
    Proj.basicOpen (grading A n) (X k * X j : MvPolynomial (Fin (n + 1)) A) ≤
      Proj.basicOpen (grading A n) (X j) :=
  Proj.basicOpen_mono _ _ _ ⟨_, mul_comm _ _⟩

lemma chart_identity (j k : Fin (n + 1)) {t : ℕ} {a : MvPolynomial (Fin (n + 1)) A}
    (ha : a ∈ grading A n (t • 1)) :
    (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_right j k)).op
        (Proj.awayToSection (grading A n) (X j) (Away.mk (grading A n) (X_mem j) t a ha)) *
      (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_left j k)).op
        (chartHom k (X j)) ^ t =
    (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_left j k)).op (chartHom k a) := by
  have ha' : a ∈ grading A n t := by rwa [smul_eq_mul, mul_one] at ha
  rw [chartHom_of_mem k (X_mem j), chartHom_of_mem k ha']
  have e1 : Proj.awayToSection (grading A n) (X k * X j)
      (awayMap (grading A n) (X_mem k) (show X k * X j = X j * X k from mul_comm _ _)
        (Away.mk (grading A n) (X_mem j) t a ha)) =
      (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_right j k)).op
        (Proj.awayToSection (grading A n) (X j) (Away.mk (grading A n) (X_mem j) t a ha)) := by
    have := congr($(Proj.awayMap_awayToSection (grading A n) (X_mem k)
      (show X k * X j = X j * X k from mul_comm _ _)) (Away.mk (grading A n) (X_mem j) t a ha))
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    exact this
  have e2 : ∀ y, Proj.awayToSection (grading A n) (X k * X j)
      (awayMap (grading A n) (X_mem j) (show X k * X j = X k * X j from rfl) y) =
      (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_left j k)).op
        (Proj.awayToSection (grading A n) (X k) y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (grading A n) (X_mem j)
      (show X k * X j = X k * X j from rfl)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    exact this
  rw [← e1, ← e2, ← e2, ← map_pow, ← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, awayMap_mk,
    Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one, one_mul]
  ring

lemma map_mul_pow_eq {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {u v w : R} (t : ℕ)
    (h : u * v ^ t = w) : φ u * φ v ^ t = φ w := by
  rw [← map_pow, ← map_mul, h]

lemma X_mem_irrelevant (k : Fin (n + 1)) :
    (X k : MvPolynomial (Fin (n + 1)) A) ∈ (HomogeneousIdeal.irrelevant (grading A n)).toIdeal := by
  change X k ∈ HomogeneousIdeal.irrelevant (grading A n)
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne _ (X_mem k) one_ne_zero]

lemma map_irrelevant_eq_top {S : Type*} [CommRing S] (f : MvPolynomial (Fin (n + 1)) A →+* S)
    (k : Fin (n + 1)) (hk : IsUnit (f (X k))) :
    (HomogeneousIdeal.irrelevant (grading A n)).toIdeal.map f = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem f (X_mem_irrelevant k)) hk

lemma iSup_basicOpen_X : ⨆ j : Fin (n + 1), Proj.basicOpen (grading A n)
    (X j : MvPolynomial (Fin (n + 1)) A) = ⊤ :=
  iSup_stdOpen

theorem eq_fromOfGlobalSections_of_preimage_eq_top {O : Scheme.{u}} (q : O ⟶ projectiveSpace A n)
    (k : Fin (n + 1)) (hq : q ⁻¹ᵁ Proj.basicOpen (grading A n) (X k) = ⊤) :
    q = Proj.fromOfGlobalSections (grading A n) ((q.appLE _ ⊤ hq.ge).hom.comp (chartHom k))
      (map_irrelevant_eq_top _ k (by
        rw [RingHom.comp_apply, chartHom_X_self, map_one]
        exact isUnit_one)) := by
  set f := (q.appLE _ ⊤ hq.ge).hom.comp (chartHom k)
  have hpre : ∀ j, q ⁻¹ᵁ Proj.basicOpen (grading A n) (X j) = O.basicOpen (f (X j)) := fun j => by
    rw [RingHom.comp_apply, Scheme.basicOpen_appLE, basicOpen_chartHom_X, Scheme.Hom.preimage_inf,
      hq, top_inf_eq, top_inf_eq]
  refine ProjHom.eq_fromOfGlobalSections (𝒜 := grading A n) (ι := Fin (n + 1)) f _ (fun j => X j) (fun _ => 1)
    (fun _ => one_pos) (fun j => X_mem j) iSup_basicOpen_X q hpre fun j t a ha => ?_
  have hW : O.basicOpen (f (X j)) ≤ q ⁻¹ᵁ Proj.basicOpen (grading A n) (X k * X j) := by
    rw [Proj.basicOpen_mul, Scheme.Hom.preimage_inf, hq, top_inf_eq, hpre]
  have hk : ∀ z, O.presheaf.map (homOfLE le_top).op (f z) =
      q.appLE _ (O.basicOpen (f (X j))) (hW.trans (q.preimage_mono (basicOpen_mul_le_left j k)))
        (chartHom k z) := fun z => by
    change O.presheaf.map _ (q.appLE _ ⊤ hq.ge (chartHom k z)) = _
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
  have hk' : ∀ z, q.appLE _ (O.basicOpen (f (X j))) (hW.trans (q.preimage_mono (basicOpen_mul_le_left j k))) z =
      q.appLE _ (O.basicOpen (f (X j))) hW ((projectiveSpace A n).presheaf.map
        (homOfLE (basicOpen_mul_le_left j k)).op z) := fun z => by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
  have hj' : ∀ (h : O.basicOpen (f (X j)) ≤ q ⁻¹ᵁ Proj.basicOpen (grading A n) (X j)) z, q.appLE _ (O.basicOpen (f (X j))) h z =
      q.appLE _ (O.basicOpen (f (X j))) hW ((projectiveSpace A n).presheaf.map
        (homOfLE (basicOpen_mul_le_right j k)).op z) := fun h z => by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
  rw [ProjHom.corr_apply, ProjHom.ι_appTop_eq, ProjHom.ι_appTop_eq, hk, hk, hk', hk', hj']
  exact map_mul_pow_eq _ t (map_mul_pow_eq _ t (chart_identity j k ha))

end ProjSpace
end
end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SectionTensor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct

universe u

noncomputable section

variable {X : Scheme.{u}}

lemma bijective_app_of_factor {A B : X.Modules} (φ : A ⟶ B) {P : PMod X}
    (p : (preMod X).obj A ⟶ P) (q : P ⟶ (preMod X).obj B)
    (hq : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj q)
    (hφ : (preMod X).map φ = p ≫ q) {W : X.Opens}
    (hp : ∀ V ≤ W, Function.Bijective (p.app (op V))) :
    ∀ V ≤ W, Function.Bijective (φ.app V) := by
  obtain ⟨hq₁, hq₂⟩ := (ModulesTensor.W_toPresheaf_iff q).1 hq
  have hφapp : ∀ (V : X.Opens) (a : Γ(A, V)), φ.app V a = q.app (op V) (p.app (op V) a) :=
    fun V a => congrArg (fun g => g.app (op V) a) hφ |>.trans rfl
  have nat : ∀ {V V' : X.Opens} (i : V' ≤ V) (σ : Γ(A, V)),
      φ.app V' (A.presheaf.map (homOfLE i).op σ) = B.presheaf.map (homOfLE i).op (φ.app V σ) :=
    fun i σ => NatTrans.naturality_apply φ.mapPresheaf (homOfLE i).op σ
  have inj : ∀ V ≤ W, Function.Injective (φ.app V) := by
    intro V hV
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    rw [hφapp] at ha
    have hS := hq₁ (op V) _ ha
    rw [Opens.mem_grothendieckTopology] at hS
    apply sheaf_eq_of_locally ⟨A.presheaf, A.isSheaf⟩ (V := V)
    intro x hx
    obtain ⟨V', i, hi, hxV'⟩ := hS x hx
    refine ⟨V', i.le, hxV', ?_⟩
    have h0 : p.app (op V') (A.presheaf.map (homOfLE i.le).op a) = 0 := by
      have := PresheafOfModules.naturality_apply p (homOfLE i.le).op a
      exact this.trans hi
    apply (hp V' (i.le.trans hV)).1
    exact h0.trans (map_zero _).symm |>.trans (congrArg _ (map_zero _).symm)
  intro V hV
  refine ⟨inj V hV, fun b => ?_⟩
  have hS := hq₂ (op V) b
  rw [Opens.mem_grothendieckTopology] at hS
  choose V' i hi hxV' using hS
  choose w hw using hi
  choose a₀ ha using fun x (hx : x ∈ V) => (hp (V' x hx) ((i x hx).le.trans hV)).2 (w x hx)
  let a : ∀ x (hx : x ∈ V), Γ(A, V' x hx) := fun x hx => a₀ x hx
  have key : ∀ x hx, φ.app (V' x hx) (a x hx) = B.presheaf.map (homOfLE (i x hx).le).op b :=
    fun x hx => (hφapp _ (a x hx)).trans ((congrArg _ (ha x hx)).trans (hw x hx))
  obtain ⟨g, hg⟩ := sheaf_exists_glue ⟨A.presheaf, A.isSheaf⟩ (V := V) (ι := {x : X // x ∈ V})
    (fun c => V' c.1 c.2) (fun c => (i c.1 c.2).le) (fun x hx => ⟨⟨x, hx⟩, hxV' x hx⟩)
    (fun c => a c.1 c.2) (by
      intro c d
      apply inj _ (inf_le_left.trans ((i c.1 c.2).le.trans hV))
      change φ.app _ (A.presheaf.map _ (a c.1 c.2)) = φ.app _ (A.presheaf.map _ (a d.1 d.2))
      rw [nat, nat, key, key]
      change ((B.presheaf.map _ ≫ B.presheaf.map _) b) = ((B.presheaf.map _ ≫ B.presheaf.map _) b)
      rw [← B.presheaf.map_comp, ← B.presheaf.map_comp]
      rfl)
  refine ⟨g, ?_⟩
  apply sheaf_eq_of_locally ⟨B.presheaf, B.isSheaf⟩ (V := V)
  intro x hx
  refine ⟨V' x hx, (i x hx).le, hxV' x hx, ?_⟩
  change B.presheaf.map _ (φ.app V g) = _
  rw [← nat]
  have := hg ⟨x, hx⟩
  simp only at this
  rw [this]
  exact key x hx

def homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) : M ⟶ S :=
  inv ((sheafifyModAdj X).counit.app M) ≫ ((sheafifyModAdj X).homEquiv _ _).symm g

lemma preMod_map_homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) :
    (preMod X).map (homOfPreMod g) = g := by
  have h1 : (preMod X).map (inv ((sheafifyModAdj X).counit.app M)) =
      (sheafifyModAdj X).unit.app ((preMod X).obj M) := by
    rw [Functor.map_inv]
    exact (IsIso.eq_inv_of_inv_hom_id ((sheafifyModAdj X).right_triangle_components M)).symm
  rw [homOfPreMod, Functor.map_comp, h1, Adjunction.homEquiv_counit, Functor.map_comp,
    ← Category.assoc]
  erw [← (sheafifyModAdj X).unit.naturality g]
  rw [Category.assoc]
  erw [(sheafifyModAdj X).right_triangle_components S]
  exact Category.comp_id g

variable (M L : X.Modules) (s : Γ(L, ⊤))

def tensorSection : (preMod X).obj M ⟶ (preMod X).obj M ⊗ (preMod X).obj L :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun m => (m : ((preMod X).obj M).obj U) ⊗ₜ
            resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s
          map_zero' := zero_tmul _ _
          map_add' := fun a b => add_tmul _ _ _ }
      naturality := fun U V g => by
        ext m
        change (((preMod X).obj M).map g m) ⊗ₜ resM ((preMod X).obj L) (le_top : V.unop ≤ ⊤) s =
          (((preMod X).obj M).map g m) ⊗ₜ ((preMod X).obj L).map g
            (resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s)
        congr 1
        change ((preMod X).obj L).map (homOfLE (le_top : V.unop ≤ ⊤)).op s =
          ((preMod X).obj L).map g (((preMod X).obj L).map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
        exact PresheafOfModules.map_comp_apply ((preMod X).obj L) (homOfLE (le_top : U.unop ≤ ⊤)).op g s }
    (fun _ _ _ => rfl)

def mulSection : M ⟶ M ⊗ L :=
  homOfPreMod (tensorSection M L s ≫ tensorToSheaf M L)

lemma preMod_map_mulSection :
    (preMod X).map (mulSection M L s) = tensorSection M L s ≫ tensorToSheaf M L :=
  preMod_map_homOfPreMod _

theorem bijective_mulSection_app {W : X.Opens}
    (hs : IsBasisOn ((preMod X).obj L) W (resM ((preMod X).obj L) le_top s)) :
    ∀ V ≤ W, Function.Bijective ((mulSection M L s).app V) := by
  refine bijective_app_of_factor _ (tensorSection M L s) (tensorToSheaf M L) (W_tensorToSheaf M L)
    (preMod_map_mulSection M L s) ?_
  intro V hV
  have e0 : resM ((preMod X).obj L) hV (resM ((preMod X).obj L) le_top s) =
      resM ((preMod X).obj L) (le_top : V ≤ ⊤) s := resM_resM _ le_top hV s
  let R := X.sheaf.obj.obj (op V)
  let e : R ≃ₗ[R] ((preMod X).obj L).obj (op V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _
      (resM ((preMod X).obj L) hV (resM ((preMod X).obj L) le_top s))) (hs V hV)
  let E := (TensorProduct.rid R (((preMod X).obj M).obj (op V))).symm ≪≫ₗ
    e.lTensor (((preMod X).obj M).obj (op V))
  have hE : ∀ m, E m = (tensorSection M L s).app (op V) m := by
    intro m
    change m ⊗ₜ e 1 = m ⊗ₜ resM ((preMod X).obj L) (le_top : V ≤ ⊤) s
    congr 1
    exact (one_smul R _).trans e0
  have : ⇑((tensorSection M L s).app (op V)) = E := funext fun m => (hE m).symm
  rw [this]
  exact E.bijective

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Support
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

def Scheme.Modules.SupportedIn (F : X.Modules) (T : Set X) : Prop :=
  ∀ U : X.Opens, Disjoint (U : Set X) T → ∀ s : Γ(F, U), s = 0

namespace Scheme.Modules.SupportedIn

lemma mono {F : X.Modules} {T T' : Set X} (h : Scheme.Modules.SupportedIn F T) (hT : T ⊆ T') :
    Scheme.Modules.SupportedIn F T' :=
  fun U hU s => h U (hU.mono_right hT) s

lemma of_iso {F G : X.Modules} (e : F ≅ G) {T : Set X} (h : Scheme.Modules.SupportedIn F T) :
    Scheme.Modules.SupportedIn G T := by
  intro U hU s
  have h1 : e.inv.app U s = 0 := h U hU _
  have h2 : e.hom.app U (e.inv.app U s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [← h2, h1, map_zero]

lemma pushforward {Z : Scheme.{u}} (j : Z ⟶ X) {G : Z.Modules} {T' : Set Z}
    (h : Scheme.Modules.SupportedIn G T') :
    Scheme.Modules.SupportedIn ((Scheme.Modules.pushforward j).obj G) (j.base '' T') := by
  intro U hU s
  refine h (j ⁻¹ᵁ U) ?_ s
  rw [Set.disjoint_left]
  intro z hz hzT
  exact Set.disjoint_left.1 hU hz ⟨z, hzT, rfl⟩

end Scheme.Modules.SupportedIn

lemma isIso_of_bijective_app {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ U : X.Opens, Function.Bijective (φ.app U)) : IsIso φ := by
  have : IsIso ((Scheme.Modules.toPresheaf X).map φ) := by
    have : ∀ U : (X.Opens)ᵒᵖ, IsIso (((Scheme.Modules.toPresheaf X).map φ).app U) := fun U =>
      (ConcreteCategory.isIso_iff_bijective _).2 (h U.unop)
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)

lemma eq_zero_of_isZero {F : X.Modules} (hF : IsZero F) (U : X.Opens) (s : Γ(F, U)) : s = 0 := by
  have : (𝟙 F : F ⟶ F).app U s = (0 : F ⟶ F).app U s := by rw [hF.eq_of_src (𝟙 F) 0]
  simpa using this

section Restrict

variable {F G : X.Modules} (φ : F ⟶ G) (W : X.Opens)

lemma kernel_supportedIn (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (φ.app U)) :
    Scheme.Modules.SupportedIn (kernel φ) (W : Set X)ᶜ := by
  intro U hU s
  have hUW : U ≤ W := fun x hx => by
    by_contra hxW
    exact Set.disjoint_left.1 hU hx hxW
  apply kernel_ι_app_injective φ U
  apply (h U hUW).1
  rw [map_zero, map_zero, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    kernel.condition]
  rfl

lemma cokernel_supportedIn (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (φ.app U)) :
    Scheme.Modules.SupportedIn (cokernel φ) (W : Set X)ᶜ := by
  intro U hU s
  have hUW : U ≤ W := fun x hx => by
    by_contra hxW
    exact Set.disjoint_left.1 hU hx hxW
  let R := Scheme.Modules.restrictFunctor W.ι
  have hφ : IsIso (R.map φ) := isIso_of_bijective_app _ fun V =>
    h _ ((W.ι.image_le_opensRange V).trans (by simp))
  have hZ : IsZero (R.obj (cokernel φ)) :=
    (isZero_cokernel_of_epi (R.map φ)).of_iso (PreservesCokernel.iso R φ)
  have hE : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hUW
  have h0 : (cokernel φ).presheaf.map (eqToHom hE).op s = 0 :=
    eq_zero_of_isZero hZ (W.ι ⁻¹ᵁ U) _
  have hinv : (cokernel φ).presheaf.map (eqToHom hE.symm).op
      ((cokernel φ).presheaf.map (eqToHom hE).op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← hinv, h0, map_zero]

end Restrict

end

end GroundTheory.Arith.SchemeCoh
end

