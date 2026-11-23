module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

def IsFinFlatRk {X Y : Scheme.{0}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ ∀ y, f.finrank y = r

lemma IsFinFlatRk.of_isPullback {P X Y T : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ Y}
    {g : T ⟶ Y} (h : IsPullback fst snd f g) {r : ℕ} (hf : IsFinFlatRk f r) : IsFinFlatRk snd r := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h h1,
    MorphismProperty.of_isPullback (P := @Flat) h h2, fun y => ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback fst snd f g h y, h3]

lemma IsFinFlatRk.iso_comp {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y} {r : ℕ}
    (hf : IsFinFlatRk f r) : IsFinFlatRk (e ≫ f) r :=
  IsFinFlatRk.of_isPullback (IsPullback.of_horiz_isIso (fst := e) (g := 𝟙 Y) ⟨by simp⟩) hf

lemma isPullback_comap {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι (Scheme.IdealSheafData.subschemeMap _ _ f (I.le_map_comap f))
      f I.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by simp [Scheme.IdealSheafData.ker_subschemeι])

variable {S Z : Scheme.{0}} (z : Z ⟶ S)

def bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    pullback z k ⟶ pullback z g :=
  pullback.map z k z g (𝟙 Z) c (𝟙 S) (by simp) (by rw [Category.comp_id, w])

lemma isPullback_bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    IsPullback (bc z c g k w) (pullback.snd z k) (pullback.snd z g) c := by
  subst w
  refine IsPullback.of_right ?_ (by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]) (IsPullback.of_hasPullback z g)
  have e : bc z c g (c ≫ g) rfl ≫ pullback.fst z g = pullback.fst z (c ≫ g) := by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]
  rw [e]
  exact IsPullback.of_hasPullback z (c ≫ g)

lemma bc_id {T : Scheme.{0}} (g : T ⟶ S) (w : 𝟙 T ≫ g = g) : bc z (𝟙 T) g g w = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [bc]

lemma bc_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (m : R ⟶ S)
    (w : a ≫ g = k) (w' : b ≫ k = m) (w'' : (b ≫ a) ≫ g = m) :
    bc z (b ≫ a) g m w'' = bc z b k m w' ≫ bc z a g k w := by
  apply pullback.hom_ext <;> simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]

variable (r : ℕ)

abbrev HIdeal {T : Scheme.{0}} (g : T ⟶ S) : Type :=
  {I : (pullback z g).IdealSheafData // IsFinFlatRk (I.subschemeι ≫ pullback.snd z g) r}

abbrev HPt (T : Scheme.{0}) : Type := Σ g : T ⟶ S, HIdeal z r g

variable {z r}

def HIdeal.pull {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HIdeal z r k :=
  ⟨I.1.comap (bc z c g k w), IsFinFlatRk.of_isPullback
    ((isPullback_comap I.1 (bc z c g k w)).flip.paste_vert (isPullback_bc z c g k w)) I.2⟩

def HPt.map {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) : HPt z r T' :=
  ⟨c ≫ x.1, x.2.pull c rfl⟩

lemma HPt.map_mk {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HPt.map c ⟨g, I⟩ = ⟨k, I.pull c w⟩ := by
  subst w; rfl

lemma HPt.mk_eq_mk_iff {T : Scheme.{0}} {g : T ⟶ S} (I J : HIdeal z r g) :
    (⟨g, I⟩ : HPt z r T) = ⟨g, J⟩ ↔ I.1 = J.1 := by
  rw [Sigma.mk.inj_iff, heq_iff_eq, Subtype.ext_iff]
  simp

lemma HPt.map_eq_mk_iff {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) {k : T' ⟶ S}
    (w : c ≫ x.1 = k) (J : HIdeal z r k) :
    HPt.map c x = ⟨k, J⟩ ↔ x.2.1.comap (bc z c x.1 k w) = J.1 := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk c w, HPt.mk_eq_mk_iff]
  rfl

lemma HPt.map_id {T : Scheme.{0}} (x : HPt z r T) : HPt.map (𝟙 T) x = x := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (𝟙 T) (Category.id_comp g), HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (𝟙 T) g g _) = I.1
  rw [bc_id, Scheme.IdealSheafData.comap_id]

lemma HPt.map_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (x : HPt z r T) :
    HPt.map (b ≫ a) x = HPt.map b (HPt.map a x) := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (b ≫ a) (Category.assoc b a g), HPt.map_mk a rfl, HPt.map_mk b rfl, HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (b ≫ a) g _ _) = (I.1.comap (bc z a g _ rfl)).comap (bc z b (a ≫ g) _ rfl)
  rw [← Scheme.IdealSheafData.comap_comp, bc_comp z b a g (a ≫ g) (b ≫ a ≫ g) rfl rfl]

variable (z r)

def hilbFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := HPt z r T.unop
  map c := TypeCat.ofHom (HPt.map c.unop)
  map_id T := ConcreteCategory.hom_ext _ _ fun x => HPt.map_id x
  map_comp a b := ConcreteCategory.hom_ext _ _ fun x => HPt.map_comp _ _ x

def hilbProj : hilbFunctor z r ⟶ yoneda.obj S where
  app T := TypeCat.ofHom fun x => x.1

variable {z r}

lemma IsFinFlatRk.ker_subschemeι {T V : Scheme.{0}} {g : T ⟶ S} (v : V ⟶ pullback z g)
    [IsClosedImmersion v] (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) :
    IsFinFlatRk (v.ker.subschemeι ≫ pullback.snd z g) r := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [e, Category.assoc]
  exact hv.iso_comp _

def mkPt {T V : Scheme.{0}} (g : T ⟶ S) (v : V ⟶ pullback z g) [IsClosedImmersion v]
    (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) : HPt z r T :=
  ⟨g, v.ker, hv.ker_subschemeι v⟩

theorem comap_eq_ker_iff {X Y V : Scheme.{0}} (m : X ⟶ Y) (I : Y.IdealSheafData) (v : V ⟶ X)
    [IsClosedImmersion v] : I.comap m = v.ker ↔ ∃ w : V ⟶ I.subscheme, IsPullback v w m I.subschemeι := by
  constructor
  · intro h
    have H : I.subschemeι.ker ≤ (v ≫ m).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le, h]
    refine ⟨IsClosedImmersion.lift I.subschemeι (v ≫ m) H,
      isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ _).symm ?_⟩
    rw [Scheme.IdealSheafData.ker_subschemeι, h]
  · rintro ⟨w, hP⟩
    rw [← hP.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

end GlobalTheory.HilbGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGenerator
section
namespace GlobalTheory

theorem commuting_multiplier_eq_const_smul_generator
    (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B]
    (σ : K →+* ℂ) (rd : A →+* B)
    (hsemi : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f)
    (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A)
    [FiniteDimensional K V] [FiniteDimensional K V']
    (hV : ∀ f ∈ V, rd f ∈ R) (hV' : ∀ f ∈ V', rd f ∈ R)
    (hind : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (hind' : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (h h' : B) (hh : h ∈ R) (hh' : h' ∈ R) (hhh : h * h' = 1)
    (hsub : ∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A)))
    (T : V →ₗ[K] V') (hT : T ≠ 0)
    (hcomm : ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  classical
  have expand : ∀ (U : Submodule K A) [FiniteDimensional K U] (f : U),
      rd (f : A) = ∑ j, σ ((Module.finBasis K U).repr f j) •
        rd ((Module.finBasis K U j : U) : A) := by
    intro U _ f
    conv_lhs => rw [← (Module.finBasis K U).sum_repr f]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, hsemi]
  set bV := Module.finBasis K V with hbV
  set bV' := Module.finBasis K V' with hbV'
  let gV : Fin (Module.finrank K V) → R := fun j => ⟨rd (bV j : A), hV _ (bV j).2⟩
  let gV' : Fin (Module.finrank K V') → R := fun j => ⟨rd (bV' j : A), hV' _ (bV' j).2⟩
  have liV : LinearIndependent ℂ gV := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind _ (fun j => (bV j : A)) (fun j => (bV j).2)
      (bV.linearIndependent.map' V.subtype V.ker_subtype)
  have liV' : LinearIndependent ℂ gV' := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind' _ (fun j => (bV' j : A)) (fun j => (bV' j).2)
      (bV'.linearIndependent.map' V'.subtype V'.ker_subtype)
  let W := Submodule.span ℂ (Set.range gV)
  let W' := Submodule.span ℂ (Set.range gV')
  have eqV : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) = ∑ j, σ (bV.repr f j) • gV j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, gV]
    exact expand V f
  have eqV' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) = ∑ j, σ (bV'.repr f j) • gV' j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, gV']
    exact expand V' f
  have memW : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) ∈ W := by
    intro f
    rw [eqV f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have memW' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) ∈ W' := by
    intro f
    rw [eqV' f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  let bW : Module.Basis (Fin (Module.finrank K V)) ℂ W := Module.Basis.span liV
  have bW_apply : ∀ j, (bW j : R) = gV j := fun j => congrArg Subtype.val (Module.Basis.span_apply liV j)
  let img : Fin (Module.finrank K V) → W' := fun j => ⟨⟨rd (T (bV j) : A), hV' _ (T (bV j)).2⟩, memW' (T (bV j))⟩
  let Tc : W →ₗ[ℂ] W' := bW.constr ℂ img
  have Tc_rd : ∀ f : V, Tc ⟨⟨rd f, hV _ f.2⟩, memW f⟩ = ⟨⟨rd (T f : A), hV' _ (T f).2⟩, memW' (T f)⟩ := by
    intro f
    have e1 : (⟨⟨rd f, hV _ f.2⟩, memW f⟩ : W) = ∑ j, σ (bV.repr f j) • bW j := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, bW_apply]
      exact eqV f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    simp only [map_smul, Tc, Module.Basis.constr_basis]
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul, img]
    conv_rhs => rw [← bV.sum_repr f]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hsemi]
  have Tc_basis : ∀ i, Tc (bW i) = img i := fun i => by
    simp only [Tc, Module.Basis.constr_basis]
  haveI : FiniteDimensional ℂ W := Module.Finite.of_basis bW
  have Tc_ne : Tc ≠ 0 := by
    obtain ⟨f, hf⟩ : ∃ f, T f ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hT (LinearMap.ext hc)
    have hfA : (T f : A) ≠ 0 := fun hz => hf (Subtype.ext hz)
    have li1 : LinearIndependent ℂ (fun _ : Fin 1 => rd (T f : A)) :=
      hind' 1 (fun _ => (T f : A)) (fun _ => (T f).2)
        (linearIndependent_unique_iff.mpr hfA)
    have hne : rd (T f : A) ≠ 0 := li1.ne_zero 0
    intro h0
    apply hne
    have := congrArg (fun x : W' => ((x : R) : B)) (Tc_rd f)
    simp only [h0, LinearMap.zero_apply] at this
    simpa using this.symm
  have spanLe : Submodule.span ℂ (rd '' (V : Set A)) ≤ W.map R.val.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨rd f, hV _ hf⟩, memW ⟨f, hf⟩, rfl⟩
  have hW'W : ∀ w ∈ W', (⟨h', hh'⟩ : R) * w ∈ W := by
    intro w hw
    have hle : W' ≤ W.comap (LinearMap.mulLeft ℂ (⟨h', hh'⟩ : R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show (⟨h', hh'⟩ : R) * gV' i ∈ W
      obtain ⟨z, hz, hzeq⟩ := spanLe (hsub _ (bV' i).2)
      have : z = (⟨h', hh'⟩ : R) * gV' i := Subtype.ext hzeq
      rw [← this]; exact hz
    exact hle hw
  have hcommTc : ∀ x y : W, ((Tc x : R)) * (y : R) = (x : R) * (Tc y : R) := by
    let B1 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ (W'.subtype ∘ₗ Tc) W.subtype
    let B2 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ W.subtype (W'.subtype ∘ₗ Tc)
    have hB : B1 = B2 := by
      refine bW.ext fun i => bW.ext fun j => ?_
      simp only [B1, B2, LinearMap.compl₁₂_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mul_apply', Tc_basis, bW_apply]
      apply Subtype.ext
      simp only [img, gV, Subalgebra.coe_mul, ← map_mul]
      rw [hcomm]
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simpa [B1, B2] using this
  have hhhR : (⟨h, hh⟩ : R) * ⟨h', hh'⟩ = 1 := Subtype.ext (by simpa using hhh)
  obtain ⟨a, ha, hkey⟩ := commuting_map_eq_smul_multiplier R W W' ⟨h, hh⟩ ⟨h', hh'⟩ hhhR hW'W Tc Tc_ne hcommTc
  refine ⟨a, ha, fun f => ?_⟩
  have := congrArg Subtype.val (hkey ⟨⟨rd f, hV _ f.2⟩, memW f⟩)
  rw [Tc_rd] at this
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
section
open NumberField IsDedekindDomain

namespace GlobalTheory.UnramCompositum

theorem card_inertia (k N : Type) [Field k] [NumberField k] [Field N] [NumberField N]
    [Algebra k N] [IsGalois k N] (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    Nat.card (Q.inertia (N ≃ₐ[k] N)) = Q.ramificationIdx (𝓞 k) := by
  have : IsGaloisGroup (N ≃ₐ[k] N) (𝓞 k) (𝓞 N) := IsGaloisGroup.of_isFractionRing _ _ _ k N
  have hpr : (Q.under (𝓞 k)).IsPrime := Ideal.IsPrime.under _ Q
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[k] N) (Q.under (𝓞 k)) Q
  rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 k)) Q (N ≃ₐ[k] N)] at hcard

theorem ramificationIdx_eq_one_iff_fix (k E N : Type) [Field k] [NumberField k] [Field E] [NumberField E]
    [Field N] [NumberField N] [Algebra k E] [Algebra k N] [Algebra E N] [IsScalarTower k E N] [IsGalois k N]
    (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    (Q.under (𝓞 E)).ramificationIdx (𝓞 k) = 1 ↔
      ∀ τ : N ≃ₐ[k] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) → ∀ y : E, τ (algebraMap E N y) = algebraMap E N y := by
  haveI : IsGalois E N := IsGalois.tower_top_of_isGalois k E N
  have h1 := card_inertia k N Q
  have h2 := card_inertia E N Q
  have h3 : Q.ramificationIdx (𝓞 k) = (Q.under (𝓞 E)).ramificationIdx (𝓞 k) * Q.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (Q.under (𝓞 E)) Q
  have h4 : 0 < Q.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos (R := 𝓞 E) Q
  let f : Q.inertia (N ≃ₐ[E] N) → Q.inertia (N ≃ₐ[k] N) := fun σ =>
    ⟨σ.1.restrictScalars k, AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp σ.2 x⟩
  have hf : Function.Injective f := fun σ σ' h =>
    Subtype.ext (AlgEquiv.restrictScalars_injective k (congrArg Subtype.val h))
  constructor
  · intro h τ hτ y
    have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [h1, h2, h3, h, one_mul])
    obtain ⟨σ, hσ⟩ := hb.2 ⟨τ, AddSubgroup.mem_inertia.mpr hτ⟩
    have : σ.1.restrictScalars k = τ := congrArg Subtype.val hσ
    rw [← this]
    exact σ.1.commutes y
  · intro h
    have hs : Function.Surjective f := fun τ =>
      ⟨⟨{ τ.1.toRingEquiv with commutes' := h τ.1 (AddSubgroup.mem_inertia.mp τ.2) },
        AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp τ.2 x⟩, rfl⟩
    have hc := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    rw [h1, h2, h3] at hc
    exact Nat.eq_of_mul_eq_mul_right h4 (by rw [one_mul]; exact hc.symm)

theorem exists_galois_above (K : Type) [Field K] [NumberField K] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra K N), IsGalois ℚ N := by
  have : IsAlgClosure ℚ (AlgebraicClosure K) := IsAlgClosure.ofAlgebraic ℚ K (AlgebraicClosure K)
  have : IsGalois ℚ (AlgebraicClosure K) := ⟨⟩
  have : NumberField (IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) := ⟨⟩
  exact ⟨IntermediateField.normalClosure ℚ K (AlgebraicClosure K), inferInstance, inferInstance, inferInstance,
    IsGalois.normalClosure ℚ K (AlgebraicClosure K)⟩

theorem exists_valuation_eq (F F' K : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K]
    [NumberField K] [Algebra F K] [Algebra F' K]
    (hgen : ∀ (N : Type) [Field N] (f g : K →+* N), (∀ x : F, f (algebraMap F K x) = g (algebraMap F K x)) →
      (∀ x : F', f (algebraMap F' K x) = g (algebraMap F' K x)) → f = g)
    (q : ℕ) (hq : q.Prime) (hd : ¬ (q : ℤ) ∣ discr F') (w : HeightOneSpectrum (𝓞 F))
    (hw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ∀ a : F, 𝔭.valuation K (algebraMap F K a) = w.valuation F a := by
  obtain ⟨N, _, _, _, hN⟩ := exists_galois_above K
  letI : Algebra F N := ((algebraMap K N).comp (algebraMap F K)).toAlgebra
  letI : Algebra F' N := ((algebraMap K N).comp (algebraMap F' K)).toAlgebra
  have : IsScalarTower F K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois F N := IsGalois.tower_top_of_isGalois ℚ F N
  have := w.isMaximal
  obtain ⟨Q, hQ, hQw⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) w.asIdeal
  have hqQ : ((q : ℕ) : 𝓞 N) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q w.asIdeal _).1 hw
    rwa [map_natCast] at this
  have hu : Algebra.IsUnramifiedAt ℤ (Q.under (𝓞 F')) :=
    (not_dvd_discr_iff_forall_mem F' (𝓞 F') (Nat.prime_iff_prime_int.1 hq)).1 hd _ inferInstance (by
      rw [Ideal.under, Ideal.mem_comap, map_intCast, Int.cast_natCast]; exact hqQ)
  have hu' : Algebra.IsUnramifiedAt (𝓞 ℚ) (Q.under (𝓞 F')) := Algebra.IsUnramifiedAt.of_restrictScalars ℤ _
  have hfix := (ramificationIdx_eq_one_iff_fix ℚ F' N Q).1 (Ideal.ramificationIdx_eq_one _ _)
  have he : (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = 1 := by
    refine (ramificationIdx_eq_one_iff_fix F K N Q).2 fun τ hτ y => ?_
    exact RingHom.congr_fun (hgen N ((τ : N →+* N).comp (algebraMap K N)) (algebraMap K N)
      (fun x => τ.commutes x) (fun x => hfix (τ.restrictScalars ℚ) hτ x)) y
  have hlo : (Q.under (𝓞 K)).LiesOver w.asIdeal := Ideal.LiesOver.tower_bot Q _ _
  let 𝔭 : HeightOneSpectrum (𝓞 K) :=
    ⟨Q.under (𝓞 K), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot _⟩
  have hlo' : 𝔭.asIdeal.LiesOver w.asIdeal := hlo
  refine ⟨𝔭, fun a => ?_⟩
  rw [← HeightOneSpectrum.valuation_liesOver K w 𝔭 a]
  change _ ^ (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = _
  rw [he, pow_one]


open Formalism.L2.Pj in
theorem exists_vLa_eq : ∀ (F F' K : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField K]
    (hF : F ≤ K), K = F ⊔ F' → ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ discr F' → ∀ w : HeightOneSpectrum (𝓞 F),
    ((q : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ 𝔭 : HeightOneSpectrum (𝓞 K),
      ∀ a : F, vLa 𝔭 (IntermediateField.inclusion hF a) = vLa w a := by
  intro F F' K _ _ _ hF hK q hq hd w hw
  have hF' : F' ≤ K := hK ▸ le_sup_right
  letI : Algebra F K := (IntermediateField.inclusion hF).toRingHom.toAlgebra
  letI : Algebra F' K := (IntermediateField.inclusion hF').toRingHom.toAlgebra
  obtain ⟨𝔭, h⟩ := exists_valuation_eq F F' K (fun N _ f g h1 h2 => by
    let T : Subfield ℂ := (RingHom.eqLocusField f g).map (K.val : K →+* ℂ)
    let S : IntermediateField ℚ ℂ := T.toIntermediateField fun x => by
      rw [eq_ratCast]; exact SubfieldClass.ratCast_mem T x
    have hle : K ≤ S := by
      refine hK.le.trans (sup_le (fun x hx => ⟨⟨x, hF hx⟩, h1 ⟨x, hx⟩, rfl⟩)
        (fun x hx => ⟨⟨x, hF' hx⟩, h2 ⟨x, hx⟩, rfl⟩))
    ext z
    obtain ⟨y, hy, hyz⟩ := hle z.2
    have hyz' : y = z := Subtype.ext hyz
    subst hyz'
    exact hy) q hq hd w hw
  exact ⟨𝔭, fun a => congrArg (fun t => -WithZero.log t) (h a)⟩

end GlobalTheory.UnramCompositum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffTsumOfLocallySummableBoundsStatement
section
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds : ∀ {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ), (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i)) → (∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧ ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  first | exact @GlobalTheory.contDiff_tsum_of_locally_summable_bounds | exact GlobalTheory.contDiff_tsum_of_locally_summable_bounds | (intros; apply GlobalTheory.contDiff_tsum_of_locally_summable_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterCocycleTrivialNearZero
section
noncomputable section

namespace GlobalTheory.CocycleChar

theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.InductiveNormBound.main
  | exact _root_.GlobalTheory.InductiveNormBound.main
  | (apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InductiveNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InductiveNormBound.main ..)

theorem cocycle_char_trivial_near_zero :
    ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  intro A V _ _ _ _ _ _ _ _ lam hlam ε ⟨N, hN, hεN⟩ hε0 χ hχ hker hmul
  have hχ0 : χ 0 = 1 := hker 0 (map_zero lam)

  have hW : lam ⁻¹' N ∩ {a : A | ‖χ a - 1‖ < 1 / 2} ∈ nhds (0 : A) := by
    refine Filter.inter_mem ?_ ?_
    · exact hlam.continuousAt.preimage_mem_nhds (by simpa using hN)
    · exact (isOpen_lt (hχ.sub continuous_const).norm continuous_const).mem_nhds (by simp [hχ0])
  obtain ⟨K₀, hK₀⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  have hpow : ∀ a ∈ K₀, ∀ n : ℕ, χ (n • a) = χ a ^ n := by
    intro a ha n
    induction n with
    | zero => simp [hχ0]
    | succ n ih =>
      have h1 : n • a ∈ K₀ := K₀.toAddSubgroup.nsmul_mem ha n
      rw [succ_nsmul, hmul, ih, hεN _ (hK₀ h1).1 _ (hK₀ ha).1, pow_succ, mul_one]
  have hK₀one : ∀ a ∈ K₀, χ a = 1 := by
    intro a ha
    refine pow_near_one fun n => ?_
    rw [← hpow a ha n]
    exact (hK₀ (K₀.toAddSubgroup.nsmul_mem ha n)).2

  set S : AddSubgroup A := K₀.toAddSubgroup ⊔ lam.ker with hSdef
  have hSopen : IsOpen (S : Set A) :=
    AddSubgroup.isOpen_mono (le_sup_left : K₀.toAddSubgroup ≤ S) K₀.isOpen
  set C : Set A := (S : Set A)ᶜ
  have hCc : IsCompact C := hSopen.isClosed_compl.isCompact
  have hLc : IsClosed (lam '' C) := (hCc.image hlam).isClosed
  have h0 : (0 : V) ∉ lam '' C := by
    rintro ⟨c, hc, hc0⟩
    exact hc (le_sup_right (a := K₀.toAddSubgroup) (AddMonoidHom.mem_ker.2 hc0))
  refine ⟨(lam '' C)ᶜ, hLc.isOpen_compl.mem_nhds h0, fun a ha => ?_⟩
  have haS : a ∈ S := by
    by_contra h
    exact ha ⟨a, h, rfl⟩
  obtain ⟨k, hk, n, hn, rfl⟩ := AddSubgroup.mem_sup.1 haS
  rw [AddMonoidHom.mem_ker] at hn
  rw [hmul, hK₀one k hk, hker n hn, hn, hε0, mul_one, mul_one]

end GlobalTheory.CocycleChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestr
section
open IsDedekindDomain

namespace GlobalTheory.LKTrip

theorem AfP.continuous_restr (p : ℕ) : Continuous (AfP.restr p) :=
  RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ) Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ RingHom.id _) (Filter.Eventually.of_forall fun _ ↦ Set.mapsTo_id _)
    (fun _ ↦ continuous_id)

end GlobalTheory.LKTrip
end

