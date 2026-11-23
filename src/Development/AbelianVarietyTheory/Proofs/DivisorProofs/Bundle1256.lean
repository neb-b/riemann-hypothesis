module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSlotsGlobal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1062
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchExistsExtendBasicOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Pinch

open TopologicalSpace

theorem appLE_congr_hom {X Y : Scheme.{0}} {φ ψ : X ⟶ Y} (h : φ = ψ) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ φ ⁻¹ᵁ U) (e' : V ≤ ψ ⁻¹ᵁ U) : φ.appLE U V e = ψ.appLE U V e' := by
  subst h; rfl

theorem resLE_comp_of_ringHom {T P X : Scheme.{0}} (V : T.Opens) (hV : IsAffineOpen V) (U : X.affineOpens)
    (ρ : Γ(X, U.1) ⟶ Γ(T, V)) (i : P ⟶ T) (hP : IsAffineOpen (i ⁻¹ᵁ V)) (x : P ⟶ X)
    (hx : i ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1) (h : ρ ≫ i.appLE V _ le_rfl = x.appLE U.1 _ hx) :
    i.resLE _ _ le_rfl ≫ (hV.isoSpec.hom ≫ Spec.map ρ ≫ U.2.fromSpec) = (i ⁻¹ᵁ V).ι ≫ x := by
  rw [← cancel_epi hP.isoSpec.inv]
  have e1 : hP.isoSpec.inv ≫ i.resLE V _ le_rfl ≫ hV.isoSpec.hom = Spec.map (i.appLE V _ le_rfl) := by
    rw [← cancel_mono hV.isoSpec.inv, ← cancel_mono V.ι]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  calc hP.isoSpec.inv ≫ i.resLE V _ le_rfl ≫ hV.isoSpec.hom ≫ Spec.map ρ ≫ U.2.fromSpec
      = (hP.isoSpec.inv ≫ i.resLE V _ le_rfl ≫ hV.isoSpec.hom) ≫ Spec.map ρ ≫ U.2.fromSpec := by
        simp only [Category.assoc]
    _ = Spec.map (x.appLE U.1 _ hx) ≫ U.2.fromSpec := by
        rw [e1, ← Category.assoc, ← Spec.map_comp, h]
    _ = hP.isoSpec.inv ≫ (i ⁻¹ᵁ V).ι ≫ x := by
        rw [IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 hP, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]

theorem exists_glue_of_sections {T P Q X : Scheme.{0}} (i : P ⟶ T) (j : Q ⟶ T)
    (V : T.Opens) (hV : IsAffineOpen V) (hVP : IsAffineOpen (i ⁻¹ᵁ V)) (hVQ : IsAffineOpen (j ⁻¹ᵁ V))
    (U : X.affineOpens) (x : P ⟶ X) (z : Q ⟶ X) (hx : i ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1) (hz : j ⁻¹ᵁ V ≤ z ⁻¹ᵁ U.1)
    (hinj : ∀ t₁ t₂ : Γ(T, V), i.appLE V (i ⁻¹ᵁ V) le_rfl t₁ = i.appLE V (i ⁻¹ᵁ V) le_rfl t₂ →
      j.appLE V (j ⁻¹ᵁ V) le_rfl t₁ = j.appLE V (j ⁻¹ᵁ V) le_rfl t₂ → t₁ = t₂)
    (hex : ∀ u : Γ(X, U.1), ∃ t : Γ(T, V), i.appLE V (i ⁻¹ᵁ V) le_rfl t = x.appLE U.1 _ hx u ∧
      j.appLE V (j ⁻¹ᵁ V) le_rfl t = z.appLE U.1 _ hz u) :
    ∃ g : V.toScheme ⟶ X, i.resLE _ _ le_rfl ≫ g = (i ⁻¹ᵁ V).ι ≫ x ∧
      j.resLE _ _ le_rfl ≫ g = (j ⁻¹ᵁ V).ι ≫ z := by
  choose ρf hρ using hex
  let ρ : Γ(X, U.1) →+* Γ(T, V) :=
    { toFun := ρf
      map_one' := hinj _ _ (by rw [(hρ 1).1, map_one, map_one]) (by rw [(hρ 1).2, map_one, map_one])
      map_mul' := fun a b => hinj _ _ (by rw [map_mul, (hρ _).1, (hρ _).1, (hρ _).1, map_mul])
        (by rw [map_mul, (hρ _).2, (hρ _).2, (hρ _).2, map_mul])
      map_zero' := hinj _ _ (by rw [(hρ 0).1, map_zero, map_zero]) (by rw [(hρ 0).2, map_zero, map_zero])
      map_add' := fun a b => hinj _ _ (by rw [map_add (f := _), (hρ _).1, (hρ _).1, (hρ _).1, map_add (f := _)])
        (by rw [map_add (f := _), (hρ _).2, (hρ _).2, (hρ _).2, map_add (f := _)]) }
  refine ⟨hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ) ≫ U.2.fromSpec, ?_, ?_⟩
  · exact resLE_comp_of_ringHom V hV U _ i hVP x hx (by ext u; exact (hρ u).1)
  · exact resLE_comp_of_ringHom V hV U _ j hVQ z hz (by ext u; exact (hρ u).2)

theorem isLocalization_away_of_eq {Y : Scheme.{0}} [IsAffine Y] (r : Γ(Y, ⊤)) (W : Y.Opens)
    (hW : W = Y.basicOpen r) :
    letI := (Y.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom.toAlgebra
    IsLocalization.Away r Γ(Y, W) := by
  subst hW
  exact (isAffineOpen_top Y).isLocalization_basicOpen r

theorem appLE_comp_res {Y Z : Scheme.{0}} (g : Y ⟶ Z) (V : Z.Opens) (W : Y.Opens) (e : W ≤ g ⁻¹ᵁ V) :
    (g.appLE V W e).hom.comp (Z.presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom =
      (Y.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom.comp g.appTop.hom := by
  have h : Z.presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ g.appLE V W e =
      g.appTop ≫ Y.presheaf.map (homOfLE le_top : W ⟶ ⊤).op := by
    rw [Scheme.Hom.map_appLE]
    simp only [Scheme.Hom.appLE]
    rfl
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, h]

theorem appTop_spMap_apply {S S' : Type} [CommRing S] [CommRing S'] (g : S →+* S') (t : Γ(Sp S, ⊤)) :
    (spMap g).appTop.hom t = (Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom
      (g ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom t)) := by
  have := congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [← this]
  simp

section
variable {R : Type} [CommRing R] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M] {β : TrivSqZeroExt R M →+* TrivSqZeroExt B M}

theorem sum_apply (hβ : IsSum β (algebraMap R B) id) (a : TrivSqZeroExt R M) :
    β a = TrivSqZeroExt.inl (algebraMap R B a.fst) + TrivSqZeroExt.inr a.snd := by
  conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
  rw [map_add (f := _), hβ.1, hβ.2]
  rfl

theorem sum_fst (hβ : IsSum β (algebraMap R B) id) (a : TrivSqZeroExt R M) :
    (β a).fst = algebraMap R B a.fst := by
  rw [sum_apply hβ]; simp

theorem sum_snd (hβ : IsSum β (algebraMap R B) id) (a : TrivSqZeroExt R M) :
    (β a).snd = a.snd := by
  rw [sum_apply hβ]; simp

theorem spMap_square (hβ : IsSum β (algebraMap R B) id) :
    spMap (algebraMap R B) ≫ spMap (TrivSqZeroExt.fstHom R R M).toRingHom =
      spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap β := by
  simp only [spMap, ← Spec.map_comp]
  congr 1
  ext a
  simp [sum_fst hβ]

end

theorem iso_inv_inj {S S' : CommRingCat.{0}} (e : S ≅ S') {y y' : S'} : e.inv.hom y = e.inv.hom y' ↔ y = y' := by
  constructor
  · intro h
    have := congrArg e.hom.hom h
    simpa using this
  · intro h; rw [h]

theorem exists_extend_basicOpen : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∀ (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)) (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s ≤ x ⁻¹ᵁ U.1 → ∃ g : ((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ x ∧ (spMap β).resLE _ _ le_rfl ≫ g = (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ z := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x z hxz s U hx
  have hsq := spMap_square hβ
  have hpt : ∀ w : Sp B, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom) ((spMap (algebraMap R B)) w) =
      (spMap β) ((spMap (TrivSqZeroExt.fstHom B B M).toRingHom) w) := fun w => by
    have := congrArg (fun q : Sp B ⟶ Sp (TrivSqZeroExt R M) => q w) hsq
    simpa using this
  have hz : spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s ≤ z ⁻¹ᵁ U.1 := by
    intro q hq
    obtain ⟨w, rfl⟩ := spMap_fst_surjective B M q
    have h1 : (spMap (algebraMap R B)) w ∈
        spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s := by
      rw [Scheme.Hom.mem_preimage, hpt]; exact hq
    have h2 := hx h1
    rw [Scheme.Hom.mem_preimage] at h2 ⊢
    have e : z ((spMap (TrivSqZeroExt.fstHom B B M).toRingHom) w) = x ((spMap (algebraMap R B)) w) := by
      have := congrArg (fun q : Sp B ⟶ X => q w) hxz
      simpa using this
    rw [e]; exact h2
  have hW : spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s) ≤
      spMap (TrivSqZeroExt.fstHom B B M).toRingHom ⁻¹ᵁ (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) := by
    intro w hw
    simp only [Scheme.Hom.mem_preimage] at hw ⊢
    rw [← hpt]; exact hw
  have hV : IsAffineOpen ((Sp (TrivSqZeroExt R M)).basicOpen s) := (isAffineOpen_top _).basicOpen s
  have hVP : IsAffineOpen (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) := by
    rw [Scheme.preimage_basicOpen]; exact (isAffineOpen_top _).basicOpen _
  have hVQ : IsAffineOpen (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) := by
    rw [Scheme.preimage_basicOpen]; exact (isAffineOpen_top _).basicOpen _
  have hcomm : (spMap (algebraMap R B)).appTop.hom.comp (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom =
      (spMap (TrivSqZeroExt.fstHom B B M).toRingHom).appTop.hom.comp (spMap β).appTop.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hsq]
  have hinj0 : ∀ a, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom a = 0 →
      (spMap β).appTop.hom a = 0 → a = 0 := by
    intro a h1 h2
    rw [appTop_spMap_apply, ← map_zero (Scheme.ΓSpecIso _).inv.hom, iso_inv_inj] at h1 h2
    have e : (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).hom.hom a = 0 := by
      ext
      · simpa using h1
      · rw [← sum_snd hβ]
        simpa using congrArg TrivSqZeroExt.snd h2
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv.hom e
    simpa using this
  have hsurj0 : ∀ r c, (spMap (algebraMap R B)).appTop.hom r =
      (spMap (TrivSqZeroExt.fstHom B B M).toRingHom).appTop.hom c →
      ∃ a, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom a = r ∧ (spMap β).appTop.hom a = c := by
    intro r c h
    rw [appTop_spMap_apply, appTop_spMap_apply, iso_inv_inj] at h
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv.hom
      (TrivSqZeroExt.inl ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) +
        TrivSqZeroExt.inr ((Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt B M))).hom.hom c).snd : TrivSqZeroExt R M), ?_, ?_⟩
    · rw [appTop_spMap_apply]
      simp
    · rw [appTop_spMap_apply]
      have e : β (TrivSqZeroExt.inl ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) +
          TrivSqZeroExt.inr ((Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt B M))).hom.hom c).snd) =
          (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt B M))).hom.hom c := by
        rw [map_add (f := _), hβ.1, hβ.2]
        ext
        · simpa using h
        · simp
      simp [e]
  letI : Algebra Γ(Sp R, ⊤) Γ(Sp R, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    ((Sp R).presheaf.map (homOfLE le_top : spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s ⟶ ⊤).op).hom.toAlgebra
  letI : Algebra Γ(Sp (TrivSqZeroExt B M), ⊤) Γ(Sp (TrivSqZeroExt B M), spMap β ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    ((Sp (TrivSqZeroExt B M)).presheaf.map (homOfLE le_top : spMap β ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s ⟶ ⊤).op).hom.toAlgebra
  letI : Algebra Γ(Sp B, ⊤) Γ(Sp B, spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s)) :=
    ((Sp B).presheaf.map (homOfLE le_top : spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s) ⟶ ⊤).op).hom.toAlgebra
  haveI : IsLocalization.Away ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom s)
      Γ(Sp R, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    isLocalization_away_of_eq _ _ (Scheme.preimage_basicOpen _ s)
  haveI : IsLocalization.Away ((spMap β).appTop.hom s)
      Γ(Sp (TrivSqZeroExt B M), spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    isLocalization_away_of_eq _ _ (Scheme.preimage_basicOpen _ s)
  haveI : IsLocalization.Away ((spMap (algebraMap R B)).appTop.hom
      ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom s))
      Γ(Sp B, spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s)) :=
    isLocalization_away_of_eq _ _ (by rw [Scheme.preimage_basicOpen _ s, Scheme.preimage_basicOpen]; rfl)
  haveI : IsLocalization.Away s Γ(Sp (TrivSqZeroExt R M), (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    (isAffineOpen_top _).isLocalization_basicOpen s
  have key := _root_.GlobalTheory.locPullback _ _ _ _ hcomm hinj0 hsurj0 s
    Γ(Sp (TrivSqZeroExt R M), (Sp (TrivSqZeroExt R M)).basicOpen s)
    Γ(Sp R, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s)
    Γ(Sp (TrivSqZeroExt B M), spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s)
    Γ(Sp B, spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s))
    ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appLE _ _ le_rfl).hom
    ((spMap β).appLE _ _ le_rfl).hom
    ((spMap (algebraMap R B)).appLE _ _ le_rfl).hom
    ((spMap (TrivSqZeroExt.fstHom B B M).toRingHom).appLE _ _ hW).hom
    (appLE_comp_res _ _ _ _) (appLE_comp_res _ _ _ _) (appLE_comp_res _ _ _ _) (appLE_comp_res _ _ _ _)
  refine exists_glue_of_sections _ _ _ hV hVP hVQ U x z hx hz ?_ ?_
  · intro t₁ t₂ h1 h2
    rw [← sub_eq_zero]
    refine key.1 _ ?_ ?_
    · rw [map_sub, h1, sub_self]
    · rw [map_sub, h2, sub_self]
  · intro u
    refine key.2 _ _ ?_
    have e1 := Scheme.Hom.appLE_comp_appLE (spMap (algebraMap R B)) x U.1 _ _ hx le_rfl
    have e2 := Scheme.Hom.appLE_comp_appLE (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) z U.1 _ _ hz hW
    have e3 := appLE_congr_hom hxz.symm U.1
      (spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
        (Sp (TrivSqZeroExt R M)).basicOpen s)) (fun w hw => hx hw) (fun w hw => hz (hW hw))
    have := congrArg (fun q => q.hom u) (e1.trans (e3.trans e2.symm))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToTransposeGramGroupMapSurjective
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareAgree


set_option maxHeartbeats 1000000 in
theorem kapX_surjective : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • Matrix.reindex e e X.gramᵀ), Function.Surjective (GlobalTheory.SquareAgree.kapX X e hJ) := by
  intro D X d e J hJ y
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin X.rank) (AE D), u.1 = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y).submatrix e e :=
    ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom y.1, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y = M := ⟨_, rfl⟩
  obtain ⟨Gt, hGt⟩ : ∃ Gt : Matrix (Fin X.rank) (Fin X.rank) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ = Gt := ⟨_, rfl⟩
  have hy : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := y.2
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e Gt := by rw [← hGt]; rfl
  rw [hM, hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1] at hy
  have hx : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one]
  have h1 : Mᵀ * reindex e e Gt * M.map (cA D) = reindex e e Gt := by
    have := congrArg (fun A => incA D D.host.xi0⁻¹ • A) hy
    simpa only [smul_smul, hx, one_smul] using this
  have h2 : (M.submatrix e e)ᵀ * Gt * (M.submatrix e e).map (cA D) = Gt := by
    have := congrArg (fun A => A.submatrix e e) h1
    rw [← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _] at this
    simpa [reindex_apply, transpose_submatrix, submatrix_submatrix, ← Matrix.submatrix_map] using this
  have hT : Gtᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := by rw [← hGt]; exact Matrix.ext fun _ _ => rfl
  have h3 := congrArg transpose h2
  rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc, hT] at h3
  rw [← hM, ← hu] at h3
  refine ⟨(⟨u, h3⟩ : HR (AF D.host.F) D.sp.cm.sig X.gram), ?_⟩
  apply Subtype.ext
  apply Units.ext
  show reindex e e u.1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y
  rw [hu]
  ext a b
  simp

end GlobalTheory.SquareAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltration
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

private theorem lau_eq_vecL {F : Type} [Field F] {n : ℕ} (y : Fin n → F⟦X⟧) :
    GlobalTheory.WachBlock.lau y = GlobalTheory.WachPlace.vecL y := by
  funext a
  rfl

private theorem unConst : UnConst := by
  exact unit_series_constant_holds

private theorem lau_mem_iff_vecL_mem {F : Type} [Field F] {n : ℕ}
    {S : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)} {y : Fin n → F⟦X⟧} :
    GlobalTheory.WachBlock.lau y ∈ S ↔ GlobalTheory.WachPlace.vecL y ∈ S := by
  rw [lau_eq_vecL]

private theorem map_comp_rk1_eq_rk1_map {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (χ : Γ →* (↥(OL LL))ˣ) :
    (Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 χ) =
      GlobalTheory.TripleGal.rk1 ((Units.map (GlobalTheory.WachBlock.ofOL l LL).toMonoidHom).comp χ) := by
  ext g i j
  simp [GlobalTheory.TripleGal.rk1, toOm, GlobalTheory.WachBlock.ofOL]
  obtain rfl := Subsingleton.elim i j
  simp


open NumberField GlobalTheory.ExpFrame in
theorem GlobalTheory.WachPlace.wach_lattices : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (red : O' →+* F) (un : PowerSeries O') (N : Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) n O') (Npsi : Fin t → Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) 1 O') (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsUn l O' (u : ℤ_[l]) un) ∧ (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧ ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l O' L' em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l N h u J em jj ∧ (∀ s, Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l (Npsi s) h u (fun i _ => bot i + ((s : ℕ) : ℤ)) em jj) ∧ GlobalTheory.WachBlock.RedFilt σ l (PowerSeries.map red un) (fun i => (N.P i).map (PowerSeries.map red)) (fun i => (N.D i).map (PowerSeries.map red)) (fun s i => PowerSeries.map red ((Npsi s).P i 0 0)) (fun s i => PowerSeries.map red ((Npsi s).D i 0 0)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl hd σ hσ n t h J bot hJ hbot hIB
  obtain ⟨LL, r, ψ, ϖ, R, M, rs, hz, hE, hcr, hψcr, hirr, hM0, hMtop, hmono, hstab, hrs, hlines⟩ := hIB
  obtain ⟨_, _, _⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI : CharP (ResidueField ↥(OL LL)) l := GlobalTheory.WachMap.charP_residueField_of_irreducible LL
  obtain ⟨x, dim, hx, hd0, hdR, hds⟩ :=
    _root_.GlobalTheory.WachChain.chain_of_lattices _ ↥(OL LL) n t R r ψ ϖ M rs hirr hM0 hMtop hmono hstab hlines
  obtain ⟨u, c, ζ, jj, hu, hc, hζ, hζm, hjj⟩ := _root_.GlobalTheory.WachExp.exists_locExp_expAt l LL hl hz
  obtain ⟨un, hun⟩ := (unConst l ↥(OL LL) hl (u : ℤ_[l]) c hu).1
  have hψ' : ∀ s, GlobalTheory.ExpFrame.CrysWith
      ((Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)} := by
    intro s
    rw [map_comp_rk1_eq_rk1_map]
    exact hψcr s
  obtain ⟨N, Nψ, y, hN, hNψ, hy⟩ := GlobalTheory.WachPlace.exists_positions_global hBS hl hd hσ
    (J := J) (wt := fun s i => bot i + ((s : ℕ) : ℤ)) hJ (fun s i => hbot i s) hz hE
    (r := r) (ψ := fun s => GlobalTheory.TripleGal.rk1 (ψ s)) hcr hψ' hx hu hun hζ (fun a ha => (hjj a ha).2)
  obtain ⟨V, e, m, hV0, hVrk, hVphi, hVgam, hVe, hVphie, hVgame⟩ :=
    GlobalTheory.WachPlace.filtration_of_chain σ (Fact.out : l.Prime).pos
      (PowerSeries.map (residue ↥(OL LL)) un)
      (fun i => (N.P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun i => (N.D i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).D i).map (PowerSeries.map (residue ↥(OL LL)))) rs dim y hd0 hdR hds hy
  refine ⟨↥(OL LL), ResidueField ↥(OL LL), ↥LL.1, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, maximalIdeal ↥(OL LL), inferInstance,
    residue ↥(OL LL), un, N, Nψ, u, c, ζ, (OL LL).val.toRingHom, jj, ⟨hu, hc, hun⟩,
    ⟨hζ, hζm, Subtype.val_injective, fun b hb => (hjj b hb).1⟩, hN, hNψ, ?_⟩
  unfold GlobalTheory.WachBlock.RedFilt
  refine ⟨R, V, rs, e, m, hrs, hV0, hVrk, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVphi i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVgam i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i s
    simp only [lau_eq_vecL]
    exact hVe i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVphie i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVgame i s

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilVacChar

variable {D : D7}

theorem hecke_mul_inv {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ * χ'⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · change Continuous fun a => χ a * (χ' a)⁻¹
    exact h.1.mul h'.1.inv
  · change χ _ * (χ' _)⁻¹ = 1
    rw [h.2 x, h'.2 x, inv_one, mul_one]

theorem resEta_mul_inv {χ χ' : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (h' : ResEta D χ' n) :
    ResEta D (χ * χ'⁻¹) 0 := by
  refine ⟨h.1, fun η hη a => ?_⟩
  change χ _ * (χ' _)⁻¹ = _
  rw [h.2 η hη a, h'.2 η hη a, mul_inv_cancel, pow_zero]

theorem mul_mul_inv_cancel (χ χ' : (AE D)ˣ →* Circle) : χ' * (χ * χ'⁻¹) = χ := by
  refine MonoidHom.ext fun a => ?_
  change χ' a * (χ a * (χ' a)⁻¹) = χ a
  rw [mul_comm (χ a), mul_inv_cancel_left]

theorem vacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → IsWeilDatumO ψ S T χS χT om → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → ∀ x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → om (g, h) f = (((((χT * (η ^ T.rank)⁻¹) x)⁻¹ * (χS * (η ^ S.rank)⁻¹) y : Circle) : ℂ) * ∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f := by
  intro D ψ hψ S T θ hθ χS χT om η hη hom sS sT hS hT g hg h hh cS cT x y hx hy f hf hv
  obtain ⟨om₀, h₀, -, hvac⟩ := _root_.GlobalTheory.WeilProduct.exists_weilDatum_etaTilde D ψ hψ S T θ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) η hη
  obtain ⟨om', h', htw⟩ := _root_.GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ S T _ _ (χS * (η ^ S.rank)⁻¹) (χT * (η ^ T.rank)⁻¹) om₀ h₀
    (hecke_mul_inv hom.hecS h₀.hecS) (hecke_mul_inv hom.hecT h₀.hecT)
    (resEta_mul_inv hom.resS h₀.resS) (resEta_mul_inv hom.resT h₀.resT)
  rw [mul_mul_inv_cancel, mul_mul_inv_cancel] at h'
  rw [_root_.GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T χS χT om om' hom h' (g, h) f hf, htw g h x y hx hy, LinearMap.smul_apply,
    hvac sS sT hS hT g hg h hh cS cT f hf hv, smul_smul]

end GlobalTheory.WeilVacChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2Statement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_unitary_adelic_L2 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : SInf F κ →ₗ[ℂ] SInf F κ) (Ω : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ (f : SInf F κ) (h : (κ → Af F) → ℂ), Ω (pureA F f h) = pureA F (L f) h) →
    (∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
      ∫ x, star (L f₁ x) * L f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖Ω φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchimedeanL2.lintegral_arch_eq | exact GlobalTheory.ArchimedeanL2.lintegral_arch_eq | (intros; apply GlobalTheory.ArchimedeanL2.lintegral_arch_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZeroDimSupportEulerChar
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem hdim_zero_twistZ_eq_chi_of_suppDim_le_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ 0 → ∀ j : ℤ, (GlobalTheory.hdim k (GlobalTheory.twistZ F L j) 0 : ℤ) = GlobalTheory.chi k F := by
  intro k _ Y _ hP L hL F _ hF j
  have := isNoetherian_of_isProjOver hP
  rw [hdim_twist_of_suppDim_le_zero k hF (Twist.isLB_lbZPow hL j) 0,
    chi_eq_hdim_zero_of_suppDim_le_zero k hF]

end GlobalTheory.HSCore
end

