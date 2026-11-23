module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentDataChartsCommon
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.CommonChart

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spinj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem flat_generic {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) [Flat φ] :
    φ (genericPoint Y) = genericPoint X := by
  have hg : GeneralizingMap φ := Flat.generalizingMap φ
  obtain ⟨y, hy, e⟩ := hg (genericPoint_specializes (φ (genericPoint Y)))
  have : y = genericPoint Y := (hy.antisymm (genericPoint_specializes y)).eq
  rw [← this, e]

theorem exists_ff {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) [Flat φ] :
    ∃ θ : X.functionField →+* Y.functionField, gp Y ≫ φ = spMap θ ≫ gp X := by
  have h := flat_generic φ
  refine ⟨((X.presheaf.stalkSpecializes (specializes_of_eq h)) ≫ φ.stalkMap (genericPoint Y)).hom, ?_⟩
  show Y.fromSpecStalk _ ≫ φ = Spec.map (_ ≫ _) ≫ X.fromSpecStalk _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem gp_spec (R : CommRingCat.{0}) [IsDomain R] :
    ∃ c : R →+* (Spec R).functionField, Function.Injective c ∧ gp (Spec R) = spMap c :=
  ⟨algebraMap R (Spec R).functionField, IsFractionRing.injective R (Spec R).functionField,
    Spec.fromSpecStalk_eq' _ _⟩

theorem gp_factor {E : Type} [CommRing E] [IsDomain E] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp E) [Flat p] :
    ∃ t : Sp Y.functionField ⟶ Sp (FractionRing E), t ≫ jK E = gp Y ≫ p := by
  obtain ⟨θ, h⟩ := exists_ff p
  obtain ⟨c, hc, this⟩ := gp_spec (CommRingCat.of E)
  have hi : Function.Injective (θ.comp c) := θ.injective.comp hc
  refine ⟨spMap (IsFractionRing.lift hi), ?_⟩
  rw [h, spc]
  rw [this, spc]
  congr 1
  ext z
  simp

theorem ring_part (R R₀ R' O Ω : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] [IsRegularLocalRing R₀]
    [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing O] [IsLocalRing O] [Field Ω]
    [Algebra R O] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime O p]
    (ρ : R →+* R₀) (hρ : ρ.Flat) (φ' : O →+* R') [IsLocalHom φ'] (u : R₀ →+* Ω) (u' : R' →+* Ω)
    (hc : IsAdicComplete (maximalIdeal R') R') (he : IsEtaleCompletion φ')
    (hu : ((residue R').comp φ').FormallyUnramified) (hk : RingHom.ker u' = maximalIdeal R')
    (huu : u.comp ρ = u'.comp (φ'.comp (algebraMap R O))) :
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : R₀ →+* E) (b : R' →+* E)
      (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp ρ = b.comp (φ'.comp (algebraMap R O)) ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (RingHom.ker u).map a = maximalIdeal E := by
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing p.primeCompl O inferInstance
  haveI hq : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
  let R₁ := Localization.AtPrime (RingHom.ker u)
  haveI : IsRegularRing R₀ := isRegularRing_of_isRegularLocalRing R₀
  haveI : IsRegularLocalRing R₁ := IsRegularRing.isRegularLocalRing_localization _
  have h1 : ∀ s : p.primeCompl, IsUnit (((algebraMap R₀ R₁).comp ρ) s) := by
    intro s
    have hs : IsUnit (u (ρ s)) := by
      have := RingHom.congr_fun huu s
      simp only [RingHom.comp_apply] at this
      rw [this]
      exact ((IsLocalization.map_units O s).map φ').map u'
    exact IsLocalization.map_units R₁ (⟨ρ s, fun h => hs.ne_zero h⟩ : (RingHom.ker u).primeCompl)
  have h2 : ∀ s : (RingHom.ker u).primeCompl, IsUnit (u s) := fun s => Ne.isUnit s.2
  let φ₁ : O →+* R₁ := IsLocalization.lift h1
  let u₁ : R₁ →+* Ω := IsLocalization.lift h2
  have e1 : φ₁.comp (algebraMap R O) = (algebraMap R₀ R₁).comp ρ := IsLocalization.lift_comp h1
  have e2 : u₁.comp (algebraMap R₀ R₁) = u := IsLocalization.lift_comp h2
  have hm : (RingHom.ker u).map (algebraMap R₀ R₁) = maximalIdeal R₁ := Localization.AtPrime.map_eq_maximalIdeal
  have k1 : RingHom.ker u₁ = maximalIdeal R₁ := by
    refine ((maximalIdeal.isMaximal R₁).eq_of_le (RingHom.ker_ne_top u₁) ?_).symm
    rw [← hm, Ideal.map_le_iff_le_comap, RingHom.comap_ker, e2]
  have e3 : u₁.comp φ₁ = u'.comp φ' := by
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [RingHom.comp_assoc, e1, ← RingHom.comp_assoc, e2, huu]; rfl
  have fl0 : (algebraMap R₀ R₁).Flat := by
    rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat R₁ (RingHom.ker u).primeCompl
  have fl1 : φ₁.Flat := by
    have hf : (φ₁.comp (algebraMap R O)).Flat := by rw [e1]; exact hρ.comp fl0
    letI : Algebra O R₁ := φ₁.toAlgebra
    letI : Algebra R R₁ := (φ₁.comp (algebraMap R O)).toAlgebra
    haveI : IsScalarTower R O R₁ := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Module.Flat R R₁ := hf
    exact (Module.flat_iff_of_isLocalization O p.primeCompl R₁).mpr this
  have lo : IsLocalHom φ₁ := by
    refine ⟨fun z hz => ?_⟩
    have : u' (φ' z) ≠ 0 := by
      have h := RingHom.congr_fun e3 z
      simp only [RingHom.comp_apply] at h
      rw [← h]; exact (hz.map u₁).ne_zero
    apply isUnit_of_map_unit φ'
    by_contra hn
    exact this (by rw [← RingHom.mem_ker, hk]; exact hn)
  obtain ⟨E, _, _, _, a, b, v, fa, fb, hab, hv, hva, hvb, hma, -⟩ :=
    _root_.GlobalTheory.exists_complete_regular_meet O R₁ R' Ω φ₁ φ' u₁ u' fl1 lo hc he hu k1 hk e3
  refine ⟨E, _, inferInstance, inferInstance, a.comp (algebraMap R₀ R₁), b, v, fl0.comp fa, fb, ?_, hv, ?_, hvb, ?_⟩
  · rw [RingHom.comp_assoc, ← e1, ← RingHom.comp_assoc, hab]; rfl
  · rw [← RingHom.comp_assoc, hva, e2]
  · rw [← Ideal.map_map, hm, hma]

theorem gen_part {X S : Scheme.{0}} {j : X ⟶ S} {A : Over X} [GrpObj A] {x : S} (C : Chart j A x)
    {E : Type} [CommRing E] [IsDomain E] (a : C.R →+* E) (ha : a.Flat) :
    ∃ (y : Sp (FractionRing E) ⟶ X)
      (l : ((Over.pullback (jK E)).obj ((Over.pullback (spMap a)).obj C.G)).left ⟶ pullback C.G.hom (jK C.R)),
      y ≫ j = jK E ≫ spMap a ≫ C.ξ ∧
      l ≫ pullback.fst _ _ = pullback.fst ((Over.pullback (spMap a)).obj C.G).hom (jK E) ≫ pullback.fst C.G.hom (spMap a) ∧
      IsGrpPullback ((Over.pullback (jK E)).obj ((Over.pullback (spMap a)).obj C.G)) A y (l ≫ C.α) := by
  have hi : Function.Injective a := by
    letI : Algebra C.R E := a.toAlgebra
    haveI : Module.Flat C.R E := ha
    exact FaithfulSMul.algebraMap_injective C.R E
  have hi' : Function.Injective ((algebraMap E (FractionRing E)).comp a) :=
    (IsFractionRing.injective E (FractionRing E)).comp hi
  let aK : FractionRing C.R →+* FractionRing E := IsFractionRing.lift hi'
  have e : jK E ≫ spMap a = spMap aK ≫ jK C.R := by
    rw [spc, spc]
    congr 1
    ext z
    simp [aK]
  have p := ((isGrpPullback_pullback ((Over.pullback (spMap a)).obj C.G) (jK E)).comp
    (isGrpPullback_pullback C.G (spMap a))).congr e rfl
  have q := isGrpPullback_pullback C.G (jK C.R)
  have w := p.1.w
  rw [← Category.assoc] at w
  refine ⟨spMap aK ≫ C.y, q.1.lift _ _ w, ?_, q.1.lift_fst _ _ w, ?_⟩
  · rw [Category.assoc, C.hy, ← Category.assoc, ← e, Category.assoc]
  · exact (IsGrpPullback.cancel q (p.congr rfl (q.1.lift_fst _ _ w).symm) (q.1.lift_snd _ _ w)).comp C.gen

theorem iso_extend {E : Type} [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E]
    (G H : Over (Sp E)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (e : (Over.pullback (jK E)).obj G ≅ (Over.pullback (jK E)).obj H) [IsMonHom e.hom] :
    ∃ F : G ≅ H, IsMonHom F.hom ∧ (Over.pullback (jK E)).map F.hom = e.hom := by
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := semiAbelian_hom_extend_generic E G H hG hH e.hom inferInstance
  obtain ⟨F', ⟨hF', eF'⟩, -⟩ := semiAbelian_hom_extend_generic E H G hH hG e.inv inferInstance
  refine ⟨⟨F, F', ?_, ?_⟩, hF, eF⟩
  · exact (semiAbelian_hom_extend_generic E G G hG hG (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, eF, eF', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (semiAbelian_hom_extend_generic E H H hH hH (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, eF, eF', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

theorem ring_setup (σ : Setup) (x x' : Sp σ.R) (Ω : Type) [Field Ω] (u : (σ.C x).R →+* Ω) (u' : (σ.C x').R →+* Ω)
    (hk : RingHom.ker u' = maximalIdeal _) (huu : u.comp (σ.ρ x) = u'.comp (σ.ρ x')) :
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : (σ.C x).R →+* E)
      (b : (σ.C x').R →+* E) (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp (σ.ρ x) = b.comp (σ.ρ x') ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (RingHom.ker u).map a = maximalIdeal E := by
  let z : Sp σ.R := (σ.C x').ξ (closedPoint (σ.C x').R)
  haveI : z.asIdeal.IsPrime := z.isPrime
  letI : Algebra σ.R ((Sp σ.R).presheaf.stalk z) := (StructureSheaf.toStalk σ.R z).hom.toAlgebra
  haveI : IsLocalization.AtPrime ((Sp σ.R).presheaf.stalk z) z.asIdeal := StructureSheaf.IsLocalization.to_stalk σ.R z
  have e : (Scheme.stalkClosedPointTo (σ.C x').ξ).hom.comp (algebraMap σ.R ((Sp σ.R).presheaf.stalk z)) = σ.ρ x' := by
    apply spinj
    rw [← spc, ← σ.hρ x']
    have h := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (σ.C x').ξ
    rw [Spec.fromSpecStalk_eq'] at h
    exact h
  have := ring_part σ.R (σ.C x).R (σ.C x').R ((Sp σ.R).presheaf.stalk z) Ω z.asIdeal (σ.ρ x) (σ.flat x)
    (Scheme.stalkClosedPointTo (σ.C x').ξ).hom u u' (σ.C x').complete (σ.C x').etc (σ.C x').unr hk (by rw [e, huu])
  rwa [e] at this

theorem ff_eq (σ : Setup) (x : Sp σ.R) {K : Type} [Field K] (θ : (σ.C x).G.left.functionField →+* K)
    (t : Sp K ⟶ pullback (σ.C x).G.hom (jK (σ.C x).R)) (ht : t ≫ pullback.fst _ _ = spMap θ ≫ gp (σ.C x).G.left) :
    t ≫ (σ.C x).α = spMap (θ.comp (σ.θ x)) ≫ gp σ.A.left := by
  obtain ⟨l, h₁, h₂⟩ := σ.hθ x
  rw [σ.compat x _ t (spMap θ ≫ l) (by rw [ht, Category.assoc, h₁]), Category.assoc, h₂, ← Category.assoc, spc]

end GlobalTheory.Desc.CommonChart

namespace GlobalTheory.Desc
open CommonChart

theorem setup_common : ∀ σ : Setup, σ.Common := by
  intro σ x x' Ω _ u u' hk huu
  obtain ⟨E, _, _, _, a, b, v, fa, fb, hab, hv, hva, hvb, hma⟩ := ring_setup σ x x' Ω u u' hk huu
  haveI : IsIntegrallyClosed E := (isDomain_and_isIntegrallyClosed_of_isRegularLocalRing E).2
  obtain ⟨ya, la, hya, hla, pa⟩ := gen_part (σ.C x) a fa
  obtain ⟨yb, lb, hyb, hlb, pb⟩ := gen_part (σ.C x') b fb
  have hy : yb = ya := by
    rw [← cancel_mono (awayMap σ.f), hya, hyb, σ.hρ, σ.hρ, spc _ a, spc _ b, hab]
  subst hy
  obtain ⟨e, he, hee⟩ := grpPullback_iso pa pb
  have sa := IsSemiAbelian.pullback (spMap a) _ (σ.C x).semi
  have sb := IsSemiAbelian.pullback (spMap b) _ (σ.C x').semi
  obtain ⟨F, hF, eF⟩ := iso_extend _ _ sa sb e
  haveI := sa
  haveI : IsIntegral ((Over.pullback (spMap a)).obj (σ.C x).G).left := isIntegral_left_of_isSemiAbelian _
  have ga := isGrpPullback_pullback (σ.C x).G (spMap a)
  have gb := ((isGrpPullback_of_iso F).comp (isGrpPullback_pullback (σ.C x').G (spMap b))).congr
    (Category.id_comp _) rfl
  haveI : Flat (spMap a) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]; exact fa
  haveI : Flat (spMap b) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]; exact fb
  haveI : Flat (pullback.fst (σ.C x).G.hom (spMap a)) := inferInstance
  haveI : Flat (F.hom.left ≫ pullback.fst (σ.C x').G.hom (spMap b)) :=
    MorphismProperty.of_isPullback (P := @Flat) gb.1.flip inferInstance
  obtain ⟨θa, ha⟩ := @exists_ff _ ((Over.pullback (spMap a)).obj (σ.C x).G).left _ _
    (pullback.fst (σ.C x).G.hom (spMap a)) inferInstance
  obtain ⟨θb, hb⟩ := exists_ff (F.hom.left ≫ pullback.fst (σ.C x').G.hom (spMap b))
  refine ⟨E, _, inferInstance, inferInstance, a, b, v, (Over.pullback (spMap a)).obj (σ.C x).G, inferInstance,
    inferInstance, _, _, θa, θb, fa, fb, hab, hv, hva, hvb, hma, sa, ga, gb,
    ⟨_, Category.comp_id _, ha⟩, ⟨_, Category.comp_id _, hb⟩, ?_⟩
  haveI := sa.smooth
  obtain ⟨t, ht⟩ := gp_factor ((Over.pullback (spMap a)).obj (σ.C x).G).hom
  let m := pullback.lift _ _ ht.symm
  have hm : m ≫ pullback.fst _ _ = gp _ := pullback.lift_fst _ _ _
  have e₁ := ff_eq σ x θa (m ≫ la) (by rw [Category.assoc, hla, ← Category.assoc, hm, ha])
  have hE : e.hom.left ≫ pullback.fst ((Over.pullback (spMap b)).obj (σ.C x').G).hom (jK E) =
      pullback.fst ((Over.pullback (spMap a)).obj (σ.C x).G).hom (jK E) ≫ F.hom.left := by
    rw [← eF]; exact pullback.lift_fst _ _ _
  have e₂ := ff_eq σ x' θb (m ≫ e.hom.left ≫ lb) (by
    rw [Category.assoc, Category.assoc, hlb, reassoc_of% hE, ← Category.assoc, hm, hb])
  haveI : Mono (gp σ.A.left) := by unfold gp; infer_instance
  apply spinj
  rw [← cancel_mono (gp σ.A.left), ← e₁, ← e₂, Category.assoc, Category.assoc, Category.assoc, hee]

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePrimeToCharTorsionRational
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsRat

theorem exists_factor_of_isFinite {K₀ K : Type} [Field K₀] [IsAlgClosed K₀] [Field K]
    (e : K₀ →+* K) {Z : Scheme.{0}} (s : Z ⟶ Sp K₀) [IsFinite s] (w : Sp K ⟶ Z)
    (hw : w ≫ s = spMap e) : ∃ w₀ : Sp K₀ ⟶ Z, w = spMap e ≫ w₀ := by
  haveI : IsAffine Z := isAffine_of_isAffineHom s
  let φ : CommRingCat.of K₀ ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ s)
  have hφ : Spec.map φ = Z.isoSpec.inv ≫ s := Spec.map_preimage _
  have hF : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hF' : φ.hom.Finite := (IsFinite.SpecMap_iff φ).1 hF
  let ψ : Γ(Z, ⊤) ⟶ CommRingCat.of K := Spec.preimage (w ≫ Z.isoSpec.hom)
  have hψ : Spec.map ψ = w ≫ Z.isoSpec.hom := Spec.map_preimage _
  have hφψ : φ ≫ ψ = CommRingCat.ofHom e := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hw]
  letI : Algebra K₀ Γ(Z, ⊤) := φ.hom.toAlgebra
  letI : Algebra K₀ K := e.toAlgebra
  haveI : Module.Finite K₀ Γ(Z, ⊤) := hF'
  have hmem : ∀ b, ψ.hom b ∈ e.range := by
    intro b
    have hb : IsIntegral K₀ b := Algebra.IsIntegral.isIntegral b
    let ψa : Γ(Z, ⊤) →ₐ[K₀] K :=
      { ψ.hom with commutes' := fun c => congrArg (fun g => g.hom c) hφψ }
    have hi : IsIntegral K₀ (ψ.hom b) := hb.map ψa
    exact minpoly.mem_range_of_degree_eq_one K₀ _
      (IsAlgClosed.degree_eq_one_of_irreducible K₀ (minpoly.irreducible hi))
  let E : K₀ ≃+* e.range := RingEquiv.ofBijective e.rangeRestrict
    ⟨fun a b h => e.injective (congrArg Subtype.val h), e.rangeRestrict_surjective⟩
  let ψ₀ : Γ(Z, ⊤) →+* K₀ := E.symm.toRingHom.comp (ψ.hom.codRestrict e.range hmem)
  refine ⟨Spec.map (CommRingCat.ofHom ψ₀) ≫ Z.isoSpec.inv, ?_⟩
  have h2 : CommRingCat.ofHom ψ₀ ≫ CommRingCat.ofHom e = ψ := by
    ext b
    show e (E.symm ⟨ψ.hom b, hmem b⟩) = ψ.hom b
    exact congrArg Subtype.val (E.apply_symm_apply ⟨ψ.hom b, hmem b⟩)
  rw [← Category.assoc, ← Spec.map_comp, h2, hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem torsion_point_rational : ∀ (K₀ K : Type) [Field K₀] [IsAlgClosed K₀] [Field K] (e : K₀ →+* K)
    (Y : Over (Sp K₀)) [GrpObj Y],
    IsAbelianScheme Y → ∀ n : ℕ, IsUnit (n : K₀) → ∀ y : Over.mk (spMap e) ⟶ Y, y ^ n = 1 →
    ∃ y₀ : Sp K₀ ⟶ Y.left, y.left = spMap e ≫ y₀ := by
  intro K₀ K _ _ _ e Y _ hY n hn y hy
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hn
    · exact h
  haveI := GlobalTheory.MulFiniteAny.isFinite_mulA K₀ Y hY n hn1
  let o : Sp K₀ ⟶ Y.left := (η[Y] : 𝟙_ (Over (Sp K₀)) ⟶ Y).left
  have hyo : y.left ≫ (mulA Y n).left = spMap e ≫ o := by
    have h1 : y ≫ mulA Y n = 1 := by
      rw [mulA, MonObj.comp_pow, Category.comp_id, hy]
    have h2 : y.left ≫ (mulA Y n).left = (toUnit (Over.mk (spMap e)) ≫ η[Y]).left := by
      rw [← Over.comp_left, h1, Hom.one_def]
    have h3 : (toUnit (Over.mk (spMap e))).left = spMap e := by
      have := Over.w (toUnit (Over.mk (spMap e)))
      simpa using this
    rw [h2, Over.comp_left, h3]
  obtain ⟨w₀, hw₀⟩ := exists_factor_of_isFinite e (pullback.snd (mulA Y n).left o)
    (pullback.lift y.left (spMap e) hyo) (pullback.lift_snd _ _ _)
  refine ⟨w₀ ≫ pullback.fst (mulA Y n).left o, ?_⟩
  rw [← Category.assoc, ← hw₀, pullback.lift_fst]

end GlobalTheory.TorsRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyReductionLiftsLineBundle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AddFamLift

theorem isPullback_lift {S : Scheme.{0}} (Z U S' : Over S) {W : Scheme.{0}} {pr : W ⟶ Z.left} {t : W ⟶ U.left}
    (hp : IsPullback pr t Z.hom U.hom) (j : (Z ⊗ (U ⊗ S')).left ⟶ W)
    (hj₁ : j ≫ pr = (fst Z (U ⊗ S')).left) (hj₂ : j ≫ t = (snd Z (U ⊗ S')).left ≫ (fst U S').left) :
    IsPullback j ((snd Z (U ⊗ S')).left ≫ (snd U S').left) (t ≫ U.hom) S'.hom := by
  have outer : IsPullback (fst Z (U ⊗ S')).left (snd Z (U ⊗ S')).left Z.hom (U ⊗ S').hom :=
    IsPullback.of_hasPullback Z.hom (U ⊗ S').hom
  have e : (U ⊗ S').hom = (fst U S').left ≫ U.hom := (Over.w _).symm
  rw [e, ← hj₁] at outer
  have left : IsPullback j (snd Z (U ⊗ S')).left t (fst U S').left := IsPullback.of_right outer hj₂ hp
  exact left.paste_vert (IsPullback.of_hasPullback U.hom S'.hom)

abbrev Ov {R C : Type} [CommRing R] [CommRing C] (σ : R →+* C) : Over (Sp R) := Over.mk (spMap σ)

theorem finiteRing_sq_sub_mul_sq_eq_of_card (hAb : AbLift) (R : Type) [CommRing R] (J : Ideal R) (hJ : J ^ 2 = ⊥) (A : Over (Sp R)) [GrpObj A]
    (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (C : Type) [CommRing C] (σ : R →+* C)
    (N : LB (A ⊗ (Ov σ ⊗ Ov (Ideal.Quotient.mk J))).left) (hN : N.IsLB) (hadd : IsAdditive N) :
    ∃ c : Pic (A ⊗ Ov σ).left, CechPic.pull (A ◁ fst (Ov σ) (Ov (Ideal.Quotient.mk J))).left c = cls N hN := by
  letI := σ.toAlgebra
  let U := Ov σ
  let S' := Ov (Ideal.Quotient.mk J)
  obtain ⟨B, _, pr, pr', hB, hBg, hp, hp', hμ, h₁, h₂, -, -⟩ := _root_.GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq R C A g hA hg
  have hp : IsPullback pr B.hom A.hom U.hom := hp
  have hp' : IsPullback pr' (B ⊗ B).hom (A ⊗ A).hom U.hom := hp'
  have wZ : ∀ Z : Over (Sp R), (fst Z (U ⊗ S')).left ≫ Z.hom = ((snd Z (U ⊗ S')).left ≫ (fst U S').left) ≫ U.hom :=
    fun Z ↦ by rw [Category.assoc, Over.w, Over.w, Over.w]
  obtain ⟨i, hi₁, hi₂⟩ : ∃ i : (A ⊗ (U ⊗ S')).left ⟶ B.left, i ≫ pr = (fst A (U ⊗ S')).left ∧
      i ≫ B.hom = (snd A (U ⊗ S')).left ≫ (fst U S').left :=
    ⟨hp.lift _ _ (wZ A), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  obtain ⟨i', hi'₁, hi'₂⟩ : ∃ i' : ((A ⊗ A) ⊗ (U ⊗ S')).left ⟶ (B ⊗ B).left,
      i' ≫ pr' = (fst (A ⊗ A) (U ⊗ S')).left ∧ i' ≫ (B ⊗ B).hom = (snd (A ⊗ A) (U ⊗ S')).left ≫ (fst U S').left :=
    ⟨hp'.lift _ _ (wZ (A ⊗ A)), hp'.lift_fst _ _ _, hp'.lift_snd _ _ _⟩
  have hJ' : J.map σ ^ 2 = ⊥ := by rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have th : IsThick (J.map σ) B.hom i := by
    have q := isPullback_lift A U S' hp i hi₁ hi₂
    exact _root_.GlobalTheory.LBLift.isThick_of_isPullback_quotient R C σ J hJ _ _ B.hom _ i q
  have th' : IsThick (J.map σ) (B ⊗ B).hom i' := by
    have q := isPullback_lift (A ⊗ A) U S' hp' i' hi'₁ hi'₂
    exact _root_.GlobalTheory.LBLift.isThick_of_isPullback_quotient R C σ J hJ _ _ (B ⊗ B).hom _ i' q
  have key : ∀ (φ : A ⊗ A ⟶ A) (φB : B ⊗ B ⟶ B), φB.left ≫ pr = pr' ≫ φ.left →
      (φ ▷ (U ⊗ S')).left ≫ i = i' ≫ φB.left := by
    intro φ φB hφ
    apply hp.hom_ext
    · rw [Category.assoc, hi₁, Category.assoc, hφ, ← Category.assoc, hi'₁, ← Over.comp_left, ← Over.comp_left,
        whiskerRight_fst]
    · rw [Category.assoc, hi₂, Category.assoc, Over.w φB, hi'₂, ← Category.assoc, ← Over.comp_left,
        whiskerRight_snd]
  have ev : ∀ φ : A ⊗ A ⟶ A, CechPic.pull (φ ▷ (U ⊗ S')).left (cls N hN) =
      evc hN (fst (A ⊗ A) (U ⊗ S') ≫ φ) (snd (A ⊗ A) (U ⊗ S')) := fun φ ↦ by
    have : φ ▷ (U ⊗ S') = lift (fst (A ⊗ A) (U ⊗ S') ≫ φ) (snd (A ⊗ A) (U ⊗ S')) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerRight_fst, lift_fst]
      · rw [whiskerRight_snd, lift_snd]
    rw [this]; rfl
  have hm : fst (A ⊗ A) (U ⊗ S') ≫ μ[A] =
      (fst (A ⊗ A) (U ⊗ S') ≫ fst A A) * (fst (A ⊗ A) (U ⊗ S') ≫ snd A A) := by
    rw [← MonObj.comp_mul]
    congr 1
    show μ[A] = lift (fst A A) (snd A A) ≫ μ[A]
    rw [lift_fst_snd, Category.id_comp]
  have add : CechPic.pull (μ[A] ▷ (U ⊗ S')).left (cls N hN) =
      CechPic.pull (fst A A ▷ (U ⊗ S')).left (cls N hN) + CechPic.pull (snd A A ▷ (U ⊗ S')).left (cls N hN) := by
    rw [ev, ev, ev, hm]
    exact (isAdditive_iff hN).1 hadd _ _ _ _
  obtain ⟨c', hc'⟩ := hAb C (J.map σ) hJ' B g hB hBg _ _ i i' _ _ _ th th' (key _ _ hμ) (key _ _ h₁) (key _ _ h₂)
    (cls N hN) add
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k : (A ⊗ U).left ⟶ B.left, k ≫ pr = (fst A U).left ∧ k ≫ B.hom = (snd A U).left :=
    ⟨hp.lift _ _ (by rw [Over.w, Over.w]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  refine ⟨CechPic.pull k c', ?_⟩
  have hk : (A ◁ fst U S').left ≫ k = i := by
    apply hp.hom_ext
    · rw [Category.assoc, hk₁, hi₁, ← Over.comp_left, whiskerLeft_fst]
    · rw [Category.assoc, hk₂, hi₂, ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  rw [← pull_comp, hk, hc']

theorem main : AbLift → ∀ (R : Type) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (C : Type) [CommRing C] (σ : R →+* C) (N : LB (A ⊗ (Over.mk (spMap σ) ⊗ Over.mk (spMap (Ideal.Quotient.mk J)))).left) (hN : N.IsLB), IsAdditive N → ∃ c : Pic (A ⊗ Over.mk (spMap σ)).left, GlobalTheory.CechPic.pull (A ◁ fst (Over.mk (spMap σ)) (Over.mk (spMap (Ideal.Quotient.mk J)))).left c = cls N hN := fun hAb R _ J hJ A _ g hA hg C _ σ N hN hadd ↦
  finiteRing_sq_sub_mul_sq_eq_of_card hAb R J hJ A g hA hg C σ N hN hadd

end GlobalTheory.AddFamLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyOfDisjointOpenPiecesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveLineBundleFamily_of_disjoint_open_pieces : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Fam A (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → Fam A Pt := by
  first | exact @GlobalTheory.DualCon.ProdGlue.fam_of_pieces | exact GlobalTheory.DualCon.ProdGlue.fam_of_pieces | (intros; apply GlobalTheory.DualCon.ProdGlue.fam_of_pieces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpensPreimageBaseChangeIsBasis
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem preAff_basis : ∀ (X₀ X₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) [IsAffineHom pr], (∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U) → (∀ (x : X₁) (U : X₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : X₁) (U : X₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ pr _ hsurj
  refine ⟨?_, ?_⟩
  · intro x U hx
    obtain ⟨V, rfl⟩ := hsurj U
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open (show pr.base x ∈ V from hx) V.isOpen
    exact ⟨Opposite.op ⟨W, hW⟩, hxW, pr.preimage_mono hWV⟩
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨V, rfl⟩ := hsurj U
    have hmem : pr.base x ∈ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := ⟨⟨h₁, h₂⟩, hx⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open hmem (t₁.unop.1 ⊓ t₂.unop.1 ⊓ V).isOpen
    have hWV' : W ≤ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := hWV
    exact ⟨Opposite.op ⟨W, hW⟩, ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₁.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_left) : W ≤ t₁.unop.1))).op⟩,
      ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₂.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_right) : W ≤ t₂.unop.1))).op⟩, hxW,
      pr.preimage_mono (le_trans hWV' inf_le_right)⟩

end GlobalTheory.Obs.BC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_eq_one_trivial_on_axis : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1 := by
  first | (exact @GlobalTheory.WeilSqKer.weilIs_eq_one) | (exact GlobalTheory.WeilSqKer.weilIs_eq_one) | (intros; apply GlobalTheory.WeilSqKer.weilIs_eq_one  <;> assumption)
end

