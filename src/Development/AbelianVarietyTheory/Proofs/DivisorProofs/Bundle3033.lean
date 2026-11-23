module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2975
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfield
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIsUnitDividingThetaConstantNeZeroDvd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep

theorem unit_ne_zero_dvd : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧ ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀
  intro hdiv
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set y' : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy'
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ y' with hy
  have h1 : y' (closedPoint V) ⤳ z₁ := sp _
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hξz : ξ ⤳ z₁ := sp _
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hx₀ : X₁.S.th x₀ ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem x₀)
  have key : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
      algebraMap V (FractionRing V) (RatModel.valLoc y' z₁ h1 ⟨_, hdiv.2 a⟩) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro a
    have hq : X₁.S.th a / X₁.S.th x₀ ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz (hdiv.2 a)
    have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hdiv.1).symm
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    change X₁.M.val y (X₁.S.th a) = _ * X₁.M.val y (X₁.S.th x₀)
    rw [show X₁.M.val y (X₁.S.th a) = X₁.M.val y (X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀) from congrArg _ e,
      RatModel.val_mul hyξ hq hx₀]
    congr 1
    exact RatModel.val_spMap_comp (algebraMap V (FractionRing V)) y' h1 ⟨_, hdiv.2 a⟩
  refine ⟨?_, ?_, fun a => ⟨_, key a⟩⟩
  · have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  · intro h0
    obtain ⟨c, -, hc⟩ := GoodOut.exists_th_notMem abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 X₁.ρ
      ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime _⟩ x₀
    exact hc (by
      change 𝔪.yK _ = 0
      rw [key, h0, mul_zero])

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsCompatOfTateIsometriesStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPoints_compat_of_tateIsometries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
  (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F']
  (σ : F →ₐ[FractionRing R] F')
  (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F')),
  GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.XFLevel C tK m1 m2 F' I' →
  ∀ (a : Dw.La) (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A),
    C.P.ToA F l.M' (I.ev l.M' a) x → C.P.ToA F' l.M' (I'.ev l.M' a) x' → x'.left = spMap σ.toRingHom ≫ x.left := by
  first | exact @GlobalTheory.LowDat.level_points_compat | exact GlobalTheory.LowDat.level_points_compat | (intros; apply GlobalTheory.LowDat.level_points_compat <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSystemOfOrderGeAlongTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory

noncomputable section

namespace GlobalTheory.USepStrait

theorem range_jK_spMap_subset_of_injective (V R : Type) [CommRing V] [IsDomain V] [CommRing R] [IsDomain R] (ρ : V →+* R)
    (hρ : Function.Injective ρ) (X : Scheme.{0}) (χ : Sp V ⟶ X) : Set.range (jK R ≫ spMap ρ ≫ χ) ⊆ Set.range (jK V ≫ χ) := by
  intro x ⟨p, hp⟩
  let q : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have key : (spMap ρ) ((jK R) p) = (jK V) q := by
    apply PrimeSpectrum.ext
    change Ideal.comap ρ (Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal) =
      Ideal.comap (algebraMap V (FractionRing V)) ⊥
    haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.comap_comap,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V)),
      Ideal.comap_bot_of_injective _ (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective R (FractionRing R)).comp hρ)]
  refine ⟨q, ?_⟩
  rw [← hp]
  change χ ((jK V) q) = χ ((spMap ρ) ((jK R) p))
  rw [key]

theorem mem_of_ordGe_on : UTraitExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (φ : InvFun (𝓞 E)) (d : ℕ) (J : C.Z.IdealSheafData), UValOn Xo c C.i φ J d → ∀ (M : Scheme.{0}) (z₁ : M) (U : M.Opens) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (N₁ : ℕ) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)), GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → Set.range (jK V ≫ spMap ev' ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) → ∀ y' : Sp (FractionRing V) ⟶ Xo.XF c, y' ≫ C.iF = spMap ((algebraMap V (FractionRing V)).comp ev') ≫ ζ → ∀ (D e : ℕ) (f : M.presheaf.stalk z₁), Φ.OrdGe φ (D * (2 * d)) e f → ev' f ∈ idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b)) ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e := by
  intro hExt E _ _ _ H Dw l Xo c C φ d J hval M z₁ U ζ N₁ Φ hT V _ _ _ _ hV ev' hev' hU y' hy' D e f hf
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hV⟩, inferInstance⟩
  obtain ⟨T, fx, fK, hfi, hfl, -, hfK, hTy⟩ := hExt E H Dw l Xo c V hB inferInstance y'
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  let evT := fx.comp ev'
  haveI : IsLocalHom evT := RingHom.isLocalHom_comp fx ev'
  have hring : (algebraMap T.V (FractionRing T.V)).comp evT = fK.comp ((algebraMap V (FractionRing V)).comp ev') :=
    RingHom.ext fun a => (hfK (ev' a)).symm
  have hsq : jK T.V ≫ spMap evT ≫ ζ = T.y ≫ C.iF := by
    rw [hTy, Category.assoc, hy', ← Category.assoc, GlobalTheory.USepTrait.sp_comp, ← Category.assoc, GlobalTheory.USepTrait.sp_comp, hring]
  have hrange : Set.range (jK T.V ≫ spMap evT ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) := by
    have e1 : jK T.V ≫ spMap evT ≫ M.fromSpecStalk z₁ = jK T.V ≫ spMap fx ≫ spMap ev' ≫ M.fromSpecStalk z₁ := by
      rw [← GlobalTheory.USepTrait.sp_comp ev' fx, Category.assoc]
    rw [e1]
    exact (range_jK_spMap_subset_of_injective V T.V fx hfi M (spMap ev' ≫ M.fromSpecStalk z₁)).trans
      (by simpa only [Category.assoc] using hU)
  have hT' := hT T evT inferInstance hsq hrange
  change ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] T.P.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp evT = Φ.ev y ∧
      ∀ k, Φ.t y k ^ 2 = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.be (e a) (e b) at hT'
  obtain ⟨y2, f₂, eq, hm, hP, hf₂i, hf₂l, hf₂c, ht⟩ := hT'
  obtain ⟨tK, m1, m2⟩ := T.gen
  have hyχ : T.y ≫ C.i = jK T.V ≫ (spMap evT ≫ ζ ≫ pullback.fst C.z (spMap C.b)) := by
    show T.y ≫ C.iF ≫ pullback.fst _ _ = _
    rw [← Category.assoc, ← hsq]
    simp only [Category.assoc]
  obtain ⟨n, hn, hid⟩ := hval T.V T.cdvr T.ϖ T.irr _ T.y hyχ T.t tK m1 m2 T.P T.be T.lev T.mono
  have hid' : (idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b))).map fx = Ideal.span {T.ϖ ^ n} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, ← hid, ← Category.assoc, GlobalTheory.USepTrait.sp_comp]
  have hm0 : 0 < Φ.m y2 := by omega
  let k : Fin (Φ.m y2) := ⟨0, hm0⟩
  have hδ : Φ.δ y2 k = pull eq.toLinearMap T.be := LinearMap.ext₂ fun a b => (ht k).2 a b
  have hev : φ.evalZ (Φ.δ y2 k) = φ.evalZ T.be := by
    rw [hδ]; exact evalZ_pull φ eq.surjective T.be
  have hb : ((D * (2 * n) : ℕ) : ℝ) = ((D * (2 * d) : ℕ) : ℝ) * φ.evalZ (Φ.δ y2 k) := by
    rw [hev]; push_cast; rw [hn]; ring
  have hmem := hf.mem y2 hP hm k (D * (2 * n)) hb
  have htp : Φ.t y2 k ^ (D * (2 * n)) = f₂ (T.ϖ ^ (n * D)) := by
    rw [show D * (2 * n) = 2 * (n * D) by ring, pow_mul, (ht k).1, map_pow]
  haveI := hf₂l
  have hK : (Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e).map f₂ =
      Ideal.span {Φ.t y2 k ^ (D * (2 * n))} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map (Φ.ev y2)) ^ e := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow, Ideal.map_map, hf₂c, htp]
  have h1 : evT f ∈ Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e := by
    rw [← GlobalTheory.USepTrait.comap_map_eq f₂ hf₂i (Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e)]
    rw [Ideal.mem_comap]
    rw [hK, ← RingHom.comp_apply, hf₂c]
    exact hmem
  haveI := hfl
  have hK' : ((idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b))) ^ D ⊔
      ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e).map fx =
      Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e := by
    rw [Ideal.map_sup, Ideal.map_pow, hid', Ideal.span_singleton_pow, ← pow_mul, Ideal.map_pow, Ideal.map_map]
  rw [← GlobalTheory.USepTrait.comap_map_eq fx hfi (_ ^ D ⊔ _), hK']
  exact h1

end GlobalTheory.USepStrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStalkNormalNoetherianFractionRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem stalk_isNoetherian_normal_fractionRing : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  intro X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  have hN := X₁.normal
  refine ⟨GlobalTheory.IsNormalScheme.isDomain_stalk z₁, ?_, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z₁, ?_⟩
  · have : FaithfulSMul (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (X₁.M.stalkHom_injective z₁)
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := X₁.M.O z₁) x
    refine ⟨(X₁.M.stalkEquiv z₁).symm a, (X₁.M.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : X₁.M.O z₁, algebraMap (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ((X₁.M.stalkEquiv z₁).symm c) = c := fun c => by
      change X₁.M.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  · have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
    have := X₁.M.lft
    have : IsLocallyNoetherian (Sp X₁.o₁) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    infer_instance

end GlobalTheory.GSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.SupISymm

theorem exists_unit_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    {c ε : Ω} (hc : c ^ 2 = 1) (hε : ε ^ ((S.r * S.N) ^ 2) = 1) : ∃ u : oˣ, c * ε = algebraMap o Ω (u : o) := by
  have hinj : Function.Injective (algebraMap o Ω) := ArithBase.inj
  have hp : IsPrimitiveRoot (algebraMap o Ω S.ζ) ((S.r * S.N) ^ 2) := S.prim.map_of_injective hinj
  have hpos : 0 < (S.r * S.N) ^ 2 := by
    have := S.N_ge; have := S.r_pos; positivity
  obtain ⟨k, -, hk⟩ := hp.eq_pow_of_pow_eq_one hε
  have hζu : IsUnit S.ζ := S.prim.isUnit hpos.ne'
  have hc' : c = 1 ∨ c = -1 := by
    have : c * c = 1 := by rw [← sq]; exact hc
    exact mul_self_eq_one_iff.1 this
  rcases hc' with rfl | rfl
  · exact ⟨(hζu.unit) ^ k, by simp [← hk, map_pow]⟩
  · exact ⟨-(hζu.unit) ^ k, by simp [← hk, map_pow]⟩

theorem exists_unit_th_neg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a) (a : S.Gam) :
    ∃ u : oˣ, S.th (-a) = algebraMap o Ω (u : o) * S.th a := by
  obtain ⟨c, ε, hc, hε, h⟩ := H a
  obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one S hc hε
  exact ⟨u, by rw [h, hu]⟩

theorem neg_mem_supI_of_parity {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a)
    (z : M.Z) (a : S.Gam) (ha : a ∈ S.supI M z) : -a ∈ S.supI M z := by
  obtain ⟨hne, hdiv⟩ := ha
  obtain ⟨u, hu⟩ := exists_unit_th_neg S H a
  have hu0 : algebraMap o Ω (u : o) ≠ 0 := by
    intro h0
    have h1 : algebraMap o Ω ((u : o) * ((u⁻¹ : oˣ) : o)) = 1 := by simp
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨by rw [hu]; exact mul_ne_zero hu0 hne, fun j => ?_⟩
  obtain ⟨v, hv⟩ := exists_unit_th_neg S H (-j)
  rw [neg_neg] at hv
  have key : S.th j / S.th (-a) = algebraMap o Ω ((v : o) * ((u⁻¹ : oˣ) : o)) * (S.th (-j) / S.th a) := by
    have hi : algebraMap o Ω ((u⁻¹ : oˣ) : o) = (algebraMap o Ω (u : o))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
    rw [hv, hu, map_mul, hi]
    field_simp
  rw [key]
  exact (M.O z).mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv (-j))

end GlobalTheory.GSep.SupISymm


open GlobalTheory.GSep.SupISymm in
theorem GlobalTheory.GSep.neg_mem_supI : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  intro X₁ z₁ a ha
  exact neg_mem_supI_of_parity X₁.S X₁.M (fun a => GlobalTheory.ThetaParity.theta_neg X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ a) z₁ a ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantEqScalarRootMulUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit : ∀ (n : ℕ), n.Prime → Odd n → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (n : V₁) →
  ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen →
  ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th →
  ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K),
    GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro n hn hodd j hj V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, rfl⟩
    omega
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  have hmu : IsUnit ((n ^ j : ℕ) : V₁) := by push_cast; exact hunit.pow j
  obtain ⟨M, lam, hM, H⟩ := GlobalTheory.T.theta_terms_separation_algebraically_closed (n ^ j) (hodd.pow) hm3 V₁ hV hmu D X C e u mo hmo hT K ev ρ₀ hρ₀ th hth
  refine ⟨M, lam, hM, fun y c hc => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant (Sp V₁) D.P ρ₀ hρ₀ (n ^ j) (hodd.pow) _ th y _ hc
  exact H (y ^ n ^ j) τ c (GlobalTheory.USep.isTorsFrame_sq _ D.P ρ₀ (n ^ j) _ (y ^ n ^ j) τ hτ) hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield : ∀ (R : Type) [CommRing R] [IsDomain R]
    (Q : DegPre R) (τ₀ : Gens Q) (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
    ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
      (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
      (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
      IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ →
      w.IsGen →
      (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) →
      ∀ (a b : Q.X) (τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])),
        τ₁.IsGen → ∃ x : k₀ˣ, ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val (τ₀ a b) (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) * val τ₁ (spMap k₀.subtype) z J₀ := by
  first | exact @GlobalTheory.UCanon.BaseDescent.main | exact GlobalTheory.UCanon.BaseDescent.main | (intros; apply GlobalTheory.UCanon.BaseDescent.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsValLocalUnitsMulSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a b : D.X, ∃ c ∈ k₀, (val (τ₀ a b) (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (a + b)).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
        (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c b).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c 0).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.fromBase_tau_val | exact GlobalTheory.USep.EvG.fromBase_tau_val | (intros; apply GlobalTheory.USep.EvG.fromBase_tau_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnBasicOpenOfComesFromBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ f : V, (∀ k, ∃ n : ℕ, s k ∣ f ^ n) → ∀ y, PsiUnitOn Q y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) := by
  first | exact @GlobalTheory.UnitOpen.psiUnitOn_basicOpen_of_divFrom | exact GlobalTheory.UnitOpen.psiUnitOn_basicOpen_of_divFrom | (intros; apply GlobalTheory.UnitOpen.psiUnitOn_basicOpen_of_divFrom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectDescendsWithPointsSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledLowerObject_descends_with_points_subfield : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (θ : o'.t.G.left ⟶ B'.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → IsGrpPullback o'.t.G B' (𝟙 _) θ → LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) → (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) → IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) ∧ LBIso o'.t.PP.L (M₀.pull (θ ≫ π₀)) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ θ ≫ π₀ = spMap k₀.subtype ≫ x₀ := by
  first | exact @GlobalTheory.UCanon.PtsDescent.pulledObj_descends_with_points | exact GlobalTheory.UCanon.PtsDescent.pulledObj_descends_with_points | (intros; apply GlobalTheory.UCanon.PtsDescent.pulledObj_descends_with_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT

theorem quasiCompact_of_qProj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    QuasiCompact f := by
  obtain ⟨N, i, -, hi, rfl⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  infer_instance

theorem Obj.eta_pow {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (x : D.La) : o.eta x ^ N = 1 := by
  have h0 : o.eta 0 = 1 := by
    have h := o.eta_add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hn : ∀ n : ℕ, o.eta (n • x) = o.eta x ^ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]
  rw [← hn, o.eta_ker]

theorem Datum.Cls.fullMark {p : ℕ} [Fact p.Prime] (D : Datum p) (N : ℕ) (hN : 0 < N) (hp : N.Coprime p)
    (D' : PLat D.O D.inv) (t : D.La → D'.La) (h : D.Cls N D' t) : FullMark N D' t := by
  obtain ⟨⟨f, ν, rfl, -, hf⟩, -⟩ := h
  exact (hf N hN hp).2.2.2.1

theorem model_uniformised : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N), 3 ≤ N → N.Coprime p →
    b.IsType σ ρ → M.Uniformised σ ρ := by
  intro p _ D R _ b N σ ρ M hN hp hty
  obtain ⟨h, hL⟩ := _root_.GlobalTheory.HTDim.relDim_and_isLB p D R b N M.X M.s M.univ
  refine ⟨h, hL, ?_⟩
  exact GlobalTheory.PELU.nonempty_unif D.O D.inv D.g ρ R σ D.La (M.univ.fam h hL) N (D.Cls N) (D.a * (D.n - 1)) hN
    (fun a => M.univ.eta_pow a) M.smooth (quasiCompact_of_qProj M.qproj)
    (fun D' t hc => Datum.Cls.fullMark D N (by omega) hp D' t hc)
    (GlobalTheory.T.complexPoints_classify_markedPeriods p D R b N σ ρ M h hL (by omega) hp hty)

end GlobalTheory.UPel.HT
end
end

