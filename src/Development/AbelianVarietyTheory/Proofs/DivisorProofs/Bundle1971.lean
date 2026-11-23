module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactConjugateExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfArcsAndGoodReductionPoints
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open GlobalTheory.ArcIntegral

namespace GlobalTheory.ArcIntegralMixed

theorem exists_denominator {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] (ϖ : A)
    (hϖ : Irreducible ϖ) (S : Type) [CommRing S] [Algebra (PowerSeries A) S]
    [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (v : S)
    (hv : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (ρ : PowerSeries A →+* R) (ψ : S →+* K),
      ψ.comp (algebraMap (PowerSeries A) S) = (algebraMap R K).comp ρ → IsUnit (ρ PowerSeries.X) →
      ψ v ∈ (algebraMap R K).range) :
    ∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s := by
  obtain ⟨hp, hdvr⟩ := _root_.GlobalTheory.PowerSeriesUniformiser.main A ϖ hϖ
  obtain ⟨R, _, _, _, _, _⟩ : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra (PowerSeries A) R), IsLocalization.AtPrime R (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}) :=
    ⟨_, _, _, hdvr, _, inferInstance⟩
  let K := FractionRing R
  have hρ : Function.Injective (algebraMap (PowerSeries A) R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}))
  let f : PowerSeries A →+* K := (algebraMap R K).comp (algebraMap (PowerSeries A) R)
  have hf : Function.Injective f := (IsFractionRing.injective R K).comp hρ
  have hC : Function.Injective (f.comp (PowerSeries.C (R := A))) := hf.comp PowerSeries.C_injective
  haveI : CharZero K := (RingHom.charZero_iff hC).1 inferInstance
  have h0 : (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) ≠ 0 :=
    mul_ne_zero (fun h => hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero
  have hu : IsUnit (f (PowerSeries.C ϖ * PowerSeries.X)) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hf).2 h0)
  obtain ⟨ψ, hψ⟩ := exists_away_lift (S := S) _ f hu
  have hψi : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, m⟩, ha⟩ :=
      IsLocalization.surj (Submonoid.powers (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A)) x
    have ha0 : a = 0 := hf (by
      have := congrArg ψ ha
      rw [map_mul, hx, zero_mul, hψ] at this
      rw [← this, map_zero])
    rw [ha0, map_zero] at ha
    exact (IsLocalization.map_units S m).mul_left_eq_zero.1 ha
  have hX : (PowerSeries.X : PowerSeries A) ∈ (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).primeCompl := by
    intro hm
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hm
    have := congrArg (PowerSeries.coeff 1) hq
    rw [PowerSeries.coeff_one_X, PowerSeries.coeff_C_mul] at this
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ this.symm)
  obtain ⟨r, hr⟩ := hv R K (algebraMap _ R) ψ (RingHom.ext hψ) (IsLocalization.map_units R ⟨_, hX⟩)
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).primeCompl r
  refine ⟨s, t, fun hd => t.2 (Ideal.mem_span_singleton.2 hd), hψi ?_⟩
  rw [map_mul, hψ, hψ, ← hr]
  exact (map_mul (algebraMap R K) _ _).symm.trans (congrArg (algebraMap R K) hst)

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ g : A →+* B, f = spMap g :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem integral_of_arcs_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.N4 → Y.SplitFibres → IsOpenImmersion Y.j → ∀ (U₀ W₀ : Y.X.Opens) (f₀ : Γ(Y.X, W₀)), (∀ x ∈ U₀, x ∈ Set.range Y.j → x ∈ W₀) → (∀ (a : ArcIn D l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ U₀ → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range) → (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), Countable R → ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range := by
  intro E _ _ _ H Dw l Xo c V Y h3 h4 hS hj U₀ W₀ f₀ hUW harc hgood R K _ _ _ _ _ _ _ z y hcount hU hy h
  by_cases hab : Set.range z ⊆ abLocus Y.t.G
  · exact hgood R K z y hU hy hab h
  have hzW : ∀ {A : Type} [CommRing A] (w : Sp A ⟶ Y.X), Set.range w ⊆ Set.range Y.j → ⊤ ≤ w ⁻¹ᵁ U₀ →
      ⊤ ≤ w ⁻¹ᵁ W₀ := fun w hr hu x hx => hUW _ (hu hx) (hr ⟨x, rfl⟩)
  obtain ⟨io, hio⟩ := exists_spMap (y ≫ pullback.snd _ _)
  obtain ⟨b₀, hover⟩ := exists_spMap (z ≫ Y.s)
  have hcomp : (algebraMap R K).comp b₀ = io.comp V.subtype := spMap_injective (by
    rw [← sp_comp, ← sp_comp, ← hover, ← hio, ← Category.assoc, ← hy, Model.j, ← Y.jQ_over]
    simp only [Category.assoc, pullback.condition])
  have hgen : Set.range (spMap (algebraMap R K) ≫ z) ⊆ Set.range Y.j := by
    rw [← hy]; rintro _ ⟨x, rfl⟩; exact ⟨y x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  have hch : CharZero R := (RingHom.charZero_iff (IsFractionRing.injective R K)).2 inferInstance
  obtain ⟨T, i, hi, hil, hcard⟩ := GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum R hcount
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  obtain ⟨iK, hiK⟩ := exists_frac_lift (K := K) _ hiF
  let y' : Sp T.V ⟶ Y.X := spMap i ≫ z
  let b : V →+* T.V := i.comp b₀
  let io' : c.F →+* T.Fr := iK.comp io
  have hbio : (algebraMap T.V T.Fr).comp b = io'.comp V.subtype := by
    simp only [b, io']
    rw [← RingHom.comp_assoc, ← hiK, RingHom.comp_assoc, hcomp, RingHom.comp_assoc]
  have hy' : y' ≫ Y.s = spMap b := by
    simp only [y', Category.assoc]; rw [hover, sp_comp]
  let zT : Sp T.Fr ⟶ Xo.XF c := spMap iK ≫ y
  have hzT : zT ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' := by
    simp only [y', zT]
    rw [Category.assoc, hy, ← Category.assoc, sp_comp, hiK, ← sp_comp, Category.assoc]
  have hzT' : zT ≫ pullback.snd _ _ = spMap io' := by
    simp only [zT, io']
    rw [Category.assoc, hio, sp_comp]
  clear_value zT
  have hbad : ¬ Set.range y' ⊆ abLocus Y.t.G := fun hy => hab (by
    rintro _ ⟨x, rfl⟩
    rcases point_cases R K x with ⟨p, rfl⟩ | rfl
    · exact range_j_subset Y (hgen ⟨p, by rw [Scheme.Hom.comp_apply]⟩)
    · have e : spMap i (IsLocalRing.closedPoint T.V) = IsLocalRing.closedPoint R := spMap_closedPoint i
      have := hy ⟨IsLocalRing.closedPoint T.V, rfl⟩
      change (spMap i ≫ z) (IsLocalRing.closedPoint T.V) ∈ _ at this
      erw [Scheme.Hom.comp_apply, e] at this; exact this)
  obtain ⟨T', g, ϖ, a, hg, hgf, hϖ, hA⟩ := _root_.GlobalTheory.ArcOfPoint.exists_arcIn_of_bad_reduction E H Dw l Xo c V Y h3 hS T io' b y' zT hbio hy' hzT' hzT hbad
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) T'.V := hϖ.maximalIdeal_eq ▸ T'.cpl
  obtain ⟨χ₀, hχ, hsp⟩ := h4 T'.V (g.comp b) ϖ a (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hover₀, hab₀, hopen, hW⟩ := (hχ χ₀).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ _ _ χ₀).1 hW
  obtain ⟨-, -, evu, hevC, hevX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser T'.V ϖ hϖ T'.cpl
  have hgF : Function.Injective ((algebraMap T'.V T'.Fr).comp g) := (IsFractionRing.injective T'.V T'.Fr).comp hg
  obtain ⟨gF, hgF'⟩ := exists_frac_lift (K := T.Fr) _ hgF
  have hχy : spMap evu ≫ χ₀ = spMap g ≫ y' := hsp hϖ (spMap g ≫ y') evu (by rw [Category.assoc, hy', sp_comp]) (by
      rintro _ ⟨x, rfl⟩
      have e : Out.jK T'.V ≫ spMap g ≫ y' = spMap gF ≫ zT ≫ Y.j := by
        rw [hzT, ← Category.assoc, ← Category.assoc, sp_comp, ← hgF', ← sp_comp]
        rfl
      exact ⟨zT (spMap gF x), by rw [e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩) hA hevC hevX
  have hχz : spMap evu ≫ χ₀ = spMap g ≫ spMap i ≫ z := hχy
  haveI hgl : IsLocalHom g := RingHom.IsIntegral.isLocalHom hgf.to_isIntegral hg
  have hχU : ⊤ ≤ χ₀ ⁻¹ᵁ U₀ := by
    have hc : χ₀ (IsLocalRing.closedPoint (PowerSeries T'.V)) ∈ U₀ := by
      rw [← spMap_closedPoint_of_surjective evu (fun x => ⟨PowerSeries.C x, hevC x⟩)]
      change (spMap evu ≫ χ₀) (IsLocalRing.closedPoint T'.V) ∈ U₀
      rw [hχz]
      exact hU (Set.mem_univ ((spMap g ≫ spMap i) (IsLocalRing.closedPoint T'.V)))
    exact ((IsLocalRing.closed_point_mem_iff (U := χ₀ ⁻¹ᵁ U₀)).1 hc).ge

  let S := Localization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries T'.V)
  let ι : PowerSeries T'.V →+* S := algebraMap _ _
  have huX : IsUnit (ι (PowerSeries.C ϖ * PowerSeries.X)) := IsLocalization.Away.algebraMap_isUnit _
  have hSj : Set.range (spMap ι ≫ χ₀) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    exact hopen (spMap ι x) fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      (show ι (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal from hx) huX)
  have hSW : ⊤ ≤ (spMap ι ≫ χ₀) ⁻¹ᵁ W₀ := hzW _ hSj (le_preimage_comp _ hχU)

  have hcard' : Cardinal.mk T'.Fr ≤ Cardinal.continuum := by
    rw [show Cardinal.mk T'.Fr = Cardinal.mk T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]
    exact mk_le_continuum_of_finite g hgf hcard
  obtain ⟨κ, hκ⟩ := @GlobalTheory.ComplexEmbedding.exists_embedding_of_mk_le_continuum c.F T'.Fr _ _ _
    (gF.comp io').toAlgebra hcard' c.F.val.toRingHom
  let κ₀ : T'.V →+* ℂ := κ.comp (algebraMap T'.V T'.Fr)
  have hκ₀ : Function.Injective κ₀ := κ.injective.comp (IsFractionRing.injective T'.V T'.Fr)
  have hb' : c.F.val.toRingHom.comp V.subtype = κ₀.comp (g.comp b) := by
    rw [← hκ]
    change κ.comp (gF.comp (io'.comp V.subtype)) = κ.comp (((algebraMap T'.V T'.Fr).comp g).comp b)
    rw [← hbio, ← hgF']; rfl
  obtain ⟨h1, h2, -, hL4, hL5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hL4.unifBaseChange hL5 E H Dw l Xo c _ _ Y T'.V ℂ
    (g.comp b) a κ₀ hκ₀ _ hb'
  obtain ⟨hW₁, -⟩ := hbc a₁ p hp
  obtain ⟨W₁, -⟩ := hW₁ χ₀ W
  have hϖ0 : κ₀ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hκ₀ (h0.trans (map_zero _).symm))
  have hXu : IsUnit ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) (PowerSeries.C ϖ * PowerSeries.X)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ (isUnit_map_X κ₀)
    rw [RingHom.comp_apply, PowerSeries.map_C]
    exact ((IsUnit.mk0 _ hϖ0).map _).map _
  obtain ⟨ιC, hιC'⟩ := exists_away_lift (S := S) _ _ hXu
  have hιC : ∀ s, ιC (ι s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ₀ s) :=
    fun s => (hιC' s).trans (RingHom.comp_apply _ _ _)
  have hpt : spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀ = spMap ιC ≫ spMap ι ≫ χ₀ := by
    rw [← Category.assoc, ← Category.assoc (spMap ιC), sp_comp, sp_comp,
      show ιC.comp ι = (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) from RingHom.ext hιC]
  have hLh : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀) ⁻¹ᵁ W₀ := by
    rw [hpt]; exact le_preimage_comp _ hSW
  have hres := harc a₁ (spMap (PowerSeries.map κ₀) ≫ χ₀) ((Y.hasArcData_iff _ _ _ _ _).2 ⟨W₁⟩) (by
      rw [Category.assoc, hover₀, sp_comp, sp_comp, sp_comp, hb']
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C κ₀ _)) (fun x hx => by
      refine hopen (spMap (PowerSeries.map κ₀) x) fun hm => ?_
      have hm' : PowerSeries.map κ₀ (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal := hm
      rw [map_mul, PowerSeries.map_C, PowerSeries.map_X] at hm'
      exact hx ((Ideal.unit_mul_mem_iff_mem _ ((IsUnit.mk0 _ hϖ0).map _)).1 hm'))
    (le_preimage_comp _ hχU) hLh
  rw [ev_factor ιC (spMap ι ≫ χ₀) _ hpt W₀ hSW hLh f₀] at hres

  have hden := exists_denominator ϖ hϖ S (ev (spMap ι ≫ χ₀) W₀ hSW f₀) (by
    intro R' K' _ _ _ _ _ _ _ ρ ψ hψ hρ
    have e : spMap (algebraMap R' K') ≫ spMap ρ ≫ χ₀ = spMap ψ ≫ spMap ι ≫ χ₀ := by
      rw [← Category.assoc, ← Category.assoc (spMap ψ), sp_comp, sp_comp, ← hψ]
    have hW' : ⊤ ≤ (spMap (algebraMap R' K') ≫ spMap ρ ≫ χ₀) ⁻¹ᵁ W₀ := by
      rw [e]; exact le_preimage_comp _ hSW
    rw [← ev_factor ψ (spMap ι ≫ χ₀) _ e W₀ hSW hW' f₀]
    refine hgood R' K' (spMap ρ ≫ χ₀) (spMap ψ ≫ IsOpenImmersion.lift Y.j (spMap ι ≫ χ₀) hSj)
      (le_preimage_comp _ hχU) (by rw [Category.assoc, IsOpenImmersion.lift_fac, e]) ?_ hW'
    rintro _ ⟨x, rfl⟩
    exact (hab₀ (spMap ρ x)).2 fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      (show ρ PowerSeries.X ∈ x.asIdeal from hx) hρ))
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X T'.V ϖ hϖ κ₀ hκ₀ S ιC hιC _ hres hden

  have hϖu : IsUnit ((algebraMap T'.V T'.Fr).comp evu (PowerSeries.C ϖ * PowerSeries.X)) := by
    rw [RingHom.comp_apply, map_mul evu, hevC, hevX]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective T'.V T'.Fr)).2
      (mul_ne_zero hϖ.ne_zero hϖ.ne_zero))
  obtain ⟨φS, hφS⟩ := exists_away_lift (S := S) _ _ hϖu
  have hgi : Function.Injective ((algebraMap T'.V T'.Fr).comp (g.comp i)) :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hg.comp hi)
  obtain ⟨la, hla⟩ := exists_frac_lift (K := K) _ hgi
  have hpt2 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap φS ≫ spMap ι ≫ χ₀ := by
    have e1 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, hla]
    have e2 : spMap φS ≫ spMap ι ≫ χ₀ = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, show φS.comp ι = (algebraMap T'.V T'.Fr).comp evu from RingHom.ext hφS,
        ← sp_comp, Category.assoc, hχz, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
    rw [e1, e2]
  have hval : la (ev (spMap (algebraMap R K) ≫ z) W₀ h f₀) = algebraMap T'.V T'.Fr (evu s) := by
    rw [← ev_factor la (spMap (algebraMap R K) ≫ z) _ rfl W₀ h (le_preimage_comp _ h),
      GlobalTheory.FlagMod.ev_congr hpt2 W₀ _ (le_preimage_comp _ hSW), ev_factor φS _ _ rfl W₀ hSW, hs, hφS]
    rfl
  haveI : IsLocalHom (g.comp i) := inferInstance
  exact mem_range_of_map (g.comp i) la (fun r => RingHom.congr_fun hla r) _ ⟨evu s, hval.symm⟩

end GlobalTheory.ArcIntegralMixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionValueTangentEqAdicExpansionSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

open IsLocalRing GlobalTheory.FormalValue

theorem isLocalRing_dualNumber (V : Type) [CommRing V] [IsLocalRing V] : IsLocalRing (DualNumber V) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

theorem thick_closedPoint (V : Type) [CommRing V] [IsLocalRing V] [IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1))] :
    thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))) = closedPoint V := by
  show PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal V ^ (0 + 1))) (closedPoint _) = closedPoint V
  refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
  haveI : (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem pow_map_le_ker (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    (m.map (algebraMap V (DualNumber V))) ^ (e + 1) ≤
      RingHom.ker ((Ideal.Quotient.mk (m ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) := by
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact ha

theorem ker_dualMap_le (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    RingHom.ker (dualMap (Ideal.Quotient.mk (m ^ (e + 1)))) ≤ (m.map (algebraMap V (DualNumber V))) ^ (e + 1) := by
  intro z hz
  rw [RingHom.mem_ker] at hz
  have h₁ : Ideal.Quotient.mk (m ^ (e + 1)) z.fst = 0 := by
    have := congrArg TrivSqZeroExt.fst hz
    simpa [dualMap] using this
  have h₂ : Ideal.Quotient.mk (m ^ (e + 1)) z.snd = 0 := by
    have := congrArg TrivSqZeroExt.snd hz
    simpa [dualMap] using this
  rw [Ideal.Quotient.eq_zero_iff_mem] at h₁ h₂
  rw [← Ideal.map_pow]
  have hz' : z = algebraMap V (DualNumber V) z.fst + algebraMap V (DualNumber V) z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hz']
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem dualMap_surjective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (dualMap f) := by
  intro w
  obtain ⟨a, ha⟩ := hf w.fst
  obtain ⟨b, hb⟩ := hf w.snd
  refine ⟨(TrivSqZeroExt.inl a + TrivSqZeroExt.inr b : DualNumber A), ?_⟩
  ext <;> simp [dualMap, ha, hb]

theorem value_mul_sumI : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → ∀ (k : ℕ) (jG : U.LG.L.ι) (J : (Sp (DualNumber V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J ψ)) → ∃ W : (DualNumber V)ˣ, (W : DualNumber V).fst * GlobalTheory.MBLow.TanExp.rigVal U.LG jG = GlobalTheory.MBLow.TanExp.rigValD D.toPre (J gm₀.b.left) ∧ ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.toUnifPre.ExpandsAt e k σ f) → GlobalTheory.UT.SumI (IsLocalRing.maximalIdeal V) (fun α => GlobalTheory.MBLow.TanExp.termV J gm₀ (f α)) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) (σ.f fun _ => jG)) := by
  intro V _ _ _ _ hV D A G _ _ _ U y gm₀ hy hT k jG J hjG hJ
  haveI : IsLocalRing (DualNumber V) := isLocalRing_dualNumber V
  haveI : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  haveI : IsAdicComplete (maximalIdeal V) V := hV
  haveI hJd : IsAdicComplete ((maximalIdeal V).map (algebraMap V (DualNumber V))) (DualNumber V) :=
    InertNorm.isAdicComplete_map_of_finite (maximalIdeal V) (DualNumber V)
  have hx : IsFormalPt U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) gm₀ y.left :=
    isFormalPt_of_surjective _ fun e => by
      obtain ⟨ye, h₁, h₂, h₃⟩ := hT e
      exact ⟨DualNumber (V ⧸ maximalIdeal V ^ (e + 1)), inferInstance, dualMap (Ideal.Quotient.mk _), ye,
        dualMap_surjective _ Ideal.Quotient.mk_surjective, ker_dualMap_le V _ e, h₁, h₂, h₃⟩
  have hL : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG := hjG
  have hM : ⊤ ≤ basePt gm₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := hJ _
  refine ⟨(tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹,
    ?_, fun σ f hE => ?_⟩
  · obtain ⟨g₀, hg₀⟩ := exists_isZero D.toPre (Over.mk (spMap (RingHom.id V)))
    haveI : IsAdicComplete ((maximalIdeal V).map (RingHom.id V)) V := by rw [Ideal.map_id]; exact hV
    have h₀ := isFormalPt_zero U.toUnifPre (RingHom.id V) hg₀
    have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := by
      show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    have hb₀ : basePt g₀ = spMap (RingHom.id V) ≫ eSec D.toPre.P.A := by
      refine (congrArg Over.Hom.left hg₀.1).trans ?_
      exact congrArg (· ≫ eSec D.toPre.P.A)
        ((Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap (RingHom.id V))))))
    have hyE : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ y.left = eSec G := hy
    have hL₀ : ⊤ ≤ (spMap (RingHom.id V) ≫ eSec G) ⁻¹ᵁ U.LG.L.U jG := by
      rw [← hyE, ← Category.assoc]; exact top_le_comp hL _
    have hxe : ∀ e, eSec (thickObj V (maximalIdeal V) e G) ≫ (fstG (maximalIdeal V) e G).left =
        spMap ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) ≫
          y.left := fun e => by
      rw [ExpansionValueZero.eSec_fstG, ← hyE]
      show _ = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp
        (TrivSqZeroExt.fstHom V V V).toRingHom)) ≫ _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hM₀ : ⊤ ≤ basePt g₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
      haveI : IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1)) :=
        isLocalRing_quotient_pow (IsLocalRing.maximalIdeal.isMaximal V).ne_top 0
      have HC := hx.hasCoords (e := 0) _ (pow_map_le_ker V _ 0) (hxe 0)
      have h₂ : thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A = spMap _ ≫ gm₀.b.left :=
        (ExpansionValueZero.eSec_pG _ (U.gt 0)).symm.trans HC.2.1
      have h₃ : ⊤ ≤ (thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A) ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
        rw [h₂]; exact top_le_comp hM _
      have h₄ : eSec D.toPre.P.A (thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1)))) ∈
          D.toPre.P.L.U (J gm₀.b.left) := h₃ (Set.mem_univ _)
      rw [thick_closedPoint] at h₄
      rw [hb₀]
      exact top_le_comp (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of V) _ h₄).ge _
    have hfst : (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left) : DualNumber V).fst =
        (tau U.toUnifPre ((maximalIdeal V).map (RingHom.id V)) (spMap (RingHom.id V) ≫ eSec G) jG
          (J gm₀.b.left) : V) := by
      refine eq_of_forall_mk_eq (maximalIdeal V) fun e => ?_
      have a₁ := map_tau_mul_wVal hx hL hM _ (pow_map_le_ker V _ e) (hxe e)
      have a₂ := map_tau_mul_wVal h₀ hL₀ hM₀ (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))
        (by rw [Ideal.map_id, Ideal.mk_ker]) (xe := eSec (thickObj V (maximalIdeal V) e G))
        (by rw [hid, Category.id_comp]; exact ExpansionValueZero.eSec_fstG _ e G)
      exact (IsUnit.of_mul_eq_one_right _ a₂).mul_right_cancel (a₁.trans a₂.symm)
    have r₀ := tau_rig h₀ hb₀ hL₀ hM₀
    have hv : ∀ (U' : (Sp V).Opens) (f : Γ(Sp V, U')),
        valR (spMap (RingHom.id V)) U' f = valR (𝟙 (Sp V)) U' f := fun _ _ => by rw [hid]
    rw [hv, hv] at r₀
    have hW : (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left))⁻¹ : (DualNumber V)ˣ) : DualNumber V).fst *
        (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
          (J gm₀.b.left) : DualNumber V).fst = 1 := by
      rw [← TrivSqZeroExt.fst_mul, Units.inv_mul, TrivSqZeroExt.fst_one]
    unfold rigVal rigValD
    rw [← r₀, ← _root_.mul_assoc, ← hfst, hW, _root_.one_mul]
    rfl
  · refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
    haveI : IsLocalRing (DualNumber V ⧸ ((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1)) :=
      isLocalRing_quotient_pow (ne_top_of_isHausdorff _) n
    obtain ⟨F, hF⟩ := map_secVal_eq U.toUnifPre (hE n)
    obtain ⟨-, h₁⟩ := hF (DualNumber V) ((maximalIdeal V).map (algebraMap V (DualNumber V))) _ gm₀ y.left hx _
      (Ideal.Quotient.mk (((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1))) (by rw [Ideal.mk_ker])
    refine ⟨F, fun T hT => ?_⟩
    have hc : ∀ α ∈ T, CohCharts gm₀ α (J gm₀.b.left) (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
        (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) := fun α _ => by
      refine ⟨fun p _ => Set.mem_iInter.2 fun i => hJ (gm₀.b.left ≫ D.toPre.famφB α i) (Set.mem_univ p),
        fun p _ => Set.mem_iInter.2 fun i => hJ (D.toPre.gtφT (epsR V) gm₀.b α i) (Set.mem_univ p), ?_⟩
      have c : ∀ a, Sum.elim (fun _ : PUnit.{1} => J gm₀.b.left) (Sum.elim (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
          (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i))) a = J (Sum.elim (fun _ : PUnit.{1} => basePt gm₀)
            (Sum.elim (fun a => basePt gm₀ ≫ D.toPre.famφB α a) (coordφ gm₀ α)) a) := by
        rintro (a | a | a) <;> rfl
      exact fun a b hab => (c a).trans ((congrArg J hab).trans (c b).symm)
    have e := h₁ T jG (J gm₀.b.left) (fun α i => J (gm₀.b.left ≫ D.toPre.famφB α i))
      (fun α i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) hT hL hM hc
    rw [Ideal.Quotient.eq] at e
    have key := Ideal.mul_mem_left _
      (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹ :
        (DualNumber V)ˣ) ^ k : DualNumber V) e
    rw [mul_sub, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul] at key
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) key

end GlobalTheory.MBLow.TanExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.LogPole

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev toBase (TF : TorFlag Xo c) (Z : Comp Xo c) : Y₀ TF.X Z ⟶ TF.Y.X := inc₀ TF.X Z ≫ TF.X.π

def IsEigBasis (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) : Prop :=
  (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧
    (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧
    ∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG TF.Y.t (LogKS.chart U) v
      (Pi.single (e ⟨τ, i⟩) (algX TF.Y.s U.1 (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (TF.Y.t.act.act a).left)

def IsCell (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) : Prop :=
  IsAffineOpen W ∧ W ≤ toBase TF Z ⁻¹ᵁ U.1 ∧ W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k ∧
    (∀ σ i j, i < j → L σ i j = 0) ∧ (∀ σ i, IsUnit (L σ i i)) ∧
    (∀ σ i j, j < i → N σ i j = 0) ∧ (∀ σ i, N σ i i = 1) ∧
    ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1)
      (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z)
      (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
      IsCombAtG TF.Y.t (z ≫ toBase TF Z)
        (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩))
        (fun j => ev z W hz ((L σ * N σ) i j)) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left

def cellCoord {R : Type} (N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R) (a : VIx Dw) : R :=
  N a.1 a.2.1.1 a.2.1.2

def IsBaseFrame (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) {K : Type} [CommRing K] [Algebra c.F K]
    (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) : Prop :=
  ∀ σ i, (tv (frVec TF.Y P rfl σ i)).left = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, i⟩)

def KSCompare (TF : TorFlag Xo c) (s : ℚ) : Prop :=
  ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v →
    ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)
      (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ →
    ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1),
      IsBaseFrame TF U e v P hU →
    ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1),
      y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) →
      (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) +
        TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) →
      FlagTan.IsKS (psiSet H) P (y' ≫ pullback.fst _ _) fun k =>
        (s : K) * ev (frX P ≫ TF.Y.j) U.1 hU (Θ (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩))

def logDet {R : Type} [CommRing R] {m : ℕ} (b : Fin m → Derivation ℤ R R) (x : Fin m → R) : R :=
  (Matrix.of fun i j => b j (x i)).det

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactConjugateExistsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_compact_conjugate_exists : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∃ κ : UA σ X.J → ℂ, ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y) := by
  first | exact @GlobalTheory.ShapeUXBas.shapeX | exact GlobalTheory.ShapeUXBas.shapeX | (intros; apply GlobalTheory.ShapeUXBas.shapeX <;> assumption)
end

