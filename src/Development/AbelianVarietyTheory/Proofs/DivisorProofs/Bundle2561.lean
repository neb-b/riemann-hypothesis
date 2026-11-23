module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecKRatioTraitDescendsToFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatioDesc

open ReciprocityTheory.ChartRestriction.G.DVR.TG

theorem pull_fst_app_injective {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}} (h : X ⟶ Sp K)
    (U : X.Opens) : Function.Injective ((pullback.fst h (spMap ψ)).app U).hom := by
  have : Flat (spMap ψ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ψ.toAlgebra
    exact (RingHom.flat_algebraMap_iff).2 inferInstance
  have : Surjective (spMap ψ) := by
    constructor
    intro x
    exact ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩
  exact app_injective_of_flat_surj _ U

variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

theorem scal_mul' (p : Y ⟶ Sp A) (a b : A) : scal p (a * b) = scal p a * scal p b := by
  unfold scal; rw [map_mul, map_mul]

theorem scal_one' (p : Y ⟶ Sp A) : scal p 1 = 1 := by
  unfold scal; rw [map_one, map_one]

theorem scal_comp' (f : Z ⟶ Y) (p : Y ⟶ Sp A) (r : A) : scal (f ≫ p) r = f.appTop.hom (scal p r) := by
  unfold scal; rw [Scheme.Hom.comp_appTop]; rfl

theorem scal_spMap {B : Type} [CommRing B] (g : Y ⟶ Sp B) (ψ : A →+* B) (r : A) :
    scal (g ≫ Spec.map (CommRingCat.ofHom ψ)) r = scal g (ψ r) := by
  rw [scal_comp']
  unfold scal
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  exact (congrArg (fun f => f.hom r) this).symm

theorem gs_top' (f : Z ⟶ Y) (z : Z) (a : Γ(Y, ⊤)) : gs f z ⊤ a = gs (𝟙 Z) z ⊤ (f.appTop.hom a) := by
  have := gs_pull (𝟙 Z) f z ⊤ trivial a
  rw [Category.id_comp] at this
  exact this.symm

theorem gs_zero'' (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs; split_ifs <;> simp

abbrev sg (g : Z ⟶ Sp A) (z : Z) (a : A) : Z.presheaf.stalk z := gs (𝟙 Z) z ⊤ (scal g a)

theorem sg_mul (g : Z ⟶ Sp A) (z : Z) (a b : A) : sg g z (a * b) = sg g z a * sg g z b := by
  unfold sg; rw [scal_mul', gs_mul _ z ⊤ trivial]

theorem sg_one (g : Z ⟶ Sp A) (z : Z) : sg g z 1 = 1 := by
  unfold sg; rw [scal_one', gs_eq _ z ⊤ trivial, map_one, map_one]

theorem sg_isUnit {F : Type} [Field F] (g : Z ⟶ Sp F) (z : Z) {a : F} (ha : a ≠ 0) : IsUnit (sg g z a) :=
  have h1 : sg g z a * sg g z a⁻¹ = 1 := by rw [← sg_mul, mul_inv_cancel₀ ha, sg_one]
  ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end GlobalTheory.Mum.RatioDesc

namespace GlobalTheory.Mum

open GlobalTheory.Mum.RatioDesc

theorem secK_ratio_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s₁ s₂ : SecK C.P.L.L C.α k) (c d : W), c ≠ 0 → d ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom c) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom d) * sval s₂ p' z J) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k s₁ s₂ c d hc hd H
  obtain ⟨ψ, hψR, hψ⟩ := _root_.GlobalTheory.Mum.Modif.exists_generic_factor R C.toModif W T.φ T.inj T.ξ T.ξ_π
  let Y : Scheme.{0} := pullback C.A.A.hom (spMap ψ)
  let q : Y ⟶ C.A.A.left := pullback.fst C.A.A.hom (spMap ψ)
  let g : Y ⟶ Sp (FractionRing W) := pullback.snd C.A.A.hom (spMap ψ)
  have hw : (q ≫ C.α) ≫ C.G.hom = (g ≫ jK W) ≫ T.ξ := by
    simp only [Category.assoc]
    rw [C.α_cart.1.w, ← Category.assoc q, pullback.condition, Category.assoc]
    exact congrArg (g ≫ ·) hψ
  let p := T.cart.1.lift (q ≫ C.α) (g ≫ jK W) hw
  have hp : p ≫ T.β = q ≫ C.α := T.cart.1.lift_fst _ _ _
  have hpG : p ≫ T.G.hom = g ≫ jK W := T.cart.1.lift_snd _ _ _
  have hsc : ∀ (y : Y) (w : W),
      gs p y ⊤ (scal T.G.hom w) = sg g y (algebraMap W (FractionRing W) w) := by
    intro y w
    rw [gs_top', ← scal_comp', hpG, scal_spMap]

  set c' := algebraMap W (FractionRing W) c with hc'
  set d' := algebraMap W (FractionRing W) d with hd'
  have hc0 : c' ≠ 0 := fun h => hc (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  have hd0 : d' ≠ 0 := fun h => hd (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  let Uc : (Fin 1 → C.P.L.L.ι) → C.A.A.left.Opens := fun j => LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) j
  have G0 : ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      sg g y c' * gs q y (Uc j) (s₁.f j) = sg g y d' * gs q y (Uc j) (s₂.f j) := by
    intro j y hy
    obtain ⟨J, hJ, hJj⟩ := exists_good C.P.L.L C.P.L.isLB y (fun _ : Unit => q ≫ C.α) (fun _ => j 0)
      (fun _ _ _ => rfl) (fun _ => by simpa using Set.mem_iInter.1 hy 0)
    have e := H Y p q hp y J hJ
    have hj : ∀ i : Fin 1, J (q ≫ C.α) = j i := fun i => by rw [Subsingleton.elim i 0]; exact hJj ()
    rw [hsc, hsc, sval_of s₁ q y J j hj, sval_of s₂ q y J j hj] at e
    exact e

  have key : ∃ m₀ : FractionRing R, m₀ ≠ 0 ∧ ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      gs q y (Uc j) (s₁.f j) = sg g y (ψ m₀) * gs q y (Uc j) (s₂.f j) := by
    by_cases h0 : ∀ j, s₂.f j = 0
    · refine ⟨1, one_ne_zero, fun j y hy => ?_⟩
      have e := G0 j y hy
      have hz : gs q y (Uc j) (s₂.f j) = 0 := by rw [h0 j]; exact gs_zero'' _ _ _
      rw [hz, mul_zero] at e
      rw [hz, mul_zero]
      exact (sg_isUnit g y hc0).mul_left_cancel (e.trans (mul_zero _).symm)
    · push Not at h0
      obtain ⟨j₀, hj₀⟩ := h0
      have e : ((q.app (Uc j₀)).hom (s₁.f j₀)) = (q.app (Uc j₀)).hom (s₂.f j₀) * resTop _ (scal g (d' / c')) := by
        apply fn_ext
        intro y hy
        have hy' : q ((𝟙 Y) y) ∈ Uc j₀ := by simpa using hy
        have e1 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₁.f j₀)
        have e2 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₂.f j₀)
        rw [Category.id_comp] at e1 e2
        rw [gs_mul _ y _ hy, gs_res _ y le_top hy]
        erw [e1, e2]
        apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j₀ y hy]
        change _ = sg g y c' * (_ * sg g y (d' / c'))
        rw [mul_comm _ (sg g y (d' / c')), ← _root_.mul_assoc, ← sg_mul, hcd]
      obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.mem_range_of_base_change_ratio_sections ψ C.A.A.hom (Uc j₀) (s₁.f j₀) (s₂.f j₀) (d' / c') hj₀ e
      refine ⟨m₀, fun h => ?_, fun j y hy => ?_⟩
      · rw [h, map_zero] at hm₀
        exact div_ne_zero hd0 hc0 hm₀.symm
      · apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j y hy, hm₀, ← _root_.mul_assoc, ← sg_mul, hcd]

  obtain ⟨m₀, hm0, hm⟩ := key
  obtain ⟨r, t, ht, hrt⟩ := IsFractionRing.div_surjective (A := R) m₀
  have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
  have ht' : algebraMap R (FractionRing R) t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hm0
    rw [← hrt, map_zero, zero_div]
  refine ⟨r, t, hr0, ht0, ?_⟩
  have hK : algebraMap R (FractionRing R) t * m₀ = algebraMap R (FractionRing R) r := by
    rw [← hrt]; field_simp
  let F₁ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₁.f j
  let F₂ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₂.f j
  have sec : ∀ j : Fin 1 → C.P.L.L.ι, resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j =
      resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j := by
    intro j
    apply pull_fst_app_injective ψ C.A.A.hom (Uc j)
    apply fn_ext
    intro y hy
    have hy' : q ((𝟙 Y) y) ∈ Uc j := by simpa using hy
    have e1 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j)
    have e2 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j)
    rw [Category.id_comp] at e1 e2
    erw [e1, e2]
    rw [gs_mul q y _ hy, gs_mul q y _ hy, gs_res q y le_top hy, gs_res q y le_top hy, gs_top' q, gs_top' q,
      ← scal_comp', ← scal_comp', pullback.condition, scal_spMap, scal_spMap]
    change sg g y _ * _ = sg g y _ * _
    rw [hm j y hy, ← _root_.mul_assoc, ← sg_mul, ← map_mul, hK]
  intro Z p' z J hJ
  have hm' : p' z ∈ Uc (fun _ => J (p' ≫ C.α)) := hJ.mem (fun _ : Fin 1 => C.α) p'
  have e := congrArg (gs p' z (Uc (fun _ => J (p' ≫ C.α)))) (sec (fun _ => J (p' ≫ C.α)))
  rw [gs_mul p' z _ hm', gs_mul p' z _ hm', gs_res p' z le_top hm', gs_res p' z le_top hm'] at e
  exact e

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianActionEqUniversalAtFieldPointsOfTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ActField

theorem exists_factor_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y : RatModel o Ω) (K : Type) [Field K]
    (s : Sp K ⟶ Y.Z), ∃ (z : Y.Z) (j : Sp (Y.O z) ⟶ Y.Z) (s' : Sp K ⟶ Sp (Y.O z)),
      spMap (algebraMap (Y.O z) Ω) ≫ j = Y.pt ∧ s' ≫ j = s ∧ j (IsLocalRing.closedPoint (Y.O z)) = z ∧ ∀ w, s w = z := by
  intro o Ω _ _ _ Y K _ s
  have hsz : ∀ w, s w = s (IsLocalRing.closedPoint K) := fun w => by
    rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
  let z := s (IsLocalRing.closedPoint K)
  let e := Y.stalkEquiv z
  let E : Y.Z.presheaf.stalk z ⟶ CommRingCat.of (Y.O z) := CommRingCat.ofHom e.toRingHom
  let E' : CommRingCat.of (Y.O z) ⟶ Y.Z.presheaf.stalk z := CommRingCat.ofHom e.symm.toRingHom
  have hEE : E ≫ E' = 𝟙 _ := by ext a; exact e.symm_apply_apply a
  refine ⟨z, Spec.map E ≫ Y.Z.fromSpecStalk z, Spec.map (E' ≫ Scheme.stalkClosedPointTo s), ?_, ?_, ?_, hsz⟩
  · have h1 : E ≫ CommRingCat.ofHom (algebraMap (Y.O z) Ω) =
        Y.Z.presheaf.stalkSpecializes (Y.pt_specializes (IsLocalRing.closedPoint Ω) z) ≫
          Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Y.pt := by
      ext a; rfl
    show Spec.map _ ≫ _ = _
    rw [← Category.assoc, ← Spec.map_comp, h1, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, hEE, Category.id_comp,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · haveI : IsLocalHom E.hom := ⟨fun a ha => by
      have h := ha.map e.symm.toRingHom
      have h' : e.symm.toRingHom (E.hom a) = a := e.symm_apply_apply a
      rwa [h'] at h⟩
    change Y.Z.fromSpecStalk z ((Spec.map E) (IsLocalRing.closedPoint (CommRingCat.of (Y.O z)))) = z
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem exists_factor_i : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (O : Type) [CommRing O] [IsLocalRing O] (g : Sp O ⟶ C.Z),
      g (IsLocalRing.closedPoint O) ∈ Set.range C.i → ∃ v : Sp O ⟶ Xo.XF c, g = v ≫ C.i := by
  intro E _ _ _ H Dw l Xo c C O _ _ g hg
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  obtain ⟨x, hx⟩ := hg
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ C.z)
  have hpt : (Spec.map φ) (IsLocalRing.closedPoint O) =
      (spMap C.b) ((pullback.snd C.z (spMap C.b)) (C.iF x)) := by
    rw [hφ]
    change C.z (g _) = _
    rw [← hx]
    change ((C.iF ≫ pullback.fst C.z (spMap C.b)) ≫ C.z) x = ((C.iF ≫ pullback.snd C.z (spMap C.b)) ≫ spMap C.b) x
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hbot : Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) = ⊥ := by
    have hc := congrArg PrimeSpectrum.asIdeal hpt
    change Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) = Ideal.comap C.b _ at hc
    haveI := ((pullback.snd C.z (spMap C.b)) (C.iF x)).isPrime
    rw [hc, Ideal.eq_bot_of_prime ((pullback.snd C.z (spMap C.b)) (C.iF x)).asIdeal]
    exact Ideal.comap_bot_of_injective _ C.inj
  have hunit : ∀ y : nonZeroDivisors C.o, IsUnit (φ.hom y) := fun y => by
    by_contra hy
    have hm : (y : C.o) ∈ Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) := (IsLocalRing.mem_maximalIdeal _).2 hy
    rw [hbot, Ideal.mem_bot] at hm
    exact nonZeroDivisors.ne_zero y.2 hm
  let ψF : c.F →+* O := IsLocalization.lift (M := nonZeroDivisors C.o) (S := c.F) hunit
  have hψF : ψF.comp C.b = φ.hom := IsLocalization.lift_comp hunit
  have w : g ≫ C.z = Spec.map (CommRingCat.ofHom ψF) ≫ spMap C.b := by
    rw [← hφ]
    show _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (RingHom.congr_fun hψF a).symm
  let g' : Sp O ⟶ pullback C.z (spMap C.b) := pullback.lift g _ w
  have hg'1 : g' ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) := (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  have hcl : g' (IsLocalRing.closedPoint O) ∈ Set.range C.iF := ⟨x, hinj (by
    change (C.iF ≫ pullback.fst _ _) x = (g' ≫ pullback.fst _ _) _
    rw [hg'1]; exact hx)⟩
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    haveI := C.iF_open
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map g'.continuous).mem_open C.iF.isOpenEmbedding.isOpen_range hcl
  haveI := C.iF_open
  refine ⟨IsOpenImmersion.lift C.iF g' hrange, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hg'1]

theorem isNoetherianRing_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (Y : RatModel o Ω)
    (z : Y.Z), IsNoetherianRing (Y.O z) := by
  intro o Ω _ _ _ _ Y z
  haveI := Y.lft
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  exact isNoetherianRing_of_ringEquiv _ (Y.stalkEquiv z)


set_option maxHeartbeats 4000000 in
theorem exists_action_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ wi : UWit X₁, ∃ (f : 𝓞 E → (out.G ⟶ out.G)) (ψ : wi.G.left ⟶ out.G.left), (∀ a, IsMonHom (f a)) ∧ IsGrpPullback wi.G out.G Y.pt ψ ∧ (∀ (T : Scheme.{0}) (w : T ⟶ wi.G.left), ∃ x' : T ⟶ pullback X₁.ρ.P.A.hom out.u₀, x' ≫ out.φ = w ≫ ψ ∧ x' ≫ pullback.fst _ _ = w ≫ wi.α) ∧ (∀ (a : 𝓞 E) (e : wi.G ⟶ wi.G), e.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e.left ≫ ψ = ψ ≫ (f a).left) ∧ ∀ (K : Type) [Field K] (s : Sp K ⟶ Y.Z) (y : Sp K ⟶ Xo.XF c), s ≫ r = y ≫ C.i → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G s γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hr wi

  have hrange : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hO.ne (x := w) trivial
  let xU : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hrange
  have hxU : xU ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hu₀ : xU ≫ out.u₀ = spMap X₁.S.R.val.toRingHom := out.u₀_gen xU hxU
  have wℓ : wi.α ≫ X₁.ρ.P.A.hom = (wi.G.hom ≫ xU) ≫ out.u₀ := by
    rw [Category.assoc, hu₀]; exact wi.hα.1.w
  let ℓ : wi.G.left ⟶ pullback X₁.ρ.P.A.hom out.u₀ := pullback.lift wi.α (wi.G.hom ≫ xU) wℓ
  have hℓα : ℓ ≫ pullback.fst _ _ = wi.α := pullback.lift_fst _ _ _
  have hℓ : IsGrpPullback wi.G ((Over.pullback out.u₀).obj X₁.ρ.P.A) xU ℓ :=
    (isGrpPullback_pullback X₁.ρ.P.A out.u₀).cancel (wi.hα.congr hu₀.symm hℓα.symm)
      (pullback.lift_snd _ _ _)
  let ψ : wi.G.left ⟶ out.G.left := ℓ ≫ out.φ
  have hψ : IsGrpPullback wi.G out.G Y.pt ψ := (hℓ.comp out.cart).congr hxU rfl

  obtain ⟨f₀, hf₀, -⟩ := _root_.GlobalTheory.PullAction.exists_action_pull E H Dw l Xo c (Sp X₁.Ω₁) X₁.uΩ wi.G wi.β wi.hβ
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hψ (isGrpPullback_pullback out.G Y.pt)
  haveI := he
  have hf' : ∀ a, IsMonHom (e.inv ≫ f₀ a ≫ e.hom) := fun a => by
    haveI := (hf₀ a).1
    infer_instance
  have hF : ∀ a, ∃ F : out.G ⟶ out.G, IsMonHom F ∧ (Over.pullback Y.pt).map F = e.inv ≫ f₀ a ≫ e.hom :=
    fun a => (out.endo _ (hf' a)).exists
  choose F hFm hFe using hF
  have hmap : ∀ {S' : Scheme.{0}} (q : S' ⟶ Y.Z) (a : 𝓞 E),
      ((Over.pullback q).map (F a)).left ≫ pullback.fst out.G.hom q = pullback.fst out.G.hom q ≫ (F a).left :=
    fun q a => pullback.lift_fst _ _ _
  have hei : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have gen₀ : ∀ a, (f₀ a).left ≫ ψ = ψ ≫ (F a).left := fun a => by
    have key : e.hom.left ≫ ((Over.pullback Y.pt).map (F a)).left = (f₀ a).left ≫ e.hom.left := by
      rw [hFe a, Over.comp_left, Over.comp_left, ← Category.assoc, hei, Category.id_comp]
    calc (f₀ a).left ≫ ψ = ((f₀ a).left ≫ e.hom.left) ≫ pullback.fst _ _ := by rw [← heψ, Category.assoc]
      _ = (e.hom.left ≫ ((Over.pullback Y.pt).map (F a)).left) ≫ pullback.fst _ _ := by rw [key]
      _ = ψ ≫ (F a).left := by rw [Category.assoc, hmap, ← Category.assoc, heψ]
  have uniq : ∀ (a : 𝓞 E) (e' : wi.G ⟶ wi.G), e'.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e' = f₀ a :=
    fun a e' h => Over.OverMorphism.ext (wi.hβ.1.hom_ext (h.trans (hf₀ a).2.symm) (by rw [Over.w, Over.w]))
  refine ⟨F, ψ, hFm, hψ, fun T w => ⟨w ≫ ℓ, Category.assoc _ _ _, by rw [Category.assoc, hℓα]⟩,
    fun a e' h => (uniq a e' h) ▸ gen₀ a, ?_⟩

  intro K _ s y hsy tK ⟨mm⟩
  haveI : IsNoetherianRing X₁.o₁ := by haveI := X₁.ar.ded; infer_instance
  obtain ⟨z₀, j, s', hj, hs', hjz, hsz⟩ := exists_factor_localRing _ _ Y K s
  haveI := isNoetherianRing_O _ _ Y z₀
  haveI := RatModel.isIntegrallyClosed_O hO.normal z₀
  have hpt : (j ≫ r) (IsLocalRing.closedPoint (Y.O z₀)) = C.i (y (IsLocalRing.closedPoint K)) := by
    change r (j (IsLocalRing.closedPoint (Y.O z₀))) = _
    rw [hjz, ← hsz (IsLocalRing.closedPoint K)]
    change (s ≫ r) _ = (y ≫ C.i) _
    rw [hsy]
  obtain ⟨v, hv⟩ := exists_factor_i E H Dw l Xo c C (Y.O z₀) (j ≫ r) ⟨_, hpt.symm⟩
  haveI := C.isPreimmersion_i
  have hsv : s' ≫ v = y := (cancel_mono C.i).1 (by rw [Category.assoc, ← hv, ← Category.assoc, hs', hsy])
  have hgv : spMap (algebraMap (Y.O z₀) X₁.Ω₁) ≫ v = X₁.uΩ :=
    (cancel_mono C.i).1 (by rw [Category.assoc, ← hv, ← Category.assoc, hj, hr])
  haveI : IsCommMonObj ((Over.pullback j).obj out.G) := Functor.isCommMonObj_obj
  have hAb : IsAbelianScheme ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G) :=
    by
      have hA : IsAbelianScheme Xo.univ.t.G := (Obj.toPolAV Xo.univ).isAb
      haveI := hA.comm
      haveI := hA.smooth
      haveI := hA.proper
      haveI := hA.geomConnected
      exact ⟨Functor.isCommMonObj_obj,
        by change Smooth (pullback.snd _ _); infer_instance,
        by change IsProper (pullback.snd _ _); infer_instance,
        by change GeometricallyConnected (pullback.snd _ _); infer_instance⟩
  have hSe := IsSemiAbelian.pullback j out.G out.semi
  have wa : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (algebraMap (Y.O z₀) X₁.Ω₁)) ≫ v ≫ pullback.fst _ _ := by
    rw [wi.hβ.1.w, ← hgv]; simp only [Category.assoc]
  let aa := pullback.lift _ _ wa
  have haa : aa ≫ pullback.fst _ _ = wi.β := pullback.lift_fst _ _ _
  have ha : IsGrpPullback wi.G ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G)
      (spMap (algebraMap (Y.O z₀) X₁.Ω₁)) aa :=
    (isGrpPullback_pullback Xo.univ.t.G _).cancel (wi.hβ.congr (by rw [← hgv, Category.assoc]) haa.symm)
      (pullback.lift_snd _ _ _)
  have wg : ψ ≫ out.G.hom = (wi.G.hom ≫ spMap (algebraMap (Y.O z₀) X₁.Ω₁)) ≫ j := by
    rw [hψ.1.w, Category.assoc, hj]
  let gg := pullback.lift _ _ wg
  have hgg : gg ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hg : IsGrpPullback wi.G ((Over.pullback j).obj out.G) (spMap (algebraMap (Y.O z₀) X₁.Ω₁)) gg :=
    (isGrpPullback_pullback out.G j).cancel (hψ.congr hj.symm hgg.symm) (pullback.lift_snd _ _ _)
  obtain ⟨i, hi, hai, hLi, hEi⟩ := _root_.GlobalTheory.UPoinc.iso_of_common_generic_fibre (Y.O z₀) _ ((Over.pullback j).obj out.G) hAb hSe X₁.Ω₁ wi.G aa gg ha hg
  haveI := hi
  obtain ⟨f₁, hf₁, hT⟩ := _root_.GlobalTheory.PullAction.exists_action_pull E H Dw l Xo c (Sp (Y.O z₀)) v ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G) (pullback.fst _ _)
    (isGrpPullback_pullback Xo.univ.t.G (v ≫ pullback.fst _ _))
  have mm' : SABMap tK Xo.univ.t ((s' ≫ v) ≫ pullback.fst _ _) := hsv ▸ mm
  obtain ⟨γ₀, hγ₀, -, hLγ, hactγ⟩ := hT (Sp K) s' tK mm'
  refine ⟨γ₀ ≫ i.hom.left ≫ pullback.fst out.G.hom j, ?_, ?_, ?_⟩
  · exact (hγ₀.comp ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback out.G j))).congr
      (by rw [Category.id_comp, hs']) rfl
  · have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    have hOL := out.L.isLB
    have sA : LBIso (X₁.ρ.P.L.pull wi.α) (out.L.L.pull ψ) :=
      GenSpread.lbIso_pull_comp ℓ hℓα.symm rfl (LBIso.symm ⟨out.w, out.w_gen⟩)
    have sB : LBIso (Xo.univ.t.PP.L.pull wi.β) (out.L.L.pull ψ) :=
      LBIso.trans (pull_isLB hU _) (pull_isLB hP _) (pull_isLB hOL _) wi.hL.symm sA
    have sC : LBIso ((Xo.univ.t.PP.L.pull (pullback.fst _ _)).pull aa)
        ((out.L.L.pull (pullback.fst out.G.hom j)).pull gg) :=
      LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (pull_isLB (pull_isLB hOL _) _)
        (GenSpread.lbIso_pull_pull hU aa haa.symm).symm
        (LBIso.trans (pull_isLB hU _) (pull_isLB hOL _) (pull_isLB (pull_isLB hOL _) _) sB
          (GenSpread.lbIso_pull_pull hOL gg hgg.symm))
    have sD := hLi _ _ (pull_isLB hU _) (pull_isLB hOL _) sC
    exact LBIso.trans tK.PP.isLB (pull_isLB (pull_isLB hU _) _) (pull_isLB hOL _) hLγ
      (LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB (pull_isLB (pull_isLB hOL _) _) _) (pull_isLB hOL _)
        (GenSpread.lbIso_pullback sD γ₀)
        (LBIso.trans (pull_isLB (pull_isLB (pull_isLB hOL _) _) _) (pull_isLB (pull_isLB hOL _) _) (pull_isLB hOL _)
          (GenSpread.lbIso_pull_pull (pull_isLB hOL _) γ₀ rfl).symm
          (GenSpread.lbIso_pull_pull hOL (γ₀ ≫ i.hom.left) (Category.assoc _ _ _).symm).symm))
  · intro a
    have h1 : (f₀ a).left ≫ aa = aa ≫ (f₁ a).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, haa, Category.assoc, (hf₁ a).2, ← Category.assoc, haa, (hf₀ a).2]
      · have w1 := Over.w (f₁ a)
        have w0 := Over.w (f₀ a)
        erw [Category.assoc, pullback.lift_snd, Category.assoc, w1, pullback.lift_snd, ← Category.assoc, w0]
    have h2 : (f₀ a).left ≫ gg = gg ≫ ((Over.pullback j).map (F a)).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hmap, hgg, ← Category.assoc gg, hgg, gen₀]
      · have w1 := Over.w ((Over.pullback j).map (F a))
        have w0 := Over.w (f₀ a)
        erw [Category.assoc, pullback.lift_snd, Category.assoc, w1, pullback.lift_snd, ← Category.assoc, w0]
    have h3 := congrArg Over.Hom.left (hEi (f₁ a) ((Over.pullback j).map (F a)) (f₀ a) h1 h2)
    rw [Over.comp_left, Over.comp_left] at h3
    rw [← Category.assoc, hactγ a]
    simp only [Category.assoc]
    rw [← Category.assoc (f₁ a).left, h3, Category.assoc, hmap]

end GlobalTheory.UPoinc.ActField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeBis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem semiAbelianLieSeminegative : GlobalTheory.Published.SemiAbelianLieSeminegative := by
  intro k _ _ C _ hs hp hc G _ hG W r hW i hi
  obtain ⟨C', _, π, hC', hdesc⟩ := _root_.GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange k C ⟨hs, hp, hc⟩ (AlgebraicClosure k)
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  refine hdesc (Lie G) ?_ W r hW i hi
  exact GlobalTheory.NeronCurve.LieDescent.semiNeg_of_iso (GlobalTheory.NeronCurve.LieDescent.lieBaseIso π G).symm
    (_root_.GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed (AlgebraicClosure k) C' hC' _ (IsSemiAbelian.pullback π G hG))

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ZH.RatModel

theorem stalkHom_stalkMap_algebraMap : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (p : M₂.Z ⟶ M₁.Z), M₂.pt ≫ p = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₂ : M₂.Z) (x : M₁.Z.presheaf.stalk (p z₂)), M₂.stalkHom z₂ ((p.stalkMap z₂).hom x) = algebraMap Ω₁ Ω₂ (M₁.stalkHom (p z₂) x) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ p hp z₂ x
  obtain ⟨U, hU, f, rfl⟩ := M₁.Z.presheaf.germ_exist x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ, RatModel.stalkHom_germ (M := M₂) (show z₂ ∈ p ⁻¹ᵁ U from hU)]
  rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valF_eq_valR, ← GlobalTheory.Points.valR_comp, hp,
    GlobalTheory.Points.valR_spMap_comp _ _ _ (M₁.top_le_preimage_pt ⟨_, hU⟩)]

end GlobalTheory.ZH.RatModel
end

