module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace GlobalTheory

theorem isStandardSmoothOfRelativeDimension_away_jacobian {R S ι σ : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Finite ι] [Finite σ]
    (P : Algebra.PreSubmersivePresentation R S ι σ) (T : Type*) [CommRing T] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] [IsLocalization.Away P.jacobian T] :
    Algebra.IsStandardSmoothOfRelativeDimension P.dimension R T := by
  let Q := Algebra.SubmersivePresentation.localizationAway T P.jacobian
  let P' : Algebra.SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { __ := Q.toPreSubmersivePresentation.comp P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit _).mul Q.jacobian_isUnit }
  refine P'.isStandardSmoothOfRelativeDimension ?_
  refine (Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension
    Q.toPreSubmersivePresentation P).trans ?_
  simp [Algebra.Presentation.dimension]

theorem isReduced_of_free_of_geometricallyReduced {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [_root_.IsReduced R] [Module.Free R A]
    [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R A)))] : _root_.IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  let b := Module.Free.chooseBasis R A
  refine b.repr.injective (Finsupp.ext fun k => ?_)
  rw [map_zero, Finsupp.zero_apply]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.mpr fun p hp => ?_)
  have h₁ : AlgebraicGeometry.IsReduced (pullback (Spec.map (CommRingCat.ofHom
      (algebraMap R p.ResidueField))) (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :=
    GeometricallyReduced.geometrically_isReduced _ _ _ (IsPullback.of_hasPullback _ _).flip
  have h₂ : _root_.IsReduced (TensorProduct R p.ResidueField A) :=
    (affine_isReduced_iff (.of (TensorProduct R p.ResidueField A))).mp
      (isReduced_of_isOpenImmersion (pullbackSpecIso R p.ResidueField A).inv)
  have h₃ : (1 : p.ResidueField) ⊗ₜ[R] a = 0 :=
    (ha.map (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField))).eq_zero
  have h₄ := congrArg (fun x => (b.baseChange p.ResidueField).repr x k) h₃
  simp only [Module.Basis.baseChange_repr_tmul, map_zero, Finsupp.zero_apply,
    ← Algebra.algebraMap_eq_smul_one] at h₄
  exact Ideal.algebraMap_residueField_eq_zero.mp h₄

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


open Polynomial in
instance free_coordinateRing : Module.Free R W.toAffine.CoordinateRing :=
  inferInstance

section Presentation

open MvPolynomial

variable (i : Fin 3)

def dehomRelation : Fin 2 → MvPolynomial (Fin 3) R := ![W.toProjective.polynomial, X i - 1]

abbrev DehomRing : Type u := MvPolynomial (Fin 3) R ⧸ Ideal.span (Set.range (dehomRelation W i))

def dehomCoord (j : Fin 3) : DehomRing W i := Ideal.Quotient.mk _ (X j)

@[simp] theorem dehomCoord_self : dehomCoord W i i = 1 :=
  Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨1, rfl⟩)

theorem eval₂_dehomCoord (p : MvPolynomial (Fin 3) R) :
    eval₂ (algebraMap R (DehomRing W i)) (dehomCoord W i) p = Ideal.Quotient.mk _ p :=
  RingHom.congr_fun (f := eval₂Hom (algebraMap R (DehomRing W i)) (dehomCoord W i))
    (MvPolynomial.ringHom_ext (fun r => by simp; rfl) (fun i => by simp [dehomCoord])) p

theorem equation_dehomCoord :
    (W.map (algebraMap R (DehomRing W i))).toProjective.Equation (dehomCoord W i) := by
  change (W.toProjective.map _).Equation _
  rw [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
    MvPolynomial.eval_map, eval₂_dehomCoord, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨0, rfl⟩

theorem bijective_awayEval_dehom : Function.Bijective
    (awayEval W i (algebraMap R _) (dehomCoord W i) (equation_dehomCoord W i) (by simp)) := by
  have hm := awayEval_awayCoord_mul W i (algebraMap R _) (dehomCoord W i)
    (equation_dehomCoord W i) (by simp)
  set ℓ := awayEval W i (algebraMap R _) (dehomCoord W i) (equation_dehomCoord W i) (by simp)
  simp only [dehomCoord_self, mul_one] at hm
  have hr : ∀ r, ℓ (awayConst W i r) = algebraMap R _ r := awayEval_awayConst W i _ _ _ _
  let g : DehomRing W i →+* AwayRing W i :=
    Ideal.Quotient.lift _ (eval₂Hom (awayConst W i) (awayCoord W i)) (by
      intro a ha
      refine (show Ideal.span (Set.range (dehomRelation W i)) ≤ RingHom.ker _ from ?_) ha
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      fin_cases k
      · have h := equation_awayCoord W i
        change (W.toProjective.map _).Equation _ at h
        rwa [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
          MvPolynomial.eval_map] at h
      · simp [dehomRelation])
  have gr : ∀ r, g (algebraMap R _ r) = awayConst W i r := fun r => eval₂_C ..
  have gc : ∀ j, g (dehomCoord W i j) = awayCoord W i j := fun j => eval₂_X ..
  refine (RingEquiv.ofRingHom ℓ g ?_ ?_).bijective
  · exact Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext
      (fun r => (congrArg ℓ (gr r)).trans (hr r)) (fun j => (congrArg ℓ (gc j)).trans (hm j)))
  · exact awayRing_hom_ext W i (fun r => by simp [hr, gr]) (fun j => by simp [hm, gc])

def dehomChart : Spec (.of (DehomRing W i)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom
    (awayEval W i (algebraMap R _) (dehomCoord W i) (equation_dehomCoord W i) (by simp))) ≫
      awayChart W i

private theorem isIso_dehomChart_eval : IsIso (CommRingCat.ofHom
    (awayEval W i (algebraMap R _) (dehomCoord W i) (equation_dehomCoord W i) (by simp))) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_awayEval_dehom W i)

instance : IsOpenImmersion (dehomChart W i) := by
  have := isIso_dehomChart_eval W i
  unfold dehomChart
  infer_instance

theorem opensRange_dehomChart : (dehomChart W i).opensRange = coordOpen W i := by
  have := isIso_dehomChart_eval W i
  unfold dehomChart
  rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_awayChart]

theorem dehomChart_toSpec : dehomChart W i ≫ toSpec W =
    Spec.map (CommRingCat.ofHom (algebraMap R (DehomRing W i))) := by
  rw [dehomChart, Category.assoc, awayChart_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact awayEval_awayConst W i _ _ _ (by simp) r

end Presentation

theorem of_dehomChart (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (h : ∀ i, P (Spec.map (CommRingCat.ofHom (algebraMap R (DehomRing W i))))) :
    P (toSpec W) := by
  refine IsZariskiLocalAtSource.of_openCover (P := P)
    (Scheme.Cover.mkOfCovers (Fin 3) _ (dehomChart W) fun x => ?_) fun (i : Fin 3) => ?_
  · rcases coordOpen_one_sup_coordOpen_two W |>.ge (Set.mem_univ x) with hx | hx
    · rw [← opensRange_dehomChart] at hx
      exact ⟨1, hx⟩
    · rw [← opensRange_dehomChart] at hx
      exact ⟨2, hx⟩
  · change P (dehomChart W i ≫ toSpec W)
    rw [dehomChart_toSpec]
    exact h i

section Smooth

open MvPolynomial

theorem nonsingular_of_Δ_ne_zero {F : Type*} [Field F] {V : WeierstrassCurve F} (hΔ : V.Δ ≠ 0)
    {P : Fin 3 → F} (h : V.toProjective.Equation P) {i : Fin 3} (hi : P i ≠ 0) :
    V.toProjective.Nonsingular P := by
  by_cases hz : P 2 = 0
  · have hx := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero h hz
    have hy : P 1 ≠ 0 := fun hy => hi <| by fin_cases i <;> assumption
    refine (WeierstrassCurve.Projective.nonsingular_of_Z_eq_zero hz).mpr ⟨h, Or.inr ?_⟩
    simpa [hx] using hy
  · exact (WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero hz).mpr <|
      (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp <|
        (WeierstrassCurve.Projective.equation_of_Z_ne_zero hz).mp h

theorem span_pderiv_eq_top {A : Type*} [CommRing A] {V : WeierstrassCurve A} (hΔ : IsUnit V.Δ)
    {P : Fin 3 → A} (h : V.toProjective.Equation P) {i : Fin 3} (hi : IsUnit (P i)) :
    Ideal.span (Set.range fun j : {j : Fin 3 // j ≠ i} =>
      MvPolynomial.eval P (pderiv j.1 V.toProjective.polynomial)) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let := Ideal.Quotient.field m
  set g : A →+* A ⧸ m := Ideal.Quotient.mk m
  have hi' : (g ∘ P) i ≠ 0 := (hi.map g).ne_zero
  have hns : (V.map g).toProjective.Nonsingular (g ∘ P) :=
    nonsingular_of_Δ_ne_zero (by rw [WeierstrassCurve.map_Δ]; exact (hΔ.map g).ne_zero)
      (h.map g) hi'
  set D : Fin 3 → A ⧸ m := fun j =>
    MvPolynomial.eval (g ∘ P) (pderiv j (V.map g).toProjective.polynomial) with hD
  have hj : ∀ j, j ≠ i → D j = 0 := fun j hj => by
    have e : (V.map g).toProjective.polynomial = MvPolynomial.map g V.toProjective.polynomial :=
      WeierstrassCurve.Projective.map_polynomial ..
    simp only [hD]
    rw [e, pderiv_map, MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span ⟨⟨j, hj⟩, rfl⟩))
  have euler : 3 * _ = (g ∘ P) 0 * D 0 + (g ∘ P) 1 * D 1 + (g ∘ P) 2 * D 2 :=
    (V.map g).toProjective.polynomial_relation (g ∘ P)
  have h0 : MvPolynomial.eval (g ∘ P) (V.map g).toProjective.polynomial = 0 := hns.1
  rw [h0, mul_zero, ← Fin.sum_univ_three
    (fun j => (g ∘ P) j * D j), Finset.sum_eq_single i (fun j _ h => by rw [hj j h, mul_zero])
    (by simp)] at euler
  have hall : ∀ j, D j = 0 := fun j => by
    by_cases h : j = i
    · exact h ▸ (mul_eq_zero.mp euler.symm).resolve_left hi'
    · exact hj j h
  rcases hns.2 with h | h | h
  exacts [h (hall 0), h (hall 1), h (hall 2)]

variable {i j : Fin 3} (hij : j ≠ i)

def dehomPresentation : Algebra.PreSubmersivePresentation R (DehomRing W i) (Fin 3) (Fin 2) :=
  .naive (v := dehomRelation W i) ![j, i] (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [hij.symm])

theorem jacobian_dehomPresentation : (dehomPresentation W hij).jacobian =
    Ideal.Quotient.mk _ (pderiv j W.toProjective.polynomial) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_fin_two]
  have h : ∀ a b, (dehomPresentation W hij).jacobiMatrix a b =
      pderiv (![j, i] a) (dehomRelation W i b) := fun a b =>
    Algebra.PreSubmersivePresentation.jacobiMatrix_naive ..
  have h₁ : (dehomPresentation W hij).jacobiMatrix 1 1 = 1 := by
    rw [h]
    change pderiv i (X i - 1 : MvPolynomial (Fin 3) R) = (1 : MvPolynomial (Fin 3) R)
    simp
  have h₂ : (dehomPresentation W hij).jacobiMatrix 0 1 = 0 := by
    rw [h]
    change pderiv j (X i - 1 : MvPolynomial (Fin 3) R) = (0 : MvPolynomial (Fin 3) R)
    simp [hij.symm]
  rw [h₁, h₂, mul_one, zero_mul, sub_zero, h, Algebra.Generators.algebraMap_apply]
  exact eval₂_dehomCoord W i _


include hij in
theorem isStandardSmoothOfRelativeDimension_away_pderiv (T : Type*) [CommRing T]
    [Algebra (DehomRing W i) T] [Algebra R T] [IsScalarTower R (DehomRing W i) T]
    [IsLocalization.Away
      (Ideal.Quotient.mk _ (pderiv j W.toProjective.polynomial) : DehomRing W i) T] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R T := by
  have : IsLocalization.Away (dehomPresentation W hij).jacobian T := by
    rwa [jacobian_dehomPresentation]
  simpa [Algebra.Presentation.dimension] using
    isStandardSmoothOfRelativeDimension_away_jacobian (dehomPresentation W hij) T

theorem locally_isStandardSmoothOfRelativeDimension_dehomRing (hΔ : IsUnit W.Δ) (i : Fin 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (DehomRing W i)) := by
  have h := span_pderiv_eq_top (V := W.map (algebraMap R (DehomRing W i)))
    (by rw [WeierstrassCurve.map_Δ]; exact hΔ.map _) (equation_dehomCoord W i) (i := i) (by simp)
  have e : (W.map (algebraMap R (DehomRing W i))).toProjective.polynomial =
      MvPolynomial.map _ W.toProjective.polynomial :=
    WeierstrassCurve.Projective.map_polynomial ..
  simp only [e, pderiv_map, MvPolynomial.eval_map, eval₂_dehomCoord] at h
  refine ⟨_, h, ?_⟩
  rintro _ ⟨⟨j, hj⟩, rfl⟩
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact isStandardSmoothOfRelativeDimension_away_pderiv W hj _

theorem smoothOfRelativeDimension_toSpec_of_isUnit (hΔ : IsUnit W.Δ) :
    SmoothOfRelativeDimension 1 (toSpec W) :=
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} 1)
  of_dehomChart W (@SmoothOfRelativeDimension 1) fun i =>
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).2
      (locally_isStandardSmoothOfRelativeDimension_dehomRing W hΔ i)

end Smooth

section Integral

open Polynomial

theorem originW_mem_nonZeroDivisors_originRing : originW W ∈ nonZeroDivisors (OriginRing W) := by
  have h : IsSMulRegular (OriginRing W) (X : R[X]) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors
      (monic_X.mem_nonZeroDivisors : (X : R[X]) ∈ nonZeroDivisors R[X])
  rw [mem_nonZeroDivisors_iff_left]
  intro a ha
  refine h.right_eq_zero_of_smul ?_
  rw [Algebra.smul_def]
  exact ha

private theorem exists_isOpenImmersion_of_origin_preimage {X : Scheme.{u}}
    (fY : Spec (.of (OriginRing W)) ⟶ scheme W) (fZ : X ⟶ scheme W)
    [IsOpenImmersion fY] [IsOpenImmersion fZ]
    (hY : fY ⁻¹ᵁ coordOpen W 2 = PrimeSpectrum.basicOpen (originW W))
    (hZ : fZ.opensRange = coordOpen W 2) :
    ∃ f : Spec (.of (Localization.Away (originW W))) ⟶ X,
      IsOpenImmersion f ∧ f ≫ fZ =
        Spec.map (CommRingCat.ofHom (algebraMap (OriginRing W) _)) ≫ fY := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap (OriginRing W) (Localization.Away (originW W))))
  have : IsOpenImmersion g := IsOpenImmersion.of_isLocalization (originW W)
  have hr : Set.range (g ≫ fY) ⊆ Set.range fZ := by
    rintro _ ⟨x, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, hZ, Scheme.Hom.comp_apply]
    change g x ∈ fY ⁻¹ᵁ coordOpen W 2
    rw [hY]
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away (originW W))
      (originW W)).le ⟨x, rfl⟩
  refine ⟨IsOpenImmersion.lift fZ (g ≫ fY) hr, ?_, IsOpenImmersion.lift_fac ..⟩
  have : IsOpenImmersion (IsOpenImmersion.lift fZ (g ≫ fY) hr ≫ fZ) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  exact .of_comp _ fZ

theorem exists_isOpenImmersion_away_originW :
    ∃ f : Spec (.of (Localization.Away (originW W))) ⟶ Spec (.of W.toAffine.CoordinateRing),
      IsOpenImmersion f ∧ f ≫ chartZ W =
        Spec.map (CommRingCat.ofHom (algebraMap (OriginRing W) _)) ≫ chartY W :=
  exists_isOpenImmersion_of_origin_preimage W (chartY W) (chartZ W)
    (chartY_preimage_coordOpen_two W) (opensRange_chartZ W)

private def originAwayChart : Spec (.of (OriginRing W)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (awayEquivOrigin W).toRingHom) ≫ awayChart W 1

private theorem isIso_originAwayChart_eval :
    IsIso (CommRingCat.ofHom (awayEquivOrigin W).toRingHom) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (awayEquivOrigin W).bijective

private instance : IsOpenImmersion (originAwayChart W) := by
  have := isIso_originAwayChart_eval W
  unfold originAwayChart
  infer_instance

private theorem originAwayChart_preimage_coordOpen_two :
    originAwayChart W ⁻¹ᵁ coordOpen W 2 = PrimeSpectrum.basicOpen (originW W) := by
  have he : (awayChart W 1) ⁻¹ᵁ coordOpen W 2 = PrimeSpectrum.basicOpen (awayCoord W 1 2) := by
    refine (Proj.awayι_preimage_basicOpen (grading W) (coord_mem W 1) one_pos
      (coord_mem W 2) one_pos).trans ?_
    congr 1
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, awayCoord]
  rw [originAwayChart, Scheme.Hom.comp_preimage, he, SpecMap_preimage_basicOpen]
  have hm := awayEval_awayCoord_mul W 1 (algebraMap R _) ![originZ W, -1, originW W]
    (equation_originZ_originW W) isUnit_one.neg 2
  have h : (awayEquivOrigin W) (awayCoord W 1 2) = -originW W := by
    change awayEval W 1 (algebraMap R _) ![originZ W, -1, originW W]
      (equation_originZ_originW W) isUnit_one.neg (awayCoord W 1 2) = _
    simpa [neg_eq_iff_eq_neg] using hm
  change PrimeSpectrum.basicOpen ((awayEquivOrigin W) (awayCoord W 1 2)) = _
  rw [h]
  ext x
  simp

instance isDomain_originRing [IsDomain R] : IsDomain (OriginRing W) := by
  have : Nontrivial (OriginRing W) := (originAug W).toRingHom.domain_nontrivial
  have hinj : Function.Injective (algebraMap (OriginRing W) (Localization.Away (originW W))) :=
    IsLocalization.injective _ (M := Submonoid.powers (originW W))
      (Submonoid.powers_le.mpr (originW_mem_nonZeroDivisors_originRing W))
  have : Nontrivial (Localization.Away (originW W)) := hinj.nontrivial
  have : IsDomain (AwayRing W 2) := (awayEquivAffine W).injective.isDomain _
  obtain ⟨f, hf, -⟩ := exists_isOpenImmersion_of_origin_preimage W (originAwayChart W) (awayChart W 2)
    (originAwayChart_preimage_coordOpen_two W) (opensRange_awayChart W 2)
  have : IsIntegral (Spec (.of (Localization.Away (originW W)))) :=
    isIntegral_of_isOpenImmersion f
  have : IsDomain (Localization.Away (originW W)) :=
    (affine_isIntegral_iff (.of (Localization.Away (originW W)))).mp this
  exact hinj.isDomain _

private theorem denseRange_of_origin_preimage {X : Scheme.{u}}
    (fY : Spec (.of (OriginRing W)) ⟶ scheme W) (fZ : X ⟶ scheme W)
    [IsOpenImmersion fY] [IsOpenImmersion fZ]
    (hY : fY.opensRange = coordOpen W 1) (hZ : fZ.opensRange = coordOpen W 2)
    (h : fY ⁻¹ᵁ coordOpen W 2 = PrimeSpectrum.basicOpen (originW W)) : DenseRange fZ := by
  intro x
  rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ x) with hx | hx
  · rw [← hY] at hx
    obtain ⟨y, rfl⟩ := Scheme.Hom.mem_opensRange.mp hx
    have hd : Dense (PrimeSpectrum.basicOpen (originW W) : Set (PrimeSpectrum (OriginRing W))) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (originW W))
        (originW W)]
      refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsLocalization.injective _
        (M := Submonoid.powers (originW W))
        (Submonoid.powers_le.mpr (originW_mem_nonZeroDivisors_originRing W)))]
      exact bot_le
    rw [← h, ← hZ] at hd
    exact fY.continuous.closure_preimage_subset _ (hd y)
  · rw [← hZ] at hx
    exact subset_closure hx

theorem denseRange_chartZ : DenseRange (chartZ W) :=
  denseRange_of_origin_preimage W (chartY W) (chartZ W)
    (opensRange_chartY W) (opensRange_chartZ W) (chartY_preimage_coordOpen_two W)

private theorem isReduced_scheme_of_reduced_charts
    [IsReduced W.toAffine.CoordinateRing] [IsReduced (OriginRing W)] :
    AlgebraicGeometry.IsReduced (scheme W) := by
  have : IsReduced (AwayRing W 1) :=
    isReduced_of_injective (awayEquivOrigin W) (awayEquivOrigin W).injective
  have : IsReduced (AwayRing W 2) :=
    isReduced_of_injective (awayEquivAffine W) (awayEquivAffine W).injective
  let f : (b : Bool) → Spec (.of (AwayRing W (if b then 1 else 2))) ⟶ scheme W :=
    fun b => awayChart W (if b then 1 else 2)
  let U : (scheme W).OpenCover := Scheme.Cover.mkOfCovers Bool _ f fun x => by
    rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ x) with hx | hx
    · rw [← opensRange_awayChart] at hx
      exact ⟨true, hx⟩
    · rw [← opensRange_awayChart] at hx
      exact ⟨false, hx⟩
  have : ∀ b, AlgebraicGeometry.IsReduced (U.X b) := by
    intro b
    cases b
    · exact inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of (AwayRing W 2))))
    · exact inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of (AwayRing W 1))))
  exact .of_openCover _ U

private theorem denseRange_awayChart_two : DenseRange (awayChart W 2) := by
  have := isIso_originAwayChart_eval W
  have hY : (originAwayChart W).opensRange = coordOpen W 1 := by
    unfold originAwayChart
    rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_awayChart]
  exact denseRange_of_origin_preimage W (originAwayChart W) (awayChart W 2)
    hY (opensRange_awayChart W 2) (originAwayChart_preimage_coordOpen_two W)

instance isIntegral_scheme [IsDomain R] : IsIntegral (scheme W) := by
  have : AlgebraicGeometry.IsReduced (scheme W) := isReduced_scheme_of_reduced_charts W
  have : IsDomain (AwayRing W 2) := (awayEquivAffine W).injective.isDomain _
  have : IrreducibleSpace (scheme W) := by
    have h := ((IrreducibleSpace.isIrreducible_univ _).image (awayChart W 2)
      (awayChart W 2).continuous.continuousOn).closure
    rw [Set.image_univ, (denseRange_awayChart_two W).closure_range] at h
    exact (irreducibleSpace_def _).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

instance geometricallyIntegral_toSpec : GeometricallyIntegral (toSpec W) :=
  ⟨geometrically_iff_of_commRing.mpr fun K _ _ _ _ _ h =>
    IsIntegral.of_isIso ((isPullback_mapHom W (algebraMap R K) rfl).isoIsPullback _ _ h).hom⟩

instance geometricallyConnected_toSpec : GeometricallyConnected (toSpec W) :=
  ⟨fun _ _ y _ fst snd h =>
    have := (geometricallyIntegral_toSpec W).1 y fst snd h
    inferInstance⟩

instance isReduced_coordinateRing [_root_.IsReduced R] : _root_.IsReduced W.toAffine.CoordinateRing :=
  have : GeometricallyReduced
      (Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing))) :=
    ⟨geometrically_iff_of_commRing.mpr fun K _ _ _ _ _ h => by
      have h' := (isPullback_chartZ W (algebraMap R K) rfl).paste_vert
        (isPullback_mapHom W (algebraMap R K) rfl)
      rw [chartZ_toSpec W] at h'
      exact isReduced_of_isOpenImmersion (h.isoIsPullback _ _ h').hom⟩
  isReduced_of_free_of_geometricallyReduced (R := R)

instance isReduced_originRing [_root_.IsReduced R] : _root_.IsReduced (OriginRing W) :=
  have : GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R (OriginRing W)))) :=
    ⟨geometrically_iff_of_commRing.mpr fun K _ _ _ _ _ h => by
      have h' := (isPullback_chartY W (algebraMap R K) rfl).paste_vert
        (isPullback_mapHom W (algebraMap R K) rfl)
      rw [chartY_toSpec W] at h'
      exact isReduced_of_isOpenImmersion (h.isoIsPullback _ _ h').hom⟩
  isReduced_of_free_of_geometricallyReduced (R := R)

instance isReduced_scheme [_root_.IsReduced R] : AlgebraicGeometry.IsReduced (scheme W) :=
  isReduced_scheme_of_reduced_charts W

end Integral

end WeierstrassCurve

end GlobalTheory
