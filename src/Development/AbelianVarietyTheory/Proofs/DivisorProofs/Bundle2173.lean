module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardSmoothRetractOfSmooth
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SmoothRetract

open MvPolynomial

variable {R₀ : Type} [CommRing R₀] {n r : ℕ}

def tang (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (i l : Fin n) : MvPolynomial (Fin n) R₀ :=
  (if i = l then 1 else 0) + ∑ k, a i k * pderiv l (g k)

def rel (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (i : Fin n) : MvPolynomial (Fin n ⊕ Fin n) R₀ :=
  rename Sum.inr (∑ k, a i k * g k) +
    ∑ l, rename Sum.inr (tang g a i l) * (X (Sum.inl l) - X (Sum.inr l))

theorem aeval_pderiv_rel (g : Fin r → MvPolynomial (Fin n) R₀)
    (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) {B : Type} [CommRing B] [Algebra R₀ B]
    (xb : Fin n → B) (hg : ∀ k, aeval xb (g k) = 0) (i j : Fin n) :
    aeval (Sum.elim xb xb) (pderiv (Sum.inr i) (rel g a j)) = -(if i = j then 1 else 0) := by
  classical
  simp [rel, Derivation.leibniz, pderiv_rename Sum.inr_injective, pderiv_X, Pi.single_apply,
    aeval_rename, Function.comp_def, hg, tang, Finset.sum_add_distrib, mul_add, add_mul]
  exact if_congr eq_comm rfl rfl

theorem sum_pderiv_mul_tang (g : Fin r → MvPolynomial (Fin n) R₀)
    (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (j : Fin r) (l : Fin n) :
    ∑ i, pderiv i (g j) * tang g a i l =
      pderiv l (g j) + ∑ i, pderiv i (g j) * ∑ k, a i k * pderiv l (g k) := by
  classical
  simp [tang, mul_add, Finset.sum_add_distrib]

theorem core (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (h1 : ∀ j, g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2)
    (h2 : ∀ j m, pderiv m (g j) + ∑ i, pderiv i (g j) * ∑ k, a i k * pderiv m (g k) ∈
      Ideal.span (Set.range g)) :
    ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀)
      (i : (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) →ₐ[R₀] C₀)
      (r : C₀ →ₐ[R₀] (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g))),
      Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  classical
  set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ
  set K : Ideal (MvPolynomial (Fin n ⊕ Fin n) R₀) := Ideal.span (Set.range (rel g a)) with hK
  let xb : Fin n → MvPolynomial (Fin n) R₀ ⧸ J := fun l => Ideal.Quotient.mk J (X l)
  have hxb : ∀ p, aeval xb p = Ideal.Quotient.mk J p := fun p =>
    AlgHom.congr_fun (MvPolynomial.algHom_ext (f := aeval xb) (g := Ideal.Quotient.mkₐ R₀ J)
      fun l => by simp [xb]) p
  have hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0 := fun k =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)
  let r₀' : MvPolynomial (Fin n ⊕ Fin n) R₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    aeval (Sum.elim xb xb)
  have hren : ∀ p, r₀' (rename Sum.inr p) = Ideal.Quotient.mk J p := fun p => by
    simp [r₀', aeval_rename, Function.comp_def, ← hxb]
  have hs0 : ∀ l, r₀' (X (Sum.inl l) - X (Sum.inr l)) = 0 := fun l => by simp [r₀']
  have hrel : ∀ i, r₀' (rel g a i) = 0 := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rel, map_add (f := _), map_sum, map_mul, hren, hs0, mul_zero, Finset.sum_const_zero,
      add_zero, hg0]
  have hKle : K ≤ RingHom.ker r₀' := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hrel i)
  let r₀ : (MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K) →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    Ideal.Quotient.liftₐ K r₀' (fun x hx => hKle hx)
  have hr₀ : ∀ p, r₀ (Ideal.Quotient.mk K p) = r₀' p := fun p => rfl
  let P := Algebra.PreSubmersivePresentation.naive (v := rel g a) Sum.inr Sum.inr_injective
  have hval : ∀ v, P.val v = Ideal.Quotient.mk K (X v) := fun v => by
    simp [P]
    rfl
  have hr₀alg : ∀ p, r₀ (algebraMap P.Ring _ p) = r₀' p := by
    intro p
    rw [Algebra.Generators.algebraMap_apply]
    have : r₀.comp (aeval P.val) = r₀' :=
      MvPolynomial.algHom_ext fun v => by simp [hval, hr₀]
    exact AlgHom.congr_fun this p
  have hjac : IsUnit (r₀ P.jacobian) := by
    rw [P.jacobian_eq_jacobiMatrix_det, hr₀alg]
    have hM : r₀'.toRingHom.mapMatrix P.jacobiMatrix = -1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply,
        Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
      change aeval (Sum.elim xb xb) _ = _
      rw [aeval_pderiv_rel g a xb (fun k => by rw [hxb, hg0])]
      simp [Matrix.one_apply]
    have : r₀' P.jacobiMatrix.det = (r₀'.toRingHom.mapMatrix P.jacobiMatrix).det :=
      RingHom.map_det _ _
    rw [this, hM, Matrix.det_neg, Matrix.det_one, _root_.mul_one]
    exact (isUnit_one.neg).pow _
  let D := MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K
  let T1 := Localization.Away P.jacobian
  haveI hT1 : Algebra.IsStandardSmooth R₀ T1 := by
    let Q := Algebra.SubmersivePresentation.localizationAway T1 P.jacobian
    let P' : Algebra.SubmersivePresentation R₀ T1 (Unit ⊕ (Fin n ⊕ Fin n)) (Unit ⊕ Fin n) :=
      { __ := Q.toPreSubmersivePresentation.comp P
        jacobian_isUnit := by
          rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
            Algebra.smul_def]
          exact (IsLocalization.Away.algebraMap_isUnit _).mul Q.jacobian_isUnit }
    exact P'.isStandardSmooth
  let r₁ : T1 →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    IsLocalization.Away.liftAlgHom P.jacobian (f := r₀) hjac
  have hr₁ : ∀ y, r₁ (algebraMap D T1 y) = r₀ y := fun y => by
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq _ _ _

  let φ : MvPolynomial (Fin n) R₀ →+* D :=
    (Ideal.Quotient.mk K).comp (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀).toRingHom
  have hφ : ∀ p, φ p = Ideal.Quotient.mk K (rename Sum.inr p) := fun p => rfl
  let G : Fin r → D := fun k => φ (g k)
  let s : Fin n → D := fun l => Ideal.Quotient.mk K (X (Sum.inl l) - X (Sum.inr l))
  let JD : Ideal D := Ideal.span (Set.range G)
  let L : Ideal D := JD ⊔ Ideal.span (Set.range s)
  have hJD : J.map φ = JD := by
    simp only [hJ, Ideal.map_span, JD, G, ← Set.range_comp]
    rfl
  have hrelD : ∀ i, φ (∑ k, a i k * g k) + ∑ l, φ (tang g a i l) * s l = 0 := by
    intro i
    have : Ideal.Quotient.mk K (rel g a i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    rw [← this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rel, map_add (f := _), map_sum, map_mul, hφ, s]
  have key : ∀ j, G j ∈ L * JD := by
    intro j
    have e1 : φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) =
        G j + ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum]
      simp only [map_mul, G]
    have hs : ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k) +
        ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by rw [← mul_add, hrelD i, mul_zero]
    have e3 : ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l) =
        ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have eq : G j = φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) +
        ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l) := by
      rw [e3]
      linear_combination -e1 - hs
    rw [eq]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun l _ => ?_)
    · have : φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) ∈ JD ^ 2 := by
        rw [← hJD, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem φ (h1 j)
      rw [pow_two] at this
      exact Ideal.mul_mono_left le_sup_left this
    · refine Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩)) ?_
      rw [sum_pderiv_mul_tang, ← hJD]
      exact Ideal.mem_map_of_mem φ (h2 j l)
  obtain ⟨e, he1, he⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul L JD
    (Submodule.fg_span (Set.finite_range G)) (by
      rw [Ideal.smul_eq_mul]
      exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact key j))
  have hL : L ≤ RingHom.ker r₀ := by
    refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      change r₀ (Ideal.Quotient.mk K (rename Sum.inr (g k))) = 0
      rw [hr₀, hren, hg0]
    · rintro _ ⟨l, rfl⟩
      change r₀ (Ideal.Quotient.mk K _) = 0
      rw [hr₀, hs0]
  have hre : r₀ e = 1 := by
    have := hL he1
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
    exact this
  let C₀ := Localization.Away (algebraMap D T1 e)
  haveI : Algebra.IsStandardSmooth T1 C₀ :=
    Algebra.IsStandardSmooth.localization_away (algebraMap D T1 e)
  have hC : Algebra.IsStandardSmooth R₀ C₀ := Algebra.IsStandardSmooth.trans R₀ T1 C₀
  let r₂ : C₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    IsLocalization.Away.liftAlgHom (algebraMap D T1 e) (f := r₁) (by rw [hr₁, hre]; exact isUnit_one)
  have hr₂ : ∀ y, r₂ (algebraMap T1 C₀ y) = r₁ y := fun y => by
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq _ _ _
  let ψ : D →ₐ[R₀] C₀ := (IsScalarTower.toAlgHom R₀ T1 C₀).comp (IsScalarTower.toAlgHom R₀ D T1)
  have hψe : IsUnit (ψ e) := IsLocalization.Away.algebraMap_isUnit (algebraMap D T1 e)
  have hψG : ∀ k, ψ (G k) = 0 := by
    intro k
    have h0 : e * G k = 0 := he (G k) (Ideal.subset_span ⟨k, rfl⟩)
    have : ψ e * ψ (G k) = 0 := by rw [← map_mul, h0, map_zero]
    exact (hψe.mul_right_eq_zero).1 this
  have hJle : J ≤ RingHom.ker (ψ.comp ((Ideal.Quotient.mkₐ R₀ K).comp
      (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀))) :=
    Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hψG k)
  let i : (MvPolynomial (Fin n) R₀ ⧸ J) →ₐ[R₀] C₀ :=
    Ideal.Quotient.liftₐ J _ (fun x hx => hJle hx)
  refine ⟨C₀, inferInstance, inferInstance, i, r₂, hC, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change r₂ (algebraMap T1 C₀ (algebraMap D T1 (Ideal.Quotient.mk K (rename Sum.inr p)))) = _
  rw [hr₂, hr₁, hr₀, hren]

theorem exists_retract_isStandardSmooth : ∀ (R₀ B₀ : Type) [CommRing R₀] [CommRing B₀] [Algebra R₀ B₀],
    Algebra.Smooth R₀ B₀ → ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀) (i : B₀ →ₐ[R₀] C₀)
      (r : C₀ →ₐ[R₀] B₀), Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  intro R₀ B₀ _ _ _ hsm
  obtain ⟨n, f, hf, hfg⟩ := Algebra.FinitePresentation.out (R := R₀) (A := B₀)
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  let e : (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀] B₀ :=
    (Ideal.quotientEquivAlgOfEq R₀ hg).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  haveI : Algebra.FormallySmooth R₀ (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) :=
    Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨a, b, hab⟩ :=
    GlobalTheory.exists_witnesses_of_formallySmooth_quotient (Fin n) R₀ r g inferInstance
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.SmoothRel.relations_combination R₀ n r g a b hab
  obtain ⟨C₀, i1, i2, i, ρ, hstd, hret⟩ := core g a h1 h2
  exact ⟨C₀, i1, i2, i.comp e.symm.toAlgHom, e.toAlgHom.comp ρ, hstd, fun x => by simp [hret]⟩

end GlobalTheory.SmoothRetract
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGenericFibreGaloisExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelGalois

theorem exists_galois (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Module.Finite F E] (n : ℕ)
    (hn : 0 < n) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω) (i : E →+* Ω) (ζ : Ωˣ), FiniteDimensional F Ω ∧ IsGalois F Ω ∧
      i.comp (algebraMap F E) = algebraMap F Ω ∧ IsPrimitiveRoot ζ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : CharZero E := (algebraMap F E).charZero_iff (algebraMap F E).injective |>.1 inferInstance
  let C := CyclotomicField n E
  haveI : Module.Finite E C := IsCyclotomicExtension.finite {n} E C
  haveI : Module.Finite F C := Module.Finite.trans E C
  let L := AlgebraicClosure C
  haveI : IsAlgClosure F L := IsAlgClosure.ofAlgebraic F C L
  let Ω := IntermediateField.normalClosure F C L
  have hz := (IsCyclotomicExtension.zeta_spec n E C).map_of_injective (algebraMap C Ω).injective
  obtain ⟨ζ, hζ⟩ := hz.isUnit hn.ne'
  refine ⟨Ω, inferInstance, inferInstance, (algebraMap C Ω).comp (algebraMap E C), ζ, inferInstance, ?_, ?_,
    IsPrimitiveRoot.coe_units_iff.1 (hζ ▸ hz)⟩
  · exact { }
  · rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq F E C, ← IsScalarTower.algebraMap_eq F C Ω]


open MonObj in
theorem nonempty_level_of_rational {F : Type} [Field F] [CharZero F] (P : PolAV (Sp F)) (n : ℕ) (hn : 0 < n) (ζ : Fˣ)
    (hζ : IsPrimitiveRoot ζ n) (Q : PolAV (Sp (AlgebraicClosure F))) (φ : Q.A.left ⟶ P.A.left)
    (hQ : IsPolFibre (algebraMap F (AlgebraicClosure F)) P Q φ)
    (H : ∀ y, y ^ n = 1 → ∃ x, ObjPull.secPull hQ.2.1 x = y) : Nonempty (Out.Level P n (unitOn ζ)) := by
  let σ := algebraMap F (AlgebraicClosure F)
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : F →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ζ) n := fun φ =>
    hζ.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hp : IsPrimitiveRoot (unitOn ζ) n := by
    have := nt F
    exact prim (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  obtain ⟨l⟩ := GlobalTheory.nonempty_level_of_isAlgClosed _ Q n (Units.map σ.toMonoidHom ζ) (Nat.cast_ne_zero.2 hn.ne') (prim σ)
  have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
      {X : Scheme} (y y' : Sp K ⟶ X) (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
    obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
    obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
    simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
    have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
        spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
          (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
      intro q ψ
      simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
    rw [e, e] at h
    have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
    simp only [Sigma.mk.inj_iff] at h2
    obtain ⟨rfl, h3⟩ := h2
    have h4 : φ = φ' := by
      have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
      ext x
      apply gam.injective
      have := congrArg (fun f => f.hom x) h5
      simpa using this
    rw [h4]
  have hinj : Function.Injective (ObjPull.secPull hQ.2.1) := fun a b h =>
    Over.OverMorphism.ext (spec_map_field_cancel σ _ _ (by
      rw [← ObjPull.secPull_left hQ.2.1, ← ObjPull.secPull_left hQ.2.1, h]))
  choose t ht using fun a => H (l.pt a) (l.torsion a)
  have tors : ∀ a, t a ^ n = 1 := fun a => hinj (by rw [map_pow, ht, map_one]; exact l.torsion a)
  have uz : ∀ {R : Type} [CommRing R] (u : Rˣ) (m : ℤ), unitOn (u ^ m) = unitOn u ^ m := fun {R} _ u m =>
    map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom) u m
  have hg : 2 * P.g = 2 * Q.g := by rw [hQ.1]
  have hs : ∀ i j, stdSymp Q.g (Fin.cast hg i) (Fin.cast hg j) = stdSymp P.g i j := fun i j => by
    simp only [stdSymp, Fin.val_cast, hQ.1]
  obtain ⟨lev, -⟩ := GlobalTheory.exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp F) P n (unitOn ζ) hp
    (fun F' _ s => by
      have := nt F'
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)⟩
      rw [← map_natCast (Spec.preimage s).hom]
      exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn.ne')) (fun i => t (Fin.cast hg i)) (fun i => tors _)
    (fun i j => by
      have h := l.pairing (Fin.cast hg i) (Fin.cast hg j)
      rw [hs, ← uz, ← map_zpow, ← ht, ← ht] at h
      rw [← uz]
      exact LevelAfterExt.weilIs_of_ext σ hQ n _ _ _ (tors _) (tors _) h)
  exact ⟨lev⟩

theorem exists_level_galois : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (ι : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (K : ℕ), 0 < K → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp ι)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  intro Ω₁ _ _ R₁ _ ι P₁ K hK
  have hB := GlobalTheory.laws_without_cohomology.2.2.1
  obtain ⟨P₀, φ₀, h₀⟩ := exists_isPolFibre hB ι P₁
  obtain ⟨E, _, _, hfin, H⟩ := LevelAfterExt.exists_ext_torsion Ω₁ P₀ K hK
  obtain ⟨Ω₂, _, _, i, ζ, hfd, hgal, hi, hζ⟩ := exists_galois Ω₁ E K hK
  haveI : CharZero Ω₂ := (algebraMap Ω₁ Ω₂).charZero_iff (algebraMap Ω₁ Ω₂).injective |>.1 inferInstance
  obtain ⟨Q, ψ, hQ⟩ := exists_isPolFibre hB (algebraMap Ω₁ Ω₂) P₀
  obtain ⟨Q', ψ', hQ'⟩ := exists_isPolFibre hB (algebraMap Ω₂ (AlgebraicClosure Ω₂)) Q
  refine ⟨Ω₂, inferInstance, inferInstance, Q, ψ ≫ φ₀, ζ, hfd, hgal, hζ, hQ.1.trans h₀.1,
    (hQ.2.1.comp h₀.2.1).congr (GlobalTheory.spMap_comp_spMap _ _) rfl, ?_,
    nonempty_level_of_rational Q K hK ζ hζ Q' ψ' hQ' (H Ω₂ _ i _ hi Q ψ hQ _ Q' ψ' hQ')⟩
  exact LBIso.trans Q.isLB (pull_isLB P₀.isLB _) (pull_isLB P₁.isLB _) hQ.2.2.symm
    (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P₁.L _ _ _ ψ fun _ => rfl) h₀.2.2.symm)

end GlobalTheory.LevelGalois
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProduct
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ContrMor

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]
  {D : Type} [CommRing D] [Algebra R D] {D' : Type} [CommRing D'] [Algebra R D']

omit [GrpObj A] in
theorem specOverOfAlgHom_pointWithZeroSecondCoord (φ : D →ₐ[R] D') (x : Pt A D) :
    spOver φ ≫ pt0 B x = pt0 B (spOver φ ≫ x : Pt A D') := by
  simp [pt0, comp_lift, MonObj.comp_one]

omit [GrpObj A] in
theorem spOver_fst_ptV (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) :
    spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x = pt0 B x := by
  have k : spOver (TrivSqZeroExt.fstHom R D D) ≫ spOver (EpsWeil.epsMap R D) =
      toUnit _ ≫ GrpTangent.epsZero R := by
    refine Over.OverMorphism.ext ?_
    rw [spOver_comp, PDiv.spOver_left, Over.comp_left, Over.toUnit_left]
    refine Eq.trans (congrArg spMap (RingHom.ext fun a ↦ ?_)) (Cris.spMap_comp
      (TrivSqZeroExt.fstHom R R R).toRingHom (algebraMap R D))
    simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl']
  ext1
  · simp only [ptV, pt0, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    rw [show (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D from
      AlgHom.ext fun _ ↦ rfl, PDiv.spOver_id, Category.id_comp]
  · simp only [ptV, pt0, comp_lift, lift_snd]
    rw [← Category.assoc, k, Category.assoc, (GrpTangent.isTangent_iff v).1 hv, MonObj.comp_one]

omit [GrpObj A] [GrpObj B] in
theorem spOver_epsHom_ptV (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    spOver (epsHom φ) ≫ ptV v x = ptV v (spOver φ ≫ x : Pt A D') := by
  ext1
  · simp only [ptV, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    congr 2
    ext c <;> simp [epsHom]
  · simp only [ptV, comp_lift, lift_snd, ← Category.assoc, spOver_comp]
    congr 2
    ext <;> simp only [AlgHom.comp_apply, EpsWeil.epsMap, epsHom, DualNumber.lift_apply_eps]

def sHom (x : Pt A D) : trivAt (pt0 B x) ⟶ thickAt B x :=
  (epsExt R D).secHom (Pt.w (pt0 B x)) (epsExt R D).i (epsExt R D).π_i

def iHom (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) : trivAt (ptV v x) ⟶ thickAt B x :=
  Thick.trivHom (T := thickAt B x) (AlgHom.id R (DualNumber D)) (by
    have := congrArg Over.Hom.left (spOver_fst_ptV v hv x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def aHom (φ : D →ₐ[R] D') (x : Pt A D) :
    trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x : Pt A D')) :=
  Thick.trivHom φ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def bHom (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x : Pt A D')) :=
  Thick.trivHom (epsHom φ) (by
    have := congrArg Over.Hom.left (spOver_epsHom_ptV v φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def τHom (φ : D →ₐ[R] D') (x : Pt A D) :
    thickAt B x ⟶ thickAt B (spOver φ ≫ x : Pt A D') :=
  (epsExt R D).thickHom (epsExt R D') (epsHom φ) φ
    (fun c ↦ by simp [epsHom, DualNumber.lift_apply_apply]) _ _ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

end GlobalTheory.PtExt.ContrMor

namespace GlobalTheory.PtExt.ContrMor

theorem exists_contr : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (v : epsR R ⟶ B), IsTangent v →
    (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D),
      let y : Pt A D' := spOver φ ≫ x
      ∃ (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
        (s' : trivAt (pt0 B y) ⟶ thickAt B y) (i' : trivAt (ptV v y) ⟶ thickAt B y)
        (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B y)) (b : trivAt (ptV v x) ⟶ trivAt (ptV v y))
        (τ : thickAt B x ⟶ thickAt B y),
        (∀ r, s.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i.φ r = r) ∧
        (∀ r, s'.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i'.φ r = r) ∧
        (∀ r, a.φ r = φ r) ∧ (∀ r, b.φ r = epsHom φ r) ∧ (∀ r, τ.φ r = epsHom φ r)) ∧
    ∀ z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), ∃ κ : Fn1 A, IsContr z v κ := by
  intro R _ A B _ _ v hv
  refine ⟨fun D _ _ D' _ _ φ x ↦ ⟨sHom x, iHom v hv x, sHom _, iHom v hv _, aHom φ x, bHom v φ x, τHom φ x,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, fun z ↦ ?_⟩
  refine ⟨fun D _ _ D' _ _ φ x ↦ TrivSqZeroExt.snd (R := D')
    (z _ _ _ (sHom x) (τHom φ x) - z _ _ _ (aHom φ x) (sHom _) - z _ _ _ (iHom v hv x) (τHom φ x) +
      z _ _ _ (bHom v φ x) (iHom v hv _)), ?_⟩
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  obtain rfl : s = sHom x := Thick.hom_ext fun r ↦ (hs r).trans rfl
  obtain rfl : i = iHom v hv x := Thick.hom_ext fun r ↦ (hi r).trans rfl
  obtain rfl : s' = sHom _ := Thick.hom_ext fun r ↦ (hs' r).trans rfl
  obtain rfl : i' = iHom v hv _ := Thick.hom_ext fun r ↦ (hi' r).trans rfl
  obtain rfl : a = aHom φ x := Thick.hom_ext fun r ↦ (ha r).trans rfl
  obtain rfl : b = bHom v φ x := Thick.hom_ext fun r ↦ (hb r).trans rfl
  obtain rfl : τ = τHom φ x := Thick.hom_ext fun r ↦ (hτ r).trans rfl
  rfl

end GlobalTheory.PtExt.ContrMor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFaithfullyFlatAlgebraOverAffineOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_faithfullyFlat_algebra_over_affine_open : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (V₀ : Y.Opens), IsAffineOpen V₀ →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    IsNoetherianRing Γ(Y, V₀) ∧ Module.Finite Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) ∧ Module.FaithfullyFlat Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := by
  first | exact @GlobalTheory.finiteFlatSurj_affine_algebra | exact GlobalTheory.finiteFlatSurj_affine_algebra | (intros; apply GlobalTheory.finiteFlatSurj_affine_algebra <;> assumption)
end

