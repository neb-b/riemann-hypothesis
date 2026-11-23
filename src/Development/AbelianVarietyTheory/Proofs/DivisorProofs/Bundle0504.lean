module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0500
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeOfRegularOfIsIntegrallyClosedIn
section
open IsLocalRing Polynomial

namespace GlobalTheory.PurityLoc

noncomputable def integralClosureEquiv (R C : Type) [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (M : Submonoid R)
    (h : IsIntegrallyClosedIn C (Localization (Algebra.algebraMapSubmonoid C M))) :
    C ≃ₐ[R] integralClosure R (Localization (Algebra.algebraMapSubmonoid C M)) :=
  AlgEquiv.ofBijective
    ((IsScalarTower.toAlgHom R C _).codRestrict _ fun c =>
      (Algebra.IsIntegral.isIntegral (R := R) c).map (IsScalarTower.toAlgHom R C _))
    (by
      obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp h
      refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun ⟨x, hx⟩ => ?_⟩
      obtain ⟨c, hc⟩ := hcl (hx.tower_top (A := C))
      exact ⟨c, Subtype.ext hc⟩)

theorem isReduced_isArtinianRing_localization (R C : Type) [CommRing R] [IsDomain R] [CommRing C]
    [Algebra R C] [Module.Finite R C]
    (h : Algebra.Etale (Localization.AtPrime (⊥ : Ideal R))
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)) :
    IsReduced (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) ∧
      IsArtinianRing (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) := by
  haveI := h
  haveI hKfr : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
    exact (congrArg (fun M : Submonoid R => IsLocalization M (Localization.AtPrime (⊥ : Ideal R)))
      (Ideal.primeCompl_bot (α := R))).mp inferInstance
  letI : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R
  haveI : IsReduced (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    Algebra.FormallyUnramified.isReduced_of_field (Localization.AtPrime (⊥ : Ideal R)) _
  haveI : IsArtinianRing (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    IsArtinianRing.of_finite (Localization.AtPrime (⊥ : Ideal R)) _
  letI : Algebra C (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) := by
    exact (congrArg (fun M : Submonoid R => IsLocalization (Algebra.algebraMapSubmonoid C M)
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)) (Ideal.primeCompl_bot (α := R))).mp
      (IsLocalization.tensorRight (S := C) (Localization.AtPrime (⊥ : Ideal R)) (⊥ : Ideal R).primeCompl)
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
    (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
    (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)
  exact ⟨isReduced_of_injective e.toRingHom e.injective, e.toRingEquiv.symm.isArtinianRing⟩

theorem etale_atPrime_of_isIntegrallyClosedIn : ∀ (R C : Type) [CommRing R] [IsDomain R] [CommRing C] [Algebra R C] [Module.Finite R C],
    IsIntegrallyClosedIn C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) →
    ∀ (P : Ideal R) [P.IsPrime], IsRegularLocalRing (Localization.AtPrime P) →
    (∀ (P' : Ideal R) [P'.IsPrime], P' ≤ P → P'.height ≤ 1 →
      Algebra.Etale (Localization.AtPrime P') (TensorProduct R (Localization.AtPrime P') C)) →
    Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  intro R C _ _ _ _ _ hC P _ hreg hP
  haveI := hreg
  obtain ⟨hred, hart⟩ := isReduced_isArtinianRing_localization R C (hP ⊥ bot_le (by simp))
  let iC := integralClosureEquiv R C (nonZeroDivisors R) hC
  have hb := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R)
    (S := Localization.AtPrime P)
    (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl
  let Φ : TensorProduct R (Localization.AtPrime P) C ≃ₐ[Localization.AtPrime P]
      integralClosure (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl iC).trans (AlgEquiv.ofBijective _ hb)
  have hRE : IsReduced (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) ∧
      IsArtinianRing (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := by
    letI : Algebra (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
        (TensorProduct R (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
      Algebra.TensorProduct.rightAlgebra
    haveI : IsLocalization (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl)
        (TensorProduct R (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
      IsLocalization.tensorRight (Localization.AtPrime P) P.primeCompl
    haveI := hred
    haveI := hart
    let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))
      (Localization (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl))
    exact ⟨isReduced_of_injective e.toRingHom e.injective,
      IsArtinianRing.localization_artinian (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl) _⟩
  have hunit : ∀ s : Localization.AtPrime P, s ≠ 0 → IsUnit (algebraMap (Localization.AtPrime P)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) s) := by
    intro s hs
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl s
    have hr : r ≠ 0 := by rintro rfl; exact hs (by simp)
    have h0 : IsUnit (algebraMap R (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) r) := by
      rw [IsScalarTower.algebraMap_apply R C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))]
      exact IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
        (⟨algebraMap R C r, Algebra.mem_algebraMapSubmonoid_of_mem
          (⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ : nonZeroDivisors R)⟩ :
            Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
    have h1 : IsUnit (algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) (algebraMap R _ r)) := by
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P),
        ← (Algebra.TensorProduct.includeRight (R := R) (A := Localization.AtPrime P)
          (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))).commutes r]
      exact h0.map _
    have h2 : algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))
          (IsLocalization.mk' (Localization.AtPrime P) r u) *
        algebraMap (Localization.AtPrime P) _ (algebraMap R (Localization.AtPrime P) u) =
        algebraMap (Localization.AtPrime P) _ (algebraMap R (Localization.AtPrime P) r) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [← h2] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hnz : NoZeroSMulDivisors (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := ⟨fun {s x} h => by
    by_cases hs : s = 0
    · exact Or.inl hs
    · right
      rw [Algebra.smul_def] at h
      exact (hunit s hs).mul_right_eq_zero.mp h⟩
  haveI hfin : Module.Finite (Localization.AtPrime P) (integralClosure (Localization.AtPrime P)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))) :=
    Module.Finite.equiv Φ.toLinearEquiv
  have hq : ∀ (q : Ideal (Localization.AtPrime P)) [q.IsPrime], q.height ≤ 1 →
      Algebra.Etale (Localization.AtPrime q) (TensorProduct (Localization.AtPrime P)
        (Localization.AtPrime q) (integralClosure (Localization.AtPrime P)
          (TensorProduct R (Localization.AtPrime P)
            (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))))) := by
    intro q _ hq1
    have hle : q.comap (algebraMap R (Localization.AtPrime P)) ≤ P := by
      have := Ideal.comap_mono (f := algebraMap R (Localization.AtPrime P))
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹q.IsPrime›))
      exact this.trans (Localization.AtPrime.under_maximalIdeal (I := P)).le
    have hh : (q.comap (algebraMap R (Localization.AtPrime P))).height ≤ 1 :=
      (le_of_eq (IsLocalization.height_under P.primeCompl q)).trans hq1
    haveI h1 := GlobalTheory.OffDivisor.etale_localization_of_comap R (Localization.AtPrime P) C _ q rfl
      (hP _ hle hh)
    exact Algebra.Etale.of_equiv ((Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
      (Localization.AtPrime q) (Localization.AtPrime q) C).symm.trans
        (Algebra.TensorProduct.congr AlgEquiv.refl Φ))
  haveI := GlobalTheory.PurityProd.etale_integralClosure_of_isArtinianRing (Localization.AtPrime P) _
    hRE.1 hRE.2 hnz hfin hq
  exact Algebra.Etale.of_equiv Φ.symm

end GlobalTheory.PurityLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIff
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem isCls_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    IsCls (0 : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F) (0 : H R E F ((1 : ℕ) : ℤ)) := by
  have hc0 : ∀ {n : ℕ}, cobd (0 : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) = 0 := by
    intro n; simp [cobd]
  obtain ⟨x, hx⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 1).1 0 hc0
  have h4 := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 0).2.2.2.1 0 x (by rw [hc0]; exact hx)
  rw [h4] at hx
  exact hx

theorem mul_inv_mul_cancel_comm {M : Type*} [AddCommGroup M] {a b c : M} (h : a - b + c = 0) : b = c + a := by
  rw [sub_add_eq_add_sub, sub_eq_zero] at h
  rw [← h, add_comm]

theorem sub_add_eq_zero_of_eq_add {M : Type*} [AddCommGroup M] {a b c : M} (h : b = c + a) : a - b + c = 0 := by
  rw [h]
  abel

theorem mem_Z1_iff_cocycle (R : Type) [CommRing R] (F : Shv R) (w : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) :
    w ∈ Z1 F A B ↔
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom w =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom w +
      ((onRings F).map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom w := Iff.rfl

theorem cobd_eq_zero_iff (R : Type) [CommRing R] (F : Shv R) (s : (free R).obj ((GlobalTheory.EtC.cech (fB A B)).obj (op ⦋1⦌)) ⟶ F) :
    cobd s = 0 ↔
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) +
      ((onRings F).map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) := by
  have hinj := (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 2 _ _ (y2 A B) (hy2 A B) (GlobalTheory.T.triple_tensor_wide_pullback_limit A B).some).1
  constructor
  · intro h
    have h2 := (val_coboundary_second_level A B R F s).symm.trans
      ((congrArg (fun t => val t (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)) h).trans (val_zero R _ _))
    exact mul_inv_mul_cancel_comm h2
  · intro h
    apply hinj
    change val (cobd s) (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B) = val 0 (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)
    rw [val_zero]
    exact (val_coboundary_second_level A B R F s).trans (sub_add_eq_zero_of_eq_add h)

def Rel (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) (x : H R (sp A) F 1) : Prop :=
  ∃ s : (free R).obj ((GlobalTheory.EtC.cech (fB A B)).obj (op ⦋1⦌)) ⟶ F,
    val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) ∧
      IsCls s (pull R (GlobalTheory.EtC.cechAug (fB A B)) F ((1 : ℕ) : ℤ) x)

theorem rel_unique [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B)
    (x x' : H R (sp A) F 1) (h : Rel A B R F u x) (h' : Rel A B R F u x') : x = x' := by
  obtain ⟨s, hs, hx⟩ := h
  obtain ⟨s', hs', hx'⟩ := h'
  have hss : s = s' :=
    (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).1 (hs.trans hs'.symm)
  subst hss
  have := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (GlobalTheory.EtC.cech (fB A B)) 1).2.2.1 s _ _ hx hx'
  obtain ⟨h1, h2⟩ := smooth_surj A B
  exact (_root_.GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology R (fB A B) F ((1 : ℕ) : ℤ)).1 this

theorem rel_exists [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) :
    ∃ x, Rel A B R F u x := by
  obtain ⟨s, hs⟩ := (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).2
    (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B)))
  have hs' : val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) := hs
  have hc : cobd s = 0 := (cobd_eq_zero_iff A B R F s).2 (by rw [hs']; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)
  obtain ⟨y, hy⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (GlobalTheory.EtC.cech (fB A B)) 1).1 s hc
  obtain ⟨h1, h2⟩ := smooth_surj A B
  obtain ⟨x, hx⟩ := (_root_.GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology R (fB A B) F ((1 : ℕ) : ℤ)).2 y
  exact ⟨x, s, hs', hx ▸ hy⟩

variable {A B} in
theorem rel_add (R : Type) [CommRing R] (F : Shv R) (u u' : Z1 F A B) (x x' : H R (sp A) F 1)
    (h : Rel A B R F u x) (h' : Rel A B R F u' x') : Rel A B R F (u + u') (x + x') := by
  obtain ⟨s, hs, hx⟩ := h
  obtain ⟨s', hs', hx'⟩ := h'
  refine ⟨s + s', ?_, ?_⟩
  · rw [val_add, hs, hs']
    rfl
  · rw [map_add (f := _)]
    exact (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.1 s s' _ _ hx hx'

theorem rel_zero (R : Type) [CommRing R] (F : Shv R) : Rel A B R F 0 0 := by
  refine ⟨0, ?_, ?_⟩
  · rw [val_zero]
    rfl
  · rw [map_zero]
    exact isCls_zero R F _


open Classical in
def gam (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) : H R (sp A) F 1 :=
  if Algebra.Etale A B ∧ Module.FaithfullyFlat A B then Classical.epsilon (Rel A B R F u) else 0

theorem gam_spec [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) :
    Rel A B R F u (gam A B R F u) := by
  unfold gam
  rw [if_pos ⟨inferInstance, inferInstance⟩]
  exact Classical.epsilon_spec (rel_exists A B R F u)

theorem gam_eq [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B)
    (x : H R (sp A) F 1) : gam A B R F u = x ↔ Rel A B R F u x :=
  ⟨fun h => h ▸ gam_spec A B R F u, fun h => rel_unique A B R F u _ _ (gam_spec A B R F u) h⟩

def gamHom (R : Type) [CommRing R] (F : Shv R) : Z1 F A B →+ H R (sp A) F 1 where
  toFun := gam A B R F
  map_zero' := by
    by_cases h : Algebra.Etale A B ∧ Module.FaithfullyFlat A B
    · haveI := h.1
      haveI := h.2
      exact (gam_eq A B R F 0 0).2 (rel_zero A B R F)
    · unfold gam
      rw [if_neg h]
  map_add' u u' := by
    by_cases h : Algebra.Etale A B ∧ Module.FaithfullyFlat A B
    · haveI := h.1
      haveI := h.2
      exact (gam_eq A B R F _ _).2 (rel_add R F _ _ _ _ (gam_spec A B R F u) (gam_spec A B R F u'))
    · unfold gam
      rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem cech1 : ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) [CommRing A], ∃ γ : ∀ (B : Type) [CommRing B] [Algebra A B], Z1 F A B →+ H R (sp A) F 1, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B], (∀ u : Z1 F A B, γ B u = 0 ↔ ∃ v : (onRings F).obj (CommRingCat.of B), (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v - ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v) ∧ (∀ x : H R (sp A) F 1, pull R (spMap (algebraMap A B)) F 1 x = 0 → ∃ u, γ B u = x) ∧ (∀ u, pull R (spMap (algebraMap A B)) F 1 (γ B u) = 0) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Algebra.Etale A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : Z1 F A B) (u' : Z1 F A B'), (u' : (onRings F).obj (CommRingCat.of (B' ⊗[A] B'))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).hom u → γ B' u' = γ B u := by
  intro R _ F A _
  refine ⟨fun B => gamHom A B R F, ?_⟩
  intro B _ _ _ _
  have bij0 := GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 0 _ _ _ _ (GlobalTheory.T.isLimit_widePullbackCone_spec_single A B).some
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    change gam A B R F u = 0 ↔ _
    rw [gam_eq]
    constructor
    · rintro ⟨s, hs, hx⟩
      rw [map_zero] at hx
      obtain ⟨t, rfl⟩ := GlobalTheory.T.simplicialCochain_coboundary_of_class_zero R F _ s hx
      exact ⟨val t (Spec (CommRingCat.of B)) (P0 A B), by rw [← hs, val_coboundary_first_level]⟩
    · rintro ⟨v, hv⟩
      obtain ⟨t, ht⟩ := bij0.2 v
      have ht' : val t (Spec (CommRingCat.of B)) (P0 A B) = v := ht
      have hval : val (cobd t) (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) := by
        rw [val_coboundary_first_level, ht', hv]
      have hc : cobd (cobd t) = 0 := (cobd_eq_zero_iff A B R F _).2 (by rw [hval]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)
      refine ⟨cobd t, hval, ?_⟩
      rw [map_zero]
      obtain ⟨x, hx⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).1 (cobd t) hc
      have h4 := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 0).2.2.2.1 t x hx
      rw [h4] at hx
      exact hx
  · intro x hx
    obtain ⟨s, hs, hcls⟩ := GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero R F _ _ (fB A B) x hx
    exact ⟨⟨val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B), (mem_Z1_iff_cocycle A B R F _).2 ((cobd_eq_zero_iff A B R F s).1 hs)⟩, (gam_eq A B R F _ x).2 ⟨s, rfl, hcls⟩⟩
  · intro u
    obtain ⟨s, hs, hcls⟩ := gam_spec A B R F u
    exact GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle R F (fB A B) s ((cobd_eq_zero_iff A B R F s).2 (by rw [hs]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)) _ hcls
  · intro B' _ _ _ _ φ u u' hu
    change gam A B' R F u' = gam A B R F u
    rw [gam_eq]
    obtain ⟨s, hs, hcls⟩ := gam_spec A B R F u
    refine ⟨(free R).map ((cechMap (fB A B) (fB A B') _ (spec_algHom φ)).app (op ⦋1⦌)) ≫ s, ?_, ?_⟩
    · rw [val_cech_map_first_level, hs, hu]
    · have := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.2.2.2 _ (cechMap (fB A B) (fB A B') _ (spec_algHom φ)) s _ hcls
      rw [← pull_comp, cechMap_aug] at this
      exact this

end GlobalTheory.CechOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosurePiOfEtale
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.PiClosure

noncomputable def integralClosurePiEquiv (R : Type) [CommRing R] (ι : Type) [Finite ι]
    (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra R (E i)] :
    integralClosure R (∀ i, E i) ≃ₐ[R] ∀ i, integralClosure R (E i) :=
  AlgEquiv.ofBijective
    (AlgHom.pi fun i =>
      ((Pi.evalAlgHom R E i).comp (integralClosure R (∀ i, E i)).val).codRestrict
        (integralClosure R (E i)) fun x => x.2.map (Pi.evalAlgHom R E i))
    (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        funext i
        exact congrArg Subtype.val (congrFun hxy i)
      · intro l
        refine ⟨⟨fun i => (l i).1,
          GlobalTheory.PurityProd.isIntegral_of_forall_apply (fun i => (l i).1) fun i => (l i).2⟩, ?_⟩
        funext i
        rfl)

theorem etale_integralClosure_pi : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  intro R _ ι _ E _ _ h
  haveI : Algebra.Etale R (∀ i, integralClosure R (E i)) := inferInstance
  exact Algebra.Etale.of_equiv (integralClosurePiEquiv R ι E).symm

end GlobalTheory.PiClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExcisionConeMapQuasiIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.excisionConeMap_quasiIso' : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  first | (exact @GlobalTheory.EtC.excisionConeMap_quasiIso) | (exact GlobalTheory.EtC.excisionConeMap_quasiIso) | (intros; apply GlobalTheory.EtC.excisionConeMap_quasiIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseUnitRigidifiedGenericGenerator
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem rigUnit_exists_ratio {X Y : Scheme.{0}} (M : LB X) (hM : M.IsLB) (f : Y ⟶ X)
    (t t' : LB.Gen (M.pull f)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → M.ι), r z ∈ (M.pull f).U j →
      gm r z ((M.pull f).U j) (t.s j) = gm r z ⊤ w * gm r z ((M.pull f).U j) (t'.s j) := by
  obtain ⟨w, hw⟩ := glue_unit (X := Y) ⊤ (fun j : PUnit → M.ι => (M.pull f).U j) (fun _ => le_top)
    (fun y _ => by
      obtain ⟨i, hi⟩ := exists_chart hM (f y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩)
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      have h1 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      have h2 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht' (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 ((map_inv _ _).trans (congrArg (·⁻¹) h2)))).trans
        (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_inv _ _))).symm)
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rfl)
  refine ⟨w, fun Z r z j hj => ?_⟩
  have e := (gm_res r z (le_top : (M.pull f).U j ≤ ⊤) hj w).symm.trans (congrArg (gm r z _) (hw j))
  rw [e, map_mul, map_inv, inv_mul_cancel_right]

theorem rigUnit_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → ∀ (eA : Sp K ⟶ pullback X.hom (spMap (algebraMap R K))), eA ≫ pullback.fst X.hom (spMap (algebraMap R K)) = spMap (algebraMap R K) ≫ e → ∀ (M : LB X.left) (rig : LB.Gen (M.pull e)) (c : LB.Gen (M.pull (pullback.fst X.hom (spMap (algebraMap R K))))), M.IsLB → rig.IsGen → LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ c eA) (LB.pullGen M _ _ rig (spMap (algebraMap R K))) → ∀ (a : Kˣ) (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ pullback X.hom (spMap (algebraMap R K))) (z : Z), pullback.fst X.hom (spMap (algebraMap R K)) (r z) ∈ M.U i → (gm (r ≫ pullback.fst X.hom (spMap (algebraMap R K))) z (M.U i) (u.s i)).val = gs (r ≫ pullback.snd X.hom (spMap (algebraMap R K))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull (pullback.fst X.hom (spMap (algebraMap R K)))).U fun _ => i) (c.s fun _ => i)).val) → ∃ b : Rˣ, algebraMap R K (b : R) = (a : K) := by
  intro R K _ _ _ _ _ X e he eA heA M rig c hM hrig hcorr a u hu H
  obtain ⟨w, hw⟩ := rigUnit_exists_ratio M hM e (LB.genPull M u e) rig (LB.isGen_genPull M u hu e) hrig
  haveI : Epi (CommRingCat.ofHom (algebraMap R K)) := by
    have := IsLocalization.epi (nonZeroDivisors R) K
    exact this
  haveI : Mono (spMap (algebraMap R K)) := by
    exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op))
  have hsnd : eA ≫ pullback.snd X.hom (spMap (algebraMap R K)) = 𝟙 _ := by
    rw [← cancel_mono (spMap (algebraMap R K)), Category.assoc, ← pullback.condition, ← Category.assoc, heA,
      Category.assoc, he, Category.comp_id, Category.id_comp]
  let z : Sp K := (⊥ : PrimeSpectrum K)
  choose J hJ using fun χ : Sp K ⟶ X.left => exists_chart hM (χ z)
  have hG : Good M z J := hJ
  have hv := val_corr hG hcorr (𝟙 _)
  rw [val_pull hG, val_pull hG, Category.id_comp, Category.id_comp,
    val_of (L := M) c eA z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => by rw [heA]),
    val_of (L := M) rig _ z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => rfl)] at hv
  have hi := hJ (spMap (algebraMap R K) ≫ e)
  generalize J (spMap (algebraMap R K) ≫ e) = i at hv hi
  have h1 := H i _ eA z (by
    have : (eA ≫ pullback.fst X.hom (spMap (algebraMap R K))) z ∈ M.U i := by rw [heA]; exact hi
    exact this)
  rw [heA, hsnd] at h1
  have hm : spMap (algebraMap R K) z ∈ (M.pull e).U (fun _ => i) := mem_pull.2 hi
  have h2 := hw _ (spMap (algebraMap R K)) z (fun _ => i) hm
  have h3 : gm (spMap (algebraMap R K)) z ((M.pull e).U (fun _ => i)) ((LB.genPull M u e).s (fun _ => i)) =
      gm (spMap (algebraMap R K) ≫ e) z (M.U i) (u.s i) :=
    (gm_res _ z _ hm _).trans (gm_pull _ e z _ hi _)
  have h4 : (gm (spMap (algebraMap R K)) z ⊤ w).val =
      gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
    have h5 := (congrArg Units.val (h2.symm.trans h3)).trans (h1.trans (congrArg (_ * ·) (congrArg Units.val hv)))
    rw [Units.val_mul] at h5
    exact (Units.mul_left_inj _).1 h5
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, ?_⟩
  let φ : K →+* (Sp K).presheaf.stalk z :=
    ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  apply φ.injective
  rw [gm_val _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at h4
  refine Eq.trans ?_ h4
  change ((Sp K).presheaf.germ ⊤ z trivial).hom _ = ((Sp K).presheaf.germ ⊤ z trivial).hom _
  congr 1
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Iso.hom_inv_id_apply] at n
  exact n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAdditiveFnPDivGroupStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_additive_fn_pDivGroup : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (b : G.A 1), cobOne R (G.A 1) b = 0 → ∃ B : G.funs, B.1 1 = b ∧ ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  first | exact @GlobalTheory.PDivGroup.exists_funs_transl_eq_add | exact GlobalTheory.PDivGroup.exists_funs_transl_eq_add | (intros; apply GlobalTheory.PDivGroup.exists_funs_transl_eq_add <;> assumption)
end

