module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitFormLocalizationEtaleNbhd
section
open GlobalTheory.EtC

namespace GlobalTheory.DivUnitForm

private lemma exists_sub_mem_span_pow_of_surj_mod_span {B A₂ : Type} [CommRing B] [CommRing A₂] [Algebra B A₂]
    (f : B) (hsurj : ∀ a' : A₂, ∃ a : B, a' - algebraMap B A₂ a ∈ Ideal.span {algebraMap B A₂ f})
    (n : ℕ) (a' : A₂) : ∃ a : B, a' - algebraMap B A₂ a ∈ Ideal.span {algebraMap B A₂ f ^ n} := by
  induction n generalizing a' with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih a'
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨a₁, ha₁⟩ := hsurj r
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 ha₁
    refine ⟨a + f ^ n * a₁, Ideal.mem_span_singleton'.2 ⟨s, ?_⟩⟩
    have hr' : a' = r * algebraMap B A₂ f ^ n + algebraMap B A₂ a := by rw [hr]; ring
    have hs' : r = s * algebraMap B A₂ f + algebraMap B A₂ a₁ := by rw [hs]; ring
    rw [hr', hs', map_add (f := _), map_mul, map_pow]
    ring

theorem _root_.GlobalTheory.DivUnitForm.unit_form : ∀ (B A₂ : Type) [CommRing B] [CommRing A₂]
    [Algebra B A₂] (f : B), _root_.GlobalTheory.EtC.IsExcisionNbhd B A₂ f →
    ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ (b₁ : B) (m : ℕ) (e : A₂),
      e - 1 ∈ Ideal.span {algebraMap B A₂ f} ∧
      algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) =
        (c : Localization.Away (algebraMap B A₂ f)) *
          algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) := by
  intro B A₂ _ _ _ f hf c
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (algebraMap B A₂ f)
    (c : Localization.Away (algebraMap B A₂ f))
  obtain ⟨l, y, hy⟩ := IsLocalization.Away.surj (algebraMap B A₂ f)
    ((c⁻¹ : (Localization.Away (algebraMap B A₂ f))ˣ) : Localization.Away (algebraMap B A₂ f))
  have hxy : algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (x * y) =
      algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f ^ (k + l)) := by
    rw [map_mul, ← hx, ← hy, map_pow, pow_add]
    have hc : (c : Localization.Away (algebraMap B A₂ f)) *
        ((c⁻¹ : (Localization.Away (algebraMap B A₂ f))ˣ) : Localization.Away (algebraMap B A₂ f))
          = 1 := Units.mul_inv c
    linear_combination (algebraMap A₂ (Localization.Away (algebraMap B A₂ f))
      (algebraMap B A₂ f) ^ k * algebraMap A₂ (Localization.Away (algebraMap B A₂ f))
        (algebraMap B A₂ f) ^ l) * hc
  obtain ⟨⟨s, hs⟩, hsxy⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap B A₂ f))
    (Localization.Away (algebraMap B A₂ f))).1 hxy
  obtain ⟨N, rfl⟩ := hs
  simp only at hsxy
  set X := x * algebraMap B A₂ f ^ N with hX
  have hXy : X * y = algebraMap B A₂ f ^ (k + N + l) := by
    rw [hX, show k + N + l = N + (k + l) by ring, pow_add]
    linear_combination hsxy
  obtain ⟨b, hb⟩ := exists_sub_mem_span_pow_of_surj_mod_span f hf.2.1 (k + N + l + 1) X
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hb
  refine ⟨b, k + N, 1 - algebraMap B A₂ f * y * r, Ideal.mem_span_singleton'.2 ⟨-(y * r), by ring⟩, ?_⟩
  have hbX : algebraMap B A₂ b = X * (1 - algebraMap B A₂ f * y * r) := by
    have h1 : X * (1 - algebraMap B A₂ f * y * r) = X - algebraMap B A₂ f * r * (X * y) := by ring
    rw [h1, hXy]
    linear_combination hr
  rw [hbX, hX]
  simp only [map_mul, map_pow]
  rw [← hx]
  ring

end GlobalTheory.DivUnitForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAdicCompletionSpan
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem faithfullyFlat_adicCompletion_span (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (t : R) (ht : t ∈ maximalIdeal R) :
    Module.FaithfullyFlat R (AdicCompletion (Ideal.span {t}) R) := by
  haveI : Module.Flat R (AdicCompletion (Ideal.span {t}) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hm]
  have hle : Ideal.span {t} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).2 ht
  have hmax := AdicCompletion.isMaximal_map_of_le (Ideal.span {t}) (maximalIdeal R) hle
    (Submodule.fg_span_singleton t)
  intro h
  apply hmax.ne_top
  have e := Ideal.smul_top_eq_map (S := AdicCompletion (Ideal.span {t}) R) (maximalIdeal R)
  rw [h] at e
  apply Submodule.restrictScalars_injective R
  rw [← e]; rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem exists_integral_point (A R C : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing R] [CommRing C] [Algebra R C] (ρ : R →+* A) (hint : Algebra.IsIntegral R C)
    (s : C →+* FractionRing A) (hs : s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) :
    ∃ g : C →+* A, (algebraMap A (FractionRing A)).comp g = s ∧ g.comp (algebraMap R C) = ρ := by
  set K := FractionRing A
  have hmem : ∀ c : C, s c ∈ (algebraMap A K).range := by
    intro c
    obtain ⟨p, hp, hpc⟩ := hint.isIntegral c
    have hi : IsIntegral A (s c) := by
      refine ⟨p.map ρ, hp.map ρ, ?_⟩
      rw [Polynomial.eval₂_map, ← hs, ← Polynomial.hom_eval₂, hpc, map_zero]
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
    exact ⟨a, ha⟩
  let e := RingEquiv.ofBijective (algebraMap A K).rangeRestrict
    ⟨fun x y h => IsFractionRing.injective A K (congrArg Subtype.val h),
     (algebraMap A K).rangeRestrict_surjective⟩
  let g : C →+* A := e.symm.toRingHom.comp (s.codRestrict _ hmem)
  have hg : (algebraMap A K).comp g = s := by
    ext c
    have : e (g c) = s.codRestrict _ hmem c := by simp [g]
    exact congrArg Subtype.val this
  refine ⟨g, hg, ?_⟩
  ext r
  apply IsFractionRing.injective A K
  have := congrArg (fun f => f r) hs
  simp only [RingHom.comp_apply] at this
  change (algebraMap A K) (g (algebraMap R C r)) = _
  rw [← this, ← hg, RingHom.comp_apply]
  rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem mem_pow_of_mul_mem_pow (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R)
    (a : A) (ha : a ≠ 0) : ∀ (n : ℕ) (r : R), algebraMap A R a * r ∈ Ideal.span {t ^ n} →
      r ∈ Ideal.span {t ^ n} := by
  have hρa : ρ (algebraMap A R a) = a := by
    simpa using congrArg (fun f => f a) hρ
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r hr
    have hr1 : algebraMap A R a * r ∈ RingHom.ker ρ := by
      rw [hker, Ideal.mem_span_singleton]
      exact (dvd_pow_self t (Nat.succ_ne_zero n)).trans (Ideal.mem_span_singleton.1 hr)
    rw [RingHom.mem_ker, map_mul, hρa] at hr1
    have hr0 : r ∈ Ideal.span {t} := by
      rw [← hker, RingHom.mem_ker]
      exact (mul_eq_zero.1 hr1).resolve_left ha
    obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton.1 hr0
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hr
    have h2 : algebraMap A R a * r' = t ^ n * q := by
      have : t * (algebraMap A R a * r') = t * (t ^ n * q) := by
        rw [pow_succ] at hq
        linear_combination hq
      have h3 : t * (algebraMap A R a * r' - t ^ n * q) = 0 := by rw [mul_sub, this, sub_self]
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h3)
    have := ih r' (Ideal.mem_span_singleton.2 ⟨q, h2⟩)
    obtain ⟨q', rfl⟩ := Ideal.mem_span_singleton.1 this
    exact Ideal.mem_span_singleton.2 ⟨q', by ring⟩

theorem torsionFree_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.TorsionFreeOver A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow] at hm
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
  exact mem_pow_of_mul_mem_pow A R ρ hρ t hker ht a ha n r hm

end GlobalTheory.GoodEtaleSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInjectiveRingHomIsLocalHomAndExtend
section
open IsLocalRing

namespace GlobalTheory

theorem finite_injective_localHom_and_extend (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R) :
    Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionExistence.main
  | exact _root_.GlobalTheory.ValuationExtensionExistence.main
  | (apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionExistence.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOfFormallyUnramified
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.AbhFin

theorem finite_integralClosure_of_formallyUnramified (R K C : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing C] [Algebra K C] [Algebra R C] [IsScalarTower R K C] [FiniteDimensional K C]
    [Algebra.FormallyUnramified K C] : Module.Finite R (integralClosure R C) := by
  classical
  haveI : IsArtinianRing C := IsArtinianRing.of_finite K C
  haveI : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field K C
  haveI := Fintype.ofFinite (MaximalSpectrum C)
  haveI : ∀ m : MaximalSpectrum C, Module.Finite R (integralClosure R (C ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : Algebra.FormallyUnramified K (C ⧸ m.asIdeal) :=
      Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal) Ideal.Quotient.mk_surjective
    haveI : Algebra.IsSeparable K (C ⧸ m.asIdeal) := Algebra.FormallyUnramified.isSeparable K _
    exact IsIntegralClosure.finite R K (C ⧸ m.asIdeal) _
  let red : ∀ m : MaximalSpectrum C, integralClosure R C →ₗ[R] integralClosure R (C ⧸ m.asIdeal) := fun m =>
    (((Ideal.Quotient.mkₐ R m.asIdeal).comp (integralClosure R C).val).codRestrict
      (integralClosure R (C ⧸ m.asIdeal))
      (fun a => (show IsIntegral R (a : C) from a.2).map (Ideal.Quotient.mkₐ R m.asIdeal))).toLinearMap
  refine Module.Finite.of_injective (LinearMap.pi red) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  apply Subtype.ext
  apply (IsArtinianRing.equivPi C).injective
  show _ = IsArtinianRing.equivPi C 0
  rw [map_zero]
  funext m
  exact congrArg Subtype.val (congrFun ha m)

end GlobalTheory.AbhFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalContaining
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_maximal_containing : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  first | (exact @GlobalTheory.finite_maximal_ideals_containing') | (exact GlobalTheory.finite_maximal_ideals_containing') | (intros; apply GlobalTheory.finite_maximal_ideals_containing' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicRootsBddMulIsIntegralStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_monic_of_roots_bdd_of_mul_isIntegral : ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  first | (exact @GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_roots_bdd_mul_isIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportStabilizerWeightedPairTerm
section
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

namespace GlobalTheory.OrbitUnfold

theorem finite_support_pairTerm :
    ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ),
      (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) →
      (∀ y : Y, (Function.support (F y)).Finite) →
      {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite →
      (Function.support (fun o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ) =>
        pairTerm F (Quotient.out o))).Finite := by
  intro Γ Y _ _ F hF hfin hS
  refine (hS.biUnion (t := fun o' =>
      (fun γ : Γ => (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of γ))) ''
        Function.support (F (Quotient.out o'))) (fun o' _ => (hfin _).image _)).subset ?_
  intro o ho
  have hne : F (Quotient.out o).1 (val (Quotient.out o).2) ≠ 0 := by
    intro h
    apply ho
    simp [pairTerm, h]
  set p := Quotient.out o with hp
  set o' : MulAction.orbitRel.Quotient Γ Y := Quotient.mk (MulAction.orbitRel Γ Y) p.1 with ho'
  obtain ⟨η, hη⟩ := Quotient.exact (Quotient.out_eq o')
  change η • p.1 = Quotient.out o' at hη
  have hval : F (Quotient.out o') (η * val p.2 * η⁻¹) ≠ 0 := by
    rw [← hη, hF]; exact hne
  refine Set.mem_biUnion (x := o') ⟨_, hval⟩ ⟨η * val p.2 * η⁻¹, hval, ?_⟩
  have hsm : (η • p : Y × ConjSelf Γ) = (Quotient.out o', of (η * val p.2 * η⁻¹)) := by
    rw [Prod.smul_def, hη]; rfl
  show Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of (η * val p.2 * η⁻¹)) = o
  rw [← hsm]
  calc Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (η • p)
      = Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p :=
        Quotient.sound ⟨η, rfl⟩
    _ = o := by rw [hp]; exact Quotient.out_eq o

end GlobalTheory.OrbitUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeInvariantsFiniteGroupAndFiniteStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteType_invariants_finite_group_and_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C'] (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C'), (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' := by
  first | exact @GlobalTheory.finiteType_invariants_and_finite | exact GlobalTheory.finiteType_invariants_and_finite | (intros; apply GlobalTheory.finiteType_invariants_and_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankEigenspaceLe
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem finrank_le_card_mul_finrank_eigenspace_le :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R]
      (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) →
      ∀ (χ : H →* Kˣ) (u : R),
      (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R →
      ∀ (Vm V Vp N : Submodule K R) [FiniteDimensional K Vm] [FiniteDimensional K V]
        [FiniteDimensional K Vp], (∀ h, ∀ x ∈ V, st h x ∈ V) →
      (∀ h, ∀ x ∈ Vm, x * st h u ∈ V) → (∀ h, ∀ x ∈ V, x * st h u ∈ Vp) →
      (∀ x, x ∈ N ↔ x ∈ V ∧ ∀ h, st h x = ((χ h : Kˣ) : K) • x) →
      Module.finrank K Vm ≤ Fintype.card H * Module.finrank K N ∧
        Fintype.card H * Module.finrank K N ≤ Module.finrank K Vp := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet Vm V Vp N _ _ _ hV hm hp hN
  obtain ⟨hTr, hPhi, hPsi⟩ := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H K R st h1 hmul χ u hdet
  have hNV : N ≤ V := fun x hx => ((hN x).1 hx).1
  have : FiniteDimensional K N := Submodule.finiteDimensional_of_le hNV
  have hrk : Module.finrank K (H → N) = Fintype.card H * Module.finrank K N := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [← hrk]
  constructor
  · have hmem : ∀ (f : Vm) (h : H),
        ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g ((f : R) * st h u) ∈ N := fun f h =>
      (hN _).2 ⟨V.sum_mem fun g _ => V.smul_mem _ (hV g _ (hm h _ f.2)), fun g => hTr _ g⟩
    let Φ : Vm →ₗ[K] (H → N) :=
      { toFun := fun f h => ⟨_, hmem f h⟩
        map_add' := fun f f' => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, map_add (f := _), smul_add, Finset.sum_add_distrib,
            Pi.add_apply]
        map_smul' := fun c f => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, map_smul, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun g _ => smul_comm _ _ _ }
    refine LinearMap.finrank_le_finrank_of_injective (f := Φ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    apply Subtype.ext
    exact hPhi f fun h => congrArg Subtype.val (congrFun hf h)
  · have hmem : ∀ F : H → N, ∑ h, (F h : R) * st h u ∈ Vp := fun F =>
      Vp.sum_mem fun h _ => hp h _ (hNV (F h).2)
    let Ψ : (H → N) →ₗ[K] Vp :=
      { toFun := fun F => ⟨_, hmem F⟩
        map_add' := fun F F' => by
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
        map_smul' := fun c F => by
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum] }
    refine LinearMap.finrank_le_finrank_of_injective (f := Ψ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    have := hPsi (fun h => (F h : R)) (fun h g => ((hN _).1 (F h).2).2 g)
      (congrArg Subtype.val hF)
    funext h
    exact Subtype.ext (congrFun this h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotOneSubIdempotentEqMulStatement
section
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k) (e : A), IsIdempotentElem e → φ e = 1 → (∀ a, φ a = 0 → IsNilpotent (e * a)) → ∀ (H : Type u) [AddCommGroup H] [Module A H] [Module k H] [IsScalarTower k A H] [FiniteDimensional k H] [Module.Projective A H], Module.finrank k (H ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A H)) = Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) * Module.finrank k (A ⧸ Ideal.span {1 - e}) := by
  first | (exact @GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (exact GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (intros; apply GlobalTheory.finrank_quot_one_sub_idem_eq_mul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMapIdempotentEqRankAtStalkStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_map_idempotent_eq_rankAtStalk : ∀ (A : Type) [CommRing A] (n : ℕ) (P : Matrix (Fin n) (Fin n) A), P * P = P →
    ∀ (k : Type) [Field k] (g : A →+* k),
      Module.finrank k (LinearMap.range (P.map g).mulVecLin) =
        Module.rankAtStalk (LinearMap.range P.mulVecLin) (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
  first | (exact @GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (exact GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (intros; apply GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCompEqFinsumCardFiberMulStatement
section
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_comp_eq_finsum_card_fiber_mul : ∀ {X Y : Type} (π : X → Y) (h : Y → ℂ), ((∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) → ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
  first | exact @GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | exact GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | (intros; apply GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul <;> assumption)
end

