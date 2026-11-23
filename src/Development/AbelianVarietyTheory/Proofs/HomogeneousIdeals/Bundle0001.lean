module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqExpFderiv
section
universe u_1

namespace GlobalTheory.ExpOfFrechetDerivative

theorem eq_exp_fderiv {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    (hd : DifferentiableAt ℂ f (0 : E)) (h0 : f (0 : E) ≠ (0 : ℂ))
    (hmul : ∀ x y : E, f (x + y) = f x * f y) (z : E) :
    f z = Complex.exp ((fderiv ℂ f (0 : E) : E → ℂ) z) := by
  set L := fderiv ℂ f (0 : E) with hL

  have hf0 : f 0 = 1 := by
    have h00 := hmul 0 0
    rw [add_zero] at h00
    have hfac : f 0 * (f 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h00, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h h0
    · exact sub_eq_zero.mp h

  have hD : ∀ x : E, HasFDerivAt f (f x • L) x := by
    intro x
    have h1 : HasFDerivAt f L (x - x) := by
      rw [sub_self]
      exact hd.hasFDerivAt
    have h2 : HasFDerivAt (fun y : E => f (y - x)) L x := by
      have h := h1.comp (f := fun y : E => y - x) x ((hasFDerivAt_id x).sub_const x)
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    refine (h2.const_mul (f x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    show f y = f x * f (y - x)
    rw [← hmul, add_sub_cancel]

  have hE : ∀ y : E, HasFDerivAt (fun y => f y * Complex.exp (-(L y)))
      (f y • (Complex.exp (-(L y)) • -L) + Complex.exp (-(L y)) • (f y • L)) y :=
    fun y => (hD y).mul (L.hasFDerivAt.neg.cexp)
  have hzero : ∀ y, fderiv ℂ (fun y => f y * Complex.exp (-(L y))) y = 0 := by
    intro y
    rw [(hE y).fderiv]
    ext v
    simp only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]
    ring
  have hc := is_const_of_fderiv_eq_zero (fun y => (hE y).differentiableAt) hzero z 0
  simp only [map_zero, neg_zero, Complex.exp_zero, mul_one, hf0] at hc
  calc f z = f z * Complex.exp (-(L z)) * Complex.exp (L z) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (L z) := by rw [hc, one_mul]

end GlobalTheory.ExpOfFrechetDerivative
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi
section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory

namespace FlatDescent

universe u

variable {X Y Z : Scheme.{u}}

theorem injective_appTop_of_epi (p : Y ⟶ X) [Epi p] : Function.Injective p.appTop := by
  have : Epi (Scheme.Γ.rightOp.map p) :=
    have := ΓSpec.adjunction.isLeftAdjoint
    inferInstance
  have : Mono p.appTop := inferInstanceAs (Mono (Scheme.Γ.rightOp.map p).unop)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback p.appTop

theorem exists_appTop_eq_of_effectiveEpi (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) (hs : f.appTop s = g.appTop s) :
    ∃ a : Γ(X, ⊤), p.appTop a = s := by
  let E := RingHom.eqLocus f.appTop.hom g.appTop.hom
  let ι : CommRingCat.of E ⟶ Γ(Y, ⊤) := CommRingCat.ofHom E.subtype
  have hι : ι ≫ f.appTop = ι ≫ g.appTop := by
    ext x
    exact x.2
  have : HasPullback p p := inferInstance
  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair p h (Y.toSpecΓ ≫ Spec.map ι) (by
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp,
      ← Spec.map_comp, hι])
  refine ⟨u.appTop ((Scheme.ΓSpecIso (.of E)).inv ⟨s, hs⟩), ?_⟩
  have h1 : (Scheme.ΓSpecIso (.of E)).inv ≫ u.appTop ≫ p.appTop = ι := by
    rw [← Scheme.Hom.comp_appTop, hu, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  exact congr($h1 ⟨s, hs⟩)

theorem appTop_appTop_eq {p : Y ⟶ X} {f g : Z ⟶ Y} (h : f ≫ p = g ≫ p) (a : Γ(X, ⊤)) :
    f.appTop (p.appTop a) = g.appTop (p.appTop a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, h]

theorem existsUnique_appTop_eq_iff (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) :
    (∃! a : Γ(X, ⊤), p.appTop a = s) ↔ f.appTop s = g.appTop s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact appTop_appTop_eq h.w a
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s hs
    exact ⟨a, ha, fun b hb => injective_appTop_of_epi p (hb.trans ha.symm)⟩

theorem isUnit_appTop_iff (p : Y ⟶ X) [EffectiveEpi p] (a : Γ(X, ⊤)) :
    IsUnit (p.appTop a) ↔ IsUnit a := by
  refine ⟨fun ha => ?_, fun ha => ha.map p.appTop.hom⟩
  obtain ⟨t, ht⟩ := ha.exists_right_inv
  have h := IsPullback.of_hasPullback p p
  obtain ⟨b, rfl⟩ := exists_appTop_eq_of_effectiveEpi p h t (by
    have h1 := congrArg (pullback.fst p p).appTop.hom ht
    have h2 := congrArg (pullback.snd p p).appTop.hom ht
    rw [map_mul, map_one] at h1 h2
    rw [appTop_appTop_eq h.w a] at h1
    exact left_inv_eq_right_inv ((mul_comm _ _).trans h1) h2)
  exact IsUnit.of_mul_eq_one b (injective_appTop_of_epi p (by rw [map_mul, ht, map_one]))

theorem existsUnique_units_appTop_eq_iff (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)ˣ) :
    (∃! a : Γ(X, ⊤)ˣ, Units.map p.appTop.hom.toMonoidHom a = s) ↔
      Units.map f.appTop.hom.toMonoidHom s = Units.map g.appTop.hom.toMonoidHom s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact Units.ext (appTop_appTop_eq h.w a)
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s (congrArg Units.val hs)
    obtain ⟨a, rfl⟩ := (isUnit_appTop_iff p a).1 (ha ▸ s.isUnit)
    exact ⟨a, Units.ext ha, fun b hb => Units.ext <|
      injective_appTop_of_epi p ((congrArg Units.val hb).trans ha.symm)⟩

section Opens

theorem isPullback_resLE {p : Y ⟶ X} {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens)
    (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) :
    IsPullback (f.resLE _ W hf) (g.resLE _ W hg) (p ∣_ U) (p ∣_ U) := by
  subst hW
  have hc : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      (s.fst ≫ (p ⁻¹ᵁ U).ι) ≫ p = (s.snd ≫ (p ⁻¹ᵁ U).ι) ≫ p := fun s => by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, s.condition_assoc]
  have hr : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      Set.range (h.lift _ _ (hc s)) ⊆ Set.range (f ⁻¹ᵁ p ⁻¹ᵁ U).ι := fun s => by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (h.lift _ _ _ x) ∈ p ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_apply, h.lift_fst, Scheme.Hom.comp_apply]
    exact (s.fst x).2
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => IsOpenImmersion.lift (f ⁻¹ᵁ p ⁻¹ᵁ U).ι
    (h.lift _ _ (hc s)) (hr s)) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono U.ι]
    simp [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, h.w]
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (f ⁻¹ᵁ p ⁻¹ᵁ U).ι, IsOpenImmersion.lift_fac]
    refine h.hom_ext ?_ ?_
    · simp [← h₁]
    · simp [← h₂]

theorem appTop_resLE_apply (f : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ f ⁻¹ᵁ V)
    (s : Γ(Y, V)) : (f.resLE V W e).appTop (V.topIso.inv s) = W.topIso.inv (f.appLE V W e s) := by
  have : V.topIso.inv ≫ (f.resLE V W e).appTop = f.appLE V W e ≫ W.topIso.inv := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc]
  exact congr($this s)

theorem appTop_morphismRestrict_apply (p : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    (p ∣_ U).appTop (U.topIso.inv a) = (p ⁻¹ᵁ U).topIso.inv (p.app U a) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, appTop_resLE_apply, Scheme.Hom.appLE_eq_app]

theorem effectiveEpi_morphismRestrict (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : EffectiveEpi (p ∣_ U) := by
  have : Flat (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : Surjective (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : QuasiCompact (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  infer_instance

theorem existsUnique_app_eq_iff (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens) (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U)
    (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) (s : Γ(Y, p ⁻¹ᵁ U)) :
    (∃! a : Γ(X, U), p.app U a = s) ↔ f.appLE _ W hf s = g.appLE _ W hg s := by
  have := effectiveEpi_morphismRestrict p U
  have hb : ∀ {T : Scheme.{u}} (V : T.Opens), Function.Bijective V.topIso.inv := fun V =>
    ConcreteCategory.bijective_of_isIso _
  rw [← (hb W).1.eq_iff, ← appTop_resLE_apply, ← appTop_resLE_apply,
    ← existsUnique_appTop_eq_iff (p ∣_ U) (isPullback_resLE h U W hW hf hg),
    ← (Equiv.ofBijective _ (hb U)).existsUnique_congr_right]
  simp only [Equiv.ofBijective_apply, appTop_morphismRestrict_apply, (hb _).1.eq_iff]

theorem isUnit_app_iff (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p] (U : X.Opens)
    (a : Γ(X, U)) : IsUnit (p.app U a) ↔ IsUnit a := by
  have := effectiveEpi_morphismRestrict p U
  rw [← isUnit_map_iff (p ⁻¹ᵁ U).topIso.inv.hom, ← appTop_morphismRestrict_apply,
    isUnit_appTop_iff, isUnit_map_iff]

end Opens

end FlatDescent

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsHomDivMulRefine
section
namespace GlobalTheory

namespace QuadRefinement

section Additive

variable {O Y M : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y]
  [AddCommGroup M]

variable {τ : Y →+ Y →+ M} {w : O}

end Additive

section Multiplicative

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A]

def mulRefine (τ : Y →+ Y →+ Additive A) (w : O) (y : Y) : A := (τ y (w • y)).toMul

variable {τ : Y →+ Y →+ Additive A} {w : O}

end Multiplicative

section HalfElement

variable {K : Type*} [Field K] [CharZero K] [StarRing K] {d : ℤ} {s : K}


end HalfElement

section Example

open QuadraticAlgebra

end Example

end QuadRefinement

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_smul_add_apply_smul_eq_of_add_star_eq_one (hsymm : ∀ y y', τ y y' = τ y' y)
    (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) (hw : w + star w = 1) (y y' : Y) :
    τ y (w • y') + τ y' (w • y) = τ y y' := by
  rw [hsymm y' (w • y), hadj, ← map_add (τ y), ← add_smul, hw, one_smul]

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_add_smul_add_eq_add_add (hsymm : ∀ y y', τ y y' = τ y' y)
    (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) (hw : w + star w = 1) (y y' : Y) :
    τ (y + y') (w • (y + y')) = τ y (w • y) + τ y' (w • y') + τ y y' := by
  rw [← apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw y y']
  simp only [smul_add, map_add (f := _), AddMonoidHom.add_apply]
  abel

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_neg_smul_neg_eq (y : Y) : τ (-y) (w • -y) = τ y (w • y) := by
  simp

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_smul_smul_smul_eq_zsmul_of_mul_star_eq (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y'))
    (a : O) (n : ℤ) (h : a * star a = n) (y : Y) :
    τ (a • y) (w • a • y) = n • τ y (w • y) := by
  have e : star a * w * a = (n : O) * w := by rw [← h]; ring
  rw [hadj, smul_smul, smul_smul, e, mul_smul, Int.cast_smul_eq_zsmul, map_zsmul]

theorem _root_.GlobalTheory.quadratic_refinement :
    (∀ {O Y A : Type} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A]
      (τ : Y →+ Y →+ Additive A) (w : O), (∀ y y', τ y y' = τ y' y) →
      (∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) → w + star w = 1 →
      (∀ y y', _root_.GlobalTheory.QuadRefinement.mulRefine τ w (y + y') =
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w y *
          _root_.GlobalTheory.QuadRefinement.mulRefine τ w y' * (τ y y').toMul) ∧
      (∀ y, _root_.GlobalTheory.QuadRefinement.mulRefine τ w (-y) =
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w y) ∧
      (∀ y, _root_.GlobalTheory.QuadRefinement.mulRefine τ w y ^ 2 = (τ y y).toMul) ∧
      (∀ (a : O) (n : ℤ), a * star a = n → ∀ y,
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w (a • y) =
          _root_.GlobalTheory.QuadRefinement.mulRefine τ w y ^ n) ∧
      (∀ ψ : Y → A, (∀ y y', ψ (y + y') = ψ y * ψ y' * (τ y y').toMul) → (∀ y, ψ (-y) = ψ y) →
        (∃ α : Multiplicative Y →* A,
          (∀ y, α (Multiplicative.ofAdd y) = ψ y / _root_.GlobalTheory.QuadRefinement.mulRefine τ w y)
            ∧ α ^ 2 = 1) ∧
        ∀ n : ℤ, w * star w = n → (∀ y, ψ (w • y) = ψ y ^ n) →
          (∀ y, ψ (star w • y) = ψ y ^ n) → ψ = _root_.GlobalTheory.QuadRefinement.mulRefine τ w) ∧
      (∀ (v : Additive A →+ ℚ) y,
        2 * v (Additive.ofMul (_root_.GlobalTheory.QuadRefinement.mulRefine τ w y)) =
          τ.compr₂ v y y)) ∧
    (∀ {K : Type} [Field K] [CharZero K] [StarRing K] (d : ℤ) (s : K), d % 8 = 7 →
      s ^ 2 = -(d : K) → star s = -s →
      IsIntegral ℤ ((1 + s) / 2) ∧ (1 + s) / 2 + star ((1 + s) / 2) = 1 ∧
      (1 + s) / 2 * star ((1 + s) / 2) = (((1 + d) / 4 : ℤ) : K) ∧
      4 * ((1 + d) / 4) = 1 + d ∧ Even ((1 + d) / 4)) := by
  refine ⟨?_, ?_⟩
  · intro O Y A _ _ _ _ _ τ w hsymm hadj hw
    set m := _root_.GlobalTheory.QuadRefinement.mulRefine τ w with hmdef
    have hm : ∀ y, m y = (τ y (w • y)).toMul := fun _ => rfl
    have hadd : ∀ y y', m (y + y') = m y * m y' * (τ y y').toMul := by
      intro y y'
      simp only [hm, apply_add_smul_add_eq_add_add hsymm hadj hw, toMul_add]
    have hneg : ∀ y, m (-y) = m y := by
      intro y
      simp only [hm, apply_neg_smul_neg_eq]
    have hsq : ∀ y, m y ^ 2 = (τ y y).toMul := by
      intro y
      rw [hm, ← toMul_nsmul, two_nsmul, apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw]
    have hpow : ∀ (a : O) (n : ℤ), a * star a = n → ∀ y, m (a • y) = m y ^ n := by
      intro a n h y
      rw [hm, hm, apply_smul_smul_smul_eq_zsmul_of_mul_star_eq hadj a n h, toMul_zsmul]
    refine ⟨hadd, hneg, hsq, hpow, ?_, ?_⟩
    · intro ψ hψ heven
      have h0 : ψ 0 = 1 := by
        have := hψ 0 0
        simpa using this
      have hψsq : ∀ y, ψ y ^ 2 = (τ y y).toMul := by
        intro y
        have h := hψ y (-y)
        rw [add_neg_cancel, h0, heven, map_neg, toMul_neg, eq_comm, mul_inv_eq_one] at h
        rw [sq, h]
      have hb : ∀ y y', ψ (y + y') / m (y + y') = ψ y / m y * (ψ y' / m y') := by
        intro y y'
        rw [hψ, hadd, mul_div_mul_right_eq_div, div_mul_div_comm]
      have hbsq : ∀ y, (ψ y / m y) ^ 2 = 1 := by
        intro y
        rw [div_pow, hψsq, hsq, div_self']
      let β : Multiplicative Y →* A :=
        MonoidHom.mk' (fun y => ψ y.toAdd / m y.toAdd) (fun y y' => by
          simp only [toAdd_mul]
          exact hb _ _)
      refine ⟨⟨β, fun y => rfl, ?_⟩, ?_⟩
      · ext y
        show β y ^ 2 = 1
        exact hbsq (Multiplicative.toAdd y)
      · intro n hn h1 h2
        funext y
        have hw1 : ψ (w • y) / m (w • y) = (ψ y / m y) ^ n := by
          rw [h1, hpow w n hn, div_zpow]
        have hw2 : ψ (star w • y) / m (star w • y) = (ψ y / m y) ^ n := by
          rw [h2, hpow (star w) n (by rw [star_star, mul_comm, hn]), div_zpow]
        have e : w • y + star w • y = y := by rw [← add_smul, hw, one_smul]
        have key : ψ y / m y = 1 := by
          calc ψ y / m y = ψ (w • y + star w • y) / m (w • y + star w • y) := by rw [e]
            _ = ((ψ y / m y) ^ 2) ^ n := by rw [hb, hw1, hw2, ← mul_zpow, ← sq]
            _ = 1 := by rw [hbsq, one_zpow]
        exact div_eq_one.mp key
    · intro v y
      rw [hm, ofMul_toMul, AddMonoidHom.compr₂_apply, ← apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw y y,
        map_add, two_mul]
  · intro K _ _ _ d s hd hs hstar
    obtain ⟨k, rfl⟩ : ∃ k, d = 8 * k + 7 := ⟨d / 8, by omega⟩
    have hq : (1 + (8 * k + 7)) / 4 = 2 * k + 2 := by omega
    rw [hq]
    push_cast at hs
    have hst : star ((1 + s) / 2) = (1 - s) / 2 := by
      rw [div_eq_mul_inv, star_mul', star_inv₀, star_add, star_one, hstar, star_ofNat]
      ring
    refine ⟨?_, ?_, ?_, by omega, ⟨k + 1, by ring⟩⟩
    · refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k + 2 : ℤ)), ?_, ?_⟩
      · monicity!
      · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        rw [algebraMap_int_eq, eq_intCast]
        push_cast
        linear_combination (1 / 4 : K) * hs
    · rw [hst]; ring
    · rw [hst]; push_cast; linear_combination (-1 / 4 : K) * hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIrreducibleGeneralizations
section
universe u_1

namespace GlobalTheory.IrreducibleGeneralizations

open AlgebraicGeometry Topology

theorem isIrreducible_generalizations {X : Scheme.{u_1}} (x : X) [IsDomain (X.presheaf.stalk x)] :
    IsIrreducible {y : X | y ⤳ x} := by

  have hSpec : IsIrreducible (Set.univ : Set (PrimeSpectrum (X.presheaf.stalk x))) :=
    IrreducibleSpace.isIrreducible_univ _
  rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
  exact hSpec.image _ (X.fromSpecStalk x).continuous.continuousOn

theorem component_eq_closure {X : Scheme.{u_1}} {x : X} [IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hx : x ∈ Z) :
    Z = closure {y : X | y ⤳ x} := by

  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hsub : Z ⊆ closure {y : X | y ⤳ x} := fun z hz =>
    closure_mono (Set.singleton_subset_iff.mpr (hη.specializes hx)) (hη.specializes hz).mem_closure
  exact hsub.antisymm (hZ.2 (isIrreducible_generalizations x).closure hsub)

theorem main : ∀ {X : AlgebraicGeometry.Scheme} {x : ↥X} [IsDomain (↑(TopCat.Presheaf.stalk (AlgebraicGeometry.PresheafedSpace.presheaf (AlgebraicGeometry.SheafedSpace.toPresheafedSpace (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace X)))) x) : Type u_1)] {Z W : Set ↥X}, Z ∈ irreducibleComponents ↥X → W ∈ irreducibleComponents ↥X → x ∈ Z → x ∈ W → Z = W := by
  intro X x _ Z W hZ hW hxZ hxW
  rw [component_eq_closure hZ hxZ, component_eq_closure hW hxW]

end GlobalTheory.IrreducibleGeneralizations
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecMap
section
universe u_1

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SchemeDominantSpecMap

theorem appTop_injective {R A : CommRingCat.{u_1}} (φ : R ⟶ A) (h : Function.Injective φ) :
    Function.Injective (Spec.map φ).appTop := by

  have e : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality φ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1.comp
    (h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1)

theorem isSchemeTheoreticallyDominant_specMap {R A : CommRingCat.{u_1}} (φ : R ⟶ A)
    (h : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    (RingHom.injective_iff_ker_eq_bot (Spec.map φ).appTop.hom).1 (appTop_injective φ h),
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_bot]

end GlobalTheory.SchemeDominantSpecMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.PowCardLeNormProd
section
namespace GlobalTheory.RootNormBound

open Polynomial

theorem pow_card_le_norm_prod {ε : ℝ} (hε : 0 ≤ ε) (s : Multiset ℂ)
    (hs : ∀ t ∈ s, ε ≤ ‖t‖) :
    ε ^ Multiset.card s ≤ ‖(s.map (fun a => (0 : ℂ) - a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, norm_mul, mul_comm]
    have ha : ε ≤ ‖(0 : ℂ) - a‖ := by
      rw [zero_sub, norm_neg]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hε _)
      (norm_nonneg _)

theorem exists_root_norm_lt {h : Polynomial ℂ} (hm : h.Monic) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ‖h.coeff 0‖ < ε ^ h.natDegree) : ∃ t : ℂ, h.IsRoot t ∧ ‖t‖ < ε := by
  by_contra hne
  push Not at hne
  have hsp : h.Splits := IsAlgClosed.splits h
  have hne0 : h ≠ 0 := hm.ne_zero
  have key := pow_card_le_norm_prod hε h.roots fun t ht => hne t ((mem_roots hne0).1 ht)
  rw [← hsp.eval_eq_prod_roots_of_monic hm 0, ← coeff_zero_eq_eval_zero,
    ← hsp.natDegree_eq_card_roots] at key
  exact absurd hc (not_lt.2 key)

end GlobalTheory.RootNormBound
end

