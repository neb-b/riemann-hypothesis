module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacter
section
noncomputable section

open Polynomial IntermediateField

namespace GlobalTheory.NeedB.KumLemma

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem pow_val_add {N : ℕ} [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem exists_pow {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    ∃ i : ZMod N, g θ = ζ ^ i.val * θ := by
  obtain ⟨c, hc⟩ := hN
  have hg : (g θ) ^ N = θ ^ N := by rw [← map_pow, ← hc, AlgEquiv.commutes]
  have h1 : (g θ / θ) ^ N = 1 := by
    rw [div_pow, hg, div_self (pow_ne_zero _ hθ)]
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_cast_of_lt hi, hi', div_mul_cancel₀ _ hθ]

theorem unique_pow {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    {a b : ZMod N} (h : ζ ^ a.val * θ = ζ ^ b.val * θ) : a = b := by
  have h' : ζ ^ a.val = ζ ^ b.val := mul_right_cancel₀ hθ h
  exact ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')

theorem kum_spec {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    g θ = ζ ^ (kum (N := N) ζ θ g).val * θ := by
  have h := exists_pow hζ hθ hN g
  unfold kum
  rw [dite_eq_left h]
  exact h.choose_spec

theorem kum_eq {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) {i : ZMod N}
    (hi : g θ = ζ ^ i.val * θ) : kum (N := N) ζ θ g = i :=
  unique_pow hζ hθ ((kum_spec hζ hθ hN g).symm.trans hi)

theorem kum_mul {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ)
    (hθ : θ ≠ 0) (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g h : Ω ≃ₐ[K] Ω) :
    kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h := by
  apply kum_eq hζ hθ hN
  rw [AlgEquiv.mul_apply, kum_spec hζ hθ hN h, map_mul, map_pow, hfix, kum_spec hζ hθ hN g,
    add_comm, pow_val_add hζ]
  ring

theorem kum_eq_zero_iff {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    kum (N := N) ζ θ g = 0 ↔ g θ = θ := by
  constructor
  · intro h
    have := kum_spec hζ hθ hN g
    rwa [h, ZMod.val_zero, pow_zero, one_mul] at this
  · intro h
    apply kum_eq hζ hθ hN
    rw [h, ZMod.val_zero, pow_zero, one_mul]

theorem kummer_character [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω) (hN0 : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) (hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) :
    IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
    (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧
    (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) := by
  haveI : NeZero N := ⟨by omega⟩
  refine ⟨?_, kum_spec hζ hθ hN, kum_mul hζ hfix hθ hN, kum_eq_zero_iff hζ hθ hN⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  haveI : FiniteDimensional K K⟮θ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral θ)
  have hopen : IsOpen ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro g' hg'
    have hfθ : (g⁻¹ * g') θ = θ := by
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' θ
        (IntermediateField.mem_adjoin_simple_self K θ)
      exact this
    have h0 := (kum_eq_zero_iff hζ hθ hN _).2 hfθ
    have : g' = g * (g⁻¹ * g') := by group
    rw [this, kum_mul hζ hfix hθ hN, h0, add_zero]

end GlobalTheory.NeedB.KumLemma


open GlobalTheory.NeedB in
theorem GlobalTheory.NeedB.KumLemma.kummer_character_main : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → θ ≠ 0 → θ ^ N ∈ Set.range (algebraMap K Ω) →
  IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
  (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧ (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) :=
  fun K Ω _ _ _ _ N ζ θ h0 hζ hf hθ hN => GlobalTheory.NeedB.KumLemma.kummer_character N ζ θ h0 hζ hf hθ hN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSq
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem kummer_aeval_mem_integralClosure {A₀ F E : Type} [CommRing A₀] [Field F] [Field E] [Algebra A₀ F]
    [Algebra F E] [Algebra A₀ E] [IsScalarTower A₀ F E] {x : E} (hx : IsIntegral A₀ x)
    (p : (integralClosure A₀ F)[X]) : IsIntegral A₀ (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
  | monomial n c =>
    rw [aeval_monomial]
    refine IsIntegral.mul ?_ (hx.pow n)
    have : algebraMap (integralClosure A₀ F) E c = algebraMap F E (c : F) := rfl
    rw [this]
    exact c.2.map (IsScalarTower.toAlgHom A₀ F E)

theorem kummer_dual_step (A₀ K₀ F E : Type) [CommRing A₀] [IsDomain A₀] [Field K₀] [Algebra A₀ K₀]
    [IsFractionRing A₀ K₀] [Field F] [Field E] [Algebra K₀ F] [Algebra F E] [Algebra K₀ E]
    [IsScalarTower K₀ F E] [Algebra A₀ F] [Algebra A₀ E] [IsScalarTower A₀ K₀ F] [IsScalarTower A₀ K₀ E]
    [IsScalarTower A₀ F E] [FiniteDimensional K₀ F] [FiniteDimensional F E] [CharZero K₀]
    (N : ℕ) (hN : IsUnit (N : A₀)) (x : E) (u : A₀ˣ) (hx : x ^ N = algebraMap A₀ E u)
    (hgen : Algebra.adjoin F {x} = ⊤)
    (hF : ∀ y : F, (∀ z : F, IsIntegral A₀ z → Algebra.trace K₀ F (y * z) ∈ (algebraMap A₀ K₀).range) →
      IsIntegral A₀ y) :
    ∀ y : E, (∀ z : E, IsIntegral A₀ z → Algebra.trace K₀ E (y * z) ∈ (algebraMap A₀ K₀).range) →
      IsIntegral A₀ y := by
  intro y hy
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K₀ F).injective
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : Algebra.IsSeparable F E := inferInstance
  let C := integralClosure A₀ F
  haveI : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension A₀ K₀ F C
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K₀
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hxA : IsIntegral A₀ x := by
    refine ⟨X ^ N - Polynomial.C (u : A₀), monic_X_pow_sub_C _ hN0, ?_⟩
    simp [eval₂_sub, hx]
  have hxC : IsIntegral C x := hxA.tower_top
  have key := traceForm_dualSubmodule_adjoin C F hgen hxC

  have hymem : y ∈ (Algebra.traceForm F E).dualSubmodule (Subalgebra.toSubmodule (Algebra.adjoin C {x})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro z hz
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    have hzA : IsIntegral A₀ (aeval x p) := kummer_aeval_mem_integralClosure hxA p
    rw [Algebra.traceForm_apply]
    have hw : IsIntegral A₀ (Algebra.trace F E (y * aeval x p)) := by
      apply hF
      intro c hc
      have : Algebra.trace F E (y * aeval x p) * c =
          Algebra.trace F E (y * (aeval x p * algebraMap F E c)) := by
        rw [mul_comm _ c, ← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def]
        ring_nf
      rw [this, Algebra.trace_trace]
      exact hy _ (hzA.mul (hc.map (IsScalarTower.toAlgHom A₀ F E)))
    exact Submodule.mem_one.mpr ⟨⟨_, hw⟩, rfl⟩
  rw [key, Submodule.mem_smul_pointwise_iff_exists] at hymem
  obtain ⟨z, hz, rfl⟩ := hymem
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨q, rfl⟩ := hz
  have hmin : minpoly F x = map (algebraMap C F) (minpoly C x) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' F hxC
  have hdvd : minpoly C x ∣ X ^ N - Polynomial.C (algebraMap A₀ C u) := by
    apply minpoly.isIntegrallyClosed_dvd hxC
    simp [hx, ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, hg⟩ := hdvd
  have hder := congrArg (fun p => aeval x (derivative p)) hg
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, derivative_mul, map_add (f := _), map_mul,
    minpoly.aeval, zero_mul, add_zero] at hder
  set d := aeval x (derivative (minpoly C x))
  let v : A₀ˣ := hN.unit * u
  have hinv : (aeval x (derivative (minpoly F x)))⁻¹ = aeval x g * x * algebraMap A₀ E (↑v⁻¹ : A₀) := by
    rw [hmin, derivative_map, aeval_map_algebraMap]
    apply inv_eq_of_mul_eq_one_right
    change d * _ = 1
    have h1 : d * aeval x g = (N : E) * x ^ (N - 1) := by rw [← hder]; simp
    have hv : ((v : A₀)) = (N : A₀) * u := by simp [v]
    calc d * (aeval x g * x * algebraMap A₀ E ↑v⁻¹)
        = (N : E) * (x ^ (N - 1) * x) * algebraMap A₀ E ↑v⁻¹ := by
          rw [← mul_assoc, ← mul_assoc, h1]; ring
      _ = algebraMap A₀ E ((v : A₀) * ↑v⁻¹) := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0), hx, map_mul, hv, map_mul,
          map_natCast]
      _ = 1 := by simp
  rw [smul_eq_mul, hinv]
  refine IsIntegral.mul (IsIntegral.mul (kummer_aeval_mem_integralClosure hxA g) hxA) isIntegral_algebraMap
    |>.mul (kummer_aeval_mem_integralClosure hxA q)

end GlobalTheory

namespace GlobalTheory

theorem kummer_dual_induction (A₀ K₀ : Type) [CommRing A₀] [IsDomain A₀] [Field K₀] [Algebra A₀ K₀]
    [IsFractionRing A₀ K₀] [CharZero K₀] (N : ℕ) (hN : IsUnit (N : A₀)) :
    ∀ (n : ℕ) (E : Type) [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E]
      [IsScalarTower A₀ K₀ E] (s : Finset E), s.card = n → IntermediateField.adjoin K₀ (s : Set E) = ⊤ →
      (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
      ∀ y : E, (∀ z : E, IsIntegral A₀ z → Algebra.trace K₀ E (y * z) ∈ (algebraMap A₀ K₀).range) →
        IsIntegral A₀ y := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ _ _ s hs hadj _ y hy
    rw [Finset.card_eq_zero] at hs
    subst hs
    rw [Finset.coe_empty, IntermediateField.adjoin_empty] at hadj
    have hr : Module.finrank K₀ E = 1 := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hadj
    have hyb : y ∈ (⊥ : IntermediateField K₀ E) := hadj ▸ IntermediateField.mem_top
    obtain ⟨k, rfl⟩ := IntermediateField.mem_bot.mp hyb
    obtain ⟨a, ha⟩ := hy 1 isIntegral_one
    rw [mul_one, Algebra.trace_algebraMap, hr, one_smul] at ha
    rw [← ha, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  | succ n ih =>
    intro E _ _ _ _ _ s hs hadj hu y hy
    classical
    obtain ⟨x, hxs⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    let t := s.erase x
    let F := IntermediateField.adjoin K₀ (t : Set E)
    let s' : Finset F := t.subtype (· ∈ F)
    have hs' : s'.card = n := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem (s := t) (p := (· ∈ F))
        (fun y hy => IntermediateField.subset_adjoin K₀ (t : Set E) hy),
        Finset.card_erase_of_mem hxs, hs]
      rfl
    have hadj' : IntermediateField.adjoin K₀ (s' : Set F) = ⊤ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
      change _ = IntermediateField.adjoin K₀ (t : Set E)
      congr 1
      ext w
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact Finset.mem_subtype.mp hw
      · intro hw
        exact ⟨⟨w, IntermediateField.subset_adjoin K₀ _ hw⟩, Finset.mem_subtype.mpr hw, rfl⟩
    have hu' : ∀ y ∈ s', ∃ u : A₀ˣ, y ^ N = algebraMap A₀ F u := by
      intro y hy
      obtain ⟨u, hu⟩ := hu y (Finset.mem_of_mem_erase (Finset.mem_subtype.mp hy))
      exact ⟨u, Subtype.ext hu⟩
    have hF := ih F s' hs' hadj' hu'
    obtain ⟨u, hux⟩ := hu x hxs
    have hgen : Algebra.adjoin F {x} = ⊤ := by
      have h1 : IntermediateField.adjoin F ({x} : Set E) = ⊤ := by
        apply IntermediateField.restrictScalars_injective K₀
        rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top, ← hadj]
        congr 1
        rw [Set.union_singleton, ← Finset.coe_insert, Finset.insert_erase hxs]
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun z _ => Algebra.IsAlgebraic.isAlgebraic z), h1]
      rfl
    haveI : IsScalarTower A₀ F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact kummer_dual_step A₀ K₀ F E N hN x u hux hgen hF y hy

end GlobalTheory

namespace GlobalTheory

theorem kummer_not_map_comap_le_sq :
    ∀ (A₀ K₀ E : Type) [CommRing A₀] [IsDedekindDomain A₀] [Field K₀] [CharZero K₀] [Algebra A₀ K₀]
      [IsFractionRing A₀ K₀] [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E]
      [IsScalarTower A₀ K₀ E] (N : ℕ), IsUnit (N : A₀) →
      ∀ s : Finset E, IntermediateField.adjoin K₀ (s : Set E) = ⊤ →
      (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
      ∀ P : Ideal (integralClosure A₀ E), P.IsPrime → P ≠ ⊥ →
        ¬ Ideal.map (algebraMap A₀ (integralClosure A₀ E))
          (P.comap (algebraMap A₀ (integralClosure A₀ E))) ≤ P ^ 2 := by
  intro A₀ K₀ E _ _ _ _ _ _ _ _ _ _ _ N hN s hadj hu P hP hP0 hle
  have hdual := kummer_dual_induction A₀ K₀ N hN _ E s rfl hadj hu
  haveI : IsFractionRing (integralClosure A₀ E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A₀ K₀ E _
  haveI : IsDedekindDomain (integralClosure A₀ E) := integralClosure.isDedekindDomain A₀ K₀ E
  haveI : Module.Finite A₀ (integralClosure A₀ E) := IsIntegralClosure.finite A₀ K₀ E _
  have hinj : Function.Injective (algebraMap A₀ E) := by
    rw [IsScalarTower.algebraMap_eq A₀ K₀ E]
    exact (algebraMap K₀ E).injective.comp (IsFractionRing.injective A₀ K₀)
  haveI : FaithfulSMul A₀ (integralClosure A₀ E) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  haveI : Module.IsTorsionFree A₀ (integralClosure A₀ E) := inferInstance
  have hone : Submodule.traceDual A₀ K₀ (1 : Submodule (integralClosure A₀ E) E) = 1 := by
    refine le_antisymm ?_ Submodule.one_le_traceDual_one
    intro y hy
    rw [Submodule.mem_traceDual] at hy
    refine Submodule.mem_one.mpr ⟨⟨y, hdual y fun z hz => ?_⟩, rfl⟩
    exact hy z (Submodule.mem_one.mpr ⟨⟨z, hz⟩, rfl⟩)
  have hdiff : differentIdeal A₀ (integralClosure A₀ E) = 1 := by
    rw [← FractionalIdeal.coeIdeal_eq_one (K := E), coeIdeal_differentIdeal A₀ K₀ E]
    have : FractionalIdeal.dual A₀ K₀
        (1 : FractionalIdeal (nonZeroDivisors (integralClosure A₀ E)) E) = 1 := by
      apply FractionalIdeal.coeToSubmodule_injective
      simp only [FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one, hone]
    rw [this, inv_one]
  obtain ⟨b, hbP, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hp0 : P.comap (algebraMap A₀ (integralClosure A₀ E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hb0 hbP (Algebra.IsIntegral.isIntegral b)
  haveI : (P.comap (algebraMap A₀ (integralClosure A₀ E))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hp0
  have h := pow_sub_one_dvd_differentIdeal_aux A₀ K₀ E
    (p := P.comap (algebraMap A₀ (integralClosure A₀ E))) P (e := 2) hp0
    (Ideal.dvd_iff_le.mpr hle)
  rw [hdiff, Ideal.dvd_iff_le] at h
  apply hP.ne_top
  simpa using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorOfChar
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem zeta_pow_val_add {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω} (hζN : ζ ^ N = 1) (x y : ZMod N) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (x.val + y.val) N, pow_add, pow_mul, hζN, one_pow, one_mul]

theorem kummer_generator_of_char : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (E : IntermediateField K Ω) (χ : (Ω ≃ₐ[K] Ω) → ZMod N),
  IsLocallyConstant χ → (∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, χ (g * h) = χ g + χ h) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ E ∧ ∀ g ∈ E.fixingSubgroup, g θ = ζ ^ (χ g).val * θ := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix E χ hχ hadd
  haveI : NeZero N := ⟨hN.ne'⟩
  classical
  set H := E.fixingSubgroup with hH
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  have h1 : χ 1 = 0 := by
    have := hadd 1 H.one_mem 1 H.one_mem
    simpa using this

  have hV : {g : Ω ≃ₐ[K] Ω | χ g = 0} ∈ nhds (1 : Ω ≃ₐ[K] Ω) := by
    have := (hχ.isOpen_fiber (χ 1)).mem_nhds (show (1 : Ω ≃ₐ[K] Ω) ∈ χ ⁻¹' {χ 1} from rfl)
    simpa [h1] using this
  obtain ⟨F, hFfin, hFV⟩ := (krullTopology_mem_nhds_one_iff K Ω _).mp hV

  let r : (Ω ≃ₐ[K] Ω) → (F →ₐ[K] Ω) := fun g => (g : Ω →ₐ[K] Ω).comp F.val
  have hr : ∀ g x, r g x = g (x : Ω) := fun _ _ => rfl
  have hrχ : ∀ g ∈ H, ∀ h ∈ H, r g = r h → χ g = χ h := by
    intro g hg h hh he
    have hm : h⁻¹ * g ∈ H := H.mul_mem (H.inv_mem hh) hg
    have hF : h⁻¹ * g ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have := congrArg (fun φ => φ ⟨x, hx⟩) he
      simp only [hr] at this
      simp [AlgEquiv.mul_apply, this]
    have h0 : χ (h⁻¹ * g) = 0 := hFV hF
    have := hadd h hh (h⁻¹ * g) hm
    rw [mul_inv_cancel_left, h0, add_zero] at this
    exact this
  haveI : FiniteDimensional K F := hFfin
  let ι := {φ : F →ₐ[K] Ω // ∃ g ∈ H, r g = φ}
  haveI : Finite (F →ₐ[K] Ω) := inferInstance
  haveI : Fintype ι := Fintype.ofFinite ι
  let s : ι → (Ω ≃ₐ[K] Ω) := fun i => i.2.choose
  have hsH : ∀ i, s i ∈ H := fun i => i.2.choose_spec.1
  have hsr : ∀ i, r (s i) = i.1 := fun i => i.2.choose_spec.2
  let a : (Ω ≃ₐ[K] Ω) → Ω := fun g => ζ ^ (χ g).val
  have ha0 : ∀ g, a g ≠ 0 := fun g => pow_ne_zero _ hζ0
  have hamul : ∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g * a h := by
    intro g hg h hh
    simp only [a, hadd g hg h hh, zeta_pow_val_add hζN]
  have hafix : ∀ (g h : Ω ≃ₐ[K] Ω), g (a h) = a h := by
    intro g h; simp only [a, map_pow, hfix]
  let w : ι → Ω := fun i => (a (s i))⁻¹

  let v : ι → (F →* Ω) := fun i => (i.1 : F →+* Ω).toMonoidHom
  have hv : Function.Injective v := by
    intro i j hij
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom F Ω).comp v hv
  obtain ⟨c, hc⟩ : ∃ c : F, ∑ i, w i * i.1 c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : ∑ i, w i • ((v i : F →* Ω) : F → Ω) = 0 := by
      funext x
      simpa [Finset.sum_apply, v] using hcon x
    have := Fintype.linearIndependent_iff.mp hli w hz ⟨r 1, 1, H.one_mem, rfl⟩
    exact inv_ne_zero (ha0 _) this
  have hmain : ∀ g ∈ H, g (∑ i, w i * i.1 c) = a g * ∑ i, w i * i.1 c := by
    intro g hg
    let e : ι → ι := fun i => ⟨r (g * s i), g * s i, H.mul_mem hg (hsH i), rfl⟩
    have hic : ∀ i : ι, i.1 c = s i (c : Ω) := by
      intro i; rw [← hsr i]; exact hr _ _
    have hec : ∀ i, (e i).1 c = g (i.1 c) := by
      intro i; rw [hic i]; rfl
    have hwe : ∀ i, w i = a g * w (e i) := by
      intro i
      have hχe : χ (s (e i)) = χ (g * s i) :=
        hrχ _ (hsH (e i)) _ (H.mul_mem hg (hsH i)) (hsr (e i))
      have : a (s (e i)) = a g * a (s i) := by
        rw [← hamul g hg (s i) (hsH i)]; simp only [a, hχe]
      simp only [w, this, mul_inv, ← mul_assoc, mul_inv_cancel₀ (ha0 g), one_mul]
    have he : Function.Injective e := by
      intro i j hij
      have h2 : r (g * s i) = r (g * s j) := congrArg Subtype.val hij
      apply Subtype.ext
      rw [← hsr i, ← hsr j]
      apply AlgHom.ext
      intro x
      have := DFunLike.congr_fun h2 x
      simp only [hr, AlgEquiv.mul_apply] at this
      simpa [hr] using g.injective this
    have hb : Function.Bijective e := Finite.injective_iff_bijective.mp he
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    simp only [map_mul, hfix, w, map_inv₀, hafix]
    refine (Fintype.sum_bijective e hb _ _ ?_)
    intro i
    have h3 := hwe i
    simp only [w] at h3
    rw [h3, ← hec i]; ring
  refine ⟨∑ i, w i * i.1 c, hc, ?_, ?_⟩
  · haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro g hg
    have key := hmain g hg
    rw [map_pow, key, mul_pow]
    have : a g ^ N = 1 := by
      show (ζ ^ (χ g).val) ^ N = 1
      rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow]
    rw [this, one_mul]
  · exact hmain

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelOneTwelveMulFinrankModularFormLowerBound
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem levelOne_twelve_mul_finrank_lower_bound :
    ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) +
      4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤
        12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  intro n hn
  rcases lt_or_ge n 0 with hneg | hpos
  · have h0 : (0 : ℤ) ≤ (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := Int.natCast_nonneg _
    obtain ⟨m, hm⟩ := hn
    generalize (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) = d at h0 ⊢
    split_ifs <;> omega
  · lift n to ℕ using hpos
    have hke : Even n := by exact_mod_cast hn
    have hrank := ModularForm.dimension_level_one n hke
    have hfin : Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) =
        if n % 12 = 2 then n / 12 else n / 12 + 1 := by
      exact Module.finrank_eq_of_rank_eq hrank
    obtain ⟨m, hm⟩ := hke
    generalize Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) = d at hfin ⊢
    split_ifs at hfin ⊢ <;> omega

end GlobalTheory.OddFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationMapAlgEquivEqOfLeOneIffIsIntegralStatement
section
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) → ∀ (g : Ω ≃ₐ[R] Ω) (x : Ω), v (g x) = v x := by
  first | exact @GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral | exact GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral | (intros; apply GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral <;> assumption)
end

