module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefPosEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorPowerSeriesCoeffAutMapComm
section
open GlobalTheory.Col PowerSeries

noncomputable section

namespace GlobalTheory.Col.NormCoeff

variable {R : Type} [CommRing R]

def smapEquiv (σ : R ≃+* R) : PowerSeries R ≃+* PowerSeries R :=
  RingEquiv.ofRingHom (smap σ) (smap σ.symm)
    (by ext h n; simp [PowerSeries.coeff_map])
    (by ext h n; simp [PowerSeries.coeff_map])

theorem smapEquiv_apply (σ : R ≃+* R) (h : PowerSeries R) : smapEquiv σ h = smap σ h := rfl

theorem map_phi (p : ℕ) (hp : 0 < p) (f : R →+* R) (h : PowerSeries R) :
    PowerSeries.map f (phi (R := R) p hp h) = phi (R := R) p hp (PowerSeries.map f h) := by
  unfold phi
  rw [PowerSeries.coe_substAlgHom]
  have key := PowerSeries.map_subst (hasSubst_om (R := R) p hp) (h := f) h
  have e : (MvPowerSeries.map f) (((1 + PowerSeries.X : PowerSeries R) ^ p) - 1)
      = ((1 + PowerSeries.X : PowerSeries R) ^ p) - 1 := by
    change PowerSeries.map f _ = _
    simp
  rw [e] at key
  exact key

theorem normOp_smap (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R) :
    normOp p (smap σ h) = smap σ (normOp p h) := by
  have key := @Algebra.norm_eq_of_equiv_equiv (PowerSeries R) (PowerSeries R) (PowerSeries R) (PowerSeries R)
    _ _ _ _ (phi (R := R) p hp.out.pos).toRingHom.toAlgebra (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
    (smapEquiv σ) (smapEquiv σ) (by
      ext1 x
      exact (map_phi p hp.out.pos (σ : R →+* R) x).symm) h
  have key2 : normOp p h = (smapEquiv σ).symm (normOp p (smap σ h)) := key
  rw [key2, ← smapEquiv_apply, ← smapEquiv_apply, RingEquiv.apply_symm_apply]

end GlobalTheory.Col.NormCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
section
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem dvr_of_separated {S : Type*} [CommRing S] (π : S) (hn : ∀ n : ℕ, π ^ n ≠ 0)
    (hnu : ¬ IsUnit π) (hu : ∀ x, ¬ π ∣ x → IsUnit x) (hsep : ∀ x, (∀ n : ℕ, π ^ n ∣ x) → x = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  classical
  have hfac : ∀ x : S, x ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra h
      push Not at h
      exact hx (hsep x fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (h n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · have := Nat.find_min hex (m := m) (by omega)
        simpa using this
    obtain ⟨u, hxu⟩ := h1
    refine ⟨Nat.find hex, u, hu u ?_, hxu⟩
    rintro ⟨v, hv⟩
    exact Nat.find_spec hex ⟨v, by rw [pow_succ, mul_assoc, ← hv]; exact hxu⟩
  have : Nontrivial S := ⟨⟨π ^ 0, 0, hn 0⟩⟩
  have : NoZeroDivisors S := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨a, u, hu', rfl⟩ := hfac x h.1
    obtain ⟨b, v, hv', rfl⟩ := hfac y h.2
    apply hn (a + b)
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy]; ring
    exact ((hu'.mul hv').mul_left_eq_zero).1 this⟩
  have hd : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := by simpa using hn 1
  have hprime : Prime π := by
    refine ⟨hπ0, hnu, fun a b hab => ?_⟩
    by_contra h
    push Not at h
    exact hnu (isUnit_of_dvd_unit hab ((hu a h.1).mul (hu b h.2)))
  refine ⟨hd, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, hprime.irreducible, fun {x} hx => ?_⟩, hprime.irreducible⟩
  obtain ⟨n, u, hu', rfl⟩ := hfac x hx
  exact ⟨n, hu'.unit, rfl⟩

theorem adicCompletion_dvr {R : Type*} [CommRing R] [IsDomain R] (a : R) (ha : a ≠ 0)
    (hmax : (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a}).IsMaximal) :
    ∃ _ : IsDomain (AdicCompletion (Ideal.span {a}) R),
      IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R) ∧
        Irreducible (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := by
  have fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton _
  have hc := AdicCompletion.isAdicComplete_self (Ideal.span {a}) fg
  rw [Ideal.map_span, Set.image_singleton] at hc
  have hnu : ¬ IsUnit (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := fun h =>
    hmax.ne_top (Ideal.span_singleton_eq_top.2 h)
  have := isLocalRing_of_isAdicComplete_maximal
    (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
  refine dvr_of_separated _ (fun n hn => ?_) hnu (fun x hx => ?_) (fun x hx => ?_)
  · rw [← map_pow] at hn
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (n + 1)) hn
    rw [AlgHom.commutes, map_zero, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ] at h2
    have h3 : a ^ n * a ∣ a ^ n * 1 := by simpa using h2
    exact hnu ((isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n ha)).1 h3)).map _)
  · by_contra hxu
    have : x ∈ IsLocalRing.maximalIdeal _ := hxu
    rw [← IsLocalRing.eq_maximalIdeal hmax, Ideal.mem_span_singleton] at this
    exact hx this
  · refine hc.toIsHausdorff.haus' x fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx n

theorem completed_laurent_isDVR (p : ℕ) [Fact p.Prime] :
    ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  have hp : (p : Lau p) ≠ 0 := by
    have h : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [← map_natCast (HahnSeries.C : ℤ_[p] →+* Lau p)]
    exact HahnSeries.C_ne_zero h
  obtain ⟨e⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))
  have := adicCompletion_dvr (p : Lau p) hp (by rw [map_natCast]; exact hmax)
  rw [map_natCast] at this
  exact this

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormEqZeroOfPeriodicOfBound
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerPositivity

theorem periodic_of_dbar : ∀ (U : ℂ → ℂ) (h : ℍ → ℂ) (w : ℕ) (T : ℝ), (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt U L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))) → (∀ s : ℂ, 0 < s.im → U (s + T) = U s) → ∀ s : ℂ, 0 < s.im → h (ofComplex (s + T)) = h (ofComplex s) := by
  intro U h w T hd hp s hs
  have hsT : 0 < (s + T).im := by simpa using hs
  obtain ⟨L0, hL0, e0⟩ := hd s hs
  obtain ⟨L1, hL1, e1⟩ := hd (s + T) hsT
  have hshift : HasFDerivAt (fun z : ℂ => U (z + T)) L1 s := by
    have := hL1.comp s ((hasFDerivAt_id (𝕜 := ℝ) s).add_const (T : ℂ))
    simpa [Function.comp_def] using this
  have hev : U =ᶠ[nhds s] fun z : ℂ => U (z + T) :=
    ((Complex.continuous_im.tendsto s).eventually (lt_mem_nhds hs)).mono fun z hz => (hp z hz).symm
  have hL : L0 = L1 := hL0.unique (hshift.congr_of_eventuallyEq hev)
  have hconj : (s + T) - (starRingEnd ℂ) (s + T) = s - (starRingEnd ℂ) s := by
    simp only [map_add (f := _), Complex.conj_ofReal]; ring
  have hne : 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w ≠ 0 := by
    have : s - (starRingEnd ℂ) s ≠ 0 := by
      rw [Complex.sub_conj]
      exact mul_ne_zero (by exact_mod_cast (by positivity : (2 * s.im) ≠ 0)) Complex.I_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (pow_ne_zero _ this)
  have key := e1
  rw [hconj, ← hL, e0] at key
  exact ((starRingEnd ℂ).injective (mul_left_cancel₀ hne key)).symm

theorem fourier_sub_eq : ∀ (U : ℂ → ℂ) (h : ℍ → ℂ) (w : ℕ) (T : ℝ) (n : ℕ) (a b : ℝ), 0 < T → 0 < a → a ≤ b → (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt U L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))) → (∀ s : ℂ, 0 < s.im → U (s + T) = U s) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → Function.Periodic (h ∘ ofComplex) T → IsBoundedAtImInfty h → (∫ x in (0 : ℝ)..T, U ((x : ℂ) + (b : ℂ) * Complex.I) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (b : ℂ) * Complex.I) / T)) - (∫ x in (0 : ℝ)..T, U ((x : ℂ) + (a : ℂ) * Complex.I) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (a : ℂ) * Complex.I) / T)) = 2 * Complex.I * (2 * Complex.I) ^ w * T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  intro U h w T n a b hT ha hab hd hp hh hper hbdd
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  refine (_root_.GlobalTheory.green_periodic_rectangle (fun z => U z * Complex.exp (2 * Real.pi * Complex.I * n * z / T))
    (fun s => Complex.exp (2 * Real.pi * Complex.I * n * s / T) *
      (2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))))
    T a b hT ha hab ?_ ?_ ?_).trans ?_
  · intro s hs
    obtain ⟨L, hL, e⟩ := hd s hs
    have h1 : HasDerivAt (fun z : ℂ => 2 * Real.pi * Complex.I * n * z / T)
        (2 * Real.pi * Complex.I * n / T) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * Real.pi * Complex.I * n : ℂ)).div_const (T : ℂ)
    refine ⟨_, hL.mul (h1.cexp.hasFDerivAt.restrictScalars ℝ), ?_⟩
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    linear_combination (Complex.exp (2 * Real.pi * Complex.I * n * s / T)) * e
  · have hc : ContinuousOn (h ∘ ofComplex) {s : ℂ | 0 < s.im} :=
      (UpperHalfPlane.mdifferentiable_iff.1 hh).continuousOn
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) (ContinuousOn.mul
      (Continuous.continuousOn ?_) (Complex.continuous_conj.comp_continuousOn hc))
    exact continuous_const.mul ((continuous_id.sub Complex.continuous_conj).pow w)
  · intro s hs
    show U (s + T) * Complex.exp _ = U s * Complex.exp _
    rw [hp s hs]
    congr 1
    rw [show 2 * (Real.pi : ℂ) * Complex.I * n * (s + T) / T =
        2 * Real.pi * Complex.I * n * s / T + n * (2 * Real.pi * Complex.I) by field_simp,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · have inner : ∀ y ∈ Set.uIcc a b,
        (∫ x in (0 : ℝ)..T, Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) *
          (2 * Complex.I * (((x : ℂ) + (y : ℂ) * Complex.I) - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I)) ^ w *
            (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))))) =
        2 * Complex.I * (2 * Complex.I) ^ w * T * (starRingEnd ℂ) ((qExpansion T h).coeff n) *
          ((y : ℂ) ^ w * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ)) := by
      intro y hy
      have hy0 : 0 < y := by
        rw [Set.uIcc_of_le hab] at hy
        exact lt_of_lt_of_le ha hy.1
      have hpt : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I) - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I) =
          2 * Complex.I * y := by
        intro x
        rw [Complex.sub_conj]
        simp
        ring
      simp_rw [hpt]
      have hfun : (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) *
          (2 * Complex.I * (2 * Complex.I * (y : ℂ)) ^ w *
            (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))))) =
          fun x : ℝ => (2 * Complex.I * (2 * Complex.I) ^ w * (y : ℂ) ^ w) *
            ((starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) *
              Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) := by
        funext x
        rw [mul_pow]
        ring
      rw [hfun, intervalIntegral.integral_const_mul, GlobalTheory.T.integral_conj_mul_exp_eq_conj_qExpansion_coeff h T n y hT hy0 hh hper hbdd]
      ring
    rw [intervalIntegral.integral_congr inner, intervalIntegral.integral_const_mul]

theorem cuspForm_eq_zero_of_periodic_of_bound : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)) (p : ℂ[X]) (h₀ : ℕ) (C : ℝ), 0 < h₀ → (∀ τ : ℍ, (eichler (k - 2) ⇑f ((h₀ : ℝ) +ᵥ τ) - (eichler (k - 2) ⇑h ((h₀ : ℝ) +ᵥ τ)).map (starRingEnd ℂ) - p).eval (((h₀ : ℝ) +ᵥ τ : ℍ) : ℂ) = (eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p).eval (τ : ℂ)) → (∀ τ : ℍ, ‖(eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p).eval (τ : ℂ)‖ ≤ C * τ.im ^ (((k : ℝ) - 2) / 2)) → h = 0 := by
  intro Γ k hfi hk f h p h₀ C hh₀ hper hbd
  have := hfi
  have hT : (0 : ℝ) < (h₀ : ℝ) := by exact_mod_cast hh₀
  have hcoe : ∀ z : ℂ, 0 < z.im → ((ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [ofComplex_apply_of_im_pos hz]
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑h) := ModularFormClass.holo h
  have hd := _root_.GlobalTheory.EichlerDbar.wirtinger_eichler (k - 2) ⇑f ⇑h p (ModularFormClass.holo f) hholo
  have hUper : ∀ s : ℂ, 0 < s.im →
      (eichler (k - 2) ⇑f (ofComplex (s + ((h₀ : ℝ) : ℂ))) -
          (eichler (k - 2) ⇑h (ofComplex (s + ((h₀ : ℝ) : ℂ)))).map (starRingEnd ℂ) - p).eval
          (s + ((h₀ : ℝ) : ℂ)) =
        (eichler (k - 2) ⇑f (ofComplex s) - (eichler (k - 2) ⇑h (ofComplex s)).map (starRingEnd ℂ) - p).eval s := by
    intro s hs
    have hs' : 0 < (s + ((h₀ : ℝ) : ℂ)).im := by simpa using hs
    have e : ofComplex (s + ((h₀ : ℝ) : ℂ)) = ((h₀ : ℝ) +ᵥ ofComplex s) := by
      ext
      rw [UpperHalfPlane.coe_vadd, hcoe _ hs', hcoe _ hs]
      ring
    have key := hper (ofComplex s)
    rw [← e, hcoe _ hs', hcoe _ hs] at key
    exact key
  have hhper := periodic_of_dbar _ ⇑h (k - 2) (h₀ : ℝ) hd hUper
  have hperh : Function.Periodic (⇑h ∘ ofComplex) ((h₀ : ℝ) : ℂ) := by
    intro s
    by_cases hs : 0 < s.im
    · exact hhper s hs
    · rw [not_lt] at hs
      simp only [Function.comp_apply]
      rw [ofComplex_apply_eq_of_im_nonpos (by simpa using hs) hs]
  have hbdd : IsBoundedAtImInfty (⇑h) := ModularFormClass.bdd_at_infty h
  have hzero : IsZeroAtImInfty (⇑h) := CuspFormClass.zero_at_infty h
  have hq : qExpansion (h₀ : ℝ) ⇑h = 0 := by
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    rcases n with _ | n
    · rw [qExpansion_coeff_zero hT (analyticAt_cuspFunction_zero hT hperh hholo hbdd) hperh,
        hzero.valueAtInfty_eq_zero]
    · have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hα : 0 < 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ) := by positivity
      have hβ : 0 < 4 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ) := by positivity
      have hK : 2 * Complex.I * (2 * Complex.I) ^ (k - 2) * ((h₀ : ℝ) : ℂ) ≠ 0 := by
        have : ((h₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
          (pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero))) this
      have hw1 : 1 ≤ k - 2 := by omega
      have hwR : (((k - 2 : ℕ) : ℝ)) = (k : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hbound : ∀ y : ℝ, 0 < y →
          ‖∫ x in (0 : ℝ)..(h₀ : ℝ),
              (eichler (k - 2) ⇑f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) -
                (eichler (k - 2) ⇑h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).map (starRingEnd ℂ) - p).eval
                ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) / ((h₀ : ℝ) : ℂ))‖ ≤
            (C * (h₀ : ℝ)) * y ^ ((((k - 2 : ℕ) : ℝ)) / 2) *
              Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y) := by
        intro y hy
        have hpt : ∀ x : ℝ,
            ‖(eichler (k - 2) ⇑f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) -
                (eichler (k - 2) ⇑h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).map (starRingEnd ℂ) - p).eval
                ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) / ((h₀ : ℝ) : ℂ))‖ ≤
            C * y ^ ((((k - 2 : ℕ) : ℝ)) / 2) * Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y) := by
          intro x
          have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
          have hb := hbd (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))
          rw [hcoe _ hz] at hb
          have him : (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
            rw [← UpperHalfPlane.coe_im, hcoe _ hz]
            simp
          rw [him, ← hwR] at hb
          rw [norm_mul, Complex.norm_exp]
          have hre : (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) /
              ((h₀ : ℝ) : ℂ)).re = -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y := by
            rw [Complex.div_ofReal_re]
            simp
            ring
          rw [hre]
          exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (h₀ : ℝ))
          (fun x _ => hpt x)
        rw [sub_zero, abs_of_pos hT] at this
        calc _ ≤ _ := this
          _ = _ := by ring
      have hc := _root_.GlobalTheory.ode_coeff_zero_of_decay_ends _ (2 * Complex.I * (2 * Complex.I) ^ (k - 2) * ((h₀ : ℝ) : ℂ))
        ((starRingEnd ℂ) ((qExpansion (h₀ : ℝ) ⇑h).coeff (n + 1)))
        (C * (h₀ : ℝ)) _ (4 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) (k - 2) hw1 hα hβ hK hbound
        (fun a b ha hab => fourier_sub_eq _ ⇑h (k - 2) (h₀ : ℝ) (n + 1) a b hT ha hab hd hUper
          hholo hperh hbdd)
      simpa using hc
  have hfun : (⇑h : ℍ → ℂ) = 0 := (qExpansion_eq_zero_iff hT hperh hholo hbdd).1 hq
  ext τ
  simpa using congrFun hfun τ

end GlobalTheory.EichlerPositivity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCompMul
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isDia_mul {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : IsDia N l d σ) (hτ : IsDia N l e τ) :
    IsDia N l (d * e) (σ * τ) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  obtain ⟨hτ0, hτ1⟩ := hτ
  have hσ0' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    have := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hσ0
    simpa using this
  constructor
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hσ0, hτ0]; ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hσ0', hσ1, hτ1]; ring

theorem dia_mul : ∀ (N l : ℕ) (k d e : ℤ) (σ τ ρ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    GlobalTheory.Hk.IsDia N l e τ → GlobalTheory.Hk.IsDia N l (d * e) ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.dia k τ (GlobalTheory.Hk.dia k σ ⇑f) = GlobalTheory.Hk.dia k ρ ⇑f := by
  intro N l k d e σ τ ρ hN hσ hτ hρ f
  have h := _root_.GlobalTheory.Hk.dia_congr N l k (d * e) (σ * τ) ρ hN (isDia_mul hσ hτ) hρ f
  rw [← h]
  simp only [dia]
  rw [SlashAction.slash_mul]

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DropConst
section
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem ffMu_eq (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a₀ : ℤ) (s : ℕ) :
    ffMu N p m k ψ a₀ s = ∑ q ∈ (s : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 ∧ q.1 ≡ a₀ [ZMOD N] then
        (q.2.sign : K) * (ψ (q.1 : ZMod (p ^ m)) * (q.1 : K) ^ (k - 2)) else 0 := by
  rw [sum_antidiag s (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d ∧ A ≡ a₀ [ZMOD N] then
        (d.sign : K) * (ψ (A : ZMod (p ^ m)) * (A : K) ^ (k - 2)) else 0)]
  unfold ffMu
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ s / d <;>
    by_cases h3 : ((s / d : ℕ) : ℤ) ≡ a₀ [ZMOD N] <;> by_cases h4 : -((s / d : ℕ) : ℤ) ≡ a₀ [ZMOD N] <;>
    simp [h1, h2, h3, h4, sub_eq_add_neg, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

theorem eeMu_eq (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (b₀ : ℤ) (s : ℕ) :
    eeMu N p m ψ b₀ s = ∑ q ∈ (s : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 ∧ q.1 ≡ b₀ [ZMOD N] then
        (q.2.sign : K) * ψ⁻¹ (q.2 : ZMod (p ^ m)) else 0 := by
  rw [sum_antidiag s (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d ∧ A ≡ b₀ [ZMOD N] then
        (d.sign : K) * ψ⁻¹ (d : ZMod (p ^ m)) else 0)]
  unfold eeMu
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ s / d <;>
    by_cases h3 : ((s / d : ℕ) : ℤ) ≡ b₀ [ZMOD N] <;> by_cases h4 : -((s / d : ℕ) : ℤ) ≡ b₀ [ZMOD N] <;>
    simp [h1, h2, h3, h4, sub_eq_add_neg, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

theorem drop_const (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (x y y₁ y₂ : ℤ) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (eisF (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val + (p : ℤ) ^ m * y₁) i *
        eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val + (p : ℤ) ^ m * y₂) j) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val + (p : ℤ) ^ m * y₁) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val + (p : ℤ) ^ m * y₂) j) := by
  have hp : p.Prime := Fact.out
  by_cases hi : i = 0
  · subst hi
    have hk1 : k - 1 ≠ 1 := by omega
    simp only [eisF, const0, if_true, if_neg hk1]
    rw [sum_zero_left p m hm ψ hψ]
    simp [coefPos]
  by_cases hj : j = 0
  · subst hj
    have e : ∀ v ∈ primeTo p m, ∀ z : ℤ, eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) z 0 =
        ((1 / 2 - frc (N * p ^ m) (N * v.val + (p : ℤ) ^ m * y) : ℚ) : K) := by
      intro v hv z
      have : ¬ ((N * p ^ m : ℕ) : ℤ) ∣ N * v.val + (p : ℤ) ^ m * y := by
        intro h
        have h1 : (p : ℤ) ^ m ∣ N * v.val + (p : ℤ) ^ m * y :=
          (show (p : ℤ) ^ m ∣ ((N * p ^ m : ℕ) : ℤ) by push_cast; exact dvd_mul_left _ _).trans h
        have h2 : (p : ℤ) ∣ (N : ℤ) * v.val := by
          have := dvd_sub h1 (dvd_mul_right ((p : ℤ) ^ m) y)
          rw [add_sub_cancel_right] at this
          exact (dvd_pow_self (p : ℤ) (by omega)).trans this
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h2 with h3 | h3
        · exact hpN (Int.natCast_dvd_natCast.mp h3)
        · exact (mem_filter.mp hv).2 (Int.natCast_dvd_natCast.mp h3)
      simp only [eisF, const0, if_true, if_neg this]
    rw [sum_congr rfl fun u _ => sum_congr rfl fun a _ => sum_congr rfl fun v hv => sum_congr rfl fun b _ => by
      rw [e v hv], sum_zero_right p m hm ψ hψ]
    simp [coefPos]
  simp only [eisF, if_neg hi, if_neg hj]

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationModIntegralExtensionPCubeStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivationModIntegral_extension_p_cube : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt (p := p) (D b - (p : Ω) ^ 3 * d b) := by
  first | exact @GlobalTheory.DerExt.exists_ext | exact GlobalTheory.DerExt.exists_ext | (intros; apply GlobalTheory.DerExt.exists_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatibleStatement
section
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivationOn_iSup_of_compatible : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B : ℕ → Subalgebra A S), Monotone B → ∀ D : ℕ → S → M, (∀ m, IsDerOn (B m) (D m)) → (∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) → ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  first | exact @GlobalTheory.AlmostEt.isDerOn_iSup_glue | exact GlobalTheory.AlmostEt.isDerOn_iSup_glue | (intros; apply GlobalTheory.AlmostEt.isDerOn_iSup_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulMemSpanAlgebraicOverPadicIntegersStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_mem_span_algebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x}),
    ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x} := by
  first | exact @GlobalTheory.K5.ReprSpan.exists_mul_mem_span | exact GlobalTheory.K5.ReprSpan.exists_mul_mem_span | (intros; apply GlobalTheory.K5.ReprSpan.exists_mul_mem_span <;> assumption)
end

