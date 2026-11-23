module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuedMapEqOfContinuousCompletionIsoExtending
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompletionIsom


open WithZero in
theorem valuation_eq_of_lt_one_iff {K : Type} [Field K] (v v' : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ y, v y < 1 ↔ v' y < 1) (π : K) (hπ : v π = exp (-1)) (y₀ : K) (hy₀ : v' y₀ = exp (-1)) :
    ∀ y, v' y = v y := by
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hy0 : y₀ ≠ 0 := by rintro rfl; rw [map_zero] at hy₀; exact exp_ne_zero hy₀.symm
  have hexp : ∀ (w : Valuation K (WithZero (Multiplicative ℤ))) (x : K), x ≠ 0 → ∃ a : ℤ, w x = exp a :=
    fun w x hx => ⟨_, (exp_log ((Valuation.ne_zero_iff w).2 hx)).symm⟩
  have hker : ∀ z, v z = 1 → v' z = 1 := by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hz; exact zero_ne_one hz
    obtain ⟨a, ha⟩ := hexp v' z hz0
    rcases lt_trichotomy a 0 with h1 | h1 | h1
    · have := (h z).2 (by rw [ha, ← exp_zero, exp_lt_exp]; exact h1)
      rw [hz] at this; exact absurd this (lt_irrefl _)
    · rw [ha, h1, exp_zero]
    · have := (h z⁻¹).2 (by rw [map_inv₀, ha, ← exp_neg, ← exp_zero, exp_lt_exp]; omega)
      rw [map_inv₀, hz, inv_one] at this; exact absurd this (lt_irrefl _)
  obtain ⟨e, he⟩ := hexp v' π hπ0
  obtain ⟨b, hb⟩ := hexp v y₀ hy0
  have he1 : e < 0 := by
    have := (h π).1 (by rw [hπ, ← exp_zero, exp_lt_exp]; omega)
    rwa [he, ← exp_zero, exp_lt_exp] at this
  have hb1 : b < 0 := by
    have := (h y₀).2 (by rw [hy₀, ← exp_zero, exp_lt_exp]; omega)
    rwa [hb, ← exp_zero, exp_lt_exp] at this
  have he2 : -1 ≤ e := by
    by_contra hc
    have := (h (π * y₀⁻¹)).2 (by
      rw [map_mul, map_inv₀, he, hy₀, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp]; omega)
    rw [map_mul, map_inv₀, hπ, hb, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp] at this
    omega
  have hπ' : v' π = exp (-1) := by rw [he]; congr 1; omega
  intro y
  by_cases hy : y = 0
  · rw [hy, map_zero, map_zero]
  obtain ⟨a, ha⟩ := hexp v y hy
  have hz := hker (y * π ^ a) (by
    rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, ← exp_zero]; congr 1; simp)
  rw [map_mul, map_zpow₀, hπ', ← exp_zsmul] at hz
  rw [ha, eq_inv_of_mul_eq_one_left hz, ← exp_neg]
  congr 1; simp

theorem valued_v_map : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  intro E E' _ _ _ _ _ w w' i hi _ y
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  have hi' : Continuous i.symm := i.toEquiv.continuous_symm_iff.2 ho
  obtain ⟨π, hπ⟩ := w.valuedAdicCompletion_surjective E (WithZero.exp (-1))
  obtain ⟨ϖ, hϖ⟩ := w'.valuedAdicCompletion_surjective E' (WithZero.exp (-1))
  refine valuation_eq_of_lt_one_iff (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
    ((Valued.v : Valuation (w'.adicCompletion E') (WithZero (Multiplicative ℤ))).comap i.toRingHom)
    (fun x => ⟨fun hx => GlobalTheory.ConjParahoric.val_lt_one_map i.toRingHom hi hx, fun hx => ?_⟩) π hπ (i.symm ϖ) ?_ y
  · have := GlobalTheory.ConjParahoric.val_lt_one_map i.symm.toRingHom hi' hx
    simpa using this
  · simpa using hϖ

end GlobalTheory.CompletionIsom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightSectionEqZeroOfVanishingFiniteExtensions
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg


set_option synthInstance.maxHeartbeats 200000 in
theorem sec_eq_zero_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  intro E _ _ _ H Dw l Xo c a n h hh hv
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_nonempty_comp E H Dw l Xo c
  funext p y
  show h p y = 0

  have key : ∀ m : Ideal p.R, m.IsMaximal → h p y ∈ m := by
    intro m hm
    letI : Field (p.R ⧸ m) := Ideal.Quotient.field m
    haveI : Algebra.FiniteType c.F (p.R ⧸ m) := inferInstance
    haveI : FiniteDimensional c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ m)
    obtain ⟨w, hw⟩ := hL.bc p.R (p.R ⧸ m) (Ideal.Quotient.mkₐ c.F m) y
    have e := evR_eq_map_of_test_point hL hh p (Ideal.Quotient.mkₐ c.F m) y w hw
    rw [hv (p.R ⧸ m) w, Ideal.Quotient.mkₐ_eq_mk] at e
    exact Ideal.Quotient.eq_zero_iff_mem.mp e.symm

  have hj : h p y ∈ (⊥ : Ideal p.R).jacobson :=
    Ideal.mem_sInf.mpr fun J hJ => key J hJ.2
  have hrad : (⊥ : Ideal p.R).IsRadical := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact p.rad ⟨k, hk⟩
  rw [IsJacobsonRing.out (inferInstance : IsJacobsonRing p.R) hrad] at hj
  exact hj

end GlobalTheory.Reg
end

