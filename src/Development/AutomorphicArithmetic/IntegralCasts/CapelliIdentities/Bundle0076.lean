module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0037
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0038
public import Formalism.ConjugateSelfDual.Statement
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CdNormLt
section
theorem UpperTheory.Reformulated.B.Gs5b.cd_norm_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {R : Type} [inst_1 : CommRing R] [inst_2 : IsLocalRing R]
      [inst_3 : Algebra (↥c.O) R] (y : R →ₐ[↥c.O] PadicAlgCl l),
      ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → PadicAlgCl l) a‖ < (1 : ℝ) := by
  intro l _ c R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one y a ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoefficientsOfField
section
theorem UpperTheory.Reformulated.B.CoefficientsOfField.coef_of_field :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] ↥K],
    ∃ (c : UpperTheory.V.HV.Coef l),
      ∀ x ∈ K,
        ‖x‖ ≤ (1 : ℝ) → x ∈ c.O := by
  intro l _ K _
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  have hd : IsDiscreteValuationRing (integralClosure ℤ_[l] K) := UpperTheory.integralClosure_isDVR K
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K _
  refine ⟨⟨(integralClosure ℤ_[l] K).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h1 => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (isIntegral_algHom_iff f hf).1 ((UpperTheory.padicAlgCl_isIntegral_iff_norm_le_one x).2 h1)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherRest
section
theorem UpperTheory.Reformulated.B.Rb6.norm_le_one_of_mem :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l _ c x hx
  have h1 : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  have h2 : IsIntegral ℤ_[l] x := h1.map c.O.val
  have h3 : IsIntegral ℚ_[l] x := h2.tower_top
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic h3),
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h2]
  intro n
  rw [Polynomial.coeff_map]
  exact PadicInt.norm_le_one _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherTail
section
theorem UpperTheory.Reformulated.B.Rc8.norm_le_one_of_mem :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l _ c x hx
  have hi : IsIntegral ℤ_[l] x :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
  have hm : minpoly ℚ_[l] x = (minpoly ℤ_[l] x).map (algebraMap ℤ_[l] ℚ_[l]) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, hm,
    spectralValue_le_one_iff ((minpoly.monic hi).map _)]
  intro n
  rw [Polynomial.coeff_map]
  exact PadicInt.norm_le_one _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfMemCoef
section
theorem UpperTheory.Reformulated.B.Rf3.norm_le_one_of_mem_coef :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l inst c x hx
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hv : ∀ y, y ∈ v.integer ↔ ‖y‖ ≤ 1 := fun y => Iff.rfl
  have h1 : IsIntegral ℤ_[l] x :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
  have h2 : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := fun a => by
    rw [hv, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
    exact a.2
  have h3 : IsIntegral v.integer x :=
    h1.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer h2) (RingHom.id _) rfl
  exact (hv x).1 ((Valuation.integer.integers v).mem_of_integral h3)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PtLt
section
theorem UpperTheory.Reformulated.B.Gs4b.pt_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {c : UpperTheory.V.HV.Coef l} {R : Type} [inst_1 : CommRing R]
      [inst_2 : Algebra (↥c.O) R] [inst_3 : IsLocalRing R] (y : R →ₐ[↥c.O] Formalism.ConjugateSelfDual.Qbar l),
      ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ < (1 : ℝ) := by
  intro l _ c R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one (l := l) (O := ↥c.O) y a ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ReducedCoefficients
section
namespace UpperTheory.Reformulated.B.CoefficientRingContainingIntegers

theorem rc_coef {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : UpperTheory.V.HV.Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O := by
  have hD : IsDiscreteValuationRing (integralClosure ℤ_[l] K) := UpperTheory.dvr_of_norm_integral K (fun x hx => UpperTheory.padicAlgCl_isIntegral_of_norm_le_one x hx)
  have hF : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h1 => ?_⟩
  exact ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 (UpperTheory.padicAlgCl_isIntegral_of_norm_le_one x h1), rfl⟩

end UpperTheory.Reformulated.B.CoefficientRingContainingIntegers
end

