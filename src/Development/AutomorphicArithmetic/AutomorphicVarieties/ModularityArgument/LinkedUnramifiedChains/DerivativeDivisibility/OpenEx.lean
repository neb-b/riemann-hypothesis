module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LinkedUnlOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.Bundle0003

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af

namespace UpperTheory.V.J

open UpperTheory.V.Pr

private theorem oe_norm {l : ℕ} [Fact l.Prime] {x : PadicAlgCl l} (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hq : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  change spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem oe_field {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R]
    (φ : R →ₐ[ℤ_[l]] PadicAlgCl l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x, φ x ∈ E ∧ ‖φ x‖ ≤ 1 := by
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := R)
  haveI := (t.finite_toSet.image φ).to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] (φ '' (t : Set R)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x => ⟨?_,
      oe_norm ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map φ)⟩⟩
  have hx : x ∈ Submodule.span ℤ_[l] (t : Set R) := ht ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [map_smul, ← algebraMap_smul ℚ_[l] a]
    exact IntermediateField.smul_mem _ hb

private theorem oe_big {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Subalgebra c.O (PadicAlgCl l)) [Module.Finite c.O A] :
    ∃ c₂ : Coef l, c.O ≤ c₂.O ∧ ∀ x ∈ A, x ∈ c₂.O := by
  haveI : Module.Finite ℤ_[l] A := Module.Finite.trans c.O A
  obtain ⟨E₁, f₁, m₁⟩ := oe_field c.O.val
  obtain ⟨E₂, f₂, m₂⟩ := oe_field (A.val.restrictScalars ℤ_[l])
  obtain ⟨c₂, hc⟩ := UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)
  exact ⟨c₂, fun x hx => (hc x).2 ⟨(le_sup_left : E₁ ≤ E₁ ⊔ E₂) (m₁ ⟨x, hx⟩).1, (m₁ ⟨x, hx⟩).2⟩,
    fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ E₁ ⊔ E₂) (m₂ ⟨x, hx⟩).1, (m₂ ⟨x, hx⟩).2⟩⟩

private theorem oe_res {l : ℕ} [Fact l.Prime] {c c₁ : Coef l} (hle : c.O ≤ c₁.O) :
    ∃ f : ResidueField c.O →+* ResidueField c₁.O,
      ∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b := by
  let i : c.O →+* c₁.O := (Subalgebra.inclusion hle).toRingHom
  have hi : i.IsIntegral := by
    haveI : Algebra.IsIntegral ℤ_[l] c₁.O := Algebra.IsIntegral.of_finite ℤ_[l] c₁.O
    have e : i.comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c₁.O := (Subalgebra.inclusion hle).comp_algebraMap
    refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] c.O) i ?_
    rw [e]
    exact fun x => Algebra.IsIntegral.isIntegral x
  haveI : IsLocalHom i := hi.isLocalHom (Subalgebra.inclusion_injective hle)
  exact ⟨ResidueField.map i, fun a b h => by
    rw [ResidueField.map_residue]
    exact congrArg _ (Subtype.ext h)⟩

end UpperTheory.V.J
