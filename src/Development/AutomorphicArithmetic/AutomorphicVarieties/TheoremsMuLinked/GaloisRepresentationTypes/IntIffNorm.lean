module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.TriangularOfReducibleRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdEndOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001

@[expose] public section

section Factor

open IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.Base

private theorem int_iff_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem loc_of_int {O R A : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A]
    [Nontrivial A] [Algebra O A] [Algebra.IsIntegral O A] (f : R →ₐ[O] A) : IsLocalHom f := by
  let g : R →+* f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' g hg
  have hl : IsLocalHom g := IsLocalHom.of_surjective _ hg
  haveI : Algebra.IsIntegral f.range A := Algebra.IsIntegral.tower_top (R := O)
  have h2 : IsLocalHom (algebraMap f.range A) := Algebra.IsIntegral.isLocalHom _ _
  exact ⟨fun x hx => hl.map_nonunit x (h2.map_nonunit (g x) hx)⟩

private theorem exists_fac {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    (f : R →ₐ[c.O] PadicAlgCl l) (hf : IsLocPt f) :
    ∃ (A : Subalgebra c.O (PadicAlgCl l)) (_ : IsDiscreteValuationRing A) (_ : Module.Finite c.O A), ∀ x, f x ∈ A := by
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI := (dvrFacts l c.O).2.2.2.1
  obtain ⟨E, hE⟩ := Loc.ptFin (l := l) R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf
  have hE' : ∀ a, f a ∈ E.1 := fun a => (hE a).1
  haveI := E.2
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  have hint : ∀ x, IsIntegral ℤ_[l] (f x) := fun x => by
    obtain ⟨a, ha⟩ := residue_surjective (res c.O R x)
    have hm : x - algebraMap c.O R a ∈ maximalIdeal R := by
      rw [← res_eq_zero_iff c.O, map_sub, AlgHom.commutes, ← ha]
      exact sub_self _
    have h1 : IsIntegral ℤ_[l] (f (algebraMap c.O R a)) := by
      rw [f.commutes]
      exact (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom ℤ_[l] c.O (PadicAlgCl l))
    have h2 := ((int_iff_norm _).2 (hf _ hm).le).add h1
    rwa [← map_add, sub_add_cancel] at h2
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E.1
  let j : E.1 →ₐ[ℤ_[l]] PadicAlgCl l := E.1.val.restrictScalars ℤ_[l]
  have hj : Function.Injective j := Subtype.val_injective
  let e := (integralClosure ℤ_[l] E.1).equivMapOfInjective j hj
  let B := (integralClosure ℤ_[l] E.1).map j
  have hB : ∀ x, f x ∈ B := fun x => ⟨⟨f x, hE' x⟩, (isIntegral_algHom_iff j hj).1 (hint x), rfl⟩
  let A : Subalgebra c.O (PadicAlgCl l) := { B.toSubsemiring with algebraMap_mem' := fun a => f.commutes a ▸ hB _ }
  have d1 : IsDiscreteValuationRing B := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have d2 : Module.Finite ℤ_[l] B := Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Finite ℤ_[l] A := d2
  exact ⟨A, d1, Module.Finite.of_restrictScalars_finite ℤ_[l] c.O A, hB⟩

end Factor

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

