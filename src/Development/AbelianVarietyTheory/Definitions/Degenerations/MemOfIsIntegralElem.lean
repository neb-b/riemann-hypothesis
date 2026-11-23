module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ToricData GlobalTheory.HostModel GlobalTheory.HostModel.ConjDual GlobalTheory.Ex.ValInh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex

section Valued

theorem mem_of_isIntegralElem {R C : Type} [CommRing R] [Field C] (S : ValuationSubring C) (j : R →+* C) (hj : ∀ r, j r ∈ S)
    {x : C} (hx : j.IsIntegralElem x) : x ∈ S := by
  obtain ⟨p, hp, h⟩ := hx
  have : IsIntegral S x := ⟨p.map (j.codRestrict S.toSubring hj), hp.map _, by rw [Polynomial.eval₂_map]; exact h⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact y.2

variable {O' : Type} [CommRing O'] [IsDomain O'] {R₁ : Type} [CommRing R₁] (g : PowerSeries O' →+* R₁) {K : Type} [Field K]
  (i : R₁ →+* K)

theorem not_allC_false (hi : Function.Injective (i.comp g))
    (halg : ∀ x : K, ∃ p : Polynomial (PowerSeries O'), p ≠ 0 ∧ p.eval₂ (i.comp g) x = 0) (hg : g.IsIntegral) :
    ¬ AllC g i fun _ _ => False := by
  intro h
  let V := PowerSeries (FractionRing O')
  obtain ⟨C, _, _, _, _, _, h1, h2⟩ := GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing V (FractionRing V)
    (a := PowerSeries.X) PowerSeries.X_ne_zero (fun e => not_isUnit_zero (PowerSeries.constantCoeff_X (R := FractionRing O') ▸ e.map PowerSeries.constantCoeff))
    (r := 1 / 2) (by norm_num) (by norm_num)
  let j₀ : V →+* C := (algebraMap (FractionRing V) C).comp (algebraMap V _)
  let j : PowerSeries O' →+* C := j₀.comp (PowerSeries.map (algebraMap O' (FractionRing O')))
  have hj : Function.Injective j := ((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V _)).comp
    (PowerSeries.map_injective _ (IsFractionRing.injective O' _))
  letI : Algebra (PowerSeries O') K := (i.comp g).toAlgebra
  letI : Algebra (PowerSeries O') C := j.toAlgebra
  haveI : FaithfulSMul (PowerSeries O') K := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  haveI : FaithfulSMul (PowerSeries O') C := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
  haveI : Algebra.IsAlgebraic (PowerSeries O') K := ⟨halg⟩
  let gam : K →ₐ[PowerSeries O'] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hc : ∀ f, gam.toRingHom (i (g f)) = j f := fun f => gam.commutes f
  letI : Algebra (FractionRing O') C := (j₀.comp PowerSeries.C).toAlgebra
  have hX : j PowerSeries.X = j₀ PowerSeries.X := congrArg j₀ (PowerSeries.map_X _)
  refine h C gam.toRingHom (Units.mk0 (j PowerSeries.X) fun e => PowerSeries.X_ne_zero (hj (e.trans (map_zero j).symm)))
    (fun x => (congrArg j₀ (PowerSeries.map_C _ x).symm).trans (hc _).symm) (fun r => ?_) (hc _).symm ?_
  · refine mem_normIntegers_iff.1 (mem_of_isIntegralElem _ j (fun f => mem_normIntegers_iff.2 ((h1 _).2 ⟨_, rfl⟩)) ?_)
    obtain ⟨p, hp, e⟩ := hg r
    refine ⟨p, hp, ?_⟩
    have := congrArg (gam.toRingHom.comp i) e
    rwa [map_zero, Polynomial.hom_eval₂, show (gam.toRingHom.comp i).comp g = j from RingHom.ext hc] at this
  · rw [Units.val_mk0, hX]
    exact h2.trans_lt (by norm_num)

theorem SerBase.not_allC_false {K : Type} [Field K] [Algebra (FractionRing O') K] {i : PowerSeries O' →+* K} (hi : SerBase i) :
    ¬ AllC (RingHom.id _) i fun _ _ => False :=
  GlobalTheory.Ex.not_allC_false (RingHom.id _) i hi.inj hi.alg (RingHom.isIntegral_of_surjective _ Function.surjective_id)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {b : O →+* O'} {Y : Model Xo c β} [IsDomain R₁] {g}
  {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c}

end Valued

namespace StepInh
section Series
variable {k K X : Type} [CommRing k] [Field K] (i : PowerSeries k →+* K)

end Series

section Terms
variable {F : Type} [Field F]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Geo.Tor.Level H)

variable (k : Type) [CommRing k] [IsDomain k] [Algebra (FractionRing k) F]

end Terms

section ToricLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Geo.Tor.Level H}
  (c : Coeff l) (k : Type) [CommRing k] [IsDomain k] (bF : c.F →+* k) {O : Type} [CommRing O] (β : O →+* c.F)
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing k) F] (ζ : ℕ → Fˣ)
  (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
  (hζ : ∀ n, 0 < n → ∀ z : c.F, (z : ℂ) = zeta n → (ζ n : F) = algebraMap (FractionRing k) F (algebraMap k _ (bF z)))


end ToricLift

section ToricSer
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Geo.Tor.Level H}
  {k : Type} [Field k] {K : Type} [Field K] (i : PowerSeries k →+* K) {ζ r : ℕ → Kˣ}
  (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hr : ∀ n, 0 < n → (r n : K) ^ n = i PowerSeries.X)




end ToricSer

section SerInh
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Geo.Tor.Level H}

end SerInh

section Settings
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_cExt (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (h : CDV W) :
    ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C)
      (_ : CharZero C) (_ : Algebra (FractionRing W) C), CExt W (IsLocalRing.maximalIdeal W) C := by
  obtain ⟨_, _, _⟩ := h
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨C, _, _, _, _, _, h1, h2⟩ := GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W)
    hp.ne_zero (hp.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self p) (r := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, _, ‹_›, ‹_›, ‹_›, charZero_of_injective_ringHom (algebraMap (FractionRing W) C).injective, _,
    fun r => (h1 _).2 ⟨r, rfl⟩, fun r hr => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.1 (hp.maximalIdeal_eq ▸ hr)
  have := (h1 _).2 ⟨s, rfl⟩
  rw [map_mul, map_mul, norm_mul, h2]
  linarith

section Tate
variable {R : Type} [CommRing R] [IsDomain R] (q : (FractionRing R)ˣ) (F : Type) [Field F] [Algebra (FractionRing R) F]

end Tate

end Settings

section GoodMdl
open UnifModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

end GoodMdl

end StepInh
end GlobalTheory.Ex
end
