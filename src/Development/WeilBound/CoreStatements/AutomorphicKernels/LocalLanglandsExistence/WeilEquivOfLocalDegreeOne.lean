module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import GroundTheory.GlobalFields.TateThesis.HeckeChar
public import GroundTheory.LocalFields.LocalZetaEpsilon
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import GroundTheory.GlobalFields.Artin.OneDim
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.TateThesis.Bundle0010
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0002
public import GroundTheory.GlobalFields.TateThesis.Bundle0006

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

theorem valuation_algebraMap_le_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F]
    [Algebra F Ω] (x : 𝓞 F) : A.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
  have hint : IsIntegral ℤ (algebraMap F Ω (x : F)) :=
    (RingOfIntegers.isIntegral_coe x).map (algebraMap F Ω).toIntAlgHom
  have hA : IsIntegral A (algebraMap F Ω (x : F)) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hA
  rw [← hy]
  exact A.valuation_le_one y

theorem card_le_of_pow_eq_self {R : Type} [CommRing R] [IsDomain R] [Fintype R] {q : ℕ} (hq : 1 < q)
    (H : ∀ z : R, z ^ q = z) : Fintype.card R ≤ q := by
  classical
  have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial R).natDegree = q := by
    have h1 : (Polynomial.X : Polynomial R).degree < (Polynomial.X ^ q : Polynomial R).degree := by
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]; exact_mod_cast hq
    rw [Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_sub_eq_left_of_degree_lt h1),
      Polynomial.natDegree_X_pow]
  have hp : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hdeg; omega
  have hsub : (Finset.univ : Finset R).val ⊆ (Polynomial.X ^ q - Polynomial.X : Polynomial R).roots := by
    intro z _
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    simp [H z]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rwa [hdeg, Finset.card_univ] at this

section Transport

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K F : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra K F] [IsScalarTower K F Ω]
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 F)}


omit [IsAlgClosure F Ω] in
theorem normV_eq_of_localDegreeOne (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x) :
    normV w = normV v := by
  classical
  obtain ⟨f, hf⟩ := GlobalTheory.WeilRestrict.normV_eq_pow_of_isPlaceOver h h'
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  have hq : 1 < normV v := one_lt_normV v
  have hφW : φ ∈ Weil h := mem_Weil_of_isFrob h hφ
  have key : ∀ x : 𝓞 F, x ^ normV v - x ∈ w.asIdeal := by
    intro x
    rw [← h' (x ^ normV v - x)]
    have h1 := hφ.2 _ (valuation_algebraMap_le_one A x)
    have h2 : φ (algebraMap F Ω (x : F)) = algebraMap F Ω (x : F) := hloc ⟨φ, hφW⟩ (x : F)
    rw [h2, Valuation.map_sub_swap] at h1
    have e : algebraMap F Ω ((x ^ normV v - x : 𝓞 F) : F) =
        algebraMap F Ω (x : F) ^ normV v - algebraMap F Ω (x : F) := by
      push_cast
      rfl
    rw [e]
    exact h1
  have : w.asIdeal.IsPrime := w.isPrime
  have : Finite (𝓞 F ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  let _ : Fintype (𝓞 F ⧸ w.asIdeal) := Fintype.ofFinite _
  have hle : normV w ≤ normV v := by
    rw [normV, Nat.card_eq_fintype_card]
    refine card_le_of_pow_eq_self hq fun z => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact key x
  have h1w : 1 < normV w := one_lt_normV w
  rw [hf] at hle h1w ⊢
  have hf1 : f ≤ 1 := by
    exact (pow_le_pow_iff_right₀ hq).mp (show normV v ^ f ≤ normV v ^ 1 by rwa [pow_one])
  have hf0 : f ≠ 0 := by rintro rfl; simp at h1w
  have : f = 1 := by omega
  rw [this, pow_one]

end Transport

section GlobalModel

end GlobalModel

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

end
