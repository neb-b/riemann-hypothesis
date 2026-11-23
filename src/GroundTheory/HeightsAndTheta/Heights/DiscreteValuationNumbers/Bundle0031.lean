module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SegreFlagIndepHomogeneousImpliesGeneral
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

universe u

namespace SegreFlagIndep

theorem isSymmetric_homogeneousComponent {σ R : Type*} [CommSemiring R] {G : MvPolynomial σ R}
    (hG : G.IsSymmetric) (c : ℕ) : (homogeneousComponent c G).IsSymmetric := by
  intro e
  ext d
  obtain ⟨d', rfl⟩ : ∃ d', d = d'.mapDomain e :=
    ⟨d.mapDomain e.symm, by rw [← Finsupp.mapDomain_comp]; simp⟩
  rw [coeff_rename_mapDomain _ e.injective, coeff_homogeneousComponent,
    coeff_homogeneousComponent, Finsupp.degree_mapDomain]
  conv_rhs => rw [← hG e, coeff_rename_mapDomain _ e.injective]

section Numbers

variable {F : Type*} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ)

def listNum (L : List (K → ℤ)) : ℤ :=
  if h : L.length = n then I V n (fun j => L.get (Fin.cast h.symm j)) else 0

theorem polyNum_eq {r : ℕ} (deg : Fin r → K → ℤ) (Q : MvPolynomial (Fin r) ℤ) :
    polyNum I V n deg Q = ∑ μ ∈ Q.support, Q.coeff μ * listNum I V n (monoList deg μ) := rfl

theorem polyNum_eq_of_subset {r : ℕ} (deg : Fin r → K → ℤ) (Q : MvPolynomial (Fin r) ℤ)
    (S : Finset (Fin r →₀ ℕ)) (hS : Q.support ⊆ S) :
    polyNum I V n deg Q = ∑ μ ∈ S, Q.coeff μ * listNum I V n (monoList deg μ) := by
  rw [polyNum_eq]
  exact Finset.sum_subset hS fun μ _ hμ => by rw [notMem_support_iff.mp hμ, zero_mul]

def polyNumHom {r : ℕ} (deg : Fin r → K → ℤ) : MvPolynomial (Fin r) ℤ →+ ℤ where
  toFun := polyNum I V n deg
  map_zero' := by simp [polyNum]
  map_add' P Q := by
    classical
    rw [polyNum_eq_of_subset I V n deg (P + Q) (P.support ∪ Q.support) support_add,
      polyNum_eq_of_subset I V n deg P (P.support ∪ Q.support) Finset.subset_union_left,
      polyNum_eq_of_subset I V n deg Q (P.support ∪ Q.support) Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    simp only [MvPolynomial.coeff_add, add_mul]

theorem polyNumHom_apply {r : ℕ} (deg : Fin r → K → ℤ) (Q : MvPolynomial (Fin r) ℤ) :
    polyNumHom I V n deg Q = polyNum I V n deg Q := rfl

theorem polyNum_monomial {r : ℕ} (deg : Fin r → K → ℤ) (μ : Fin r →₀ ℕ) (a : ℤ) :
    polyNum I V n deg (monomial μ a) = a * listNum I V n (monoList deg μ) := by
  classical
  rw [polyNum_eq_of_subset I V n deg _ {μ} support_monomial_subset]
  simp

end Numbers

section Lists

variable {K : Type}

theorem monoList_append {N r : ℕ} (d : Fin N → K → ℤ) (Y : Fin r → K → ℤ) (α : Fin N →₀ ℕ)
    (ν : Fin r →₀ ℕ) :
    monoList (Fin.append d Y) (α.mapDomain (Fin.castAdd r) + ν.mapDomain (Fin.natAdd N)) =
      monoList d α ++ monoList Y ν := by
  unfold monoList
  rw [← List.ofFn_id, List.ofFn_add, List.flatMap_append, List.ofFn_eq_map, List.ofFn_eq_map,
    List.flatMap_map, List.flatMap_map]
  congr 1
  · congr 1
    funext s
    have h1 : (Fin.castLE (Nat.le_add_right N r) s) = Fin.castAdd r s := rfl
    simp only [id, h1, Finsupp.add_apply,
      Finsupp.mapDomain_apply_of_injective (Fin.castAdd_injective N r), Fin.append_left]
    rw [Finsupp.mapDomain_of_notMem_range, add_zero]
    rintro ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp at this
    omega
  · congr 1
    funext s
    simp only [id, Finsupp.add_apply,
      Finsupp.mapDomain_apply_of_injective (Fin.natAdd_injective r N), Fin.append_right]
    rw [Finsupp.mapDomain_of_notMem_range, zero_add]
    rintro ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp at this
    omega

theorem length_monoList {N : ℕ} (d : Fin N → K → ℤ) (α : Fin N →₀ ℕ) :
    (monoList d α).length = α.degree := by
  rw [Finsupp.degree_eq_sum]
  simp [monoList, List.length_flatMap, Fin.sum_univ_def]

theorem monoList_ones {n : ℕ} (Y : Fin n → K → ℤ) :
    monoList Y (∑ j : Fin n, Finsupp.single j 1) = List.ofFn Y := by
  classical
  rw [List.ofFn_eq_map]
  unfold monoList
  have : ∀ s : Fin n, (∑ j : Fin n, Finsupp.single j 1) s = 1 := by
    intro s
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp only [this, List.replicate_one]
  induction List.finRange n with
  | nil => rfl
  | cons a l ih => simp [ih]

end Lists

section Expand

variable {F : Type*} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (e : ℕ)

theorem polyNum_mul_monomial {N r : ℕ} (d : Fin N → K → ℤ) (Y : Fin r → K → ℤ)
    (A : MvPolynomial (Fin N) ℤ) (ν : Fin r →₀ ℕ) :
    polyNum I V e (Fin.append d Y) (rename (Fin.castAdd r) A * rename (Fin.natAdd N) (monomial ν 1)) =
      ∑ α ∈ A.support, A.coeff α * listNum I V e (monoList d α ++ monoList Y ν) := by
  conv_lhs => rw [as_sum A]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul, ← polyNumHom_apply, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [rename_monomial, rename_monomial, monomial_mul, polyNumHom_apply, polyNum_monomial,
    monoList_append, mul_one]

theorem polyNum_mul_eq_sum {N r : ℕ} (d : Fin N → K → ℤ) (Y : Fin r → K → ℤ)
    (A : MvPolynomial (Fin N) ℤ) (R : MvPolynomial (Fin r) ℤ) :
    polyNum I V e (Fin.append d Y) (rename (Fin.castAdd r) A * rename (Fin.natAdd N) R) =
      ∑ ν ∈ R.support, R.coeff ν *
        polyNum I V e (Fin.append d Y) (rename (Fin.castAdd r) A * rename (Fin.natAdd N) (monomial ν 1)) := by
  conv_lhs => rw [as_sum R]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, ← polyNumHom_apply, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have : monomial ν (R.coeff ν) = R.coeff ν • monomial ν (1 : ℤ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_zsmul, mul_smul_comm, map_zsmul, polyNumHom_apply, smul_eq_mul]

theorem prod_X_natAdd (N n : ℕ) :
    (∏ j : Fin n, X (Fin.natAdd N j) : MvPolynomial (Fin (N + n)) ℤ) =
      rename (Fin.natAdd N) (monomial (∑ j : Fin n, Finsupp.single j 1) 1) := by
  rw [monomial_sum_one, map_prod]
  simp [rename_X, ← X.eq_1]

end Expand

end SegreFlagIndep

variable (F : Type*) [Field F] (Ω : Type*) [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def SegreFlagIndep₂.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (e : ℕ), IsProjVarF (mcIdeal F x) e →
    ∀ (N : ℕ) (E : Type u) [AddCommGroup E] [Module Ω E] (B : ChartBundle F (mseg x) N E)
      (fl₁ fl₂ : FullFlag F x B) (I₀ : IFamily F ι), IsFieldIntersection I₀ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (Y : Fin r → K → ℤ) (R : MvPolynomial (Fin r) ℤ),
      polyNum I₀ (mcIdeal F x) e (Fin.append fl₁.deg Y)
          (rename (Fin.castAdd r) G * rename (Fin.natAdd N) R) =
        polyNum I₀ (mcIdeal F x) e (Fin.append fl₂.deg Y)
          (rename (Fin.castAdd r) G * rename (Fin.natAdd N) R)

namespace SegreFlagIndep

theorem segreFlagIndep_homogeneous_implies_general (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{u} F Ω ι) :
    SegreFlagIndep₂.Statement.{u} F Ω ι := by
  intro x e hV N E _ _ B fl₁ fl₂ I₀ hI G hG r Y R
  have hsplit : ∀ d : Fin N → K → ℤ,
      polyNum I₀ (mcIdeal F x) e (Fin.append d Y) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) R) =
        ∑ c ∈ Finset.range (G.totalDegree + 1), polyNum I₀ (mcIdeal F x) e (Fin.append d Y)
          (rename (Fin.castAdd r) (homogeneousComponent c G) * rename (Fin.natAdd N) R) := by
    intro d
    conv_lhs => rw [← sum_homogeneousComponent G]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, ← polyNumHom_apply, map_sum]
    rfl
  rw [hsplit, hsplit]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [polyNum_mul_eq_sum, polyNum_mul_eq_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  set Gc := homogeneousComponent c G
  have hGc : Gc.IsHomogeneous c := homogeneousComponent_isHomogeneous c G
  set L := monoList Y ν

  have hmono : ∀ d : Fin N → K → ℤ,
      polyNum I₀ (mcIdeal F x) e (Fin.append d Y)
          (rename (Fin.castAdd r) Gc * rename (Fin.natAdd N) (monomial ν 1)) =
        polyNum I₀ (mcIdeal F x) e (Fin.append d L.get)
          (rename (Fin.castAdd L.length) Gc * ∏ j : Fin L.length, X (Fin.natAdd N j)) := by
    intro d
    rw [prod_X_natAdd, polyNum_mul_monomial, polyNum_mul_monomial, monoList_ones, List.ofFn_get]
  rw [hmono, hmono]
  by_cases hce : c + L.length = e
  · exact h x e hV N E B fl₁ fl₂ I₀ hI Gc (isSymmetric_homogeneousComponent hG c) c L.length L.get
      hGc hce
  · have hzero : ∀ d : Fin N → K → ℤ, polyNum I₀ (mcIdeal F x) e (Fin.append d L.get)
        (rename (Fin.castAdd L.length) Gc * ∏ j : Fin L.length, X (Fin.natAdd N j)) = 0 := by
      intro d
      rw [prod_X_natAdd, polyNum_mul_monomial, monoList_ones, List.ofFn_get]
      refine Finset.sum_eq_zero fun α hα => ?_
      have hdeg : α.degree = c := by
        have := hGc (mem_support_iff.mp hα)
        rwa [Finsupp.degree_eq_weight_one]
      rw [listNum, dite_eq_right, mul_zero]
      rw [List.length_append, length_monoList, hdeg]
      exact hce
    rw [hzero, hzero]

end SegreFlagIndep

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpHorizontalSat.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      ∀ F : MRing (extIdx ι J) O, F ∈ W ↔ ∃ s : MRing ι O, s ∉ W.comap (liftForm (ι := ι) (J := J) (R := O)) ∧
        (liftForm (ι := ι) (J := J) (R := O)) s * F ∈ blowUpOf P u ⊔ Ideal.map (liftForm (ι := ι) (J := J) (R := O)) (W.comap (liftForm (ι := ι) (J := J) (R := O)))

def BlowUpHorizontalMult.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      divCycle P x (W.comap (liftForm (ι := ι) (J := J) (R := O))) = divCycle (blowUpOf P u) (liftForm x) W

def BlowUpHorizontalLift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), divCycle P x W ≠ 0 → (C ϖ : MRing ι O) ∉ W →
      ∃ W' : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W' ≠ 0 ∧
        (C ϖ : MRing (extIdx ι J) O) ∉ W' ∧ W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W

def BlowUpHorizontalStrict.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      (∃ j, u j ∉ W.comap (liftForm (ι := ι) (J := J) (R := O))) → W = blowUpOf (W.comap (liftForm (ι := ι) (J := J) (R := O))) u

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleChartSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def FlagBundleChartSection.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (i : Fin N) (c : ∀ k, ι k), segreVec y c ≠ 0 →
      ∃ (dl dm : Option K → ℕ) (l μ : MRing (bundleIdx ι M) F) (m : K → ℕ),
        μ = ∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ m k ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaDeg + liftDeg (b i - a) ∧
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) l =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) μ ∧
        ∀ q ∈ projIdeal F y w φ (truncCoord t i), ∃ n : ℕ,
          (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n * q ∈
            projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {l}

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Defs

variable {R : Type*} [CommRing R]

abbrev localQuot (P U : Ideal R) [U.IsPrime] : Type _ :=
  Localization.AtPrime U ⧸ P.map (algebraMap R (Localization.AtPrime U))

def localQuotMap (P U : Ideal R) [U.IsPrime] : R →+* localQuot P U :=
  (Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime U))

end Defs

section Lemmas

def LocalQuotRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P.IsPrime → P ≤ U →
    IsDomain (localQuot P U) ∧ IsLocalRing (localQuot P U) ∧
      (∀ y : localQuot P U, IsUnit y ↔ y ∉ U.map (localQuotMap P U)) ∧
      ∀ x : R, localQuotMap P U x = 0 ↔ x ∈ P

def LocalQuotPrimes.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    (∀ W : Ideal R, W.IsPrime → P ≤ W → W ≤ U →
      (W.map (localQuotMap P U)).IsPrime ∧ (W.map (localQuotMap P U)).comap (localQuotMap P U) = W) ∧
    ∀ p : Ideal (localQuot P U), p.IsPrime →
      P ≤ p.comap (localQuotMap P U) ∧ p.comap (localQuotMap P U) ≤ U ∧
        (p.comap (localQuotMap P U)).map (localQuotMap P U) = p

def LocCycleLocalQuot.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (J W : Ideal R), P ≤ J → W.IsPrime → P ≤ W →
    W ≤ U → locCycle J W = locCycle (J.map (localQuotMap P U)) (W.map (localQuotMap P U))

def LocalQuotColon.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (f g : R),
    ((P ⊔ Ideal.span {f}).colon {g}).map (localQuotMap P U) =
      (Ideal.span {localQuotMap P U f}).colon {localQuotMap P U g}

def LocalQuotFinsum.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    ∀ (F : Ideal R → ℤ) (F' : Ideal (localQuot P U) → ℤ),
      (∀ G, F G ≠ 0 → G.IsPrime ∧ P ≤ G ∧ G ≤ U) → (∀ p, F' p ≠ 0 → p.IsPrime) →
      (∀ G : Ideal R, G.IsPrime → P ≤ G → G ≤ U → F G = F' (G.map (localQuotMap P U))) →
      ∑ᶠ G, F G = ∑ᶠ p, F' p

def LocalCoeffLocal.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    ∀ f g s u v : A, f ≠ 0 → g ≠ 0 → s ≠ 0 → IsUnit u → u * f = v * g →
    (∀ W : Ideal A, locCycle (Ideal.span {s}) W ≠ 0 →
      locCycle (Ideal.span {f}) W = locCycle (Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      ∑ᶠ W, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ (Ideal.span {f}).colon {g}) (IsLocalRing.maximalIdeal A)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeLinesIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PairConeLinesIndep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (Φ : Type) [Field Φ] [Algebra Ω Φ] (K : Type) (N : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E),
    LinearIndependent Ω ψ → ∀ (t : Fin N → Φ), AlgebraicIndependent Ω t → ∀ g : Φ, g ≠ 0 →
      AlgebraicIndependent
        (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
        (Sum.elim (fun i : Fin N => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))) * X (some none))
          (fun _ : Unit => (C g * X none : MvPolynomial (Option (Option K)) Φ)))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsProjIdealFormValue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ProjIdealFormValue.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [DecidableEq K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (w : Module.Basis (Fin N) Ω E)
    (M : ℕ) (φ : Fin M → Module.Dual Ω E) (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ)
    (d : Option K → ℕ) (x : MRing (bundleIdx ι M) F), IsMultiHomog x d →
      (x ∈ projIdeal F y w φ t ↔
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) x = 0)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

