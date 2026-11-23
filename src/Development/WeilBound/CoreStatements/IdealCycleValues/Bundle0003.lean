module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset
public import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.IdealCycleValues.CycNumMulExpansion
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycNum_mul_expansion : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * cycNum Z cls H (classList cls μ ++ Q) := by
  intro O _ _ _ K _ _ ι _ σ Z cls H G Q
  classical
  have key : ∀ (P : MvPolynomial σ ℝ) (L : List (K → ℤ)) (s : Finset (σ →₀ ℕ)), P.support ⊆ s →
      cycNum Z cls P L = ∑ κ ∈ s, AddMonoidAlgebra.coeff P κ * (cycList Z (classList cls κ ++ L) : ℝ) := by
    intro P L s hs
    show ∑ κ ∈ P.support, AddMonoidAlgebra.coeff P κ * (cycList Z (classList cls κ ++ L) : ℝ) = _
    refine Finset.sum_subset hs (fun κ _ hκ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul]
  have hadd : ∀ P P' : MvPolynomial σ ℝ, cycNum Z cls (P + P') Q = cycNum Z cls P Q + cycNum Z cls P' Q := by
    intro P P'
    rw [key (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add,
      key P Q (P.support ∪ P'.support) Finset.subset_union_left,
      key P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : cycNum Z cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 Q ∅ (by simp)]
    simp
  have hsum : ∀ (α : Type) (s : Finset α) (P : α → MvPolynomial σ ℝ),
      cycNum Z cls (∑ a ∈ s, P a) Q = ∑ a ∈ s, cycNum Z cls (P a) Q := by
    intro α s P
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hmon : ∀ (κ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial κ c) Q = c * (cycList Z (classList cls κ ++ Q) : ℝ) := by
    intro κ c
    rw [key _ Q {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
  have hperm : ∀ ν μ : σ →₀ ℕ, cycList Z (classList cls (ν + μ) ++ Q) = cycList Z (classList cls ν ++ (classList cls μ ++ Q)) := by
    intro ν μ
    have hp : (classList cls (ν + μ)).Perm (classList cls ν ++ classList cls μ) := by
      rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
      simp only [classList, Multiset.coe_toList, Finsupp.toMultiset_add, Multiset.map_add (f := _)]
    rw [← List.append_assoc]
    exact BaseChangeColon.intersection_numbers_perm_invariant.2 O K ι Z _ _ (hp.append_right Q)
  conv_lhs => rw [H.as_sum, G.as_sum, Finset.sum_mul_sum]
  rw [hsum]
  simp_rw [hsum, MvPolynomial.monomial_mul, hmon]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [key H (classList cls μ ++ Q) H.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [hperm]
  ring
end

-- bundled from Development.WeilBound.CoreStatements.IdealCycleValues.FlagFrameOfPointIdeal
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace BaseChangeColon

theorem foldr_diffStep_zero {K : Type} (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l) (h : (K → ℤ) → ℤ) :
    l.foldr diffStep h = 0 := by
  induction l with
  | nil => simp at hl
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hl with hb | hb
    · subst hb
      funext m
      simp [diffStep]
    · rw [ih hb]
      funext m
      simp [diffStep]

theorem intNumL_of_zero_mem {F : Type} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (V : Ideal (MRing ι F)) (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l) : intNumL F V l = 0 := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get, foldr_diffStep_zero l hl]
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, hm⟩ := h.choose_spec.exists
    exact hm.symm
  · rfl

theorem flag_frame_of_point_ideal : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ a : ℕ, 1 ≤ a → ∀ Y : List (K → ℤ), a + Y.length = e → ∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F (pointIdeal F y) (rootList (fun i => -b i) α ++ Y) = 0 := by
  intro hS F _ Ω _ _ K _ _ ι _ y e hP hd N w b hw a ha Y hY
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact Finset.sum_eq_zero fun α hα => by
      rw [Finset.Nat.mem_antidiagonalTuple] at hα
      simp at hα
  have ht : AlgebraicIndependent Ω
      ((IsScalarTower.toAlgHom Ω (MvPolynomial (Fin N) Ω) (FractionRing (MvPolynomial (Fin N) Ω))) ∘ X) :=
    (MvPolynomial.algebraicIndependent_X (Fin N) Ω).map'
      (IsFractionRing.injective (MvPolynomial (Fin N) Ω) (FractionRing (MvPolynomial (Fin N) Ω)))
  have h1 := hS F Ω K ι y e hP hd N hN _ _ w b hw N 0 _ (isTwistedDualGens_triv F y N) _ _ ht
    (N - 1 + a) Y (by omega)
  have h2 := hS F Ω K ι y e hP hd N hN _ _ _ _ (isFlagFrame_scaledTriv F y N (one_ne_zero (α := Ω))) N 0 _
    (isTwistedDualGens_triv F y N) _ _ ht (N - 1 + a) Y (by omega)
  rw [projIdeal_independent_of_basis F Ω K ι y N N _ w (scaledBasis N (one_ne_zero (α := Ω))) _ _ _ ht, h2,
    if_pos (Nat.le_add_right _ _), if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at h1
  simp only [zero_sub] at h1
  rw [← h1]
  refine Finset.sum_eq_zero fun α hα => intNumL_of_zero_mem _ _ ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hα
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) (by omega)
  refine List.mem_append_left _ ?_
  unfold rootList
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_replicate.mpr ⟨hi, by simp⟩⟩

end BaseChangeColon
end

-- bundled from Development.WeilBound.CoreStatements.IdealCycleValues.GenNumMulExpansion
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.genNum_mul_expansion : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * genNum F V cls H (classList cls μ ++ Q) := by
  intro F _ K _ _ ι _ σ V cls H G Q
  classical
  have key : ∀ (P : MvPolynomial σ ℝ) (L : List (K → ℤ)) (s : Finset (σ →₀ ℕ)), P.support ⊆ s →
      genNum F V cls P L = ∑ κ ∈ s, AddMonoidAlgebra.coeff P κ * (intNumL F V (classList cls κ ++ L) : ℝ) := by
    intro P L s hs
    show ∑ κ ∈ P.support, AddMonoidAlgebra.coeff P κ * (intNumL F V (classList cls κ ++ L) : ℝ) = _
    refine Finset.sum_subset hs (fun κ _ hκ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul]
  have hadd : ∀ P P' : MvPolynomial σ ℝ, genNum F V cls (P + P') Q = genNum F V cls P Q + genNum F V cls P' Q := by
    intro P P'
    rw [key (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add,
      key P Q (P.support ∪ P'.support) Finset.subset_union_left,
      key P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : genNum F V cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 Q ∅ (by simp)]
    simp
  have hsum : ∀ (α : Type) (s : Finset α) (P : α → MvPolynomial σ ℝ),
      genNum F V cls (∑ a ∈ s, P a) Q = ∑ a ∈ s, genNum F V cls (P a) Q := by
    intro α s P
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hmon : ∀ (κ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial κ c) Q = c * (intNumL F V (classList cls κ ++ Q) : ℝ) := by
    intro κ c
    rw [key _ Q {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
  have hperm : ∀ ν μ : σ →₀ ℕ, intNumL F V (classList cls (ν + μ) ++ Q) = intNumL F V (classList cls ν ++ (classList cls μ ++ Q)) := by
    intro ν μ
    have hp : (classList cls (ν + μ)).Perm (classList cls ν ++ classList cls μ) := by
      rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
      simp only [classList, Multiset.coe_toList, Finsupp.toMultiset_add, Multiset.map_add (f := _)]
    rw [← List.append_assoc]
    exact BaseChangeColon.intersection_numbers_perm_invariant.1 F K ι V _ _ (hp.append_right Q)
  conv_lhs => rw [H.as_sum, G.as_sum, Finset.sum_mul_sum]
  rw [hsum]
  simp_rw [hsum, MvPolynomial.monomial_mul, hmon]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [key H (classList cls μ ++ Q) H.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [hperm]
  ring
end

