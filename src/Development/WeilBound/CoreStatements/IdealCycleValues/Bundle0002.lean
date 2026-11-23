module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.IdealCycleValues.CycNumLinearInPolynomial
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycNum_linear_in_polynomial : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), cycNum Z cls (C c * H) Q = c * cycNum Z cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, cycNum Z cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial μ c) Q = c * (cycList Z (classList cls μ ++ Q) : ℝ) := by
  intro O _ _ _ K _ _ ι _ σ Z cls Q
  classical
  set g : (σ →₀ ℕ) → ℝ := fun μ => (cycList Z (classList cls μ ++ Q) : ℝ) with hg
  have key : ∀ (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      cycNum Z cls H Q = ∑ μ ∈ s, AddMonoidAlgebra.coeff H μ * g μ := by
    intro H s hs
    show ∑ μ ∈ H.support, AddMonoidAlgebra.coeff H μ * g μ = _
    refine Finset.sum_subset hs (fun μ _ hμ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hμ, zero_mul]
  have hadd : ∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q := by
    intro H H'
    rw [key (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
      key H (H.support ∪ H'.support) Finset.subset_union_left,
      key H' (H.support ∪ H'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : cycNum Z cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 ∅ (by simp)]
    simp
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c H
    have hs : (MvPolynomial.C c * H).support ⊆ H.support := by
      intro μ hμ
      rw [MvPolynomial.mem_support_iff] at hμ ⊢
      rw [MvPolynomial.coeff_C_mul] at hμ
      exact right_ne_zero_of_mul hμ
    rw [key _ H.support hs, key H H.support subset_rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_C_mul, mul_assoc]
  · intro α s H
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  · intro μ c
    rw [key _ {μ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
end

-- bundled from Development.WeilBound.CoreStatements.IdealCycleValues.CycNumRenameVariables
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycNum_rename_variables : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) := by
  refine ⟨?_, ?_⟩
  · intro O _ _ _ K _ _ ι _ σ σ' e Z cls H Q
    unfold cycNum classList
    rw [BaseChangeColon.evL_eq, BaseChangeColon.evL_eq, BaseChangeColon.evL_rename]
    simp only [BaseChangeColon.classes_mapDomain]
  · intro F _ K _ _ ι _ σ σ' e V cls H Q
    unfold genNum classList
    rw [BaseChangeColon.evL_eq, BaseChangeColon.evL_eq, BaseChangeColon.evL_rename]
    simp only [BaseChangeColon.classes_mapDomain]
end

-- bundled from Development.WeilBound.CoreStatements.IdealCycleValues.GenNumLinearInPolynomial
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.genNum_linear_in_polynomial : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, genNum F V cls (H + H') Q = genNum F V cls H Q + genNum F V cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), genNum F V cls (C c * H) Q = c * genNum F V cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), genNum F V cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, genNum F V cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial μ c) Q = c * (intNumL F V (classList cls μ ++ Q) : ℝ) := by
  intro F _ K _ _ ι _ σ V cls Q
  classical
  set g : (σ →₀ ℕ) → ℝ := fun μ => (intNumL F V (classList cls μ ++ Q) : ℝ) with hg
  have key : ∀ (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      genNum F V cls H Q = ∑ μ ∈ s, AddMonoidAlgebra.coeff H μ * g μ := by
    intro H s hs
    show ∑ μ ∈ H.support, AddMonoidAlgebra.coeff H μ * g μ = _
    refine Finset.sum_subset hs (fun μ _ hμ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hμ, zero_mul]
  have hadd : ∀ H H' : MvPolynomial σ ℝ, genNum F V cls (H + H') Q = genNum F V cls H Q + genNum F V cls H' Q := by
    intro H H'
    rw [key (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
      key H (H.support ∪ H'.support) Finset.subset_union_left,
      key H' (H.support ∪ H'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : genNum F V cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 ∅ (by simp)]
    simp
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c H
    have hs : (MvPolynomial.C c * H).support ⊆ H.support := by
      intro μ hμ
      rw [MvPolynomial.mem_support_iff] at hμ ⊢
      rw [MvPolynomial.coeff_C_mul] at hμ
      exact right_ne_zero_of_mul hμ
    rw [key _ H.support hs, key H H.support subset_rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_C_mul, mul_assoc]
  · intro α s H
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  · intro μ c
    rw [key _ {μ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
end

-- bundled from Development.WeilBound.CoreStatements.IdealCycleValues.HomogeneousSumLinearChangeClasses
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.homogeneous_sum_linear_change_classes : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  intro G _ d n hperm hadd σ σ' _ cls M H m hH Q hQ
  exact (BaseChangeColon.subst_abs d n hperm hadd cls M H m hH Q hQ).trans
    (BaseChangeColon.evL_eq _ _).symm
end

-- bundled from Development.WeilBound.CoreStatements.IdealCycleValues.IntersectionNumbersPermInvariant
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

private theorem intNum_get_eq_of_perm {K : Type} [DecidableEq K] {ι : K → Type} (F : Type) [Field F]
    (P : Ideal (MRing ι F)) {l l' : List (K → ℤ)} (h : l.Perm l') :
    intNum F P l.get = intNum F P l'.get := by
  unfold intNum mixedDiff
  rw [List.ofFn_get, List.ofFn_get]
  haveI : LeftCommutative (diffStep (K := K)) := ⟨fun a b f => by
    funext m
    simp only [diffStep]
    rw [show m - a - b = m - b - a by abel]
    ring⟩
  rw [h.foldr_eq]

theorem BaseChangeColon.intNumL_perm (F : Type) [Field F] (K : Type) [DecidableEq K] (ι : K → Type)
    (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)) (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  unfold intNumL
  exact intNum_get_eq_of_perm F V h

theorem BaseChangeColon.intersection_numbers_perm_invariant : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (MRing ι O) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  refine ⟨fun F _ K _ _ ι _ V l l' h => BaseChangeColon.intNumL_perm F K ι V l l' h, ?_⟩
  intro O _ _ _ K _ _ ι _ Z l l' h
  unfold cycList
  congr 1
  funext W
  unfold vNumL vNum
  exact intNum_get_eq_of_perm _ _ h
end

-- bundled from Development.WeilBound.CoreStatements.IdealCycleValues.ProjIdealIndependentOfBasis
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace BaseChangeColon

section

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {K : Type} {ι : K → Type}
  {N M : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

noncomputable def polyCoord (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) : (Σ o, bundleIdx ι M o) → MvPolynomial (Fin N) Ω
  | ⟨none, l⟩ => ∑ i, X i * C (φ l (w i))
  | ⟨some k, i⟩ => C (y ⟨k, i⟩)

noncomputable def polyCone (F : Type) [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) :
    MRing (bundleIdx ι M) F →+* MvPolynomial (Option K) (MvPolynomial (Fin N) Ω) :=
  eval₂Hom (C.comp ((C : Ω →+* MvPolynomial (Fin N) Ω).comp (algebraMap F Ω)))
    (fun p => C (polyCoord y w φ p) * X p.1)

theorem aeval_polyCoord (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {Φ : Type} [Field Φ] [Algebra Ω Φ] (s : Fin N → Φ)
    (p : Σ o, bundleIdx ι M o) : aeval s (polyCoord y w φ p) = projCoord y w φ s p := by
  obtain ⟨_ | k, i⟩ := p
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [polyCoord, projCoord, map_sum, map_mul, aeval_X, aeval_C]
  · simp only [polyCoord, projCoord, aeval_C]

theorem projIdeal_eq_ker (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {Φ : Type} [Field Φ] [Algebra Ω Φ] (s : Fin N → Φ) :
    projIdeal F y w φ s = RingHom.ker ((MvPolynomial.map
      ((aeval s : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ) : MvPolynomial (Fin N) Ω →+* Φ)).comp
        (polyCone F y w φ)) := by
  unfold projIdeal
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [polyCone]
  · simp [polyCone, aeval_polyCoord]

theorem projCoord_change (y : (Σ k, ι k) → Ω) (w w' : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {Φ : Type} [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ) :
    projCoord y w φ (fun i => ∑ j, t j * algebraMap Ω Φ (w.repr (w' j) i)) = projCoord y w' φ t := by
  funext p
  obtain ⟨_ | k, l⟩ := p
  · simp only [projCoord, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← w.sum_repr (w' j)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  · simp only [projCoord]

theorem projIdeal_le (y : (Σ k, ι k) → Ω) (w w' : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {Φ : Type} [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ)
    (ht : AlgebraicIndependent Ω t) : projIdeal F y w φ t ≤ projIdeal F y w' φ t := by
  have e : projIdeal F y w' φ t =
      projIdeal F y w φ (fun i => ∑ j, t j * algebraMap Ω Φ (w.repr (w' j) i)) := by
    unfold projIdeal
    rw [projCoord_change]
  rw [e, projIdeal_eq_ker, projIdeal_eq_ker]
  intro f hf
  rw [RingHom.mem_ker, RingHom.comp_apply] at hf ⊢
  have h0 : polyCone F y w φ f = 0 :=
    MvPolynomial.map_injective
      ((aeval t : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ) : MvPolynomial (Fin N) Ω →+* Φ) ht
      (by rw [hf, map_zero])
  rw [h0, map_zero]

end

theorem projIdeal_independent_of_basis : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (N M : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (w w' : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t → projIdeal F y w φ t = projIdeal F y w' φ t := by
  intro F _ Ω _ _ K _ _ ι _ y N M E _ _ w w' φ Φ _ _ t ht
  exact le_antisymm (projIdeal_le y w w' φ t ht) (projIdeal_le y w' w φ t ht)

end BaseChangeColon
end

