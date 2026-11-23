module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLinearQuotient

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open IntermediateField IntermediateField.algebraAdjoinAdjoin Module

theorem AdjoinIndepRelfinrank.proof : AdjoinIndepRelfinrank.Statement := by
  intro F Ω _ _ _ L₀ L ι t hle ht
  set L' : IntermediateField L₀ Ω := extendScalars hle with hL'
  set A : IntermediateField L₀ Ω := adjoin L₀ (Set.range t) with hA
  have ht' : AlgebraicIndependent L' t := ht

  let b := Module.Free.chooseBasis L₀ L'

  have hR : LinearIndependent (Algebra.adjoin L₀ (Set.range t)) (algebraMap L' Ω ∘ b) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hmem : ∀ j, ∃ p : MvPolynomial ι L₀, MvPolynomial.aeval t p = (g j : Ω) := fun j => by
      have : (g j : Ω) ∈ (MvPolynomial.aeval t : MvPolynomial ι L₀ →ₐ[L₀] Ω).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval]
        exact (g j).2
      obtain ⟨p, hp⟩ := this
      exact ⟨p, hp⟩
    choose p hp using hmem
    set q : MvPolynomial ι L' :=
      ∑ j ∈ s, MvPolynomial.C (b j) * MvPolynomial.map (algebraMap L₀ L') (p j) with hq
    have hq0 : q = 0 := by
      apply ht'.eq_zero_of_aeval_eq_zero
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hq, map_sum]
      rw [← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap, hp, Subalgebra.smul_def,
        Function.comp_apply, mul_comm]
      rfl
    have hcoef : ∀ m, ∀ j ∈ s, AddMonoidAlgebra.coeff (p j) m = 0 := by
      intro m
      have h := congrArg (AddMonoidAlgebra.coeff · m) hq0
      rw [hq, MvPolynomial.coeff_sum] at h
      simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply] at h
      have hb := (linearIndependent_iff'.mp b.linearIndependent) s (fun j => AddMonoidAlgebra.coeff (p j) m)
      apply hb
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have hpi : p i = 0 := MvPolynomial.ext _ _ fun m => hcoef m i hi
    apply Subtype.ext
    rw [← hp i, hpi, map_zero]
    rfl
  have hK : LinearIndependent A (algebraMap L' Ω ∘ b) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin L₀ (Set.range t)) A).mp hR
  have hdisj : A.LinearDisjoint L' := LinearDisjoint.of_basis_right' b hK

  have hlow : A.restrictScalars F = L₀ ⊔ adjoin F (Set.range t) := by
    rw [hA, restrictScalars_adjoin_eq_sup]
  have hle' : A ≤ (adjoin L' (A : Set Ω)).restrictScalars L₀ := subset_adjoin L' (A : Set Ω)
  have hup : ((adjoin L' (A : Set Ω)).restrictScalars L₀).restrictScalars F =
      L ⊔ adjoin F (Set.range t) := by
    refine (restrictScalars_adjoin_eq_sup F L (A : Set Ω)).trans ?_
    have hAF : adjoin F (A : Set Ω) = L₀ ⊔ adjoin F (Set.range t) := by
      rw [← hlow]
      exact adjoin_self F (A.restrictScalars F)
    rw [hAF, ← sup_assoc, sup_eq_left.mpr hle]
  have hrel : IntermediateField.relfinrank (L₀ ⊔ adjoin F (Set.range t)) (L ⊔ adjoin F (Set.range t)) =
      finrank A (extendScalars hle') := by
    rw [← hlow, ← hup]
    exact relfinrank_eq_finrank_of_le hle'
  rw [hrel, relfinrank_eq_finrank_of_le hle]
  by_cases hfin : Module.Finite L₀ L'
  · have : Algebra.IsAlgebraic L₀ L' := Algebra.IsAlgebraic.of_finite L₀ L'
    have := hdisj.adjoin_rank_eq_rank_right_of_isAlgebraic_right
    exact congrArg Cardinal.toNat this
  · rw [finrank_of_not_finite hfin]
    have : Module.Free A (extendScalars hle') :=
      Module.Free.of_divisionRing (K := A) (V := extendScalars hle')
    apply finrank_of_not_finite
    intro hfin'
    apply hfin
    let v : _ → extendScalars hle' := fun j => ⟨algebraMap L' Ω (b j), by
      exact IntermediateField.algebraMap_mem (adjoin L' (A : Set Ω)) (b j)⟩
    have hv : LinearIndependent A v := by
      apply LinearIndependent.of_comp (extendScalars hle').val.toLinearMap
      exact hK
    have := hv.finite_of_isNoetherian
    exact Module.Finite.of_basis b
end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartPrimElt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

theorem ChartPrimElt.proof : ChartPrimElt.Statement := by
  intro Φ _ _ Φ' _ _ Q _ r hfin
  set L := IntermediateField.adjoin Φ (Set.range r) with hL
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Φ L
  have hint : IsIntegral Φ α := IsIntegral.of_finite Φ α
  have hmemL : ∀ q, r q ∈ L := fun q => IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩
  have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
    rintro _ ⟨q, rfl⟩
    exact (IntermediateField.isAlgebraic_iff (x := (⟨r q, hmemL q⟩ : L))).1
      (Algebra.IsAlgebraic.isAlgebraic _)
  have hmem : (α : Φ') ∈ Algebra.adjoin Φ (Set.range r) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact α.2
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  obtain ⟨τ, hτ0⟩ := hmem
  have hτ : MvPolynomial.aeval r τ = (α : Φ') := hτ0
  have hm : minpoly Φ (MvPolynomial.aeval r τ) = minpoly Φ α := by
    rw [hτ]
    exact minpoly.algHom_eq L.val Subtype.val_injective α
  have hg : ∀ q, ∃ p : Φ[X], aeval α p = (⟨r q, hmemL q⟩ : L) := by
    intro q
    have h1 : (⟨r q, hmemL q⟩ : L) ∈ IntermediateField.adjoin Φ ({α} : Set L) := by rw [hα]; trivial
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨p, hp⟩ := h1
    exact ⟨p, hp⟩
  choose g hg using hg
  have hgθ : ∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q := by
    intro q
    rw [hτ, show (α : Φ') = L.val α from rfl, Polynomial.aeval_algHom_apply, hg q]
    rfl
  have hirr : Irreducible (minpoly Φ (MvPolynomial.aeval r τ)) := by
    rw [hm]
    exact minpoly.irreducible hint
  refine ⟨τ, g, ?_⟩
  have hsep : IsCoprime (minpoly Φ (MvPolynomial.aeval r τ))
      (derivative (minpoly Φ (MvPolynomial.aeval r τ))) := hirr.separable
  obtain ⟨a, b, hab⟩ := hsep
  refine ⟨b, ?_, hgθ, ⟨-a, by linear_combination hab⟩, ?_, ?_⟩
  · rw [hm]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq Φ α).1 hα
  · apply minpoly.dvd
    have hfun : (fun q => aeval (MvPolynomial.aeval r τ) (g q)) = r := funext hgθ
    rw [map_sub, aeval_X, MvPolynomial.comp_aeval_apply, hfun, sub_self]
  · intro q hq
    have hnd : ¬ minpoly Φ (MvPolynomial.aeval r τ) ∣ g q := by
      rintro ⟨c, hc⟩
      apply hq
      rw [← hgθ q, hc, map_mul, minpoly.aeval, zero_mul]
    obtain ⟨a', b', hab'⟩ := (hirr.coprime_iff_not_dvd).2 hnd
    exact ⟨b', ⟨-a', by linear_combination hab'⟩⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFIntZeroMixed
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo

variable {D : ℕ}

theorem sum_neg_one_pow_superset_eq_zero (p : Finset (Fin D) → Prop) [DecidablePred p] (a : Fin D)
    (hp : ∀ T, p (insert a T) ↔ p T) (X : ℂ) :
    ∑ T : Finset (Fin D), (-1 : ℂ) ^ (D - T.card) * (if p T then X else 0) = 0 := by
  rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ a),
    Finset.sum_powerset_insert (Finset.notMem_erase a _), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun T hT => ?_
  have haT : a ∉ T := fun h => Finset.notMem_erase a _ (Finset.mem_powerset.mp hT h)
  have hlt : T.card < D := by
    have := Finset.card_le_card (Finset.mem_powerset.mp hT)
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin] at this
    have : 0 < D := Fin.pos a
    omega
  rw [Finset.card_insert_of_notMem haT]
  have hD : D - T.card = (D - (T.card + 1)) + 1 := by omega
  by_cases h : p T
  · rw [if_pos h, if_pos ((hp T).mpr h), hD, pow_succ]
    ring
  · rw [if_neg h, if_neg fun h' => h ((hp T).mp h')]
    ring

theorem mixedDisc_eq_zero_of_cols (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (S C : Finset (Fin D))
    (hcard : D < C.card + S.card) (hB : ∀ k ∈ S, ∀ j ∈ C, ∀ i, B k i j = 0) : mixedDisc B = 0 := by
  classical
  unfold mixedDisc
  refine mul_eq_zero_of_right _ ?_
  have hdet : ∀ T : Finset (Fin D), (∑ k ∈ T, B k).det = ∑ σ : Equiv.Perm (Fin D), ∑ f : Fin D → Fin D,
      (if ∀ i, f i ∈ T then (Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i else 0) := by
    intro T
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.sum_apply]
    rw [Finset.prod_univ_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]
    have hpi : Fintype.piFinset (fun _ : Fin D => T) = Finset.univ.filter (fun f : Fin D → Fin D => ∀ i, f i ∈ T) := by
      ext f; simp [Fintype.mem_piFinset]
    rw [hpi, Finset.sum_filter]
  simp_rw [hdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun f _ => ?_
  by_cases hf : Function.Surjective f
  · have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hf, hf⟩
    have hpre : (S.preimage f hbij.1.injOn).card = S.card := by
      rw [Finset.card_preimage]
      congr 1
      exact Finset.filter_true_of_mem fun x _ => hf x
    obtain ⟨i, hi⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ C)
      (Finset.subset_univ (S.preimage f hbij.1.injOn)) (by rw [hpre, Finset.card_univ, Fintype.card_fin]; exact hcard)
    rw [Finset.mem_inter, Finset.mem_preimage] at hi
    have h0 : ∏ i, B (f i) (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (hB _ hi.2 _ hi.1 _)
    refine Finset.sum_eq_zero fun T _ => ?_
    simp [h0]
  · obtain ⟨a, ha⟩ := not_forall.mp hf
    push Not at ha
    have := sum_neg_one_pow_superset_eq_zero (fun T => ∀ i, f i ∈ T) a
      (fun T => ⟨fun h i => (Finset.mem_insert.mp (h i)).resolve_left (ha i), fun h i => Finset.mem_insert_of_mem (h i)⟩)
      ((Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i)
    exact this

theorem mixedDisc_mul_right (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => A k * P) = mixedDisc A * P.det := by
  unfold mixedDisc
  simp_rw [← Finset.sum_mul, Matrix.det_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T _ => by ring

theorem mixedDisc_map_star (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
  unfold mixedDisc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_mul, map_pow, map_neg, map_one, RingHom.map_det]
    congr 2
    ext i j
    simp [Matrix.sum_apply]

theorem mixedDisc_eq_zero_of_ker (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (V : Submodule ℂ (Fin D → ℂ))
    (S : Finset (Fin D)) (hdim : D < Module.finrank ℂ V + S.card) (hA : ∀ k ∈ S, ∀ x ∈ V, A k *ᵥ x = 0) :
    mixedDisc A = 0 := by
  classical
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl V
  set b0 := ((Module.finBasis ℂ V).prod (Module.finBasis ℂ U)).map (Submodule.prodEquivOfIsCompl V U hU) with hb0
  have hcardι : Fintype.card (Fin (Module.finrank ℂ V) ⊕ Fin (Module.finrank ℂ U)) = D := by
    rw [← Module.finrank_eq_card_basis b0, Module.finrank_fin_fun]
  set e := Fintype.equivFinOfCardEq hcardι
  set b := b0.reindex e
  have hbV : ∀ i, b (e (Sum.inl i)) ∈ V := by
    intro i
    simp [b, hb0, Basis.reindex_apply, Basis.map_apply, Basis.prod_apply]
  set P : Matrix (Fin D) (Fin D) ℂ := (Pi.basisFun ℂ (Fin D)).toMatrix b
  have hP : IsUnit P.det := by
    rw [← Basis.det_apply]
    exact (Pi.basisFun ℂ (Fin D)).isUnit_det b
  set C := Finset.univ.image fun i => e (Sum.inl i)
  have hC : C.card = Module.finrank ℂ V := by
    rw [Finset.card_image_of_injective (f := fun i => e (Sum.inl i)) _
      (fun x y h => Sum.inl_injective (e.injective h)), Finset.card_univ, Fintype.card_fin]
  have hcol : ∀ k ∈ S, ∀ j ∈ C, ∀ i, (A k * P) i j = 0 := by
    intro k hk j hj i
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hj
    have h := congrFun (hA k hk _ (hbV l)) i
    simpa [P, Matrix.mul_apply, Matrix.mulVec, dotProduct, Basis.toMatrix_apply] using h
  have h := mixedDisc_eq_zero_of_cols (fun k => A k * P) S C (by rw [hC]; exact hdim) hcol
  rw [mixedDisc_mul_right] at h
  exact (mul_eq_zero.mp h).resolve_right hP.ne_zero

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFinrankAdjoinRange
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem FinrankAdjoinRange.proof : FinrankAdjoinRange.Statement := by
  intro F Φ Ω _ _ _ _ _ _ _ S
  set f := IsScalarTower.toAlgHom F Φ Ω
  set Φ₁ : IntermediateField F Ω := f.fieldRange
  let i : Φ ≃ₐ[F] Φ₁ := AlgEquiv.ofInjectiveField f
  have hi : (algebraMap Φ Ω : Φ → Ω) = (algebraMap Φ₁ Ω) ∘ i := by
    funext x; rfl

  have hres : (IntermediateField.adjoin Φ S).restrictScalars F =
      (IntermediateField.adjoin Φ₁ S).restrictScalars F :=
    IntermediateField.restrictScalars_adjoin_of_algEquiv i hi S

  have hle : Φ₁ ≤ Φ₁ ⊔ IntermediateField.adjoin F S := le_sup_left
  have hext : IntermediateField.extendScalars hle = IntermediateField.adjoin Φ₁ S := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.extendScalars_restrictScalars,
      IntermediateField.restrictScalars_adjoin_eq_sup]
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext]

  let j : IntermediateField.adjoin Φ S ≃+* IntermediateField.adjoin Φ₁ S :=
    (IntermediateField.equivOfEq hres).toRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv j ?_
  ext x
  rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLinearQuotient
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial

theorem LinearQuotient.proof : LinearQuotient.Statement := by
  intro F _ σ _ S hS
  classical

  let ℓ : (σ → F) →ₗ[F] MvPolynomial σ F := Fintype.linearCombination F (fun s => (X s : MvPolynomial σ F))
  have hSrange : ∀ f ∈ S, f ∈ LinearMap.range ℓ := by
    intro f hf
    rw [Fintype.range_linearCombination, ← homogeneousSubmodule_one_eq_span_X]
    exact hS f hf
  let L : Submodule F (σ → F) := (Submodule.span F S).comap ℓ
  let b := Module.finBasis F ((σ → F) ⧸ L)
  let r := Module.finrank F ((σ → F) ⧸ L)
  let θ : (σ → F) →ₗ[F] MvPolynomial (Fin r) F :=
    Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F)) ∘ₗ
      (b.equivFun.toLinearMap ∘ₗ L.mkQ)
  have hθ : ∀ v, θ v = ∑ i, b.equivFun (L.mkQ v) i • (X i : MvPolynomial (Fin r) F) := fun v => rfl
  let φ : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin r) F := aeval (fun s => θ (Pi.single s 1))

  have key : ∀ c, φ (ℓ c) = θ c := by
    have : φ.toLinearMap ∘ₗ ℓ = θ := by
      refine LinearMap.pi_ext (fun s x => ?_)
      have hx : (Pi.single s x : σ → F) = x • Pi.single s (1 : F) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ℓ,
        Fintype.linearCombination_apply_single, map_smul, φ, aeval_X]
      rw [hx, map_smul]
    exact fun c => LinearMap.congr_fun this c

  let lift : Fin r → (σ → F) := fun i => (L.mkQ_surjective (b i)).choose
  have hlift : ∀ i, L.mkQ (lift i) = b i := fun i => (L.mkQ_surjective (b i)).choose_spec
  let ψ : MvPolynomial (Fin r) F →ₐ[F] MvPolynomial σ F := aeval (fun i => ℓ (lift i))
  have hφψ : φ.comp ψ = AlgHom.id F _ := by
    refine MvPolynomial.algHom_ext (fun i => ?_)
    have he : b.equivFun (b i) = Pi.single i 1 := by
      funext j
      rw [Module.Basis.equivFun_self, Pi.single_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    simp only [AlgHom.comp_apply, ψ, aeval_X, key, AlgHom.id_apply]
    rw [show θ (lift i) = Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F))
      (b.equivFun (L.mkQ (lift i))) from rfl, hlift, he, Fintype.linearCombination_apply_single, one_smul]
  have hψθ : ∀ v, ψ (θ v) = ℓ (∑ i, b.equivFun (L.mkQ v) i • lift i) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hθ, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, map_smul, aeval_X]
  have hspan : Submodule.span F S ≤ (Ideal.span S).restrictScalars F :=
    Submodule.span_le.mpr (fun f hf => Ideal.subset_span hf)
  refine ⟨r, φ, fun p => ⟨ψ p, by simpa using AlgHom.congr_fun hφψ p⟩, ?_, fun s => ?_⟩
  · apply le_antisymm
    · have hmk : (Ideal.Quotient.mkₐ F (Ideal.span S)).comp (ψ.comp φ) = Ideal.Quotient.mkₐ F (Ideal.span S) := by
        refine MvPolynomial.algHom_ext (fun s => ?_)
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq]
        have h1 : φ (X s) = θ (Pi.single s 1) := aeval_X _ _
        rw [h1, hψθ]
        have hmem : (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) - Pi.single s 1 ∈ L := by
          rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
          have : (Submodule.Quotient.mk (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) : (σ → F) ⧸ L) =
              ∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • b i := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [← Submodule.mkQ_apply, map_sum]
            simp only [map_smul, hlift]
          rw [this, b.sum_equivFun, Submodule.mkQ_apply, sub_self]
        have h2 := hspan hmem
        rw [map_sub] at h2
        have h3 : ℓ (Pi.single s 1) = X s := by
          simp [ℓ]
        rwa [h3] at h2
      intro f hf
      rw [RingHom.mem_ker] at hf
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := AlgHom.congr_fun hmk f
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [← this, hf, map_zero, map_zero]
    · refine Ideal.span_le.mpr (fun f hf => ?_)
      obtain ⟨c, rfl⟩ := hSrange f hf
      have hc : c ∈ L := Submodule.subset_span hf
      show φ (ℓ c) = 0
      rw [key, hθ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero L).mpr hc]
      simp
  · rw [← mem_homogeneousSubmodule, homogeneousSubmodule_one_eq_span_X, ← Fintype.range_linearCombination]
    refine ⟨b.equivFun (L.mkQ (Pi.single s 1)), ?_⟩
    rw [show φ (X s) = θ (Pi.single s 1) from aeval_X _ _]
    rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocAwaySpec
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter


open Classical in
theorem LocAwaySpec.proof : LocAwaySpec.Statement := by
  intro R _ Φ _ φ S hrep
  choose f g hg hfg using hrep
  have hE0 : IsUnit (φ (∏ c ∈ S, g c)) := by
    rw [map_prod]
    exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
  refine ⟨∏ c ∈ S, g c, hE0, ?_, ?_⟩
  · intro c hc
    set E := ∏ d ∈ S, g d with hEdef
    have hE : IsUnit (φ E) := by
      rw [hEdef, map_prod]
      exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
    have hunitE : IsUnit (algebraMap R (Localization.Away E) E) :=
      IsLocalization.Away.algebraMap_isUnit E
    have hu : IsUnit (algebraMap R (Localization.Away E) (g c)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem g hc)) hunitE
    refine ⟨algebraMap R (Localization.Away E) (f c) * ↑hu.unit⁻¹, ?_⟩
    have h1 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit = φ (g c) := by
      rw [IsUnit.unit_spec, IsLocalization.Away.lift_eq]
    have h2 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit⁻¹ = (φ (g c))⁻¹ := by
      rw [← h1, ← map_units_inv]
    rw [map_mul, IsLocalization.Away.lift_eq, h2, ← div_eq_mul_inv]
    exact (hfg c).symm
  · intro B _ ψ hψ hker z hz
    rw [RingHom.mem_ker] at hz ⊢
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (∏ c ∈ S, g c)) z
    have hsφ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hE0 : Localization.Away (∏ c ∈ S, g c) →+* Φ) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, hz, zero_mul] at hsφ
    have ha : ψ a = 0 := hker (RingHom.mem_ker.mpr hsφ.symm)
    have hsψ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hψ :
      Localization.Away (∏ c ∈ S, g c) →+* B) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, ha] at hsψ
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
    have hsu : IsUnit (ψ (s : R)) := by
      rw [← hn, map_pow]
      exact hψ.pow n
    exact (hsu.mul_left_eq_zero).mp hsψ

end GroundTheory.Heights₂.Heights.Inter
end
end

