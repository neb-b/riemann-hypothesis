module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IsClosedCongruenceSubgroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.NonDeg

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.OrbitMeasure
section
noncomputable section

namespace PI.LocMassTypM

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
open PI.LocMassTypW

theorem orbit_measure : OmMeas := by
  intro F E _ _ _ _ _ σ n J ψ v r g P P' Λ T T' κ μG μS0 μS0' hyp
  obtain ⟨-, -, -, hSD, -, hg, hgv, -⟩ := hyp
  have hKv : IsClosed (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdKv.isClosed_Kv σ J v Λ hSD
  have hK1 : IsClosed (K1 σ J v Λ g P) := isClosed_congruence_subgroup σ J v Λ hSD hg P

  have hK1' : ∀ k : HA (Fv F v) σ J, IsClosed {c | k⁻¹ * c * κ⁻¹ ∈ K1 σ J v Λ g P} := fun k =>
    hK1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  exact ⟨measurableSet_omTyp v Λ σ J hSD hg hgv r, LocMassOrdKv.kv_measurableSet σ J v Λ hSD,
    hK1.measurableSet, measurableSet_image_closed σ J v hKv _,
    fun k => measurableSet_image_closed σ J v (hK1' k) _⟩

end PI.LocMassTypM
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.RightInvariantCompact
section
noncomputable section

namespace PI.LocMassTypR

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
open PI.LocMassTypW

theorem kv_mul_right_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) {κ c : HA (Fv F v) σ J}
    (hκ : κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    c * κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ↔ c ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  by
  unfold Formalism.L2.SG.TypedSets.Kv at hκ ⊢
  simp only [Set.mem_setOf_eq, map_mul] at hκ ⊢
  exact Subgroup.mul_mem_cancel_right _ hκ

theorem right_invariant_compact : RightK := by
  intro F E _ _ _ _ _ σ n J ψ v Λ μG _ hSD _ _ hLat hH κ hκ A _
  haveI := hH
  haveI : LocallyCompactSpace (HA (Fv F v) σ J) := PI.LocMassTypM.lc_HA σ J v
  haveI : SecondCountableTopology (HA (Fv F v) σ J) := PI.LocMassTypM.sc_HA σ J v
  have hKc : IsCompact (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdND.isCompact_Kv σ J v Λ hSD hLat.1
  have hKo : IsOpen (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdND.isOpen_Kv σ J v Λ hSD hLat.1
  set e : HA (Fv F v) σ J ≃ᵐ HA (Fv F v) σ J := MeasurableEquiv.mulRight κ with he
  have hcoe : ∀ x, e x = x * κ := fun x => rfl
  set μ' : Measure (HA (Fv F v) σ J) := μG.map e with hμ'
  have hμ'app : ∀ s, μ' s = μG ((fun c => c * κ) ⁻¹' s) := fun s => by
    rw [hμ', MeasurableEquiv.map_apply]
    rfl
  haveI : μ'.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, hμ'app, hμ'app]
    have hpre : (fun c => c * κ) ⁻¹' ((fun x => g * x) ⁻¹' s) =
        (fun x => g * x) ⁻¹' ((fun c => c * κ) ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage, mul_assoc]
    rw [hpre, ← Measure.map_apply (measurable_const_mul g) ((measurable_mul_const κ) hs),
      MeasureTheory.map_mul_left_eq_self μG g]
  haveI : IsFiniteMeasureOnCompacts μ' := by
    refine ⟨fun C hC => ?_⟩
    rw [hμ'app]
    have hC' : IsCompact ((fun c => c * κ) ⁻¹' C) :=
      (Homeomorph.mulRight κ).isCompact_preimage.mpr hC
    exact hC'.measure_lt_top
  have hsmul := Measure.isMulLeftInvariant_eq_smul μ' μG
  have hKpre : (fun c => c * κ) ⁻¹' (Formalism.L2.SG.TypedSets.Kv σ J Λ v) = Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
    ext c
    exact kv_mul_right_iff σ J v Λ hκ
  have hm0 : μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) ≠ 0 := hKo.measure_ne_zero μG ⟨κ, hκ⟩
  have hmt : μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) ≠ ⊤ := hKc.measure_lt_top.ne
  have hc1 : ((Measure.haarScalarFactor μ' μG : NNReal) : ENNReal) = 1 := by
    have h := congrArg (fun m : Measure (HA (Fv F v) σ J) => m (Formalism.L2.SG.TypedSets.Kv σ J Λ v)) hsmul
    simp only [Measure.smul_apply, hμ'app, hKpre, ENNReal.smul_def, smul_eq_mul] at h
    have h2 : ((Measure.haarScalarFactor μ' μG : NNReal) : ENNReal) * μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) =
        1 * μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := by rw [one_mul]; exact h.symm
    first
      | exact (ENNReal.mul_left_inj hm0 hmt).mp h2
      | exact ENNReal.mul_right_cancel hm0 hmt h2
      | exact (ENNReal.mul_eq_mul_right hm0 hmt).mp h2
  rw [← hμ'app, hsmul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc1, one_mul]

end PI.LocMassTypR
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SaturatedSplitLattice
section
noncomputable section

namespace PI.LocMassTypW.WSatP

open Matrix

theorem leftInv_field {K : Type*} [Field K] {n m : ℕ} (A : Matrix (Fin n) (Fin m) K)
    (h : ∀ t, A *ᵥ t = 0 → t = 0) : ∃ L : Matrix (Fin m) (Fin n) K, L * A = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' A) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    exact h t (by simpa [Matrix.toLin'_apply] using ht)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' A, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem leftInv_lift {O : Type*} [CommRing O] [IsLocalRing O] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) O)
    (h : ∃ L : Matrix (Fin m) (Fin n) (IsLocalRing.ResidueField O),
      L * A.map (IsLocalRing.residue O) = 1) :
    ∃ L : Matrix (Fin m) (Fin n) O, L * A = 1 := by
  obtain ⟨Lb, hLb⟩ := h
  let L0 : Matrix (Fin m) (Fin n) O :=
    Matrix.of fun i j => Classical.choose (IsLocalRing.residue_surjective (Lb i j))
  have hL0 : L0.map (IsLocalRing.residue O) = Lb :=
    Matrix.ext fun i j => Classical.choose_spec (IsLocalRing.residue_surjective (Lb i j))
  have hdet : IsUnit (L0 * A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
      Matrix.map_mul, hL0, hLb, Matrix.det_one]
    exact one_ne_zero
  refine ⟨(L0 * A)⁻¹ * L0, ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]

end PI.LocMassTypW.WSatP

namespace PI.LocMassTypW

open Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem saturated_split_lattice : SatSplit := by
  intro F _ _ v n m A hsat
  apply WSatP.leftInv_lift
  apply WSatP.leftInv_field
  intro tb htb
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, tb j ≠ 0 := by
    by_contra hall
    exact hne (funext fun k => not_not.mp fun h' => hall ⟨k, h'⟩)
  let t : Fin m → v.adicCompletionIntegers F := fun j =>
    Classical.choose (IsLocalRing.residue_surjective (tb j))
  have ht : ∀ j, IsLocalRing.residue _ (t j) = tb j := fun j =>
    Classical.choose_spec (IsLocalRing.residue_surjective (tb j))
  have htj : IsUnit (t j) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [ht]; exact hj)
  have hAt : ∀ i, (A *ᵥ t) i ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro i
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_mulVec]
    have : (IsLocalRing.residue _ ∘ t) = tb := funext ht
    rw [this, htb]
    rfl
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  let I : Ideal (v.adicCompletionIntegers F) := Ideal.span (insert x (Set.range (A *ᵥ t)))
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmemI : ∀ y ∈ insert x (Set.range (A *ᵥ t)), ∃ q, q * c = y := by
    intro y hy
    have : y ∈ I := Ideal.subset_span hy
    rw [hc] at this
    exact Ideal.mem_span_singleton'.mp this
  have hcm : c ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    have : c ∈ I := by rw [hc]; exact Submodule.mem_span_singleton_self c
    refine (Ideal.span_le.mpr ?_) this
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact (IsLocalRing.mem_maximalIdeal _).mpr hx.not_isUnit
    · exact hAt i
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hmemI x (Set.mem_insert _ _)
    rw [mul_zero] at hq
    exact hx.ne_zero hq.symm
  have hcK : (c : v.adicCompletion F) ≠ 0 := by
    intro h0; exact hc0 (Subtype.ext h0)
  let f := (v.adicCompletionIntegers F).subtype
  let t' : Fin m → v.adicCompletion F := (c : v.adicCompletion F)⁻¹ • (f ∘ t)
  have hint : ∀ i, (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t') i ∈
      v.adicCompletionIntegers F := by
    intro i
    obtain ⟨q, hq⟩ := hmemI ((A *ᵥ t) i) (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    have e1 : (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t') i =
        (c : v.adicCompletion F)⁻¹ * f ((A *ᵥ t) i) := by
      rw [Matrix.mulVec_smul, RingHom.map_mulVec]
      rfl
    rw [e1, ← hq, map_mul]
    have e2 : (c : v.adicCompletion F)⁻¹ * (f q * f c) = f q := by
      change (c : v.adicCompletion F)⁻¹ * (f q * (c : v.adicCompletion F)) = f q
      field_simp
    rw [e2]
    exact q.2
  have hj' := hsat t' hint j
  have e3 : t' j = (c : v.adicCompletion F)⁻¹ * (t j : v.adicCompletion F) := rfl
  rw [e3] at hj'
  set s : v.adicCompletionIntegers F := ⟨_, hj'⟩ with hs
  have hts : t j = c * s := by
    apply Subtype.ext
    change (t j : v.adicCompletion F) = (c : v.adicCompletion F) * ((c : v.adicCompletion F)⁻¹ * (t j : v.adicCompletion F))
    field_simp
  have : t j ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [hts]; exact Ideal.mul_mem_right _ _ hcm
  exact ((IsLocalRing.mem_maximalIdeal _).mp this) htj

end PI.LocMassTypW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SplitDecomp
section
noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

theorem hform_eq_dot (σ : A →+* A) (M : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform σ M x y = (fun i => σ (x i)) ⬝ᵥ (M *ᵥ y) := by
  show (∑ i, ∑ j, σ (x i) * M i j * y j) = ∑ i, σ (x i) * ∑ j, M i j * y j
  simp only [Finset.mul_sum, mul_assoc]

theorem hform_mulVec (σ : A →+* A) (J M : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have hx : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    show σ (∑ j, M i j * x j) = ∑ j, σ (M i j) * σ (x j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
  have hc : Formalism.UG.cT σ M = (M.map σ)ᵀ := rfl
  rw [hform_eq_dot, hform_eq_dot, hx, hc, ← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, vecMul_transpose]

theorem hform_ext (σ : A →+* A) (M₁ M₂ : Matrix (Fin n) (Fin n) A)
    (h : ∀ x y, Formalism.UG.hform σ M₁ x y = Formalism.UG.hform σ M₂ x y) : M₁ = M₂ := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  first
    | simpa [Formalism.UG.hform, Pi.single_apply, apply_ite σ] using hij
    | (simp only [Formalism.UG.hform, Pi.single_apply, apply_ite σ, map_one, map_zero, ite_mul, one_mul,
        zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at hij
       exact hij)

end Generic

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem sc_mul (a b : Fv F v) : sc (E := E) v (a * b) = sc (E := E) v a * sc (E := E) v b := by
  simp only [sc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := rfl

theorem split_decomp {e : Fv F v ⊗[F] E} {π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v}
    (h1 : ∀ x, x * e = sc (E := E) v (π₁ x) * e) (h2 : ∀ x, x * (1 - e) = sc (E := E) v (π₂ x) * (1 - e))
    (x : Fv F v ⊗[F] E) : x = sc (E := E) v (π₁ x) * e + sc (E := E) v (π₂ x) * (1 - e) := by
  linear_combination h1 x + h2 x

theorem split_ext {e : Fv F v ⊗[F] E} {π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v}
    (h1 : ∀ x, x * e = sc (E := E) v (π₁ x) * e) (h2 : ∀ x, x * (1 - e) = sc (E := E) v (π₂ x) * (1 - e))
    {x y : Fv F v ⊗[F] E} (hx : π₁ x = π₁ y) (hy : π₂ x = π₂ y) : x = y := by
  rw [split_decomp v h1 h2 x, split_decomp v h1 h2 y, hx, hy]

end Split

end PI.LocMassTypW
end
end

