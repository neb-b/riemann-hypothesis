module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
public import GroundTheory.GlobalFields.IdeleGroups.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicSL2.EqSl2RatMulOfGl2RatSmulAdelicSL2IdeleMapEq
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

private theorem us_pos (x : US) : ((x : (A ℚ)ˣ) : IdeleGroup ℚ) ∈ RationalIdeles.positiveSubgroup := by
  obtain ⟨h1, h2⟩ := x.2
  set t : IdeleGroup ℚ := (x : (A ℚ)ˣ) with ht
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨?_, ?_⟩
  · change IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ
    refine (mem_finiteIntegralUnits ℚ).2 fun v => ?_
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rw [RationalIdeles.coe_realPart]
    have h1' : (t : NumberField.AdeleRing (𝓞 ℚ) ℚ).1 = 1 := h1
    rw [h1', map_one]
    exact one_pos

theorem UpperTheory.eq_sl2Rat_mul_of_gl2Rat_smul_adelicSL2IdeleMap_eq :
    ∀ (γ : Ga) (p q : G1 ℚ × US), γ • pm p = pm q → q.2 = p.2 ∧ ∃ s : SpecialLinearGroup (Fin 2) ℚ, q.1 = ratS ℚ s * p.1 ∧ ((γ : GG) : GL (Fin 2) (A ℚ)) = gl (ratS ℚ s) := by
  intro γ p q h
  obtain ⟨r, hr⟩ := γ.2
  have h1 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (gl p.1 * dM (p.2 : (A ℚ)ˣ)) = gl q.1 * dM (q.2 : (A ℚ)ˣ) := by
    rw [hr]
    exact congrArg Subtype.val h
  have hdet : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) =
      IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) := by
    refine Units.ext ?_
    rw [GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
    exact (RingHom.map_det (algebraMap ℚ _) (r : Matrix (Fin 2) (Fin 2) ℚ)).symm
  have h2 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) * (p.2 : (A ℚ)ˣ) = (q.2 : (A ℚ)ˣ) := by
    have := congrArg (GroundTheory.Automorphic.AdelicGLn.det ℚ 2) h1
    rwa [map_mul, det_el, det_el, hdet] at this
  have h3 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = ((q.2 * p.2⁻¹ : US) : (A ℚ)ˣ) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← h2, mul_inv_cancel_right]
  have h4 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = 1 := by
    have hm : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) ∈
        RationalIdeles.positiveSubgroup ⊓ (IdeleGroup.diagonal ℚ).range :=
      ⟨h3 ▸ us_pos _, ⟨_, rfl⟩⟩
    rw [RationalIdeles.positiveSubgroup_inf_diagonal_range] at hm
    exact hm
  have h5 : (q.2 : (A ℚ)ˣ) = (p.2 : (A ℚ)ˣ) := by rw [← h2, h4, one_mul]
  have h6 : (r : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    have := congrArg Units.val h4
    rw [IdeleGroup.coe_diagonal, Units.val_one] at this
    apply NumberField.AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ
    rw [map_one]
    exact this
  let s : SpecialLinearGroup (Fin 2) ℚ := ⟨r.val, h6⟩
  have h7 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r = gl (ratS ℚ s) := by
    apply Units.ext
    ext i j
    rfl
  refine ⟨Subtype.ext h5, s, ?_, hr.symm.trans h7⟩
  rw [h5, h7, ← mul_assoc] at h1
  have h8 : gl (ratS ℚ s) * gl p.1 = gl q.1 := mul_right_cancel h1
  apply Subtype.ext
  have := congrArg Units.val h8
  exact this.symm
end

-- bundled from Development.AutomorphicArithmetic.AdelicSL2.ExistsGl2RatSmulMemRangeAdelicSL2IdeleMap
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

private lemma eq_one_of_mul' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma mem_UU_of_pos {y : IdeleGroup ℚ} (hy : y ∈ RationalIdeles.positiveSubgroup)
    (hm : (IdeleGroup.ideleModule ℚ y : ℝ) = 1) : y ∈ UU := by
  obtain ⟨h1, h2⟩ := RationalIdeles.mem_positiveSubgroup.1 hy
  rw [IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one,
    IdeleGroup.infiniteModule, Fintype.prod_unique,
    InfinitePlace.IsReal.mult_eq_one (RationalIdeles.isReal_infinitePlace default), pow_one] at hm
  refine ⟨?_, fun v => ?_⟩
  · have hn : ‖(RationalIdeles.realPart y : ℝ)‖ = 1 := by
      rw [RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply, ← hm]
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero
        (map_zero _) _
    rw [Real.norm_eq_abs, abs_of_pos h2, RationalIdeles.coe_realPart] at hn
    exact RationalIdeles.realEquiv.injective (hn.trans (map_one _).symm)
  · obtain ⟨ha, hb⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v
    refine eq_one_of_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) ?_
    rw [← map_mul]
    have h := congrArg (fun x : NumberField.AdeleRing (𝓞 ℚ) ℚ => x.2 v) (Units.mul_inv y)
    have h' : (y : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v *
        ((y⁻¹ : IdeleGroup ℚ) : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v = 1 := h
    exact (congrArg _ h').trans (map_one _)

theorem UpperTheory.exists_gl2Rat_smul_mem_range_adelicSL2IdeleMap :
    ∀ x : GG, ∃ γ : Ga, γ • x ∈ Set.range pm := by
  intro x
  obtain ⟨⟨q, y⟩, hq⟩ := RationalIdeles.mulMap_bijective.2
    (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ)))
  rw [RationalIdeles.mulMap_apply] at hq
  dsimp only at hq
  have hx := GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2
  rw [← hq, map_mul, IdeleGroup.ideleModule_diagonal, one_mul] at hx
  have hy : (y : IdeleGroup ℚ) ∈ UU := mem_UU_of_pos y.2 hx
  obtain ⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.det r = q⁻¹ := by
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, ((q⁻¹ : ℚˣ) : ℚ)] ?_, Units.ext ?_⟩
    · simp [Matrix.det_fin_two_of]
    · simp [Matrix.det_fin_two_of]
  have h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) =
      IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) := by
    refine Units.ext ?_
    rw [GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
    exact (RingHom.map_det (algebraMap ℚ (NumberField.AdeleRing (𝓞 ℚ) ℚ))
      (r : Matrix (Fin 2) (Fin 2) ℚ)).symm
  refine ⟨⟨⟨GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r,
    GroundTheory.Automorphic.Reduction.rationalGL_le_normOneGL ⟨r, rfl⟩⟩, ⟨r, rfl⟩⟩, ?_⟩
  rw [range_pm]
  change GroundTheory.Automorphic.AdelicGLn.det ℚ 2
    (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (x : GL (Fin 2) (A ℚ))) ∈ UU
  rw [map_mul, h, hr, ← hq, map_inv, inv_mul_cancel_left]
  exact hy
end

-- bundled from Development.AutomorphicArithmetic.AdelicSL2.ExistsHaarRestrictRangeEqSmulMapOfInvariant
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

theorem UpperTheory.exists_haar_restrict_range_eq_smul_map_of_invariant :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (e : X → G) (ν : Measure X) [IsFiniteMeasureOnCompacts ν], IsOpenEmbedding e → (1 : G) ∈ Set.range e → (∀ a ∈ Set.range e, ∀ b ∈ Set.range e, a * b ∈ Set.range e) → (∀ a ∈ Set.range e, a⁻¹ ∈ Set.range e) → ν ≠ 0 → (∀ x, ∃ T : X → X, MeasurePreserving T ν ν ∧ ∀ y, e x * e y = e (T y)) → ∃ c : ℝ≥0, μ.restrict (Set.range e) = c • ν.map e := by
  intro G X _ _ _ _ _ _ _ _ μ _ _ _ _ e ν _ he h1 hmul hinv hν hT
  let H : Subgroup G :=
    { carrier := Set.range e
      mul_mem' := fun ha hb => hmul _ ha _ hb
      one_mem' := h1
      inv_mem' := fun ha => hinv _ ha }
  have hHo : IsOpen (H : Set G) := he.isOpen_range
  have hemb : IsOpenEmbedding (H.subtype) := hHo.isOpenEmbedding_subtypeVal
  haveI : LocallyCompactSpace H := hemb.locallyCompactSpace
  haveI hHaar : (μ.comap H.subtype).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) μ hemb
  have hme : MeasurableEmbedding (H.subtype) := hemb.measurableEmbedding
  let e' : X → H := fun x => ⟨e x, x, rfl⟩
  have he'c : Continuous e' := he.continuous.subtype_mk _
  have he'i : IsInducing e' :=
    (IsInducing.of_comp_iff (g := H.subtype) IsInducing.subtypeVal).mp he.isInducing
  have he'sur : Function.Surjective e' := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hval : H.subtype ∘ e' = e := rfl
  have hlamval : (ν.map e').map H.subtype = ν.map e := by
    rw [Measure.map_map hme.measurable he'c.measurable, hval]
  have hlam0 : ν.map e' ≠ 0 := by
    intro h0
    apply hν
    rw [← Measure.measure_univ_eq_zero]
    have := congrArg (fun m : Measure H => m Set.univ) h0
    simpa [Measure.map_apply he'c.measurable MeasurableSet.univ] using this
  haveI : IsFiniteMeasureOnCompacts (ν.map e') := ⟨fun K hK => by
    rw [Measure.map_apply he'c.measurable hK.measurableSet]
    exact (he'i.isCompact_preimage (by simp [he'sur.range_eq]) hK).measure_lt_top⟩
  haveI : (ν.map e').IsMulLeftInvariant := ⟨fun h => by
    obtain ⟨_, x, rfl⟩ := h
    obtain ⟨T, hTm, hTe⟩ := hT x
    rw [Measure.map_map (measurable_const_mul _) he'c.measurable]
    have hcomp : (fun y : H => (⟨e x, x, rfl⟩ : H) * y) ∘ e' = e' ∘ T :=
      funext fun y => Subtype.ext (hTe y)
    rw [hcomp, ← Measure.map_map he'c.measurable hTm.measurable, hTm.map_eq]⟩
  have key := Measure.isMulLeftInvariant_eq_smul (ν.map e') (μ.comap H.subtype)
  set c := Measure.haarScalarFactor (ν.map e') (μ.comap H.subtype) with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hlam0
    rw [key, h0, zero_smul]
  have hμH : μ.comap H.subtype = c⁻¹ • ν.map e' := by
    rw [key, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨c⁻¹, ?_⟩
  have hres : μ.restrict (Set.range e) = (μ.comap H.subtype).map H.subtype := by
    rw [hme.map_comap]
    congr 1
    simp [H]
    rfl
  rw [hres, hμH, Measure.map_smul, hlamval]
  exact hme.measurable.aemeasurable
end

-- bundled from Development.AutomorphicArithmetic.AdelicSL2.IsOpenEmbeddingProjection
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal
private theorem continuous_gl' : Continuous (gl : G1 ℚ → GL (Fin 2) (A ℚ)) := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  have h : (fun g : G1 ℚ => (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun g : G1 ℚ => ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ)) := by
    funext g
    have : (gl g)⁻¹ = gl g⁻¹ := by
      rw [inv_eq_iff_mul_eq_one]
      exact Units.ext (by
        change (g : Matrix (Fin 2) (Fin 2) (A ℚ)) * ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ)) = 1
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one])
    rw [this]
    rfl
  rw [show (fun x : G1 ℚ => ((((gl x)⁻¹ : GL (Fin 2) (A ℚ))) : Matrix (Fin 2) (Fin 2) (A ℚ))) = _ from h]
  exact continuous_subtype_val.comp (continuous_inv : Continuous fun g : G1 ℚ => g⁻¹)

private theorem dM_inv' (t : (A ℚ)ˣ) : (dM t)⁻¹ = dM t⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← dM_mul, mul_inv_cancel]
  apply Units.ext
  change !![1, 0; 0, ((1 : (A ℚ)ˣ) : A ℚ)] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem continuous_dM_val : Continuous (fun t : (A ℚ)ˣ => ((dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) := by
  have h : (fun t : (A ℚ)ˣ => ((dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun t : (A ℚ)ˣ => !![1, 0; 0, (t : A ℚ)] := rfl
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact Units.continuous_val

private theorem continuous_dM' : Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) := by
  refine Units.continuous_iff.2 ⟨continuous_dM_val, ?_⟩
  have h : (fun t : (A ℚ)ˣ => (((dM t)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun t : (A ℚ)ˣ => ((dM t⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) := by
    funext t
    rw [dM_inv']
  exact h ▸ (continuous_dM_val.comp continuous_inv)

private theorem det_dM' (t : (A ℚ)ˣ) : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (dM t) = t := by
  have h := det_el 1 t
  simpa using h

private theorem det_rest (x : GL (Fin 2) (A ℚ)) :
    Matrix.det (((x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹ : GL (Fin 2) (A ℚ))) : Matrix (Fin 2) (Fin 2) (A ℚ)) = 1 := by
  have h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹) = 1 := by
    rw [map_mul, map_inv, det_dM', mul_inv_cancel]
  have := congrArg Units.val h
  rwa [GroundTheory.Automorphic.AdelicGLn.coe_det] at this

private noncomputable def rt (x : GL (Fin 2) (A ℚ)) : G1 ℚ × (A ℚ)ˣ :=
  (⟨((x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)), det_rest x⟩,
    GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x)

private theorem continuous_rt : Continuous rt := by
  have hd := GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hd
  exact Units.continuous_val.comp (continuous_id.mul (continuous_dM'.comp hd).inv)

private theorem rt_pre : Function.LeftInverse rt (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) := by
  rintro ⟨g, t⟩
  refine Prod.ext (Subtype.ext ?_) (det_el g t)
  change (((gl g * dM t) * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (gl g * dM t)))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = (g : Matrix (Fin 2) (Fin 2) (A ℚ))
  rw [det_el, mul_inv_cancel_right]
  rfl

private theorem pos_of_UU {t : (A ℚ)ˣ} (ht : t ∈ UU) : t ∈ RationalIdeles.positiveSubgroup := by
  have hi : (t⁻¹ : (A ℚ)ˣ) ∈ UU := US.inv_mem (show t ∈ US from ht)
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨(IdeleGroup.mem_standardOpenSubgroup ℚ).2 fun v => ⟨?_, ?_⟩, ?_⟩
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (ht.2 v).le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hi.2 v).le
  · rw [RationalIdeles.coe_realPart, ht.1, map_one]
    exact one_pos

private theorem UU_of_pos {t : (A ℚ)ˣ} (hp : t ∈ RationalIdeles.positiveSubgroup)
    (hm : ((IdeleGroup.ideleModule ℚ t : {r : ℝ // 0 < r}) : ℝ) = 1) : t ∈ UU := by
  have hr : (RationalIdeles.realPart t : ℝ) = 1 := by
    rw [← GroundTheory.Automorphic.GL2Classical.ideleModule_eq_realPart_of_mem hp, hm]
  obtain ⟨hs, -⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  refine ⟨RationalIdeles.realEquiv.injective ?_, fun v => ?_⟩
  · rw [map_one, ← RationalIdeles.coe_realPart, hr]
  · obtain ⟨ha, hb⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 hs v
    have ha' : Valued.v (H.cp v (t : A ℚ)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha
    have hb' : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb
    have hm1 : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (t : A ℚ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    refine le_antisymm ha' ?_
    calc (1 : _) = Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (t : A ℚ)) := hm1.symm
      _ ≤ Valued.v (H.cp v (t : A ℚ)) := mul_le_of_le_one_left' hb'

theorem UpperTheory.isOpenEmbedding_projection :
    IsOpenEmbedding pm := by
  have hf : Topology.IsEmbedding (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) :=
    Function.LeftInverse.isEmbedding rt_pre continuous_rt
      ((continuous_gl'.comp continuous_fst).mul (continuous_dM'.comp continuous_snd))
  have hu : Topology.IsEmbedding (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ) :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have he : (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ)) =
      (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) ∘ (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ) := by
    funext p
    rfl
  have hc : Topology.IsEmbedding (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ)) := by
    rw [he]
    exact hf.comp hu
  have hp : Continuous pm := Continuous.subtype_mk hc.continuous _
  refine ⟨Topology.IsEmbedding.of_comp hp continuous_subtype_val hc, ?_⟩
  have hs : Set.range pm = (fun x : GG => GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ))) ⁻¹'
      (RationalIdeles.positiveSubgroup : Set (IdeleGroup ℚ)) := by
    rw [range_pm]
    ext x
    refine ⟨fun h => pos_of_UU h, fun h => UU_of_pos h ?_⟩
    exact GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2
  rw [hs]
  exact RationalIdeles.isOpen_positiveSubgroup.preimage
    ((GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2).comp continuous_subtype_val)
end

