module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDual
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.GlobalFields.TateThesis.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.PhiMem
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private abbrev Fa : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

private theorem dv_iff {N : ℕ} (hN : 0 < N) (z : Fa) :
    (∀ v : H.P ℚ, Valued.v (z v) ≤ Valued.v ((N : H.Kv v))) ↔
      ∃ u : Fa, (∀ v, u v ∈ v.adicCompletionIntegers ℚ) ∧ z = N • u := by
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set w : Fa := algebraMap ℚ Fa (N : ℚ)⁻¹ with hw
  have hwN : w * (N : Fa) = 1 := by
    rw [hw, ← map_natCast (algebraMap ℚ Fa), ← map_mul, inv_mul_cancel₀ hNq, map_one]
  constructor
  · intro h
    refine ⟨w * z, fun v => ?_, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have e1 : (w * z) v = w v * z v := rfl
      have e2 : w v * (N : H.Kv v) = 1 := by
        have := congrArg (pLoc ℚ v) hwN
        rwa [map_mul, map_natCast, map_one] at this
      rw [e1, map_mul]
      calc Valued.v (w v) * Valued.v (z v) ≤ Valued.v (w v) * Valued.v (N : H.Kv v) := mul_le_mul' le_rfl (h v)
        _ = 1 := by rw [← map_mul, e2, map_one]
    · rw [nsmul_eq_mul, ← mul_assoc, mul_comm (N : Fa), hwN, one_mul]
  · rintro ⟨u, hu, rfl⟩ v
    have e1 : (N • u) v = (N : H.Kv v) * u v := by
      exact (map_nsmul (pLoc ℚ v) N u).trans (nsmul_eq_mul _ _)
    rw [e1, map_mul]
    have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hu v)
    exact mul_le_of_le_one_right' this

private abbrev Mx : Type := mixedEmbedding.mixedSpace ℚ

private instance : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (Subsingleton.elim w.1 Rat.infinitePlace ▸ Rat.isReal_infinitePlace)⟩

private def mE : Mx ≃L[ℝ] ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => y.1 ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun t => (fun _ => t, 0)
      left_inv := fun y => by
        refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
        exact congrArg y.1 (Subsingleton.elim (α := {w : InfinitePlace ℚ // w.IsReal}) _ _)
      right_inv := fun _ => rfl }

private def eE : (Fin 2 → Mx) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.piCongrRight fun _ => mE).trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

private theorem eE_apply (x : Fin 2 → A ℚ) (i : Fin 2) : eE (infPartPi x) i = re (x i) := rfl

private theorem temp (p : MvPolynomial (Fin 2) ℂ) :
    (fun y : Fin 2 → Mx => MvPolynomial.eval (fun i => ((eE y i : ℝ) : ℂ)) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    exact (Complex.ofRealCLM.comp ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
      eE.toContinuousLinearMap)).hasTemperateGrowth

private def phiS (p : MvPolynomial (Fin 2) ℂ) : SchwartzMap (Fin 2 → Mx) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun y : Fin 2 → Mx => MvPolynomial.eval (fun i => ((eE y i : ℝ) : ℂ)) p)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eE (gaussianSchwartz (EuclideanSpace ℝ (Fin 2))))

private theorem cond_iff {N : ℕ} (hN : 0 < N) (x : Fin 2 → A ℚ) :
    (∀ v, Dv N v (x 0) ∧ Dv N v (x 1 - 1)) ↔
      ∀ i, ∃ u : Fa, (∀ v, u v ∈ v.adicCompletionIntegers ℚ) ∧
        finPartPi x i = algebraMap ℚ Fa ((![0, 1] : Fin 2 → ℚ) i) + N • u := by
  have h0 := dv_iff hN (x 0).2
  have h1 := dv_iff hN ((x 1 - 1).2)
  have e1 : ∀ u : Fa, (x 1 - 1).2 = N • u ↔ (x 1).2 = 1 + N • u := fun u => by
    change (x 1).2 - 1 = N • u ↔ _
    rw [sub_eq_iff_eq_add']
  constructor
  · intro h i
    fin_cases i
    · obtain ⟨u, hu, e⟩ := h0.1 fun v => (h v).1
      exact ⟨u, hu, by simpa [finPartPi] using e⟩
    · obtain ⟨u, hu, e⟩ := h1.1 fun v => (h v).2
      exact ⟨u, hu, by simpa [finPartPi] using (e1 u).1 e⟩
  · intro h v
    refine ⟨h0.2 ?_ v, h1.2 ?_ v⟩
    · obtain ⟨u, hu, e⟩ := h 0
      exact ⟨u, hu, by simpa [finPartPi] using e⟩
    · obtain ⟨u, hu, e⟩ := h 1
      exact ⟨u, hu, (e1 u).2 (by simpa [finPartPi] using e)⟩

private theorem phiS_apply (p : MvPolynomial (Fin 2) ℂ) (x : Fin 2 → A ℚ) :
    phiS p (infPartPi x) = MvPolynomial.eval (fun i => (re (x i) : ℂ)) p *
      Complex.exp (-(Real.pi : ℂ) * ((re (x 0) ^ 2 + re (x 1) ^ 2 : ℝ) : ℂ)) := by
  rw [phiS, SchwartzMap.smulLeftCLM_apply_apply (temp p), SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, gaussianSchwartz_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, smul_eq_mul]
  simp only [eE_apply]
  push_cast
  rfl

theorem phiMem_of :
    PhiMem := by
  intro N p hN
  have e : PhiN N p = schwartzBruhatTensorPi (phiS p) (GlobalTheory.CompanionTheory.ThetaUniq.cosetInd ℚ N ![0, 1]) := by
    funext x
    rw [PhiN, schwartzBruhatTensorPi, phiS_apply, GlobalTheory.CompanionTheory.ThetaUniq.cosetInd, Set.indicator_apply]
    split_ifs with h h' h''
    · rw [Pi.one_apply, mul_one]
    · exact absurd ((cond_iff hN x).1 h) h'
    · exact absurd ((cond_iff hN x).2 h'') h
    · rw [mul_zero]
  rw [e]
  exact schwartzBruhatTensorPi_mem _
    ((mem_finiteSchwartzBruhatPi ℚ).2 (GlobalTheory.CompanionTheory.ThetaUniq.cosetInd_mem_SB ℚ (Fin 2) N hN _))

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UMeasEx
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private lemma eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma mem_UU_iff (t : IdeleGroup ℚ) :
    t ∈ UU ↔ IdeleGroup.toInfinite ℚ t = 1 ∧ IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ := by
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Units.ext h1, (mem_finiteIntegralUnits ℚ).2 fun v => ?_⟩
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rintro ⟨h1, h2⟩
    refine ⟨congrArg Units.val h1, fun v => ?_⟩
    obtain ⟨ha, hb⟩ := (mem_finiteIntegralUnits ℚ).1 h2 v
    exact eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) (by rw [mul_comm]; exact hinv v)

private lemma measurableSet_UU : MeasurableSet (UU : Set (IdeleGroup ℚ)) := by
  have h : (UU : Set (IdeleGroup ℚ)) = {t | IdeleGroup.toInfinite ℚ t = 1} ∩
      IdeleGroup.toFinite ℚ ⁻¹' (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    ext t
    exact mem_UU_iff t
  rw [h]
  exact (isClosed_eq (IdeleGroup.continuous_toInfinite ℚ) continuous_const).measurableSet.inter
    ((isOpen_finiteIntegralUnits ℚ).preimage (IdeleGroup.continuous_toFinite ℚ)).measurableSet

private noncomputable def ef (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : IdeleGroup ℚ := (IdeleGroup.prodEquiv ℚ).symm (1, x)

private lemma measurable_ef : Measurable ef :=
  ((map_continuous (IdeleGroup.prodEquiv ℚ).symm).comp (continuous_const.prodMk continuous_id)).measurable

private lemma toInfinite_ef (x) : IdeleGroup.toInfinite ℚ (ef x) = 1 :=
  congrArg Prod.fst ((IdeleGroup.prodEquiv ℚ).apply_symm_apply (1, x))

private lemma toFinite_ef (x) : IdeleGroup.toFinite ℚ (ef x) = x :=
  congrArg Prod.snd ((IdeleGroup.prodEquiv ℚ).apply_symm_apply (1, x))

private lemma mul_ef {t : IdeleGroup ℚ} (h : IdeleGroup.toInfinite ℚ t = 1) (x) :
    t * ef x = ef (IdeleGroup.toFinite ℚ t * x) := by
  refine (IdeleGroup.prodEquiv ℚ).injective ?_
  rw [map_mul]
  refine Prod.ext ?_ ?_
  · change IdeleGroup.toInfinite ℚ t * IdeleGroup.toInfinite ℚ (ef x) = IdeleGroup.toInfinite ℚ (ef _)
    rw [h, toInfinite_ef, toInfinite_ef, one_mul]
  · change IdeleGroup.toFinite ℚ t * IdeleGroup.toFinite ℚ (ef x) = IdeleGroup.toFinite ℚ (ef _)
    rw [toFinite_ef, toFinite_ef]

theorem uMeasEx_of :
    UMeasEx := by
  have hU : MeasurableSet (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
    (isOpen_finiteIntegralUnits ℚ).measurableSet
  refine ⟨⟨((finiteIdeleMeasure ℚ).restrict (finiteIntegralUnits ℚ)).map ef, ⟨?_⟩, ?_, ?_⟩⟩
  · rw [Measure.map_apply measurable_ef MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, finiteIdeleMeasure_finiteIntegralUnits]
  · rw [Measure.map_apply measurable_ef measurableSet_UU.compl,
      Measure.restrict_apply (measurable_ef measurableSet_UU.compl)]
    convert measure_empty (μ := finiteIdeleMeasure ℚ)
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe,
      Set.mem_empty_iff_false, iff_false, not_and, not_not]
    intro hx hxU
    exact hx ((mem_UU_iff _).2 ⟨toInfinite_ef x, by rwa [toFinite_ef]⟩)
  · intro t ht
    obtain ⟨h1, h2⟩ := (mem_UU_iff t).1 ht
    have hg := (measurePreserving_mul_left (finiteIdeleMeasure ℚ) (IdeleGroup.toFinite ℚ t)).restrict_preimage hU
    have hpre : (fun x => IdeleGroup.toFinite ℚ t * x) ⁻¹'
        (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) = finiteIntegralUnits ℚ := by
      ext x
      exact (finiteIntegralUnits ℚ).mul_mem_cancel_left h2
    rw [hpre] at hg
    have hf : Measurable fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ) :=
      (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hf measurable_ef]
    have hc : (fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ)) ∘ ef = ef ∘ fun x => IdeleGroup.toFinite ℚ t * x := by
      funext x
      exact mul_ef h1 x
    rw [hc, ← Measure.map_map measurable_ef hg.measurable, hg.map_eq]

end UpperTheory.ConvolutionTheory.RankTwoDescent
end

