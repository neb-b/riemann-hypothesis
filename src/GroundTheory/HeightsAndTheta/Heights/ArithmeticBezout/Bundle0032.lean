module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0016

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFormsThroughPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem aeval_mul_homogeneousComponent {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ}
    (q : MvPolynomial (Fin n) F) (e : ℕ) (t : Ω) (x : Fin n → Ω) :
    aeval (fun m => t * x m) (homogeneousComponent e q) = t ^ e * aeval x (homogeneousComponent e q) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.mem_filter] at hα
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hdeg : Finsupp.degree α = ∑ i ∈ α.support, α i := rfl
  rw [← hα.2, hdeg]
  ring

theorem FormsThroughPoint.proof (hZ : IncidenceZeroLocus.Statement) (hI : ThroughPointIncIdeal.Statement)
    (hC : ChartZeroTrdeg.Statement) (hT : ThroughTwoPointsTrdeg.Statement)
    (hB : TrdegBaseAlgebraic.Statement) : FormsThroughPoint.Statement := by
  intro F _ n k Q hQ hdim x hx hxQ
  obtain ⟨q, hqQ, hqx⟩ := hxQ

  have h1 := ComponentOfIncIdeal.one_le_ringKrullDim_quot hQ
  obtain ⟨d, hd, hdk⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) ∧
      d + 1 ≤ k := by
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at h1 hdim ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd h1 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := hdim
        exact absurd (WithBot.coe_le_coe.mp h') (by simp)
      | coe m =>
        have h1' : 1 ≤ m := by exact_mod_cast h1
        have hm : m ≤ k := by exact_mod_cast hdim
        refine ⟨m - 1, ?_, by omega⟩
        rw [show m - 1 + 1 = m by omega]
        rfl

  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  let c : Fin n → AlgebraicClosure F := Pi.single j₀ (x j₀)⁻¹
  have hj₀' : x j₀ ≠ 0 := hj₀
  have hc : ∑ j, c j * x j = 1 := by
    rw [Finset.sum_eq_single j₀ (fun b _ hb => by simp [c, hb]) (by simp)]
    simp [c, hj₀']
  by_contra hno
  push Not at hno

  have hg := hI F n k Q x c hc hno
  let K := AlgebraicClosure F
  let R := MvPolynomial (Fin k × Fin n) K
  let Ω := AlgebraicClosure (FractionRing R)
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) Ω]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let v : Fin k × Fin n → Ω := fun ij => algebraMap R Ω (genSubst x c ij)
  have hv : ∀ g ∈ incIdeal Q k, aeval v g = 0 := by
    intro g hgI
    have hval : aeval v g = algebraMap R Ω (aeval (genSubst x c) g) := aeval_algebraMap_apply Ω (genSubst x c) g
    rw [hval, hg g hgI, map_zero]
  obtain ⟨y, hy0, hyQ, hyv⟩ := hZ F n k Q hQ.isHomog Ω v hv

  have hnp : ∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m) := by
    intro t ht
    obtain ⟨e, he⟩ : ∃ e, aeval x (homogeneousComponent e q) ≠ 0 := by
      by_contra h
      push Not at h
      apply hqx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_homogeneousComponent q, map_sum]
      exact Finset.sum_eq_zero fun e _ => h e
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hy0
      rw [ht]
      funext m
      simp
    have hzero := hyQ _ (hQ.isHomog q hqQ e)
    have hscale := aeval_mul_homogeneousComponent q e t (algebraMap K Ω ∘ x)
    simp only [Function.comp_apply] at hscale
    rw [ht, hscale, aeval_algebraMap_apply] at hzero
    exact mul_ne_zero (pow_ne_zero _ ht0) ((map_ne_zero _).mpr he) hzero

  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy0
  have hk := hT K Ω n k hinj x c hc y j hj hnp hyv
  have hb := hB F K Ω inferInstance (Fin n) (fun m => y m * (y j)⁻¹)
  have hd' := hC F n d Q hQ hd Ω y j hyQ hj
  have hkd : (k : Cardinal) ≤ d := hk.trans (hb.trans hd')
  norm_cast at hkd
  omega

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set

open scoped ENNReal

noncomputable section

theorem GraphAreaFibre.differentiableAt_graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {Φ : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hΦ : DifferentiableAt ℂ Φ x) : DifferentiableAt ℂ (graphPt e Φ) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => Φ y i) (e j)) x
  rcases e j with i | i
  · exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · exact (differentiableAt_piLp 2).1 hΦ i

theorem GraphAreaFibre.continuous_graphBase {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k) :
    Continuous (graphBase e : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin d)) := by
  unfold graphBase
  fun_prop

theorem GraphAreaFibre.proof (hInt : GraphAreaIntegral.Statement) (hJac : TangentJacComp.Statement)
    (hMult : AreaMultiplicityWeight.Statement) : GraphAreaFibre.Statement := by
  intro d k n e Ω Φ hΩ hΦ P hPΩ hPm T hT π
  set G : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := graphPt e Φ with hGdef
  set μ : Measure (EuclideanSpace ℂ (Fin d)) := Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) with hμdef
  have hdim : ((2 * d : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have : μ.IsAddHaarMeasure := by
    rw [hμdef, hdim]
    infer_instance

  set A : Set (EuclideanSpace ℂ (Fin d)) := Ω ∩ G ⁻¹' P with hAdef
  have hAΩ : A ⊆ Ω := inter_subset_left
  have hGA : G '' A = P := by
    rw [hAdef, image_inter_preimage]
    exact inter_eq_right.2 hPΩ
  have hAm : MeasurableSet A := by
    have hAeq : A = graphBase e '' P := by
      ext x
      constructor
      · rintro ⟨-, hxP⟩
        exact ⟨G x, hxP, graphBase_graphPt e Φ x⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨x, hx, rfl⟩ := hPΩ hy
        rw [graphBase_graphPt]
        exact ⟨hx, hy⟩
    rw [hAeq]
    refine hPm.image_of_continuousOn_injOn (GraphAreaFibre.continuous_graphBase e).continuousOn ?_
    intro y hy y' hy' h
    obtain ⟨x, -, rfl⟩ := hPΩ hy
    obtain ⟨x', -, rfl⟩ := hPΩ hy'
    rw [hGdef, graphBase_graphPt, graphBase_graphPt] at h
    rw [h]

  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ G x := fun x hx =>
    GraphAreaFibre.differentiableAt_graphPt e ((hΦ x hx).differentiableAt (hΩ.mem_nhds hx))
  let Lπ : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
    LinearMap.toContinuousLinearMap (linProjₗ π)
  set f : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin d) := fun x => linProj π (G x) with hfdef
  have hfd : ∀ x ∈ Ω, HasFDerivAt f ((Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ) x := fun x hx =>
    (Lπ.hasFDerivAt.comp x (hGd x hx).hasFDerivAt).restrictScalars ℝ
  have hf' : ∀ x ∈ A, HasFDerivWithinAt f (fderiv ℝ f x) A x := fun x hx =>
    (hfd x (hAΩ hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  obtain ⟨hNm, hN⟩ := hMult (EuclideanSpace ℂ (Fin d)) μ A f (fun x => fderiv ℝ f x) hAm hf'

  have hcount : ∀ w, {y | y ∈ P ∧ linProj π y = w}.encard = {x ∈ A | f x = w}.encard := by
    intro w
    have hset : {y | y ∈ P ∧ linProj π y = w} = G '' {x ∈ A | f x = w} := by
      ext y
      constructor
      · rintro ⟨hy, hyw⟩
        obtain ⟨x, hx, rfl⟩ := hPΩ hy
        exact ⟨x, ⟨⟨hx, hy⟩, hyw⟩, rfl⟩
      · rintro ⟨x, ⟨⟨-, hxP⟩, hxw⟩, rfl⟩
        exact ⟨hxP, hxw⟩
    rw [hset, (graphPt_injective_of_graphBase e Φ).injOn.encard_image]
  have hNfun : (fun w : EuclideanSpace ℂ (Fin d) =>
      (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞)) =
      fun w => (({x ∈ A | f x = w}.encard : ℕ∞) : ℝ≥0∞) := by
    funext w
    rw [hcount w]

  have hc : μ = μ.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  refine ⟨?_, fun g hg => ?_⟩
  · rw [hNfun]
    exact hNm.mono_ac (Measure.absolutelyContinuous_isAddHaarMeasure volume μ)

  have h1 : ∫⁻ y in P, g (linProj π y) * ENNReal.ofReal (tangentJac π (T y))
      ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)) =
      ∫⁻ x in A, g (f x) * ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
    rw [← hGA, hInt d k n e Ω Φ hΩ hΦ A hAΩ hAm]
    refine setLIntegral_congr_fun hAm fun x hx => ?_
    have hG' : fderiv ℝ G x = (fderiv ℂ G x).restrictScalars ℝ :=
      ((hGd x (hAΩ hx)).hasFDerivAt.restrictScalars ℝ).fderiv
    have hf'x : fderiv ℝ f x = (Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ := (hfd x (hAΩ hx)).fderiv
    have hJ := hJac d n (fderiv ℂ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) π
    have hTx : T (G x) = LinearMap.range (fderiv ℂ G x :
        EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := hT x (hAΩ hx) hx.2
    have hnn : 0 ≤ tangentJac π (T (G x)) := by
      unfold tangentJac
      positivity
    rw [mul_assoc, ← ENNReal.ofReal_mul hnn, hTx, hG', hf'x]
    congr 2
  rw [h1, hN g hg]
  simp_rw [hcount]
  rw [hc, Measure.smul_apply, lintegral_smul_measure]
  simp only [ENNReal.smul_def, smul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

theorem GraphAreaIntegral.continuous_areaJacobian {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt

theorem GraphAreaIntegral.proof (h : GraphAreaHolomorphic.Statement) : GraphAreaIntegral.Statement := by
  intro d m n e Ω F hΩ hF A hAΩ hA g
  set G := graphPt e F with hGdef
  set μ : Measure (EuclideanSpace ℂ (Fin d)) := μH[((2 * d : ℕ) : ℝ)] with hμ
  set ν : Measure (EuclideanSpace ℂ (Fin n)) := μH[((2 * d : ℕ) : ℝ)] with hν
  set J : EuclideanSpace ℂ (Fin d) → ℝ≥0∞ := fun x => ENNReal.ofReal (areaJacobian
    (fderiv ℝ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) with hJ
  have hJm : Measurable J := ENNReal.measurable_ofReal.comp
    (GraphAreaIntegral.continuous_areaJacobian.measurable.comp (measurable_fderiv ℝ G))
  have hGc : ContinuousOn G A := (continuousOn_graphPt e hF.continuousOn).mono hAΩ
  let f : A → EuclideanSpace ℂ (Fin n) := fun a => G a
  have hfc : Continuous f := hGc.domRestrict
  have hf : MeasurableEmbedding f :=
    { injective := fun a b hab => Subtype.ext (graphPt_injective_of_graphBase e F hab)
      measurable := hfc.measurable
      measurableSet_image' := fun s hs => by
        have hs' : MeasurableSet (((↑) : A → EuclideanSpace ℂ (Fin d)) '' s) :=
          MeasurableSet.subtype_image hA hs
        have : f '' s = G '' (((↑) : A → EuclideanSpace ℂ (Fin d)) '' s) := by
          rw [Set.image_image]
        rw [this]
        exact hs'.image_of_continuousOn_injOn (hGc.mono (by rintro _ ⟨a, -, rfl⟩; exact a.2))
          (graphPt_injective_of_graphBase e F).injOn }
  set M : Measure A := (μ.withDensity J).comap ((↑) : A → EuclideanSpace ℂ (Fin d)) with hM
  have hmeas : ν.restrict (G '' A) = M.map f := by
    ext1 S hS
    have hpre : ((↑) : A → EuclideanSpace ℂ (Fin d)) '' (f ⁻¹' S) = A ∩ G ⁻¹' S := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.2, ha⟩
      · rintro ⟨hx, hxS⟩
        exact ⟨⟨x, hx⟩, hxS, rfl⟩
    have hmS : MeasurableSet (A ∩ G ⁻¹' S) := by
      rw [← hpre]
      exact MeasurableSet.subtype_image hA (hf.measurable hS)
    rw [Measure.restrict_apply hS, Measure.map_apply hf.measurable hS,
      (MeasurableEmbedding.subtype_coe hA).comap_apply, hpre, withDensity_apply _ hmS,
      Set.inter_comm S, ← Set.image_inter_preimage]
    exact h d m n e Ω F hΩ hF _ (Set.inter_subset_left.trans hAΩ) hmS
  calc ∫⁻ y in G '' A, g y ∂ν = ∫⁻ y, g y ∂(M.map f) := by rw [hmeas]
    _ = ∫⁻ a, g (f a) ∂M := hf.lintegral_map g
    _ = ∫⁻ x in A, g (G x) ∂(μ.withDensity J) := lintegral_subtype_comap hA (fun x => g (G x))
    _ = ∫⁻ x, g (G x) ∂((μ.restrict A).withDensity J) := by rw [restrict_withDensity hA]
    _ = ∫⁻ x in A, J x * g (G x) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul_non_measurable _ hJm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = ∫⁻ x in A, g (G x) * J x ∂μ := by simp_rw [mul_comm]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSecDegreeLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SecDegreeLe.proof : SecDegreeLe.Statement := by
  intro k E _ _ _ n e δ Q g y hQ hg hδ hfin hdom hsep hne
  classical
  set QE := Q.map (MvPolynomial.map (algebraMap k E))
  set A := Vertical.SecAlg QE y
  have : Module.Finite E A := hfin
  have : IsDomain A := hdom
  have : Algebra.IsSeparable E A := hsep
  have : Module.Free E A := Module.Free.of_divisionRing E A
  set N := Vertical.normForm (R := E) A (Vertical.secCoord QE y)
  set G := Vertical.specRest (algebraMap k E) g y

  have hirr : Irreducible N := Vertical.NormFormIrreducible.full E A n (Vertical.secCoord QE y)
    (fun j => y (.inr j)) (Vertical.secCoord_adjoin _ _) (Vertical.secCoord_chart _ _)
  obtain ⟨m, -, hm⟩ := Vertical.ChowSecDvd.full k E n e Q g y hQ hg
  have hd := Vertical.NormFormDvd.full E A n (Vertical.secCoord QE y) (G ^ m) (by rwa [map_pow])
  rw [← pow_mul] at hd
  have hNG : N ∣ G := hirr.prime.dvd_of_dvd_pow hd

  let b := Module.Free.chooseBasis E A
  have hN : N.IsHomogeneous (Module.finrank E A) := by
    show (Vertical.normForm (R := E) A (Vertical.secCoord QE y)).IsHomogeneous _
    rw [Vertical.normForm_eq_det b, Module.finrank_eq_card_chooseBasisIndex]
    refine Vertical.isHomogeneous_det_linear _ fun i k' => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X E j).mul (isHomogeneous_C (Fin n) _)
  have hN0 : N ≠ 0 := by
    intro h0
    have hv := Vertical.NormFormEval.full E A n (Vertical.secCoord QE y) (fun j => y (.inr j))
    change eval (fun j => y (.inr j)) N = _ at hv
    rw [h0, map_zero, Vertical.secCoord_chart, map_one] at hv
    exact zero_ne_one hv

  have hG : G.IsHomogeneous δ := Vertical.isHomogeneous_specRest _ hδ y
  rw [← hN.totalDegree hN0, ← hG.totalDegree hne]
  exact totalDegree_le_of_dvd_of_isDomain hNG hne

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacComp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem TangentJacComp.real_inner_eq_re {d : ℕ} (x y : EuclideanSpace ℂ (Fin d)) :
    @inner ℝ _ _ x y = RCLike.re (@inner ℂ _ _ x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [PiLp.inner_apply, Complex.inner, map_sum]

theorem TangentJacComp.adjoint_restrictScalars {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    LinearMap.adjoint (L.restrictScalars ℝ) = (LinearMap.adjoint L).restrictScalars ℝ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [TangentJacComp.real_inner_eq_re, TangentJacComp.real_inner_eq_re]
  simp [LinearMap.adjoint_inner_left]

theorem TangentJacComp.areaJacobian_eq {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    areaJacobian (L.restrictScalars ℝ) = L.normDet ^ 2 := by
  have hsq : ((L.normDet ^ 2 : ℝ) : ℂ) = LinearMap.det (LinearMap.adjoint L ∘ₗ L) := L.normDet_sq
  rw [areaJacobian, TangentJacComp.adjoint_restrictScalars]
  have hc : (LinearMap.adjoint L).restrictScalars ℝ ∘ₗ L.restrictScalars ℝ =
      (LinearMap.adjoint L ∘ₗ L).restrictScalars ℝ := rfl
  rw [hc, LinearMap.det_restrictScalars, ← hsq, Algebra.norm_complex_apply, Complex.normSq_ofReal,
    Real.sqrt_mul_self (by positivity)]

theorem TangentJacComp.proof : TangentJacComp.Statement := by
  intro d n L π
  have hc := LinearMap.normDet_comp L (linProjₗ π)
  have hr : |LinearMap.det (((linProjₗ π).comp L).restrictScalars ℝ)| =
      ((linProjₗ π).comp L).normDet ^ 2 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.normDet_eq_norm_det,
      Complex.sq_norm, abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [hr, hc, tangentJac, TangentJacComp.areaJacobian_eq]
  rw [mul_pow]
  rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacCompress
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

theorem det_starProjection_compress {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →L[ℂ] F) (T : Submodule ℂ E) :
    (T.starProjection ∘L A.adjoint ∘L A ∘L T.starProjection + (1 - T.starProjection)).det =
      (LinearMap.adjoint ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) ∘ₗ ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype)).det := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : E →L[ℂ] E,
      Q = T.starProjection ∘L A.adjoint ∘L A ∘L T.starProjection + (1 - T.starProjection) := ⟨_, rfl⟩
  rw [← hQdef]
  have hQx : ∀ x : E, Q x =
      T.starProjection (A.adjoint (A (T.starProjection x))) + (x - T.starProjection x) := by
    intro x; subst hQdef; simp
  have hQT : T ≤ T.comap (Q : E →ₗ[ℂ] E) := by
    intro x hx
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hQx,
      Submodule.starProjection_eq_self_iff.mpr hx, sub_self, add_zero]
    exact T.starProjection_apply_mem _
  have hres : (Q : E →ₗ[ℂ] E).restrict hQT =
      LinearMap.adjoint ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) ∘ₗ ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) := by
    ext1 x
    apply ext_inner_right ℂ
    intro z
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, Submodule.coe_inner,
      LinearMap.coe_restrict_apply, ContinuousLinearMap.coe_coe, hQx,
      Submodule.starProjection_eq_self_iff.mpr x.2, sub_self, add_zero,
      Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr z.2,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hquot : T.mapQ T (Q : E →ₗ[ℂ] E) hQT = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_comp, ContinuousLinearMap.coe_coe]
    rw [Submodule.Quotient.eq, hQx]
    have h : T.starProjection (A.adjoint (A (T.starProjection x))) + (x - T.starProjection x) - x =
        T.starProjection (A.adjoint (A (T.starProjection x))) - T.starProjection x := by abel
    rw [h]
    exact T.sub_mem (T.starProjection_apply_mem _) (T.starProjection_apply_mem _)
  rw [ContinuousLinearMap.det, LinearMap.det_eq_det_mul_det T _ hQT, hres, hquot, LinearMap.det_id,
    mul_one]

theorem TangentJacCompress.proof : TangentJacCompress.Statement := by
  intro n m π T
  unfold tangentJac
  have h := LinearMap.normDet_sq (𝕜 := ℂ) (U := T) (V := EuclideanSpace ℂ (Fin m)) ((linProjₗ π).comp T.subtype)
  exact h.trans (det_starProjection_compress (LinearMap.toContinuousLinearMap (linProjₗ π)) T).symm

end

end GroundTheory.Heights₂.Heights
end

