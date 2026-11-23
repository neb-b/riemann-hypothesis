module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSmoothLocalGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

variable {n : ℕ}

theorem hasFDerivAt_eval_mvPolynomial (q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    HasFDerivAt (fun z : Fin n → ℂ => eval z q)
      (∑ j, eval x (pderiv j q) • ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ) x := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    have e1 : (fun z : Fin n → ℂ => eval z (C a)) = fun _ => a := by
      funext z
      simp
    rw [e1]
    convert hasFDerivAt_const (𝕜 := ℂ) a x
    ext v
    simp
  | add p q hp hq =>
    have e1 : (fun z : Fin n → ℂ => eval z (p + q)) = fun z => eval z p + eval z q := by
      funext z
      simp
    rw [e1]
    refine (hp.add hq).congr_fderiv ?_
    ext v
    simp [Finset.sum_add_distrib, add_mul]
  | mul_X p i hp =>
    have hfun : (fun z : Fin n → ℂ => eval z (p * X i)) = (fun z => eval z p) * (fun z => z i) := by
      funext z
      simp
    rw [hfun]
    refine (hp.mul (hasFDerivAt_apply i x)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, pderiv_mul,
      pderiv_X, map_add, map_mul, eval_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
    simp only [apply_ite, map_one, map_zero, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · by_cases hij : i = i <;> simp [mul_comm]

def HermNorm.pointOfE (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
  h.pointOfL.toLinearEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))

theorem HermNorm.pointOfE_apply (h : HermNorm n) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOfE v = h.pointOf v := rfl

def HermNorm.pointOfC (h : HermNorm n) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ))

theorem HermNorm.pointOfC_apply (h : HermNorm n) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOfC v = h.pointOf v := rfl

theorem hasFDerivAt_eval_pointOf (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    HasFDerivAt (fun w => eval (h.pointOf w) q)
      ((∑ j, eval (h.pointOf z) (pderiv j q) • ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).comp
        h.pointOfC) z :=
  (hasFDerivAt_eval_mvPolynomial q (h.pointOfC z)).comp z h.pointOfC.hasFDerivAt

theorem fderiv_eval_pointOf_apply (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ)
    (z v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℂ (fun w => eval (h.pointOf w) q) z v =
      ∑ j, eval (h.pointOf z) (pderiv j q) * h.pointOf v j := by
  rw [(hasFDerivAt_eval_pointOf h q z).fderiv]
  simp [HermNorm.pointOfC_apply]

theorem contDiff_eval_pointOf (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ 1 (fun w => eval (h.pointOf w) q) := by
  have ha : AnalyticOnNhd ℂ (fun w => eval (h.pointOfC w) q) Set.univ :=
    (AnalyticOnNhd.eval_mvPolynomial q).comp (h.pointOfC.analyticOnNhd Set.univ)
      (fun _ _ => Set.mem_univ _)
  exact contDiffOn_univ.1 (ha.contDiffOn uniqueDiffOn_univ)

theorem coneTangent_eq_comap (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) :
    coneTangent h J z = (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) (h.pointOf z)).comap
      (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) := rfl

theorem finrank_comap_equiv {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (φ : E ≃ₗ[ℂ] F) (S : Submodule ℂ F) :
    finrank ℂ (S.comap (φ : E →ₗ[ℂ] F)) = finrank ℂ S := by
  rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

theorem ConeSmoothLocalGraph.proof (hGen : PolyLocalGenerators.Statement)
    (hImp : HolomorphicImplicitGraph.Statement) : ConeSmoothLocalGraph.Statement := by
  intro n m h J hJ hdim y hy htan
  have hpy : ∀ q ∈ J, eval (h.pointOf y) q = 0 := hy
  have htanp : finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) (h.pointOf y)) = m := by
    rw [← htan, coneTangent_eq_comap, finrank_comap_equiv]
  obtain ⟨q, g, hqJ, hgp, htanq, hgen⟩ := hGen n m J hJ hdim (h.pointOf y) hpy htanp
  set f : Fin (n - m) → EuclideanSpace ℂ (Fin n) → ℂ := fun i w => eval (h.pointOf w) (q i) with hf
  have hker : ∀ z, (⨅ i, LinearMap.ker (fderiv ℂ (f i) z : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = (polyTangent (Set.range q) (h.pointOf z)).comap
        (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) := by
    intro z
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_comap,
      LinearEquiv.coe_coe, HermNorm.pointOfE_apply, hf, fderiv_eval_pointOf_apply]
    constructor
    · rintro hv _ ⟨i, rfl⟩
      exact hv i
    · intro hv i
      exact hv _ ⟨i, rfl⟩
  have hfC : ∀ i, ContDiff ℂ 1 (f i) := fun i => contDiff_eval_pointOf h (q i)
  set V : Set (EuclideanSpace ℂ (Fin n)) := {z | eval (h.pointOf z) g ≠ 0} with hV
  have hVo : IsOpen V :=
    isOpen_ne_fun ((continuous_eval g).comp h.continuous_pointOf) continuous_const
  have hfy : ∀ i, f i y = 0 := fun i => hpy _ (hqJ i)
  have hrank : finrank ℂ ↥(⨅ i, LinearMap.ker (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = m := by
    rw [hker, finrank_comap_equiv, htanq]
  obtain ⟨e, Ω, Φ, U, hU, hyU, hUV, hΩ, hΦ, hG, htanG⟩ := hImp n m f y V hfC hVo hgp hfy hrank
  have hGC : graphPt e Φ '' Ω ⊆ coneSet h J := by
    intro z hz
    rw [hG] at hz
    obtain ⟨hzU, hzq⟩ := hz
    have hgz : eval (h.pointOf z) g ≠ 0 := hUV hzU
    intro r hr
    have hspan : Ideal.span (Set.range q) ≤ RingHom.ker (eval (h.pointOf z)) :=
      Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hzq i)
    have h0 := hspan (hgen r hr)
    rw [RingHom.mem_ker, map_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left hgz
  refine ⟨e, Ω, Φ, U, hU, hyU, ?_, hΩ, hΦ, hGC, ?_⟩
  · rintro z ⟨hz, hzU⟩
    rw [hG]
    exact ⟨hzU, fun i => hz _ (hqJ i)⟩
  · intro x hx
    apply le_antisymm
    · rw [htanG x hx, hker, coneTangent_eq_comap]
      intro v hv
      simp only [Submodule.mem_comap] at hv ⊢
      rintro _ ⟨i, rfl⟩
      exact hv (q i) (hqJ i)
    · rintro _ ⟨v, rfl⟩
      intro r hr
      simp only [ContinuousLinearMap.coe_coe]
      by_cases hd : DifferentiableAt ℂ (graphPt e Φ) x
      · have hzero : (fun w => eval (h.pointOf w) r) ∘ graphPt e Φ =ᶠ[nhds x] fun _ => (0 : ℂ) := by
          filter_upwards [hΩ.mem_nhds hx] with w hw
          exact hGC ⟨w, hw, rfl⟩ r hr
        have hD := hzero.fderiv_eq (𝕜 := ℂ)
        rw [fderiv_const_apply, fderiv_comp x (hasFDerivAt_eval_pointOf h r _).differentiableAt hd] at hD
        have hDv := congrArg (fun L : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ => L v) hD
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.zero_apply,
          ContinuousLinearMap.zero_apply, fderiv_eval_pointOf_apply] at hDv
        exact hDv
      · rw [fderiv_zero_of_not_differentiableAt hd]
        have h0 : h.pointOf 0 = 0 := by simpa using h.pointOf_smul' 0 0
        simp [h0]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

variable {n : ℕ}

def HermNorm.pointEquiv (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (Matrix.toLinearEquiv' h.mat.transpose
      (Matrix.invertibleOfIsUnitDet _ (by rw [Matrix.det_transpose]; exact h.isUnit_det)))

theorem HermNorm.pointEquiv_apply (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.pointEquiv y = h.pointOf y := rfl

theorem hausdorffMeasure_pointOf_preimage_null (h : HermNorm n) {d : ℝ} (hd : 0 ≤ d)
    {S : Set (EuclideanSpace ℂ (Fin n))} (hS : μH[d] S = 0) :
    μH[d] {y | WithLp.toLp 2 (h.pointOf y) ∈ S} = 0 := by
  let E : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    h.pointEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let F := LinearMap.toContinuousLinearMap E.symm.toLinearMap
  refine measure_mono_null (t := F '' S) (fun y hy => ⟨E y, hy, ?_⟩) ?_
  · simp [F]
  · exact le_zero_iff.1 ((F.lipschitz.hausdorffMeasure_image_le hd S).trans (by rw [hS, mul_zero]))

theorem frameDeriv_basisFun (j : Fin n) (g : MvPolynomial (Fin n) ℂ) :
    frameDeriv (EuclideanSpace.basisFun (Fin n) ℂ) j g = pderiv j g := by
  simp [frameDeriv, EuclideanSpace.basisFun_apply, PiLp.single_apply, apply_ite C, ite_mul]

theorem finrank_coneTangent_of_jacobian (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ)
    (hf : ∀ k, f k ∈ J) (hs : ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f))
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ coneSet h J) (hsy : eval (h.pointOf y) s ≠ 0)
    (hD : eval (h.pointOf y) (frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f) ≠ 0) :
    finrank ℂ (coneTangent h J y) = I₀.card := by
  set x := h.pointOf y with hx
  let a : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun k j => eval x (pderiv j (f k))

  have hT : coneTangent h J y = (LinearMap.ker a.mulVecLin).comap h.pointEquiv.toLinearMap := by
    ext v
    simp only [coneTangent, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, HermNorm.pointEquiv_apply]
    constructor
    · intro hv
      funext k
      simpa [Matrix.mulVec, dotProduct, a] using hv (f k) (hf k)
    · intro hv q hq
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hs q hq)
      have hq0 : eval x q = 0 := hy q hq
      have hf0 : ∀ k, eval x (f k) = 0 := fun k => hy _ (hf k)
      have hder : ∀ j, eval x s * eval x (pderiv j q) = ∑ k, eval x (c k) * a k j := by
        intro j
        have := congrArg (fun P => eval x (pderiv j P)) hc
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, pderiv_mul, map_add (f := _), map_mul, hq0, hf0, mul_zero, zero_add] at this
        simpa [a, mul_comm] using this.symm
      have hk : ∀ k, ∑ j, a k j * h.pointOf v j = 0 := fun k => by
        simpa [Matrix.mulVec, dotProduct] using congrFun hv k
      have : eval x s * ∑ j, eval x (pderiv j q) * h.pointOf v j = 0 := by
        rw [Finset.mul_sum]
        simp_rw [← mul_assoc, hder, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc, ← Finset.mul_sum, hk, mul_zero, Finset.sum_const_zero]
      exact (mul_eq_zero.1 this).resolve_left hsy

  let M : Matrix {j // j ∉ I₀} {j // j ∉ I₀} ℂ := Matrix.of fun k j => a k j
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    convert hD using 1
    rw [frameJacobianDet, RingHom.map_det]
    congr 1
    ext k j
    simp [M, a, frameDeriv_basisFun]
  have hsurj : Function.Surjective a.mulVecLin := by
    intro t
    obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM t
    refine ⟨fun j => if hj : j ∉ I₀ then v ⟨j, hj⟩ else 0, ?_⟩
    rw [← hv]
    funext k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply]
    rw [← Finset.sum_subset (Finset.subset_univ I₀ᶜ) (fun j _ hj => by
      simp only [Finset.mem_compl, not_not] at hj; simp [hj]),
      Finset.sum_subtype I₀ᶜ (p := fun j => j ∉ I₀) (fun j => Finset.mem_compl)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [j.2]
  have hrank := LinearMap.finrank_range_add_finrank_ker a.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin] at hrank
  rw [hT, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hle : I₀.card ≤ n := by simpa using Finset.card_le_univ I₀
  omega

theorem ConeTangentDim.proof (hDim : ConeKrullDimLe.Statement) (hNull : NullSmaller.Statement)
    (hJac : FrameJacobianGeneric.Statement) : ConeTangentDim.Statement := by
  intro n m h J hJ hm hmn hfin
  have := hJ.isPrime
  rw [ae_restrict_iff' (isClosed_coneSet h J).measurableSet, ae_iff]
  rcases (hDim n m h J hJ hm hmn hfin).lt_or_eq with hlt | heq
  · refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m J hlt))
    exact fun q hq => (Classical.not_imp.1 hy).1 q hq
  · obtain ⟨I₀, f, s, hcard, hf, hsJ, hDJ, hspan⟩ :=
      hJac n m J hJ.isPrime heq (EuclideanSpace.basisFun (Fin n) ℂ)
    set D := frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f
    have hsD : s * D ∉ J := fun h' => (hJ.isPrime.mem_or_mem h').elim hsJ hDJ
    have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {s * D})) < m := by
      rw [← ringKrullDim_eq_of_ringEquiv
          (R := (MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) (Ideal.span {s * D}))
          (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {s * D})),
        Ideal.map_span, Set.image_singleton]
      have hnz : Ideal.Quotient.mk J (s * D) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
        mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
      rw [heq] at h1
      by_contra hge
      have h2 : ((m : ℕ) : WithBot ℕ∞) + 1 ≤
          ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J (s * D)}) + 1 := by
        gcongr; exact not_lt.1 hge
      have h3 := h2.trans h1
      exact absurd h3 (by exact_mod_cast (by omega : ¬ m + 1 ≤ m))
    refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m _ hdim))
    obtain ⟨hyC, hyT⟩ := Classical.not_imp.1 hy
    have hsD0 : eval (h.pointOf y) (s * D) = 0 := by
      by_contra hne
      rw [map_mul] at hne
      exact hyT (hcard ▸ finrank_coneTangent_of_jacobian h J I₀ f s hf hspan y hyC
        (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne))
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    change eval (h.pointOf y) (a + c * (s * D)) = 0
    rw [map_add (f := _), map_mul, hsD0, mul_zero, add_zero]
    exact hyC a ha

end

end GroundTheory.Heights₂.Heights
end

