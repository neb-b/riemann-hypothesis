module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GramDetSandwich
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameGraphGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem FrameGraphGeneric.proof (hA : FrameJacobianGeneric.Statement) (hB : FrameImplicitGraph.Statement) :
    FrameGraphGeneric.Statement := by
  intro n d J hJ hd b
  obtain ⟨I₀, f, s, hcard, hfJ, hs, hM, hgen⟩ := hA n d J hJ hd b
  refine ⟨I₀, frameJacobianDet b I₀ f * s, hcard, fun h => (hJ.mem_or_mem h).elim hM hs, ?_⟩
  intro z hz hq
  rw [map_mul] at hq
  set W : Set (EuclideanSpace ℂ (Fin n)) := {x | eval (fun i => x i) s ≠ 0} with hWdef
  have hW : IsOpen W := isOpen_ne_fun ((MvPolynomial.continuous_eval s).comp
    (by fun_prop : Continuous fun x : EuclideanSpace ℂ (Fin n) => fun i => x i)) continuous_const
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hVW, hg, hproj, hgraph⟩ :=
    hB n b I₀ f z (fun k => hz _ (hfJ k)) (left_ne_zero_of_mul hq) W hW (right_ne_zero_of_mul hq)
  refine ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, ?_⟩
  rw [← hgraph]
  ext x
  simp only [zeroSetEuc, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxV⟩
    exact ⟨fun k => hx _ (hfJ k), hxV⟩
  · rintro ⟨hx, hxV⟩
    refine ⟨fun p hp => ?_, hxV⟩
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker (eval fun i => x i) :=
      Ideal.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact RingHom.mem_ker.mpr (hx k))
    have h0 := RingHom.mem_ker.mp (hle (hgen p hp))
    rw [map_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hVW hxV)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameImplicitGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

namespace FrameImplicitGraph

variable {n : ℕ}

def polyDeriv (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
  ∑ l, eval (fun i => x i) (pderiv l p) • EuclideanSpace.proj l

theorem polyDeriv_apply (p : MvPolynomial (Fin n) ℂ) (x v : EuclideanSpace ℂ (Fin n)) :
    polyDeriv p x v = ∑ l, eval (fun i => x i) (pderiv l p) * v l := by
  simp [polyDeriv]

theorem hasStrictFDerivAt_eval (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) => eval (fun i => y i) p) (polyDeriv p x) x :=
  _root_.UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval p x

def projCLM (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) :=
  ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i)

def phi (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    (I → ℂ) × ({j // j ∉ I} → ℂ) :=
  (frameProj b I x, fun k => eval (fun i => x i) (f k))

def phiDeriv (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ) :=
  (projCLM b I).prod (ContinuousLinearMap.pi fun k => polyDeriv (f k) x)

theorem hasStrictFDerivAt_phi (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    HasStrictFDerivAt (phi b I f) (phiDeriv b I f x) x :=
  (projCLM b I).hasStrictFDerivAt.prodMk (hasStrictFDerivAt_pi.2 fun k => hasStrictFDerivAt_eval (f k) x)

theorem phiDeriv_injective (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hx : eval (fun i => x i) (frameJacobianDet b I f) ≠ 0) :
    Function.Injective (phiDeriv b I f x) := by
  refine (injective_iff_map_eq_zero (phiDeriv b I f x)).2 fun v hv => ?_
  set c : Fin n → ℂ := fun j => inner ℂ (b j) v with hc
  have h1 : ∀ i ∈ I, c i = 0 := fun i hi => by
    have := congrFun (congrArg Prod.fst hv) ⟨i, hi⟩
    simpa [phiDeriv, projCLM, c] using this
  have hvl : ∀ l, v l = ∑ j, c j * b j l := fun l => by
    have := congrArg (fun y : EuclideanSpace ℂ (Fin n) => y l) (b.sum_repr' v)
    simpa [c, smul_eq_mul] using this.symm
  have h2 : ∀ k, ∑ j, c j * eval (fun i => x i) (frameDeriv b j (f k)) = 0 := fun k => by
    have := congrFun (congrArg Prod.snd hv) k
    simp only [phiDeriv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply, polyDeriv_apply,
      Prod.snd_zero, Pi.zero_apply] at this
    rw [← this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [frameDeriv, map_sum, map_mul, eval_C, hvl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  let M : Matrix {j // j ∉ I} {j // j ∉ I} ℂ := Matrix.of fun k j => eval (fun i => x i) (frameDeriv b j (f k))
  have hM : M.det ≠ 0 := by
    have : eval (fun i => x i) (frameJacobianDet b I f) = M.det := by
      rw [frameJacobianDet, RingHom.map_det]
      rfl
    rwa [← this]
  have hMc : M.mulVec (fun j => c j) = 0 := by
    funext k
    rw [Pi.zero_apply, ← h2 k, ← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ I)]
    simp [M, Matrix.mulVec, dotProduct, h1, mul_comm]
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hM hMc
  have hc0 : ∀ j, c j = 0 := fun j => by
    by_cases hj : j ∈ I
    · exact h1 j hj
    · exact congrFun h3 ⟨j, hj⟩
  have hv' : v = ∑ j, c j • b j := (b.sum_repr' v).symm
  rw [hv']
  simp [hc0]

theorem finrank_eq (I : Finset (Fin n)) :
    Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Module.finrank ℂ ((I → ℂ) × ({j // j ∉ I} → ℂ)) := by
  have h1 : Fintype.card {j // j ∉ I} = n - I.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp
  have h2 : I.card ≤ n := by simpa using I.card_le_univ
  simp only [finrank_euclideanSpace, Fintype.card_fin, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    h1, Fintype.card_coe]
  omega

theorem phiDeriv_equiv (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hx : eval (fun i => x i) (frameJacobianDet b I f) ≠ 0) :
    ∃ e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ),
      (e : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ)) = phiDeriv b I f x := by
  refine ⟨(LinearMap.linearEquivOfInjective (phiDeriv b I f x : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] _)
    (phiDeriv_injective b I f x hx) (finrank_eq I)).toContinuousLinearEquiv, ?_⟩
  ext v
  all_goals simp [LinearMap.linearEquivOfInjective_apply]

theorem continuous_eval (p : MvPolynomial (Fin n) ℂ) :
    Continuous fun y : EuclideanSpace ℂ (Fin n) => eval (fun i => y i) p :=
  continuous_iff_continuousAt.2 fun x => (hasStrictFDerivAt_eval p x).continuousAt

theorem proof : FrameImplicitGraph.Statement := by
  intro n b I f z hz hdet U hU hzU
  obtain ⟨e0, he0⟩ := phiDeriv_equiv b I f z hdet
  have hs : HasStrictFDerivAt (phi b I f)
      (e0 : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ)) z :=
    he0 ▸ hasStrictFDerivAt_phi b I f z
  let e := hs.toOpenPartialHomeomorph (phi b I f)
  have hecoe : (e : EuclideanSpace ℂ (Fin n) → (I → ℂ) × ({j // j ∉ I} → ℂ)) = phi b I f := rfl
  let W := {x : EuclideanSpace ℂ (Fin n) | eval (fun i => x i) (frameJacobianDet b I f) ≠ 0}
  have hW : IsOpen W := isOpen_ne_fun (continuous_eval _) continuous_const
  let V := e.source ∩ U ∩ W
  have hV : IsOpen V := (e.open_source.inter hU).inter hW
  let ι : (I → ℂ) → (I → ℂ) × ({j // j ∉ I} → ℂ) := fun w => (w, 0)
  have hι : Continuous ι := continuous_id.prodMk continuous_const
  refine ⟨ι ⁻¹' (e.target ∩ e.symm ⁻¹' V), V, fun w => e.symm (ι w),
    (e.continuousOn_symm.isOpen_inter_preimage e.open_target hV).preimage hι, hV,
    ⟨⟨hs.mem_toOpenPartialHomeomorph_source, hzU⟩, hdet⟩, fun x hx => hx.1.2, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨ex, hex⟩ := phiDeriv_equiv b I f _ hw.2.2
    have hd : HasFDerivAt e (ex : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ))
        (e.symm (ι w)) := by
      rw [hecoe, hex]
      exact (hasStrictFDerivAt_phi b I f _).hasFDerivAt
    have hιd : HasFDerivAt ι ((ContinuousLinearMap.id ℂ (I → ℂ)).prod 0) w :=
      (hasFDerivAt_id w).prodMk (hasFDerivAt_const 0 w)
    exact ((e.hasFDerivAt_symm hw.1 hd).comp w hιd).differentiableAt.differentiableWithinAt
  · intro w hw
    have := congrArg Prod.fst (e.right_inv hw.1)
    rw [hecoe] at this
    exact this
  · ext x
    constructor
    · rintro ⟨hx0, hxV⟩
      have hex : e x = ι (frameProj b I x) := by
        rw [hecoe]
        exact Prod.ext rfl (funext hx0)
      refine ⟨frameProj b I x, ⟨?_, ?_⟩, ?_⟩
      · rw [← hex]; exact e.map_source hxV.1.1
      · show e.symm (ι (frameProj b I x)) ∈ V
        rw [← hex, e.left_inv hxV.1.1]; exact hxV
      · show e.symm (ι (frameProj b I x)) = x
        rw [← hex, e.left_inv hxV.1.1]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨fun k => ?_, hw.2⟩
      have := congrArg (fun p => p.2 k) (e.right_inv hw.1)
      rw [hecoe] at this
      exact this

end FrameImplicitGraph

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGramDetSandwich
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem GramDetSandwich.loewner_inv {N : ℕ} (hN : 0 < N) (H : Matrix (Fin N) (Fin N) ℂ) (c M : ℝ)
    (hc : 0 < c) (hH : H.PosDef)
    (h1 : (H⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef)
    (h2 : ((M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - H⁻¹).PosSemidef) :
    c ≤ M ∧ (H - ((M⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
      (((c⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - H).PosSemidef := by
  have hcM : c ≤ M := by
    have h3 := (h1.add h2).diag_nonneg (i := ⟨0, hN⟩)
    simp only [sub_add_sub_cancel', Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
      mul_one] at h3
    have h4 : (0 : ℂ) ≤ ((M - c : ℝ) : ℂ) := by push_cast; linear_combination h3
    linarith [Complex.zero_le_real.mp h4]
  have hM : 0 < M := hc.trans_le hcM
  have hHu : IsUnit H.det := (isUnit_iff_isUnit_det H).mp hH.isUnit
  refine ⟨hcM, ?_, ?_⟩
  · have hpos : IsStrictlyPositive H⁻¹ := hH.inv.isStrictlyPositive
    have hle : H⁻¹ ≤ (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := h2
    have := CStarAlgebra.ringInverse_le_ringInverse hle hpos
    rw [← nonsing_inv_eq_ringInverse, ← nonsing_inv_eq_ringInverse, nonsing_inv_nonsing_inv _ hHu] at this
    have hinv : ((M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = ((M⁻¹ : ℝ) : ℂ) • 1 := by
      apply inv_eq_left_inv
      rw [smul_mul_smul_comm, Matrix.one_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hM.ne',
        Complex.ofReal_one, one_smul]
    rw [hinv] at this
    exact this
  · have hpos : IsStrictlyPositive ((c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
      (PosDef.one.smul (by exact_mod_cast hc)).isStrictlyPositive
    have hle : (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) ≤ H⁻¹ := h1
    have := CStarAlgebra.ringInverse_le_ringInverse hle hpos
    rw [← nonsing_inv_eq_ringInverse, ← nonsing_inv_eq_ringInverse, nonsing_inv_nonsing_inv _ hHu] at this
    have hinv : ((c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = ((c⁻¹ : ℝ) : ℂ) • 1 := by
      apply inv_eq_left_inv
      rw [smul_mul_smul_comm, Matrix.one_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne',
        Complex.ofReal_one, one_smul]
    rw [hinv] at this
    exact this

theorem GramDetSandwich.re_det_ofReal_smul {k : ℕ} (t : ℝ) (X : Matrix (Fin k) (Fin k) ℂ) :
    ((t : ℂ) • X).det.re = t ^ k * X.det.re := by
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem GramDetSandwich.proof : GramDetSandwich.Statement := by
  intro N k H A c M hc hH h1 h2
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have e1 : Aᴴ * A = 0 := by ext i j; simp [Matrix.mul_apply]
    have e2 : Aᴴ * H * A = 0 := by ext i j; simp [Matrix.mul_apply]
    rw [e1, e2]
    rcases k with _ | k
    · simp
    · simp [det_zero]
  obtain ⟨hcM, hlo, hhi⟩ := GramDetSandwich.loewner_inv hN H c M hc hH h1 h2
  have hM : 0 < M := hc.trans_le hcM
  have hG : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  have hlo' : (Aᴴ * H * A - ((M⁻¹ : ℝ) : ℂ) • (Aᴴ * A)).PosSemidef := by
    have := hlo.conjTranspose_mul_mul_same A
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at this
  have hhi' : (((c⁻¹ : ℝ) : ℂ) • (Aᴴ * A) - Aᴴ * H * A).PosSemidef := by
    have := hhi.conjTranspose_mul_mul_same A
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at this
  have k1 := MCDet.re_det_mono (hG.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hM.le))) hlo'
  have k2 := MCDet.re_det_mono (hH.posSemidef.conjTranspose_mul_mul_same A) hhi'
  simp only [RCLike.re_to_complex] at k1 k2
  rw [GramDetSandwich.re_det_ofReal_smul] at k1 k2
  exact ⟨k1, k2⟩

end GroundTheory.Heights₂.Heights.NineStatements
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJacobianRankGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem JacobianRankGeneric.kaehler_D_aeval {σ K : Type*} [Fintype σ] [Field K] [Algebra ℂ K] (x : σ → K)
    (f : MvPolynomial σ ℂ) :
    KaehlerDifferential.D ℂ K (aeval x f) =
      ∑ l, aeval x (pderiv l f) • KaehlerDifferential.D ℂ K (x l) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib, add_smul]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, Finset.smul_sum, smul_smul, map_add (f := _), add_smul,
      Finset.sum_add_distrib, pderiv_X, smul_eq_mul, Pi.single_apply]
    rw [add_left_inj]
    simp [apply_ite, ite_smul]

theorem JacobianRankGeneric.finrank_kaehler_eq_card {k K : Type} [Field k] [Field K] [Algebra k K] (s : Finset K)
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    (H : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K) :
    Module.finrank K Ω[K⁄k] = s.card := by
  have hx : AlgebraicIndependent k (fun i : s => (i : K)) := hs.1
  let _ : Algebra (MvPolynomial s k) K := (aeval (fun i : s => (i : K))).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial s k) K := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  let _ : Algebra (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    ((hx.aevalEquivField).toRingHom.comp (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)))).toAlgebra
  let e : FractionRing (MvPolynomial s k) ≃ₐ[MvPolynomial s k]
      IntermediateField.adjoin k (Set.range fun i : s => (i : K)) :=
    { hx.aevalEquivField with commutes' := fun q => rfl }
  have : Algebra.FormallyEtale (MvPolynomial s k) (FractionRing (MvPolynomial s k)) :=
    .of_isLocalization (nonZeroDivisors _)
  have : Algebra.FormallyEtale (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    .of_equiv e
  have : IsScalarTower (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    IsScalarTower.of_algebraMap_eq fun q => by
      change aeval (fun i : s => (i : K)) q =
        ((hx.aevalEquivField (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) q) : _) : K)
      rw [hx.aevalEquivField_algebraMap_apply_coe]
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K := by
    convert! H <;> simp
  have : Algebra.FormallyEtale (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    .of_isSeparable _ K
  have : Algebra.FormallyEtale (MvPolynomial s k) K :=
    .comp (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K
  have : Module.Free (MvPolynomial s k) Ω[MvPolynomial s k⁄k] :=
    Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis k s)
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial s k) K).finrank_eq,
    Module.finrank_baseChange, Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k s),
    Fintype.card_coe]

theorem JacobianRankGeneric.proof : JacobianRankGeneric.Statement := by
  classical
  intro n d J _ hd
  set A := MvPolynomial (Fin n) ℂ ⧸ J
  set K := FractionRing A

  let ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ A K).comp (Ideal.Quotient.mkₐ ℂ J)
  let x : Fin n → K := fun l => ψ (X l)
  have hψ : ∀ f, ψ f = aeval x f := fun f => congrArg (fun φ => φ f) (MvPolynomial.aeval_unique ψ)
  have hgrad : ∀ f l, genericGradient J f l = aeval x (pderiv l f) := fun f l => hψ (pderiv l f)
  let Φ : (Fin n → K) →ₗ[K] Ω[K⁄ℂ] :=
    ∑ l, (LinearMap.proj l : (Fin n → K) →ₗ[K] K).smulRight (KaehlerDifferential.D ℂ K (x l))
  have hΦ : ∀ w, Φ w = ∑ l, w l • KaehlerDifferential.D ℂ K (x l) := fun w => by
    simp [Φ, LinearMap.sum_apply]

  have hker : Submodule.span K (genericGradient J '' (J : Set _)) ≤ LinearMap.ker Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h0 : aeval x f = 0 := by
      rw [← hψ]
      simp only [ψ, AlgHom.comp_apply]
      rw [show Ideal.Quotient.mkₐ ℂ J f = 0 from Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hΦ, hgrad]
    rw [← JacobianRankGeneric.kaehler_D_aeval, h0, map_zero]

  have hsurj : LinearMap.range Φ = ⊤ := by
    have hA : ∀ f, KaehlerDifferential.D ℂ K (ψ f) ∈ LinearMap.range Φ := fun f =>
      ⟨fun l => aeval x (pderiv l f), by rw [hΦ, hψ, JacobianRankGeneric.kaehler_D_aeval]⟩
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, v, _, rfl⟩ := IsFractionRing.div_surjective (A := A) a
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hf := hA f
    have hg := hA g
    change KaehlerDifferential.D ℂ K (ψ f / ψ g) ∈ _
    rw [Derivation.leibniz_div]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg))

  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField ℂ K
  have hcard : s.card = d := by
    have h1 := hs.cardinalMk_eq_trdeg
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing ℂ (A := A) K
    rw [hd, ← h1, Cardinal.mk_coe_finset] at h2
    simp at h2
    exact_mod_cast h2.symm
  have hrank : Module.finrank K Ω[K⁄ℂ] = d := by
    rw [JacobianRankGeneric.finrank_kaehler_eq_card s hs H, hcard]

  have h1 := Submodule.finrank_mono hker
  have h2 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, finrank_top, hrank, Module.finrank_fin_fun] at h2
  change Module.finrank K (Submodule.span K (genericGradient J '' (J : Set _))) ≤ n - d
  calc _ ≤ _ := h1
    _ = n - d := by
      generalize Module.finrank K (LinearMap.ker Φ) = m at h2 ⊢
      omega

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNumberFieldBoxCountX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem NumberFieldBoxCount.proof_closed : NumberFieldBoxCount.Statement :=
  NumberFieldBoxCount.proof LatticeImageZLattice.proof CovolumeRelIndex.proof EmbeddingSumPlaces.proof
    (MixedBoxCount.proof LatticeCountVolume.proof)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StConormalGenerationGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def ConormalGenerationGeneric.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] (ι : Type) [Fintype ι]
    (f : ι → MvPolynomial (Fin n) ℂ),
    (∀ i, f i ∈ J) →
    Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (Set.range (genericGradient J ∘ f)) =
      Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (genericGradient J '' (J : Set _)) →
    ∃ s : MvPolynomial (Fin n) ℂ, s ∉ J ∧ ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights
end

