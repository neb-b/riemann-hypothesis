module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyMulBaseChangeFiniteMapOfIsPushoutStatement
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout : ∀ {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field K']
    [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K'), (∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) →
    ∀ b : B, charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by
  first | exact @GlobalTheory.NormalDescent.charK_map_of_isPushout | exact GlobalTheory.NormalDescent.charK_map_of_isPushout | (intros; apply GlobalTheory.NormalDescent.charK_map_of_isPushout <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero : ∀ {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ} (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R), (∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) → M.charpolyRev * N.charpolyRev = 1 := by
  first | exact @GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | exact GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | (intros; apply GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtCoordinateCauchyIntegral
section
open Metric Filter Topology Set

noncomputable section

namespace GlobalTheory

def updCLM (n : ℕ) (k : Fin n) : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if i = k then ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ
    else (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)

theorem updCLM_apply (n : ℕ) (k : Fin n) (p : (Fin n → ℂ) × ℂ) :
    updCLM n k p = Function.update p.1 k p.2 := by
  funext i
  simp only [updCLM, ContinuousLinearMap.pi_apply, Function.update_apply]
  split_ifs <;> simp

theorem cauchyCoord_differentiableAt :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ),
      0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U →
      DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} →
      DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  intro n U k f z₀ r hr hz₀ hU hball hf
  set V : Set (Fin n → ℂ) := {z | z ∈ U ∧ z k ≠ 0} with hVdef
  have hV : IsOpen V := hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  have hfa : AnalyticOnNhd ℂ f V := ReciprocityTheory.AnForm.Osgood.osgood n V f hV hf
  set Φ : (Fin n → ℂ) × ℂ → ℂ := fun p => (p.2 - p.1 k)⁻¹ • f (Function.update p.1 k p.2) with hΦdef
  set Wd : Set ((Fin n → ℂ) × ℂ) := {p | Function.update p.1 k p.2 ∈ V ∧ p.2 - p.1 k ≠ 0} with hWdef
  have hupd : Continuous fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2 :=
    continuous_fst.update k continuous_snd
  have hWo : IsOpen Wd :=
    (hV.preimage hupd).inter (isOpen_ne_fun (continuous_snd.sub ((continuous_apply k).comp continuous_fst))
      continuous_const)
  have hΦa : AnalyticOnNhd ℂ Φ Wd := by
    intro p hp
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) p := by
      have he : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) = updCLM n k :=
        funext fun p => (updCLM_apply n k p).symm
      rw [he]; exact (updCLM n k).analyticAt p
    have h2 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => f (Function.update p.1 k p.2)) p :=
      AnalyticAt.comp (g := f) (f := fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) (hfa _ hp.1) h1
    have h3 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => p.2 - p.1 k) p :=
      analyticAt_snd.sub (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt _).comp
        analyticAt_fst)
    exact (h3.inv hp.2).smul h2
  have hΦc : ContinuousOn Φ Wd := hΦa.continuousOn
  have hD : ContinuousOn (fun p => fderiv ℂ Φ p) Wd :=
    (hΦa.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen hWo le_rfl

  set K : Set ((Fin n → ℂ) × ℂ) := closedBall z₀ (r / 2) ×ˢ sphere (0 : ℂ) r
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKW : K ⊆ Wd := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    simp only [mem_closedBall, mem_sphere_iff_norm, sub_zero] at hz ht
    have hzk : ‖z k‖ ≤ r / 2 := by
      have := dist_le_pi_dist z z₀ k
      rw [hz₀, dist_zero_right] at this
      linarith [this]
    refine ⟨⟨hball ?_, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_pi_le_iff hr.le]
      intro i
      by_cases hi : i = k
      · subst hi; simp [hz₀, ht]
      · rw [Function.update_of_ne hi]
        exact (dist_le_pi_dist z z₀ i).trans (by linarith)
    · simp only [Function.update_self]
      intro h; rw [h, norm_zero] at ht; linarith
    · intro h
      have : t = z k := sub_eq_zero.mp h
      rw [this] at ht; linarith
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hD.mono hKW)
  have hcirc : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ => circleMap_mem_sphere 0 hr.le θ
  have hmemW : ∀ z ∈ closedBall z₀ (r / 2), ∀ θ : ℝ, (z, circleMap 0 r θ) ∈ Wd := fun z hz θ =>
    hKW ⟨hz, hcirc θ⟩
  have hderc : Continuous fun θ => deriv (circleMap 0 r) θ := by
    have : (fun θ => deriv (circleMap 0 r) θ) = fun θ => circleMap 0 r θ * Complex.I :=
      funext fun θ => deriv_circleMap 0 r θ
    rw [this]; exact (continuous_circleMap 0 r).mul continuous_const
  have hpath : ∀ z : Fin n → ℂ, Continuous fun θ : ℝ => (z, circleMap 0 r θ) := fun z =>
    continuous_const.prodMk (continuous_circleMap 0 r)
  have hr2 : 0 < r / 2 := half_pos hr
  set F : (Fin n → ℂ) → ℝ → ℂ := fun z θ => deriv (circleMap 0 r) θ • Φ (z, circleMap 0 r θ)
  set F' : (Fin n → ℂ) → ℝ → (Fin n → ℂ) →L[ℂ] ℂ := fun z θ =>
    deriv (circleMap 0 r) θ • (fderiv ℂ Φ (z, circleMap 0 r θ)).comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ)
  have hFc : ∀ z ∈ closedBall z₀ (r / 2), Continuous (F z) := fun z hz =>
    hderc.smul (hΦc.comp_continuous (hpath z) (hmemW z hz))
  have hF'c : Continuous (F' z₀) :=
    hderc.smul ((hD.comp_continuous (hpath z₀) (hmemW z₀ (mem_closedBall_self hr2.le))).clm_comp
      continuous_const)
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := MeasureTheory.volume)
    (a := 0) (b := 2 * Real.pi) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun _ => r * (B * ‖ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ‖)) (ball_mem_nhds z₀ hr2)
    (eventually_of_mem (ball_mem_nhds z₀ hr2) fun z hz =>
      (hFc z (ball_subset_closedBall hz)).aestronglyMeasurable)
    ((hFc z₀ (mem_closedBall_self hr2.le)).intervalIntegrable _ _)
    hF'c.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      simp only [F', norm_smul]
      rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hB _ ⟨ball_subset_closedBall hz, hcirc θ⟩) (norm_nonneg _))) hr.le)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      have hd : DifferentiableAt ℂ Φ (z, circleMap 0 r θ) :=
        (hΦa _ (hmemW z (ball_subset_closedBall hz) θ)).differentiableAt
      exact (hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℂ) z (circleMap 0 r θ))).const_smul
        (deriv (circleMap 0 r) θ))
  exact key.differentiableAt

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral
section
open TensorProduct Polynomial

namespace GlobalTheory.DiscConductor

theorem isIntegral_trace_of_isIntegral
    (U L Ω : Type) [CommRing U] [Field L] [CommRing Ω] [Algebra U L] [Algebra L Ω] [Algebra U Ω]
    [IsScalarTower U L Ω] [Module.Finite L Ω] (ω : Ω) (h : IsIntegral U ω) :
    IsIntegral U (Algebra.trace L Ω ω) := by
  classical
  let b := Module.finBasis L Ω
  let A := AlgebraicClosure L
  let f : Ω →ₐ[U] Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A :=
    (((Algebra.ofId L A).mapMatrix).comp (Algebra.leftMulMatrix b)).restrictScalars U
  have hM : IsIntegral U (f ω) := h.map f
  have htr : algebraMap L A (Algebra.trace L Ω ω) = (f ω).trace := by
    rw [Algebra.trace_eq_matrix_trace b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := L) (B := A) , htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (f ω).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum A (f ω) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (f ω) (p.map (algebraMap U A)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (f ω) (p.map (algebraMap U A)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

theorem det_smul_eq_sum
    (U L Ω ι : Type) [CommRing U] [Field L] [CommRing Ω] [Algebra U L] [Algebra L Ω]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L Ω) (ω : Ω)
    (hG : ∀ i j, ∃ u : U, algebraMap U L u = Algebra.trace L Ω (b i * b j))
    (hω : ∀ i, ∃ u : U, algebraMap U L u = Algebra.trace L Ω (ω * b i)) :
    ∃ v : ι → U, (Algebra.traceMatrix L b).det • ω = ∑ j, algebraMap U L (v j) • b j := by
  choose g hg using hG
  choose w hw using hω
  have hG : (algebraMap U L).mapMatrix (Matrix.of g) = Algebra.traceMatrix L b := by
    ext i j
    simp [hg, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have h1 : (Algebra.traceMatrix L b).mulVec (b.equivFun ω) = fun i => algebraMap U L (w i) := by
    rw [Algebra.traceMatrix_of_basis_mulVec]
    ext i
    rw [hw]
  have h2 : (Algebra.traceMatrix L b).det • b.equivFun ω =
      fun j => algebraMap U L ((Matrix.of g).adjugate.mulVec w j) := by
    have h3 := congrArg ((Algebra.traceMatrix L b).adjugate.mulVec) h1
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
    rw [h3, ← hG, ← RingHom.map_adjugate]
    ext j
    simp [Matrix.mulVec, dotProduct]
  refine ⟨(Matrix.of g).adjugate.mulVec w, ?_⟩
  conv_lhs => rw [← b.sum_equivFun ω, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, ← congrFun h2 j]
  rfl

theorem exists_conductor_of_fractionFields
    (T U C F K L : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T]
    [CommRing U] [IsDomain U] [IsIntegrallyClosed U]
    [CommRing C] [IsDomain C] [Field F] [Field K] [Field L]
    [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F]
    [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L]
    [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K]
    [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L]
    [Module.Flat T U] [Module.Finite T C] :
    ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c →
      ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s =
        algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by
  classical
  obtain ⟨n, b, hbC, hbT⟩ := GlobalTheory.T.exists_basis_of_integral_with_trace_in_base T C F K
  obtain ⟨φ, hφi, hφ⟩ := _root_.GlobalTheory.flat_tensor_embeds_tensor_fractionFields T U C F K L
  have hφu := GlobalTheory.T.isUnit_map_of_mem_nonZeroDivisors_tensor' T U C F K L φ hφi hφ
  choose t ht using hbT
  choose e he using hbC
  let Gt : Matrix (Fin n) (Fin n) T := Matrix.of t
  have hG : (algebraMap T F).mapMatrix Gt = Algebra.traceMatrix F b := by
    ext i j
    simp [Gt, ht, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  haveI : FiniteDimensional F K := Module.Finite.of_basis b
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective T F)
  have hd : algebraMap T F Gt.det = (Algebra.traceMatrix F b).det := by
    rw [RingHom.map_det, hG]
  refine ⟨Gt.det, ?_, ?_⟩
  · intro h0
    apply Algebra.discr_not_zero_of_basis F b
    rw [Algebra.discr_def, ← hd, h0, map_zero]
  intro c hc
  let B : Module.Basis (Fin n) L (L ⊗[F] K) := b.baseChange L
  have hB : ∀ i, B i = 1 ⊗ₜ b i := fun i => Module.Basis.baseChange_apply L b i
  haveI : Module.Finite L (L ⊗[F] K) := Module.Finite.of_basis B
  have htr : ∀ x : K, Algebra.trace L (L ⊗[F] K) (1 ⊗ₜ x) = algebraMap F L (Algebra.trace F K x) := by
    intro x
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
      LinearMap.trace_baseChange]
  have htow : ∀ x : T, algebraMap F L (algebraMap T F x) = algebraMap U L (algebraMap T U x) := by
    intro x
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hBB : ∀ i j, algebraMap U L (algebraMap T U (t i j)) =
      Algebra.trace L (L ⊗[F] K) (B i * B j) := by
    intro i j
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, htr, ← ht, htow]
  let ψ : FractionRing (U ⊗[T] C) →+* L ⊗[F] K :=
    IsLocalization.lift (M := nonZeroDivisors (U ⊗[T] C)) (g := φ) (fun s => hφu s.1 s.2)
  have hψ : ∀ s, ψ (algebraMap (U ⊗[T] C) _ s) = φ s := fun s => IsLocalization.lift_eq _ s
  have hψi : Function.Injective ψ := by
    refine (RingHom.injective_iff_ker_eq_bot ψ).2 ((RingHom.ker_eq_bot_iff_eq_zero ψ).2 ?_)
    intro x hx
    obtain ⟨⟨s, r⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (U ⊗[T] C)) x
    have h1 := congrArg ψ h
    rw [map_mul, hx, zero_mul, hψ] at h1
    have h2 : s = 0 := hφi (by rw [map_zero]; exact h1.symm)
    rw [h2, map_zero] at h
    exact (IsLocalization.map_units (FractionRing (U ⊗[T] C)) r).mul_left_eq_zero.1 h
  have hω : IsIntegral U (ψ c) := by
    obtain ⟨p, hp, hpc⟩ := hc
    refine _root_.GlobalTheory.integral_of_finite_base_change_image T U C F K L φ hφ (ψ c) p hp ?_
    have h1 := congrArg ψ hpc
    rw [hom_eval₂, map_zero] at h1
    have h2 : ψ.comp (algebraMap (U ⊗[T] C) _) = φ := RingHom.ext hψ
    rwa [h2] at h1
  have hBi : ∀ i, IsIntegral U (B i) := by
    intro i
    refine _root_.GlobalTheory.integral_of_finite_base_change_image T U C F K L φ hφ (B i) (X - Polynomial.C (1 ⊗ₜ e i))
      (monic_X_sub_C _) ?_
    rw [eval₂_sub, eval₂_X, eval₂_C, hφ, map_one, he, hB, sub_self]
  obtain ⟨v, hv⟩ := det_smul_eq_sum U L (L ⊗[F] K) (Fin n) B (ψ c)
    (fun i j => ⟨_, hBB i j⟩) (fun i => IsIntegrallyClosed.isIntegral_iff.1
      (isIntegral_trace_of_isIntegral U L (L ⊗[F] K) _ (hω.mul (hBi i))))
  have hdet : (Algebra.traceMatrix L B).det = algebraMap U L (algebraMap T U Gt.det) := by
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp [Gt, hBB, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  refine ⟨∑ j, v j ⊗ₜ e j, hψi ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, hψ, hψ, map_sum, Algebra.TensorProduct.algebraMap_apply, hφ, map_one, ← hdet]
  have h1 : ((Algebra.traceMatrix L B).det ⊗ₜ[F] (1 : K)) * ψ c =
      (Algebra.traceMatrix L B).det • ψ c := by
    rw [Algebra.smul_def]; rfl
  rw [h1, hv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hφ, he, hB, smul_tmul', smul_eq_mul, mul_one]


attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
theorem discr_mul_mem_of_isIntegral : ∀ (T U C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T] [CommRing U] [IsDomain U] [IsIntegrallyClosed U] [Algebra T U] [Module.Flat T U] [CommRing C] [IsDomain C] [Algebra T C] [Module.Finite T C], Function.Injective (algebraMap T U) → Function.Injective (algebraMap T C) → ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c → ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s = algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by
  intro T U C _ _ _ _ _ _ _ _ _ _ _ _ _ hU hC
  haveI : FaithfulSMul T U := (faithfulSMul_iff_algebraMap_injective _ _).2 hU
  haveI : FaithfulSMul T C := (faithfulSMul_iff_algebraMap_injective _ _).2 hC
  exact exists_conductor_of_fractionFields T U C (FractionRing T) (FractionRing C) (FractionRing U)

end GlobalTheory.DiscConductor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpolyBaseChangeIntegrallyClosed
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent TensorProduct

namespace GlobalTheory.NormalDescent

theorem exists_map_eq_charK : ∀ {A B K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] (φ : A →+* B) (hφ : φ.Finite) (b : B),
    ∃ P : A[X], P.map (algebraMap A K) = charK φ hφ K b := by
  intro A B K _ _ _ _ _ _ _ φ hφ b
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  obtain ⟨g, hgm, hg⟩ := (Algebra.IsIntegral.isIntegral (R := A) b)
  have hT : aeval (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (g.map (algebraMap A K)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap]
    have : (1 : K) ⊗ₜ[A] b = Algebra.TensorProduct.includeRight b := rfl
    rw [this, Polynomial.aeval_algHom_apply, show aeval b g = 0 from hg, map_zero, map_zero]
  have hd := _root_.GlobalTheory.CharpolyDvd.main _ _ hT
  rw [← Polynomial.map_pow] at hd
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (hgm.pow _) hd
  refine ⟨P, ?_⟩
  have hm : (charK φ hφ K b).Monic := charK_monic φ hφ K b
  have : (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly = charK φ hφ K b := rfl
  rw [this, hm.leadingCoeff, C_1, mul_one] at hP
  exact hP

end GlobalTheory.NormalDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinearIndependentRatBasisAdaptedSubspaceStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIndependent_rat_basis_adapted_subspace : ∀ (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)), I ≤ L → Module.finrank ℚ L = g → ∃ rk : ℕ, rk ≤ g ∧ ∃ ε : Fin g → Fin r → ℚ, LinearIndependent ℚ ε ∧ (∀ i, ε i ∈ L) ∧ (∀ i : Fin g, i.val < rk → ε i ∈ I) ∧ ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i | i.val < rk}) := by
  first | exact @GlobalTheory.adapted_basis_extension | exact GlobalTheory.adapted_basis_extension | (intros; apply GlobalTheory.adapted_basis_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalSectionOfIsIntegralElemNormalScheme
section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem exists_section_of_isIntegralElem_of_isOpenImmersion {T Z : Scheme.{0}}
    [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j] :
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  intro hd U s hs u hu
  let C : irreducibleComponents Z := ⟨_, irreducibleComponent_mem_irreducibleComponents u⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, huW, hWle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show u ∈ ((U ⊓ IsNormalScheme.component C : Z.Opens) : Set Z) from
      ⟨hu, mem_irreducibleComponent⟩)
    (U ⊓ IsNormalScheme.component C).isOpen
  have hWU : W ≤ U := fun x hx ↦ (hWle hx).1
  refine ⟨W, hWU, huW, ?_⟩
  have hWirr : IsIrreducible (W : Set Z) :=
    ⟨⟨u, huW⟩, C.2.1.2.open_subset W.isOpen fun x hx ↦ (hWle hx).2⟩
  obtain ⟨_, _⟩ := IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWirr
  obtain ⟨x, hxW, hfr, hgen⟩ : ∃ (x : Z) (hxW : x ∈ W),
      (letI := Z.presheaf.algebra_section_stalk (U := W) ⟨x, hxW⟩;
        IsFractionRing Γ(Z, W) (Z.presheaf.stalk x)) ∧ ∀ w ∈ W, x ⤳ w := by
    let P : Spec Γ(Z, W) := ⟨⊥, Ideal.isPrime_bot⟩
    have hxW : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
    refine ⟨_, hxW, ?_, ?_⟩
    · let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
      have h := hW.isLocalization_stalk' P hxW
      have e : P.asIdeal.primeCompl = nonZeroDivisors Γ(Z, W) := by
        ext a
        simp [P, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
      unfold IsLocalization.AtPrime at h
      rw [e] at h
      exact h
    · intro w hw
      obtain ⟨q, rfl⟩ : w ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hw
      exact ((PrimeSpectrum.le_iff_specializes P q).mp bot_le).map hW.fromSpec.continuous
  obtain ⟨y, rfl⟩ : x ∈ Set.range j := by
    obtain ⟨w, hw, hwr⟩ := hd.inter_open_nonempty _ W.isOpen ⟨u, huW⟩
    exact (hgen w hw).mem_open j.isOpenEmbedding.isOpen_range hwr
  let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
  let _ : Algebra Γ(Z, W) Γ(T, j ⁻¹ᵁ W) := (j.app W).hom.toAlgebra
  have hyW : y ∈ j ⁻¹ᵁ W := hxW
  have hnat : (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op).hom.comp (j.app U).hom =
      (algebraMap Γ(Z, W) Γ(T, j ⁻¹ᵁ W)).comp (Z.presheaf.map (homOfLE hWU).op).hom := by
    change _ = (j.app W).hom.comp _
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, j.naturality]
    rfl
  have hs₁ : IsIntegral Γ(Z, W) (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) := by
    obtain ⟨p, hp, hps⟩ := hs
    refine ⟨p.map (Z.presheaf.map (homOfLE hWU).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hnat, ← Polynomial.hom_eval₂, hps, map_zero]
  have hgerm (a : Γ(Z, W)) : j.stalkMap y (Z.presheaf.germ W (j y) hxW a) =
      T.presheaf.germ (j ⁻¹ᵁ W) y hyW (j.app W a) :=
    j.germ_stalkMap_apply W y hxW a
  have hbij : Function.Bijective (j.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  let φ : Γ(T, j ⁻¹ᵁ W) ⟶ Z.presheaf.stalk (j y) :=
    T.presheaf.germ (j ⁻¹ᵁ W) y hyW ≫ inv (j.stalkMap y)
  have hφ (c : Γ(T, j ⁻¹ᵁ W)) : j.stalkMap y (φ c) = T.presheaf.germ (j ⁻¹ᵁ W) y hyW c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(T, j ⁻¹ᵁ W) →ₐ[Γ(Z, W)] Z.presheaf.stalk (j y) :=
    { φ.hom with commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.map ψ hs₁)
  refine ⟨a, ?_⟩
  have hg : T.presheaf.germ (j ⁻¹ᵁ W) y hyW
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) = 0 := by
    rw [map_sub, ← hgerm, ← hφ, sub_eq_zero]
    exact congr(j.stalkMap y $ha)
  have : IsReduced T := isReduced_of_isOpenImmersion j
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro t ht
  have hyt : y ⤳ t :=
    j.isOpenEmbedding.isInducing.specializes_iff.mp (hgen _ (T.basicOpen_le _ ht))
  have hy : y ∈ T.basicOpen
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) :=
    hyt.mem_open (T.basicOpen _).isOpen ht
  rw [Scheme.mem_basicOpen _ _ _ hyW, hg] at hy
  exact (not_isUnit_zero hy).elim

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegrallyClosedOfConductorNonZeroDivisorOfAssStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P)) → (∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) → IsIntegrallyClosed R := by
  first | exact @GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | exact GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | (intros; apply GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
section
open IsLocalRing

namespace GlobalTheory.AdicNoeth

theorem isNoetherianRing_adicCompletion : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsNoetherianRing (AdicCompletion I R) := by
  intro R _ _ I
  have fg : I.FG := I.fg_of_isNoetherianRing
  have hc := AdicCompletion.isAdicComplete_self I fg
  have e : (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) ≃+* R ⧸ I := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I)
  exact isNoetherianRing_of_isAdicComplete _ _ (fg.map _) hc
    (isNoetherianRing_of_ringEquiv _ e.symm)

end GlobalTheory.AdicNoeth
end

