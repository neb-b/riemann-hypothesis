module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import GroundTheory.AutomorphicForms.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.NormApplyLeOfLaplacianLowerBound
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_apply_le_of_laplacian_lower_bound :
    ∀ (d : ℕ) (c C : ℝ) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) → ∃ C' : ℝ, ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (A : Fin d → Module.End ℂ M), (∀ i, ∀ x ∈ V, A i x ∈ V) → (∀ i, ∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (A i x)) (j y) + inner ℂ (j x) (j (A i y)) = 0) → ∀ v ∈ V, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re → (∀ i, ε i = -1 → ‖j (A i v)‖ ≤ C * ‖j v‖) → ∀ i, ‖j (A i v)‖ ≤ C' * ‖j v‖ := by
  intro d c C ε hε
  refine ⟨Real.sqrt (|c| + (d + 1) * C ^ 2), ?_⟩
  intro M H _ _ _ _ j V A hA hskew v hv hcas hC i
  have h1 : ∀ k, inner ℂ (j v) (j (A k (A k v))) = -((‖j (A k v)‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have h := hskew k v hv (A k v) (hA k v hv)
    rw [inner_self_eq_norm_sq_to_K] at h
    push_cast
    exact eq_neg_of_add_eq_zero_right h
  have h2 : (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re
      = -∑ k, ε k * ‖j (A k v)‖ ^ 2 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, inner_smul_right, h1 k, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  rw [h2] at hcas
  have h3 : ∀ k, ε k = -1 → ‖j (A k v)‖ ^ 2 ≤ C ^ 2 * ‖j v‖ ^ 2 := by
    intro k hk
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC k hk) 2
  have hCN : 0 ≤ C ^ 2 * ‖j v‖ ^ 2 := by positivity
  have h4 : ∀ k, 0 ≤ ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2 := by
    intro k
    rcases hε k with hk | hk
    · rw [hk]; positivity
    · have := h3 k hk
      rw [hk]; linarith
  have h5 : ε i * ‖j (A i v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2
      ≤ ∑ k, (ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2) :=
    Finset.single_le_sum (f := fun k => ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2)
      (fun k _ => h4 k) (Finset.mem_univ i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h5
  have hc : c * ‖j v‖ ^ 2 ≤ |c| * ‖j v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
  have hc0 : 0 ≤ |c| * ‖j v‖ ^ 2 := by positivity
  have hd : 0 ≤ (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) := by positivity
  have h6 : ‖j (A i v)‖ ^ 2 ≤ (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2 := by
    have e : (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2
        = |c| * ‖j v‖ ^ 2 + (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) + C ^ 2 * ‖j v‖ ^ 2 := by ring
    rw [e]
    rcases hε i with hk | hk
    · rw [hk] at h5; linarith
    · have := h3 i hk
      linarith
  have h7 := Real.le_sqrt_of_sq_le h6
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] at h7
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.NormExpSmulSubLeNormDerivOp
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_exp_smul_sub_le_norm_derivOp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E) (X : 𝔤), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → ‖π (h.expG X) v - v‖ ≤ ‖h.derivOp π X v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h E _ _ π v X hπ hv
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => π (h.expG (s • X)) v)
      (π (h.expG (t • X)) (h.derivOp π X v)) t := by
    intro t
    have h2 := ((π (h.expG (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (h.hasDerivAt_derivOp π hv X)
    have h3 : HasDerivAt (fun s : ℝ => π (h.expG ((t + s) • X)) v)
        (π (h.expG (t • X)) (h.derivOp π X v)) (t - t) := by
      rw [sub_self]
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
      rw [h.expG_add_smul, BanachRep.map_mul_apply]
    have h4 := h3.comp_sub_const t t
    simpa only [add_sub_cancel] using h4
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => π (h.expG (s • X)) v)
    (f' := fun t : ℝ => π (h.expG (t • X)) (h.derivOp π X v)) (C := ‖h.derivOp π X v‖)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => (hπ _ _).le)
  simpa using hm
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.NormSkewAdjointLeOfEigenvalueBound
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_skewAdjoint_le_of_eigenvalue_bound :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (D : Module.End ℂ E) (M : ℝ), (∀ x y, inner ℂ (D x) y + inner ℂ x (D y) = 0) → (∀ z : ℂ, D.HasEigenvalue z → ‖z‖ ≤ M) → ∀ x, ‖D x‖ ≤ M * ‖x‖ := by
  intro E _ _ _ D M hskew hev x
  have hT : (Complex.I • D : E →ₗ[ℂ] E).IsSymmetric := by
    intro x y
    have h := hskew x y
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_I]
    linear_combination (-Complex.I) * h
  have hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  have hb : ∀ i, |hT.eigenvalues hn i| ≤ M := by
    intro i
    have h1 := hT.apply_eigenvectorBasis hn i
    have h2 : D (hT.eigenvectorBasis hn i) = (-Complex.I * (hT.eigenvalues hn i : ℂ)) • hT.eigenvectorBasis hn i := by
      have h3 : D (hT.eigenvectorBasis hn i) = (-Complex.I) • ((Complex.I • D : E →ₗ[ℂ] E) (hT.eigenvectorBasis hn i)) := by
        rw [LinearMap.smul_apply, smul_smul]; simp
      rw [h3, h1, smul_smul]; rfl
    have h4 : D.HasEigenvalue (-Complex.I * (hT.eigenvalues hn i : ℂ)) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 h2, (hT.eigenvectorBasis hn).orthonormal.ne_zero i⟩
    have h5 := hev _ h4
    simpa using h5
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : x = 0 := Subsingleton.elim _ _
    subst this
    simp
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb ⟨0, Module.finrank_pos⟩)
  have hDx : ‖D x‖ = ‖(Complex.I • D : E →ₗ[ℂ] E) x‖ := by
    simp [norm_smul]
  rw [hDx, ← (hT.eigenvectorBasis hn).repr.norm_map ((Complex.I • D : E →ₗ[ℂ] E) x),
    ← (hT.eigenvectorBasis hn).repr.norm_map x]
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h6 := hT.eigenvectorBasis_apply_self_apply hn x i
  rw [h6, norm_mul, mul_pow]
  gcongr
  simpa using hb i
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.NormTraceCompLeMulTraceNorm
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.norm_trace_comp_le_mul_traceNorm :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ι : Type) (b : HilbertBasis ι ℂ H) (T D : H →L[ℂ] H) (c : ℝ), 0 ≤ c → IsTraceClass T → (∀ i, ∃ d : ℂ, ‖d‖ ≤ c ∧ T (D (b i)) = d • T (b i)) → ‖trace (D ∘L T)‖ ≤ c * (traceNorm T).toReal := by
  intro H _ _ _ ι b T D c hc hT hd
  have hs := hT.summable_norm_inner b
  have h1 := (hT.comp_right D).hasSum_trace b
  rw [trace_comp_comm hT D]
  have h2 : ‖trace (T ∘L D)‖ ≤ ∑' i, c * ‖inner ℂ (b i) (T (b i))‖ :=
    h1.norm_le_of_bounded (hs.mul_left c).hasSum fun i => by
      obtain ⟨d, hd1, hd2⟩ := hd i
      rw [ContinuousLinearMap.comp_apply, hd2, inner_smul_right, norm_mul]
      exact mul_le_mul_of_nonneg_right hd1 (norm_nonneg _)
  have h3 : ∑' i, ‖inner ℂ (b i) (T (b i))‖ ≤ (traceNorm T).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal (show traceNorm T < ⊤ from hT).ne,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    simp only [ofReal_norm]
    exact tsum_enorm_inner_self_le b T
  rw [tsum_mul_left] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h3 hc)
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.PrjEigInOfEigenvectorPrj
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.prj_eigIn_of_eigenvector_prj :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → ∀ (v : H) (μ x : ℝ), A (prj W v) = (μ : ℂ) • prj W v → prj (eigIn W A x) v = if x = μ then prj W v else 0 := by
  intro H _ _ _ W A hW hA v μ x hv
  have hWc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hPW : prj W v ∈ W := by
    have : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hWc] at this
  have hperp : ∀ w ∈ W, inner ℂ w (v - prj W v) = 0 := by
    intro w hw
    have : v - prj W v ∈ W.topologicalClosureᗮ := Submodule.sub_starProjection_mem_orthogonal v
    exact this w (W.le_topologicalClosure hw)
  have hmem : ∀ w, w ∈ eigIn W A x ↔ w ∈ W ∧ A w = (x : ℂ) • w := by
    intro w
    simp [eigIn, Module.End.mem_eigenspace_iff]
  have key : ∀ u ∈ eigIn W A x, (∀ w ∈ eigIn W A x, inner ℂ w (v - u) = 0) →
      prj (eigIn W A x) v = u := by
    intro u hu h
    refine Submodule.eq_starProjection_of_mem_orthogonal
      ((eigIn W A x).le_topologicalClosure hu) ?_
    rw [Submodule.orthogonal_closure]
    exact fun w hw => h w hw
  split_ifs with hx
  · subst hx
    exact key _ ((hmem _).2 ⟨hPW, hv⟩) fun w hw => hperp w ((hmem w).1 hw).1
  · refine key 0 (Submodule.zero_mem _) fun w hw => ?_
    obtain ⟨hwW, hwA⟩ := (hmem w).1 hw
    have h1 : inner ℂ (A w) (prj W v) = inner ℂ w (A (prj W v)) :=
      hA.isSymmetric w (prj W v)
    rw [hwA, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
    have h2 : inner ℂ w (prj W v) = 0 := by
      by_contra h0
      exact hx (by exact_mod_cast mul_right_cancel₀ h0 h1)
    have h3 := hperp w hwW
    rw [inner_sub_right, h2] at h3
    rw [inner_sub_right, inner_zero_right]
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ReInnerGeOfSpanEigenvectors
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.re_inner_ge_of_span_eigenvectors :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (T : Module.End ℂ M) (c : ℝ) (s : Set M), (∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (T x)) (j y) = inner ℂ (j x) (j (T y))) → (∀ x ∈ s, x ∈ V ∧ ∃ κ : ℂ, -c ≤ κ.re ∧ T x = κ • x) → ∀ v ∈ Submodule.span ℂ s, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (T v))).re := by
  intro M H _ _ _ _ j V T c s hsym hs v hv
  classical
  have hle : Submodule.span ℂ s ≤
      ⨆ κ : {κ : ℂ // -c ≤ κ.re}, (V ⊓ Module.End.eigenspace T (κ : ℂ)) := by
    refine Submodule.span_le.2 fun x hx => ?_
    obtain ⟨hxV, κ, hκ, hT⟩ := hs x hx
    exact Submodule.mem_iSup_of_mem (⟨κ, hκ⟩ : {κ : ℂ // -c ≤ κ.re})
      ⟨hxV, Module.End.mem_eigenspace_iff.2 hT⟩
  obtain ⟨f, hf, hfv⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hle hv)
  have hV : ∀ κ, f κ ∈ V := fun κ => (hf κ).1
  have hT : ∀ κ, T (f κ) = (κ : ℂ) • f κ := fun κ => Module.End.mem_eigenspace_iff.1 (hf κ).2
  have hrel : ∀ a b : {κ : ℂ // -c ≤ κ.re}, (starRingEnd ℂ) (a : ℂ) * inner ℂ (j (f a)) (j (f b))
      = (b : ℂ) * inner ℂ (j (f a)) (j (f b)) := by
    intro a b
    have := hsym _ (hV a) _ (hV b)
    rwa [hT, hT, map_smul, map_smul, inner_smul_left, inner_smul_right] at this
  have horth : ∀ a b, a ≠ b → inner ℂ (j (f a)) (j (f b)) = 0 := by
    intro a b hab
    by_cases h0 : j (f a) = 0
    · rw [h0, inner_zero_left]
    · have h1 : (starRingEnd ℂ) (a : ℂ) = a :=
        mul_right_cancel₀ (fun h => h0 (inner_self_eq_zero.1 h)) (hrel a a)
      have h2 := hrel a b
      rw [h1] at h2
      by_contra h3
      exact hab (Subtype.ext (mul_right_cancel₀ h3 h2))
  have hv' : v = ∑ a ∈ f.support, f a := hfv.symm
  have e1 : inner ℂ (j v) (j v) = ∑ a ∈ f.support, inner ℂ (j (f a)) (j (f a)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv', map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha]
    intro b _ hb
    exact horth a b hb.symm
  have e2 : inner ℂ (j v) (j (T v))
      = ∑ a ∈ f.support, (a : ℂ) * inner ℂ (j (f a)) (j (f a)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv', map_sum T, map_sum, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha, hT, map_smul, inner_smul_right]
    intro b _ hb
    rw [hT, map_smul, inner_smul_right, horth a b hb.symm, mul_zero]
  have hn : ∀ x : H, inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have e3 : ‖j v‖ ^ 2 = ∑ a ∈ f.support, ‖j (f a)‖ ^ 2 := by
    simp only [hn] at e1
    exact_mod_cast e1
  rw [e2, e3, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [hn, Complex.re_mul_ofReal]
  exact mul_le_mul_of_nonneg_right a.2 (sq_nonneg _)
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TrOnSubSumEqTraceCompCompression
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

private lemma prj_idem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : prj V ∘L prj V = prj V := by
  ext v
  have h : prj V v ∈ V.topologicalClosure := by
    simp [prj]
  simpa [prj] using Submodule.starProjection_eq_self_iff.2 h

private lemma prj_comp_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {V W : Submodule ℂ H} (h : V ≤ W) : prj W ∘L prj V = prj V := by
  ext v
  have h1 : prj V v ∈ V.topologicalClosure := by
    simp [prj]
  have h2 : prj V v ∈ W.topologicalClosure := Submodule.topologicalClosure_mono h h1
  simpa [prj] using Submodule.starProjection_eq_self_iff.2 h2

private lemma prj_adj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : ContinuousLinearMap.adjoint (prj V) = prj V := by
  have : IsSelfAdjoint (prj V) := by
    simpa [prj] using isSelfAdjoint_starProjection V.topologicalClosure
  exact this

private lemma prj_comp_le' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {V W : Submodule ℂ H} (h : V ≤ W) : prj V ∘L prj W = prj V := by
  have := congrArg ContinuousLinearMap.adjoint (prj_comp_le h)
  simpa [ContinuousLinearMap.adjoint_comp, prj_adj] using this

theorem UpperTheory.trOn_sub_sum_eq_trace_comp_compression :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (E : ℝ → Submodule ℂ H) (S : Finset ℝ) (a : ℝ → ℂ) (F T : H →L[ℂ] H), (∀ x, E x ≤ W) → IsTraceClass (prj W ∘L T ∘L prj W) → trOn W (F ∘L prj W ∘L T) - ∑ x ∈ S, a x * trOn (E x) T = trace ((prj W ∘L F ∘L prj W - ∑ x ∈ S, a x • prj (E x)) ∘L (prj W ∘L T ∘L prj W)) := by
  intro H _ _ _ W E S a F T hE hT
  set P := prj W with hPdef
  set T0 := P ∘L T ∘L P with hT0
  have hPP : P ∘L P = P := prj_idem W
  let L : (H →L[ℂ] H) →ₗ[ℂ] ℂ :=
    { toFun := fun C => trace (C ∘L T0)
      map_add' := fun C D => by
        rw [ContinuousLinearMap.add_comp]
        exact trace_add (hT.comp_left C) (hT.comp_left D)
      map_smul' := fun c C => by
        rw [ContinuousLinearMap.smul_comp]
        exact trace_smul c (hT.comp_left C) }
  have hL : ∀ C, L C = trace (C ∘L T0) := fun _ => rfl
  have h1 : trOn W (F ∘L P ∘L T) = L (P ∘L F ∘L P) := by
    rw [hL, trOn]
    congr 1
    have : (P ∘L F ∘L P) ∘L T0 = P ∘L F ∘L (P ∘L P) ∘L T ∘L P := by
      simp only [hT0, ContinuousLinearMap.comp_assoc]
    rw [this, hPP]
    simp only [hPdef, ContinuousLinearMap.comp_assoc]
  have h2 : ∀ x, trOn (E x) T = L (prj (E x)) := by
    intro x
    set Q := prj (E x) with hQ
    have hQP : Q ∘L P = Q := prj_comp_le' (hE x)
    have hPQ : P ∘L Q = Q := prj_comp_le (hE x)
    have hQQ : Q ∘L Q = Q := prj_idem (E x)
    have hc := trace_comp_comm (hT.comp_left Q) Q
    have e1 : Q ∘L (Q ∘L T0) = Q ∘L T0 := by
      rw [← ContinuousLinearMap.comp_assoc, hQQ]
    have e2 : (Q ∘L T0) ∘L Q = Q ∘L T ∘L Q := by
      have : (Q ∘L T0) ∘L Q = (Q ∘L P) ∘L T ∘L (P ∘L Q) := by
        simp only [hT0, ContinuousLinearMap.comp_assoc]
      rw [this, hQP, hPQ]
    rw [e1, e2] at hc
    rw [hL, trOn, hc]
  rw [h1]
  simp only [h2]
  have h3 : L (P ∘L F ∘L P - ∑ x ∈ S, a x • prj (E x)) = trace ((P ∘L F ∘L P - ∑ x ∈ S, a x • prj (E x)) ∘L T0) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h3, map_sub, map_sum]
  simp only [map_smul, smul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TraceMixedSpaceEqMixedTraceLMul
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

private theorem algebra_trace_pi_eq_sum_trace {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
    [Module.Free R A] [Module.Finite R A] (x : ι → A) :
    Algebra.trace R (ι → A) x = ∑ i, Algebra.trace R A (x i) := by
  classical
  let b := Module.Free.chooseBasis R A
  rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]

theorem UpperTheory.trace_mixedSpace_eq_mixedTraceL_mul :
    ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.mixedEmbedding.mixedSpace K),
      Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) x =
        mixedTraceL (K := K) (x * ((fun _ => (1 : ℝ)), (fun _ => (2 : ℂ)))) := by
  classical
  intro K _ _ x
  rw [Algebra.trace_prod_apply, algebra_trace_pi_eq_sum_trace, algebra_trace_pi_eq_sum_trace]
  simp [mixedTraceL, Algebra.trace_complex_apply, mul_comm]
end

