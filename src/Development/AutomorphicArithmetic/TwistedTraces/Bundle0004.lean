module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsNhdsDisplacementLeHalfOfDerivOpBound
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ h.lieSubalgebra) (C : ℝ), ∃ N ∈ 𝓝 (1 : G), ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → (∀ i, ‖h.derivOp π (h.ofLie (b i)) v‖ ≤ C * ‖v‖) → ∀ a ∈ N, ‖π a v - v‖ ≤ 1 / 2 * ‖v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b C
  let T : 𝔤 →ₗ[ℝ] h.lieSubalgebra :=
    { toFun := h.toLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let S : h.lieSubalgebra →ₗ[ℝ] 𝔤 :=
    { toFun := h.ofLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hST : ∀ X : 𝔤, S (T X) = X := fun _ => rfl
  let f : 𝔤 → ℝ := fun X => (∑ i, |b.repr (h.toLie X) i|) * |C|
  have hf : Continuous f := by
    refine Continuous.mul (continuous_finsetSum _ fun i _ => ?_) continuous_const
    exact (LinearMap.continuous_of_finiteDimensional ((b.coord i) ∘ₗ T)).abs
  have hf0 : f 0 = 0 := by
    have : h.toLie 0 = 0 := rfl
    simp [f, this]
  have hO : {X : 𝔤 | f X < 1 / 2} ∈ 𝓝 (0 : 𝔤) :=
    (isOpen_lt hf continuous_const).mem_nhds (by simp [hf0])
  have h0 : (0 : 𝔤) ∈ (h.chart 1).symm.source := h.zero_mem_nhd
  have hexp0 : h.expG 0 = 1 := by
    apply Subtype.ext; apply Units.ext
    simp [IsExpLieAlgebra.coe_expG]
  refine ⟨h.expG '' {X : 𝔤 | f X < 1 / 2}, ?_, ?_⟩
  · have h1 := (h.chart 1).symm.image_mem_nhds h0 hO
    have e1 : (h.chart 1).symm 0 = 1 := by
      show 1 * h.expG 0 = 1
      rw [hexp0, one_mul]
    rw [e1] at h1
    refine Filter.mem_of_superset h1 ?_
    rintro _ ⟨X, hX, rfl⟩
    refine ⟨X, hX, ?_⟩
    show h.expG X = 1 * h.expG X
    rw [one_mul]
  · rintro E _ _ π v hπ hv hb _ ⟨X, hX, rfl⟩
    refine (UpperTheory.norm_exp_smul_sub_le_norm_derivOp 𝔸 G 𝔤 h E π v X hπ hv).trans ?_
    have hsum : X = ∑ i, b.repr (h.toLie X) i • h.ofLie (b i) := by
      conv_lhs => rw [← hST X]
      show S (h.toLie X) = _
      conv_lhs => rw [← b.sum_repr (h.toLie X)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul S _ _
    have hD : h.derivOp π X v =
        ∑ i, b.repr (h.toLie X) i • h.derivOp π (h.ofLie (b i)) v := by
      show fderiv ℝ (h.expOrbit π v) 0 X = ∑ i, b.repr (h.toLie X) i •
        fderiv ℝ (h.expOrbit π v) 0 (h.ofLie (b i))
      conv_lhs => rw [hsum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have hbound : ‖h.derivOp π X v‖ ≤ f X * ‖v‖ := by
      rw [hD]
      refine (norm_sum_le _ _).trans ?_
      simp only [f, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (hb i).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg v))
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_of_lt hX) (norm_nonneg v))
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.NormGeneratorLeOfPolynomialAnnihilated
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_generator_le_of_polynomial_annihilated :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (u : ℝ → Module.End ℂ E) (D : Module.End ℂ E) (p : ℝ → ℂ[X]) (M : ℝ), u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t x, ‖u t x‖ = ‖x‖) → (∀ x, HasDerivAt (fun t : ℝ => u t x) (D x) 0) → (∀ t, aeval (u t) (p t) = 0) → (∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M) → ∀ x, ‖D x‖ ≤ M * ‖x‖ := by
  intro E _ _ _ u D p M h0 hadd hiso hder hroot hM x
  have hshift : ∀ (t : ℝ) (w : E), HasDerivAt (fun s : ℝ => u s w) (u t (D w)) t := by
    intro t w
    let L : E →L[ℂ] E := LinearMap.toContinuousLinearMap (u t)
    let LR : E →L[ℝ] E := L.restrictScalars ℝ
    have h1 : HasDerivAt (fun s : ℝ => LR (u s w)) (LR (D w)) 0 :=
      LR.hasFDerivAt.comp_hasDerivAt 0 (hder w)
    have h2 : HasDerivAt (fun s : ℝ => LR (u (s - t) w)) (LR (D w)) t := by
      apply HasDerivAt.comp_sub_const t t (f := fun s : ℝ => LR (u s w))
      simpa using h1
    have h3 : (fun s : ℝ => LR (u (s - t) w)) = fun s => u s w := by
      funext s
      show u t (u (s - t) w) = u s w
      rw [← Module.End.mul_apply, ← hadd]
      congr 2
      ring
    rw [h3] at h2
    exact h2
  have hinner : ∀ (t : ℝ) (a b : E), inner ℂ (u t a) (u t b) = inner ℂ a b := by
    intro t a b
    exact LinearIsometry.inner_map_map (⟨u t, hiso t⟩ : E →ₗᵢ[ℂ] E) a b
  have h0' : ∀ a : E, u 0 a = a := by
    intro a
    rw [h0]
    rfl
  have hskew : ∀ a b : E, inner ℂ (D a) b + inner ℂ a (D b) = 0 := by
    intro a b
    have h1 := (hder a).inner ℂ (hder b)
    have h2 : (fun t : ℝ => inner ℂ (u t a) (u t b)) = fun _ => inner ℂ a b := by
      funext t
      exact hinner t a b
    rw [h2] at h1
    have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ a b))
    rw [h0', h0'] at h3
    rw [add_comm]
    exact h3
  have hev : ∀ z : ℂ, D.HasEigenvalue z → ‖z‖ ≤ M := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_hasEigenvector
    have hDw : D w = z • w := hw.apply_eq_smul
    have hw0 : w ≠ 0 := hw.2
    have hconst : ∀ t : ℝ, Complex.exp (-(z * t)) • u t w = w := by
      have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(z * s)) • u s w) 0 t := by
        intro t
        have he : HasDerivAt (fun s : ℝ => Complex.exp (-(z * s)))
            (Complex.exp (-(z * t)) * (-z)) t := by
          have hl : HasDerivAt (fun s : ℝ => -(z * (s : ℂ))) (-z) t := by
            have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
              simpa using (hasDerivAt_id t).ofReal_comp
            have h2 := h.const_mul (-z)
            simpa [neg_mul] using h2
          exact hl.cexp
        have h1 := he.smul (hshift t w)
        have h2 : Complex.exp (-(z * t)) • u t (D w) + (Complex.exp (-(z * t)) * (-z)) • u t w = 0 := by
          rw [hDw, map_smul, smul_smul, ← add_smul]
          have : Complex.exp (-(z * t)) * z + Complex.exp (-(z * t)) * (-z) = 0 := by ring
          rw [this, zero_smul]
        rw [h2] at h1
        exact h1
      intro t
      have hc := is_const_of_deriv_eq_zero (f := fun s : ℝ => Complex.exp (-(z * s)) • u s w)
        (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
      simpa [h0'] using hc
    have hut : ∀ t : ℝ, u t w = Complex.exp (z * t) • w := by
      intro t
      have h1 := congrArg (fun v => Complex.exp (z * t) • v) (hconst t)
      simp only [smul_smul] at h1
      rw [← Complex.exp_add] at h1
      simpa using h1
    apply hM
    intro t
    have hvec : (u t).HasEigenvector (Complex.exp (z * t)) w :=
      ⟨Module.End.mem_eigenspace_iff.2 (hut t), hw0⟩
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p t) hvec
    rw [hroot t] at h1
    have h2 : (p t).eval (Complex.exp (z * t)) • w = 0 := by
      rw [← h1]
      rfl
    exact (smul_eq_zero.1 h2).resolve_right hw0
  exact UpperTheory.norm_skewAdjoint_le_of_eigenvalue_bound E D M hskew hev x
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TrFormDefiniteOnArchSkewArchHerm
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

open scoped Classical in
private theorem trace_mixedSpace_eq {K : Type} [Field K] [NumberField K]
    (x : NumberField.mixedEmbedding.mixedSpace K) :
    Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) x =
      mixedTraceL K x + ∑ v, (x.2 v).re := by
  rw [UpperTheory.trace_mixedSpace_eq_mixedTraceL_mul, mixedTraceL_apply, mixedTraceL_apply]
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, mul_zero, sub_zero, ← Finset.sum_mul]
  ring

open scoped Classical in
private theorem trace_eq_zero_of_star_neg {K : Type} [Field K] [NumberField K]
    (z : NumberField.mixedEmbedding.mixedSpace K) (hz : star z = -z) :
    Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) z = 0 := by
  have h1 : mixedTraceL K (star z) = mixedTraceL K z := mixedTraceL_star z
  rw [hz, map_neg] at h1
  have h2 : ∑ v, (z.2 v).re = 0 := by
    have h3 : ∀ v, (z.2 v).re = 0 := fun v => by
      have h4 : star (z.2 v) = -(z.2 v) := congrFun (congrArg Prod.snd hz) v
      have h5 := congrArg Complex.re h4
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h5
      linarith
    simp [h3]
  rw [trace_mixedSpace_eq, h2]
  linarith

open scoped Classical in
private theorem trace_conjTranspose_mul_pos {K : Type} [Field K] [NumberField K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (NumberField.mixedEmbedding.mixedSpace K)} (hA : A ≠ 0) :
    0 < Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
      (Matrix.trace (A.conjTranspose * A)) := by
  rw [trace_mixedSpace_eq]
  have h1 := mixedTraceL_trace_conjTranspose_mul_self_pos hA
  have h2 : 0 ≤ ∑ v, ((Matrix.trace (A.conjTranspose * A)).2 v).re := by
    refine Finset.sum_nonneg fun v _ => ?_
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Prod.snd_sum, Finset.sum_apply, Complex.re_sum, Prod.snd_mul, Pi.mul_apply, Prod.snd_star,
      Pi.star_apply]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  linarith

theorem UpperTheory.trForm_definite_on_archSkew_archHerm :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), (∀ X ∈ archSkew K n, X ≠ 0 → trForm K n X X < 0) ∧ (∀ X ∈ archHerm K n, X ≠ 0 → 0 < trForm K n X X) ∧ (∀ X ∈ archSkew K n, ∀ Y ∈ archHerm K n, trForm K n X Y = 0) := by
  intro K _ _ n
  refine ⟨fun X hX h0 => ?_, fun X hX h0 => ?_, fun X hX Y hY => ?_⟩
  · rw [mem_archSkew] at hX
    have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
    have e : mat (X : ArchMatrix K n) * mat (X : ArchMatrix K n) =
        -((mat (X : ArchMatrix K n)).conjTranspose * mat (X : ArchMatrix K n)) := by
      rw [hX, Matrix.neg_mul, neg_neg]
    have h := trace_conjTranspose_mul_pos hX0
    have h2 : trForm K n X X = Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (X : ArchMatrix K n))) := rfl
    rw [h2, e, Matrix.trace_neg, map_neg]
    linarith
  · rw [mem_archHerm] at hX
    have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
    have h := trace_conjTranspose_mul_pos hX0
    rw [hX] at h
    exact h
  · rw [mem_archSkew] at hX
    rw [mem_archHerm] at hY
    have h2 : trForm K n X Y = Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))) := rfl
    rw [h2]
    refine trace_eq_zero_of_star_neg _ ?_
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX, hY, Matrix.mul_neg,
      Matrix.trace_neg, Matrix.trace_mul_comm]
end

