module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HasDerivAtDetOneAdd
section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.Rg.Sw.HSt

theorem hasDerivAt_det_one_add {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • M).det) M.trace 0 := by
  set p : ℂ[X] := (1 + (X : ℂ[X]) • M.map C).det with hp
  have e : (fun s : ℂ => (1 + s • M).det) = fun s => p.eval s := by
    funext s
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp [mul_comm]
  rw [e]
  have h := p.hasDerivAt 0
  rwa [hp, Matrix.derivative_det_one_add_X_smul] at h

theorem hasDerivAt_det_add {ι : Type} [Fintype ι] [DecidableEq ι] (A X : Matrix ι ι ℂ) (hA : IsUnit A.det) :
    HasDerivAt (fun s : ℂ => (A + s • X).det) (A.det * (A⁻¹ * X).trace) 0 := by
  have e : (fun s : ℂ => (A + s • X).det) = fun s => A.det * (1 + s • (A⁻¹ * X)).det := by
    funext s
    rw [← det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
  rw [e]
  exact (hasDerivAt_det_one_add (A⁻¹ * X)).const_mul _

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IteratedDerivEqOfEventuallyEq
section
noncomputable section

open Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

theorem iteratedDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) (k : ℕ) :
    iteratedDeriv k f s = iteratedDeriv k g s := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedDerivWithin_eq (by simpa using h) h.eq_of_nhds

theorem leib {U : Set ℂ} (hU : IsOpen U) : ∀ (j : ℕ) (h₁ h₂ : ℂ → ℂ), DifferentiableOn ℂ h₁ U → DifferentiableOn ℂ h₂ U →
    ∀ s ∈ U, iteratedDeriv j (fun z => h₁ z * h₂ z) s =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i h₁ s * iteratedDeriv (j - i) h₂ s := by
  intro j
  induction j with
  | zero => intro h₁ h₂ _ _ s _; simp
  | succ j ih =>
    intro h₁ h₂ hd₁ hd₂ s hs
    have hd₁' : DifferentiableOn ℂ (deriv h₁) U := hd₁.deriv hU
    have hd₂' : DifferentiableOn ℂ (deriv h₂) U := hd₂.deriv hU
    have hev : deriv (fun z => h₁ z * h₂ z) =ᶠ[𝓝 s] fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact deriv_mul ((hd₁.differentiableAt (hU.mem_nhds hz))) ((hd₂.differentiableAt (hU.mem_nhds hz)))
    rw [iteratedDeriv_succ', iteratedDeriv_eq_of_eventuallyEq hev]
    have hc₁ : ContDiffAt ℂ j (fun z => deriv h₁ z * h₂ z) s :=
      ((hd₁'.mul hd₂).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hc₂ : ContDiffAt ℂ j (fun z => h₁ z * deriv h₂ z) s :=
      ((hd₁.mul hd₂').contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hsplit : (fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z) =
        (fun z => deriv h₁ z * h₂ z) + (fun z => h₁ z * deriv h₂ z) := rfl
    rw [hsplit, iteratedDeriv_add hc₁ hc₂, ih _ _ hd₁' hd₂ s hs, ih _ _ hd₁ hd₂' s hs]
    have key := Finset.sum_choose_succ_mul (R := ℂ) (fun a b => iteratedDeriv a h₁ s * iteratedDeriv b h₂ s) j
    simp only [mul_assoc] at key ⊢
    rw [key, add_comm]
    congr 1
    all_goals
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      (try rw [← iteratedDeriv_succ']); (try rw [show j + 1 - i = j - i + 1 by omega])

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ParamCD
section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.PCD

variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]

structure Good {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : Set F) (K : F → X → E) : Prop where
  smooth : ∀ u, ContDiffOn ℝ ∞ (K · u) Ω
  cont : ∀ N : ℕ, ContinuousOn (fun p : F × X => iteratedFDeriv ℝ N (K · p.2) p.1) (Ω ×ˢ univ)
  supp : ∀ x ∈ Ω, ∃ V : Set F, IsOpen V ∧ x ∈ V ∧ ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ V, ∀ u ∉ C, K x' u = 0

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}

theorem Good.continuousOn (hK : Good Ω K) : ContinuousOn (fun p : F × X => K p.1 p.2) (Ω ×ˢ univ) := by
  have h := (continuousMultilinearCurryFin0 ℝ F E).continuous.comp_continuousOn (hK.cont 0)
  refine h.congr fun p _ => ?_
  simp

theorem Good.dK (hΩ : IsOpen Ω) (hK : Good Ω K) : Good Ω (fun x u => fderiv ℝ (K · u) x) := by
  refine ⟨fun u => ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 (hK.smooth u)).2, fun N => ?_, fun x hx => ?_⟩
  · have h : ContinuousOn (fun p : F × X => (continuousMultilinearCurryRightEquiv' ℝ N F E)
        (iteratedFDeriv ℝ (N + 1) (K · p.2) p.1)) (Ω ×ˢ univ) :=
      (LinearIsometryEquiv.continuous _).comp_continuousOn (hK.cont (N + 1))
    refine h.congr fun p _ => ?_
    simp only [Function.comp_apply]
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
  · obtain ⟨V, hV, hxV, C, hC, hKV⟩ := hK.supp x hx
    refine ⟨V, hV, hxV, C, hC, fun x' hx' u hu => ?_⟩
    have : (K · u) =ᶠ[𝓝 x'] fun _ => 0 := by
      filter_upwards [hV.mem_nhds hx'] with y hy using hKV y hy u hu
    rw [this.fderiv_eq]
    simp

theorem Good.integrable (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] {x : F} (hx : x ∈ Ω) :
    Integrable (K x) ν := by
  obtain ⟨V, -, hxV, C, hC, hKV⟩ := hK.supp x hx
  have hc : Continuous (K x) := by
    have := hK.continuousOn
    exact this.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hC fun u hu => hKV x hxV u hu)

theorem Good.hasFDerivAt [CompleteSpace E] (hΩ : IsOpen Ω) (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    {x₀ : F} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ u, K x u ∂ν) (∫ u, fderiv ℝ (K · u) x₀ ∂ν) x₀ := by
  obtain ⟨V, hV, hxV, C, hC, hKV⟩ := hK.supp x₀ hx₀
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 (hΩ.inter hV) x₀ ⟨hx₀, hxV⟩
  have hK' := hK.dK hΩ
  have hc' := hK'.continuousOn
  have hcb : IsCompact (Metric.closedBall x₀ (ε / 2) ×ˢ C) := (isCompact_closedBall _ _).prod hC
  have hsub : Metric.closedBall x₀ (ε / 2) ×ˢ C ⊆ Ω ×ˢ univ := by
    intro p hp
    exact ⟨(hεs (Metric.closedBall_subset_ball (by linarith) hp.1)).1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hcb.exists_bound_of_continuousOn (hc'.mono hsub)
  have hcont_u : ∀ x ∈ Ω, Continuous (K x) := fun x hx =>
    hK.continuousOn.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  have hcont'_u : ∀ x ∈ Ω, Continuous (fun u => fderiv ℝ (K · u) x) := fun x hx =>
    hc'.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  have hball : Metric.ball x₀ (ε / 2) ⊆ Ω ∩ V := fun y hy => hεs (Metric.ball_subset_ball (by linarith) hy)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := K) (F' := fun x u => fderiv ℝ (K · u) x)
    (s := Metric.ball x₀ (ε / 2))
    (bound := C.indicator fun _ => M) (Metric.ball_mem_nhds _ (by linarith)) ?_ (hK.integrable ν hx₀)
    (hcont'_u x₀ hx₀).aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [hΩ.mem_nhds hx₀] with x hx using (hcont_u x hx).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u x hx => ?_
    by_cases hu : u ∈ C
    · rw [indicator_of_mem hu]
      exact hM (x, u) ⟨Metric.ball_subset_closedBall hx, hu⟩
    · rw [indicator_of_notMem hu]
      have : (K · u) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hV.mem_nhds (hball hx).2] with y hy using hKV y hy u hu
      rw [this.fderiv_eq]
      simp
  · exact (integrableOn_const (C := M) hC.measure_lt_top.ne).integrable_indicator hC.isClosed.measurableSet
  · refine Filter.Eventually.of_forall fun u x hx => ?_
    have hxΩ := (hball hx).1
    exact ((hK.smooth u).differentiableOn (by simp) x hxΩ).differentiableAt (hΩ.mem_nhds hxΩ) |>.hasFDerivAt

omit [NormedSpace ℝ E] in
theorem contDiffOn_nat (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (N : ℕ) :
    ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (K : F → X → E'), Good Ω K →
      ContDiffOn ℝ N (fun x => ∫ u, K x u ∂ν) Ω := by
  induction N with
  | zero =>
    intro E' _ _ _ K hK
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hK.hasFDerivAt hΩ ν hx).continuousAt.continuousWithinAt
  | succ N ih =>
    intro E' _ _ _ K hK
    rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx => (hK.hasFDerivAt hΩ ν hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine (ih (F →L[ℝ] E') _ (hK.dK hΩ)).congr fun x hx => ?_
    exact (hK.hasFDerivAt hΩ ν hx).fderiv

theorem contDiffOn_integral [CompleteSpace E] (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hK : Good Ω K) : ContDiffOn ℝ ∞ (fun x => ∫ u, K x u ∂ν) Ω :=
  contDiffOn_infty.2 fun N => contDiffOn_nat hΩ ν N E K hK

section Kernel

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set F}

omit [FiniteDimensional ℝ F] in
theorem slice (hΩ : IsOpen Ω) {k : F × V → E} (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (N : ℕ) {x : F} (hx : x ∈ Ω) (w : V) :
    iteratedFDeriv ℝ N (fun x => k (x, w)) x =
      (iteratedFDeriv ℝ N k (x, w)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ F V) := by
  set f' : F × V → E := fun p => k (p + (0, w))
  have hS : IsOpen (Ω ×ˢ (univ : Set V)) := hΩ.prod isOpen_univ
  have hf' : ContDiffOn ℝ ∞ f' (Ω ×ˢ univ) := by
    refine hk.comp (contDiffOn_id.add contDiffOn_const) fun p hp => ?_
    exact ⟨by simpa using hp.1, mem_univ _⟩
  have hpre : (ContinuousLinearMap.inl ℝ F V) ⁻¹' (Ω ×ˢ univ) = Ω := by ext y; simp
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right (ContinuousLinearMap.inl ℝ F V) hf'
    hS.uniqueDiffOn (by rw [hpre]; exact hΩ.uniqueDiffOn) (x := x) (by simpa using hx) (i := N) (by exact_mod_cast le_top)
  rw [hpre, iteratedFDerivWithin_of_isOpen N hΩ hx, iteratedFDerivWithin_of_isOpen N hS (by simpa using hx)] at h1
  have h2 : (f' ∘ ContinuousLinearMap.inl ℝ F V) = fun x => k (x, w) := by
    funext y; simp [f']
  rw [h2] at h1
  rw [h1]
  congr 1
  have h3 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := k) N ((0 : F), w) (ContinuousLinearMap.inl ℝ F V x)
  simpa using h3

theorem good_of_joint (hΩ : IsOpen Ω) (k : F × V → E) (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V)
    (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) :
    Good Ω (fun x u => h u • k (x, v u)) := by
  have hsl : ∀ u, ContDiffOn ℝ ∞ (fun x => k (x, v u)) Ω := fun u =>
    hk.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  refine ⟨fun u => (hsl u).const_smul (h u), fun N => ?_, fun x hx => ?_⟩
  · have hS : IsOpen (Ω ×ˢ (univ : Set V)) := hΩ.prod isOpen_univ
    have hcont : ContinuousOn (fun q : F × V => iteratedFDeriv ℝ N k q) (Ω ×ˢ univ) := by
      have := hk.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hS.uniqueDiffOn
      exact this.congr fun q hq => (iteratedFDerivWithin_of_isOpen N hS hq).symm
    let hL := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := E)
      (fun _ : Fin N => ContinuousLinearMap.inl ℝ F V)
    have hc2 : ContinuousOn (fun p : F × X => h p.2 • (hL (iteratedFDeriv ℝ N k (p.1, v p.2)))) (Ω ×ˢ univ) := by
      refine (hh.comp continuous_snd).continuousOn.smul (hL.continuous.comp_continuousOn ?_)
      exact hcont.comp (continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn fun p hp => ⟨hp.1, mem_univ _⟩
    refine hc2.congr fun p hp => ?_
    have hx : p.1 ∈ Ω := hp.1
    simp only
    rw [iteratedFDeriv_const_smul_apply' ((hsl p.2).contDiffAt (hΩ.mem_nhds hx) |>.of_le (by exact_mod_cast le_top)),
      slice hΩ hk N hx (v p.2)]
    rfl
  · obtain ⟨W, hW, C, hC, hKW⟩ := hsupp x hx
    obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.1 hW
    exact ⟨W', hW'o, hxW', C, hC, fun x' hx' u hu => by simp [hKW x' (hW'W hx') u hu]⟩

theorem contDiffOn_integral' (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (k : F × V → E)
    (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V) (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ u, h u • k (x, v u) ∂ν) Ω :=
  contDiffOn_integral hΩ ν (good_of_joint hΩ k hk v hv h hh hsupp)

end Kernel

end PositivityTheory.Rg.Sw.HSt.PCD
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SpanUnitaryMatrix
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

variable {n : ℕ}

theorem span_unitary_matrix :
    Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) = ⊤ := by
  open scoped Matrix.Norms.L2Operator in exact CStarAlgebra.span_unitary (A := Matrix (Fin n) (Fin n) ℂ)

def pm (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if σ i = j then 1 else 0

theorem pm_conj (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    pm σ * X * (pm σ)ᴴ = X.submatrix σ σ := by
  ext i j
  simp [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, eq_comm]

theorem pm_unit (σ : Equiv.Perm (Fin n)) : (pm σ)ᴴ * pm σ = 1 := by
  ext i j
  simp only [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases h : i = j <;> simp [h, eq_comm, Equiv.apply_eq_iff_eq_symm_apply]
  · intro k _ hk
    have : σ k ≠ i := fun e => hk (by rw [← e]; simp)
    simp [this]
  · simp

def dph (a : Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if i = a then Complex.I else 1

theorem dph_unit (a : Fin n) : (dph a)ᴴ * dph a = 1 := by
  rw [dph, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i
  by_cases hi : i = a <;> simp [hi]

theorem dph_conj {a b : Fin n} (hab : a ≠ b) :
    dph a * Matrix.single a b (1 : ℂ) * (dph a)ᴴ = Complex.I • Matrix.single a b (1 : ℂ) := by
  ext i j
  rw [dph, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  by_cases hi : a = i <;> by_cases hj : b = j
  · subst hi hj; simp [hab.symm]
  · simp [hj]
  · simp [hi]
  · simp [hi, hj]

theorem inv_trace (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → Xᴴ * X = 1 → L (U * X * Uᴴ) = L X) :
    ∀ X, L X = L 1 / n * X.trace := by

  have h' : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → L (U * X * Uᴴ) = L X := by
    intro U X hU
    let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      L.comp ((LinearMap.mulLeft ℂ U).comp (LinearMap.mulRight ℂ Uᴴ)) - L
    have hC : Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set _) ≤ LinearMap.ker C := by
      rw [Submodule.span_le]
      intro Y hY
      have hY' : Yᴴ * Y = 1 := hY.1
      simp only [SetLike.mem_coe, LinearMap.mem_ker, C, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← Matrix.mul_assoc]
      rw [h U Y hU hY', sub_self]
    have hX : X ∈ LinearMap.ker C := hC (by rw [span_unitary_matrix]; trivial)
    simpa [C, sub_eq_zero, ← Matrix.mul_assoc] using hX

  have hoff : ∀ a b : Fin n, a ≠ b → L (Matrix.single a b 1) = 0 := by
    intro a b hab
    have e := h' (dph a) (Matrix.single a b 1) (dph_unit a)
    rw [dph_conj hab, L.map_smul, smul_eq_mul] at e
    have : (Complex.I - 1) * L (Matrix.single a b 1) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (by simp [sub_eq_zero, Complex.ext_iff])
    · exact h0

  have hdiag : ∀ a b : Fin n, L (Matrix.single a a 1) = L (Matrix.single b b 1) := by
    intro a b
    have e := h' (pm (Equiv.swap a b)) (Matrix.single a a 1) (pm_unit _)
    rw [pm_conj] at e
    have : (Matrix.single a a (1 : ℂ)).submatrix (Equiv.swap a b) (Equiv.swap a b) = Matrix.single b b 1 := by
      have key : ∀ x, a = (Equiv.swap a b) x ↔ b = x := by
        intro x; rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, eq_comm]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.single_apply, key]
    rw [this] at e
    exact e.symm
  intro X
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : X = 0 := Subsingleton.elim _ _
    simp [this]
  set κ := L (Matrix.single (⟨0, hn⟩ : Fin n) ⟨0, hn⟩ 1)
  have hsum : ∀ Y : Matrix (Fin n) (Fin n) ℂ, L Y = κ * Y.trace := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    rw [Matrix.trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [show Matrix.single a a (Y a a) = Y a a • Matrix.single a a (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, smul_eq_mul, hdiag a ⟨0, hn⟩, Matrix.diag_apply]; ring
    · intro b _ hb
      rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, hoff a b (Ne.symm hb), smul_zero]
    · simp
  have h1 : L 1 = κ * n := by rw [hsum, trace_one, Fintype.card_fin]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hsum X, h1]; field_simp

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

