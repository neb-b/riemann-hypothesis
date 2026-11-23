module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzClosureStableLinearFormFourier
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem topologicalClosure_stable_of_continuousLinearMap {M : Type} [TopologicalSpace M] [AddCommGroup M]
    [Module ℂ M] [ContinuousSMul ℂ M] [ContinuousAdd M] (W : Submodule ℂ M) (T : M →L[ℂ] M)
    (hT : ∀ f ∈ W, T f ∈ W) : ∀ f ∈ W.topologicalClosure, T f ∈ W.topologicalClosure := by
  intro f hf
  have h1 : Submodule.map (T : M →ₗ[ℂ] M) W ≤ W := by
    rintro _ ⟨g, hg, rfl⟩
    exact hT g hg
  have h2 := Submodule.topologicalClosure_map T W
  exact Submodule.topologicalClosure_mono h1 (h2 ⟨f, hf, rfl⟩)

theorem schwartz_closure_stable_linearForm_fourier :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  intro E _ _ _ _ _ W hmul hF
  constructor
  · intro ℓ f f₁ hf hf₁
    have hg : Function.HasTemperateGrowth (fun x : E => ((ℓ x : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.comp ℓ).hasTemperateGrowth
    set T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ x : ℝ) : ℂ)) with hTdef
    have hTapp : ∀ g : SchwartzMap E ℂ, ∀ x, T g x = (ℓ x : ℂ) * g x := by
      intro g x
      rw [hTdef, SchwartzMap.smulLeftCLM_apply hg]
      rfl
    have hTW : ∀ g ∈ W, T g ∈ W := fun g hg' => hmul ℓ g (T g) hg' (hTapp g)
    have hf₁T : f₁ = T f := by
      ext x
      rw [hf₁ x, hTapp f x]
    rw [hf₁T]
    exact topologicalClosure_stable_of_continuousLinearMap W T hTW f hf
  · intro f hf
    have hTW : ∀ g ∈ W, SchwartzMap.fourierTransformCLM ℂ g ∈ W := by
      intro g hg
      rw [SchwartzMap.fourierTransformCLM_apply]
      exact hF g hg
    have := topologicalClosure_stable_of_continuousLinearMap W (SchwartzMap.fourierTransformCLM ℂ) hTW f hf
    rwa [SchwartzMap.fourierTransformCLM_apply] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
section
open Filter Topology

namespace GlobalTheory

theorem norm_fderiv_le_of_small_of_lipschitz {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : V → E} (hg : Differentiable ℝ g) {C δ t : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t)
    (hL : ∀ a b, ‖fderiv ℝ g a - fderiv ℝ g b‖ ≤ C * ‖a - b‖) (hδ : ∀ w, ‖g w‖ ≤ δ) (v : V) :
    ‖fderiv ℝ g v‖ ≤ 2 * δ / t + C * t := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  have key : ∀ h : V, ‖h‖ = t → ‖fderiv ℝ g v h‖ ≤ 2 * δ + C * t * t := by
    intro h hh
    have hψd : ∀ x, DifferentiableAt ℝ (fun y => g y - fderiv ℝ g v y) x :=
      fun x => (hg x).sub (fderiv ℝ g v).differentiableAt
    have hψf : ∀ x, fderiv ℝ (fun y => g y - fderiv ℝ g v y) x = fderiv ℝ g x - fderiv ℝ g v := by
      intro x
      exact ((hg x).hasFDerivAt.sub (fderiv ℝ g v).hasFDerivAt).fderiv
    have hb : ∀ x ∈ Metric.closedBall v t,
        ‖fderiv ℝ (fun y => g y - fderiv ℝ g v y) x‖ ≤ C * t := by
      intro x hx
      rw [hψf]
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      exact (hL x v).trans (mul_le_mul_of_nonneg_left hx hC)
    have hvh : v + h ∈ Metric.closedBall v t := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hh]
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hψd x) hb
      (convex_closedBall v t) (Metric.mem_closedBall_self ht.le) hvh
    rw [add_sub_cancel_left, hh, map_add (f := _)] at hmv
    have e1 : g (v + h) - (fderiv ℝ g v v + fderiv ℝ g v h) - (g v - fderiv ℝ g v v) =
        (g (v + h) - g v) - fderiv ℝ g v h := by abel
    rw [e1] at hmv
    have e2 : fderiv ℝ g v h = (g (v + h) - g v) - ((g (v + h) - g v) - fderiv ℝ g v h) := by abel
    rw [e2]
    calc _ ≤ ‖g (v + h) - g v‖ + ‖(g (v + h) - g v) - fderiv ℝ g v h‖ := norm_sub_le _ _
      _ ≤ (δ + δ) + C * t * t :=
          add_le_add ((norm_sub_le _ _).trans (add_le_add (hδ _) (hδ _))) hmv
      _ = 2 * δ + C * t * t := by ring
  have hnn : 0 ≤ 2 * δ / t + C * t := add_nonneg (div_nonneg (by linarith) ht.le) (mul_nonneg hC ht.le)
  refine ContinuousLinearMap.opNorm_le_bound _ hnn (fun u => ?_)
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hs : 0 ≤ t / ‖u‖ := div_nonneg ht.le hu'.le
  have hk := key ((t / ‖u‖) • u) (by rw [norm_smul, Real.norm_of_nonneg hs, div_mul_cancel₀ t hu'.ne'])
  rw [ContinuousLinearMap.map_smul, norm_smul, Real.norm_of_nonneg hs] at hk
  have h3 : ‖fderiv ℝ g v u‖ * t ≤ (2 * δ + C * t * t) * ‖u‖ := by
    have e : ‖fderiv ℝ g v u‖ * t = (t / ‖u‖ * ‖fderiv ℝ g v u‖) * ‖u‖ := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hk hu'.le
  have e3 : (2 * δ / t + C * t) * ‖u‖ = (2 * δ + C * t * t) * ‖u‖ / t := by
    field_simp
  rw [e3, le_div_iff₀ ht]
  exact h3

theorem norm_iteratedFDeriv_sub_le_of_bound {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : V → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) {C : ℝ}
    (hC : ∀ v, ‖iteratedFDeriv ℝ (n + 1) f v‖ ≤ C) (a b : V) :
    ‖iteratedFDeriv ℝ n f a - iteratedFDeriv ℝ n f b‖ ≤ C * ‖a - b‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ n f) (fun x _ => hd x)
    (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hC x) convex_univ (Set.mem_univ b)
    (Set.mem_univ a)

theorem eventually_forall_norm_le_of_lipschitz_of_decay {X V E : Type*} {l : Filter X}
    [NormedAddCommGroup V] [ProperSpace V] [NormedAddCommGroup E] {h : X → V → E}
    (hp : ∀ v, Tendsto (fun x => h x v) l (𝓝 0)) {C D : ℝ} (hC : 0 ≤ C)
    (hL : ∀ᶠ x in l, ∀ a b, ‖h x a - h x b‖ ≤ C * ‖a - b‖)
    (hD : ∀ᶠ x in l, ∀ v, ‖v‖ * ‖h x v‖ ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∀ v, ‖h x v‖ ≤ ε := by
  have hR1 : (1 : ℝ) ≤ max 1 (D / ε) := le_max_left _ _
  have hDR : D ≤ ε * max 1 (D / ε) := by
    calc D = ε * (D / ε) := by field_simp
      _ ≤ ε * max 1 (D / ε) := mul_le_mul_of_nonneg_left (le_max_right _ _) hε.le
  have hη : 0 < ε / (2 * (C + 1)) := div_pos hε (by linarith)
  have hCη : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) two_pos]
    nlinarith
  obtain ⟨S, -, hSfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : V) (max 1 (D / ε))) hη
  have hS : ∀ᶠ x in l, ∀ s ∈ S, ‖h x s‖ < ε / 2 := by
    rw [hSfin.eventually_all]
    intro s _
    have hs := hp s
    rw [tendsto_zero_iff_norm_tendsto_zero] at hs
    exact hs.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hS, hL, hD] with x hxS hxL hxD v
  by_cases hv : ‖v‖ ≤ max 1 (D / ε)
  · have hvb : v ∈ Metric.closedBall (0 : V) (max 1 (D / ε)) := by rwa [mem_closedBall_zero_iff]
    obtain ⟨s, hs, hvs⟩ := Set.mem_iUnion₂.1 (hcover hvb)
    rw [Metric.mem_ball, dist_eq_norm] at hvs
    have e : h x v = h x s + (h x v - h x s) := by abel
    calc ‖h x v‖ = ‖h x s + (h x v - h x s)‖ := by rw [← e]
      _ ≤ ‖h x s‖ + ‖h x v - h x s‖ := norm_add_le _ _
      _ ≤ ε / 2 + C * (ε / (2 * (C + 1))) :=
          add_le_add (hxS s hs).le ((hxL v s).trans (mul_le_mul_of_nonneg_left hvs.le hC))
      _ ≤ ε := by linarith
  · replace hv := not_le.1 hv
    have hvpos : 0 < ‖v‖ := lt_of_lt_of_le one_pos (hR1.trans hv.le)
    have hmul : ‖v‖ * ‖h x v‖ ≤ ‖v‖ * ε := by
      calc ‖v‖ * ‖h x v‖ ≤ D := hxD v
        _ ≤ ε * max 1 (D / ε) := hDR
        _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_left hv.le hε.le
        _ = ‖v‖ * ε := mul_comm _ _
    exact le_of_mul_le_mul_left hmul hvpos

theorem eventually_forall_norm_iteratedFDeriv_le {X V : Type*} {l : Filter X}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {h : X → SchwartzMap V ℂ}
    (hp : ∀ v, Tendsto (fun x => h x v) l (𝓝 0))
    (hb : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (h x) v‖ ≤ C)
    (n : ℕ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ v, ‖iteratedFDeriv ℝ n (h x) v‖ ≤ ε := by
  induction n with
  | zero =>
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ := hb 0 1
    obtain ⟨D, -, hDb⟩ := hb 1 0
    refine eventually_forall_norm_le_of_lipschitz_of_decay
      (h := fun x v => iteratedFDeriv ℝ 0 (h x) v) (C := C) (D := D) (fun v => ?_) hC0 ?_ ?_ hε
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_iteratedFDeriv_zero]
      exact tendsto_zero_iff_norm_tendsto_zero.1 (hp v)
    · filter_upwards [hCb] with x hx a b
      exact norm_iteratedFDeriv_sub_le_of_bound ((h x).smooth ⊤) 0 (fun w => by simpa using hx w) a b
    · filter_upwards [hDb] with x hx w
      simpa using hx w
  | succ n ih =>
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ := hb 0 (n + 2)
    have ht : 0 < ε / (2 * (C + 1)) := div_pos hε (by linarith)
    have hCt : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) two_pos]
      nlinarith
    have hδ : 0 < ε * (ε / (2 * (C + 1))) / 4 := by
      have := mul_pos hε ht
      linarith
    filter_upwards [ih _ hδ, hCb] with x hx hxC v
    have hsm := (h x).smooth ⊤
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (h x)) :=
      hsm.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
    have hLip : ∀ a b, ‖fderiv ℝ (iteratedFDeriv ℝ n (h x)) a - fderiv ℝ (iteratedFDeriv ℝ n (h x)) b‖ ≤
        C * ‖a - b‖ := by
      intro a b
      rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      exact norm_iteratedFDeriv_sub_le_of_bound hsm (n + 1) (fun w => by simpa using hxC w) a b
    have hv := norm_fderiv_le_of_small_of_lipschitz hdiff hC0 ht hLip hx v
    rw [norm_fderiv_iteratedFDeriv] at hv
    have e : 2 * (ε * (ε / (2 * (C + 1))) / 4) / (ε / (2 * (C + 1))) = ε / 2 := by
      field_simp
      ring
    rw [e] at hv
    linarith

theorem schwartz_continuousAt_of_pointwise_of_bounded :
    ∀ {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : X → SchwartzMap V ℂ) (x0 : X), (∀ v, ContinuousAt (fun x => F x v) x0) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in nhds x0, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x) v‖ ≤ C) → ContinuousAt F x0 := by
  intro X _ V _ _ _ F x0 hc hb
  have hb' : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in nhds x0, ∀ v,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ ≤ C := by
    intro k n
    obtain ⟨C, hC⟩ := hb k n
    refine ⟨max C 0 + SchwartzMap.seminorm ℝ k n (F x0), add_nonneg (le_max_right _ _) (apply_nonneg _ _), ?_⟩
    filter_upwards [hC] with x hx v
    calc _ ≤ SchwartzMap.seminorm ℝ k n (F x - F x0) := SchwartzMap.le_seminorm ℝ k n _ v
      _ ≤ SchwartzMap.seminorm ℝ k n (F x) + SchwartzMap.seminorm ℝ k n (F x0) := map_sub_le_add _ _ _
      _ ≤ _ := add_le_add (SchwartzMap.seminorm_le_bound ℝ k n (F x) (le_max_right _ _)
          (fun w => (hx w).trans (le_max_left _ _))) le_rfl
  have hp : ∀ v, Tendsto (fun x => (F x - F x0) v) (nhds x0) (𝓝 0) := by
    intro v
    have h2 := (hc v).tendsto.sub_const (F x0 v)
    rw [sub_self] at h2
    exact h2
  rw [ContinuousAt, (schwartz_withSeminorms ℝ V ℂ).tendsto_nhds F (F x0)]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨C2, hC20, hC2⟩ := hb' (2 * k) n
  have hη : 0 < ε ^ 2 / (4 * (C2 + 1)) := div_pos (pow_pos hε 2) (by linarith)
  have hCη : C2 * (ε ^ 2 / (4 * (C2 + 1))) ≤ (ε / 2) ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ε]
  filter_upwards [eventually_forall_norm_iteratedFDeriv_le (h := fun x => F x - F x0) hp hb' n _ hη, hC2]
    with x hx hx2
  show SchwartzMap.seminorm ℝ k n (F x - F x0) < ε
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n _ (by linarith : (0 : ℝ) ≤ ε / 2)
    (fun v => ?_)) (by linarith)
  have ha : 0 ≤ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ := by positivity
  have hsq : (‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) ^ 2 ≤ (ε / 2) ^ 2 := by
    have e : (‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) ^ 2 =
        (‖v‖ ^ (2 * k) * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ := by
      rw [pow_mul']
      ring
    rw [e]
    exact (mul_le_mul (hx2 v) (hx v) (norm_nonneg _) hC20).trans hCη
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDensityTransportLinearEquivChirp
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.GaussTransport

theorem iteratedDeriv_cexp_mul (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

theorem hasTemperateGrowth_expI : Function.HasTemperateGrowth (fun t : ℝ => Complex.exp (Complex.I * t)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (Complex.I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, ‖Complex.I‖ ^ n, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_mul, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (Complex.I * x)‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

theorem hasTemperateGrowth_chirp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (s : ℝ) :
    Function.HasTemperateGrowth (fun x : V => Complex.exp (Complex.I * ((s * (Q x x).im : ℝ) : ℂ))) := by
  have h1 : Function.HasTemperateGrowth (fun x : V => Q x x) :=
    Q.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' Function.HasTemperateGrowth.id'
  have h2 : Function.HasTemperateGrowth (fun x : V => s * (Q x x).im) := by
    have := ((s • Complex.imCLM : ℂ →L[ℝ] ℝ)).hasTemperateGrowth.comp h1
    simpa [Function.comp_def] using this
  exact hasTemperateGrowth_expI.comp h2

end GlobalTheory.GaussTransport

namespace GlobalTheory.GaussTransport


open LineDeriv in
theorem transport : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : V ≃L[ℝ] E) (Q : V →L[ℝ] V →L[ℝ] ℂ) (N : Submodule ℂ (SchwartzMap V ℂ)),
    (∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re) →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ N₂ : Submodule ℂ (SchwartzMap E ℂ),
      (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N₂) ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N₂) ∧
      (∀ (g : SchwartzMap V ℂ) (G : SchwartzMap E ℂ), (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
        (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N₂) ∧
      (Dense (N₂ : Set (SchwartzMap E ℂ)) → Dense (N : Set (SchwartzMap V ℂ))) := by
  intro V _ _ _ E _ _ _ A Q N hQ hD hL
  set χ : V → ℂ := fun x => Complex.exp (Complex.I * ((-1 * (Q x x).im : ℝ) : ℂ)) with hχdef
  set χi : V → ℂ := fun x => Complex.exp (Complex.I * ((1 * (Q x x).im : ℝ) : ℂ)) with hχidef
  have hχ : χ.HasTemperateGrowth := hasTemperateGrowth_chirp Q (-1)
  have hχi : χi.HasTemperateGrowth := hasTemperateGrowth_chirp Q 1
  have hχχi : ∀ x, χ x * χi x = 1 := by
    intro x
    simp only [hχdef, hχidef, ← Complex.exp_add]
    rw [← Complex.exp_zero]; congr 1; push_cast; ring
  let Ψ : SchwartzMap E ℂ →L[ℂ] SchwartzMap V ℂ :=
    (SchwartzMap.smulLeftCLM ℂ χ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A)
  have hΨ : ∀ f x, Ψ f x = χ x * f (A x) := by
    intro f x
    simp [Ψ, SchwartzMap.smulLeftCLM_apply_apply hχ]
  refine ⟨N.comap (Ψ : SchwartzMap E ℂ →ₗ[ℂ] SchwartzMap V ℂ), ?_, ?_, ?_, ?_⟩
  · intro w f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    set v : V := A.symm w with hv
    let lam : V →L[ℝ] ℝ := Complex.imCLM.comp (Q.flip v + Q v)
    have hlam : ∀ x, lam x = (Q x v).im + (Q v x).im := by intro x; simp [lam]
    have hlamT : (fun x : V => ((lam x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp lam).hasTemperateGrowth
    have h1N : ∂_{v} (Ψ f) ∈ N := hD v (Ψ f) _ hf (fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv v (Ψ f) x)
    have h2N : SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) ∈ N :=
      hL lam (Ψ f) _ hf (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hlamT, smul_eq_mul])
    have hder : ∀ x, fderiv ℝ (⇑(Ψ f)) x v =
        χ x * fderiv ℝ (⇑f) (A x) w - Complex.I * ((lam x : ℂ) * (χ x * f (A x))) := by
      intro x
      have hfun : (⇑(Ψ f)) = χ * (fun y => f (A y)) := funext (hΨ f)
      let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp ((-1 : ℝ) • Complex.imCLM)
      have hq := Q.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
      have hu := ((L.hasFDerivAt).comp x hq).const_mul Complex.I
      have hχd : HasFDerivAt χ (Complex.exp (Complex.I * L (Q x x)) • (Complex.I • (L.comp
          (((ContinuousLinearMap.precompR V Q) (id x)) (ContinuousLinearMap.id ℝ V) +
            ((ContinuousLinearMap.precompL V Q) (ContinuousLinearMap.id ℝ V)) (id x))))) x := by
        refine hu.cexp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        simp [χ, L]
      have hfA : HasFDerivAt (fun y => f (A y)) ((fderiv ℝ (⇑f) (A x)).comp (A : V →L[ℝ] E)) x :=
        (f.differentiableAt.hasFDerivAt).comp x A.hasFDerivAt
      rw [hfun, (hχd.mul hfA).fderiv]
      have hχx : χ x = Complex.exp (-(Complex.I * ((Q x x).im : ℂ))) := by simp [χ]
      simp [L, v, hlam]
      rw [hχx]
      ring
    have hsum : Ψ f₁ = ∂_{v} (Ψ f) + Complex.I • SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) := by
      ext x
      rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hlamT,
        SchwartzMap.lineDerivOp_apply_eq_fderiv, hder, hΨ, hΨ, hf₁, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsum]
    exact N.add_mem h1N (N.smul_mem _ h2N)
  · intro ℓ f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    refine hL (ℓ.comp (A : V →L[ℝ] E)) (Ψ f) (Ψ f₁) hf (fun x => ?_)
    rw [hΨ, hΨ, hf₁]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    ring
  · intro g G hg hgN hG
    rw [Submodule.mem_comap]
    simp only [ContinuousLinearMap.coe_coe]
    have hΨG : Ψ G = g := by
      ext x
      rw [hΨ, hG, hg, hχdef]
      simp only
      rw [← Complex.exp_add]
      congr 1
      conv_rhs => rw [← Complex.re_add_im (Q x x)]
      rw [← hQ x]
      push_cast
      ring
    rw [hΨG]; exact hgN
  · intro hd
    have hsurj : Function.Surjective Ψ := by
      intro k
      refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (SchwartzMap.smulLeftCLM ℂ χi k), ?_⟩
      ext x
      rw [hΨ]
      simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply, SchwartzMap.smulLeftCLM_apply_apply hχi, smul_eq_mul]
      rw [← mul_assoc, hχχi, one_mul]
    refine (hsurj.denseRange.dense_image Ψ.continuous hd).mono ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hf

end GlobalTheory.GaussTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSuperposition
section
open MeasureTheory

namespace GlobalTheory

theorem one_add_pow_le_two_pow_mul_one_add_pow (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + a ^ n) := by
        have : 0 ≤ a ^ n := pow_nonneg ha n
        nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) n]
  · calc (1 + a) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow 2 a n
      _ ≤ 2 ^ n * (1 + a ^ n) := by
        have : 0 ≤ (2:ℝ) ^ n := by positivity
        nlinarith


open Real in
theorem fourier_inversion_real_linear_forms :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : SchwartzMap V ℂ),
    ∃ (m : ℕ) (A : EuclideanSpace ℝ (Fin m) →L[ℝ] (V →L[ℝ] ℝ)) (φ : EuclideanSpace ℝ (Fin m) → ℂ),
      Continuous φ ∧ (∀ n : ℕ, Integrable (fun w => (1 + ‖w‖) ^ n * ‖φ w‖)) ∧
      ∀ x, ψ x = ∫ w, φ w * Complex.exp ((A w x : ℂ) * Complex.I) := by
  intro V _ _ _ ψ
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let ψ' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm ψ
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V →L[ℝ] ℝ :=
    (2 * π) • (((ContinuousLinearMap.compL ℝ V _ ℝ).flip (e : V →L[ℝ] _)).comp (innerSL ℝ))
  have hA : ∀ w x, A w x = 2 * π * inner ℝ w (e x) := by
    intro w x
    simp [A]
  let Φ : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ := FourierTransform.fourier ψ'
  refine ⟨Module.finrank ℝ V, A, (Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ),
    Φ.continuous, fun n => ?_, fun x => ?_⟩
  · have hi : Integrable (fun w : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) =>
        2 ^ n * (‖Φ w‖ + ‖w‖ ^ n * ‖Φ w‖)) :=
      ((Φ.integrable_pow_mul volume 0).norm.add (Φ.integrable_pow_mul volume n) |>.congr
        (Filter.Eventually.of_forall fun w => by simp)).const_mul _
    refine hi.mono' (by fun_prop) (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 + ‖w‖) ^ n * ‖Φ w‖ ≤ 2 ^ n * (1 + ‖w‖ ^ n) * ‖Φ w‖ :=
          mul_le_mul_of_nonneg_right (one_add_pow_le_two_pow_mul_one_add_pow _ (norm_nonneg _) n) (norm_nonneg _)
      _ = 2 ^ n * (‖Φ w‖ + ‖w‖ ^ n * ‖Φ w‖) := by ring
  · have h1 : ψ x = ψ' (e x) := by
      simp [ψ']
    have h2 := congrArg (fun f : SchwartzMap _ ℂ => f (e x))
      (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ) ψ')
    rw [h1, ← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    congr 1
    ext w
    rw [hA, smul_eq_mul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInnerProductContinuous
section
open MeasureTheory

namespace GlobalTheory

theorem schwartz_pairing_conj_clm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by
  intro V _ _ _ μ hμ w
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  have hg : Function.HasTemperateGrowth (fun x => starRingEnd ℂ (w x)) :=
    (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).hasTemperateGrowth.comp w.hasTemperateGrowth
  refine ⟨(SchwartzMap.integralCLM ℂ μ).comp (SchwartzMap.smulLeftCLM ℂ (fun x => starRingEnd ℂ (w x))), ?_⟩
  intro u
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
  congr 1
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, mul_comm]

end GlobalTheory
end

