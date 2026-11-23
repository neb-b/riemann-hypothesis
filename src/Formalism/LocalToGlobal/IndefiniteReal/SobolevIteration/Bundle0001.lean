module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.DifferentiableUpdate
section
noncomputable section

open scoped ContDiff

namespace Formalism.IndefR.Tow.OrbStPf

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def pd (i : Fin N) (f : (Fin N → ℝ) → H) : (Fin N → ℝ) → H :=
  fun p => fderiv ℝ f p (Pi.single i 1)

def pds (L : List (Fin N)) (f : (Fin N → ℝ) → H) : (Fin N → ℝ) → H := L.foldr pd f

@[simp] lemma pds_nil (f : (Fin N → ℝ) → H) : pds [] f = f := rfl

@[simp] lemma pds_cons (i : Fin N) (L : List (Fin N)) (f : (Fin N → ℝ) → H) :
    pds (i :: L) f = pd i (pds L f) := rfl

lemma contDiff_pd (i : Fin N) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (pd i f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  exact hd.clm_apply contDiff_const

lemma contDiff_pds (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (pds L f) := by
  induction L with
  | nil => simpa using hf
  | cons i L ih => simpa only [pds_cons] using contDiff_pd i ih

lemma differentiable_pds (L : List (Fin N)) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (pds L f) := by
  exact (contDiff_pds L hf).differentiable (by simp)

lemma pd_hasDerivAt (i : Fin N) {f : (Fin N → ℝ) → H} (p : Fin N → ℝ) (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun t : ℝ => f (p + t • Pi.single i 1)) (pd i f p) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => p + t • (Pi.single i 1 : Fin N → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin N → ℝ)).const_add p
  have h2 : HasFDerivAt f (fderiv ℝ f (p + (0 : ℝ) • Pi.single i 1)) (p + (0 : ℝ) • Pi.single i 1) := by
    simpa using hf.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  simpa [pd, Function.comp_def] using h3

lemma pd_eq_deriv (i : Fin N) {f : (Fin N → ℝ) → H} (p : Fin N → ℝ) (hf : DifferentiableAt ℝ f p) :
    pd i f p = deriv (fun t : ℝ => f (p + t • Pi.single i 1)) 0 := by
  exact (pd_hasDerivAt i p hf).deriv.symm

lemma pd_clm (i : Fin N) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : Differentiable ℝ f) :
    pd i (fun p => A (f p)) = fun p => A (pd i f p) := by
  funext p
  have h := (A.hasFDerivAt.comp p (hf p).hasFDerivAt).fderiv
  simp only [pd]
  rw [show (fun q => A (f q)) = A ∘ f from rfl, h]
  rfl

lemma pds_clm (L : List (Fin N)) (A : H →L[ℝ] H) {f : (Fin N → ℝ) → H} (hf : ContDiff ℝ ∞ f) :
    pds L (fun p => A (f p)) = fun p => A (pds L f p) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih, pd_clm i A (differentiable_pds L hf)]

lemma update_add_single {i j : Fin N} (hij : i ≠ j) (r : Fin N → ℝ) (s t : ℝ) :
    Function.update (r + t • Pi.single i 1) j s = Function.update r j s + t • Pi.single i 1 := by
  funext k
  by_cases hk : k = j <;> simp [Function.update_apply, hk, Pi.single_apply, Ne.symm hij]

lemma differentiable_update (j : Fin N) (s : ℝ) :
    Differentiable ℝ (fun r : Fin N → ℝ => Function.update r j s) := by
  refine differentiable_pi.2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    simp
  · simpa [Function.update_of_ne hk] using
      (differentiable_apply k : Differentiable ℝ fun r : Fin N → ℝ => r k)

lemma pd_update (i j : Fin N) (hij : i ≠ j) (s : ℝ) {g : (Fin N → ℝ) → H} (hg : Differentiable ℝ g) :
    pd i (fun r => g (Function.update r j s)) = fun r => pd i g (Function.update r j s) := by
  funext r
  rw [pd_eq_deriv i (f := fun r => g (Function.update r j s)) r
      ((hg.comp (differentiable_update j s)) r),
    pd_eq_deriv i _ (hg _)]
  congr 1
  funext t
  rw [update_add_single hij r s t]

lemma pds_update (L : List (Fin N)) (j : Fin N) (hL : ∀ i ∈ L, i ≠ j) (s : ℝ) {g : (Fin N → ℝ) → H}
    (hg : ContDiff ℝ ∞ g) :
    pds L (fun r => g (Function.update r j s)) = fun r => pds L g (Function.update r j s) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [pds_cons]
    rw [ih (fun k hk => hL k (by simp [hk])),
      pd_update i j (hL i (by simp)) s (differentiable_pds L hg)]

end Formalism.IndefR.Tow.OrbStPf

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.HasFDerivAtIntegralPIter
section
noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace Formalism.IndefR.Tow.SobPf.Avg

variable {m : ℕ} {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def pIter (Φ : (Fin m → ℝ) → X → E) (j : ℕ) (t : Fin m → ℝ) (k : X) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin m → ℝ) E :=
  iteratedFDeriv ℝ j (fun t => Φ t k) t

omit [SecondCountableTopology X] [OpensMeasurableSpace X] [NormedSpace ℝ E] [CompleteSpace E] in
theorem ae_mem_of_compl {μ : Measure X} {K : Set X} (hμK : μ Kᶜ = 0) : ∀ᵐ x ∂μ, x ∈ K := mem_ae_iff.2 hμK

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem aesm_of_continuousOn {μ : Measure X} {K : Set X} (hKm : MeasurableSet K) (hμK : μ Kᶜ = 0)
    {F : Type*} [NormedAddCommGroup F] {f : X → F} (hf : ContinuousOn f K) : AEStronglyMeasurable f μ := by
  have h := hf.aestronglyMeasurable (μ := μ) hKm
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem_of_compl hμK)] at h

omit [CompleteSpace E] in
theorem pIter_contOn_slice {K : Set X} {Φ : (Fin m → ℝ) → X → E} {j : ℕ}
    (hc : ContinuousOn (fun q : (Fin m → ℝ) × X => pIter Φ j q.1 q.2) (Set.univ ×ˢ K)) (t : Fin m → ℝ) :
    ContinuousOn (fun k => pIter Φ j t k) K :=
  hc.comp (by fun_prop : Continuous fun k : X => (t, k)).continuousOn
    (fun _ hk => Set.mk_mem_prod (Set.mem_univ _) hk)

private theorem natCast_lt_top_withTop_enat (j : ℕ) : (j : WithTop ℕ∞) < ∞ := by
  exact_mod_cast ENat.natCast_lt_top j

theorem hasFDerivAt_pIter {Φ : (Fin m → ℝ) → X → E} {k : X} (hΦ : ContDiff ℝ ∞ fun t => Φ t k) (j : ℕ)
    (t : Fin m → ℝ) :
    HasFDerivAt (fun t => pIter Φ j t k)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Fin m → ℝ) E (pIter Φ (j + 1) t k)) t := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ j (fun t => Φ t k)) :=
    hΦ.differentiable_iteratedFDeriv (natCast_lt_top_withTop_enat j)
  have h2 := (hd t).hasFDerivAt
  rw [fderiv_iteratedFDeriv] at h2
  simpa [pIter] using h2

theorem hasFDerivAt_integral_pIter {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμK : μ Kᶜ = 0) {Φ : (Fin m → ℝ) → X → E}
    (hΦ : ∀ k ∈ K, ContDiff ℝ ∞ fun t => Φ t k)
    (hc : ∀ j : ℕ, ContinuousOn (fun q : (Fin m → ℝ) × X => pIter Φ j q.1 q.2) (Set.univ ×ˢ K))
    (j : ℕ) (t₀ : Fin m → ℝ) :
    HasFDerivAt (fun t => ∫ k, pIter Φ j t k ∂μ)
      (∫ k, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Fin m → ℝ) E (pIter Φ (j + 1) t₀ k) ∂μ)
      t₀ := by
  have hae : ∀ᵐ k ∂μ, k ∈ K := ae_mem_of_compl hμK
  have hsm : ∀ (i : ℕ) (t : Fin m → ℝ),
      AEStronglyMeasurable (fun k => pIter Φ i t k) μ := fun i t =>
    aesm_of_continuousOn hKm hμK (pIter_contOn_slice (hc i) t)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t₀ 1).prod hK).exists_bound_of_continuousOn
    ((hc (j + 1)).mono (Set.prod_mono (Set.subset_univ _) subset_rfl))
  obtain ⟨C₀, hC₀⟩ :=
    hK.exists_bound_of_continuousOn (pIter_contOn_slice (hc j) t₀)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun t k => pIter Φ j t k)
    (F' := fun t k => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Fin m → ℝ) E
      (pIter Φ (j + 1) t k))
    (bound := fun _ => C) (s := ball t₀ 1) (ball_mem_nhds t₀ zero_lt_one) ?_ ?_ ?_ ?_ (integrable_const C) ?_
  · filter_upwards with t using hsm j t
  · exact Integrable.mono' (integrable_const C₀) (hsm j t₀)
      (by filter_upwards [hae] with k hk using hC₀ k hk)
  · exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (hsm (j + 1) t₀)
  · filter_upwards [hae] with k hk t ht
    exact (LinearIsometryEquiv.norm_map _ _).trans_le
      (hC (t, k) (Set.mk_mem_prod (ball_subset_closedBall ht) hk))
  · filter_upwards [hae] with k hk t _
    exact hasFDerivAt_pIter (hΦ k hk) j t

private theorem integral_linearIsometryEquiv_comp {α F G : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F ≃ₗᵢ[ℝ] G) (φ : α → F) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.toContinuousLinearEquiv.integral_comp_comm φ

theorem contDiff_integral_param {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμK : μ Kᶜ = 0) {Φ : (Fin m → ℝ) → X → E}
    (hΦ : ∀ k ∈ K, ContDiff ℝ ∞ fun t => Φ t k)
    (hc : ∀ j : ℕ, ContinuousOn (fun q : (Fin m → ℝ) × X => pIter Φ j q.1 q.2) (Set.univ ×ˢ K)) :
    (∀ j : ℕ, iteratedFDeriv ℝ j (fun t => ∫ k, Φ t k ∂μ) = fun t => ∫ k, pIter Φ j t k ∂μ) ∧
      ContDiff ℝ ∞ (fun t => ∫ k, Φ t k ∂μ) := by
  have key : ∀ j : ℕ, iteratedFDeriv ℝ j (fun t => ∫ k, Φ t k ∂μ) =
      fun t => ∫ k, pIter Φ j t k ∂μ := by
    intro j
    induction j with
    | zero =>
      funext t
      simp only [pIter, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      rw [integral_linearIsometryEquiv_comp]
    | succ j ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, ih]
      funext t
      rw [Function.comp_apply,
        (hasFDerivAt_integral_pIter hK hKm hμK hΦ hc j t).fderiv,
        integral_linearIsometryEquiv_comp]
      simp
  refine ⟨key, ?_⟩
  apply contDiff_of_differentiable_iteratedFDeriv
  intro i _
  rw [key i]
  intro t
  exact (hasFDerivAt_integral_pIter hK hKm hμK hΦ hc i t).differentiableAt

end Formalism.IndefR.Tow.SobPf.Avg

end
end

