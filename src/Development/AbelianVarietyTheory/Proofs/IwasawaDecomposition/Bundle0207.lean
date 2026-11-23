module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem toMK_mem_UJ (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem continuous_orbit (hσ : IsURepOn (UJset ε) σ) (w : H) : Continuous fun k : KG ε => σ (toMK k) w :=
  (hσ.2.2 w).comp_continuous (continuous_toMK ε) toMK_mem_UJ

theorem integrable_avg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (w : H) :
    Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) :=
  (he.smul (continuous_orbit hσ w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem sigma_K_mul (hσ : IsURepOn (UJset ε) σ) (a b : KG ε) (w : H) :
    σ (toMK (a * b)) w = σ (toMK a) (σ (toMK b) w) :=
  sigma_mul hσ (toMK_mem_UJ a) (toMK_mem_UJ b) w

theorem inner_K (hσ : IsURepOn (UJset ε) σ) (a : KG ε) (x w : H) :
    ⟪σ (toMK a) w, x⟫_ℂ = ⟪w, σ (toMK a⁻¹) x⟫_ℂ := by
  have h := LinearIsometry.inner_map_map ⟨(σ (toMK a) : H →ₗ[ℂ] H), hσ.2.1 _ (toMK_mem_UJ a)⟩ w (σ (toMK a⁻¹) x)
  have e : σ (toMK a) (σ (toMK a⁻¹) x) = x := by
    rw [← sigma_K_mul hσ, mul_inv_cancel]; exact sigma_one hσ x
  rw [← h]
  exact congrArg (fun z => ⟪σ (toMK a) w, z⟫_ℂ) e.symm

theorem kFinFun_coef (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : IsKFin ε σ y) :
    KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) := by
  obtain ⟨S, hS, hyS, hK⟩ := hy
  let φ : H → H → KG ε → ℂ := fun s s' k => ⟪σ (toMK k) s', s⟫_ℂ
  obtain ⟨t, ht⟩ : S.FG := Module.Finite.iff_fg.1 hS
  have hfin : (Set.image2 φ (t : Set H) (t : Set H)).Finite := t.finite_toSet.image2 _ t.finite_toSet
  have key : ∀ s ∈ S, ∀ s' ∈ S, φ s s' ∈ Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)) := by
    intro s hs s' hs'
    rw [← ht] at hs hs'
    induction hs using Submodule.span_induction with
    | mem x hx =>
      induction hs' using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span (Set.mem_image2_of_mem hx hz)
      | zero =>
        have : φ x 0 = 0 := by ext k; simp [φ]
        rw [this]; exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : φ x (a + b) = φ x a + φ x b := by ext k; simp [φ, inner_add_left]
        rw [this]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : φ x (c • a) = (starRingEnd ℂ c) • φ x a := by ext k; simp [φ, inner_smul_left, mul_comm]
        rw [this]; exact Submodule.smul_mem _ _ ha
    | zero =>
      have : φ 0 s' = 0 := by ext k; simp [φ]
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : φ (a + b) s' = φ a s' + φ b s' := by ext k; simp [φ, inner_add_right]
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : φ (c • a) s' = c • φ a s' := by ext k; simp [φ, inner_smul_right]
      rw [this]; exact Submodule.smul_mem _ _ ha
  have htS : ∀ x ∈ (t : Set H), x ∈ S := fun x hx => ht ▸ Submodule.subset_span hx
  refine ⟨Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)), FiniteDimensional.span_of_finite ℂ hfin, ?_, ?_, ?_⟩
  · have : (fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ) = φ y y := by
      ext k; exact inner_conj_symm _ _
    rw [this]; exact key y hyS y hyS
  · intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, -, b, -, rfl⟩ := hx
      exact (continuous_orbit hσ b).inner continuous_const
    | zero => exact continuous_zero
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  · intro ψ hψ k₀
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      constructor
      · have : (fun k => φ a b (k₀ * k)) = φ (σ (toMK k₀⁻¹) a) b := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ, inner_K hσ]
        rw [this]; exact key _ (hK _ (toMK_mem_K _) _ (htS a ha)) _ (htS b hb)
      · have : (fun k => φ a b (k * k₀)) = φ a (σ (toMK k₀) b) := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ]
        rw [this]; exact key _ (htS a ha) _ (hK _ (toMK_mem_K _) _ (htS b hb))
    | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨Submodule.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
    | smul c a _ ha => exact ⟨Submodule.smul_mem _ c ha.1, Submodule.smul_mem _ c ha.2⟩

variable [CompleteSpace H]

theorem inner_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (x w : H) :
    ⟪x, kAvg ε σ e w⟫_ℂ = ∫ k, e k * ⟪x, σ (toMK k) w⟫_ℂ ∂(muK ε) := by
  rw [kAvg, ← integral_inner (integrable_avg hσ he w)]
  simp only [inner_smul_right]

theorem inner_kAvg_ne_zero (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : y ≠ 0) :
    ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0 := by
  have hc : Continuous fun k : KG ε => ⟪y, σ (toMK k) y⟫_ℂ := continuous_const.inner (continuous_orbit hσ y)
  rw [inner_kAvg hσ (e := fun k => star ⟪y, σ (toMK k) y⟫_ℂ) (continuous_star.comp hc)]
  have e : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  simp only [e]
  rw [integral_complex_ofReal]
  have hpos : 0 < ∫ k : KG ε, ‖⟪y, σ (toMK k) y⟫_ℂ‖ ^ 2 ∂(muK ε) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (hc.norm.pow 2)
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_
    have : σ (toMK (1 : KG ε)) y = y := sigma_one hσ y
    rw [this]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hy))
  exact_mod_cast hpos.ne'


omit [CompleteSpace H] in
theorem exists_clm_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w := by
  let L : H →ₗ[ℂ] H :=
    { toFun := kAvg ε σ e
      map_add' := fun x y => by
        simp only [kAvg, map_add (f := _), smul_add]
        exact integral_add (integrable_avg hσ he x) (integrable_avg hσ he y)
      map_smul' := fun c x => by
        simp only [kAvg, map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂(muK ε)) fun w => ?_, fun w => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, fun k : KG ε => hσ.2.1 _ (toMK_mem_UJ k) w]
  exact integral_mul_const _ _

theorem kAvg_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {S : Submodule ℂ H}
    [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H} (hz : z ∈ S) : kAvg ε σ e z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro u hu
  rw [inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪u, σ (toMK k) z⟫_ℂ = 0 := fun k =>
    Submodule.inner_left_of_mem_orthogonal (hK _ (toMK_mem_K k) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KCoef

namespace GlobalTheory.TypeSum

theorem kCoef_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ y, IsKFin ε σ y → KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ)) ∧ (∀ y : H, y ≠ 0 → ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0) ∧ (∀ e : KG ε → ℂ, Continuous e → ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w) ∧ ∀ e : KG ε → ℂ, Continuous e → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ z ∈ S, kAvg ε σ e z ∈ S :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hy => KCoef.kFinFun_coef hσ hy, fun _ hy => KCoef.inner_kAvg_ne_zero hσ hy,
    fun _ he => KCoef.exists_clm_kAvg hσ he, fun _ he _ _ hK _ hz => KCoef.kAvg_mem hσ he hK hz⟩

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAvgClosure
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem isAvg_sigma {g : Mx n} (hg : g ∈ UJset ε) : IsAvg ε σ (σ g) :=
  ⟨{g}, 1, isCompact_singleton, Set.singleton_subset_iff.2 hg, zero_le_one, fun ι _ x w M _ h => by
    rw [one_mul]; exact h g rfl⟩

theorem IsAvg.add {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') : IsAvg ε σ (fun w => T w + T' w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨Z ∪ Z', C + C', h1.union k1, Set.union_subset h2 k2, add_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_add_right, Finset.sum_add_distrib, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h4 ι x w M hM fun y hy => hb y (Or.inl hy))
    (k4 ι x w M hM fun y hy => hb y (Or.inr hy)))

theorem IsAvg.comp (hσ : IsURepOn (UJset ε) σ) {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') :
    IsAvg ε σ (fun w => T (T' w)) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨(fun p : Mx n × Mx n => p.1 * p.2) '' (Z ×ˢ Z'), C * C',
    (h1.prod k1).image (continuous_fst.matrix_mul continuous_snd), ?_, mul_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact mul_mem_UJ (h2 hp.1) (k2 hp.2)
  rw [mul_assoc]
  refine h4 ι x (fun j => T' (w j)) (C' * M) (mul_nonneg k3 hM) fun y hy => ?_
  simp only [inner_sigma hσ (h2 hy)]
  refine k4 ι (fun j => σ y⁻¹ (x j)) w M hM fun y' hy' => ?_
  have := hb (y * y') ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
  simpa only [sigma_mul hσ (h2 hy) (k2 hy'), inner_sigma hσ (h2 hy)] using this

theorem IsAvg.smul (c : ℂ) {T : H → H} (h : IsAvg ε σ T) : IsAvg ε σ (fun w => c • T w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  refine ⟨Z, ‖c‖ * C, h1, h2, mul_nonneg (norm_nonneg _) h3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h4 ι x w M hM hb) (norm_nonneg _)

theorem isAvg_zero : IsAvg ε σ (fun _ => 0) :=
  ⟨∅, 0, isCompact_empty, Set.empty_subset _, le_rfl, fun ι _ x w M _ _ => by simp⟩

theorem isAvg_kAvg [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    IsAvg ε σ (kAvg ε σ e) := by
  refine ⟨Kset ε, ∫ k, ‖e k‖ ∂(muK ε), (maximal_compact_facts n ε).2.1, fun k hk => K_le_UJ hk,
    integral_nonneg fun _ => norm_nonneg _, fun ι _ x w M hM hb => ?_⟩
  have hi : ∀ v : H, Integrable (fun k : KG ε => e k • σ (toMK k) v) (muK ε) := fun v =>
    (he.smul ((hσ.2.2 v).comp_continuous (continuous_toMK ε)
      fun k => K_le_UJ (toMK_mem_K k))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [kAvg]
  simp only [fun j => (integral_inner (𝕜 := ℂ) (hi (w j)) (x j)).symm]
  rw [← integral_finsetSum _ fun j _ => (hi (w j)).const_inner (x j), ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((he.norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).mul_const M) (Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb _ (toMK_mem_K k)) (norm_nonneg _)

theorem isAvg_closure : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ g ∈ UJset ε, IsAvg ε σ (σ g)) ∧ (∀ T T' : H → H, IsAvg ε σ T → IsAvg ε σ T' → IsAvg ε σ (fun w => T w + T' w) ∧ IsAvg ε σ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : H → H), IsAvg ε σ T → IsAvg ε σ (fun w => c • T w)) ∧ (∀ e : KG ε → ℂ, Continuous e → IsAvg ε σ (kAvg ε σ e)) ∧ IsAvg ε σ (fun _ => 0) :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hg => isAvg_sigma hg, fun _ _ h h' => ⟨h.add h', h.comp hσ h'⟩,
    fun c _ h => h.smul c, fun _ he => isAvg_kAvg hσ he, isAvg_zero⟩

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedDerivativeFamiliesModerateGrowth
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.FamClosed

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_flow {R : ℝ → (E →L[ℂ] E)} (hR : ∀ s t, R (s + t) = (R s).comp (R t)) {a b : E}
    (h : HasDerivAt (fun t : ℝ => R t a) b 0) (s : ℝ) : HasDerivAt (fun t : ℝ => R t a) (R s b) s := by
  have h1 := ((R s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = R s (R (t - s) a)
  rw [← ContinuousLinearMap.comp_apply, ← hR, add_sub_cancel]

theorem norm_sub_le {f f' : ℝ → E} (hf : ∀ s, HasDerivAt f (f' s) s) {t C : ℝ}
    (hC : ∀ s, |s| ≤ |t| → ‖f' s‖ ≤ C) : ‖f t - f 0‖ ≤ C * |t| := by
  have := (convex_closedBall (0 : ℝ) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := C)
    (fun s _ => (hf s).hasDerivWithinAt) (fun s hs => hC s (by simpa using hs))
    (Metric.mem_closedBall_self (abs_nonneg t)) (y := t) (by simp)
  simpa using this

theorem taylor_bound {R : ℝ → (E →L[ℂ] E)} (h0 : R 0 = 1) (hR : ∀ s t, R (s + t) = (R s).comp (R t)) {M : ℝ}
    (hM : ∀ s, |s| ≤ 1 → ‖R s‖ ≤ M) {a b c : E} (ha : HasDerivAt (fun t : ℝ => R t a) b 0)
    (hb : HasDerivAt (fun t : ℝ => R t b) c 0) {t : ℝ} (ht : |t| ≤ 1) :
    ‖R t a - a - t • b‖ ≤ M * ‖c‖ * |t| * |t| := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have h1 : ∀ s, |s| ≤ |t| → ‖R s b - b‖ ≤ M * ‖c‖ * |t| := fun s hs => by
    have := norm_sub_le (hasDerivAt_flow hR hb) (t := s) (C := M * ‖c‖) fun u hu =>
      ((R u).le_opNorm c).trans (mul_le_mul_of_nonneg_right (hM u (hu.trans (hs.trans ht))) (norm_nonneg _))
    simp only [h0, ContinuousLinearMap.one_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have h2 := norm_sub_le (f := fun s : ℝ => R s a - s • b) (f' := fun s => R s b - b)
    (fun s => by
      have := (hasDerivAt_flow hR ha s).fun_sub ((hasDerivAt_id' s).smul_const b)
      rwa [one_smul] at this) h1
  simp only [h0, ContinuousLinearMap.one_apply, zero_smul, sub_zero] at h2
  rwa [sub_right_comm]

theorem hasDerivAt_of_bound {f : ℝ → E} {b : E} {K : ℝ}
    (h : ∀ t, |t| ≤ 1 → ‖f t - f 0 - t • b‖ ≤ K * |t| * |t|) : HasDerivAt f b 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  have h1 : (fun t : ℝ => f t - f 0 - t • b) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
    have := h t (by simpa using ht)
    rwa [norm_pow, Real.norm_eq_abs, sq, ← mul_assoc]
  exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

end GlobalTheory.TypeSum.FamClosed


open GlobalTheory.TypeSum.FamClosed in
theorem GlobalTheory.TypeSum.isClosed_fam (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : Mx n → (E →L[ℂ] E)) (hρ : ModRep ε ρ) : IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) := by
  obtain ⟨h1, hmul, C, N, hC⟩ := hρ
  refine isClosed_of_closure_subset fun v hv => ⟨fun l X => ?_, fun l₁ l₂ a X Y => ?_, fun l₁ l₂ X Y Z hZ => ?_⟩
  · have hX : (X : Mx n) ∈ lieSet ε := X.2
    have h0 : ρ (NormedSpace.exp ((0 : ℝ) • (X : Mx n))) = 1 := by rw [zero_smul, NormedSpace.exp_zero, h1]
    have hR : ∀ s t : ℝ, ρ (NormedSpace.exp ((s + t) • (X : Mx n))) =
        (ρ (NormedSpace.exp (s • (X : Mx n)))).comp (ρ (NormedSpace.exp (t • (X : Mx n)))) := fun s t => by
      rw [exp_add_smul, hmul _ (exp_mem_UJ hX s) _ (exp_mem_UJ hX t)]
    have hc : Continuous fun s : ℝ => C * (1 + hs (NormedSpace.exp (s • (X : Mx n)))) ^ N :=
      continuous_const.mul ((continuous_const.add (continuous_hs.comp (continuous_exp_smul _))).pow N)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ) 1).bddAbove_image hc.continuousOn
    have hM' : ∀ s : ℝ, |s| ≤ 1 → ‖ρ (NormedSpace.exp (s • (X : Mx n)))‖ ≤ M := fun s hs =>
      (hC _ (exp_mem_UJ hX s)).trans (hM ⟨s, by simpa using hs, rfl⟩)
    refine hasDerivAt_of_bound (K := M * ‖v (X :: X :: l)‖) fun t ht => ?_
    simp only [h0, ContinuousLinearMap.one_apply]
    have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        ‖ρ (NormedSpace.exp (t • (X : Mx n))) (w l) - w l - t • w (X :: l)‖ ≤ M * ‖w (X :: X :: l)‖ * |t| * |t|} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w (hw : w ∈ (Fam ε ρ : Set (List (lie (Jm ε)) → E))) => taylor_bound (R := fun s : ℝ => ρ (NormedSpace.exp (s • (X : Mx n))))
      h0 hR hM' (hw.1 l X) (hw.1 (X :: l) X) ht) hcl hv
  · have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        w (l₁ ++ (a • X + Y) :: l₂) = (a : ℂ) • w (l₁ ++ X :: l₂) + w (l₁ ++ Y :: l₂)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w (hw : w ∈ (Fam ε ρ : Set (List (lie (Jm ε)) → E))) => hw.2.1 l₁ l₂ a X Y) hcl hv
  · have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        w (l₁ ++ X :: Y :: l₂) - w (l₁ ++ Y :: X :: l₂) = w (l₁ ++ Z :: l₂)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w (hw : w ∈ (Fam ε ρ : Set (List (lie (Jm ε)) → E))) => hw.2.2 l₁ l₂ X Y Z hZ) hcl hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem isKFin_dRep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε,
      IsKFin ε σ (dRep σ X v) := by
  intro n ε H _ _ _ σ h v hv X hX
  obtain ⟨S, h1, h2, h3⟩ := hv
  have hS : S ≤ smooth (Jm ε) σ := fun s hs => h.2.2.1 s ⟨S, h1, hs, h3⟩
  let b := Module.finBasis ℝ (lie (Jm ε))
  let L : Fin (Module.finrank ℝ (lie (Jm ε))) → (S →ₗ[ℂ] H) := fun i =>
    (smooth (Jm ε) σ).subtype ∘ₗ dOp (isUnit_Jm ε) h.1 (b i).2 ∘ₗ Submodule.inclusion hS
  have hL : ∀ i (s : S), L i s = dRep σ (b i) s := fun _ _ => rfl
  let T : Submodule ℂ H := ⨆ i, LinearMap.range (L i)
  have hT : ∀ Y ∈ lieSet ε, ∀ s ∈ S, dRep σ Y s ∈ T := by
    intro Y hY s hs
    have e : Y = ∑ i, b.repr ⟨Y, hY⟩ i • (b i : Mx n) := by
      have := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
      simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using this.symm
    rw [e, h.dRep_sum (fun i => (b i).2) (hS hs)]
    refine T.sum_mem fun i _ => T.smul_mem _ ?_
    exact Submodule.mem_iSup_of_mem i ⟨⟨s, hs⟩, rfl⟩
  refine ⟨T, inferInstance, hT X hX v h2, fun k hk w hw => ?_⟩
  have hg := K_le_UJ hk
  have : T ≤ T.comap (σ k : H →ₗ[ℂ] H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    have hinv : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv (mul_inv_UJ hg)
    have hY : k * (b i : Mx n) * k⁻¹ ∈ lieSet ε := by
      have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) (b i).2
      rwa [hinv] at this
    have e := Dw_translate h.1 hg (hS s.2) (l := [k * (b i : Mx n) * k⁻¹]) (by simpa using hY)
    have e2 : k⁻¹ * (k * (b i : Mx n) * k⁻¹) * k = b i := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_UJ hg, one_mul, mul_assoc, inv_mul_UJ hg, mul_one]
    simp only [Dw, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e2] at e
    show σ k (dRep σ (b i) s) ∈ T
    rw [← e]
    exact hT _ hY _ (h3 k hk s s.2)
  exact this hw

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelChoices

open Formalism.L2.Host Formalism.L2.Herm

variable {D : D7}

theorem mem_crdLat (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ crdLat V V.L0 ↔ (crd V).symm x ∈ V.L0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (crd V).symm (crd V y) ∈ V.L0
    rwa [LinearEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, (crd V).apply_symm_apply x⟩

theorem coe_crdLat (V : HSp D) : (crdLat V V.L0 : Set (Fin V.rank → D.host.E)) = L0c D V := by
  ext x
  rw [SetLike.mem_coe, mem_crdLat]
  show V.frame.equivFun.symm x ∈ V.L0 ↔ _
  rw [Module.Basis.equivFun_symm_apply]
  rfl

theorem dualL_crdLat (V : HSp D) : dualL D.sp.cm V (crdLat V V.L0) = crdLat V V.L0 := by
  unfold dualL
  conv_rhs => rw [← Submodule.span_eq (crdLat V V.L0)]
  congr 1
  ext x
  rw [SetLike.mem_coe, mem_crdLat]
  conv_rhs => rw [← V.baseLattice_isUnimodular]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Submodule.mem_one]
  constructor
  · intro h y hy
    have := h (crd V y) ⟨y, hy, rfl⟩
    rw [hT_crd D.sp.cm, LinearEquiv.apply_symm_apply]
    exact this
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    rw [hT_crd D.sp.cm, LinearEquiv.apply_symm_apply] at this
    exact this

theorem isSDFrame_of_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) (N : ℕ) : IsSDFrame V β Λ N := by
  obtain ⟨c, hc⟩ := h
  refine ⟨0, ?_⟩
  rw [one_pow] at hc
  rwa [pow_zero]

theorem isUnitary_of_orderDvd {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) :
    χ.IsUnitary := by
  intro x
  have h1 : (χ.1 x) ^ n = 1 := by
    have : (χ ^ n).1 x = 1 := by rw [h]; rfl
    rw [← this]; rfl
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem exists_levCh (D : D7) (C : CharFrame D) (T : Type) (μ0 : T) (ξ : T → HChar D.host.E)
    (Q : T → Finset (Pl D.host.E)) (hinj : Function.Injective ξ) (hbase : ξ μ0 = 1)
    (hfin : ∀ t, ∃ n : ℕ, 0 < n ∧ (ξ t).OrderDvd n) (htriv : ∀ t, (ξ t).TrivOn D.host.F)
    (htame : ∀ t v, (ξ t).TameAt v) (hpl : ∀ t, Lev.IsTwistPlaces D.host.g (Q t))
    (hoff : ∀ t, ∀ PP ∈ Q t, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
      ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hde : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
      ∀ t, ∀ PP ∈ Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭)
    (hram : ∀ t PP, ¬ (ξ t).UnrAt PP ↔ PP ∈ Q t ∨ ∃ PP' ∈ Q t, Lev.IsConjPl PP' PP) :
    ∃ L : LevCh D T, L.C = C ∧ L.xiH = ξ ∧ L.Q = Q ∧ (∀ j, L.ΛY j = crdLat _ (Yc D j).L0) ∧ L.Is μ0 := by
  classical
  choose m hm using fun j : Fin D.R.m => _root_.GlobalTheory.CharTransport.exists_chrEq D (C.mu0 j) (C.isMu0 j).unitary
  obtain ⟨η, hη⟩ := _root_.GlobalTheory.CharTransport.exists_chrEq D C.eta C.isEta.unitary
  choose x hx using fun t => _root_.GlobalTheory.CharTransport.exists_chrEq D (ξ t) (by obtain ⟨n, hn, h⟩ := hfin t; exact isUnitary_of_orderDvd hn h)
  choose r hr using fun (j : Fin D.R.m) PP => GlobalTheory.exists_isRes_of_tameAt D (C.mu0 j) PP ((C.isMu0 j).tame PP)
  choose s hs using fun t PP => GlobalTheory.exists_isRes_of_tameAt D (ξ t) PP (htame t PP)
  choose β hβ using fun V : HSp D => _root_.GlobalTheory.AdelicFrame.exists_isSDFrame D V (crdLat V V.L0) (coe_crdLat V) (dualL_crdLat V)
  refine ⟨{ C := C, xiH := ξ
            mu0 := fun j => if h : j - 1 < D.R.m then m ⟨j - 1, h⟩ else 1
            eta := η, xi := x
            Pg := Finset.univ.biUnion fun k => aboveF (L := D.host.E) D.host.K (C.P.pb k)
            Q := Q
            chi := fun j PP => if h : j - 1 < D.R.m then (r ⟨j - 1, h⟩ PP)⁻¹ else 1
            xiR := s
            ΛY := fun _ => crdLat _ (HSpace.L0 _), ΛX := crdLat _ (HSpace.L0 _)
            ΛV := fun _ => crdLat _ (HSpace.L0 _), ΛW := fun _ => crdLat _ (HSpace.L0 _)
            βY := fun _ => β _, βX := β _, βV := fun _ => β _, βW := fun _ => β _ }, rfl, rfl, rfl, fun _ => rfl, ?_⟩
  exact
    { mu0 := fun j => by
        have h : (j : ℕ) + 1 - 1 < D.R.m := j.2
        simp only [dif_pos h]
        exact hm j
      eta := hη, xi := hx, xi_inj := hinj, xi_base := hbase, xi_fin := hfin, xi_triv := htriv, xi_tame := htame
      Pg := fun PP => by
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, aboveF, Set.Finite.mem_toFinset]
        rfl
      Q_pl := hpl, Q_off := hoff, Q_de := hde, Q_ram := hram
      chi := fun j PP _ => by
        have h : (j : ℕ) + 1 - 1 < D.R.m := j.2
        simp only [dif_pos h, inv_inv]
        exact hr j PP
      xiR := fun t PP _ => hs t PP
      βY := fun j _ => isSDFrame_of_one (hβ _) _
      βX := hβ _, βV := fun _ => hβ _, βW := fun _ => hβ _ }

theorem exists_levCh_unit : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D), ∃ L : LevCh D Unit, L.C = C ∧ L.Is () := by
  intro D C
  obtain ⟨L, h1, -, -, -, h2⟩ := exists_levCh D C Unit () (fun _ => 1) (fun _ => ∅) (fun _ _ _ => rfl) rfl
    (fun _ => ⟨1, one_pos, one_pow 1⟩) (fun _ => (isPsi_one (H := D.host) 2).triv) (fun _ _ _ _ _ => rfl)
    (fun _ _ h => absurd h (Finset.notMem_empty _)) (fun _ _ h => absurd h (Finset.notMem_empty _))
    (fun _ _ => ⟨C.P.pb 0, fun _ _ h => absurd h (Finset.notMem_empty _)⟩)
    (fun _ _ => iff_of_false (fun h => h fun _ _ => rfl) (by simp))
  exact ⟨L, h1, h2⟩

end GlobalTheory.LevelChoices
end

