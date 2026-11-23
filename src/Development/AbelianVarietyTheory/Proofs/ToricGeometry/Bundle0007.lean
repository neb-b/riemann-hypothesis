module

public import Mathlib
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.DifferentiableOnThetaProdOfNormal
section
open ReciprocityTheory.PTheta

namespace GlobalTheory

theorem differentiable_thetaTerm_prod {ι : Type} [Fintype ι] (a b : ι → ℝ) (l : ι → ℤ) :
    Differentiable ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l) := by
  unfold thetaTerm eC
  simp only [dotProduct, Matrix.mulVec, shiftVec, ofRealVec, Pi.add_apply, Matrix.of_apply]
  fun_prop

theorem differentiableOn_theta_prod_of_normal {ι : Type} [Fintype ι] (a b : ι → ℝ)
    {U : Set ((ι → ℂ) × (ι → ι → ℂ))} (hU : IsOpen U)
    (hle : ∀ K ⊆ U, IsCompact K → ∃ u : (ι → ℤ) → ℝ, Summable u ∧
      ∀ l, ∀ p ∈ K, ‖thetaTerm a b p.1 (Matrix.of p.2) l‖ ≤ u l) :
    DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) U := by
  intro c hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc
  have hK : Metric.closedBall c (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨u, hu, hbd⟩ := hle _ hK (isCompact_closedBall c (ε / 2))
  have hr : (0 : ℝ) < ε / 4 := by positivity
  have hlim : TendstoUniformlyOn
      (fun s : Finset (ι → ℤ) => fun p : (ι → ℂ) × (ι → ι → ℂ) =>
        ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) Filter.atTop
      (Metric.ball c (2 * (ε / 4))) := by
    have h := tendstoUniformlyOn_tsum hu (fun l p hp => hbd l p hp)
    refine h.mono ?_
    intro p hp
    exact Metric.ball_subset_closedBall (by simpa [show 2 * (ε / 4) = ε / 2 by ring] using hp)
  have hF : ∀ᶠ s : Finset (ι → ℤ) in Filter.atTop, DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (Metric.ball c (2 * (ε / 4))) :=
    Filter.Eventually.of_forall fun s => by
      have h := Differentiable.sum (u := s) fun l _ => differentiable_thetaTerm_prod a b l
      have e : (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l) =
          ∑ l ∈ s, fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l := by
        funext p
        rw [Finset.sum_apply]
      rw [e]
      exact h.differentiableOn
  have hd := (GlobalTheory.SCV.tendstoUniformlyOn_fderiv_ball hlim hF).1
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

theorem thetaHolo_of_domainOpen_of_mTest (hopen : DomainOpenStatement)
    (hM : ThetaMTestStatement) : ThetaHoloStatement := by
  intro ι _ a b
  refine differentiableOn_theta_prod_of_normal a b ((hopen ι).preimage continuous_snd) ?_
  intro K hKU hK
  obtain ⟨u, hu, hbd⟩ := hM ι a K hK (fun p hp => hKU hp)
  exact ⟨u, hu, fun l p hp => hbd b p hp l⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMulDotProductLeOfIsCompactThetaDomain
section
open Complex Matrix ReciprocityTheory.PTheta

noncomputable section

namespace GlobalTheory

variable {ι : Type*} [Fintype ι]

open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
private lemma im_quadForm_pos_of_mem_thetaDomain {τ : Matrix ι ι ℂ} (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.ThetaDomain ι)
    (x : ι → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ τ.map Complex.im *ᵥ x := by
  have h : ((τ.map Complex.im) + (τ.map Complex.im).transpose).PosDef := by
    unfold _root_.ReciprocityTheory.PTheta.ThetaDomain at hτ
    exact hτ
  have h1 : x ⬝ᵥ (τ.map Complex.im)ᵀ *ᵥ x = x ⬝ᵥ τ.map Complex.im *ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have h2 := h.dotProduct_mulVec_pos hx
  rw [add_mulVec, dotProduct_add, star_trivial, h1] at h2
  linarith

open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
private lemma exists_uniform_im_quadForm_lower_bound_on_compact {K : Set ((ι → ℂ) × (ι → ι → ℂ))}
    (hK : IsCompact K) (hKd : ∀ p ∈ K, Matrix.of p.2 ∈ _root_.ReciprocityTheory.PTheta.ThetaDomain ι) :
    ∃ c > 0, ∀ p ∈ K, ∀ x : ι → ℝ,
      c * x ⬝ᵥ x ≤ x ⬝ᵥ (Matrix.of p.2).map Complex.im *ᵥ x := by
  classical
  set g : ((ι → ℂ) × (ι → ι → ℂ)) × (ι → ℝ) → ℝ :=
    fun q => q.2 ⬝ᵥ (Matrix.of q.1.2).map Complex.im *ᵥ q.2 with hg_def
  have hg : Continuous g := by
    simp only [hg_def, dotProduct, mulVec, Matrix.map_apply, Matrix.of_apply]
    fun_prop
  have hS : IsCompact (K ×ˢ Metric.sphere (0 : ι → ℝ) 1) := hK.prod (isCompact_sphere 0 1)
  rcases (K ×ˢ Metric.sphere (0 : ι → ℝ) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      have hmem : (p, ‖x‖⁻¹ • x) ∈ K ×ˢ Metric.sphere (0 : ι → ℝ) 1 :=
        ⟨hp, by simp [norm_smul, hx]⟩
      rw [he] at hmem
      exact hmem
  · obtain ⟨q, hq, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
    have hq0 : q.2 ≠ 0 := by
      intro h
      have := hq.2
      simp [h] at this
    have hm : 0 < g q := im_quadForm_pos_of_mem_thetaDomain (hKd q.1 hq.1) q.2 hq0
    refine ⟨g q / (Fintype.card ι + 1), by positivity, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 : g q ≤ g (p, ‖x‖⁻¹ • x) := hmin ⟨hp, by simp [norm_smul, ht.ne']⟩
    have h2 : g (p, ‖x‖⁻¹ • x) =
        ‖x‖⁻¹ ^ 2 * (x ⬝ᵥ (Matrix.of p.2).map Complex.im *ᵥ x) := by
      simp only [hg_def, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    have h3 : x ⬝ᵥ x ≤ Fintype.card ι * ‖x‖ ^ 2 := by
      simp only [dotProduct]
      calc ∑ i, x i * x i ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
            have := norm_le_pi_norm x i
            rw [Real.norm_eq_abs] at this
            nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
        _ = _ := by simp
    set Q := x ⬝ᵥ (Matrix.of p.2).map Complex.im *ᵥ x
    have h4 : g q * ‖x‖ ^ 2 ≤ Q := by
      rw [h2] at h1
      calc g q * ‖x‖ ^ 2 ≤ ‖x‖⁻¹ ^ 2 * Q * ‖x‖ ^ 2 := by gcongr
        _ = Q := by field_simp
    have hxx : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    calc g q / (Fintype.card ι + 1) * (x ⬝ᵥ x)
        ≤ g q / (Fintype.card ι + 1) * (Fintype.card ι * ‖x‖ ^ 2) := by gcongr
      _ ≤ g q * ‖x‖ ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hm.le (sq_nonneg ‖x‖)]
      _ ≤ Q := h4


open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
theorem _root_.GlobalTheory.thetaMTest_holds : _root_.ReciprocityTheory.PTheta.ThetaMTestStatement := by
  unfold _root_.ReciprocityTheory.PTheta.ThetaMTestStatement
  intro ι _ a K hK hKd
  obtain ⟨c, hc, hcK⟩ := exists_uniform_im_quadForm_lower_bound_on_compact hK hKd
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn (f := fun p => p.1) continuous_fst.continuousOn
  refine ⟨_root_.GlobalTheory.riemannThetaBound a c S, _root_.GlobalTheory.summable_riemannThetaBound a hc S,
    fun b p hp l => ?_⟩
  exact _root_.GlobalTheory.norm_riemannThetaTerm_le a b (hcK p hp)
    (fun i => (_root_.GlobalTheory.abs_im_apply_le_norm p.1 i).trans (hS p hp)) l


open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
theorem _root_.GlobalTheory.thetaSummable_holds : _root_.ReciprocityTheory.PTheta.ThetaSummableStatement := by
  have hM := _root_.GlobalTheory.thetaMTest_holds
  unfold _root_.ReciprocityTheory.PTheta.ThetaMTestStatement at hM
  unfold _root_.ReciprocityTheory.PTheta.ThetaSummableStatement
  intro ι _ a b z τ hτ
  obtain ⟨u, hu, hbound⟩ := hM ι a {(z, (τ : ι → ι → ℂ))} isCompact_singleton
    (fun p hp => by
      obtain rfl : p = (z, (τ : ι → ι → ℂ)) := hp
      exact hτ)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun l => hbound b _ (Set.mem_singleton _) l) hu


open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
theorem _root_.GlobalTheory.thetaMTest_and_thetaSummable : _root_.ReciprocityTheory.PTheta.ThetaMTestStatement ∧ _root_.ReciprocityTheory.PTheta.ThetaSummableStatement :=
  ⟨_root_.GlobalTheory.thetaMTest_holds, _root_.GlobalTheory.thetaSummable_holds⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemThetaDomainIffIsSiegelAddTranspose
section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta

namespace GlobalTheory

variable {ι : Type*} [Fintype ι]

theorem siegelH_subset_thetaDomain : SiegelH ι ⊆ ThetaDomain ι := by
  intro τ hτ
  obtain ⟨hs, hp⟩ := hτ
  have ht : (τ.map Complex.im)ᵀ = τ.map Complex.im := by
    rw [← Matrix.transpose_map, hs.eq]
  show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
  rw [ht]
  exact hp.add hp

theorem isOpen_thetaDomain : IsOpen (ThetaDomain ι) := by
  set S : Matrix ι ι ℂ → Matrix ι ι ℝ :=
    fun τ => τ.map Complex.im + (τ.map Complex.im)ᵀ with hS
  have hherm : ∀ τ, (S τ).IsHermitian := by
    intro τ
    ext i j
    simp [hS, add_comm]
  have hscale : ∀ τ (c : ℝ) (x : ι → ℝ),
      (c • x) ⬝ᵥ (S τ *ᵥ (c • x)) = c * c * (x ⬝ᵥ (S τ *ᵥ x)) := by
    intro τ c x
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have key : ∀ τ, τ ∈ ThetaDomain ι ↔
      ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x) := by
    intro τ
    change (S τ).PosDef ↔ _
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    simp only [star_trivial]
    constructor
    · rintro ⟨-, h⟩ x hx
      apply h
      rintro rfl
      simp at hx
    · intro h
      refine ⟨hherm τ, fun x hx => ?_⟩
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hn.ne']
      have h1 := h _ hy
      rw [hscale] at h1
      by_contra hle
      have : ‖x‖⁻¹ * ‖x‖⁻¹ * (x ⬝ᵥ (S τ *ᵥ x)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hle)
      linarith
  have hcont : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.2 ⬝ᵥ (S p.1 *ᵥ p.2) := by
    have hm : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.1.map Complex.im :=
      continuous_fst.matrix_map Complex.continuous_im
    exact continuous_snd.dotProduct ((hm.add hm.matrix_transpose).matrix_mulVec continuous_snd)
  rw [isOpen_iff_eventually]
  intro τ₀ h₀
  have hev : ∀ᶠ τ in 𝓝 τ₀, ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x) := by
    refine (isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually
      (P := fun τ x => 0 < x ⬝ᵥ (S τ *ᵥ x)) fun x hx => ?_
    exact (hcont.continuousAt (x := (τ₀, x))).eventually (lt_mem_nhds ((key τ₀).1 h₀ x hx))
  filter_upwards [hev] with τ hτ
  exact (key τ).2 hτ

theorem siegelSubDomain_and_domainOpen : SiegelSubDomainStatement ∧ DomainOpenStatement := by
  refine ⟨fun κ _ => siegelH_subset_thetaDomain, fun κ _ => ?_⟩
  exact isOpen_thetaDomain

end GlobalTheory
end

