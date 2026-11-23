module

public import Mathlib
public import GroundTheory.GlobalFields.ComplexMultiplication.JInvariant
public import GroundTheory.GlobalFields.ComplexMultiplication.UniformizationEisenstein

@[expose] public section

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.JInvariantHomothety
section
open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem G_eq_of_lattice_eq_smul {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice) (n : ℕ) :
    L'.G n = (c ^ n)⁻¹ * L.G n := by
  have hmem : ∀ l ∈ L.lattice, c * l ∈ L'.lattice := fun l hl ↦ by
    have : c * l ∈ (L'.lattice : Set ℂ) := by rw [h]; exact ⟨l, hl, rfl⟩
    exact this
  have hmem' : ∀ l ∈ L'.lattice, c⁻¹ * l ∈ L.lattice := fun l hl ↦ by
    have : l ∈ (c * ·) '' (L.lattice : Set ℂ) := by rw [← h]; exact hl
    obtain ⟨m, hm, rfl⟩ := this
    rwa [inv_mul_cancel_left₀ hc]
  let e : L.lattice ≃ L'.lattice :=
    { toFun := fun l ↦ ⟨c * l, hmem _ l.2⟩
      invFun := fun l ↦ ⟨c⁻¹ * l, hmem' _ l.2⟩
      left_inv := fun l ↦ by ext; simp [hc]
      right_inv := fun l ↦ by ext; simp [hc] }
  rw [PeriodPair.G, PeriodPair.G, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  show ((c * (l : ℂ)) ^ n)⁻¹ = (c ^ n)⁻¹ * ((l : ℂ) ^ n)⁻¹
  rw [mul_pow, mul_inv]

lemma discr_of_g₂_g₃ {L L' : PeriodPair} {t : ℂ} (h₂ : L'.g₂ = t ^ 4 * L.g₂)
    (h₃ : L'.g₃ = t ^ 6 * L.g₃) : discr L' = t ^ 12 * discr L := by
  rw [discr, discr, h₂, h₃]
  ring

lemma weierstrassCurve_j_eq_of_g₂_g₃ {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (h₂ : L'.g₂ = t ^ 4 * L.g₂) (h₃ : L'.g₃ = t ^ 6 * L.g₃) :
    (weierstrassCurve L).j = (weierstrassCurve L').j := by
  rw [weierstrassCurve_j, weierstrassCurve_j, discr_of_g₂_g₃ h₂ h₃, h₂,
    show 1728 * (t ^ 4 * L.g₂) ^ 3 = t ^ 12 * (1728 * L.g₂ ^ 3) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ ht)]

lemma exists_pos_le_norm (L : PeriodPair) : ∃ ε > 0, ∀ l ∈ L.lattice, l ≠ 0 → ε ≤ ‖l‖ := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  refine ⟨ε, hε, fun l hl h0 ↦ ?_⟩
  by_contra hlt
  have := h (mem_ball_zero_iff.2 (not_le.1 hlt))
  exact this ⟨hl, h0⟩

lemma weierstrassLaurentCoeff_eq_of_G_eq {L L' : PeriodPair} {t : ℂ}
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) (j : ℕ) :
    weierstrassLaurentCoeff (L := L') j = t ^ (j + 2) * weierstrassLaurentCoeff (L := L) j := by
  rcases Nat.even_or_odd' j with ⟨n, rfl | rfl⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [weierstrassLaurentCoeff]
    simp only [weierstrassLaurentCoeff, ite_eq_right (show 2 * n ≠ 0 by omega)]
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, hG (n + 1) (by omega)]
    ring
  · have hodd : Odd (2 * n + 1 + 2) := ⟨n + 1, by ring⟩
    simp [weierstrassLaurentCoeff, L'.G_eq_zero_of_odd _ hodd, L.G_eq_zero_of_odd _ hodd]

theorem weierstrassP_eq_of_G_eq {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) {z : ℂ} (hz0 : z ≠ 0)
    (hz' : ∀ l : L'.lattice, (l : ℂ) ≠ 0 → ‖z‖ < ‖(l : ℂ)‖)
    (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → ‖t * z‖ < ‖(l : ℂ)‖) :
    ℘[L'] z = t ^ 2 * ℘[L] (t * z) := by
  have hasSum_laurent (P : PeriodPair) (w : ℂ)
      (hw : ∀ l : P.lattice, (l : ℂ) ≠ 0 → ‖w‖ < ‖(l : ℂ)‖) :
      HasSum (fun j ↦ weierstrassLaurentCoeff (L := P) j * w ^ j) (℘[P] w - 1 / w ^ 2) := by
    have h := P.weierstrassPExceptSeries_hasSum 0 w 0 (fun l hl ↦ by simpa using hw l hl)
    rw [weierstrassP_eq_except_zero w, add_sub_cancel_right]
    convert h using 2 with j
    rw [sub_zero, PeriodPair.weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars,
      weierstrassLaurentCoeff]
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [hj, P.lattice.zero_mem, P.sumInvPow_zero]
  have h1 := hasSum_laurent L' z hz'
  have h2 := (hasSum_laurent L (t * z) hz).mul_left (t ^ 2)
  have h3 : HasSum (fun j ↦ weierstrassLaurentCoeff (L := L') j * z ^ j)
      (t ^ 2 * (℘[L] (t * z) - 1 / (t * z) ^ 2)) := by
    have hfun : (fun j ↦ weierstrassLaurentCoeff (L := L') j * z ^ j) =
        fun j ↦ t ^ 2 * (weierstrassLaurentCoeff (L := L) j * (t * z) ^ j) := by
      funext j
      rw [weierstrassLaurentCoeff_eq_of_G_eq hG, mul_pow]
      ring
    rw [hfun]
    exact h2
  have e := h1.unique h3
  have e' : t ^ 2 * (1 / (t * z) ^ 2) = 1 / z ^ 2 := by
    field_simp
  linear_combination e - e'

theorem mul_mem_lattice_of_G_eq {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) {z : ℂ}
    (hz : z ∈ L'.lattice) : t * z ∈ L.lattice := by
  obtain ⟨ε', hε', hL'⟩ := exists_pos_le_norm L'
  obtain ⟨ε, hε, hL⟩ := exists_pos_le_norm L
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  set ρ := min ε' (ε / ‖t‖) with hρ
  have hρ0 : 0 < ρ := lt_min hε' (div_pos hε htn)

  set S : Set ℂ := (L'.lattice : Set ℂ) ∪ (fun w ↦ t * w) ⁻¹' L.lattice with hS
  have hcount : ∀ L₀ : PeriodPair, (L₀.lattice : Set ℂ).Countable := fun L₀ ↦ by
    have : Countable L₀.lattice := L₀.latticeEquivProd.injective.countable
    exact Set.countable_coe_iff.1 this
  have hScount : S.Countable :=
    (hcount L').union ((hcount L).preimage (mul_right_injective₀ ht))
  have hSclosed : IsClosed S :=
    L'.isClosed_lattice.union (L.isClosed_lattice.preimage (continuous_const.mul continuous_id))
  have hU : IsPreconnected Sᶜ := by
    have h2 : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
    exact (hScount.isPathConnected_compl_of_one_lt_rank h2).isConnected.isPreconnected
  have hf : AnalyticOnNhd ℂ ℘[L'] Sᶜ := fun w hw ↦
    L'.analyticOnNhd_weierstrassP w fun h ↦ hw (Or.inl h)
  have hgat : ∀ w, t * w ∉ L.lattice → AnalyticAt ℂ (fun w ↦ t ^ 2 * ℘[L] (t * w)) w := fun w hw ↦
    analyticAt_const.mul ((L.analyticOnNhd_weierstrassP (t * w) hw).comp (by fun_prop))
  have hg : AnalyticOnNhd ℂ (fun w ↦ t ^ 2 * ℘[L] (t * w)) Sᶜ := fun w hw ↦
    hgat w fun h ↦ hw (Or.inr h)

  have hsmall : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → w ∈ Sᶜ ∧ ℘[L'] w = t ^ 2 * ℘[L] (t * w) := by
    intro w hw0 hw
    have hw1 : ‖w‖ < ε' := hw.trans_le (min_le_left _ _)
    have hw2 : ‖t * w‖ < ε := by
      have : ‖w‖ < ε / ‖t‖ := hw.trans_le (min_le_right _ _)
      rw [norm_mul]
      rw [lt_div_iff₀ htn] at this
      linarith
    refine ⟨?_, weierstrassP_eq_of_G_eq ht hG hw0 (fun l hl ↦ hw1.trans_le (hL' _ l.2 hl))
      (fun l hl ↦ hw2.trans_le (hL _ l.2 hl))⟩
    rintro (h | h)
    · exact absurd (hL' w h hw0) (not_le.2 hw1)
    · exact absurd (hL (t * w) h (mul_ne_zero ht hw0)) (not_le.2 hw2)
  set z₀ : ℂ := ((ρ / 2 : ℝ) : ℂ) with hz₀
  have hz₀n : ‖z₀‖ = ρ / 2 := by
    rw [hz₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hz₀0 : z₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz₀n
    linarith
  have hz₀ρ : ‖z₀‖ < ρ := by rw [hz₀n]; linarith
  have hopen : IsOpen {w : ℂ | w ≠ 0 ∧ ‖w‖ < ρ} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  have hev : ℘[L'] =ᶠ[𝓝 z₀] fun w ↦ t ^ 2 * ℘[L] (t * w) := by
    filter_upwards [hopen.mem_nhds ⟨hz₀0, hz₀ρ⟩] with w hw
    exact (hsmall w hw.1 hw.2).2
  have hEq : EqOn ℘[L'] (fun w ↦ t ^ 2 * ℘[L] (t * w)) Sᶜ :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg hU (hsmall z₀ hz₀0 hz₀ρ).1 hev

  by_contra hnot
  have hpunct : ℘[L'] =ᶠ[𝓝[≠] z] fun w ↦ t ^ 2 * ℘[L] (t * w) := by
    have hclosed : IsClosed ((fun w ↦ t * w) ⁻¹' (L.lattice : Set ℂ)) :=
      L.isClosed_lattice.preimage (continuous_const.mul continuous_id)
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds z),
      nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hnot)] with w hwz hw1 hw2
    refine hEq ?_
    rintro (h | h)
    · exact hw1 ⟨h, hwz⟩
    · exact hw2 h
  have hord := meromorphicOrderAt_congr hpunct
  rw [L'.order_weierstrassP z hz] at hord
  have hnn := (hgat z hnot).meromorphicOrderAt_nonneg
  rw [← hord] at hnn
  exact absurd hnn (by decide)

theorem lattice_eq_of_G_eq {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) :
    (L'.lattice : Set ℂ) = (t⁻¹ * ·) '' L.lattice := by
  have hG' : ∀ k, 2 ≤ k → L.G (2 * k) = t⁻¹ ^ (2 * k) * L'.G (2 * k) := fun k hk ↦ by
    rw [hG k hk, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ ht)]
  ext z
  constructor
  · intro hz
    exact ⟨t * z, mul_mem_lattice_of_G_eq ht hG hz, by simp [ht]⟩
  · rintro ⟨w, hw, rfl⟩
    exact mul_mem_lattice_of_G_eq (inv_ne_zero ht) hG' hw

lemma g₂_g₃_of_variableChange {L L' : PeriodPair} {C : WeierstrassCurve.VariableChange ℂ}
    (hC : C • weierstrassCurve L = weierstrassCurve L') :
    L'.g₂ = ((C.u⁻¹ : ℂˣ) : ℂ) ^ 4 * L.g₂ ∧ L'.g₃ = ((C.u⁻¹ : ℂˣ) : ℂ) ^ 6 * L.g₃ := by
  have hu : ((C.u⁻¹ : ℂˣ) : ℂ) ≠ 0 := (C.u⁻¹).ne_zero
  have h1 := congrArg WeierstrassCurve.a₁ hC
  have h2 := congrArg WeierstrassCurve.a₂ hC
  have h3 := congrArg WeierstrassCurve.a₃ hC
  have h4 := congrArg WeierstrassCurve.a₄ hC
  have h6 := congrArg WeierstrassCurve.a₆ hC
  rw [WeierstrassCurve.variableChange_a₁] at h1
  rw [WeierstrassCurve.variableChange_a₂] at h2
  rw [WeierstrassCurve.variableChange_a₃] at h3
  rw [WeierstrassCurve.variableChange_a₄] at h4
  rw [WeierstrassCurve.variableChange_a₆] at h6
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆] at h1 h2 h3 h4 h6
  have hs : C.s = 0 := by
    have := (mul_eq_zero.1 h1).resolve_left hu
    linear_combination this / 2
  have ht : C.t = 0 := by
    have := (mul_eq_zero.1 h3).resolve_left (pow_ne_zero _ hu)
    linear_combination this / 2
  have hr : C.r = 0 := by
    have := (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ hu)
    rw [hs] at this
    linear_combination this / 3
  rw [hs, ht, hr] at h4
  rw [ht, hr] at h6
  constructor
  · linear_combination 4 * h4
  · linear_combination 4 * h6

theorem weierstrassCurve_j_eq_iff {L L' : PeriodPair} :
    (weierstrassCurve L).j = (weierstrassCurve L').j ↔
      ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = (c * ·) '' L.lattice := by
  constructor
  · intro hj
    obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj
    obtain ⟨h₂, h₃⟩ := g₂_g₃_of_variableChange hC
    set t : ℂ := ((C.u⁻¹ : ℂˣ) : ℂ)
    have ht : t ≠ 0 := (C.u⁻¹).ne_zero
    have hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k) := fun k hk ↦
      G_eq_of_g₂_g₃ (L := L) h₂ h₃ hk
    exact ⟨t⁻¹, inv_ne_zero ht, lattice_eq_of_G_eq ht hG⟩
  · rintro ⟨c, hc, h⟩
    have hG := G_eq_of_lattice_eq_smul hc h
    refine weierstrassCurve_j_eq_of_g₂_g₃ (t := c⁻¹) (inv_ne_zero hc) ?_ ?_
    · rw [PeriodPair.g₂, PeriodPair.g₂, hG, inv_pow]
      ring
    · rw [PeriodPair.g₃, PeriodPair.g₃, hG, inv_pow]
      ring

theorem modularJ_eq_iff (τ τ' : UpperHalfPlane) :
    modularJ τ = modularJ τ' ↔ ∃ c : ℂ, c ≠ 0 ∧
      ((latticeOfTau τ').lattice : Set ℂ) = (c * ·) '' (latticeOfTau τ).lattice := by
  rw [← weierstrassCurve_latticeOfTau_j, ← weierstrassCurve_latticeOfTau_j, weierstrassCurve_j_eq_iff]

end Elliptic
end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.JInvariantSurjective
section
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem tendsto_E₄_atImInfty : Tendsto (fun τ : ℍ ↦ E₄ τ) atImInfty (𝓝 1) := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero (f := E₄) one_pos
    one_mem_strictPeriods_SL
  have h0 : cuspFunction 1 E₄ 0 = 1 := by
    have := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
    simpa [qExpansion_coeff] using this
  have hcomp : ∀ τ : ℍ, cuspFunction 1 E₄ (Function.Periodic.qParam 1 τ) = E₄ τ := fun τ ↦
    SlashInvariantFormClass.eq_cuspFunction E₄ τ one_mem_strictPeriods_SL one_ne_zero
  have := ha.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)
  rw [h0] at this
  exact this.congr hcomp

theorem tendsto_discriminant_atImInfty :
    Tendsto (fun τ : ℍ ↦ ModularForm.discriminant τ) atImInfty (𝓝 0) :=
  ModularForm.discriminant_isZeroAtImInfty

theorem eventually_le_norm_modularJ (R : ℝ) : ∀ᶠ τ in atImInfty, R ≤ ‖modularJ τ‖ := by
  have h1 : ∀ᶠ τ in atImInfty, (1 / 2 : ℝ) ≤ ‖E₄ τ‖ :=
    tendsto_E₄_atImInfty.norm.eventually (Ici_mem_nhds (by norm_num))
  have hc : (0 : ℝ) < 1 / (8 * (|R| + 1)) := by positivity
  have h2 : ∀ᶠ τ in atImInfty, ‖ModularForm.discriminant τ‖ < 1 / (8 * (|R| + 1)) :=
    tendsto_discriminant_atImInfty.norm.eventually (Iio_mem_nhds (by simpa using hc))
  filter_upwards [h1, h2] with τ h1 h2
  have hpos : 0 < ‖ModularForm.discriminant τ‖ :=
    norm_pos_iff.2 (ModularForm.discriminant_ne_zero τ)
  rw [modularJ, norm_div, norm_pow, le_div_iff₀ hpos]
  have hR : R ≤ |R| + 1 := by linarith [le_abs_self R]
  have h3 : (|R| + 1) * ‖ModularForm.discriminant τ‖ ≤ 1 / 8 := by
    rw [lt_div_iff₀ (by positivity)] at h2
    linarith
  have h4 : (1 / 2 : ℝ) ^ 3 ≤ ‖E₄ τ‖ ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  nlinarith

theorem exists_le_norm_modularJ (R : ℝ) : ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → R ≤ ‖modularJ τ‖ :=
  (atImInfty_mem _).1 (eventually_le_norm_modularJ R)

def modularJC (z : ℂ) : ℂ := modularJ (ofComplex z)

lemma modularJC_coe (τ : ℍ) : modularJC τ = modularJ τ := by
  rw [modularJC, ofComplex_apply]

lemma differentiableOn_modularJC : DifferentiableOn ℂ modularJC {z : ℂ | 0 < z.im} := by
  have h4 : DifferentiableOn ℂ ((fun τ : ℍ ↦ E₄ τ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo E₄)
  have hΔ : DifferentiableOn ℂ ((fun τ : ℍ ↦ ModularForm.discriminant τ) ∘ ofComplex)
      {z : ℂ | 0 < z.im} := by
    have := UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo CuspForm.discriminant)
    simpa [CuspForm.coe_discriminant] using this
  refine (h4.pow 3).div hΔ fun z _ ↦ ModularForm.discriminant_ne_zero _

lemma analyticOnNhd_modularJC : AnalyticOnNhd ℂ modularJC {z : ℂ | 0 < z.im} :=
  differentiableOn_modularJC.analyticOnNhd isOpen_upperHalfPlaneSet

lemma range_modularJ : range modularJ = modularJC '' {z : ℂ | 0 < z.im} := by
  ext w
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ, τ.im_pos, modularJC_coe τ⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ofComplex z, rfl⟩

lemma not_exists_modularJC_const : ¬ ∃ w, ∀ z ∈ {z : ℂ | 0 < z.im}, modularJC z = w := by
  rintro ⟨w, hw⟩
  obtain ⟨A, hA⟩ := exists_le_norm_modularJ (‖w‖ + 1)
  let τ : ℍ := ⟨(|A| + 1) * Complex.I, by simp; positivity⟩
  have hτ : A ≤ τ.im := by
    show A ≤ ((|A| + 1) * Complex.I).im
    simp
    linarith [le_abs_self A]
  have h1 := hA τ hτ
  rw [← modularJC_coe, hw _ τ.im_pos] at h1
  linarith

def fdBelow (A : ℝ) : Set ℂ :=
  {z | 1 ≤ normSq z ∧ |z.re| ≤ 1 / 2 ∧ 0 ≤ z.im ∧ z.im ≤ A}

lemma im_pos_of_mem_fdBelow {A : ℝ} {z : ℂ} (hz : z ∈ fdBelow A) : 0 < z.im := by
  obtain ⟨h1, h2, h3, -⟩ := hz
  rw [normSq_apply] at h1
  have hre : z.re * z.re ≤ 1 / 4 := by
    have := abs_le.1 h2
    nlinarith
  rcases h3.lt_or_eq with h | h
  · exact h
  · rw [← h] at h1
    nlinarith

lemma isCompact_fdBelow (A : ℝ) : IsCompact (fdBelow A) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_normSq).inter
      ((isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / 2 + |A|)).subset fun z hz ↦ ?_
    obtain ⟨-, h2, h3, h4⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
      _ ≤ 1 / 2 + |A| :=
        add_le_add h2 (by rw [abs_of_nonneg h3]; exact h4.trans (le_abs_self A))

lemma isOpen_range_modularJ : IsOpen (range modularJ) := by
  rw [range_modularJ]
  rcases analyticOnNhd_modularJC.is_constant_or_isOpen
      (convex_halfSpace_im_gt 0).isPreconnected with h | h
  · exact absurd h not_exists_modularJC_const
  · exact h _ subset_rfl isOpen_upperHalfPlaneSet

lemma isClosed_range_modularJ : IsClosed (range modularJ) := by
  refine closure_subset_iff_isClosed.1 fun w hw ↦ ?_
  obtain ⟨A, hA⟩ := exists_le_norm_modularJ (‖w‖ + 1)
  have hK : IsCompact (modularJC '' fdBelow A) :=
    (isCompact_fdBelow A).image_of_continuousOn
      (differentiableOn_modularJC.continuousOn.mono fun z hz ↦ im_pos_of_mem_fdBelow hz)
  have hsub : range modularJ ⊆ modularJC '' fdBelow A ∪ {y | ‖w‖ + 1 ≤ ‖y‖} := by
    rintro _ ⟨τ, rfl⟩
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    rw [← modularJ_smul g τ]
    by_cases him : A ≤ (g • τ).im
    · exact Or.inr (hA _ him)
    · refine Or.inl ⟨(g • τ : ℍ), ⟨hg.1, hg.2, (g • τ).im_pos.le, ?_⟩, modularJC_coe _⟩
      exact (not_le.1 him).le
  have hclosed : IsClosed (modularJC '' fdBelow A ∪ {y : ℂ | ‖w‖ + 1 ≤ ‖y‖}) :=
    hK.isClosed.union (isClosed_le continuous_const continuous_norm)
  rcases closure_minimal hsub hclosed hw with h | h
  · obtain ⟨z, hz, rfl⟩ := h
    exact ⟨ofComplex z, rfl⟩
  · have h' : ‖w‖ + 1 ≤ ‖w‖ := h
    linarith

theorem modularJ_surjective : Function.Surjective modularJ := by
  have h : range modularJ = univ :=
    IsClopen.eq_univ ⟨isClosed_range_modularJ, isOpen_range_modularJ⟩ (range_nonempty _)
  exact Set.range_eq_univ.1 h

theorem exists_variableChange_eq_weierstrassCurve_latticeOfTau (W : WeierstrassCurve ℂ)
    [W.IsElliptic] :
    ∃ τ : ℍ, ∃ C : WeierstrassCurve.VariableChange ℂ, C • W = weierstrassCurve (latticeOfTau τ) := by
  obtain ⟨τ, hτ⟩ := modularJ_surjective W.j
  refine ⟨τ, W.exists_variableChange_of_j_eq _ ?_⟩
  rw [weierstrassCurve_latticeOfTau_j, hτ]

theorem exists_variableChange_eq_weierstrassCurve (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ L : PeriodPair, ∃ C : WeierstrassCurve.VariableChange ℂ, C • W = weierstrassCurve L := by
  obtain ⟨τ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve_latticeOfTau W
  exact ⟨latticeOfTau τ, C, hC⟩

end Elliptic
end GroundTheory.Global
end
end

