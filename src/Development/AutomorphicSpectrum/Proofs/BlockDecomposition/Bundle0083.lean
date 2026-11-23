module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChamberPairThreeFour
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0054
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripEntireOfFac
section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

section Slice

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma Fac_const (c : X) (Ω : Set (ℝ × ℝ)) : Fac (fun _ => c) Ω :=
  ⟨fun _ _ => differentiableOn_const c, continuousOn_const, fun _ _ _ => ⟨‖c‖, fun _ _ => le_rfl⟩⟩

lemma Fac_exp (Ω : Set (ℝ × ℝ)) : Fac (fun l : ℂ × ℂ => Complex.exp (l.1 ^ 2 + l.2 ^ 2)) Ω := by
  refine ⟨lineHol_exp _, by fun_prop, fun C _ hCc => ?_⟩
  have hc : Continuous fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2 := by fun_prop
  obtain ⟨M, hM⟩ := (hCc.image hc).bddAbove
  refine ⟨Real.exp M, fun l hl => ?_⟩
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 (le_trans ?_ (hM ⟨_, hl, rfl⟩))
  simp only [pow_two, Complex.add_re, Complex.mul_re]
  nlinarith [mul_self_nonneg l.1.im, mul_self_nonneg l.2.im]

lemma line_zero (τ : ℂ) : (0 : ℂ × ℂ) + τ • ((0 : ℂ), (1 : ℂ)) = (0, τ) := by
  ext <;> simp

lemma slice_mem_tube {C : Set ℝ} {y : ℂ} (h : y.re ∈ C) :
    ((0 : ℂ), y) ∈ tube (({0} : Set ℝ) ×ˢ C) := by
  simpa [tube] using h

lemma leftGood_of_fac {f : ℂ → X} {A : ℂ × ℂ → X} {a : ℝ} (hA : Fac A {x | x.2 < a})
    (h : ∀ y, f y = A (0, y)) : LeftGood f a := by
  refine ⟨?_, fun b c hc => ?_⟩
  · have h₁ := hA.hol 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube {x : ℝ × ℝ | x.2 < a}} = {z | z.re < a} := by
      ext z; simp [tube]
    rw [hs] at h₁
    have e : f = fun τ => A (0, τ) := funext h
    rw [e]
    exact h₁
  · obtain ⟨M, hM⟩ := hA.bdd (({0} : Set ℝ) ×ˢ Set.Icc b c)
      (by rintro x ⟨-, hx⟩; exact lt_of_le_of_lt hx.2 hc)
      (isCompact_singleton.prod isCompact_Icc)
    exact ⟨M, fun z h₁ h₂ => by rw [h]; exact hM _ (slice_mem_tube ⟨h₁, h₂⟩)⟩

lemma stripEntire_of_fac {f : ℂ → X} {A : ℂ × ℂ → X} (hA : Fac A Set.univ)
    (h : ∀ y, f y = A (0, y)) : StripEntire f := by
  refine ⟨?_, fun b c => ?_⟩
  · have h₁ := hA.hol 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube (Set.univ : Set (ℝ × ℝ))} = Set.univ := by
      ext z; simp [tube]
    rw [hs] at h₁
    have e : f = fun τ => A (0, τ) := funext h
    rw [e]
    exact differentiableOn_univ.1 h₁
  · obtain ⟨M, hM⟩ := hA.bdd (({0} : Set ℝ) ×ˢ Set.Icc b c) (Set.subset_univ _)
      (isCompact_singleton.prod isCompact_Icc)
    exact ⟨M, fun z h₁ h₂ => by rw [h]; exact hM _ (slice_mem_tube ⟨h₁, h₂⟩)⟩

lemma slice_good {T : Type} [TopologicalSpace T] {Φ : ℂ × ℂ → T → X} (hΦ : TubeGood Φ Set.univ) :
    (∀ g, Differentiable ℂ fun y : ℂ => Φ (0, y) g) ∧
    (Continuous fun y : ℂ × T => Φ (0, y.1) y.2) ∧
    ∀ (b a : ℝ) (g : T), ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g' ∈ U,
      ‖Φ (0, z) g'‖ ≤ M := by
  refine ⟨fun g => ?_, ?_, fun b a g => ?_⟩
  · have h₁ := hΦ.hol g 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube (Set.univ : Set (ℝ × ℝ))} = Set.univ := by
      ext z; simp [tube]
    rw [hs] at h₁
    exact differentiableOn_univ.1 h₁
  · have hc : Continuous fun y : ℂ × T => (((0 : ℂ), y.1), y.2) := by fun_prop
    have := hΦ.cont.comp hc.continuousOn (s := Set.univ) (fun y _ => by simp [tube])
    exact continuousOn_univ.1 this
  · obtain ⟨U, hU, M, hM⟩ := hΦ.bdd (({0} : Set ℝ) ×ˢ Set.Icc b a) (Set.subset_univ _)
      (isCompact_singleton.prod isCompact_Icc) g
    exact ⟨U, hU, M, fun z h₁ h₂ g' hg' => hM _ (slice_mem_tube ⟨h₁, h₂⟩) g' hg'⟩

end Slice

lemma exists_ne_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h₁ : ∃ z, f z ≠ 0) (h₂ : ∃ z, g z ≠ 0) : ∃ z, f z * g z ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨z₀, hz₀⟩ := h₁
  obtain ⟨z₁, hz₁⟩ := h₂
  have hev : ∀ᶠ z in 𝓝 z₀, f z ≠ 0 := hf.continuous.continuousAt.eventually_ne hz₀
  have hg0 : g =ᶠ[𝓝 z₀] 0 :=
    hev.mono fun z hz => (mul_eq_zero.1 (hcon z)).resolve_left hz
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  exact hz₁ (hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z₀) hg0 (Set.mem_univ z₁))

lemma exists_ne_aff {f : ℂ → ℂ} (h : ∃ z, f z ≠ 0) (α β γ : ℝ) (hβ : β ≠ 0) :
    ∃ y : ℂ, f (aff α β γ (0, y)) ≠ 0 := by
  obtain ⟨z, hz⟩ := h
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  refine ⟨(z - γ) / β, ?_⟩
  have e : aff α β γ (0, (z - γ) / (β : ℂ)) = z := by
    simp only [aff]
    field_simp
    ring
  rwa [e]

lemma ex_bounds (u R : ℝ) :
    ∃ m M : ℝ, m ≤ u ∧ m ≤ -2 * R ∧ (m = u ∨ m = -2 * R) ∧ u ≤ M ∧ R ≤ M ∧ (M = u ∨ M = R) :=
  ⟨min u (-2 * R), max u R, min_le_left _ _, min_le_right _ _, min_choice _ _, le_max_left _ _,
    le_max_right _ _, max_choice _ _⟩

section Conds

variable {G : Type} [Group G]

lemma conv_congr {Γ P : Subgroup G} {f f' : G → ℝ} (h : Conv Γ P f') (e : ∀ g, f g = f' g) :
    Conv Γ P f := by
  have : f = f' := funext e
  rwa [this]

variable {Γ A B : Subgroup G} {a b h : G → ℝ} {N R Rw : ℝ}

lemma cond_first (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneI (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ A (fun g => p * a g + t * h g) ∧
        Conv Γ B fun g => (h g + N * b g) - q * b g + t * h g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · exact conv_congr (hA (M + 1) t (by linarith) (by linarith [ht'.1])) fun g => rfl
  · refine conv_congr (hB (N - (m - 1)) (1 + t - N + (m - 1)) (by linarith [hN'.1]) ?_)
      fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1, hN'.2]

lemma cond_c (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneC (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ B (fun g => p * (-b g) + t * (h g + b g)) ∧
        Conv Γ B fun g => (-b g) - q * (-b g) + t * (h g + b g) := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hB (t - (M + 1)) (M + 1) ?_ (by linarith)) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · refine conv_congr (hB (t - 1 + (m - 1)) (1 - (m - 1)) ?_ (by linarith)) fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1]

lemma cond_a (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneA (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ B (fun g => p * b g + t * h g) ∧
        Conv Γ A fun g => (N * a g - h g) - q * a g + t * h g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hB (M + 1) (t - (M + 1)) (by linarith) ?_) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · exact conv_congr (hA (N - (m - 1)) (t - 1) (by linarith [hN'.1]) (by linarith [ht'.1]))
      fun g => by ring

lemma cond_b (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g) :
    ∀ x ∈ coneC (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ A (fun g => p * (h g - a g) + t * a g) ∧
        Conv Γ A fun g => ((N - 1) * (h g - a g)) - q * (h g - a g) + t * a g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hA (t - (M + 1)) (M + 1) ?_ (by linarith)) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · refine conv_congr (hA (t - N + 1 + (m - 1)) (N - 1 - (m - 1)) ?_ (by linarith [hN'.1]))
      fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1, hN'.2]

end Conds

section Series

variable {G : Type} [Group G]

lemma tsum_cos_inf {X : Type} [AddCommMonoid X] [TopologicalSpace X] (Γ S : Subgroup G)
    (f : G → X) : ∑' r : Cos (Γ ⊓ S) Γ, f (rep r) = ∑' q : Cos S Γ, f (rep q) := by
  have e : (Γ ⊓ S).subgroupOf Γ = S.subgroupOf Γ := Subgroup.inf_subgroupOf_left S Γ
  have key : ∀ U V : Subgroup Γ, U = V →
      ∑' r : Quotient (QuotientGroup.rightRel U), f (Quotient.out r).1 =
        ∑' q : Quotient (QuotientGroup.rightRel V), f (Quotient.out q).1 := by
    rintro U _ rfl
    rfl
  exact key _ _ e

variable {L W : Type} [NormedAddCommGroup L] [NormedSpace ℂ L] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]

lemma outer_apply {Γ Δ : Subgroup G} (ξ : G → ℝ) (H : ℂ → G → L →L[ℂ] W) (l : ℂ × ℂ) (g : G)
    (hs : Summable fun r : Cos Δ Γ => ‖Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)‖)
    (w : L) : outer Γ Δ ξ H l g w =
      ∑' r : Cos Δ Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w :=
  (ContinuousLinearMap.apply ℂ W w).map_tsum hs.of_norm

end Series

section Eis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]

lemma eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (s : ℂ)
    (w : W) : eis Γ K P c ρ Λ g (s • w) = s • eis Γ K P c ρ Λ g w := by
  simp only [eis, map_smul]
  rw [← tsum_const_smul'' s]
  congr 1
  ext q
  rw [smul_comm]

end Eis

end GlobalTheory.CompanionTheory.RgEisGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformVerticalInvariance
section
noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem continuous_mk_im_shiftSnd (x : ℝ) : Continuous fun y : ℝ => (⟨x, y⟩ : ℂ) := by
  have h : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
    ext y
    apply Complex.ext <;> simp
  rw [h]
  fun_prop

theorem continuous_pt_shiftSnd (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by
  unfold pt
  exact ((continuous_mk_im_shiftSnd x.1).comp continuous_fst).prodMk ((continuous_mk_im_shiftSnd x.2).comp continuous_snd)

theorem integrable_gauss_prod_shiftSnd (K : ℝ) :
    Integrable fun y : ℝ × ℝ => K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) := by
  have h1 : Integrable fun x : ℝ => Real.exp (-1 * x ^ 2) := integrable_exp_neg_mul_sq one_pos
  have h2 := (h1.mul_prod h1).const_mul K
  rw [Measure.volume_eq_prod]
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Real.exp_add]
  congr 2
  ring

theorem phi_shift_snd (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ))
    (G : ℂ × ℂ → X) (hG : GaussTube G Ω) (a b c : ℝ) (hab : a ≤ b) (hs : ∀ s ∈ Set.Icc a b, (c, s) ∈ Ω)
    (t : ℝ × ℝ) : phi G (c, a) t = phi G (c, b) t := by
  set C : Set (ℝ × ℝ) := (fun s : ℝ => (c, s)) '' Set.Icc a b with hC
  have hCc : IsCompact C := isCompact_Icc.image (by fun_prop)
  have hCΩ : C ⊆ Ω := by
    rintro _ ⟨s, hs', rfl⟩
    exact hs s hs'
  obtain ⟨M, hM⟩ := hG.decay C hCΩ hCc
  obtain ⟨B, hB⟩ := (hCc.image (f := fun x : ℝ × ℝ => Real.exp (-(x.1 * t.1 + x.2 * t.2)))
    (by fun_prop)).bddAbove
  let H : ℂ × ℂ → X := fun l => Complex.exp (-dot l t) • G l
  have hexp : Continuous fun l : ℂ × ℂ => Complex.exp (-dot l t) := by
    unfold dot
    fun_prop
  have hbound : ∀ l ∈ tube C, ‖H l‖ ≤ (|B| * |M|) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
    intro l hl
    have h1 : ‖Complex.exp (-dot l t)‖ ≤ |B| := by
      rw [Complex.norm_exp]
      have h : (-dot l t).re = -(l.1.re * t.1 + l.2.re * t.2) := by simp [dot]
      rw [h]
      exact (hB ⟨(l.1.re, l.2.re), hl, rfl⟩).trans (le_abs_self B)
    have h2 : ‖G l‖ ≤ |M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) :=
      (hM l hl).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)
    calc ‖H l‖ = ‖Complex.exp (-dot l t)‖ * ‖G l‖ := norm_smul _ _
      _ ≤ |B| * (|M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))) := by gcongr
      _ = _ := by ring
  have hcont : ContinuousOn H (tube Ω) := hexp.continuousOn.smul hG.cont
  have hmem : ∀ s ∈ Set.Icc a b, ∀ y : ℝ × ℝ, pt (c, s) y ∈ tube C := fun s hs' y => ⟨s, hs', rfl⟩
  have hint : ∀ s ∈ Set.Icc a b, Integrable fun y : ℝ × ℝ => H (pt (c, s) y) := by
    intro s hs'
    have hc : Continuous fun y : ℝ × ℝ => H (pt (c, s) y) :=
      hcont.comp_continuous (continuous_pt_shiftSnd _) fun y => hs s hs'
    refine (integrable_gauss_prod_shiftSnd (|B| * |M|)).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    exact hbound _ (hmem s hs' y)
  have hphi : ∀ s ∈ Set.Icc a b, phi G (c, s) t = ∫ y₁ : ℝ, ∫ y₂ : ℝ, H (⟨c, y₁⟩, ⟨s, y₂⟩) := by
    intro s hs'
    have h := hint s hs'
    rw [Measure.volume_eq_prod] at h
    have h' := integral_prod _ h
    rw [← Measure.volume_eq_prod] at h'
    exact h'
  rw [hphi a (Set.left_mem_Icc.2 hab), hphi b (Set.right_mem_Icc.2 hab)]
  refine integral_congr_ae (Eventually.of_forall fun y₁ => ?_)
  simp only
  refine _root_.GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line X (fun z => H (⟨c, y₁⟩, z)) a b (|B| * |M|) hab ?_ ?_
  · let p : ℂ × ℂ := (⟨c, y₁⟩, 0)
    let v : ℂ × ℂ := (0, 1)
    have e : ∀ τ : ℂ, p + τ • v = (⟨c, y₁⟩, τ) := by
      intro τ
      simp [p, v]
    have h1 : DifferentiableOn ℂ (fun τ : ℂ => G (⟨c, y₁⟩, τ)) {z : ℂ | z.re ∈ Set.Icc a b} := by
      have h := hG.hol p v
      simp only [e] at h
      exact h.mono fun z hz => hs _ hz
    have h2 : Differentiable ℂ fun τ : ℂ => Complex.exp (-dot ((⟨c, y₁⟩, τ) : ℂ × ℂ) t) := by
      unfold dot
      fun_prop
    exact h2.differentiableOn.smul h1
  · intro z hz
    have h := hbound (⟨c, y₁⟩, z) ⟨z.re, hz, rfl⟩
    refine h.trans ?_
    have hK : 0 ≤ |B| * |M| := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
    have : 0 ≤ y₁ ^ 2 := sq_nonneg _
    simp only
    linarith

end GlobalTheory.CompanionTheory.TubeFourier
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHaarRightInvariant
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.HaarUnimod

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

theorem modularCharacterFun_eq_one (hG : IsUnimod G) (g : G) : modularCharacterFun g = 1 :=
  hG g

theorem isMulRightInvariant_of_isUnimod :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G →
      ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro G _ _ _ _ _ _ _ hG μ _
  refine ⟨fun g => ?_⟩
  rw [isMulLeftInvariant_eq_smul (map (· * g) μ) μ,
    ← modularCharacterFun_eq_haarScalarFactor, modularCharacterFun_eq_one hG g, one_smul]

end GlobalTheory.CompanionTheory.HaarUnimod
end

