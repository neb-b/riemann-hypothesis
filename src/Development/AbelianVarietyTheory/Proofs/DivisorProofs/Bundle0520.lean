module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHolomorphicMorseInequalityUniform
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory

theorem integral_ball_translate {n : ℕ} (z : V n) (δ : ℝ) (F : V n → ℝ) :
    ∫ w in ball (0 : V n) δ, F (z + w) = ∫ w in ball z δ, F w := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  have key : (fun w => (ball (0 : V n) δ).indicator (fun w => F (z + w)) w) =
      fun w => (ball z δ).indicator F (z + w) := by
    funext w
    have hiff : w ∈ ball (0 : V n) δ ↔ z + w ∈ ball z δ := by
      simp [mem_ball, dist_eq_norm]
    by_cases hw : w ∈ ball (0 : V n) δ
    · simp [Set.indicator, hw, hiff.1 hw]
    · simp [Set.indicator, hw, (not_congr hiff).1 hw]
  rw [key]
  exact integral_add_left_eq_self (fun w => (ball z δ).indicator F w) z

theorem morse_local : ∀ (n : ℕ) (U K : Set (V n)) (φ g : V n → ℝ) (ε : ℝ), IsOpen U → IsCompact K →
    K ⊆ U → ContDiffOn ℝ 2 φ U →
    (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → ContinuousOn g U →
    (∀ z ∈ U, 0 < g z) → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ (∀ z ∈ K, closedBall z δ ⊆ U) ∧
    ∀ᶠ m : ℕ in atTop, ∀ z ∈ K, ∀ f : V n → ℂ, DifferentiableOn ℂ f U →
      ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z ≤
        ((cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n *
          ∫ w in ball z δ, ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w := by
  intro n U K φ g ε hU hK hKU hφ hlevi hg hgpos hε
  have hcont : ∀ j l, ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U :=
    _root_.GlobalTheory.continuousOn_cHess_of_contDiffOn_two n U φ hU hφ

  obtain ⟨C, hC⟩ : ∃ C, ∀ z ∈ K, ∀ j l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ ≤ C := by
    have hc : ContinuousOn (fun z => ∑ j, ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖) K :=
      continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun l _ =>
        ((hcont j l).mono hKU).norm
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨C, fun z hz j l => ?_⟩
    have h1 := hC z hz
    rw [Real.norm_of_nonneg (by positivity)] at h1
    refine le_trans ?_ h1
    calc ‖cHess n (fun v => (φ v : ℂ)) z j l‖
        ≤ ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ :=
          Finset.single_le_sum (f := fun l => ‖cHess n (fun v => (φ v : ℂ)) z j l‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
      _ ≤ ∑ j, ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ :=
          Finset.single_le_sum (f := fun j => ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖)
            (fun _ _ => by positivity) (Finset.mem_univ j)

  obtain ⟨D, hD0, hD⟩ : ∃ D, 0 ≤ D ∧
      ∀ z ∈ K, (cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n ≤ D := by
    have hHc : ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z) U :=
      continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j l
    have hc : ContinuousOn (fun z => (cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n) K :=
      ((Complex.continuous_re.comp (continuous_id.matrix_det)).comp_continuousOn
        (hHc.mono hKU)).div_const _
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hc
    exact ⟨max D 0, le_max_right _ _, fun z hz =>
      ((le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hD z hz)).trans (le_max_left _ _)⟩

  set τ : ℝ := ε / (2 * (D + ε)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ < 1 := by
    rw [hτ, div_lt_one (by positivity)]; linarith
  have hτd : ∀ d, 0 ≤ d → d ≤ D → d + ε / 2 ≤ (1 - τ) * (d + ε) := by
    intro d hd hdD
    have : τ * (d + ε) ≤ ε / 2 := by
      rw [hτ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith

  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hS : IsCompact (cthickening r K) := hK.cthickening
  obtain ⟨c, hc0, hcK⟩ : ∃ c, 0 < c ∧ ∀ z ∈ K, c ≤ g z := by
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · exact ⟨1, one_pos, by simp [hK0]⟩
    · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne (hg.mono hKU)
      exact ⟨g x, hgpos x (hKU hx), fun z hz => hmin hz⟩
  obtain ⟨δ₂, hδ₂, huc⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous (hg.mono hrU)) (τ * c) (by positivity)
  set δ₃ : ℝ := min r (δ₂ / 2) with hδ₃
  have hδ₃0 : 0 < δ₃ := by positivity
  have hgw : ∀ z ∈ K, ∀ w : V n, ‖w‖ ≤ δ₃ → (1 - τ) * g z ≤ g (z + w) := by
    intro z hz w hw
    have hzS : z ∈ cthickening r K := self_subset_cthickening K hz
    have hdist : dist (z + w) z = ‖w‖ := by simp [dist_eq_norm]
    have hzwS : z + w ∈ cthickening r K :=
      mem_cthickening_of_dist_le _ z r K hz (by rw [hdist]; exact hw.trans (min_le_left _ _))
    have h1 := huc (z + w) hzwS z hzS (by rw [hdist]; linarith [min_le_right r (δ₂ / 2)])
    rw [Real.dist_eq, abs_lt] at h1
    have := hcK z hz
    nlinarith

  obtain ⟨η, hη, htr⟩ := _root_.GlobalTheory.TruncGauss.trunc_gauss n C (ε / 2) (by positivity)
  obtain ⟨δ₁, hδ₁, hty⟩ := _root_.GlobalTheory.PluriTaylor.taylor_levi_unif n U K φ η hU hK hKU hφ hη
  refine ⟨min δ₁ δ₃, lt_min hδ₁ hδ₃0, fun z hz =>
    (closedBall_subset_closedBall (min_le_left _ _)).trans (hty z hz).1, ?_⟩
  set δ : ℝ := min δ₁ δ₃ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₃0
  filter_upwards [htr δ hδ0] with m hm
  intro z hz f hf
  obtain ⟨hzU, h, hh, hh0, hbd⟩ := hty z hz
  set H := cHess n (fun v => (φ v : ℂ)) z with hH
  have hpsd : H.PosSemidef :=
    GlobalTheory.T.complexHessian_posSemidef_of_leviForm_nonneg n φ z (hφ.contDiffAt (hU.mem_nhds (hKU hz))) (hlevi z (hKU hz))
  have hT := hm H hpsd (hC z hz)
  set d := H.det.re / Real.pi ^ n with hd
  have hd0 : 0 ≤ d := by
    have h1 := hpsd.det_nonneg
    have h2 : 0 ≤ H.det.re := (Complex.le_def.1 h1).1
    positivity
  have hdD : d ≤ D := hD z hz

  set Wf : V n → ℝ := fun w => Real.exp (-(m * ((∑ j, ∑ l, H j l * w j *
    (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) with hWf
  set F : V n → ℂ := fun w => f (z + w) * Complex.exp (-((m : ℂ) * h w)) with hF
  set U' : Set (V n) := (fun w => z + w) ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have hballU : ∀ w ∈ closedBall (0 : V n) δ, z + w ∈ closedBall z δ := by
    intro w hw
    simpa [mem_closedBall, dist_eq_norm] using hw
  have hball' : closedBall (0 : V n) δ ⊆ U' := fun w hw =>
    (closedBall_subset_closedBall (min_le_left _ _)).trans hzU (hballU w hw)
  have hFd : DifferentiableOn ℂ F U' := by
    have h1 : DifferentiableOn ℂ (fun w => f (z + w)) U' :=
      hf.comp ((differentiable_const z).add differentiable_id).differentiableOn
        (fun w hw => hw)
    exact h1.mul ((hh.const_mul (m : ℂ)).neg.cexp.differentiableOn)
  have hWc : Continuous Wf := by
    simp only [hWf]; fun_prop
  have hW0 : ∀ w, 0 ≤ Wf w := fun w => (Real.exp_pos _).le
  have hWinv : ∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → Wf (θ • w) = Wf w := by
    intro θ w hθ
    have hθ' : θ * (starRingEnd ℂ) θ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]; simp
    have hsum : (∑ j, ∑ l, H j l * (θ • w) j * (starRingEnd ℂ) ((θ • w) l)) =
        ∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      have e1 : (θ • w) j = θ * w j := by simp
      have e2 : (θ • w) l = θ * w l := by simp
      rw [e1, e2, map_mul]
      calc H j l * (θ * w j) * ((starRingEnd ℂ) θ * (starRingEnd ℂ) (w l))
          = H j l * w j * (starRingEnd ℂ) (w l) * (θ * (starRingEnd ℂ) θ) := by ring
        _ = _ := by rw [hθ', mul_one]
    simp only [hWf, hsum, norm_smul, hθ, one_mul]
  have hcirc := _root_.GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant n δ U' F Wf hδ0 hU'o hball' hFd hWc.continuousOn hW0 hWinv
  have hF0 : F 0 = f z := by simp [hF, hh0]
  rw [hF0] at hcirc

  have hmaps : Set.MapsTo (fun w => z + w) (closedBall (0 : V n) δ) U := fun w hw =>
    hball' hw
  have hfc : ContinuousOn (fun w => f (z + w)) (closedBall (0 : V n) δ) :=
    hf.continuousOn.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hφc : ContinuousOn (fun w => φ (z + w)) (closedBall (0 : V n) δ) :=
    hφ.continuousOn.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hgc : ContinuousOn (fun w => g (z + w)) (closedBall (0 : V n) δ) :=
    hg.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hFc : ContinuousOn F (closedBall (0 : V n) δ) := hFd.continuousOn.mono hball'
  set G : V n → ℝ := fun w => ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w with hG
  have hGc : ContinuousOn (fun w => G (z + w)) (closedBall (0 : V n) δ) := by
    simp only [hG]
    exact ((hfc.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul hφc).neg))).mul hgc
  set k : ℝ := Real.exp (-(m * φ z)) * g z * (1 - τ) with hk
  have hk0 : 0 ≤ k := by
    have := hgpos z (hKU hz)
    have : 0 < 1 - τ := by linarith
    positivity
  have hpt : ∀ w ∈ ball (0 : V n) δ, k * (‖F w‖ ^ 2 * Wf w) ≤ G (z + w) := by
    intro w hw
    have hw' : ‖w‖ < δ := by simpa using hw
    have hw1 : w ∈ closedBall (0 : V n) δ₁ := by
      simp only [mem_closedBall, dist_zero_right]; linarith [min_le_left δ₁ δ₃]
    have hb := hbd w hw1
    have hq : (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re =
        (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re := by
      simp [hH, leviV, cHess]
    have hgzw := hgw z hz w (by linarith [min_le_right δ₁ δ₃])
    have hFn : ‖F w‖ ^ 2 = ‖f (z + w)‖ ^ 2 * Real.exp (-(m * (h w).re)) ^ 2 := by
      simp [hF, norm_mul, Complex.norm_exp, mul_pow]
    have hE : Real.exp (-(m * φ z)) * (Real.exp (-(m * (h w).re)) ^ 2 * Wf w) ≤
        Real.exp (-(m * φ (z + w))) := by
      simp only [hWf]
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := mul_le_mul_of_nonneg_left hb hm0
      rw [hq]
      nlinarith
    have hP : 0 ≤ ‖f (z + w)‖ ^ 2 := by positivity
    have hgz : 0 ≤ (1 - τ) * g z := by
      have := hgpos z (hKU hz); have : 0 < 1 - τ := by linarith
      positivity
    calc k * (‖F w‖ ^ 2 * Wf w)
        = ((1 - τ) * g z) * (‖f (z + w)‖ ^ 2 *
            (Real.exp (-(m * φ z)) * (Real.exp (-(m * (h w).re)) ^ 2 * Wf w))) := by
          rw [hFn, hk]; ring
      _ ≤ g (z + w) * (‖f (z + w)‖ ^ 2 * Real.exp (-(m * φ (z + w)))) := by
          apply mul_le_mul hgzw (mul_le_mul_of_nonneg_left hE hP)
          · have := hW0 w; positivity
          · exact (hgpos _ (hmaps (ball_subset_closedBall hw))).le
      _ = G (z + w) := by simp only [hG]; ring
  have hint1 : IntegrableOn (fun w => k * (‖F w‖ ^ 2 * Wf w)) (ball (0 : V n) δ) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 δ)
      (continuousOn_const.mul ((hFc.norm.pow 2).mul hWc.continuousOn))).mono_set
      ball_subset_closedBall
  have hint2 : IntegrableOn (fun w => G (z + w)) (ball (0 : V n) δ) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 δ) hGc).mono_set
      ball_subset_closedBall
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_ball hpt
  rw [integral_const_mul, integral_ball_translate z δ G] at hmono

  set J := ∫ w in ball (0 : V n) δ, Wf w with hJ
  set I := ∫ w in ball z δ, G w with hI
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_ball fun w _ => hW0 w
  set A := ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z with hA
  have hA0 : 0 ≤ A := by have := hgpos z (hKU hz); positivity
  have hAJ : (1 - τ) * (A * J) ≤ I := by
    have h1 := mul_le_mul_of_nonneg_left hcirc hk0
    calc (1 - τ) * (A * J) = k * (‖f z‖ ^ 2 * J) := by rw [hA, hk]; ring
      _ ≤ _ := h1
      _ ≤ I := hmono
  have hmn : 0 ≤ (m : ℝ) ^ n := by positivity
  have hkey := hτd d hd0 hdD
  change A ≤ (d + ε) * (m : ℝ) ^ n * I
  calc A = A * 1 := (mul_one A).symm
    _ ≤ A * ((d + ε / 2) * (m : ℝ) ^ n * J) := mul_le_mul_of_nonneg_left hT hA0
    _ ≤ A * ((1 - τ) * (d + ε) * (m : ℝ) ^ n * J) := by
        apply mul_le_mul_of_nonneg_left _ hA0
        have := mul_nonneg hmn hJ0
        nlinarith
    _ = (d + ε) * (m : ℝ) ^ n * ((1 - τ) * (A * J)) := by ring
    _ ≤ (d + ε) * (m : ℝ) ^ n * I := by
        apply mul_le_mul_of_nonneg_left hAJ
        have : 0 ≤ d + ε := by linarith
        positivity

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExtendClassCoprimeEtaleExcision
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.MVGlue

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem etale_awayMap : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C] (f : A), @Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) _ _ (Localization.awayMap (algebraMap A C) f).toAlgebra := by
  intro A C _ _ _ _ f
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale C (Localization.Away (algebraMap A C f)) := Algebra.Etale.of_isLocalizationAway (algebraMap A C f)
  haveI : Algebra.Etale A (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  haveI : Algebra.Etale A (Localization.Away (algebraMap A C f)) := Algebra.Etale.comp A C _
  haveI : IsScalarTower A (Localization.Away f) (Localization.Away (algebraMap A C f)) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show _ = Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) a)
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply A C (Localization.Away (algebraMap A C f))]
  exact Algebra.Etale.of_restrictScalars A _ _

theorem pull_spMap_comp (q : ℕ) {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (g.comp f)) _ _ x = pull _ (spMap g) _ _ (pull _ (spMap f) _ _ x) := by
  rw [spMap_comp', pull_comp]

theorem pull_spMap_id (q : ℕ) {A : Type} [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ _ x = x := by
  have : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
    exact sch.map_id _
  rw [this, pull_id]

theorem glue : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a := by
  intro q A C _ _ _ f g hfg hC n i a ha
  obtain ⟨hEt, h1, h2⟩ := hC
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) := etale_awayMap A C f
  have hB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) =
      Localization.awayMap (algebraMap A C) f := rfl
  set h : Localization.Away f := algebraMap A (Localization.Away f) g with hh
  have c1 := GlobalTheory.T.away_congr_mod_of_isCoprime A C f g hfg h1
  have c2 := GlobalTheory.T.awayMap_span_singleton_divisibility_descends A C f g h2
  rw [← hB] at c1 c2

  have hu1 : IsUnit (((algebraMap (Localization.Away f) (Localization.Away h)).comp
      (algebraMap A (Localization.Away f))) (f * g)) := by
    rw [map_mul, RingHom.comp_apply, RingHom.comp_apply]
    refine IsUnit.mul ?_ ?_
    · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map
        (algebraMap (Localization.Away f) (Localization.Away h))
    · exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h
  let ψ : Localization.Away (f * g) →+* Localization.Away h :=
    IsLocalization.Away.lift (S := Localization.Away (f * g)) (f * g) hu1
  have hψ : ∀ x : A, ψ (algebraMap A _ x) = algebraMap _ _ (algebraMap A (Localization.Away f) x) := fun x => by
    simp only [ψ, IsLocalization.Away.lift_eq, RingHom.comp_apply]
  have hgB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h =
      algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C g) := by
    rw [hB, hh]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hu2 : IsUnit (((algebraMap (Localization.Away (algebraMap A C f))
      (Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h))).comp
      (algebraMap C (Localization.Away (algebraMap A C f)))) (algebraMap A C (f * g))) := by
    rw [map_mul, map_mul, RingHom.comp_apply, RingHom.comp_apply, ← hgB]
    refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap A C f)) (algebraMap A C f)).map _
  let χ : Localization.Away (algebraMap A C (f * g)) →+*
      Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h) :=
    IsLocalization.Away.lift (S := Localization.Away (algebraMap A C (f * g))) (algebraMap A C (f * g)) hu2
  have hsq : (Localization.awayMap (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f))) h).comp ψ =
      χ.comp (Localization.awayMap (algebraMap A C) (f * g)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, χ]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsLocalization.Away.lift_eq, hB]
  obtain ⟨b, hb, -⟩ := GlobalTheory.T.localization_pullback_injective q (Localization.Away f) (Localization.Away (algebraMap A C f)) h c1 c2 n i
    (pull _ (spMap ψ) _ _ a) 0 (by
      rw [map_zero, ← pull_spMap_comp, hsq, pull_spMap_comp, ha, map_zero])
  refine ⟨b, fun ρ hρ => ?_⟩
  have hρu : IsUnit (ρ h) := by
    rw [hh, ← RingHom.comp_apply, hρ, map_mul] at *
    exact isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g))
  let ψ' : Localization.Away h →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift (S := Localization.Away h) h hρu
  have h1' : ψ'.comp (algebraMap (Localization.Away f) (Localization.Away h)) = ρ :=
    IsLocalization.Away.lift_comp _ _
  have h2' : ψ'.comp ψ = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, ψ', IsLocalization.Away.lift_eq, RingHom.id_apply]
    rw [← RingHom.comp_apply ρ, hρ]
  rw [← h1', pull_spMap_comp, hb, ← pull_spMap_comp, h2', pull_spMap_id]

end GlobalTheory.MVGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNbhdTransitionMapDirectedSystem
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem algebraMap_comp_eq_of_pt {i j : EtNbhd R} (φ₁ φ₂ : i.A →ₐ[R] j.A)
    (h₁ : j.pt.comp φ₁ = i.pt) (h₂ : j.pt.comp φ₂ = i.pt) (a : i.A) :
    algebraMap j.A j.B (φ₁ a) = algebraMap j.A j.B (φ₂ a) := by
  let ψ₁ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₁
  let ψ₂ : i.A →ₐ[R] j.B := (IsScalarTower.toAlgHom R j.A j.B).comp φ₂
  have : ψ₁ = ψ₂ := by
    refine GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq fun b => ?_
    rw [← sub_eq_zero, ← (residue j.B).map_sub (ψ₁ b) (ψ₂ b), residue_eq_zero_iff]
    show algebraMap j.A j.B (φ₁ b) - algebraMap j.A j.B (φ₂ b) ∈ maximalIdeal j.B
    rw [← (algebraMap j.A j.B).map_sub (φ₁ b) (φ₂ b), IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show φ₁ b - φ₂ b ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congr($h₁ b)).trans (congr($h₂ b)).symm
  exact congr($this a)

theorem trans_algebraMap_eq_of_pt {i j : EtNbhd R} (h : i ≤ j) (φ : i.A →ₐ[R] j.A)
    (hφ : j.pt.comp φ = i.pt) (a : i.A) :
    trans h (algebraMap i.A i.B a) = algebraMap j.A j.B (φ a) := by
  unfold trans
  rw [Localization.localRingHom_to_map]
  exact algebraMap_comp_eq_of_pt _ _ h.choose_spec hφ a

end GlobalTheory.Henselisation.EtNbhd

namespace GlobalTheory.Henselisation

theorem trans_system : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (i : EtNbhd R) (x : i.B), EtNbhd.trans (le_refl i) x = x) ∧ ∀ (i j k : EtNbhd R) (hij : i ≤ j) (hjk : j ≤ k) (x : i.B), EtNbhd.trans hjk (EtNbhd.trans hij x) = EtNbhd.trans (hij.trans hjk) x := by
  intro R _ _
  refine ⟨fun i x => ?_, fun i j k hij hjk x => ?_⟩
  · have : EtNbhd.trans (le_refl i) = RingHom.id i.B :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.id_apply]
        exact EtNbhd.trans_algebraMap_eq_of_pt _ (AlgHom.id R i.A) (AlgHom.comp_id _) a)
    exact congr($this x)
  · have : (EtNbhd.trans hjk).comp (EtNbhd.trans hij) = EtNbhd.trans (hij.trans hjk) :=
      IsLocalization.ringHom_ext i.q.primeCompl (RingHom.ext fun a => by
        simp only [RingHom.comp_apply]
        rw [EtNbhd.trans_algebraMap_eq_of_pt hij hij.choose hij.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt hjk hjk.choose hjk.choose_spec,
          EtNbhd.trans_algebraMap_eq_of_pt (hij.trans hjk) (hjk.choose.comp hij.choose)
            (by rw [← AlgHom.comp_assoc, hjk.choose_spec, hij.choose_spec])]
        rfl)
    exact congr($this x)

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnOfPsiOn
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiUnitOfPsiOn

theorem injective_of_isIso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] : Function.Injective f.hom := by
  intro a b e
  have := congrArg (inv f).hom e
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

theorem mem_wchart1 {Y B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (z : Y) (i : M.ι) (hz : φ z ∈ M.U i) :
    z ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => i) := Set.mem_iInter.2 fun _ => hz

theorem psiUnitOn_of_psiOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), PsiOn D W → ∀ y : D.X, PsiUnitOn D y (W : Set (Spec (CommRingCat.of R))) := by
  intro R _ _ D W ψ y j V _ hVW hj h
  obtain ⟨p, rfl⟩ : ∃ p, j = fun _ => p := ⟨j PUnit.unit, funext fun _ => rfl⟩
  have hle : W.ι ⁻¹ᵁ V ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    fun z hz => mem_wchart1 _ _ _ _ (hj hz)
  have hVr : V ≤ W.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact hVW
  haveI := W.ι.isIso_app V hVr
  set u : Γ(W.toScheme, W.ι ⁻¹ᵁ V)ˣ := res hle ((ψ.psi y).s (fun _ => p)) with hu
  set r : Γ(Spec (CommRingCat.of R), V) := (inv (W.ι.app V)).hom u.val with hr
  have hr' : (W.ι.app V).hom r = u.val := by
    rw [hr, ← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  refine ⟨r, u.isUnit.map (inv (W.ι.app V)).hom, ?_⟩
  have hKr : jK R ⁻¹ᵁ V ≤ (jK R ⁻¹ᵁ W).ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]; exact fun z hz => hVW hz
  haveI := (jK R ⁻¹ᵁ W).ι.isIso_app (jK R ⁻¹ᵁ V) hKr
  apply injective_of_isIso ((jK R ⁻¹ᵁ W).ι.app (jK R ⁻¹ᵁ V))
  refine fn_ext ?_
  intro z hz
  have hι : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hzV : jK R ((jK R ⁻¹ᵁ W).ι z) ∈ V := hz
  have hpt : W.ι ((jK R ∣_ W) z) = jK R ((jK R ⁻¹ᵁ W).ι z) := congrArg (fun q => q z) hι
  have hm : (jK R ∣_ W) z ∈ W.ι ⁻¹ᵁ V := by
    show W.ι ((jK R ∣_ W) z) ∈ V
    rw [hpt]; exact hzV
  have h₁ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hm)
  have h₂ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ⁻¹ᵁ W).ι ≫ D.xK y) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hzV)
  have e₃ := (gm_pullGen D.P.L _ _ (ψ.psi y) (jK R ∣_ W) (𝟙 _) z (fun _ => p) h₁).symm.trans
    ((gm_corr D.P.L (ψ.psi_eq y) (𝟙 _) z p h₁ h₂).trans
      (gm_pullGen D.P.L _ _ (D.psi y) (jK R ⁻¹ᵁ W).ι (𝟙 _) z (fun _ => p) h₂))
  rw [Category.id_comp, Category.id_comp] at e₃
  have l₁ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz ((jK R).app V |>.hom r)
  have l₂ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz
    (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi y).s (fun _ => p)).val)
  rw [Category.id_comp] at l₁ l₂
  rw [l₁, l₂, gs_pull _ _ z V hzV r, ← hι, ← gs_pull _ _ z V hm r, hr', hu,
    gs_unit _ z _ hm]
  erw [gm_res _ z hle hm]
  erw [gs_res _ z h hz]
  rw [gs_unit _ z _ (h hz)]
  exact congrArg Units.val e₃


end GlobalTheory.PsiUnitOfPsiOn
end
end

