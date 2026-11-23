module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0076
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOffZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

theorem hessC_half_log_normSq_add {D : ℕ} (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ)
    (hh : AnalyticAt ℂ h y) (hy : h y ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y =
      ((ε / (2 * (‖h y‖ ^ 2 + ε) ^ 2) : ℝ) : ℂ) • hessC (fun w => ‖h w‖ ^ 2) y := by
  set L : (Fin D → ℂ) → ℝ := fun w => Real.log ‖h w‖ with hLdef
  set F : ℝ → ℝ := fun t => Real.log (Real.exp (2 * t) + ε) / 2 with hFdef
  set G : ℝ → ℝ := fun t => Real.exp (2 * t) with hGdef
  have hhc : ContDiffAt ℝ 2 h y := (hh.contDiffAt (n := 2)).restrict_scalars ℝ
  have hLc : ContDiffAt ℝ 2 L y := (hhc.norm ℝ hy).log (norm_ne_zero_iff.2 hy)
  have hL0 : hessC L y = 0 := ReciprocityTheory.AnForm.A.hessC_log_norm h y hh hy
  have he : ∀ t, HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul 2).exp
  have hFc : ContDiff ℝ 2 F :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).add contDiff_const).log
      (fun t => by simp only [Function.comp_apply, id]; positivity) |>.div_const 2
  have hGc : ContDiff ℝ 2 G := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hF := HessCCompPluri.proof D F L y hFc.contDiffAt hLc hL0
  have hG := HessCCompPluri.proof D G L y hGc.contDiffAt hLc hL0
  have hdF : deriv F = fun t => Real.exp (2 * t) / (Real.exp (2 * t) + ε) := by
    funext t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    refine (((he t).add_const ε).log hp |>.div_const 2).deriv.trans ?_
    field_simp
  have hddF : ∀ t, deriv (deriv F) t = 2 * ε * Real.exp (2 * t) / (Real.exp (2 * t) + ε) ^ 2 := by
    intro t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    rw [hdF]
    refine ((he t).div ((he t).add_const ε) hp).deriv.trans ?_
    field_simp
    ring
  have hdG : deriv G = fun t => Real.exp (2 * t) * 2 := funext fun t => (he t).deriv
  have hddG : ∀ t, deriv (deriv G) t = Real.exp (2 * t) * 2 * 2 := fun t => by
    rw [hdG]
    exact ((he t).mul_const 2).deriv
  have hexp : ∀ w, h w ≠ 0 → Real.exp (2 * L w) = ‖h w‖ ^ 2 := fun w hw => by
    rw [hLdef, show 2 * Real.log ‖h w‖ = Real.log (‖h w‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  have hev : ∀ᶠ w in 𝓝 y, h w ≠ 0 := hh.continuousAt.eventually_ne hy
  have eF : hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y = hessC (fun w => F (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hFdef, hexp w hw])
  have eG : hessC (fun w => ‖h w‖ ^ 2) y = hessC (fun w => G (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hGdef, hexp w hw])
  rw [eF, eG, hF, hG, hddF, hddG, hexp y hy, smul_smul]
  congr 1
  have ha : 0 < ‖h y‖ ^ 2 := by positivity
  push_cast
  field_simp

theorem LelongLimitOffZero.proof (hM : ChartMassCompact.Statement) : LelongLimitOffZero.Statement := by
  classical
  intro n d J u f φ hJ hdim hu hf hfc hφ hdisj
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection J A := hA.choose_spec
  have hZc : IsClosed (zeroSet J) := by
    have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
      ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hK : IsCompact (tsupport f ∩ zeroSet J) := hfc.isCompact.inter_right hZc
  have hu0 : ∀ x ∈ tsupport f ∩ zeroSet J, linEval u x ≠ 0 := fun x hx h0 =>
    Set.disjoint_left.1 hdisj hx.1 ⟨hx.2, h0⟩
  set q : (Fin n → ℂ) → ℝ := fun x => ‖linEval u x‖ ^ 2 with hq
  have hqc : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).comp (contDiff_linEval u)
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ tsupport f ∩ zeroSet J, m ≤ q x := by
    rcases (tsupport f ∩ zeroSet J).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hqc.continuous.continuousOn
      exact ⟨q x₀, by have := hu0 x₀ hx₀; simp only [hq]; positivity, fun x hx => hmin hx⟩
  have hGi : Integrable (chartAbsDens J A f (vecCons q φ)) := by
    refine hM n (d + 1) J A f _ hJ hdim hAf hf.continuous.continuousOn (fun i => ?_) (Or.inl hfc)
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hqc
    · simpa using hφ j
  have hb : ∀ ε : ℝ, 0 < ε → ∀ y, ‖chartDens J A f (vecCons (logReg u ε) φ) y‖ ≤
      ε / (2 * m ^ 2) * chartAbsDens J A f (vecCons q φ) y := by
    intro ε hε y
    rw [Real.norm_eq_abs]
    refine (abs_chartDens_le J A f _ y).trans ?_
    have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hAf y).2.1
    unfold chartAbsDens
    refine sheetSum_le_mul hfin _ _ _ fun x hx s hs => ?_
    by_cases hfx : f x = 0
    · simp [hfx]
    have hxK : x ∈ tsupport f ∩ zeroSet J := ⟨subset_tsupport _ hfx, hx.1⟩
    obtain rfl : A *ᵥ x = y := hx.2
    obtain ⟨U, hU, hxU, hsd, hsx, -, -⟩ := hs
    have hsa : AnalyticAt ℂ s (A *ᵥ x) := analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ U (fun z => s z i) hU (differentiableOn_pi.1 hsd i) _ hxU
    have hha : AnalyticAt ℂ (fun w => linEval u (s w)) (A *ᵥ x) := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 hsa) j)
    have hne : linEval u (s (A *ᵥ x)) ≠ 0 := by rw [hsx]; exact hu0 x hxK
    have hH0 := hessC_half_log_normSq_add (fun w => linEval u (s w)) _ hha hne hε
    simp only [hsx] at hH0
    have hH : hessC (logReg u ε ∘ s) (A *ᵥ x) =
        ((ε / (2 * (q x + ε) ^ 2) : ℝ) : ℂ) • hessC (q ∘ s) (A *ᵥ x) := hH0
    rw [vecCons_comp, vecCons_comp, maDens_cons_of_hessC_eq_smul (logReg u ε ∘ s) (q ∘ s) _ _ _ hH]
    have ha : m ≤ q x := hm x hxK
    have hc0 : 0 ≤ ε / (2 * (q x + ε) ^ 2) := by positivity
    have hc : ε / (2 * (q x + ε) ^ 2) ≤ ε / (2 * m ^ 2) :=
      div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith)
    calc |f x * (ε / (2 * (q x + ε) ^ 2) * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x))|
        = ε / (2 * (q x + ε) ^ 2) * |f x * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x)| := by
          rw [mul_left_comm, abs_mul, abs_of_nonneg hc0]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hlim : Tendsto (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y) := by
      fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto' 0 0 (by simp))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  unfold chartInt
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (hGi.const_mul _) (Eventually.of_forall (hb ε hε))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem mem_minimalPrimes_sup_linForm {n : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    {u : Fin n → ℂ} (hWm : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) :
    W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0 := by
  have hle : J ⊔ Ideal.span {linForm u} ≤ W := hWm.1.2
  refine ⟨hWm.1.1, fun x hx q hq => hx q (hle (Ideal.mem_sup_left hq)), fun x hx => ?_⟩
  have := hx _ (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  simpa [linForm, linEval] using this

theorem lelongSides_add (hAdd : VarIntAdd.Statement) {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {u : Fin n → ℂ} {φ : Fin d → (Fin n → ℂ) → ℝ} (hJ : J.IsPrime)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) (g₁ g₂ : (Fin n → ℂ) → ℝ) (h1 : ContDiff ℝ ∞ g₁)
    (h1c : HasCompactSupport g₁) (h2 : ContDiff ℝ ∞ g₂) (h2c : HasCompactSupport g₂) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), varInt J (d + 1) (g₁ + g₂) (vecCons (logReg u ε) φ) =
      varInt J (d + 1) g₁ (vecCons (logReg u ε) φ) + varInt J (d + 1) g₂ (vecCons (logReg u ε) φ)) ∧
    (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d (g₁ + g₂) φ) =
      (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g₁ φ) +
      ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g₂ φ := by
  classical
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine hAdd n (d + 1) J g₁ g₂ _ hJ h1.continuous h1c h2.continuous h2c fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
    · simpa using hφ j
  · rw [← finsum_mem_add_distrib (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)]
    refine finsum_mem_congr rfl fun W hWm => ?_
    obtain ⟨hWp, hWJ, -⟩ := mem_minimalPrimes_sup_linForm hWm
    have hφW : ∀ i, SmoothNear (zeroSet W) (φ i) := fun i => by
      obtain ⟨U, hU, hSU, hC⟩ := hφ i
      exact ⟨U, hU, hWJ.trans hSU, hC⟩
    rw [hAdd n d W g₁ g₂ φ hWp h1.continuous h1c h2.continuous h2c hφW, mul_add]

theorem lelongLimit_off_small (hOff : LelongLimitOffZero.Statement) (hAdd : VarIntAdd.Statement)
    {n d : ℕ} {J I : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ} {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hu : linForm u ∉ J) (hφ : ∀ i, SmoothNear (zeroSet J) (φ i))
    (hloc : ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
      ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
          (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
              (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ)))
    (g : (Fin n → ℂ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgI : Disjoint (tsupport g) (zeroSet I)) :
    Tendsto (fun ε => varInt J (d + 1) g (vecCons (logReg u ε) φ)) (𝓝[>] 0)
      (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
          (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ)) := by
  classical
  have hclosed : IsClosed (zeroSet J ∩ {x | linEval u x = 0}) := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
    · exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  refine tendsto_of_forall_local_on_tsupport
    (fun ε g => varInt J (d + 1) g (vecCons (logReg u ε) φ))
    (fun g => ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
      (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ)
    (fun g₁ g₂ h1 h1c h2 h2c => (lelongSides_add hAdd hJ hφ g₁ g₂ h1 h1c h2 h2c).1)
    (fun g₁ g₂ h1 h1c h2 h2c => (lelongSides_add hAdd (u := u) hJ hφ g₁ g₂ h1 h1c h2 h2c).2)
    g hg hgc fun q hq => ?_
  by_cases hq0 : q ∈ zeroSet J ∩ {x | linEval u x = 0}
  · exact hloc q hq0.1 hq0.2 (Set.disjoint_left.1 hgI hq)
  · refine ⟨_, hclosed.isOpen_compl.mem_nhds hq0, fun g' hg' hg'c hg'N => ?_⟩
    have h0 : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
        (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g' φ) = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
      rw [finsum_eq_dif]
      by_cases hWm : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes
      · obtain ⟨-, hWJ, hWu⟩ := mem_minimalPrimes_sup_linForm hWm
        rw [dite_eq_left hWm, varInt_eq_zero_of_vanish W g' φ fun x hx =>
          image_eq_zero_of_notMem_tsupport fun hxs => hg'N hxs ⟨hWJ hx, hWu x hx⟩, mul_zero]
      · rw [dite_eq_right hWm]
    simp only [h0]
    exact hOff n d J u g' φ hJ hdim hu hg' hg'c hφ
      (Set.disjoint_left.2 fun x hx hx' => hg'N hx hx')

theorem LelongLimitOnZero.proof (hOff : LelongLimitOffZero.Statement)
    (hGood : LelongLimitGoodPoints.Statement) (hSmall : LelongMassNearSmall.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimitOnZero.Statement := by
  classical
  intro n d J u φ p hJ hdim hu hφ _ _
  refine ⟨Set.univ, Filter.univ_mem, fun f hf hfc _ => ?_⟩
  obtain ⟨I, hI, hIdim, hloc⟩ := hGood n d J u φ hJ hdim hu hφ
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨χ, hχ, ⟨U, hU, hIU, hχ1⟩, hTχ, hLχ⟩ :=
    hSmall n d J I u φ f hJ hdim hu hφ hI hIdim hf hfc (δ / 3) (by positivity)
  have hχf : ContDiff ℝ ∞ (fun x => χ x * f x) := hχ.mul hf
  have hχfc : HasCompactSupport (fun x => χ x * f x) := hfc.mul_left
  have hg : ContDiff ℝ ∞ (fun x => (1 - χ x) * f x) := (contDiff_const.sub hχ).mul hf
  have hgc : HasCompactSupport (fun x => (1 - χ x) * f x) := hfc.mul_left
  have hgI : Disjoint (tsupport fun x => (1 - χ x) * f x) (zeroSet I) := by
    refine Disjoint.mono_right hIU (Disjoint.closure_left ?_ hU)
    refine Set.disjoint_left.2 fun x hx hxU => hx ?_
    simp [hχ1 x hxU]
  have hsum : (fun x => χ x * f x) + (fun x => (1 - χ x) * f x) = f := by
    funext x
    simp only [Pi.add_apply]
    ring
  obtain ⟨hTadd, hLadd⟩ := lelongSides_add hAdd (u := u) hJ hφ _ _ hχf hχfc hg hgc
  rw [hsum] at hTadd hLadd
  refine ((Metric.tendsto_nhds.1
    (lelongLimit_off_small hOff hAdd hJ hdim hu hφ hloc _ hg hgc hgI) (δ / 3) (by positivity)).and
    (hTχ.and hTadd)).mono fun ε ⟨h1, h2, h3⟩ => ?_
  rw [Real.dist_eq] at h1 ⊢
  rw [h3, hLadd]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at h2 hLχ
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hLχ.1, hLχ.2]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongRegularise
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace LelongRegularise

theorem mdisc_eq_zero_of_eq_zero {D : ℕ} (B : Fin (D + 1) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (h : B 0 = 0) : ReciprocityTheory.AnForm.mdisc B = 0 := by
  classical
  unfold ReciprocityTheory.AnForm.mdisc
  refine mul_eq_zero_of_right _ ?_
  have hu : (Finset.univ : Finset (Fin (D + 1))) = insert 0 (Finset.univ.erase 0) :=
    (Finset.insert_erase (Finset.mem_univ 0)).symm
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert (Finset.notMem_erase 0 _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun t ht => ?_
  have h0t : (0 : Fin (D + 1)) ∉ t := fun h0 => Finset.notMem_erase 0 _ (Finset.mem_powerset.1 ht h0)
  have hc : t.card ≤ D := by
    have := Finset.card_le_card (Finset.mem_powerset.1 ht)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [Finset.sum_insert h0t, h, zero_add, Finset.card_insert_of_notMem h0t]
  have he : D + 1 - t.card = (D + 1 - (t.card + 1)) + 1 := by omega
  rw [he, pow_succ]
  ring

theorem maDens_eq_zero_of_eventually {D : ℕ} (F : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ)
    {y : Fin (D + 1) → ℂ} (h : F 0 =ᶠ[𝓝 y] fun _ => 0) : ReciprocityTheory.AnForm.maDens F y = 0 := by
  have h2 : fderiv ℝ (fderiv ℝ (F 0)) y = 0 := by
    rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    simp
  have hH : ReciprocityTheory.AnForm.hessC (F 0) y = 0 := by
    ext i j
    simp [ReciprocityTheory.AnForm.hessC, h2]
  unfold ReciprocityTheory.AnForm.maDens
  rw [mdisc_eq_zero_of_eq_zero (fun k => ReciprocityTheory.AnForm.hessC (F k) y) hH]
  simp

theorem abs_half_log_le {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (t ^ 2 + ε) / 2| ≤ |Real.log t| + |Real.log (2 * t)| := by
  have ht2 : 0 < t ^ 2 := by positivity
  have hlo : Real.log t ≤ Real.log (t ^ 2 + ε) / 2 := by
    have : Real.log (t ^ 2) ≤ Real.log (t ^ 2 + ε) := Real.log_le_log ht2 (by linarith)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hup : Real.log (t ^ 2 + ε) ≤ 2 * (|Real.log t| + |Real.log (2 * t)|) := by
    have h1 : Real.log (t ^ 2 + ε) ≤ Real.log (t ^ 2 + 1) := Real.log_le_log (by positivity) (by linarith)
    have h2t : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht.ne'
    rcases le_total t 1 with h | h
    · have : Real.log (t ^ 2 + 1) ≤ Real.log (2 ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this
      push_cast at this
      have a1 := le_abs_self (Real.log (2 * t))
      have a2 := neg_abs_le (Real.log t)
      linarith
    · have : Real.log (t ^ 2 + 1) ≤ Real.log ((2 * t) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this
      push_cast at this
      have a1 := le_abs_self (Real.log (2 * t))
      have a2 := abs_nonneg (Real.log t)
      linarith
  rw [abs_le]
  constructor
  · have a1 := neg_abs_le (Real.log t)
    have a2 := abs_nonneg (Real.log (2 * t))
    linarith
  · linarith

theorem exists_poly_of_linEval_eq_zero {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A)
    (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ y x, x ∈ fibre J A y → linEval u x = 0 → MvPolynomial.eval y P = 0 := by
  classical
  have := hJ
  set a := Ideal.Quotient.mk J (linForm u) with ha_def
  have ha : a ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hint : (projHom J A).toRingHom.IsIntegralElem a := hA.finite.to_isIntegral _
  have hex : ∃ k, ∃ p : Polynomial (MvPolynomial (Fin d) ℂ), p.Monic ∧ p.natDegree = k ∧
      p.eval₂ (projHom J A).toRingHom a = 0 := by
    obtain ⟨p, hpm, hp⟩ := hint
    exact ⟨_, p, hpm, rfl, hp⟩
  obtain ⟨p, hpm, hpk, hp⟩ := Nat.find_spec hex
  refine ⟨p.coeff 0, fun h0 => ?_, ?_⟩
  · obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hpm
    have hq : q.eval₂ (projHom J A).toRingHom a = 0 := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hp
      exact (mul_eq_zero.1 hp).resolve_left ha
    have hlt : q.natDegree < Nat.find hex := by
      rw [← hpk, Polynomial.natDegree_X_mul hqm.ne_zero]
      omega
    exact Nat.find_min hex hlt ⟨q, hqm, rfl, hq⟩
  · rintro y x ⟨hx, hxy⟩ hux
    have h := congrArg (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) hp
    rw [Polynomial.hom_eval₂, IndefiniteRowSideFullHecke.ComplexSets.lift_eval_comp_projHom J A hx, map_zero] at h
    have hax : (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) a = 0 := by
      rw [ha_def, Ideal.Quotient.lift_mk, ← hux]
      simp [linForm, linEval]
    rw [hax, Polynomial.eval₂_at_zero, hxy] at h
    exact h

theorem ae_eval_ne_zero {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : ι → ℂ, MvPolynomial.eval w g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun w => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖w‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm w i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r)
    (fun w => MvPolynomial.eval w g ≠ 0)).mpr fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

theorem norm_chartDens_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) {R : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {y : Fin (d + 1) → ℂ}
    (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    ‖chartDens J A (logReg u ε) (vecCons f φ) y‖ ≤
      chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖)
          (vecCons f φ) y +
        chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval ((2 : ℂ) • u) x‖)
          (vecCons f φ) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs]
    by_cases hxB : x ∈ Metric.closedBall 0 R
    · rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_mul, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have h2 : ‖linEval ((2 : ℂ) • u) x‖ = 2 * ‖linEval u x‖ := by
        have : linEval ((2 : ℂ) • u) x = 2 * linEval u x := by
          simp [linEval, Finset.mul_sum, mul_assoc]
        rw [this, norm_mul]
        norm_num
      rw [h2]
      exact abs_half_log_le (norm_pos_iff.2 (hy x hx)) hε hε1
    · have hM : ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ hs.choose) y = 0 := by
        obtain ⟨U, hU, hxU, hsd, hsx, -⟩ := hs.choose_spec
        refine maDens_eq_zero_of_eventually _ ?_
        have hc : ContinuousAt hs.choose y := by
          rw [← hx.2]
          exact hsd.continuousOn.continuousAt (hU.mem_nhds hxU)
        have hx' : x ∉ tsupport f := fun h => hxB (hR h)
        have hn : (tsupport f)ᶜ ∈ 𝓝 (hs.choose y) := by
          rw [← hx.2, hsx]
          exact (isClosed_tsupport f).isOpen_compl.mem_nhds hx'
        filter_upwards [hc.preimage_mem_nhds hn] with w hw
        simp only [Matrix.cons_val_zero, Function.comp_apply]
        exact image_eq_zero_of_notMem_tsupport hw
      rw [hM]
      simp
  · simp only [dif_neg hs]
    simp

end LelongRegularise

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelDivisorChartGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem NormalModelDivisorChartGeneric.proof (h₁ : NormalModelGoodPointGeneric.Statement)
    (h₂ : NormalModelGoodPointChart.Statement) : NormalModelDivisorChartGeneric.Statement := by
  intro n d J u M hJ hd hu
  obtain ⟨B, hB, hBd, hgood⟩ := h₁ n d J u M hJ hd hu
  exact ⟨B, hB, hBd, fun w hw hu0 hwB => h₂ n d J u M w (hgood w hw hu0 hwB)⟩

end

end GroundTheory.Heights₂.Heights
end

