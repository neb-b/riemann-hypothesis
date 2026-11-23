module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MaMeasureEqOfConst
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_eq_of_const {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) (c : Fin e → ℝ)
    (h : ∀ i x y, (Ψ i).φ x y = (Φ i).φ x y + c i) : maMeasure A Ψ = maMeasure A Φ := by
  have hH : ∀ (F : (Fin e → ℂ) → ℝ) (a : ℝ) (y : Fin e → ℂ),
      hessC (fun z => F z + a) y = hessC F y := by
    intro F a y
    have h1 : fderiv ℝ (fun z => F z + a) = fderiv ℝ F := funext fun z => fderiv_add_const a
    unfold hessC
    rw [h1]
  have hD : ∀ j, locDens A Ψ j = locDens A Φ j := by
    intro j
    funext y
    unfold locDens maDens
    have hk : (fun k => hessC (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) =
        fun k => hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      funext k
      simp only [h k]
      exact hH _ _ y
    rw [hk]
  unfold maMeasure
  simp only [hD]

theorem exists_pos_le_all {e : ℕ} (f : Fin e → ℝ) (hf : ∀ i, 0 < f i) (a : ℝ) (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ b ≤ a ∧ ∀ i, b ≤ f i := by
  have hne : (insert a (Finset.univ.image f)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨_, (Finset.lt_min'_iff _ hne).2 fun x hx => ?_,
    Finset.min'_le _ _ (Finset.mem_insert_self _ _),
    fun i => Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ i)))⟩
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact ha
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf i

theorem tail_uniform : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → ∃ K t₁ : ℝ, 0 < t₁ ∧ (0 < t₀ → t₁ ≤ t₀) ∧ ∀ τ : Fin e → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ t₁) → (∀ i, IsPotential A (th i + LocPot.ofFun (phT i (τ i)) + Θ) ∧ IsPsh A (th i + LocPot.ofFun (phT i (τ i)) + Θ)) ∧ ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  intro hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR
  choose t₂ ht₂ ht₂₀ hfix using fun i =>
    fixedMember_base A Θ L s (th i) (ph i) (phT i) C₅ C t₀ hΘ hpos hnorm (hW i) (hR i)
  obtain ⟨a, ha, hε⟩ := epsT_small C
  obtain ⟨t₁, ht₁, ht₁a, ht₁0, ht₁2⟩ : ∃ t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ a ∧ (0 < t₀ → t₁ ≤ t₀) ∧
      ∀ i, t₁ ≤ t₂ i := by
    obtain ⟨b, hb, hba, hbf⟩ := exists_pos_le_all t₂ ht₂ a ha
    by_cases h0 : 0 < t₀
    · exact ⟨min b t₀, lt_min hb h0, (min_le_left _ _).trans hba, fun _ => min_le_right _ _,
        fun i => (min_le_left _ _).trans (hbf i)⟩
    · exact ⟨b, hb, hba, fun h => absurd h h0, hbf⟩
  have hB := fun i => hfix i t₁ ht₁ (ht₁2 i)
  obtain ⟨Ct, hCt⟩ := hTB A (fun i => th i + LocPot.ofFun (phT i t₁) + Θ) L s m W
    (fun i => (hB i).1) (fun i => (hB i).2.2.1) hL hS hSNC hnorm
  have hC₁ : 0 ≤ |C₅| + |C| + 1 := by positivity
  refine ⟨Ct * (|C₅| + |C| + 1 + 3), t₁, ht₁, ht₁0, fun τ hτ => ⟨fun i => ?_, fun R hRe => ?_⟩⟩
  · have hτ0 : τ i ≤ t₀ := ((hτ i).2.trans (ht₁2 i)).trans (ht₂₀ i)
    obtain ⟨hsm, -, -, -, hpsh, -, -, -⟩ := (hR i).2.2 (τ i) (hτ i).1 hτ0
    have hth := (hW i).1
    have hεi := (abs_le.1 (hε (τ i) (hτ i).1 ((hτ i).2.trans ht₁a)).1).2
    refine ⟨isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ hsm)) hΘ,
      isPsh_of_le A Θ (th i) (phT i (τ i)) hΘ hpos hth hsm (epsT C (τ i)) 1 0 (by linarith) hpsh _
        (fun x z hz => ⟨hz.1.1, hz.2⟩) (fun x z => ?_)⟩
    show (th i).φ x z + phT i (τ i) z + Θ.φ x z = _
    ring
  · have hL' := fun i => (hB i).2.2.2 (τ i) (hτ i).1 (hτ i).2
    have hm : maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) =
        maMeasure A (fun i => (th i + LocPot.ofFun (phT i t₁) + Θ) +
          LocPot.ofFun (fun y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁)) :=
      maMeasure_eq_of_const A _ _ (fun _ => C * epsT C t₁) fun i x y => by
        show (th i).φ x y + phT i (τ i) y + Θ.φ x y =
          (th i).φ x y + phT i t₁ y + Θ.φ x y +
            (phT i (τ i) y - phT i t₁ y - C * epsT C t₁) + C * epsT C t₁
        ring
    rw [hm]
    exact hCt (|C₅| + |C| + 1) (fun i y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁) hC₁
      (fun i => (hL' i).1) (fun i => (hL' i).2.1)
      (fun i y hy => ⟨(hL' i).2.2.2 y hy, (hL' i).2.2.1 y⟩) R hRe

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartWOfContinuousPeriod
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] {L : Flat.LogPeriods n a g Λ}
  {bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ} {A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
  {B : Fin a → Matrix (Fin g) (Fin g) ℤ} {c ρ : ℝ}

theorem exists_ball_det (h : IsChart L bas A T0 B c ρ) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ', (A z).det ≠ 0 := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  obtain ⟨ρ₂, K, hρ₂, -, hinv⟩ := GlobalTheory.CompanionTheory.Ar.RiemannLimit.inv n g A
    (h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)) h.A_det
  exact ⟨min ρ₂ ρ, lt_min hρ₂ h.ρ_pos, min_le_right _ _,
    fun z hz => (hinv z (Metric.ball_subset_ball (min_le_left _ _) hz)).1⟩

theorem A_tendsto (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) : Tendsto (fun m => A (zs m)) atTop (𝓝 (A 0)) := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  exact ((h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto).comp hz

theorem T_tendsto (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) : Tendsto (fun m => T0 (zs m)) atTop (𝓝 (T0 0)) := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  exact ((h.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto).comp hz

theorem inv_period (h : IsChart L bas A T0 B c ρ) {ρ' : ℝ}
    (hdet : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ', (A z).det ≠ 0) (w : Fin n → ℂ)
    (hw : w ∈ logCover L.a_le) (hz : expCover a w ∈ Metric.ball (0 : Fin n → ℂ) ρ') (x : Λ) :
    ((A (expCover a w))ᵀ)⁻¹ *ᵥ L.P w x =
      cst (uCo bas x) + tauAt L.a_le T0 B w *ᵥ cst (vCo bas x) := by
  rw [h.per w hw x, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (Ne.isUnit (by rw [det_transpose]; exact hdet _ hz)),
    Matrix.one_mulVec]

theorem tendsto_inv_mulVec (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) {q : ℕ → Fin g → ℂ} {p : Fin g → ℂ}
    (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun m => ((A (zs m))ᵀ)⁻¹ *ᵥ q m) atTop (𝓝 (((A 0)ᵀ)⁻¹ *ᵥ p)) := by
  have hinv := tendsto_inv_transpose (A_tendsto h hz) h.A_det
  have hy := (((continuous_fst.matrix_mulVec continuous_snd :
    Continuous fun q : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => q.1 *ᵥ q.2)).tendsto
      (((A 0)ᵀ)⁻¹, p)).comp (hinv.prodMk_nhds hq)
  exact hy.congr fun m => rfl

theorem ker_each (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℝ)
    (hv : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) (j : Fin a) :
    (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 := by
  have hR : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have h0 : v ⬝ᵥ ((∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v) = 0 := by rw [hv]; simp
  rw [hR, Matrix.sum_mulVec, dotProduct_sum] at h0
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ v ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ v) := fun i _ => by
    simpa using (hB i).dotProduct_mulVec_nonneg v
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
  exact ((hB j).dotProduct_mulVec_zero_iff).1 (by simpa using h1)

theorem lower_at_centre (h : IsChart L bas A T0 B c ρ) (v : Fin g → ℝ)
    (hv : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) :
    c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((T0 0).map Complex.im) *ᵥ v) := by
  have := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
    Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball h.ρ_le)) h.B_psd h.c_pos h.im_lower
    0 (Metric.mem_ball_self h.ρ_pos) (fun _ => 0) (fun j hj => (hj rfl).elim) (fun _ _ => rfl) v
    (fun j _ => ker_each h.B_psd v hv j)
  simpa using this

theorem exp_cast (ha : a ≤ n) (w : Fin n → ℂ) (j : Fin a) :
    Complex.exp (w (Fin.castLE ha j)) = expCover a w (Fin.castLE ha j) := by
  have hj : (Fin.castLE ha j).val < a := j.2
  simp only [expCover, if_pos hj]

theorem extend_mem (h : IsChart L bas A T0 B c ρ) (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ)
    (ht : ContinuousAt t 0) (hP : ∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) :
    x ∈ chartW bas B := by
  classical
  obtain ⟨ρ', hρ', hρle, hdet⟩ := exists_ball_det h
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  set r : ℕ → ℝ := fun m => ρ'⁻¹ + m with hr
  set tm : ℕ → ℂ := fun m => ((r m / (2 * Real.pi) : ℝ) : ℂ) * Complex.I with htm
  set ws : ℕ → Fin n → ℂ := fun m k => if k.val < a then -(r m : ℂ) else 0 with hws
  have hrpos : ∀ m, 0 < r m := fun m => by
    have : 0 < ρ'⁻¹ := inv_pos.2 hρ'
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp only [hr]; linarith
  have hexpr : ∀ m, Real.exp (-(r m)) < ρ' := by
    intro m
    have h1 : r m + 1 ≤ Real.exp (r m) := Real.add_one_le_exp _
    have h3 : ρ'⁻¹ ≤ r m := by
      have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [hr]; linarith
    rw [Real.exp_neg]
    have h4 : ρ'⁻¹ < Real.exp (r m) := by linarith
    exact inv_lt_of_inv_lt₀ hρ' h4
  have hws_cast : ∀ m (j : Fin a), ws m (Fin.castLE L.a_le j) = -(r m : ℂ) := by
    intro m j
    have hj : (Fin.castLE L.a_le j).val < a := j.2
    simp only [hws, if_pos hj]
  have hws_mem : ∀ m, ws m ∈ logCover L.a_le := by
    intro m
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · rw [hws_cast]
      simp [hrpos m]
    · have hk' : ¬ k.val < a := not_lt.2 hk
      simp only [hws, if_neg hk']
      simp
  set zs : ℕ → Fin n → ℂ := fun m => expCover a (ws m) with hzs
  have hzs_k : ∀ m k, zs m k = if k.val < a then ((Real.exp (-(r m)) : ℝ) : ℂ) else 0 := by
    intro m k
    simp only [hzs, expCover, hws]
    by_cases hk : k.val < a
    · simp [hk]
    · simp [hk]
  have hzs_ball : ∀ m, zs m ∈ Metric.ball (0 : Fin n → ℂ) ρ' := by
    intro m
    rw [mem_ball_zero_iff, pi_norm_lt_iff hρ']
    intro k
    rw [hzs_k]
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]; exact hexpr m
    · simpa using hρ'
  have hrtop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hzs_lim : Tendsto zs atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro k
    simp only [hzs_k]
    by_cases hk : k.val < a
    · simp only [hk, if_true]
      have h1 : Tendsto (fun m => Real.exp (-(r m))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hrtop)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa only [Function.comp_def, Complex.ofReal_zero, Pi.zero_apply] using h2
    · simp only [hk, if_false]
      exact tendsto_const_nhds
  have hdiv : ∀ m, (-(r m : ℂ)) / (2 * Real.pi * Complex.I) = tm m := by
    intro m
    rw [div_eq_iff h2pi]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [htm]
    push_cast
    field_simp
    simp
  have hC : (∑ j, B j).map (fun x : ℤ => (x : ℂ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℂ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have hdec : ∀ m, tauAt L.a_le T0 B (ws m) =
      T0 (zs m) + tm m • (∑ j, B j).map (fun x : ℤ => (x : ℂ)) := by
    intro m
    have hsum : ∑ j, (ws m (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ)) = tm m • (∑ j, B j).map (fun x : ℤ => (x : ℂ)) := by
      rw [hC, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hws_cast, hdiv]
    simp only [tauAt]
    rw [hsum]
  have him : Tendsto (fun m => (tm m).im) atTop atTop := by
    have h1 : ∀ m, (tm m).im = r m / (2 * Real.pi) := fun m => by
      simp only [htm, Complex.mul_I_im, Complex.ofReal_re]
    simp only [h1]
    exact hrtop.atTop_div_const (by positivity)
  have hYm : ∀ m, ((tauAt L.a_le T0 B (ws m)).map Complex.im -
      c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef := fun m =>
    h.im_lower _ (Metric.ball_subset_ball hρle (hzs_ball m))
      (fun j => ws m (Fin.castLE L.a_le j)) (fun j => exp_cast L.a_le (ws m) j)
  have hq := tendsto_inv_mulVec h hzs_lim (ht.tendsto.comp hzs_lim)
  have hy' : Tendsto (fun m => (fun k => ((uCo bas x k : ℤ) : ℂ)) +
      tauAt L.a_le T0 B (ws m) *ᵥ (fun k => ((vCo bas x k : ℤ) : ℂ))) atTop
      (𝓝 (((A 0)ᵀ)⁻¹ *ᵥ t 0)) := hq.congr fun m => by
    have := inv_period h hdet (ws m) (hws_mem m) (hzs_ball m) x
    rw [hP _ (hws_mem m)] at this
    exact this
  obtain ⟨u, v, hv, -, hev⟩ := _root_.GlobalTheory.CompanionTheory.PeriodLimitSeq.limit_seq g (∑ j, B j) (T0 0) (fun m => T0 (zs m))
    (fun m => tauAt L.a_le T0 B (ws m)) tm c (fun _ => uCo bas x) (fun _ => vCo bas x) _ h.c_pos
    (T_tendsto h hzs_lim) him hdec hYm (lower_at_centre h) hy'
  obtain ⟨m, hm⟩ := hev.exists
  have hvx : vCo bas x = v := hm.2
  rw [chartW, LinearMap.mem_ker, LinearMap.comp_apply, hvx, Matrix.mulVecLin_apply]
  exact hv

theorem limit_mem (h : IsChart L bas A T0 B c ρ) (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ)
    (hws : ∀ k, ws k ∈ logCover L.a_le)
    (hz : Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0))
    (hp : Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p)) :
    ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ := by
  obtain ⟨ρ', hρ', hρle, hdet⟩ := exists_ball_det h
  have hU : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ' := Metric.mem_ball_self hρ'
  have hq := tendsto_inv_mulVec h hz hp
  have key := GlobalTheory.CompanionTheory.PeriodLimit.limit_period n a g L.a_le (Metric.ball 0 ρ') T0 B c
    Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball (hρle.trans h.ρ_le))) h.B_psd h.c_pos
    (fun z hz => h.im_lower z (Metric.ball_subset_ball hρle hz)) 0 hU (fun _ => 0)
    (fun j hj => (hj rfl).elim) (fun _ _ => rfl) (((A 0)ᵀ)⁻¹ *ᵥ p)
  obtain ⟨u, v, hv, hw⟩ := key (mem_closure_of_tendsto (hz.prodMk_nhds hq) (by
    filter_upwards [hz.eventually (Metric.isOpen_ball.mem_nhds hU)] with k hk
    exact ⟨hk, fun j => ws k (Fin.castLE L.a_le j), uCo bas (x k), vCo bas (x k),
      fun j => exp_cast L.a_le (ws k) j, inv_period h hdet _ (hws k) hk (x k)⟩))
  simp only [zero_div, zero_smul, Finset.sum_const_zero, add_zero] at hw
  have hw' : ((A 0)ᵀ)⁻¹ *ᵥ p = cst u + T0 0 *ᵥ cst v := hw
  refine ⟨⟨mk bas u v, ?_⟩, ?_⟩
  · rw [chartW, LinearMap.mem_ker, LinearMap.comp_apply, vCo_mk, Matrix.mulVecLin_apply,
      Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun j _ => hv j rfl
  · show p = (A 0)ᵀ *ᵥ (cst (uCo bas (mk bas u v)) + T0 0 *ᵥ cst (vCo bas (mk bas u v)))
    rw [uCo_mk, vCo_mk, ← hw', Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Ne.isUnit (by rw [det_transpose]; exact h.A_det)),
      Matrix.one_mulVec]

theorem periods_at_centre : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 → (∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) → x ∈ chartW bas B) ∧ ∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨fun x t ht hP => extend_mem h x t ht hP, fun ws x p hws hz hp => limit_mem h ws x p hws hz hp⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorExpansionOfScaledProduct
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

theorem pos_cover (b : Fin (p + q)) : (∃ a, b = omEmb p q a) ∨ ∃ a, b = wEmb p q a := by
  rcases h : (blockEquiv p q).symm b with a | a
  · exact Or.inl ⟨a, (blockEquiv p q).symm.injective (h.trans (BlockEmbeddings.blockEquiv_symm_omEmb a).symm)⟩
  · exact Or.inr ⟨a, (blockEquiv p q).symm.injective (h.trans (BlockEmbeddings.blockEquiv_symm_wEmb a).symm)⟩

theorem aExt_posOf (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ) (j : Fin (n s))
    (l : Fin (rk Ψ p q s)) : aExt C s j (posOf p q s l) = C s j l := by
  have hi := (BlockEmbeddings.posOf_strictMono (p := p) (q := q) s).injective
  simp only [aExt]
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun e => hb (hi e)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_off (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ) (j : Fin (n s))
    (b : Fin (p + q)) (hb : ¬ ∃ l, posOf p q s l = b) : aExt C s j b = 0 :=
  Finset.sum_eq_zero fun l _ => if_neg fun e => hb ⟨l, e⟩

theorem tMat_posOf (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (s : Ψ ⊕ Ψ)
    (hs : s = .inl τ ∨ s = .inr τ) (l l' : Fin (rk Ψ p q s)) :
    tMat Ts τ (posOf p q s l) (posOf p q s l') = Ts s l l' := by
  rcases hs with rfl | rfl
  · exact BlockEmbeddings.blocks_wEmb _ _ l l'
  · exact BlockEmbeddings.blocks_omEmb _ _ l l'

theorem blocks_wEmb_omEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R)
    (a : Fin p) (b : Fin q) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (wEmb p q a) (omEmb p q b) =
      0 := by
  rw [Matrix.submatrix_apply, BlockEmbeddings.blockEquiv_symm_wEmb, BlockEmbeddings.blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₂₁]
  rfl

theorem blocks_omEmb_wEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R)
    (a : Fin q) (b : Fin p) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (omEmb p q a) (wEmb p q b) =
      0 := by
  rw [Matrix.submatrix_apply, BlockEmbeddings.blockEquiv_symm_wEmb, BlockEmbeddings.blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₁₂]
  rfl

theorem tMat_off (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (s : Ψ ⊕ Ψ)
    (hs : s = .inl τ ∨ s = .inr τ) (l : Fin (rk Ψ p q s)) (b : Fin (p + q))
    (hb : ¬ ∃ l', posOf p q s l' = b) : tMat Ts τ (posOf p q s l) b = 0 := by
  rcases hs with rfl | rfl
  · rcases pos_cover b with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact blocks_wEmb_omEmb _ _ l a
    · exact absurd ⟨a, rfl⟩ hb
  · rcases pos_cover b with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact absurd ⟨a, rfl⟩ hb
    · exact blocks_omEmb_wEmb _ _ l a

theorem aExt_mul_tMat (A C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (x : Ω) (m : Ψ ⊕ Ψ → ℕ)
    (hAT : ∀ s, A s * Ts s = (x ^ m s) • C s) (τ : Ψ) (s : Ψ ⊕ Ψ) (hs : s = .inl τ ∨ s = .inr τ) :
    aExt A s * tMat Ts τ = (x ^ m s) • aExt C s := by
  ext j b
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 := BlockEmbeddings.sum_aExt_mul A (RingHom.id Ω) s j (fun a => tMat Ts τ a b)
  simp only [RingHom.id_apply] at h1
  rw [h1]
  by_cases hb : ∃ l', posOf p q s l' = b
  · obtain ⟨l', rfl⟩ := hb
    have h2 := congrFun (congrFun (hAT s) j) l'
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h2
    rw [aExt_posOf, ← h2]
    exact Finset.sum_congr rfl fun l _ => by rw [tMat_posOf Ts τ s hs]
  · rw [aExt_off C s j b hb, mul_zero]
    exact Finset.sum_eq_zero fun l _ => by rw [tMat_off Ts τ s hs l b hb, mul_zero]

theorem sum_cMin_minorIJ (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (t : StepIx Ψ p q)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (G : Matrix (Fin (p + q)) (Fin (p + q)) Ω)
    (S : Finset (Fin (p + q))) (hS : S.card = (t.2 : ℕ) + 1) :
    ∑ I, cMin C t J I * minorIJ G I S =
      ((aExt C t.1).submatrix J id * G.submatrix id (S.orderEmbOfFin hS)).det := by
  rw [BlockEmbeddings.det_mul_cols _ _ S hS]
  rfl

theorem sum_cMin_tMat_mul (A C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (x : Ω) (m : Ψ ⊕ Ψ → ℕ)
    (hAT : ∀ s, A s * Ts s = (x ^ m s) • C s) (τ : Ψ) (t : StepIx Ψ p q) (hs : t.1 = .inl τ ∨ t.1 = .inr τ)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (h : Matrix (Fin (p + q)) (Fin (p + q)) Ω)
    (S : Finset (Fin (p + q))) (hS : S.card = (t.2 : ℕ) + 1) :
    ∑ I, cMin A t J I * minorIJ (tMat Ts τ * h) I S =
      x ^ (m t.1 * ((t.2 : ℕ) + 1)) * ∑ I, cMin C t J I * minorIJ h I S := by
  rw [sum_cMin_minorIJ A t J _ S hS, sum_cMin_minorIJ C t J _ S hS]
  have hm : (aExt A t.1).submatrix J id * (tMat Ts τ * h).submatrix id (S.orderEmbOfFin hS) =
      (x ^ m t.1) • ((aExt C t.1).submatrix J id * h.submatrix id (S.orderEmbOfFin hS)) := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← Matrix.mul_assoc, aExt_mul_tMat A C Ts x m hAT τ t.1 hs, Matrix.smul_mul]
    rfl
  rw [hm, Matrix.det_smul, Fintype.card_fin, pow_mul]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TMatBlockDiagDetFactors
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω]

theorem tMat_blockEquiv (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (a b : Fin q ⊕ Fin p) :
    tMat Ts τ (blockEquiv p q a) (blockEquiv p q b) =
      (Matrix.fromBlocks (Ts (.inr τ)) 0 0 (Ts (.inl τ)) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) Ω) a b := by
  simp [tMat]
  rfl

theorem omBlock_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    omBlock (tMat Ts τ) = Ts (.inr τ) := by
  ext a b
  exact tMat_blockEquiv Ts τ (.inl a) (.inl b)

theorem wBlock_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    wBlock (tMat Ts τ) = Ts (.inl τ) := by
  ext a b
  exact tMat_blockEquiv Ts τ (.inr a) (.inr b)

theorem isBlockDiag_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    IsBlockDiag p (tMat Ts τ) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
  rw [tMat_blockEquiv]
  rcases a with a | a <;> rcases b with b | b
  · exact absurd (by
      have h1 := a.2
      have h2 := b.2
      show ((a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p)
      omega) hab
  · rfl
  · rfl
  · exact absurd (by
      show (q + (a : ℕ) < p + q - p ↔ q + (b : ℕ) < p + q - p)
      omega) hab

theorem tMat_main {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω]
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    IsBlockDiag p (tMat Ts τ) ∧ (tMat Ts τ).det = (Ts (.inr τ)).det * (Ts (.inl τ)).det ∧
      ∀ i : Fin (p + q), detFac p i (tMat Ts τ) =
        (if p ≤ (i : ℕ) + 1 then (Ts (.inl τ)).det else 1) * (if (i : ℕ) + 1 = p + q then (Ts (.inr τ)).det else 1) := by
  refine ⟨isBlockDiag_tMat Ts τ, ?_, fun i => ?_⟩
  · have h := (isBlockDiag_tMat Ts τ).det_eq_blocks
    rw [omBlock_tMat, wBlock_tMat] at h
    exact h
  · have h1 : minorIJ (tMat Ts τ) (wIdx (p + q) p) (wIdx (p + q) p) = (Ts (.inl τ)).det := by
      rw [minorIJ_wIdx, wBlock_tMat]
      rfl
    have h2 : minorIJ (tMat Ts τ) (omIdx (p + q) p) (omIdx (p + q) p) = (Ts (.inr τ)).det := by
      rw [minorIJ_omIdx, omBlock_tMat]
      rfl
    rw [detFac, h1, h2]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

