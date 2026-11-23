module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZero
section
open Filter Topology

namespace GlobalTheory.CharSeriesCoef

noncomputable def avg {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y)
    (χ : AddChar Y ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ i, χ (w i)

theorem norm_avg_le_one_of {ι : Type} [Fintype ι] (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖(Fintype.card ι : ℂ)⁻¹ * ∑ i, f i‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · simp [h]
  have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast h
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hc, mul_one]
  calc ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum (fun i _ => hf i)
    _ = Fintype.card ι := by simp

theorem avg_prod {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y) (y : Y) (K : ℕ)
    (χ : AddChar Y ℂ) :
    avg (fun ik : ι × Fin K => w ik.1 + (ik.2 : ℕ) • y) χ
      = avg w χ * ((K : ℂ)⁻¹ * ∑ k : Fin K, χ y ^ (k : ℕ)) := by
  unfold avg
  rw [Fintype.sum_prod_type]
  simp only [AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [← Finset.sum_mul_sum, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [mul_inv]
  ring

theorem geom_avg_le {ζ : ℂ} (hζ : ζ ≠ 1) (h1 : ‖ζ‖ = 1) (K : ℕ) (hK : 0 < K) :
    ‖(K:ℂ)⁻¹ * ∑ k : Fin K, ζ ^ (k:ℕ)‖ ≤ 2 / (K * ‖ζ - 1‖) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ζ ^ k) K, geom_sum_eq hζ K]
  have hz : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ)
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hnum : ‖ζ ^ K - 1‖ ≤ 2 := by
    calc ‖ζ ^ K - 1‖ ≤ ‖ζ ^ K‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, h1]; norm_num
  rw [norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  calc (K:ℝ)⁻¹ * (‖ζ ^ K - 1‖ / ‖ζ - 1‖) ≤ (K:ℝ)⁻¹ * (2 / ‖ζ - 1‖) := by gcongr
    _ = 2 / (K * ‖ζ - 1‖) := by field_simp

theorem exists_avg {Y Ξ : Type} [AddCommGroup Y] [Zero Ξ] (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (δ : ℝ) (hδ : 0 < δ) (T : Finset Ξ) (h0 : (0:Ξ) ∉ T) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (w : ι → Y),
      ∀ b ∈ T, ‖avg w (e b)‖ ≤ δ := by
  classical
  revert h0
  refine Finset.induction_on T ?_ ?_
  · intro _
    exact ⟨Unit, inferInstance, inferInstance, fun _ => 0, by simp⟩
  · intro a T ha ih h0
    have ha0 : a ≠ 0 := fun h => h0 (by simp [h])
    have hT0 : (0:Ξ) ∉ T := fun h => h0 (Finset.mem_insert_of_mem h)
    obtain ⟨ι, _, _, w, hw⟩ := ih hT0
    obtain ⟨y, hy⟩ := hne a ha0
    have hz : 0 < ‖e a y - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / (δ * ‖e a y - 1‖))
    have hK0 : (0:ℝ) < K := lt_trans (by positivity) hK
    have hKn : 0 < K := by exact_mod_cast hK0
    haveI : Nonempty (Fin K) := ⟨⟨0, hKn⟩⟩
    refine ⟨ι × Fin K, inferInstance, inferInstance,
      fun ik => w ik.1 + (ik.2 : ℕ) • y, ?_⟩
    intro b hb
    rw [avg_prod, norm_mul]
    have hA : ‖avg w (e b)‖ ≤ 1 := norm_avg_le_one_of _ (fun i => (hn b _).le)
    have hG : ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 := by
      have := norm_avg_le_one_of (ι := Fin K) (fun k => e b y ^ (k:ℕ))
        (fun k => by rw [norm_pow, hn]; simp)
      simpa using this
    rcases Finset.mem_insert.mp hb with rfl | hbT
    · have hg := geom_avg_le hy (hn b y) K hKn
      have : 2 / (K * ‖e b y - 1‖) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ (by positivity)] at hK
        nlinarith
      calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 * δ := by
            gcongr
            exact hg.trans this
        _ = δ := one_mul δ
    · calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ δ * 1 := by
            gcongr
            exact hw b hbT
        _ = δ := mul_one δ

theorem continuousAt_coef_zero {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P]
    (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (he0 : ∀ y, e 0 y = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ) (hM : Summable M)
    (hb : ∀ᶠ p in 𝓝 p0, ∀ a, ‖c p a‖ ≤ M a)
    (hc : ∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) :
    ContinuousAt (fun p => c p 0) p0 := by
  classical
  have hM0 : ∀ a, 0 ≤ M a := fun a => (norm_nonneg _).trans (hb.self_of_nhds a)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set S := ∑' a, M a with hSdef
  have hS : 0 ≤ S := tsum_nonneg hM0
  obtain ⟨s, hs⟩ : ∃ s : Finset Ξ, S - ∑ a ∈ s, M a < ε / 6 := by
    have h2 := (Metric.tendsto_nhds.mp hM.hasSum) (ε / 6) (by positivity)
    obtain ⟨s, hs⟩ := h2.exists
    refine ⟨s, ?_⟩
    rw [Real.dist_eq] at hs
    linarith [neg_abs_le (∑ a ∈ s, M a - S)]
  set δ := ε / 6 / (S + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδS : δ * S ≤ ε / 6 := by
    have : δ * (S + 1) = ε / 6 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨ι, _, _, w, hw⟩ := exists_avg e hn hne δ hδ (s.erase 0) (by simp)
  set α : Ξ → ℂ := fun b => avg w (e b) with hαdef
  have hα1 : ∀ b, ‖α b‖ ≤ 1 := fun b => norm_avg_le_one_of _ (fun i => (hn b _).le)
  have hα0 : α 0 = 1 := by
    simp only [hαdef, avg, he0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  let A : P → ℂ := fun p => (Fintype.card ι : ℂ)⁻¹ * ∑ i, ∑' a, e a (w i) * c p a
  have hAc : ContinuousAt A p0 :=
    continuousAt_const.mul (tendsto_finsetSum _ (fun i _ => hc (w i)))

  have key : ∀ p, (∀ a, ‖c p a‖ ≤ M a) → ‖A p - c p 0‖ ≤ δ * S + (S - ∑ a ∈ s, M a) := by
    intro p hp
    have hsum : ∀ i, HasSum (fun a => e a (w i) * c p a) (∑' a, e a (w i) * c p a) := by
      intro i
      refine (Summable.of_norm_bounded hM (fun a => ?_)).hasSum
      rw [norm_mul, hn, one_mul]; exact hp a
    have h1 : HasSum (fun a => α a * c p a) (A p) := by
      have := (hasSum_sum (s := Finset.univ) (fun i _ => hsum i)).mul_left
        ((Fintype.card ι : ℂ)⁻¹)
      have hfun : (fun a => α a * c p a)
          = fun a => (Fintype.card ι : ℂ)⁻¹ * ∑ i, e a (w i) * c p a := by
        funext a
        simp only [hαdef, avg, Finset.sum_mul, mul_assoc]
      rw [hfun]; exact this
    have h2 : HasSum (fun a : Ξ => if a = (0:Ξ) then c p 0 else 0) (c p 0) := hasSum_ite_eq (0:Ξ) (c p 0)
    have h3 : HasSum (fun a => α a * c p a - if a = 0 then c p 0 else 0) (A p - c p 0) :=
      HasSum.sub h1 h2
    have hg : HasSum (fun a => δ * M a + (M a - if a ∈ s then M a else 0))
        (δ * S + (S - ∑ a ∈ s, M a)) := by
      refine (hM.hasSum.mul_left δ).add (hM.hasSum.sub ?_)
      have : HasSum (fun a => if a ∈ s then M a else 0) (∑ b ∈ s, if b ∈ s then M b else 0) :=
        hasSum_sum_of_ne_finset_zero (fun b hb => if_neg hb)
      have e2 : (∑ b ∈ s, if b ∈ s then M b else 0) = ∑ b ∈ s, M b :=
        Finset.sum_congr rfl (fun b hb => if_pos hb)
      rw [e2] at this
      exact this
    refine h3.norm_le_of_bounded hg (fun a => ?_)
    have hMa := hM0 a
    by_cases ha : a = 0
    · subst ha
      simp only [hα0, one_mul, if_true, sub_self, norm_zero]
      split_ifs <;> nlinarith [mul_nonneg hδ.le hMa]
    · simp only [ha, if_false, sub_zero]
      by_cases has : a ∈ s
      · simp only [has, if_true, sub_self, add_zero]
        rw [norm_mul]
        have := hw a (Finset.mem_erase.mpr ⟨ha, has⟩)
        exact mul_le_mul this (hp a) (norm_nonneg _) hδ.le
      · simp only [has, if_false, sub_zero]
        rw [norm_mul]
        have : ‖α a‖ * ‖c p a‖ ≤ 1 * M a := mul_le_mul (hα1 a) (hp a) (norm_nonneg _) zero_le_one
        nlinarith
  have hAev := (Metric.tendsto_nhds.mp hAc) (ε / 3) (by positivity)
  have hp0 := key p0 hb.self_of_nhds
  filter_upwards [hb, hAev] with p hp hAp
  have hpk := key p hp
  rw [dist_eq_norm] at hAp ⊢
  have : c p 0 - c p0 0 = -(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0) := by ring
  rw [this]
  calc ‖-(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0)‖
      ≤ ‖-(A p - c p 0)‖ + ‖A p - A p0‖ + ‖A p0 - c p0 0‖ := norm_add₃_le
    _ < ε := by rw [norm_neg]; linarith

end GlobalTheory.CharSeriesCoef

theorem GlobalTheory.continuousAt_charSeries_coef_zero :
    ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 :=
  fun e hn he0 hne c p0 M hM hb hc =>
    GlobalTheory.CharSeriesCoef.continuousAt_coef_zero e hn he0 hne c p0 M hM hb hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
section
noncomputable section

open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform

namespace GlobalTheory.RealWeil

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def gau (u : V) : ℂ := cexp (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2)

def IsHeis (om : V → V → ℝ) (ρ : V → B →L[ℂ] B) : Prop :=
  (∀ f, ρ 0 f = f) ∧ (∀ u v f, ρ u (ρ v f) = cexp (π * I * (om u v : ℂ)) • ρ (u + v) f) ∧
    (∀ u f, ‖ρ u f‖ = ‖f‖) ∧ ∀ f, Continuous fun u => ρ u f

def Sm (ρ : V → B →L[ℂ] B) (f : B) : Prop := ContDiff ℝ ∞ fun v => ρ v f

def IsOsc (ρ : V → B →L[ℂ] B) {G : Type} [Group G] (k : G → V → V) (Ω : G → B → B) : Prop :=
  (∀ g f f', Sm ρ f → Sm ρ f' → Ω g (f + f') = Ω g f + Ω g f') ∧
  (∀ g (a : ℂ) f, Sm ρ f → Ω g (a • f) = a • Ω g f) ∧
  (∀ g f, Sm ρ f → Sm ρ (Ω g f)) ∧
  (∀ f, Sm ρ f → Ω 1 f = f) ∧
  (∀ g g' f, Sm ρ f → Ω (g * g') f = Ω g (Ω g' f)) ∧
  (∀ g v f, Sm ρ f → Ω g (ρ v f) = ρ (k g v) (Ω g f)) ∧
  (∀ g (A : B →L[ℂ] B), (∀ v f, A (ρ v f) = ρ v (A f)) → ∀ f, Sm ρ f → Ω g (A f) = A (Ω g f)) ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H),
    (∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) → ∀ g f, Sm ρ f → ‖Φ (Ω g f)‖ = ‖Φ f‖

theorem norm_gau (u : V) : ‖gau u‖ = Real.exp (-(π / 2) * ‖u‖ ^ 2) := by
  unfold gau
  rw [Complex.norm_exp]
  congr 1
  have : (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2) = ((-(π / 2) * ‖u‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ofReal_re]

theorem gau_ne_zero (u : V) : gau u ≠ 0 := Complex.exp_ne_zero _

theorem gau_zero : gau (0 : V) = 1 := by simp [gau]

theorem gau_neg (u : V) : gau (-u) = gau u := by simp [gau]

theorem continuous_gau : Continuous (gau : V → ℂ) := by unfold gau; fun_prop

theorem IsHeis.twist {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) (g : V →L[ℝ] V)
    (hg : ∀ x y, om (g x) (g y) = om x y) : IsHeis om fun v => ρ (g v) :=
  ⟨fun f => by simp only [map_zero, h.1], fun u v f => by simp only [h.2.1, hg, map_add (f := _)], fun u f => h.2.2.1 _ f,
    fun f => (h.2.2.2 f).comp g.continuous⟩

theorem IsHeis.continuous {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) {Y : Type} [TopologicalSpace Y]
    {a : Y → V} {x : Y → B} (ha : Continuous a) (hx : Continuous x) : Continuous fun y => ρ (a y) (x y) := by
  have : Continuous fun p : B × V => ρ p.2 p.1 :=
    continuous_prod_of_continuous_lipschitzWith (fun p : B × V => ρ p.2 p.1) 1
      (fun f => h.2.2.2 f) fun v => LipschitzWith.of_dist_le_mul fun x y => by
        simp only [dist_eq_norm, ← map_sub, h.2.2.1]; simp
  exact this.comp (hx.prodMk ha)

end General

def dP {ι : Type} [Fintype ι] [DecidableEq ι] (s g : Matrix ι ι ℂ) : ℂ :=
  ((1 / 2 : ℂ) • ((1 + s) * g) + (1 / 2 : ℂ) • (1 - s)).det

section Inner

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

def omJ (J : V ≃ₗᵢ[ℝ] V) (x y : V) : ℝ := ⟪x, J y⟫

def lam (g : V → V) : ℂ := ∫ u, gau u * gau (g u)

def mu (J : V ≃ₗᵢ[ℝ] V) (g₁ g₂ : V → V) : ℂ :=
  ∫ u, ∫ v, gau u * gau v * (cexp (π * I * (omJ J (g₁ u) (g₂ v) : ℂ)) * gau (g₁ u + g₂ v))

theorem integrable_gau : Integrable (gau : V → ℂ) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (π / 2 : ℂ)) (by simpa using Real.pi_pos) 0 0
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [gau]

variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}

omit [CompleteSpace B] in
theorem IsHeis.integrable (h : IsHeis om ρ) (f : B) : Integrable fun u => gau u • ρ u f := by
  refine Integrable.mono' ((integrable_gau (V := V)).norm.mul_const ‖f‖)
    (continuous_gau.smul (h.2.2.2 f)).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_smul, h.2.2.1]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace B] in
theorem IsHeis.continuous_gau_smul (h : IsHeis om ρ) (f : B) : Continuous fun u => gau u • ρ u f :=
  continuous_gau.smul (h.2.2.2 f)

def proj (h : IsHeis om ρ) : B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u, gau u • ρ u f
      map_add' := fun f f' => by
        rw [← integral_add (h.integrable f) (h.integrable f')]
        simp only [map_add (f := _), smul_add]
      map_smul' := fun a f => by
        rw [RingHom.id_apply, ← integral_smul]
        simp only [map_smul, smul_comm a] }
    (∫ u : V, ‖gau u‖) fun f => by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp only [norm_smul, h.2.2.1]
      rw [integral_mul_const]

omit [CompleteSpace B] in
theorem proj_apply (h : IsHeis om ρ) (f : B) : proj h f = ∫ u, gau u • ρ u f := rfl

def Good (h : IsHeis om ρ) (f : B) : Prop := ∀ n : ℕ, Integrable fun w => ‖w‖ ^ n * ‖proj h (ρ (-w) f)‖

variable {J : V ≃ₗᵢ[ℝ] V}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem omJ_skew (hJ : ∀ x, J (J x) = -x) (x y : V) : omJ J y x = -omJ J x y := by
  unfold omJ
  rw [← J.inner_map_map, hJ, inner_neg_right, real_inner_comm]

theorem proj_translate (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (w : V) :
    proj h (ρ (-w) f) = ρ (-w) (𝓕 (fun u => gau u • ρ u f) (J w)) := by
  rw [proj_apply, Real.fourier_eq', ← ContinuousLinearMap.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [map_smul, h.2.1, smul_smul]
    rw [add_comm (-w) u, omJ_skew hJ u (-w)]
    congr 1
    have e : omJ J u (-w) = -⟪u, J w⟫ := by simp [omJ]
    rw [e, mul_right_comm _ (gau u), ← Complex.exp_add, mul_comm]
    congr 2
    push_cast
    ring
  · have := (Real.fourierIntegral_convergent_iff (J w)).2 (h.integrable f)
    simpa only [Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul, Complex.ofReal_neg] using this

theorem Good.fourier (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) (n : ℕ) :
    Integrable fun w => ‖w‖ ^ n * ‖𝓕 (fun u => gau u • ρ u f) w‖ := by
  have := hf n
  simp only [proj_translate hJ, h.2.2.1] at this
  rw [← J.measurePreserving.integrable_comp_emb J.toHomeomorph.measurableEmbedding]
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  simp

theorem continuous_fourier_gau (h : IsHeis om ρ) (f : B) : Continuous (𝓕 fun u => gau u • ρ u f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (h.integrable f)

theorem Good.integrable_fourier (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    Integrable (𝓕 fun u => gau u • ρ u f) := by
  have := hf.fourier hJ 0
  simp only [pow_zero, one_mul] at this
  exact (integrable_norm_iff (continuous_fourier_gau h f).aestronglyMeasurable).1 this

theorem Good.inversion (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    ∫ w, ρ w (proj h (ρ (-w) f)) = f := by
  have e : ∀ w, ρ w (proj h (ρ (-w) f)) = 𝓕 (fun u => gau u • ρ u f) (J w) := by
    intro w
    have h0 : omJ J w (-w) = 0 := by
      have := omJ_skew hJ w w
      have e : omJ J w (-w) = -omJ J w w := by simp [omJ]
      linarith
    rw [proj_translate hJ, h.2.1, h0, add_neg_cancel, h.1]
    simp
  simp only [e]
  rw [J.measurePreserving.integral_comp J.toHomeomorph.measurableEmbedding]
  have := congrFun ((h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f)
    (hf.integrable_fourier hJ)) 0
  rw [Real.fourierInv_eq] at this
  simpa [gau_zero, h.1] using this

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem contDiff_gau_inv : ContDiff ℝ ∞ fun u : V => (gau u)⁻¹ := by
  have : (fun u : V => (gau u)⁻¹) = fun u => cexp ((π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    rw [gau, ← Complex.exp_neg]
    push_cast
    ring_nf
  rw [this]
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ)))

theorem Good.sm (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) : Sm ρ f := by
  have h1 := (h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f) (hf.integrable_fourier hJ)
  have h2 : ContDiff ℝ ∞ (𝓕 (𝓕 fun u => gau u • ρ u f)) := Real.contDiff_fourier fun n _ => hf.fourier hJ n
  have h3 : ContDiff ℝ ∞ fun u => gau u • ρ u f := by
    rw [← h1]
    have : 𝓕⁻ (𝓕 fun u => gau u • ρ u f) = fun u => 𝓕 (𝓕 fun u => gau u • ρ u f) (-u) := by
      funext u; rw [Real.fourierInv_eq_fourier_neg]
    rw [this]
    exact h2.comp contDiff_neg
  have : ContDiff ℝ ∞ fun u => (gau u)⁻¹ • gau u • ρ u f := (contDiff_gau_inv (V := V)).smul h3
  simpa only [smul_smul, inv_mul_cancel₀ (gau_ne_zero _), one_smul, Sm] using this

end Inner

end GlobalTheory.RealWeil

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCoordsOfLinearIndependent
section
open Filter Topology

namespace GlobalTheory

open Matrix

noncomputable def realDotC {g : ℕ} (u w : Fin g → ℂ) : ℝ :=
  ∑ k, ((u k).re * (w k).re + (u k).im * (w k).im)

lemma realDotC_comm {g : ℕ} (u w : Fin g → ℂ) : realDotC u w = realDotC w u := by
  unfold realDotC; refine Finset.sum_congr rfl (fun k _ => ?_); ring

lemma realDotC_sum_right {g m : ℕ} (u : Fin g → ℂ) (x : Fin m → ℝ) (μ : Fin m → Fin g → ℂ) :
    realDotC u (∑ i, x i • μ i) = ∑ i, x i * realDotC u (μ i) := by
  unfold realDotC
  simp only [Finset.sum_apply, Pi.smul_apply, Complex.re_sum, Complex.im_sum, Complex.smul_re,
    Complex.smul_im, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)); ring

lemma realDotC_self_eq_zero {g : ℕ} (u : Fin g → ℂ) (h : realDotC u u = 0) : u = 0 := by
  unfold realDotC at h
  have hn : ∀ k ∈ Finset.univ, 0 ≤ (u k).re * (u k).re + (u k).im * (u k).im :=
    fun k _ => by nlinarith [sq_nonneg (u k).re, sq_nonneg (u k).im]
  rw [Finset.sum_eq_zero_iff_of_nonneg hn] at h
  funext k
  have hk := h k (Finset.mem_univ _)
  apply Complex.ext <;> simp <;> nlinarith [sq_nonneg (u k).re, sq_nonneg (u k).im]

theorem continuousOn_coords_of_linearIndependent :
    ∀ (g m : ℕ) (U : Set ℂ) (μ : ℂ → Fin m → Fin g → ℂ) (v : ℂ → Fin g → ℂ) (c : ℂ → Fin m → ℝ),
      ContinuousOn μ U → ContinuousOn v U → (∀ s ∈ U, LinearIndependent ℝ (μ s)) →
      (∀ s ∈ U, v s = ∑ i, c s i • μ s i) → ContinuousOn c U := by
  intro g m U μ v c hμ hv hli hc
  rw [continuousOn_iff_continuous_restrict] at hμ hv ⊢
  let G : U → Matrix (Fin m) (Fin m) ℝ := fun s a b => realDotC (μ s a) (μ s b)
  let b : U → Fin m → ℝ := fun s a => realDotC (μ s a) (v s)
  have hdot : Continuous (fun p : (Fin g → ℂ) × (Fin g → ℂ) => realDotC p.1 p.2) := by
    unfold realDotC; fun_prop
  have hμa : ∀ a, Continuous (fun s : U => μ s a) := fun a => (continuous_apply a).comp hμ
  have hGc : Continuous G :=
    continuous_pi (fun a => continuous_pi (fun b' => hdot.comp ((hμa a).prodMk (hμa b'))))
  have hbc : Continuous b := continuous_pi (fun a => hdot.comp ((hμa a).prodMk hv))
  have hGc_eq : ∀ s : U, G s *ᵥ (c s) = b s := by
    intro s; funext a
    simp only [G, b, Matrix.mulVec, dotProduct]
    rw [hc s s.2, realDotC_sum_right]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
  have hdet : ∀ s : U, (G s).det ≠ 0 := by
    intro s hd
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    apply hx0
    have hw : ∑ i, x i • μ s i = 0 := by
      apply realDotC_self_eq_zero
      rw [realDotC_sum_right]
      have key : ∀ i, realDotC (μ s i) (∑ j, x j • μ s j) = (G s *ᵥ x) i := by
        intro i; rw [realDotC_sum_right]; simp only [G, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl (fun j _ => ?_); ring
      simp_rw [realDotC_comm _ (μ s _), key, hx]; simp
    funext i
    exact Fintype.linearIndependent_iff.mp (hli s s.2) x hw i
  have hceq : U.domRestrict c = fun s => ((G s).det)⁻¹ • ((G s).adjugate *ᵥ b s) := by
    funext s
    have h1 : c s = (G s)⁻¹ *ᵥ b s := by
      rw [← hGc_eq s, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet s)), Matrix.one_mulVec]
    show c s = _
    rw [h1, Matrix.inv_def, Ring.inverse_eq_inv']
    ext a; simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Finset.mul_sum, mul_assoc]
  rw [hceq]
  exact (hGc.matrix_det.inv₀ hdet).smul (hGc.matrix_adjugate.matrix_mulVec hbc)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeEmbeddingPi
section
namespace GlobalTheory.DenseEmbeddingProduct

open NumberField NumberField.InfinitePlace

theorem denseRange_embedding_pi {E : Type} [Field E] [NumberField E] [IsCMField E] :
    DenseRange fun (x : E) (w : InfinitePlace E) ↦ (InfinitePlace.embedding w : E → ℂ) x := by
  let Φ : InfiniteAdeleRing E → (InfinitePlace E → ℂ) :=
    fun y w ↦ Completion.extensionEmbedding w (y w)
  have hc : Continuous Φ := continuous_pi fun w ↦
    (Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have hs : Function.Surjective Φ := by
    intro f
    choose y hy using fun w : InfinitePlace E ↦
      Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (f w)
    exact ⟨y, funext hy⟩
  have h := hs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc
  convert h using 1
  funext x w
  simp [Φ]

end GlobalTheory.DenseEmbeddingProduct
end

