module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsIntegralSubConstMulLeOfSplit
section
open MeasureTheory

namespace GlobalTheory

theorem abs_integral_sub_const_mul_le_of_split :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (M : Set X) (K : X → ℝ) (nr fr : X → ENNReal) (c a b e : ℝ), MeasurableSet M → Integrable K μ → (∀ x, 0 ≤ K x) → Measurable nr → 0 ≤ c → 0 ≤ a → 0 ≤ b → 0 ≤ e → (∀ x ∈ M, ENNReal.ofReal |K x - c| ≤ nr x + fr x) → ∫⁻ x in M, nr x ∂μ ≤ ENNReal.ofReal a → ∫⁻ x in M, fr x ∂μ ≤ ENNReal.ofReal b → ∫⁻ x in Mᶜ, ENNReal.ofReal (K x) ∂μ ≤ ENNReal.ofReal e → |∫ x, K x ∂μ - c * (μ Set.univ).toReal| ≤ a + b + c * (μ Mᶜ).toReal + e := by
  intro X _ μ _ M K nr fr c a b e hM hK hK0 hnr hc ha hb he hpt hna hfb hce
  have hsplit : ∫ x, K x ∂μ = ∫ x in M, K x ∂μ + ∫ x in Mᶜ, K x ∂μ :=
    (integral_add_compl hM hK).symm
  have hmeas : (μ Set.univ).toReal = (μ M).toReal + (μ Mᶜ).toReal := by
    rw [← measure_add_measure_compl hM,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hintM : ∫ x in M, (K x - c) ∂μ = ∫ x in M, K x ∂μ - c * (μ M).toReal := by
    rw [integral_sub hK.integrableOn (integrable_const c), setIntegral_const, smul_eq_mul,
      measureReal_def, mul_comm]

  have h1 : |∫ x in M, (K x - c) ∂μ| ≤ a + b := by
    have hle : ∫⁻ x in M, ENNReal.ofReal ‖K x - c‖ ∂μ ≤ ENNReal.ofReal (a + b) := by
      calc ∫⁻ x in M, ENNReal.ofReal ‖K x - c‖ ∂μ ≤ ∫⁻ x in M, (nr x + fr x) ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hM] with x hx
            simpa [Real.norm_eq_abs] using hpt x hx
        _ = ∫⁻ x in M, nr x ∂μ + ∫⁻ x in M, fr x ∂μ := lintegral_add_left hnr _
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal b := add_le_add hna hfb
        _ = ENNReal.ofReal (a + b) := (ENNReal.ofReal_add ha hb).symm
    have hn := norm_integral_le_lintegral_norm (μ := μ.restrict M) (fun x => K x - c)
    rw [Real.norm_eq_abs] at hn
    exact hn.trans (ENNReal.toReal_le_of_le_ofReal (add_nonneg ha hb) hle)

  have h2 : ∫ x in Mᶜ, K x ∂μ ≤ e := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hK0)
      hK.integrableOn.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal he hce
  have h3 : 0 ≤ ∫ x in Mᶜ, K x ∂μ := integral_nonneg fun x => hK0 x
  have h4 : 0 ≤ c * (μ Mᶜ).toReal := mul_nonneg hc ENNReal.toReal_nonneg
  have key : ∫ x, K x ∂μ - c * (μ Set.univ).toReal =
      ∫ x in M, (K x - c) ∂μ + (∫ x in Mᶜ, K x ∂μ - c * (μ Mᶜ).toReal) := by
    rw [hsplit, hmeas, hintM]; ring
  rw [key]
  calc _ ≤ |∫ x in M, (K x - c) ∂μ| + |∫ x in Mᶜ, K x ∂μ - c * (μ Mᶜ).toReal| := abs_add_le _ _
    _ ≤ (a + b) + (c * (μ Mᶜ).toReal + e) := by
        gcongr
        rw [abs_le]; constructor <;> linarith
    _ = a + b + c * (μ Mᶜ).toReal + e := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsOpIntIntegrable
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem absOpInt_integrable {G : Type} [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {Hp : Type} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun g => π g x) (φ : G → ℂ) (hφ : Integrable φ μ) (y : Hp) :
    Integrable (fun g => φ g • π g y) μ := by
  refine Integrable.mono' (hφ.norm.mul_const ‖y‖) ?_ (ae_of_all _ fun g => ?_)
  · exact hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable
  · rw [norm_smul, hn]

theorem absOpInt : ∀ (G : Type) [Group G] [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) → ∀ φ : G → ℂ, Integrable φ μ → ∃ P : Hp →L[ℂ] Hp, (∀ y, P y = ∫ g, φ g • π g y ∂μ) ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ := by
  intro G _ _ _ _ _ μ Hp _ _ _ π hn hc φ hφ
  let L : Hp →ₗ[ℂ] Hp :=
    { toFun := fun y => ∫ g, φ g • π g y ∂μ
      map_add' := fun y z => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (absOpInt_integrable μ π hn hc φ hφ y)
          (absOpInt_integrable μ π hn hc φ hφ z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        simp_rw [smul_comm (φ _) c]
        exact integral_smul c _ }
  refine ⟨L.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun y => rfl, fun x y => ?_⟩
  · calc ‖L y‖ = ‖∫ g, φ g • π g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • π g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by simp_rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · change ⟪x, ∫ g, φ g • π g y ∂μ⟫_ℂ = _
    rw [← integral_inner (absOpInt_integrable μ π hn hc φ hφ y)]
    simp_rw [inner_smul_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsSubLeExpNegSixteenthMul
section
open Matrix Finset Real

namespace GlobalTheory

theorem abs_sub_le_exp_neg_sixteenth_mul :
    ∀ (D Ds n f : ℝ), 0 ≤ D → 0 ≤ Ds → Real.exp 15 ≤ n → 1 ≤ f → |D - Ds| ≤ (2 * Real.exp (-(1 / 4) * n * f * Real.log n) + Real.exp (-n ^ 2 * f)) * Ds + Real.exp (-n ^ 2 * f) * D → |D - Ds| ≤ Real.exp (-(1 / 16) * n * f * Real.log n) * Ds := by
  intro D Ds n f hD hDs hn hf h
  have hn16 : (16:ℝ) ≤ n := by
    have := Real.add_one_le_exp (15:ℝ); linarith
  have hn0 : 0 < n := by linarith
  have hL : 15 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 15) hn
    rwa [Real.log_exp] at this
  have hLn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn0; linarith
  have hnf : 16 ≤ n * f := by nlinarith
  have ha : 240 ≤ n * f * Real.log n := by nlinarith
  have hnn : n * f * Real.log n ≤ n ^ 2 * f := by
    have := mul_le_mul_of_nonneg_left hLn (by linarith : (0:ℝ) ≤ n * f)
    nlinarith
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8); linarith
  have hT8 : Real.exp (-(1 / 16) * n * f * Real.log n - Real.log 8) =
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  have e1 : Real.exp (-(1 / 4) * n * f * Real.log n) ≤
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have e2 : Real.exp (-n ^ 2 * f) ≤ Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have hT1 : Real.exp (-(1 / 16) * n * f * Real.log n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; nlinarith
  have hδ0 : 0 ≤ Real.exp (-n ^ 2 * f) := (Real.exp_pos _).le
  have hδ : Real.exp (-n ^ 2 * f) ≤ 1 / 2 := by linarith
  have hX : 0 ≤ |D - Ds| := abs_nonneg _
  have hD' : D ≤ Ds + |D - Ds| := by have := le_abs_self (D - Ds); linarith
  have p1 := mul_le_mul_of_nonneg_left hD' hδ0
  have p2 := mul_le_mul_of_nonneg_right hδ hX
  have p3 := mul_le_mul_of_nonneg_right e1 hDs
  have p4 := mul_le_mul_of_nonneg_right e2 hDs
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AeEqOfDenseOfLocalSqBound
section
open MeasureTheory

namespace GlobalTheory

theorem ae_eq_of_dense_of_local_sq_bound : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set H), Dense D → ∀ P Q : H → X → E,
    (∀ u u', (fun x => P u x - P u' x) =ᵐ[μ] P (u - u')) →
    (∀ u u', (fun x => Q u x - Q u' x) =ᵐ[μ] Q (u - u')) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (P u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖P u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (Q u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖Q u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ u ∈ D, P u =ᵐ[μ] Q u) → ∀ u, P u =ᵐ[μ] Q u := by
  intro X _ μ K _hK hcov H _ _ E _ _ D hD P Q hP hQ hPb hQb hPQ u
  have key : ∀ n, ∀ᵐ x ∂μ.restrict (K n), P u x = Q u x := by
    intro n
    obtain ⟨CP, hCP⟩ := hPb n
    obtain ⟨CQ, hCQ⟩ := hQb n
    have hmeas : AEMeasurable (fun x => ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2) (μ.restrict (K n)) :=
      (((hCP u).1.sub (hCQ u).1).nnnorm.aemeasurable.coe_nnreal_ennreal).pow_const 2
    set M : ℝ := 2 * (|CP| + |CQ|) with hM
    have hbound : ∀ δ : ℝ, 0 < δ →
        ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) ≤ ENNReal.ofReal (M * δ ^ 2) := by
      intro δ hδ
      obtain ⟨u', hu'D, hdist⟩ := hD.exists_dist_lt u hδ
      have hwδ : ‖u - u'‖ ^ 2 ≤ δ ^ 2 := by
        have : ‖u - u'‖ < δ := by rw [← dist_eq_norm]; exact hdist
        exact pow_le_pow_left₀ (norm_nonneg _) this.le 2
      have hae : ∀ᵐ x ∂(μ.restrict (K n)), ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ≤
          2 * ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2 := by
        have h1 := ae_restrict_of_ae (s := K n) (hP u u')
        have h2 := ae_restrict_of_ae (s := K n) (hQ u u')
        have h3 := ae_restrict_of_ae (s := K n) (hPQ u' hu'D)
        filter_upwards [h1, h2, h3] with x e1 e2 e3
        have e1' : P u x - P u' x = P (u - u') x := e1
        have e2' : Q u x - Q u' x = Q (u - u') x := e2
        have e3' : P u' x = Q u' x := e3
        have e : P u x - Q u x = P (u - u') x - Q (u - u') x := by
          have : P u x - Q u x = (P u x - P u' x) - (Q u x - Q u' x) + (P u' x - Q u' x) := by abel
          rw [this, e1', e2', e3', sub_self, add_zero]
        rw [e]
        have hn : ‖P (u - u') x - Q (u - u') x‖₊ ≤ ‖P (u - u') x‖₊ + ‖Q (u - u') x‖₊ := nnnorm_sub_le _ _
        have hsq : ‖P (u - u') x - Q (u - u') x‖₊ ^ 2 ≤
            2 * ‖P (u - u') x‖₊ ^ 2 + 2 * ‖Q (u - u') x‖₊ ^ 2 := by
          have hn' : ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) ≤
              ((‖P (u - u') x‖₊ : NNReal) : ℝ) + ((‖Q (u - u') x‖₊ : NNReal) : ℝ) := by exact_mod_cast hn
          have h0 : (0:ℝ) ≤ ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) := NNReal.coe_nonneg _
          have hreal : ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) ^ 2 ≤
              2 * ((‖P (u - u') x‖₊ : NNReal) : ℝ) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : NNReal) : ℝ) ^ 2 := by
            nlinarith [sq_nonneg (((‖P (u - u') x‖₊ : NNReal) : ℝ) - ((‖Q (u - u') x‖₊ : NNReal) : ℝ))]
          exact_mod_cast hreal
        have := ENNReal.coe_le_coe.mpr hsq
        push_cast at this
        exact this
      calc ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n))
          ≤ ∫⁻ x, (2 * ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2)
              ∂(μ.restrict (K n)) := lintegral_mono_ae hae
        _ = 2 * ∫⁻ x, ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) +
              2 * ∫⁻ x, ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) := by
            rw [lintegral_add_left'
              (((hCP (u - u')).1.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2).const_mul 2),
              lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * ENNReal.ofReal (CP * ‖u - u'‖ ^ 2) + 2 * ENNReal.ofReal (CQ * ‖u - u'‖ ^ 2) := by
            gcongr
            · exact (hCP (u - u')).2
            · exact (hCQ (u - u')).2
        _ ≤ 2 * ENNReal.ofReal (|CP| * δ ^ 2) + 2 * ENNReal.ofReal (|CQ| * δ ^ 2) := by
            gcongr <;> first | exact le_abs_self _ | exact hwδ
        _ = ENNReal.ofReal (M * δ ^ 2) := by
            have : M * δ ^ 2 = 2 * (|CP| * δ ^ 2) + 2 * (|CQ| * δ ^ 2) := by rw [hM]; ring
            rw [this, ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            simp
    have hzero : ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) = 0 := by
      have hlim : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (M * δ ^ 2)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (ENNReal.ofReal (M * 0 ^ 2))) := by
        apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
        exact (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow 2))).tendsto 0
      have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall (fun δ hδ => hbound δ hδ))
      simpa using this
    have hae0 := (lintegral_eq_zero_iff' hmeas).mp hzero
    filter_upwards [hae0] with x hx
    have hx' : ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 = 0 := hx
    simpa [sub_eq_zero] using hx'
  have hall : ∀ᵐ x ∂μ.restrict (⋃ n, K n), P u x = Q u x :=
    (ae_restrict_iUnion_iff K (fun x => P u x = Q u x)).mpr key
  rw [hcov, Measure.restrict_univ] at hall
  exact hall

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep
section
open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise

namespace GlobalTheory.RightRegFund

variable {G : Type} [Group G]

def Good (Γ : Subgroup G) (D : Set G) (y : G) : Prop :=
  ∀ γ γ' : Γ, (γ : G) * y ∈ D → (γ' : G) * y ∈ D → γ = γ'

theorem Good.mul {Γ : Subgroup G} {D : Set G} {y : G} (h : Good Γ D y) (δ : Γ) :
    Good Γ D ((δ : G) * y) := by
  intro γ γ' h1 h2
  have := h (γ * δ) (γ' * δ) (by simpa [mul_assoc] using h1) (by simpa [mul_assoc] using h2)
  exact mul_right_cancel this

theorem good_mul_iff {Γ : Subgroup G} {D : Set G} {y : G} (δ : Γ) :
    Good Γ D ((δ : G) * y) ↔ Good Γ D y :=
  ⟨fun h => by simpa using h.mul δ⁻¹, fun h => h.mul δ⟩

variable {Γ : Subgroup G} {D : Set G} {r : G → G}

theorem rep_eq (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {y : G} (h : Good Γ D y)
    {γ : Γ} (hγ : (γ : G) * y ∈ D) : r y = γ * y := by
  obtain ⟨δ, h1, h2⟩ := hr y
  rw [h1, h δ γ (h1 ▸ h2) hγ]

theorem rep_mul (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {y : G} (h : Good Γ D y)
    (δ : Γ) : r ((δ : G) * y) = r y := by
  obtain ⟨γ, h1, h2⟩ := hr ((δ : G) * y)
  have : r y = ((γ * δ : Γ) : G) * y :=
    rep_eq hr h (by simpa [mul_assoc, ← h1] using h2)
  rw [this, h1]; simp [mul_assoc]

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]

theorem ae_good (hD : IsFundamentalDomain Γ D μ) : ∀ᵐ y ∂μ, Good Γ D y := by
  unfold Good
  refine ae_all_iff.2 fun γ => ae_all_iff.2 fun γ' => ?_
  by_cases h : γ = γ'
  · exact Eventually.of_forall fun _ _ _ => h
  · have h' : γ⁻¹ ≠ γ'⁻¹ := fun e => h (inv_injective e)
    have := hD.aedisjoint h'
    refine (measure_eq_zero_iff_ae_notMem.1 this).mono fun y hy h1 h2 => absurd ?_ hy
    refine ⟨?_, ?_⟩
    · exact mem_inv_smul_set_iff.2 h1
    · exact mem_inv_smul_set_iff.2 h2

theorem ae_rep (hDm : MeasurableSet D) (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    {p : G → Prop} (hp : ∀ᵐ x ∂(μ.restrict D), p x) : ∀ᵐ y ∂μ, p (r y) := by
  rw [ae_restrict_iff' hDm] at hp
  have : ∀ᵐ y ∂μ, ∀ γ : Γ, (γ : G) * y ∈ D → p (γ * y) :=
    ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae hp
  refine this.mono fun y hy => ?_
  obtain ⟨γ, h1, h2⟩ := hr y
  rw [h1] at h2 ⊢
  exact hy γ h2

theorem aestronglyMeasurable_comp_rep (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {f : G → ℂ} (hf : StronglyMeasurable f) :
    AEStronglyMeasurable (fun y => f (r y)) μ := by
  have hU : (⋃ γ : Γ, (fun y => (γ : G) * y) ⁻¹' D) = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨γ, h1, h2⟩ := hr y
    exact mem_iUnion.2 ⟨γ, by simpa [← h1] using h2⟩
  rw [← Measure.restrict_univ (μ := μ), ← hU, aestronglyMeasurable_iUnion_iff]
  intro γ
  have hm : Measurable fun y => (γ : G) * y := measurable_const_mul _
  refine ((hf.comp_measurable hm).aestronglyMeasurable).congr ?_
  refine (ae_restrict_iff' (hm hDm)).2 ((ae_good hD).mono fun y hy h => ?_)
  simp only [Function.comp]
  rw [rep_eq hr hy h]

theorem ae_rep_eq_self (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) : ∀ᵐ x ∂(μ.restrict D), r x = x := by
  refine (ae_restrict_iff' hDm).2 ((ae_good hD).mono fun y hy h => ?_)
  simpa using rep_eq hr hy (γ := 1) (by simpa using h)

variable [μ.IsMulRightInvariant]

theorem ae_good_mul (hD : IsFundamentalDomain Γ D μ) (g : G) : ∀ᵐ y ∂μ, Good Γ D (y * g) :=
  (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae (ae_good hD)

theorem lintegral_comp_rep_mul (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) (φ : G → ℝ≥0∞) (g : G) :
    ∫⁻ x in D, φ (r (x * g)) ∂μ = ∫⁻ x in D, φ x ∂μ := by
  classical
  let ψ : G → ℝ≥0∞ := fun y => if Good Γ D y then φ (r y) else 0
  have hψ : ∀ (γ : Γ) (y : G), ψ (γ • y) = ψ y := by
    intro γ y
    change ψ ((γ : G) * y) = ψ y
    by_cases h : Good Γ D y
    · simp only [ψ, if_pos h, if_pos (h.mul γ), rep_mul hr h]
    · simp only [ψ, if_neg h, if_neg (mt (good_mul_iff γ).1 h)]
  have hD' : IsFundamentalDomain Γ ((fun x => x * g⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => by
        change ((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)
        rw [mul_assoc]
  have h1 := (measurePreserving_mul_right μ g⁻¹).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulRight g⁻¹) (fun x => ψ (x * g)) D
  simp only [inv_mul_cancel_right] at h1
  calc ∫⁻ x in D, φ (r (x * g)) ∂μ = ∫⁻ x in D, ψ (x * g) ∂μ :=
        lintegral_congr_ae (ae_restrict_of_ae ((ae_good_mul hD g).mono fun y hy => by
          simp only [ψ, if_pos hy]))
    _ = ∫⁻ x in D, ψ x ∂μ := by rw [← h1]; exact hD'.setLIntegral_eq hD ψ hψ
    _ = ∫⁻ x in D, φ x ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (ae_good hD), ae_rep_eq_self hD hDm hr] with y hy h2
        simp only [ψ, if_pos hy, h2]

variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}

theorem map_one (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) : R 1 = 1 := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [hR 1 F, ae_rep_eq_self hD hDm hr] with x h1 h2
  rw [h1, mul_one, h2]; rfl

theorem map_mul (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) (g h : G) :
    R (g * h) = R g * R h := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  have h1 : ∀ᵐ y ∂μ, (R h F : G → ℂ) (r y) = F (r (y * h)) := by
    filter_upwards [ae_rep hDm hr (hR h F), ae_good_mul hD h] with y e1 e2
    obtain ⟨γ, e3, -⟩ := hr y
    rw [e1, e3, mul_assoc, rep_mul hr e2]
  have h2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1
  filter_upwards [hR (g * h) F, hR g (R h F), ae_restrict_of_ae h2] with x e1 e2 e3
  rw [e1, ContinuousLinearMap.mul_apply, e2, e3, mul_assoc]

theorem norm_map (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) (g : G)
    (F : Lp ℂ 2 (μ.restrict D)) : ‖R g F‖ = ‖F‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hR g F),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      ((Lp.aestronglyMeasurable (R g F)).congr (hR g F)),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (Lp.aestronglyMeasurable F),
    lintegral_comp_rep_mul hD hDm hr (fun x => ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal) g]

theorem edist_indicator_le (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g)))
    (c : ℂ) {s : Set G} (hs : MeasurableSet s) (hμs : μ.restrict D s ≠ ∞) (g g₀ : G) :
    edist (R g (indicatorConstLp 2 hs hμs c)) (R g₀ (indicatorConstLp 2 hs hμs c)) ≤
      ‖c‖ₑ * μ (((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D))) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
  set F := indicatorConstLp 2 hs hμs c with hF
  set S := ((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D)) with hS
  have h1 : ∀ᵐ y ∂μ, (F : G → ℂ) (r y) = s.indicator (fun _ => c) (r y) :=
    ae_rep hDm hr (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c))
  have key : ∀ a b x : G, Good Γ D (x * b) → r (x * a) ∈ s → r (x * b) ∉ s →
      ∃ γ : Γ, (γ : G) * x * a ∈ s ∩ D ∧ (γ : G) * x * b ∉ s ∩ D := by
    intro a b x hb h2 h3
    obtain ⟨γ, e1, e2⟩ := hr (x * a)
    refine ⟨γ, by rw [mul_assoc, ← e1]; exact ⟨h2, e2⟩, fun h => h3 ?_⟩
    rw [mul_assoc] at h
    rw [rep_eq hr hb h.2]; exact h.1
  have hU : μ.restrict D (⋃ γ : Γ, γ • S) ≤ μ S := by
    rw [hD.measure_eq_tsum S]
    refine (measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => ?_))
    rw [Measure.restrict_apply' hDm]
  have hSm : MeasurableSet S := by
    apply MeasurableSet.symmDiff <;> exact (hs.inter hDm).preimage (by fun_prop)
  have hUm : NullMeasurableSet (⋃ γ : Γ, γ • S) (μ.restrict D) := by
    apply MeasurableSet.nullMeasurableSet
    exact MeasurableSet.iUnion fun γ => hSm.const_smul γ
  rw [Lp.edist_def]
  calc eLpNorm (⇑(R g F) - ⇑(R g₀ F)) 2 (μ.restrict D)
      ≤ eLpNorm ((⋃ γ : Γ, γ • S).indicator fun _ => c) 2 (μ.restrict D) := by
        refine eLpNorm_mono_eNorm_ae ((Lp.aestronglyMeasurable (R g F)).sub
          (Lp.aestronglyMeasurable (R g₀ F))) ?_
        filter_upwards [hR g F, hR g₀ F,
          ae_restrict_of_ae ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1),
          ae_restrict_of_ae ((measurePreserving_mul_right μ g₀).quasiMeasurePreserving.ae h1),
          ae_restrict_of_ae (ae_good_mul hD g), ae_restrict_of_ae (ae_good_mul hD g₀)]
          with x e1 e2 e3 e4 e5 e6
        rw [Pi.sub_apply, e1, e2, e3, e4]
        by_cases a : r (x * g) ∈ s <;> by_cases b : r (x * g₀) ∈ s
        · simp [a, b]
        · obtain ⟨γ, k1, k2⟩ := key g g₀ x e6 a b
          have : x ∈ ⋃ γ : Γ, γ • S :=
            mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inl ⟨k1, k2⟩)⟩
          rw [indicator_of_mem this]; simp [a, b]
        · obtain ⟨γ, k1, k2⟩ := key g₀ g x e5 b a
          have : x ∈ ⋃ γ : Γ, γ • S :=
            mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inr ⟨k1, k2⟩)⟩
          rw [indicator_of_mem this]; simp [a, b]
        · simp [a, b]
    _ ≤ _ := eLpNorm_indicator_const_le c 2 hUm
    _ ≤ _ := by gcongr

theorem continuous_map [LocallyCompactSpace G] [SecondCountableTopology G]
    [IsFiniteMeasureOnCompacts μ]
    (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g)))
    (F : Lp ℂ 2 (μ.restrict D)) : Continuous fun g => R g F := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => R g F)
    ?_ ?_ ?_ F
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    refine continuous_iff_continuousAt.2 fun g₀ => tendsto_iff_edist_tendsto_0.2 ?_
    let m : C(G, C(G, G)) := ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩
    have ht : Tendsto (fun g => μ (((fun x => x * g) ⁻¹' (s ∩ D)) ∆
        ((fun x => x * g₀) ⁻¹' (s ∩ D)))) (𝓝 g₀) (𝓝 0) :=
      tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀)
        (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g)
        (measurePreserving_mul_right μ g₀) (hs.inter hDm).nullMeasurableSet
        (by rw [← Measure.restrict_apply hs]; exact hμs.ne)
    have ht2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp ht
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at ht2
    have ht3 := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) ht2 (Or.inr enorm_ne_top)
    rw [mul_zero] at ht3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht3 (fun _ => zero_le)
      fun g => edist_indicator_le hD hDm hr hR c hs hμs.ne g g₀
  · intro f g hf hg _ h1 h2
    simp only [map_add (f := _)]
    exact h1.add h2
  · refine isClosed_of_closure_subset fun F hF => ?_
    refine TendstoUniformly.continuous (F := fun F' g => R g F') (p := 𝓝 F) ?_
      (mem_closure_iff_frequently.1 hF)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds F hε] with F' h g
    rw [dist_eq_norm, ← map_sub, norm_map hD hDm hr hR, ← dist_eq_norm, dist_comm]
    exact h

end GlobalTheory.RightRegFund
end

