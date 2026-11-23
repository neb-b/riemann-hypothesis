module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
section
open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.Mem.ZetaPole

theorem dedekindZeta_eq_tsum_ideal (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h := (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs).of_norm.hasSum
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).hasSum_iff] at h
  refine HasSum.tsum_eq (h.sigma fun n => ?_)
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ∘
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ =
          (n : ℂ) ^ (-s) := by
    rintro ⟨I, rfl⟩; rfl
  simp only [this]
  have := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have e : LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n =
      ∑ _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, (n : ℂ) ^ (-s) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hs0]
    · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
      simp
  rw [e]
  exact hasSum_fintype _

noncomputable def logFactor (n : ℕ) (s : ℝ) : ℝ := -Real.log (1 - (n : ℝ) ^ (-s))

theorem rpow_lt_one {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : (n : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by linarith)

theorem logFactor_nonneg {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : 0 ≤ logFactor n s := by
  have h1 := rpow_lt_one hn hs
  have h2 : 0 ≤ (n : ℝ) ^ (-s) := by positivity
  unfold logFactor
  have := Real.log_nonpos (x := 1 - (n : ℝ) ^ (-s)) (by linarith) (by linarith)
  linarith

theorem logFactor_le {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 1 ≤ s) : logFactor n s ≤ logFactor n 1 := by
  have h1 := rpow_lt_one hn one_pos
  have h2 : (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) (by linarith)
  unfold logFactor
  have := Real.log_le_log (x := 1 - (n : ℝ) ^ (-1 : ℝ)) (y := 1 - (n : ℝ) ^ (-s))
    (by linarith) (by linarith)
  linarith

theorem ofReal_logFactor {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) :
    ((logFactor n s : ℝ) : ℂ) = -Complex.log (1 - (n : ℂ) ^ (-(s : ℂ))) := by
  have h1 := rpow_lt_one hn hs
  unfold logFactor
  rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp

theorem summable_logFactor (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => logFactor (Ideal.absNorm v.asIdeal) s := by
  have hS := (GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (s : ℂ)) (by simpa using hs)).of_norm
  have pinj : Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal := fun v w h =>
    HeightOneSpectrum.ext h
  have h := (Summable.clog_one_sub (hS.comp_injective pinj)).neg
  rw [← Complex.summable_ofReal]
  refine h.congr fun v => ?_
  rw [ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)]
  rfl

theorem norm_dedekindZeta_eq_exp (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    ‖dedekindZeta K s‖ =
      Real.exp (∑' v : HeightOneSpectrum (𝓞 K), logFactor (Ideal.absNorm v.asIdeal) s) := by
  classical
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have hs0 : (s : ℂ) ≠ 0 := by rintro h; rw [h] at hs'; norm_num at hs'
  have h := GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1)
    (by simp) (by simp) (fun I J => by
      by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])
    (fun I => by split_ifs <;> simp) s hs'
  have e1 : ∀ I : Ideal (𝓞 K), (if I = ⊥ then (0 : ℂ) else 1) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ))
      = ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)) := fun I => by
    by_cases hI : I = ⊥
    · simp [hI, hs0]
    · simp [hI]
  simp only [e1] at h
  simp only [← ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm _)
    (lt_trans one_pos hs)] at h
  rw [dedekindZeta_eq_tsum_ideal K hs', h, ← Complex.ofReal_tsum, Complex.norm_exp,
    Complex.ofReal_re]

theorem not_injective_double_primes :
    ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} × Bool → HeightOneSpectrum (𝓞 F), Function.Injective f → (∀ x, Ideal.absNorm (f x).asIdeal = Ideal.absNorm x.1.1.asIdeal) → False := by
  intro K F _ _ _ _ S hS f hf hN
  set c : ℝ := ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) 1 with hc
  have key : ∀ s : ℝ, 1 < s →
      Real.exp (-2 * c) * ‖dedekindZeta K s‖ ^ 2 ≤ ‖dedekindZeta F s‖ := by
    intro s hs
    rw [norm_dedekindZeta_eq_exp K hs, norm_dedekindZeta_eq_exp F hs, sq, ← Real.exp_add,
      ← Real.exp_add, Real.exp_le_exp]
    have hK := summable_logFactor K hs
    have hF := summable_logFactor F hs
    have h1 := tsum_comp_le_tsum_of_inj hF (fun v => logFactor_nonneg
      (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)) hf
    have h2 := hF.comp_injective hf
    have e : ((fun v : HeightOneSpectrum (𝓞 F) => logFactor (Ideal.absNorm v.asIdeal) s) ∘ f) =
        fun x => logFactor (Ideal.absNorm x.1.1.asIdeal) s := by
      funext x
      simp only [Function.comp_apply, hN]
    rw [e] at h1 h2
    rw [h2.tsum_prod] at h1
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      tsum_mul_left, Nat.cast_ofNat] at h1
    have h3 := hK.sum_add_tsum_compl (s := hS.toFinset)
    rw [hS.coe_toFinset] at h3
    have h4 : ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) s ≤ c :=
      Finset.sum_le_sum fun v _ =>
        logFactor_le (NumberField.HeightOneSpectrum.one_lt_absNorm v) hs.le
    have h5 : ∑' x : ↑(Sᶜ), logFactor (Ideal.absNorm x.1.asIdeal) s =
      ∑' x : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, logFactor (Ideal.absNorm x.1.asIdeal) s := rfl
    linarith
  have tK := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have tF := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have t0 : Tendsto (fun s : ℝ => ‖(s : ℂ) - 1‖) (𝓝[>] 1) (𝓝 0) := by
    have : Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ := by fun_prop
    simpa using (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have hle := le_of_tendsto_of_tendsto ((tK.pow 2).const_mul (Real.exp (-2 * c))) (t0.mul tF) (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have := mul_le_mul_of_nonneg_left (key s hs) (sq_nonneg ‖(s : ℂ) - 1‖)
    simp only [norm_mul]
    nlinarith)
  have hpos : 0 < ‖(dedekindZeta_residue K : ℂ)‖ :=
    norm_pos_iff.2 (by exact_mod_cast dedekindZeta_residue_ne_zero K)
  have : 0 < Real.exp (-2 * c) * ‖(dedekindZeta_residue K : ℂ)‖ ^ 2 := by positivity
  linarith

end GlobalTheory.Mem.ZetaPole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionCoordinateHyperplane
section
open Metric Filter Topology Set

namespace GlobalTheory

theorem riemann_extension_coordinate_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by
  intro n U k f hU hd hb
  refine ⟨fun z => if z k = 0 then limUnder (𝓝[≠] (0 : ℂ)) (fun t => f (Function.update z k t)) else f z,
    ?_, fun z _ hz => by simp [hz]⟩
  have hO : IsOpen {z : Fin n → ℂ | z ∈ U ∧ z k ≠ 0} :=
    hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  intro z₀ hz₀
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases h0 : z₀ k = 0
  · obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz₀) hV)
    have hr : 0 < ε / 3 := by positivity
    have h2 : ball z₀ (2 * (ε / 3)) ⊆ U ∩ V := (ball_subset_ball (by linarith)).trans hball
    have hG := ((_root_.GlobalTheory.cauchyCoord_differentiableAt n U k f z₀ (ε / 3) hr h0 hU
      ((closedBall_subset_ball (by linarith)).trans (hball.trans inter_subset_left)) hd).const_smul
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹))
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact (_root_.GlobalTheory.cauchy_slice_removable_extension n U k f z₀ (ε / 3) M hr h0 hU (h2.trans inter_subset_left) hd
      (fun z hz hzk => hM z (h2 hz).2 (h2 hz).1 hzk) z hz).symm
  · have hf : DifferentiableAt ℂ f z₀ := hd.differentiableAt (hO.mem_nhds ⟨hz₀, h0⟩)
    refine hf.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds ⟨hz₀, h0⟩] with z hz
    simp [hz.2]
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetIntegralMulLeft
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.AverageConst

@[to_additive setIntegral_add_left]
theorem setIntegral_mul_left {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (φ : Z → ℂ)
    (hφ : ∀ γ ∈ Λ, ∀ z, φ (γ * z) = φ z) (a : Z) : ∫ z in F, φ (a * z) ∂μ = ∫ z in F, φ z ∂μ := by
  have : SMulCommClass Z Λ Z := ⟨fun a γ z => by
    change a * ((γ : Z) * z) = (γ : Z) * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  rw [hF.setIntegral_eq (hF.smul_of_comm a) fun γ z => hφ γ γ.2 z]
  exact ((measurePreserving_mul_left μ a).setIntegral_image_emb (measurableEmbedding_mulLeft a) φ F).symm

theorem average_const {Y Z A : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (Γ : AddSubgroup Y)
    [DiscreteTopology Γ] {K : Set Y} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) [AddCommGroup A] (χ : A → Y → ℂ)
    (h1 : ∀ a, Continuous (χ a)) (h2 : ∀ a x y, χ a (x + y) = χ a x * χ a y) (h3 : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (h4 : ∀ x, χ 0 x = 1) (h5 : ∀ a x, ‖χ a x‖ = 1) (h6 : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ)
    (ν : Measure Y) [ν.IsAddHaarMeasure] {G : Set Y} (hG : IsAddFundamentalDomain Γ G ν)
    [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (hfin : μ F ≠ ⊤)
    (k : Z → Y → ℂ) (kz : ∀ y, Continuous fun z => k z y) (ky : ∀ z, Continuous (k z)) {C : ℝ} (kb : ∀ z y, ‖k z y‖ ≤ C)
    (kΛ : ∀ γ ∈ Λ, ∀ z y, k (γ * z) y = k z y) (kΓ : ∀ γ ∈ Γ, ∀ z y, k z (γ + y) = k z y)
    (htw : ∀ a, (∀ y, χ a y = 1) ∨ ∃ (z₁ : Z) (c : ℂ), c ≠ 1 ∧
      ∀ z, ∫ y in G, χ a y * k (z₁ * z) y ∂ν = c * ∫ y in G, χ a y * k z y ∂ν) (y₀ : Y) :
    ∫ z in F, k z y₀ ∂μ = ∫ z in F, k z 0 ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (ν.restrict G) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov ν hG⟩
  have : IsFiniteMeasure (μ.restrict F) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Y → ℂ, ∀ y, Φ y = ∫ z in F, k z y ∂μ := ⟨_, fun _ => rfl⟩
  have hΦc : Continuous Φ := by
    rw [funext hΦ]
    exact continuous_of_dominated (bound := fun _ => C) (fun y => (kz y).aestronglyMeasurable)
      (fun y => .of_forall fun z => kb z y) (integrable_const _) (.of_forall ky)
  have hΦp : ∀ γ ∈ Γ, ∀ y, Φ (γ + y) = Φ y := fun γ hγ y => by simp only [hΦ, kΓ γ hγ]
  have hΦb : ∀ y, ‖Φ y‖ ≤ C * (μ.restrict F).real Set.univ := fun y => by
    rw [hΦ]; exact norm_integral_le_of_norm_le_const (.of_forall fun z => kb z y)
  have hint : ∀ a y₁, Integrable (fun y => χ a y * Φ (y₁ + y)) (ν.restrict G) := fun a y₁ =>
    Integrable.of_bound ((h1 a).mul (hΦc.comp (continuous_const.add continuous_id))).aestronglyMeasurable _
      (.of_forall fun y => by rw [norm_mul, h5, one_mul]; exact hΦb _)
  have hco : ∀ a, (∀ y, χ a y = 1) ∨ ∫ y in G, χ a y * Φ y ∂ν = 0 := fun a => (htw a).imp_right fun ⟨z₁, c, hc1, h⟩ => by
    have hm : StronglyMeasurable (Function.uncurry fun y z => χ a y * k z y) :=
      stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun z => (h1 a).mul (ky z))
        fun y => (continuous_const.mul (kz y)).stronglyMeasurable
    have e : ∫ y in G, χ a y * Φ y ∂ν = ∫ z in F, ∫ y in G, χ a y * k z y ∂ν ∂μ := by
      simp only [hΦ, ← integral_const_mul]
      exact integral_integral_swap (Integrable.of_bound hm.aestronglyMeasurable C (.of_forall fun p => by
        rw [Function.uncurry, norm_mul, h5, one_mul]; exact kb _ _))
    have e2 := setIntegral_mul_left hc Λ μ hF (fun z => ∫ y in G, χ a y * k z y ∂ν)
      (fun γ hγ z => by simp only [kΛ γ hγ]) z₁
    simp only [h, integral_const_mul] at e2
    rw [e]
    exact (mul_left_eq_self₀.1 e2).resolve_left hc1
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero Y Γ K hK hcov A χ h1 h2 h3 h4 h5 h6 ν G
    inferInstance hG (fun y => Φ (y₀ + y) - Φ (0 + y))
    ((hΦc.comp (continuous_const.add continuous_id)).sub (hΦc.comp (continuous_const.add continuous_id)))
    (fun γ hγ y => by rw [add_left_comm, hΦp γ hγ, add_left_comm, hΦp γ hγ]) fun a => by
      have e := setIntegral_add_left add_comm Γ ν hG (fun y => χ a y * Φ y)
        (fun γ hγ y => by rw [h2, (h6 γ).2 hγ, one_mul, hΦp γ hγ]) y₀
      simp only [h2, mul_assoc, integral_const_mul] at e
      simp only [mul_sub]
      rw [integral_sub (hint a _) (hint a _), sub_eq_zero]
      simp only [zero_add]
      rcases hco a with h | h
      · rwa [h, one_mul] at e
      · rw [h] at e ⊢
        exact (mul_eq_zero.1 e).resolve_left fun h0 => by simpa [h0] using h5 a y₀
  have := congrFun key 0
  simp only [add_zero, Pi.zero_apply, sub_eq_zero] at this
  rw [← hΦ, ← hΦ, this]

end GlobalTheory.AverageConst
end

