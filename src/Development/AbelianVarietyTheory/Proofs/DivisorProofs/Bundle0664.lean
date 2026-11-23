module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqNormSmoothSectionSubGluedLe
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.GlueDist

theorem sq_norm_smoothSection_sub_glued_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n0 A la (F0 - glue C la u) ≤ (C.m : ℝ≥0∞) * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 u hF hu
  classical
  set L := A.kap + la with hL

  set D : Fin C.m → ι → Y → ℂ := fun a j y =>
    F0 j y - A.g L j (C.idx a) y * u a (A.chart (C.idx a) y) with hD
  set S : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hS
  have hSo : ∀ a, IsOpen (S a) := fun a =>
    (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hsec : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source, ∀ j, y ∈ (A.chart j).source →
      D a j y = A.g L j (C.idx a) y * D a (C.idx a) y := by
    intro a y hy j hj
    simp only [hD]
    rw [hF.2 j (C.idx a) y hj hy, A.g_self L (C.idx a) hy]
    ring
  have hchart : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source,
      A.nsq L (D a) y = ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y) := by
    intro a y hy
    rw [A.nsq_chart L (D a) (C.idx a) hy (hsec a y hy _ (A.mem_pick y))]
    simp only [hD, A.g_self L (C.idx a) hy, one_mul]

  have hsum1 : ∀ y, ∑ a, (C.chi a y : ℂ) = 1 := by
    intro y; rw [← Complex.ofReal_sum, C.sum_one y, Complex.ofReal_one]
  have hG : F0 - glue C la u = fun j y => ∑ a, (C.chi a y : ℂ) * D a j y := by
    funext j y
    simp only [Pi.sub_apply, glue, hD, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hsum1 y, one_mul]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hchi1 : ∀ a y, C.chi a y ≤ 1 := by
    intro a y
    rw [← C.sum_one y]
    exact Finset.single_le_sum (fun b _ => C.nonneg b y) (Finset.mem_univ a)

  have hpt : ∀ y, A.nsq L (F0 - glue C la u) y ≤
      (C.m : ℝ) * ∑ a, (S a).indicator (A.nsq L (D a)) y := by
    intro y
    rw [hG]
    refine (A.nsq_sum_le L Finset.univ (fun a j y => (C.chi a y : ℂ) * D a j y) y).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)
    have he : A.nsq L (fun j y => (C.chi a y : ℂ) * D a j y) y = C.chi a y ^ 2 * A.nsq L (D a) y := by
      unfold WeightedAtlas.nsq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.nonneg a y)]
      ring
    rw [he]
    by_cases h0 : C.chi a y = 0
    · rw [h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y
    · have hyS : y ∈ S a := C.supp a (subset_tsupport _ h0)
      rw [Set.indicator_of_mem hyS]
      have h2 : C.chi a y ^ 2 ≤ 1 := pow_le_one₀ (C.nonneg a y) (hchi1 a y)
      nlinarith [A.nsq_nonneg L (D a) y]

  have hF0c : ∀ i, ContinuousOn (F0 i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (F0 i ∘ (A.chart i).symm) (A.chart i).target := (hF.1 i).continuousOn
    refine (h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)).congr
      (fun x hx => ?_)
    simp [Function.comp, (A.chart i).left_inv hx]
  have hcont : ∀ a, ContinuousOn (fun y => ENNReal.ofReal (A.nsq L (D a) y)) (S a) := by
    intro a
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    have hu' : ContinuousOn (fun y => u a (A.chart (C.idx a) y)) (S a) :=
      (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
        (fun y hy => hy.2)
    have hc : ContinuousOn (fun y => ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y)) (S a) :=
      ((((hF0c (C.idx a)).mono Set.inter_subset_left).sub hu').norm.pow 2).mul
        ((A.continuousOn_ph L (C.idx a)).mono Set.inter_subset_left).neg.rexp
    exact hc.congr (fun y hy => hchart a y hy.1)
  have hmeas : ∀ a, AEMeasurable ((S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y))) A.mu :=
    fun a => (aemeasurable_indicator_iff (hSo a).measurableSet).2
      ((hcont a).aemeasurable (hSo a).measurableSet)

  have hpiece : ∀ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu =
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hWt : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    have heq : ∀ v ∈ ball (C.c a) (C.r a),
        D a (C.idx a) ((A.chart (C.idx a)).symm v) = F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v := by
      intro v hv
      have hvt := hWt hv
      simp only [hD, A.g_self L (C.idx a) ((A.chart (C.idx a)).map_target hvt),
        (A.chart (C.idx a)).right_inv hvt, one_mul]
    have hae : AEMeasurable (D a (C.idx a) ∘ (A.chart (C.idx a)).symm) (volume.restrict (ball (C.c a) (C.r a))) := by
      have hc : ContinuousOn (fun v => F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v) (ball (C.c a) (C.r a)) :=
        (((hF.1 (C.idx a)).continuousOn.mono hWt).sub (hu a).continuousOn)
      exact (hc.congr (fun v hv => heq v hv)).aemeasurable measurableSet_ball
    rw [_root_.GlobalTheory.OTY.lintegral_nsq_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (D a) measurableSet_ball hWt
      (fun y hy _ => hsec a y hy _ (A.mem_pick y)) hae]
    refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
    rw [heq v hv]

  unfold n0
  calc ∫⁻ y, ENNReal.ofReal (A.nsq L (F0 - glue C la u) y) ∂A.mu
      ≤ ∫⁻ y, (C.m : ℝ≥0∞) * ∑ a, (S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y)) y ∂A.mu := by
        refine lintegral_mono fun y => ?_
        refine (ENNReal.ofReal_le_ofReal (hpt y)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun a _ => Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y)]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hy : y ∈ S a
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
    _ = (C.m : ℝ≥0∞) * ∑ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_finsetSum' _ (fun a _ => hmeas a)]
        congr 1
        exact Finset.sum_congr rfl fun a _ => lintegral_indicator (hSo a).measurableSet _
    _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun a _ => hpiece a

end GlobalTheory.GlueDist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupEqTopOfLeMaximal
section
open NumberField

namespace GlobalTheory.PrimesAboveExistence

theorem sup_eq_top_of_le_maximal {R : Type} [CommRing R] {A B I : Ideal R}
    (h : ∀ M : Ideal R, M.IsMaximal → B ≤ M → A ≤ M) (hA : I ⊔ A = ⊤) : I ⊔ B = ⊤ := by
  by_contra hne

  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hAM : A ≤ M := h M hM (le_sup_right.trans hle)
  exact hM.ne_top (top_le_iff.mp (hA ▸ sup_le (le_sup_left.trans hle) hAM))

theorem exists_primes_above {F : Type} [Field F] [NumberField F] (l : ℕ) (hl : Nat.Prime l) :
    ∃ P : Finset (Ideal (𝓞 F)),
      (∀ 𝔭 ∈ P, Ideal.IsMaximal 𝔭 ∧ 𝔭 ≠ ⊥ ∧ l ∣ (Ideal.absNorm : Ideal (𝓞 F) → ℕ) 𝔭) ∧
      ∀ I : Ideal (𝓞 F), Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔
        Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  classical
  set L : Ideal (𝓞 F) := Ideal.span {(l : 𝓞 F)} with hL
  have hL0 : L ≠ ⊥ := by
    rw [hL, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero

  refine ⟨(UniqueFactorizationMonoid.normalizedFactors L).toFinset, ?_, ?_⟩
  · intro 𝔭 h𝔭
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0] at h𝔭
    obtain ⟨hp, hle⟩ := h𝔭
    have hne : 𝔭 ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hle))
    have hmax : 𝔭.IsMaximal := hp.isMaximal hne
    refine ⟨hmax, hne, ?_⟩

    have hdvd : Ideal.absNorm 𝔭 ∣ l ^ Module.finrank ℤ (𝓞 F) := by
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rwa [hL, Ideal.absNorm_span_singleton,
        show (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) by simp,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hmax.ne_top (Ideal.absNorm_eq_one_iff.mp (by simpa using hk))
    change l ∣ Ideal.absNorm 𝔭
    rw [hk]
    exact dvd_pow_self l hk0
  · intro I
    unfold Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo
    refine and_congr_right fun _ =>
      ⟨fun h => sup_eq_top_of_le_maximal ?_ h, fun h => sup_eq_top_of_le_maximal ?_ h⟩
    ·
      intro M hM hLM
      have hmem : M ∈ (UniqueFactorizationMonoid.normalizedFactors L).toFinset := by
        rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0]
        exact ⟨hM.isPrime, hLM⟩
      exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun 𝔭 => 𝔭) hmem)
    ·
      intro M hM hPM
      obtain ⟨𝔭, h𝔭, hle⟩ := (Ideal.IsPrime.prod_le hM.isPrime).mp hPM
      rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0] at h𝔭
      have hne : 𝔭 ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ h𝔭.2))
      have h𝔭M : 𝔭 = M := (h𝔭.1.isMaximal hne).eq_of_le hM.ne_top hle
      exact h𝔭M ▸ h𝔭.2

end GlobalTheory.PrimesAboveExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailSubstPAdicallySmallOfIntegralDifferential
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem GlobalTheory.tail_subst_small : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → ∀ m : ℕ, ∃ M0 : ℕ, ∀ M ≥ M0, ∀ n : σ →₀ ℕ, ∃ b : B, MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) (f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q)))) = algebraMap B Q (p ^ m * b) := by
  intro p hp B O Q _ _ _ _ θ hF σ _ _ z hz τ _ _ u f hu hD m
  have hpr : p.Prime := hp.out
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.trunc'_eval_dvd_of_order p B σ z hz
  obtain ⟨M0, hM0⟩ := _root_.GlobalTheory.VSubArith.add_mul_le_of_pow_le p L m hpr.two_le
  refine ⟨M0, fun M hM n => ?_⟩
  set g : MvPowerSeries τ Q := f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q) with hg
  have hfin := Finsupp.finite_of_degree_le (σ := τ) n.degree
  rw [GlobalTheory.T.mvPowerSeries_eval_trunc_subst_eq_sum B Q σ τ z u hu g n hfin.toFinset (fun α hα => by simpa using hα)]

  have key : ∀ α : τ →₀ ℕ, ∃ b : B, coeff α g * algebraMap B Q (MvPolynomial.eval z
      (trunc' B n (α.prod fun j e => u j ^ e))) = algebraMap B Q (p ^ m * b) := by
    intro α
    by_cases hα : α ≤ Finsupp.equivFunOnFinite.symm fun _ => M
    · refine ⟨0, ?_⟩
      have : coeff α g = 0 := by
        simp [hg, coeff_trunc', hα]
      simp [this]
    · have hcg : coeff α g = coeff α f := by
        simp [hg, coeff_trunc', hα]
      rw [hcg]
      obtain ⟨i, hi⟩ : ∃ i, M < α i := by
        by_contra h
        push_neg at h
        exact hα (fun i => by simpa using h i)
      obtain ⟨b, -, hb⟩ := hD α i
      obtain ⟨v, n', hn', hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := α i) (by omega) p hpr.one_lt.ne'
      have hcop : Nat.Coprime n' p := ((Nat.Prime.coprime_iff_not_dvd hpr).2 hn').symm
      obtain ⟨w, hw⟩ := (hF.unit_coprime n' hcop).exists_right_inv
      have hn'pos : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hdec; omega)
      have hpv : p ^ v ≤ α.degree := by
        have : p ^ v ≤ α i := by rw [hdec]; exact Nat.le_mul_of_pos_right _ hn'pos
        exact this.trans (Finsupp.le_degree i α)
      have hdeg : (v + m) * L ≤ α.degree :=
        hM0 α.degree v (by have := Finsupp.le_degree i α; omega) hpv
      obtain ⟨c, hc⟩ := hL (v + m) (α.prod fun j e => u j ^ e) (fun β hβ =>
        _root_.GlobalTheory.DivMono.coeff_finsuppProd_eq_zero_of_degree_lt B σ τ u hu α β (by rw [mul_comm] at hβ; omega)) n
      refine ⟨b * w * c, ?_⟩
      rw [hc]
      rw [hdec] at hb
      have hw' := congrArg (algebraMap B Q) hw
      simp only [map_mul, map_pow, map_natCast, map_one, Nat.cast_mul, Nat.cast_pow] at hb hw' ⊢
      linear_combination ((p : Q) ^ m * algebraMap B Q w * algebraMap B Q c) * hb
        - (coeff α f * (p : Q) ^ (v + m) * algebraMap B Q c) * hw'
  choose bb hbb using key
  refine ⟨∑ α ∈ hfin.toFinset, bb α, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun α _ => hbb α
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependent
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.Untwist

theorem res_X_isZero {R : Type} [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) :=
  (injectiveResolution F).cocomplex.isZero_extend_X ComplexShape.embeddingUpNat n (fun i hi => by
    change (i : ℤ) = n at hi; omega)

theorem sec_eq_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (y : Sec F U) : y = 0 := by
  have h := congrArg (fun φ : F ⟶ F => Sec.map φ y) (hF.eq_of_src (𝟙 F) 0)
  exact h

theorem sec_res_neg {R : Type} [CommRing R] (F : Shv R) {n : ℤ} (hn : n < 0) {U : Scheme.{0}} (y z : Sec ((res R F).X n) U) :
    y = z := (sec_eq_zero (res_X_isZero F n hn) y).trans (sec_eq_zero (res_X_isZero F n hn) z).symm

theorem cocycle_ext_zero {R : Type} [CommRing R] {X : Scheme.{0}} {F : Shv R}
    (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0)
    (h : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 0 (by simp) U x = ev β.1 0 0 (by simp) U x) : α = β := by
  refine Cocycle.ext (CupSpec.ev_ext _ _ fun p s hs U x => ?_)
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using hs.symm
    exact h U x
  | succ p => exact sec_res_neg F (by omega) _ _

theorem cup_rootClass {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (a b : ℤ) :
    cup q (rootClass a ζ) (rootClass b ζ) = (rootClass (a + b) ζ : Ht q (sch.obj X) (0 + 0) (a + b)) := by
  obtain ⟨α, hα, hα'⟩ := rootClass_spec a ζ
  obtain ⟨β, hβ, hβ'⟩ := rootClass_spec b ζ
  obtain ⟨γ, hγ, hγ'⟩ := rootClass_spec (a + b) ζ
  rw [← hα, ← hβ, ← hγ]
  refine Pair.cup_spec (twPair q a b) (sch.obj X) rfl α β γ ?_
  intro N w hw U x
  cases N with
  | zero =>
    obtain rfl : w = 0 := by simpa using hw.symm
    rw [Fin.sum_univ_one]
    change ev γ.1 0 0 _ U x = ((0 : ℤ) * 0).negOnePow • (twPair q a b).mul U 0 0 0 rfl (ev α.1 0 0 (by simp) U x) (ev β.1 0 0 (by simp) U x)
    have e1 : ev α.1 0 0 (by simp) U x = _ := hα' U x
    have e2 : ev β.1 0 0 (by simp) U x = _ := hβ' U x
    rw [e1, e2, mul_zero, Int.negOnePow_zero, one_smul]
    refine Eq.trans (hγ' U x) ?_
    change Sec.res (show U ⟶ X from x) _ = (twPair q a b).mul U 0 0 0 rfl (Sec.res (show U ⟶ X from x) _) (Sec.res (show U ⟶ X from x) _)
    rw [ClsSpec.res_resGen, ClsSpec.res_resGen, ClsSpec.res_resGen]
    exact (twPair_spec q a b U _).symm
  | succ N => exact sec_res_neg _ (by omega) _ _

theorem rootClass_zero {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (hX : Inv q (sch.obj X)) :
    rootClass 0 ζ = one q (sch.obj X) := by
  obtain ⟨α, hα, hα'⟩ := rootClass_spec 0 ζ
  obtain ⟨β, hβ, hβ'⟩ := one_spec q (sch.obj X) hX
  rw [← hα, ← hβ]
  refine congrArg CohomologyClass.mk (cocycle_ext_zero α β fun U x => ?_)
  rw [hα', hβ' U x (ζ.map x.appTop.hom), ClsSpec.res_resGen]

section Cast
variable {q : ℕ} {E : Spc}

theorem cast_cast {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (h₁ : n = n') (h₂ : i = i') (h₃ : n' = n'') (h₄ : i' = i'') :
    (x.cast h₁ h₂).cast h₃ h₄ = x.cast (h₁.trans h₃) (h₂.trans h₄) := by
  subst h₁; subst h₂; subst h₃; subst h₄; rfl

theorem cast_add {n i n' i' : ℤ} (x y : Ht q E n i) (hn : n = n') (hi : i = i') :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

theorem eq_cast_symm {n i n' i' : ℤ} {x : Ht q E n i} {y : Ht q E n' i'} (hn : n' = n) (hi : i' = i) (h : x = y.cast hn hi) :
    y = x.cast hn.symm hi.symm := by
  subst hn; subst hi; exact h.symm

theorem cup_cast_left {n m i j n' i' : ℤ} (x : Ht q E n i) (b : Ht q E m j) (hn : n = n') (hi : i = i') :
    cup q (x.cast hn hi) b = (cup q x b).cast (congrArg (· + m) hn) (congrArg (· + j) hi) := by
  subst hn; subst hi; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (a : Ht q E n i) (y : Ht q E m j) (hm : m = m') (hj : j = j') :
    cup q a (y.cast hm hj) = (cup q a y).cast (congrArg (n + ·) hm) (congrArg (i + ·) hj) := by
  subst hm; subst hj; rfl

theorem cup_cup_of_unit [NeZero q] (hE : Inv q E) {d e n i : ℤ} (u : Ht q E 0 d) (v : Ht q E 0 e) (hde : (0 : ℤ) = e + d)
    (hvu : cup q v u = (one q E).cast (by simp) hde) (a : Ht q E n i)
    {k : ℤ} (h₁ : 0 + n = n) (h₂ : d + i = k) (h₃ : 0 + n = n) (h₄ : e + k = i) :
    (cup q v ((cup q u a).cast h₁ h₂)).cast h₃ h₄ = a := by
  have hring := GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q E
  have hassoc := eq_cast_symm _ _ (hring.2.1 v u a)
  rw [cup_cast_right, cast_cast, hassoc, cast_cast, hvu, cup_cast_left, cast_cast, hring.1 hE a, cast_cast]
  rfl

end Cast

theorem rootClass_cast {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) {k k' : ℤ} (h : k = k') (hn : (0 : ℤ) = 0 + 0) :
    (rootClass k ζ).cast hn h = (rootClass k' ζ : Ht q (sch.obj X) (0 + 0) k') := by
  subst h; rfl

noncomputable def twistEquiv {q : ℕ} [NeZero q] {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (hX : Inv q (sch.obj X)) (n i j : ℤ) :
    Ht q (sch.obj X) n i ≃+ Ht q (sch.obj X) n j := by
  have key : ∀ d e : ℤ, ∀ hde : (0 : ℤ) = e + d,
      cup q (rootClass e ζ) (rootClass d ζ) = (one q (sch.obj X)).cast (by simp) hde := by
    intro d e hde
    rw [cup_rootClass, ← rootClass_zero ζ hX, rootClass_cast ζ hde]
  exact
    { toFun := fun a => (cup q (rootClass (j - i) ζ) a).cast (zero_add n) (by ring)
      invFun := fun b => (cup q (rootClass (i - j) ζ) b).cast (zero_add n) (by ring)
      left_inv := fun a => cup_cup_of_unit hX _ _ (by ring) (key _ _ (by ring)) a _ _ _ _
      right_inv := fun b => cup_cup_of_unit hX _ _ (by ring) (key _ _ (by ring)) b _ _ _ _
      map_add' := fun a b => by simp only [map_add (f := _), cast_add] }

end GlobalTheory.EtC.Untwist


open GlobalTheory.EtC.Untwist in
theorem GlobalTheory.EtC.untwist : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) →
    (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → ∀ n i j : ℤ, Nonempty (Ht q (sp A) n i ≃+ Ht q (sp A) n j) := by
  intro q _ A _ hq ⟨z, hz⟩ n i j
  let φ : A →+* Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hX : Inv q (sp A) := fun U ⟨x⟩ => by
    have h := (hq.map φ).map (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom
    simpa only [map_natCast] using h
  exact ⟨twistEquiv (Prim.map φ ⟨z, hq, hz⟩) hX n i j⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
section
set_option autoImplicit false

open Filter Topology

namespace GlobalTheory.PeriodFamily

section
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt (f g : (I → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) =
      _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← add_smul, show (fun z ↦ f z + g z) = f + g from rfl,
    iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt, ContinuousMultilinearMap.add_apply, mul_add]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_const_fun (c : ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ => ?_]
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_congr_germ (f g : (I → ℂ) → ℂ) (h : f =ᶠ[𝓝 0] g) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span (f : (I → ℂ) → ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t) := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ']
  have h0 : ∑ s : Fin 0 → I, ((↑(Nat.factorial 0))⁻¹ * (iteratedFDeriv ℂ 0 f 0)
      fun a ↦ Pi.single (s a) 1) • ∏ a, t (s a) = algebraMap ℂ D (f 0) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h0, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun s _ => ?_
  rw [Algebra.smul_def, Fin.prod_univ_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s 0, rfl⟩))

end


set_option autoImplicit false in
open Filter Topology in
theorem _root_.GlobalTheory.PeriodFamily.taylor_formal_properties : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) = _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (c : ℂ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ c * f z) = c • _root_.GlobalTheory.PeriodFamily.taylor N t f) ∧ (∀ c : ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c) ∧ (∀ f g : (I → ℂ) → ℂ, f =ᶠ[𝓝 0] g → _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ), ψ (_root_.GlobalTheory.PeriodFamily.taylor N t f) = _root_.GlobalTheory.PeriodFamily.taylor N (fun i ↦ ψ (t i)) f) ∧ (∀ f : (I → ℂ) → ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t)) := by
  intro I _ _ D _ _ N t
  refine ⟨fun f g hf hg => _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t f g hf hg,
    fun c f hf => ?_, _root_.GlobalTheory.PeriodFamily.taylor_const_fun N t,
    _root_.GlobalTheory.PeriodFamily.taylor_congr_germ N t, fun D' _ _ ψ f => ?_,
    _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t⟩
  · unfold _root_.GlobalTheory.PeriodFamily.taylor
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show (fun z ↦ c * f z) = fun z ↦ c • f z from rfl,
      iteratedFDeriv_const_smul_apply' hf.contDiffAt, ContinuousMultilinearMap.smul_apply,
      smul_eq_mul, smul_smul, mul_left_comm]
  · unfold _root_.GlobalTheory.PeriodFamily.taylor
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_prod]

end GlobalTheory.PeriodFamily
end

