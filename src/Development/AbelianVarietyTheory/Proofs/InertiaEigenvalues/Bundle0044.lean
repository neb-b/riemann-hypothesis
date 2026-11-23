module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumOneAddNormRpowNegLeEuclidean
section
open MeasureTheory Metric Module
open scoped ENNReal

namespace GlobalTheory.LatticeCount

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma one_add_norm_rpow_neg_le {s r : ℝ} (hs : 0 ≤ s) {x y : V} (hx : r ≤ ‖x‖)
    (hy : y ∈ ball x (r / 2)) :
    (1 + ‖x‖) ^ (-s) ≤ 2 ^ s * (1 + ‖y‖) ^ (-s) := by
  have hd : dist y x < r / 2 := mem_ball.mp hy
  rw [dist_eq_norm] at hd
  have h1 := norm_sub_norm_le y x
  have hx0 := norm_nonneg x
  have key : 1 + ‖y‖ ≤ 2 * (1 + ‖x‖) := by linarith
  have hpos : 0 < 1 + ‖y‖ := by positivity
  calc (1 + ‖x‖) ^ (-s) = 2 ^ s * (2 * (1 + ‖x‖)) ^ (-s) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← mul_assoc, ← Real.rpow_add (by norm_num)]
        simp
    _ ≤ 2 ^ s * (1 + ‖y‖) ^ (-s) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos key (by linarith)) (by positivity)

lemma sum_mul_measure_ball_le [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {s : ℝ} (hs : 0 ≤ s) (Λ : AddSubgroup V) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) (t : Finset ((Λ : Set V) \ {0} : Set V)) :
    (∑ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s))) * μ (ball 0 (r / 2)) ≤
      ENNReal.ofReal (2 ^ s) * ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ := by
  classical
  have hpt : ∀ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s)) * μ (ball 0 (r / 2)) ≤
      ENNReal.ofReal (2 ^ s) *
        ∫⁻ y in ball (x : V) (r / 2), ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ := by
    intro x _
    rw [← Measure.addHaar_ball_center μ (x : V) (r / 2), ← setLIntegral_const,
      ← lintegral_const_mul' (ENNReal.ofReal (2 ^ s)) _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_ball
    intro y hy
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    exact one_add_norm_rpow_neg_le hs (hmin _ (SetLike.mem_coe.mp x.2.1) (by simpa using x.2.2)) hy
  have hdisj : Set.PairwiseDisjoint (↑t)
      (fun x : ((Λ : Set V) \ {0} : Set V) => ball (x : V) (r / 2)) := by
    intro a _ b _ hab
    show Disjoint (ball (a : V) (r / 2)) (ball (b : V) (r / 2))
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have hmem : (a : V) - b ∈ Λ :=
      Λ.sub_mem (SetLike.mem_coe.mp a.2.1) (SetLike.mem_coe.mp b.2.1)
    have hne : (a : V) - b ≠ 0 := sub_ne_zero.mpr (fun h => hab (Subtype.ext h))
    linarith [hmin _ hmem hne]
  calc (∑ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s))) * μ (ball 0 (r / 2))
      = ∑ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s)) * μ (ball 0 (r / 2)) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ t, ENNReal.ofReal (2 ^ s) *
          ∫⁻ y in ball (x : V) (r / 2), ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ :=
        Finset.sum_le_sum hpt
    _ = ENNReal.ofReal (2 ^ s) *
          ∫⁻ y in ⋃ x ∈ t, ball (x : V) (r / 2), ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
    _ ≤ ENNReal.ofReal (2 ^ s) * ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ :=
        mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) (zero_le)

lemma sum_le_mul_rpow [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    [Nontrivial V] {s : ℝ} (hs : (finrank ℝ V : ℝ) < s) (Λ : AddSubgroup V) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) (t : Finset ((Λ : Set V) \ {0} : Set V)) :
    ∑ x ∈ t, (1 + ‖(x : V)‖) ^ (-s) ≤
      (2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ).toReal * 2 ^ finrank ℝ V /
        (μ (ball 0 1)).toReal) * r ^ (-(finrank ℝ V : ℝ)) := by
  have hD0 : (0 : ℝ) ≤ finrank ℝ V := Nat.cast_nonneg _
  have hs0 : 0 ≤ s := by linarith
  have hI : ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ < ∞ := finite_integral_one_add_norm hs
  have hB0 : 0 < μ (ball (0 : V) 1) := measure_ball_pos μ 0 one_pos
  have hBt : μ (ball (0 : V) 1) < ∞ := measure_ball_lt_top
  have hBpos : 0 < (μ (ball (0 : V) 1)).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
  have h2 := sum_mul_measure_ball_le μ hs0 Λ hr hmin t
  rw [Measure.addHaar_ball μ 0 (by positivity : (0 : ℝ) ≤ r / 2),
    ← ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity)] at h2
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun x _ => by positivity)),
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at h3
  have e : 2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ).toReal * 2 ^ finrank ℝ V /
        (μ (ball 0 1)).toReal * r ^ (-(finrank ℝ V : ℝ)) =
      (2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ).toReal) /
        ((r / 2) ^ finrank ℝ V * (μ (ball 0 1)).toReal) := by
    rw [Real.rpow_neg hr.le, Real.rpow_natCast, div_pow]
    field_simp
  rw [e, le_div_iff₀ (mul_pos (pow_pos (by positivity) _) hBpos)]
  linarith [h3]

private lemma rpow_neg_mul_one_add_le_two_mul {D : ℝ} (hD : 1 ≤ D) {r : ℝ} (hr : 0 < r) :
    r ^ (-D) * (1 + r) ≤ 2 * (r ^ (-D) + 1) := by
  have h0 : 0 ≤ r ^ (-D) := by positivity
  rcases le_total r 1 with h | h
  · have : r ^ (-D) * r ≤ r ^ (-D) := mul_le_of_le_one_right h0 h
    nlinarith
  · have h1 : r ^ (-D) * r ≤ 1 := by
      rw [← Real.rpow_add_one hr.ne']
      exact Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have h2 : r ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    nlinarith

theorem tsum_one_add_norm_rpow_neg_le (hD : 1 ≤ finrank ℝ V) {M : ℝ}
    (hM : (finrank ℝ V : ℝ) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup V) (r : ℝ), 0 < r → (∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) →
      Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-M)) ∧
      ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M) ≤
        C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have _ : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hD1 : (1 : ℝ) ≤ (finrank ℝ V : ℝ) := by exact_mod_cast hD
  set s : ℝ := min M ((finrank ℝ V : ℝ) + 1) with hsdef
  have hsD : (finrank ℝ V : ℝ) < s := lt_min hM (by linarith)
  have hsM : s ≤ M := min_le_left _ _
  have hsD1 : s ≤ (finrank ℝ V : ℝ) + 1 := min_le_right _ _
  set K : ℝ := 2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂(Measure.addHaar : Measure V)).toReal *
    2 ^ finrank ℝ V / ((Measure.addHaar : Measure V) (ball 0 1)).toReal with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨2 * K + 1, by positivity, fun Λ r hr hmin => ?_⟩
  have hfs : ∀ u : Finset ((Λ : Set V) \ {0} : Set V),
      ∑ x ∈ u, (1 + ‖(x : V)‖) ^ (-s) ≤ K * r ^ (-(finrank ℝ V : ℝ)) :=
    fun u => sum_le_mul_rpow (Measure.addHaar : Measure V) hsD Λ hr hmin u
  have hf0 : ∀ x : ((Λ : Set V) \ {0} : Set V), 0 ≤ (1 + ‖(x : V)‖) ^ (-s) :=
    fun x => by positivity
  have hsum : Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-s)) :=
    summable_of_sum_le hf0 hfs
  have hle : ∀ x : ((Λ : Set V) \ {0} : Set V),
      (1 + ‖(x : V)‖) ^ (-M) ≤ (1 + ‖(x : V)‖) ^ (-s) * (1 + r) ^ (s - M) := by
    intro x
    have hx : r ≤ ‖(x : V)‖ := hmin _ (SetLike.mem_coe.mp x.2.1) (by simpa using x.2.2)
    have hpos : 0 < 1 + ‖(x : V)‖ := by positivity
    calc (1 + ‖(x : V)‖) ^ (-M) = (1 + ‖(x : V)‖) ^ (-s) * (1 + ‖(x : V)‖) ^ (s - M) := by
          rw [← Real.rpow_add hpos]; congr 1; ring
      _ ≤ (1 + ‖(x : V)‖) ^ (-s) * (1 + r) ^ (s - M) := by
          apply mul_le_mul_of_nonneg_left _ (hf0 x)
          exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hsumM : Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-M)) :=
    Summable.of_nonneg_of_le (fun x => by positivity) hle (hsum.mul_right _)
  refine ⟨hsumM, ?_⟩
  have hpow := rpow_neg_mul_one_add_le_two_mul hD1 hr
  have hsplit : (1 + r) ^ (s - M) = (1 + r) ^ (s - finrank ℝ V) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have hsD' : (1 + r) ^ (s - finrank ℝ V) ≤ 1 + r := by
    calc (1 + r) ^ (s - finrank ℝ V) ≤ (1 + r) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 + r := Real.rpow_one _
  have hA : 0 ≤ r ^ (-(finrank ℝ V : ℝ)) := by positivity
  have hB : 0 ≤ (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by positivity
  calc ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M)
      ≤ ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-s) * (1 + r) ^ (s - M) :=
        Summable.tsum_le_tsum hle hsumM (hsum.mul_right _)
    _ = (∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-s)) * (1 + r) ^ (s - M) :=
        tsum_mul_right
    _ ≤ (K * r ^ (-(finrank ℝ V : ℝ))) * (1 + r) ^ (s - M) :=
        mul_le_mul_of_nonneg_right (hsum.tsum_le_of_sum_le hfs) (by positivity)
    _ = K * (r ^ (-(finrank ℝ V : ℝ)) * (1 + r) ^ (s - finrank ℝ V)) *
          (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by rw [hsplit]; ring
    _ ≤ K * (r ^ (-(finrank ℝ V : ℝ)) * (1 + r)) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
        gcongr
    _ ≤ K * (2 * (r ^ (-(finrank ℝ V : ℝ)) + 1)) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
        gcongr
    _ ≤ (2 * K + 1) * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
        nlinarith [mul_nonneg (add_nonneg hA zero_le_one) hB]

theorem tsum_one_add_norm_rpow_neg_le_regimes (hD : 1 ≤ finrank ℝ V) {M : ℝ}
    (hM : (finrank ℝ V : ℝ) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup V) (r : ℝ), 0 < r → (∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) →
      Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-M)) ∧
      (r ≤ 1 → ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M) ≤
        C * r ^ (-(finrank ℝ V : ℝ))) ∧
      (1 ≤ r → ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M) ≤
        C * r ^ ((finrank ℝ V : ℝ) - M)) := by
  obtain ⟨C, hC, h⟩ := tsum_one_add_norm_rpow_neg_le hD hM
  have hD0 : (0 : ℝ) ≤ finrank ℝ V := Nat.cast_nonneg _
  refine ⟨2 * C, by positivity, fun Λ r hr hmin => ⟨(h Λ r hr hmin).1, fun hr1 => ?_, fun hr1 => ?_⟩⟩
  · have hb := (h Λ r hr hmin).2
    have e1 : (1 + r) ^ ((finrank ℝ V : ℝ) - M) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have e2 : 1 ≤ r ^ (-(finrank ℝ V : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
    have e3 : 0 ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) := by positivity
    calc _ ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := hb
      _ ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * 1 := mul_le_mul_of_nonneg_left e1 e3
      _ ≤ 2 * C * r ^ (-(finrank ℝ V : ℝ)) := by nlinarith
  · have hb := (h Λ r hr hmin).2
    have e1 : (1 + r) ^ ((finrank ℝ V : ℝ) - M) ≤ r ^ ((finrank ℝ V : ℝ) - M) :=
      Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
    have e2 : r ^ (-(finrank ℝ V : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith)
    calc _ ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := hb
      _ ≤ (C * 2) * r ^ ((finrank ℝ V : ℝ) - M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC.le) e1 (by positivity)
            (by positivity)
      _ = 2 * C * r ^ ((finrank ℝ V : ℝ) - M) := by ring

end GlobalTheory.LatticeCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSetIntegralEqZeroOfStabilizer
section
open MeasureTheory MulAction
open scoped Pointwise ENNReal

namespace GlobalTheory

section SlopeTestRemainingChoices
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem setIntegral_subgroup_mul_left (ν : Measure G) [ν.IsMulLeftInvariant] {Λ : Subgroup G}
    (c : Λ) (f : G → ℂ) (s : Set G) :
    ∫ g in s, f ((c : G) * g) ∂ν = ∫ g in c • s, f g ∂ν := by
  have hpre : (fun g : G => (c : G) * g) ⁻¹' (c • s) = s := by
    ext g
    simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have h := (measurePreserving_mul_left ν (c : G)).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft (c : G)) f (c • s)
  rwa [hpre] at h

theorem setLIntegral_subgroup_mul_left (ν : Measure G) [ν.IsMulLeftInvariant] {Λ : Subgroup G}
    (c : Λ) (f : G → ℝ≥0∞) (s : Set G) :
    ∫⁻ g in s, f ((c : G) * g) ∂ν = ∫⁻ g in c • s, f g ∂ν := by
  have hpre : (fun g : G => (c : G) * g) ⁻¹' (c • s) = s := by
    ext g
    simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have h := (measurePreserving_mul_left ν (c : G)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft (c : G)) f (c • s)
  rwa [hpre] at h

theorem isFundamentalDomain_iUnion_inv_smul {ν : Measure G} [ν.IsMulLeftInvariant]
    {Λ : Subgroup G} [Countable Λ] {𝓖 : Set G} (h : IsFundamentalDomain Λ 𝓖 ν)
    (S : Subgroup Λ) [Countable (Λ ⧸ S)] :
    IsFundamentalDomain (S.map Λ.subtype) (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ν := by
  refine ⟨.iUnion (fun q => h.nullMeasurableSet_smul q.out⁻¹), ?_, ?_⟩
  · filter_upwards [h.ae_covers] with g hg
    obtain ⟨l, hl⟩ := hg
    have hs : ((QuotientGroup.mk l : Λ ⧸ S).out)⁻¹ * l ∈ S :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
    refine ⟨⟨(((QuotientGroup.mk l : Λ ⧸ S).out⁻¹ * l : Λ) : G), ⟨_, hs, rfl⟩⟩,
      Set.mem_iUnion.2 ⟨QuotientGroup.mk l, ?_⟩⟩
    rw [Set.mem_inv_smul_set_iff]
    simpa [Subgroup.smul_def, mul_assoc] using hl
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
    have hsub : (⟨Λ.subtype s', hs⟩ : S.map Λ.subtype) • (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ∩
        (⟨Λ.subtype t', ht⟩ : S.map Λ.subtype) • (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ⊆
        ⋃ q : Λ ⧸ S, ⋃ r : Λ ⧸ S, ((s' * (q.out)⁻¹) • 𝓖 ∩ (t' * (r.out)⁻¹) • 𝓖) := by
      rintro x ⟨hx1, hx2⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_iUnion] at hx1 hx2
      obtain ⟨q, hq⟩ := hx1
      obtain ⟨r, hr⟩ := hx2
      rw [Set.mem_inv_smul_set_iff] at hq hr
      refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨r, ?_, ?_⟩⟩
      · rw [Set.mem_smul_set_iff_inv_smul_mem]
        simpa [Subgroup.smul_def, mul_assoc] using hq
      · rw [Set.mem_smul_set_iff_inv_smul_mem]
        simpa [Subgroup.smul_def, mul_assoc] using hr
    refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun r => ?_)
    apply h.aedisjoint
    intro he
    apply hst
    have he' : (q.out) * s'⁻¹ = (r.out) * t'⁻¹ := by
      have := congrArg (·⁻¹) he
      simpa [mul_inv_rev] using this
    have hqr : q = r := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
      apply QuotientGroup.eq.mpr
      have : (q.out)⁻¹ * r.out = s'⁻¹ * t' := by
        rw [← mul_inv_eq_iff_eq_mul.mpr he'.symm]
        group
      rw [this]
      exact S.mul_mem (S.inv_mem hs') ht'
    subst hqr
    have : s' = t' := by simpa using he'
    subst this
    rfl

end SlopeTestRemainingChoices

theorem tsum_setIntegral_eq_zero_of_stabilizer :
    ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G)
    [ν.IsMulLeftInvariant], SFinite ν → ∀ (Λ : Subgroup G), Countable Λ → ∀ 𝓖 : Set G,
    IsFundamentalDomain Λ 𝓖 ν → ∀ (a : Λ → X → X), (∀ x, a 1 x = x) →
    (∀ γ δ x, a (γ * δ) x = a γ (a δ x)) → ∀ F : X → G → ℂ,
    (∀ γ x g, F (a γ x) g = F x ((γ : G)⁻¹ * g)) → (∀ x, AEStronglyMeasurable (F x) ν) →
    ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν ≠ ⊤ →
    (∀ x (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x = x) → ∀ 𝓓 : Set G,
      IsFundamentalDomain Γ 𝓓 ν → IntegrableOn (F x) 𝓓 ν → ∫ g in 𝓓, F x g ∂ν = 0) →
    ∑' x, ∫ g in 𝓖, F x g ∂ν = 0 := by
  intro G X _ _ _ ν _ _ Λ hΛ 𝓖 h𝓖 a ha1 ham F hF hmeas hfin hzero
  letI : MulAction Λ X := { smul := a, one_smul := ha1, mul_smul := ham }
  have hsmul : ∀ (γ : Λ) (x : X), γ • x = a γ x := fun _ _ => rfl
  set T : X → ℂ := fun x => ∫ g in 𝓖, F x g ∂ν with hTdef
  have hT : ∀ (γ : Λ) x, T (γ • x) = ∫ g in γ⁻¹ • 𝓖, F x g ∂ν := by
    intro γ x
    rw [← setIntegral_subgroup_mul_left ν γ⁻¹]
    simp only [hTdef, hsmul, hF, Subgroup.coe_inv]
  have hL : ∀ (γ : Λ) x, ∫⁻ g in 𝓖, ‖F (γ • x) g‖ₑ ∂ν = ∫⁻ g in γ⁻¹ • 𝓖, ‖F x g‖ₑ ∂ν := by
    intro γ x
    rw [← setLIntegral_subgroup_mul_left ν γ⁻¹]
    simp only [hsmul, hF, Subgroup.coe_inv]
  have hsum : Summable T := by
    refine Summable.of_norm ?_
    have h1 : ∑' x, ‖T x‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hfin
      (ENNReal.tsum_le_tsum fun x => enorm_integral_le_lintegral_enorm _)
    simpa using ENNReal.summable_toReal h1
  have horb : ∀ x₀ : X,
      HasSum (fun q : Λ ⧸ stabilizer Λ x₀ => T (ofQuotientStabilizer Λ x₀ q)) 0 := by
    intro x₀
    set S := stabilizer Λ x₀ with hSdef
    haveI : Countable (Λ ⧸ S) := QuotientGroup.mk_surjective.countable
    have hofq : ∀ q : Λ ⧸ S, ofQuotientStabilizer Λ x₀ q = q.out • x₀ := by
      intro q
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hinj : Function.Injective fun q : Λ ⧸ S => q.out • x₀ := by
      intro q r hqr
      exact injective_ofQuotientStabilizer Λ x₀ (by simpa only [hofq] using hqr)
    have hD := isFundamentalDomain_iUnion_inv_smul h𝓖 S
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν) fun q : Λ ⧸ S => (q.out)⁻¹ • 𝓖) := by
      intro q r hqr
      refine h𝓖.aedisjoint fun e => hqr ?_
      exact Quotient.out_injective (inv_injective e)
    have hint : IntegrableOn (F x₀) (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ν := by
      refine ⟨(hmeas x₀).restrict, ?_⟩
      show ∫⁻ g in ⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν < ⊤
      calc ∫⁻ g in ⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν
          ≤ ∑' q : Λ ⧸ S, ∫⁻ g in (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν := lintegral_iUnion_le _ _
        _ = ∑' q : Λ ⧸ S, ∫⁻ g in 𝓖, ‖F (q.out • x₀) g‖ₑ ∂ν := by simp only [hL]
        _ ≤ ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun x => ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν)
        _ < ⊤ := hfin.lt_top
    have hmem : ∀ g, g ∈ S.map Λ.subtype ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x₀ = x₀ := by
      intro g
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h, hx⟩
        exact ⟨⟨g, h⟩, hx, rfl⟩
    have h0 := hzero x₀ (S.map Λ.subtype) hmem _ hD hint
    have hs := hasSum_integral_iUnion_ae (fun q => h𝓖.nullMeasurableSet_smul _) hdisj hint
    rw [h0] at hs
    simpa only [hofq, hT] using hs
  let e := selfEquivSigmaOrbitsQuotientStabilizer Λ X
  have h1 : HasSum (T ∘ e.symm) (∑' x, T x) := (e.symm.hasSum_iff).2 hsum.hasSum
  have h2 : HasSum (fun _ : Quotient (orbitRel Λ X) => (0 : ℂ)) (∑' x, T x) := by
    refine h1.sigma fun ω => ?_
    convert horb ω.out using 2 with q
    rfl
  exact h2.unique hasSum_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSetIntegralProdEqZeroOfInner
section
open MeasureTheory

namespace GlobalTheory

theorem tsum_setIntegral_prod_eq_zero_of_inner :
    ∀ {G X : Type} [MeasurableSpace G], Countable X → ∀ (ν : Measure G), SFinite ν → ∀ (𝓖 : Set G) (H : X → G × G → ℂ), (∀ x, AEStronglyMeasurable (H x) (ν.prod ν)) → ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' x, ‖H x (g₁, g₂)‖ₑ ∂ν ∂ν ≠ ⊤ → (∀ g₂, ∑' x, ∫⁻ g₁ in 𝓖, ‖H x (g₁, g₂)‖ₑ ∂ν ≠ ⊤ → ∑' x, ∫ g₁ in 𝓖, H x (g₁, g₂) ∂ν = 0) → ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν) = 0 := by
  intro G X _ hX ν hν 𝓖 H hH hfin hslice
  set μ := ν.restrict 𝓖 with hμ
  have hprod : (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) = μ.prod μ := (Measure.prod_restrict 𝓖 𝓖).symm
  have hHm : ∀ x, AEStronglyMeasurable (H x) (μ.prod μ) := fun x => by
    rw [← hprod]; exact (hH x).restrict
  have hFm : AEMeasurable (fun p => ∑' x, ‖H x p‖ₑ) (μ.prod μ) :=
    AEMeasurable.tsum fun x => (hHm x).enorm
  have hFint : ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) ≠ ⊤ := by
    rw [lintegral_prod _ hFm]; exact hfin
  have hsum : ∑' x, ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) = ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) :=
    (lintegral_tsum fun x => (hHm x).enorm).symm
  have hInt : ∀ x, Integrable (H x) (μ.prod μ) := fun x =>
    ⟨hHm x, by
      have : ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) ≤ ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) :=
        lintegral_mono fun p => ENNReal.le_tsum (f := fun x => ‖H x p‖ₑ) x
      exact lt_of_le_of_lt this (lt_top_iff_ne_top.2 hFint)⟩
  have hswap : ∀ x, ∫⁻ g₂, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ∂μ = ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) :=
    fun x => (lintegral_prod_symm _ (hHm x).enorm).symm
  have hLm : ∀ x, AEMeasurable (fun g₂ => ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ) μ := fun x =>
    ((hHm x).enorm.prod_swap).lintegral_prod_right'
  have hG2 : ∀ᵐ g₂ ∂μ, ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ≠ ⊤ := by
    have hm : AEMeasurable (fun g₂ => ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ) μ :=
      AEMeasurable.tsum hLm
    have hi : ∫⁻ g₂, ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum hLm, tsum_congr hswap, hsum]; exact hFint
    filter_upwards [ae_lt_top' hm hi] with g₂ h using h.ne
  have hKm : ∀ x, AEStronglyMeasurable (fun g₂ => ∫ g₁, H x (g₁, g₂) ∂μ) μ := fun x =>
    (hHm x).prod_swap.integral_prod_right'
  have hKfin : ∑' x, ∫⁻ g₂, ‖∫ g₁, H x (g₁, g₂) ∂μ‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hFint ?_
    rw [← hsum]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← hswap x]
    exact lintegral_mono fun g₂ => enorm_integral_le_lintegral_enorm _
  have key := integral_tsum hKm hKfin
  have h0 : ∫ g₂, ∑' x, ∫ g₁, H x (g₁, g₂) ∂μ ∂μ = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hG2] with g₂ h using hslice g₂ h
  calc ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν)
        = ∑' x, ∫ g₂, ∫ g₁, H x (g₁, g₂) ∂μ ∂μ := by
          refine tsum_congr fun x => ?_
          rw [hprod]; exact integral_prod_symm _ (hInt x)
    _ = 0 := by rw [← key, h0]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricMatrixInvNearOne
section
namespace GlobalTheory

theorem matrix_inv_near_one : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n]
    [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 →
    (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by
  intro E _ _ n _ _ X Z t ht0 ht1 hZX hX i j
  have key : Z - 1 = -((X - 1) + (Z - 1) * (X - 1)) := by
    have h : (Z - 1) * (X - 1) = Z * X - Z - X + 1 := by noncomm_ring
    rw [h, hZX]; abel
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨i0, j0⟩, hmax⟩ := Finite.exists_max (fun p : n × n => ‖(Z - 1) p.1 p.2‖)
  set s := ‖(Z - 1) i0 j0‖ with hs
  have hbound : ∀ a b, ‖(Z - 1) a b‖ ≤ max t (s * t) := by
    intro a b
    have hprod : ‖((Z - 1) * (X - 1)) a b‖ ≤ s * t := by
      rw [Matrix.mul_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg (norm_nonneg _) ht0) fun k _ => ?_
      rw [norm_mul]
      exact mul_le_mul (hmax (a, k)) (hX k b) (norm_nonneg _) (norm_nonneg _)
    rw [key, Matrix.neg_apply, norm_neg, Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hX a b) hprod)
  have hs0 : 0 ≤ s := norm_nonneg _
  have hst : s ≤ t := by
    by_contra hlt
    push_neg at hlt
    have h1 := hbound i0 j0
    rw [← hs] at h1
    rcases le_max_iff.mp h1 with h | h
    · linarith
    · nlinarith
  exact (hmax (i, j)).trans hst

end GlobalTheory
end

