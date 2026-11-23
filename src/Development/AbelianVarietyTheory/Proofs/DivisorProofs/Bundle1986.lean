module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1938
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmBilinFormEqZeroOfWeightedQuadraticSumLifts
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Span

lemma dvd_apply_of_coord {r : ℕ} (N : ℤ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (d z : Fin r → ℤ)
    (hd : ∀ i, N ∣ d i) : N ∣ b d z := by
  choose ν hν using hd
  have : d = N • ν := by funext i; simp [hν i]
  rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

lemma qW_dvd {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N : ℕ) [NeZero N]
    (μ : (Fin s → Fin r → ZMod N) → (Fin s → Fin r → ℤ)) (hμ : ∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i)
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hb : ∀ x y, b x y = b y x) (h0 : ∀ c, qW W b (μ c) = 0)
    (y : Fin s → Fin r → ℤ) : (N : ℤ) ∣ qW W b y := by
  set c : Fin s → Fin r → ZMod N := fun u i => (y u i : ZMod N)
  have hd : ∀ u i, (N : ℤ) ∣ y u i - μ c u i := by
    intro u i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hμ]; simp [c]
  have key : qW W b y = qW W b y - qW W b (μ c) := by rw [h0]; ring
  rw [key, qW, qW, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun v _ => ?_
  rw [← mul_sub]
  refine dvd_mul_of_dvd_right ?_ _
  have e : b (y u) (y v) - b (μ c u) (μ c v) = b (y u - μ c u) (y v) + b (y v - μ c v) (μ c u) := by
    rw [hb (y v - μ c v) (μ c u)]
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [e]
  exact dvd_add (dvd_apply_of_coord _ b _ _ fun i => by simpa using hd u i)
    (dvd_apply_of_coord _ b _ _ fun i => by simpa using hd v i)

lemma dvd_all {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N : ℕ) [NeZero N]
    (hε : ∃ ε : Fin s → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs))
    (μ : (Fin s → Fin r → ZMod N) → (Fin s → Fin r → ℤ)) (hμ : ∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i)
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hb : ∀ x y, b x y = b y x) (h0 : ∀ c, qW W b (μ c) = 0) :
    ∀ x z, (N : ℤ) ∣ b x z := by
  obtain ⟨ε, hε⟩ := hε
  set q := ∑ u, ∑ v, W u v * ε u * ε v with hq
  have hcop : IsCoprime (N : ℤ) q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Nat.Coprime.coprime_mul_left_right hε
    simpa [Int.gcd] using this
  have h2 : IsCoprime (N : ℤ) 2 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Nat.Coprime.coprime_mul_right_right hε
    simpa [Int.gcd] using this
  have hxx : ∀ x, (N : ℤ) ∣ b x x := by
    intro x
    have h := qW_dvd W N μ hμ b hb h0 (fun u => ε u • x)
    have e : qW W b (fun u => ε u • x) = q * b x x := by
      simp only [qW, map_smul, LinearMap.smul_apply, smul_eq_mul, hq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [e] at h
    exact hcop.dvd_of_dvd_mul_left h
  intro x z
  have e : 2 * b x z = b (x + z) (x + z) - b x x - b z z := by
    simp only [map_add (f := _), LinearMap.add_apply, hb z x]
    ring
  have h : (N : ℤ) ∣ 2 * b x z := by
    rw [e]; exact dvd_sub (dvd_sub (hxx _) (hxx x)) (hxx z)
  exact h2.dvd_of_dvd_mul_left h

end GlobalTheory.Poinc.Span

namespace GlobalTheory.Poinc.Span

lemma pow_dvd_all {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N : ℕ) [NeZero N]
    (hε : ∃ ε : Fin s → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs))
    (μ : (Fin s → Fin r → ZMod N) → (Fin s → Fin r → ℤ)) (hμ : ∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i)
    (k : ℕ) : ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ c, qW W b (μ c) = 0) →
      ∀ x z, (N : ℤ) ^ k ∣ b x z := by
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro b hb h0 x z
    have hd := dvd_all W N hε μ hμ b hb h0
    let b' : LinearMap.BilinForm ℤ (Fin r → ℤ) := LinearMap.mk₂ ℤ (fun x z => b x z / N)
      (fun m₁ m₂ n => by simp only [map_add (f := _), LinearMap.add_apply, Int.add_ediv_of_dvd_left (hd m₁ n)])
      (fun c m n => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Int.mul_ediv_assoc c (hd m n)])
      (fun m n₁ n₂ => by simp only [map_add (f := _), Int.add_ediv_of_dvd_left (hd m n₁)])
      (fun c m n => by simp only [map_smul, smul_eq_mul, Int.mul_ediv_assoc c (hd m n)])
    have hbb : ∀ x z, b x z = N * b' x z := fun x z => by
      simp only [b', LinearMap.mk₂_apply]; exact (Int.mul_ediv_cancel' (hd x z)).symm
    have hb' : ∀ x z, b' x z = b' z x := fun x z => by simp only [b', LinearMap.mk₂_apply, hb x z]
    have h0' : ∀ c, qW W b' (μ c) = 0 := by
      intro c
      have e : qW W b (μ c) = N * qW W b' (μ c) := by
        simp only [qW, hbb, Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
      have := h0 c
      rw [e] at this
      exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast NeZero.ne N)
    rw [hbb, pow_succ, mul_comm ((N : ℤ) ^ k)]
    exact mul_dvd_mul_left _ (ih b' hb' h0' x z)

end GlobalTheory.Poinc.Span

theorem GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts :
    ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ,
      (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) →
      ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) →
      ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ c, qW W b (μ c) = 0) → b = 0 := by
  intro W _ N _ hN r hε μ hμ b hb h0
  refine LinearMap.ext₂ fun x z => ?_
  have h := GlobalTheory.Poinc.Span.pow_dvd_all W N hε μ hμ (b x z).natAbs b hb h0 x z
  simp only [LinearMap.zero_apply]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentNormalizedHaarLeTwoMulLieHaar
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.UpDens

open Filter Topology Metric Set GlobalTheory.SUVol.DensOne
open scoped NNReal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem tangentHaar_le_two_mul_lam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤ 2 * lam s := by
  intro E _ _ _ r Ψ G hG lam _
  obtain ⟨hH, hD⟩ := tangentHaar_realSU_of_det Ψ G hG lam
  generalize tangentHaar (realSU Ψ G) (lam.map Subtype.val) = μ at hH hD ⊢
  let ι : realLie Ψ G →ₗᵢ[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    ⟨(incl Ψ G).toLinearMap, fun X => norm_incl Ψ G X⟩
  let L₀ : (Ψ → Matrix (Fin r) (Fin r) ℂ) →ₗ[ℝ]
      ((Ψ → Matrix (Fin r) (Fin r) ℂ) →L[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  have he : Continuous (chartExp Ψ G hG) := continuous_chartExp Ψ G hG
  have he0 : chartExp Ψ G hG 0 = 1 := chartExp_zero Ψ G hG
  have hd : HasStrictFDerivAt (fun x => matR Ψ G (chartExp Ψ G hG x)) ι.toContinuousLinearMap 0 :=
    hasStrictFDerivAt_chart Ψ G hG
  have hL : ContinuousAt (fun g => L₀ (matR Ψ G g)) 1 := (hL₀.comp (continuous_matR Ψ G)).continuousAt
  have hL1 : (fun g => L₀ (matR Ψ G g)) 1 = ContinuousLinearMap.id ℝ _ := by ext1 A; exact one_mul A
  have hm : ∀ g h, matR Ψ G (g * h) = (fun g => L₀ (matR Ψ G g)) g (matR Ψ G h) := fun g h => rfl
  have hn : ∀ ρ : ℝ, 0 < ρ → chartExp Ψ G hG '' ball 0 ρ ∈ 𝓝 (1 : realSU Ψ G) := fun ε hε =>
    (tendsto_iff_comap.1 ((continuous_matR Ψ G).tendsto 1))
      (eventually_mem_image Ψ G hG (ball_mem_nhds 0 hε))

  haveI : ProperSpace (realLie Ψ G) := FiniteDimensional.proper_real _
  obtain ⟨δ₀, hδ₀, hinj⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ InjOn (chartExp Ψ G hG) (closedBall 0 δ₀) := by
    obtain ⟨s, hs, ha⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
    obtain ⟨δ, hδ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hs
    refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
    have h1 := ha x (hsub hx) y (hsub hy)
    simp only [hxy, sub_self, zero_sub, norm_neg, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] at h1
    have h2 : ‖x - y‖ ≤ 0 := by
      have h3 : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
      rw [h3] at h1
      linarith
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  have hK : MeasurableSet (closedBall (0 : realLie Ψ G) δ₀) := measurableSet_closedBall
  have hemb := ContinuousOn.measurableEmbedding hK he.continuousOn hinj
  set ν : Measure (realLie Ψ G) :=
    (μ.comap ((closedBall (0 : realLie Ψ G) δ₀).domRestrict (chartExp Ψ G hG))).map Subtype.val with hν
  have hνS : ∀ S : Set (realLie Ψ G), MeasurableSet S →
      ν S = μ (chartExp Ψ G hG '' (S ∩ closedBall 0 δ₀)) := by
    intro S hS
    rw [hν, Measure.map_apply measurable_subtype_coe hS, hemb.comap_apply]
    congr 1
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hνsub : ∀ S : Set (realLie Ψ G), MeasurableSet S → S ⊆ closedBall 0 δ₀ →
      ν S = μ (chartExp Ψ G hG '' S) := fun S hS h => by rw [hνS S hS, inter_eq_left.2 h]
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνS _ MeasurableSet.univ, univ_inter]
    exact ((isCompact_closedBall _ _).image he).measure_lt_top
  have hball : ∀ (X : realLie Ψ G) (ρ : ℝ), ‖X‖ + ρ ≤ δ₀ → ball X ρ ⊆ closedBall 0 δ₀ := by
    intro X ρ h y hy
    rw [mem_ball_iff_norm] at hy
    rw [mem_closedBall_zero_iff]
    have := norm_le_norm_add_norm_sub' y X
    linarith
  have hpos : ∀ ρ > 0, 0 < ν (closedBall (0 : realLie Ψ G) ρ) := by
    intro ρ hρ
    have h1 : ν (ball 0 (min ρ δ₀)) ≠ 0 := by
      rw [hνsub _ measurableSet_ball (hball 0 _ (by simp))]
      exact (μ.measure_pos_of_mem_nhds (hn _ (lt_min hρ hδ₀))).ne'
    exact pos_iff_ne_zero.2 fun h => h1 (measure_mono_null
      ((ball_subset_closedBall).trans (closedBall_subset_closedBall (min_le_left _ _))) h)

  have himg : ∀ (g : realSU Ψ G) (S : Set (realSU Ψ G)), μ ((fun h => g * h) '' S) = μ S := fun g S => by
    rw [image_mul_left, measure_preimage_mul]
  have hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, Formalism.BasicNotions.Examples₂.CD.QInv ν ε δ := by
    intro ε hε0 hε1
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.translate_chart_ball_distortion _ _ _ (chartExp Ψ G hG) (matR Ψ G) ι
      (fun g => L₀ (matR Ψ G g)) he he0 hd hL hL1 hm hn (1 + ε / 3) (by linarith)
    refine ⟨min (δ / 2) (δ₀ / 4), by positivity, fun X hX ρ hρ0 hρ => ?_⟩
    have hXδ : ‖X‖ < δ / 2 := lt_of_lt_of_le hX (min_le_left _ _)
    have hX4 : ‖X‖ < δ₀ / 4 := lt_of_lt_of_le hX (min_le_right _ _)
    have hρδ : ρ < δ / 2 := lt_of_lt_of_le hρ (min_le_left _ _)
    have hρ4 : ρ < δ₀ / 4 := lt_of_lt_of_le hρ (min_le_right _ _)
    have hXb : X ∈ ball (0 : realLie Ψ G) δ := mem_ball_zero_iff.2 (by linarith)
    have hκ0 : 0 < 1 + ε / 3 := by linarith
    have hκ2 : 1 + ε / 3 < 2 := by linarith
    have hcl0 : closedBall (0 : realLie Ψ G) ρ ⊆ closedBall 0 δ₀ :=
      closedBall_subset_closedBall (by linarith)
    constructor
    · have hr1 : 0 < ρ / (1 + ε / 3) := div_pos hρ0 hκ0
      have hr2 : ρ / (1 + ε / 3) < ρ := div_lt_self hρ0 (by linarith)
      have hr3 : (1 - ε) * ρ < ρ / (1 + ε / 3) := by
        rw [lt_div_iff₀ hκ0]; nlinarith [mul_pos hρ0 hε0, mul_pos (mul_pos hρ0 hε0) hε0]
      have H2 := (H X hXb (ρ / (1 + ε / 3)) ⟨hr1, by linarith⟩).2
      rw [mul_div_cancel₀ _ hκ0.ne'] at H2
      calc ν (closedBall X ((1 - ε) * ρ)) ≤ ν (ball X (ρ / (1 + ε / 3))) :=
            measure_mono (closedBall_subset_ball hr3)
        _ = μ (chartExp Ψ G hG '' ball X (ρ / (1 + ε / 3))) :=
            hνsub _ measurableSet_ball (hball X _ (by linarith))
        _ ≤ μ ((fun h => chartExp Ψ G hG X * h) '' (chartExp Ψ G hG '' ball 0 ρ)) := measure_mono H2
        _ = μ (chartExp Ψ G hG '' ball 0 ρ) := himg _ _
        _ ≤ μ (chartExp Ψ G hG '' closedBall 0 ρ) := measure_mono (image_mono ball_subset_closedBall)
        _ = ν (closedBall 0 ρ) := (hνsub _ measurableSet_closedBall hcl0).symm
    · have hr1 : 0 < (1 + ε / 3) * ρ := by positivity
      have hr2 : (1 + ε / 3) * ρ < δ := by nlinarith
      have H1 := (H X hXb ((1 + ε / 3) * ρ) ⟨hr1, hr2⟩).1
      have hsq : (1 + ε / 3) * ((1 + ε / 3) * ρ) ≤ (1 + ε) * ρ := by
        nlinarith [mul_pos (mul_pos hρ0 hε0) (by linarith : (0:ℝ) < 3 - ε)]
      calc ν (closedBall 0 ρ) ≤ ν (ball 0 ((1 + ε / 3) * ρ)) :=
            measure_mono (closedBall_subset_ball (by nlinarith))
        _ = μ (chartExp Ψ G hG '' ball 0 ((1 + ε / 3) * ρ)) :=
            hνsub _ measurableSet_ball (hball 0 _ (by rw [norm_zero]; nlinarith))
        _ = μ ((fun h => chartExp Ψ G hG X * h) '' (chartExp Ψ G hG '' ball 0 ((1 + ε / 3) * ρ))) :=
            (himg _ _).symm
        _ ≤ μ (chartExp Ψ G hG '' ball X ((1 + ε / 3) * ((1 + ε / 3) * ρ))) := measure_mono H1
        _ = ν (ball X ((1 + ε / 3) * ((1 + ε / 3) * ρ))) :=
            (hνsub _ measurableSet_ball (hball X _ (by nlinarith))).symm
        _ ≤ ν (closedBall X ((1 + ε) * ρ)) :=
            measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hsq))
  obtain ⟨c, hc0, hct, hup, hdown⟩ := Formalism.BasicNotions.Examples₂.CD.exists_density lam ν hq hpos

  have hνt : ∀ ε : ℝ, 0 < ε → (lam.map Subtype.val) (tanBall Ψ r ε) = lam (ball 0 ε) := by
    intro ε hε
    rw [Measure.map_apply measurable_subtype_coe, preimage_tanBall Ψ G hε]
    rw [show tanBall Ψ r ε = ball (0 : Ψ → Fin r → Fin r → ℂ) ε by
      ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl]
    exact measurableSet_ball
  have hc : c < ((2 : ℝ≥0) : ℝ≥0∞) := by
    by_contra hcon
    rw [not_lt] at hcon
    have h32 : (((3 / 2 : ℝ≥0)) : ℝ≥0∞) < c :=
      lt_of_lt_of_le (by rw [ENNReal.coe_lt_coe]; norm_num) hcon
    obtain ⟨δ₁, hδ₁, H1⟩ := hdown (3 / 2) h32
    obtain ⟨t, ht1, htn⟩ : ∃ t : ℝ, 1 < t ∧ t ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 := by
      have h := ((continuous_pow (Module.finrank ℝ (realLie Ψ G))).tendsto (1 : ℝ)).eventually
        (gt_mem_nhds (show (1 : ℝ) ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 by norm_num))
      have h' : ∀ᶠ x in 𝓝[>] (1 : ℝ), x ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 :=
        h.filter_mono nhdsWithin_le_nhds
      obtain ⟨t, h1, h2⟩ := (h'.and self_mem_nhdsWithin).exists
      exact ⟨t, h2, h1⟩
    have ht0 : 0 < t := by linarith
    have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((3 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t⁻¹ ^ Module.finrank ℝ (realLie Ψ G)) ≤
        μ (grpBall (realSU Ψ G) ε) / (lam.map Subtype.val) (tanBall Ψ r ε) := by
      filter_upwards [chart_squeeze Ψ G hG ht1,
        Ioo_mem_nhdsGT (show 0 < min δ₁ δ₀ * t by positivity)] with ε hsq hε
      obtain ⟨hε0, hε1⟩ := hε
      have hte : t⁻¹ * ε < min δ₁ δ₀ := by
        rw [inv_mul_lt_iff₀ ht0, mul_comm]; exact hε1
      rw [lt_min_iff] at hte
      rw [hνt ε hε0]
      rw [ENNReal.le_div_iff_mul_le (Or.inl (measure_ball_pos lam 0 hε0).ne')
        (Or.inl measure_ball_lt_top.ne)]
      calc ((3 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t⁻¹ ^ Module.finrank ℝ (realLie Ψ G)) * lam (ball 0 ε)
          = ((3 / 2 : ℝ≥0) : ℝ≥0∞) * lam (ball 0 (t⁻¹ * ε)) := by
            rw [Measure.addHaar_ball_mul_of_pos lam 0 hti0 ε, mul_assoc]
        _ ≤ ν (ball 0 (t⁻¹ * ε)) := H1 _ (ball_subset_ball hte.1.le)
        _ = μ (chartExp Ψ G hG '' ball 0 (t⁻¹ * ε)) :=
            hνsub _ measurableSet_ball (hball 0 _ (by rw [norm_zero]; linarith))
        _ ≤ μ (grpBall (realSU Ψ G) ε) := measure_mono hsq.1
    have h1 := ge_of_tendsto hD hev
    have h2 : 1 < ((3 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t⁻¹ ^ Module.finrank ℝ (realLie Ψ G)) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
        ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      have hp : 0 < t ^ Module.finrank ℝ (realLie Ψ G) := by positivity
      rw [inv_pow]
      push_cast
      rw [← div_eq_mul_inv, lt_div_iff₀ hp]
      linarith
    exact absurd h1 (not_le.2 h2)
  obtain ⟨δ₂, hδ₂, H2⟩ := hup 2 hc
  refine ⟨min δ₂ δ₀, lt_min hδ₂ hδ₀, fun s hs hsub => ?_⟩
  have h1 := H2 s (hsub.trans (ball_subset_ball (min_le_left _ _)))
  have h2 : ν s = μ (chartExp Ψ G hG '' s) :=
    hνsub s hs (hsub.trans ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall))
  rw [← h2]
  calc ν s ≤ ((2 : ℝ≥0) : ℝ≥0∞) * lam s := h1
    _ = 2 * lam s := by norm_num

end GlobalTheory.CovTop.VolUp.UpDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitary
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaRatPair

theorem det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id]
    simp [Matrix.transpose_submatrix, Matrix.submatrix_map]
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self] at this
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at this
  exact pow_ne_zero s (by norm_num : (-1 : ℂ) ≠ 0) this.symm

theorem det_ne_zero_of_map {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem thetaSum_om_rat : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine det_ne_zero_of_map W.J (B.emb w).1 fun h0 => det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ

end GlobalTheory.ThetaRatPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtFiniteSet
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.PureStabFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (c : AF F) (g₁ g : UA σ J)
    (hg : c • (mat g - 1) = 0) (hg₁ : c • (mat g₁ - 1) = 0) : c • (mat (g₁⁻¹ * g) - 1) = 0 := by
  have hmul : mat (g₁⁻¹ * g) = mat g₁⁻¹ * mat g := rfl
  have hNM : mat g₁⁻¹ * mat g₁ = 1 := by
    change ((g₁.1⁻¹ : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (g₁.1 : Matrix _ _ _) = 1
    exact Units.inv_mul g₁.1
  have key : mat (g₁⁻¹ * g) - 1 = mat g₁⁻¹ * (mat g - 1) - mat g₁⁻¹ * (mat g₁ - 1) := by
    rw [hmul, Matrix.mul_sub, Matrix.mul_sub, hNM, Matrix.mul_one]; abel
  rw [key, smul_sub, ← Matrix.mul_smul, ← Matrix.mul_smul, hg, hg₁, Matrix.mul_zero, sub_zero]

open scoped Classical in
theorem supp_of_split {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (w : Pl (F := F)) (S : Finset (Pl (F := F)))
    (g₁ g₂ : UA σ J) (hg : ∀ u : AF F, (∀ x ∈ insert w S, evFin F x u = 0) → u • (mat (g₁ * g₂) - 1) = 0)
    (hg₁ : At (evFin F w) (mat g₁ - 1)) (hg₂ : ∀ u : AF F, At (evFin F w) u → u • (mat g₂ - 1) = 0) :
    ∀ u : AF F, (∀ x ∈ S, evFin F x u = 0) → u • (mat g₂ - 1) = 0 := by
  intro u hu
  set e : AF F := GlobalTheory.UnitaryPlaceSplit.idemAt w with he
  have hew : evFin F w e = 1 := GlobalTheory.UnitaryPlaceSplit.evFin_idemAt w
  have h1 : At (evFin F w) (u * e) := fun u' hu' => by
    change u' * (u * e) = 0
    rw [← mul_assoc]
    exact GlobalTheory.UnitaryPlaceSplit.mul_idemAt_of_evFin w (by rw [map_mul, hu', zero_mul])
  have hcw : evFin F w (u * (1 - e)) = 0 := by rw [map_mul, map_sub, map_one, hew, sub_self, mul_zero]
  have h2 : (u * (1 - e)) • (mat g₂ - 1) = 0 := by
    have e2 : g₂ = g₁⁻¹ * (g₁ * g₂) := (inv_mul_cancel_left g₁ g₂).symm
    rw [e2]
    refine smul_mat_inv_mul _ _ _ (hg _ fun x hx => ?_) (hg₁ _ hcw)
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hcw
    · rw [map_mul, hu x hx, zero_mul]
  have hsplit : u = u * e + u * (1 - e) := by ring
  rw [hsplit, add_smul, hg₂ _ h1, h2, add_zero]

theorem pure_stab_fin : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g - 1) = 0) →
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ₂ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ∉ S → φ₂ w = φ w) ∧ om' (g, h) (pure f φ) = pure f φ₂ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro g h hg hh f φ hφ hcof
    have hg1 : g = 1 := by
      have := hg 1 (by simp)
      rw [one_smul, sub_eq_zero] at this
      exact Subtype.ext (Units.ext this)
    have hh1 : h = 1 := by
      have := hh 1 (by simp)
      rw [one_smul, sub_eq_zero] at this
      exact Subtype.ext (Units.ext this)
    subst hg1 hh1
    refine ⟨φ, hφ, fun _ _ => rfl, ?_⟩
    rw [Prod.mk_one_one, map_one]
    rfl
  | insert w S hw ih =>
    intro g h hg hh f φ hφ hcof
    obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := GlobalTheory.UnitaryPlaceSplit.exists_split_at F E σ a' G.V'.J w g
    obtain ⟨h₁, h₂, rfl, hh₁, hh₂⟩ := GlobalTheory.UnitaryPlaceSplit.exists_split_at F E σ (a + a') G.W.J w h
    have hg₂S := supp_of_split w S g₁ g₂ hg hg₁ hg₂
    have hh₂S := supp_of_split w S h₁ h₂ hh hh₁ hh₂
    obtain ⟨φ₂, hφ₂, hφ₂S, hφ₂e⟩ := ih g₂ h₂ hg₂S hh₂S f φ hφ hcof
    have hcof₂ : ∀ᶠ x in Filter.cofinite, φ₂ x = G.M'.vac x := by
      filter_upwards [hcof, S.eventually_cofinite_notMem] with x hx hxS
      rw [hφ₂S x hxS, hx]
    obtain ⟨φ', hφ', hφ'w, -, hφ'e⟩ :=
      GlobalTheory.T.local_unitary_action_schwartz_inf hP F E σ B a a' G X om om' hT w g₁ hg₁ h₁ hh₁ f φ₂ hφ₂ hcof₂
    refine ⟨φ', hφ', fun x hx => ?_, ?_⟩
    · rw [Finset.mem_insert, not_or] at hx
      rw [hφ'w x hx.1, hφ₂S x hx.2]
    · have hpr : ((g₁ * g₂, h₁ * h₂) : UA σ G.V'.J × UA σ G.W.J) = (g₁, h₁) * (g₂, h₂) := rfl
      rw [hpr, map_mul, Module.End.mul_apply, hφ₂e, hφ'e]

end GlobalTheory.PureStabFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionDualCharValuesMulCubeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_dualCharValues_mul_cube : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)) (χ χ' : D.X),
    vE (gm.s (χ + χ')) (𝟙 _) ν.J *
        vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      vE (gm.s χ) (𝟙 _) ν.J * vE (gm.s χ') (𝟙 _) ν.J := by
  first | exact @GlobalTheory.DualMult.mult_vE | exact GlobalTheory.DualMult.mult_vE | (intros; apply GlobalTheory.DualMult.mult_vE <;> assumption)
end

