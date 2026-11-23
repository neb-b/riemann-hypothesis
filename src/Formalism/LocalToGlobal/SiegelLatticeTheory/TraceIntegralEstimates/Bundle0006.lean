module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ConvGGG
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.S.Pv.ConvG

open Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem weil_inv {μ μS ν : Measure G} [SFinite μS] [SFinite ν]
    (hW : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) (Ψ : G → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z, ∫⁻ s, Ψ (s⁻¹ * z) ∂μS ∂ν = ∫⁻ x, Ψ x ∂μ := by
  rw [hW Ψ hΨ]
  refine lintegral_congr fun z => ?_
  have hm : Measurable (fun s : G => Ψ (s * z)) := hΨ.comp (measurable_id.mul measurable_const)
  conv_rhs => rw [← hinv]
  rw [lintegral_map hm measurable_inv]

variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
  {V V' : Type} [NormedAddCommGroup V] [NormedAddCommGroup V']

@[irreducible] def PhiGG (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (W' : G → V') (γ : G) (a b : G) : ℝ≥0∞ :=
  ‖⟪σ a w, σ γ (σ b w)⟫_ℂ‖ₑ * ‖W a‖ₑ * ‖W' b‖ₑ

theorem measurable_PhiGG {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun p : G × G => PhiGG σ w W W' γ p.1 p.2) := by
  unfold PhiGG
  have h1 : Continuous (fun p : G × G => ⟪σ p.1 w, σ γ (σ p.2 w)⟫_ℂ) :=
    Continuous.inner (𝕜 := ℂ) ((hσ.2.2.2 w).comp continuous_fst)
      ((σ γ).continuous.comp ((hσ.2.2.2 w).comp continuous_snd))
  exact ((h1.enorm.measurable).mul ((hW.comp continuous_fst).enorm.measurable)).mul
    ((hW'.comp continuous_snd).enorm.measurable)

theorem quad_eq_GG {μ μS ν μS' ν' : Measure G} [SFinite μS] [SFinite ν] [SFinite μS'] [SFinite ν'] [SFinite μ]
    {S S' : Set G} {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hWc : Continuous W) (hWc' : Continuous W')
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hWe' : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS' ∂ν')
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) (hiS : ∀ a ∈ S, a⁻¹ ∈ S) (hiS' : ∀ a ∈ S', a⁻¹ ∈ S')
    (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) (hWS' : ∀ s ∈ S', ∀ x, ‖W' (s * x)‖ = ‖W' x‖) (γ : G) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂μS ∂ν' ∂ν =
      ∫⁻ x, ∫⁻ y, PhiGG σ w W W' γ x y ∂μ ∂μ := by
  have hΦ := measurable_PhiGG hσ w hWc hWc' γ

  have hpt : ∀ z z' s s', s ∈ S → s' ∈ S' →
      ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ = PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') := by
    intro z z' s s' hs hs'
    unfold PhiGG
    rw [coef_shift hσ w γ z s z' s']
    have e1 : ‖W (s⁻¹ * z)‖ₑ = ‖W z‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS _ (hiS s hs)]
    have e2 : ‖W' (s'⁻¹ * z')‖ₑ = ‖W' z'‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS' _ (hiS' s' hs')]
    rw [e1, e2]
  have haeS : ∀ᵐ s ∂μS, s ∈ S := by rw [ae_iff]; exact h0
  have haeS' : ∀ᵐ s ∂μS', s ∈ S' := by rw [ae_iff]; exact h0'
  have hin : ∀ z z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂μS =
      ∫⁻ s, ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂μS := by
    intro z z'
    refine lintegral_congr_ae ?_
    filter_upwards [haeS] with s hs
    refine lintegral_congr_ae ?_
    filter_upwards [haeS'] with s' hs'
    exact hpt z z' s s' hs hs'
  simp only [hin]

  have hswap : ∀ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂μS ∂ν' =
      ∫⁻ s, ∫⁻ z', ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂ν' ∂μS := by
    intro z
    have hm : Measurable (Function.uncurry fun z' s : G => ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS') := by
      have hg : Measurable (fun q : (G × G) × G => ((q.1.2⁻¹ * z, q.2⁻¹ * q.1.1) : G × G)) :=
        (((measurable_snd.comp measurable_fst).inv.mul measurable_const)).prodMk
          ((measurable_snd.inv).mul (measurable_fst.comp measurable_fst))
      have h3 : Measurable (fun q : (G × G) × G => PhiGG σ w W W' γ (q.1.2⁻¹ * z) (q.2⁻¹ * q.1.1)) :=
        hΦ.comp hg
      exact h3.lintegral_prod_right'
    exact lintegral_lintegral_swap hm.aemeasurable
  simp only [hswap]

  have hy : ∀ a, ∫⁻ z', ∫⁻ s', PhiGG σ w W W' γ a (s'⁻¹ * z') ∂μS' ∂ν' = ∫⁻ y, PhiGG σ w W W' γ a y ∂μ := by
    intro a
    exact weil_inv hWe' hinv' (fun y => PhiGG σ w W W' γ a y) (hΦ.comp (measurable_const.prodMk measurable_id))
  simp only [hy]

  have hmy : Measurable (fun a => ∫⁻ y, PhiGG σ w W W' γ a y ∂μ) := hΦ.lintegral_prod_right'
  exact weil_inv hWe hinv (fun a => ∫⁻ y, PhiGG σ w W W' γ a y ∂μ) hmy

theorem triple_lintegral_eq {μ μS ν : Measure G} [SFinite μS] [SFinite ν] {S : Set G} {σ : G → (HH →L[ℂ] HH)}
    (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (h0 : μS Sᶜ = 0) (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν =
      ∫⁻ z, ‖W z‖ₑ * ∫⁻ y, ‖⟪σ z w, σ y w⟫_ℂ‖ₑ * ‖W y‖ₑ ∂μ ∂ν := by
  refine lintegral_congr fun z => ?_
  set H : G → ℝ≥0∞ := fun y => ‖⟪σ z w, σ y w⟫_ℂ‖ₑ * ‖W y‖ₑ with hHdef
  have hHm : Measurable H := by
    have h1 : Continuous (fun y => ⟪σ z w, σ y w⟫_ℂ) := Continuous.inner (𝕜 := ℂ) continuous_const (hσ.2.2.2 w)
    exact (h1.enorm.measurable).mul hWc.enorm.measurable
  have hae : ∀ᵐ s ∂μS, s ∈ S := by rw [ae_iff]; exact h0
  have hin : ∀ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS =
      ‖W z‖ₑ * ∫⁻ s, H (s * z') ∂μS := by
    intro z'
    rw [← lintegral_const_mul (‖W z‖ₑ) (f := fun s => H (s * z')) (hHm.comp (measurable_mul_const z'))]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    simp only [hHdef]
    have e1 : σ s (σ z' w) = σ (s * z') w := (rep_mul_apply hσ s z' w)
    have e2 : ‖W z'‖ₑ = ‖W (s * z')‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS s hs z']
    rw [e1, e2]
    ring
  simp only [hin]
  have hmeas : Measurable (fun z' : G => ∫⁻ s, H (s * z') ∂μS) := by
    have h2 : Measurable (fun p : G × G => H (p.2 * p.1)) := hHm.comp (measurable_snd.mul measurable_fst)
    exact h2.lintegral_prod_right'
  rw [lintegral_const_mul (‖W z‖ₑ) (f := fun z' => ∫⁻ s, H (s * z') ∂μS) hmeas]
  congr 1
  exact (hWe H hHm).symm

end Formalism.L2.S.Pv.ConvG
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolner
section
noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section Folner

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem ratio_le_one {μS : Measure G} {Ω A : Set G} (hA : A ⊆ Ω) (hfin : μS Ω < ⊤) :
    (μS A).toReal / (μS Ω).toReal ≤ 1 := by
  apply div_le_one_of_le₀ _ ENNReal.toReal_nonneg
  exact ENNReal.toReal_mono hfin.ne (measure_mono hA)

theorem ratio_nonneg {μS : Measure G} {Ω A : Set G} : 0 ≤ (μS A).toReal / (μS Ω).toReal := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem folner_seq [LocallyCompactSpace G] [SecondCountableTopology G] {S : Set G} {μS : Measure G}
    (hS : IsHaarSub S μS) (hF : IsFolner S μS) :
    ∃ Ω : ℕ → Set G, (∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤) ∧
      ∀ K : Set G, IsCompact K → K ⊆ S →
        Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1) := by
  let Kx := CompactExhaustion.choice G
  have hε : ∀ n : ℕ, (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    ENNReal.ofReal_pos.mpr (by positivity)
  choose Ω hΩm hΩS hpos hfin hle using fun n : ℕ =>
    hF (Kx n ∩ S) ((Kx.isCompact n).inter_right hS.1) Set.inter_subset_right _ (hε n)
  refine ⟨Ω, fun n => ⟨hΩm n, hΩS n, hpos n, hfin n⟩, ?_⟩
  intro K hK hKS
  obtain ⟨N, hN⟩ := Kx.exists_superset_of_isCompact hK
  have hlow : Tendsto (fun n : ℕ => 1 / (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 (1 / (1 + 0))) :=
      tendsto_const_nhds.div h1 (by norm_num)
    rwa [add_zero, div_one] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hsub : {t | t ∈ Ω n ∧ ∀ k ∈ Kx n ∩ S, k * t ∈ Ω n} ⊆ {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n} :=
      fun t ht => ⟨ht.1, fun k hk => ht.2 k ⟨Kx.subset hn (hN hk), hKS hk⟩⟩
    have hAB := measure_mono (μ := μS) hsub
    have hBΩ : μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n} ≤ μS (Ω n) := measure_mono (fun t ht => ht.1)
    have hBfin := (hBΩ.trans_lt (hfin n)).ne
    have hAfin := ((hAB.trans hBΩ).trans_lt (hfin n)).ne
    have hΩpos : 0 < (μS (Ω n)).toReal := ENNReal.toReal_pos (hpos n).ne' (hfin n).ne
    have hkey := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hAfin) (hle n)
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_one] at hkey
    have hAB' := ENNReal.toReal_mono hBfin hAB
    have hc : 0 < 1 + 1 / ((n : ℝ) + 1) := by positivity
    rw [div_le_div_iff₀ hc hΩpos]
    nlinarith [mul_le_mul_of_nonneg_left hAB' hc.le]
  · exact Filter.Eventually.of_forall fun n => ratio_le_one (fun t ht => ht.1) (hfin n)

end Folner

section Limit

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def rat (μS : Measure G) (Ω : Set G) (q : G) : ℝ := (cnt μS Ω q).toReal / (μS Ω).toReal

theorem sumsq_div_eq {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {μS ν : Measure G} (hS : IsHaarSub S μS) [SFinite ν] {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W) (hW1 : ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S)
    (hfin : μS Ω < ⊤)
    (hint : Integrable (fun x : G × G × G => rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    (((∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS Ω).toReal : ℝ) : ℂ) =
      ∫ x, rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) := by
  have : SigmaFinite μS := hS.2.2.2.2.1
  by_cases hm : (μS Ω).toReal = 0
  · simp [rat, hm]
  · have hI := ‹Integrable (fun x : G × G × G => rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2)
      (ν.prod (ν.prod μS))›
    have hfI : Integrable (fun x : G × G × G => (cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2)
        (ν.prod (ν.prod μS)) := by
      refine (hI.smul (μS Ω).toReal).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.smul_apply, rat, smul_smul]
      congr 1
      first
        | rw [mul_div_assoc', mul_div_cancel_left₀ _ hm]
        | field_simp
    have hprod : ∫ x, (cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) =
        ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
      rw [integral_prod _ hfI]
      refine integral_congr_ae ?_
      filter_upwards [hfI.prod_right_ae] with z hz
      exact integral_prod _ hz
    have hrhs : ∫ x, rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) =
        ∫ x, ((μS Ω).toReal⁻¹ : ℝ) • ((cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2)
          ∂(ν.prod (ν.prod μS)) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [rat, smul_smul, div_eq_inv_mul]
    rw [hrhs, integral_smul, hprod, ← sumsq_eq hσ hw hS hWeq hτu hWc hW1 hΩm hΩS hfin,
      Complex.real_smul]
    push_cast
    ring

theorem folner_limit {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH}
    {S : Set G} {μS ν : Measure G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hσ : IsUnitRep σ) (hSch : IsSchur μ σ d) (hw : ‖w‖ = 1) (hS : IsHaarSub S μS) (hν : SFinite ν)
    (hq : IsQuot μ μS ν) (hW : IsWAbs μ σ d w S τ ν W)
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤)
    (Ω : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S →
      Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => (∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS (Ω n)).toReal)
      atTop (𝓝 (1 / d)) := by
  have : SFinite ν := hν
  have : SigmaFinite μS := hS.2.2.2.2.1
  have hd : 0 < d := hSch.1
  have hWeq := hW.2.2.2.1
  have hτu := hW.2.2.1
  have hWc := hW.2.2.2.2.1
  have hW1 := hW.2.2.2.2.2.2.1
  have hS0 : μS Sᶜ = 0 := hS.2.2.2.2.2.2.1
  have hΦ := Fk_integrable hσ w hS0 hWeq hτu hWc hconv
  have hmeas : ∀ n, Measurable (fun x : G × G × G => rat μS (Ω n) x.2.2) := fun n =>
    (((cnt_measurable (μS := μS) (hΩ n).1).ennreal_toReal).div_const _).comp measurable_snd.snd
  have hr : ∀ n q, 0 ≤ rat μS (Ω n) q ∧ rat μS (Ω n) q ≤ 1 := by
    intro n q
    unfold rat cnt
    exact ⟨ratio_nonneg, ratio_le_one (fun t ht => ht.1) (hΩ n).2.2.2⟩
  have hbound : ∀ n (x : G × G × G), ‖rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2‖ ≤
      ‖Fk σ w W x.1 x.2.1 x.2.2‖ := by
    intro n x
    rw [norm_smul, Real.norm_of_nonneg (hr n x.2.2).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hr n x.2.2).2
  have hint_r : ∀ n, Integrable (fun x : G × G × G => rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2)
      (ν.prod (ν.prod μS)) := fun n =>
    hΦ.mono ((hmeas n).aestronglyMeasurable.smul hΦ.aestronglyMeasurable) (ae_of_all _ (hbound n))
  have hS_ae : ∀ᵐ x ∂(ν.prod (ν.prod μS)), x.2.2 ∈ S := by
    rw [ae_iff]
    have hset : {x : G × G × G | ¬ x.2.2 ∈ S} = Set.univ ×ˢ (Set.univ ×ˢ Sᶜ) := by
      ext x; simp
    rw [hset, Measure.prod_prod, Measure.prod_prod, hS0, mul_zero, mul_zero]
  have hlim : Tendsto (fun n => ∫ x, rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2
      ∂(ν.prod (ν.prod μS))) atTop (𝓝 (∫ x, Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖Fk σ w W x.1 x.2.1 x.2.2‖)
      (fun n => (hint_r n).aestronglyMeasurable) hΦ.norm (fun n => ae_of_all _ (hbound n)) ?_
    filter_upwards [hS_ae] with x hx
    have h1 : Tendsto (fun n => rat μS (Ω n) x.2.2) atTop (𝓝 1) := by
      have h0 := hF {x.2.2} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
      simpa [rat, cnt] using h0
    have h2 := h1.smul_const (Fk σ w W x.1 x.2.1 x.2.2)
    rwa [one_smul] at h2
  rw [Fk_value hσ hd hq hW hΦ] at hlim
  have hlim' : Tendsto (fun n => (((∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) /
      (μS (Ω n)).toReal : ℝ) : ℂ)) atTop (𝓝 ((1 / d : ℝ) : ℂ)) :=
    hlim.congr fun n => (sumsq_div_eq hσ hw hS hWeq hτu hWc hW1 (hΩ n).1 (hΩ n).2.1
      (hΩ n).2.2.2 (hint_r n)).symm
  have h3 := (Complex.continuous_re.tendsto _).comp hlim'
  simpa only [Function.comp_def, Complex.ofReal_re] using h3

end Limit

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsTrunc
section
noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def fY (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (e : V) (p : G × G) : HH :=
  ⟪W (p.2⁻¹ * p.1), e⟫_ℂ • σ (p.2⁻¹ * p.1) w

theorem continuous_fY {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hW : Continuous W)
    (e : V) : Continuous (fY σ w W e) := by
  have hc : Continuous (fun p : G × G => p.2⁻¹ * p.1) := continuous_snd.inv.mul continuous_fst
  have h1 : Continuous (fun p : G × G => W (p.2⁻¹ * p.1)) := hW.comp hc
  have h2 : Continuous (fun p : G × G => σ (p.2⁻¹ * p.1) w) := (hσ.2.2.2 w).comp hc
  exact (h1.inner continuous_const).smul h2

private theorem norm_rep_apply_of_isUnitRep {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) (x : G) (a : HH) :
    ‖σ x a‖ = ‖a‖ := by
  have h := hσ.2.2.1 x a a
  have h2 : ‖σ x a‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, h]
  rw [← Real.sqrt_sq (norm_nonneg (σ x a)), h2, Real.sqrt_sq (norm_nonneg a)]

theorem norm_fY_le {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) (W : G → V) (e : V) (p : G × G) :
    ‖fY σ w W e p‖ ≤ ‖W (p.2⁻¹ * p.1)‖ * ‖e‖ * ‖w‖ := by
  unfold fY
  rw [norm_smul, norm_rep_apply_of_isUnitRep hσ]
  exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)

private theorem ae_prod_restrict_snd_mem {ν μS : Measure G} [SFinite ν] [SFinite μS] {A : Set G} (hA : MeasurableSet A) :
    ∀ᵐ p ∂(ν.prod (μS.restrict A)), p.2 ∈ A := by
  rw [ae_iff]
  have hs : {p : G × G | ¬ p.2 ∈ A} = (Set.univ : Set G) ×ˢ Aᶜ := by
    ext p
    simp
  rw [hs, Measure.prod_prod, Measure.restrict_apply hA.compl, Set.compl_inter_self, measure_empty,
    mul_zero]

theorem integrable_fY {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) : Integrable (fY σ w W e) (ν.prod (μS.restrict A)) := by
  have : IsFiniteMeasure (μS.restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hWc : Continuous W := hW.2.2.2.2.1
  have hWi : Integrable (fun z => ‖W z‖) ν := by
    refine ⟨hWc.norm.aestronglyMeasurable, ?_⟩
    simpa [HasFiniteIntegral, enorm_norm] using hW.2.2.2.2.2.2.1
  have hg : Integrable (fun p : G × G => ‖W p.1‖ * (‖e‖ * ‖w‖)) (ν.prod (μS.restrict A)) :=
    hWi.mul_prod (integrable_const (‖e‖ * ‖w‖))
  refine hg.mono' (continuous_fY hσ w hWc e).aestronglyMeasurable ?_
  filter_upwards [ae_prod_restrict_snd_mem (ν := ν) (μS := μS) hA] with p hp
  have h1 := norm_fY_le hσ w W e p
  rw [(norm_W_shift hW) hinv (hAS hp)] at h1
  exact h1.trans_eq (by ring)

theorem yv_eq_integral {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) : yv μS ν σ w W A e = ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A)) := by
  rw [integral_prod _ (integrable_fY hσ hW hinv hA hAS hAf e)]
  rfl

theorem inner_integral_left {α : Type*} [MeasurableSpace α] {m : Measure α} {f : α → HH} (hf : Integrable f m)
    (v : HH) : ⟪∫ x, f x ∂m, v⟫_ℂ = ∫ x, ⟪f x, v⟫_ℂ ∂m := by
  have h : ∫ x, ⟪v, f x⟫_ℂ ∂m = ⟪v, ∫ x, f x ∂m⟫_ℂ := integral_inner hf v
  calc ⟪∫ x, f x ∂m, v⟫_ℂ = conj ⟪v, ∫ x, f x ∂m⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (∫ x, ⟪v, f x⟫_ℂ ∂m) := by rw [h]
    _ = ∫ x, conj ⟪v, f x⟫_ℂ ∂m := integral_conj.symm
    _ = ∫ x, ⟪f x, v⟫_ℂ ∂m := by simp_rw [inner_conj_symm]

def Xop (μS ν μS' ν' : Measure G) (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V')
    (A A' : Set G) (γ : G) : V' →L[ℂ] V :=
  (d : ℂ) • sand σ (Yop μS ν σ w W A) (Yop μS' ν' σ w W' A') γ

theorem op_ext_basis (X Z : V' →L[ℂ] V)
    (h : ∀ i j, ⟪stdOrthonormalBasis ℂ V i, X (stdOrthonormalBasis ℂ V' j)⟫_ℂ =
      ⟪stdOrthonormalBasis ℂ V i, Z (stdOrthonormalBasis ℂ V' j)⟫_ℂ) : X = Z := by
  have hcol : ∀ j, X (stdOrthonormalBasis ℂ V' j) = Z (stdOrthonormalBasis ℂ V' j) := by
    intro j
    first
    | exact ext_inner_left_basis (stdOrthonormalBasis ℂ V).toBasis (fun i => by simpa using h i j)
    | (apply (stdOrthonormalBasis ℂ V).repr.injective
       ext i
       simpa [OrthonormalBasis.repr_apply_apply] using h i j)
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ V').toBasis.ext (fun j => by simpa using hcol j)

private theorem rk1A_apply (u : V) (v : V') (x : V') : Formalism.L2.SG.Pf.EnergyAbs.rk1A u v x = ⟪v, x⟫_ℂ • u := by
  rfl

private theorem inner_kG_apply_eq (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V')
    (γ : G) (a : V) (b : V') (p p' : G × G) :
    ⟪a, kG σ d w W W' γ (φinv p, φinv p') b⟫_ℂ =
      (d : ℂ) * ⟪fY σ w W a p, σ γ (fY σ w W' b p')⟫_ℂ := by
  unfold kG fY φinv
  simp only [ContinuousLinearMap.smul_apply, rk1A_apply, inner_smul_right, inner_smul_left,
    map_smul, inner_conj_symm]
  ring

private theorem integrable_apply_of_integrable_clm {α : Type*} [MeasurableSpace α] {m : Measure α} {F : α → (V' →L[ℂ] V)}
    (hF : Integrable F m) (b : V') : Integrable (fun x => F x b) m := by
  exact hF.apply_continuousLinearMap b

private theorem integrable_inner_apply_of_integrable_clm {α : Type*} [MeasurableSpace α] {m : Measure α} {F : α → (V' →L[ℂ] V)}
    (hF : Integrable F m) (a : V) (b : V') : Integrable (fun x => ⟪a, F x b⟫_ℂ) m := by
  exact (integrable_apply_of_integrable_clm hF b).const_inner a

private theorem inner_integral_clm_apply_eq_integral {α : Type*} [MeasurableSpace α] {m : Measure α} {F : α → (V' →L[ℂ] V)}
    (hF : Integrable F m) (a : V) (b : V') : ⟪a, (∫ x, F x ∂m) b⟫_ℂ = ∫ x, ⟪a, F x b⟫_ℂ ∂m := by
  have happ : (∫ x, F x ∂m) b = ∫ x, F x b ∂m := by
    exact ContinuousLinearMap.integral_apply hF b
  rw [happ]
  exact (integral_inner (integrable_apply_of_integrable_clm hF b) a).symm

theorem Xop_eq_integral {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν μS' ν' : Measure G} [SFinite ν]
    [SFinite μS] [SFinite ν'] [SFinite μS'] {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
    {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') {A A' : Set G} (hA : MeasurableSet A)
    (hAS : A ⊆ S) (hAf : μS A < ⊤) (hA' : MeasurableSet A') (hAS' : A' ⊆ S') (hAf' : μS' A' < ⊤) (γ : G)
    (hK : Integrable (fun q : (G × G) × (G × G) => kG σ d w W W' γ (φinv q.1, φinv q.2))
      ((ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A')))) :
    Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q, kG σ d w W W' γ (φinv q.1, φinv q.2) ∂((ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A'))) := by
  refine op_ext_basis _ _ (fun i j => ?_)
  have hf := integrable_fY hσ hW hinv hA hAS hAf (stdOrthonormalBasis ℂ V i)
  have hf' := integrable_fY hσ hW' hinv' hA' hAS' hAf' (stdOrthonormalBasis ℂ V' j)
  have hL : ⟪stdOrthonormalBasis ℂ V i,
      Xop μS ν μS' ν' σ d w W W' A A' γ (stdOrthonormalBasis ℂ V' j)⟫_ℂ =
      ∫ p, ∫ p', (d : ℂ) * ⟪fY σ w W (stdOrthonormalBasis ℂ V i) p,
        σ γ (fY σ w W' (stdOrthonormalBasis ℂ V' j) p')⟫_ℂ
          ∂(ν'.prod (μS'.restrict A')) ∂(ν.prod (μS.restrict A)) := by
    rw [Xop, ContinuousLinearMap.smul_apply, inner_smul_right, inner_sand,
      Yop_apply_basis, Yop_apply_basis,
      yv_eq_integral hσ hW hinv hA hAS hAf,
      yv_eq_integral hσ hW' hinv' hA' hAS' hAf',
      ← (σ γ).integral_comp_comm hf', inner_integral_left hf, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    try dsimp only
    rw [integral_const_mul, integral_inner ((σ γ).integrable_comp hf')]
  rw [hL, inner_integral_clm_apply_eq_integral hK (stdOrthonormalBasis ℂ V i) (stdOrthonormalBasis ℂ V' j),
    integral_prod _ (integrable_inner_apply_of_integrable_clm hK (stdOrthonormalBasis ℂ V i) (stdOrthonormalBasis ℂ V' j))]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  try dsimp only
  refine integral_congr_ae (ae_of_all _ fun p' => ?_)
  try dsimp only
  exact (inner_kG_apply_eq σ d w W W' γ _ _ p p').symm

end Formalism.L2.S.Pv.EnergyAbs
end
end

