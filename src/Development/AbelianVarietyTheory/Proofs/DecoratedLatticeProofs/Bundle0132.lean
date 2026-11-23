module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsDenseContinuousThetaLaw
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisSmoothing

open GlobalTheory.FockCompare

theorem norm_integral_sub_le {X : Type} [MeasurableSpace X] (μ : Measure X) (φ : X → ℝ) (F : X → ℂ) (c : ℂ) (δ : ℝ)
    (h0 : ∀ x, 0 ≤ φ x) (h1 : ∫ x, φ x ∂μ = 1) (hφ : Integrable φ μ) (hF : Integrable (fun x => (φ x : ℂ) * F x) μ)
    (hb : ∀ x, φ x ≠ 0 → ‖F x - c‖ ≤ δ) : ‖∫ x, (φ x : ℂ) * F x ∂μ - c‖ ≤ δ := by
  have hc : Integrable (fun x => (φ x : ℂ) * c) μ := hφ.ofReal.mul_const c
  have e : ∫ x, (φ x : ℂ) * c ∂μ = c := by
    rw [integral_mul_const, integral_complex_ofReal, h1]
    simp
  have e2 : ∫ x, φ x * δ ∂μ = δ := by rw [integral_mul_const, h1, one_mul]
  rw [← e2]
  conv_lhs => rw [← e, ← integral_sub hF hc]
  refine norm_integral_le_of_norm_le (hφ.mul_const δ) (Filter.Eventually.of_forall fun x => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 x)]
  by_cases hx : φ x = 0
  · rw [hx, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hb x hx) (h0 x)

theorem isAddHaarMeasure_volume (ι m n : Type) [Fintype ι] [Fintype m] [Fintype n] :
    (volume : Measure (ι → m → n → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (m → n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem exists_theta_of_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (f : WO A T → ℂ), Continuous f → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), f (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * f u) → (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ A T u f = f) → ∀ N ∈ 𝓝 (0 : WO A T), ∀ δ : ℝ, (∀ a ∈ N, ∀ w, ‖heisO ψ A T a f w - f w‖ ≤ δ) → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ w, ‖g w - f w‖ ≤ δ := by
  intro D ψ hψ A T f hf hlaw hlev N hN δ hδ
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨i1, -⟩ := lattice_Mx D T.rank A.rank
  haveI : (volume : Measure (RW T A)).IsAddHaarMeasure := isAddHaarMeasure_volume _ _ _
  have hι : Continuous (iotaW σ T A) := h.continuous_iota T A
  have hN' : iotaW σ T A ⁻¹' N ∈ 𝓝 (0 : RW T A) :=
    hι.continuousAt.preimage_mem_nhds (by rw [AddMonoidHom.map_zero]; exact hN)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN'
  let b : ContDiffBump (0 : RW T A) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let φ : RW T A → ℝ := b.normed volume
  have hφs : ContDiff ℝ ∞ φ := b.contDiff_normed
  have hφc : HasCompactSupport φ := b.hasCompactSupport_normed
  let g : WO A T → ℂ := fun w => ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
  have hsm : Sm (iotaW σ T A) g := _root_.GlobalTheory.HeisAverage.sm_heisO_average D θ σ h ψ hψ A T φ hφs hφc f hf
  have hl : ∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ A T u g = g := by
    obtain ⟨U, hU, hUf⟩ := hlev
    refine ⟨U, hU, fun u hu h0 => funext fun w => ?_⟩
    show ψ (symplOH A T w u) * ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (w + u) = _
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e := congrFun (GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (h.real_iota T A x) (hUf u hu h0)) w
    show _ = (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
    rw [← e]
    exact mul_left_comm _ _ _
  refine ⟨g, ⟨fun γ w => ?_, hl, GlobalTheory.OrientedHeis.continuous_of_level h hψ.1.1 g hl hsm,
    ((smooth_iff_sm_and_real_lines D θ σ h T A).1 g).2 hsm⟩, fun w => ?_⟩
  · show ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (ratW T A γ + w) =
      _ * ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (ratW T A γ + w) = _
    rw [GlobalTheory.OrientedHeis.heisO_quasi _ f hlaw]
    exact mul_left_comm _ _ _
  · have hc : Continuous fun x : RW T A => heisO ψ A T (iotaW σ T A x) f w :=
      (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_const hι)).mul
        (hf.comp (continuous_const.add hι))
    have hφℂ : HasCompactSupport fun x => (φ x : ℂ) := hφc.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
    refine norm_integral_sub_le volume φ _ (f w) δ b.nonneg_normed b.integral_normed b.integrable_normed
      (((Complex.continuous_ofReal.comp hφs.continuous).mul hc).integrable_of_hasCompactSupport hφℂ.mul_right)
      fun x hx => hδ _ (hrN ?_) w
    have : x ∈ Function.support φ := hx
    rwa [b.support_normed_eq] at this

theorem exists_theta_near : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ u, ‖q u - g u‖ ≤ ε := by
  have h1 := _root_.GlobalTheory.HeisNearZero.heisO_near_zero_unif
  have h2a := _root_.GlobalTheory.SmallLevel.exists_small_level
  have h2b := _root_.GlobalTheory.HeisAvgCompact.exists_average
  have h4 := exists_theta_of_level
  intro D ψ hψ A T q hq hlaw ε hε
  obtain ⟨N, hN, hNq⟩ := h1 D ψ hψ A T q hq hlaw (ε / 2) (half_pos hε)
  obtain ⟨K, hKc, hKN, -, ⟨U, hU, hUK⟩, hKψ⟩ := h2a D ψ hψ A T N hN
  obtain ⟨g1, hg1c, hg1law, hg1K, hg1near⟩ := h2b D ψ hψ A T K hKc hKψ q hq hlaw
  have hg1q : ∀ w, ‖g1 w - q w‖ ≤ ε / 2 := hg1near (ε / 2) (fun a ha w => hNq a (hKN ha) w)
  obtain ⟨N2, hN2, hN2g⟩ := h1 D ψ hψ A T g1 hg1c hg1law (ε / 2) (half_pos hε)
  obtain ⟨g, hg, hgg1⟩ := h4 D ψ hψ A T g1 hg1c hg1law ⟨U, hU, fun u hu h0 => hg1K u (hUK u hu h0)⟩ N2 hN2 (ε / 2) hN2g
  refine ⟨g, hg, fun w => ?_⟩
  have e : q w - g w = (g1 w - g w) - (g1 w - q w) := by ring
  rw [e]
  calc ‖(g1 w - g w) - (g1 w - q w)‖ ≤ ‖g1 w - g w‖ + ‖g1 w - q w‖ := norm_sub_le _ _
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · rw [norm_sub_rev]; exact hgg1 w
        · exact hg1q w
    _ = ε := add_halves ε

end GlobalTheory.HeisSmoothing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Pointwise

noncomputable section

namespace GlobalTheory.MajSum

variable {D : D7}

theorem realSize_add_le (θ : InfFam D) {m n : ℕ} (x y : Mx D m n) :
    realSize θ (x + y) ≤ realSize θ x + realSize θ y := by
  unfold realSize
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have : Formalism.IndefR.Datum.compAt θ τ (x + y) i j =
      Formalism.IndefR.Datum.compAt θ τ x i j + Formalism.IndefR.Datum.compAt θ τ y i j := by
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add (infPart D), RingHom.map_add (θ τ)]
  rw [this]
  exact norm_add_le _ _

theorem maj_le_shift (θ : InfFam D) {m n : ℕ} (K C : Set (Mx D m n)) (N : ℕ) (γ w : Mx D m n)
    (hwC : w ∈ C) (hw : realSize θ w ≤ 1) :
    maj θ K N γ ≤ 2 ^ N * maj θ (K + C) N (γ + w) := by
  unfold maj
  by_cases hγ : InBox K γ
  · have hbox : InBox (K + C) (γ + w) := by
      obtain ⟨k, hk, hk0⟩ := hγ
      refine ⟨k + w, Set.add_mem_add hk hwC, ?_⟩
      have : γ + w - (k + w) = γ - k := by abel
      rw [this]; exact hk0
    rw [if_pos hγ, if_pos hbox]
    have h0 := realSize_nonneg θ γ
    have h1 := realSize_nonneg θ (γ + w)
    have h2 : 1 + realSize θ (γ + w) ≤ 2 * (1 + realSize θ γ) := by
      have := realSize_add_le θ γ w; linarith
    have hp : (0:ℝ) < (1 + realSize θ (γ + w)) ^ N := by positivity
    have hq : (0:ℝ) < (1 + realSize θ γ) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + realSize θ (γ + w)) ^ N ≤ (2 * (1 + realSize θ γ)) ^ N := by gcongr
      _ = 2 ^ N * (1 + realSize θ γ) ^ N := by rw [mul_pow]
  · rw [if_neg hγ]
    have := maj_nonneg θ (K + C) N (γ + w)
    unfold maj at this
    positivity

end GlobalTheory.MajSum

namespace GlobalTheory.MajSum

theorem realSize_zero {D : D7} (θ : InfFam D) {m n : ℕ} : realSize θ (0 : Mx D m n) = 0 := by
  have h : ∀ τ (i : Fin m) (j : Fin n), Formalism.IndefR.Datum.compAt θ τ (0 : Mx D m n) i j = 0 := by
    intro τ i j
    show θ τ (infPart D 0) = 0
    rw [RingHom.map_zero (infPart D), RingHom.map_zero (θ τ)]
  unfold realSize
  simp only [h, norm_zero, Finset.sum_const_zero]


set_option synthInstance.maxHeartbeats 400000 in
theorem tsum_maj_ne_top : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K →
    (∑' y : ratMx D m n, ENNReal.ofReal (maj θ K N y)) ≠ ⊤ := by
  intro D θ hθ m n
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let μ : Measure (Mx D m n) := Measure.addHaar
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) :=
    ((_root_.GlobalTheory.Unf.maj_measurable_rat D θ hθ).1 m n ∅ isCompact_empty).2.1
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Unf.MajInt.maj_integrable D θ hθ m n (fun _ _ => True) 0 μ inferInstance
    (Filter.Eventually.of_forall fun x i j h => (h trivial).elim)
    (fun t _ => by
      have e : (fun x : Mx D m n => x + t) = fun x => t + x := funext fun x => add_comm x t
      rw [e]; exact map_add_left_eq_self μ t)
  refine ⟨N, fun K hK => ?_⟩

  obtain ⟨U, hUo, hU⟩ : ∃ U : Set (Mx D m n), IsOpen U ∧ ∀ γ ∈ ratMx D m n, γ ∈ U ↔ γ = 0 := by
    have h0 : IsOpen ({0} : Set (ratMx D m n)) := @isOpen_discrete (ratMx D m n) _ i5 _
    obtain ⟨U, hUo, hUe⟩ := isOpen_induced_iff.mp h0
    refine ⟨U, hUo, fun γ hγ => ?_⟩
    have := Set.ext_iff.mp hUe ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    rw [this]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h0U : (0 : Mx D m n) ∈ U := (hU 0 (zero_mem _)).2 rfl
  have hsub : {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} ∈ nhds ((0 : Mx D m n), (0 : Mx D m n)) := by
    have hc : Continuous fun p : Mx D m n × Mx D m n => p.1 - p.2 := continuous_fst.sub continuous_snd
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hUo.mem_nhds h0U
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hsub
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (0 : Mx D m n)
  have hR : {w : Mx D m n | realSize θ w < 1} ∈ nhds (0 : Mx D m n) := by
    refine (isOpen_lt hcont continuous_const).mem_nhds ?_
    show realSize θ (0 : Mx D m n) < 1
    rw [realSize_zero]; exact one_pos
  set W := interior (A ∩ B ∩ C ∩ {w : Mx D m n | realSize θ w < 1}) with hWdef
  have hW0 : (0 : Mx D m n) ∈ W :=
    mem_interior_iff_mem_nhds.2 (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA hB) hC) hR)
  have hμW : μ W ≠ 0 := (isOpen_interior.measure_pos μ ⟨0, hW0⟩).ne'

  let s : ratMx D m n → Set (Mx D m n) := fun γ => (fun x => -(γ : Mx D m n) + x) ⁻¹' W
  have hs : ∀ γ, MeasurableSet (s γ) := fun γ =>
    (isOpen_interior.preimage (continuous_const.add continuous_id)).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro γ γ' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    have hxA : -(γ : Mx D m n) + x ∈ A := (interior_subset hx).1.1.1
    have hxB : -(γ' : Mx D m n) + x ∈ B := (interior_subset hx').1.1.2
    have hmem : (-(γ : Mx D m n) + x, -(γ' : Mx D m n) + x) ∈ {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} :=
      hAB ⟨hxA, hxB⟩
    simp only [Set.mem_setOf_eq] at hmem
    have e : -(γ : Mx D m n) + x - (-(γ' : Mx D m n) + x) = (γ' : Mx D m n) - γ := by abel
    rw [e] at hmem
    have := (hU _ (sub_mem γ'.2 γ.2)).1 hmem
    exact Subtype.ext (sub_eq_zero.1 this).symm
  set K' := K + C
  have hK' : IsCompact K' := hK.add hCc
  have hfin : ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ < ⊤ := (hN K' hK').lintegral_lt_top
  have key : ∀ γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ) * μ W ≤
      2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    intro γ
    calc ENNReal.ofReal (maj θ K N γ) * μ W = ∫⁻ _x in s γ, ENNReal.ofReal (maj θ K N γ) ∂μ := by
          rw [setLIntegral_const]
          congr 1
          exact (measure_preimage_add μ (-(γ : Mx D m n)) W).symm
      _ ≤ ∫⁻ x in s γ, 2 ^ N * ENNReal.ofReal (maj θ K' N x) ∂μ := by
          refine setLIntegral_mono' (hs γ) fun x hx => ?_
          have hw := interior_subset hx
          have h1 := maj_le_shift θ K C N (γ : Mx D m n) (-(γ : Mx D m n) + x) hw.1.2 (le_of_lt hw.2)
          rw [add_neg_cancel_left] at h1
          calc ENNReal.ofReal (maj θ K N γ) ≤ ENNReal.ofReal (2 ^ N * maj θ K' N x) :=
                ENNReal.ofReal_le_ofReal h1
            _ = 2 ^ N * ENNReal.ofReal (maj θ K' N x) := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      _ = 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hsum : (∑' γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ)) * μ W ≤
      2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    rw [← ENNReal.tsum_mul_right]
    calc _ ≤ ∑' γ : ratMx D m n, 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          ENNReal.tsum_le_tsum key
      _ = 2 ^ N * ∑' γ : ratMx D m n, ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := ENNReal.tsum_mul_left
      _ = 2 ^ N * ∫⁻ x in ⋃ γ, s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by rw [lintegral_iUnion hs hdisj]
      _ ≤ 2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
          gcongr; exact Measure.restrict_le_self
  intro htop
  rw [htop, ENNReal.top_mul hμW] at hsum
  exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hfin).ne (top_le_iff.1 hsum)

end GlobalTheory.MajSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicRankZeroProjMulEmb
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TargetIsom

open GlobalTheory.Mem.Isom

variable {D : D7}

theorem entries_fix {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) : c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix' {A : Type} [CommRing A] {m n k : ℕ} (c : A) {M : Matrix (Fin n) (Fin k) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (i : Fin m) (j : Fin k) : c * (P * M) i j = (P * M) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l j]
  ring

theorem sub_one_conj {A : Type} [CommRing A] {m n : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (PQ : P * Q = 1)
    (M : Matrix (Fin n) (Fin n) A) : P * M * Q - 1 = P * (M - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, PQ]

theorem det_conj_rect {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A}
    (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP, Matrix.det_one, mul_one]

theorem isThetaFunO_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {f : WO S V → ℂ}
    (hf : IsThetaFunO ψ S V f) : IsThetaFunO ψ S V' (I.trW S f) := by
  have hinf : ∀ w : WO S V', w.map (infPart D) = 0 → ((I.phi S).symm w).map (infPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (infPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  have hfin : ∀ w : WO S V', w.map (finPart D) = 0 → ((I.phi S).symm w).map (finPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (finPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (I.continuous_phi_symm S), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (I.phi S).surjective w
    have e : ratW V' S γ = I.phi S (ratW V S (I.Q * γ)) := by
      rw [IsoMat.phi_ratW, ← Matrix.mul_assoc, I.PQ, Matrix.one_mul]
    rw [e, ← map_add (f := _), I.symplOH_phi]
    simp only [IsoMat.trW, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.map (I.phi S).toAddMonoidHom, ?_, ?_⟩
    · have e : ((U.map (I.phi S).toAddMonoidHom : AddSubgroup (WO S V')) : Set (WO S V')) = (I.phi S).symm ⁻¹' U := by
        ext w
        simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using hu
        · intro hw
          exact ⟨_, hw, by simp⟩
      rw [e]
      exact hU.preimage (I.continuous_phi_symm S)
    · rintro _ ⟨u, hu, rfl⟩ h0
      have h1 : u.map (infPart D) = 0 := by
        have := hinf _ h0
        simpa using this
      show heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S f
      rw [I.heisO_trW, e u hu h1]
  · have := hf.smooth k ((I.phi S).symm.toAddMonoidHom.comp L) ((I.continuous_phi_symm S).comp hL) (fun t => hfin _ (h0 t))
      ((I.phi S).symm w)
    simpa [IsoMat.trW] using this

theorem isWeilDatumO_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)}
    (h : IsWeilDatumO ψ S V χ χ' om) : IsWeilDatumO ψ S V' χ χ' (I.omT S om) := by
  have hT : ∀ f, IsThetaFunO ψ S V' f → IsThetaFunO ψ S V (I.symm.trW S f) := fun f hf => isThetaFunO_tr I.symm S hf
  refine ⟨h.std, h.hecS, h.hecT, h.resS, I.rank_eq ▸ h.resT, fun p f hf => ?_, fun g k w₀ f hf => ?_, fun γ hγ γ' hγ' f hf => ?_,
    fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · exact isThetaFunO_tr I S (h.om_pres _ _ (hT f hf))
  · rw [IsoMat.omT_apply, IsoMat.omT_apply, ← I.symm.heisO_trW S ψ w₀ f, h.om_heis _ _ _ _ (hT f hf), ← I.heisO_trW, I.actO_phi]
    congr 2
    · exact I.kap.apply_symm_apply k
    · exact (I.phi S).apply_symm_apply w₀
  · rw [IsoMat.omT_apply]
    show om (γ, I.kap.symm γ') (I.symm.trW S f) ((I.phi S).symm 0) = f 0
    have := h.om_aut γ hγ (I.kap.symm γ') (I.symm.kap_mem_GQ hγ') _ (hT f hf)
    rw [map_zero, this]
    show f ((I.phi S) 0) = f 0
    rw [map_zero]
  · exact (h.om_cont _ (hT f hf) ((I.phi S).symm w)).comp
      (continuous_fst.prodMk ((I.continuous_kap_symm).comp continuous_snd))
  · obtain ⟨ν, 𝓖, hν, h𝓖, hu⟩ := GlobalTheory.Mem.Isom.haar_fd_phi D V V' I S μ 𝓕 hμ h𝓕
    have e1 := hu fun x => ‖om (p.1, I.kap.symm p.2) (I.symm.trW S f) x‖ₑ ^ 2
    have e2 := hu fun x => ‖I.symm.trW S f x‖ₑ ^ 2
    have e3 : ∀ w, I.symm.trW S f ((I.phi S).symm w) = f w := fun w => congrArg f ((I.phi S).apply_symm_apply w)
    simp only [e3] at e2
    rw [IsoMat.omT_apply]
    exact e1.trans ((h.om_unit ν 𝓖 hν h𝓖 _ _ (hT f hf)).trans e2.symm)
  · have e0 : mt V (I.kap.symm k) - 1 = _ := sub_one_conj I.aQ_aP (mt V' k)
    have hsupp : SuppAt e V (I.kap.symm k) := fun i j => by
      unfold SuppAt at hk
      rw [e0]
      exact entries_fix _ hk _ _ i j
    have e1 : (mt V (I.kap.symm k)).det = (mt V' k).det := det_conj_rect I.rank_eq.symm I.aP_aQ (mt V' k)
    have hdet : IsDetAt e V (I.kap.symm k) y := by
      unfold IsDetAt at hy ⊢
      rw [e1]
      exact hy
    obtain ⟨r, hr, H⟩ := h.om_split e he g (I.kap.symm k) hg hsupp x y hx hdet
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hinv : ∀ u : WO S V, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S V f →
        (ℓ ∘ₗ I.trL S) (heisO ψ S V u f) = (ℓ ∘ₗ I.trL S) f := by
      intro u hu f hf
      show ℓ (I.trW S (heisO ψ S V u f)) = ℓ (I.trW S f)
      rw [← I.heisO_trW]
      exact hℓ _ (fun i j => entries_fix' _ hu I.aP i j) _ (isThetaFunO_tr I S hf)
    have := H (ℓ ∘ₗ I.trL S) hinv _ (hT f hf)
    have e1 : (ℓ ∘ₗ I.trL S) (I.symm.trW S f) = ℓ f := congrArg ℓ (I.symm.trW_symm_trW S f)
    rw [e1] at this
    exact this

variable {T T₀ : HSp D} (d : HypDec T T₀ 0)

theorem mul_fin_zero {m n : ℕ} (A : Matrix (Fin m) (Fin 0) D.host.E) (B : Matrix (Fin 0) (Fin n) D.host.E) : A * B = 0 := by
  ext i j; simp [Matrix.mul_apply]

theorem mul_fin_zero' {m n : ℕ} (A : Mx D m 0) (B : Mx D 0 n) : A ⬝ B = 0 := by
  ext i j; simp [Matrix.mul_apply]

theorem wittHyperbolicRankZero_proj_mul_emb : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)

theorem wittHyperbolicRankZero_emb_mul_proj : d.i₀ * d.q0 = 1 := by
  have h := d.sum_eq_one_rat
  rwa [mul_fin_zero, mul_fin_zero, zero_add, add_zero] at h

def iso : IsoMat T₀ T where
  P := d.i₀
  Q := d.q0
  PQ := wittHyperbolicRankZero_emb_mul_proj d
  QP := wittHyperbolicRankZero_proj_mul_emb d
  gram := d.iso

theorem kap_eq (h : GA D T₀) : (iso d).kap h = d.emb0 h := by
  apply mt_injective T
  rw [IsoMat.mt_kap, IsoMat.conjM_apply, HypDec.unitaryMatrix_wittCoreEmbedding, mul_fin_zero' d.jX, mul_fin_zero' d.jY, zero_add, add_zero]
  rfl

end GlobalTheory.TargetIsom

open GlobalTheory.TargetIsom in
theorem GlobalTheory.TargetIsom.transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T T₀ : HSp D) (d : HypDec T T₀ 0), IsStdChar D ψ (-1) → Function.Bijective (d.inc0 S) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ S T₀ (fun w => f (d.inc0 S w)) ↔ IsThetaFunO ψ S T f) ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S T₀), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T₀ χS χT om₀ → ∀ g h f, IsThetaFunO ψ S T f → om₀ (g, h) (fun w => f (d.inc0 S w)) = fun w => om (g, d.emb0 h) f (d.inc0 S w) := by
  intro D ψ S T T₀ d hψ
  have hphi : (d.inc0 S : WO S T₀ → WO S T) = (iso d).phi S := funext fun w => rfl
  refine ⟨hphi ▸ ((iso d).phi S).bijective, fun f => ⟨fun hf => ?_, fun hf => ?_⟩, fun χS χT om om₀ hom hom₀ g h f hf => ?_⟩
  · have := isThetaFunO_tr (iso d) S hf
    convert this using 1
    funext w
    show f w = f ((iso d).phi S (((iso d).phi S).symm w))
    rw [AddEquiv.apply_symm_apply]
  · exact isThetaFunO_tr (iso d).symm S hf
  · have hT := isWeilDatumO_tr (iso d).symm S hom
    have hf0 : IsThetaFunO ψ S T₀ (fun w => f (d.inc0 S w)) := isThetaFunO_tr (iso d).symm S hf
    rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T₀ χS χT om₀ _ hom₀ hT (g, h) _ hf0]
    funext w
    rw [GlobalTheory.Mem.Isom.IsoMat.omT_apply]
    have e1 : ((iso d).symm.kap.symm h) = d.emb0 h := kap_eq d h
    have e2 : (iso d).symm.symm.trW S (fun w => f (d.inc0 S w)) = f := (iso d).symm.trW_symm_trW S f
    rw [e1, e2]
    rfl
end
end

