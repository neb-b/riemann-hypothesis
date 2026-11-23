module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0060
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRkNBound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix GlobalTheory.CompanionTheory.EisRk1Bound

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem summable_prod_coord {α : Type*} {g : α → ℝ} (h0 : ∀ x, 0 ≤ g x) (hg : Summable g) :
    Summable fun ξ : ι → α ↦ ∏ i, g (ξ i) :=
  _root_.UpperTheory.Reformulated.B.Qo1.summable_prod_coord h0 hg

theorem inv_mulVec_mulVec (x : ι → 𝔸[K]) (h : GL ι 𝔸[K]) :
    ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) *ᵥ ((h : Matrix ι ι 𝔸[K]) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem continuous_inv_entry (i j : ι) :
    Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j := by
  have h : Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) :=
    Units.continuous_val.comp continuous_inv
  exact h.matrix_elem i j


omit [DecidableEq ι] in
theorem finPartPi_mulVec (M : Matrix ι ι 𝔸[K]) (x : ι → 𝔸[K]) :
    finPartPi (M *ᵥ x) = M.map Adele2.finRingHom *ᵥ finPartPi x := by
  funext i
  show Adele2.finRingHom (∑ j, M i j * x j) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _


omit [DecidableEq ι] in
theorem infPartPi_mulVec (M : Matrix ι ι 𝔸[K]) (x : ι → 𝔸[K]) :
    infPartPi (M *ᵥ x) = M.map Adele2.infRingHom *ᵥ infPartPi x := by
  funext i
  show Adele2.infRingHom (∑ j, M i j * x j) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _


omit [DecidableEq ι] in
theorem norm_mulVec_le (M : Matrix ι ι (mixedSpace K)) (u : ι → mixedSpace K) :
    ‖M *ᵥ u‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
  have hc : 0 ≤ ∑ i, ∑ j, ‖M i j‖ :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).mpr fun i ↦ ?_
  calc ‖(M *ᵥ u) i‖ = ‖∑ j, M i j * u j‖ := rfl
    _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖u‖ := Finset.sum_le_sum fun j _ ↦
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖u‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i ↦ ∑ j, ‖M i j‖)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)

theorem exists_fractionalIdeal_of_isCompact (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ι → 𝔸ᶠ[K])
    {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) :
    ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ h ∈ C, ∀ ξ : ι → K,
      (∀ i, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i)) i - b i ∈
        idealFiniteAdeles I) → ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  set B : Set (ι → 𝔸ᶠ[K]) :=
    Set.pi Set.univ fun i ↦ b i +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])
  have hB : IsCompact B := isCompact_univ_pi fun i ↦ (isCompact_idealFiniteAdeles I).vadd (b i)
  let T : GL ι 𝔸[K] × (ι → 𝔸ᶠ[K]) → ι → 𝔸ᶠ[K] := fun p ↦
    (((p.1⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.finRingHom) *ᵥ p.2
  have hT : Continuous T := by
    refine continuous_pi fun i ↦ ?_
    simp only [T, Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine continuous_finsetSum _ fun j _ ↦ ?_
    exact (continuous_finRingHom.comp ((continuous_inv_entry i j).comp continuous_fst)).mul
      ((continuous_apply j).comp continuous_snd)
  set S : Set 𝔸ᶠ[K] := ⋃ i : ι, (fun x : ι → 𝔸ᶠ[K] ↦ x i) '' (T '' (C ×ˢ B))
  have hS : IsCompact S := isCompact_iUnion fun i ↦
    ((hC.prod hB).image hT).image (continuous_apply i)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)), ?_⟩
  intro h hh ξ hξ i
  set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)
  have hTX : T (h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)) =
      fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i) := by
    show _ *ᵥ finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) = _
    rw [← finPartPi_mulVec, inv_mulVec_mulVec, finPartPi_algebraMap]
  have hmem : algebraMap K 𝔸ᶠ[K] (ξ i) ∈ S := by
    have hp : finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) ∈ B := fun j _ ↦
      mem_vadd_idealFiniteAdeles.mpr (hξ j)
    have hq : (fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)) ∈ T '' (C ×ˢ B) :=
      ⟨(h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)), ⟨hh, hp⟩, hTX⟩
    exact Set.mem_iUnion.mpr ⟨i, _, hq, rfl⟩
  have h1 := hd _ hmem
  rw [← map_mul] at h1
  have h2 : dK * ξ i ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
  rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

theorem summable_latticeWeight_prod (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable fun ξ : ι → K ↦
      ∏ i, latticeWeight J (Module.finrank ℤ (idealLattice K J) + 1) (ξ i) :=
  summable_prod_coord (latticeWeight_nonneg J _)
    (summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ ((1 + ‖x‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹)
      (summable_inv_one_add_norm_pow_idealLattice J))

theorem exists_summable_bound_tensor_cosetIndicator (φ : 𝓢(ι → mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ι → 𝔸ᶠ[K]) {C : Set (GL ι 𝔸[K])}
    (hC : IsCompact C) :
    ∃ u : (ι → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → K,
      ‖schwartzBruhatTensorPi φ (finiteTensor fun i ↦ cosetIndicator I (b i))
        ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i))‖ ≤ u ξ := by
  obtain ⟨J, hJ⟩ := exists_fractionalIdeal_of_isCompact I b hC
  set k := Module.finrank ℤ (idealLattice K J) + 1
  set n := Fintype.card ι
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ (k * n)
  let c : GL ι 𝔸[K] → ℝ := fun h ↦ ∑ i, ∑ j,
    ‖(((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) i j‖
  have hc : Continuous c := continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    (continuous_infRingHom.comp (continuous_inv_entry i j)).norm
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  refine ⟨fun ξ ↦ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i),
    (summable_latticeWeight_prod J).mul_left _, ?_⟩
  intro h hh ξ
  have hu0 : 0 ≤ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i) :=
    mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ ↦ latticeWeight_nonneg J k _)
  set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)
  set Y := (h : Matrix ι ι 𝔸[K]) *ᵥ X
  simp only [schwartzBruhatTensorPi, finiteTensor]
  by_cases hm : ∀ i, finPartPi Y i - b i ∈ idealFiniteAdeles I
  · have h1 : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 1 :=
      Finset.prod_eq_one fun i _ ↦ by rw [cosetIndicator_apply, if_pos (hm i)]
    rw [h1, mul_one]
    have hξJ := hJ h hh ξ hm
    have hw : ∀ i, latticeWeight J k (ξ i) = ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ :=
      fun i ↦ if_pos (hξJ i)
    simp only [hw]
    set y := infPartPi Y
    have hy : embPi K ξ =
        (((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) *ᵥ y := by
      rw [← infPartPi_mulVec, inv_mulVec_mulVec, infPartPi_algebraMap]
    have hcB : c h ≤ B' := (le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le (hB h hh)).trans
      (le_max_left _ _))
    have he : ‖embPi K ξ‖ ≤ B' * ‖y‖ := by
      rw [hy]
      exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hcB (norm_nonneg _))
    set t := B' * (1 + ‖y‖)
    have ht : 0 < t := by positivity
    have hle : ∀ i, 1 + ‖mixedEmbedding K (ξ i)‖ ≤ t := fun i ↦ by
      have h1 : ‖mixedEmbedding K (ξ i)‖ ≤ ‖embPi K ξ‖ := norm_le_pi_norm (embPi K ξ) i
      have : t = B' + B' * ‖y‖ := by simp only [t]; ring
      linarith
    have hinv : ∀ i, (t ^ k)⁻¹ ≤ ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ := fun i ↦ by
      have h0 : 0 < 1 + ‖mixedEmbedding K (ξ i)‖ := by positivity
      gcongr
      exact hle i
    calc ‖φ y‖ ≤ A * ((1 + ‖y‖) ^ (k * n))⁻¹ := hφ y
      _ = A * B' ^ (k * n) * ∏ _i : ι, (t ^ k)⁻¹ := by
          have hB0 : B' ^ (k * n) ≠ 0 := by positivity
          have hprod : ∏ _i : ι, (t ^ k)⁻¹ = (t ^ (k * n))⁻¹ := by
            rw [Finset.prod_const, Finset.card_univ, inv_pow, ← pow_mul]
          have ht' : t ^ (k * n) = B' ^ (k * n) * (1 + ‖y‖) ^ (k * n) := mul_pow _ _ _
          rw [hprod, ht', mul_inv, ← mul_assoc, mul_assoc A, mul_inv_cancel₀ hB0, mul_one]
      _ ≤ A * B' ^ (k * n) * ∏ i, ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ hinv i
  · push_neg at hm
    obtain ⟨i, hi⟩ := hm
    have hz : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [cosetIndicator_apply, if_neg hi])
    rw [hz, mul_zero, norm_zero]
    exact hu0

theorem exists_summable_bound_mulVec {F : (ι → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := K) (ι := ι))
    {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) :
    ∃ u : (ι → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → K,
      ‖F ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i))‖ ≤ u ξ := by
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_summable_bound_tensor_cosetIndicator φ I b hC
  | zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨w, hw, hHw⟩ := hH
    exact ⟨u + w, hu.add hw,
      fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩
  | smul r G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)

theorem exists_summable_bound_thetaC {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι))
    {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) :
    ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → k,
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ PositivityTheory.RgEis.ratV ξ)‖ ≤ u ξ :=
  exists_summable_bound_mulVec hF hC

end

end GlobalTheory.CompanionTheory.EisRkNBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
section
noncomputable section

open MeasureTheory Filter Topology Metric
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
open scoped NNReal Real Pointwise

namespace GlobalTheory.CompanionTheory.RgEisHGood

theorem differentiable_of_pointwise {K : Type} [TopologicalSpace K] [CompactSpace K] (F : ℂ → C(K, ℂ))
    (hc : Continuous F) (hp : ∀ κ, Differentiable ℂ fun z => F z κ) : Differentiable ℂ F := by
  intro c
  have hint : CircleIntegrable F c ((1 : ℝ≥0) : ℝ) := hc.continuousOn.circleIntegrable'
  have hfp := hasFPowerSeriesOn_cauchy_integral hint one_pos
  simp only [NNReal.coe_one] at hfp
  have heq : ∀ w ∈ ball c (1 : ℝ), ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) = F w := by
    intro w hw
    ext κ
    have hcau := ((hp κ).diffContOnCl (s := ball c 1)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
    have hne : ∀ θ : ℝ, circleMap c 1 θ - w ≠ 0 := fun θ h => by
      have h1 : circleMap c 1 θ ∈ sphere c (1 : ℝ) := circleMap_mem_sphere c zero_le_one θ
      rw [sub_eq_zero.1 h] at h1
      exact (ne_of_lt (mem_ball.1 hw)) (mem_sphere.1 h1)
    have hcont : Continuous (fun θ : ℝ => deriv (circleMap c 1) θ • (circleMap c 1 θ - w)⁻¹ • F (circleMap c 1 θ)) := by
      have e : deriv (circleMap c 1) = fun θ => circleMap 0 1 θ * Complex.I := funext (deriv_circleMap c 1)
      rw [e]
      exact ((continuous_circleMap 0 1).mul continuous_const).smul
        ((((continuous_circleMap c 1).sub continuous_const).inv₀ hne).smul (hc.comp (continuous_circleMap c 1)))
    have hcomm : (∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ = ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z κ := by
      have e2 := (ContinuousMap.evalCLM ℂ κ : C(K, ℂ) →L[ℂ] ℂ).intervalIntegral_comp_comm
        (hcont.intervalIntegrable (μ := volume) 0 (2 * π))
      simp only [circleIntegral]
      refine e2.symm.trans ?_
      simp [ContinuousMap.evalCLM]
    have hfin : ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ
        = (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ := rfl
    rw [hfin, hcomm]
    exact hcau
  have han : AnalyticAt ℂ F c := by
    have h1 := hfp.analyticAt
    refine h1.congr ?_
    filter_upwards [ball_mem_nhds c (one_pos : (0:ℝ) < 1)] with w hw using heq w hw
  exact han.differentiableAt

theorem exists_integralCLM {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (μ : Measure K) [IsProbabilityMeasure μ]
    (r : K → E) (hr : Continuous r) : ∃ L : C(K, ℂ) →L[ℂ] E, ∀ f : C(K, ℂ), L f = ∫ κ, f κ • r κ ∂μ := by
  haveI : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • r κ) μ := fun f =>
    (f.continuous.smul hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let rc : C(K, E) := ⟨r, hr⟩
  let L₀ : C(K, ℂ) →ₗ[ℂ] E :=
    { toFun := fun f => ∫ κ, f κ • r κ ∂μ
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun a f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact integral_smul a _ }
  refine ⟨L₀.mkContinuous ‖rc‖ fun f => ?_, fun f => rfl⟩
  have hb : ∀ κ, ‖f κ • r κ‖ ≤ ‖rc‖ * ‖f‖ := fun κ => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (rc.norm_coe_le_norm κ) (f.norm_coe_le_norm κ) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hb)
  change ‖∫ κ, f κ • r κ ∂μ‖ ≤ _
  simpa using this

theorem gauss_bound (b a : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ a →
    ‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2 ≤ M := by
  set B : ℝ := |a| + |b| with hB
  have hB0 : 0 ≤ B := by positivity
  set c : ℝ := 3 + B with hc
  refine ⟨Real.exp (B ^ 2) * (6 * Real.exp c), by positivity, fun z h1 h2 => ?_⟩
  have hx : |z.re| ≤ B := by
    rw [abs_le]; constructor
    · have := neg_abs_le b; have := abs_nonneg a; linarith
    · have := le_abs_self a; have := abs_nonneg b; linarith
  set t : ℝ := |z.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hz : ‖z‖ ≤ B + t := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hexp : ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    rw [Complex.norm_exp]; congr 1
    simp [pow_two, Complex.mul_re]
  have h1z : ‖z - 1‖ ≤ 1 + ‖z‖ := by
    refine (norm_sub_le _ _).trans ?_
    simp [add_comm]
  have hs : 1 + ‖z‖ ≤ c + t ^ 2 - 1 := by nlinarith [sq_nonneg (t - 1)]
  have hn0 : 0 ≤ 1 + ‖z‖ := by positivity
  have hc0 : 0 ≤ c + t ^ 2 := by positivity
  have hcube : (1 + ‖z‖) ^ 3 ≤ 6 * Real.exp (c + t ^ 2) := by
    have h3 := Real.pow_div_factorial_le_exp (c + t ^ 2) hc0 3
    have h4 : (1 + ‖z‖) ^ 3 ≤ (c + t ^ 2) ^ 3 := pow_le_pow_left₀ hn0 (by linarith) 3
    have h5 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h5] at h3
    linarith [(div_le_iff₀ (by norm_num : (0:ℝ) < 6)).1 h3]
  have hre : z.re ^ 2 ≤ B ^ 2 := by
    have := sq_le_sq' (by linarith [(abs_le.1 hx).1]) (abs_le.1 hx).2
    exact this
  have him : z.im ^ 2 = t ^ 2 := by rw [ht, sq_abs]
  calc ‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2
      = Real.exp (z.re ^ 2 - z.im ^ 2) * (‖z - 1‖ * (1 + ‖z‖) ^ 2) := by
        rw [norm_mul, hexp]; ring
    _ ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * ((1 + ‖z‖) ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : (1 + ‖z‖) ^ 3 = (1 + ‖z‖) * (1 + ‖z‖) ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h1z (by positivity)
    _ ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * (6 * Real.exp (c + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hcube (Real.exp_pos _).le
    _ = Real.exp (z.re ^ 2) * (6 * Real.exp c) := by
        rw [him, Real.exp_add, Real.exp_sub, Real.exp_add]
        have := (Real.exp_pos (t ^ 2)).ne'
        field_simp
    _ ≤ Real.exp (B ^ 2) * (6 * Real.exp c) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hre) (by positivity)

theorem hGood : HGood := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hprob Φ hΦ
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨L, hL⟩ := exists_integralCLM μ (fun κ => ρ κ) hρ
  let Ψ₀ : C((ℂ × G) × K, ℂ) := ⟨fun p => Φ p.1.1 (p.1.2 * p.2),
    hΦ.cont.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)))⟩
  let Ψ : C(ℂ × G, C(K, ℂ)) := Ψ₀.curry
  have hA : ∀ (z : ℂ) (g : G), avg μ ρ (fun κ => Φ z (g * κ)) = L (Ψ (z, g)) := by
    intro z g
    rw [hL]
    rfl
  refine ⟨fun g => ?_, ?_, fun b a g => ?_⟩
  · simp only [hA]
    have hF : Differentiable ℂ fun z : ℂ => Ψ (z, g) :=
      differentiable_of_pointwise _ (Ψ.continuous.comp (by fun_prop)) fun κ => hΦ.ent (g * κ)
    exact ((Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul
      (differentiable_id.sub_const 1)).smul (L.differentiable.comp hF)
  · simp only [hA, Prod.mk.eta]
    exact (by fun_prop : Continuous fun y : ℂ × G => Complex.exp (y.1 ^ 2) * (y.1 - 1)).smul
      (L.continuous.comp Ψ.continuous)
  · obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds g
    obtain ⟨M, hM⟩ := hΦ.strip b a (U * (K : Set G)) (hUc.mul hK)
    obtain ⟨M2, hM2, hg⟩ := gauss_bound b a
    refine ⟨U, hU, ‖L‖ * |M| * M2, fun z h1 h2 g' hg' => ?_⟩
    rw [hA, norm_smul]
    have hΨ : ‖Ψ (z, g')‖ ≤ |M| * (1 + ‖z‖) ^ 2 := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun κ => ?_
      have h := hM z h1 h2 (g' * κ) (Set.mul_mem_mul hg' κ.2)
      exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
    calc ‖Complex.exp (z ^ 2) * (z - 1)‖ * ‖L (Ψ (z, g'))‖
        ≤ ‖Complex.exp (z ^ 2) * (z - 1)‖ * (‖L‖ * (|M| * (1 + ‖z‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left ((L.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hΨ (norm_nonneg _))) (norm_nonneg _)
      _ = ‖L‖ * |M| * (‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2) := by ring
      _ ≤ ‖L‖ * |M| * M2 := mul_le_mul_of_nonneg_left (hg z h1 h2) (by positivity)

end GlobalTheory.CompanionTheory.RgEisHGood
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPi
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

open scoped SchwartzMap Classical

set_option synthInstance.maxSize 1000

noncomputable section

namespace GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat

open GroundTheory.Automorphic.Adele2 NumberField.mixedEmbedding

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

def mulVecCLE (M : GL ι (mixedSpace k)) : (ι → mixedSpace k) ≃L[ℝ] (ι → mixedSpace k) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u ↦ (M : Matrix ι ι (mixedSpace k)) *ᵥ u
      invFun := fun u ↦ ((M⁻¹ : GL ι (mixedSpace k)) : Matrix ι ι (mixedSpace k)) *ᵥ u
      map_add' := fun u v ↦ mulVec_add _ u v
      map_smul' := fun c u ↦ mulVec_smul _ c u
      left_inv := fun u ↦ by
        simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
      right_inv := fun u ↦ by
        simp only [mulVec_mulVec, Units.mul_inv, one_mulVec] }

theorem mulVecCLE_apply (M : GL ι (mixedSpace k)) (u : ι → mixedSpace k) :
    mulVecCLE M u = (M : Matrix ι ι (mixedSpace k)) *ᵥ u := rfl

def mulVecHomeo (M : GL ι 𝔸ᶠ[k]) : (ι → 𝔸ᶠ[k]) ≃ₜ (ι → 𝔸ᶠ[k]) where
  toFun u := (M : Matrix ι ι 𝔸ᶠ[k]) *ᵥ u
  invFun u := ((M⁻¹ : GL ι 𝔸ᶠ[k]) : Matrix ι ι 𝔸ᶠ[k]) *ᵥ u
  left_inv u := by simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
  right_inv u := by simp only [mulVec_mulVec, Units.mul_inv, one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem comp_mulVec_mem_finiteSchwartzBruhatPi (M : GL ι 𝔸ᶠ[k]) {g : (ι → 𝔸ᶠ[k]) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi k) :
    (fun z ↦ g ((M : Matrix ι ι 𝔸ᶠ[k]) *ᵥ z)) ∈ finiteSchwartzBruhatPi k := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi k).1 hg
  exact (mem_finiteSchwartzBruhatPi k).2
    ⟨h1.comp_continuous (mulVecHomeo M).continuous,
      h2.comp_isClosedEmbedding (mulVecHomeo M).isClosedEmbedding⟩

theorem infPartPi_mulVec (A : Matrix ι ι 𝔸[k]) (x : ι → 𝔸[k]) :
    infPartPi (A *ᵥ x) = A.map infRingHom *ᵥ infPartPi x := by
  funext i
  exact RingHom.map_mulVec infRingHom A x i

theorem finPartPi_mulVec (A : Matrix ι ι 𝔸[k]) (x : ι → 𝔸[k]) :
    finPartPi (A *ᵥ x) = A.map finRingHom *ᵥ finPartPi x := by
  funext i
  exact RingHom.map_mulVec finRingHom A x i

theorem ltr_schwartzBruhatTensorPi (A : GL ι 𝔸[k]) (φ : 𝓢(ι → mixedSpace k, ℂ))
    (g : (ι → 𝔸ᶠ[k]) → ℂ) :
    ltr A (schwartzBruhatTensorPi φ g) =
      schwartzBruhatTensorPi
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mulVecCLE (Matrix.GeneralLinearGroup.map infRingHom A)) φ)
        (fun z ↦ g ((Matrix.GeneralLinearGroup.map finRingHom A : GL ι 𝔸ᶠ[k]) *ᵥ z)) := by
  funext x
  have h1 : ((Matrix.GeneralLinearGroup.map infRingHom A : GL ι (mixedSpace k)) :
      Matrix ι ι (mixedSpace k)) = (A : Matrix ι ι 𝔸[k]).map infRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  have h2 : ((Matrix.GeneralLinearGroup.map finRingHom A : GL ι 𝔸ᶠ[k]) :
      Matrix ι ι 𝔸ᶠ[k]) = (A : Matrix ι ι 𝔸[k]).map finRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  simp only [ltr, schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, mulVecCLE_apply, h1, h2, infPartPi_mulVec, finPartPi_mulVec]

theorem ltr_mem {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]) :
    ltr A F ∈ schwartzBruhatPi (K := k) (ι := ι) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [ltr_schwartzBruhatTensorPi]
    exact schwartzBruhatTensorPi_mem _ (comp_mulVec_mem_finiteSchwartzBruhatPi _ hg)
  | zero => exact zero_mem _
  | add G H _ _ ihG ihH => exact add_mem ihG ihH
  | smul a G _ ih => exact Submodule.smul_mem _ a ih

end GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat
end
end

