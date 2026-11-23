module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNonnegFamilyOfDifferentiableOn
section
open Filter Topology

namespace GlobalTheory

theorem summable_nonneg_family_of_differentiableOn {ι : Type} (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ) (hc : ∀ i, 0 ≤ c i) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hser : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => (c i : ℂ) * z ^ n i) (R z))
    (x : ℝ) (hx0 : 0 ≤ x) (hxr : x < r) : Summable (fun i => c i * x ^ n i) := by
  have hr : 0 < r := lt_of_le_of_lt hx0 hxr
  set t0 : ℝ := ε / 2 with ht0
  have ht0pos : 0 < t0 := by positivity
  have ht0ε : t0 < ε := by linarith
  have hnt0 : ‖(t0 : ℂ)‖ = t0 := by simp [abs_of_pos ht0pos]
  have hsum0 : Summable (fun i => c i * t0 ^ n i) := by
    have h := (hser (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable
    have e : (fun i => (c i : ℂ) * (t0 : ℂ) ^ n i) = fun i => ((c i * t0 ^ n i : ℝ) : ℂ) := by
      funext i; push_cast; rfl
    rw [e] at h
    exact Complex.summable_ofReal.mp h
  have hfib : ∀ m : ℕ, Summable (fun i : n ⁻¹' {m} => c i) := by
    intro m
    have h1 := (hsum0.subtype (fun i => n i = m)).mul_right (t0 ^ m)⁻¹
    refine h1.congr fun i => ?_
    have hi : n i.val = m := i.2
    simp only [Function.comp_apply]
    rw [hi, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0pos.ne'), mul_one]
  set C : ℕ → ℝ := fun m => ∑' i : n ⁻¹' {m}, c i with hC
  have hCnn : ∀ m, 0 ≤ C m := fun m => tsum_nonneg (fun i => hc i)
  have hgroup : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun m => (C m : ℂ) * z ^ m) (R z) := by
    intro z hz1 hz2
    refine ((hser z hz1 hz2).tsum_fiberwise n).congr_fun fun m => ?_
    have e1 : (∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ n i) = ∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ m :=
      tsum_congr fun i => by rw [show n i = m from i.2]
    rw [e1, tsum_mul_right, hC, Complex.ofReal_tsum]
  have hCt0 : Summable (fun m => C m * t0 ^ m) := by
    have h := (hgroup (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable
    have e : (fun m => (C m : ℂ) * (t0 : ℂ) ^ m) = fun m => ((C m * t0 ^ m : ℝ) : ℂ) := by
      funext m; push_cast; rfl
    rw [e] at h
    exact Complex.summable_ofReal.mp h
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => (C m : ℂ)) with hq
  have hqapply : ∀ (m : ℕ) (z : ℂ), q m (fun _ => z) = (C m : ℂ) * z ^ m := by
    intro m z; rw [hq, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  set t0n : NNReal := ⟨t0, ht0pos.le⟩ with ht0n
  have hrad : (t0n : ENNReal) ≤ q.radius := by
    refine q.le_radius_of_bound (∑' m, C m * t0 ^ m) fun m => ?_
    rw [show ((t0n : ℝ)) = t0 from rfl]
    have hn : ‖q m‖ = C m := by
      rw [hq, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hCnn m)]
    rw [hn]
    exact hCt0.le_tsum m (fun j _ => mul_nonneg (hCnn j) (pow_nonneg ht0pos.le _))
  have hradpos : 0 < q.radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (NNReal.coe_pos.mp (show (0:ℝ) < (t0n : ℝ) from ht0pos))) hrad
  have hqball := q.hasFPowerSeriesOnBall hradpos
  have hRan : AnalyticAt ℂ R 0 := hR.analyticAt (Metric.ball_mem_nhds 0 hr)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), R z = q.sum z := by
    apply Eventually.frequently
    have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) ε :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hb, self_mem_nhdsWithin] with z hz hz0
    have hz0' : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [mem_ball_zero_iff] at hz
    rw [FormalMultilinearSeries.sum]
    simp_rw [hqapply]
    exact ((hgroup z hz0' hz).tsum_eq).symm
  have hev := (hRan.frequently_eq_iff_eventually_eq hqball.analyticAt).mp hfreq
  have hRq : HasFPowerSeriesAt R q 0 := hqball.hasFPowerSeriesAt.congr (hev.mono fun z h => h.symm)
  set ρ : ℝ := (x + r) / 2 with hρ
  have hρpos : 0 < ρ := by linarith
  set ρn : NNReal := ⟨ρ, hρpos.le⟩ with hρn
  have hcl : DifferentiableOn ℂ R (Metric.closedBall 0 (ρn : ℝ)) :=
    hR.mono (Metric.closedBall_subset_ball (by show ρ < r; linarith))
  have hp := hcl.hasFPowerSeriesOnBall (by exact_mod_cast hρpos)
  have hpq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hRq
  rw [hpq] at hp
  have hxn : ‖(x : ℂ)‖₊ < ρn := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    show x < ρ
    linarith
  have hxmem : (x : ℂ) ∈ Metric.eball (0 : ℂ) (ρn : ENNReal) := by
    show edist (x : ℂ) 0 < ρn
    rw [edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast hxn
  have hsx := (hp.hasSum hxmem).summable
  simp_rw [hqapply] at hsx
  have hCx : Summable (fun m => C m * x ^ m) := by
    have e : (fun m => (C m : ℂ) * (x : ℂ) ^ m) = fun m => ((C m * x ^ m : ℝ) : ℂ) := by
      funext m; push_cast; rfl
    rw [e] at hsx
    exact Complex.summable_ofReal.mp hsx
  rw [← (Equiv.sigmaFiberEquiv n).summable_iff]
  refine (summable_sigma_of_nonneg fun p => ?_).mpr ⟨fun m => ?_, ?_⟩
  · exact mul_nonneg (hc _) (pow_nonneg hx0 _)
  · refine ((hfib m).mul_right (x ^ m)).congr fun i => ?_
    simp [Equiv.sigmaFiberEquiv, show n i = m from i.2]
  · refine hCx.congr fun m => ?_
    have e1 : (∑' i : {i // n i = m}, ((fun i => c i * x ^ n i) ∘ (Equiv.sigmaFiberEquiv n))
        ⟨m, i⟩) = ∑' i : n ⁻¹' {m}, c i * x ^ m :=
      tsum_congr fun i => by simp [Equiv.sigmaFiberEquiv, show n i = m from i.2]
    rw [e1, tsum_mul_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNormCosetOut
section
open MeasureTheory

namespace GlobalTheory

theorem summable_norm_coset_out (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (hμ : μ K = 1) (F : G → ℂ)
    (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (hint : Integrable F μ) :
    Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  classical
  set C : G ⧸ K → Set G := fun x => (fun y => x.out⁻¹ * y) ⁻¹' (K : Set G) with hCdef
  have hCmeas : ∀ x, MeasurableSet (C x) := fun x =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hCμ : ∀ x, μ (C x) = 1 := by
    intro x
    simp only [C]
    rw [measure_preimage_mul]; exact hμ
  have hconst : ∀ x, ∀ y ∈ C x, F y = F x.out := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have := hF x.out _ hy'
    simpa using this
  have hmk : ∀ x, ∀ y ∈ C x, (QuotientGroup.mk y : G ⧸ K) = x := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have h1 : (QuotientGroup.mk y : G ⧸ K) = QuotientGroup.mk x.out :=
      (QuotientGroup.eq.mpr hy').symm
    rw [h1]; exact Quotient.out_eq x
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro x y hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    exact hxy ((hmk x z hzx).symm.trans (hmk y z hzy))
  have hnorm : Integrable (fun y => ‖F y‖) μ := hint.norm
  have hterm : ∀ x, ∫ y in C x, ‖F y‖ ∂μ = ‖F x.out‖ := by
    intro x
    rw [setIntegral_congr_fun (hCmeas x) (g := fun _ => ‖F x.out‖) (fun y hy => by
      simp only; rw [hconst x y hy])]
    rw [setIntegral_const]
    simp [Measure.real, hCμ x]
  refine summable_of_sum_le (c := ∫ y, ‖F y‖ ∂μ) (fun x => norm_nonneg _) ?_
  intro S
  calc ∑ x ∈ S, ‖F x.out‖ = ∑ x ∈ S, ∫ y in C x, ‖F y‖ ∂μ := by
        simp only [hterm]
    _ = ∫ y in ⋃ x ∈ S, C x, ‖F y‖ ∂μ := by
        rw [integral_biUnion_finset S (fun x _ => hCmeas x) (hdisj.set_pairwise _)
          (fun x _ => hnorm.integrableOn)]
    _ ≤ ∫ y, ‖F y‖ ∂μ :=
        setIntegral_le_integral hnorm (Filter.Eventually.of_forall (fun y => norm_nonneg _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMatrixPiOperator
section
namespace GlobalTheory

theorem trace_matrix_pi_operator : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  intro W _ _ _ m h A
  have key : ∀ k j : Fin m, LinearMap.trace ℂ (Fin m → W)
      (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ LinearMap.proj j)
      = if k = j then LinearMap.trace ℂ W A else 0 := by
    intro k j
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    by_cases hkj : k = j
    · subst hkj
      rw [LinearMap.proj_comp_single_same, LinearMap.comp_id, if_pos rfl]
    · rw [LinearMap.proj_comp_single_ne (R := ℂ) (φ := fun _ : Fin m => W) j k (Ne.symm hkj), LinearMap.comp_zero, map_zero, if_neg hkj]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.sum_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbits
section
open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace OrbitUnfold

variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}

def pull (𝓕 : Set H) (g : H) : Set H := (fun h => g * h) ⁻¹' 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull (hF : IsFundamentalDomain Γ 𝓕 ν) (g : H) :
    NullMeasurableSet (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 g) ν :=
  hF.nullMeasurableSet.preimage (measurePreserving_mul_left ν g).quasiMeasurePreserving

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull (hF : IsFundamentalDomain Γ 𝓕 ν) {a b : Γ}
    (hab : a ≠ b) :
    AEDisjoint ν (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (a : H)) (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (b : H)) := by
  have key : ∀ c : Γ, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (c : H) = c⁻¹ • 𝓕 := fun c => by
    ext x
    simp [_root_.GlobalTheory.OrbitUnfold.pull, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  rw [key, key]
  exact hF.aedisjoint (inv_injective.ne hab)

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (g : H) (f : H → ℂ) :
    ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setIntegral_preimage_emb (measurableEmbedding_mulLeft g) f 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (g : H) (f : H → ℝ≥0∞) :
    ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫⁻ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft g) f 𝓕


open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull (hF : IsFundamentalDomain Γ 𝓕 ν)
    (y₀ : Y) {O : Set Y}
    [Countable O] (hO : ∀ γ : Γ, γ • y₀ ∈ O) (σ : O → Γ) (hσ : ∀ a : O, σ a • y₀ = a) :
    IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype)
      (⋃ a : O, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν := by
  refine ⟨.iUnion (fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _), ?_, ?_⟩
  ·
    filter_upwards [hF.ae_covers] with x ⟨γ, hγ⟩
    let a : O := ⟨γ • y₀, hO γ⟩
    have hs : (σ a)⁻¹ * γ ∈ MulAction.stabilizer Γ y₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ a]
    refine ⟨⟨Γ.subtype ((σ a)⁻¹ * γ), Subgroup.mem_map_of_mem _ hs⟩, Set.mem_iUnion.2 ⟨a, ?_⟩⟩
    simpa [_root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def, mul_assoc] using hγ
  ·
    rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hst
    have hset : ∀ (u : Γ) (hu : u ∈ MulAction.stabilizer Γ y₀) (a : O),
        (⟨Γ.subtype u, Subgroup.mem_map_of_mem _ hu⟩ :
            (MulAction.stabilizer Γ y₀).map Γ.subtype) •
          _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H) = (σ a * u⁻¹)⁻¹ • 𝓕 := by
      intro u hu a
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem, _root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def,
        mul_assoc]
    simp only [Function.onFun, Set.smul_set_iUnion, hset s hs, hset t ht]
    refine AEDisjoint.iUnion_left_iff.2 fun a => AEDisjoint.iUnion_right_iff.2 fun b => ?_
    refine hF.aedisjoint (inv_injective.ne fun h => hst ?_)
    have hab : a = b := by
      apply Subtype.ext
      have h1 := congrArg (· • y₀) h
      simp only [mul_smul] at h1
      rwa [inv_smul_eq_iff.2 hs.symm, inv_smul_eq_iff.2 ht.symm, hσ, hσ] at h1
    subst hab
    have : s = t := inv_injective (mul_left_cancel h)
    subst this
    rfl

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
private theorem selfEquivSigmaOrbits_symm_mk {G X : Type} [Group G] [MulAction G X]
    (ω : MulAction.orbitRel.Quotient G X) (x : MulAction.orbit G ω.out) :
    (MulAction.selfEquivSigmaOrbits G X).symm ⟨ω, x⟩ = x := rfl


open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H)
      [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y]
      [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ,
      (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) →
      ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ →
      (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν →
        IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) →
      ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  intro H _ _ _ ν _ Γ _ Y _ _ 𝓕 hF Φ hmeas hinv hfin hzero
  have horbit : ∀ y₀ : Y, ∑' a : MulAction.orbit Γ y₀, ∫ h in 𝓕, Φ a h ∂ν = 0 := by
    intro y₀
    have hO : ∀ γ : Γ, γ • y₀ ∈ MulAction.orbit Γ y₀ := fun γ => MulAction.mem_orbit y₀ γ
    choose σ hσ using fun a : MulAction.orbit Γ y₀ =>
      (MulAction.mem_orbit_iff.1 a.2 : ∃ g : Γ, g • y₀ = a)
    have hT := _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull hF y₀ hO σ hσ
    have hshift : ∀ a : MulAction.orbit Γ y₀, ∀ h, Φ a ((σ a : H) * h) = Φ y₀ h := fun a h => by
      rw [← hinv (σ a) y₀ h, hσ]
    have hpt : ∀ a : MulAction.orbit Γ y₀,
        ∫ h in 𝓕, Φ a h ∂ν = ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), Φ y₀ h ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (σ a : H) (Φ a)]
      simp only [hshift]
    have hlpt : ∀ a : MulAction.orbit Γ y₀,
        ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (σ a : H) (fun h => ‖Φ a h‖ₑ)]
      simp only [hshift]
    have hσinj : Function.Injective σ := fun a b hab =>
      Subtype.ext (by rw [← hσ a, ← hσ b, hab])
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν)
        fun a : MulAction.orbit Γ y₀ => _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) :=
      fun a b hab => _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull hF (hσinj.ne hab)
    have hint : IntegrableOn (Φ y₀)
        (⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν := by
      refine ⟨(hmeas y₀).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ h in ⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν
          ≤ ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν :=
            lintegral_iUnion_le _ _
        _ = ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by simp only [hlpt]
        _ ≤ ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
            (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
        _ < ⊤ := lt_top_iff_ne_top.2 hfin
    simp only [hpt]
    rw [← integral_iUnion_ae (fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hdisj hint]
    exact hzero y₀ _ hT hint
  have hsum : Summable fun y => ∫ h in 𝓕, Φ y h ∂ν := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun y => ?_
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono (ENNReal.ne_top_of_tsum_ne_top hfin y)
      (enorm_integral_le_lintegral_enorm _)
  have hs' := ((MulAction.selfEquivSigmaOrbits Γ Y).symm.summable_iff
    (f := fun y => ∫ h in 𝓕, Φ y h ∂ν)).2 hsum
  rw [← (MulAction.selfEquivSigmaOrbits Γ Y).symm.tsum_eq (fun y => ∫ h in 𝓕, Φ y h ∂ν)]
  simp only [Function.comp_def] at hs'
  rw [Summable.tsum_sigma hs']
  simp only [Function.comp_apply, selfEquivSigmaOrbits_symm_mk, horbit, tsum_zero]

end OrbitUnfold
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldIntegralFundamentalDomain
section
open MeasureTheory

namespace GlobalTheory

theorem unfold_integral_fundamentalDomain (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) : μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → ∀ c g : G → ℂ, Integrable c μ → Continuous g → (∃ B : ℝ, ∀ w, ‖g w‖ ≤ B) → ∫ w, c w * g w ∂μ = ∫ w in 𝓕, ∑' γ : Γ, c ((γ : G) + w) * g ((γ : G) + w) ∂μ := by
  intro hμ 𝓕 h𝓕 c g hc hg hB
  obtain ⟨B, hB⟩ := hB
  have hcg : Integrable (fun w => c w * g w) μ :=
    hc.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  rw [h𝓕.integral_eq_tsum'' _ hcg]
  have hmeas : ∀ γ : Γ, AEStronglyMeasurable (fun w => c ((γ : G) + w) * g ((γ : G) + w)) (μ.restrict 𝓕) := by
    intro γ
    exact (hcg.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_left μ (γ : G))).restrict
  have hfin : ∑' γ : Γ, ∫⁻ w in 𝓕, ‖c ((γ : G) + w) * g ((γ : G) + w)‖ₑ ∂μ ≠ ⊤ := by
    have := h𝓕.lintegral_eq_tsum'' (fun w => ‖c w * g w‖ₑ)
    simp only [AddSubgroup.vadd_def, vadd_eq_add] at this
    rw [← this]
    exact hcg.2.ne
  simp only [AddSubgroup.vadd_def, vadd_eq_add]
  exact (integral_tsum hmeas hfin).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryExistsSkewLog
section
open Matrix

namespace GlobalTheory


open scoped Matrix.Norms.L2Operator in
theorem unitary_submonoid_exists_skewAdjoint_log_polynomial (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ)
    (hk : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      star X = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  classical
  have hspec := spectrum.subset_circle_of_unitary (𝕜 := ℂ) hk
  have hfin := Matrix.finite_spectrum k
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k) := fun f => hfin.continuousOn f
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ z ∈ spectrum ℂ k, p.eval z = Complex.log z := by
    refine ⟨Lagrange.interpolate hfin.toFinset id Complex.log, fun z hz => ?_⟩
    have := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) (i := z) Complex.log
      (Set.injOn_id _) (by simpa using hz)
    simpa using this
  refine ⟨cfc Complex.log k, p, ?_, ?_, ?_⟩
  · rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    have h1 : ‖z‖ = 1 := by simpa using hspec hz
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
  · rw [← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp Complex.exp Complex.log k
      (hg := (Set.Finite.image _ hfin).continuousOn _) (hf := hcont _)]
    have h0 : ∀ z ∈ spectrum ℂ k, (Complex.exp ∘ Complex.log) z = id z := by
      intro z hz
      have h1 : ‖z‖ = 1 := by simpa using hspec hz
      have : z ≠ 0 := by rintro rfl; simp at h1
      simp [Complex.exp_log this]
    rw [cfc_congr h0, cfc_id ℂ k]
  · rw [← cfc_polynomial p k]
    exact cfc_congr fun z hz => (hp z hz).symm

theorem unitary_exists_skew_log (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ) (hk : kᴴ * k = 1) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  have hmem : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨hk, mul_eq_one_comm.mp hk⟩
  obtain ⟨X, p, h1, h2, h3⟩ := unitary_submonoid_exists_skewAdjoint_log_polynomial n k hmem
  exact ⟨X, p, h1, h2, h3⟩

end GlobalTheory
end

