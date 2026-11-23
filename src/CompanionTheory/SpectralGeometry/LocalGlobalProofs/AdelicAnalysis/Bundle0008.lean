module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0007
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicCharacterExponentialFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem DM_mulVec_emb_apply {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (y : ι → F) (i : ι) (w : InfinitePlace F) :
    (DM B ρ *ᵥ emb ρ y) (i, w) = ρ w ((B *ᵥ y) i) := by
  have h : ρ w ((B *ᵥ y) i) = ∑ j, ρ w (B i j) * ρ w (y j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, map_sum, map_mul]
  rw [h]
  simp only [mulVec, dotProduct, DM, emb, Fintype.sum_prod_type_right, blockDiagonal_apply]
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · simp

theorem emb_dotProduct_DM {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (a y : ι → F) :
    emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) = ∑ w, ρ w (a ⬝ᵥ (B *ᵥ y)) := by
  have h : ∀ w, ρ w (a ⬝ᵥ (B *ᵥ y)) = ∑ i, ρ w (a i) * ρ w ((B *ᵥ y) i) := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, map_sum, map_mul]
  simp only [h]
  rw [dotProduct, Fintype.sum_prod_type_right]
  simp only [DM_mulVec_emb_apply, emb]

theorem toA_dotProduct_Bf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (B : Matrix ι ι F) (a y : ι → F) :
    toA a ⬝ᵥ (Bf B *ᵥ toA y) = algebraMap F (A F) (a ⬝ᵥ (B *ᵥ y)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, toA, Bf, map_sum, map_mul, Matrix.map_apply]

theorem chiB_toA_eq_exp (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ)
    (hψ : IsStdChar F ψ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (hQ : QSetup M B ρ P) (a y : ι → F) :
    chiB ψ (Bf B) (toA a) (toA y) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
      ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) : ℝ) : ℂ)) := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  rw [chiB, toA_dotProduct_Bf, hψ.2, emb_dotProduct_DM, sum_rho_eq_trace hT hρ]
  norm_cast

end GlobalTheory.CompanionTheory.SW.ThW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompacts
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW

theorem not_lt_of_setLIntegral_compact_eq {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν]
    [ν.IsOpenPosMeasure] {B : Set X} (hB : IsOpen B) {D D' : X → ℝ≥0∞}
    (hD : ContinuousOn D B) (hD' : ContinuousOn D' B)
    (h : ∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν)
    {b : X} (hb : b ∈ B) : ¬ D b < D' b := by
  intro hlt
  obtain ⟨c1, h1, h12⟩ := exists_between hlt
  obtain ⟨c2, hc, h2⟩ := exists_between h12
  have hDa : ContinuousAt D b := hD.continuousAt (hB.mem_nhds hb)
  have hD'a : ContinuousAt D' b := hD'.continuousAt (hB.mem_nhds hb)

  have hN : {x | D x < c1} ∩ {x | c2 < D' x} ∩ B ∈ 𝓝 b :=
    Filter.inter_mem (Filter.inter_mem (hDa.eventually (gt_mem_nhds h1))
      (hD'a.eventually (lt_mem_nhds h2))) (hB.mem_nhds hb)
  obtain ⟨S, hSn, hSN, hS⟩ := local_compact_nhds hN
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hpos : ν S ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hSn).ne'
  have htop : ν S ≠ ∞ := hS.measure_lt_top.ne
  have hle1 : ∫⁻ x in S, D x ∂ν ≤ c1 * ν S := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hSm).2
      (Filter.Eventually.of_forall fun x hx => (hSN hx).1.1.le))
  have hle2 : c2 * ν S ≤ ∫⁻ x in S, D' x ∂ν := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hSm).2
      (Filter.Eventually.of_forall fun x hx => (hSN hx).1.2.le))
  have hmid : c1 * ν S < c2 * ν S := (ENNReal.mul_lt_mul_iff_left hpos htop).2 hc
  exact (hle1.trans_lt (hmid.trans_le hle2)).ne (h S hS fun x hx => (hSN hx).2)

theorem eq_of_setLIntegral_compact_eq :
    ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
      [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν]
      [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B →
      ContinuousOn D' B →
      (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) →
      ∀ b ∈ B, D b = D' b := by
  intro X _ _ _ _ _ _ ν _ _ B hB D D' hD hD' h b hb
  exact le_antisymm
    (not_lt.1 (not_lt_of_setLIntegral_compact_eq ν hB hD' hD (fun S hS hSB => (h S hS hSB).symm) hb))
    (not_lt.1 (not_lt_of_setLIntegral_compact_eq ν hB hD hD' h hb))

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinatePolynomialsFormMemKernelDifferential
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.SemilocalColumn

private lemma exists_sub_iota_mem_of_sub_involution_mem (A : Type) [CommRing A] [Finite (MaximalSpectrum A)]
    (y : MaximalSpectrum A → A) : ∃ a : A, ∀ M : MaximalSpectrum A, a - y M ∈ M.asIdeal := by
  have hcop : Pairwise (Function.onFun IsCoprime fun M : MaximalSpectrum A => M.asIdeal) := by
    intro M N hMN
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (M.isMaximal.coprime_of_ne N.isMaximal fun h => hMN (MaximalSpectrum.ext h))
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hcop fun M => Ideal.Quotient.mk M.asIdeal (y M)
  exact ⟨a, fun M => Ideal.Quotient.eq.mp (ha M)⟩

theorem exists_isUnit_add (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (m : ℕ)
    (x : Fin (m + 1) → A) (hx : ∃ c : Fin (m + 1) → A, ∑ i, c i * x i = 1) :
    ∃ a : Fin m → A, IsUnit (x 0 + ∑ k, a k * x k.succ) := by
  classical
  have hnot : ∀ M : MaximalSpectrum A, x 0 ∈ M.asIdeal → ∃ k : Fin m, x k.succ ∉ M.asIdeal := by
    intro M h0
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨c, hc⟩ := hx
    have hmem : ∀ i, x i ∈ M.asIdeal := fun i => Fin.cases h0 hall i
    apply M.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← hc]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hmem i)
  choose kM hkM using hnot
  let y : Fin m → MaximalSpectrum A → A := fun k M =>
    if h : x 0 ∈ M.asIdeal then (if kM M h = k then 1 else 0) else 0
  choose a ha using fun k => exists_sub_iota_mem_of_sub_involution_mem A (y k)
  refine ⟨a, ?_⟩
  by_contra hu
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.mpr hu)
  let M : MaximalSpectrum A := ⟨N, hN⟩
  have huM : x 0 + ∑ k, a k * x k.succ ∈ M.asIdeal := hle (Ideal.mem_span_singleton_self _)
  by_cases h0 : x 0 ∈ M.asIdeal
  · have hy : ∑ k, y k M * x k.succ = x (kM M h0).succ := by
      simp only [y, dif_pos h0, ite_mul, one_mul, zero_mul]
      simp [Finset.sum_ite_eq]
    have hin : x 0 + ∑ k, (a k - y k M) * x k.succ ∈ M.asIdeal :=
      M.asIdeal.add_mem h0 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (ha k M))
    have e : x (kM M h0).succ =
        (x 0 + ∑ k, a k * x k.succ) - (x 0 + ∑ k, (a k - y k M) * x k.succ) := by
      rw [← hy]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    exact hkM M h0 (e ▸ M.asIdeal.sub_mem huM hin)
  · apply h0
    have hs : ∑ k, a k * x k.succ ∈ M.asIdeal := by
      refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
      simpa [y, h0] using ha k M
    simpa using M.asIdeal.sub_mem huM hs

theorem exists_invertible_first_column :
    ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (m : ℕ) (x : Fin (m + 1) → A),
      (∃ c : Fin (m + 1) → A, ∑ i, c i * x i = 1) →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) A, IsUnit g.det ∧ ∀ i, g i 0 = x i := by
  intro A _ _ m x hx
  classical
  obtain ⟨a, ha⟩ := exists_isUnit_add A m x hx
  set u := x 0 + ∑ k, a k * x k.succ with hu
  let b : Fin (m + 1) → A := Fin.cons 0 a
  let E : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
    Matrix.of fun i j => if i = j then 1 else if i = 0 then -b j else 0
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
    Matrix.of fun i j => if j = 0 then (if i = 0 then u else x i) else if i = j then 1 else 0
  have hE : E.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · exact Finset.prod_eq_one fun i _ => by simp [E]
    · intro i j hij
      have hji : j < i := hij
      have hi : i ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hji
      simp [E, hji.ne', hi]
  have hD : D.det = u := by
    rw [Matrix.det_of_isLowerTriangular]
    · rw [Fin.prod_univ_succ]
      simp [D, Fin.succ_ne_zero]
    · intro i j hij
      have hij' : i < j := hij
      have hj : j ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hij'
      simp [D, hj, hij'.ne]
  refine ⟨E * D, ?_, fun i => ?_⟩
  · rw [Matrix.det_mul, hE, hD, one_mul]
    exact ha
  · rw [Matrix.mul_apply]
    by_cases hi : i = 0
    · subst hi
      rw [Fin.sum_univ_succ]
      simp [E, D, b, (Fin.succ_ne_zero _).symm, hu, Finset.sum_neg_distrib]
    · rw [Finset.sum_eq_single i]
      · simp [E, D, hi]
      · intro j _ hji
        simp [E, D, Ne.symm hji, hi]
      · simp

end GlobalTheory.CompanionTheory.SW.SemilocalColumn
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreFam

section Top

variable {V : Type} [TopologicalSpace V]

theorem exists_bump [LocallyCompactSpace V] [T2Space V] {K O : Set V} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧ (∀ v, 0 ≤ φ v) ∧
      (∀ v, φ v ≤ 1) ∧ ∀ v ∈ K, φ v = 1 := by
  obtain ⟨f, hf1, hfc, hfs, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  exact ⟨f, f.continuous, hfc, hfs, fun v => (hf01 v).1, fun v => (hf01 v).2, fun v hv => hf1 hv⟩

theorem exists_exhaustion [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} (hU : IsOpen U) :
    ∃ K W : ℕ → Set V, (∀ n, IsCompact (K n)) ∧ (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ K n) ∧
      (∀ n, K n ⊆ U) ∧ Monotone K ∧ Monotone W ∧ (⋃ n, K n) = U ∧ (⋃ n, W n) = U := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  have hint : ⋃ n, interior (E n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ n, E n := by
      rw [E.iUnion_eq]
      exact Set.mem_univ x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + 1, E.subset_interior_succ n hn⟩
  refine ⟨fun n => (↑) '' E n, fun n => (↑) '' interior (E n),
    fun n => (E.isCompact n).image continuous_subtype_val,
    fun n => hU.isOpenMap_subtype_val _ isOpen_interior, fun n => Set.image_mono interior_subset,
    fun n => by
      rintro _ ⟨x, -, rfl⟩
      exact x.2,
    fun m n hmn => Set.image_mono (E.subset hmn),
    fun m n hmn => Set.image_mono (interior_mono (E.subset hmn)), ?_, ?_⟩
  · rw [← Set.image_iUnion, E.iUnion_eq, Set.image_univ, Subtype.range_coe]
  · rw [← Set.image_iUnion, hint, Set.image_univ, Subtype.range_coe]

end Top

section Meas

variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]

theorem le_lintegral_bump [T2Space V] (m : Measure V) {K : Set V} (hK : IsCompact K) {φ : V → ℝ}
    (h0 : ∀ v, 0 ≤ φ v) (h1 : ∀ v ∈ K, φ v = 1) : m K ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [← lintegral_indicator_one hKm]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ K
  · simp [Set.indicator_apply, hv, h1 v hv]
  · simp [Set.indicator_apply, hv]

theorem lintegral_bump_le (m : Measure V) {O : Set V} (hO : IsOpen O) {φ : V → ℝ}
    (h1 : ∀ v, φ v ≤ 1) (hs : tsupport φ ⊆ O) : ∫⁻ v, ENNReal.ofReal (φ v) ∂m ≤ m O := by
  rw [← lintegral_indicator_one hO.measurableSet]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ O
  · simpa [Set.indicator_apply, hv] using h1 v
  · have hz : φ v = 0 := by
      by_contra hne
      exact hv (hs (subset_tsupport φ hne))
    simp [Set.indicator_apply, hv, hz]

variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def BumpFamily (U : Set V) (B : Set X) (fib : X → Measure V) : Prop :=
  (∀ b, b ∉ B → fib b = 0) ∧
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∀ b ∈ B, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) B

theorem BumpFamily.measurable_lintegral {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {φ : V → ℝ} (hc : Continuous φ)
    (hcs : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
  classical
  obtain ⟨h0B, hφ⟩ := h
  obtain ⟨hint, hcont⟩ := hφ φ hc hcs hs
  have heq : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =
      B.piecewise (fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b))) (fun _ => 0) := by
    funext b
    by_cases hb : b ∈ B
    · simp only [Set.piecewise_eq_of_mem, hb]
      rw [ofReal_integral_eq_lintegral_ofReal (hint b hb) (ae_of_all _ h0)]
    · simp [Set.piecewise, hb, h0B b hb]
  rw [heq]
  exact (ENNReal.continuous_ofReal.comp_continuousOn hcont).measurable_piecewise continuousOn_const
    hB.measurableSet

theorem BumpFamily.measurable_open [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {O : Set V} (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable fun b => fib b O := by
  obtain ⟨K, W, hKc, -, -, hKO, hKmono, -, hKU, -⟩ := exists_exhaustion hO
  have hφ : ∀ n, ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧ (∀ v, 0 ≤ φ v) ∧
      (∀ v, φ v ≤ 1) ∧ ∀ v ∈ K n, φ v = 1 := fun n => exists_bump (hKc n) hO (hKO n)
  choose φ hφc hφcs hφs hφ0 hφ1 hφK using hφ
  have hmeas : ∀ n, Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ n v) ∂(fib b) := fun n =>
    h.measurable_lintegral hB (hφc n) (hφcs n) ((hφs n).trans hOU) (hφ0 n)
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr fun b => ?_)
  have hlow : Filter.Tendsto (fun n => fib b (K n)) Filter.atTop (𝓝 (fib b O)) := by
    have h2 := tendsto_measure_iUnion_atTop (μ := fib b) hKmono
    rw [hKU] at h2
    exact h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => le_lintegral_bump (fib b) (hKc n) (hφ0 n) (hφK n))
    (fun n => lintegral_bump_le (fib b) hO (hφ1 n) (hφs n))

theorem BumpFamily.lt_top [LocallyCompactSpace V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hU : IsOpen U) {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) (b : X) :
    fib b K < ∞ := by
  by_cases hb : b ∈ B
  · obtain ⟨φ, hc, hcs, hs, h0, -, hK1⟩ := exists_bump hK hU hKU
    have hint := (h.2 φ hc hcs hs).1 b hb
    exact lt_of_le_of_lt (le_lintegral_bump (fib b) hK h0 hK1) hint.lintegral_lt_top
  · rw [h.1 b hb]
    simp

theorem BumpFamily.measurable_apply [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) (hU : IsOpen U) (hc : ∀ b, fib b Uᶜ = 0)
    {A : Set V} (hA : MeasurableSet A) : Measurable fun b => fib b A := by
  obtain ⟨K, W, hKc, hWo, hWK, hKU, -, hWmono, -, hWU⟩ := exists_exhaustion hU
  have hWn : ∀ n, Measurable fun b => fib b (A ∩ W n) := by
    intro n
    haveI : ∀ b, IsFiniteMeasure ((fib b).restrict (W n)) := fun b =>
      isFiniteMeasure_restrict.mpr
        (ne_of_lt (lt_of_le_of_lt (measure_mono (hWK n)) (h.lt_top hU (hKc n) (hKU n) b)))
    have hmeas : Measurable fun b => (fib b).restrict (W n) := by
      refine Measurable.measure_of_isPiSystem (S := {s : Set V | IsOpen s}) BorelSpace.measurable_eq
        isPiSystem_isOpen ?_ ?_
      · intro s hs
        have hso : IsOpen s := hs
        simp only [Measure.restrict_apply hso.measurableSet]
        exact h.measurable_open hB (hso.inter (hWo n))
          (Set.inter_subset_right.trans ((hWK n).trans (hKU n)))
      · simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact h.measurable_open hB (hWo n) ((hWK n).trans (hKU n))
    have h2 := (Measure.measurable_coe hA).comp hmeas
    simpa [Function.comp_def, Measure.restrict_apply hA] using h2
  have hlim : ∀ b, Filter.Tendsto (fun n => fib b (A ∩ W n)) Filter.atTop (𝓝 (fib b A)) := by
    intro b
    have hmono : Monotone fun n => A ∩ W n := fun m n hmn => Set.inter_subset_inter_right _ (hWmono hmn)
    have h2 := tendsto_measure_iUnion_atTop (μ := fib b) hmono
    rw [← Set.inter_iUnion, hWU, measure_inter_conull (hc b)] at h2
    exact h2
  exact measurable_of_tendsto_metrizable hWn (tendsto_pi_nhds.mpr hlim)

end Meas

theorem fibre_family_basic : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g →
    (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V,
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib →
    (∀ b, IsLocallyFiniteMeasure (fib b)) ∧ (∀ b, b ∉ B → fib b = 0) ∧
    (∀ A : Set V, MeasurableSet A → Measurable fun b => fib b A) ∧
    ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B →
      ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hfv B hB fib hF
  classical
  obtain ⟨hfib0, -, hbump⟩ := hF
  have hU : IsOpen (g ⁻¹' B) := hB.preimage hg
  have hmemι : ∀ b w, w ∈ f ⁻¹' {ι b} → g w = b := by
    intro b w hw
    apply hι
    rw [← hfv w]
    exact hw
  have hfibB : ∀ b, b ∉ B → fib b = 0 := by
    intro b hb
    have hempty : f ⁻¹' {ι b} ∩ g ⁻¹' B = ∅ := by
      refine Set.subset_empty_iff.mp fun w hw => (hb ?_).elim
      rw [← hmemι b w hw.1]
      exact hw.2
    have h0 := hfib0 b
    rw [hempty, Set.compl_empty] at h0
    exact Measure.measure_univ_eq_zero.mp h0
  have hBF : BumpFamily (g ⁻¹' B) B fib := ⟨hfibB, hbump⟩
  refine ⟨?_, hfibB, ?_, ?_⟩
  · intro b
    refine ⟨fun v => ?_⟩
    by_cases hb : b ∈ B
    · by_cases hgv : g v = b
      · have hvU : v ∈ g ⁻¹' B := by
          rw [Set.mem_preimage, hgv]
          exact hb
        obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds (hU.mem_nhds hvU)
        exact ⟨K, hKn, hBF.lt_top hU hKc hKU b⟩
      · refine ⟨g ⁻¹' {b}ᶜ, (isClosed_singleton.preimage hg).isOpen_compl.mem_nhds hgv, ?_⟩
        have h0 : fib b (g ⁻¹' {b}ᶜ) = 0 := by
          exact measure_mono_null (show g ⁻¹' {b}ᶜ ⊆ (f ⁻¹' {ι b} ∩ g ⁻¹' B)ᶜ from
            fun w hw hw' => hw (hmemι b w hw'.1)) (hfib0 b)
        rw [h0]
        exact ENNReal.zero_lt_top
    · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      rw [hfibB b hb]
      simp
  · intro A hA
    exact hBF.measurable_apply hB hU (fun b => measure_mono_null
      (show (g ⁻¹' B)ᶜ ⊆ (f ⁻¹' {ι b} ∩ g ⁻¹' B)ᶜ from fun w hw hw' => hw hw'.2) (hfib0 b)) hA
  · intro C D hC hD hDB
    have hC' : IsCompact (C ∩ g ⁻¹' D) := hC.inter_right (hD.isClosed.preimage hg)
    have hC'U : C ∩ g ⁻¹' D ⊆ g ⁻¹' B := fun w hw => hDB hw.2
    obtain ⟨φ, hc, hcs, hs, h0, -, h1⟩ := exists_bump hC' hU hC'U
    obtain ⟨hint, hcont⟩ := hbump φ hc hcs hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hcont.mono hDB)
    refine ⟨Real.toNNReal M, fun b hb => ?_⟩
    calc fib b C = fib b (C ∩ (f ⁻¹' {ι b} ∩ g ⁻¹' B)) := (measure_inter_conull (hfib0 b)).symm
      _ ≤ fib b (C ∩ g ⁻¹' D) := by
          refine measure_mono (show C ∩ (f ⁻¹' {ι b} ∩ g ⁻¹' B) ⊆ C ∩ g ⁻¹' D from
            fun w hw => ⟨hw.1, ?_⟩)
          show g w ∈ D
          rw [hmemι b w hw.2.1]
          exact hb
      _ ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := le_lintegral_bump (fib b) hC' h0 h1
      _ = ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
          (ofReal_integral_eq_lintegral_ofReal (hint b (hDB hb)) (ae_of_all _ h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hM b hb))
      _ = (Real.toNNReal M : ℝ≥0∞) := rfl

end GlobalTheory.CompanionTheory.SW.FibreFam
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FibreFamilySmul
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.Rescale

theorem isFibreFamily_rescale (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y)
    (ι : X → Y) (U : Set V) (B : Set X) (fib : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) (a c : ℝ≥0) (hc : c ≠ 0) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (a • μ) f ι U (c • ν) B (fun b => (a / c) • fib b) := by
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h ⊢
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · rw [Measure.smul_apply, h.1 b, smul_zero]
  · simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [h.2.1 φ hφ, lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_comm c, div_mul_cancel₀ a hc]
  · obtain ⟨h1, h2⟩ := h.2.2 φ hφc hφs hφU
    refine ⟨fun b hb => (h1 b hb).smul_measure_nnreal, ?_⟩
    have e : (fun b => ∫ v, φ v ∂((a / c) • fib b)) = fun b => ((a / c : ℝ≥0) : ℝ) • ∫ v, φ v ∂fib b := by
      funext b
      rw [integral_smul_nnreal_measure, NNReal.smul_def]
    rw [e]
    exact h2.const_smul ((a / c : ℝ≥0) : ℝ)

end GlobalTheory.CompanionTheory.SW.Rescale
end

