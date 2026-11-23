module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IsClosedRangeNU
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem isClosed_range_nU {F : Type} [Field F] [NumberField F] :
    IsClosed (Set.range (nU : A F → G1 F)) := by
  have e : Set.range (nU : A F → G1 F) = {g : G1 F | g 0 0 = 1} ∩ ({g : G1 F | g 1 0 = 0} ∩ {g : G1 F | g 1 1 = 1}) := by
    ext g
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A F)) 0 0 = 1
        simp
      · show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A F)) 1 0 = 0
        simp
      · show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A F)) 1 1 = 1
        simp
    · rintro ⟨h0, h1, h2⟩
      refine ⟨g 0 1, Subtype.ext ?_⟩
      simp only [Set.mem_setOf_eq] at h0 h1 h2
      ext i j
      fin_cases i <;> fin_cases j <;> simp [nU, h0, h1, h2]
  rw [e]
  exact (isClosed_eq (M.continuous_entry 0 0) continuous_const).inter
    ((isClosed_eq (M.continuous_entry 1 0) continuous_const).inter
      (isClosed_eq (M.continuous_entry 1 1) continuous_const))

private theorem quot_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {U : Set (IdeleGroup F)} (hbor : ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → a ∈ U ∧ ab a = 1)
    {a a' : (A F)ˣ} {b : A F} {k k' : G1 F} (hk : k ∈ KK F) (hk' : k' ∈ KK F)
    (h : mD a * k = nU b * mD a' * k') : a'⁻¹ * a ∈ U := by
  obtain ⟨hKs, -⟩ := M.kkCpt F
  have hm : k' * k⁻¹ ∈ KK F := by
    rw [hKs] at hk hk' ⊢
    exact (M.Ks F).mul_mem hk' ((M.Ks F).inv_mem hk)
  have e : k' * k⁻¹ = nU (((a'⁻¹ : (A F)ˣ) : A F) ^ 2 * (-b)) * mD (a'⁻¹ * a) := by
    rw [M.mD_mul, ← mul_assoc, ← M.mD_mul_nU, M.nU_neg, M.mD_inv]
    have : k' = (mD a')⁻¹ * (nU b)⁻¹ * (mD a * k) := by rw [h]; group
    rw [this]; group
  rw [e] at hm
  exact (hbor _ _ hm).1

theorem UpperTheory.ConvolutionTheory.R2.M.siegJ :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M₀ : Meas F) (C : Set (IdeleGroup F)) (ρ : IdeleGroup F), IsCompact C → 1 < ab ρ → MeasurableSet {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} ∧ M.J0 M₀ (Set.indicator {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} 1) < ⊤ := by
  intro F _ _ _ M₀ C ρ hC hρ
  obtain ⟨-, hKc⟩ := M.kkCpt F
  obtain ⟨U, hU, hbor⟩ := M.borK F
  constructor
  · have e : {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} =
        ⋃ n : ℕ, Set.range (nU : A F → G1 F) * ((mD '' ((ρ ^ n * ·) '' C)) * KK F) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_mul, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨b, n, x, hx, k, hk, rfl⟩
        exact ⟨n, _, ⟨b, rfl⟩, _, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, k, hk, rfl⟩, (mul_assoc _ _ _).symm⟩
      · rintro ⟨n, _, ⟨b, rfl⟩, _, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, k, hk, rfl⟩, rfl⟩
        exact ⟨b, n, x, hx, k, hk, (mul_assoc _ _ _).symm⟩
    rw [e]
    refine MeasurableSet.iUnion fun n => ?_
    have hc : IsCompact ((mD '' ((ρ ^ n * ·) '' C)) * KK F) :=
      ((hC.image (continuous_const_mul _)).image M.continuous_mD).mul hKc
    exact (isClosed_range_nU.mul_right_of_isCompact hc).measurableSet
  · set S : Set (G1 F) := {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} with hS
    set W : Set (IdeleGroup F) := ⋃ n : ℕ, (ρ ^ n * ·) '' (C * U) with hW
    have hCU : IsCompact (C * U) := hC.mul hU
    have hWm : MeasurableSet W := MeasurableSet.iUnion fun n =>
      (hCU.image (continuous_const_mul _)).measurableSet
    haveI := M₀.prob
    have hae : ∀ᵐ p ∂M₀.ν, p.2 ∈ KK F := by
      have h0 : ∀ᵐ k ∂M₀.κ, k ∈ KK F := M₀.supp
      exact Measure.quasiMeasurePreserving_snd.ae h0
    have hle : M.J0 M₀ (S.indicator 1) ≤ ∫⁻ p, W.indicator M.wt p.1 ∂M₀.ν := by
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with p hp
      by_cases hmem : mD p.1 * p.2 ∈ S
      · obtain ⟨b, n, x, hx, k, hk, h⟩ := id hmem
        have hq := quot_mem hbor hp hk h
        have hpW : p.1 ∈ W := by
          refine Set.mem_iUnion.2 ⟨n, x * ((ρ ^ n * x)⁻¹ * p.1), ⟨x, hx, _, hq, rfl⟩, ?_⟩
          show ρ ^ n * (x * ((ρ ^ n * x)⁻¹ * p.1)) = p.1
          group
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpW]
        simp
      · rw [Set.indicator_of_notMem hmem]
        simp
    have heq : ∫⁻ p, W.indicator M.wt p.1 ∂M₀.ν = ∫⁻ a in W, M.wt a ∂(ideleMeasure F) := by
      rw [← lintegral_indicator hWm, Meas.ν,
        lintegral_prod (fun p : IdeleGroup F × G1 F => W.indicator M.wt p.1)
          ((M.measurable_wt.indicator hWm).comp measurable_fst).aemeasurable]
      simp
    exact hle.trans_lt (heq ▸ M.ideleSum F (C * U) ρ hCU hρ)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.iwa :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ g : G1 F, ∃ (b : A F) (a : (A F)ˣ), ∃ k ∈ KK F, g = nU b * mD a * k := by
  intro F _ _ _ g
  obtain ⟨b, hb, k, hk, e⟩ := Reduction.exists_adelicBorel_mul_maxCompact (K := F) (n := 2) (gl g)
  obtain ⟨x, a, k', hk', hg, -, -⟩ := UpperTheory.ConvolutionTheory.R2.M.fromGL F g b hb k hk e
  exact ⟨x, a, k', hk', hg⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.MeasMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem absUnf {G P B ι : Type} [MeasurableSpace G] [MeasurableSpace P] [MeasurableSpace B] [Countable ι]
    (m₀ : Measure G) (e : ι → G → G) (he : ∀ i, Measurable (e i)) (ρ : Measure P) [SFinite ρ]
    (β : Measure B) [SFinite β] (s : P × B → G) (hs : Measurable s) (u : G → ℂ) (hu : Measurable u)
    (hL : ∀ φ : ℂ → ℝ≥0∞, Measurable φ →
      ∫⁻ x, ∑' i, φ (u (e i x)) ∂m₀ = ∫⁻ q, φ (u (s q)) ∂(ρ.prod β))
    (hfin : ∫⁻ q, ‖u (s q)‖ₑ ∂(ρ.prod β) ≠ ⊤) :
    (∀ᵐ x ∂m₀, Summable fun i => ‖u (e i x)‖) ∧ Integrable (fun x => ∑' i, u (e i x)) m₀ ∧
      Integrable (fun p => ∫ b, u (s (p, b)) ∂β) ρ ∧
      ∫ x, ∑' i, u (e i x) ∂m₀ = ∫ p, ∫ b, u (s (p, b)) ∂β ∂ρ := by
  have hS := M.sumSide G ι m₀ e he
  have hv : Measurable fun q => u (s q) := hu.comp hs
  have hvi : Integrable (fun q => u (s q)) (ρ.prod β) :=
    ⟨hv.aestronglyMeasurable, lt_top_iff_ne_top.2 hfin⟩
  have hT := M.transfer (m := Measure.sum fun i => m₀.map (e i)) (n := ρ.prod β) hu hv
    (fun φ hφ => (hS.1 _ (hφ.comp hu)).trans (hL φ hφ))
  obtain ⟨h1, h2, h3⟩ := hS.2 u hu (hT.1.2 hvi)
  refine ⟨h1, h2, hvi.integral_prod_left, h3.trans (hT.2.trans ?_)⟩
  exact integral_prod _ hvi

private theorem meas_mul (F : Type) [Field F] [NumberField F] : Measurable fun q : G1 F × G1 F => q.1 * q.2 :=
  (continuous_fst.mul continuous_snd).measurable

private theorem meas_nU (F : Type) [Field F] [NumberField F] : Measurable (nU : A F → G1 F) :=
  M.continuous_nU.measurable

private theorem meas_mD (F : Type) [Field F] [NumberField F] : Measurable (mD : IdeleGroup F → G1 F) :=
  M.continuous_mD.measurable

private theorem measMul {G X : Type} [Mul G] [MeasurableSpace G] [MeasurableSpace X] {a b : X → G}
    (hm : Measurable fun q : G × G => q.1 * q.2) (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x => a x * b x := hm.comp (ha.prodMk hb)

private theorem meas_g (F : Type) [Field F] [NumberField F] :
    Measurable fun q : G1 F × A F => nU q.2 * q.1 :=
  measMul (a := fun q : G1 F × A F => nU q.2) (b := fun q => q.1) (meas_mul F)
    ((meas_nU F).comp measurable_snd) measurable_fst

private theorem meas_m (F : Type) [Field F] [NumberField F] :
    Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
  measMul (a := fun p : IdeleGroup F × G1 F => mD p.1) (b := fun p => p.2) (meas_mul F)
    ((meas_mD F).comp measurable_fst) measurable_snd

private theorem meas_q (F : Type) [Field F] [NumberField F] :
    Measurable fun q : (IdeleGroup F × G1 F) × A F => nU q.2 * (mD q.1.1 * q.1.2) :=
  measMul (a := fun q : (IdeleGroup F × G1 F) × A F => nU q.2)
    (b := fun q => mD q.1.1 * q.1.2) (meas_mul F)
    ((meas_nU F).comp measurable_snd) ((meas_m F).comp measurable_fst)

private theorem meas_l (F : Type) [Field F] [NumberField F] (x : G1 F) :
    Measurable fun g : G1 F => x * g :=
  measMul (a := fun _ : G1 F => x) (b := fun g => g) (meas_mul F) measurable_const measurable_id

private theorem key (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (ρ : Measure (IdeleGroup F × G1 F)) [SFinite ρ]
    (hρ : ∀ u : G1 F → ℝ≥0∞, Measurable u → ∫⁻ p, u (mD p.1 * p.2) ∂ρ = M.J0 M₀ u)
    (w : G1 F → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ q, w (nU q.2 * (mD q.1.1 * q.1.2)) ∂(ρ.prod ((adeleMeasure F).restrict (fundamentalSet F))) =
      M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, w (nU b * g) ∂(adeleMeasure F) := by
  refine (lintegral_prod (fun q : (IdeleGroup F × G1 F) × A F => w (nU q.2 * (mD q.1.1 * q.1.2)))
    (hw.comp (meas_q F)).aemeasurable).trans ?_
  exact hρ _ (Measurable.lintegral_prod_right' (f := fun q : G1 F × A F => w (nU q.2 * q.1)) (hw.comp (meas_g F)))

theorem UpperTheory.ConvolutionTheory.R2.M.unfC :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (σ) (u : G1 F → ℂ), M.RowSec (F := F) σ → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → (M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, ‖u (nU b * g)‖ₑ ∂(adeleMeasure F)) ≠ ⊤ → (∀ᵐ g ∂(M₀.μ.restrict M₀.D), Summable fun r => ‖u (ratS F (σ r) * g)‖) ∧ IntegrableOn (fun g => ∑' r, u (ratS F (σ r) * g)) M₀.D M₀.μ ∧ Integrable (iw fun g => ∫ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F)) M₀.ν ∧ ∫ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ = M₀.I0 fun g => ∫ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) := by
  intro F _ _ M₀ σ u hσ hu hinv hfin
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨ρ, hρs, hρ1, hρ2⟩ := M.iwDens F M₀
  have hk := key F M₀ ρ hρ1
  obtain ⟨h1, h2, h3, h4⟩ := absUnf (M₀.μ.restrict M₀.D) (fun (r : {r : Fin 2 → F // r ≠ 0}) g => ratS F (σ r) * g)
    (fun r => meas_l F _) ρ ((adeleMeasure F).restrict (fundamentalSet F))
    (fun q => nU q.2 * (mD q.1.1 * q.1.2)) (meas_q F) u hu
    (fun φ hφ => (M.unfL F M₀ σ (fun g => φ (u g)) hσ (hφ.comp hu)
        (fun ξ g => by simp only [hinv])).trans (hk _ (hφ.comp hu)).symm)
    (by rw [hk (fun g => ‖u g‖ₑ) hu.enorm]; exact hfin)
  refine ⟨h1, h2, ((hρ2 _).1).1 h3, h4.trans ((hρ2 _).2)⟩
end

