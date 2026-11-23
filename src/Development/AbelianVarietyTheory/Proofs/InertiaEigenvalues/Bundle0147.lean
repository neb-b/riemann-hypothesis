module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTruncatedFourierTendstoZeroEtale
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.PlancherelZero

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_char (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  refine (continuousAt_const (y := ψ x)).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
  have h1 : ψ (z - x) = 1 := hψ.1 _ (by simpa [dist_eq_norm] using hz)
  calc ψ x = ψ x * ψ (z - x) := by rw [h1, mul_one]
    _ = ψ z := by rw [← AddChar.map_add_eq_mul]; congr 1; abel

theorem kerK_eq (A : Et F E) (ψ : AddChar F ℂ) :
    A.kerK ψ = fun x y => ψ (Algebra.traceForm F A.K x y) := by
  funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]

theorem continuous_kerK (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (y : A.K) :
    Continuous fun x => A.kerK ψ x y := by
  have hl : Continuous ((Algebra.trace F A.K).comp (LinearMap.mulRight F y)) :=
    IsModuleTopology.continuous_of_linearMap _
  exact ((continuous_char ψ hψ).comp hl).congr (fun x => by simp [Et.kerK, Et.psiK])

theorem integrable_mul_kerK (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f : A.K → ℂ} (hf : IsTest f) (y : A.K) :
    Integrable (fun x => f x * A.kerK ψ x y) μ :=
  (hf.1.continuous.mul (continuous_kerK A ψ hψ y)).integrable_of_hasCompactSupport hf.2.mul_right

theorem fourB_sub (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f g : A.K → ℂ} (hf : IsTest f) (hg : IsTest g) (y : A.K) :
    fourB μ (A.kerK ψ) (f - g) y = fourB μ (A.kerK ψ) f y - fourB μ (A.kerK ψ) g y := by
  unfold fourB
  rw [← integral_sub (integrable_mul_kerK A ψ hψ μ hf y) (integrable_mul_kerK A ψ hψ μ hg y)]
  congr 1; funext x; simp [sub_mul]

theorem lintegral_sq_eq_ofReal {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {g : X → ℂ} (hg : IsTest g) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hc : Continuous fun x => ‖g x‖ ^ 2 := (hg.1.continuous.norm).pow 2
  have hs : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ g) := hg.2.comp_left (by simp)
  rw [ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hs)
    (ae_of_all _ fun x => by simp only [Pi.zero_apply]; positivity)]
  congr 1; funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable [Unram F E]

theorem isTest_fourB (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) : IsTest (fourB μK (A.kerK ψ) f) := by
  obtain ⟨-, -, hnd, -⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  rw [kerK_eq A ψ]
  exact (_root_.GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd).2 μK hsd.1 f hf

theorem plancherel (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) :
    ∫⁻ y, ‖fourB μK (A.kerK ψ) f y‖ₑ ^ 2 ∂μK = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μK := by
  haveI := hsd.1
  obtain ⟨-, -, hnd, -⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  have hB := kerK_eq A ψ
  have hP := (_root_.GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd μK
    hsd.1).2 (hB ▸ hsd) f hf
  rw [lintegral_sq_eq_ofReal μK (isTest_fourB A ψ hψ μK hsd hf), lintegral_sq_eq_ofReal μK hf, hB, hP]

end GlobalTheory.PlancherelZero

namespace GlobalTheory.PlancherelZero

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def box (A : Et F E) (c : F) : Set A.K := {z | c • z ∈ A.OK}

theorem isOpen_box (A : Et F E) (hO : IsOpen A.OK) (c : F) : IsOpen (box A c) :=
  hO.preimage (continuous_const_smul c)

theorem isClosed_box (A : Et F E) (hO : IsClosed A.OK) (c : F) : IsClosed (box A c) :=
  hO.preimage (continuous_const_smul c)

theorem isCompact_box (A : Et F E) (hO : IsCompact A.OK) {c : F} (hc : c ≠ 0) : IsCompact (box A c) :=
  (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero c hc)).2 hO

theorem isTest_indicator_box (A : Et F E) {u : A.K → ℂ} (hu : IsLocallyConstant u) (hOo : IsOpen A.OK)
    (hOc : IsClosed A.OK) (hOk : IsCompact A.OK) {c : F} (hc : c ≠ 0) : IsTest ((box A c).indicator u) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_box A hOk hc) (isClosed_box A hOc c)
    fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ box A c
  · filter_upwards [(isOpen_box A hOo c).mem_nhds hx, (IsLocallyConstant.iff_eventually_eq u).1 hu x] with y hy h
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx, h]
  · filter_upwards [(isClosed_box A hOc c).isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem fourB_indicator_box (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.K) (u : A.K → ℂ) (c : F)
    (hM : MeasurableSet (box A c)) (y : A.K) :
    fourB μ (A.kerK ψ) ((box A c).indicator u) y = ∫ z in box A c, u z * A.psiK ψ (-((-y) * z)) ∂μ := by
  unfold fourB
  have h : ∀ x, (box A c).indicator u x * A.kerK ψ x y = (box A c).indicator (fun x => u x * A.kerK ψ x y) x :=
    fun x => by by_cases hx : x ∈ box A c <;> simp [hx]
  simp_rw [h]
  rw [integral_indicator hM]
  congr 1; funext z
  rw [Et.kerK, neg_mul, neg_neg, mul_comm z y]

end GlobalTheory.PlancherelZero

namespace GlobalTheory.PlancherelZero

theorem eq_zero_of_tendsto_fourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ (u : A.K → ℂ), IsLocallyConstant u → ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK < ⊤ → (∀ a : A.K, IsUnit a → Tendsto (fun c : F => ∫ z in {z : A.K | c • z ∈ A.OK}, u z * A.psiK ψ (-(a * z)) ∂μK) (𝓝[≠] 0) (𝓝 0)) → u = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd u hu hT hlim
  haveI := hsd.1
  obtain ⟨-, -, -, -, -, -, -, -, hnull, hOo, hOk, R, hR⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  have hOc : IsClosed A.OK := by
    have hRo : IsOpen ((R.toAddSubgroup : AddSubgroup A.K) : Set A.K) := by rw [← hR] at hOo; exact hOo
    rw [← hR]; exact R.toAddSubgroup.isClosed_of_isOpen hRo
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one F
  have hpow : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1
  have hne : ∀ n : ℕ, ϖ ^ n ≠ 0 := fun n => pow_ne_zero n (norm_pos_iff.1 hϖ0)
  have hpow' : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hpow, Eventually.of_forall hne⟩
  set M : ℕ → Set A.K := fun n => box A (ϖ ^ n) with hMdef
  have hMm : ∀ n, MeasurableSet (M n) := fun n => (isOpen_box A hOo _).measurableSet
  set g : ℕ → A.K → ℂ := fun n => (M n).indicator u with hgdef
  have hg : ∀ n, IsTest (g n) := fun n => isTest_indicator_box A hu hOo hOc hOk (hne n)
  have hTc : ∀ n, Continuous (fourB μK (A.kerK ψ) (g n)) := fun n =>
    (isTest_fourB A ψ hψ μK hsd (hg n)).1.continuous
  have huc : Continuous u := hu.continuous
  have hum : Measurable fun z => ‖u z‖ₑ ^ 2 := (huc.measurable.enorm).pow_const 2
  set b : ℕ → ENNReal := fun n => ∫⁻ z, (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) z ∂μK with hbdef
  have hev : ∀ z : A.K, ∀ᶠ n in atTop, z ∈ M n := by
    intro z
    have ht : Tendsto (fun n : ℕ => ϖ ^ n • z) atTop (𝓝 0) := by
      simpa using hpow.smul_const z
    exact ht (hOo.mem_nhds h0)
  have hb : Tendsto b atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μK)
      (F := fun n z => (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) z) (f := fun _ => 0) (fun z => ‖u z‖ₑ ^ 2)
      (fun n => hum.indicator (hMm n).compl) (fun n => ae_of_all _ fun z => Set.indicator_le_self _ _ z) hT.ne
      (ae_of_all _ fun z => tendsto_const_nhds.congr'
        ((hev z).mono fun n hn => (Set.indicator_of_notMem (fun h : z ∈ (M n)ᶜ => h hn) _).symm))
    simpa using this
  have hlimF : ∀ y : A.K, IsUnit y → Tendsto (fun n => fourB μK (A.kerK ψ) (g n) y) atTop (𝓝 0) := by
    intro y hy
    exact ((hlim (-y) hy.neg).comp hpow').congr fun n => (fourB_indicator_box A ψ μK u _ (hMm n) y).symm
  have hae : ∀ᵐ y ∂μK, IsUnit y := ae_iff.2 (hnull μK hsd.1)
  have key : ∀ N, ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK ≤ b N := by
    intro N
    rw [← plancherel A ψ hψ μK hsd (hg N)]
    have hFd : ∀ n, ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2 ∂μK
        = ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK := by
      intro n
      have := plancherel A ψ hψ μK hsd (f := g N - g n) ⟨(hg N).1.sub (hg n).1, (hg N).2.sub (hg n).2⟩
      simp only [Pi.sub_apply] at this
      rw [← this]
      congr 1; funext y
      rw [fourB_sub A ψ hψ μK (hg N) (hg n) y]
    have hpt : ∀ n x, ‖g N x - g n x‖ₑ ^ 2 ≤
        (M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x + (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x := by
      intro n x
      by_cases h1 : x ∈ M N <;> by_cases h2 : x ∈ M n <;> simp [g, h1, h2]
    have hle : ∀ n, ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK ≤ b N + b n := by
      intro n
      calc _ ≤ ∫⁻ x, ((M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x + (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x) ∂μK :=
            lintegral_mono (hpt n)
        _ = b N + b n := lintegral_add_left (hum.indicator (hMm N).compl) _
    have hliminf : ∀ᵐ y ∂μK,
        liminf (fun n => ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2) atTop
          = ‖fourB μK (A.kerK ψ) (g N) y‖ₑ ^ 2 := by
      filter_upwards [hae] with y hy
      have ht := ((ENNReal.continuous_pow 2).tendsto _).comp
        ((continuous_enorm.tendsto _).comp ((tendsto_const_nhds (x := fourB μK (A.kerK ψ) (g N) y)).sub (hlimF y hy)))
      simpa [Function.comp_def] using ht.liminf_eq
    calc ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y‖ₑ ^ 2 ∂μK
        = ∫⁻ y, liminf (fun n => ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2) atTop ∂μK :=
          lintegral_congr_ae (hliminf.mono fun y h => h.symm)
      _ ≤ liminf (fun n => ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2 ∂μK) atTop :=
          lintegral_liminf_le' fun n => ((((hTc N).sub (hTc n)).measurable.enorm).pow_const 2).aemeasurable
      _ = liminf (fun n => ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK) atTop := by simp_rw [hFd]
      _ ≤ liminf (fun n => b N + b n) atTop := liminf_le_liminf (Eventually.of_forall hle)
      _ = b N := by
          have : Tendsto (fun n => b N + b n) atTop (𝓝 (b N + 0)) := tendsto_const_nhds.add hb
          simpa using this.liminf_eq
  have hsplit : ∀ N, ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK = ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK + b N := by
    intro N
    calc ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK
        = ∫⁻ x, (‖g N x‖ₑ ^ 2 + (M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x) ∂μK := by
          congr 1; funext x
          by_cases h : x ∈ M N <;> simp [g, h]
      _ = ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK + b N := lintegral_add_right _ (hum.indicator (hMm N).compl)
  have hT0 : ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK = 0 := by
    refine le_antisymm ?_ (by simp)
    have h2 : Tendsto (fun N => b N + b N) atTop (𝓝 0) := by simpa using hb.add hb
    exact ge_of_tendsto' h2 fun N => (hsplit N).trans_le (add_le_add (key N) le_rfl)
  have hae0 : u =ᵐ[μK] 0 := by
    filter_upwards [(lintegral_eq_zero_iff hum).1 hT0] with z hz
    simpa using hz
  exact (Continuous.ae_eq_iff_eq μK huc continuous_const).1 hae0

end GlobalTheory.PlancherelZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisTraceInvolutionDetUnitUnramified
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
      (letI : Algebra K.E K'.E := φ.toAlgebra
       ∃ w : Module.Basis (Fin d) K.E K'.E,
         (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧
           val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0) := by
  intro K K' d φ h hd
  let : Algebra K.E K'.E := φ.toAlgebra
  have hbasis : ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E,
      (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔
        ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
    obtain ⟨w, key⟩ := IntBasis.exists_key h
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hmax (a : Fin d → K.E) : ∃ m, ∀ k, IntBasis.adicVal K (a k) ≤ IntBasis.adicVal K (a m) :=
      Finite.exists_max (fun k => IntBasis.adicVal K (a k))
    have hli : LinearIndependent K.E w := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      obtain ⟨m, hm⟩ := hmax g
      have hk := key g m hm
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hg
      rw [hg, map_zero] at hk
      have hgm : g m = 0 := (Valuation.zero_iff _).1 hk.symm
      intro k
      have hkm := hm k
      rw [hgm, map_zero] at hkm
      exact (Valuation.zero_iff _).1 (le_antisymm hkm zero_le)
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by
      rw [Fintype.card_fin]
      exact h.2.2.2.2.symm)
    refine ⟨B, fun z => ?_⟩
    have hz : ∑ k, φ (B.repr z k) * w k = z := by
      conv_rhs => rw [← B.sum_repr z]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coe_basisOfLinearIndependentOfCardEqFinrank, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    obtain ⟨m, hm⟩ := hmax (B.repr z)
    have hv := key _ m hm
    rw [hz] at hv
    rw [← IntBasis.adicVal_le_one_iff K' z]
    constructor
    · intro hzO k
      rw [← IntBasis.adicVal_le_one_iff]
      exact (hm k).trans (hv ▸ hzO)
    · intro hall
      rw [hv]
      exact (IntBasis.adicVal_le_one_iff K _).2 (hall m)
  obtain ⟨w, hw⟩ := hbasis
  refine ⟨w, ?_⟩
  obtain ⟨π, π', hππ, hm, hm'⟩ := GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt K K' d φ h
  have hw1 : ∀ k, ∃ y : K'.O, algebraMap K'.O K'.E y = w k := by
    intro k
    apply (hw _).2
    intro m
    by_cases hkm : k = m
    · subst m
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hkm]⟩
  have hdiscr : ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u =
      (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det := by
    have hj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
    have hi : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E

    have hlift : ∀ a : K.O, φ (algebraMap K.O K.E a) ∈ (algebraMap K'.O K'.E).range := by
      intro a
      apply (hw _).2
      intro k
      obtain ⟨c, hc⟩ := (hw 1).1 ⟨1, map_one _⟩ k
      refine ⟨a * c, ?_⟩
      have h1 : φ (algebraMap K.O K.E a) = (algebraMap K.O K.E a) • (1 : K'.E) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hc]
    let e : K'.O ≃+* (algebraMap K'.O K'.E).range :=
      RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
        ⟨fun x y h => hj (congrArg Subtype.val h), (algebraMap K'.O K'.E).rangeRestrict_surjective⟩
    let ι : K.O →+* K'.O :=
      e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift)
    have hι : ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
      intro a
      exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift a))
    let : Algebra K.O K'.O := ι.toAlgebra
    have hsm : ∀ (a : K.O) (y : K'.O),
        algebraMap K'.O K'.E (a • y) = algebraMap K.O K.E a • algebraMap K'.O K'.E y := by
      intro a y
      rw [Algebra.smul_def, map_mul, Algebra.smul_def]
      exact congrArg (· * _) (hι a)
    have hsum : ∀ (g : Fin d → K.O) (v : Fin d → K'.O),
        algebraMap K'.O K'.E (∑ k, g k • v k) = ∑ k, algebraMap K.O K.E (g k) • algebraMap K'.O K'.E (v k) := by
      intro g v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => hsm _ _

    choose bv hbv using hw1
    have hcoord : ∀ (y : K'.O) (k : Fin d), ∃ a : K.O, algebraMap K.O K.E a = w.repr (algebraMap K'.O K'.E y) k :=
      fun y => (hw _).1 ⟨y, rfl⟩
    choose c hc using hcoord
    have hli : LinearIndependent K.O bv := by
      rw [Fintype.linearIndependent_iff]
      intro g hg k
      have h1 := congrArg (algebraMap K'.O K'.E) hg
      rw [hsum, map_zero] at h1
      simp only [hbv] at h1
      have h2 := (Fintype.linearIndependent_iff.1 w.linearIndependent) _ h1 k
      exact hi (by rw [h2, map_zero])
    have hsp : ⊤ ≤ Submodule.span K.O (Set.range bv) := by
      intro y _
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨c y, hj ?_⟩
      rw [hsum]
      simp only [hbv, hc]
      exact w.sum_repr _
    let b : Module.Basis (Fin d) K.O K'.O := Module.Basis.mk hli hsp
    have hb : ∀ k, algebraMap K'.O K'.E (b k) = w k := fun k => by
      rw [Module.Basis.mk_apply]; exact hbv k
    have hrep : ∀ y k, algebraMap K.O K.E (b.repr y k) = w.repr (algebraMap K'.O K'.E y) k := by
      intro y k
      conv_rhs => rw [← b.sum_repr y, hsum]
      simp only [hb]
      rw [w.repr_sum_self]

    have hTr : ∀ y, algebraMap K.O K.E (Algebra.trace K.O K'.O y) =
        Algebra.trace K.E K'.E (algebraMap K'.O K'.E y) := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace w, Matrix.trace, Matrix.trace,
        map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
        Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hrep, map_mul, hb]

    have hιπ : ι π = π' := hj (by rw [hι, hππ])
    have hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
      rw [hm, Ideal.map_span, Set.image_singleton]
      have h1 : algebraMap K.O K'.O π = π' := hιπ
      rw [h1, ← hm']
      exact IsLocalRing.maximalIdeal.isMaximal _
    refine ⟨Algebra.discr K.O b, ResDisc.isUnit_discr_of_isMaximal_map b hmax, ?_⟩
    rw [Algebra.discr_def, RingHom.map_det]
    congr 1
    ext k m
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Matrix.of_apply, hTr, map_mul, hb]
  obtain ⟨u, hu, hue⟩ := hdiscr
  have hφ := h.2.1
  have hunit : ∃ u : K.O, IsUnit u ∧
      algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by
    set C : Matrix (Fin d) (Fin d) K.E := Matrix.of fun m l => w.repr (K'.c (w l)) m with hC
    have hsm : ∀ (e : K.E) (x : K'.E), e • x = φ e * x := fun e x => rfl
    have hint : ∀ m l, ∃ a : K.O, algebraMap K.O K.E a = C m l := by
      intro m l
      obtain ⟨y, hy⟩ := hw1 l
      obtain ⟨y', hy'⟩ := K'.c_int y
      have h2 : ∃ y : K'.O, algebraMap K'.O K'.E y = K'.c (w l) := ⟨y', by rw [← hy', hy]⟩
      exact (hw _).1 h2 m
    choose A hA using hint
    have hrep : ∀ (x : K'.E) (n : Fin d), w.repr (K'.c x) n = ∑ m, K.c (w.repr x m) * C n m := by
      intro x n
      have hx : K'.c x = ∑ m, K.c (w.repr x m) • K'.c (w m) := by
        conv_lhs => rw [← w.sum_repr x]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hsm, hsm, map_mul, ← hφ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    have hCC : C * (K.c : K.E →+* K.E).mapMatrix C = 1 := by
      ext n l
      have h := hrep (K'.c (w l)) n
      rw [K'.c_c, w.repr_self, Finsupp.single_apply] at h
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe]
      rw [eq_comm]
      convert h using 1
      · exact if_congr eq_comm rfl rfl
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_comm]
      rfl
    have hdet : C.det * K.c C.det = 1 := by
      have h := congrArg Matrix.det hCC
      rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det] at h
      exact h
    have hdetA : algebraMap K.O K.E (Matrix.of A).det = C.det := by
      rw [RingHom.map_det]
      congr 1
      ext m l
      simp [hA]
    refine ⟨(Matrix.of A).det, ?_, hdetA⟩
    obtain ⟨β, hβ⟩ := K.c_int (Matrix.of A).det
    apply IsUnit.of_mul_eq_one β
    apply IsFractionRing.injective K.O K.E
    rw [map_mul, ← hβ, hdetA, hdet, map_one]
  obtain ⟨v, hv, hve⟩ := hunit
  have key : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))) =
      (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)) * (Matrix.of fun m l => w.repr (K'.c (w l)) m) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply]
    conv_lhs => rw [← w.sum_repr (K'.c (w l))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hdet : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = algebraMap K.O K.E (u * v) := by
    rw [key, Matrix.det_mul, ← hue, ← hve, map_mul]
  rw [hdet]
  refine ⟨?_, GlobalTheory.UnitLemma.Orbit.val_unit _ (hu.mul hv)⟩
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
  exact (hu.mul hv).ne_zero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralPsiKOverScaledIntegersEqVolumeIndicator
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem charIntegral_inv_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ c : F, c ≠ 0 → ∀ b : A.K, ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * b) ∂μK = Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} (fun _ => ((μK {z : A.K | c • z ∈ A.OK}).toReal : ℂ)) b := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ c hc b
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hO, hC, R, hR⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribSMul.toAddMonoidHom A.K c)
  have hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z
    simp [M, ← hR]
  have hMO : IsOpen (M : Set A.K) := by
    rw [hM]
    exact hO.preimage (continuous_const_smul c)
  have hMC : IsCompact (M : Set A.K) := by
    rw [hM]
    exact (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero c hc)).mpr hC
  have key := ((_root_.GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hμ).1
    M hMO hMC).2 b
  have hpsi : ∀ z y : A.K, A.psiK ψ (z * y) = ψ (Algebra.traceForm F A.K z y) := by
    intro z y
    simp [Et.psiK, Algebra.traceForm_apply]
  simp_rw [hpsi]
  rw [← hM]
  convert key using 2
  ext y
  simp only [Set.mem_setOf_eq, Algebra.traceForm_apply]
  constructor
  · intro h x hx
    exact h x (by simpa [hM] using (show x ∈ (M : Set A.K) from hx))
  · intro h z hz
    exact h z (show z ∈ (M : Set A.K) by rw [hM]; exact hz)

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), 1 ≤ j → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ (l ^ j) → ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  first | exact @GlobalTheory.Cyc.norm_primitiveRoot_sub_one | exact GlobalTheory.Cyc.norm_primitiveRoot_sub_one | (intros; apply GlobalTheory.Cyc.norm_primitiveRoot_sub_one <;> assumption)
end

