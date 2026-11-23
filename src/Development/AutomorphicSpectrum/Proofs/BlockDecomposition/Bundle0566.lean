module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuous
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral

open scoped Pointwise

theorem sq_lintegral_mul_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {a b : X → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ w, a w * b w ∂ν) ^ 2 ≤ (∫⁻ w, a w ∂ν) * ∫⁻ w, a w * b w ^ 2 ∂ν :=
  _root_.UpperTheory.Reformulated.B.P6.r96a.GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.sq_lintegral_mul_le ν ha hb

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem eventually_lintegral_translate_le [LocallyCompactSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {α : G → ℂ} (hα : Continuous α) (hs : HasCompactSupport α)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (1 : G), ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ε := by
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  have hC : IsCompact (V * tsupport α) := hVc.mul hs
  set C : Set G := V * tsupport α with hCdef
  have hfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  have hc : 0 < ε / (μ C + 1) :=
    ENNReal.div_pos hε.ne' (by simp [hfin])
  set c : ℝ≥0∞ := ε / (μ C + 1) with hcdef
  have hunif : ∀ᶠ y in 𝓝 (1 : G), ∀ w ∈ C, ‖α (y⁻¹ * w) - α w‖ₑ < c := by
    refine hC.eventually_forall_of_forall_eventually fun w _ => ?_
    have hcont : Continuous fun z : G × G => ‖α (z.1⁻¹ * z.2) - α z.2‖ₑ := by
      fun_prop
    have h0 : ‖α ((1 : G)⁻¹ * w) - α w‖ₑ < c := by simpa using hc
    exact hcont.continuousAt.eventually_lt continuousAt_const h0
  filter_upwards [hunif, hV] with y hy hyV
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hle : ∀ w, ‖α (y⁻¹ * w) - α w‖ₑ ≤ C.indicator (fun _ => c) w := by
    intro w
    by_cases hw : w ∈ C
    · rw [Set.indicator_of_mem hw]
      exact (hy w hw).le
    · rw [Set.indicator_of_notMem hw]
      have h1 : α w = 0 := by
        by_contra h
        exact hw (Set.mem_mul.2 ⟨1, mem_of_mem_nhds hV, w, subset_tsupport _ h, one_mul w⟩)
      have h2 : α (y⁻¹ * w) = 0 := by
        by_contra h
        exact hw (Set.mem_mul.2 ⟨y, hyV, y⁻¹ * w, subset_tsupport _ h, by group⟩)
      simp [h1, h2]
  calc ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ∫⁻ w, C.indicator (fun _ => c) w ∂μ := lintegral_mono hle
    _ = c * μ C := lintegral_indicator_const hCm c
    _ ≤ c * (μ C + 1) := by gcongr; exact le_self_add
    _ = ε := ENNReal.div_mul_cancel (by simp) (by simp [hfin])

variable [LocallyCompactSpace G] [SecondCountableTopology G]

theorem enorm_translate_sub_le (μ : Measure G) [μ.IsHaarMeasure] {α ψ : G → ℂ} (hα : Continuous α)
    (hs : HasCompactSupport α) (hψ : Continuous ψ) {s : ℂ}
    (hrep : ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) (x y : G) :
    ‖s‖ₑ * ‖ψ (x * y) - ψ x‖ₑ ≤ ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ * ‖ψ (x * w)‖ₑ ∂μ := by
  have h1 : s * ψ (x * y) = ∫ w, α (y⁻¹ * w) * ψ (x * w) ∂μ := by
    rw [← hrep (x * y), ← integral_mul_left_eq_self (fun w => α (y⁻¹ * w) * ψ (x * w)) y]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp [mul_assoc]
  have hcs : HasCompactSupport fun w => α (y⁻¹ * w) := hs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)
  have hi1 : Integrable (fun w => α (y⁻¹ * w) * ψ (x * w)) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hcs.mul_right
  have hi2 : Integrable (fun w => α w * ψ (x * w)) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hs.mul_right
  have h3 : s * (ψ (x * y) - ψ x) = ∫ w, (α (y⁻¹ * w) - α w) * ψ (x * w) ∂μ := by
    rw [mul_sub, h1, ← hrep x, ← integral_sub hi1 hi2]
    exact integral_congr_ae (ae_of_all _ fun w => by ring)
  rw [← enorm_mul, h3]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  exact lintegral_congr fun w => enorm_mul _ _

theorem lintegral_right_translate (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {ψ : G → ℂ}
    (hl : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (w : G) :
    ∫⁻ x in F, ‖ψ (x * w)‖ₑ ^ 2 ∂μ = ∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ := by
  have hF' : IsFundamentalDomain Γ (MulOpposite.op w • F) μ := hF.smul_of_comm (MulOpposite.op w)
  have himg : (fun x => x * w) '' F = MulOpposite.op w • F := rfl
  have h1 := (measurePreserving_mul_right μ w).setLIntegral_comp_emb
    (MeasurableEquiv.mulRight w).measurableEmbedding (fun x => ‖ψ x‖ₑ ^ 2) F
  rw [h1, himg]
  refine hF'.setLIntegral_eq hF _ fun γ x => ?_
  simp only [Subgroup.smul_def, smul_eq_mul]
  rw [hl _ γ.2]

theorem sq_mean_translate_le (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {α ψ : G → ℂ}
    (hα : Continuous α) (hs : HasCompactSupport α) (hψ : Continuous ψ)
    (hl : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) {s : ℂ}
    (hrep : ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x)
    (hn : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (y : G)
    (hA : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≠ ∞) :
    ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ (∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ) ^ 2 := by
  set a : G → ℝ≥0∞ := fun w => ‖α (y⁻¹ * w) - α w‖ₑ with ha_def
  have hac : Continuous a := by fun_prop
  have ha : Measurable a := hac.measurable
  have hjm : Measurable fun z : G × G => a z.2 * ‖ψ (z.1 * z.2)‖ₑ ^ 2 := by
    have hc : Continuous fun z : G × G => ‖ψ (z.1 * z.2)‖ₑ := by fun_prop
    exact (ha.comp measurable_snd).mul (hc.measurable.pow_const 2)
  calc ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ
      = ∫⁻ x in F, (‖s‖ₑ * ‖ψ (x * y) - ψ x‖ₑ) ^ 2 ∂μ := by
        rw [← lintegral_const_mul' _ _ (by simp)]
        exact lintegral_congr fun x => (mul_pow _ _ _).symm
    _ ≤ ∫⁻ x in F, (∫⁻ w, a w * ‖ψ (x * w)‖ₑ ∂μ) ^ 2 ∂μ :=
        lintegral_mono fun x => by
          gcongr
          exact enorm_translate_sub_le μ hα hs hψ hrep x y
    _ ≤ ∫⁻ x in F, (∫⁻ w, a w ∂μ) * ∫⁻ w, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ :=
        lintegral_mono fun x => sq_lintegral_mul_le μ ha (by
          have : Continuous fun w => ‖ψ (x * w)‖ₑ := by fun_prop
          exact this.measurable)
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ x in F, ∫⁻ w, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ :=
        lintegral_const_mul' _ _ hA
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ w, ∫⁻ x in F, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hjm.aemeasurable]
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ w, a w ∂μ := by
        congr 1
        refine lintegral_congr fun w => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_right_translate μ Γ hF hl w, hn, mul_one]
    _ = (∫⁻ w, a w ∂μ) ^ 2 := (sq _).symm

theorem exists_nhds_sq_mean_le (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {α : G → ℂ} {δ : ℝ} {F : Set G}
    (hα : Continuous α) (hs : HasCompactSupport α) (hδ : 0 < δ) (hF : IsFundamentalDomain Γ F μ)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : G → ℂ, Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
      (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  set d : ℝ≥0∞ := ENNReal.ofReal δ with hd
  have hd0 : d ≠ 0 := by simpa [hd] using hδ
  have hdt : d ≠ ∞ := ENNReal.ofReal_ne_top
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0
  have hd2t : d ^ 2 ≠ ∞ := ENNReal.pow_ne_top hdt
  set ε : ℝ≥0∞ := min 1 (η * d ^ 2) with hε
  have hε0 : 0 < ε := lt_min one_pos (ENNReal.mul_pos hη.ne' hd2)
  have hε1 : ε ≤ 1 := min_le_left _ _
  refine ⟨_, eventually_lintegral_translate_le μ hα hs hε0, ?_⟩
  rintro ψ hψ hl ⟨s, hsδ, hrep⟩ hn y hy
  have hy' : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ε := hy
  have hA : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≠ ∞ := (hy'.trans hε1).trans_lt ENNReal.one_lt_top |>.ne
  have hb := sq_mean_translate_le μ Γ hF hα hs hψ hl hrep hn y hA
  have hds : d ≤ ‖s‖ₑ := by
    rw [hd, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal hsδ
  have hεε : ε ^ 2 ≤ η * d ^ 2 := by
    calc ε ^ 2 = ε * ε := sq ε
      _ ≤ 1 * ε := by gcongr
      _ = ε := one_mul ε
      _ ≤ η * d ^ 2 := min_le_right _ _
  have hfin : d ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ d ^ 2 * η := by
    calc d ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ
        ≤ ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ := by gcongr
      _ ≤ (∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ) ^ 2 := hb
      _ ≤ ε ^ 2 := by gcongr
      _ ≤ η * d ^ 2 := hεε
      _ = d ^ 2 * η := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_right hd2 hd2t).1 hfin

end GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral

theorem GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∀ η : ℝ≥0∞, 0 < η → ∃ U ∈ 𝓝 (1 : GA E N), ∀ ψ : GA E N → ℂ, Continuous ψ →
  (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) → (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
  (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  intro E _ _ _ N _ _ μ _ α δ F hα hs hδ hF η hη
  haveI : μ.IsMulRightInvariant := _root_.GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA E N μ
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  set_option synthInstance.maxHeartbeats 200000 in
    exact GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.exists_nhds_sq_mean_le μ (latticeGL E N) hα hs hδ hF hη
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBound
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.LeafB

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_infOf (hD : DiscInf) (hT : TopInf) (τ : E →+* ℂ) :
    ∀ {N : ℕ} {t : Tr E N}, t.Good → ∃ m', t.InfOf τ m' := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨-, hV, -⟩
    · exact ⟨_, 0, hT E τ, rfl⟩
    · obtain ⟨m₀, hm₀⟩ := hD E _ V hV τ
      exact ⟨_, m₀, hm₀, rfl⟩
  | node t₁ t₂ i₁ i₂ =>
    intro h
    obtain ⟨m₁, h₁⟩ := i₁ h.1
    obtain ⟨m₂, h₂⟩ := i₂ h.2
    exact ⟨_, m₁, m₂, h₁, h₂, rfl⟩

theorem leaf_entries (hD : DiscInf) (hT : TopInf) (B : ℝ) :
    ∀ {N : ℕ} {t : Tr E N}, t.Good → (∀ τ m', t.InfOf τ m' → ∀ x ∈ m', ‖x‖ ≤ B) →
      LeafZ (fun M V z => 0 < M → GlobalTheory.UnitaryBC.IsDiscrete V ∧
        ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) t := by
  intro N t
  induction t with
  | leaf V z =>
    intro h hb hM
    rcases h with ⟨h0, -, -⟩ | ⟨-, hV, -⟩
    · omega
    · refine ⟨hV, fun τ m₀ hm₀ x hx => ?_⟩
      exact hb τ (m₀.map (· + z)) ⟨m₀, hm₀, rfl⟩ _ (Multiset.mem_map_of_mem _ hx)
  | node t₁ t₂ i₁ i₂ =>
    intro h hb
    refine ⟨i₁ h.1 fun τ m₁ h₁ x hx => ?_, i₂ h.2 fun τ m₂ h₂ x hx => ?_⟩
    · obtain ⟨m₂, h₂⟩ := exists_infOf hD hT τ h.2
      exact hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inl hx))
    · obtain ⟨m₁, h₁⟩ := exists_infOf hD hT τ h.1
      exact hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inr hx))

theorem norm_sum_le (s : Multiset ℂ) (B : ℝ) (h : ∀ x ∈ s, ‖x‖ ≤ B) :
    ‖s.sum‖ ≤ (Multiset.card s : ℝ) * B := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.card_cons]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have h3 := norm_add_le a s.sum
    push_cast
    linarith

theorem sum_map_add_const (s : Multiset ℂ) (z : ℂ) :
    (s.map (· + z)).sum = s.sum + (Multiset.card s : ℂ) * z := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    ring

theorem leaf_bound (hD : DiscInf) {M : ℕ} (hM : 0 < M) {V : Submodule ℂ (Sm E M)} (hV : GlobalTheory.UnitaryBC.IsDiscrete V) {z : ℂ} {B : ℝ}
    (hb : ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) :
    InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B := by
  choose m₀ hm₀ using hD E M V hV
  have htr : ∑ τ, (m₀ τ).sum = 0 := GlobalTheory.CompanionTheory.TotalTrace.total_trace_eq_zero hV hm₀
  have hcard : ∀ τ, Multiset.card (m₀ τ) = M := fun τ => (hm₀ τ).1
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hd : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos_iff.2 ⟨τ₀⟩
  have hB : 0 ≤ B := by
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hcard τ₀]; exact hM)
    exact (norm_nonneg _).trans (hb τ₀ _ (hm₀ τ₀) x hx)
  have hsum : ∑ τ, ((m₀ τ).map (· + z)).sum = (Fintype.card (E →+* ℂ) : ℂ) * ((M : ℂ) * z) := by
    simp only [sum_map_add_const, hcard, Finset.sum_add_distrib, htr, zero_add, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hle : ‖∑ τ, ((m₀ τ).map (· + z)).sum‖ ≤ (Fintype.card (E →+* ℂ) : ℝ) * ((M : ℝ) * B) := by
    refine (norm_sum_le_of_le Finset.univ (n := fun _ => (M : ℝ) * B) fun τ _ => ?_).trans_eq (by simp)
    have := norm_sum_le ((m₀ τ).map (· + z)) B (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
      exact hb τ _ (hm₀ τ) x hx)
    simpa [hcard] using this
  have hz : ‖z‖ ≤ B := by
    rw [hsum, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast] at hle
    have hdM : (0 : ℝ) < (Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ) := by positivity
    have : ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * ‖z‖ ≤ ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * B := by
      nlinarith [hle]
    exact le_of_mul_le_mul_left this hdM
  refine ⟨fun τ => ⟨m₀ τ, hm₀ τ, fun x hx => ?_⟩, by linarith⟩
  have h1 := hb τ _ (hm₀ τ) x hx
  have h2 : ‖x‖ ≤ ‖x + z‖ + ‖z‖ := by simpa using norm_sub_le (x + z) z
  linarith

theorem leaves_of_entries (hD : DiscInf) (B : ℝ) : ∀ {N : ℕ} {t : Tr E N},
    LeafZ (fun M V z => 0 < M → GlobalTheory.UnitaryBC.IsDiscrete V ∧
      ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) t →
    LeafZ (fun M V z => 0 < M → InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B) t := by
  intro N t
  induction t with
  | leaf V z =>
    intro key hM
    obtain ⟨hV, hb⟩ := key hM
    exact leaf_bound hD hM hV hb
  | node t₁ t₂ i₁ i₂ => exact fun key => ⟨i₁ key.1, i₂ key.2⟩

theorem leafBound : DiscInf → TopInf → InfOfEq → LeafBound := by
  intro hD hT hQ E _ _ _ N t ψ m B hI hG hψ hψ0 hC hB
  refine leaves_of_entries hD B (leaf_entries hD hT B hG fun τ m' hm' x hx => ?_)
  rw [hQ E N t ψ m τ m' hI hm' hψ hψ0 hC] at hx
  exact hB τ x hx

end GlobalTheory.CompanionTheory.EGlue.LeafB

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitLists
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

section LimLists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem limL_allLeaves_strip (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    ∀ {N : ℕ} (t : Tr E N), t.strip.AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_shift (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) (z : ℂ) :
    ∀ {N : ℕ} (t : Tr E N), (t.shift z).AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z' => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_mono {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (h : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact h _ _
  | node t₁ t₂ i₁ i₂ => exact fun a => ⟨i₁ a.1, i₂ a.2⟩

theorem limL_disc_shift (z : ℂ) : ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Disc → (t.shift z).Disc := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr h
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

theorem limL_good_shift {z : ℂ} (hz : z.re = 0) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Good → (t.shift z).Good := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr ⟨h.1, h.2.1, by simp [h.2.2, hz]⟩
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

def LimDiscBody (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ))
    (K : Subgroup (GL (Fin M) (Af E))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ [MeasurableSpace (GA E M)] [BorelSpace (GA E M)] (μ : Measure (GA E M)) [μ.IsHaarMeasure] (R : ℝ), 0 < M →
  ReproAll E →
  ∀ V : ℕ → Submodule ℂ (Sm E M), (∀ k, IsDiscrete (V k)) → (∀ k, HasType K W (V k)) → (∀ k, InfBdd R (V k)) →
  ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (t₀ : Tr E M), StrictMono φ ∧ t₀.Good ∧ (∀ k, (t k).Disc) ∧
    (∀ k, (t k).strip = t₀.strip) ∧
    t₀.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (t₀.twists.getD i 0))) ∧
    ∀ k, Emb (V (φ k)) (· ∈ (t k).space)

theorem limL_exists_haar (M : ℕ) : ∃ (_ : MeasurableSpace (GA E M)) (_ : BorelSpace (GA E M)) (μ : Measure (GA E M)),
    μ.IsHaarMeasure := by
  letI : MeasurableSpace (GA E M) := borel _
  haveI : BorelSpace (GA E M) := ⟨rfl⟩
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E M
  exact ⟨_, inferInstance, Measure.haar, inferInstance⟩

theorem limL_lim_one (hS : ConvStrip) (hSh : ConvShift) (hC : ConvComp) (hT : TwShift) {M : ℕ} (hM : 0 < M)
    {W : Submodule ℂ (Kinf E M → ℂ)} {K : Subgroup (GL (Fin M) (Af E))}
    {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hB : LimDiscBody E M W K Ω Θ) (V : ℕ → Submodule ℂ (Sm E M)) (z : ℕ → ℂ) (R : ℝ) (hR : ReproAll E)
    (hD : ∀ k, IsDiscrete (V k)) (hz : ∀ k, (z k).re = 0) (hTy : ∀ k, HasType K W (V k))
    (hI : ∀ k, InfBdd R (V k)) (hzR : ∀ k, ‖z k‖ ≤ R) :
    ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (s : Tr E M), StrictMono φ ∧ Conv t s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧ (∀ k, (t k).Disc) ∧
      ∀ k, Emb (tw (V (φ k)) (z (φ k))) (· ∈ (t k).space) := by
  obtain ⟨_, _, μ, _⟩ := limL_exists_haar (E := E) M
  obtain ⟨φ, tt, t₀, hφ, hG, hDt, hst, hL, htw, hE⟩ := hB μ R hM hR V hD hTy hI
  obtain ⟨z₀, hz₀, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded (x := fun k => z (φ k))
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)) (fun k => by simpa using hzR (φ k))
  have hre : z₀.re = 0 := by
    have h1 : Tendsto (fun k => (z (φ (ψ k))).re) atTop (𝓝 z₀.re) :=
      (Complex.continuous_re.tendsto z₀).comp hlim
    simp only [hz, ] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  have hpos : t₀.AllLeaves (fun M _ => 0 < M) := limL_allLeaves_mono (fun _ _ h => h.1) hL
  have hposk : ∀ k, (tt k).AllLeaves (fun M _ => 0 < M) := fun k => by
    rw [← limL_allLeaves_strip, hst k, limL_allLeaves_strip]
    exact hpos
  have hconv : Conv tt t₀ := (hS E M tt t₀).2 ⟨hst, htw⟩
  have hconv' : Conv (fun k => (tt (ψ k)).shift (z (φ (ψ k)))) (t₀.shift z₀) :=
    hSh E M _ t₀ _ z₀ (hC E M tt t₀ ψ hconv hψ) hlim
  have hL' : (t₀.shift z₀).AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) :=
    (limL_allLeaves_shift _ _ _).2 hL
  exact ⟨fun k => φ (ψ k), fun k => (tt (ψ k)).shift (z (φ (ψ k))), t₀.shift z₀, hφ.comp hψ, hconv',
    red_of_leaves hL', limL_good_shift hre hpos hG, hL', fun k => limL_disc_shift _ (hposk _) (hDt _),
    fun k => hT E M _ _ _ (hD _).stable (hE _)⟩

end LimLists

theorem limLists : ConvStrip → ConvShift → ConvComp → LimLists := by
  intro hS hSh hC h5 hT E _ _ _ N Ωs hΩs
  have h1 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)),
      ∃ Ω : ∀ M' : ℕ, Set (Submodule ℂ (Kinf E M' → ℂ)), KTypes E Ω ∧
        (FiniteDimensional ℂ W → ∀ K : Subgroup (GL (Fin M) (Af E)), IsOpen (K : Set (GL (Fin M) (Af E))) →
          ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧ LimDiscBody E M W K Ω Θ) := by
    intro M W
    by_cases hW : FiniteDimensional ℂ W
    · obtain ⟨Ω, hΩ, h⟩ := h5 E M W hW
      exact ⟨Ω, hΩ, fun _ K hK => h K hK⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, by simp⟩, fun h => absurd h hW⟩
  choose Om hOm hOm' using h1
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, Om M W M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ => (hOm M W M').1, ?_⟩
    intro W' hW'
    simp only [Set.mem_iUnion] at hW'
    obtain ⟨M, _, W, _, h⟩ := hW'
    exact (hOm M W M').2 W' h
  intro Θs hΘs
  have h2 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)) (K : Subgroup (GL (Fin M) (Af E))),
      ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧
        (FiniteDimensional ℂ W → IsOpen (K : Set (GL (Fin M) (Af E))) → LimDiscBody E M W K (Om M W) Θ) := by
    intro M W K
    by_cases h : FiniteDimensional ℂ W ∧ IsOpen (K : Set (GL (Fin M) (Af E)))
    · obtain ⟨Θ, hΘ, hb⟩ := hOm' M W h.1 K h.2
      exact ⟨Θ, hΘ, fun _ _ => hb⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, fun _ hk => False.elim hk⟩,
        fun a b => absurd ⟨a, b⟩ h⟩
  choose Th hTh hTh' using h2
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, ⋃ K ∈ Θs M, Th M W K M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ =>
      (hΘs M).1.biUnion fun K _ => (hTh M W K M').1, ?_⟩
    intro K' hK'
    simp only [Set.mem_iUnion] at hK'
    obtain ⟨M, _, W, _, K, _, h⟩ := hK'
    exact (hTh M W K M').2 K' h
  intro M hM hMN V z R hR hD hz hTy hI hzR
  choose Kk hKk Wk hWk hty using hTy
  have hfin : (Θs M ×ˢ Ωs M).Finite := (hΘs M).1.prod (hΩs M).1
  haveI := hfin.to_subtype
  obtain ⟨⟨⟨K, W⟩, hKW⟩, hinf⟩ := Finite.exists_infinite_fiber
    (fun k : ℕ => (⟨(Kk k, Wk k), hKk k, hWk k⟩ : ↥(Θs M ×ˢ Ωs M)))
  have hfr : ∃ᶠ k in atTop, Kk k = K ∧ Wk k = W := by
    refine Nat.frequently_atTop_iff_infinite.2 ((Set.infinite_coe_iff.1 hinf).mono ?_)
    intro k hk
    have h := congrArg Subtype.val (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hk))
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨a, ha, hak⟩ := extraction_of_frequently_atTop hfr
  have hK : K ∈ Θs M := hKW.1
  have hW : W ∈ Ωs M := hKW.2
  have hbody : LimDiscBody E M W K (Om M W) (Th M W K) := hTh' M W K ((hΩs M).2 W hW) ((hΘs M).2 K hK)
  have htyp : ∀ k, HasType K W (V (a k)) := fun k => by
    have h := hty (a k)
    rwa [(hak k).1, (hak k).2] at h
  obtain ⟨φ, t, s, hφ, hc, hr, hg, hl, hd, he⟩ := limL_lim_one hS hSh hC hT hM hbody (fun k => V (a k))
    (fun k => z (a k)) R hR (fun k => hD _) (fun k => hz _) htyp (fun k => hI _) (fun k => hzR _)
  refine ⟨fun k => a (φ k), t, s, ha.comp hφ, hc, hr, hg, limL_allLeaves_mono ?_ hl, hd, he⟩
  rintro M' V' ⟨-, K'', hK'', W'', hW'', h⟩
  refine Or.inr ⟨K'', ?_, W'', ?_, h⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, K, hK, hK''⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, hW''⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

