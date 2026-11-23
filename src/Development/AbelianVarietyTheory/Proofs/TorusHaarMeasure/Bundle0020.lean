module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroup
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.DriftUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.DriftUnitary.continuous_orbit {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    Continuous fun g : H => X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC
  refine continuous_pi fun τ => ?_
  exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).matrix_mul
    continuous_const

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem single_one_mulVec_eq_pi_single (r : ℕ) (j k : Fin r) (w : Fin r → ℂ) :
    (Matrix.single j k (1 : ℂ)).mulVec w = Pi.single j (w k) := by
  ext i
  by_cases hi : i = j
  · subst hi; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hi, Ne.symm hi]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem eq_bot_or_eq_whole_of_single_mulVec_invariant (r p : ℕ) (hp : 0 < p) (hpr : p < r)
    (W : Submodule ℂ (Fin r → ℂ))
    (hW : ∀ (j k : Fin r), (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W,
      (Matrix.single j k 1).mulVec v ∈ W ∧ (Matrix.single k j 1).mulVec v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  have hsmul : ∀ (i : Fin r) (z : ℂ), z ≠ 0 → Pi.single i z ∈ W → Pi.single i (1 : ℂ) ∈ W := by
    intro i z hz h
    have e : z⁻¹ • (Pi.single i z : Fin r → ℂ) = Pi.single i 1 := by
      ext l
      by_cases hl : l = i <;> simp [hl, hz]
    rw [← e]
    exact W.smul_mem _ h
  let j0 : Fin r := ⟨0, by omega⟩
  let k0 : Fin r := ⟨p, hpr⟩
  have hj0 : (j0 : ℕ) < p := hp
  have hk0' : p ≤ (k0 : ℕ) := le_rfl
  have hk0 : Pi.single k0 (1 : ℂ) ∈ W := by
    rcases Nat.lt_or_ge (m : ℕ) p with h | h
    · have h1 := (hW m k0 h hk0' v hvW).2
      rw [single_one_mulVec_eq_pi_single] at h1
      exact hsmul _ _ hm h1
    · have h1 := (hW j0 m hj0 h v hvW).1
      rw [single_one_mulVec_eq_pi_single] at h1
      have h3 := (hW j0 k0 hj0 hk0' _ (hsmul _ _ hm h1)).2
      rw [single_one_mulVec_eq_pi_single] at h3
      simpa using h3
  have he0 : Pi.single j0 (1 : ℂ) ∈ W := by
    have h1 := (hW j0 k0 hj0 hk0' _ hk0).1
    rw [single_one_mulVec_eq_pi_single] at h1
    simpa using h1
  have hall : ∀ i : Fin r, Pi.single i (1 : ℂ) ∈ W := by
    intro i
    rcases Nat.lt_or_ge (i : ℕ) p with h | h
    · have h1 := (hW i k0 h hk0' _ hk0).1
      rw [single_one_mulVec_eq_pi_single] at h1
      simpa using h1
    · have h1 := (hW j0 i hj0 h _ he0).2
      rw [single_one_mulVec_eq_pi_single] at h1
      simpa using h1
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ i, w i • (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact Submodule.sum_mem _ fun i _ => W.smul_mem _ (hall i)


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.DriftUnitary.exists_drift_function :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < X.p0 → X.p0 < r → ∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  intro r X H hH _ _ hp0 hpr x0 hx0
  obtain ⟨S, hSne, hS1, hS2, hS3⟩ := _root_.GlobalTheory.exists_finite_symmetric_irreducible_rotations
    eq_bot_or_eq_whole_of_single_mulVec_invariant r X.p0 hp0 hpr
  obtain ⟨τ0⟩ := _root_.GlobalTheory.LineHeight.nonempty_cmType X
  obtain ⟨f, c, b, hc0, hc1, hb, hlsc, hf0, hfinv, hdrift, hla⟩ :=
    _root_.GlobalTheory.exists_drift_function_orthFrames r X hp0 hpr τ0 S hS1 hS2 (fun a ha => (hS3 a ha).1)
  have horb := (((_root_.GlobalTheory.UnitaryFrames.unitary_group_frames (E := E)).2 r X H hH).2.2 x0 hx0).1
  have hstep := fun a : S => _root_.GlobalTheory.UnitaryLift.step_of_right_mul r X H hH x0 hx0 τ0 a.1
    (hS3 a.1 a.2).2.choose (hS3 a.1 a.2).1 (hS3 a.1 a.2).2.choose_spec.1 (hS3 a.1 a.2).2.choose_spec.2
  choose hS kS hkS hupd using hstep
  refine ⟨S, inferInstance, hSne.to_subtype, hS,
    fun g => f (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0), c, b,
    fun s => ⟨kS s, hkS s⟩, ?_, fun g => hf0 _ (horb g), ?_, hc0, hc1, hb, ?_, ?_⟩
  · have hcont := _root_.GlobalTheory.DriftUnitary.continuous_orbit X H x0
    have hl : LowerSemicontinuous fun g : H =>
        f (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
      intro g y hy
      have ht : Filter.Tendsto (fun g : H =>
          X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) (𝓝 g)
          (𝓝[{x | _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x}] (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) :=
        tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto g, Filter.Eventually.of_forall fun g' => show _ ∈ {x | _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x} from horb g'⟩
      exact ht.eventually (hlsc _ (horb g) y hy)
    exact hl.measurable
  · rintro u ⟨γ, hγ, hu⟩ g
    have e : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
      funext τ
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hu τ,
        Matrix.mul_assoc]
      rfl
    show f _ = f _
    rw [e]
    exact hfinv γ hγ _ (horb g)
  · intro g
    simp only [hupd, Fintype.card_coe]
    exact (Finset.sum_coe_sort S _).trans_le (hdrift _ (horb g))
  · intro M
    obtain ⟨ε, hε, h⟩ := hla M
    exact ⟨ε, hε, fun g hg => h _ (horb g) hg⟩

end GlobalTheory.DriftUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegralEqIntegralTsumOfLintegral
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UnfoldComplex

theorem integral_eq_integral_tsum_of_lintegral {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ ν : Measure α) (f : α → ℂ) (g : ι → α → ℂ) (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (H : ∀ φ : ℂ → ℝ≥0∞, Measurable φ → ∫⁻ z, φ (f z) ∂μ = ∫⁻ z, ∑' i, φ (g i z) ∂ν)
    (hi : Integrable f μ) : ∫ z, f z ∂μ = ∫ z, ∑' i, g i z ∂ν := by
  have hmap : μ.map f = Measure.sum fun i => ν.map (g i) := by
    ext s hs
    have hφ : Measurable (s.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hs
    have h1 := H _ hφ
    rw [lintegral_tsum (f := fun i z => s.indicator (1 : ℂ → ℝ≥0∞) (g i z))
      fun i => (hφ.comp (hg i)).aemeasurable] at h1
    rw [Measure.sum_apply _ hs, ← lintegral_indicator_one hs, lintegral_map hφ hf, h1]
    refine tsum_congr fun i => ?_
    rw [← lintegral_indicator_one hs, lintegral_map hφ (hg i)]
  have hfin : ∑' i, ∫⁻ z, ‖g i z‖ₑ ∂ν ≠ ⊤ := by
    have h1 := H (fun w => ‖w‖ₑ) measurable_enorm
    rw [lintegral_tsum fun i => (hg i).enorm.aemeasurable] at h1
    rw [← h1]
    exact hi.2.ne
  have hid : Integrable (fun w : ℂ => w) (μ.map f) :=
    (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).mpr hi
  rw [integral_tsum (fun i => (hg i).aestronglyMeasurable) hfin]
  calc ∫ z, f z ∂μ = ∫ w, w ∂(μ.map f) := (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
    _ = ∑' i, ∫ w, w ∂(ν.map (g i)) := by
        rw [hmap] at hid ⊢
        exact integral_sum_measure hid
    _ = ∑' i, ∫ z, g i z ∂ν :=
        tsum_congr fun i => integral_map (hg i).aemeasurable aestronglyMeasurable_id

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (fun y : Frame Ψ r => lact δ y) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun y : Frame Ψ r =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ)
  have hM : Continuous fun y : Frame Ψ r => mat y τ := continuous_apply τ
  exact continuous_const.matrix_mul hM

theorem unfold_integral :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ h : Frame X.Ψ r → ℂ, Measurable h → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, h (rmul x b) = h x) → Integrable (fun z => h (cpt X x0 z)) (muF X x0) → ∫ z, h (cpt X x0 z) ∂muF X x0 = ∫ z in FF, ∑' γ : X.Γ, h (lact γ.1 (cpt X x0 z)) ∂muF X x0) := by
  intro H r X x0 ho FF hFF h hm hinv hint
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  refine integral_eq_integral_tsum_of_lintegral (muF X x0) ((muF X x0).restrict FF)
    (fun z => h (cpt X x0 z)) (fun (γ : X.Γ) z => h (lact γ.1 (cpt X x0 z))) (hm.comp hc)
    (fun γ => hm.comp ((continuous_lact γ.1).measurable.comp hc)) ?_ hint
  intro φ hφ
  exact H r X x0 ho FF hFF (fun x => φ (h x)) (hφ.comp hm)
    (fun x hx b hb => by simp only [hinv x hx b hb])

end GlobalTheory.UnfoldComplex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetBorSat
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameMeas

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : Set (Frame X.Ψ r) :=
  {y | ∃ x ∈ C, ∃ b ∈ Bor X.Ψ r, y = rmul x b}

theorem borSat_subset_dom {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hC : C ⊆ X.dom) :
    borSat X C ⊆ X.dom := by
  rintro y ⟨x, hx, b, hb, rfl⟩
  exact OrthogonalFrameDomain.rmul_mem_dom X (hC hx) hb

theorem subset_borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : C ⊆ borSat X C :=
  fun x hx => ⟨x, hx, ExtFPf.oneF X, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X x).symm⟩

theorem rmul_mem_borSat_iff {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ borSat X C ↔ y ∈ borSat X C := by
  constructor
  · rintro ⟨x, hx, b', hb', h⟩
    refine ⟨x, hx, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨x, hx, b', hb', rfl⟩
    exact ⟨x, hx, rmul b' b, ExtFPf.mul_mem X hb' hb, ExtFPf.rmul_assoc X _ _ _⟩

theorem measurableSet_borSat {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hK : IsCompact C)
    (hC : C ⊆ X.dom) : MeasurableSet (borSat X C) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hK
  let T : Set (Frame X.Ψ r × C) := {p | ∀ τ : X.Ψ, ∀ a c : Fin r, c < a →
    ((mat p.2.1 τ).adjugate * ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat p.1 τ) a c = 0}
  have hm : ∀ τ : X.Ψ, Continuous fun y : Frame X.Ψ r => mat y τ := fun τ => continuous_apply τ
  have hT : IsClosed T := by
    simp only [T, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (((((hm τ).comp (continuous_subtype_val.comp continuous_snd)).matrix_adjugate).matrix_mul
      continuous_const).matrix_mul ((hm τ).comp continuous_fst)).matrix_elem a c
  have hT' : IsClosed (Prod.fst '' T) := isClosedMap_fst_of_compactSpace T hT
  have hU : IsOpen {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun τ => isOpen_ne_fun (hm τ).matrix_det continuous_const
  have heq : borSat X C = {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} ∩ Prod.fst '' T := by
    ext y
    constructor
    · intro hy
      have hyd : ∀ τ, (mat y τ).det ≠ 0 := fun τ => (borSat_subset_dom X hC hy τ).1
      obtain ⟨x, hx, b, hb, h⟩ := hy
      refine ⟨hyd, (y, ⟨x, hx⟩), ?_, rfl⟩
      exact (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mp
        ⟨b, hb, by rw [FundSetPf.lact_one]; exact h⟩
    · rintro ⟨hyd, ⟨y', x, hx⟩, hp, rfl⟩
      obtain ⟨b, hb, h⟩ := (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mpr hp
      rw [FundSetPf.lact_one] at h
      exact ⟨x, hx, b, hb, h⟩
  rw [heq]
  exact hU.measurableSet.inter hT'.measurableSet

theorem sat_eq_preimage {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {C : Set (Frame X.Ψ r)}
    (hC : C ⊆ X.dom) : sat X x0 C = cpt X x0 ⁻¹' borSat X C := by
  ext z
  exact ⟨fun h => h.2, fun h => ⟨borSat_subset_dom X hC h, h⟩⟩

theorem frameMeas_of_local (hI : MeasInvStatement (E := E))
    (hL : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 → ∀ b1 ∈ Bor X.Ψ r,
      ∃ U ∈ 𝓝 (rmul x1 b1), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
        ∫⁻ x in U, G x ≤ K * ∫⁻ z, G (cpt X x1 z) ∂muF X x1) :
    FrameMeasStatement (E := E) := by
  intro r X x0 hx0 C hK hC
  have key : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in C, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0 := by
    refine hK.induction_on (p := fun s => ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞,
      Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in s, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0) ?_ ?_ ?_ ?_
    · exact ⟨0, ENNReal.zero_lt_top, fun G _ _ => by simp⟩
    · rintro s t hst ⟨K, hK, h⟩
      exact ⟨K, hK, fun G hG hB => (lintegral_mono_set hst).trans (h G hG hB)⟩
    · rintro s t ⟨K, hK, h⟩ ⟨K', hK', h'⟩
      refine ⟨K + K', ENNReal.add_lt_top.mpr ⟨hK, hK'⟩, fun G hG hB => ?_⟩
      rw [add_mul]
      exact (lintegral_union_le _ _ _).trans (add_le_add (h G hG hB) (h' G hG hB))
    · intro x hx
      obtain ⟨x1, hx1, b1, hb1, rfl⟩ := ortho_holds r X x (hC hx)
      obtain ⟨U, hU, K, hK, h⟩ := hL r X x1 hx1 b1 hb1
      refine ⟨U, mem_nhdsWithin_of_mem_nhds hU, K, hK, fun G hG hB => ?_⟩
      rw [hI r X x0 x1 hx0 hx1 G hG hB]
      exact h G hG hB
  obtain ⟨K, hKt, h⟩ := key
  refine ⟨K, hKt, fun G hG hB => ?_⟩
  have hS := measurableSet_borSat X hK hC
  have h1 := h ((borSat X C).indicator G) (hG.indicator hS) (by
    intro x hx b hb
    by_cases hxS : x ∈ borSat X C
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem ((rmul_mem_borSat_iff X C hb).mpr hxS),
        hB x hx b hb]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem fun h => hxS ((rmul_mem_borSat_iff X C hb).mp h)])
  have h2 : ∫⁻ x in C, (borSat X C).indicator G x = ∫⁻ x in C, G x :=
    setLIntegral_congr_fun hK.measurableSet fun x hx =>
      Set.indicator_of_mem (subset_borSat X C hx) G
  have h3 : ∫⁻ z, (borSat X C).indicator G (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0 := by
    rw [sat_eq_preimage X x0 hC,
      ← lintegral_indicator ((FundSetPf.cont_cpt X x0).measurable hS)]
    rfl
  rw [← h2, ← h3]
  exact h1

end GlobalTheory.FrameMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PairUnfoldOfUnfold
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PairUnfold

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
def pairDens {r : ℕ} (X : Data E r) (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) :
    Frame X.Ψ r → ℂ :=
  fun y => X.dom.piecewise (fun y => P y * (starRingEnd ℂ) (f0 y)) 0 y * ((W y).toReal : ℂ)

theorem pairDens_dom {r : ℕ} (X : Data E r) (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    pairDens X P f0 W x = P x * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ) := by
  simp [pairDens, Set.piecewise, hx]

theorem pairDens_meas {r : ℕ} (X : Data E r) {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ContinuousOn P X.dom) (hf : ContinuousOn f0 X.dom) (hW : Measurable W) :
    Measurable (pairDens X P f0 W) := by
  classical
  unfold pairDens
  exact (ContinuousOn.measurable_piecewise
    (hP.mul (Complex.continuous_conj.comp_continuousOn hf)) continuousOn_const
    (FourierCoefficientDomain.isOpen_dom X).measurableSet).mul
    (Complex.measurable_ofReal.comp hW.ennreal_toReal)

theorem pairDens_rmul {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : IsMetricW X la W) :
    ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, pairDens X P f0 W (rmul x b) = pairDens X P f0 W x := by
  intro x hx b hb
  have h0 := OntoE.bchar_ne X la hb
  have h1 : (starRingEnd ℂ) (bchar la b) ≠ 0 := by simpa using h0
  rw [pairDens_dom X P f0 W (OntoS.dom_rmul X hx hb), pairDens_dom X P f0 W hx, hP x hx b hb,
    hf x hx b hb, hW.2.1 x hx b hb, ENNReal.toReal_div, ENNReal.toReal_ofReal (sq_nonneg _), map_mul]
  push_cast
  rw [← Complex.mul_conj']
  field_simp

theorem pairDens_lact {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞}
    (hf : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, f0 (lact γ x) = X.χ la γ * f0 x)
    (hW : IsMetricW X la W) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    pairDens X P f0 W (lact γ x) =
      (X.χ la γ)⁻¹ * P (lact γ x) * ((starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ)) := by
  rw [pairDens_dom X P f0 W (OntoS.dom_lact X hγ hx), hf γ hγ x hx, hW.2.2 γ hγ x hx, map_mul,
    Complex.inv_eq_conj (OntoE.chi_norm X la hγ)]
  ring

theorem kaF_meas {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kaF X x0 bb) := by
  unfold kaF rhF
  refine Real.measurable_exp.comp (measurable_const.mul (Measurable.neg ?_))
  refine Finset.measurable_fun_sum _ fun τ _ => Real.measurable_log.comp ?_
  exact (OntoB.cd_dmin X x0 τ _).continuous.norm.measurable

theorem enorm_le {k : ℝ} (hk : 0 < k) (u g : ℂ) (w : ℝ≥0∞) :
    ‖u * (starRingEnd ℂ) g * (w.toReal : ℂ)‖ₑ ≤
      ENNReal.ofReal (‖u‖ ^ 2 / k) * w + ENNReal.ofReal k * (ENNReal.ofReal (‖g‖ ^ 2) * w) := by
  have h1 := OntoG.amgm (x := ‖u‖) (y := ‖g‖) hk
  have h2 : ‖u‖ * ‖g‖ ≤ ‖u‖ ^ 2 / k + k * ‖g‖ ^ 2 := by
    have : 0 ≤ ‖u‖ * ‖g‖ := by positivity
    linarith
  rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_mul (by positivity),
    ← mul_assoc, ← ENNReal.ofReal_mul hk.le, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal h2) ENNReal.ofReal_toReal_le

theorem pairUnfold_of_unfold :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ h : Frame X.Ψ r → ℂ, Measurable h → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, h (rmul x b) = h x) → Integrable (fun z => h (cpt X x0 z)) (muF X x0) → ∫ z, h (cpt X x0 z) ∂muF X x0 = ∫ z in FF, ∑' γ : X.Γ, h (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (KaUnfoldStatement (E := E)) → (PairUnfoldStatement (E := E)) := by
  intro hU hKa r X x0 hx0 hPD la W bb hW _ hbb F P _ hIn hP hPF FF hFF f0 hf0 hfF
  have hsec := hf0.1.1
  obtain ⟨C, hCt, hC⟩ := hKa r X x0 hx0 hPD FF hFF bb hbb
  have hφm := OntoE.phiF_meas X hsec.1.continuousOn hW.1
  have hφ := hC (OntoE.phiF X f0 W) hφm (OntoE.phiF_B X hsec.2.1 hW) (OntoE.phiF_G X hsec.2.2 hW)
  have hFFeq : ∫⁻ z in FF, OntoE.phiF X f0 W (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in FF, ENNReal.ofReal (‖f0 (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 :=
    setLIntegral_congr_fun hFF.1 (fun z hz => OntoE.phiF_dom X f0 W (hFF.2.1 hz))
  have hI : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * OntoE.phiF X f0 W (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine hφ.trans_lt (ENNReal.mul_lt_top hCt ?_)
    rw [hFFeq]; exact hfF
  have hcm : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  have hae := FundSetPf.ae_OmF' X x0
  have hm := pairDens_meas X hP.1.continuousOn hsec.1.continuousOn hW.1
  have hint : Integrable (fun z => pairDens X P f0 W (cpt X x0 z)) (muF X x0) := by
    refine ⟨(hm.comp hcm).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ z, ‖pairDens X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0
        ≤ ∫⁻ z, (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) +
            ENNReal.ofReal (kaF X x0 bb z) * OntoE.phiF X f0 W (cpt X x0 z)) ∂muF X x0 := by
          refine lintegral_mono_ae (hae.mono fun z hz => ?_)
          rw [pairDens_dom X P f0 W hz, OntoE.phiF_dom X f0 W hz, hPF z hz]
          exact enorm_le (Real.exp_pos _) _ _ _
      _ < ⊤ := by
          have hB : Measurable fun z => ENNReal.ofReal (kaF X x0 bb z) *
              OntoE.phiF X f0 W (cpt X x0 z) :=
            (ENNReal.measurable_ofReal.comp (kaF_meas X x0 bb)).mul (hφm.comp hcm)
          rw [lintegral_add_right _ hB]
          exact ENNReal.add_lt_top.2 ⟨hIn, hI⟩
  have key := hU r X x0 hx0 FF hFF _ hm (pairDens_rmul X hP.2 hsec.2.1 hW) hint
  calc _ = ∫ z in FF, ∑' γ : X.Γ, pairDens X P f0 W (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by
        refine setIntegral_congr_fun hFF.1 fun z hz => ?_
        have hz' : cpt X x0 z ∈ X.dom := hFF.2.1 hz
        simp only [poin]
        rw [mul_assoc, ← tsum_mul_right]
        exact tsum_congr fun γ => (pairDens_lact X hsec.2.2 hW γ.2 hz').symm
    _ = _ := by
        rw [← key]
        refine integral_congr_ae (hae.mono fun z hz => ?_)
        simp only
        rw [pairDens_dom X P f0 W hz, hPF z hz]

end

end GlobalTheory.PairUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PropDiscOfFlagDomainData
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

namespace GlobalTheory

theorem propDisc_of_flagDomainData :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), PropDisc X :=
  fun _ _ _ _ => GlobalTheory.ClosedDiscontinuity.propDisc_and_la1GG.1

end GlobalTheory
end

