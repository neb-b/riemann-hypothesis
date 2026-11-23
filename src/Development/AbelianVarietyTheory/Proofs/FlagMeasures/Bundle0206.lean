module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralPiProdTwo
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
open scoped ENNReal

noncomputable section

namespace GlobalTheory.PiCoord

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm
        (μ.prod (Measure.pi fun _ : Fin n => μ)) (Measure.pi fun _ : Fin (n + 1) => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have split : ∀ p : E × (Fin n → E),
        (∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm p i)) =
          f 0 p.1 * ∏ j : Fin n, f j.succ (p.2 j) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    simp_rw [split]
    have hrest : Measurable fun z : Fin n → E => ∏ j : Fin n, f j.succ (z j) :=
      Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)
    rw [lintegral_prod_mul (hf 0).aemeasurable hrest.aemeasurable,
      ih (fun j => f j.succ) (fun j => hf j.succ), Fin.prod_univ_succ]

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e)
      (Measure.pi fun _ : Fin (Fintype.card ι) => μ) (Measure.pi fun _ : ι => μ) :=
    measurePreserving_piCongrLeft (fun _ : ι => μ) e
  calc ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ)
      = ∫⁻ y : Fin (Fintype.card ι) → E, ∏ j, f (e j) (y j) ∂(Measure.pi fun _ => μ) := by
        rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        refine lintegral_congr fun y => ?_
        rw [← e.prod_comp]
        simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    _ = ∏ j, ∫⁻ t, f (e j) t ∂μ := lintegral_pi_fin _ μ _ fun j => hf (e j)
    _ = ∏ i, ∫⁻ t, f i t ∂μ := e.prod_comp fun i => ∫⁻ t, f i t ∂μ

theorem pi_withDensity {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : E → ℝ≥0∞) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : ι → E, (Set.univ.pi s).indicator (fun x => ∏ i, f (x i)) x =
      ∏ i, (s i).indicator f (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ i)) f).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)).symm
  simp_rw [hind]
  rw [lintegral_pi_prod μ (fun i => (s i).indicator f) fun i => hf.indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

private theorem lintegral_indicator_one_mul_eq_setLIntegral {X : Type*} [MeasurableSpace X] (m : Measure X) {t : Set X}
    (ht : MeasurableSet t) (w : X → ℝ≥0∞) :
    ∫⁻ x, t.indicator 1 x * w x ∂m = ∫⁻ x in t, w x ∂m := by
  rw [← lintegral_indicator ht]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ t
  · simp [hx]
  · simp [hx]

theorem pi_change {ι P D : Type*} [Fintype ι] [MeasurableSpace P] [MeasurableSpace D]
    (μ : Measure P) (ν : Measure D) [SigmaFinite μ] [SigmaFinite ν] (c : P → D) (hc : Measurable c)
    (ρ : D → ℝ) (σ : P → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρ0 : ∀ g, 0 ≤ ρ g) (hσ0 : ∀ h, 0 ≤ σ h)
    (H : ∀ φ : D → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g * ENNReal.ofReal (ρ g) ∂ν = ∫⁻ p, φ (c p) * ENNReal.ofReal (σ p) ∂μ)
    (φ : (ι → D) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) ∂(Measure.pi fun _ => ν) =
      ∫⁻ p : ι → P, φ (fun i => c (p i)) * ENNReal.ofReal (∏ i, σ (p i)) ∂(Measure.pi fun _ => μ) := by
  have hρm : Measurable fun g => ENNReal.ofReal (ρ g) := hρ.ennreal_ofReal
  have hσm : Measurable fun p => ENNReal.ofReal (σ p) := hσ.ennreal_ofReal
  have hmap : ν.withDensity (fun g => ENNReal.ofReal (ρ g)) =
      (μ.withDensity fun p => ENNReal.ofReal (σ p)).map c := by
    ext s hs
    rw [withDensity_apply _ hs, Measure.map_apply hc hs, withDensity_apply _ (hc hs)]
    have h1 := H (s.indicator 1) (measurable_one.indicator hs)
    rw [lintegral_indicator_one_mul_eq_setLIntegral ν hs] at h1
    have hpre : ∀ p, s.indicator (1 : D → ℝ≥0∞) (c p) = (c ⁻¹' s).indicator 1 p := by
      intro p
      by_cases hp : c p ∈ s
      · simp [hp]
      · simp [hp]
    simp_rw [hpre] at h1
    rw [lintegral_indicator_one_mul_eq_setLIntegral μ (hc hs)] at h1
    exact h1
  have hcm : Measurable fun (p : ι → P) (i : ι) => c (p i) :=
    Measurable.of_eval fun i => hc.comp (measurable_pi_apply i)
  have : SigmaFinite ((μ.withDensity fun p => ENNReal.ofReal (σ p)).map c) := by
    rw [← hmap]; infer_instance
  have hprodρ : ∀ g : ι → D, ENNReal.ofReal (∏ i, ρ (g i)) = ∏ i, ENNReal.ofReal (ρ (g i)) :=
    fun g => ENNReal.ofReal_prod_of_nonneg fun i _ => hρ0 _
  have hprodσ : ∀ p : ι → P, ENNReal.ofReal (∏ i, σ (p i)) = ∏ i, ENNReal.ofReal (σ (p i)) :=
    fun p => ENNReal.ofReal_prod_of_nonneg fun i _ => hσ0 _
  have hdρ : Measurable fun g : ι → D => ∏ i, ENNReal.ofReal (ρ (g i)) :=
    Finset.measurable_prod _ fun i _ => hρm.comp (measurable_pi_apply i)
  have hdσ : Measurable fun p : ι → P => ∏ i, ENNReal.ofReal (σ (p i)) :=
    Finset.measurable_prod _ fun i _ => hσm.comp (measurable_pi_apply i)
  calc ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) ∂(Measure.pi fun _ => ν)
      = ∫⁻ g, ((fun g : ι → D => ∏ i, ENNReal.ofReal (ρ (g i))) * φ) g ∂(Measure.pi fun _ => ν) := by
        refine lintegral_congr fun g => ?_
        rw [hprodρ, Pi.mul_apply, mul_comm]
    _ = ∫⁻ g, φ g ∂((Measure.pi fun _ : ι => ν).withDensity fun g => ∏ i, ENNReal.ofReal (ρ (g i))) :=
        (lintegral_withDensity_eq_lintegral_mul _ hdρ hφ).symm
    _ = ∫⁻ g, φ g ∂(Measure.pi fun _ : ι => ν.withDensity fun g => ENNReal.ofReal (ρ g)) := by
        rw [pi_withDensity ν _ hρm]
    _ = ∫⁻ g, φ g ∂(Measure.pi fun _ : ι => (μ.withDensity fun p => ENNReal.ofReal (σ p)).map c) := by
        rw [hmap]
    _ = ∫⁻ g, φ g ∂((Measure.pi fun _ : ι => μ.withDensity fun p => ENNReal.ofReal (σ p)).map
          fun (p : ι → P) (i : ι) => c (p i)) := by
        rw [Measure.pi_map_pi fun _ => hc.aemeasurable]
    _ = ∫⁻ p, φ (fun i => c (p i)) ∂(Measure.pi fun _ : ι => μ.withDensity fun p => ENNReal.ofReal (σ p)) :=
        lintegral_map hφ hcm
    _ = ∫⁻ p, φ (fun i => c (p i)) ∂((Measure.pi fun _ : ι => μ).withDensity
          fun p => ∏ i, ENNReal.ofReal (σ (p i))) := by
        rw [pi_withDensity μ _ hσm]
    _ = ∫⁻ p : ι → P, φ (fun i => c (p i)) * ENNReal.ofReal (∏ i, σ (p i)) ∂(Measure.pi fun _ => μ) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hdσ
          (show Measurable fun p : ι → P => φ (fun i => c (p i)) from hφ.comp hcm)]
        refine lintegral_congr fun p => ?_
        rw [hprodσ, Pi.mul_apply, mul_comm]

theorem lintegral_pi_prod_two {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (F : (ι → A × B) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, F p ∂(Measure.pi fun _ => μ.prod ν) =
      ∫⁻ a : ι → A, ∫⁻ b : ι → B, F (fun i => (a i, b i)) ∂(Measure.pi fun _ => ν)
        ∂(Measure.pi fun _ => μ) := by
  have hp : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow A B ι)
      (Measure.pi fun _ : ι => μ.prod ν) ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => ν)) :=
    measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => μ) (fun _ => ν)
  rw [← hp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
    lintegral_prod (fun z => F ((MeasurableEquiv.arrowProdEquivProdArrow A B ι).symm z))
      (show Measurable fun z => F ((MeasurableEquiv.arrowProdEquivProdArrow A B ι).symm z) from
        hF.comp (MeasurableEquiv.measurable _)).aemeasurable]
  rfl

theorem pi_change_three {ι A B C D : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (α : Measure A) (β : Measure B) (γ : Measure C) (ν : Measure D)
    [SigmaFinite α] [SigmaFinite β] [SigmaFinite γ] [SigmaFinite ν]
    (c : A → B → C → D) (hc : Measurable fun p : A × B × C => c p.1 p.2.1 p.2.2)
    (ρ : D → ℝ) (σ : B → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρ0 : ∀ g, 0 ≤ ρ g) (hσ0 : ∀ h, 0 ≤ σ h)
    (H : ∀ φ : D → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g * ENNReal.ofReal (ρ g) ∂ν =
        ∫⁻ x, ∫⁻ h, ∫⁻ T, φ (c x h T) * ENNReal.ofReal (σ h) ∂γ ∂β ∂α)
    (φ : (ι → D) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) ∂(Measure.pi fun _ => ν) =
      ∫⁻ x : ι → A, ∫⁻ h : ι → B, ∫⁻ T : ι → C,
        φ (fun i => c (x i) (h i) (T i)) * ENNReal.ofReal (∏ i, σ (h i))
        ∂(Measure.pi fun _ => γ) ∂(Measure.pi fun _ => β) ∂(Measure.pi fun _ => α) := by
  have hσ' : Measurable fun p : A × B × C => σ p.2.1 := hσ.comp (measurable_fst.comp measurable_snd)
  have H' : ∀ ψ : D → ℝ≥0∞, Measurable ψ → ∫⁻ g, ψ g * ENNReal.ofReal (ρ g) ∂ν =
      ∫⁻ p, ψ (c p.1 p.2.1 p.2.2) * ENNReal.ofReal (σ p.2.1) ∂(α.prod (β.prod γ)) := by
    intro ψ hψ
    have m1 : Measurable fun p : A × B × C => ψ (c p.1 p.2.1 p.2.2) * ENNReal.ofReal (σ p.2.1) :=
      (hψ.comp hc).mul hσ'.ennreal_ofReal
    rw [H ψ hψ, lintegral_prod _ m1.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact (lintegral_prod (fun q : B × C => ψ (c x q.1 q.2) * ENNReal.ofReal (σ q.1))
      (m1.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
  rw [pi_change (α.prod (β.prod γ)) ν (fun p => c p.1 p.2.1 p.2.2) hc ρ (fun p => σ p.2.1) hρ hσ'
    hρ0 (fun p => hσ0 _) H' φ hφ]
  have hF : Measurable fun p : ι → A × B × C =>
      φ (fun i => c (p i).1 (p i).2.1 (p i).2.2) * ENNReal.ofReal (∏ i, σ (p i).2.1) :=
    (hφ.comp (Measurable.of_eval fun i => hc.comp (measurable_pi_apply i))).mul
      (Finset.measurable_prod _ fun i _ => hσ'.comp (measurable_pi_apply i)).ennreal_ofReal
  rw [lintegral_pi_prod_two α (β.prod γ) _ hF]
  refine lintegral_congr fun x => ?_
  have hG : Measurable fun q : ι → B × C =>
      φ (fun i => c (x i) (q i).1 (q i).2) * ENNReal.ofReal (∏ i, σ (q i).1) :=
    hF.comp (Measurable.of_eval fun i => (measurable_const.prodMk (measurable_pi_apply i)))
  exact lintegral_pi_prod_two β γ _ hG

theorem piCoord : ∀ (ι : Type) [Fintype ι] (k : ℕ) (c : (Fin (k + 1) → ℂ) → (Fin k → Fin k → ℂ) → (Fin k → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ), Measurable (fun p : (Fin (k + 1) → ℂ) × (Fin k → Fin k → ℂ) × (Fin k → ℂ) => c p.1 p.2.1 p.2.2) → ∀ (ρ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ℝ) (σ : (Fin k → Fin k → ℂ) → ℝ), Measurable ρ → Measurable σ → (∀ g, 0 ≤ ρ g) → (∀ h, 0 ≤ σ h) → (∀ φ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ENNReal, Measurable φ → ∫⁻ g, φ g * ENNReal.ofReal (ρ g) = ∫⁻ x, ∫⁻ h, ∫⁻ T, φ (c x h T) * ENNReal.ofReal (σ h)) → ∀ φ : (ι → Fin (k + 1) → Fin (k + 1) → ℂ) → ENNReal, Measurable φ → ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) = ∫⁻ x : ι → Fin (k + 1) → ℂ, ∫⁻ h : ι → Fin k → Fin k → ℂ, ∫⁻ T : ι → Fin k → ℂ, φ (fun i => c (x i) (h i) (T i)) * ENNReal.ofReal (∏ i, σ (h i)) := by
  intro ι _ k c hc ρ σ hρ hσ hρ0 hσ0 H φ hφ
  exact pi_change_three volume volume volume volume c hc ρ σ hρ hσ hρ0 hσ0 H φ hφ

end GlobalTheory.PiCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTsumCosetsFundamentalDomainEqCovol
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem translate_inter_null {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    (μ : Measure G) (fund : Set G) (hμ : ∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) (hf : MeasurableSet fund)
    (hd : ∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) {a b : G} (ha : a ∈ Γ) (hb : b ∈ Γ)
    (hab : a ≠ b) :
    μ ((fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund) = 0 := by
  have hc : a⁻¹ * b ∈ Γ := Γ.mul_mem (Γ.inv_mem ha) hb
  have hc1 : a⁻¹ * b ≠ 1 := fun h => hab (inv_mul_eq_one.mp h)
  have hset : (fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund
      ⊆ (fun y => a⁻¹ * y) ⁻¹' ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund) := by
    rintro y ⟨h1, h2⟩
    refine ⟨⟨b⁻¹ * y, h2, ?_⟩, h1⟩
    show a⁻¹ * b * (b⁻¹ * y) = a⁻¹ * y
    group
  refine measure_mono_null hset (nonpos_iff_eq_zero.mp ?_)
  calc μ ((fun y => a⁻¹ * y) ⁻¹' ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund))
      ≤ μ.map (fun y => a⁻¹ * y) ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund) :=
        MeasureTheory.Measure.le_map_apply (measurable_const_mul _).aemeasurable _
    _ = 0 := by rw [hμ _ (Γ.inv_mem ha)]; exact hd _ hc hc1

private theorem withDensity_preimage_inv_mul_eq_setLIntegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) (Φ : G → ENNReal) (hΦ : Measurable Φ) (a : G) (hμa : μ.map (fun y => a * y) = μ)
    (fund : Set G) (hf : MeasurableSet fund) :
    μ.withDensity Φ ((fun y => a⁻¹ * y) ⁻¹' fund) = ∫⁻ g in fund, Φ (a * g) ∂μ := by
  classical
  have hT : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' fund) := hf.preimage (measurable_const_mul _)
  rw [withDensity_apply _ hT, ← lintegral_indicator hT, ← lintegral_indicator hf]
  have hm : Measurable (((fun y => a⁻¹ * y) ⁻¹' fund).indicator Φ) := hΦ.indicator hT
  have key := MeasureTheory.lintegral_map (μ := μ) hm (measurable_const_mul a)
  rw [hμa] at key
  rw [key]
  congr 1
  funext x
  by_cases hx : x ∈ fund
  · have hx' : a * x ∈ (fun y => a⁻¹ * y) ⁻¹' fund := by
      show a⁻¹ * (a * x) ∈ fund
      rwa [inv_mul_cancel_left]
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
  · have hx' : a * x ∉ (fun y => a⁻¹ * y) ⁻¹' fund := by
      show a⁻¹ * (a * x) ∉ fund
      rwa [inv_mul_cancel_left]
    rw [Set.indicator_apply, Set.indicator_apply, if_neg hx', if_neg hx]

private theorem withDensity_preimage_mul_eq_of_invariant {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) (Φ : G → ENNReal) (hΦ : Measurable Φ) (s : G) (hμs : μ.map (fun y => s * y) = μ)
    (hΦs : ∀ g, Φ (s * g) = Φ g) (Q : Set G) (hQ : MeasurableSet Q) :
    μ.withDensity Φ ((fun y => s * y) ⁻¹' Q) = μ.withDensity Φ Q := by
  classical
  have hT : MeasurableSet ((fun y => s * y) ⁻¹' Q) := hQ.preimage (measurable_const_mul _)
  rw [withDensity_apply _ hT, withDensity_apply _ hQ, ← lintegral_indicator hT, ← lintegral_indicator hQ]
  have key := MeasureTheory.lintegral_map (μ := μ) (hΦ.indicator hQ) (measurable_const_mul s)
  rw [hμs] at key
  rw [key]
  congr 1
  funext y
  by_cases hy : s * y ∈ Q
  · have hy' : y ∈ (fun y => s * y) ⁻¹' Q := hy
    rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy, hΦs]
  · have hy' : y ∉ (fun y => s * y) ⁻¹' Q := hy
    rw [Set.indicator_apply, Set.indicator_apply, if_neg hy', if_neg hy]

theorem lintegral_tsum_cosets_eq_covol : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ S : Subgroup G) (μ : Measure G) (fund : Set G) (Φ : G → ENNReal) (ι : Type) [Countable ι] (r : ι → G), (Γ : Set G).Countable → S ≤ Γ → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → Measurable Φ → (∀ γ ∈ S, ∀ g, Φ (γ * g) = Φ g) → (∀ i, r i ∈ Γ) → (∀ γ ∈ Γ, ∃! i, γ * (r i)⁻¹ ∈ S) → ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ = covol (S : Set G) (μ.withDensity Φ) Set.univ := by
  intro G _ _ _ Γ S μ fund Φ ι _ r hΓ hSΓ hμ hf hcov hd hΦ hΦS hr hrep
  have hTm : ∀ a : G, MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' fund) :=
    fun a => hf.preimage (measurable_const_mul _)
  have hSc : (S : Set G).Countable := hΓ.mono hSΓ
  have hD0m : MeasurableSet (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) := MeasurableSet.iUnion fun i => hTm _
  have hnull : ∀ a b : G, a ∈ Γ → b ∈ Γ → a ≠ b →
      μ.withDensity Φ ((fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund) = 0 :=
    fun a b ha hb hab => withDensity_absolutelyContinuous μ Φ
      (translate_inter_null Γ μ fund hμ hf hd ha hb hab)
  have hL : ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ
      = μ.withDensity Φ (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) := by
    rw [lintegral_tsum (f := fun i g => Φ (r i * g)) fun i => (hΦ.comp (measurable_const_mul (r i))).aemeasurable]
    rw [measure_iUnion₀ ?_ fun i => (hTm _).nullMeasurableSet]
    · exact tsum_congr fun i =>
        (withDensity_preimage_inv_mul_eq_setLIntegral μ Φ hΦ (r i) (hμ _ (hr i)) fund hf).symm
    · intro i j hij
      refine hnull _ _ (hr i) (hr j) fun he => hij ?_
      have h1 : r i * (r i)⁻¹ ∈ S := by simpa using S.one_mem
      exact (hrep _ (hr i)).unique h1 (by rw [he]; simpa using S.one_mem)
  rw [hL]
  unfold GlobalTheory.FlagMeas.covol
  apply le_antisymm
  · refine le_iInf fun D => le_iInf fun hDm => le_iInf fun hDc => ?_
    calc μ.withDensity Φ (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund)
        ≤ μ.withDensity Φ (⋃ s ∈ (S : Set G), (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ (fun y => s * y) ⁻¹' D) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨s, hs, hsx⟩ := hDc x (Set.mem_univ x)
          exact Set.mem_biUnion hs ⟨hx, hsx⟩
      _ ≤ ∑' p : (S : Set G), μ.withDensity Φ ((⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ (fun y => (p : G) * y) ⁻¹' D) :=
          measure_biUnion_le _ hSc _
      _ = ∑' p : (S : Set G), μ.withDensity Φ ((fun y => (p : G)⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) := by
          refine tsum_congr fun p => ?_
          have hpS : (p : G) ∈ S := p.2
          rw [← withDensity_preimage_mul_eq_of_invariant μ Φ hΦ (p : G) (hμ _ (hSΓ hpS)) (fun g => hΦS _ hpS g) _
            ((hD0m.preimage (measurable_const_mul _)).inter hDm)]
          congr 1
          ext y
          simp only [Set.mem_inter_iff, Set.mem_preimage, inv_mul_cancel_left]
      _ = μ.withDensity Φ (⋃ s ∈ (S : Set G), (fun y => s⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) := by
          refine (measure_biUnion₀ hSc ?_ fun s _ =>
            ((hD0m.preimage (measurable_const_mul _)).inter hDm).nullMeasurableSet).symm
          intro s hs s' hs' hne
          have hsub : ((fun y => s⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) ∩
              ((fun y => s'⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) ⊆
              ⋃ i, ⋃ j, (fun y => (s * r i)⁻¹ * y) ⁻¹' fund ∩ (fun y => (s' * r j)⁻¹ * y) ⁻¹' fund := by
            rintro y ⟨⟨hy1, -⟩, hy2, -⟩
            simp only [Set.mem_preimage, Set.mem_iUnion] at hy1 hy2
            obtain ⟨i, hi⟩ := hy1
            obtain ⟨j, hj⟩ := hy2
            simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, _root_.mul_inv_rev, mul_assoc]
            exact ⟨i, j, hi, hj⟩
          refine measure_mono_null hsub (measure_iUnion_null fun i => measure_iUnion_null fun j => ?_)
          refine hnull _ _ (Γ.mul_mem (hSΓ hs) (hr i)) (Γ.mul_mem (hSΓ hs') (hr j)) fun he => hne ?_
          have h1 : s * r i * (r i)⁻¹ ∈ S := by rw [mul_inv_cancel_right]; exact hs
          have h2 : s * r i * (r j)⁻¹ ∈ S := by rw [he, mul_inv_cancel_right]; exact hs'
          have hij := (hrep _ (Γ.mul_mem (hSΓ hs) (hr i))).unique h1 h2
          subst hij
          exact mul_right_cancel he
      _ ≤ μ.withDensity Φ D := measure_mono (Set.iUnion₂_subset fun _ _ => Set.inter_subset_right)
  · refine iInf_le_of_le _ (iInf_le_of_le hD0m (iInf_le _ ?_))
    intro x _
    obtain ⟨γ, hγ, hγx⟩ := hcov x
    obtain ⟨i, hi, -⟩ := hrep γ⁻¹ (Γ.inv_mem hγ)
    refine ⟨(γ⁻¹ * (r i)⁻¹)⁻¹, S.inv_mem hi, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    show (r i)⁻¹ * ((γ⁻¹ * (r i)⁻¹)⁻¹ * x) ∈ fund
    have e : (r i)⁻¹ * ((γ⁻¹ * (r i)⁻¹)⁻¹ * x) = γ * x := by group
    rw [e]; exact hγx

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureCommonStabilizerCoordsBoxImage
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefMeas

theorem image_meas {ι X Y Z : Type} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z]
    (μ : Measure X) [SigmaFinite μ] (ν : Measure Z) (c : X → Y) (hc : Measurable c) (hi : Function.Injective c)
    (a : Z → ι → X) (ha : MeasurePreserving a ν (Measure.pi fun _ : ι => μ)) (hai : Function.Injective a)
    (S : Set Z) (hS : MeasurableSet S) :
    MeasurableSet ((fun p v => c (a p v)) '' S) ∧
      Measure.pi (fun _ : ι => μ.map c) ((fun p v => c (a p v)) '' S) = ν S := by
  have he : MeasurableEmbedding c := hc.measurableEmbedding hi
  haveI : SigmaFinite (μ.map c) := he.sigmaFinite_map
  have h1 : MeasurePreserving (fun (q : ι → X) (v : ι) => c (q v)) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ.map c) :=
    measurePreserving_pi _ _ fun _ => ⟨hc, rfl⟩
  have h2 : MeasurePreserving (fun (p : Z) (v : ι) => c (a p v)) ν (Measure.pi fun _ : ι => μ.map c) := h1.comp ha
  have hinj : Function.Injective (fun (p : Z) (v : ι) => c (a p v)) := fun p q h =>
    hai (funext fun v => hi (congrFun h v))
  have hm : MeasurableSet ((fun p v => c (a p v)) '' S) := hS.image_of_measurable_injOn h2.measurable hinj.injOn
  refine ⟨hm, ?_⟩
  rw [← h2.measure_preimage hm.nullMeasurableSet, Set.preimage_image_eq _ hinj]

theorem box_meas : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) → ∀ (F₁ : UTin β → Set (ι → ℂ)) (F₂ : {a : Fin r // j ≤ a.val} → Set (ι → Fin (k + 1) → ℂ)) (F₃ : {p : UT r // j ≤ p.1.1.val} → Set (ι → ℂ)) (F₄ : {a : Fin r // j ≤ a.val} → Set (ι → ℝ)), (∀ i, MeasurableSet (F₁ i)) → (∀ i, MeasurableSet (F₂ i)) → (∀ i, MeasurableSet (F₃ i)) → (∀ i, MeasurableSet (F₄ i)) → ∀ Ω : Set (ι → Mt k r), Ω = (fun (p : Crd ι k r j β) (v : ι) => (Matrix.of.symm (CC p v) : Mt k r)) '' (Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) → MeasurableSet Ω ∧ Measure.pi (fun _ : ι => lebR0 k r j β) Ω = (∏ i, volume (F₁ i)) * ((∏ i, volume (F₂ i)) * ((∏ i, volume (F₃ i)) * ∏ i, volume (F₄ i))) := by
  intro ι _ k r j β hm hβ hat F₁ F₂ F₃ F₄ h₁ h₂ h₃ h₄ Ω hΩ
  obtain ⟨hl, -, hinj, -⟩ := Swap.range_eq_and_injective_parabolic_unipotent_product k r j β hm hβ
  haveI s1 : SigmaFinite (volume : Measure (Swap.STop r j)) := Measure.prod.instSigmaFinite
  haveI s2 : SigmaFinite (volume : Measure (PTop k r j)) := Measure.prod.instSigmaFinite
  haveI s3 : SigmaFinite (volume : Measure ((UTin β → ℂ) × PTop k r j)) := Measure.prod.instSigmaFinite
  haveI b1 : BorelSpace (Swap.STop r j) := Prod.borelSpace
  haveI b2 : BorelSpace (PTop k r j) := Prod.borelSpace
  haveI b3 : BorelSpace ((UTin β → ℂ) × PTop k r j) := Prod.borelSpace
  have hG : Continuous fun q : (UTin β → ℂ) × PTop k r j =>
      (Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1)) : Mt k r) :=
    (Swap.cont_pTop.comp continuous_snd).matrix_mul ((GlobalTheory.Amp.Swap.cont_uEmb k r).comp
      ((Swap.extZ (fun p : UT r => β p.1.1 = β p.1.2) ℂ).continuous_of_finiteDimensional.comp continuous_fst))
  have hS : MeasurableSet ((Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) : Set (Crd ι k r j β)) :=
    (MeasurableSet.univ_pi h₁).prod ((MeasurableSet.univ_pi h₂).prod ((MeasurableSet.univ_pi h₃).prod (MeasurableSet.univ_pi h₄)))
  haveI d1 : StandardBorelSpace (Swap.STop r j) := StandardBorelSpace.prod
  haveI d2 : StandardBorelSpace (PTop k r j) := StandardBorelSpace.prod
  haveI d3 : StandardBorelSpace ((UTin β → ℂ) × PTop k r j) := StandardBorelSpace.prod
  haveI d4 : StandardBorelSpace (Mt k r) := StandardBorelSpace.pi_countable
  haveI d5 : StandardBorelSpace (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)) := StandardBorelSpace.prod
  haveI d6 : StandardBorelSpace ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) := StandardBorelSpace.pi_countable
  haveI d7 : StandardBorelSpace (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := StandardBorelSpace.prod
  haveI d8 : StandardBorelSpace (Crd ι k r j β) := StandardBorelSpace.prod
  have key := image_meas (volume : Measure ((UTin β → ℂ) × PTop k r j)) volume _ hG.measurable
    (Matrix.of.symm.injective.comp hinj) atP hat usage₂.1 _ hS
  rw [← hl] at key
  subst hΩ
  refine ⟨key.1, key.2.trans ?_⟩
  haveI t1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) :=
    Measure.prod.instSigmaFinite
  haveI t3 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := Measure.pi.sigmaFinite _
  haveI t4 : SigmaFinite (volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)) := Measure.pi.sigmaFinite _
  haveI t2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) :=
    Measure.prod.instSigmaFinite
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    volume_pi_pi, volume_pi_pi, volume_pi_pi, volume_pi_pi]

end GlobalTheory.DegVol.RefMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingRearrangePiProdMeasures
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem measurePreserving_rearrange (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V')
    (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type)
    [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w))
    [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ) (hb : ∀ i, 0 ≤ b i) (hc : ∀ w, 0 ≤ c w) :
    MeasurePreserving
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v)))
      (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) •
        (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν))
      (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  have hm : Measurable
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) := by
    fun_prop
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq_generateFrom
    (C := fun v => Set.image2 (· ×ˢ ·)
      (Set.pi Set.univ '' Set.pi Set.univ fun i => {s : Set (X i) | MeasurableSet s})
      {s : Set (Y (σ v)) | MeasurableSet s})
    (fun v => (generateFrom_eq_prod generateFrom_pi MeasurableSpace.generateFrom_measurableSet
      (IsCountablySpanning.pi fun _ => isCountablySpanning_measurableSet)
      isCountablySpanning_measurableSet))
    (fun _ => isPiSystem_pi.prod MeasurableSpace.isPiSystem_measurableSet)
    (fun v => (Measure.FiniteSpanningSetsIn.pi fun i =>
      (ENNReal.ofReal (b i) • m i).toFiniteSpanningSetsIn).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v)).toFiniteSpanningSetsIn) ?_).symm
  intro s hs
  choose t' ht' u hu hst using hs
  choose t ht htt using ht'
  have htm : ∀ v i, MeasurableSet (t v i) := fun v i => ht v i (Set.mem_univ _)
  have hs' : ∀ v, s v = (Set.pi Set.univ (t v)) ×ˢ u v := fun v => by rw [← hst v, htt v]
  have hsm : MeasurableSet (Set.pi Set.univ s) := by
    refine MeasurableSet.univ_pi fun v => ?_
    rw [hs' v]
    exact (MeasurableSet.univ_pi fun i => htm v i).prod (hu v)
  obtain ⟨u', hu'⟩ : ∃ u' : ∀ w, Set (Y w), ∀ v, u' (σ v) = u v :=
    ⟨Equiv.piCongrLeft (fun w => Set (Y w)) σ u, fun v => Equiv.piCongrLeft_apply_apply _ _ _ _⟩
  rw [Measure.map_apply hm hsm]
  have hpre : (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) ⁻¹'
      Set.pi Set.univ s =
      (Set.pi Set.univ fun i => Set.pi Set.univ fun v' => t (β.symm v') i) ×ˢ Set.pi Set.univ u' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, hs', Set.mem_prod, forall_and]
    refine and_congr ?_ ?_
    · rw [forall_comm]
      refine forall_congr' fun i => ?_
      rw [← β.forall_congr_right]
      simp only [Equiv.symm_apply_apply]
    · rw [← σ.forall_congr_right]
      simp only [hu']
  rw [hpre, Measure.smul_apply, Measure.prod_prod]
  simp only [hs', Measure.prod_prod, Measure.pi_pi, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have h1 : ∏ i, ∏ v', m i (t (β.symm v') i) = ∏ v, ∏ i, m i (t v i) := by
    rw [Finset.prod_comm]
    exact β.symm.prod_comp fun v => ∏ i, m i (t v i)
  have h2 : ∏ w, ν w (u' w) = ∏ v, ν (σ v) (u v) := by
    rw [← σ.prod_comp]
    simp only [hu']
  have h3 : ENNReal.ofReal (∏ w, c w) = ∏ v, ENNReal.ofReal (c (σ v)) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun w _ => hc w, ← σ.prod_comp]
  have h4 : ∏ i, ENNReal.ofReal (b i ^ Fintype.card V) = (∏ i, ENNReal.ofReal (b i)) ^ Fintype.card V := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_pow (hb i) _
  rw [h1, h2, h3, h4]
  ring

end GlobalTheory.LeviIso
end

