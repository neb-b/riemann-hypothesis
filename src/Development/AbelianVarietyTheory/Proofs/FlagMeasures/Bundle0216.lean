module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0195

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CwContIntegralComm
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CWIntegral

open PI.UpqRep GlobalTheory.CWDeriv

theorem exists_functional {S E : Type} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : S →ₗ[ℂ] E) (φ : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ s, ‖φ s‖ ≤ C * ‖T s‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ s, Λ (T s) = φ s := by
  have hker : LinearMap.ker T ≤ LinearMap.ker φ := by
    intro s hs
    rw [LinearMap.mem_ker] at hs ⊢
    have h1 := h s
    rw [hs, norm_zero, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  let ψ : LinearMap.range T →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ φ hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hψT : ∀ s, ψ ⟨T s, LinearMap.mem_range_self T s⟩ = φ s := by
    intro s
    have hq : T.quotKerEquivRange.symm ⟨T s, LinearMap.mem_range_self T s⟩ = (LinearMap.ker T).mkQ s :=
      LinearMap.quotKerEquivRange_symm_apply_image T s _
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hbd : ∀ y : LinearMap.range T, ‖ψ y‖ ≤ max C 0 * ‖y‖ := by
    rintro ⟨y, s, rfl⟩
    rw [hψT]
    calc ‖φ s‖ ≤ C * ‖T s‖ := h s
      _ ≤ max C 0 * ‖T s‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (LinearMap.range T) (ψ.mkContinuous (max C 0) hbd)
  refine ⟨Λ, fun s => ?_⟩
  have := hΛ ⟨T s, LinearMap.mem_range_self T s⟩
  rw [LinearMap.mkContinuous_apply, hψT] at this
  exact this

variable {k r : ℕ}

def linOn (R : Rep k r) {V : Type} [AddCommGroup V] [Module ℂ V] (B : R.H → V)
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, B (v + w) = B v + B w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, B (a • v) = a • B v) :
    R.smSub →ₗ[ℂ] V where
  toFun v := B v
  map_add' v w := ha _ v.2 _ w.2
  map_smul' a v := hs a _ v.2

theorem dsigW_smul {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (a : ℂ) (v : R.H) (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v) = a • dsigW (k := k) (r := r) R.σ W v := by
  revert hW
  induction W with
  | nil => intro _; rfl
  | cons X W ih =>
    intro hW
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem X hY)
    have hX : InLieHpk k r X := hW X (List.mem_cons_self ..)
    show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (a • v)) =
      a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)
    rw [ih hW']
    have hv' := dsigW_mem hD W hW' v hv
    have hd := ((hD X hX).1 _ hv').2.const_smul a
    have hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) (a • dsigW (k := k) (r := r) R.σ W v))
        (a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)) 0 := by
      simpa only [map_smul, Pi.smul_def] using hd
    exact hd'.deriv

theorem dsigW_add {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (v : R.H) (hv : v ∈ R.sm) (w : R.H) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (v + w) =
      dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w := by
  revert hW
  induction W with
  | nil => intro _; rfl
  | cons X W ih =>
    intro hW
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem X hY)
    have hX : InLieHpk k r X := hW X (List.mem_cons_self ..)
    show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (v + w)) =
      dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) +
        dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)
    rw [ih hW']
    have hv' := dsigW_mem hD W hW' v hv
    have hw' := dsigW_mem hD W hW' w hw
    have hd := ((hD X hX).1 _ hv').2.add ((hD X hX).1 _ hw').2
    have hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X))
        (dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w))
        (dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) +
          dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)) 0 := by
      simpa only [map_add (f := _), Pi.add_def] using hd
    exact hd'.deriv

theorem dsigW_integral {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → R.H) (hf : ∀ x, f x ∈ R.sm)
    (hi : Integrable f μ) (hi' : Integrable (fun x => dsigW (k := k) (r := r) R.σ W (f x)) μ)
    (hu : (∫ x, f x ∂μ) ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (∫ x, f x ∂μ) = ∫ x, dsigW (k := k) (r := r) R.σ W (f x) ∂μ := by
  have hmem : ∀ x, dsigW (k := k) (r := r) R.σ W (f x) ∈ R.smSub := fun x => dsigW_mem hD W hW _ (hf x)
  have hcl : ((R.smSub.topologicalClosure : Submodule ℂ R.H) : Set R.H) = closure R.sm :=
    Submodule.topologicalClosure_coe _
  have hy : (∫ x, dsigW (k := k) (r := r) R.σ W (f x) ∂μ) ∈ R.smSub.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro z hz
    rw [← integral_inner hi']
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    exact Submodule.inner_left_of_mem_orthogonal (hmem x) hz
  have hd : dsigW (k := k) (r := r) R.σ W (∫ x, f x ∂μ) ∈ R.smSub := dsigW_mem hD W hW _ hu
  refine sub_eq_zero.mp (eq_zero_of_closure ?_ ?_)
  · rw [← hcl]
    exact Submodule.sub_mem _ (R.smSub.le_topologicalClosure hd) hy
  · intro w hw
    obtain ⟨w', hw'⟩ := dsigW_adjoint hD W hW w hw
    rw [inner_sub_right, hw' _ hu, ← integral_inner hi, ← integral_inner hi', sub_eq_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (hw' _ (hf x)).symm

end GlobalTheory.CWIntegral

namespace GlobalTheory

open PI.UpqRep GlobalTheory.CWDeriv GlobalTheory.CWIntegral

theorem cwCont_integral_comm : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (κ : X → Mx k r) (p : X → ℂ), Continuous κ → (∀ x, κ x ∈ GG k r) → Continuous p → ∀ v ∈ R.sm, (∫ x, p x • R.σ (κ x) v ∂μ) ∈ R.sm → Bm (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, p x • Bm (R.σ (κ x) v) ∂μ := by
  intro hKS k r ε mu R hR V indexVFirst indexVSecond indexVThird indexVFourth Bm hadd hsmul hcw X iX1 iX2 iX3 iX4 iX5 μ iμ κ p hκ hκG hp v hv hu
  have hD : DerFacts R := fun Y hY =>
    ⟨(GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).1, (GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).2.2.2.2⟩
  have hσ : ∀ x, R.σ (κ x) v ∈ R.sm := fun x => (rep_basic_of_isDS hKS k r ε mu R hR).2.2.2.1 _ (hκG x) v hv
  have hf : ∀ x, p x • R.σ (κ x) v ∈ R.sm := fun x => R.smSub.smul_mem (p x) (hσ x)
  have hint : ∀ {E : Type} [NormedAddCommGroup E] (g : X → E), Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport g) (Set.subset_univ _))
  have hcW : ∀ W : List (Mx k r), (∀ Y ∈ W, InLieHpk k r Y) →
      Continuous (fun x => PI.UpqRep.dsigW (k := k) (r := r) R.σ W (R.σ (κ x) v)) := fun W hW =>
    (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW)).comp_continuous hκ hκG
  have hBc : Continuous (fun x => Bm (R.σ (κ x) v)) :=
    (cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1.comp_continuous hκ hκG
  obtain ⟨C, Ws, hWs, hB⟩ := hcw
  have hWi : ∀ i : Fin Ws.length, ∀ Y ∈ Ws.get i, InLieHpk k r Y := fun i => hWs _ (List.get_mem Ws i)
  let T : R.smSub →ₗ[ℂ] (Fin Ws.length → R.H) :=
    linOn R (fun u i => PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) u)
      (fun a ha b hb => funext fun i => dsigW_add hD _ (hWi i) a ha b hb)
      (fun c a ha => funext fun i => dsigW_smul hD _ (hWi i) c a ha)
  refine ext_inner_left ℂ (fun e => ?_)
  let φ : R.smSub →ₗ[ℂ] ℂ := (innerSL ℂ e : V →L[ℂ] ℂ).toLinearMap.comp (linOn R Bm hadd hsmul)
  have hφ : ∀ s, φ s = ⟪e, Bm s⟫_ℂ := fun s => rfl
  have hbound : ∀ s, ‖φ s‖ ≤ (‖e‖ * (|C| * Ws.length)) * ‖T s‖ := by
    intro s
    have h1 : ‖Bm s‖ ≤ C * (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum := hB s s.2
    have h2 : (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum ≤ Ws.length * ‖T s‖ := by
      have h3 := List.sum_le_card_nsmul (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖) ‖T s‖
        (by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
          obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
          exact norm_le_pi_norm (T s) i)
      rwa [List.length_map, nsmul_eq_mul] at h3
    have h0 : 0 ≤ (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum :=
      List.sum_nonneg (fun y hy => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hy
        exact norm_nonneg _)
    have h4 : ‖Bm s‖ ≤ |C| * (Ws.length * ‖T s‖) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) h0).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    rw [hφ]
    calc ‖⟪e, Bm s⟫_ℂ‖ ≤ ‖e‖ * ‖Bm s‖ := norm_inner_le_norm _ _
      _ ≤ ‖e‖ * (|C| * (Ws.length * ‖T s‖)) := mul_le_mul_of_nonneg_left h4 (norm_nonneg e)
      _ = (‖e‖ * (|C| * Ws.length)) * ‖T s‖ := by ring
  obtain ⟨Λ, hΛ⟩ := exists_functional T φ _ hbound
  let F : X → (Fin Ws.length → R.H) := fun x i =>
    p x • PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (R.σ (κ x) v)
  have hFi : Integrable F μ := hint F (continuous_pi fun i => hp.smul (hcW _ (hWi i)))
  have hTu : T ⟨_, hu⟩ = ∫ x, F x ∂μ := by
    funext i
    have hpi := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin Ws.length => R.H) i).integral_comp_comm hFi
    simp only [ContinuousLinearMap.proj_apply] at hpi
    rw [← hpi]
    show PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, F x i ∂μ
    have hi0 : Integrable (fun x => p x • R.σ (κ x) v) μ := hint _ (hp.smul (hcW [] (by simp)))
    have hi1 : Integrable (fun x => PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (p x • R.σ (κ x) v)) μ :=
      (hint _ (hp.smul (hcW _ (hWi i)))).congr
        (Filter.Eventually.of_forall fun x => (dsigW_smul hD _ (hWi i) (p x) _ (hσ x)).symm)
    rw [dsigW_integral hD _ (hWi i) μ _ hf hi0 hi1 hu]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => dsigW_smul hD _ (hWi i) (p x) _ (hσ x))
  calc ⟪e, Bm (∫ x, p x • R.σ (κ x) v ∂μ)⟫_ℂ = φ ⟨_, hu⟩ := (hφ ⟨_, hu⟩).symm
    _ = Λ (T ⟨_, hu⟩) := (hΛ ⟨_, hu⟩).symm
    _ = Λ (∫ x, F x ∂μ) := by rw [hTu]
    _ = ∫ x, Λ (F x) ∂μ := (Λ.integral_comp_comm hFi).symm
    _ = ∫ x, ⟪e, p x • Bm (R.σ (κ x) v)⟫_ℂ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hF : F x = p x • T ⟨_, hσ x⟩ := rfl
        show Λ (F x) = ⟪e, p x • Bm (R.σ (κ x) v)⟫_ℂ
        rw [hF, map_smul, hΛ, hφ, inner_smul_right, smul_eq_mul]
    _ = ⟪e, ∫ x, p x • Bm (R.σ (κ x) v) ∂μ⟫_ℂ := integral_inner (hint _ (hp.smul hBc)) e

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EuclideanBallAsymptoticsFinitePi
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem IsRadial.comp_measurableEquiv {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) {q : X → ℝ} {p : Y → ℝ} {d : ℕ}
    (hq : ∀ x, q x = p (e x)) (h : IsRadial ν p d) : IsRadial μ q d := by
  unfold IsRadial at *
  refine h.congr fun r => ?_
  rw [← he.measure_preimage_equiv]
  simp only [hq, Set.preimage_ofPred_eq]

theorem isRadial_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) →
    (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) →
    IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  intro a
  induction a with
  | zero =>
    intro X _ μ _ q d _ _ _
    rw [Fin.sum_univ_zero]
    unfold IsRadial
    rw [volume_euclideanSpace_eq_dirac, Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    rw [Measure.pi_of_empty, Measure.dirac_apply_of_mem (by simpa using hr')]
    simp
  | succ a ih =>
    intro X _ μ _ q d hm h0 hr
    have h := _root_.GlobalTheory.LeviIso.isRadial_prod _ _ (μ 0) (Measure.pi fun j => μ (Fin.succAbove 0 j)) (q 0)
      (fun x => ∑ j, q (Fin.succAbove 0 j) (x j)) (d 0) (∑ j, d (Fin.succAbove 0 j)) (hm 0)
      (Finset.measurable_sum _ fun j _ => (hm _).comp (measurable_pi_apply j)) (h0 0)
      (fun y => Finset.sum_nonneg fun j _ => h0 _ _) (hr 0)
      (ih _ _ _ _ (fun j => hm _) (fun j => h0 _) fun j => hr _)
    rw [Fin.sum_univ_succAbove d 0]
    exact h.comp_measurableEquiv _ (measurePreserving_piFinSuccAbove μ 0)
      fun x => Fin.sum_univ_succAbove (fun i => q i (x i)) 0

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBiorthogonalFrameOfSaturatedFlagStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biorthogonal_frame_of_saturated_flag : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ), Monotone F → F 0 = ⊥ → (∀ b, m ≤ b → F b = F m) → Submodule.IsFullLattice E (F m) → (∀ b, ∀ y ∈ F m, y ∈ Submodule.span E (F b : Set (Fin n → E)) → y ∈ F b) → (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) → ∃ (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' ∧ (∀ b, Submodule.IsFullLattice E (Λ b)) ∧ ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0) := by
  first
  | exact @GlobalTheory.RadCov.exists_biorth_of_saturated_flag
  | intro E _ _ n m F r hmono h0 hm hL hsat hrk
    obtain ⟨T, T', Λ, hB, hΛ, hmem⟩ :=
      GlobalTheory.RadCov.exists_biorth_of_saturated_flag E n m F r hmono h0 hm
        hL.toIsLattice hsat hrk
    refine ⟨T, T', Λ, hB, ?_, hmem⟩
    intro b
    let : Submodule.IsLattice E (Λ b) := hΛ b
    refine { span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro v _
    have hle : Submodule.span E (F m : Set (Fin n → E)) ≤
        (Submodule.span E (Λ b : Set (Fin (r b) → E))).comap (T' b).mulVecLin := by
      apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span ((hmem m x).1 hx b).1
    have hx : T' b *ᵥ (T b *ᵥ v) ∈ Submodule.span E (Λ b : Set (Fin (r b) → E)) :=
      hle (by rw [hL.span_eq_top]; trivial)
    rw [Matrix.mulVec_mulVec, hB.1 b, Matrix.one_mulVec] at hx
    exact hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlace
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem star_dot_Jm {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = (qEps ε x : ℂ) := by
  unfold qEps Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (starRingEnd ℂ) (x i) * x i = ((‖x i‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' (x i)
  split_ifs
  · simp [hi]
  · simp [hi]

theorem realUJ_eq {n : ℕ} (ε : Fin n → Bool) :
    Formalism.UG.UJ (starRingEnd ℂ) (Formalism.REAL.Jm ε) = Formalism.REAL.UJ ε := by
  unfold Formalism.REAL.UJ Formalism.UG.UJ Formalism.REAL.inUJ
  have hc : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro M
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  ext g
  change Formalism.UG.cT (starRingEnd ℂ) (g : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε ↔
    (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [hc]

theorem exists_closedEmbedding_unitary_orthogonal (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool)
    (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (hn : m + 1 = n) (hq : qEps ε x₀ = sgn ℝ s)
    (hx : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0) (hB : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧
      ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  unfold uMat
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    rw [diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  have hdet : (Formalism.REAL.Jm ε').det ≠ 0 := by
    unfold Formalism.REAL.Jm
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by by_cases h : ε' a <;> simp [h]
  have hβ : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0 := by
    rw [star_dot_Jm, hq]
    cases s <;> simp [sgn]
  obtain ⟨u, A', hA'B, hA'x, huB, hux, hres, hBJx⟩ :=
    exists_dual_of_anisotropic_orthogonal ℂ n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ B hn hJh hdet hβ hx hB
  have hcT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ), Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro p q M
    ext i k
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  have hstar : (fun i => starRingEnd ℂ (x₀ i)) = star x₀ := by
    funext i
    simp [Complex.star_def]
  obtain ⟨j, hjmat, hjrange⟩ := _root_.GlobalTheory.StabRing.exists_emb ℂ (starRingEnd ℂ) n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ u B A'
    (by rw [hstar]; exact isUnit_iff_ne_zero.mpr hβ) (by rw [hstar]; exact hx) (by rw [hcT]; exact hBJx)
    (by rw [hcT]; exact hB) hA'B hA'x huB hux hres
  obtain ⟨jj, hjj, hrange⟩ : ∃ jj : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε,
      (∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        vecMulVec x₀ u + B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A') ∧
      ∀ h : Formalism.REAL.UJ ε, ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ → ∃ g, jj g = h := by
    refine ⟨(MulEquiv.subgroupCongr (realUJ_eq ε)).toMonoidHom.comp
      (j.comp (MulEquiv.subgroupCongr (realUJ_eq ε')).symm.toMonoidHom), fun g => hjmat _, ?_⟩
    intro h hh
    obtain ⟨g', hg'⟩ := hjrange ((MulEquiv.subgroupCongr (realUJ_eq ε)).symm h) hh
    refine ⟨MulEquiv.subgroupCongr (realUJ_eq ε') g', ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hg'
  have h0 : vecMulVec x₀ u * B = 0 := by
    ext i k
    have hk := congrFun huB k
    simp only [vecMul, dotProduct, Pi.zero_apply] at hk
    change (∑ j, (x₀ i * u j) * B j k) = 0
    simp only [mul_assoc, ← Finset.mul_sum, hk, mul_zero]
  have hv : vecMulVec x₀ u *ᵥ x₀ = x₀ := by
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum]
    rw [show ∑ k, u k * x₀ k = 1 from hux, mul_one]
  have hfix : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ := by
    intro g
    rw [hjj, add_mulVec, hv, ← mulVec_mulVec, hA'x, mulVec_zero, add_zero]
  have hcomm : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B =
      B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
    intro g
    rw [hjj, Matrix.add_mul, h0, zero_add, Matrix.mul_assoc (B * _), hA'B, Matrix.mul_one]
  have hback : ∀ M : Matrix (Fin m) (Fin m) ℂ, A' * (vecMulVec x₀ u + B * M * A') * B = M := by
    intro M
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc A' (vecMulVec x₀ u), h0, Matrix.mul_zero, zero_add,
      Matrix.mul_assoc, Matrix.mul_assoc, hA'B, Matrix.mul_one, ← Matrix.mul_assoc, hA'B, Matrix.one_mul]
  have hval' : Continuous fun g : Formalism.REAL.UJ ε' => ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hinv' : Continuous fun g : Formalism.REAL.UJ ε' => (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hjinv : ∀ g, ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      vecMulVec x₀ u + B * (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A' := by
    intro g
    have h1 := hjj g⁻¹
    rw [map_inv] at h1
    exact h1
  have hcont : Continuous jj := by
    refine continuous_induced_rng.2 ?_
    rw [Units.continuous_iff]
    constructor
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hval').matrix_mul continuous_const))
        fun g => (hjj g).symm
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hinv').matrix_mul continuous_const))
        fun g => (hjinv g).symm
  let ψ : Formalism.REAL.UJ ε → Matrix (Fin m) (Fin m) ℂ × (Matrix (Fin m) (Fin m) ℂ)ᵐᵒᵖ := fun h =>
    (A' * ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B,
      MulOpposite.op (A' * (((h : GL (Fin n) ℂ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B))
  have hψc : Continuous ψ := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
        continuous_const
    · exact MulOpposite.continuous_op.comp ((continuous_const.matrix_mul
        (Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_mul continuous_const)
  have hψ : ∀ g, ψ (jj g) = Units.embedProduct _ (g : GL (Fin m) ℂ) := by
    intro g
    refine Prod.ext ?_ ?_
    · show A' * ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B = ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjj, hback]
    · show MulOpposite.op (A' * ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B) =
        MulOpposite.op ((((g : GL (Fin m) ℂ))⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjinv, hback]
  have hind : Topology.IsInducing jj := by
    refine Topology.IsInducing.of_comp hcont hψc ?_
    have he : ψ ∘ jj = fun g : Formalism.REAL.UJ ε' => Units.embedProduct _ (g : GL (Fin m) ℂ) := funext hψ
    rw [he]
    exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  have hinj : Function.Injective jj := by
    intro a b hab
    have hc := congrArg ψ hab
    rw [hψ, hψ] at hc
    exact Subtype.ext (Units.ext (congrArg Prod.fst hc))
  have hrng : Set.range jj = {h : Formalism.REAL.UJ ε | ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀} := by
    ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact hfix g
    · intro hh
      exact hrange h hh
  have hclosed : IsClosed (Set.range jj) := by
    rw [hrng]
    exact isClosed_eq ((Units.continuous_val.comp continuous_subtype_val).matrix_mulVec continuous_const)
      continuous_const
  exact ⟨jj, ⟨⟨hind, hinj⟩, hclosed⟩, fun g => ⟨hfix g, hcomm g⟩⟩

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainEmbeddedRowsLatticeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_embeddedRowsLattice : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → ∃ P : Set (VecInf E k), MeasurableSet P ∧ volume P = ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) ∧ (∀ T : VecInf E k, ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ (fun w b => T w b + w.embedding (τ b)) ∈ P) ∧ ∀ (T : VecInf E k) (τ : Fin k → E), (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) → T ∈ P → (fun w b => T w b + w.embedding (τ b)) ∈ P → τ = 0 := by
  intro E _ _ hE k Λ₀ Λ' h₀ h'
  first
  | exact GlobalTheory.RowDomain.rowDomain E hE k Λ₀ Λ' h₀ h'
  | exact GlobalTheory.RowDomain.rowDomain E hE k Λ₀ Λ' h₀.toIsLattice h'.toIsLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermitianSqrtInSignedUnitaryGroupStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_sqrt_in_signedUnitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin n) ℂ), C.det ≠ 0 → (Cᴴ * C) * Formalism.REAL.Jm ε * (Cᴴ * C) = Formalism.REAL.Jm ε → ∃ s : Formalism.REAL.UJ ε, (uMat s)ᴴ = uMat s ∧ uMat s * uMat s = Cᴴ * C := by
  first | exact @GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ | exact GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ | (intros; apply GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableUnitaryLeviBlockMapStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_unitaryLeviBlockMap : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∃ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ ∧ ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
  first | exact @GlobalTheory.LeviIso.exists_measurable_levMap | exact GlobalTheory.LeviIso.exists_measurable_levMap | (intros; apply GlobalTheory.LeviIso.exists_measurable_levMap <;> assumption)
end

