module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationDegenerateSidePieceBound
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.DegSide

variable {k r : ℕ}

theorem measurableSet_GG : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  simpa [Set.compl_setOf] using (WUnfold.measurableSet_not_GG (k := k) (r := r)).compl

theorem measurable_indicator_GG {β : Type} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [Zero β]
    {f : Mat k r → β} (hf : ContinuousOn f (GG k r)) :
    Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => f (Matrix.of x)) := by
  classical
  have h : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} := hf
  have := h.measurable_piecewise (g := fun _ => (0 : β)) continuousOn_const measurableSet_GG
  rwa [← Set.piecewise_eq_indicator]

theorem measurable_mulP : Measurable fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := by
  have : Continuous fun p : Mat k r × Mat k r => p.1 * p.2 := continuous_fst.matrix_mul continuous_snd
  have h : Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := this
  exact h.measurable

theorem measurable_conjM (h : Mat k r) : Measurable (conjM h : Mt k r → Mt k r) := by
  have : Continuous fun x : Mat k r => h * x * h⁻¹ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h' : Continuous (conjM h : Mt k r → Mt k r) := this
  exact h'.measurable

theorem null_of_fibres {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN ν : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN) (hq : IsQuotMeas μG (muProd μW μN) ν)
    {A : Set (Mt k r)} (hA : MeasurableSet A) (h0 : ∀ g : Mat k r, μN (rmulM g ⁻¹' A) = 0) : μG A = 0 := by
  haveI := hN.1
  have hconj : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN :=
    (GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW μN hz hT hW hN).2.2.2.2
  have hm : Measurable (A.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, hq _ hm]
  refine (lintegral_congr fun x => ?_).trans lintegral_zero
  have hx : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  show ∫⁻ s, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) ∂(muProd μW μN) = 0
  unfold muProd
  rw [lintegral_map hx measurable_mulP, lintegral_prod (fun p : Mt k r × Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of p.1) p.2)))
      (hx.comp measurable_mulP).aemeasurable]
  have haeW : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := hW.2.2.1
  refine (lintegral_congr_ae (haeW.mono fun h hh => ?_)).trans lintegral_zero
  have hg : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of h * Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  have e : ∀ n : Mt k r, rmulM (Matrix.of x) (lmulM (Matrix.of h) n) =
      rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n) := by
    intro n
    show (Matrix.of h * Matrix.of n * Matrix.of x : Mat k r) =
      Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
    rw [Matrix.mul_assoc (Matrix.of h * Matrix.of n : Mat k r),
      Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hh.1)]
  show ∫⁻ n, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of h) n)) ∂μN = 0
  simp only [e]
  rw [← lintegral_map hg (measurable_conjM _), hconj _ hh, ← h0 (Matrix.of h * Matrix.of x),
    ← lintegral_indicator_one ((continuous_rmulM _).measurable hA)]
  rfl

theorem mem_Sset_of_mem_Nset (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg2_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {s x : Mat k r}
    (hs : s ∈ Sset k r z) (hx : x ∈ GG k r) : Sg2 k r z (s * x) = Sg2 k r z x := by
  have := (_root_.GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.1 x hx s hs 1 ⟨isClosedSub_GG.2.2.1, one_mem _⟩
  rwa [Matrix.mul_one] at this

theorem tail {Wq : Type} [NormedAddCommGroup Wq] {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {ν : Measure (Mt k r)} {Φ : Mat k r → Wq} {q : ℕ} {H₁ : ℝ} (hH : 1 ≤ H₁) (ht : TailBd z ν Φ q H₁) (i : ℕ)
    {Q : Set (Mt k r)} (hQ : MeasurableSet Q) (hsub : ∀ x ∈ Q, i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z (Matrix.of x)) :
    ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤
      ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG ν Φ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine (setLIntegral_le_lintegral _ _).trans (le_mul_of_one_le_left zero_le ?_)
    rw [ENNReal.one_le_ofReal]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one]
    linarith
  · have h2 : (0 : ℝ) < 2 ^ i := by positivity
    have h := ht (2 ^ i) h2
    have e : 2 * (2 * r + 2 : ℝ) * (2 ^ i : ℝ) ^ (-(2 * (q : ℝ))) = (4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹ := by
      rw [Real.rpow_neg h2.le, ← Real.rpow_natCast (2 ^ i : ℝ) (2 * q)]
      push_cast
      ring
    rw [e] at h
    refine le_trans ?_ h
    rw [← lintegral_indicator hQ]
    refine lintegral_mono (Set.indicator_le_indicator_of_subset (fun x hx => ?_) fun _ => zero_le)
    have hx' := (hsub x hx).resolve_left hi.ne'
    have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
    rcases ((_root_.GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.2.2 (Matrix.of x)).2.2.2 with h' | ⟨a, ha⟩
    · exfalso
      rw [h'] at hx'
      nlinarith
    · exact ⟨a, ha ▸ hx'.le⟩

theorem side_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yj k r hj z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset0 k r hj z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol0 k r j R₀ De y * ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  intro k r j hj z z' Wq _ _ _ π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hjk hκ hs hH hO ht hDe hNR hqR
  have hO' := hO
  obtain ⟨hz', hT', hnt, hπ, -, hG, hW, -, hN, hqS, hψ, hΦ, hΦc, hc, hl2⟩ := hO'
  have hz := hNR.1
  have hT := hNR.2.2.1
  obtain ⟨hγ, hRc, hRh, hRu, -⟩ := _root_.GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' γ s μR hs hNR
  obtain ⟨hoff, hnull, φ, hφ, hcut⟩ := _root_.GlobalTheory.Amp.CutQuot.cut_quotient k r _ μG μR νR hRc hG hRh hRu hqR
  have hV := _root_.GlobalTheory.Amp.FibreVolume.fibre_volume k r j hj z z' γ De s μR hj1 hjk hDe hs hNR
  obtain ⟨hYm, hEm⟩ := _root_.GlobalTheory.Amp.YMeas.yj_measurable k r j hj z z' γ hz hz' hT hT' hγ
  have hYi : ∀ ρ ∈ Rset k r γ, ∀ x ∈ GG k r, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x :=
    fun ρ hρ x hx => (_root_.GlobalTheory.Amp.YjInv.yj_invariant k r j hj z z' γ hz hz' hγ x hx).2.2 ρ hρ
  have hmul : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := isClosedSub_GG.2.2.2.1
  refine ⟨?_, fun w hw i R₀ y hR hy => ?_⟩
  · set A : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (Matrix.of x) = 0} with hAdef
    have hA : MeasurableSet A := by
      have := measurableSet_GG.inter (hYm (measurableSet_singleton 0))
      convert this using 1
      ext x
      refine and_congr_right fun hx => ?_
      rw [Set.mem_preimage, Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
      rfl
    have hA0 : μG A = 0 := by
      refine null_of_fibres hz' hT' hW hN hqS hA fun g => ?_
      by_cases hg : g ∈ GG k r
      · rw [Measure.smul_apply, measure_mono_null (s := rmulM g ⁻¹' A) (t := {n | Yj k r hj z z' γ (Matrix.of n * g) = 0}) (fun n hn => hn.2)
          (hV g hg).1, smul_zero]
      · refine measure_mono_null (t := {x | Matrix.of x ∉ Nset k r}) (fun n hn hn' => hg ?_) hN.2.2.1
        exact (WUnfold.mul_mem_GG_iff hn'.1).1 hn.1
    have hA1 : νR A = 0 := by
      refine hnull A hA (fun ρ hρ x hx => ?_) hA0
      show (ρ * Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (ρ * Matrix.of x) = 0) ↔ (_ ∧ _)
      rw [hYi ρ hρ _ hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hoff hA1)
    by_cases hx' : Matrix.of x ∈ GG k r
    · exact Or.inr ⟨hx', hx.resolve_left (not_not.2 hx')⟩
    · exact Or.inl hx'
  · set E := Eset0 k r hj z z' γ R₀ y with hE
    set Q : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x))} with hQdef
    have hQ : MeasurableSet Q := by
      have h1 := measurable_indicator_GG (_root_.GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z' hz' hT').2.2.1
      have h2 := measurableSet_GG.inter ((MeasurableSet.const (i = 0)).union (measurableSet_lt
        (measurable_const (a := 2 ^ i * H₁)) h1))
      convert h2 using 1
      ext x
      refine and_congr_right fun hx => ?_
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rw [Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
    have hEQ : E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)} = E ∩ Q := by
      ext x
      exact and_congr_right fun hx => ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩
    have hQi : ∀ s ∈ Sset k r z', ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q) := by
      intro s hs x hx
      show (s * Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (s * Matrix.of x))) ↔ (_ ∧ _)
      rw [Sg2_left hz' hT' hs hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ (WUnfold.Sset_subset _ hs) _ hx, h.2⟩⟩
    have hEi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ E ↔ x ∈ E) := by
      intro ρ hρ x hx
      show (ρ * Matrix.of x ∈ GG k r ∧ Sg2 k r z' (ρ * Matrix.of x) ≤ R₀ ∧ Sg2 k r z (γ * (ρ * Matrix.of x)) ≤ R₀ ∧
        y < Yj k r hj z z' γ (ρ * Matrix.of x) ∧ Yj k r hj z z' γ (ρ * Matrix.of x) ≤ 2 * y) ↔ (_ ∧ _)
      have e : γ * (ρ * Matrix.of x) = γ * ρ * γ⁻¹ * (γ * Matrix.of x) := by
        rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hγ), Matrix.mul_assoc]
      rw [hYi ρ hρ _ hx, Sg2_left hz' hT' (mem_Sset_of_mem_Nset _ hρ.1) hx, e,
        Sg2_left hz hT (mem_Sset_of_mem_Nset _ hρ.2) (hmul _ hγ _ hx)]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    set g : Mt k r → ℝ≥0∞ := fun x => (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 with hg
    have hgi : ∀ ρ ∈ Nset k r, ∀ x, Matrix.of x ∈ GG k r → g (lmulM ρ x) = g x := by
      intro ρ hρ x hx
      have h1 := hΦ 1 (isClosedSub_UWset z').2.2.1 ρ hρ _ hx
      rw [Matrix.one_mul, hπ.1.1] at h1
      have h2 : ‖ψ' ρ‖₊ = 1 := NNReal.eq (hψ ρ hρ)
      show (‖⟪w, Φ' (ρ * Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 = _
      rw [h1, inner_smul_right, nnnorm_mul, h2, one_mul]
      rfl
    have hFm : Measurable ((E ∩ Q).indicator g) := by
      have h1 : ContinuousOn (fun x : Mat k r => (‖⟪w, Φ' x⟫_ℂ‖₊ : ℝ≥0∞) ^ 2) (GG k r) :=
        (ENNReal.continuous_pow 2).comp_continuousOn
          (ENNReal.continuous_coe.comp_continuousOn (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const hΦc).nnnorm)
      have h2 := (measurable_indicator_GG h1).indicator ((hEm R₀ y).inter hQ)
      rwa [Set.indicator_indicator, (Set.inter_eq_left (t := {x : Mt k r | Matrix.of x ∈ GG k r})).2
        (fun x (hx : x ∈ E ∩ Q) => hx.2.1)] at h2
    have hFi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r →
        (E ∩ Q).indicator g (lmulM ρ x) = (E ∩ Q).indicator g x := by
      intro ρ hρ x hx
      have hiff : lmulM ρ x ∈ E ∩ Q ↔ x ∈ E ∩ Q :=
        and_congr (hEi ρ hρ x hx) (hQi ρ (mem_Sset_of_mem_Nset _ hρ.1) x hx)
      by_cases h : x ∈ E ∩ Q
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.2 h), hgi ρ hρ.1 x hx]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.1 h)]
    have hP := _root_.GlobalTheory.Amp.OnePiece.one_piece k r z' π' ψ' μG μW' _ νS' Φ' c hO (fun x => φ x * E.indicator 1 x) Q
      (ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s))
      (hφ.1.mul (measurable_one.indicator (hEm R₀ y))) hQ hQi (fun g hg => by
        rw [lintegral_smul_measure, smul_eq_mul]
        exact mul_le_mul_right ((hV g hg).2 φ hφ R₀ y hR hy) _) w hw
    have hTl := tail hz' hT' hH ht i (Q := Q) hQ fun x hx => hx.2
    have hfib : 0 ≤ fibVol0 k r j R₀ De y := by
      have := hDe.1
      unfold fibVol0
      positivity
    have hd : (0 : ℝ) < Module.finrank ℂ Wq := Nat.cast_pos.2 Module.finrank_pos
    calc ∫⁻ x in E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)},
          ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR
        = ∫⁻ x, (E ∩ Q).indicator g x ∂νR := by
          rw [hEQ, lintegral_indicator ((hEm R₀ y).inter hQ)]
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
          rfl
      _ = ∫⁻ x in Q, φ x * E.indicator 1 x * g x ∂μG := by
          rw [hcut _ hFm hFi, ← lintegral_indicator hQ]
          refine lintegral_congr fun x => ?_
          by_cases h1 : x ∈ E <;> by_cases h2 : x ∈ Q <;> simp [h1, h2]
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s) * (Module.finrank ℂ Wq : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS' Φ') :=
          hP.trans (mul_le_mul_right hTl _)
      _ = _ := by
          rw [hl2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hd, ← ENNReal.ofReal_mul hκ.le,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp

end GlobalTheory.Amp.DegSide
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivity
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpNormal

theorem det_hpk (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

noncomputable def lmulEquiv {k r : ℕ} (t : MatKR k r) (ht : IsUnit t.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (t⁻¹ * Matrix.of x) i j
  invFun x := fun i j => (t * Matrix.of x) i j
  left_inv x := by
    show t * (t⁻¹ * Matrix.of x) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
  right_inv x := by
    show t⁻¹ * (t * Matrix.of x) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.one_mul]
  measurable_toFun := by
    have : Continuous fun x : MatKR k r => t⁻¹ * x := continuous_const.matrix_mul continuous_id
    exact Continuous.measurable (f := fun x : Mt k r => (fun i j => (t⁻¹ * Matrix.of x) i j : Mt k r)) this
  measurable_invFun := by
    have : Continuous fun x : MatKR k r => t * x := continuous_const.matrix_mul continuous_id
    exact Continuous.measurable (f := fun x : Mt k r => (fun i j => (t * Matrix.of x) i j : Mt k r)) this

theorem one_side (hH : Hyps) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ}
    {μW μN μG νq : Measure (Mt k r)} {B l : R.H → Wp} {w : R.H} {dd m : ℝ}
    (hds : R.IsDS ε mu) (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hS : SideG k r z π u μW μN μG νq) (hc : c ≠ 0)
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B)
    (hl : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l)
    (hbe : ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hw : R.KFin w) (hm : 0 < m)
    (hmass : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) = ENNReal.ofReal m)
    (hd0 : 0 < dd) (hdd : ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) :
    (∃ v, R.KFin v ∧ l v ≠ 0) ∧ ∃ β : ℂ, (∀ v ∈ R.sm, B v = β • l v) ∧ m * dd = ‖β‖ ^ 2 * ‖w‖ ^ 2 := by
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hmul, hone, hinn, hsm, hTKsm, hTK, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hKF k r ε mu R hds
  obtain ⟨hG1, hGm, hGi⟩ := uHGroup _ _ (det_hpk k r)
  obtain ⟨t, ht, hN, hz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, hcomm, hpsi⟩ := hz z hS.1
  have htd : IsUnit t.det := (hGi t ht).1
  have hti : t⁻¹ ∈ GG k r := (hGi t ht).2
  have hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ := by
    refine ⟨⟨ContinuousLinearMap.ext hone, fun a ha b hb => ContinuousLinearMap.ext (hmul a ha b hb)⟩, fun g hg v => ?_,
      hcont⟩
    rw [@norm_eq_sqrt_re_inner ℂ, hinn g hg, ← @norm_eq_sqrt_re_inner ℂ]
  have e1 : ∀ v, R.σ t⁻¹ (R.σ t v) = v := fun v => by
    rw [← hmul _ hti _ ht, Matrix.nonsing_inv_mul _ htd, hone]
  have e2 : ∀ v, R.σ t (R.σ t⁻¹ v) = v := fun v => by
    rw [← hmul _ ht _ hti, Matrix.mul_nonsing_inv _ htd, hone]
  obtain ⟨hS', hR⟩ := GlobalTheory.BesselMove.bessel_move hH k r Wp z π u c μW μN μG νq t ht hN hcomm hpsi hS
  obtain ⟨hbes, hmove⟩ := hR R hU
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.exists_normalised_bessel_map hH k r ε mu h R Wp z π u μW _ μG _ hds hgap hok hS'
  have hl₂ : IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) (fun v => l (R.σ t v)) := by
    refine ⟨(hbes l).1 hl, fun x hx v hv => ⟨(hl₁.2 x hx v hv).1, ?_⟩⟩
    rw [(hl₁.2 x hx v hv).2, ← hbe _ (hsm t ht x hx) _ (hTK t ht v hv),
      hmove l₁ hl₁ _ (hsm t ht x hx) _ (hTK t ht v hv), e1, e1]
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r :=
    (GlobalTheory.quotMeas_ae_mem_and_measurable hKF k r ε mu R Wp z π u μW μN μG νq hds hS).1
  have htr : ∀ F : R.H → Wp,
      PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) (fun g => F (R.σ t (R.σ g w))) =
        PI.BesselPeriodGGP.l2SG νq (fun g => F (R.σ g w)) := by
    intro F
    unfold PI.BesselPeriodGGP.l2SG
    refine (lintegral_map_equiv _ (lmulEquiv t htd)).trans (lintegral_congr_ae ?_)
    filter_upwards [hae] with x hx
    have : R.σ t (R.σ (Matrix.of (lmulEquiv t htd x)) w) = R.σ (Matrix.of x) w := by
      show R.σ t (R.σ (t⁻¹ * Matrix.of x) w) = _
      rw [hmul _ hti _ hx, e2]
    simp only [this]
  have hB₁ : IsBes R z π (fun v => B (R.σ t v)) := (hbes B).1 hB
  obtain ⟨v, hv, hv0⟩ := _root_.GlobalTheory.BesselPeriodNonzero.exists_kFin_period_ne_zero hH k r ε mu h R Wp z π u μW _ μG _ (fun v => B (R.σ t v))
    (fun v => l (R.σ t v)) w hds hgap hok hS' hB₁ hw
    (by rw [htr B, hmass]; exact (ENNReal.ofReal_pos.2 hm).ne') (by rw [htr B, hmass]; exact ENNReal.ofReal_ne_top) hl₂
  have hvs : v ∈ R.sm := hTKsm v (hKT v hv)
  have hnz : NzOn R (fun v => l (R.σ t v)) := ⟨v, hvs, hv0⟩
  refine ⟨GlobalTheory.exists_kFin_ne_zero_of_cwCont hKF k r ε mu R hds Wp l hl.1 hl.2.1 hl.2.2.2 ⟨_, hsm t ht v hvs, hv0⟩, ?_⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.BesselLine.bessel_line hH k r ε mu R Wp z π u μW _ μG _ _ _ hds hS' hl₂.1 hnz hB₁
  have hβ' : ∀ v ∈ R.sm, B v = β • l v := fun v hv => by
    have := hβ _ (hsm _ hti v hv)
    simpa only [e2] using this
  refine ⟨β, hβ', ?_⟩
  have hws : w ∈ R.sm := hTKsm w (hKT w hw)
  have hiso := (GlobalTheory.scaled_bessel_isometric hH k r ε mu h R Wp z π u μW _ μG _ _ dd hds hgap hok hS' hl₂ hdd hnz).2 w hws
  have h2 := (htr fun v => ((Real.sqrt dd : ℝ) : ℂ) • l v).symm.trans hiso
  have h3 : ENNReal.ofReal dd * PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) =
      ENNReal.ofReal (‖β‖ ^ 2) * PI.BesselPeriodGGP.l2SG νq (fun g => ((Real.sqrt dd : ℝ) : ℂ) • l (R.σ g w)) := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have en : ∀ y : Wp, ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := fun y => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl
    rw [en, en, hβ' _ (hsm _ hx w hws), ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
      norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow,
      Real.sq_sqrt hd0.le]
    congr 1
    ring
  rw [hmass, h2, ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h3
  linarith

theorem scale_pos {k r : ℕ} {μG μW ν : Measure (Mt k r)} {κ : ℝ≥0∞} (hG : μG ≠ 0)
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) κ)) ν) : 0 < κ := by
  rw [pos_iff_ne_zero]
  rintro rfl
  apply hG
  have := hq (fun _ => 1) measurable_const
  simpa [muS, haarLie] using this

theorem sideG_of {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : Fin k → ℝ}
    {μW μG νq : Measure (Mt k r)} {κ : ℝ≥0∞} (hκ : κ < ⊤) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) (hW : IsHaarOn (UWset k r z) μW) (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) κ)) νq) :
    ∃ U, SideG k r z π U μW (haarLie (Nset k r) κ) μG νq := by
  refine ⟨fun n => if h : n - 1 < k then u ⟨n - 1, h⟩ else 0, hz, hT, ⟨u, hπ⟩,
    GlobalTheory.ThA.capParam_of_isHCTypeW k r z u _ Wp π hz hT hπ (fun i => by simp), hW,
    _root_.GlobalTheory.haarLie_isHaarOn_Nset k r κ (scale_pos hG.2.1 hq) hκ, hG, hq⟩

theorem dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : MatKR k r → (H →L[ℂ] H)) (w : List (MatKR k r)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ w v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v)
    rw [ih]; rfl

theorem isBesselMapSm_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (h : Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simpa only [dsigW_eq] using h5 v hv

theorem amp_eq_smul_normalised : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  intro hH D τ w w' θ W lam A h l l' hθ hka hT hT' hW hA hgap hok hl hl' hbe hbe'
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW
  obtain ⟨hlam, hds, b1, b2, hsm0, hv0, ⟨P, hP, hlowK⟩, hc, l1, l2, -⟩ := hA
  set R : Rep D.R.k D.R.rS := ⟨A.H, A.σ⟩ with hR
  have hDS : R.IsDS (epsSH D.R) lam := ⟨hlam, hds⟩
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨-, -, -, hsm, hTKsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF _ _ _ _ R hDS
  obtain ⟨-, hGm, -⟩ := uHGroup _ _ (det_hpk D.R.k D.R.rS)
  rw [hN] at q1 q2 hbe hbe'
  obtain ⟨U, hS⟩ := sideG_of ENNReal.ofReal_lt_top z1 (t1 ▸ hT) c1 w1 hG q1
  obtain ⟨U', hS'⟩ := sideG_of ENNReal.ofReal_lt_top z2 (t2 ▸ hT') c2 w2 hG q2
  have hcs : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have : 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) = 2 * (D.host.ka / gg D) := by
      rw [mul_div_assoc]; rfl
    rw [this]
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * (D.host.ka / gg D)).ne'
  have hn : 0 < ‖A.v0‖ := norm_pos_iff.2 hv0
  set w0 : A.H := ((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0 with hw0
  have hw1 : ‖w0‖ = 1 := by rw [hw0, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hlow : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 :=
    ⟨P, hP, hw1, Submodule.smul_mem _ _ hlowK⟩
  have hv : A.v0 = ((‖A.v0‖ : ℝ) : ℂ) • w0 := by
    rw [hw0, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  have hvK : R.KFin A.v0 := by
    obtain ⟨S, h1, h2, h3⟩ := hwK
    exact ⟨S, h1, hv ▸ S.smul_mem _ h2, h3⟩
  have hws : w0 ∈ R.sm := hTKsm _ (hKT _ hwK)
  obtain ⟨c₀, hc₀, hdeg⟩ := GlobalTheory.BesselDegree.schur_fdeg hH _ _ (epsSH D.R) W.μG hG
  have hdd := (hdeg lam R hDS).1
  have hd0 : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC lam := mul_pos hc₀ (GlobalTheory.BesselNorm.fdegHC_pos lam hlam.1.injective)
  set dd := c₀ * Formalism.QuantumDeterminants.fdegHC lam
  have hp : (0 : ℝ) < Module.finrank ℂ W.Wp := by
    obtain ⟨g, -, hnt, -⟩ := c1
    exact_mod_cast Module.finrank_pos
  have hq : (0 : ℝ) < Module.finrank ℂ W.Wq := by
    obtain ⟨g, -, hnt, -⟩ := c2
    exact_mod_cast Module.finrank_pos
  obtain ⟨nz1, β, hβ, e1⟩ := one_side hH R (B := A.B) (l := l) hDS hgap hok hS hcs (isBesselMapSm_of b1) hl hbe hvK (mul_pos hc hp) l1 hd0 hdd
  obtain ⟨nz2, β', hβ', e2⟩ := one_side hH R (B := A.B') (l := l') hDS hgap hok hS' hcs (isBesselMapSm_of b2) hl' hbe' hvK (mul_pos hc hq) l2 hd0 hdd
  refine ⟨nz1, nz2, w0, (A.cN : ℂ)⁻¹ * ((β * (‖A.v0‖ : ℝ)) * star (β' * (‖A.v0‖ : ℝ))), hlow, ?_, ?_⟩
  · have hw00 : w0 ≠ 0 := by rw [← norm_pos_iff, hw1]; exact one_pos
    rw [show PI.BesselPeriodGGP.fdegH W.μG A.σ w0 = dd from hdd w0 hw00]
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    simp only [norm_mul, norm_star, norm_inv, Complex.norm_real, norm_norm, Real.norm_of_nonneg hc.le]
    have e1' : ‖β‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wp * dd := e1.symm
    have e2' : ‖β'‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wq * dd := e2.symm
    rw [mul_pow, mul_pow, mul_pow, mul_pow, e1', e2']
    field_simp
  · intro ν γ hγ hν
    have hae : ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := hν
    unfold LocS.J amp ampJ
    rw [Complex.ofReal_one, inv_one, one_smul, mul_smul]
    congr 1
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have a1 : A.Φ (γ * Matrix.of x) = (β * (‖A.v0‖ : ℝ)) • l (A.σ (γ * Matrix.of x) w0) := by
      have hs := hsm _ (hGm _ hγ _ hx) w0 hws
      have hs' := hsm _ (hGm _ hγ _ hx) A.v0 hsm0
      unfold LocS.Φ
      rw [hβ _ hs', mul_smul, ← hl.2.1 _ _ hs, ← map_smul, ← hv]
    have a2 : A.Φ' (Matrix.of x) = (β' * (‖A.v0‖ : ℝ)) • l' (A.σ (Matrix.of x) w0) := by
      have hs := hsm _ hx w0 hws
      have hs' := hsm _ hx A.v0 hsm0
      unfold LocS.Φ'
      rw [hβ' _ hs', mul_smul, ← hl'.2.1 _ _ hs, ← map_smul, ← hv]
    rw [a1, a2]
    ext y
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, ContinuousLinearMap.smul_apply,
      smul_smul]
    congr 1
    simp only [RCLike.star_def]
    ring

end GlobalTheory.AmpNormal
end

