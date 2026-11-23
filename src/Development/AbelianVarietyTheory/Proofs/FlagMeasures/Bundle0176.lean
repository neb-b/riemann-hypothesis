module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroup
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryOpNormBoundedByTwoFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedFormOrthogonalFinrankDetUnitary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfolding
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OnePiece

variable {k r : ℕ}

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact (continuous_const.matrix_mul continuous_id.matrixOf).matrix_mul continuous_const

def grp (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ GG k r}

theorem measurableSet_grp : MeasurableSet (grp k r) := by
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r)ᴴ * Hpk k r * Matrix.of x :=
    (continuous_id.matrixOf.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id.matrixOf
  exact (isClosed_eq hc continuous_const).measurableSet

private theorem continuous_matrix_of : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) :=
  continuous_id.matrixOf

theorem measurable_indicator_grp {f : Mat k r → ℝ≥0∞} (hf : ContinuousOn f (GG k r)) :
    Measurable ((grp k r).indicator fun x => f (Matrix.of x)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise
    (hf.comp continuous_matrix_of.continuousOn fun _ hx => hx) continuousOn_const measurableSet_grp

theorem mem_GG_of_mul {s x : Mat k r} (hs : s ∈ GG k r) (h : s * x ∈ GG k r) : x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have h' : (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r := h
  show xᴴ * Hpk k r * x = Hpk k r
  calc xᴴ * Hpk k r * x = xᴴ * (sᴴ * Hpk k r * s) * x := by rw [hs']
    _ = (s * x)ᴴ * Hpk k r * (s * x) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := h'

theorem continuousOn_sq {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] {g : X → E} {s : Set X}
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (‖g x‖₊ : ℝ≥0∞) ^ 2) s :=
  ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)).comp_continuousOn hg

private theorem mul_mem_UH_Hpk' {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem aemeasurable_comp_of_continuousOn_closed {S : Set (Mat k r)} (hS : IsClosed S) {μ : Measure (Mt k r)}
    (hμ : μ {x | Matrix.of x ∉ S} = 0) {g : Mat k r → ℝ≥0∞} (hg : ContinuousOn g S) :
    AEMeasurable (fun x => g (Matrix.of x)) μ := by
  classical
  have hm : MeasurableSet {x : Mt k r | Matrix.of x ∈ S} :=
    (hS.preimage continuous_matrix_of).measurableSet
  have h1 : Measurable ({x : Mt k r | Matrix.of x ∈ S}.piecewise (fun x => g (Matrix.of x)) 0) :=
    ContinuousOn.measurable_piecewise (hg.comp continuous_matrix_of.continuousOn fun _ hx => hx)
      continuousOn_const hm
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := by rw [ae_iff]; exact hμ
  refine h1.aemeasurable.congr ?_
  filter_upwards [hae] with x hx
  exact Set.piecewise_eq_of_mem _ _ _ hx

private theorem ofReal_one_sq_mul_norm_sq_div {E : Type} [NormedAddCommGroup E] (v : E) (d : ℕ) (hd : 0 < d) :
    ENNReal.ofReal ((1 : ℝ) ^ 2 * ‖v‖ ^ 2 / d) = (d : ℝ≥0∞)⁻¹ * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  rw [one_pow, one_mul, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hd'.le),
    ENNReal.ofReal_inv_of_pos hd', ENNReal.ofReal_natCast, ← coe_nnnorm v, ← NNReal.coe_pow,
    ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]

theorem one_piece : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (c : ℝ), OneSide z π ψ μG μW μN νS Φ c → ∀ (f : Mt k r → ℝ≥0∞) (Q : Set (Mt k r)) (Vol : ℝ≥0∞), Measurable f → MeasurableSet Q → (∀ s ∈ Sset k r z, ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q)) → (∀ g ∈ GG k r, ∫⁻ n, f (rmulM g n) ∂μN ≤ Vol) → ∀ w : Wp, ‖w‖ = 1 → ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS := by
  intro k r Wp _ _ _ z π ψ μG μW μN νS Φ c hOS f Q Vol hf hQ hQinv hVol w hw
  obtain ⟨hz, hT, hnt, hU, hI, hG, hW, hW1, hN, hQm, hψ, hE, hΦ, -, -⟩ := hOS
  haveI := hnt
  have hd : 0 < Module.finrank ℂ Wp := Module.finrank_pos
  have hinC : Continuous fun v : Wp => ⟪w, v⟫_ℂ := continuous_const.inner continuous_id
  set A : Mt k r → ℝ≥0∞ := (grp k r).indicator fun y => (‖⟪w, Φ (Matrix.of y)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2
    with hAdef
  set B : Mt k r → ℝ≥0∞ := (grp k r).indicator fun y => (‖Φ (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2
    with hBdef
  have hAm : Measurable A :=
    measurable_indicator_grp (f := fun g => (‖⟪w, Φ g⟫_ℂ‖₊ : ℝ≥0∞) ^ 2)
      (continuousOn_sq (hinC.comp_continuousOn hΦ))
  have hBm : Measurable B :=
    measurable_indicator_grp (f := fun g => (‖Φ g‖₊ : ℝ≥0∞) ^ 2) (continuousOn_sq hΦ)
  set F : Mt k r → ℝ≥0∞ := Q.indicator fun y => f y * A y with hFdef
  have hFm : Measurable F := (hf.mul hAm).indicator hQ
  have haeG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := by rw [ae_iff]; exact hG.2.2.1
  have haeW : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
  have haeN : ∀ᵐ n ∂μN, Matrix.of n ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1

  have step1 : ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG = ∫⁻ x, F x ∂μG := by
    rw [← lintegral_indicator hQ]
    refine lintegral_congr_ae ?_
    filter_upwards [haeG] with x hx
    have hxg : x ∈ grp k r := hx
    by_cases hxQ : x ∈ Q
    · rw [hFdef, hAdef]
      simp only [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxg]
    · rw [hFdef]
      simp only [Set.indicator_of_notMem hxQ]

  have inner_le : ∀ x : Mt k r,
      ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ≤
        Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
    intro x
    have hit : ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ≤
        ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW :=
      calc ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN)
          ≤ ∫⁻ p, F (lmulM (Matrix.of p.1 * Matrix.of p.2) x) ∂(μW.prod μN) := by
            apply lintegral_map_le
            have hc : Continuous (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
              exact continuous_fst.matrixOf.matrix_mul continuous_snd.matrixOf
            exact hc.measurable.aemeasurable
        _ ≤ ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW := lintegral_prod_le _
    refine hit.trans ?_
    have zero_case : (∀ h : Mt k r, Matrix.of h ∈ UWset k r z → ∀ n : Mt k r,
        Matrix.of n ∈ Nset k r → F (lmulM (Matrix.of h * Matrix.of n) x) = 0) →
        ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW ≤
          Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
      intro h0
      refine le_trans ?_ (zero_le ..)
      calc ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW
          ≤ ∫⁻ _h, (0 : ℝ≥0∞) ∂μW := by
            refine lintegral_mono_ae ?_
            filter_upwards [haeW] with h hh
            calc ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ≤ ∫⁻ _n, (0 : ℝ≥0∞) ∂μN := by
                  refine lintegral_mono_ae ?_
                  filter_upwards [haeN] with n hn
                  exact (h0 h hh n hn).le
              _ = 0 := lintegral_zero
        _ = 0 := lintegral_zero
    by_cases hxg : x ∈ grp k r
    · by_cases hxQ : x ∈ Q
      · have hB : Q.indicator B x = (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
          rw [hBdef]
          simp only [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxg]
        have hmain : ∀ h : Mt k r, Matrix.of h ∈ UWset k r z → ∀ n : Mt k r,
            Matrix.of n ∈ Nset k r → F (lmulM (Matrix.of h * Matrix.of n) x) =
              f (lmulM (Matrix.of h * Matrix.of n) x) *
                (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := by
          intro h hh n hn
          have hs : Matrix.of h * Matrix.of n ∈ Sset k r z := by
            show ∃ h' ∈ UWset k r z, ∃ m ∈ Nset k r, Matrix.of h * Matrix.of n = h' * m
            exact ⟨_, hh, _, hn, rfl⟩
          have hSQ : lmulM (Matrix.of h * Matrix.of n) x ∈ Q := (hQinv _ hs x hxg).2 hxQ
          have hSG : lmulM (Matrix.of h * Matrix.of n) x ∈ grp k r :=
            mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hh.1 hn.1) hxg
          have hΦS : Φ (Matrix.of (lmulM (Matrix.of h * Matrix.of n) x)) =
              ψ (Matrix.of n) • π (Matrix.of h) (Φ (Matrix.of x)) := hE _ hh _ hn _ hxg
          have hψ1 : ‖ψ (Matrix.of n)‖₊ = 1 := by ext; simpa using hψ _ hn
          rw [hFdef, hAdef]
          simp only [Set.indicator_of_mem hSQ, Set.indicator_of_mem hSG, hΦS, inner_smul_right,
            nnnorm_mul, hψ1, one_mul]
        have hfib : ∀ h : Mt k r, Matrix.of h ∈ UWset k r z →
            ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ≤ Vol := by
          intro h hh
          have hdet : IsUnit (Matrix.of h : Mat k r).det := isUnit_det_of_mem_GG hh.1
          have key : ∀ n : Mt k r, lmulM (Matrix.of h * Matrix.of n) x =
              rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n) := by
            intro n
            show (Matrix.of h * Matrix.of n * Matrix.of x : Mat k r) =
              Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
            rw [Matrix.mul_assoc (Matrix.of h * Matrix.of n) (Matrix.of h)⁻¹,
              ← Matrix.mul_assoc (Matrix.of h)⁻¹, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
          have hrc : Continuous (rmulM (Matrix.of h * Matrix.of x) : Mt k r → Mt k r) := by
            unfold rmulM
            exact continuous_matrix_of.matrix_mul continuous_const
          have hinv : μN.map (conjM (Matrix.of h)) = μN :=
            ((_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μN).2.1 hN).2 _ hh
          calc ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN
              = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n)) ∂μN :=
                lintegral_congr fun n => congrArg f (key n)
            _ = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) n) ∂(μN.map (conjM (Matrix.of h))) :=
                (lintegral_map (hf.comp hrc.measurable) (continuous_conj _).measurable).symm
            _ = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) n) ∂μN := by rw [hinv]
            _ ≤ Vol := hVol _ (mul_mem_UH_Hpk' hh.1 hxg)
        have hAEM : AEMeasurable (fun h : Mt k r =>
            (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2) μW :=
          aemeasurable_comp_of_continuousOn_closed (isClosedSub_UWset z).2.1 hW.2.2.1
            (g := fun g => (‖⟪w, π g (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2)
            (continuousOn_sq (hinC.comp_continuousOn (hU.2.2 (Φ (Matrix.of x)))))
        calc ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW
            ≤ ∫⁻ h, Vol * (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW := by
              refine lintegral_mono_ae ?_
              filter_upwards [haeW] with h hh
              calc ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN
                  = ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) *
                      (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μN := by
                    refine lintegral_congr_ae ?_
                    filter_upwards [haeN] with n hn
                    exact hmain h hh n hn
                _ = (∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN) *
                      (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
                    lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
                _ ≤ Vol * (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
                    mul_le_mul_of_nonneg_right (hfib h hh) (zero_le ..)
          _ = Vol * ∫⁻ h, (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW :=
              lintegral_const_mul'' _ hAEM
          _ = Vol * ENNReal.ofReal (‖w‖ ^ 2 * ‖Φ (Matrix.of x)‖ ^ 2 / Module.finrank ℂ Wp) := by
              rw [(_root_.GlobalTheory.Amp.Schur.type_irred_and_avg k r z π hz hT).2 μW hU hI hW hW1 w (Φ (Matrix.of x))]
          _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
              rw [hB, hw, ofReal_one_sq_mul_norm_sq_div _ _ hd, mul_assoc]
      · refine zero_case fun h hh n hn => ?_
        have hs : Matrix.of h * Matrix.of n ∈ Sset k r z := by
          show ∃ h' ∈ UWset k r z, ∃ m ∈ Nset k r, Matrix.of h * Matrix.of n = h' * m
          exact ⟨_, hh, _, hn, rfl⟩
        have hSQ : lmulM (Matrix.of h * Matrix.of n) x ∉ Q := fun h' => hxQ ((hQinv _ hs x hxg).1 h')
        rw [hFdef]
        simp only [Set.indicator_of_notMem hSQ]
    · refine zero_case fun h hh n hn => ?_
      have hS : lmulM (Matrix.of h * Matrix.of n) x ∉ grp k r := fun hS =>
        hxg (mem_GG_of_mul (s := Matrix.of h * Matrix.of n) (x := Matrix.of x)
          (mul_mem_UH_Hpk' hh.1 hn.1) hS)
      rw [hFdef, hAdef]
      by_cases hSQ : lmulM (Matrix.of h * Matrix.of n) x ∈ Q
      · simp only [Set.indicator_of_mem hSQ, Set.indicator_of_notMem hS, mul_zero]
      · simp only [Set.indicator_of_notMem hSQ]
  calc ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG = ∫⁻ x, F x ∂μG := step1
    _ = ∫⁻ x, ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ∂νS := hQm F hFm
    _ ≤ ∫⁻ x, Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x ∂νS := lintegral_mono inner_le
    _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x, Q.indicator B x ∂νS :=
        lintegral_const_mul _ (hBm.indicator hQ)
    _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, B x ∂νS := by rw [lintegral_indicator hQ]
    _ ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun x => Set.indicator_le_self _ _ x) (zero_le ..)

end GlobalTheory.Amp.OnePiece
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormCoeffProductFubiniIntegrable
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

theorem integrable_opn_rpow_neg {k r : ℕ} (μ : Measure (Mt k r)) (A : ℝ)
    (hc : Continuous fun x : Mat k r => opn x) (h : normInt μ A < ⊤) :
    Integrable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) μ := by
  have hm : Measurable fun x : Mt k r => opn (Matrix.of x) ^ (-A) :=
    (show Continuous fun x : Mt k r => opn (Matrix.of x) from hc).measurable.pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (opn_nonneg _) _)).2 h

theorem rpow_fubini_ineq {x y t a : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (ht : 0 < t) (hyt : t / x ≤ y)
    (ha : 0 ≤ a) : x ^ (-a) * y ^ (-a) ≤ x ^ (-(a / 2)) * t ^ (-(a / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h1 : y ^ (-a) ≤ y ^ (-(a / 2)) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have h2 : y ^ (-(a / 2)) ≤ (t / x) ^ (-(a / 2)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos ht hx0) hyt (by linarith)
  have h3 : (t / x) ^ (-(a / 2)) = t ^ (-(a / 2)) / x ^ (-(a / 2)) := Real.div_rpow ht.le hx0.le _
  have h4 : x ^ (-a) = x ^ (-(a / 2)) * x ^ (-(a / 2)) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hxp : 0 < x ^ (-(a / 2)) := Real.rpow_pos_of_pos hx0 _
  calc x ^ (-a) * y ^ (-a) ≤ x ^ (-a) * ((t / x) ^ (-(a / 2))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-(a / 2)) * t ^ (-(a / 2)) := by
        rw [h3, h4]; field_simp

theorem fubini_bound : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ v₁ ∈ DD σ w, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) (μG.prod μS) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv v₁ hv₁
  obtain ⟨hk, hrep, -, -, hHG, -, ha, hdec, -⟩ := hStd
  obtain ⟨hz, hT, -, hHS, -⟩ := hSide
  obtain ⟨hGc, -, -, hSc, -⟩ := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  obtain ⟨hN1, -, hNc, -, -, -, hN7, -⟩ := _root_.GlobalTheory.SgInf.opn_facts k r
  have hA := (_root_.GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five k r a hk ha).1
  have hIG := _root_.GlobalTheory.SgGrowth.normInt_lt_top k r (GG k r) μG (a / 2) hGc hHG hA
  have hIS := _root_.GlobalTheory.SgGrowth.normInt_lt_top k r (Sset k r z) μS (a / 2) hSc hHS hA
  obtain ⟨C, hC⟩ := hdec u hu v hv
  obtain ⟨C₁, hC₁⟩ := hdec u₁ hu₁ v₁ hv₁
  haveI := hHG.1
  haveI := hHS.1
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  set T : Set (Mt k r × Mt k r) := {p | Matrix.of p.1 ∈ GG k r ∧ Matrix.of p.2 ∈ Sset k r z} with hTdef
  have hTm : MeasurableSet T := by
    have h1 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.1 ∈ GG k r} :=
      hGc.2.1.preimage continuous_fst
    have h2 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.2 ∈ Sset k r z} :=
      hSc.2.1.preimage continuous_snd
    exact (h1.inter h2).measurableSet
  have hTae : ∀ᵐ p ∂(μG.prod μS), p ∈ T := by
    rw [ae_iff]
    refine measure_mono_null (t := ({x : Mt k r | Matrix.of x ∉ GG k r} ×ˢ Set.univ) ∪
      (Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Sset k r z})) ?_ ?_
    · intro p hp
      simp only [Set.mem_setOf_eq, hTdef, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, trivial⟩
      · exact Or.inr ⟨trivial, hp⟩
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hHG.2.2.1, zero_mul]
      · rw [Measure.prod_prod, hHS.2.2.1, mul_zero]
  have hg : Integrable (fun p : Mt k r × Mt k r => (|C| * |C₁|) *
      (opn (Matrix.of p.1) ^ (-(a / 2)) * opn (Matrix.of p.2) ^ (-(a / 2)))) (μG.prod μS) :=
    ((integrable_opn_rpow_neg μG _ hNc hIG).mul_prod (integrable_opn_rpow_neg μS _ hNc hIS)).const_mul _
  have hcont : ContinuousOn (fun p : Mt k r × Mt k r =>
      coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) T := by
    have c1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1) u) T :=
      (hrep.2.2 u).comp (continuous_fst.continuousOn) (fun p hp => hp.1)
    have hmul : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.2 * Matrix.of p.1 : Mat k r) :=
      (continuous_snd (X := Mat k r) (Y := Mat k r)).matrix_mul continuous_fst
    have c2 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.2 * Matrix.of p.1) u₁) T :=
      (hrep.2.2 u₁).comp hmul.continuousOn
        (fun p hp => hGc.2.2.2.1 _ (hSc.1 hp.2) _ hp.1)
    exact (continuousOn_const.inner c1).mul (continuous_star.comp_continuousOn (continuousOn_const.inner c2))
  refine hg.mono' ?_ ?_
  · have := hcont.aestronglyMeasurable (μ := μG.prod μS) hTm
    rwa [Measure.restrict_eq_self_of_ae_mem hTae] at this
  · filter_upwards [hTae] with p hp
    obtain ⟨hpG, hpS⟩ := hp
    have hSG : Matrix.of p.2 ∈ GG k r := hSc.1 hpS
    have hyG : (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ∈ GG k r := hGc.2.2.2.1 _ hSG _ hpG
    have hx1 := (hN1 _ hpG).2
    have ht1 := (hN1 _ hSG).2
    have hy1 := (hN1 _ hyG).2
    have hyt : opn (Matrix.of p.2 : Mat k r) / opn (Matrix.of p.1 : Mat k r) ≤
        opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) := (hN7 _ hSG _ hpG).1
    have e1 : ‖coef σ u v (Matrix.of p.1)‖ ≤ |C| * opn (Matrix.of p.1 : Mat k r) ^ (-a) :=
      (hC _ hpG).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (opn_nonneg _) _))
    have e2 : ‖coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1)‖ ≤
        |C₁| * opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a) :=
      (hC₁ _ hyG).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) (Real.rpow_nonneg (opn_nonneg _) _))
    have key := rpow_fubini_ineq hx1 hy1 (lt_of_lt_of_le one_pos ht1) hyt ha0
    rw [norm_mul, norm_star]
    calc ‖coef σ u v (Matrix.of p.1)‖ * ‖coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1)‖
        ≤ (|C| * opn (Matrix.of p.1 : Mat k r) ^ (-a)) *
            (|C₁| * opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _))
      _ = (|C| * |C₁|) * (opn (Matrix.of p.1 : Mat k r) ^ (-a) *
            opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg (abs_nonneg _) (abs_nonneg _))

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRegularDoubleCosetPolynomialProperness
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PolyProper

variable {k r : ℕ}

theorem gram_det_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hermitian_pos_facts_hold k r).2.1

theorem mul_mem {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (unitary_group_holds _ _ gram_det_unit).2.1 g hg h hh

theorem inv_mem {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).2

theorem det_unit {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).1

theorem mem_of_S {z : Fin (2 * r + k + 1) → ℂ} {s : Mat k r} (hs : s ∈ Sset k r z) : s ∈ GG k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact mul_mem hh.1 hm.1

theorem inv_eq {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc (Hpk k r), Matrix.mul_assoc (Hpk k r), h]
  exact (hermitian_pos_facts_hold k r).2.1

theorem left_bound (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)) (hz : inWb k r z)
    (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hC : IsCompact C)
    (hCr : C ⊆ Greg k r z z') :
    ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z',
      opn s ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  obtain ⟨C1, h1⟩ := _root_.GlobalTheory.SgInf.frame_image_bound k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C2, h2⟩ := _root_.GlobalTheory.SgInf.isom_frame_bound k r z z' C hz hz' hT hT' hC
    (fun γ hγ => ⟨(hCr hγ).1, (hCr hγ).2.2⟩)
  obtain ⟨hN1, -, -, -, hN5, -⟩ := _root_.GlobalTheory.SgInf.opn_facts k r
  refine ⟨C2 * (max 1 C1) ^ 2, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hx1 : 1 ≤ opn (s * γ * s'⁻¹) := (hN1 _ hxG).2
  have hxs : (s * γ * s'⁻¹) * s' = s * γ := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_unit hs'G), Matrix.mul_one]
  have h1' := h1 γ hγ s hs s' hs'
  have h5 := hN5 (s * γ * s'⁻¹)
  set X := opn (s * γ * s'⁻¹) with hX
  have hp1 : 1 ≤ X ^ (r * (r + 1)) := one_le_pow₀ hx1
  have hm1 : (1 : ℝ) ≤ max 1 C1 := le_max_left _ _
  have hle : C1 * X ^ (r * (r + 1)) ≤ max 1 C1 * X ^ (r * (r + 1)) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hQ1 : 1 ≤ max 1 C1 * X ^ (r * (r + 1)) := one_le_mul_of_one_le_of_one_le hm1 hp1
  have hB : 1 ≤ X * (max 1 C1 * X ^ (r * (r + 1))) := one_le_mul_of_one_le_of_one_le hx1 hQ1
  have key := h2 γ hγ s hsG (X * (max 1 C1 * X ^ (r * (r + 1)))) hB (by
    rintro (a | b)
    · show eucl (s *ᵥ fvec k r z a) ≤ _
      refine ((h1' a).1.trans hle).trans ?_
      exact le_mul_of_one_le_left (by linarith) hx1
    · show eucl (s *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [Matrix.mulVec_mulVec, ← hxs, ← Matrix.mulVec_mulVec]
      refine (h5 _).trans ?_
      exact mul_le_mul_of_nonneg_left ((h1' b).2.trans hle) (by linarith))
  refine key.trans (le_of_eq ?_)
  ring

theorem poly_proper : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  intro k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C1, h1⟩ := left_bound z z' C hz hz' hT hT' hC hCr
  have hcont : Continuous fun g : Mat k r => Hpk k r * gᴴ * Hpk k r :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hCr' : (fun g : Mat k r => Hpk k r * gᴴ * Hpk k r) '' C ⊆ Greg k r z' z := by
    rintro _ ⟨γ, hγ, rfl⟩
    have hγG : γ ∈ GG k r := (hCr hγ).1
    show Hpk k r * γᴴ * Hpk k r ∈ _
    rw [← inv_eq hγG]
    exact (GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγG).2.1 (hCr hγ)
  obtain ⟨C2, h2⟩ := left_bound z' z _ hz' hz hT' hT (hC.image hcont) hCr'
  obtain ⟨hN1, -⟩ := _root_.GlobalTheory.SgInf.opn_facts k r
  refine ⟨max 1 (max C1 C2), le_max_left _ _, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hinv : s' * γ⁻¹ * s⁻¹ = (s * γ * s'⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_unit hs'G),
      Matrix.mul_assoc]
  have ha := h1 γ hγ s hs s' hs'
  have hb := h2 γ⁻¹ ⟨γ, hγ, (inv_eq hγG).symm⟩ s' hs' s hs
  rw [hinv, (hN1 _ hxG).1] at hb
  have hp : 0 ≤ opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := pow_nonneg (opn_nonneg _) _
  refine max_le (ha.trans ?_) (hb.trans ?_)
  · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hp
  · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hp

end GlobalTheory.SgInf.PolyProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralRadicalEqTopSectionSplitStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_radical_eq_top_section_split : ∀ (k r j : ℕ) (f : Mat k r → ℝ≥0∞), Measurable (fun x : Mt k r => f (Matrix.of x)) → ∫⁻ q : PPar k r, f (pOf k r q) = ∫⁻ q' : PSec k r j, ∫⁻ q : PTop k r j, f (pTop k r j q * pSec k r j q') := by
  first | exact @GlobalTheory.Amp.PSplit.lintegral_split | exact GlobalTheory.Amp.PSplit.lintegral_split | (intros; apply GlobalTheory.Amp.PSplit.lintegral_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedFormOrthogonalFinrankDetUnitaryStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Submodule ℂ (Fin n → ℂ)), (∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) → Module.finrank ℂ V' + Module.finrank ℂ V = n ∧ (∀ x, (∀ y ∈ V', star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) → x ∈ V) ∧ ∀ m : Formalism.REAL.UJ ε, ‖(uMat m).det‖ = 1 ∧ ((∀ y ∈ V, uMat m *ᵥ y ∈ V) → (∀ y ∈ V', uMat m *ᵥ y ∈ V') ∧ detOn (uMat m) V' = detOn (uMat m) V ∧ 0 < detOn (uMat m) V) := by
  first | exact @GlobalTheory.PerpModulus.perp_modulus | exact GlobalTheory.PerpModulus.perp_modulus | (intros; apply GlobalTheory.PerpModulus.perp_modulus <;> assumption)
end

