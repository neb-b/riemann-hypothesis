module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeDegenerateOperatorNormLeRealPlace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0312
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0145

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeAbsolutelyConvergentOperatorNormLeStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (z z' : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → MomBd z νS Φ (24 * r ^ 3 + 1) H₁ → MomBd z' νS' Φ' (24 * r ^ 3 + 1) H₁ → TwoFl k r z z' γ → DeOK k r z z' γ De → NormR k r γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * absBd k r H₁ De (Dr k r z z' γ) := by
  first | exact @GlobalTheory.Amp.AbsConv.abs_core | exact GlobalTheory.Amp.AbsConv.abs_core | (intros; apply GlobalTheory.Amp.AbsConv.abs_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeDegenerateOperatorNormLeRealPlaceStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_degenerate_operatorNorm_le_realPlace : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 16 * r ^ 3 + 4 * r + 2 ≤ q → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z νS Φ q H₁ → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * degBd k r j q H₁ De (Dj k r hj z z' γ) (sgV k r z z' γ H₁) := by
  first | exact @GlobalTheory.Amp.DegConv.deg_core | exact GlobalTheory.Amp.DegConv.deg_core | (intros; apply GlobalTheory.Amp.DegConv.deg_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointBoundCuspidalIsometricIntertwinerFamily
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.DeepFamilyGap

theorem one_mem_NA (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) : (1 : I.GA) ∈ I.NA W := by
  unfold AutInst.NA
  refine ⟨fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := by
      first
      | exact (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
      | exact I.P_unit v
    have hg : I.P v * uMat ((1 : I.GA).1 v) * (I.P v)⁻¹ = 1 := by
      rw [show uMat ((1 : I.GA).1 v) = 1 from rfl, mul_one]
      exact Matrix.mul_nonsing_inv _ hdet
    rw [hg]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp
  · have hf : I.fmat (1 : I.GA).2 = 1 := by
      first
      | rfl
      | simp
      | exact map_one _
    rw [hf]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp

theorem self_mem_omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) {ρ : ℝ} (h : 0 ≤ ρ) :
    x ∈ omega I x W ρ := by
  refine ⟨rfl, fun _ => 0, fun _ => 0, fun v => ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem,
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem⟩, ?_, fun v => by simp, fun s t => ⟨1, ?_, fun v => ?_⟩⟩
  · simpa [GlobalTheory.SobolevBound.hs_eq_trace] using h
  · exact one_mem_NA I W
  · rw [smul_zero, smul_zero, NormedSpace.exp_zero, mul_one, mul_one]
    exact one_mul _

theorem beP_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ beP n b P := by
  unfold beP
  positivity

theorem monotone₂ (n : ℕ) (b : ℝ) {P Q : ℕ} (h : P ≤ Q) : beP n b P ≤ beP n b Q := by
  unfold beP
  have : (P : ℝ) ≤ Q := by exact_mod_cast h
  linarith

theorem iterate (B : RowsAut) (b ρ M β : ℝ) (P₀ : ℕ) (D : ℕ)
    (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA)
    (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (hg : 1 ≤ B.g) (hW : B.I.IsIsot W)
    (hcov : ∀ ν : B.I.Ginf, ((ν, 1) : B.I.GA) ∈ B.I.NA W → ∃ γ ∈ B.I.GFset, ∃ k ∈ B.I.Kg B.g,
      ∃ y ∈ omega B.I x W ρ, ((ν, 1) : B.I.GA) * x = γ * y * (1, k))
    (hS : ∀ P, StepBoundAt B b P) (hR : ∀ i, IsReps B (T i) (Fr i))
    (hC : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hβ : beP B.I.n b P₀ ≤ β)
    (h0 : ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P₀, ‖vv B Fr u y‖ ≤ M * ‖u‖) :
    ∀ k P : ℕ, P + k = P₀ → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P,
      ‖vv B Fr u y‖ ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M * ‖u‖ := by
  have hβ0 : 0 ≤ β := le_trans (beP_nonneg _ _ _) hβ
  have hc0 : 0 ≤ 2 * ρ * Real.sqrt B.I.f * β :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ) (Real.sqrt_nonneg _)) hβ0
  intro k
  induction k with
  | zero =>
    intro P hP y hy u hu
    have hPP : P = P₀ := by simpa using hP
    subst hPP
    simpa using h0 y hy u hu
  | succ k ih =>
    intro P hP y hy u hu
    have hP' : (P + 1) + k = P₀ := by omega
    have hM' : 0 ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M := mul_nonneg (pow_nonneg hc0 _) hM
    have key := GlobalTheory.DeepStep.step_bound B b ρ ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) P D T Fr x W hg hW
      hcov (hS P) hR hC hM' (ih (P + 1) hP') y hy u hu
    have hle : beP B.I.n b P ≤ β := le_trans (monotone₂ _ _ (by omega : P ≤ P₀)) hβ
    calc ‖vv B Fr u y‖
        ≤ 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := key
      _ ≤ 2 * ρ * Real.sqrt B.I.f * β * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := by
          gcongr
      _ = (2 * ρ * Real.sqrt B.I.f * β) ^ (k + 1) * M * ‖u‖ := by ring

theorem mult_le {n τ t : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hτ1 : τ < 1 / 2) (ht : τ / 2 ≤ t) :
    1 + 4 * Real.sqrt n / t ^ 2 ≤ 17 * Real.sqrt n / τ ^ 2 := by
  have hs : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn
  have ht0 : 0 < t := by linarith
  have hτt : τ ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have h1 : 4 * Real.sqrt n / t ^ 2 ≤ 16 * Real.sqrt n / τ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : 1 ≤ Real.sqrt n / τ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : 17 * Real.sqrt n / τ ^ 2 = 16 * Real.sqrt n / τ ^ 2 + Real.sqrt n / τ ^ 2 := by ring
  linarith

theorem deep_bound_family : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ v, IsGauge (B.I.ε v) (c v)) → least B.I x < tauStar B q b → (∀ i, IsReps B (T i) (Fr i)) → (∀ i u, ‖T i u‖ = ‖u‖) → (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) → ‖vv B Fr (B.tens B.w) x‖ ^ 2 ≤ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal := by
  intro B Cg n₀ d p q b c x D T Fr hn₀ hq hCH hc hτ hR hiso hcusp
  obtain ⟨hDS, -, hn₀n, hq2, -, -, hb2, -, -, hg, -⟩ := id hCH
  obtain ⟨-, hrd, hf, -, -, -, hrk, -, -, -, -, htau, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn₀ hCH
  obtain ⟨htau2, hb19⟩ := htau hq
  have hn8 : 8 ≤ B.I.n := le_trans hn₀ hn₀n
  have hn1 : 1 ≤ B.I.n := by omega
  have hτpos : 0 < least B.I x :=
    ((GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 hn1).1
  have hτhalf : least B.I x < 1 / 2 := lt_trans hτ htau2
  have hτ1 : tau1 B.I x = least B.I x := min_eq_right hτhalf.le
  obtain ⟨W, hW, hcov⟩ := GlobalTheory.DeepCover.unipotent_orbit_cover B.I x B.g q hg hn1
    (fun v => (hrk v).le) hτhalf
  have hτX : least B.I x ≤ ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b)⁻¹ ^ (11 * q) := hτ.le
  have hex := GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn8 hf hq hq2 hrd hb2
    (by exact_mod_cast hg) hτpos hτX
  have hrho : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) ≤ Real.log 2 := hex.1
  have hρ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh
    have hg0 : (1 : ℝ) ≤ B.g := by exact_mod_cast hg
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (Real.sqrt_nonneg _)) (by linarith)) (by linarith)) (Real.rpow_nonneg (by linarith) _))
      (by norm_num)
  have hS : ∀ P, StepBoundAt B b P := _root_.GlobalTheory.Dec.stepBoundAt_of_countHyp B Cg n₀ d p q b hn₀ hCH
  have hβ : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + B.I.n ^ 2 * B.I.f) =
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := rfl
  have hβ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact beP_nonneg _ _ _
  have hβle : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) ≤
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact monotone₂ _ _ (Nat.le_add_right _ _)
  have hc0 : 0 < ∏ v, c v := Finset.prod_pos fun v _ => GlobalTheory.SobolevBound.gauge_pos (hc v)
  have hN : B.I.n ^ 2 * B.I.f = GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B := rfl
  have hK0 : 0 ≤ (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
      (Real.exp_pos _).le) (pow_nonneg (by positivity) _)) (Nat.cast_nonneg _)) hc0.le)
      ENNReal.toReal_nonneg
  have h0 : ∀ y ∈ omega B.I x W (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)),
      ∀ u ∈ VP B (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B), ‖vv B Fr u y‖ ≤
        Real.sqrt ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ := by
    intro y hy u hu
    have hs := GlobalTheory.SobolevBound.sobolev_bound B b c (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr hn8 hg hb19 hc hS
      hR hiso y u hu
    rw [hβ, hN] at hs
    have ht : least B.I x / 2 ≤ tau1 B.I y := by
      rw [← hτ1]; exact GlobalTheory.OmegaLeast.half_truncatedLeastLatticeSize_le_unipotentNeighbourhood B.I x W _ hn1 hrho y hy
    have hm := mult_le (n := (B.I.n : ℝ)) (by exact_mod_cast hn1) hτpos hτhalf ht
    have hle : ‖vv B Fr u y‖ ^ 2 ≤ ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ ^ 2 := by
      refine hs.trans ?_
      gcongr
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hK0, Real.sqrt_sq (norm_nonneg _)] at this
  have key := GlobalTheory.DeepFamilyGap.iterate B b (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)) _ _
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr x W hg hW hcov hS hR hcusp hρ0 (Real.sqrt_nonneg _) hβle h0
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) 0 (by simp) x (self_mem_omega B.I x W hρ0) (B.tens B.w)
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).1
  rw [(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).2, mul_one] at key
  have hA0 : 0 ≤ 2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f *
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0) (Real.sqrt_nonneg _)) hβ0
  have hsq := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [mul_pow, ← pow_mul, Real.sq_sqrt hK0] at hsq
  refine hsq.trans (le_of_eq ?_)
  rw [show 8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * 2 = 16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B by ring]
  ring

end GlobalTheory.DeepFamilyGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DegreeNearParameterBound
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OpenCellNorm

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = ‖t‖ ^ 2 * hsNormSq A := by
  have h : hsInner (t • A) (t • A) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hsInner A A := by
    simp only [hsInner, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsNormSq, h, Complex.re_ofReal_mul, hsNormSq]

theorem bigCell_mem_of_weight {k r : ℕ} (hk : 2 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ}
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : IsSection k r z z' μsec) {q : (Fin r → ℂ) × ℂ}
    (hq : bcWeight k r (Tz k r z) (Tz k r z') q ≠ 0) : bigCell k r q.1 (μsec q.2) ∈ UH (Hpk k r) := by
  unfold bcWeight at hq
  split_ifs at hq with h
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hq
    refine GlobalTheory.bigCell_mem_unitary k r _ _ (fun a ha => ?_) (hs.2 _ (lt_of_le_of_ne h fun e => ?_)).1
    · refine Finset.prod_ne_zero_iff.1 h1 a (Finset.mem_univ a) ?_
      rw [ha, norm_zero]
      exact zero_pow (by unfold Mdim; omega)
    · rw [e, sub_self] at h2
      exact h2 (zero_pow (by omega))
  · exact absurd rfl hq

theorem lintegral_weight_smul {k r : ℕ} (hk : 2 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ}
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : IsSection k r z z' μsec)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {J J' : MatKR k r → (Wq →L[ℂ] Wp)} {η : ℂ} (h : ∀ γ ∈ UH (Hpk k r), J γ = η • J' γ) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q *
        hsNormSq (J (bigCell k r q.1 (μsec q.2)))) =
      ENNReal.ofReal (‖η‖ ^ 2) * ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q *
        hsNormSq (J' (bigCell k r q.1 (μsec q.2)))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  by_cases hq : bcWeight k r (Tz k r z) (Tz k r z') q = 0
  · simp [hq]
  · rw [h _ (bigCell_mem_of_weight hk hs hq), hsNormSq_smul, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm]

theorem exists_bessel_scale (hH : Hyps) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)}
    {u : ℕ → ℝ} {c : ℂ} {μW μN μG νq : Measure (Mt k r)} (hc : c ≠ 0) (hS : SideG k r z π u μW μN μG νq)
    {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ} (R : Rep k r) (hR : R.IsDS ε mu)
    (hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ) (hg : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) :
    ∃ l : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l ∧
      ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
  obtain ⟨t, ht, hN, hz, -⟩ := _root_.GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, hW, hψ⟩ := hz z hS.1
  obtain ⟨hS', hm⟩ := GlobalTheory.T.torus_normaliser_bessel hH k r Wp z π u c μW μN μG νq t ht hN hW hψ hS
  obtain ⟨l₁, hl⟩ := GlobalTheory.exists_normalised_bessel_map hH k r ε mu h R Wp _ _ _ _ _ _ _ hR hg hok hS'
  obtain ⟨h1, h2⟩ := hm R hU
  refine ⟨fun v => l₁ (R.σ t⁻¹ v), (h1 _).2 ?_, h2 l₁ hl⟩
  have e : (fun v => l₁ (R.σ t⁻¹ (R.σ t v))) = l₁ := by
    funext v
    have h3 := hU.1.2 _ (PI.HwUniqW.inv_mem_UH ht) _ ht
    rw [show t⁻¹ * t = 1 from PI.HwUniqW.inv_mul_UH' ht, hU.1.1] at h3
    exact congrArg l₁ (congrArg (fun T : R.H →L[ℂ] R.H => T v) h3).symm
  show IsBes R z π (fun v => l₁ (R.σ t⁻¹ (R.σ t v)))
  rw [e]
  exact hl.1

theorem norm_eq_const_div_deg : Hyps → AmpKF → CellConv → ∀ Cg cb Cu cT CT C0 C1 Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∃ K : ℝ, 0 < K ∧ ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A → MMv D w w' A μsec = ENNReal.ofReal (K / A.deg) := by
  intro hH hKF hCC Cg cb Cu cT CT C0 C1 Cn
  refine ⟨Cn, fun D large₂ C' Cl hCl hBig hcd hZ τ w w' hTT θ hθw W hW μsec hsec => ?_⟩
  by_cases hex : ∃ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A
  swap
  · exact ⟨1, one_pos, fun lam' _ A hA => absurd ⟨lam', A, hA⟩ hex⟩
  obtain ⟨lam₀, A₀, hA₀⟩ := hex
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  have hθ : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.exp_pos _) _) hθw.1
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : 0 < D.host.v := by linarith
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hv
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hkg : 0 < D.host.ka / gg D := div_pos hka (mul_pos hg0 hg1)
  have hc : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  have hT : 0 < Tr D w := by unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by unfold Tr; exact_mod_cast hTT.2.1.pos
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hκN : kapN D θ ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨-, -, -, o1, o2⟩ := _root_.GlobalTheory.Amp.Side.both_sides D τ w w' θ W lam₀ A₀ hθ hv hTT hW hA₀
  have n1' : 0 < Module.finrank ℂ W.Wp := by haveI := o1.2.2.1; exact Module.finrank_pos
  have n2' : 0 < Module.finrank ℂ W.Wq := by haveI := o2.2.2.1; exact Module.finrank_pos
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := o1.2.2.2.2.2.2.2.2.1
  obtain ⟨κ, hκ, hdeg⟩ := _root_.GlobalTheory.DegreeTie.deg_eq_mul_fdegH hH D τ w w' θ W hcd hW
  obtain ⟨c, hc0, hnorm⟩ := GlobalTheory.T.uniform_bessel_constant hH hKF hCC _ _ (toBessel D τ w w' θ W lam₀ A₀ hW hA₀ hT hT') W.μG μsec hk hc
    hκN ENNReal.ofReal_ne_top hW.2.2.2.2.2.2.1 hsec
  have hW' := hW
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW'
  let sq : (Fin D.R.k → ℝ) → ℕ → ℝ := fun u n => if h : n - 1 < D.R.k then u ⟨n - 1, h⟩ else 0
  have hsq : ∀ u (i : Fin D.R.k), sq u (i.val + 1) = u i := fun u i => by simp [sq]
  have s1 : SideG D.R.k D.R.rS W.z W.π (sq (uS D w τ)) W.μW W.μN W.μG W.νS :=
    ⟨z1, t1 ▸ hT, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 (t1 ▸ hT) c1 (hsq _), w1, hNH, hG, q1⟩
  have s2 : SideG D.R.k D.R.rS W.z' W.π' (sq (uS D w' τ)) W.μW' W.μN W.μG W.νS' :=
    ⟨z2, t2 ▸ hT', ⟨_, c2⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z2 (t2 ▸ hT') c2 (hsq _), w2, hNH, hG, q2⟩
  obtain ⟨hNum, hcell, heps⟩ := _root_.GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ (hsq _)
  obtain ⟨⟨-, -, -, -, hok⟩, hν⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hNum
  refine ⟨c * κ * (Module.finrank ℂ W.Wp * Module.finrank ℂ W.Wq), by positivity, fun lam' hl A hA => ?_⟩
  obtain ⟨ν, hlam, hn1, -⟩ := GlobalTheory.hcParam_sub_integral _ (lamD D τ) lam' hNum.2.1 hA.1
  have hq : n1 ν ≤ D.R.k * D.R.m ^ 5 := by
    have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h1 : Cn ≤ (D.R.m : ℝ) ^ 2 := by have := hBig.2.2; nlinarith
    have h2 : ((n1 ν : ℕ) : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 5 := by
      rw [hn1]
      calc _ ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := hl
        _ ≤ (D.R.m : ℝ) ^ 2 * D.R.k * (D.R.m : ℝ) ^ 3 := by gcongr
        _ = _ := by ring
    exact_mod_cast h2
  have hgap : GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) := by
    rw [hlam, ← heps]; exact (hν ν hq).2.2.1
  have hDS : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).IsDS (epsSH D.R) lam' := ⟨hA.1, hA.2.1⟩
  have hU := (_root_.GlobalTheory.Amp.Side.both_sides D τ w w' θ W lam' A hθ hv hTT hW hA).1
  obtain ⟨l, b1, e1⟩ := exists_bessel_scale hH hc s1 ⟨A.H, A.σ⟩ hDS hU hgap hok
  obtain ⟨l', b2, e2⟩ := exists_bessel_scale hH hc s2 ⟨A.H, A.σ⟩ hDS hU hgap hok
  obtain ⟨k1, k2, w0, η, hw0, hη, hJ⟩ :=
    GlobalTheory.T.bessel_period_positivity hH D τ w w' θ W lam' A _ l l' hθ hkg hT hT' hW hA hgap hok b1 b2 e1 e2
  have hw0' : w0 ≠ 0 := by
    obtain ⟨P, -, h1, -⟩ := hw0
    rintro rfl
    simp at h1
  obtain ⟨d1, d2⟩ := hdeg lam' A hA w0 hw0'
  have hd : 0 < PI.BesselPeriodGGP.fdegH W.μG A.σ w0 := by
    rw [d1] at d2; exact (mul_pos_iff_of_pos_left hκ).1 d2
  rw [hN] at e1 e2
  have key := hnorm ⟨A.H, A.σ⟩ lam' _ l l' w0 hDS hgap hok hcell e1 e2 k1 k2 hw0
  have h5 := lintegral_weight_smul hk hsec (J := A.J W.μG)
    (J' := amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 W.μG) (η := η) fun γ hγ => hJ W.μG γ hγ hG.2.2.1
  unfold MMv
  rw [← t1, ← t2, h5]
  refine (congrArg _ key).trans ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _), hη, mul_pow, Real.sq_sqrt (by positivity), d1]
  congr 1
  show _ * (c / PI.BesselPeriodGGP.fdegH W.μG A.σ w0 ^ 3) = _
  field_simp

end GlobalTheory.Amp.OpenCellNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibre
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalStabiliserHaar

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, Formalism.UG.hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

theorem linearIndependent_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type)
    [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : HA R σ J) {X : Fin a → Fin n → R ⊗[F] E} (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (g • X) := by
  have hker : LinearMap.ker (lin R σ J g) = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y hxy => ?_
    rw [← lin_inv_lin R σ J g x, hxy, lin_inv_lin]
  exact hX.map' (lin R σ J g) hker

theorem exists_haar_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure ∧ ((fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT)) {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y} = 0 ∧ ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∀ s : (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y) → s y • ratTup (Fv F v) (F0 P) = y) → ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ0 ∂(fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT))) := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP hT μ ν hμ hν fib hfib μG hμG
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := _root_.GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := h5
  haveI := h6
  haveI := h7
  haveI := h8
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HA (Fv F v) σ J) := ⟨rfl⟩
  obtain ⟨-, -, -, -, hfree⟩ := GlobalTheory.T.standardFrame_gram_det_ne_zero F E σ hCM n J hJ r P T hP
  have hx0 := hfree v
  set x0 := ratTup (F := F) (Fv F v) (F0 P) with hx0def
  set S := hermOf (Fv F v) σ (gramE σ J (F0 P)) hT with hS
  have hgram : gramR (Fv F v) σ J x0 = (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :=
    gramR_ratTup (Fv F v) σ J (F0 P)
  obtain ⟨hne, hfin⟩ := _root_.GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib x0 S hx0 hgram
  have hinv := _root_.GlobalTheory.LocalFibreInvariant.fibre_invariant F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib S
  have hcont := (h9 (r + 1)).2
  have hnull : (fib S) {y | ¬ ∃ g : HA (Fv F v) σ J, g • x0 = y} = 0 := by
    refine measure_mono_null (fun y hy => ?_) (hfib.1 S)
    intro hmem
    exact hy (_root_.GlobalTheory.LocalWittFree.exists_smul_ratTup_eq F E σ hCM n J hJ v r P T hP y hmem.2 hmem.1)
  have hsmul : ∀ g : HA (Fv F v) σ J, Continuous
      (fun y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E => g • y) := fun g =>
    hcont.comp (Continuous.prodMk continuous_const continuous_id)
  have hinv' : ∀ (g : HA (Fv F v) σ J) (s : Set (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)),
      MeasurableSet s → (fib S) ((fun y => g • y) ⁻¹' s) = (fib S) s := by
    intro g s hs
    rw [← Measure.map_apply (hsmul g).measurable hs, hinv g]
  have hcpt : ∀ K : Set (HA (Fv F v) σ J), IsCompact K →
      (fib S) ((fun g => g • x0) '' K) < ⊤ := by
    intro K hK
    refine hfin _ (hK.image ?_) ?_
    · exact hcont.comp (Continuous.prodMk continuous_id continuous_const)
    · rintro _ ⟨g, -, rfl⟩
      exact linearIndependent_smul (Fv F v) σ J g hx0
  obtain ⟨μ0, hμ0, hw⟩ := _root_.GlobalTheory.WeilOrbit.weil_formula (HA (Fv F v) σ J) (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) x0
    hcont μG hμG (fib S) hnull hinv' hcpt hne
  exact ⟨μ0, hμ0, hnull, hw⟩

end GlobalTheory.LocalStabiliserHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponentsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelesCmField_eq_zero_of_components : ∀ (L : Type) [Field L] [NumberField L] (a : ReciprocityTheory.Aut.AL L), (∀ v, ReciprocityTheory.Aut.compAt L v a = 0) → a = 0 := by
  first | exact @GlobalTheory.AL_eq_zero_of_compAt | exact GlobalTheory.AL_eq_zero_of_compAt | (intros; apply GlobalTheory.AL_eq_zero_of_compAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InstFactDecLow
section
namespace GlobalTheory.DecTransport

theorem decLow_main : Formalism.FourierDecayAlt.ThreeDimData.DecLow := decLow_holds

end GlobalTheory.DecTransport
end

