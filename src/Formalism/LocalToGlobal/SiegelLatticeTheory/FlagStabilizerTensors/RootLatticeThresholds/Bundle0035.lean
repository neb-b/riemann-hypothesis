module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCov
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPin

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem choose_congr {α : Sort*} {p q : α → Prop} (e : p = q) (h : ∃ x, p x) (h' : ∃ x, q x) :
    h.choose = h'.choose := by
  subst e; rfl

theorem orbIntegrand_smul (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ) (p : Formalism.FourierDecayAlt.B.SS k r) :
    Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p = c • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p := by
  unfold Formalism.FourierDecayAlt.D.orbIntegrand Formalism.FourierDecayAlt.B.rho
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem orbJ_smulF (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) {c : ℂ} (hc : c ≠ 0) :
    Formalism.FourierDecayAlt.D.orbJ D γ μ (fun g => c • F g) = c • Formalism.FourierDecayAlt.D.orbJ D γ μ F := by
  have hP : (fun θ => Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
      (fun θ => Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS) := by
    funext θ
    have e : (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) =
        c • (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) := by
      funext p; rw [orbIntegrand_smul, smul_comm]; rfl
    rw [e, integrable_smul_iff hc]
  have e2 : ∀ θ : Formalism.FourierDecayAlt.B.SS k r → ℝ, (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) =
      fun p => c • (θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) := fun θ => by
    funext p; rw [orbIntegrand_smul, smul_comm]
  unfold Formalism.FourierDecayAlt.D.orbJ
  by_cases h2 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS
  · have h1 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS := by
      rw [show (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
        ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS from congrArg Exists hP]
      exact h2
    rw [dite_eq_left h1, dite_eq_left h2, choose_congr hP h1 h2, e2, integral_smul]
  · have h1 : ¬ ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS := by
      rw [show (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
        ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS from congrArg Exists hP]
      exact h2
    rw [dite_eq_right h1, dite_eq_right h2, smul_zero]

end Lin

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

end Formalism.L2.SG.Pf.Carrier.CarPin
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGPhiOfNeZeroAndLtInfty
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped ENNReal
open Matrix

set_option linter.unusedVariables false

namespace Formalism.L2.SG.Pf.GoodS

theorem nu_conc {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hS : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS) (hq : Formalism.MainNotions.S.IsQuotMeas μG μS ν) :
    ν {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 := by
  classical
  have hUH : ∀ a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro a b ha hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']
  have hSG : ∀ M, M ∈ Formalism.QuantumDeterminants.Sset k r z → M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rintro M ⟨g, hg, m, hm, rfl⟩
    exact hUH g m hg.1 hm.1
  have hc : Continuous fun x : Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x := by
    have h0 : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => Matrix.of x := continuous_id
    exact (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
  have hBm : MeasurableSet
      {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
    have hcl : IsClosed {x : Formalism.QuantumDeterminants.Mt k r |
        (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r} :=
      isClosed_eq hc continuous_const
    exact hcl.measurableSet.compl
  have hq1 := hq
    ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
      fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hBm)
  rw [lintegral_indicator_const hBm, hG.2.2.1, mul_zero] at hq1
  have hpt : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
        fun _ => μS Set.univ) x ≤
      ∫⁻ s, ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
        fun _ => (1 : ℝ≥0∞)) (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
    · have hnm : x ∉ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
        fun h => h hx
      rw [Set.indicator_apply, if_neg hnm]
      exact bot_le
    · have hxm : x ∈ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := hx
      rw [Set.indicator_apply, if_pos hxm]
      calc μS Set.univ = ∫⁻ _, (1 : ℝ≥0∞) ∂μS := lintegral_one.symm
        _ ≤ _ := by
          apply lintegral_mono_ae
          have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Formalism.QuantumDeterminants.Sset k r z := ae_iff.mpr hS.2.2.1
          filter_upwards [hae] with s hs
          have hsG : (Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of s = Formalism.QuantumDeterminants.Hpk k r :=
            hSG _ hs
          have hmem : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈
              {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
            show ¬ (Matrix.of (fun i j => (Matrix.of s * Matrix.of x) i j) ∈
              Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
            intro hG'
            have e : (Matrix.of s * Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r *
                (Matrix.of s * Matrix.of x) = Formalism.QuantumDeterminants.Hpk k r := hG'
            apply hx
            show (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r
            rw [Matrix.conjTranspose_mul] at e
            calc (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x
                = (Matrix.of x)ᴴ * ((Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of s) *
                    Matrix.of x := by rw [hsG]
              _ = Formalism.QuantumDeterminants.Hpk k r := by simpa only [Matrix.mul_assoc] using e
          simp only [Set.indicator_of_mem hmem, le_refl]
  have hle := lintegral_mono (μ := ν) hpt
  rw [lintegral_indicator_const hBm, ← hq1] at hle
  have hpos : μS Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr hS.2.1).ne'
  rcases mul_eq_zero.mp (nonpos_iff_eq_zero.mp hle) with h | h
  · exact absurd h hpos
  · exact h

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (m : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS) (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    phiOf hB u τ m = wT C u τ (m * C.y τ) := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hy := C.y_mem τ
  obtain ⟨hrep, -⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hm hy
  have hJ : (C.Q τ * (m * C.y τ) * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * (m * C.y τ) * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    have hmy' : (m * C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (m * C.y τ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hmy
    calc (C.Q τ * (m * C.y τ) * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * (m * C.y τ) * C.Qi τ)
        = (C.Qi τ)ᴴ * ((m * C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * (m * C.y τ)) *
            C.Qi τ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hmy', qiHqi _ h2 hg]
  set γ := toUJn (C.Q τ * (m * C.y τ) * C.Qi τ) hJ
  have hγ : uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ := rfl
  have hW := (hB u τ).choose_spec.2 γ
  have e1 : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) = X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ)) := by
    unfold v0Of
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hm _ hy, hγ]
    rfl
  unfold phiOf bOf
  rw [e1, ← hW, ← Formalism.L2.SG.Pf.WuBL.wT_at C u τ γ, hγ]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem l2SG_phiOf_ne_zero_and_lt_infty (C : Choice X θ) (hLF : LocFactor C) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤ := by
  obtain ⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩ := hLF u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  have hHG := Formalism.L2.SG.Pf.haarTr C τ
  have hq := C.nuS_q u τ
  have hy := C.y_mem τ
  have hconc := nu_conc hz hT hHG hSH hq
  have hπ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT (Formalism.L2.SG.Pf.colsTypeTr C u τ)
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
    rintro _ ⟨h0, hh0, n0, hn0, rfl⟩ x hx
    rw [hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, Formalism.L2.SG.Pf.WuBL.norm_psi, one_mul, hπ.2.1 h0 hh0]
  have heq := Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm D.R.k D.R.rS _ hz hT _ _ _ hHG hSH hq _ (wT C u τ) hWc
    (Formalism.L2.SG.Pf.WuBL.wT_off C u τ) hinv (C.y τ) hy
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hphi : l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) := by
    unfold l2SG
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [phi_eq C hB u τ _ hx]
  rw [hphi, heq]
  exact ⟨hne, hfin⟩

end Formalism.L2.SG.Pf.GoodS
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MonoZhMulVec
section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ) (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1))
  (blk : Fin (r + 1) → ℕ)
  (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

def kap (x : Fin N → ℂ) : Fin (r + 1) ⊕ Fin (r + 1) → ℂ :=
  ((Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G)⁻¹ *ᵥ (((Wfg F G)ᴴ * Formalism.REAL.Jm ε) *ᵥ x)

include hFF hGG hπ hZ hgap in
theorem kap_eq (x : Fin N → ℂ) :
    Matrix.fromBlocks (lastDiag (-(T : ℂ))) (Zm ε F G) (Zm ε F G)ᴴ (lastDiag (-(T' : ℂ))) *ᵥ kap ε F G x =
      Sum.elim (fun a => hJ ε (F a) x) (fun b => hJ ε (G b) x) := by
  rw [← gram_eq ε F G T T' π hFF hGG hπ hZ, kap, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap), Matrix.one_mulVec, wjx]

theorem Yc_sub (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : Fin N → ℂ) :
    Yc ε F G C *ᵥ x - x = ∑ a, ((Am ε F G C - 1) *ᵥ (kap ε F G x ∘ Sum.inl)) a • F a +
      ∑ b, ((C - 1) *ᵥ (kap ε F G x ∘ Sum.inr)) b • G b := by
  unfold Yc
  rw [Ymat_sub, Wfg_mulVec]
  unfold Mm
  rw [Matrix.fromBlocks_mulVec]
  simp [kap]

include hπ hZ in
theorem monoZ_mulVec (v : Fin (r + 1) → ℂ) (a : Fin (r + 1)) : (Zm ε F G *ᵥ v) a = Zm ε F G a (π a) * v (π a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π a)]
  · intro j _ hj
    have : Zm ε F G a j = 0 := by by_contra h; exact hj (by rw [(hZ a j).1 h, hπ])
    rw [this, zero_mul]
  · simp

include hπ hZ in
theorem monoZh_mulVec (v : Fin (r + 1) → ℂ) (b : Fin (r + 1)) :
    ((Zm ε F G)ᴴ *ᵥ v) b = starRingEnd ℂ (Zm ε F G (π b) b) * v (π b) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π b)]
  · simp [Matrix.conjTranspose_apply]
  · intro j _ hj
    have : Zm ε F G j b = 0 := by by_contra h; exact hj ((hZ j b).1 h)
    simp [Matrix.conjTranspose_apply, this]
  · simp

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpF {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ a, a ≠ Fin.last r → hJ ε (F a) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (F '' {a | a ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hG0 : ∀ j, j ≠ π (Fin.last r) → κ (Sum.inr j) = 0 := by
    intro j hj
    have ha : π j ≠ Fin.last r := fun h => hj (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inl (π j))
    simp only [Sum.elim_inl, Pi.add_apply] at h1
    rw [hx _ ha, lastDiag_mulVec, Pi.single_apply, if_neg ha, zero_add, monoZ_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : Zm ε F G (π j) j ≠ 0 := (hZ _ _).2 rfl
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have h2 : ∑ b, ((C - 1) *ᵥ (κ ∘ Sum.inr)) b • G b = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) b = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hC, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hG0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, add_zero]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a = Fin.last r
  · subst ha
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
      rw [Matrix.sub_apply, rowLast blk hA, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpG {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ b, b ≠ Fin.last r → hJ ε (G b) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (G '' {b | b ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hF0 : ∀ i, i ≠ π (Fin.last r) → κ (Sum.inl i) = 0 := by
    intro i hi
    have hb : π i ≠ Fin.last r := fun h => hi (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inr (π i))
    simp only [Sum.elim_inr, Pi.add_apply] at h1
    rw [hx _ hb, lastDiag_mulVec, Pi.single_apply, if_neg hb, add_zero, monoZh_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : starRingEnd ℂ (Zm ε F G i (π i)) ≠ 0 := by
      rw [map_ne_zero]; exact (hZ _ _).2 (hπ i).symm
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
  have h2 : ∑ a, ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a • F a = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hA, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hF0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, zero_add]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : b = Fin.last r
  · subst hb
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Matrix.sub_apply, rowLast blk hC, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

