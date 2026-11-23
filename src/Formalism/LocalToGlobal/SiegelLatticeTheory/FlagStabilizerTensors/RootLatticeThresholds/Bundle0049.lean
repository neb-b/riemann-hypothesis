module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0047
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinJB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotGeo
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbVecFin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BlockScaling
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdAtPlaceBounds

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsAddFin
section
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsAddFin

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem eHom_fin (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
    FiniteDimensional ℂ (X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) := by
  have hint := Formalism.L2.SG.Pf.RowDictPf.hint_of_gap X hG
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re
    X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hint X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens
    X.B.tens_spec
  have : FiniteDimensional ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) :=
    Formalism.L2.SG.Pf.RowDictPf.finiteDimensional_HHX_of_gap X hHC hG
  exact Formalism.L2.SG.RowsDef.finiteDimensional_eHom hB.1 hB.2

theorem rowsAdd_holds (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : RowsAdd X :=
  Formalism.L2.SG.Pf.AllRowsAdd.rowsAdd_of X (eHom_fin X hHC hG)

end Formalism.L2.SG.Pf.AllRowsAddFin
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTTypes
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

def CapFromHC : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (u : Fin k → ℝ) (π : Formalism.FourierDecayAlt.Q.Mx k r → (Wp →L[ℂ] Wp)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π → ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) →
    PI.UpqRep.IsHCTypeW k r z u π →
    Formalism.FourierDecayAlt.Q.CapParam k r z π (fun i => if h : i - 1 < k then u ⟨i - 1, h⟩ else 0)

section Block

variable {k r : ℕ}

theorem mvs {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : (M *ᵥ Pi.single j (1 : ℂ)) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem blockW_fix (h : Matrix (Fin k) (Fin k) ℂ) (j : Fin (2 * r + k + 1)) (hj : ¬ (r ≤ j.val ∧ j.val < r + k)) :
    Formalism.MainNotions.S.blockW k r h *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j := by
  funext i
  unfold Formalism.QuantumDeterminants.bvec
  rw [mvs]
  unfold Formalism.MainNotions.S.blockW
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dite_eq_left hi, dite_eq_right hj, Pi.single_apply, if_neg]
    intro e; rw [e] at hi; exact hj hi
  · rw [dite_eq_right hi, Pi.single_apply]

theorem blockW_UH (h : Matrix (Fin k) (Fin k) ℂ) (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (Formalism.MainNotions.S.blockW k r h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.QuantumDeterminants.Hpk k r
  have hs : hᴴ * h = 1 := Matrix.mem_unitaryGroup_iff'.mp hh
  have e1 : (Formalism.MainNotions.S.blockW k r h)ᴴ = Formalism.MainNotions.S.blockW k r hᴴ := PI.HwUniqW.blockW_conjTranspose h
  have e2 : Formalism.QuantumDeterminants.Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r h * Formalism.QuantumDeterminants.Hpk k r :=
    PI.HwUniqW.Hpk_blockW_comm h
  have e3 : Formalism.MainNotions.S.blockW k r hᴴ * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r (hᴴ * h) :=
    PI.HwUniqW.blockW_mul hᴴ h
  have e4 : Formalism.MainNotions.S.blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := PI.HwUniqW.blockW_one
  rw [e1, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, e3, hs, e4, Matrix.one_mul]

theorem conj_blockW_mem {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : Formalism.MainNotions.S.IsFrameW k r z g) (h : Matrix (Fin k) (Fin k) ℂ) (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g * Formalism.MainNotions.S.blockW k r h * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := by
  obtain ⟨hgU, hge, hgz⟩ := hg
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hgU
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hgU
  have hinv : ∀ x, g *ᵥ x = x → g⁻¹ *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
  have hfix : ∀ x, g *ᵥ x = x → Formalism.MainNotions.S.blockW k r h *ᵥ x = x → (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) *ᵥ x = x :=
    fun x h1 h2 => by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv x h1, h2, h1]
  refine ⟨PI.HwUniqW.mul_mem_UH (PI.HwUniqW.mul_mem_UH hgU (blockW_UH h hh)) (PI.HwUniqW.inv_mem_UH hgU),
    fun a => ⟨hfix _ (hge a).1 (blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.eI]; omega)),
      hfix _ (hge a).2 (blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.esI]; omega))⟩, ?_⟩
  have hx : ∀ x, g⁻¹ *ᵥ (g *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
  rw [← hgz, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul,
    blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.wI, Fin.val_last]; omega)]

end Block

theorem isType_of_hc (hcap : CapFromHC) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.Q.Mx k r → (Wp →L[ℂ] Wp)}
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hHC : Formalism.MainNotions.S.IsHCTypeW k r z u π)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π ∧
      (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, ‖π h x‖ = ‖x‖) ∧ ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z))
    (w : ℕ → ℝ) (hw : ∀ i ∈ Finset.Icc 1 k, w i = if h : i - 1 < k then u ⟨i - 1, h⟩ else 0) :
    Formalism.FourierDecayAlt.Q.IsType k r z π w := by
  obtain ⟨g, hg, hU⟩ := hHC
  refine ⟨hU.1, hrep.1, hrep.2.2, hrep.2.1, fun S hS => ?_, ?_⟩
  · have hK := hU.2.2.2.2.2.1 S le_top (fun h hh v hv => hS _ (conj_blockW_mem hg h hh.1) v hv)
    exact hK
  · intro Bs hBs x v
    rw [hcap Wp k r z u π hz hT hrep.1 hrep.2.2 ⟨g, hg, hU⟩ Bs hBs x v]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by rw [hw i hi]

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXCap
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isHCParam_cast {m n : ℕ} (h : m = n) (f : Fin n → ℝ) (hf : Formalism.QuantumDeterminants.IsHCParam f) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin m => f (Fin.cast h i)) := by
  subst h
  exact hf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem isHCParam_lamX (w : InfinitePlace X.B.I.F) : Formalism.QuantumDeterminants.IsHCParam (X.B.lam w) := by
  have hf := Formalism.MainNotions.S.Inh.amp_isHCParam_lamSH D.R (D.hc (X.pl w))
  have e : X.B.lam w = fun i => lamSH D.R (D.hc (X.pl w)) (Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) i) := by
    funext i
    rw [X.lam_eq]
    rfl
  rw [e]
  exact isHCParam_cast _ _ hf

theorem gap_X {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 1000 ≤ Cl)
    (hk : 1801 ≤ D.R.k) (w : InfinitePlace X.B.I.F) :
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h := by
  refine ⟨Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L, ?_, ?_⟩
  · have hg := Formalism.MainNotions.BridgeLemma.szh_gap hS0 (X.pl w)
    set c : Fin X.B.I.n → Fin (2 * D.R.rS + D.R.k + 1) := Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) with hc
    have ea : ∀ a, X.B.I.ε w a = epsSH D.R (c a) := fun a => by rw [X.eps_eq]; rfl
    have la : ∀ a, X.B.lam w a = lamSH D.R (D.hc (X.pl w)) (c a) := fun a => by rw [X.lam_eq]; rfl
    intro a b hab
    rw [la a, la b]
    exact hg (c a) (c b) (by rwa [ea a, ea b] at hab)
  · have hn : (D.R.r : ℝ) = (X.B.I.n : ℝ) := by rw [X.n_eq]
    have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
    have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
    have hn900 : (900 : ℝ) ≤ (X.B.I.n : ℝ) := by
      rw [← hn, hr]; push_cast
      have : (1801 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
      have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _
      linarith
    have hthr := Formalism.MainNotions.GapDS.thrX_le (X.B.I.ε w) hn900
    rw [← hn] at hthr
    have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) (X.pl w)
    have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
    have hL : (1 / 2 : ℝ) ≤ large₂.sc.L := by
      by_contra hcn
      push Not at hcn
      have h1 : Real.exp (2 * large₂.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
      have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
      linarith
    have hf : (2 : ℝ) ≤ (D.R.f : ℝ) := by
      have : 2 ≤ D.R.f := by
        unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
      exact_mod_cast this
    have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
      have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf 5
      norm_num at this; linarith
    have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by
      rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
    have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
    have h3 : (D.R.r : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have e3 : 1000 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right hCl hn19
    have hr0 : (0 : ℝ) < (D.R.r : ℝ) ^ 19 := by positivity
    linarith

theorem smooth_tr {n m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (J : Matrix (Fin n) (Fin n) ℂ) (K : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (h3 : Qᴴ * J * Q = K) (b : H) (hs : Formalism.QuantumDeterminants.SmoothOnH K (fun x => σ (Q * x * Qi) b)) :
    Formalism.QuantumDeterminants.SmoothOnH J (fun g => σ g b) := by
  have h2' : Qiᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have hU : ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.QuantumDeterminants.inUH J g → Formalism.QuantumDeterminants.inUH K (Qi * g * Q) := by
    intro g hg
    have hg' : gᴴ * J * g = J := hg
    show (Qi * g * Q)ᴴ * K * (Qi * g * Q) = K
    rw [← h3]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qiᴴ Qᴴ, h2', Matrix.one_mul, ← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
    rw [← Matrix.mul_assoc gᴴ J, ← Matrix.mul_assoc (gᴴ * J) g, hg']
  have hback : ∀ g : Matrix (Fin n) (Fin n) ℂ, Q * (Qi * g * Q) * Qi = g := by
    intro g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  let Lφ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun g => Qi * g * Q
      map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  have hφ : ContDiff ℝ ⊤ (fun g : Matrix (Fin n) (Fin n) ℂ => Qi * g * Q) :=
    (LinearMap.toContinuousLinearMap Lφ).contDiff
  intro g₀ hg₀
  obtain ⟨U, F, hUo, h0, hF, hE⟩ := hs (Qi * g₀ * Q) (hU g₀ hg₀)
  refine ⟨(fun g => Qi * g * Q) ⁻¹' U, fun g => F (Qi * g * Q), hUo.preimage hφ.continuous, h0,
    hF.comp (hφ.of_le le_top).contDiffOn (fun g hg => hg), ?_⟩
  intro g hgU hgJ
  have := hE _ hgU (hU g hgJ)
  simp only [hback] at this
  exact this

variable {θ : ℝ} (C : Choice X θ)


variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] in
theorem coefCap_ITc {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 1000 ≤ Cl)
    (hk : 1801 ≤ D.R.k) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hkb : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j)) :
    CoefCap (ITc X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c i0' Θ TP A₀) := by
  have hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)) := by
    intro j
    have hsmv : Formalism.MainNotions.S.IsSmoothVec (k := D.R.k) (r := D.R.rS)
        (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j) :=
      Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth D.R.k D.R.rS (epsSH D.R) (lamD D (e (plE D j))) _
        (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _)
        (Formalism.L2.SG.Pf.dsTr C (e (plE D j))) (b j) (hkb j)
    obtain ⟨h1, h2, h3, -⟩ := C.isT (e (plE D j))
    exact smooth_tr (X.B.σ (vOf X (e (plE D j)))) _ _ (C.Q (e (plE D j))) (C.Qi (e (plE D j))) h1 h2 h3 (b j) hsmv
  exact coefCap_carrierInT X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀
    hb (isHCParam_lamX X) (gap_X X hS0 hCl hk)

end Formalism.L2.SG.Pf.CarrierXAll
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXJointAt
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

theorem jointTensorAt_of_carrier (I : CarrierIn X u u') (Mo : ModelsFor (sOf I)) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hN : NuQPin X u u' νq) (hG : JointQuot.StVGeo X u u') (hpin : JointPin.PinCov (CarrierOf I Mo))
    (hRT : JointPinJB.RelTr (CarrierOf I Mo) sc i0 i0') (hOV : JointPinJB.OrbVecAt (CarrierOf I Mo) sc i0 i0')
    (hsc : 0 < sc) (hFX : (CarrierOf I Mo).FromX) (hBase : (CarrierOf I Mo).Base i0 i0')
    (hEmb : ∀ j x, (CarrierOf I Mo).S.emb j (X.ιE x) = X.B.I.φ ((CarrierOf I Mo).τ j) x)
    (hBuilt : (CarrierOf I Mo).Built) :
    JointTensorAt X u u' (sOf I) I.T I.fc I.ν' I.m₀ I.τ I.eP I.eQ sc i0 i0' νq :=
  JointPin.jointTensor_of_pin (CarrierOf I Mo) sc i0 i0' νq hN (JointQuot.stRel_holds X u u')
    (JointQuot.locUni_of X u u' hG) (JointQuot.globProd_of X u u' hG) hpin
    (JointPinJB.jointBridge_of_open _ sc i0 i0' hRT hOV) hsc hFX hBase hEmb hBuilt

theorem jointTensorAt_carrierInOf (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : Formalism.L2.SG.Pf.Carrier.PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀)))
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hN : NuQPin X u u' νq) (hG : JointQuot.StVGeo X u u')
    (hpin : JointPin.PinCov (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo))
    (hsc : 0 < sc)
    (hFX : (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).FromX)
    (hBase : (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).Base i0 i0')
    (hEmb : ∀ j x, (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).S.emb j
      (X.ιE x) = X.B.I.φ ((CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).τ j) x)
    (hBuilt : (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).Built) :
    JointTensorAt X u u' (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀))
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).T
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).fc
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).ν'
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).m₀
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).τ
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).eP
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).eQ sc i0 i0' νq := by
  have hMP : MeasPinAt X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0' :=
    Formalism.L2.SG.Pf.Carrier.measPinAt_of X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo
      sc hsc i0 i0' hFX hBase hEmb (fun _ => (hBuilt.2 _).2.2.1)
  refine jointTensorAt_of_carrier _ Mo sc i0 i0' νq hN hG hpin ?_ ?_ hsc hFX hBase hEmb hBuilt
  · intro h1 h2 h3 h4 h5
    exact relTr_carrierOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0' h1 h2 h3 h4 h5
  · intro h1 h2 h3 h4 h5
    exact orbVecAt_carrierOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0'
      (fun v => (h5.2 _).2.2.1) hMP h1 h2 h3 h4


open scoped Matrix in
open Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf in
set_option maxHeartbeats 4000000 in
theorem jointTensorAt_ITcMo (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : Formalism.L2.SG.Pf.Carrier.PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)))
    (sc : ℝ) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq)
    (hpin : JointPin.PinCov (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) Mo))
    (hsc : 0 < sc) (hBuilt : (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) Mo).Built) :
    JointTensorAt X u u' (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).ν'
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).m₀
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eP
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eQ sc i0 i0' νq := by
  have hG : JointQuot.StVGeo X u u' :=
    JointQuot.stVGeo_of_sec X u u' (Formalism.L2.S.L6.UnitaryStandardVectors.stVSec_holds X u u')
  have hFX := BaseOf.fromX X C u u' e he hv CA de de' l grid grid1 fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
    (nuE X C u' e i0') (m0E X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (nuE X C u' e i0' j)
      (m0E X C u u' e j) (Θ j) (TP j)) A₀ Mo
  have hQ : ∀ v, (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Q v *
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Qi v = 1 :=
    fun v => (isTransp_cs (Formalism.L2.SG.Pf.torTie X) C (X.pl v)).2.1
  have hBase := base_carrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) Mo i0 i0' hQ hi
    (fun j => rfl) (fun j => rfl)
  have hEmb := emb_carrierInOf e he hv C CA de de' l grid grid1 (towersOf X C u u' e) (Tz_towersOf_base_eq_T X C u u' e) fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
    (nuE X C u' e i0') (m0E X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (nuE X C u' e i0' j)
      (m0E X C u u' e j) (Θ j) (TP j)) A₀
  exact jointTensorAt_carrierInOf X u u' e he hv C CA de de' l grid grid1 (towersOf X C u u' e)
    (Tz_towersOf_base_eq_T X C u u' e) fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
    (nuE X C u' e i0') (m0E X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (nuE X C u' e i0' j)
      (m0E X C u u' e j) (Θ j) (TP j)) A₀ Mo sc i0 i0' νq hN hG hpin hsc hFX hBase hEmb hBuilt

theorem TT_nonneg (I : CarrierIn X u u') (v : Fin (sOf I).f) : 0 ≤ (Formalism.FourierDecayAlt.D.parOf (sOf I) v).TT := by
  show 0 ≤ (((D.mem u).A.T : ℕ) : ℝ) * (((D.mem u').A.T : ℕ) : ℝ)
  positivity

def modelsOf (I : CarrierIn X u u') : ModelsFor (sOf I) where
  L := fun v => (Formalism.FourierDecayAlt.P.level_exists_alt (Formalism.FourierDecayAlt.D.parOf (sOf I) v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf (sOf I) v)) (Formalism.FourierDecayAlt.P.analytic_laws _ _ (TT_nonneg I v))).choose
  j := fun _ _ => 0
  lam := fun _ _ => 0
  c := Formalism.L2.SG.Pf.CarrierT.cutStd
  Cm := fun _ => 0
  σ := fun _ => 0
  Lw := fun _ _ => 0
  Ll := fun _ _ _ => 0
  Ll' := fun _ _ _ => 0


open scoped Matrix in
open Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf in
set_option maxHeartbeats 4000000 in
theorem jointTensor_compact_test (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : Formalism.L2.SG.Pf.Carrier.PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (sc : ℝ) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq)
    (hpin : JointPin.PinCov (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)
      (modelsOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))))
    (hsc : 0 < sc) (hBuilt : (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)
      (modelsOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))).Built) :
    JointTensorAt X u u' (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).ν'
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).m₀
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eP
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eQ sc i0 i0' νq :=
  jointTensorAt_ITcMo X C u u' e he hv CA de de' l grid grid1 fc c i0 i0' hi Θ TP A₀ (modelsOf _) sc νq hN hpin hsc hBuilt

end Formalism.L2.SG.Pf.CarrierXAll
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdLevels
section
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ThresholdLevels

variable (C0 : ℝ)

theorem thrRow_holds {𝒞 : FamClass} : ∀ CA : ℝ, 1 ≤ CA → Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
    AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
      ∀ u u' : (Fm.D x i).what₂.Word, u ≠ u' → Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces CA (Fm.D x i) u u' := by
  intro CA hCA

  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 40⟩, fun Fm CH _ hL => ?_⟩⟩
  have h40 : (40 : ℝ) ≤ sCl Fm := (le_sC'_sCl hL).2
  refine ⟨0, fun x _ i hH u u' _ => ?_⟩
  obtain ⟨hD, hHy, _⟩ := hH
  exact ThresholdOrder.thrAt_of_pos CA (Fm.D x i) u u' (ThresholdAtPlaceBounds.thrSet_pos_at hD hHy h40 _ hCA u u')

end Formalism.L2.SG.Pf.ThresholdLevels
end
end

