module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0060
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0033

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCell
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

theorem cj_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) :
    cj k r κ τ h = h := by
  ext i j
  rw [cj_apply]
  by_cases h0 : h i j = 0
  · rw [h0, mul_zero]
  · have e := fix_gen (fun i => ((tV k r κ τ i : ℝ) : ℂ)) 1 (fun i h1 h2 => by simp [tV_wb i h1 h2]) hh.1 hh.2.1 i j h0
    have e' : tV k r κ τ i = tV k r κ τ j := by exact_mod_cast e
    rw [e', inv_mul_cancel₀ (tV_pos hκ hτ j).ne']
    simp

theorem map_cjT_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)}
    (h : IsHaarOn (UWset k r z) μ) : μ.map (cjT k r κ τ) = μ := by
  have hae : cjT k r κ τ =ᵐ[μ] id := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) h.2.2.1
    simp only [Set.mem_ofPred_eq] at hx ⊢
    intro hU
    apply hx
    funext i j
    show cj k r κ τ (Matrix.of x) i j = x i j
    rw [cj_UW hκ hτ hU]; rfl
  rw [Measure.map_congr hae, Measure.map_id]

theorem haarProb_unique {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn (UWset k r z) μ) (hμ1 : μ Set.univ = 1) (hν : IsHaarOn (UWset k r z) ν) (hν1 : ν Set.univ = 1) :
    μ = ν := by
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  have hC := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hK := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT
  have fin : ∀ (m : Measure (Mt k r)), m Set.univ = 1 → ∀ K : Set (Mt k r), IsCompact K → m K < ⊤ :=
    fun m hm K _ => (measure_mono (Set.subset_univ K)).trans_lt (by rw [hm]; exact ENNReal.one_lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 μ hC h0 hμ.2.2.1 hμ.2.2.2 (fin μ hμ1)
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 ν hC h0 hν.2.2.1 hν.2.2.2 (fin ν hν1)
  have hfin : μ0 Set.univ ≠ ⊤ := by
    have hle := measure_univ_le_add_compl (μ := μ0) (UWset k r z : Set (Mt k r))
    have hc0 : μ0 (UWset k r z : Set (Mt k r))ᶜ < ⊤ := (le_of_eq h0.conc).trans_lt ENNReal.zero_lt_top
    exact (lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨h0.finite_compact _ hK, hc0⟩)).ne
  have hne : μ0 Set.univ ≠ 0 := by
    intro h; apply h0.ne_zero; rw [← Measure.measure_univ_eq_zero]; exact h
  have e1 : (c : ENNReal) * μ0 Set.univ = 1 := by rw [← hμ1, hc]; rfl
  have e2 : (d : ENNReal) * μ0 Set.univ = 1 := by rw [← hν1, hd]; rfl
  have hcd : (c : ENNReal) = d := by
    have := e1.trans e2.symm
    exact (ENNReal.mul_left_inj hne hfin).mp this
  rw [hc, hd, ENNReal.coe_injective hcd]

section Choice

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem muWc_eq (u : D.what₂.Word) (τ : D.what₂.Tau) (hz : inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ))
    (hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1) := by
  rw [map_cjT_UW (inv_pos.mpr (kaB_pos D)) one_pos (C.muW_haar u τ)]
  show (μW_exists X C u (vOf X τ)).choose = _
  obtain ⟨h1, h2⟩ := (μW_exists X C u (vOf X τ)).choose_spec
  generalize (μW_exists X C u (vOf X τ)).choose = m at h1 h2 ⊢
  have hS : UWset D.R.k D.R.rS (zc X C u (vOf X τ)) = UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [zc_vOf_eq_zB_of_inWb C u u τ hz, UWset_smul one_pos]
  rw [hS] at h1
  exact haarProb_unique hz hT h1 h2 (C.muW_haar u τ) (C.muW_one u τ)

end Choice

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellS
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

def HaarTr (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
      μRv →
    IsHaarOn (RStab D.R.k D.R.rS (gB C τ γ)) (muRB C τ μRv)

def QuotTr (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
      μRv →
    IsQuotLoc μRv ν →
    PI.BesselPeriodGGP.IsQuotMeas (locW C u u' τ).μG
      ((muRB C τ μRv).map (fun x i j => ((gB C τ γ)⁻¹ * Matrix.of x * gB C τ γ) i j))
      (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ))

def PinHypAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) : Prop :=
  0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C6.IsRelevant (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
    (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) ∧
  IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
    μRv ∧ IsQuotLoc μRv ν

def CutAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
          (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x))) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ)
        (fcAt C u u' τ a b ξ ξ' c) p) (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).μSS

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsLowUnitHBaseVector
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf

theorem isLowUnitH_base_vector {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) := by
  obtain ⟨P, hP, hmem⟩ := C.y_low τ
  refine ⟨P, hP, ?_, hmem⟩
  obtain ⟨-, hiso⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  show ‖X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))‖ = 1
  rw [← (X.low (vOf X τ)).1]
  exact hiso (C.y τ) (C.y_mem τ) (X.B.w (vOf X τ))


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem goodSRest_all {D : D7} {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hT : Formalism.BasicNotions.dsigTie D) {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    GoodSRest hB u u' τ :=
  goodSRest_of_loc (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) hB u u' τ
    (Formalism.L2.SG.Pf.WuDec.lowSmoothSK (dsTr C τ) (isLowUnitH_base_vector C τ)) hT

end Formalism.L2.SG.Pf
end
end

