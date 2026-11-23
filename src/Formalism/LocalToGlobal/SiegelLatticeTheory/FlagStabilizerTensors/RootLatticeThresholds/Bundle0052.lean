module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0035
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0091

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsDcount
section
noncomputable section

open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsDcount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsAdd

variable {D : D7} (X : HidaSetting D)

theorem reT_rph (S : Set (Tup2 D)) : (ReT X S).comp X.Rph = X.Rph.comp (ReT X S) := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
    X.Rph_spec, X.Rph_spec]
  congr 1
  funext g
  rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    reT_comm]

theorem HH_eq_VT (t : Tup2 D) :
    Formalism.L2.SG.RowsDef.HH X.B.I X.B.μf X.B.fund (ReT X {t}) X.Rph = Formalism.L2.SG.Pf.RowsGoodRed.VT X t := by
  have hPE : (ReT X {t}).comp X.B.Re = ReT X {t} := by
    rw [← reT_univ' X, reT_inter, Set.inter_univ]
  have hEP : X.B.Re.comp (ReT X {t}) = ReT X {t} := by
    rw [← reT_univ' X, reT_inter, Set.univ_inter]
  have hPP : (ReT X {t}).comp (ReT X {t}) = ReT X {t} := by
    rw [reT_inter, Set.inter_self]
  have hR := reT_rph X {t}
  apply le_antisymm
  · rintro v ⟨y, rfl⟩
    refine ⟨⟨ReT X {t} y, ?_⟩, ?_⟩
    · show X.B.Re (X.Rph (ReT X {t} y)) = ReT X {t} (X.Rph y)
      have := congrArg (fun L => L y) hR
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [← this]
      have := congrArg (fun L => L (X.Rph y)) hEP
      simpa only [ContinuousLinearMap.comp_apply] using this
    · show ReT X {t} (ReT X {t} (X.Rph y)) - ReT X {t} (X.Rph y) = 0
      have := congrArg (fun L => L (X.Rph y)) hPP
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this, sub_self]
  · rintro v ⟨⟨y, hy⟩, hv⟩
    have hv' : ReT X {t} v = v := by
      have : ReT X {t} v - v = 0 := hv
      exact sub_eq_zero.1 this
    refine ⟨y, ?_⟩
    show ReT X {t} (X.Rph y) = v
    have hy' : X.B.Re (X.Rph y) = v := hy
    rw [← hv', ← hy']
    have := congrArg (fun L => L (X.Rph y)) hPE
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this.symm

theorem dcountEq_holds (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : Formalism.L2.SG.Pf.RowsGoodRed.DcountEq X := by
  intro t _ _
  have hint := Formalism.L2.SG.Pf.RowDictPf.hint_of_gap X hG
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec (eT X {t})
    (ReT X {t}) (reT_spec X (etInt_holds X) {t}) X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1)
    (fun v => (X.ds v).2.2.2.1) (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hint X.Rph X.Rph_spec
    X.B.Hs X.B.σs X.B.tens X.B.tens_spec
  delta dimX
  rw [← Formalism.L2.SG.RowsDef.finrank_HH_eq_Dcount hB.1 hB.2, HH_eq_VT]

end Formalism.L2.SG.Pf.AllRowsDcount
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWin
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.AmpWin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

def kap (τ : D.what₂.Tau) : ℝ := Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ)

def AmpWinP : Prop :=
  (∏ τ, kap u u' C hB τ) * c0X X u (Y.FN u) * c0X X u' (Y.FN u') =
    X.volK2 ^ 2 * (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u')

def MassU : Prop :=
  (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal =
    Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * ∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal

end Defs

section Lemmas

variable {D : D7} {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hB : WuBessel C)

theorem cOf_pos {u : D.what₂.Word} {τ : D.what₂.Tau} (h0 : l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0)
    (ht : l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤) : 0 < cOf hB u τ := by
  have hl : 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := ENNReal.toReal_pos h0 ht.ne
  have hd : 0 < Module.finrank ℂ (X.Vloc u (vOf X τ)) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ (X.Vloc u (vOf X τ))) with h | h
    · exfalso
      have : Subsingleton (X.Vloc u (vOf X τ)) := Module.finrank_zero_iff.1 h
      apply h0
      unfold l2SG
      simp [Subsingleton.elim (phiOf hB u τ _) 0]
    · exact h
  unfold cOf
  exact div_pos hl (by exact_mod_cast hd)

theorem kap_eq {u u' : D.what₂.Word} {τ : D.what₂.Tau} (hc : 0 < cOf hB u τ) (hc' : 0 < cOf hB u' τ) :
    kap u u' C hB τ = 1 / (cOf hB u τ * cOf hB u' τ) := by
  unfold kap Formalism.L2.SG.Pf.LocNorm.aT sclOf
  have hb : cOf hB u' τ = (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal / ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) := rfl
  have hd0 : (0 : ℝ) ≤ ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hb] at hc' ⊢
  generalize cOf hB u τ = a at hc ⊢
  generalize (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal = L at hc' ⊢
  generalize ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) = d at hd0 hc' ⊢
  have hd : 0 < d := lt_of_le_of_ne hd0 (fun h => by rw [← h, div_zero] at hc'; exact lt_irrefl _ hc')
  have hL : 0 < L := by
    have h1 := mul_pos hc' hd
    rwa [div_mul_cancel₀ _ hd.ne'] at h1
  have hx : 0 ≤ a * d / L := div_nonneg (mul_nonneg hc.le hd.le) hL.le
  first
    | (rw [Complex.normSq_mul, Complex.normSq_ofReal, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp; ring)
    | (simp only [Complex.normSq_mul, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp; ring)
    | (rw [Complex.normSq_mul, Complex.normSq_ofReal, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp)

theorem finrank_tau (u : D.what₂.Word) :
    (Module.finrank ℂ (X.Vpi u) : ℝ) = ∏ τ, (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) := by
  rw [Formalism.L2.SG.Pf.finrank_Vpi, Nat.cast_prod]
  exact (Fintype.prod_equiv X.pl.symm _ _ fun τ => rfl).symm

end Lemmas

section Main

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

theorem poincareConstant_of_mass (hM : MassU Y u C hB) :
    c0X X u (Y.FN u) = X.volK2 * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * ∏ τ, cOf hB u τ := by
  unfold c0X
  unfold MassU at hM
  rw [mul_assoc X.volK2, hM, finrank_tau u]
  have hP : ∏ τ, cOf hB u τ = (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) / ∏ τ, ((Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℕ) : ℝ) := by
    rw [← Finset.prod_div_distrib]
    rfl
  rw [hP]
  ring

theorem ampWin_of (hM : MassU Y u C hB) (hM' : MassU Y u' C hB)
    (hl : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤)
    (hl' : ∀ τ, l2SG (C.nuS u' τ) (phiOf hB u' τ) ≠ 0 ∧ l2SG (C.nuS u' τ) (phiOf hB u' τ) < ⊤) :
    AmpWinP Y u u' C hB := by
  unfold AmpWinP
  have hc : ∀ τ, 0 < cOf hB u τ := fun τ => cOf_pos hB (hl τ).1 (hl τ).2
  have hc' : ∀ τ, 0 < cOf hB u' τ := fun τ => cOf_pos hB (hl' τ).1 (hl' τ).2
  have hk : ∀ τ, kap u u' C hB τ = 1 / (cOf hB u τ * cOf hB u' τ) := fun τ => kap_eq hB (hc τ) (hc' τ)
  have hP : (∏ τ, kap u u' C hB τ) * (∏ τ, cOf hB u τ) * (∏ τ, cOf hB u' τ) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    have h1 := (hc τ).ne'
    have h2 := (hc' τ).ne'
    rw [hk τ]
    field_simp
  rw [poincareConstant_of_mass _ _ _ _ hM, poincareConstant_of_mass _ _ _ _ hM']
  linear_combination (X.volK2 ^ 2 * (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u')) * hP

theorem poincareConstant_nonneg (w : D.what₂.Word) : 0 ≤ c0X X w (Y.FN w) := by
  unfold c0X
  first
    | positivity
    | (have := X.levelVolume_pos; positivity)
    | (have := X.volK2_nonneg; positivity)
    | (unfold HidaSetting.volK2; positivity)
    | (unfold Formalism.L2.SG.HidaSetting.HidaSetting.volK2; done)

theorem K0_eq_covN_of_ampWin (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2) :
    Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB =
      Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u' := by
  have ha := poincareConstant_nonneg Y u
  have hb := poincareConstant_nonneg Y u'
  unfold Formalism.L2.SG.Pf.LocNorm.K0 Formalism.L2.SG.Pf.OOCore3.sclV TermOp.scl
  unfold AmpWinP at hA
  have hkap : ∀ τ, kap u u' C hB τ = Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ) := fun τ => rfl
  simp only [hkap] at hA
  generalize (∏ τ, Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ)) = P at hA ⊢
  generalize c0X X u (Y.FN u) = a at ha hA ⊢
  generalize c0X X u' (Y.FN u') = b at hb hA ⊢
  generalize Formalism.L2.SG.LoopTerm.covN (Y := Y) C u = m at hA ⊢
  generalize Formalism.L2.SG.LoopTerm.covN (Y := Y) C u' = m' at hA ⊢
  generalize X.volK2 = V at hA hV ⊢
  clear hkap
  rw [Complex.normSq_ofReal]
  rcases (mul_nonneg ha hb).eq_or_lt with h0 | h0
  · rw [← h0, Real.sqrt_zero, inv_zero, zero_mul, mul_zero, div_zero]
    have h1 : V ^ 2 * (m * m') = 0 := by rw [← hA, mul_assoc, ← h0, mul_zero]
    exact ((mul_eq_zero.mp h1).resolve_left (pow_pos hV 2).ne').symm
  · have hs : (√(a * b)) ^ 2 = a * b := Real.sq_sqrt h0.le
    have hs0 : √(a * b) ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
    have hden : (√(a * b))⁻¹ * V * ((√(a * b))⁻¹ * V) = V ^ 2 / (a * b) := by
      first
        | rw [inv_mul_eq_div, div_mul_div_comm, ← sq, ← sq, hs]
        | (field_simp; rw [hs]; ring)
        | (field_simp; rw [Real.mul_self_sqrt h0.le]; ring)
    rw [hden, div_div_eq_mul_div, div_eq_iff (pow_pos hV 2).ne']
    linarith [hA]

theorem minWeight_pos (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2)
    (hc : 0 < Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u') :
    0 < Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB := by
  rw [K0_eq_covN_of_ampWin Y u u' C hB hA hV]
  exact hc

theorem K0_mem_covWin_of_ampWin (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2) {large₂} {C1 : ℝ}
    (hW : Formalism.L2.SG.LoopTerm.CovWinN (Y := Y) C large₂ C1 u u') :
    Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB) := by
  rw [K0_eq_covN_of_ampWin Y u u' C hB hA hV]
  first
    | exact hW
    | (unfold Formalism.L2.SG.LoopTerm.CovWinN at hW; exact hW)
    | (unfold Formalism.L2.SG.LoopTerm.CovWinN at hW; done)

end Main

end Formalism.L2.SG.Pf.AmpWin
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTTypesClosed
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

private theorem list_prod_apply_eq_foldr {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (l : List (Module.End ℂ W)) (v : W) :
    l.prod v = List.foldr (fun (T : W → W) (h : W) => T h) v
      (l.map (fun (T : Module.End ℂ W) => (T : W → W))) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.prod_cons, Module.End.mul_apply, ih]

private theorem qmF_eq_qdet_apply {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℕ}
    (E : Fin m → Fin m → Module.End ℂ W) (w : ℂ) (v : W) :
    Formalism.FourierDecayAlt.Q.qmF (fun a b => (E a b : W → W)) id id w v = (Formalism.REAL.qdet E w) v := by
  simp only [Formalism.FourierDecayAlt.Q.qmF, Formalism.REAL.qdet, Formalism.REAL.qminor]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Module.End.mul_apply, Module.End.intCast_apply, list_prod_apply_eq_foldr, List.map_ofFn]
  rw [← Int.cast_smul_eq_zsmul ℂ]
  congr 2
  congr 1
  funext j y
  simp only [Function.comp, Formalism.REAL.Tm, id]
  split_ifs <;> simp [Module.algebraMap_end_apply, sub_smul, Nat.cast_smul_eq_nsmul]

theorem capacity_from_hermitian_char : CapFromHC := by
  intro Wp _ _ k r z u π hz hT hrep hcont hHC
  obtain ⟨g, ⟨hgU, hgfix, hgz⟩, hU⟩ := hHC
  haveI : FiniteDimensional ℂ Wp := hU.2.1
  intro Bs hBs w v
  have hfr := Formalism.FourierDecayAlt.P.QrCap.fr_frame hgU hgfix _ hgz
  have hcore := Formalism.FourierDecayAlt.P.QrCap.core (u := u) hz hT ⟨hrep, hcont⟩ hgU hgfix _ hgz hU.2.2.2 w v
  have hE : (fun a b => Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r) Bs a b))
      = fun a b => ((Formalism.FourierDecayAlt.Qr.EB π Bs a b : Module.End ℂ Wp) : Wp → Wp) := by
    funext a b y
    exact Formalism.FourierDecayAlt.P.QrD.ecRep_eq hrep hcont (Formalism.FourierDecayAlt.P.QrD.frame_lie hBs a b).1
      (Formalism.FourierDecayAlt.P.QrD.frame_lie hBs a b).2 y
  have hcap : Formalism.FourierDecayAlt.Q.capRep k r π Bs w v = (Formalism.REAL.qdet (Formalism.FourierDecayAlt.Qr.EB π Bs) w) v := by
    simp only [Formalism.FourierDecayAlt.Q.capRep]
    rw [hE, qmF_eq_qdet_apply]
  rw [hcap, Formalism.FourierDecayAlt.P.QrCap.capChange hz hT ⟨hrep, hcont⟩ hBs hfr w, hcore]
  congr 1
  simp only [Formalism.FourierDecayAlt.Qr.cpol, Formalism.FourierDecayAlt.P.QrCap.lowK_allPos]
  have hI : Finset.Icc 1 k = (Finset.range k).map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [hI, Finset.prod_map, Finset.prod_range]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp [Nat.succ_sub_one, j.isLt]
  push_cast
  ring

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLocG
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx

theorem ne_val {r : ℕ} {i j : Fin r} (h : i.1 ≠ j.1) : i ≠ j := fun e => h (congrArg Fin.val e)

theorem rv_inj {n : ℕ} {a b : Fin n} : rv a = rv b ↔ a = b :=
  ⟨fun h => by rw [← rv_rv a, h, rv_rv], fun h => h ▸ rfl⟩

theorem gram_of {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {u v : VA I} {P Q : Prop} [Decidable P] [Decidable Q]
    (h : hhat I u v - (if P then 1 else 0) ∈ Wq I w) (hPQ : P ↔ Q) :
    hhat I u v - (if Q then 1 else 0) ∈ Wq I w := by
  have e : (if P then (1 : I.E ⊗[I.F] Af I.F) else 0) = if Q then 1 else 0 := by
    by_cases hp : P
    · rw [if_pos hp, if_pos (hPQ.1 hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hPQ.2 hq))]
  rwa [e] at h

theorem gram_ne {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {u v : VA I} {Q : Prop} [Decidable Q]
    (h : hhat I u v ∈ Wq I w) (hQ : ¬ Q) : hhat I u v - (if Q then 1 else 0) ∈ Wq I w := by
  rwa [if_neg hQ, sub_zero]

variable {D : D7} (X : HidaSetting D)

theorem sg_hA (u v : VA X.B.I) : sg X.B.I (hA X.B.I u v) = hhat X.B.I v u := hhat_conj X.B.I u v

theorem fr_wt (i : Fin D.R.k) : fr X true (wI (hrD D) i) = X.bw i := by rw [fr_w]; rfl
theorem fr_wf (i : Fin D.R.k) : fr X false (wI (hrD D) i) = X.bwd (rv i) := by rw [fr_w]; rfl
theorem frd_wt (i : Fin D.R.k) : frd X true (wI (hrD D) i) = X.bwd i := by rw [frd_w]; rfl
theorem frd_wf (i : Fin D.R.k) : frd X false (wI (hrD D) i) = X.bw (rv i) := by rw [frd_w]; rfl

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)}

theorem wq (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g c) : c ∈ Wq X.B.I w := zmod_Wq hg h

theorem wqs (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g c) : sg X.B.I c ∈ Wq X.B.I w := zmod_Wq hg (zmod_sg h)

theorem xI_inj {a b : Fin D.R.rS} : xI (hrD D) a = xI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa [xI, wI, yI] using this), fun h => h ▸ rfl⟩
theorem wI_inj {a b : Fin D.R.k} : wI (hrD D) a = wI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa [xI, wI, yI] using this), fun h => h ▸ rfl⟩
theorem yI_inj {a b : Fin D.R.rS} : yI (hrD D) a = yI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa [xI, wI, yI] using this), fun h => h ▸ rfl⟩

theorem gram (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w) :
    GramW w (fr X ob) (frd X ob) := by
  intro i j
  have sg_ite : ∀ (P : Prop) [Decidable P],
      sg X.B.I (if P then (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) else 0) = if P then 1 else 0 := by
    intro P _; split_ifs <;> simp
  rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ <;>
  rcases kind_cases (hrD D) j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩
  ·
    rw [dual_frame_isotropic, frame_isotropic]
    have h := wqs X hg ((X.gramIntegral b a).2.2)
    rw [map_sub, sg_hA, sg_ite] at h
    exact gram_of h (by rw [xI_inj]; exact eq_comm)
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [dual_frame_isotropic, fr_wf]; exact wq X hg ((X.weightVectorsIntegral (rv b)).2.2 a).2.2.2
    · rw [dual_frame_isotropic, fr_wt]; exact wq X hg ((X.weightVectorsIntegral b).2.2 a).2.1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_isotropic, frame_anisotropic]; exact wq X hg (X.formsAtZero.2 a).2
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_isotropic, fr_y]; exact wq X hg (X.gramIntegral a (rv b)).2.1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_wf, frame_isotropic]; have := wqs X hg ((X.weightVectorsIntegral (rv a)).2.2 b).1; rwa [sg_hA] at this
    · rw [frd_wt, frame_isotropic]; have := wqs X hg ((X.weightVectorsIntegral a).2.2 b).2.2.1; rwa [sg_hA] at this
  ·
    cases ob
    · rw [frd_wf, fr_wf]
      simp only [Bool.false_eq_true, if_false] at hsew
      have h := wqs X hg (X.bw_dual (rv b) (rv a))
      rw [map_sub, sg_hA] at h
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl] at h ⊢
        have := add_mem h hsew
        convert this using 1; ring
      · rw [if_neg (fun h' => hab (rv_inj.1 h'.symm)), map_zero, sub_zero] at h
        exact gram_ne h (fun h' => hab (wI_inj.1 h'))
    · rw [frd_wt, fr_wt]
      simp only [if_true] at hew
      have h := wq X hg (X.bw_dual a b)
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl] at h ⊢
        change hhat X.B.I (X.bwd a) (X.bw a) - X.ew ∈ _ at h
        have := add_mem h hew
        convert this using 1; ring
      · rw [if_neg hab, sub_zero] at h
        exact gram_ne h (fun h' => hab (wI_inj.1 h'))
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_wf, frame_anisotropic]; have := wqs X hg (X.weightVectorsIntegral (rv a)).1; rwa [sg_hA] at this
    · rw [frd_wt, frame_anisotropic]; have := wqs X hg (X.weightVectorsIntegral a).2.1; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_wf, fr_y]; have := wqs X hg ((X.weightVectorsIntegral (rv a)).2.2 (rv b)).2.1; rwa [sg_hA] at this
    · rw [frd_wt, fr_y]; have := wqs X hg ((X.weightVectorsIntegral a).2.2 (rv b)).2.2.2; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_anisotropic, frame_isotropic, hhat_neg_left]
    refine neg_mem ?_
    have := wqs X hg (X.formsAtZero.2 b).1; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [dual_frame_anisotropic, fr_wf, hhat_neg_left]; exact neg_mem (wq X hg (X.weightVectorsIntegral (rv b)).2.1)
    · rw [dual_frame_anisotropic, fr_wt, hhat_neg_left]; exact neg_mem (wq X hg (X.weightVectorsIntegral b).1)
  ·
    rw [dual_frame_anisotropic, frame_anisotropic, hhat_neg_left, if_pos rfl]
    have := neg_mem (wq X hg X.formsAtZero.1)
    convert this using 1
    show -hhat X.B.I X.z0 X.z0 - 1 = -(hA X.B.I X.z0 X.z0 + 1)
    rw [show hA X.B.I X.z0 X.z0 = hhat X.B.I X.z0 X.z0 from rfl]; ring
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_anisotropic, fr_y, hhat_neg_left]
    refine neg_mem ?_
    have := wqs X hg (X.formsAtZero.2 (rv b)).2; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [frd_y, frame_isotropic]; exact wq X hg (X.gramIntegral (rv a) b).1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_y, fr_wf]; exact wq X hg ((X.weightVectorsIntegral (rv b)).2.2 (rv a)).2.2.1
    · rw [frd_y, fr_wt]; exact wq X hg ((X.weightVectorsIntegral b).2.2 (rv a)).1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [frd_y, frame_anisotropic]; exact wq X hg (X.formsAtZero.2 (rv a)).1
  ·
    rw [frd_y, fr_y]
    exact gram_of (wq X hg (X.gramIntegral (rv a) (rv b)).2.2) (by rw [rv_inj, yI_inj])

end Formalism.L2.SG.Pf.KppLoc
end
end

