module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.DegIUp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormLeadMinorOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0028

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypFD

variable {D : D7}

def DsigHC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1 ≤ Cl * large₂.sc.L →
    ∀ τ : D.what₂.Tau, D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ))

theorem dsig_eq [hF : Fact DsigHC] {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hF.out D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem vv_eq_vand {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by
  have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
  have hSF : (0 : ℝ) < ∏ i ∈ range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [dsig_eq hT hH hCL τ, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq]
  field_simp


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem fdl_of_ties {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    Sz.FormalDegreeLower (Formalism.MainNotions.BridgeLemma.cfgOf D τ) (1 / 2) (VV D τ) := by
  unfold Sz.FormalDegreeLower
  rw [Formalism.MainNotions.BridgeLemma.Vand_lam D τ, vv_eq_vand hT hH hCL τ]
  have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
  linarith

end Formalism.L2.SG.Pf.SzHypFD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TheoremBFixedOfExpansionLemmaJ
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.JointAmplitudePoints Formalism.L2.SG.Pf.ThmBChain Formalism.L2.SG.RealObj
open scoped ENNReal

namespace Formalism.L2.SG.Pf.OOCore3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section K

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
  {θ : ℝ} (C : Choice X θ) (hB : WuBessel C) (large₂ : SizeData₂ D) (C1 : ℝ)

def sclV : ℝ :=
  Complex.normSq ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ)

def WinK (K : ℝ) : Prop := normWin D large₂ C1 (K ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)))

def OOCorePK : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧
      sclV Y u u' * Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν w) * K = localAmplitudeProduct u u' hB w

def JFactPK : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧ J2of Y u u' ν (toPts w) * K = localAmplitudeProduct u u' hB w

theorem jFactPK_of_core (h : OOCorePK Y u u' ν C hB large₂ C1) : JFactPK Y u u' ν C hB large₂ C1 := by
  intro w hb hJ
  obtain ⟨w', hw', g, hg⟩ := isPtRep_of_J2of hJ
  have hw'w : w' = w := toPts_injective hw'
  subst hw'w
  rw [Formalism.L2.SG.Pf.OOCore.joint_amplitude_eq_normSq Y u u' ν w' ⟨g, hg⟩]
  exact h w' hb ⟨g, hg⟩

theorem localAmplitudesPositive_of_kernel (h : JFactPK Y u u' ν C hB large₂ C1) : LocalAmplitudesPositive Y u u' ν C hB := by
  intro w hb hJ
  obtain ⟨K, hK, -, e⟩ := h w hb hJ
  rw [← e]
  exact mul_pos hJ hK

theorem thetaWinP_of_K (h : JFactPK Y u u' ν C hB large₂ C1) : ThetaWinP Y u u' ν C hB large₂ C1 := by
  intro w hb hJ
  obtain ⟨K, hK, hW, e⟩ := h w hb hJ
  have hP : 0 < localAmplitudeProduct u u' hB w := by rw [← e]; exact mul_pos hJ hK
  have e2 : thetaP u u' hB (J2of Y u u' ν (toPts w)) w = K ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    unfold thetaP
    rw [if_pos ⟨hJ, hP⟩, ← e, mul_div_cancel_left₀ _ hJ.ne']
  rw [e2]
  exact hW

def LocNormPK (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧
      sclV Y u u' * (∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))) * K = localAmplitudeProduct u u' hB w

theorem ooCorePK_of (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl) (hN : LocNormPK Y u u' C hB large₂ C1 νl) :
    OOCorePK Y u u' ν C hB large₂ C1 := by
  intro w hb hw
  rw [Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.hsNormSq_OOP_quot u u' ν νl hQ w hw (Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.gxPos_holds u u' w hb hw)]
  exact hN w hb hw

end K

end Formalism.L2.SG.Pf.OOCore3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdOrder
section
noncomputable section

open scoped Classical
open Finset Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt

namespace Formalism.L2.SG.Pf.ThresholdOrder

theorem isGreatest_pow_inv {s : Set ℝ} (hs : s.Finite) (hne : s.Nonempty) (hpos : ∀ x ∈ s, 0 < x) {f : ℕ} (hf : 0 < f) :
    ∃ Th : ℝ, 0 < Th ∧ IsGreatest s ((Th ^ f)⁻¹) := by
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image s id hs hne
  have hm0 : 0 < m⁻¹ := inv_pos.mpr (hpos m hm)
  refine ⟨m⁻¹ ^ ((f : ℝ)⁻¹), Real.rpow_pos_of_pos hm0 _, ?_⟩
  rw [Real.rpow_inv_natCast_pow hm0.le hf.ne', inv_inv]
  exact ⟨hm, fun b hb => hmax b hb⟩

variable {ι : Type} [Fintype ι] (G : Sz.Glob ι)

theorem thrSet_finite (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) : (G.thrSet C de de' T T' l).Finite := by
  have key : G.thrSet C de de' T T' l ⊆ ⋃ i ∈ Finset.range (G.r + 2), ⋃ s ∈ Finset.range (G.r + 3),
      ({∏ w, Sz.xHat 1 C G.ka G.N G.lenI G.g (G.cutSupLong de de' T T' l w),
        ∏ w, Sz.xHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w),
        ∏ w, Sz.lamHat i s C G.ka G.N G.lenI G.g (G.supI de de' T T' l w),
        ∏ w, Sz.lamPrimeHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')} : Set ℝ) := by
    rintro x ⟨i, hi1, hir, h⟩
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨s, _, hsi, rfl⟩ | rfl
    · exact ⟨i, by omega, 0, by omega, Or.inl rfl⟩
    · exact ⟨i, by omega, 0, by omega, Or.inr (Or.inl rfl)⟩
    · exact ⟨i, by omega, s, by omega, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨i, by omega, 0, by omega, Or.inr (Or.inr (Or.inr rfl))⟩
  refine Set.Finite.subset ?_ key
  refine Set.Finite.biUnion (Finset.range _).finite_toSet fun i _ => ?_
  refine Set.Finite.biUnion (Finset.range _).finite_toSet fun s _ => ?_
  exact Set.toFinite _

theorem thrSet_nonempty (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) : (G.thrSet C de de' T T' l).Nonempty :=
  ⟨_, 1, le_rfl, by omega, Or.inl ⟨rfl, rfl⟩⟩

theorem thrAt_of_pos (CA : ℝ) (D : D7) (u u' : D.what₂.Word)
    (hpos : ∀ x ∈ (Formalism.L2.SG.SpectralTiesReal.gOf D (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm).thrSet CA
      (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u') (D.mem u).A.T (D.mem u').A.T
      (Formalism.L2.SG.SpectralTiesReal.lOf D (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')), 0 < x) :
    Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces CA D u u' := by
  unfold Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces
  refine isGreatest_pow_inv (thrSet_finite _ _ _ _ _ _ _) (thrSet_nonempty _ _ _ _ _ _ _) hpos ?_
  unfold Formalism.FourierDecayAlt.Sz.Glob.f
  exact Fintype.card_pos

end Formalism.L2.SG.Pf.ThresholdOrder
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WeightDeterminantBlockEq
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem rd_eq' : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE := by
  simp [Formalism.FourierDecayAlt.S6.rd, Formalism.BasicNotions.Host.rdE, one_div]

theorem blk_norm (τ : D.what₂.Tau) (σ : D.host.E →+* ℂ) (hσ : ∀ t, σ t = Formalism.MainNotions.S.plEmb D τ t) (b s m : ℕ)
    (t : D.host.E) :
    ‖((Formalism.MainNotions.S.rhoReal D b s : ℝ) : ℂ) * Formalism.MainNotions.S.plEmb D τ ((-1) ^ m * t)‖ =
      Formalism.FourierDecayAlt.S6.rd D.host.E ^ (-(Formalism.FourierDecayAlt.S6.nuBlock (D.R.rS : ℤ) (b : ℤ) (s : ℤ) : ℝ)) * ‖σ t‖ := by
  have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by unfold Formalism.MainNotions.S.rhoReal; positivity), map_mul,
    map_pow, map_neg, map_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hσ, rd_eq']
  unfold Formalism.MainNotions.S.rhoReal Formalism.FourierDecayAlt.S6.nuBlock
  rw [show (-(((2 * (D.R.rS : ℤ) + 3 - 2 * (b : ℤ) - (s : ℤ)) : ℤ) : ℝ)) =
      ((-(((2 * D.R.rS + 3 : ℕ) : ℤ) - 2 * (b : ℤ) - (s : ℤ)) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]

theorem weightDeterminant_block_eq (τ : D.what₂.Tau) (σ : D.host.E →+* ℂ) (hσ : ∀ t, σ t = Formalism.MainNotions.S.plEmb D τ t) (k : ℕ) (GG : ℝ) :
    ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (b : ℕ), 1 ≤ b →
    Formalism.FourierDecayAlt.C.nAux k D.R.rS GG
              (fun b s => Formalism.FourierDecayAlt.S6.rd D.host.E ^ (-(Formalism.FourierDecayAlt.S6.nuBlock (D.R.rS : ℤ) (b : ℤ) (s : ℤ) : ℝ))) b
              (Formalism.FourierDecayAlt.C.loc σ p) =
      WtDet.FA k D.R.rS GG b (Formalism.MainNotions.S.locBlocksFrom D (Formalism.MainNotions.S.rhoReal D) τ (b - 1)
        ((Formalism.L2.SG.DataInst.signAux D.R.rS b p).map Prod.swap))
  | [], _, _ => by simp [Formalism.FourierDecayAlt.C.loc, Formalism.FourierDecayAlt.C.nAux, Formalism.L2.SG.DataInst.signAux, Formalism.MainNotions.S.locBlocksFrom, WtDet.FA]
  | (s, t) :: rest, b, hb => by
    have ih := weightDeterminant_block_eq τ σ hσ k GG rest (b + s) (by omega)
    simp only [Formalism.FourierDecayAlt.C.loc, List.map_cons, Formalism.FourierDecayAlt.C.nAux, Formalism.L2.SG.DataInst.signAux, Prod.swap_prod_mk,
      Formalism.MainNotions.S.locBlocksFrom, WtDet.FA]
    rw [show b - 1 + 1 = b by omega, show b - 1 + s = b + s - 1 by omega]
    simp only [Formalism.FourierDecayAlt.C.loc] at ih
    rw [ih, blk_norm τ σ hσ b s _ t]

theorem nHead_eq (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : InfinitePlace X.B.I.F) (τ : D.what₂.Tau) (hpl : X.pl v = τ) :
    ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (b : ℕ), 1 ≤ b → b + (p.map Prod.fst).sum ≤ D.R.rS + 2 → (∀ x ∈ p, 1 ≤ x.1) →
    RealObj.nHead X v b ((Formalism.L2.SG.DataInst.signAux D.R.rS b p).map Prod.swap) =
      WtDet.FH D.R.rS b (Formalism.MainNotions.S.locBlocksFrom D (Formalism.MainNotions.S.rhoReal D) τ (b - 1)
        ((Formalism.L2.SG.DataInst.signAux D.R.rS b p).map Prod.swap))
  | [], _, _, _, _ => by simp [RealObj.nHead, Formalism.L2.SG.DataInst.signAux, Formalism.MainNotions.S.locBlocksFrom, WtDet.FH]
  | (s, t) :: rest, b, hb, hsz, hpos => by
    simp only [List.map_cons, List.sum_cons] at hsz
    have hs1 : 1 ≤ s := hpos (s, t) (by simp)
    have ih := nHead_eq X v τ hpl rest (b + s) (by omega) (by omega) (fun x hx => hpos x (by simp [hx]))
    simp only [List.map_cons, RealObj.nHead, Formalism.L2.SG.DataInst.signAux, Prod.swap_prod_mk,
      Formalism.MainNotions.S.locBlocksFrom, WtDet.FH]
    rw [show b - 1 + 1 = b by omega, show b - 1 + s = b + s - 1 by omega, ih]
    congr 2
    have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
    have hφ : X.B.I.φ v (X.ιE.symm ((-1) ^ (D.R.rS + 1 - (b + s - 1)) * t)) =
        Formalism.MainNotions.S.plEmb D τ ((-1) ^ (D.R.rS + 1 - (b + s - 1)) * t) := by
      rw [X.φ_eq, RingEquiv.apply_symm_apply, hpl]; rfl
    rw [hφ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by unfold Formalism.MainNotions.S.rhoReal; positivity)]
    congr 1
    unfold Formalism.MainNotions.S.rhoReal
    have hexp : ((2 * (D.R.rS + 1) - b - (b + s - 1) : ℕ) : ℤ) =
        ((2 * D.R.rS + 3 : ℕ) : ℤ) - 2 * (b : ℤ) - (s : ℤ) := by omega
    rw [← hexp, zpow_neg, zpow_natCast]

theorem signFlip_append {K : Type} [Ring K] (r : ℕ) : ∀ (L1 L2 : Formalism.FourierDecayAlt.TB.Pt K) (b : ℕ),
    Formalism.L2.SG.DataInst.signAux r b (L1 ++ L2) =
      Formalism.L2.SG.DataInst.signAux r b L1 ++ Formalism.L2.SG.DataInst.signAux r (b + (L1.map Prod.fst).sum) L2
  | [], L2, b => by simp [Formalism.L2.SG.DataInst.signAux]
  | (s, t) :: L1, L2, b => by
    simp only [List.cons_append, Formalism.L2.SG.DataInst.signAux, signFlip_append r L1 L2 (b + s), List.map_cons,
      List.sum_cons, add_assoc]

theorem locBlocksFrom_append (ρ : ℕ → ℕ → ℝ) (τ : D.what₂.Tau) : ∀ (L1 L2 : List (D.host.E × ℕ)) (a : ℕ),
    Formalism.MainNotions.S.locBlocksFrom D ρ τ a (L1 ++ L2) =
      Formalism.MainNotions.S.locBlocksFrom D ρ τ a L1 ++ Formalism.MainNotions.S.locBlocksFrom D ρ τ (a + (L1.map Prod.snd).sum) L2
  | [], L2, a => by simp [Formalism.MainNotions.S.locBlocksFrom]
  | (t, s) :: L1, L2, a => by
    simp only [List.cons_append, Formalism.MainNotions.S.locBlocksFrom, locBlocksFrom_append ρ τ L1 L2 (a + s), List.map_cons,
      List.sum_cons, add_assoc]

theorem nHead_nonneg (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : InfinitePlace X.B.I.F) :
    ∀ (b : ℕ) (L : List (D.host.E × ℕ)), 0 ≤ RealObj.nHead X v b L
  | _, [] => by simp [RealObj.nHead]
  | b, (t, s) :: rest => by
    simp only [RealObj.nHead]
    have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
    exact mul_nonneg (pow_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hrd.le _)) (norm_nonneg _)) _)
      (nHead_nonneg X v (b + s) rest)

theorem sqrt_prod' {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    Real.sqrt (∏ i, x i) = ∏ i, Real.sqrt (x i) := by
  rw [Real.sqrt_eq_iff_mul_self_eq (Finset.prod_nonneg fun i _ => hx i)
    (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (Real.mul_self_sqrt (hx i)).symm

variable (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)


open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT in
theorem wtTie_carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ) :
    WtTie X (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)) u u' := by
  intro p w hp hgood
  obtain ⟨hrep, hG⟩ := hgood
  have hk := Formalism.MainNotions.BridgeLemma.five_le_k D

  have hpt := hp
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList at hpt
  split_ifs at hpt with hPtL
  have hw1 : w.1 = (Formalism.L2.SG.DataInst.signAux D.R.rS 1 p).map Prod.swap := by
    rw [← Option.some_inj.mp hpt]; rfl
  have hfst : (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst = p.map Prod.fst :=
    Formalism.L2.SG.DataInst.sign_list_fst D.R.rS 1 p
  have hblk : ∀ b ∈ p, 1 ≤ b.1 := by
    intro b hb
    have : b.1 ∈ (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst := by
      rw [hfst]; exact List.mem_map_of_mem hb
    obtain ⟨b', hb', hbb⟩ := List.mem_map.mp this
    rw [← hbb]; exact (hPtL.2 b' hb').1
  have hsum : (p.map Prod.fst).sum = D.R.rS + 1 := by rw [← hfst, hPtL.1]
  have hne : p ≠ [] := by rintro rfl; simp at hsum

  have hplace : ∀ j : Fin (nfE D),
      Formalism.FourierDecayAlt.C.nLoc (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.k
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.r
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).fr
        ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).pd j).G
        (Formalism.FourierDecayAlt.C.loc ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j) p) =
      GX X u u' D.host.rdE (gamW X u u' w) (tauE X e j) ^ (D.R.k - 1) * RealObj.nHead X (tauE X e j) 1 w.1 := by
    intro j
    set τ := e (plE D j) with hτ
    have hpl : X.pl (tauE X e j) = τ := by
      show X.pl (X.pl.symm (e (plE D j))) = _
      exact Equiv.apply_symm_apply _ _
    have hσ : ∀ t, (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j t =
        Formalism.MainNotions.S.plEmb D τ t := by
      intro t
      show X.B.I.φ (tauE X e j) (X.ιE.symm t) = _
      rw [X.φ_eq, RingEquiv.apply_symm_apply, hpl]; rfl
    obtain ⟨p1, x, hpx⟩ : ∃ p1 x, p = p1 ++ [x] := ⟨p.dropLast, p.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    obtain ⟨s, t⟩ := x
    have hq : (Formalism.MainNotions.S.ThB.ptLoc D τ w).1 =
        Formalism.MainNotions.S.locBlocksFrom D (Formalism.MainNotions.S.rhoReal D) τ 0 ((Formalism.L2.SG.DataInst.signAux D.R.rS 1 p).map Prod.swap) := by
      rw [← hw1]; rfl
    set L1 := Formalism.MainNotions.S.locBlocksFrom D (Formalism.MainNotions.S.rhoReal D) τ 0
      ((Formalism.L2.SG.DataInst.signAux D.R.rS 1 p1).map Prod.swap)
    have hsz1 : (((Formalism.L2.SG.DataInst.signAux D.R.rS 1 p1).map Prod.swap).map Prod.snd).sum = (p1.map Prod.fst).sum := by
      rw [List.map_map]
      have := Formalism.L2.SG.DataInst.sign_list_fst D.R.rS 1 p1
      rw [← this]; rfl
    have hq2 : (Formalism.MainNotions.S.ThB.ptLoc D τ w).1 = L1 ++
        [(((Formalism.MainNotions.S.rhoReal D (1 + (p1.map Prod.fst).sum) s : ℝ) : ℂ) *
          Formalism.MainNotions.S.plEmb D τ ((-1) ^ (D.R.rS + 1 - (1 + (p1.map Prod.fst).sum + s - 1)) * t), s)] := by
      rw [hq, hpx, signFlip_append, List.map_append, locBlocksFrom_append, hsz1]
      simp [Formalism.L2.SG.DataInst.signAux, Formalism.MainNotions.S.locBlocksFrom, add_comm]
      rfl
    have hsum1 : (p1.map Prod.fst).sum + s = D.R.rS + 1 := by
      rw [hpx] at hsum; simpa using hsum

    have hGv : ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).pd j).G
        (Formalism.FourierDecayAlt.C.loc ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j) p) =
        Complex.normSq (Formalism.MainNotions.S.plEmb D τ t) - Tw (D := D) u * Tw (D := D) u' := by
      have hT := (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).hT j
      show Formalism.FourierDecayAlt.D.ptGG (Formalism.QuantumDeterminants.Tz _ _ _ * Formalism.QuantumDeterminants.Tz _ _ _) _ = _
      rw [hT.1, hT.2]
      unfold Formalism.FourierDecayAlt.D.ptGG Formalism.FourierDecayAlt.D.ptLast
      rw [hpx]
      simp [Formalism.FourierDecayAlt.C.loc, hσ]
      rfl
    have hGG : s = 1 → Complex.normSq (Formalism.MainNotions.S.plEmb D τ t) - Tw (D := D) u * Tw (D := D) u' =
        ‖((Formalism.MainNotions.S.rhoReal D (1 + (p1.map Prod.fst).sum) s : ℝ) : ℂ) *
          Formalism.MainNotions.S.plEmb D τ ((-1) ^ (D.R.rS + 1 - (1 + (p1.map Prod.fst).sum + s - 1)) * t)‖ ^ 2 -
          Tw (D := D) u * Tw (D := D) u' := by
      intro hs1
      rw [blk_norm τ (Formalism.MainNotions.S.plEmb D τ) (fun _ => rfl), Complex.normSq_eq_norm_sq]
      congr 2
      have : (Formalism.FourierDecayAlt.S6.nuBlock (D.R.rS : ℤ) ((1 + (p1.map Prod.fst).sum : ℕ) : ℤ) (s : ℤ)) = 0 := by
        unfold Formalism.FourierDecayAlt.S6.nuBlock; subst hs1; rw [Nat.cast_add, Nat.cast_one]; omega
      rw [this]; simp
    have hcore := WtDet.core_wt D.R.k D.R.rS (by omega) (Tw (D := D) u) (Tw (D := D) u') (Formalism.MainNotions.S.ThB.ptLoc D τ w)
      L1 _ s hq2 _ hGG
    have hA := weightDeterminant_block_eq τ ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j) hσ
      D.R.k (Complex.normSq (Formalism.MainNotions.S.plEmb D τ t) - Tw (D := D) u * Tw (D := D) u') p 1 le_rfl
    have hH := nHead_eq X (tauE X e j) τ hpl p 1 le_rfl (by omega) hblk
    have hgx := Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.gx_eq u u' w hrep τ
    unfold Formalism.FourierDecayAlt.C.nLoc
    rw [hGv]
    change Formalism.FourierDecayAlt.C.nAux D.R.k D.R.rS _
      (fun b s => Formalism.FourierDecayAlt.S6.rd D.host.E ^ (-(Formalism.FourierDecayAlt.S6.nuBlock (D.R.rS : ℤ) (b : ℤ) (s : ℤ) : ℝ))) 1 _ = _
    rw [hA, show (1 : ℕ) - 1 = 0 from rfl, ← hq, ← hcore, hw1, hH, ← hq]
    rw [show tauE X e j = vOf X τ from rfl, hgx]
  unfold nW
  rw [sqrt_prod' _ (fun v => mul_nonneg (pow_nonneg (hG v).le _) (nHead_nonneg X v 1 w.1))]
  symm
  exact Fintype.prod_equiv (tauE X e) _ _ (fun j => by rw [hplace j])

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

