module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0041

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdPairOfTermBeta
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def BwdTerm' : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ',
        (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) →
        IsTerm Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ AdmWit Λ₂ (gS D) (lf D F0) (liftF F'₂) 1 ∧
          IsGeneric Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ FrameOK D Λ₂ (liftF F'₂)

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.NGAnalytic.MassDataLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Inst

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev anY : AnIn :=
  anOf (Y.tO u u') (Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1) (Formalism.L2.SG.RealObj.degX X)
    ((locOf X u u' ψ).volZZ / (((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) * (locOf X u u' ψ).volPP) *
      ((locOf X u u' ψ).volPP * (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)))
    (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D) (Formalism.L2.SG.RealObj.IntOO X u u' 1) sd C Th D.R.rS
    (Fintype.card (InfinitePlace X.B.I.F))
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq),
      KtopVOf X u u' Y.M Y.δ (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq)⟩

def FrameVolAt : Prop :=
  (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).unitLevelVolume / (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).volZZ =
    (2 * D.host.v) ^ (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) *
      (X.B.g : ℝ) ^ (D.R.f * (D.R.rS + 1) * (2 * D.R.rS + 3))

theorem kapN_pos (hg : 0 < (X.B.g : ℝ)) : 0 < Formalism.L2.SG.MassDataConc.kapN D := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  have hgS : 0 < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
    unfold Formalism.MainNotions.S.Lat.gS
    first
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos D.host.g_prime.1.pos D.host.g_prime.2.pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).one_lt.le (D.host.g_prime 1).one_lt.le)
  positivity

theorem massDataValid_bk_of {large₂ : SizeData₂ D} {Cg cb Cw cT CT C0 C' Cl : ℝ} (hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u')
    (hrd : 0 < 2 * D.host.v) (hg : 0 < (X.B.g : ℝ)) (hT : MassDataTie X hb X0 ψ)
    (hLS : InLevelSAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hMs : InMassesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hCol : InColumnsAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hInd : InIndicesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hVol : InVolumesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hKpp : KppVolAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hTy : InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq)
    (hPC : ProdConv X u u' ψ) (hPr : PrimX X u) (hPr' : PrimX X u') (hKap : KapX X u u')
    (hNu : Formalism.L2.SG.RealObj.InNuX X u u' 1) (hInf : Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Pos)
    (hFV : FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) :
    ∃ Irat Ire : ℝ, MassDataAdmissible X Y u u' (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire := by
  obtain ⟨hM, hψ, hStd, hMC, hLC, -, hdet⟩ := hT
  have hH : HypX X hb (Y.FN u) (Y.FN u') u u' := ⟨hM, hc.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  have hk := kapN_pos X hg
  have hDst : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Dstar = DstC X :=
    Formalism.L2.SG.IntegralApproximation.MassDataDstarX_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq
      (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hH hKpp
  set B := bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq with hB
  have hCoo : 0 ≤ Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
    unfold Formalism.L2.SG.RealObj.DisintegrationConstant
    split_ifs with h
    · exact h.choose_spec.1.le
    · exact le_rfl
  have hdeg : 0 < B.deg := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hPos
    exact h
  have hNI : PN.NormInputs B := by
    refine ⟨hPos, rfl, ?_, ?_, ?_, hLS hH, hMs hH, hCol hH, ?_, ?_, hInd hH⟩
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 =
        Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 *
          (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)
      unfold Formalism.L2.SG.RealObj.IntOO Formalism.L2.SG.RealObj.IntC
      rw [hNu, ENNReal.toReal_mul, ENNReal.toReal_ofReal hCoo]
      field_simp
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 ≤ 1 / Formalism.L2.SG.RealObj.degX X
      have hd : 0 < Formalism.L2.SG.RealObj.degX X := hdeg
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hInf.2.2
    · exact inVolumes_of_compat X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ)
        (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hVol hH ⟨ψ, hψ, hStd, hMC⟩ hdet
    · exact inOrdinary_bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq hPC
    · exact hTy hH hPC (locTieX_of X ψ u (hLC u) hPr) (locTieX_of X ψ u' (hLC u') hPr')
        (typFacts_of X u u' (Formalism.L2.SG.Pf.gSplitX_holds X) (tCongX X u u') hKap)
  have hLam : 0 < PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
      (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) := by
    unfold PN.abelian₂
    exact mul_pos (pow_pos hrd _) (Real.rpow_pos_of_pos hrd _)
  refine ⟨(B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)),
    (B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)) /
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
        (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3)), ?_, ?_, hNI, ?_⟩
  · exact Formalism.L2.SG.IntegralApproximation.Gam1TieC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq Y
  · show B.d * B.d' / B.Dstar = duC X Y u * duC X Y u' / DstC X
    rw [hDst]
    rfl
  · have hL1 : PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f ≠ 0 := by
      unfold PN.abelian₂; exact (pow_pos hrd _).ne'
    have hL2 : (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) ≠ 0 :=
      (Real.rpow_pos_of_pos hrd _).ne'
    refine ⟨hrd, hg, hFV, ?_, ?_⟩
    · field_simp
    · field_simp

end Inst

section Closed

def pairSys0 {D : D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂ :=
  ⟨Empty, Empty.elim, Empty.elim, fun p => p.elim, fun p => p.elim, fun _ => False⟩

def idx0 (D : D7) : Fin D.R.k := ⟨0, by have := D.R.m_add_three_le_k; omega⟩

abbrev bk0 {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    S3.MassData (TypX X) :=
  bk X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

abbrev canonicalAnalyticData {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : AnIn :=
  anY X Y u u' ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

def OnTied (P : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I → Full X → D.what₂.Word → D.what₂.Word →
    (Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) → AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ → Prop) : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → P D X hb Y u u' X0 ψ

end Closed

end Formalism.L2.SG.NGAnalytic.MassDataLemmas
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPf
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace CohCut

def t2 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Λ : Submodule (Zd.M p).L.O (Vp D p)) : Loc.Term (Vp D p) (Zd.M p) D.R.rS :=
  ⟨Λ, (tLoc Zd p γ).f, locF' Zd p F'₂, (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def vP (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → Vp D p :=
  (locH Zd p).MMfam (t2 Zd p γ F'₂ ⊥)

end CohCut

open CohCut

def CohHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  Ctx γ Z ∧ ZhatL (lf D F0) F'₂ = Z ∧ starCompat γ F'₂ ∧
    ∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _) (φ' p)

variable (u u' F0 what₂)

def CohGen : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ (locH Zd p).IsGeneric (t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))}.Finite

def CohGood : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂)}.Finite

variable {u u' F0 what₂}

theorem locSet_eq_single {p : PlF D} {γ : TermDef.Term D u u' F0 what₂}
    {F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    {φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)}
    (hmem : lattice₂ D Zd.M p γ.lam ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ')
    (hN : Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂)) :
    locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ' = {lattice₂ D Zd.M p γ.lam} := by
  ext Λ₂
  rw [Set.mem_singleton_iff]
  constructor
  · intro h2
    have hL : (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f = (locH Zd p).Lset Λ₂ (tLoc Zd p γ).f := by
      have h := h2.2.1
      exact (Set.image_id _).symm.trans h
    have hX := Formalism.MainNotions.S.Loc.HermSp.CohU.X_le_MMfam (H := locH Zd p) (t2 Zd p γ F'₂ ⊥)
    exact (Formalism.MainNotions.S.Loc.HermSp.CohU.lat_eq_of_Lset hN hX hmem.1.1.1 h2.1.1.1 hmem.1.2.1 h2.1.2.1 hL).symm
  · intro h
    rw [h]
    exact hmem

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobMoveOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def StabApprox (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z₁ A₀ B₀ : PairVal.MatR D), AtMat w Z₁ → IsLo A₀ → IsUp B₀ →
    (∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) →
    ∃ X Y : PairVal.MatR D, IsLo X ∧ IsUp Y ∧
      X * (Z₁ * Sg D.host.E D.R.rS) * Y = Z₁ * Sg D.host.E D.R.rS ∧
      ∀ p, TieN.IntLow (Zd.M p) (locL Zd p (A₀ * X) (Y * B₀)) ∧ TieN.IntUp (Zd.M p) (locR Zd p (A₀ * X) (Y * B₀))

def Dict : Prop :=
  ∀ A B : PairVal.MatR D, IsLo A → IsUp B →
    (∀ p, TieN.IntLow (Zd.M p) (locL Zd p A B) ∧ TieN.IntUp (Zd.M p) (locR Zd p A B)) →
    IntFr A.conjTranspose ∧ IntFr (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS) ∧
      TieG A.conjTranspose (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS)

variable {Zd}

theorem isUpUni_of {K : Type*} [CommRing K] {n : ℕ} {U : Matrix (Fin n) (Fin n) K} (h : IsUp U) : IsUpUni U :=
  fun i j => ⟨fun hji => h.2 j i hji, by rintro rfl; exact h.1 i⟩

theorem isUp_conjT {n : ℕ} {A : Matrix (Fin n) (Fin n) D.host.E} (h : IsLo A) : IsUp A.conjTranspose :=
  ⟨fun a => by simp [Matrix.conjTranspose_apply, h.1 a],
    fun a b hab => by simp [Matrix.conjTranspose_apply, h.2 a b hab]⟩

theorem globMove_of (u u' : D.what₂.Word) (hS : StabApprox Zd u u') (hD : Dict Zd) : GlobMove D Zd.M Zd.δ u u' := by
  intro w Z₁ Z₂ _ hZ₁ hZ₂ htup
  have hZ₁' := hZ₁
  obtain ⟨L1, U1, hL1, hU1, e1⟩ := hZ₁
  obtain ⟨L2, U2, hL2, hU2, e2⟩ := hZ₂
  rw [Formalism.L2.SG.Pf.AtPt.zhatOM_eq] at e1 e2
  have lo : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsLoUni L → Formalism.DoubleCosetMeasures.IsLowUni L :=
    fun L h => ⟨fun i j hij => (h i j).1 hij, fun a => (h a a).2 rfl⟩
  have up : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni U → Formalism.DoubleCosetMeasures.IsUpUni U :=
    fun U h => ⟨fun i j hji => (h i j).1 hji, fun a => (h a a).2 rfl⟩
  have lo' : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L → IsLo L :=
    fun L h => ⟨h.2, fun a b hab => h.1 hab⟩
  have up' : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U → IsUp U :=
    fun U h => ⟨h.2, fun a b hab => h.1 hab⟩
  have detL : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L →
      IsUnit L.det := fun L h => by
    rw [Matrix.det_of_lowerTriangular L h.1]
    simp [h.2]
  have detU : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U →
      IsUnit U.det := fun U h => by
    rw [Matrix.det_of_upperTriangular h.1]
    simp [h.2]
  have hA₀lo : IsLo (L2 * L1⁻¹) :=
    isLo_mul (lo' _ (lo _ hL2)) (lo' _ (Formalism.DoubleCosetMeasures.isLowUni_inv (hx := lo _ hL1)))
  have hB₀up : IsUp (U1⁻¹ * U2) :=
    isUp_mul (up' _ (Formalism.DoubleCosetMeasures.isUpUni_inv (hx := up _ hU1))) (up' _ (up _ hU2))
  have hmove : Z₂ * Sg D.host.E D.R.rS = (L2 * L1⁻¹) * (Z₁ * Sg D.host.E D.R.rS) * (U1⁻¹ * U2) := by
    rw [e2, e1]
    have i1 : L1⁻¹ * L1 = 1 := Matrix.nonsing_inv_mul L1 (detL _ (lo _ hL1))
    have i2 : U1 * U1⁻¹ = 1 := Matrix.mul_nonsing_inv U1 (detU _ (up _ hU1))
    calc L2 * ptMat w * U2 = L2 * (L1⁻¹ * L1) * ptMat w * ((U1 * U1⁻¹) * U2) := by
          rw [i1, i2, Matrix.mul_one, Matrix.one_mul]
      _ = L2 * L1⁻¹ * (L1 * ptMat w * U1) * (U1⁻¹ * U2) := by simp only [Matrix.mul_assoc]
  have hstab : ∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) *
          locR Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ := by
    intro p
    have hmem := mem_kkOrb_self (M := Zd.M) p (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p)
    have ht := htup p
    unfold tupZ at ht
    rw [← ht] at hmem
    obtain ⟨l, ρ, hl, hρ, heq⟩ := hmem
    refine ⟨l, ρ, hl, hρ, ?_⟩
    rw [← locMove (Zd := Zd) u u' p hA₀lo hB₀up hmove]
    exact heq
  obtain ⟨X, Y, hX, hY, hXY, hint⟩ := hS w Z₁ (L2 * L1⁻¹) (U1⁻¹ * U2) hZ₁' hA₀lo hB₀up hstab
  obtain ⟨hIA, hIB, hT⟩ := hD (L2 * L1⁻¹ * X) (Y * (U1⁻¹ * U2)) (isLo_mul hA₀lo hX) (isUp_mul hY hB₀up) hint
  have hSg : Sg D.host.E D.R.rS =
      Matrix.diagonal (fun b : Fin (D.R.rS + 1) => (-1 : D.host.E) ^ (D.R.rS - b.val)) := by
    have h1 := (Formalism.L2.SG.Pf.AtPt.zhatOM_eq (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).symm.trans
      (Formalism.L2.SG.Pf.zhatOM_eq_pv 1)
    simpa using h1
  have hsq : ∀ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - b.val) * (-1 : D.host.E) ^ (D.R.rS - b.val) = 1 := by
    intro b
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hSS : Sg D.host.E D.R.rS * Sg D.host.E D.R.rS = 1 := by
    rw [hSg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact hsq b
  refine ⟨(L2 * L1⁻¹ * X).conjTranspose, Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS,
    isUpUni_of (isUp_conjT (isLo_mul hA₀lo hX)), isUpUni_of ?_, hIA, hIB, hT, ?_⟩
  · rw [hSg]
    exact isUp_conj (isUp_mul hY hB₀up) _ _ hsq
  · rw [Matrix.conjTranspose_conjTranspose]
    have h3 : Z₂ * Sg D.host.E D.R.rS =
        L2 * L1⁻¹ * X * (Z₁ * Sg D.host.E D.R.rS) * (Y * (U1⁻¹ * U2)) := by
      rw [hmove]
      conv_lhs => rw [← hXY]
      simp only [Matrix.mul_assoc]
    calc Z₂ = Z₂ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      _ = L2 * L1⁻¹ * X * Z₁ * (Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS) := by
          rw [h3]
          simp only [Matrix.mul_assoc]

end Formalism.L2.SG.Pf.TupGlob
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalCountOfGlue
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Top2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem latSide_at' (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hR : ClaimR M r n) : LatSide M r n :=
  latSide_at M r n hM hE hV hP (gramMM_holds M r n) (thFG_at M r hM) (thSpan_at M r hM) hR

theorem localCount_of_glue (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hR : ClaimR M r n) (h0 : ModSide0 M r n M.split.isSome)
    (hU : ModSideU M r n M.split.isSome) : Formalism.MainNotions.ThinScalesBound.FamilyLocalModel M r n := by
  intro V _ _ H hn t₁ hg f₂ f₂' φ φ' hF hF' hI hs hs'
  have hT : LocalCountHypotheses H t₁ f₂ f₂' φ φ' := ⟨hg, hF, hF', hI, hs, hs'⟩
  have hL := latSide_at' M r n hM hE hV hP hR V H hn t₁ f₂ f₂' φ φ' hT
  dsimp only
  refine ⟨fun hz Z₁ Z₂ h₁ h₂ => ?_, fun hu Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb => ?_⟩
  · rw [hL]
    exact h0 rfl V H hn t₁ f₂ f₂' φ φ' hT hz Z₁ Z₂ h₁ h₂
  · rw [hL]
    exact hU rfl V H hn t₁ f₂ f₂' φ φ' hT hu Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb

end Top2

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfIntegral
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

theorem shUnit_holds (D : Formalism.BasicNotions.D7) : ShUnit D := by
  intro p c
  haveI : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  haveI : Module.Free (D.s.atP p).Fp (D.s.atP p).Ep := (D.s.atP p).free
  haveI : FiniteDimensional (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  by_contra hcon
  simp only [not_exists] at hcon
  let f : Module.End (D.s.atP p).Fp (D.s.atP p).Ep := LinearMap.mulLeft (D.s.atP p).Fp c
  have hev : ∀ n : Fin 3, ∃ y : (D.s.atP p).Ep, f.HasEigenvector (-(((n : ℕ) : (D.s.atP p).Fp))) y := by
    intro n
    have hnu := hcon n
    have hni : ¬ Function.Injective
        (LinearMap.mulLeft (D.s.atP p).Fp (c + (((n : ℕ)) : (D.s.atP p).Ep))) := by
      intro hinj
      obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
      exact hnu (isUnit_iff_exists_inv.2 ⟨y, hy⟩)
    rw [← LinearMap.ker_eq_bot, ← ne_eq, Submodule.ne_bot_iff] at hni
    obtain ⟨y, hyk, hy0⟩ := hni
    refine ⟨y, ?_, hy0⟩
    rw [Module.End.mem_eigenspace_iff]
    have h1 : (c + (((n : ℕ)) : (D.s.atP p).Ep)) * y = 0 := hyk
    rw [add_mul] at h1
    show c * y = _
    rw [eq_neg_of_add_eq_zero_left h1, neg_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  choose y hy using hev
  have hinj : Function.Injective (fun n : Fin 3 => -(((n : ℕ) : (D.s.atP p).Fp))) := fun a b h => by
    have h' : ((a : ℕ) : (D.s.atP p).Fp) = ((b : ℕ) : (D.s.atP p).Fp) := neg_inj.1 h
    exact Fin.ext (Nat.cast_injective h')
  have hli := Module.End.eigenvectors_linearIndependent' f _ hinj y hy
  have hc := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, (D.s.atP p).rank] at hc
  omega

theorem partnerCount_of_integral {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd)
    (hB : BridgeBA) : PartnerIsomorphismCount Zd :=
  partnerCount_of_shUnit Zd hT2 hI (shUnit_holds D) hB

end Formalism.L2.SG.Pf.PCount
end
end

