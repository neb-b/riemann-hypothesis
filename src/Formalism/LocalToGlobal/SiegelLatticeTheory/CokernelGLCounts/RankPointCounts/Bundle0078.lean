module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0076
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCV
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfD
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0031
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0074
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0059
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AutLzNonempty
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem autLz_nonempty {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (autLz D F0 Λ).Nonempty := by
  have h1 : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := ⟨one_mem _, fun j => kmap_one _, rfl⟩
  exact ⟨ind F0 h1, (autLz_iff F0 Λ _).2 ⟨1, h1, gmap_one' Λ, rfl⟩⟩

theorem massRows_pos {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) :
    0 < Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
  have hne : (Y.what₂ u).Nonempty := ⟨_, (cls_spec (Y.rowsOK u) (latRowLat X u) 1).1⟩
  unfold Formalism.MainNotions.S.Cnt.massRows
  refine Finset.sum_pos (fun Λ hΛ => ?_) hne
  haveI := Formalism.L2.SG.Pf.FibreCounting.autLz_finite (Y := Y) (Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) hΛ
  have hpos : 0 < Nat.card ↥(autLz D (X.Fu u) Λ) := by
    obtain ⟨φ, hφ⟩ := autLz_nonempty (X.Fu u) Λ
    haveI : Nonempty ↥(autLz D (X.Fu u) Λ) := ⟨⟨φ, hφ⟩⟩
    exact Nat.card_pos
  unfold Formalism.MainNotions.S.wRow
  exact inv_pos.2 (Nat.cast_pos.2 hpos)

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_closed {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  RhoTieC_holds X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.latRowLat X u) (Formalism.L2.SG.Pf.latInj X u)
    (Formalism.L2.SG.Pf.latSurj X u)

end Formalism.L2.SG.MassDataConc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoordCovolOf
section
namespace Formalism.L2.SG.Pf.NcReal.JX

theorem coordCovol_of (hL : KapLaw) (hN : NOfib) (hB : BlockCovol) : Formalism.L2.SG.Pf.LsNc5.CoordCovol :=
  coordCovol_of_cut hL kapSurj_holds hN hB (fun X u => cVal_prod X u)

end Formalism.L2.SG.Pf.NcReal.JX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerRight
section
noncomputable section

open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Corner

variable {K : Type*} [CommRing K] (cj : K →+* K) {r : ℕ}

def cornerM (g : K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then g else 0

theorem corner_left (L : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hcj : cj 1 = 1) (g : K) : L * cornerM (r := r) g * cjT cj L = cornerM g := by
  ext i j
  simp only [Matrix.mul_apply, cornerM, Matrix.of_apply, cjT, Matrix.transpose_apply, Matrix.map_apply]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, if_pos rfl]
    rw [hL i, hL j]
    by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj, hcj]
  · intro b _ hb; simp [hb]
  · simp

theorem corner_right (P : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0)
    (hcj : cj 1 = 1) (g : K) : cjT cj P * cornerM (r := r) g * P = cornerM g := by
  ext i j
  simp only [Matrix.mul_apply, cornerM, Matrix.of_apply, cjT, Matrix.transpose_apply, Matrix.map_apply]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hP i]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hP j]
  by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj, hcj]

end Corner

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem gDiag_corner (p : PlF D) (T : D.host.E) :
    gDiag δ M p T = cornerM (frFac δ p (Fin.last D.R.rS) * (M p).L.cj (frFac δ p (Fin.last D.R.rS)) *
      (D.s.atP p).ιE (-T)) := by
  ext a b
  simp only [gDiag, cornerM, Matrix.of_apply]
  by_cases h : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
  · rw [if_pos h, if_pos h, h.1, h.2]
  · rw [if_neg h, if_neg h, map_zero, mul_zero]

theorem gaCong_L (hA : ∀ q, Agree δ M q) (p : PlF D) (hs : (M p).split = none) (T T' : D.host.E) (Z Z' : MatZ D)
    (L P : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)
    (hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0)
    (hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0)
    (hLO : ∀ i j, L i j ∈ (M p).L.O) (hPO : ∀ i j, P i j ∈ (M p).L.O)
    (hLu : ∃ y ∈ (M p).L.O, L.det * y = 1) (hPu : ∃ y ∈ (M p).L.O, P.det * y = 1)
    (hX : ZhatLoc M δ p Z' = L * ZhatLoc M δ p Z * P) :
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      GaPlus M δ p T T' Z' = (A.map (M p).L.cj).transpose * GaPlus M δ p T T' Z * A := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) with hcj
  have hinv : ∀ x, cj (cj x) = x := fun x => (M p).L.cj_cj x
  refine ⟨Matrix.fromBlocks (cjT cj L) 0 0 P, ?_, ?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O (M p).L _ (hLO j i)
    · exact (M p).L.O.zero_mem
    · exact (M p).L.O.zero_mem
    · exact hPO i j
  · obtain ⟨y, hy, hLy⟩ := hLu
    obtain ⟨z, hz, hPz⟩ := hPu
    refine ⟨cj y * z, (M p).L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O (M p).L _ hy) hz, ?_⟩
    rw [Matrix.det_fromBlocks_zero₂₁]
    have hd : (cjT cj L).det = cj L.det := by
      unfold cjT; rw [Matrix.det_transpose]; exact (RingHom.map_det cj L).symm
    rw [hd]
    calc cj L.det * P.det * (cj y * z) = cj (L.det * y) * (P.det * z) := by rw [map_mul]; ring
      _ = 1 := by rw [hLy, hPz, map_one, one_mul]
  · have e1 : GaPlus M δ p T T' Z' = GaLoc M δ p T T' Z' := by unfold GaPlus; rw [hs]
    have e2 : GaPlus M δ p T T' Z = GaLoc M δ p T T' Z := by unfold GaPlus; rw [hs]
    rw [e1, e2, gaLoc_blocks δ M hA, gaLoc_blocks δ M hA]
    show _ = cjT cj _ * _ * _
    refine (block_cong cj hinv _ _ _ _ _ _ _ _ ?_ ?_ ?_).symm
    · rw [cjT_cjT cj hinv, gDiag_corner]
      exact corner_left cj L hL (map_one cj) _
    · rw [cjT_cjT cj hinv, hX]
    · rw [gDiag_corner]
      exact corner_right cj P hP (map_one cj) _

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolumeSpans
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vector_eq_zero_of_orbital_zero {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (h : OOt t = 0) : (Y.tO u u).vec t = 0 := by
  unfold Full.tO tOf
  dsimp only
  unfold vec ampN
  rw [h]
  simp only [map_zero, smul_zero, ite_self]
  first
    | rfl
    | simp

theorem irrVec_nohyp {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (t : GTu Y u) (ht : ¬ t.relevant) :
    (Y.tO u u).vec t = 0 :=
  vector_eq_zero_of_orbital_zero Y t
    (Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
      Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
      Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t ht)

theorem IrrVecC_holds : IrrVecC := by
  intro D X Y u _ _ t _ ht
  exact irrVec_nohyp Y u t ht

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaID
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7)

def SpanOm : Prop :=
  ∀ {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T'),
    (Zhat F F').det ≠ 0 → Gflag F F' ≠ 0 →
    ∀ m ∈ orth (VS D) F'.X, ∃ x' ∈ F'.X, ∃ w ∈ orth (VS D) (F.Xplus ⊔ F'.Xplus), ∃ a b : D.host.E,
      m = x' + w + a • F'.z + b • Gom F.fvec F'.fvec

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExist
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LprEx

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem scal_rep (hrows : IsRowReps D F0 what₂) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hP : IsPartner γ Z F'')
    (hGr : Gval (lf D F0) (repF γ) ≠ 0) :
    ∃ β, IsPair γ.lam (lf D F0) (repF γ) F'' β (gS D) ∧ s0 γ.lam (lf D F0) (repF γ) F'' β D.R.k = 1 ∧
      IsScalar γ.lam (lf D F0) (repF γ) F'' β := by
  obtain ⟨hE, γ', ⟨pr, hp1, hp2, hps, hpsc⟩, h3, h3e⟩ := hP
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGF : Gval (lf D F0) F'' ≠ 0 := hE.1.2.2
  obtain ⟨lam, mem, cls⟩ := γ
  obtain ⟨lam', mem', cls'⟩ := γ'
  obtain ⟨lp, mp, p1, p2, gp1, gp2, bp, ip⟩ := pr
  simp only [Formalism.L2.SG.Corank.Pair.pfst, Formalism.L2.SG.Corank.Pair.psnd] at hp1 hp2
  obtain ⟨rfl, hc1⟩ := hp1
  obtain ⟨rfl, hc2⟩ := hp2
  exact scal_move (hrows.1 _ mp) ⟨p1, gp1⟩ ⟨p2, gp2⟩ ⟨⟨repF _, h2⟩, hGr⟩ ⟨⟨F'', h3⟩, hGF⟩ h2e.symm h3e.symm
    ⟨bp, ip, hps, hpsc⟩

variable (Zd : LocDat D)


set_option maxHeartbeats 1000000 in
theorem lprExist_of (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprExist Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'' hP p
  obtain ⟨w, hγ, -⟩ := hC
  have hR : IsRowLat D F0 γ.lam := hrows.1 γ.lam γ.mem
  have hF : FixedHyp D γ.lam (lf D F0) := hR.2.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGr : Gval (lf D F0) (repF γ) ≠ 0 := gval_repF γ w hγ
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) := by
    obtain ⟨hgen, -⟩ := hγ.1
    obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
    have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
      (h1e.trans h2e.symm)
    exact (PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hE := hP.1
  obtain ⟨β, hPair, hs, hsc⟩ := scal_rep hrows γ Z F'' hP hGr
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u'
  have hG := Formalism.L2.SG.Pf.ScalarFramePf.gfacts_of γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1
    hE.2.2.2.1.1 hPair hs hsc hGr hE.1.2.2 hT hT'
  have hIo := hI D Zd γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1 hE.2.2.2.1.1 h2.2.1 hE.1.2.1 hPair
    hgenR hE.2.2.1 hs hsc hGr hE.1.2.2 hT hT' p
  have hξ := admissibility_witness_unitriangular γ.lam (lf D F0) F''
  have hG2 := gfacts_frameAct (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hG
  have hI2 := iotaEl_frameAct Zd p (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hIo
  obtain ⟨hId, hRe⟩ := Formalism.L2.SG.Pf.ScalarFramePf.identResp_lt Zd p γ.lam (frame (lf D F0)) _ (frame F'') β
    (Tu D u) (Tu D u') hG2 hI2
  exact ⟨Formalism.L2.SG.Pf.ScalarFramePf.phiP Zd p γ.lam (frame (lf D F0)) _ (frame F'') β hG2, hId, hRe.2.2.2.1,
    hRe.2.2.1, hRe.2.2.2.2⟩

theorem lprPart_of_iota (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprPart Zd u u' F0 what₂ :=
  lprPart_of' Zd (lprExist_of Zd hI)

end LprEx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelPf
section
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.Pf.FormRelPf

def ofPts {K : Type} {i : ℕ} (s : Σ c : Composition (i + 1), (Fin c.length → K)) : List (K × ℕ) :=
  List.ofFn fun a => (s.2 a, s.1.blocksFun a)

theorem ofPts_toPts {K : Type} [Zero K] {i : ℕ} (p : Point K (i + 1)) : ofPts (toPts p) = p.1 := by
  apply List.ext_get
  · simp [ofPts, toPts, Composition.length]
  · intro n h1 h2
    simp [ofPts, toPts, Composition.blocksFun]

theorem toPts_injective {K : Type} [Zero K] {i : ℕ} :
    Function.Injective (toPts : Point K (i + 1) → Σ c : Composition (i + 1), (Fin c.length → K)) := by
  intro p q h
  apply Subtype.ext
  rw [← ofPts_toPts p, ← ofPts_toPts q, h]

end Formalism.L2.SG.Pf.FormRelPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.FormRel Formalism.L2.SG.Pf.FormRelPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem formRelC_of (hRD : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.Pf.RowForm.RealDecompC X Y u u')
    (hRC : Formalism.L2.SG.Pf.RelCharC) : FormRelC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ ν hν t ht hv => ?_⟩
  have hG : t.G ≠ 0 := Formalism.L2.SG.Pf.RowForm.realDecomp_G_ne X Y u u' t ht
  have hrel : t.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨hpt, hall⟩ := hRD D X Y u u' t hrel hG
  refine ⟨⟨_, rfl, hpt⟩, fun w hw hwr => ?_⟩
  have hw' : w = Formalism.L2.SG.PairVal.ptOf t.toTerm := toPts_injective hw
  subst hw'
  have hγ := Formalism.L2.SG.Pf.RowForm.isPtRep_gamW X u u' hwr
  obtain ⟨g, hg, g', hg', hdec⟩ := hall _ hγ
  obtain ⟨c, hc⟩ := formTransp_any (X := X) (Y := Y) (u := u) (u' := u') (νq := ν) hν.2 hRC t hrel hwr g hg g' hg'
    hdec
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  have := FiniteDimensional.complete ℂ (X.Vpi u')
  refine ⟨(c : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g')),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'), ?_⟩
  rw [hc, hdec, Formalism.L2.SG.Pf.RowForm.ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' (X.psiInfU u g) (X.psiInfU u' g')
    (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg) (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg')
    (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x), ← Complex.coe_smul, smul_smul]

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrFacInvMul
section
noncomputable section

open scoped Classical Matrix

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Key

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem cj_iota (x : D.host.E) :
    (Z.M p).L.cj ((D.s.atP p).ιE x) = (D.s.atP p).ιE (star x) := by
  have hstar : star x = D.conjF x := by
    rw [D.conjF_eq]
    have := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm
  rw [Z.hcj p, (D.s.atP p).cj_ιE, hstar]

theorem frFac_inv_mul (a : Fin (D.R.rS + 1)) : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1 :=
  Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)

theorem frFac_mul_inv (a : Fin (D.R.rS + 1)) : frFac Z.δ p a * Ring.inverse (frFac Z.δ p a) = 1 :=
  Ring.mul_inverse_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)

theorem key_rel (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hrel : Nᴴ * Z₂ = Z₁ * M) :
    ((locU Z p N).map (Z.M p).L.cj)ᵀ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, locU_apply,
    Formalism.L2.SG.CntLocal.ZhatLoc, Matrix.of_apply]
  have hL : ∀ c, (Z.M p).L.cj (Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (N c a) * frFac Z.δ p a) *
      (frFac Z.δ p b * (Z.M p).L.cj (frFac Z.δ p c) * (D.s.atP p).ιE (Z₂ c b)) =
      (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (star (N c a) * Z₂ c b) := by
    intro c
    rw [map_mul, map_mul, cj_iota Z p, map_mul (D.s.atP p).ιE]
    have h1 : (Z.M p).L.cj (Ring.inverse (frFac Z.δ p c)) * (Z.M p).L.cj (frFac Z.δ p c) = 1 := by
      rw [← map_mul, frFac_inv_mul, map_one]
    calc _ = ((Z.M p).L.cj (Ring.inverse (frFac Z.δ p c)) * (Z.M p).L.cj (frFac Z.δ p c)) *
          ((Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b *
            ((D.s.atP p).ιE (star (N c a)) * (D.s.atP p).ιE (Z₂ c b))) := by ring
      _ = _ := by rw [h1, one_mul]
  have hR : ∀ c, frFac Z.δ p c * (Z.M p).L.cj (frFac Z.δ p a) * (D.s.atP p).ιE (Z₁ a c) *
      (Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (M c b) * frFac Z.δ p b) =
      (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (Z₁ a c * M c b) := by
    intro c
    rw [map_mul (D.s.atP p).ιE]
    calc _ = (frFac Z.δ p c * Ring.inverse (frFac Z.δ p c)) *
          ((Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b *
            ((D.s.atP p).ιE (Z₁ a c) * (D.s.atP p).ιE (M c b))) := by ring
      _ = _ := by rw [frFac_mul_inv, one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl (fun c _ => hL c), Finset.sum_congr rfl (fun c _ => hR c), ← Finset.mul_sum,
    ← Finset.mul_sum, ← map_sum, ← map_sum]
  congr 2
  have := congrFun (congrFun hrel a) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at this
  exact this

end Key

end Formalism.L2.SG.Pf.FibQ
end
end

