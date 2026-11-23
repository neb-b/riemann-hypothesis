module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhaseL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ScalKindPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCountTh
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiProdE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowsInputPOfTermsFiniteSig
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0003

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutAt
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_leaves {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hA : ∀ p, Agree δ M p) (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hP : PrimeHyp D u (Tu D u')) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hM : Formalism.L2.SG.Pf.NormRepMove D u u')
    (hPG : PhaseLocG M δ u u' F0 what₂) (hVP : VolIdxProd M δ u u' F0 what₂)
    (hE : PCount.ExistP ⟨δ, M, hA⟩ u u' F0 what₂) (hS : PCount.SumFrP ⟨δ, M, hA⟩ u u' F0 what₂)
    (hG : PCount.FrGlobP ⟨δ, M, hA⟩ u u' F0 what₂) (hI : PCount.IntGenP ⟨δ, M, hA⟩)
    (hτ : PCount.TauOneReduction ⟨δ, M, hA⟩ u u' F0 what₂) (hT : PCount.PartnerIsomorphismCount ⟨δ, M, hA⟩)
    (hFS : FCount.FibSum M δ u u' F0 what₂) (hDT : FCount.DensTh M δ L u u') :
    CutAt M δ L u u' F0 what₂ := by
  have hNR := normRepElig_of hN
  have hU := Formalism.L2.SG.Pf.locUnram_holds hA u u'
  have hR := Formalism.L2.SG.Pf.thRestricted_holds_of hA hrows hN PCount.eligRel_holds
  have hTS := Formalism.L2.SG.Pf.thSome_holds hA hc hrows hNR
  refine ⟨LocOrbSumPf.localOrbitSum_holds M δ u u' hA, Formalism.L2.SG.Pf.scalKind_of hrows,
    coefficient_product_of_local hA hc hrows hN hM (phaseLoc_of hA hPG) (psi_product_e D) hVP,
    Formalism.L2.SG.Pf.partnerCount_holds hA hc hrows hP hU hR hE hS hG hI hτ hT,
    FCount.fiberCount_of_rest hA hc hP hU hR hrows hN PCount.eligRel_holds (hE ⟨hc, hrows, hP⟩) hTS hFS
      nu_not_class_holds hDT (FCount.eligible_totally_positive u u' F0 what₂),
    hNR, hTS, ⟨LocModel.thTriv M, hU, hR⟩⟩

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerShOfKind
section
noncomputable section

open scoped Classical
open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cornerSh_of_kind (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D)
    {w w' : Point D.host.E (D.R.rS + 1)} (h : kind w = kind w') : cornerSh δ T T' p w = cornerSh δ T T' p w' := by
  unfold kind at h
  unfold cornerSh
  by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0
  · simp [h1, h2]
  · simp [h1, h2] at h
  · simp [h1, h2] at h
  · simp only [h1, h2, if_false] at h ⊢
    rw [Option.some.inj h]

theorem sgn_sq (q : ℕ) :
    (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem lead_at {w : Point D.host.E (D.R.rS + 1)} {Z : PairVal.MatR D} (hZ : AtMat w Z) (q : ℕ) (hq : q ≤ D.R.rS + 1) :
    leadMinorE Z q = (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * Dmin w q := by
  have h1 := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_cell (ZhatOM Z) w hZ q
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_ZhatOM Z q hq, Formalism.L2.SG.NGCut.NormalVectorPairings.leadingMinor_eq_pointMinor w q hq] at h1
  rw [h1, ← mul_assoc, sgn_sq, one_mul]

theorem cross_of_kind {w w' : Point D.host.E (D.R.rS + 1)} {Z Z' : PairVal.MatR D} (hk : kind w = kind w')
    (hZ : AtMat w Z) (hZ' : AtMat w' Z') :
    leadMinorE Z D.R.rS * leadMinorE Z' (D.R.rS + 1) = leadMinorE Z' D.R.rS * leadMinorE Z (D.R.rS + 1) := by
  rw [lead_at hZ _ (Nat.le_succ _), lead_at hZ' _ le_rfl, lead_at hZ' _ (Nat.le_succ _), lead_at hZ _ le_rfl]
  have key : Dmin w D.R.rS * Dmin w' (D.R.rS + 1) = Dmin w' D.R.rS * Dmin w (D.R.rS + 1) := by
    unfold kind at hk
    by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0
    · rw [h1, h2]; ring
    · simp [h1, h2] at hk
    · simp [h1, h2] at hk
    · simp only [h1, h2, if_false, Option.some.injEq] at hk
      unfold zetaOf at hk
      field_simp at hk
      linear_combination -hk
  linear_combination (∏ b : Fin D.R.rS, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) *
    (∏ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * key

theorem inv_last_mul_det {K : Type*} [CommRing K] {m : ℕ} (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hY : IsUnit Y.det) :
    Y⁻¹ (Fin.last m) (Fin.last m) * Y.det = (Y.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, smul_eq_mul]
  simp only [Fin.succAbove_last, Fin.val_last]
  rw [show ((-1 : K) ^ (m + m)) = 1 by rw [← two_mul, pow_mul]; simp, one_mul, mul_comm, ← mul_assoc,
    Ring.mul_inverse_cancel _ hY, one_mul]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open BwdCut BwdBetaCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaCut


variable (u u' F0 what₂) in
def BHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  CtxP u u' F0 what₂ ∧ Ctx γ Z ∧ StarHyp Zd γ Z F'₂ φ φ' ∧ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ' ∧
    (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) ∧
    TermHyp (F0 := F0) Λ₂ F'₂ ∧ PD D γ.lam (lf D F0) u' (repF γ) ∧ Gval (lf D F0) (repF γ) ≠ 0

def OmB {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {T' : D.host.E} (F' F₂ : LFlag (D.sp.Y 0) D.R.rS T')
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  star (GDl (frame F) (frame F₂) (D.R.rS + 1)) • β (Gom (frame F) (frame F')) -
      star (GDl (frame F) (frame F') (D.R.rS + 1)) • Gom (frame F) (frame F₂) ∈ Xsp F₂

end BwdBetaCut

variable (u u' F0 what₂)

def BetaRat : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∃ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) ∧
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ ∧ OmB (lf D F0) (repF γ) (liftF F'₂) β₀

def ScalarOf : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V, β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β (frame (repF γ) b) = frame (liftF F'₂) b) → OmB (lf D F0) (repF γ) (liftF F'₂) β →
      Scalar₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β

def BetaInt : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∃ v : (VS D).V ≃ₗ[D.host.E] (VS D).V, v ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
        (∀ b, v (frame (liftF F'₂) b) = frame (liftF F'₂) b) ∧
        (∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), v y - y ∈ Xsp (liftF F'₂)) ∧
        Formalism.HermitianLatticesTheory.gmap (v * β₀) γ.lam = Λ₂ ∧ IotaC₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀)

variable {u u' F0 what₂}

namespace BwdBetaCut

variable {T T' : D.host.E}

theorem fvec_cs' (F : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) : frame F i.castSucc = F.fl.e i := by
  first
  | exact PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc F.fl i
  | simp [frame]
  | rfl

theorem fvec_last' (F : LFlag (D.sp.Y 0) D.R.rS T) : frame F (Fin.last _) = F.fl.z := by
  first
  | exact PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last F.fl
  | simp [frame]
  | rfl

theorem e_of_frame (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F F₂ : LFlag (D.sp.Y 0) D.R.rS T')
    (h : ∀ b, β (frame F b) = frame F₂ b) (i : Fin D.R.rS) : β (F.fl.e i) = F₂.fl.e i := by
  have hi := h i.castSucc
  rwa [fvec_cs', fvec_cs'] at hi

theorem Xflag_of_frame (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F F₂ : LFlag (D.sp.Y 0) D.R.rS T')
    (h : ∀ b, β (frame F b) = frame F₂ b) (j : ℕ) :
    (Xflag F j).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag F₂ j := by
  ext x
  rw [Submodule.mem_map_equiv]
  exact (Formalism.L2.SG.Pf.mem_xflag_of_frame (fun a => (h a).symm) j x).symm

theorem Xsp_of_frame (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F F₂ : LFlag (D.sp.Y 0) D.R.rS T')
    (h : ∀ b, β (frame F b) = frame F₂ b) :
    (Xsp F).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F₂ := by
  rw [← Formalism.L2.SG.FourParts.Xflag_r, ← Formalism.L2.SG.FourParts.Xflag_r]
  exact Xflag_of_frame β F F₂ h D.R.rS

theorem Gom_orth (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Gom (frame F) (frame F') ∈ orth (VS D) (Xsp F') := by
  have om_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
      (VS D).hT (Gom u v) (v b) = if b = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
    have key := congrFun (congrFun (Matrix.adjugate_mul (GZ u v)) (Fin.last _)) b
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
    unfold GDl
    rw [dite_eq_left le_rfl]
    unfold Gom
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
    change (∑ a, (GZ u v).adjugate (Fin.last _) a * GZ u v a b) = _
    rw [key]
    rcases eq_or_ne b (Fin.last _) with hb | hb
    · subst hb
      simp
    · rw [if_neg (Ne.symm hb), if_neg hb, smul_zero]
  unfold orth Xsp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  unfold Formalism.MainNotions.S.FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [← fvec_cs' F' i, PI.NRL.herm_eq, om_pair,
      if_neg (Fin.castSucc_lt_last i).ne, star_zero]
  | zero => simp
  | add y z _ _ hy hz => simp [map_add (f := _), hy, hz]
  | smul a y _ hy => simp [hy]

end BwdBetaCut

namespace BwdBetaCut

theorem comb_mem {V : Type*} [AddCommGroup V] [Module D.host.E V] {X : Submodule D.host.E V}
    (v : V ≃ₗ[D.host.E] V) (a c : D.host.E) (p q : V) (h : a • p - c • q ∈ X) (hvX : ∀ y ∈ X, v y ∈ X)
    (hq : v q - q ∈ X) : a • v p - c • q ∈ X := by
  have h1 := hvX _ h
  rw [map_sub, map_smul, map_smul] at h1
  have h2 := X.add_mem h1 (X.smul_mem c hq)
  convert h2 using 1
  rw [smul_sub]
  abel

private theorem Hp_le_orth_Xsp (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsFullLattice D.host.E Λ)
    {T₁ T₂ : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T₁) (F' : LFlag (D.sp.Y 0) D.R.rS T₂) :
    Hp Λ F F' ≤ orth (VS D) (Xsp F') := by
  have hX : Xsp F' ≤ UUE Λ F F' :=
    PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' (VS D) Λ hΛ F F'
  unfold Hp UUE
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
  intro x hx
  exact hy x (hX hx)

end BwdBetaCut

theorem betaCore₂_of (h1 : BetaRat Zd u u' F0 what₂) (h2 : ScalarOf Zd u u' F0 what₂) (h3 : BetaInt Zd u u' F0 what₂) :
    BetaCore₂ Zd u u' F0 what₂ := by
  unfold BetaRat at h1
  unfold ScalarOf at h2
  unfold BetaInt at h3
  unfold BetaCore₂
  intro hP γ Z hC F'₂ φ φ' hS Λ₂ hG hn hT hPD hv0
  have hB : BwdBetaCut.BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ := by
    unfold BwdBetaCut.BHyp
    exact ⟨hP, hC, hS, hG, hn, hT, hPD, hv0⟩
  obtain ⟨β₀, hi₀, hf₀, hW₀, hO₀⟩ := h1 γ Z F'₂ φ φ' Λ₂ hB
  obtain ⟨v, hiv, hfv, hov, hgm, hio⟩ := h3 γ Z F'₂ φ φ' Λ₂ hB β₀ hi₀ hf₀ hW₀ hO₀
  have hfr : ∀ b, (v * β₀) (frame (repF γ) b) = frame (liftF F'₂) b := by
    intro b
    rw [LinearEquiv.mul_apply, hf₀, hfv]
  have hXv : ∀ y ∈ Xsp (liftF F'₂), v y ∈ Xsp (liftF F'₂) := by
    intro y hy
    rw [← BwdBetaCut.Xsp_of_frame v (liftF F'₂) (liftF F'₂) hfv]
    exact Submodule.mem_map_of_mem hy
  have hO : BwdBetaCut.OmB (lf D F0) (repF γ) (liftF F'₂) (v * β₀) := by
    unfold BwdBetaCut.OmB at hO₀ ⊢
    rw [LinearEquiv.mul_apply]
    exact BwdBetaCut.comb_mem v _ _ _ _ hO₀ hXv (hov _ (BwdBetaCut.Gom_orth _ _))
  have hi : v * β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hiv hi₀
  have hW : BwdBetaCut.W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀) := by
    unfold BwdBetaCut.W0₂ at hW₀ ⊢
    intro w hw
    obtain ⟨w₂, hw₂, hd1, hd2⟩ := hW₀ w hw
    refine ⟨w₂, hw₂, hd1, ?_⟩
    have hw₂o := BwdBetaCut.Hp_le_orth_Xsp Λ₂ hG.1 _ _ hw₂
    have hs := (Xsp (liftF F'₂)).add_mem (hXv _ hd2) (hov _ hw₂o)
    rw [LinearEquiv.mul_apply]
    convert hs using 1
    rw [map_sub]
    abel
  refine ⟨v * β₀, ?_⟩
  unfold BwdBetaCut.IsPair₂
  refine ⟨hi, hgm, fun j => BwdBetaCut.Xflag_of_frame _ _ _ hfr j, ?_, hio, hW,
    h2 γ Z F'₂ φ φ' Λ₂ hB _ hi hfr hO⟩
  rw [← BwdBetaCut.fvec_last' (repF γ), ← BwdBetaCut.fvec_last' (liftF F'₂)]
  exact hfr _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNF
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem mem_of_bcP {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) {x : (VS D).V}
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ) : x ∈ Λ := by
  refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) Λ hΛ.toIsLattice x fun v => ?_
  have := v.isPrime
  letI := hΛ
  have h2 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd v (Λ := Λ) (by infer_instance) x).1 (h v)
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal Λ x).1 h2

theorem baseChange_mem_localLattice {Λ : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ Λ) (p : PlF D) :
    baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ := Submodule.subset_span ⟨x, hx, rfl⟩

theorem iE_intD (p : PlF D) {y : D.host.E} (hy : IsIntegral ℤ y) : (D.s.atP p).ιE y ∈ (Zd.M p).L.O := by
  rw [LocFacts.lf_hO Zd p]
  exact Formalism.L2.SG.Pf.StabIntSh.lg_iota_int p ⟨y, hy⟩

theorem int_of_loc {y : D.host.E} (h : ∀ p, (D.s.atP p).ιE y ∈ (Zd.M p).L.O) : IsIntegral ℤ y :=
  Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc y fun p => by rw [← LocFacts.lf_hO Zd p]; exact h p

theorem localForm_baseChange (p : PlF D) (x y : (VS D).V) :
    (locH Zd p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
  baseChangeAt_form Zd.M p (Zd.hcj p) x y

theorem h_eq (p : PlF D) : (locH Zd p).h = LocFacts₂ Zd.M p := rfl

theorem sd_of_loc {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hloc : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ)) : BwdNA.SD (VS D) Λ := by
  intro x
  constructor
  · intro hx y hy
    refine int_of_loc Zd fun p => ?_
    rw [← localForm_baseChange]
    exact ((hloc p).2.2 (baseChange₂ D p x)).1 (baseChange_mem_localLattice Zd hx p) (baseChange₂ D p y) (baseChange_mem_localLattice Zd hy p)
  · intro h
    refine mem_of_bcP Zd hΛ fun p => ((hloc p).2.2 _).2 fun w hw => ?_
    rw [h_eq]
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← h_eq, localForm_baseChange]
      exact iE_intD Zd p (h y hy)
    | zero => rw [LocFacts.localForm_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right]; exact add_mem ha hb
    | smul o w _ hw =>
      change LocFacts₂ Zd.M p (baseChange₂ D p x) ((o : (D.s.atP p).Ep) • w) ∈ _
      rw [LocFacts.localForm_smul_right]
      exact mul_mem (LocFacts.lf_cjM_mem Zd p _ o.2) hw

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem tf (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (a : Fin (D.R.rS + 1)) :
    (tLoc Zd p γ).f a = (TermLoc.sgnP D p a * frFac Zd.δ p a) • baseChange₂ D p (frame (lf D F0) a) := rfl

theorem sgnP_last (p : PlF D) : TermLoc.sgnP D p (Fin.last D.R.rS) = 1 := by
  unfold TermLoc.sgnP
  split
  · simp
  · rfl

theorem frFac_last' (p : PlF D) : frFac Zd.δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac; simp

theorem tf_last (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) :
    (tLoc Zd p γ).f (Fin.last D.R.rS) = baseChange₂ D p F0.z := by
  rw [tf, sgnP_last, frFac_last', one_mul, one_smul]
  congr 1
  simp [frame, FlagG.fvec]

theorem frame_cs (i : Fin D.R.rS) : frame (lf D F0) i.castSucc = F0.e i := by
  simp [frame, FlagG.fvec]

theorem unit_of_frame (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {L : Submodule (Zd.M p).L.O (Vp D p)}
    {T : (D.s.atP p).Fp} (hfr : (locH Zd p).IsFrame L D.R.rS (tLoc Zd p γ).f T) (a : Fin (D.R.rS + 1)) :
    IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := by
  have hs : IsUnit (TermLoc.sgnP D p a) := ⟨⟨TermLoc.sgnP D p a, TermLoc.sgnP D p a, TermLoc.localSign_sq p a, TermLoc.localSign_sq p a⟩, rfl⟩
  refine hs.mul ?_
  by_cases h : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
      (D.R.rS - a.val))
  · obtain ⟨w, hw⟩ := h
    unfold frFac
    rw [← hw, Ring.inverse_unit]
    exact Units.isUnit _
  · exfalso
    have h0 : frFac Zd.δ p a = 0 := by unfold frFac; exact Ring.inverse_non_unit _ h
    have hne := hfr.1.2.1.ne_zero a
    apply hne
    rw [tf, h0, mul_zero, zero_smul]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

