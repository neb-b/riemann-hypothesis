module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0021
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.IdxCocycle

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfModUnits
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

section Shape

variable {K : Type*} [CommRing K] {r : ℕ}

theorem leadM_zero_row (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (k : Fin (r + 1)) (hk : k ≠ Fin.last r)
    (h : ∀ b, b ≠ Fin.last r → A k b = 0) : leadM A r = 0 := by
  have hk' : k.val < r := Fin.val_lt_last hk
  unfold leadM
  rw [dite_eq_left (Nat.le_succ r)]
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨k.val, hk'⟩ fun b => ?_
  simp only [Matrix.submatrix_apply]
  have e : Fin.castLE (Nat.le_succ r) ⟨k.val, hk'⟩ = k := Fin.ext rfl
  rw [e]
  exact h _ (castLE_ne_last b)

theorem det_of_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (h : ∀ a : Fin r, A a.castSucc (Fin.last r) = 0 ∧ A (Fin.last r) a.castSucc = 0) :
    A.det = A (Fin.last r) (Fin.last r) * leadM A r := by
  have hA : A = (A + (-A (Fin.last r) (Fin.last r)) • Ecorner r) + A (Fin.last r) (Fin.last r) • Ecorner r := by
    rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
  have h0 : (A + (-A (Fin.last r) (Fin.last r)) • Ecorner r).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero (Fin.last r) fun b => ?_
    by_cases hb : b = Fin.last r
    · subst hb; simp [Ecorner]
    · obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.2 hb
      simp [Ecorner, (h b').2, Fin.castSucc_ne_last]
  conv_lhs => rw [hA]
  rw [det_add_corner, h0, zero_add, leadM_add_corner]

end Shape

section ModShape

variable {D : Formalism.BasicNotions.D7}

theorem lead_zero_of_sg (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (h : sgF w (Fin.last D.R.rS) ≠ Fin.last D.R.rS) :
    leadM (modMat δ T T' p w) D.R.rS = 0 ∧ Dmin w D.R.rS = 0 := by
  constructor
  · exact leadM_zero_row _ (sgF w (Fin.last _)) h fun b hb => by
      rw [modMat_apply', if_neg (by rw [sgF_sgF]; exact hb)]
  · exact leadM_zero_row (ptMat w) (sgF w (Fin.last _)) h fun b hb => by
      rw [ptMat_apply', if_neg (by rw [sgF_sgF]; exact hb)]

theorem shape_of_sg (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (h : sgF w (Fin.last D.R.rS) = Fin.last D.R.rS) :
    (∀ a : Fin D.R.rS, modMat δ T T' p w a.castSucc (Fin.last _) = 0 ∧
      modMat δ T T' p w (Fin.last _) a.castSucc = 0) ∧
    (∀ a : Fin D.R.rS, ptMat w a.castSucc (Fin.last _) = 0 ∧ ptMat w (Fin.last _) a.castSucc = 0) ∧
    modMat δ T T' p w (Fin.last _) (Fin.last _) = blkMod δ T T' p (D.R.rS + 1) 1 (pTau w.1 D.R.rS) ∧
    ptMat w (Fin.last _) (Fin.last _) = pTau w.1 D.R.rS := by
  have hne : ∀ a : Fin D.R.rS, a.castSucc ≠ sgF w (Fin.last _) := fun a => by
    rw [h]; exact Fin.castSucc_ne_last a
  have hne' : ∀ a : Fin D.R.rS, Fin.last _ ≠ sgF w a.castSucc := fun a e => by
    have := congrArg (sgF w) e
    rw [sgF_sgF, h] at this
    exact Fin.castSucc_ne_last a this.symm
  have hp : pSig w.1 D.R.rS = D.R.rS := by
    have := congrArg Fin.val h
    simpa [sgF] using this
  have hsum := w.2.2
  obtain ⟨-, -, h3, -, h5⟩ := pBlock w.1 D.R.rS (by rw [hsum]; omega)
  have h5' := h5 (by rw [hsum])
  rw [hsum] at h5'
  rw [hp] at h3
  refine ⟨fun a => ⟨?_, ?_⟩, fun a => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [modMat_apply', if_neg (hne' a)]
  · rw [modMat_apply', if_neg (hne a)]
  · rw [ptMat_apply', if_neg (hne' a)]
  · rw [ptMat_apply', if_neg (hne a)]
  · rw [modMat_apply', if_pos h.symm]
    simp only [Fin.val_last]
    rw [show 1 + pSt w.1 D.R.rS = D.R.rS + 1 by omega, show pSz w.1 D.R.rS = 1 by omega]
  · rw [ptMat_apply', if_pos h.symm]
    simp only [Fin.val_last]

variable (Zd : LocDat D)

def ModUnits : Prop :=
  ∀ (p : PlF D) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)), sgF w (Fin.last D.R.rS) = Fin.last D.R.rS →
    Dmin w D.R.rS ≠ 0 ∧ IsUnit (leadM (modMat Zd.δ T T' p w) D.R.rS) ∧
    IsUnit (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (pTau w.1 D.R.rS) +
      ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (pTau w.1 D.R.rS)) : ℕ) : (D.s.atP p).Ep))

theorem modKind_of (hU : ModUnits Zd) : ModKind Zd := by
  intro p T T' w
  by_cases hs : sgF w (Fin.last D.R.rS) = Fin.last D.R.rS
  · obtain ⟨hD, hu, hn⟩ := hU p T T' w hs
    obtain ⟨hm, hpt, hc, hpc⟩ := shape_of_sg Zd.δ T T' p w hs
    have hz : zetaOf w = pTau w.1 D.R.rS := by
      unfold zetaOf
      have e : Dmin w (D.R.rS + 1) = pTau w.1 D.R.rS * Dmin w D.R.rS := by
        show leadM (ptMat w) (D.R.rS + 1) = _ * leadM (ptMat w) D.R.rS
        rw [leadM_top, det_of_corner _ hpt, hpc]
      rw [e, mul_div_cancel_right₀ _ hD]
    refine ⟨fun h => absurd h hD, fun _ => ⟨hu, hm, ?_, ?_⟩⟩ <;> rw [hz]
    · exact hc
    · exact hn
  · obtain ⟨h1, h2⟩ := lead_zero_of_sg Zd.δ T T' p w hs
    exact ⟨fun _ => h1, fun h => absurd h2 h⟩

theorem partnerCount_of_modUnits (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd) (hU : ModUnits Zd) (hB : BridgeBA) : PartnerIsomorphismCount Zd :=
  partnerIsomorphismCount_of_bounds Zd hT2 hI (leadZZ_holds Zd) (modKind_of Zd hU) hB

end ModShape

end Formalism.L2.SG.Pf.PCount
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountP
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section P

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def CtxP : Prop :=
  (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ IsRowReps D F0 what₂ ∧ Lat.PrimeHyp D u (Tu D u')

def FrGlobP : Prop := CtxP u u' F0 what₂ → FrGlob Zd u u' F0 what₂

def TauOneReduction : Prop := CtxP u u' F0 what₂ → Tau1 Zd u u' F0 what₂

def ExistP : Prop := CtxP u u' F0 what₂ → Exist Zd.M Zd.δ u u'

def SumFrP : Prop := CtxP u u' F0 what₂ → SumFr Zd.M Zd.δ u u' F0 what₂

variable {u u' F0 what₂}

theorem normRepExists_ctx (h : CtxP u u' F0 what₂) : PairVal.NormRepExists D u u' F0 what₂ := normRepExists_of (NormRepX.norm_representative_holds D u u' h.2.2) (Formalism.L2.SG.Closed.TermFun_holds D u u') h.2.1

theorem frCount_ctx (hG : FrGlobP Zd u u' F0 what₂) (hI : IntGenP Zd) (hτ : TauOneReduction Zd u u' F0 what₂) (hT : PartnerIsomorphismCount Zd)
    (h : CtxP u u' F0 what₂) : FrCount Zd.M Zd.δ u u' F0 what₂ := pcount_frCount Zd (normRepExists_ctx h) h.2.1 (hG h) hI (inOrbZ_holds Zd u u') (hτ h) hT

theorem partnerCount_ctx {θ0 : ∀ p, Option ((Zd.M p).Cls D.R.rS)}
    (hU : LocUnram Zd.M Zd.δ u u' θ0) (hR : ThRestricted Zd.M Zd.δ u u' F0 what₂ θ0)
    (hE : ExistP Zd u u' F0 what₂) (hS : SumFrP Zd u u' F0 what₂)
    (hG : FrGlobP Zd u u' F0 what₂) (hI : IntGenP Zd) (hτ : TauOneReduction Zd u u' F0 what₂) (hT : PartnerIsomorphismCount Zd)
    (h : CtxP u u' F0 what₂) : PartnerCount Zd.M Zd.δ u u' F0 what₂ := partnerCount_of hU hR h.2.1 (normRepExists_ctx h) eligRel_holds
    (restr_of Zd.3 h.2.1 (normRepExists_ctx h) eligRel_holds) (hE h) (hS h) (frCount_ctx Zd hG hI hτ hT h)

end P

end Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem partnerCount_holds {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hrows : IsRowReps D F0 what₂)
    (hP : Lat.PrimeHyp D u (Tu D u')) {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LsDatumB.LocUnram M δ u u' θ0) (hR : LsDatumB.ThRestricted M δ u u' F0 what₂ θ0)
    (hE : PCount.ExistP ⟨δ, M, hA⟩ u u' F0 what₂) (hS : PCount.SumFrP ⟨δ, M, hA⟩ u u' F0 what₂)
    (hG : PCount.FrGlobP ⟨δ, M, hA⟩ u u' F0 what₂) (hI : PCount.IntGenP ⟨δ, M, hA⟩)
    (hτ : PCount.TauOneReduction ⟨δ, M, hA⟩ u u' F0 what₂) (hT : PCount.PartnerIsomorphismCount ⟨δ, M, hA⟩) :
    LsDatumB.PartnerCount M δ u u' F0 what₂ := PCount.partnerCount_ctx ⟨δ, M, hA⟩ hU hR hE hS hG hI hτ hT ⟨hc, hrows, hP⟩

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TargetFact
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Helpers

variable {K : Type*} [CommRing K] {n : ℕ}

theorem isUp_sconj {S X : Matrix (Fin n) (Fin n) K} (s d d' : Fin n → K) (hS : S = Matrix.diagonal s)
    (hs : ∀ a, s a * s a = 1) (hd : ∀ a, d a * d' a = 1) (hX : IsUp X) :
    IsUp (S * Matrix.diagonal d * X * Matrix.diagonal d' * S) := by
  have e : S * Matrix.diagonal d * X * Matrix.diagonal d' * S =
      Matrix.diagonal (fun a => s a * d a) * X * Matrix.diagonal (fun a => d' a * s a) := by
    rw [hS, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc _ (Matrix.diagonal d'), Matrix.diagonal_mul_diagonal]
  rw [e]
  exact isUp_conj hX _ _ fun a => by
    calc s a * d a * (d' a * s a) = (d a * d' a) * (s a * s a) := by ring
      _ = 1 := by rw [hd, hs, one_mul]

theorem isLo_sconj {S X : Matrix (Fin n) (Fin n) K} (s d d' : Fin n → K) (hS : S = Matrix.diagonal s)
    (hs : ∀ a, s a * s a = 1) (hd : ∀ a, d a * d' a = 1) (hX : IsLo X) :
    IsLo (S * Matrix.diagonal d * X * Matrix.diagonal d' * S) := by
  have e : S * Matrix.diagonal d * X * Matrix.diagonal d' * S =
      Matrix.diagonal (fun a => s a * d a) * X * Matrix.diagonal (fun a => d' a * s a) := by
    rw [hS, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc _ (Matrix.diagonal d'), Matrix.diagonal_mul_diagonal]
  rw [e]
  exact isLo_conj hX _ _ fun a => by
    calc s a * d a * (d' a * s a) = (d a * d' a) * (s a * s a) := by ring
      _ = 1 := by rw [hd, hs, one_mul]

theorem isLo_one' {K : Type*} [CommRing K] {n : ℕ} : IsLo (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne]⟩

theorem isUp_one' {K : Type*} [CommRing K] {n : ℕ} : IsUp (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩

end Helpers

section ClearFp

variable {D : Formalism.BasicNotions.D7}

theorem clear_Fp (p : PlF D) {ι : Type} [Fintype ι] (z : ι → (D.s.atP p).Fp) :
    ∃ c : 𝓞 D.host.F, c ≠ 0 ∧ ∀ k,
      (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c) * z k ∈ (haveI := (D.s.atP p).lf; 𝒪[(D.s.atP p).Fp]) := by
  haveI := (D.s.atP p).lf
  have h := fun k => clear_F (fun q => D.s.atP q) p (z k)
  choose t ht0 htz using h
  refine ⟨∏ k, t k, Finset.prod_ne_zero_iff.2 fun k _ => ht0 k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), map_mul, map_mul,
    mul_comm ((D.s.atP p).ιF (algebraMap _ _ (t k))), mul_assoc]
  exact Subring.mul_mem _ (iotaF_int_mem (fun q => D.s.atP q) p _) (htz k)

end ClearFp

section TypedFact

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)
  (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
  (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Zd.M p).L) (hM : (Zd.M p).split = some g)
  (hge : g.e = sg.e) (hgq : g.q = sg.q)
include hR hM hge hgq


set_option maxHeartbeats 1000000 in
theorem zz_fact (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {L B : PairVal.MatR D} (hL : IsLo L)
    (hB : IsUp B) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) * LsDatumB.sgnP p =
      glue sg.e (Matrix.diagonal (cf Zd p) * L.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))
          (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p)) *
        glue sg.e ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
            (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
              (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS)
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
            (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
              ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS) *
        glue sg.e (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))
          (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) := by
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  set S := Sg (D.s.atP p).Fp D.R.rS with hS
  have hZ : (L * ptMat w * B * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w * B := by
    rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  have hΛ1 : IsLo (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) :=
    isLo_conj (isLo_map φ1 hL) _ _ (cf_cfi Zd p)
  have hV1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map φ1 * Matrix.diagonal (cf Zd p)) :=
    isUp_conj (isUp_map φ1 hB) _ _ (cfi_cf Zd p)
  have hBt : IsLo (S * (B.map φ2).transpose * S) :=
    isLo_conj (isLo_transpose (isUp_map φ2 hB)) _ _ (fun a => sgn_sq' D.R.rS a)
  have hLt : IsUp (S * (L.map φ2).transpose * S) :=
    isUp_conj (isUp_transpose (isLo_map φ2 hL)) _ _ (fun a => sgn_sq' D.R.rS a)
  have hΛ2 : IsLo (Matrix.diagonal (cf Zd p) * (S * (B.map φ2).transpose * S) * Matrix.diagonal (cfi Zd p)) :=
    isLo_conj hBt _ _ (cf_cfi Zd p)
  have hV2 : IsUp (Matrix.diagonal (cfi Zd p) * (S * (L.map φ2).transpose * S) * Matrix.diagonal (cf Zd p)) :=
    isUp_conj hLt _ _ (cfi_cf Zd p)
  refine mat_eq sg.e ?_ ?_
  · have l1 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) *
        LsDatumB.sgnP p).map (p1 sg.e) =
        (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) *
          ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map φ1 * Matrix.diagonal (cf Zd p))) *
          (Matrix.diagonal (cfi Zd p) * B.map φ1 * Matrix.diagonal (cf Zd p)) -
        (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
      rw [zz1' Zd p sg hR g hM hge hgq, hZ, Matrix.map_mul, Matrix.map_mul, fact1 _ _ (cfi_cf Zd p)]
    rw [l1, Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, glue_map_fst, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hΛ1 hV1]
  · have e2 : ((L * ptMat w * B * Sg D.host.E D.R.rS).map φ2).transpose * S =
        (S * (B.map φ2).transpose * S) * (S * (ptMat w).map φ2 * S) * (S * (L.map φ2).transpose * S) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
      exact fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])
    have l2 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) *
        LsDatumB.sgnP p).map (p2 sg.e) =
        (Matrix.diagonal (cf Zd p) * (S * (B.map φ2).transpose * S) * Matrix.diagonal (cfi Zd p)) *
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (S * (ptMat w).map φ2 * S) *
            Matrix.diagonal (cf Zd p))) *
          (Matrix.diagonal (cfi Zd p) * (S * (L.map φ2).transpose * S) * Matrix.diagonal (cf Zd p)) -
        ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
      rw [zz2' Zd p sg hR g hM hge hgq, e2, fact1 _ _ (cfi_cf Zd p)]
    rw [l2, Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, glue_map_snd, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hΛ2 hV2]


set_option maxHeartbeats 1000000 in
theorem target_fact (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) :
    ∃ Gl Gu : MatP D p, IsLo Gl ∧ IsUp Gu ∧
      glue sg.e ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
            (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
              (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS)
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
            (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
              ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS) =
        Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0 :=
    fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  obtain ⟨L1, U1, hL1, hU1, h1⟩ := generic_comp (sgF w) (sgF_sgF _) (isLo_one' (K := (D.s.atP p).Fp))
    (isUp_one' (K := (D.s.atP p).Fp))
    (W := (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE))
    (fun a b hb => by simp only [Matrix.map_apply, ptMat_apply', if_neg hb, map_zero])
    (fun a => by
      simp only [Matrix.map_apply, ptMat_apply', if_true]
      exact (map_ne_zero _).2 (pTau_ne' _ a))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (sg.q : (D.s.atP p).Fp)⁻¹ (inv_ne_zero hq)
    (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  obtain ⟨L2, U2, hL2, hU2, h2⟩ := generic_comp (sgF w) (sgF_sgF _) (isLo_one' (K := (D.s.atP p).Fp))
    (isUp_one' (K := (D.s.atP p).Fp))
    (W := Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS)
    (fun a b hb => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb, map_zero,
        mul_zero, zero_mul])
    (fun a => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true]
      exact mul_ne_zero (mul_ne_zero (hs0 _) ((map_ne_zero _).2 (pTau_ne' _ a))) (hs0 _))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (-(sg.q : (D.s.atP p).Fp)⁻¹) (neg_ne_zero.2 (inv_ne_zero hq))
    ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  rw [Matrix.one_mul, Matrix.mul_one] at h1 h2
  refine ⟨glue sg.e L1 L2, glue sg.e U1 U2, isLo_glue sg.e hL1 hL2, isUp_glue sg.e hU1 hU2, mat_eq sg.e ?_ ?_⟩
  · rw [glue_map_fst, h1, Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, mm1' Zd p sg hR g hM hge hgq]
  · rw [glue_map_snd, h2, Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, mm2' Zd p sg hR g hM hge hgq]

end TypedFact

end Formalism.L2.SG.Pf.PCountEx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupGlob
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

def IntFr (U : PairVal.MatR D) : Prop :=
  ∀ c b : Fin (D.R.rS + 1), c < b → ∀ x ∈ FibQ.aaF D b, x * U c b ∈ FibQ.aaF D c

def TieG (U U' : PairVal.MatR D) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ c b : Fin (D.R.rS + 1),
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * (U c b - U' c b) = ((Lat.gS D : ℕ) : D.host.E) * o


variable (D) in
def GlobMove (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z₁ Z₂ : PairVal.MatR D), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
    AtMat w Z₁ → AtMat w Z₂ → (∀ p, tupZ M δ u u' Z₁ p = tupZ M δ u u' Z₂ p) →
    ∃ U U' : PairVal.MatR D, IsUpUni U ∧ IsUpUni U' ∧ IntFr U ∧ IntFr U' ∧ TieG U U' ∧ Z₂ = U.conjTranspose * Z₁ * U'

end Formalism.L2.SG.Pf.TupGlob
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolCut
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolCut

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.Coef Formalism.L2.SG.PairVal Formalism.L2.SG.Pf.IndexCocycleOrbits
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def HypE (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D) : Prop :=
  (∀ p, Agree δ M p) ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ IsRowReps D F0 what₂ ∧
    PrimeHyp D u (Tu D u') ∧ EligAt γ w ∧ PairVal.NormRep γ w F' L U

def stZSet (Z L : PairVal.MatR D) : Set (PairVal.GLR D) :=
  {a | ∃ a' : PairVal.GLR D, (a : PairVal.MatR D) = L⁻¹ * (a' : PairVal.MatR D) * L ∧ IsLoUni (a' : PairVal.MatR D) ∧
    ∃ b : PairVal.MatR D, IsUpUni b ∧ (a' : PairVal.MatR D) * ZhatOM Z * b = ZhatOM Z ∧
      ∀ p : PlF D, ∃ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
        Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧
        ∀ Z' : PairVal.MatR D, CntLocal.ZZP (M := M) δ u u' p (ZhatOM ((a' : PairVal.MatR D) * ZhatOM Z' * b)) =
          l * CntLocal.ZZP (M := M) δ u u' p Z' * ρ}

def CZ (Z L : PairVal.MatR D) : Subgroup (PairVal.GLR D) := Subgroup.closure (stZSet M δ u u' Z L)

def OrbStabE (C : PairVal.MatR D → PairVal.MatR D → Subgroup (PairVal.GLR D)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    PairVal.stabAut D u u' F0 what₂ γ F' L ≤ C (ZhatL (lf D F0) F') L ∧
      (PairVal.stabAut D u u' F0 what₂ γ F' L).relIndex (C (ZhatL (lf D F0) F') L) =
        (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard ∧
      (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard ≠ 0

def ProdE (C : PairVal.MatR D → PairVal.MatR D → Subgroup (PairVal.GLR D)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    IdxRatio (PairVal.stabInt D u u' δ M w) (C (ZhatL (lf D F0) F') L) =
      ∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

theorem volIdxProd_of (hP : PrimeHyp D u (Tu D u')) (C : PairVal.MatR D → PairVal.MatR D → Subgroup (PairVal.GLR D))
    (h1 : OrbStabE M δ u u' F0 what₂ C) (h2 : ProdE M δ u u' F0 what₂ C) : VolIdxProd M δ u u' F0 what₂ := by
  intro hA hT hR γ w F' L U hE hN
  have hH : HypE M δ u u' F0 what₂ γ w F' L U := ⟨hA, hT, hR, hP, hE, hN⟩
  obtain ⟨hle, hidx, hne⟩ := h1 γ w F' L U hH
  have hne' : (PairVal.stabAut D u u' F0 what₂ γ F' L).relIndex (C (ZhatL (lf D F0) F') L) ≠ 0 := by
    rw [hidx]; exact hne
  have hco := Formalism.L2.SG.Pf.IndexCocycleOrbits.idxCocycle (PairVal.GLR D) (PairVal.stabInt D u u' δ M w)
    (PairVal.stabAut D u u' F0 what₂ γ F' L) (C (ZhatL (lf D F0) F') L) hle hne'
  have hv : PairVal.volIdx D u u' F0 what₂ δ M γ w F' L =
      IdxRatio (PairVal.stabInt D u u' δ M w) (PairVal.stabAut D u u' F0 what₂ γ F' L) := by rfl
  rw [hv, hco, hidx, h2 γ w F' L U hH]

end Formalism.L2.SG.Pf.ZsVolCut

end
end

