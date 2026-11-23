module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNHomPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.VanishNConj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.CharacterFixedPoints
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.CharacterOnFixedPoints

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem chiN_of_fix {κ : X.B.I.Gf} (h : ∀ a, (X.B.I.fmat κ - 1) *ᵥ nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g) :
    chiN X κ = 1 := by
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (Formalism.L2.SG.Pf.ChiNHomPf.gB_ne_zero X) ?_
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  have hf0 : X.f0 a ∈ X.B.I.Lf := (X.vectorsInLattice.1 a).2
  have e : X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a = nxt X.e0 X.z0 a + (X.B.I.fmat κ - 1) *ᵥ nxt X.e0 X.z0 a := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [e, hA_add_right]
  exact Z_add X.B.I X.B.g
    (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (Formalism.L2.SG.Pf.ChiNHomPf.hfe X) (Formalism.L2.SG.Pf.ChiNHomPf.hfz X) a)
    (mL_Qs X.B.I X.B.g hf0 (h a))

end Formalism.L2.SG.Pf.CharacterOnFixedPoints

namespace Formalism.L2.SG.NormCut

section KeyGen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

theorem key_gen (hTF : FrameTie X u u' F0 F0') (hM : Formalism.L2.SG.NormCut.ModGAt X)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ what₂) (x : X.B.I.GA) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hRL : RatLink X x γ) (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (hξm : ∀ c, ModG (VS D) Λ (gS D) (γ (frame (lf D F0') c) - frameAct (frame (lf D F0)) ξ c))
    (hKp : kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) x ∈ X.B.I.Kset) :
    ∀ c, X.B.I.fmat (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) x) *ᵥ
        (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) -
      ∑ a, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) •
        (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a) ∈ mL X.B.I X.B.g := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  set g1 : X.B.I.Gf := (cs.h (cs.base Λ) : X.B.I.Gf) * X.xu u with hg1
  set g2 : X.B.I.Gf := (cs'.h (cs'.base Λ') : X.B.I.Gf) * X.xu u' with hg2
  have hκK := hKp
  set κ := kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) x with hκ
  have hκ' : κ = g1⁻¹ * x.2 * g2 := rfl
  have hb : cs.lamOf (cs.base Λ) = Λ := cs.base_lam _ hΛ
  have hlat : ∀ y, y ∈ Λ ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := fun y => by
    rw [← hb]; exact cs.lat_eq _ y

  set s : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
    fun a c => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) with hs
  have hsI : ∀ a c, s a c ∈ IntAf X.B.I.F X.B.I.E := fun a c => inclE_int X (ξ a c)

  set Y : Fin (D.R.rS + 1) → VA X.B.I := fun a => X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (F0.fvec a)) with hY
  set Y' : Fin (D.R.rS + 1) → VA X.B.I := fun c => X.B.I.fmat g2⁻¹ *ᵥ incl X.B.I (X.crd (F0'.fvec c)) with hY'
  have key2 : ∀ c, InAt X.B.I X.B.g X.B.g (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a) := by
    intro c
    have h1 := hM g1 Λ hlat _ (hξm c)
    have e : X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (γ (frame (lf D F0') c) -
        frameAct (frame (lf D F0)) ξ c)) = X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a := by
      simp only [frameAct, crd_sub', crd_sum', crd_smul', incl_sub', incl_sum', incl_smul', Matrix.mulVec_sub,
        mulVec_fsum, Matrix.mulVec_smul, ratLink_incl X hRL]
      congr 1
      simp only [hY', Matrix.mulVec_mulVec, hκ', ← fmat_mul]
      congr 2
      group
    rw [e] at h1
    exact h1

  have fixE : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w) (a : Fin D.R.rS),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) :=
    fun w h a => fixes_inv X (fixes_mul X (h.2 _ (Or.inl (Or.inl ⟨a, rfl⟩))) ((X.xu_fix w a).1))
  have fixZ : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) =
        X.B.I.fmat (X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) := by
    intro w h
    have hz : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) = incl X.B.I (X.crd (X.zu w)) :=
      fixes_inv X (h.2 _ (Or.inr rfl))
    rw [_root_.mul_inv_rev, fmat_mul, ← Matrix.mulVec_mulVec, hz]
  set e0v : Fin (D.R.rS + 1) → VA X.B.I := Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 with he0v
  have hYa : ∀ a, InAt X.B.I X.B.g X.B.g (e0v a - Y a) := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, hY, Fin.snoc_last, FlagG.fvec, hTF.2.1, hg1, fixZ]
      have := InAt_neg X (X.xu_z u)
      rwa [neg_sub] at this
    · simp only [he0v, hY, Fin.snoc_castSucc, FlagG.fvec, hTF.1 i, hg1, fixE]
      exact (X.basisApprox i).1
  have hY'a : ∀ c, InAt X.B.I X.B.g X.B.g (e0v c - Y' c) := by
    intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [he0v, hY', Fin.snoc_last, FlagG.fvec, hTF.2.2.2, hg2, fixZ]
      have := InAt_neg X (X.xu_z u')
      rwa [neg_sub] at this
    · simp only [he0v, hY', Fin.snoc_castSucc, FlagG.fvec, hTF.2.2.1 i, hg2, fixE]
      exact (X.basisApprox i).1
  have he0vL : ∀ a, e0v a ∈ X.B.I.Lf := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, Fin.snoc_last]; exact hZ0
    · simp only [he0v, Fin.snoc_castSucc]; exact hE0 i
  have key4 : ∀ c, X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a ∈ mL X.B.I X.B.g := by
    intro c
    have hsm : ∀ (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), z ∈ IntAf X.B.I.F X.B.I.E → w ∈ X.B.I.Lf →
        z • w ∈ X.B.I.Lf := fun z w hz hw => by
      have : z • w = (⟨z, hz⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ hw
    refine mem_mL_of_InAt X (sub_mem (K_mv X.B.I hκK (he0vL c)) (sum_mem fun a _ => hsm _ _ (hsI a c) (he0vL a))) ?_
    have e : X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a =
        (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a) + X.B.I.fmat κ *ᵥ (e0v c - Y' c) -
          ∑ a, s a c • (e0v a - Y a) := by
      simp only [Matrix.mulVec_sub, smul_sub, Finset.sum_sub_distrib]; abel
    rw [e]
    exact InAt_sub X (InAt_add X (key2 c) (InAt_K X hκK (hY'a c)))
      (InAt_sum X _ _ fun a _ => InAt_smul X (hsI a c) (hYa a))
  exact key4

end KeyGen

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
section
noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.TermOp.Vanish

theorem nilradical_conj_level' : NilradicalConjLevel :=
  nilradical_conj_level_of_mem fun _ X u => unipotent_in_level X u

theorem chiTrivialC_outright : ChiTrivialC := chiTrivialC_of_nconj nilradical_conj_level'

theorem lemmaVC_of_rest (hA : AvgCore) (h3 : RCocompactC) (h4 : NonRelCharC) : Formalism.L2.SG.Full.LemmaVC :=
  lemmaVC_of_nconj hA nilradical_conj_level' h3 h4

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormRegularity
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.FormRegularity

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames
  Formalism.MainNotions.S.Lat

section Mat

variable {r : ℕ}

def sgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.1)

theorem sgn_sq : sgn r * sgn r = 1 := by
  rw [sgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem zhatO_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ZhatO Z = Z * sgn r := by
  ext a b
  rw [ZhatO, sgn, Matrix.mul_diagonal, mul_comm]

theorem isLoUni_map {K : Type*} [Field K] (ψ : K →+* ℂ) {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : IsLoUni L) : IsLoUni (L.map ψ) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.map_apply, (h i j).1 hij, map_zero]
  · rw [Matrix.map_apply, (h i j).2 hij, map_one]

theorem isLoUni_star {L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsLoUni L) : IsLoUni (L.map star) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.map_apply, (h i j).1 hij, star_zero]
  · rw [Matrix.map_apply, (h i j).2 hij, star_one]

theorem isLoUni_sgnT {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsUpUni U) :
    IsLoUni (sgn r * U * sgn r)ᵀ := by
  intro i j
  simp only [Matrix.transpose_apply, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [(h j i).1 hij]; ring
  · subst hij
    rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp

theorem det_lo {K : Type*} [Field K] {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => (h i j).1 (OrderDual.toDual_lt_toDual.1 hij))]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem det_up {K : Type*} [Field K] {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem isUpUni_map {K : Type*} [Field K] (ψ : K →+* ℂ) {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : IsUpUni U) : IsUpUni (U.map ψ) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.map_apply, (h i j).1 hij, map_zero]
  · rw [Matrix.map_apply, (h i j).2 hij, map_one]

theorem cancel {L A B U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hL : L.det ≠ 0) (hU : U.det ≠ 0)
    (h : L * A * U = L * B * U) : A = B :=
  ((Matrix.isUnit_iff_isUnit_det L).2 (Ne.isUnit hL)).mul_left_cancel
    (((Matrix.isUnit_iff_isUnit_det U).2 (Ne.isUnit hU)).mul_right_cancel h)

theorem sgLo_eq {K : Type} [Field K] (L : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.L2.SG.PairVal.sgLo L = ∑ a : Fin r, L a.succ a.castSucc := by
  unfold Formalism.L2.SG.PairVal.sgLo
  rw [Fin.sum_univ_castSucc, dite_eq_right (by simp), add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_left (by simp)]
  rfl

theorem sgUp_eq {K : Type} [Field K] (U : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.L2.SG.PairVal.sgUp U = ∑ a : Fin r, U a.castSucc a.succ := by
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc, dite_eq_right (by simp), add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_left (by simp)]
  rfl

theorem sgn_adj (a : Fin r) : (-1 : ℂ) ^ (r - a.castSucc.1) * (-1 : ℂ) ^ (r - a.succ.1) = -1 := by
  have h : r - a.castSucc.1 = (r - a.succ.1) + 1 := by
    simp only [Fin.coe_castSucc, Fin.val_succ]; omega
  rw [h, ← pow_add]
  exact Odd.neg_one_pow ⟨r - a.succ.1, by ring⟩

end Mat

theorem psiInf_neg {E : Type} [Field E] [NumberField E] (g : ℕ) (x : E) :
    Formalism.L2.SG.PairVal.psiInf g (-x) = (Formalism.L2.SG.PairVal.psiInf g x)⁻¹ := by
  unfold Formalism.L2.SG.PairVal.psiInf
  rw [← Complex.exp_neg, map_neg]
  congr 1
  push_cast
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem zx_eq (u u' : D.what₂.Word) (δ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    ZX X u u' 1 δ v = Zhat (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
      (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (δ v)) := by
  simp only [ZX, frm, FlagExtensionRegularity.famSc_one]

theorem psi_of_frame (u : D.what₂.Word) (s : X.B.I.Ginf)
    (P : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ)
    (hP : ∀ v a, uMat (s v) *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) a =
       ∑ c, P v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) c)
    (y : D.host.E) (hy : ∀ v, ∑ a : Fin D.R.rS, (P v a.succ a.castSucc + star (P v a.succ a.castSucc)) =
       X.B.I.φ v (X.ιE.symm y) + star (X.B.I.φ v (X.ιE.symm y))) :
    X.psiInfU u s = Formalism.L2.SG.PairVal.psiInf X.B.g y := by
  have hfr := fun v => HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v
  have hrc : ∀ v a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (uMat (s v)) a = P v a.succ a.castSucc := fun v a =>
    HermitianSumRootCoordinateFrames.RootCoordFrame_holds _ _ _ _ _ _ (hfr v).2.2.2.1 (fun a => ((hfr v).2.2.2.2.1 a).2) _ _ (hP v) a
  unfold HidaSetting.psiInfU psiInf psiR
  simp only [hrc, hy]
  rw [PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g (X.ιE.symm y), RingEquiv.apply_symm_apply]

end Main

end Formalism.L2.SG.RealObj.FormRegularity
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjClosed
section
open Formalism.BasicNotions Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf

theorem realObj_inNuX {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ) : InNuX X u u' sc := by
  have hC : 0 ≤ DisintegrationConstant X u u' sc := by
    unfold DisintegrationConstant
    split_ifs with h
    · exact h.choose_spec.1.le
    · exact le_rfl
  have hO : ∀ c, 0 ≤ hilbertSchmidtSqGram X u u' sc c := fun c => by
    unfold hilbertSchmidtSqGram hs2
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : Measurable (fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (InfCut.wt_cont X u u').measurable)
  unfold InNuX intOOe intCe nuM
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine MeasureTheory.lintegral_congr fun c => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul' (hO c), ← ENNReal.ofReal_mul hC, mul_assoc]

end Formalism.L2.SG.Pf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLChi
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ChiNBiAll : Prop := ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), ChiNBi X

namespace ChiLeft

theorem kBB_mem {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u')
    (p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : kBB Y u u' Λ Λ' p.1.1 ∈ X.B.I.Kset := by
  obtain ⟨hRL, -, hmap, -⟩ := p.2
  have hRL' : RatLink X p.1.1 p.1.2 := hRL
  have hmap' : Formalism.HermitianLatticesTheory.gmap p.1.2 Λ' = Λ := hmap
  have hb0 := (Y.cs u).base_lam Λ hΛ
  have hb1 := (Y.cs u').base_lam Λ' hΛ'
  have key : (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) ∈ X.B.I.Kset := by
    refine LatDictK.dict_K X _ _ {y | y ∈ Λ} (fun y => ?_) (fun y => ?_)
    · show y ∈ Λ ↔ _
      conv_lhs => rw [← hb0]
      exact (Y.cs u).lat_eq _ y
    · show y ∈ Λ ↔ _
      have e1 : y ∈ Λ ↔ p.1.2.symm y ∈ Λ' := by
        constructor
        · intro hy
          rw [← hmap'] at hy
          obtain ⟨z, hz, hzy⟩ := hy
          have : p.1.2.symm y = z := by rw [← hzy]; simp
          rw [this]; exact hz
        · intro h
          rw [← hmap']
          exact ⟨p.1.2.symm y, h, by simp⟩
      have hlat : ∀ w, w ∈ Λ' ↔ X.B.I.fmat (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ *ᵥ
          incl X.B.I (X.crd w) ∈ X.B.I.Lf := fun w => by
        have := (Y.cs u').lat_eq ((Y.cs u').base Λ') w
        rw [hb1] at this
        exact this
      rw [e1, hlat, show (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u'))⁻¹ =
          (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ * p.1.1.2⁻¹ from _root_.mul_inv_rev _ _,
        LatDictK.fmatK_mul, ← Matrix.mulVec_mulVec, LatDictK.ratLink_incl_inv X hRL']
  have e : kBB Y u u' Λ Λ' p.1.1 = (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) := by
    simp only [kBB, kOf, mul_assoc]
  rw [e]
  exact key

theorem kB_inv_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {w : D.what₂.Word}
    {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (γ : Gam X w) (hk : kB c Λ γ ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (kB c Λ γ)⁻¹ *ᵥ X.f0 a) (X.f0 a) := by
  have e : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) = (kB c Λ γ)⁻¹ := by
    unfold kB
    push_cast
    group
  have hK : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [e]; exact mem_Kset_inv X hk
  have h := (column_fixed_holds X w (iotaF X w γ * c.h (c.base Λ)) (c.h (c.base Λ)) hK).1
  rw [e] at h
  exact h

theorem one_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (w : D.what₂.Word) (h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (1 : X.B.I.Gf) *ᵥ nxt X.e0 X.z0 a) (nxt X.e0 X.z0 a) := by
  have hK : (((1 : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * (((1 : Hfin X w) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [inv_mul_cancel]; exact h1
  have h := (column_fixed_holds X w 1 1 hK).2
  simpa only [inv_mul_cancel] using h

end ChiLeft

theorem chiNLeft_holds (hB : ChiNBiAll) : ChiNLeft := by
  intro D X Y u u' Λ Λ' hΛ hΛ' γ hk p
  have hκ := ChiLeft.kBB_mem Y u u' hΛ hΛ' p
  have h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    have h := mem_Kset_mul X hk (mem_Kset_inv X hk)
    rwa [mul_inv_cancel] at h
  have h := hB D X (kBB Y u u' Λ Λ' p.1.1) (kB (Y.cs u) Λ γ) 1 hκ hk h1
    (ChiLeft.kB_inv_fix (Y.cs u) Λ γ hk) (ChiLeft.one_fix u h1)
  rwa [mul_one] at h

end Formalism.L2.SG.Pf.SatGramActL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLIota
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem satGramActLIota_kB_good {D : D7} {X : HidaSetting D} {w : D.what₂.Word}
    {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (γ : Gam X w) (hk : kB c Λ γ ∈ X.B.I.Kset) : Good X (kB c Λ γ) := by
  have e : kB c Λ γ = ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w)⁻¹ *
      (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w) := by
    simp only [kB, Subgroup.coe_mul, mul_assoc]
  rw [e] at hk ⊢
  refine colGood X w _ _ hk ?_
  have h2 := K_inv X.B.I hk
  rwa [mul_inv_rev, inv_inv] at h2

theorem levi_kB_mul_kBB_of_good {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (γ : Gam X u) (hk : kB (Y.cs u) Λ γ ∈ X.B.I.Kset)
    (x : X.B.I.GA) (hG : Good X (kBB Y u u' Λ Λ' x)) :
    levi Y.TR (kB (Y.cs u) Λ γ * kBB Y u u' Λ Λ' x) = levi Y.TR (kB (Y.cs u) Λ γ) * levi Y.TR (kBB Y u u' Λ Λ' x) :=
  levi_mul Y.TR (satGramActLIota_kB_good (Y.cs u) Λ γ hk) hG

theorem iotaLeft_holds : IotaLeft := by
  intro D X Y u u' t γ hk
  exact levi_kB_mul_kBB_of_good Y u u' t.lam t.lam' γ hk t.rep.1.1
    (Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') t)

end Formalism.L2.SG.Pf.SatGramActL
end
end

