module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealPhaseFrames
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeftInverseThreeBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.TermStableHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealPointRepresentatives
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Matrix

namespace Formalism.L2.SG.RealObj.RealPointRepresentatives

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames Formalism.L2.SG.RealObj.FormRegularity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem exists_ptRep (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1))
    (L U : Formalism.L2.SG.PairVal.MatR D) (hLo : IsLoUni L) (hUp : IsUpUni U)
    (hZ : ∀ v, ZhatO (ZX X u u' 1 γ v) = (L * ptMat w * U).map (fun x => X.B.I.φ v (X.ιE.symm x))) :
    ∃ γw, IsPtRep X u u' w γw := by
  let ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ := fun v => (X.B.I.φ v).comp X.ιE.symm.toRingHom
  let P : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v => (L.map (ψ v)).map star
  let P' : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
    fun v => (sgn D.R.rS * U.map (ψ v) * sgn D.R.rS)ᵀ
  have hzz : ∀ (w' : D.what₂.Word) v, hJ (X.B.I.ε v) (rv X.B.I v (X.zR w')) (rv X.B.I v (X.zR w')) ≠ 0 := by
    intro w' v
    rw [(HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.1]
    exact neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.2)
  have hs : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v),
      InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s) ∧
      ∀ a, uMat s *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) a =
        ∑ c, P v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) c := fun v =>
    ThreeBlockFrameInverses.NRealize_holds X.B.I.n D.R.rS (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.1
      (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.2.1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.2.2.2.1 (hzz u v) (P v)
      (isLoUni_star (isLoUni_map _ hLo))
  have hs' : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v),
      InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat s) ∧
      ∀ a, uMat s *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) a =
        ∑ c, P' v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) c := fun v =>
    ThreeBlockFrameInverses.NRealize_holds X.B.I.n D.R.rS (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u')) (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.1
      (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.2.1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.2.2.2.1 (hzz u' v) (P' v)
      (isLoUni_sgnT (isUpUni_map _ hUp))
  choose s hsN hsP using hs
  choose s' hs'N hs'P using hs'
  have hsN' : s ∈ X.NinfU u := fun v => hsN v
  have hs'N' : s' ∈ X.NinfU u' := fun v => hs'N v
  have hsS : s ∈ X.SinfU u := fun v => (hsN v).1
  have hs'S : s' ∈ X.SinfU u' := fun v => (hs'N v).1

  have hPt : IsPtRep X u u' w (s * γ * s'⁻¹) := by
    intro v
    have hg : s⁻¹ * (s * γ * s'⁻¹) * s' = γ := by group
    have h4 := HermitianSumRootCoordinateFrames.ZhatNAct_holds _ _ (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
      (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (s v)) (uMat (s⁻¹ v)) (uMat (s' v))
      (uMat ((s * γ * s'⁻¹) v)) (P v) (P' v) (InfCut.uMat_inv_mul' (s v)) (hJ_map _ (s v).2) (hsP v) (hs'P v)
    have hγv : uMat (s⁻¹ v) * uMat ((s * γ * s'⁻¹) v) * uMat (s' v) = uMat (γ v) := by
      calc uMat (s⁻¹ v) * uMat ((s * γ * s'⁻¹) v) * uMat (s' v)
          = uMat ((s⁻¹ * (s * γ * s'⁻¹) * s') v) := by
            simp only [uMat, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]
        _ = uMat (γ v) := by rw [hg]
    rw [hγv, ← zx_eq, ← zx_eq] at h4
    have h5 : ZhatO (ZX X u u' 1 γ v) = (L * ptMat w * U).map (ψ v) := hZ v
    rw [Matrix.map_mul, Matrix.map_mul, zhatO_eq, h4] at h5
    have hPs : (P v).map star = L.map (ψ v) := by
      ext i j
      simp only [P, Matrix.map_apply, star_star]
    have hPt' : (P' v)ᵀ = sgn D.R.rS * U.map (ψ v) * sgn D.R.rS := Matrix.transpose_transpose _
    rw [hPs, hPt'] at h5
    have h6 : L.map (ψ v) * ZhatO (ZX X u u' 1 (s * γ * s'⁻¹) v) * U.map (ψ v) =
        L.map (ψ v) * ptC X v w * U.map (ψ v) := by
      refine Eq.trans ?_ h5
      rw [zhatO_eq]
      simp only [Matrix.mul_assoc, sgn_sq, Matrix.mul_one]
    exact cancel (by rw [det_lo (isLoUni_map _ hLo)]; exact one_ne_zero)
      (by rw [det_up (isUpUni_map _ hUp)]; exact one_ne_zero) h6
  exact ⟨_, hPt⟩

end Formalism.L2.SG.RealObj.RealPointRepresentatives
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabN
section
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

section StabNSec

open Matrix
open scoped TensorProduct

def StabLatC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2 →
      Formalism.HermitianLatticesTheory.gmap σ ((Y.cs u').lamOf ρ') = (Y.cs u').lamOf ρ'

def StabFlagC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      ∀ j, ∀ x ∈ Xflag (lf D (X.Fu u')) (j + 1), σ x - x ∈ Xflag (lf D (X.Fu u')) j

def StabOrthC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2 →
      ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), σ x - x ∈ Xsp (lf D (X.Fu u'))

theorem stabNC_of (hL : StabLatC) (hF : StabFlagC) (hO : StabOrthC) : StabNC := by
  intro D X Y u u' hH ρ' s σ hs hσ hS hk
  exact ⟨⟨hσ, hL D X Y u u' hH ρ' s σ hs hσ hS hk⟩, hF D X Y u u' hH s σ hs hσ hS,
    hO D X Y u u' hH ρ' s σ hs hσ hS hk⟩

theorem lattice_stabilizer_holds : StabLatC := by
  intro D X Y u u' hH ρ' s σ hs hσ hS hk
  obtain ⟨M, -, -, h2, h3⟩ := hs
  set a : X.B.I.Gf := ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u' with ha
  have hkK : a⁻¹ * s.2 * a ∈ X.B.I.Kset := hH.1.2.1 _ hk
  have hfm : ∀ x y : X.B.I.Gf, X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := by
    intro x y; simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : ∀ y : (VS D).V, σ y ∈ (Y.cs u').lamOf ρ' ↔ y ∈ (Y.cs u').lamOf ρ' := by
    intro y
    rw [(Y.cs u').lat_eq, (Y.cs u').lat_eq, h3, ← Formalism.L2.SG.Pf.Level.incl_mulVec X, ← h2]
    have e : X.B.I.fmat a⁻¹ *ᵥ (X.B.I.fmat s.2 *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd y)) =
        X.B.I.fmat (a⁻¹ * s.2 * a) *ᵥ (X.B.I.fmat a⁻¹ *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd y)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hfm, ← hfm]
      congr 2
      group
    rw [e]
    exact (hkK _).symm
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).2 hx
  · intro hy
    refine Submodule.mem_map.2 ⟨σ.symm y, (key _).1 (by simpa using hy), by simp⟩

def StabOrthDescC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (s : X.B.I.GA)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s.2 ∈ X.NfinU u' →
      ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), σ x - x ∈ Xsp (lf D (X.Fu u'))

theorem stab_nfin (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK)
    {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u' : D.what₂.Word) (hKL : X.LevelSubgroupNormalized)
    (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (hS : s ∈ Srat X u')
    (hk : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2) :
    s.2 ∈ X.NfinU u' := by
  have hK := Y.hK
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' s hS
  obtain ⟨ν, η, rfl, hνr, hν1, hν2, hη⟩ := Formalism.L2.SG.Pf.ratLevi_holds X u' _ (Subgroup.mem_inf.1 hS).1 h1 h2
  have hηp := Subgroup.mem_prod.1 (Subgroup.mem_inf.1 hη).2
  set hh : Hfin X u' := (Y.cs u').h ρ' with hhh
  have hn' : (hh : X.B.I.Gf)⁻¹ * ν.2 * hh ∈ X.NfinU u' := by
    have := (Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X u' hh⁻¹ ν.2 hν2).1
    simpa using this
  let g2 : Hfin X u' := hh⁻¹ * ⟨η.2, hηp.2⟩ * hh
  have hLD := Formalism.L2.SG.PoincareInHH.Cut.levelDec_of X u' hK (Formalism.L2.SG.Pf.ksetSplit_holds X u')
    (Formalism.L2.SG.Pf.unipotent_in_level X u') _ hn' g2 (by
      have e : (X.xu u')⁻¹ * ((hh : X.B.I.Gf)⁻¹ * ν.2 * hh * (g2 : X.B.I.Gf)) * X.xu u' =
          ((hh : X.B.I.Gf) * X.xu u')⁻¹ * (ν * η).2 * ((hh : X.B.I.Gf) * X.xu u') := by
        simp only [g2, Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul]
        group
      rw [e]; exact hk)
  have hη1 : (⟨η, hη⟩ : Gam X u') = 1 := by
    refine hN D X Y u' hKL hh ⟨η, hη⟩ ?_
    show (X.xu u')⁻¹ * ((hh⁻¹ * Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u' ⟨η, hη⟩ * hh : Hfin X u') : X.B.I.Gf) *
      X.xu u' ∈ X.K2
    exact hLD.1
  have hη1' : η = 1 := congrArg Subtype.val hη1
  rw [hη1', mul_one]
  exact hν2

theorem stabOrthC_of (hD : StabOrthDescC)
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabOrthC := by
  intro D X Y u u' hH ρ' s σ hs hσ hS hk
  exact hD D X u' s σ hs hσ (stab_nfin hN Y u' hH.1 ρ' s hS hk)

theorem incl_descent (I : Formalism.MainNotions.S.AutInst) [Nontrivial (Af I.F)] (S : Set (Fin I.n → I.E)) (w : Fin I.n → I.E)
    (hw : Formalism.L2.SG.HidaSetting.incl I w ∈
      Submodule.span (I.E ⊗[I.F] Af I.F) (Formalism.L2.SG.HidaSetting.incl I '' S)) :
    w ∈ Submodule.span I.E S := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap I.E (I.E ⊗[I.F] Af I.F)) (by
    rw [LinearMap.ker_eq_bot]
    intro a b h
    exact Algebra.TensorProduct.includeLeft_injective (S := I.F) (algebraMap I.F (Af I.F)).injective h)
  have hgc : ∀ c : I.E, g (Formalism.UG.inclE (F := I.F) (Af I.F) c) = c := fun c => LinearMap.congr_fun hg c
  have hgm : ∀ (r : I.E ⊗[I.F] Af I.F) (c : I.E), g (r * Formalism.UG.inclE (F := I.F) (Af I.F) c) = c * g r := by
    intro r c
    have e : r * Formalism.UG.inclE (F := I.F) (Af I.F) c = c • r := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [e, map_smul, smul_eq_mul]
  obtain ⟨m, f, t, hsum⟩ := Submodule.mem_span_set'.1 hw
  have ht : ∀ i, ∃ s ∈ S, Formalism.L2.SG.HidaSetting.incl I s = (t i : Formalism.L2.SG.HidaSetting.VA I) := fun i => (t i).2
  choose s hs hst using ht
  have e : w = ∑ i, g (f i) • s i := by
    funext k
    have hk := congrFun hsum k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hst] at hk ⊢
    have hk2 := congrArg g hk
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.L2.SG.HidaSetting.incl, map_sum, hgm, hgc] at hk2
    rw [← hk2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))

theorem crd_inj' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {y y' : (VS D).V} (h : X.crd y = X.crd y') : y = y' := by
  apply X.bas.repr.injective
  ext i
  have := congrFun h i
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf] at this
  exact X.ιE.symm.injective this

theorem crd_descent {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : (VS D).V)
    (hv : X.crd v ∈ Submodule.span X.B.I.E (Set.range X.eR)) :
    v ∈ Submodule.span D.host.E (Set.range X.eX) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun X.B.I.E).1 hv
  have e : v = ∑ a, X.ιE (c a) • X.eX a := by
    apply crd_inj' X
    rw [← hc]
    change _ = Formalism.L2.SG.Pf.Vanish2.crdHom X (∑ a, X.ιE (c a) • X.eX a)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ = X.crd (X.ιE (c a) • X.eX a)
    rw [Formalism.L2.SG.Pf.crd_smul X, RingEquiv.symm_apply_apply]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem orthogonal_stabilizer_descent : StabOrthDescC := by
  intro D X u' s σ hs hσ hn x hx
  obtain ⟨M, -, -, h2, h3⟩ := hs
  have : Nontrivial (Af X.B.I.F) := Formalism.L2.SG.Pf.Level.af_ntriv X.B.I.F
  have hx0 : ∀ a, Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a)) (Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd x)) = 0 := by
    intro a
    rw [Formalism.L2.SG.PoincareInHH.Cut.hA_incl X]
    have hmem : X.eX a ∈ Xsp (lf D (X.Fu u')) := by
      show X.eX a ∈ Submodule.span D.host.E (Set.range (X.Fu u').e)
      rw [X.Fu_e]
      exact Submodule.subset_span ⟨a, rfl⟩
    have h0 : (VS D).hT (X.eX a) x = 0 := (mem_orth_iff _ _).1 hx _ hmem
    have h1 : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.crd x) = 0 := by
      apply X.ιE.injective
      rw [map_zero, show X.eR a = X.crd (X.eX a) from rfl, Formalism.L2.SG.PoincareInHH.Cut.hform_crd X]
      exact h0
    rw [h1, map_zero]
  have hmem := hn.2.2 _ hx0
  have e : (X.B.I.fmat s.2 - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd x) =
      Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd (σ x - x)) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h2, Formalism.L2.SG.Pf.Level.incl_mulVec X, ← h3,
      Formalism.L2.SG.Pf.Vanish2.crd_sub' X]
    funext i
    simp [Formalism.L2.SG.HidaSetting.incl]
  rw [e] at hmem
  have hd := incl_descent X.B.I (Set.range X.eR) _ (by rw [← Set.range_comp]; exact hmem)
  show σ x - x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e)
  rw [X.Fu_e]
  exact crd_descent X _ hd

theorem orthogonal_stabilizer_of_neat
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabOrthC :=
  stabOrthC_of orthogonal_stabilizer_descent hN

end StabNSec

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfTermCar
section
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
open Formalism.L2.SG.HidaSetting Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

section TermCarSec

def RatIsoC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (γ : X.B.I.GA), γ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I →
    ∃ σ : (VS D).V ≃ₗ[D.host.E] (VS D).V, RatLink X γ σ ∧ σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT

def ModGOfAtC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g1 : X.B.I.Gf) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    (∀ y, y ∈ Λ ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf) →
    ∀ v, InAt X.B.I X.B.g X.B.g (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v)) → ModG (VS D) Λ (gS D) v

def FrameCongC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (ρ : (Y.cs u).Cl) (ρ' : (Y.cs u').Cl) (γ : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    RatLink X γ σ → kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) γ ∈ X.K2 →
    ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧
      ∀ b, InAt X.B.I X.B.g X.B.g (X.B.I.fmat (aC (Y.cs u) ρ)⁻¹ *ᵥ
        incl X.B.I (X.crd (σ (frame (lf D (X.Fu u')) b) - frameAct (frame (lf D (X.Fu u))) ξ b)))

section Tr2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
  {γ : S.V ≃ₗ[E] S.V} {T' : E} {x F₂ : LFlag S r T'}

theorem transport_x_lattice (Λ₂ Λ : Submodule (𝓞 E) S.V) (hΛ : PI.TCS.Tr γ Λ₂ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) :
    PI.TCS.Tr γ (XLam Λ₂ F₂) (XLam Λ x) :=
  PI.TCS.Tr.inf hΛ (PI.TCS.trE_Xsp he).toO

theorem transport_lattice_sub (Λ₂ Λ : Submodule (𝓞 E) S.V) (hΛ : PI.TCS.Tr γ Λ₂ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k))
    (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) : PI.TCS.Tr γ (Lsub Λ₂ F₂) (Lsub Λ x) :=
  PI.TCS.Tr.inf (PI.TCS.Tr.sup (PI.TCS.Tr.inf hΛ ((PI.TCS.trE_Xsp he).perp hiso).toO) (PI.TCS.trE_Xsp he).toO)
    ((PI.TCS.trE_Xsp he).perp hiso).toO

theorem fixed_conv_transport (Λ₂ Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hΛ : PI.TCS.Tr γ Λ₂ Λ)
    (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) (hz : F₂.fl.z = γ x.fl.z) (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b)
    (hx : IsFixedConv Λ g x) : IsFixedConv Λ₂ g F₂ := by
  refine ⟨fun P => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc0, hc1, heq⟩ := hx.1 P
    refine ⟨c, hc0, hc1, ?_⟩
    have := P.isPrime
    refine PI.TCS.Tr.eq (transport_x_lattice Λ₂ Λ hΛ he).localization₂ (PI.TCS.Tr.span ?_).localization₂ heq
    rw [← Set.range_comp]
    congr 1
    funext a
    simp [he a, map_smul]
  · apply hx.2 c
    have := ((transport_lattice_sub Λ₂ Λ hΛ he hiso) _).mp hc
    simpa [hz, map_smul] using this

end Tr2

section Main

variable {D : D7}

theorem frame_ok_transport {T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {x F₂ : LFlag (D.sp.Y 0) D.R.rS T'} (Λ₂ Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : PI.TCS.Tr γ Λ₂ Λ)
    (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) (hz : F₂.fl.z = γ x.fl.z)
    (hiso : ∀ a b, (VS D).hT (γ a) (γ b) = (VS D).hT a b) (hx : FrameOK D Λ x) : FrameOK D Λ₂ F₂ :=
  ⟨fixed_conv_transport Λ₂ Λ (gS D) hΛ he hz hiso hx.1, PI.TCS.Tr.eq (transport_x_lattice Λ₂ Λ hΛ he) (PI.TCS.tr_XS D he) hx.2⟩

theorem pd_of_tr {T : D.host.E} (u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hTr : PI.TCS.Tr σ Λ Λ')
    (hL : IsLift Λ' F') (hOK : FrameOK D Λ' F')
    (hA : ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧
      ∀ b, ModG (VS D) Λ (gS D) (σ (frame F' b) - frameAct (frame F) ξ b)) :
    TermDef.PD D Λ F u' (mapLF σ F') := by
  have hmap : mapLF σ F' = ⟨mapFlag σ hiso F'.fl, σ F'.zt⟩ := by
    unfold mapLF; rw [dite_eq_left hiso]
  have hisoT : ∀ a b, (VS D).hT (σ a) (σ b) = (VS D).hT a b := fun a b => hiso a b
  have hfr : ∀ b, frame (mapLF σ F') b = σ (frame F' b) := Formalism.L2.SG.NormCut.frame_mapLF hiso F'
  change IsLift Λ (mapLF σ F') ∧ IsAdmissible Λ (gS D) F (mapLF σ F') ∧ FrameOK D Λ (mapLF σ F')
  refine ⟨?_, ?_, ?_⟩
  · rw [hmap]
    refine ⟨(hTr _).mpr ?_, ?_⟩
    · show σ.symm (σ F'.fl.z) ∈ Λ'
      simpa using hL.1
    · show σ F'.zt = σ F'.fl.z
      rw [hL.2]
  · obtain ⟨ξ, hl, hd, hc⟩ := hA
    refine ⟨ξ, hl, hd, fun b => ?_⟩
    rw [hfr b]
    exact hc b
  · rw [hmap]
    exact frame_ok_transport Λ Λ' hTr (fun j => rfl) rfl hisoT hOK

theorem termCarC_of (h1 : RatIsoC) (h2 : ModGOfAtC) (h3 : FrameCongC) : TermCarC := by
  intro D X Y u u' hH ρ ρ' γ hγ
  obtain ⟨hγr, hk⟩ := hγ
  obtain ⟨σ, hRL, hiso⟩ := h1 D X γ hγr
  have hK := Y.hK
  set k := kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) γ with hkdef
  have hkK : k ∈ X.B.I.Kset := hk.1
  have hkK' : k⁻¹ ∈ X.B.I.Kset := (hK.2.2.1 k hk).1

  have hTr : PI.TCS.Tr σ ((Y.cs u).lamOf ρ) ((Y.cs u').lamOf ρ') := by
    intro v
    rw [(Y.cs u).lat_eq ρ v, (Y.cs u').lat_eq ρ' (σ.symm v), ← LatDictK.ratLink_incl_inv X hRL v,
      mulVec_mulVec, ← LatDictK.fmatK_mul]
    have e : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * γ.2⁻¹ =
        k⁻¹ * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ := by
      rw [hkdef]; unfold kOf; group
    rw [e, LatDictK.fmatK_mul, ← mulVec_mulVec]
    constructor
    · intro hw
      exact unitaryCongruence.K_mv X.B.I hkK' hw
    · intro hw
      have := unitaryCongruence.K_mv X.B.I hkK hw
      rwa [mulVec_mulVec, ← LatDictK.fmatK_mul, mul_inv_cancel, show X.B.I.fmat 1 = 1 by
        simp [AutInst.fmat], one_mulVec] at this
  have hgm : Formalism.HermitianLatticesTheory.gmap σ ((Y.cs u').lamOf ρ') = (Y.cs u).lamOf ρ := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hTr _).mpr (by simpa using hy)
    · intro hv
      exact ⟨σ.symm v, (hTr v).mp hv, by simp⟩

  obtain ⟨-, ⟨-, -, hLift, hFC⟩, hXL⟩ := (Y.rowsOK u').1 _ ((Y.cs u').lam_mem ρ')
  refine ⟨⟨(γ, σ), hRL, hiso, hgm, ?_⟩, rfl⟩
  refine pd_of_tr u' _ _ (lf D (X.Fu u)) (lf D (X.Fu u')) σ hiso hTr hLift ⟨hFC, hXL⟩ ?_
  obtain ⟨ξ, hl, hd, hc⟩ := h3 D X Y u u' ρ ρ' γ σ hRL hk
  exact ⟨ξ, hl, hd, fun b => h2 D X (aC (Y.cs u) ρ) _ ((Y.cs u).lat_eq ρ) _ (hc b)⟩

end Main

end TermCarSec

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfSteps
section
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LeviFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word),
    ∃ F : Submodule (𝓞 D.host.E) (VS D).V → Submodule (𝓞 D.host.E) (VS D).V →
        Finset ((VS D).V ≃ₗ[D.host.E] (VS D).V),
      ∀ Λ₁ ∈ Y.what₂ u', ∀ Λ₂ ∈ Y.what₂ u', ∀ (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : X.B.I.GA),
        RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' → Formalism.HermitianLatticesTheory.gmap σ Λ₂ = Λ₁ →
          ∃ f ∈ F Λ₁ Λ₂, f⁻¹ * σ ∈ NLam Λ₂ (lf D (X.Fu u'))

theorem tsum_comp_le_of_fibre {ι κ β : Type*} (φ : ι → κ) (g : κ → ℝ≥0∞) (M : ℕ)
    (hfib : ∀ k, ∃ (S : Finset β) (e : ι → β), S.card ≤ M ∧
      ∀ i, φ i = k → e i ∈ S ∧ ∀ j, φ j = k → e i = e j → i = j) :
    ∑' i, g (φ i) ≤ (M : ℝ≥0∞) * ∑' k, g k := by
  rw [← (Equiv.sigmaFiberEquiv φ).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  obtain ⟨S, e, hS, he⟩ := hfib k
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hc : s.card ≤ M := by
    refine le_trans ?_ hS
    refine Finset.card_le_card_of_injOn (fun i => e (i : ι)) (fun i _ => (he i.1 i.2).1) ?_
    intro i _ j _ hij
    exact Subtype.ext ((he i.1 i.2).2 j.1 j.2 hij)
  calc ∑ i ∈ s, g (φ ((Equiv.sigmaFiberEquiv φ) ⟨k, i⟩))
      = ∑ i ∈ s, g k := Finset.sum_congr rfl fun i _ => by
          show g (φ i.1) = g k
          rw [i.2]
    _ = (s.card : ℝ≥0∞) * g k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ≥0∞) * g k := by gcongr

end Formalism.L2.SG.Pf.SlabCount
end
end

