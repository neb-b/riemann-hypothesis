module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.XflagEqMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.HTSpanLeft
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BigCellDiagIff
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem dl_diagonal {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (h : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE h i) := by
  unfold Dl
  simp only [dif_pos h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective h), Matrix.det_diagonal,
    Function.comp_apply]

theorem dcLoc_eq (r : ℕ) : dcLoc (r := r) = (2 : ℝ≥0∞) ^ (r + 1) • (volume : Measure (Fin (r + 1) → ℂ)) := by
  haveI : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by rw [two_smul]; infer_instance
  unfold dcLoc
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNMul
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.ChiNMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem gB_ne_zero : X.B.g ≠ 0 := by
  rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem hfe : ∀ a b : Fin D.R.rS, a ≠ b → ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (X.e0 b)) := by
  intro a b hab
  rw [hA_symm]
  have := (X.gramIntegral b a).2.2
  rw [if_neg (Ne.symm hab), sub_zero] at this
  exact Z_sig X.B.I X.B.g this

theorem hfz : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) X.z0) := fun a => ((X.formsAtZero).2 a).2

theorem e_step' {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset)
    (hc1 : ∀ a : Fin D.R.rS, (X.B.I.fmat x - 1) *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}))
    (a : Fin D.R.rS) : ∀ v ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1 + 1}),
      (X.B.I.fmat x - 1) *ᵥ v ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}) :=
  pres1 X.B.I hx X.B.g _ _ (by
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b.1 < a.1 + 1 := hb
    exact Mo_mono X.B.I (Set.image_mono (lt_sub (by omega))) (hc1 b)) (mL_Mo X.B.I)

theorem nxt_cong' {y : X.B.I.Gf} (hcy : Formalism.L2.SG.NormCut.NCong X y) (a : Fin D.R.rS) :
    (X.B.I.fmat y - 1) *ᵥ nxt X.e0 X.z0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1 + 1}) := by
  unfold nxt
  split_ifs with h
  · exact hcy.1 ⟨a.1 + 1, h⟩
  · refine Mo_mono X.B.I ?_ hcy.2
    rintro _ ⟨b, rfl⟩
    have := b.2
    exact ⟨b, show b.1 < a.1 + 1 by omega, rfl⟩

theorem chiN_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hcx : Formalism.L2.SG.NormCut.NCong X x)
    (hcy : Formalism.L2.SG.NormCut.NCong X y) : chiN X (x * y) = chiN X x * chiN X y := by
  unfold chiN
  refine psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  exact term_Z X.B.I X.B.g _ _ (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a)
    (Me_Q X.B.I X.B.g X.e0 X.f0 hf0 (hfe X) a (e_step' X hx hcx.1 a _ (nxt_cong' X hcy a)))

theorem chiN_one : chiN X 1 = 1 := by
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_
  simp only [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
  exact Z_sum X.B.I X.B.g _ _ fun a _ => nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a

end Formalism.L2.SG.Pf.ChiNMul

namespace Formalism.L2.SG.NormCut

section ChiNOut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

theorem chiN_colDiff (w : D.what₂.Word) (h h' : Hfin X w)
    (hk : ((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset) :
    chiN X (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) = 1 := by
  have s := colStab X w h h' hk
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (Formalism.L2.SG.Pf.ChiNMul.gB_ne_zero X) ?_
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  have hf0 : X.f0 a ∈ X.B.I.Lf := (X.vectorsInLattice.1 a).2
  have hd : X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a -
      nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g := by
    unfold nxt; split_ifs
    · exact s.1 _
    · exact s.2
  rw [show X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a =
    nxt X.e0 X.z0 a + (X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a -
      nxt X.e0 X.z0 a) by abel, hA_add_right]
  exact Z_add X.B.I X.B.g (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (Formalism.L2.SG.Pf.ChiNMul.hfe X)
    (Formalism.L2.SG.Pf.ChiNMul.hfz X) a) (mL_Qs X.B.I X.B.g hf0 hd)

theorem chiNIndep_of_frameTie (hTF : FrameTie X u u' F0 F0') : ChiNIndep F0 F0' cs cs' := by
  intro t ρ ρ' hρ hρ' _
  have hb : cs.lamOf (cs.base t.lam) = t.lam := cs.base_lam _ t.mem
  have hb' : cs'.lamOf (cs'.base t.lam') = t.lam' := cs'.base_lam _ t.mem'
  have k1K := Formalism.L2.SG.Pf.colLatK X cs ρ (cs.base t.lam) (hρ.trans hb.symm)
  have k2K := Formalism.L2.SG.Pf.colLatK X cs' (cs'.base t.lam') ρ' (hb'.trans hρ'.symm)
  have κK := Formalism.L2.SG.Pf.termK X cs cs' (F0 := F0) (F0' := F0') t
  have κN := adm_norm_of_fixed_frames cs cs' hTF (Formalism.L2.SG.Pf.termK X cs cs') (Formalism.L2.SG.Pf.modGAt X) t
  have k1N := ncong_colDiff u _ _ k1K
  have k2N := ncong_colDiff u' _ _ k2K
  have hκ : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt =
      (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)) *
        kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt *
        (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h ρ' : X.B.I.Gf) * X.xu u')) := by
    unfold kOf; group
  rw [hκ, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X (K_mul X.B.I k1K κK) (ncong_mul X k1K k1N κN) k2N,
    Formalism.L2.SG.Pf.ChiNMul.chiN_mul X k1K k1N κN, chiN_colDiff u _ _ k1K, chiN_colDiff u' _ _ k2K, one_mul,
    mul_one]

end ChiNOut

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem uMat_inv_mul (g : UJ ε) : Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  show (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

theorem uMat_mul_inv (g : UJ ε) : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  show _ * (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

theorem uMat_mul (g h : UJ ε) : Formalism.MainNotions.S.uMat (g * h) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat h := rfl

theorem inv_fix {g : UJ ε} {v : Fin n → ℂ} (h : Formalism.MainNotions.S.uMat g *ᵥ v = v) : Formalism.MainNotions.S.uMat g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [mulVec_mulVec, uMat_inv_mul, one_mulVec]

theorem fix_span {g : Matrix (Fin n) (Fin n) ℂ} (hg : ∀ a, g *ᵥ e a = e a) (a : ℕ) :
    ∀ x ∈ spanLt e a, g *ᵥ x = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, _, rfl⟩ := hy
    exact hg b
  | zero => exact mulVec_zero _
  | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
  | smul c x _ hx => rw [mulVec_smul, hx]

theorem InN_one : InN ε e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨UnitaryIsometries.RI.inS_one e z, fun y _ => by rw [sub_self, zero_mulVec]; exact Submodule.zero_mem _⟩

theorem InN_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InN ε e z g) (hh : InN ε e z h) : InN ε e z (g * h) := by
  refine ⟨UnitaryIsometries.RI.inS_mul e z hg.1 hh.1, fun y hy => ?_⟩
  have key : (g * h - 1) *ᵥ y = g *ᵥ ((h - 1) *ᵥ y) + (g - 1) *ᵥ y := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  rw [key]
  exact Submodule.add_mem _ (UnitaryIsometries.RI.inS_pres e z hg.1 r _ (hh.2 y hy)) (hg.2 y hy)

def NG : Subgroup (UJ ε) where
  carrier := NLoc ε e z
  one_mem' := InN_one ε e z
  mul_mem' {g h} hg hh := InN_mul ε e z hg hh
  inv_mem' {g} hg := by
    have hS : g⁻¹ ∈ UnitaryIsometries.RI.SG ε e z := (UnitaryIsometries.RI.SG ε e z).inv_mem hg.1
    refine ⟨hS, fun y hy => ?_⟩
    have key : (Formalism.MainNotions.S.uMat g⁻¹ - 1) *ᵥ y = -(Formalism.MainNotions.S.uMat g⁻¹ *ᵥ ((Formalism.MainNotions.S.uMat g - 1) *ᵥ y)) := by
      rw [mulVec_mulVec, Matrix.mul_sub, uMat_inv_mul, Matrix.mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec]
      abel
    rw [key]
    exact Submodule.neg_mem _ (UnitaryIsometries.RI.inS_pres e z hS r _ (hg.2 y hy))

def HG : Subgroup (UJ ε) where
  carrier := HLoc ε e p z
  one_mem' := ⟨fun a => one_mulVec _, fun a => one_mulVec _, one_mulVec _⟩
  mul_mem' {g h} hg hh := ⟨fun a => by rw [uMat_mul, ← mulVec_mulVec, hh.1 a, hg.1 a],
    fun a => by rw [uMat_mul, ← mulVec_mulVec, hh.2.1 a, hg.2.1 a],
    by rw [uMat_mul, ← mulVec_mulVec, hh.2.2, hg.2.2]⟩
  inv_mem' {g} hg := ⟨fun a => inv_fix ε (hg.1 a), fun a => inv_fix ε (hg.2.1 a), inv_fix ε hg.2.2⟩

theorem coe_NG : (NG ε e z : Set (UJ ε)) = NLoc ε e z := rfl

theorem coe_HG : (HG ε e p z : Set (UJ ε)) = HLoc ε e p z := rfl

theorem NG_closed : IsClosed (NG ε e z : Set (UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ v) := fun v =>
    ((UnitaryIsometries.RI.continuous_uMat ε).sub continuous_const).matrix_mulVec continuous_const
  have e1 : (NG ε e z : Set (UJ ε)) = (UnitaryIsometries.RI.SG ε e z : Set (UJ ε)) ∩
      ⋂ y ∈ {y : Fin n → ℂ | ∀ a, hJ ε (e a) y = 0},
        (fun g : UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ y) ⁻¹' (spanLt e r : Set (Fin n → ℂ)) := by
    ext g
    simp only [coe_NG, NLoc, InN, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
    rfl
  rw [e1]
  exact (UnitaryIsometries.RI.SG_closed ε e z).inter (isClosed_biInter fun y _ =>
    (Submodule.closed_of_finiteDimensional _).preimage (hc y))

theorem HG_closed : IsClosed (HG ε e p z : Set (UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : UJ ε => Formalism.MainNotions.S.uMat g *ᵥ v) := fun v =>
    (UnitaryIsometries.RI.continuous_uMat ε).matrix_mulVec continuous_const
  have e1 : (HG ε e p z : Set (UJ ε)) = (⋂ a, {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ e a = e a}) ∩
      ((⋂ a, {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ p a = p a}) ∩ {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ z = z}) := by
    ext g
    simp only [coe_HG, HLoc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e1]
  exact (isClosed_iInter fun a => isClosed_eq (hc _) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_eq (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const))

theorem NG_le_SG : NG ε e z ≤ UnitaryIsometries.RI.SG ε e z := fun _ hg => hg.1

theorem HG_le_SG : HG ε e p z ≤ UnitaryIsometries.RI.SG ε e z := by
  intro g hg
  refine ⟨fun a => ?_, ?_⟩
  · rw [Matrix.sub_mulVec, one_mulVec, hg.1 a, sub_self]
    exact Submodule.zero_mem _
  · rw [Matrix.sub_mulVec, one_mulVec, hg.2.2, sub_self]
    exact Submodule.zero_mem _

theorem conj_mem {h g : UJ ε} (hh : h ∈ HG ε e p z) (hg : g ∈ NG ε e z) : h * g * h⁻¹ ∈ NG ε e z := by
  have hfix : ∀ a, Formalism.MainNotions.S.uMat h *ᵥ e a = e a := hh.1
  have hfix' : ∀ a, Formalism.MainNotions.S.uMat h⁻¹ *ᵥ e a = e a := fun a => inv_fix ε (hh.1 a)
  have key : ∀ v, (Formalism.MainNotions.S.uMat (h * g * h⁻¹) - 1) *ᵥ v =
      Formalism.MainNotions.S.uMat h *ᵥ ((Formalism.MainNotions.S.uMat g - 1) *ᵥ (Formalism.MainNotions.S.uMat h⁻¹ *ᵥ v)) := by
    intro v
    rw [uMat_mul, uMat_mul, mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      uMat_mul_inv, Matrix.sub_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, hfix', fix_span e hfix a.1 _ (hg.1.1 a)]
    exact hg.1.1 a
  · rw [key, inv_fix ε hh.2.2, fix_span e hfix r _ hg.1.2]
    exact hg.1.2
  · have hy' : ∀ a, hJ ε (e a) (Formalism.MainNotions.S.uMat h⁻¹ *ᵥ y) = 0 := by
      intro a
      rw [← hfix' a, UnitaryIsometries.isIsom_uMat ε h⁻¹, hy a]
    rw [key, fix_span e hfix r _ (hg.2 _ hy')]
    exact hg.2 _ hy'

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValG
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.PairValG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gval_eq_G (hrows : IsRowReps D F0 what₂) {t : Term D u u' F0 what₂}
    {F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)} (hrep : Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F') :
    Gval (lf D F0) F' = t.G := by
  obtain ⟨h, hmk⟩ := hrep
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' F0 t.lam (hrows.1 t.lam t.mem)).1
  change _ = Gt t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls
  rw [← hmk]
  exact (Gt_mk hGF ⟨F', h⟩).symm

end Formalism.L2.SG.Pf.PairValG
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf
section
noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.RealObj.InfCut

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def StepPtRepDiag : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k), PtRepExists X u u' sc i0 i0

namespace PtRepPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hJ_crd (v : InfinitePlace X.B.I.F) (x y : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (rv X.B.I v (X.crd y)) = X.B.I.φ v (X.ιE.symm ((VS D).hT x y)) := by
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) x y]
  first
  | rw [RingEquiv.symm_apply_apply]
  | simp only [RingEquiv.symm_apply_apply]
  | simp
  exact PI.ScPiFrameW.hJ_rv X.B.I v (X.crd x) (X.crd y)

def frU (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fr (X.B.I.ε v) D.R.rS D.R.k where
  e := fun a => rv X.B.I v (X.eR a)
  fd := fun a => rv X.B.I v (X.fR a)
  z := rv X.B.I v (X.zR u)
  wb := X.wfr u v
  T := Tw u
  T_pos := by unfold Tw; exact_mod_cast (D.mem u).A.T_prime.pos
  card := by have h1 := X.n_eq; have h2 := Formalism.MainNotions.S.dimS_eq D.R; omega
  ee := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.eX b))) = 0
    rw [hJ_crd, X.ee, map_zero, map_zero]
  ff := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.fY b))) = 0
    rw [hJ_crd, X.ff, map_zero, map_zero]
  ef := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.fY b))) = _
    rw [hJ_crd, X.ef]
    split_ifs <;> simp
  ez := fun a => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.zu u))) = 0
    rw [hJ_crd, (X.zu_orth u a).1, map_zero, map_zero]
  fz := fun a => by
    show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.zu u))) = 0
    rw [hJ_crd, (X.zu_orth u a).2, map_zero, map_zero]
  zz := by
    show hJ _ (rv X.B.I v (X.crd (X.zu u))) (rv X.B.I v (X.crd (X.zu u))) = _
    rw [hJ_crd, X.zu_norm, map_neg, map_neg, map_natCast, map_natCast]
    simp [Tw]
  ww := X.wfr_on u v
  ew := fun a i => ((X.wfr_perp u v i).1 a).1
  fw := fun a i => ((X.wfr_perp u v i).1 a).2
  zw := fun i => (X.wfr_perp u v i).2

theorem zhatO_zhatO {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ZhatO (ZhatO Z) = Z := by
  ext a b
  simp only [Formalism.L2.SG.RealObj.ZhatO, ← mul_assoc, ← mul_pow]
  norm_num

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a
  simp only [Formalism.L2.SG.RealObj.famSc, Complex.ofReal_one, one_pow, inv_one, one_smul]

end PtRepPf


open PtRepPf in
theorem real_point_representative_diagonal : StepPtRepDiag := by
  intro D X u u' sc hsc i0 w hw
  have hloc := fun v => locMain (frU X u v) (frU X u' v) rfl (i0 v) (ZhatO (ptC X v w)) (hw v) sc hsc
  choose g hgZ φ hφ hD using hloc
  have hω : ∀ v, hJ (X.B.I.ε v) (X.wfr u' v (i0 v)) (X.wfr u' v (i0 v)) = 1 := fun v => by
    rw [X.wfr_on, if_pos rfl]
  refine ⟨g, fun v => ?_, 1, fun v => rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v), ?_, ?_, ?_⟩
  · show ZhatO (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat (g v))) = ptC X v w
    simp only [frm, famSc_one]
    rw [show Zhat (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
        (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (g v)) = ZhatO (ptC X v w) from hgZ v,
      zhatO_zhatO]
  · intro v x _
    show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) *ᵥ rv X.B.I v x = rv X.B.I v x
    simp [uMat]
  · intro v x hx
    rw [rotU_mulVec]
    have h0 : hJ (X.B.I.ε v) (X.wfr u' v (i0 v)) (rv X.B.I v x) = 0 := by
      rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
      · exact (frU X u' v).we (i0 v) a
      · exact (frU X u' v).wf (i0 v) a
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact (frU X u' v).wz (i0 v)
    rw [h0, mul_zero, zero_smul, add_zero]
  · intro v
    have hm1 : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v 1 = 1 := by
      ext a b
      show hJ (X.B.I.ε v) (X.wfr u v a) (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) *ᵥ X.wfr u v b) = _
      simp [uMat, X.wfr_on, Matrix.one_apply]
    have hm2 : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v
        (fun v => rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v)) =
        Matrix.diagonal fun i => if i = i0 v then φ v else 1 := by
      ext a b
      show hJ (X.B.I.ε v) (X.wfr u' v a)
        (uMat (rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v)) *ᵥ X.wfr u' v b) = _
      rw [rotU_mulVec, hJ_add_right, hJ_smul_right, X.wfr_on, X.wfr_on, X.wfr_on, diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = i0 v
        · subst ha; simp
        · simp [ha, Ne.symm ha]
      · by_cases hb : b = i0 v
        · subst hb; simp [hab]
        · simp [hab, hb, Ne.symm hb]
    rw [hm1, hm2]
    exact hD v

theorem real_point_representative_exists : StepPtRep := real_point_representative_diagonal

end Formalism.L2.SG.RealObj.InfCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SurjOfIndep
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n : ℕ} (ε : Fin n → Bool)

abbrev dl (i : Fin n) : Fin n → ℂ := Pi.single i 1

theorem hJ_dl (i j : Fin n) : hJ ε (dl i) (dl j) = if i = j then (if ε i then 1 else -1) else 0 := by
  unfold hJ
  simp only [dl, Formalism.REAL.Jm, mulVec_diagonal, dotProduct, Pi.star_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simp [h]
    · simp [hl]

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end

