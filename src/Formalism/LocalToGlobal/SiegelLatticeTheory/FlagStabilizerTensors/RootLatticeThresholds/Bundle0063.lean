module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0010
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.SettingExistsOfGap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EPerpMid
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut

section Fwd

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem Qi_spanLt (hT : TrHyp F Qm Qim c) {a : ℕ} {v : Fin n → ℂ} (hv : v ∈ spanLt F.e a) :
    ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qim *ᵥ v) i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro i hi
    rw [Qi_e hT b]
    have hne : i ≠ Formalism.QuantumDeterminants.eI k r b := fun h => by
      have := congrArg Fin.val h; simp only [Formalism.QuantumDeterminants.eI] at this; simp only [Set.mem_setOf_eq] at hb; omega
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply, hne]
  | zero => intro i _; simp
  | add x y _ _ hx hy => intro i hi; rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
  | smul d x _ hx => intro i hi; rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero]

theorem e_perp_mid (hT : TrHyp F Qm Qim c) (a : Fin r) (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val)
    (hj2 : j.val ≤ r + k) : hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := by
  have he : F.e a = (c a)⁻¹ • (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) := by
    rw [hT.he, smul_smul, inv_mul_cancel₀ (c_ne hT a), one_smul]
  have h0 : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) j = 0 := by
    have ha := a.isLt
    have hsum : a.val + j.val ≠ 2 * r + k := by omega
    unfold Formalism.QuantumDeterminants.Hpk
    simp only [Formalism.QuantumDeterminants.eI, hsum, not_lt.mpr hj1, not_le.mpr ha,
      and_false, false_and, if_false]
  rw [he, PtRepPf.hJ_smul_left, ← herm_Q hT]
  simp only [Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.bvec,
    ← Pi.single_star, star_one, single_dotProduct, Matrix.mulVec_single_one,
    Matrix.col_apply, h0, mul_zero]

theorem fwd_N (hT : TrHyp F Qm Qim c) {g : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ}
    (hgU : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) (hg : InN ε F.e z g) :
    Qim * g * Qm ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hQQ : Qimᴴ * Qmᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hT.h2, Matrix.conjTranspose_one]
  have hcol : ∀ (j i : Fin (2 * r + k + 1)), (Qim * g * Qm) i j = (Qim *ᵥ (g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j))) i := by
    intro j i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]
  refine ⟨?_, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩
  · show (Qim * g * Qm)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qim * g * Qm) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hT.hH]
    calc (Qim * g * Qm)ᴴ * (Qmᴴ * Formalism.REAL.Jm ε * Qm) * (Qim * g * Qm)
        = Qmᴴ * gᴴ * (Qimᴴ * Qmᴴ) * Formalism.REAL.Jm ε * (Qm * Qim) * g * Qm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qmᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * Qm := by
          rw [hQQ, hT.h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hgU]
  · rw [hcol, hT.he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply]
    have hsplit : g *ᵥ F.e a = F.e a + (g - 1) *ᵥ F.e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.1.1 a) i hi, add_zero, Qi_e hT a,
      Pi.smul_apply, smul_smul, mul_inv_cancel₀ (c_ne hT a), one_smul]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]
  · rw [hcol]
    have hw : ∀ a, hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := fun a => e_perp_mid hT a j hj1 hj2
    have hsplit : g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = Qm *ᵥ Formalism.QuantumDeterminants.bvec j + (g - 1) *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.2 _ hw) i hi, add_zero, Matrix.mulVec_mulVec,
      hT.h1, Matrix.one_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]

end Fwd

end Formalism.L2.SG.Pf.Bridge
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSF
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gap

def GapEv {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ y : ℝ, ∀ x, y ≤ x → ∀ i : Fm.Ix x, Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i)

def CG (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ GapEv Fm

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def selG : SSel (CG 𝒞) := fun Fm h => sel Fm h.1

def yFG : ∀ {eps : ℝ} (Fm : FamP eps), CG 𝒞 Fm → ℝ := fun _ h => Classical.choose h.2

theorem gap_of {eps : ℝ} {Fm : FamP eps} (h : CG 𝒞 Fm) {x : ℝ} (hx : yFG Fm h ≤ x) (i : Fm.Ix x) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
  Classical.choose_spec h.2 x hx i

theorem hyFG (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) : YFOK (selG sel) yFG := by
  intro eps Fm hc x hx h0 hy i
  have hg := gap_of hc hy i
  exact ⟨hFX _ _ hg, (hWu _ hg _).1⟩

def CX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : Formalism.L2.SG.LocWSOf.Choice X 1 :=
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  Classical.choice (Formalism.L2.SG.Pf.choiceExists X 1 one_pos)


theorem closed_sub {𝒞' : FamClass} (hs : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm)
    {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P) : Closed 𝒞' P := by
  obtain ⟨e, he, H⟩ := h
  exact ⟨e, he, fun eps h1 h2 => by
    obtain ⟨K, hK⟩ := H eps h1 h2
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (hs Fm hc) hL⟩⟩

variable (C0 : ℝ)

theorem loopRowS_of_sub (hG : Closed 𝒞 fun Fm _ => 𝒞 Fm → GapEv Fm) (h : LoopRowS C0 (CG 𝒞) (selG sel)) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  obtain ⟨e1, he1, H1⟩ := h aF
  obtain ⟨e2, he2, H2⟩ := hG
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  refine ⟨K1.sup K2, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL
  intro hc'
  have hg := hK2 Fm CH hc hL2 hc'
  exact hK1 Fm CH ⟨hc', hg⟩ hL1 ⟨hc', hg⟩

end Gap

section PartC

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def RMeasExAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (u u' : D.what₂.Word),
    (∀ τ, GoodW D τ u u' 1 (Formalism.L2.SG.LocWSOf.locW C u u' τ)) → LoopTerm.RMeasEx hI C u u'

def JFactNAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (hB : Formalism.L2.SG.LocWSOf.WuBessel C) (u u' : D.what₂.Word),
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D → LoopTerm.JFactN hI C hB u u'


variable (C0 : ℝ)

end PartC

end Formalism.L2.SG.LoopsTies
end
end

