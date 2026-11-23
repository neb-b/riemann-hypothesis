module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramCPf
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

theorem satGramC'_of (hL : Formalism.L2.SG.Pf.SatGramActL.LeftActC') (hR : Formalism.L2.SG.Pf.SatGramActR.RightActC') :
    SatGramC' := by
  intro D X Y u u' hI hA hF
  have h1 := Set.mem_insert (Y.tO u u').genSet {(Y.tO u u').ngSet, (Y.tO u u').degSet}
  have h2 : (Y.tO u u').ngSet ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  exact ⟨Formalism.L2.SG.Pf.SatGram.satGram_of (hL := hL D X Y u u' hI hA hF _ h1) (hR := hR D X Y u u' hI hA hF _ h1),
    Formalism.L2.SG.Pf.SatGram.satGram_of (hL := hL D X Y u u' hI hA hF _ h2) (hR := hR D X Y u u' hI hA hF _ h2)⟩

theorem leviOntoC_holds : LeviOntoC := fun _ _ Y u => Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u)

theorem normExpSatC'_of_acts (hN : NeatC) (hM : MassAC) (hL : Formalism.L2.SG.Pf.SatGramActL.LeftActC')
    (hR : Formalism.L2.SG.Pf.SatGramActR.RightActC') : NormExpSatC' :=
  normExpSatC'_of hN leviOntoC_holds hM (satGramC'_of hL hR)

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GFInfInj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.GA), s ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I → s.1 = 1 → s = 1

def NStrongApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (n : X.B.I.Gf),
    X.LevelSubgroupNormalized → n ∈ X.NfinU u → ∃ ν ∈ Srat X u,
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (ν.2 * n) * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2

def NDense : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (n : X.B.I.Gf), n ∈ X.NfinU u →
    ∀ U : Set X.B.I.Gf, IsOpen U → n ∈ U →
      ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧ ν.2 ∈ U

def NLift : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (t : X.B.I.Ginf),
    t ∈ NOcol (X.Fu u) (Y.cs u) ρ → ∃ s ∈ Srat X u, s.1 = t ∧
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2

def NRatLam : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (ν : X.B.I.GA),
    X.LevelSubgroupNormalized → ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I → ν.1 ∈ X.NinfU u → ν.2 ∈ X.NfinU u →
    (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2 →
    ν.1 ∈ NOcol (X.Fu u) (Y.cs u) ρ

def RatLeviC : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u

def PsiDdC : Prop := ∀ (D : D7) (X : HidaSetting D), PsiDd X

theorem hfin_sfin {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (h : Hfin X u) :
    (h : X.B.I.Gf) ∈ SfinU X u := by
  rw [Formalism.L2.SG.PoincareInHH.Cut.sfin_iff]
  refine ⟨?_, ?_⟩
  · intro a
    have e := h.2 (X.eR a) (by simp [fixSet])
    try beta_reduce
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _
  · have e := h.2 (X.zR u) (by simp [fixSet])
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _

theorem gam_srat {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (γ : X.B.I.GA) (hγ : γ ∈ Gam X u) :
    γ ∈ Srat X u := by
  obtain ⟨h1, h2⟩ := hγ
  obtain ⟨h21, h22⟩ := h2
  refine ⟨h1, Subgroup.subset_closure ⟨?_, hfin_sfin X u ⟨γ.2, h22⟩⟩⟩
  rw [Formalism.L2.SG.PoincareInHH.Cut.sinf_iff]
  intro v
  refine ⟨?_, ?_⟩
  · intro a
    have e := h21 v (X.eR a) (by simp [fixSet])
    try beta_reduce
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _
  · have e := h21 v (X.zR u) (by simp [fixSet])
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _

theorem iotaF_coe {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u) :
    ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl

end Formalism.L2.SG.Pf.SlabCoverPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPfSupp
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.SlabMajPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_supp {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    ∃ (h : Hfin X u') (κ : X.B.I.Gf), κ ∈ X.K2 ∧
      t.pt.2⁻¹ * Formalism.L2.SG.Pf.Slab.aB Y u t.lam = (h : X.B.I.Gf) * X.xu u' * κ := by
  have hTF := Full.frameTie (X := X) u u'
  have hKk := Formalism.L2.SG.Closed.TermK_holds (F0 := X.Fu u) (F0' := X.Fu u') (Y.cs u) (Y.cs u') t
  have hNk := Formalism.L2.SG.Closed.AdmN_holds (Y.cs u) (Y.cs u') hTF t
  have hGk := Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') hTF t
  obtain ⟨h, hc, -, hlev⟩ := Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u')
    ⟨t.lam', t.mem'⟩
    (levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt))⁻¹
  have hNc := Formalism.L2.SG.NormCut.ncong_colDiff u' _ _ hc
  have hGc := Formalism.L2.SG.NormCut.good_of_ncong X hc hNc
  have hKkc := Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I hKk hc
  have hNkc := Formalism.L2.SG.NormCut.ncong_mul X hKk hNk hNc
  have hGkc := Formalism.L2.SG.NormCut.good_mul X hGk hGc
  have hlevkc := Formalism.L2.SG.NormCut.levi_mul Y.TR hGk hGc
  rw [hlev, mul_inv_cancel] at hlevkc
  have hK2 := Formalism.L2.SG.NormCut.mem_level_of_unitriangular Y.TR hGkc hNkc (fun v => by
    rw [hlevkc, Pi.one_apply]
    exact Formalism.L2.SG.GGMirabolic.isUni_one)
  refine ⟨h, _, Y.hK.2.2.1 _ hK2, ?_⟩
  simp only [Formalism.L2.SG.Pf.Slab.aB, kOf, Formalism.L2.SG.Pf.NormSteps.colDS]
  group

end Formalism.L2.SG.Pf.SlabMajPt
end
end

