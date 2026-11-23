module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpInhab
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetOnePf
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

section Gen

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem nlam_iff_of_rel {Λ : Submodule (𝓞 D.host.E) (VS D).V} {p q : GCar X u u F0 F0 Λ Λ}
    (h : GRel X u u F0 F0 Λ Λ p q) : p.1.2 ∈ NLam Λ (lf D F0) ↔ q.1.2 ∈ NLam Λ (lf D F0) := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  let H := NLamSub Λ (lf D F0)
  rw [hq]
  constructor
  · intro hp
    exact H.mul_mem (H.mul_mem hn hp) hn'
  · intro hq'
    have e : p.1.2 = n⁻¹ * (n * p.1.2 * n') * n'⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hn) hq') (H.inv_mem hn')

theorem nlam_out_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} (p : GCar X u u F0 F0 Λ Λ) :
    (Quot.out (Quot.mk (GRel X u u F0 F0 Λ Λ) p)).1.2 ∈ NLam Λ (lf D F0) ↔ p.1.2 ∈ NLam Λ (lf D F0) := by
  have key : ∀ a b : GCar X u u F0 F0 Λ Λ, Relation.EqvGen (GRel X u u F0 F0 Λ Λ) a b →
      (a.1.2 ∈ NLam Λ (lf D F0) ↔ b.1.2 ∈ NLam Λ (lf D F0)) := by
    intro a b hab
    induction hab with
    | rel a b h => exact nlam_iff_of_rel h
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact key _ _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk (GRel X u u F0 F0 Λ Λ) p)))

theorem isId_of_lin {t : GTerm X u u F0 F0 what₂ what₂} (h : t.lin ∈ NLam t.lam (lf D F0)) : t.isId := by
  unfold GTerm.isId Formalism.L2.SG.FourParts.termIsId Formalism.L2.SG.FourParts.IsIdT
  refine ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, ?_⟩
  unfold Formalism.L2.SG.FourParts.IsIdF
  have hi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hf : mapLF t.lin (lf D F0) = _ := dif_pos hi
  rw [show t.frame = mapLF t.lin (lf D F0) from rfl, hf]
  refine ⟨t.lin, h, fun a => rfl, ?_⟩
  have hz : (mapFlag t.lin hi (lf D F0).fl).z = t.lin (lf D F0).fl.z := rfl
  show t.lin (lf D F0).fl.z - (mapFlag t.lin hi (lf D F0).fl).z ∈ _
  rw [hz, sub_self]
  exact zero_mem _

end Gen

theorem idMeetOneC_of (hK : IdMeetKeyC) : IdMeetOneC := by
  intro D X Y u hneat _
  refine ⟨fun ρ ρ' t hid hm => (hK D X Y u hneat ρ ρ' t hid hm).1, ?_, ?_⟩
  · intro ρ t t' hid hid' hm hm'
    have h1 := (hK D X Y u hneat ρ ρ t hid hm).2
    have h2 := (hK D X Y u hneat ρ ρ t' hid' hm').2
    obtain ⟨hl, hl', -⟩ := hm
    obtain ⟨hr, hr', -⟩ := hm'
    obtain ⟨lam, mem, lam', mem', cls⟩ := t
    obtain ⟨lam₂, mem₂, lam₂', mem₂', cls₂⟩ := t'
    simp only at hl hl' hr hr'
    subst hl hl' hr hr'
    have h1' : (Quot.out cls).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h1
    have h2' : (Quot.out cls₂).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h2
    have hrel : GRel X u u (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) (Quot.out cls) (Quot.out cls₂) :=
      ⟨(Quot.out cls₂).1.2 * ((Quot.out cls).1.2)⁻¹,
        Subgroup.mul_mem _ h2' (Subgroup.inv_mem _ h1'), 1, Formalism.L2.SG.Pf.nlam_one _ _, by group⟩
    have hs := Quot.sound hrel
    have hc : cls = cls₂ := (Quot.out_eq cls).symm.trans (hs.trans (Quot.out_eq cls₂))
    subst hc
    rfl
  · intro ρ
    have hΛ := (Y.cs u).lam_mem ρ
    let t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) :=
      idGTerm X ((Y.cs u).lamOf ρ) hΛ ((Y.rowsOK u).1 _ hΛ)
    have hlin : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) :=
      (nlam_out_iff _).2 (Formalism.L2.SG.Pf.nlam_one _ _)
    refine ⟨t, isId_of_lin hlin, rfl, rfl, ?_⟩
    exact (Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin t.rep.2.1).1

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetPhasePf
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem idMeetPhaseC_of (hK : IdMeetKeyC) : IdMeetPhaseC := by
  intro D X Y u hneat _ ρ t hid hmeet
  obtain ⟨-, hlin⟩ := hK D X Y u hneat ρ ρ t hid hmeet
  have hR : RatLink X t.pt t.lin := t.rep.2.1
  have hN : t.pt.1 ∈ X.NinfU u := Formalism.L2.SG.Pf.nLamNinf_holds D X u _ t.pt t.lin hR hlin
  have hNf : t.pt.2 ∈ X.NfinU u := Formalism.L2.SG.Pf.nLamNfin_holds D X u _ t.pt t.lin hR hlin
  obtain ⟨h1, hmul, hinv⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  obtain ⟨-, hchi, -⟩ := Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin hR
  have hprod := Formalism.L2.SG.Pf.psiProd_all D X u t.pt (ratLink_mem X hR) hN hNf
  refine ⟨hinv _ hN, ?_⟩
  have hψ1 : X.psiInfU u 1 = 1 := by
    have h11 := (hmul 1 h1 1 h1).2
    rw [mul_one] at h11
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u 1
    have h0 : X.psiInfU u 1 ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    exact mul_left_cancel₀ h0 (h11.symm.trans (mul_one _).symm)
  have hinvψ : X.psiInfU u t.pt.1⁻¹ * X.psiInfU u t.pt.1 = 1 := by
    rw [← (hmul _ (hinv _ hN) _ hN).2, inv_mul_cancel, hψ1]
  have hconj : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = X.psiInfU u t.pt.1 := by
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u t.pt.1⁻¹
    have hz : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = (X.psiInfU u t.pt.1⁻¹)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
    rw [hz, inv_eq_of_mul_eq_one_right hinvψ]
  show X.chi2 ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *
    starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = 1
  rw [hchi, hconj, mul_comm]
  exact hprod

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem roinf_eq_nocol {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (ρ : (Y.cs u).Cl)
    (t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) (hl : t.lam = (Y.cs u).lamOf ρ)
    (hl' : t.lam' = (Y.cs u).lamOf ρ) (hγ : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))) :
    ROinf t = Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ := by
  ext y
  unfold ROinf ROset Formalism.L2.SG.TermOp.KExpCut.NOcol
  rw [hl, hl']
  constructor
  · rintro ⟨x, n, hx, hy, hn, -⟩
    exact ⟨x, n, hx, hy, hn⟩
  · rintro ⟨x, n, hx, hy, hn⟩
    refine ⟨x, n, hx, hy, hn, ?_⟩
    let H := NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u))
    exact H.mul_mem (H.mul_mem (H.inv_mem hγ) hn) hγ

theorem idMeetVolC_of (hK : IdMeetKeyC) (hV : VolColC) : IdMeetVolC := by
  intro D X Y u hN hF ρ t ht hm
  obtain ⟨-, hlin⟩ := hK D X Y u hN ρ ρ t ht hm
  have hR := roinf_eq_nocol Y ρ t hm.1.symm hm.2.1.symm hlin
  have hex : ∃ Ω, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) Ω := hF t
  unfold FundOf
  rw [dite_eq_left hex]
  apply hV D X Y u ρ
  rw [← hR]
  exact hex.choose_spec

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

section Defs

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def concreteLevelAdelicSubset (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' := fun ha hb => hK.2.1 _ ha _ hb
  inv_mem' := fun ha => hK.2.2.1 _ ha

def UcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) : Subgroup X.B.I.Gf :=
  Formalism.L2.SG.Pf.NfinSub (I := X.B.I) X.eR (X.zR u) ⊓ (concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom

def RcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) : Subgroup X.B.I.GA :=
  Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ (Formalism.L2.SG.Pf.NinfSub (I := X.B.I) X.eR (X.zR u)).prod (UcS X u hK c)

def GcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) : Subgroup X.B.I.Ginf := (RcS X u hK c).map (MonoidHom.fst _ _)

end Defs

def NOinfEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), NOinf X u = (GcS X u hK (X.xu u) : Set X.B.I.Ginf)

def NOcolEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl),
    Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ =
      (GcS X u Y.hK (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) : Set X.B.I.Ginf)

def GcCountC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf), Countable (GcS X u hK c)

def FundMeasEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Γ : Subgroup X.B.I.Ginf) (Ω Ω' : Set X.B.I.Ginf),
    (Γ : Set X.B.I.Ginf) ⊆ X.NinfU u → Countable Γ → IsSFund X.B.I Γ Ω → IsSFund X.B.I Γ Ω' →
      X.muN u Ω = X.muN u Ω'

def IndexVolC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Γ Γ' : Subgroup X.B.I.Ginf) (Ω : Set X.B.I.Ginf),
    Γ' ≤ Γ → (Γ : Set X.B.I.Ginf) ⊆ X.NinfU u → Countable Γ → Γ'.relIndex Γ ≠ 0 → IsSFund X.B.I Γ Ω →
      ∃ Ω', IsSFund X.B.I Γ' Ω' ∧ X.muN u Ω' = (Γ'.relIndex Γ : ℝ≥0∞) * X.muN u Ω

def IndexTransferC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (g h : Hfin X u),
    (GcS X u hK ((h : X.B.I.Gf) * X.xu u)).relIndex (GcS X u hK ((g : X.B.I.Gf) * X.xu u)) =
        (UcS X u hK ((h : X.B.I.Gf) * X.xu u)).relIndex (UcS X u hK ((g : X.B.I.Gf) * X.xu u)) ∧
      (UcS X u hK ((h : X.B.I.Gf) * X.xu u)).relIndex (UcS X u hK ((g : X.B.I.Gf) * X.xu u)) ≠ 0

def ConjUC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (g : Hfin X u) (c : X.B.I.Gf),
    UcS X u hK ((g : X.B.I.Gf) * c) = (UcS X u hK c).map (MulAut.conj (g : X.B.I.Gf)).toMonoidHom

def GcFundC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (h : Hfin X u),
    ∃ Ω, IsSFund X.B.I (GcS X u Y.hK ((h : X.B.I.Gf) * X.xu u)) Ω

def GcConjC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK),
    (GcS X u hK ((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) * X.xu u) : Set X.B.I.Ginf) =
      (fun s => (γ : X.B.I.GA).1 * s * (γ : X.B.I.GA).1⁻¹) '' (GcS X u hK ((h : X.B.I.Gf) * X.xu u) : Set X.B.I.Ginf)

def HinfConjC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (h : X.B.I.Ginf), h ∈ Hinf X u → ∀ Ω : Set X.B.I.Ginf,
    MeasurableSet Ω → X.muN u ((fun s => h * s * h⁻¹) '' Ω) = X.muN u Ω

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictPf
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.IotaDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem levi_one_iff {δ : X.B.I.Gf} (gδ : Good X δ) :
    levi TR δ = 1 ↔ ∀ j, (X.B.I.fmat δ - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  refine ⟨fun h1 i => ?_, fun h => Formalism.L2.SG.Pf.AmpIota.levi_eq_one_of TR gδ h⟩
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  set w := X.B.I.fmat δ *ᵥ X.bw i with hwdef
  have hwL : w ∈ X.B.I.Lf := K_mv X.B.I gδ.1.1 (hB i)
  have hwM := gδ.1.2.2 i
  have hd := dual_coords X hwL
  have hZe : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w) := fun a =>
    Z_pair_Mo X (hE0 a) (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · exact (X.gramIntegral a b).1
      · exact ((X.weightVectorsIntegral l).2.2 a).1) _ hwM
  have hZz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 w) :=
    Z_pair_Mo X hZ0 (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · rw [hA_symm]; exact Z_sig X.B.I X.B.g ((X.formsAtZero).2 b).1
      · exact (X.weightVectorsIntegral l).1) _ hwM
  have hbw0 : ∀ j, hA X.B.I (X.bw j) w = 0 := fun j => by
    rw [hwdef, X.bw_w j, X.bw_w i, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
    have := X.ew_orth
    linear_combination (hA X.B.I (X.bw j) (X.B.I.fmat δ *ᵥ X.bw i)) * this
  have hcoef : ∀ j : Fin D.R.k, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) := by
    intro j
    have hI := hA_int X.B.I (hBd j) hwL
    have hIt : ((if j = i then 1 else 0 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := by
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have hres : ∀ v, TR.res v ⟨_, sub_mem hI hIt⟩ = 0 := by
      intro v
      have hent : leviM TR δ v j i = if j = i then 1 else 0 := by
        rw [← levi_coe TR gδ, h1, Pi.one_apply, Units.val_one, Matrix.one_apply]
      have e : (⟨_, sub_mem hI hIt⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, hI⟩ - ⟨_, hIt⟩ := by
        apply Subtype.ext; simp
      rw [e, map_sub]
      have h2 : TR.res v ⟨_, hI⟩ = leviM TR δ v j i := by
        show _ = resT TR v (hA X.B.I (X.bwd j) (X.B.I.fmat δ *ᵥ X.bw i))
        rw [resT_of_mem TR v hI]
      rw [h2, hent]
      by_cases h : j = i
      · subst h
        have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 1 := by apply Subtype.ext; simp
        rw [if_pos rfl, this, map_one, sub_self]
      · have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 0 := by apply Subtype.ext; simp [h]
        rw [if_neg h, this, map_zero, sub_self]
    have hZ := (TR.res_ker ⟨_, sub_mem hI hIt⟩).1 hres
    have e : X.ew * (hA X.B.I (X.bwd j) w - if j = i then 1 else 0) =
        hA X.B.I (X.bwd j) w - if j = i then X.ew else 0 := by
      rw [mul_sub, ← bwc_ew δ j i]
      split_ifs <;> ring
    simpa [e] using hZ
  have e1 : (X.B.I.fmat δ - 1) *ᵥ X.bw i = (w - repr0 X w) +
      ((∑ a, hA X.B.I (X.f0 a) w • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) w • X.f0 a) - hA X.B.I X.z0 w • X.z0 +
        (∑ j, (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) • X.bw j) +
        (∑ j, hA X.B.I (X.bw j) w • X.bwd j)) := by
    have hbi : (∑ j, (if j = i then X.ew else 0) • X.bw j) = X.bw i := by
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact (X.bw_w i).symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hwdef]
    unfold repr0
    simp only [sub_smul, Finset.sum_sub_distrib, hbi]
    abel
  rw [e1]
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (s : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      s ∈ Set.range X.e0 → c • s ∈ Mo X.B.I X.B.g (Set.range X.e0) := fun c s hc hs => by
    have : c • s = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • s := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hs)
  refine add_mem (mL_Mo X.B.I hd) (add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_)
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF0 a) hwL) ⟨a, rfl⟩
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (hZe a) (hF0 a))
  · exact mL_Mo X.B.I (Z_smul_mL X hZz hZ0)
  · exact sum_mem fun j _ => mL_Mo X.B.I (Z_smul_mL X (hcoef j) (hB j))
  · refine sum_mem fun j _ => ?_
    rw [hbw0, zero_smul]; exact zero_mem _

theorem iotaOf_split {u u' : D.what₂.Word} (Y : Formalism.L2.SG.Full.Full X)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam') :
    Good X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) ∧
      NCong X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) ∧
      iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ = levi Y.TR ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
        (s₂.pt.2 * s₁.pt.2⁻¹) * (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) *
        iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ := by
  have hTF := Formalism.L2.SG.Full.Full.frameTie (X := X) u u'
  have hN := adm_norm_of_fixed_frames (Y.cs u) (Y.cs u') hTF (Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u')) (Formalism.L2.SG.Pf.modGAt X)
  have hA := adm_parity_of_norm (Y.cs u) (Y.cs u') (Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u')) hN
  have g1 := hA s₁
  have g2 := hA s₂
  have n1 := hN s₁
  have n2 := hN s₂
  have k1 := Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u') (F0 := X.Fu u) (F0' := X.Fu u') s₁
  have k2 := Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u') (F0 := X.Fu u) (F0' := X.Fu u') s₂
  rw [← hl, ← hl'] at g2 n2 k2
  have e : (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
      (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u) =
      kOf X u u' ((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s₁.lam') : X.B.I.Gf) s₂.pt *
      (kOf X u u' ((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s₁.lam') : X.B.I.Gf) s₁.pt)⁻¹ := by
    unfold kOf; group
  rw [e]
  refine ⟨good_mul X g2 (good_inv X g1), ncong_mul X k2 n2 (ncong_inv X k1 n1), ?_⟩
  unfold iotaOf
  rw [← hl, ← hl', levi_mul Y.TR g2 (good_inv X g1), mul_assoc, ← levi_mul Y.TR (good_inv X g1) g1, inv_mul_cancel,
    levi_one, mul_one]

end Formalism.L2.SG.Pf.IotaDictPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.IotaDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AdTriv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (δ : X.B.I.Gf) : Prop :=
  ∀ j, (X.B.I.fmat δ - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0)

def RatTriv {D : D7} (u : D.what₂.Word) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ x ∈ Lrep Λ (lf D (X.Fu u)), β x - x ∈ NgX Λ (gS D) (lf D (X.Fu u)) (lf D (X.Fu u))

def IotaDictC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic → s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D))

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfFinal
section
namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

theorem regrouping_of_neatness (hSA : NStrongApproxC) (hO : OrbitAlgC) (hSC : Formalism.L2.SG.Pf.Slab.SlabCoverC)
    (hR : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.FoldReadyX X)
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word),
      X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) :
    Formalism.L2.SG.Pf.Slab.RegroupC :=
  regrouping_of_closed_lemmas phase_well_defined_all_words column_uniqueness (colCoverC_of hSA) (slabAbsC_of phase_well_defined_all_words hSC hR hN) hO

end Formalism.L2.SG.Pf.RegroupPf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfNSA
section
noncomputable section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

section NSAPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NDense : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : X.B.I.Gf), n ∈ X.NfinU u →
    ∀ U : Set X.B.I.Gf, IsOpen U → n ∈ U →
      ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧ ν.2 ∈ U

theorem nStrongApproxC_of (hD : NDense) : NStrongApproxC := by
  intro D X u hK hKL n hn c
  have hcl := Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL
  have hc : Continuous fun m : X.B.I.Gf => c⁻¹ * (m⁻¹ * n) * c :=
    (continuous_const.mul (continuous_inv.mul continuous_const)).mul continuous_const
  obtain ⟨ν, hνr, hν1, hν2, hνU⟩ := hD D X u n hn {m | c⁻¹ * (m⁻¹ * n) * c ∈ X.K2} (hcl.2.preimage hc)
    (by simpa using hK.1)
  exact ⟨ν, hνr, hν1, hν2, hνU⟩

end NSAPf

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlgOut
section
namespace Formalism.L2.SG.Pf.RegroupPf

theorem orbit_algebra_of_stabilizer (hC : TermCarC) (hS : StabNC) : OrbitAlgC :=
  orbitAlgC_of Formalism.L2.SG.Pf.nilradical_conj_level' hC hS

end Formalism.L2.SG.Pf.RegroupPf
end

