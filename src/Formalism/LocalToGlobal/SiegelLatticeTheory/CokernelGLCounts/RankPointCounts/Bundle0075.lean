module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0073
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohLp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0065

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc
  Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf.MainEqFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ampG {Cl Nu : Type} (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ := ∏ p, L.aZ p (d p)

variable {D : D7}

theorem localLeG_of_fam {Z : LocDat D} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (C1 C0n : ℕ) (AAre : ℝ) (hk : 2 * D.R.rS + 5 ≤ D.R.k)
    (hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS (C1 : ℝ))
    (h : ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ Fm : LocFam Z Cl Nu,
      FamOKS N γ S C0n AAre (fun L => ampG L) Fm) :
    LocalInputLeG X N C1 C0n AAre := by
  intro γ hγ S
  obtain ⟨Fm, hR, hex, hOm, hD, hn, hV0, hrw, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  have hrank : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    rw [finrank_Vp]
    have h1 := D.R.r_eq
    have h2 : 2 * D.R.rS + 2 = D.R.m := by
      have hm2 := D.R.two_le_m
      obtain ⟨j, hj⟩ := D.R.m_even
      simp only [Formalism.BasicNotions.Ranks.rS]; omega
    omega
  have hNG : ∀ p ∈ Fm.P, LocNG.NGAt D.R.k (Fm.FP p) (C1 : ℝ) := fun p hp =>
    hQ (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p) (Z.agree p).1 (Vp D p) (locH Z p) (hrank p) (Fm.FP p) (hR p hp)
  have hq2 : ∀ p ∈ Fm.P, 2 ≤ LocNG.qF (D.s.atP p).Fp := fun p hp => Formalism.MainNotions.KappaEndpoints.two_le_residue_card (Z.agree p).1
  have hqH : ∀ p ∈ Fm.P, ¬ (Fm.FP p).PrimeTo → (LocNG.qF (D.s.atP p).Fp : ℝ) ≤ (Fm.FP p).Hp := fun p hp hpr =>
    Formalism.L2.SG.Pf.residue_le_height_nonprime (Z.agree p).1 (hR p hp) (hex p hp) hpr
  have hH1 : ∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp := by
    intro p hp
    by_cases hpr : (Fm.FP p).PrimeTo
    · exact le_of_eq ((hNG p hp (Fm.R p) (Fm.d0 p)).2.2.2 hpr).1.symm
    · have h2 : (2 : ℝ) ≤ (LocNG.qF (D.s.atP p).Fp : ℝ) := by exact_mod_cast hq2 p hp
      linarith [hqH p hp hpr]
  have hHp : ∀ p ∈ Fm.P, 0 ≤ (Fm.FP p).Hp := fun p hp => le_trans zero_le_one (hH1 p hp)
  have hB : Fm.toL.Basic := by
    refine ⟨fun p d => ?_, fun p => hH1 p.1 p.2, fun p => hq2 p.1 p.2, fun p hp => hqH p.1 p.2 ((hOm p).1 hp),
      fun p => ENNReal.toReal_nonneg, hV0, hrw⟩
    show 0 ≤ LocNG.Datum.wt (Fm.d0 p.1) d.1
    unfold LocNG.Datum.wt LocNG.volRel
    positivity
  exact ⟨Fm.toL, hB, (ngAt_toL Fm C1 hk hNG hD hn hHp).2, hM, hU, ha, hH, hpos, hle⟩

def StepFamG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u) × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u)) (NuC D),
            FamOKS (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)
              (fun L => ampG L) Fm

end Formalism.L2.SG.Pf.MainEqFam

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqFam

theorem stepLocPinnedG_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFamG) : StepLocPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLeG_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps
  Formalism.L2.SG.NGCut.NormalVectorPairings

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.MainEqNml

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def OccTG (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u) : Prop :=
  t ∈ (Y.tO u u).genSet ∧ (Y.tO u u).vec t ≠ 0 ∧ clsG Y u t = c ∧ ptPN t = γ

theorem occ_iffG (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν ↔ ∃ t, OccTG Y u c γ t ∧ nmlOf Y u u t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    have e : t ∈ (Y.tO u u).genSet := by
      simp only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢
      exact h1
    exact ⟨t, ⟨e, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    have e : t ∈ (genT (Y.tO u u)).ngSet := by
      simp only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢
      exact h1
    exact ⟨t, e, h2, h3, h4, h5⟩

variable {Y u}

theorem relC_of_occG (hE : ScalEquivOn (Y.tO u u)) {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS}
    {t0 t : TauC Y u u} (h0 : OccTG Y u c γ t0) (h : OccTG Y u c γ t) : RelC Y u u t0 t := by
  unfold Formalism.L2.SG.Pf.MainEqSteps.ScalEquivOn at hE
  obtain ⟨h01, h02, h03, h04⟩ := h0
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hmem : t ∈ clsG Y u t := ⟨h1, rfl, (hE.1 t h1).1, (hE.1 t h1).2⟩
  rw [h3, ← h03] at hmem
  exact ⟨hmem.2.1, hmem.2.2.1⟩

end Formalism.L2.SG.Pf.MainEqNml

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqNml

theorem nmlInvG_of (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : Formalism.L2.SG.NGCut.NormalInvariants.Gen.NmlInvG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occ_iffG Y u νL νB ng c γ ν0).1 hν0
  have hE : ScalEquivOn (Y.tO u u) := stepClassG_holds D X Y u (g_ge_three hctx) hctx.2.2
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u := fun ν =>
    if h : ∃ t, OccTG Y u c γ t ∧ nmlOf Y u u t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν →
      OccTG Y u c γ (pick ν) ∧ nmlOf Y u u (pick ν) = ν := by
    intro ν hν
    have h := (occ_iffG Y u νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u t0 (pick ν), coefA' Y u u t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (relC_of_occG hE ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (relC_of_occG hE ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (relC_of_occG hE ht0 hp1) (relC_of_occG hE ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NOinfClosedUnderMulInv
section
namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem nOinf_closed_under_mul_inv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ⊆ X.NinfU u ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      δ * δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, δ⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) := by
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hc := Formalism.L2.SG.Pf.NOsub_coe X u hK
  refine ⟨fun s hs => Formalism.L2.SG.Pf.no_sub_ninf X u hs, fun δ hδ δ' hδ' => ?_, fun δ hδ => ?_⟩
  · rw [← hc] at hδ hδ' ⊢
    exact (Formalism.L2.SG.Pf.NOsub X u hK).mul_mem hδ hδ'
  · rw [← hc] at hδ ⊢
    exact (Formalism.L2.SG.Pf.NOsub X u hK).inv_mem hδ

end Formalism.L2.SG.Pf.NcReal.JX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NegOnePowMulSelf
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Conj

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (hA : ∀ q, Agree δ M q)

include hA in
theorem dd_conj {h : ℕ} (hk : h ≤ D.R.rS) {x : D.host.E} (hx : x ∈ ddPow D h) : D.conjF x ∈ ddPow D h := by
  rw [← locGlob _ (shapeNZ.1 h)] at hx ⊢
  exact fun p => locMem_conj δ M hA p hk (hx p)

include hA in
theorem qd_conj {h : ℕ} (hk : h ≤ D.R.rS) {x : D.host.E} (hx : x ∈ qdPow D h) : D.conjF x ∈ qdPow D h := by
  rw [qdPow_mem_iff] at hx ⊢
  have := dd_conj δ M hA hk hx
  rwa [map_div₀, map_natCast] at this

end Conj

theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : D.host.E) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩

variable (w : Point D.host.E (D.R.rS + 1))

def sgm (a c : Fin (D.R.rS + 1)) : D.host.E := (-1) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val)

omit w in
theorem sgm_mul (a d c : Fin (D.R.rS + 1)) : sgm a d * sgm d c = sgm a c := by
  unfold sgm
  have := neg_one_pow_mul_self (D := D) (D.R.rS - d.val)
  linear_combination ((-1 : D.host.E) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val)) * this

omit w in
theorem sgm_self (a : Fin (D.R.rS + 1)) : sgm a a = (1 : D.host.E) := neg_one_pow_mul_self _

omit w in
theorem sgm_conj (a c : Fin (D.R.rS + 1)) : D.conjF (sgm a c) = sgm a c := by
  simp [sgm, map_pow, map_neg, map_one]

omit w in
theorem sgm_cases (a c : Fin (D.R.rS + 1)) : sgm a c = (1 : D.host.E) ∨ sgm a c = -1 := by
  unfold sgm
  rw [← pow_add]
  exact neg_one_pow_eq_or _ _

theorem sgm_pinv (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    sgm a c * sgm (pinv w c) (pinv w a) = (1 : D.host.E) := by
  unfold sgm
  have h1 := pinv_add w a c hs
  have ha := a.isLt; have hc := c.isLt; have ha' := (pinv w a).isLt; have hc' := (pinv w c).isLt
  rw [show ((-1 : D.host.E)) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val) *
      ((-1) ^ (D.R.rS - (pinv w c).val) * (-1) ^ (D.R.rS - (pinv w a).val)) =
      (-1) ^ ((D.R.rS - a.val) + (D.R.rS - c.val) + (D.R.rS - (pinv w c).val) + (D.R.rS - (pinv w a).val)) by ring]
  exact Even.neg_one_pow ⟨2 * D.R.rS - (pinv w a).val - a.val, by omega⟩

def Psi (Mt : MatR D) : MatR D := fun a c => sgm a c * D.conjF (Mt (pinv w c) (pinv w a))

def piPerm : Equiv.Perm (Fin (D.R.rS + 1)) := ⟨pinv w, pinv w, pinv_pinv w, pinv_pinv w⟩

theorem Psi_sub (A B : MatR D) : Psi w (A - B) = Psi w A - Psi w B := by
  funext a c; simp [Psi, map_sub, mul_sub]

theorem Psi_mul (A B : MatR D) : Psi w (A * B) = Psi w B * Psi w A := by
  funext a c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Psi, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (piPerm w) _ _ (fun e => ?_)
  simp only [piPerm, Equiv.coe_fn_mk, pinv_pinv]
  rw [← sgm_mul a (pinv w e) c]; ring

theorem Psi_one : Psi w (1 : MatR D) = 1 := by
  funext a c
  simp only [Psi, Matrix.one_apply]
  by_cases h : a = c
  · subst h; simp [sgm_self]
  · have : pinv w c ≠ pinv w a := fun e => h (pinv_inj w e).symm
    simp [this, h]

theorem Psi_inv {A : MatR D} (hA : IsUnit A.det) : Psi w A⁻¹ = (Psi w A)⁻¹ := by
  have : Psi w A⁻¹ * Psi w A = 1 := by rw [← Psi_mul, Matrix.mul_nonsing_inv _ hA, Psi_one]
  exact (Matrix.inv_eq_left_inv this).symm

theorem Psi_Psi {A : MatR D} (hB : IsBlockDiagonalMatrix w A) : Psi w (Psi w A) = A := by
  funext a c
  simp only [Psi, pinv_pinv, map_mul, Formalism.MainNotions.BridgeLemma.conjF_inv, sgm_conj]
  by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
  · rw [← mul_assoc, sgm_pinv w a c hs, one_mul]
  · rw [hB a c hs, mul_zero, mul_zero]

theorem Psi_blk {A : MatR D} (hB : IsBlockDiagonalMatrix w A) : IsBlockDiagonalMatrix w (Psi w A) := by
  intro a c hne
  have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
    rw [blkOf_pinv, blkOf_pinv]; exact fun e => hne e.symm
  simp only [Psi, hB _ _ this, map_zero, mul_zero]

theorem Psi_upU {A : MatR D} (hU : UpU A) (hB : IsBlockDiagonalMatrix w A) : UpU (Psi w A) := by
  intro a c
  refine ⟨fun hca => ?_, fun hac => ?_⟩
  · simp only [Psi]
    by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
    · have := (pinv_lt_iff w c a hs.symm).1 hca
      rw [(hU _ _).1 this, map_zero, mul_zero]
    · have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
      rw [hB _ _ this, map_zero, mul_zero]
  · subst hac; simp [Psi, sgm_self, (hU _ _).2 rfl]

theorem Psi_grD (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ q, Agree δ M q) {A : MatR D} (hB : IsBlockDiagonalMatrix w A) (hG : GrD A) : GrD (Psi w A) := by
  intro a c hac
  simp only [Psi]
  by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
  · have hle : pinv w c ≤ pinv w a := by
      rcases eq_or_lt_of_le hac with h | h
      · rw [h]
      · exact le_of_lt ((pinv_lt_iff w a c hs).1 h)
    have hh : (pinv w a).val - (pinv w c).val = c.val - a.val := by
      have := pinv_add w a c hs; omega
    have h1 := hG _ _ hle
    rw [hh] at h1
    have h2 := dd_conj δ M hA (by have := c.isLt; omega) h1
    rcases sgm_cases a c with e | e
    · rw [e, one_mul]; exact h2
    · rw [e, neg_one_mul]; exact (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem h2
  · have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
      rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
    rw [hB _ _ this, map_zero, mul_zero]; exact FractionalIdeal.zero_mem _

theorem blk_inv {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) : IsBlockDiagonalMatrix w X⁻¹ := by
  obtain ⟨hlo, hXi, hW, -⟩ := st_of_X w hU hB
  set β := ptMat w * X * (ptMat w)⁻¹
  have hu := ptMat_isUnit w
  have hβd : IsUnit β.det := by rw [loU_det (show LoU β from hlo)]; exact isUnit_one
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hW' : β⁻¹ * ptMat w * X = ptMat w := by
    have : ptMat w * X⁻¹ = β⁻¹ * ptMat w := by
      calc ptMat w * X⁻¹ = β⁻¹ * (β * ptMat w * X⁻¹) := by
            rw [Matrix.mul_assoc β]; exact (Matrix.nonsing_inv_mul_cancel_left β _ hβd).symm
        _ = β⁻¹ * ptMat w := by rw [hW]
    rw [← this, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hXd, Matrix.mul_one]
  obtain ⟨h1, -, h3⟩ := X_of_st w (loU_inv (show LoU β from hlo)) hU hW'
  rw [h1] at h3
  exact h3

end Formalism.L2.SG.Pf.StabIntLat
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StarExists2OfGood
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem starExists2_of_good (hP : CtxP u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_parts Zd u u' F0 what₂ hP (cohGen_of Zd (cohInt_holds Zd) (cohDG_holds Zd) hGood)
    (cohIota_holds Zd) hGood

theorem starExists2_holds (hP : CtxP u u' F0 what₂) : StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_good Zd u u' F0 what₂ hP (cohGood_of Zd globGramNe_holds)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

