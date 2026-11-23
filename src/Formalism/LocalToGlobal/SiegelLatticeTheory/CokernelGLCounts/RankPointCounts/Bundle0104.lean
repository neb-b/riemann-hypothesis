module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0103
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocalCountZeroGlobalHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocCntUG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0097

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountAtOfParts
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

section Parts2

variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a) (πa : UP p →* UP p)
  (hD : CountAb.Data a.mat (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa)

theorem img_eq :
    img (retr_of M δ u u' w p a πa hD hB) (KP M p ⊓ StabX p (XP M δ u u' (p := p) w L U)) (H_le_UP M _) =
      (((CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB)).map πa).map (tauU p)).map (UP p).subtype := by
  ext z
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hU' := H_le_UP M _ hh
    have hy := (mem_H_iff M δ u u' w hA L U hL hU a hB ⟨h, hU'⟩).1 hh
    refine ⟨tauU p (πa (tauU p ⟨h, hU'⟩)), ⟨πa (tauU p ⟨h, hU'⟩), ⟨_, hy, rfl⟩, rfl⟩, ?_⟩
    exact (piG_of p πa ⟨h, hU'⟩).symm
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨((tauU p y : UP p) : GG p), ?_, ?_⟩
    · exact (mem_H_iff M δ u u' w hA L U hL hU a hB (tauU p y)).2 (by rw [tauU_tauU]; exact hy)
    · show piG p πa ((tauU p y : UP p) : GG p) = _
      rw [piG_of]
      simp only [piU, MonoidHom.comp_apply, tauU_tauU]
      rfl

include hB in
theorem Ag_eq :
    Ag M δ u u' (p := p) w =
      (((KU M p) ⊓ MulAction.stabilizer (UP p) a.mat).map (tauU p)).map (UP p).subtype := by
  ext z
  rw [mem_Ag_iff]
  constructor
  · rintro ⟨hS, hK⟩
    obtain ⟨hzU, hzY⟩ := (mem_StP_iff M δ u u' w p z).1 hS
    have hfix := (fixes_base_iff M δ u u' w p a hB ⟨z, hzU⟩).1 hzY
    refine ⟨⟨z, hzU⟩, ⟨tauU p ⟨z, hzU⟩, ⟨?_, ?_⟩, tauU_tauU p _⟩, rfl⟩
    · show ((tauU p ⟨z, hzU⟩ : UP p) : GG p) ∈ KP M p
      exact tau_mem_KP M p hK
    · exact hfix
  · rintro ⟨_, ⟨y, ⟨hyK, hyS⟩, rfl⟩, rfl⟩
    refine ⟨(mem_StP_iff M δ u u' w p _).2 ⟨(tauU p y).2, ?_⟩, ?_⟩
    · exact (fixes_base_iff M δ u u' w p a hB (tauU p y)).2 (by rw [tauU_tauU]; exact hyS)
    · exact tau_mem_KP M p hyK


include hD in
theorem countAt_of_parts (v : ℝ)
    (hv : (Nat.card (Quotient (CountAb.cellRel a.mat πa.ker (KU M p) (gU M δ u u' w hA L U hL hU a hB))) : ℝ) = v)
    (hpos : Nat.card (Quotient (CountAb.cellRel a.mat πa.ker (KU M p) (gU M δ u u' w hA L U hL hU a hB))) ≠ 0) :
    CountAt M δ u u' w hA L U hL hU v := by
  have hcard := CountAb.card_cells' (a.mat) (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa
    (gU M δ u u' w hA L U hL hU a hB) hD
  have hidx : (img (retr_of M δ u u' w p a πa hD hB) (KP M p ⊓ StabX p (XP M δ u u' (p := p) w L U))
      (H_le_UP M _)).relIndex (Ag M δ u u' (p := p) w) =
      ((CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB)).map πa).relIndex
        ((KU M p) ⊓ MulAction.stabilizer (UP p) a.mat) := by
    rw [img_eq M δ u u' w hA L U hL hU a hB πa hD, Ag_eq M δ u u' w a hB,
      Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective,
      Subgroup.relIndex_map_map_of_injective _ _ (tauU_inj (p := p))]
  refine ⟨UP p, piG p πa, retr_of M δ u u' w p a πa hD hB, H_le_UP M _, conjugator_mem_unipotent M δ hA L U hL hU, ?_, ?_, ?_⟩
  · rw [img_eq M δ u u' w hA L U hL hU a hB πa hD, Ag_eq M δ u u' w a hB]
    apply Subgroup.map_mono
    apply Subgroup.map_mono
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hD.kπ z hz.1, hD.mem z⟩
  · rw [hidx, ← hcard]
    exact hpos
  · rw [hidx, ← hcard, hv]

end Parts2

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntegralClosureRankAndResidueTrdegLe
section
namespace Formalism.L2.SG.LsDatumA

theorem modSide0G : ModSide0G := Formalism.L2.SG.LocalCountModules.localCountZeroGlobal_holds

theorem modSideUG : ModSideUG := Formalism.L2.SG.LocalCountModules.localCountUnitGlobal_holds

theorem integralClosureRank_and_residueTrdegLe (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.ThinScalesBound.T2 D := globalCount_of_split_mode D modSide0G modSideUG

end Formalism.L2.SG.LsDatumA
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxFin
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Code

theorem relIndex_ne_zero_of_code {G : Type*} [Group G] (H A : Subgroup G) {Q : Type*} [Finite Q] (φ : A → Q)
    (hφ : ∀ k k' : A, φ k = φ k' → ((k⁻¹ * k' : A) : G) ∈ H) : H.relIndex A ≠ 0 := by
  classical
  have hfin : Finite (A ⧸ H.subgroupOf A) := by
    choose rep hrep using fun v : Set.range φ => v.2
    refine Finite.of_surjective (fun v : Set.range φ => (QuotientGroup.mk (rep v) : A ⧸ H.subgroupOf A)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      refine ⟨⟨φ k, k, rfl⟩, ?_⟩
      show (QuotientGroup.mk (rep ⟨φ k, k, rfl⟩) : A ⧸ H.subgroupOf A) = QuotientGroup.mk k
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact hφ _ _ (hrep _)
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

end Code

section Fin

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem R_sub_O {p : PlF D} (hA : Agree δ M p) {x : (D.s.atP p).Ep} (hx : x ∈ (M p).R) : x ∈ (D.s.atP p).O := by
  obtain ⟨-, -, -, hO, -, hsp⟩ := hA
  revert hx
  show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R → _
  rcases hM : (M p).split with _ | g
  · intro hx
    have : x ∈ (M p).L.O := hx
    rwa [hO] at this
  · rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      intro hx
      rw [Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split] at hx
      rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1]
      exact ⟨hx.1, hx.2.1⟩

def dO {p : PlF D} (c : (D.s.atP p).Fp) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).O :=
  ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c, alg_mem_O hc⟩

theorem finite_quot {p : PlF D} (hA : Agree δ M p) (c : (D.s.atP p).Fp) (hc0 : c ≠ 0) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    Finite ((D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) := by
  obtain ⟨hOK, -, -, hO, -, -⟩ := hA
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  obtain ⟨hOo, hOc, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top (M p).L
  rw [hO] at hOo hOc
  have : CompactSpace (D.s.atP p).O := isCompact_iff_compactSpace.1 hOc
  have hc' : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have hopen : IsOpen (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) := by
    have h1 : (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) =
        (fun y : (D.s.atP p).O => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep)) ⁻¹'
          ((D.s.atP p).O : Set (D.s.atP p).Ep) := by
      ext y
      simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_preimage]
      rw [Ideal.mem_span_singleton']
      constructor
      · rintro ⟨z, rfl⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * ((z : (D.s.atP p).Ep) * algebraMap _ _ c) ∈ (D.s.atP p).O
        rw [mul_comm (z : (D.s.atP p).Ep), ← mul_assoc, hc', one_mul]
        exact z.2
      · intro hy
        refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep) * algebraMap _ _ c = y
        rw [mul_comm, ← mul_assoc, mul_comm (algebraMap _ _ c), hc', one_mul]
    rw [h1]
    exact hOo.preimage (by fun_prop)
  exact AddSubgroup.quotient_finite_of_isOpen _ hopen

theorem quot_eq {p : PlF D} {c : (D.s.atP p).Fp} {hc : c ∈ 𝒪[(D.s.atP p).Fp]} {x y : (D.s.atP p).O}
    (h : (QuotientAddGroup.mk x : (D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) = QuotientAddGroup.mk y) :
    (y : (D.s.atP p).Ep) - x ∈ latS (D.s.atP p) c := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  refine mem_latS.2 ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_neg] at this
  rw [show (y : (D.s.atP p).Ep) - x = -x + y by ring, ← this]
  show (z : (D.s.atP p).Ep) * algebraMap _ _ c = _
  ring

theorem entIn_int_mul {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (B * X) :=
  entIn_mul (J1 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => O_mul_latS hx hy) (fun i j => hB i j) hX

theorem entIn_mul_int {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (X * B) :=
  entIn_mul (J2 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => by rw [mul_comm]; exact O_mul_latS hy hx) hX
    (fun i j => hB i j)

end Fin

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerInCongruenceHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolOrb

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem stabilizer_in_congruence_holds : StabInCZ M δ u u' F0 what₂ :=
  Formalism.L2.SG.Pf.ZsVolIn.stabInCZ_of M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolLat.frameShape_holds M δ u u' F0 what₂)

theorem orbStabE_of_act (h : OrbActE M δ u u' F0 what₂) : Formalism.L2.SG.Pf.ZsVolCut.OrbStabE M δ u u' F0 what₂
    (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') :=
  orbStabE_of M δ u u' F0 what₂ (stabilizer_in_congruence_holds M δ u u' F0 what₂) h
    (Formalism.L2.SG.Pf.ZsVolFin.orbitFinite_holds M δ u u' F0 what₂)

end Formalism.L2.SG.Pf.ZsVolOrb

end
end

