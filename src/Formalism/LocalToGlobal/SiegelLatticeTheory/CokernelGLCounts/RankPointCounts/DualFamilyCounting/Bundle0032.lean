module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsPrescFamily
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PhiCountingHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantGroupCounts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsNearOfSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniformizerValuationHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXLeb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CardFilterLtInj
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem card_filter_lt_inj {n : ℕ} (P : Finset (Fin n)) {i k : Fin n} (hi : i ∈ P) (hk : k ∈ P)
    (e : (P.filter (· < i)).card = (P.filter (· < k)).card) : i = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : (P.filter (· < i)).card < (P.filter (· < k)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩
      · have := hsub (Finset.mem_filter.2 ⟨hi, h⟩)
        simp at this
    omega
  · have : (P.filter (· < k)).card < (P.filter (· < i)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩
      · have := hsub (Finset.mem_filter.2 ⟨hk, h⟩)
        simp at this
    omega

theorem card_filter_lt_lt {n : ℕ} (P : Finset (Fin n)) {i : Fin n} (hi : i ∈ P) :
    (P.filter (· < i)).card < P.card :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, hi, lt_irrefl i⟩)

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensEqZeroOfNotMem
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem algebraMap_mem_LO (c : F) (hc : c ∈ 𝒪[F]) : algebraMap F E c ∈ M.L.O := by
  rw [M.L.O_def]
  have h := isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨c, hc⟩)
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h
  exact h

theorem dens_eq_zero_of_not_mem (H : Loc.HermSp M V) (ϖ : 𝒪[F]) {abelian₂ : Submodule M.L.O V} (hSD : H.IsSelfDual abelian₂)
    {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E) (a b : ι) (hab : G₀ a b ∉ M.L.O) : H.dens ϖ abelian₂ G₀ = 0 := by
  unfold Loc.HermSp.dens
  have hE : IsEmpty {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} := by
    refine ⟨fun v => hab ?_⟩
    obtain ⟨hP, hG⟩ := v.2
    have h1 : H.h (v.1 b) (v.1 a) ∈ M.L.O := (hSD.2.2 (v.1 b)).1 (hP.1 b) (v.1 a) (hP.1 a)
    have h2 := hG a b
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
    have hϖ : algebraMap F E (ϖ : F) ∈ M.L.O := algebraMap_mem_LO _ ϖ.2
    have h3 : H.h (v.1 b) (v.1 a) - G₀ a b ∈ M.L.O := by
      rw [← hc]
      exact M.L.O.mul_mem c.2 hϖ
    have h4 : G₀ a b = H.h (v.1 b) (v.1 a) - (H.h (v.1 b) (v.1 a) - G₀ a b) := by ring
    rw [h4]
    exact M.L.O.sub_mem h1 h3
  have h0 : Set.range (fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
        fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)) = ∅ :=
    Set.range_eq_empty _
  rw [h0]
  simp

end Local

def GaPlusIntMM : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (∀ (p : PlF D) (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)),
          GaPlus M δ p (Tn u) (Tn u') Z a b ∈ (M p).L.O) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')

theorem notIntDens_of (h1 : LocSelfDual) (hG : GaPlusIntMM) : NotIntDens := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  by_contra hall
  push_neg at hall
  apply hI
  refine hG D δ M hA L u u' hT F0 what₂ hR Z F' hz hZ hP fun p a b => ?_
  by_contra hab
  exact hall p (dens_eq_zero_of_not_mem (L.H p) (ϖ p) (h1 D δ M hA L p) _ a b hab)

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensProdValOf
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem alpha_split' {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) {a b : ℕ} (hab : a ≤ b) :
    alphaStd K 𝔭 b = alphaStd K 𝔭 a *
      ∏ i ∈ Finset.Icc (a + 1) b, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ))) := by
  unfold alphaStd
  rw [← Finset.prod_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_Icc] at hi hi'
    omega

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiagonalFormCounting
section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.G5

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem alphaDisc_of (hP : PhiCount) (hKc : KerCount) (hD : DiscOnto) : AlphaDisc := by
  unfold AlphaDisc
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L hL hLi 𝔭 h𝔭 b a hJ
  have : Fact (IsFixF K F) := ⟨hF⟩
  have hk1 : 2 * vd h L 𝔭 + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have hk2 : 2 * vJof 𝔭 a + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have hk0 : 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have ha : ∀ i, a i ≠ 0 := hJ.2.2.2.2
  have hm : finrank K (⊤ : Submodule K V) = finrank K V := finrank_top K V
  have hlin : LinearIndependent K b :=
    Formalism.L2.SG.Pf.GluingBases.linearIndependent_orth h b hJ.2.2.1 (fun i => by
      rw [hJ.2.2.2.1 i]
      exact (map_ne_zero (algebraMap F K)).2 (by exact_mod_cast ha i))
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_span_eq_card hlin, Fintype.card_fin]
  have hfull : Submodule.IsFullLattice K L := by
    refine { toIsLattice := hL, span_eq_top := ?_ }
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Formalism.L2.SG.Pf.GluingBases.locF_subset_span h𝔭.isPrime L
    rw [← hJ.2.1]
    exact Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
  have hphi := hP K F hK 𝔭 h𝔭 _ a ha _ hk0 0 (by simp) (fun i j => by simp)
  have hfib : ∀ T : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
      (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)), Tᴴ = T →
      (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)))) →
      Nat.card {Y : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
        (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) //
          phiQ K 𝔭 (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) a Y = T} =
      Nat.card {Y : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
        (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) //
          phiQ K 𝔭 (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) a Y = 0} := by
    intro T hT hTm
    have h1 := hP K F hK 𝔭 h𝔭 _ a ha _ hk0 T hT hTm
    exact_mod_cast h1.trans hphi.symm
  have hker := hKc K F hK 𝔭 h𝔭 _ a ha _ hk2 _ hfib
  have hdisc := hD K F V hK h hs hd L hL hLi 𝔭 h𝔭 b a hJ _ hk2
  have hpos : (0 : ℝ) < Ideal.absNorm 𝔭 := by exact_mod_cast Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.absNorm_pos h𝔭
  have e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K (⊤ : Submodule K V) ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2) := by
    have h1 := congrArg (fun m : ℕ => (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1))) hm
    rw [h1]
    ring
  have e2 : finrank K (⊤ : Submodule K V) - cJof 𝔭 a = finrank K V - cJof 𝔭 a :=
    congrArg (fun x => x - cJof 𝔭 a) hm
  rw [Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hfull hLi h𝔭 hk1, hdisc, hker, Nat.cast_mul, hphi, e1, e2]
  have hne : (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2) ≠ 0 :=
    pow_ne_zero _ hpos.ne'
  field_simp

theorem alphaDisc_of_discOnto (hD : DiscOnto) : AlphaDisc :=
  alphaDisc_of Formalism.L2.SG.Pf.LocalizedFibreSets.phi_counting_holds
    (by
      unfold KerCount
      intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk N hN
      exact Formalism.L2.SG.Pf.discriminantGroupCounts.kerCount_main hK h𝔭 ha hk N hN) hD

end Formalism.L2.SG.Pf.G5
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualFLeOfInv
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.DualFormInverse

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_one {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p : ι} {α : K}
    (hα : α ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p := by
  refine ⟨fun t => if t = p then α else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    · exact hα
    · exact S.zero_mem
  · rw [Fintype.sum_eq_single p]
    · simp
    · intro t ht
      simp [ht]

theorem exists_two {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p q : ι} (hpq : p ≠ q)
    {α β : K} (hα : α ∈ S) (hβ : β ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p + β * g s q := by
  refine ⟨fun t => if t = p then α else if t = q then β else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    exacts [hα, hβ, S.zero_mem]
  · rw [Fintype.sum_eq_add p q hpq]
    · simp [hpq.symm]
    · rintro t ⟨h1, h2⟩
      simp [h1, h2]

theorem dualF_le_of_inv {ι : Type} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hnd : Nondeg h) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (G : ι → V)
    (hG : Submodule.span K (Set.range G) = ⊤)
    (hinv : ∀ u, ∃ κ : ι → K, (∀ t, κ t ∈ SP K 𝔭) ∧
      ∀ s, ∑ t, κ t * h (G s) (G t) = if s = u then 1 else 0) :
    dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range G))) ≤
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range G)) := by
  choose κ hκS hκ using hinv
  intro x hx
  have hX : ∀ u, h (G u) x ∈ SP K 𝔭 := fun u => by
    rw [mem_SP_iff_locF]
    exact hx (G u) (LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨u, rfl⟩))
  have hyx : ∀ s, h (G s) (x - ∑ t, (∑ u, κ u t * h (G u) x) • G t) = 0 := by
    intro s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [form_smul_right]
    have e : ∀ t, (∑ u, κ u t * h (G u) x) * h (G s) (G t) =
        ∑ u, h (G u) x * (κ u t * h (G s) (G t)) := fun t => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_comm]
    simp only [← Finset.mul_sum, hκ]
    simp
  have hxy := eq_zero_of_orth hs hnd G hG hyx
  rw [sub_eq_zero] at hxy
  rw [hxy]
  refine Submodule.sum_mem _ fun t _ => smul_mem_locF_of_SP ?_ (Submodule.subset_span ⟨t, rfl⟩)
  exact (SP K 𝔭).sum_mem fun u _ => (SP K 𝔭).mul_mem (hκS u t) (hX u)

end Formalism.L2.SG.Pf.DualFormInverse
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanIsometryHolds
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem jordanIsom_of (hE : ExactVec) (hR : Rebase) (hL : LocSpan) (hU : UnifVal)
    (hJ : JordSpan) : Formalism.L2.SG.Pf.Cnt.JordanIsom := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L L' hLl hLl' 𝔭 h𝔭 b a b' a' hb hb' hv
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  obtain ⟨π, hπ, hval⟩ := hU K F hK hF P hP
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨-, hbL, hbo, hbn, hba⟩ := hb
  obtain ⟨-, hbL', hbo', hbn', hba'⟩ := hb'
  have span_of_jordan (c : Fin (finrank K (⊤ : Submodule K V)) → V)
      (d : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F)
      (ho : ∀ i j, i ≠ j → h (c i) (c j) = 0)
      (hn : ∀ i, h (c i) (c i) = algebraMap F K ((d i : 𝓞 F) : F))
      (hd : ∀ i, d i ≠ 0) : Submodule.span K (Set.range c) = ⊤ := by
    have hi : LinearIndependent K c := LinearMap.linearIndependent_of_isOrthoᵢ ho (fun i => by
      rw [hn i]
      apply (map_ne_zero (algebraMap F K)).2
      intro hz
      apply hd i
      exact FaithfulSMul.algebraMap_injective (𝓞 F) F (by simpa using hz))
    apply hi.span_eq_top_of_card_eq_finrank'
    simp
  have hsp := span_of_jordan b a hbo hbn hba
  have hsp' := span_of_jordan b' a' hbo' hbn' hba'
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨g, hg, -, hgm⟩ := core_of_split hs hda
    (splitAt_of (hE K F V hK hF h hs hd P hP π hπ) (hR K V (locRing P) π h hS hπ hs hda))
    _ (Fin _) le_rfl b b' (fun i => vF _ (a i)) 1 hbo hbo'
    (fun i => by rw [hbn i]; exact hval _ (hba i))
    (fun i => by rw [hbn' i, hv i]; exact hval _ (hba' i)) (one_mem _)
    (fun v => by
      rw [hsp, hsp']
      exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  refine ⟨g, hg, gmap_eq_of_iff fun v => ?_⟩
  rw [← hbL, ← hbL', locF_eq_loc hK hF hP, locF_eq_loc hK hF hP, hL K F V hK hF P hP,
    hL K F V hK hF P hP]
  exact hgm v

end Formalism.L2.SG.Pf.G3

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_isometry_holds : JordanIsom :=
  Formalism.L2.SG.Pf.G3.jordanIsom_of Formalism.L2.SG.Pf.TemperedBoundGL3.exact_vector_holds Formalism.L2.SG.Pf.TemperedBoundGL3.rebasing_holds
    Formalism.L2.SG.Pf.G3.local_span_holds Formalism.L2.SG.Pf.TemperedBoundGL3.uniformizer_valuation_holds Formalism.L2.SG.Pf.G3.jordan_span_holds

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCR
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RefNBox : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u w : D.what₂.Word),
    (Measure.pi (refNX X u)) (LsNc5.boxN X w) =
      ENNReal.ofReal ((Tw w)⁻¹ ^ (D.R.rS * Fintype.card (InfinitePlace X.B.I.F)) *
        (2 : ℝ) ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * D.R.k + D.R.rS ^ 2)))

theorem refNX_haar {D : D7} (X : HidaSetting D) (u w : D.what₂.Word) :
    IsHaarOnSet X.B.I (X.NinfU w) (Measure.pi (refNX X u)) := by
  have hR := fun v : InfinitePlace X.B.I.F => refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v)
    (X.wfr u v) (ProductExactness.zV X u v) (ProductExactness.zV X w v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v)
    (fX_ww X u v) (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X w v)
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v => (hR v).1
  have hco : X.NinfU w = (ProductExactness.NinfG X w : Set X.B.I.Ginf) := (ProductExactness.NinfG_coe X w).symm
  refine ⟨inferInstance, ProductExactness.PiM.pi_ne_zero _ fun v => (hR v).2.1, ?_, ?_⟩
  · rw [hco, ProductExactness.NinfG, Subgroup.coe_pi]
    exact ProductExactness.PiM.pi_conc _ _ fun v => (hR v).2.2.1
  · intro g hg
    rw [hco] at hg
    exact ProductExactness.PiM.pi_map_mul_left _ g fun v => (hR v).2.2.2 (g v) (hg v (Set.mem_univ v))

theorem covol_refN (hN : LsNc5.CovolN) (hB : RefNBox) {D : D7} (X : HidaSetting D) (u w : D.what₂.Word)
    (FdN : Set X.B.I.Ginf) (hF : IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X w) FdN) :
    ((Measure.pi (refNX X u)) FdN).toReal = |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent D.R.rS D.R.k := by
  rw [hN D X w _ FdN (refNX_haar X u w) hF, hB X u w]
  set f := Fintype.card (InfinitePlace X.B.I.F) with hf
  set r := D.R.rS with hr
  set k := D.R.k with hk
  have hT : 0 < Tw (D := D) w := ProductExactness.Tw_pos w
  have hd : 0 < |(NumberField.discr X.B.I.F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have h2r : 2 * (r * (r - 1) / 2) + 2 * (r * (r + 1) / 2) = 2 * r ^ 2 := by
    have e1 : 2 * (r * (r - 1) / 2) = r * (r - 1) := Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
    have e2 : 2 * (r * (r + 1) / 2) = r * (r + 1) := Nat.mul_div_cancel' (Nat.even_mul_succ_self r).two_dvd
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      ring
  have hsum : r * (r - 1) / 2 + r * (r + 1) / 2 = r ^ 2 := by omega
  unfold LsNc5.covolN
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rw [show ((D.mem w).A.T : ℕ) = Tw (D := D) w from rfl]
  have hpow : (2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
      (2 : ℝ) ^ (f * (r * k + r ^ 2)) = 1 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← hsum]
    rw [show f * (r * k + (r * (r - 1) / 2 + r * (r + 1) / 2)) =
      f * (r * k + r * (r - 1) / 2) + f * (r * (r + 1) / 2) by ring, pow_add]
    have h1 : (0 : ℝ) < 2 ^ (f * (r * k + r * (r - 1) / 2)) := by positivity
    have h2 : (0 : ℝ) < 2 ^ (f * (r * (r + 1) / 2)) := by positivity
    field_simp
  have hTp : (Tw (D := D) w : ℝ) ^ (r * f) * (Tw (D := D) w)⁻¹ ^ (r * f) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hT.ne', one_pow]
  calc (Tw (D := D) w : ℝ) ^ (r * f) * (2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
        ((Tw (D := D) w)⁻¹ ^ (r * f) * (2 : ℝ) ^ (f * (r * k + r ^ 2)))
      = ((Tw (D := D) w : ℝ) ^ (r * f) * (Tw (D := D) w)⁻¹ ^ (r * f)) *
        ((2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
          (2 : ℝ) ^ (f * (r * k + r ^ 2))) * |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k := by ring
    _ = |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k := by rw [hTp, hpow, one_mul, one_mul]

theorem covolRef_of (hN : LsNc5.CovolN) (hB : RefNBox) : CovolRef := by
  delta CovolRef
  intro D X hb FdN FdN' u u' hH
  have hd : (0 : ℝ) < |(NumberField.discr X.B.I.F : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  rw [covol_refN hN hB X u _ FdN hH.2.2.1,
    covol_refN hN hB X u _ FdN' (by first | exact hH.2.2.2.1 | exact hH.2.2.2), ← Real.rpow_add hd]
  congr 1
  delta eDF LsNc5.covolumeExponent
  ring

theorem covolRef_of_steps (hC : LsNc5.CoordCovol) (hB : RefNBox) : CovolRef :=
  covolRef_of (covolN_of_coordCovol hC) hB

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdFull
section
namespace Formalism.L2.SG.Pf.NcVal

theorem volOrdV_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : VolOrdV X u u' ψ :=
  volOrdV_of X u u' ψ Formalism.L2.SG.Pf.conductor_inverse_different

end Formalism.L2.SG.Pf.NcVal
end

