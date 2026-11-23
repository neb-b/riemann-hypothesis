module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0082
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LevelClauseAdaptedBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0009
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0038
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSIdx
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)

theorem comp_set_conjugated_level_eq : compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 =
    (fun z => PIW.MassDataColumns.xuP X hb u p * z * (PIW.MassDataColumns.xuP X hb u p)⁻¹) '' MassDataIdxSteps.KppX X hb p := by
  unfold MassDataIdxSteps.KppX compSet K2u
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr fun y _ => ?_
  simp only [map_mul, map_inv]

theorem mem_compSet_iff (x : PIW.MassDataColumns.KvH X u p.1) :
    ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
        compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ↔
      x ∈ (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
  rw [PIW.MassDataColumns.mem_K2Hp_iff X hb (Formalism.L2.SG.Closed.level_subgroup_is_group X) (Formalism.L2.SG.Closed.level_subgroup_properties X) u p x,
    comp_set_conjugated_level_eq]
  constructor
  · rintro ⟨z, hz, hzx⟩
    rw [← hzx]
    simpa [mul_assoc] using hz
  · intro h
    exact ⟨_, h, by group⟩

theorem idxHp_eq : MassDataLevelSSteps.idxHp X hb u p = PIW.MassDataColumns.lIdxH X hb u p := by
  have hKv : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 ↔ y ∈ PIW.MassDataColumns.KvH X u p.1 :=
    fun y => Iff.rfl
  have hC2 : Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = PIW.MassDataColumns.KvH X u p.1 := by
    have e : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = (PIW.MassDataColumns.KvH X u p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
      Set.ext hKv
    rw [e, Subgroup.closure_eq]
  have hS : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 →
      y ∈ PIW.MassDataColumns.KvH X u p.1 ∧ y ∈ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 := by
    intro y hy
    have hyK : y ∈ PIW.MassDataColumns.KvH X u p.1 :=
      (hKv y).1 ((level_compression_chain (X := X) (hb := hb) (p := p) u).2 hy)
    refine ⟨hyK, ?_⟩
    exact Subgroup.mem_subgroupOf.1 ((mem_compSet_iff X hb u p ⟨y, hyK⟩).1 hy)
  have hinf : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ⊓ PIW.MassDataColumns.KvH X u p.1 =
      PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 ⊓ PIW.MassDataColumns.KvH X u p.1 := by
    have hle : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≤ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 :=
      (Subgroup.closure_le _).2 fun y hy => (hS y hy).2
    refine le_antisymm (inf_le_inf_right _ hle) ?_
    rintro y ⟨hy2, hyK⟩
    refine ⟨Subgroup.subset_closure ?_, hyK⟩
    exact (mem_compSet_iff X hb u p ⟨y, hyK⟩).2 (Subgroup.mem_subgroupOf.2 hy2)
  have hsub : (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)))).subgroupOf
      (PIW.MassDataColumns.KvH X u p.1) =
      (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    have h1 := SetLike.ext_iff.1 hinf (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))
    simp only [Subgroup.mem_inf] at h1
    exact ⟨fun h => (h1.1 ⟨h, x.2⟩).1, fun h => (h1.2 ⟨h, x.2⟩).1⟩
  unfold MassDataLevelSSteps.idxHp PIW.MassDataColumns.lIdxH
  rw [hC2]
  exact congrArg Subgroup.index hsub

theorem sTypIdx_holds : STypIdx := by
  intro D X hb u p hT _
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have h1 := MassDataLevelSSteps.haarIdxLoc_holds X hb hK hT hL u p
  rw [MassDataLevelSSteps.locLevi_holds X hb hK hT hL u p, idxHp_eq X hb u p] at h1
  obtain ⟨ρ, hs, hk, hc⟩ := (PIW.MassDataColumns.locRedH_of_rest (PIW.MassDataColumns.locRedRest_of_models
    (PIW.MassDataColumns.hModelAll_of (PIW.MassDataColumns.hAdaptAll_of PIW.MassDataColumns.adapted_basis_every_place)
      PIW.MassDataColumns.level_clause_adapted_basis))) X hb hK u hT hL p
  rw [PIW.MassDataColumns.lIdxH_eq_of_red X hb u p ρ hs hk hc] at h1
  exact h1

theorem typedAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := typedAll_of_idx sTypIdx_holds

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdSPow
section
noncomputable section

open scoped Classical Matrix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_ddS_pow (t : 𝓞 D.host.F) (ht : t ∈ differentIdeal ℤ (𝓞 D.host.F)) (k : ℕ) :
    (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ k : 𝓞 D.host.E) : D.host.E) ∈ ddS D ^ k := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈
      Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :=
    Ideal.mem_map_of_mem _ ht
  have h2 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) ∈ ddS D :=
    FractionalIdeal.mem_coeIdeal_of_mem _ h1
  have h3 := Submodule.pow_mem_pow (ddS D : Submodule (𝓞 D.host.E) D.host.E) h2 k
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
  push_cast
  exact h3

theorem dict_holds (Zd : LocDat D) : Formalism.L2.SG.Pf.TupGlob.Dict Zd := by
  intro A B hA hB hloc
  have hAu : IsLoUni A := fun i j => ⟨hA.2 i j, fun h => h ▸ hA.1 i⟩
  have hBu : IsUpUni B := Formalism.L2.SG.Pf.TupGlob.isUpUni_of hB
  have hsh : ∀ p, Formalism.L2.SG.Pf.StabIntSh.LocEntryShape D p A B := fun p =>
    (Formalism.L2.SG.Pf.StabIntSh.loc_iff Formalism.L2.SG.Pf.StabIntSh.locShapeL Formalism.L2.SG.Pf.StabIntSh.locShapeG (p := p)
      Zd.agree hAu hBu).1
      ⟨by rw [lOf_eq]; exact (hloc p).1, by rw [ρOf_eq]; exact Formalism.L2.SG.Pf.FibQ.sgn_conj_intUp Zd p (hloc p).2⟩
  have hES := (Formalism.L2.SG.Pf.StabIntSh.glob_iff Formalism.L2.SG.Pf.StabIntSh.locGlob Formalism.L2.SG.Pf.StabIntSh.shapeNZ A B).1 hsh
  refine ⟨fun c b hcb x hx => ?_, fun c b hcb x hx => ?_, fun P hP c b => ?_⟩
  · rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF]
    exact mem_aaF hcb hx (ddPow_conj Zd (by have := b.isLt; omega) (hES b c hcb).1)
  · rw [sg_entry]
    exact mem_aaF hcb hx (hES b c hcb).2.1
  · rcases lt_trichotomy c b with h | h | h
    · have hq := (hES b c h).2.2
      unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at hq
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hq
      obtain ⟨z, hz, hzy⟩ := hq
      obtain ⟨t, ht, htP⟩ := diff_avoid P hP
      have hk : b.val - c.val ≤ D.R.rS := by have := b.isLt; omega
      have hz' := ddPow_conj Zd hk hz
      have hprod := FractionalIdeal.mul_mem_mul (mem_ddS_pow t ht (b.val - c.val)) hz'
      unfold Formalism.L2.SG.Pf.StabIntSh.ddPow at hprod
      rw [← zpow_natCast, ← zpow_add₀ (PI.NRCW.ddS_ne_zero D), add_neg_cancel, zpow_zero] at hprod
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
      refine ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ (b.val - c.val), fun hs => htP (P.isPrime.mem_of_pow_mem _ hs),
        o, ?_⟩
      rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, sg_entry]
      have e1 : D.conjF (A b c) - Formalism.L2.SG.Pf.StabIntSh.bt D B c b =
          D.conjF (algebraMap (𝓞 D.host.E) D.host.E ((gS D : ℕ) : 𝓞 D.host.E) * z) := by
        have := congrArg D.conjF hzy
        simpa only [map_sub, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol] using this
      rw [e1, map_mul, map_natCast, map_natCast, mul_left_comm, ← ho]
    · subst h
      refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.1 c, hB.1 c, ← pow_add, ← two_mul, pow_mul]
    · refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.2 b c h, hB.2 b c h]

end Formalism.L2.SG.Pf.FibD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemROf
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem comp_mem {x : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O) :
    (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(Z.M p).L.O_def] at hx
  have h := hx.map (g.e.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])
  have h1 := h.map ((AlgHom.fst (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])
  have h2 := h.map ((AlgHom.snd (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])
  exact ⟨PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h1, PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h2⟩

theorem mem_R_of (hs : (Z.M p).split = some g) {x : (D.s.atP p).Ep}
    (h1 : (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp]) (h2 : (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp])
    (h3 : ∃ o ∈ 𝒪[(D.s.atP p).Fp], (g.e x).1 - (g.e x).2 = (g.q : (D.s.atP p).Fp) * o) : x ∈ (Z.M p).R := by
  unfold Formalism.MainNotions.S.Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  refine ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, ?_⟩
  · simp only [RingHom.mem_eqLocus, RingHom.comp_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨o, ho, he⟩ := h3
    refine ⟨⟨o, ho⟩, ?_⟩
    apply Subtype.ext
    show o * (g.q : (D.s.atP p).Fp) = (g.e x).1 - (g.e x).2
    rw [he, mul_comm]
  · rfl

def emap (Y : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => g.e.symm ((g.e (Y a b)).1 / (g.q : (D.s.atP p).Fp), -((g.e (Y b a)).2 / (g.q : (D.s.atP p).Fp)))

def lmat (l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => g.e.symm ((g.e (l a b)).1, (g.e (ρ b a)).2)

theorem emap_mul (l Y ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    emap Z p g (l * Y * ρ) = lmat Z p g l ρ * emap Z p g Y * lmat Z p g ρ l := by
  ext a b
  apply g.e.injective
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [emap, lmat, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, AlgEquiv.apply_symm_apply]
  ext
  · simp only [Prod.fst_sum, Prod.fst_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  · simp only [Prod.snd_sum, Prod.snd_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_div, neg_div,
      ← Finset.sum_neg_distrib, mul_neg, neg_mul]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)
    ring

end Split

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OmegaHermitianZ
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')

theorem GZ_eq : GZ F.fvec F'.fvec = Zhat F F' := by
  ext a b; rfl

theorem GDl_eq (l : ℕ) : GDl F.fvec F'.fvec l = Dl F F' l := by
  unfold GDl Dl leadMinorE
  rw [GZ_eq]

theorem om_X' {y : (VS D).V} (hy : y ∈ F'.X) : (VS D).hT (Gom F.fvec F'.fvec) y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, ← fvec_cs F' i, om_pair, if_neg (Fin.castSucc_ne_last i), smul_zero]

theorem omega_hermitian_z : (VS D).hT (Gom F.fvec F'.fvec) F'.z = GDl F.fvec F'.fvec (D.R.rS + 1) := by
  rw [← fvec_last F', om_pair, if_pos rfl]

theorem f_om (a : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (Gom F.fvec F'.fvec) =
      if a = Fin.last D.R.rS then star ((GZ F.fvec F'.fvec).adjugate (Fin.last _) (Fin.last _)) * -T else 0 := by
  unfold Gom
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul, hff]
  rw [Finset.sum_eq_single (Fin.last D.R.rS)]
  · by_cases ha : a = Fin.last D.R.rS
    · rw [if_pos ⟨ha, rfl⟩, if_pos ha]
    · rw [if_neg (fun h => ha h.1), if_neg ha, mul_zero]
  · intro b _ hb
    rw [if_neg (fun h => hb h.2), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem om_om : (VS D).hT (Gom F.fvec F'.fvec) (Gom F.fvec F'.fvec) =
    -T * (GDl F.fvec F'.fvec D.R.rS * star (GDl F.fvec F'.fvec D.R.rS)) := by
  have e : (VS D).hT (Gom F.fvec F'.fvec) (Gom F.fvec F'.fvec) =
      ∑ a, (GZ F.fvec F'.fvec).adjugate (Fin.last _) a * (VS D).hT (F.fvec a) (Gom F.fvec F'.fvec) := by
    conv_lhs => arg 1; unfold Gom
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  rw [e, Finset.sum_eq_single (Fin.last D.R.rS)]
  · rw [f_om, if_pos rfl, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r']
    ring
  · intro b _ hb
    rw [f_om, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem om_uniq (hdet : GDl F.fvec F'.fvec (D.R.rS + 1) ≠ 0) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range F.fvec)) (hxX : ∀ y ∈ F'.X, (VS D).hT y x = 0) :
    ∃ c : D.host.E, x = c • Gom F.fvec F'.fvec := by
  set c : D.host.E := star ((VS D).hT x F'.z / GDl F.fvec F'.fvec (D.R.rS + 1)) with hc
  refine ⟨c, sub_eq_zero.1 (eq_zero_of_orth_of_det_ne_zero F.fvec F'.fvec hdet
    (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (Gom_mem _ _))) fun b => ?_)⟩
  rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, om_pair]
  induction b using Fin.lastCases with
  | last =>
    rw [if_pos rfl, fvec_last, hc, star_star, div_mul_cancel₀ _ hdet, sub_self]
  | cast i =>
    rw [if_neg (Fin.castSucc_ne_last i), mul_zero, sub_zero, fvec_cs, hsw',
      hxX _ (Submodule.subset_span ⟨i, rfl⟩), star_zero]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.RootPatterns

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.RealConjugatorData

variable {D : D7}

theorem blockIdx_loc (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) :
    ∀ (bs : List (D.host.E × ℕ)) (a i : ℕ), blockIdx (locBlocksFrom D ρ v a bs) i = Formalism.L2.SG.RealObj.blkOf bs i
  | [], _, _ => rfl
  | (t, s) :: bs, a, i => by
    simp only [locBlocksFrom, blockIdx, Formalism.L2.SG.RealObj.blkOf]
    split_ifs
    · rfl
    · rw [blockIdx_loc ρ v bs (a + s) (i - s), add_comm]

theorem mem_rootPat_iff (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) (q : Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :
    q ∈ rootPat (ptLoc D τ w) ↔ q.1 < q.2 ∧ Formalism.L2.SG.RealObj.blkOf w.1 q.1.1 = Formalism.L2.SG.RealObj.blkOf w.1 q.2.1 := by
  simp only [rootPat, ptLoc, ptLocS, locBlocks, Set.mem_setOf_eq, blockIdx_loc]
  simp [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ]

def idxF (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) : ↥(rootPat (ptLoc D τ w)) ≃ Formalism.L2.SG.RealObj.FreeE w where
  toFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).1 q.2⟩
  invFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).2 q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rootCoords_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z p) := by
  unfold Formalism.MainNotions.S.rootCoords
  refine continuous_pi (fun q => ?_)
  unfold flagMat
  first
    | fun_prop
    | (simp only [Matrix.mul_apply, Matrix.of_apply]; fun_prop)
    | continuity
    | (exact ((continuous_apply _).comp (continuous_apply _)).comp
        (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const))

variable {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

theorem stCoordV_comp :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) =
      (MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)) ∘
        rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ cMr C γ τ := by
  funext y q
  have ha : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega
  have hpc : ∀ x : ↥(rootPat (ptLoc D τ w)) → ℂ,
      MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w) x q = x ((idxF τ w).symm q) :=
    fun x => by simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp only [Function.comp_apply]
  rw [hpc, Formalism.L2.SG.RealFrameCoordinates.stCoordV_eq C u' w γ τ y q]
  unfold rootCoords flagMat
  rw [dite_eq_left (show ((idxF τ w).symm q).1.1.val < D.R.rS from ha), ← cMr_eq]
  rfl


include C in
theorem place (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) (hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) :
    ∃ (μ : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) (c : ℝ≥0∞),
      Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) μ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
        μ.map (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) =
          c • Measure.pi (fun _ : Formalism.L2.SG.RealObj.FreeE w => (volume : Measure ℂ)) := by
  obtain ⟨hzW, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hzW', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => by
    unfold Tr
    exact Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg0 : Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  obtain ⟨μ₀, c, hHaar, hc0, hctop, hmap⟩ := hLoc D.R.k D.R.rS hk _ _ hzW (by rw [hTz]; exact hT u) hzW'
    (by rw [hTz']; exact hT u') (ptLoc D τ w) _ hg0 (Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point C u u' w γ hrep τ)
  have hemb := cMr_measEmb C γ τ
  set μ := Measure.comap (cMr C γ τ) μ₀ with hμ
  have hconc : μ₀ (Set.range (cMr C γ τ))ᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) hHaar.2.2.1
    intro hR
    exact hx (rset_range C γ τ x hR)
  have hres : μ₀.restrict (Set.range (cMr C γ τ)) = μ₀ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hconc)
  have hmapc : μ.map (cMr C γ τ) = μ₀ := by rw [hμ, hemb.map_comap, hres]
  have : SigmaFinite μ₀ := hHaar.1
  refine ⟨μ, c, ⟨?_, ?_, ?_, fun s hs => ?_⟩, hc0, hctop, ?_⟩
  · exact SigmaFinite.of_map μ hemb.measurable.aemeasurable (by rw [hmapc]; infer_instance)
  · intro h0
    apply hHaar.2.1
    rw [← hmapc, h0, Measure.map_zero]
  · rw [hμ, hemb.comap_apply]
    refine measure_mono_null ?_ hHaar.2.2.1
    rintro _ ⟨y, hy, rfl⟩ hR
    exact hy ((stV_iff C γ τ u u' y).2 hR)
  · have hs0 := (stV_iff C γ τ u u' s).1 hs
    have hfun : cMr C γ τ ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (cMr C γ τ s) ∘ cMr C γ τ := by
      funext x
      obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
      show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat (s * x) * (uMat (γ (vOf X τ)) * C.Q τ) =
        (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * (uMat (γ (vOf X τ)) * C.Q τ)) *
          (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat x * (uMat (γ (vOf X τ)) * C.Q τ))
      rw [show uMat (s * x) = uMat s * uMat x from rfl]
      calc C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * (uMat s * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ)
          = C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * ((uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) *
              (uMat (γ (vOf X τ)))⁻¹) * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ) := by
            rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.one_mul]
            simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hmeas_s : Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => s * x) := measurable_const_mul s
    have hmeas_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) (cMr C γ τ s)) := by
      refine Continuous.measurable ?_
      unfold Formalism.QuantumDeterminants.lmulM
      refine Continuous.matrix_mul continuous_const ?_
      exact continuous_id
    have key : (μ.map (fun x => s * x)).map (cMr C γ τ) = μ.map (cMr C γ τ) := by
      rw [Measure.map_map hemb.measurable hmeas_s, hfun, ← Measure.map_map hmeas_l hemb.measurable, hmapc]
      exact hHaar.2.2.2 _ hs0
    calc μ.map (fun x => s * x) = (((μ.map (fun x => s * x)).map (cMr C γ τ))).comap (cMr C γ τ) :=
          (hemb.comap_map _).symm
      _ = μ := by rw [key, hemb.comap_map]
  · rw [stCoordV_comp C u' w γ τ, ← Measure.map_map (MeasurableEquiv.piCongrLeft _ _).measurable
      ((rootCoords_cont _ _ _ _).measurable.comp hemb.measurable),
      ← Measure.map_map (rootCoords_cont _ _ _ _).measurable hemb.measurable, hmapc, hmap, Measure.map_smul,
      (volume_measurePreserving_piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)).map_eq]
    · rfl
    · exact (MeasurableEquiv.piCongrLeft _ _).measurable.aemeasurable

theorem placeHaar_of_loc (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) : Formalism.L2.SG.NGPin.PlaceHaar := by
  intro D X u u' w γ hrep v
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  exact place C u u' w γ τ hLoc hrep

end Formalism.L2.SG.RootPatterns

end
end

