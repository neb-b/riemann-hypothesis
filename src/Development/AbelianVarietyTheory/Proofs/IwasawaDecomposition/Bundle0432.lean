module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle0026
public import Formalism.LocalToGlobal.Columns.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullHermitianColumnsTrueColumns
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E)))

theorem mem_integralNormOne_of_normOneDetClass_eq_one (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (h : u1Dt H SQ x = 1) :
    x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H) := by
  obtain ⟨a, ha⟩ := exists_lift H x
  have e : (QuotientGroup.mk a : DtQ H SQ) = 1 := (normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha).symm.trans h
  have ha' : a ∈ KDq H SQ := (QuotientGroup.eq_one_iff a).1 e
  refine (_root_.GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val R H x a ha).2 fun w => ?_
  exact (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).1 (Subgroup.mem_sup_left (KDq_le_KD H SQ ha')) w (conjPrime₂ w)
    ((isConjPl_iff H w _).2 rfl)

theorem unitIdeleImage_eq_map_integralNormOne : UOQ H SQ = ((Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)).subgroupOf (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))).map (u1Dt H SQ) := by
  ext t
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := exists_of_idele H a
    refine ⟨x, ?_, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩
    refine (_root_.GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val R H x a hx).2 fun w => ?_
    exact (ha w).trans (ha (conjPrime₂ w)).symm
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := exists_lift H x
    rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, mk_mem_UOQ, KDq_sup_unitIdl]
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).2 fun w w' hw => ?_
    rw [(isConjPl_iff H w w').1 hw]
    exact (_root_.GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val R H x a ha).1 hx w

end Gen

section Main

open Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem detPt_of_reads (hI : I.Ok) (u : B.Word) (i : ℕ) {Ch : Type} {chOf : (I.stp u I.mu0 i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u I.mu0 i chOf Lb U chi y st k) (c : (I.stp u I.mu0 i).Cl)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det (y c)) :
    detPt B.host I.SQ ((I.stp u I.mu0 i).rep c).1.1 = u1Dt B.host I.SQ x := by
  obtain ⟨p, hp, hN⟩ := hR.k_std (chOf c)
  refine GlobalTheory.T.pointDeterminant_eq_normOneClass_of_level B.R B.host _ _ _ _ I.SQ _ (y c) (k (chOf c)) x (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1 (hR.pt c) hp.uni
    (hN ▸ hp.lat) (fun P hP => ?_) hx
  refine hR.k_off _ _ (_root_.GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P hP) ?_ (Or.inl rfl)
  rintro ⟨Q, hQ, -⟩
  rw [_root_.GlobalTheory.Mem.Col2.RefTup.twistPrimes_reference_tuple_eq_empty B X I] at hQ
  exact absurd hQ (Finset.notMem_empty Q)

theorem det_reGL {a b : ℕ} (h : a = b) {A : Type} [CommRing A] (g : GL (Fin a) A) :
    Matrix.GeneralLinearGroup.det (reGL h A g) = Matrix.GeneralLinearGroup.det g := by
  subst h
  refine Units.ext ?_
  simp [reGL, Matrix.GeneralLinearGroup.det]

variable (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : ColsTiedSym (I.rec7 l Z))


include I in
theorem det_normOne_classStepZero_trueColumns (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (c : ((I.rec7 l Z).mem u).C.cls 0)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det ((C.herm.base.lev0 u).y c).1) :
    (I.rec7 l Z).detCls u 0 c = u1Dt B.host I.SQ x := by
  obtain ⟨k, hk⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  refine detPt_of_reads I hI u 0 hk c x ?_
  have e := (C.car0 u).y_eq c
  rw [hx]
  exact (e ▸ det_reGL _ _).symm


include I in
theorem detI_std (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ B.R.m)
    (c : ((I.rec7 l Z).mem u).C.cls i) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det
      ((C.herm.base.cls u i h1 hm (C.herm.base.chOf u i c)).y ⟨c, rfl⟩).1) :
    (I.rec7 l Z).detCls u i c = u1Dt B.host I.SQ x := by
  by_cases h2 : i + 1 ≤ B.R.m
  · obtain ⟨k, hk⟩ := (hS u).mid i h1 h2
    refine detPt_of_reads I hI u i hk c x ?_
    have e := (C.carC u i h1 h2 (C.herm.base.chOf u i c)).y_eq ⟨c, rfl⟩
    rw [hx]
    exact (e ▸ det_reGL _ _).symm
  · obtain rfl : i = B.R.m := by omega
    obtain ⟨k, hk⟩ := (hS u).ends B.R.m le_rfl (Or.inr rfl)
    refine detPt_of_reads I hI u _ hk c x ?_
    have e := (C.carM u).y_eq c
    have key : ∀ (β : C.herm.base.Ch u B.R.m) (hb : C.herm.base.chOf u B.R.m c = β),
        Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm β).y ⟨c, hb⟩).1 =
          Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm (C.herm.base.chOf u B.R.m c)).y ⟨c, rfl⟩).1 := by
      rintro _ rfl
      rfl
    rw [hx, ← key _ (chOf_m C.herm.base u c)]
    exact (e ▸ det_reGL _ _).symm

def hermS (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricHermitianColumns (I.rec7 l Z) :=
  { C.herm.base with
    dt := u1Dt B.host I.SQ
    dt_surj := normOneFiniteAdeleDetClass_surjective B.host I.SQ
    dt_ker := mem_integralNormOne_of_normOneDetClass_eq_one B.host I.SQ
    dt_open := GlobalTheory.T.isOpen_ker_normOneFiniteAdeleDetClass B.R B.host _ I.SQ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1
    dt_UO := unitIdeleImage_eq_map_integralNormOne B.host I.SQ
    dt_rat := fun z x h => _root_.GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq B.R B.host I.SQ z x h
    det0 := fun u c x h => det_normOne_classStepZero_trueColumns I l Z C hI hS u c x h
    detI := fun u i h1 hm c x h => detI_std I l Z C hI hS u i h1 hm c x h }

theorem relDet_std (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricRelativeDeterminant (I.rec7 l Z) (hermS I l Z C hI hS) := by
  intro N L L' g _ hg x hx
  obtain ⟨idl, hp⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by ext t; exact ⟨fun h => ⟨t, h, rfl⟩, fun ⟨_, h, e⟩ => e ▸ h⟩) (fun _ => rfl)
    (fun N L L' t h => h)
  exact GlobalTheory.Mem.NormOneIdeal.relDet_eq_of_pinned (I.rec7 l Z) idl hp _ (hermS I l Z C hI hS).dt (hermS I l Z C hI hS).dt_ker
    (hermS I l Z C hI hS).dt_UO (hermS I l Z C hI hS).dt_rat L L' g x hg hx

theorem exists_colsFullS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (C : ColsTiedSym (I.rec7 l Z)) (g : Formalism.L2.Herm.SymmetricGroupCompatibility (I.rec7 l Z) C.herm.base), I.StdC l Z C → Formalism.L2.Herm.VolumeCompatible (I.rec7 l Z) → ∃ Fu : ColsFullS C, HEq Fu.1.g g ∧ I.StdDt l Z Fu.1.base.dt := by
  intro B X I hI _ l Z C g hS hV
  let Fu : Formalism.L2.Herm.FullTiedS (I.rec7 l Z) :=
    { base := hermS I l Z C hI hS
      atT := C.herm.atT
      vol := hV
      levelZeroCompatibility := C.herm.levelZeroCompatibility
      g := g
      ad := C.herm.ad
      cof := C.herm.cof
      piG := C.herm.piG
      stabMap := C.herm.stabMap
      fvI := C.herm.fvI
      relDet := relDet_std I l Z C hI hS
      std := C.herm.std
      vpos := B.V_pos
      baseL := C.herm.baseL }
  refine ⟨⟨Fu, rfl⟩, HEq.rfl, ?_⟩
  intro x a ha
  exact normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x a ha

end Main

end GlobalTheory.Mem.Col2.FullDt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertHeckeDoubleCosetOperatorsLifts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.InertTie

theorem conj_symm_apply {K M N : Type} [CommSemiring K] [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (e : M ≃ₗ[K] N) (T : Module.End K M) (x : N) : e.symm (e.conj T x) = T (e.symm x) := by
  simp [LinearEquiv.conj_apply]

theorem opEq (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X))
    (P : LiftBrg.PresL X I hX U Xg tr L cV i t) (hP : LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P)
    (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (R : Finset (Bridge.Gf (Vc X.toD7 i)))
    (hN : ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet (E := X.toD7.host.E) (n := X.B.R.nV) (ST := ∅) (SG := LiftBrg.sgL X I U t) → M)
        (g : Bridge.Gf (Vc X.toD7 i)),
        ∑ a ∈ R, ψ (LiftBrg.ptL X I U i t A k (g * a)) =
          ∑ e ∈ (LiftBrg.ptL X I U i t A k g).inertNb ((q.1.1 : PlI X.B px).1).asIdeal q.2, ψ e)
    (f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
    P.ext ((((famR X I hX U Xg tr).heckeLI i t q f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
        ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) =
      Bridge.dcOp R (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
  funext g
  rw [hP]
  unfold Bridge.dcOp
  rw [Finset.sum_congr rfl (fun a _ => hP f (g * a))]
  rw [hN _ (fun e => P.coef ((((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f).1 e)) g]
  refine (congrArg P.coef ?_).trans (map_sum P.coef _ _)
  change (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm
        (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).conj
        (Formalism.L2.Col.heckeFamI (formPts _ _) ∅ (offSubI.lev q.1, q.2)) f)).1 _ = _
  erw [conj_symm_apply]
  erw [Formalism.L2.Col.heckeI_op_apply]
  unfold Formalism.L2.Col.DecoPts.nbI
  simp [formPts]
  rfl

theorem exists_inertTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).heckeLI i t)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
      (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
      fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hF P hR
  classical
  have hN := fun (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ)
      (hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2) =>
    GlobalTheory.T.inertNeighbours_lifts_doubleCoset_translates X px I hX U Xg tr L eG hI hV hL hG cV i t A k hF q hq
  exact ⟨{
    hx := fun q => if hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 then (hN q hq).choose else 1
    hA := fun q => if hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 then (hN q hq).choose_spec.choose else ∅
    hx_ok := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.1
    hA_loc := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.1
    chi_loc := fun q _ j hj => GlobalTheory.T.levelChar_eq_one_inert_prime_off_level X px I hX U Xg tr L eG hI hV hL hG cV i t q j hj
    hDC := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.2.1
    op_eq := fun q hq f => by
      simp only [dif_pos hq]
      exact opEq X I hX U Xg tr L cV i t A k P hR q _ (hN q hq).choose_spec.choose_spec.2.2.2 f }⟩

end GlobalTheory.Mem.R3.LiftBrg.InertTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilDatumOOfRankEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilOriented

theorem exists_isWeilDatumO_of_rank_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), AdmE V W χ χ' → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  intro D ψ hψ V W χ χ' om ha hw
  have hr : V.rank ≤ W.rank := ha.1.le
  obtain ⟨e, hc, hcs, he, hrat, hsm, hheis, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr
  let E : (WA V W → ℂ) ≃ₗ[ℂ] (WO V W → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.toEquiv
  obtain ⟨omO, hom⟩ := exists_extend (ThS ψ V W) E om
  have hom' : ∀ p (Φ : ThS ψ V W), omO p (fun x => Φ.1 (e x)) = fun x => (om p Φ).1 (e x) := hom
  have hsurj : ∀ f, IsThetaFunO ψ V W f → ∃ Φ : ThS ψ V W, f = fun x => Φ.1 (e x) := fun f hf => by
    have e1 : f = fun x => (fun y => f (e.symm y)) (e x) := by funext x; simp
    refine ⟨⟨fun y => f (e.symm y), mem_ThS.2 ((hth ψ _).1 ?_)⟩, e1⟩
    rw [← e1]; exact hf
  have hTh : ∀ Φ : ThS ψ V W, IsThetaFunO ψ V W fun x => Φ.1 (e x) := fun Φ => (hth ψ _).2 (mem_ThS.1 Φ.2)
  have hact : ∀ g h x, e (actO V W g h x) = actHom V W g h (e x) := fun g h x => by
    rw [he, he]; exact (GlobalTheory.OrientedSmall.bridgeSmall D V W hr).2 g h x
  refine ⟨omO, ⟨hψ, ha.2.1.1, ha.2.2.1.1, ha.2.2.2.1, ha.2.2.2.2, fun p f hf => ?_, fun g h w₀ f hf => ?_,
    fun γ hγ γ' hγ' f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_,
    fun ε hε g h hg hh x y hx hy => ?_⟩, fun p Φ => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']; exact hTh _
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    let Φ' : ThS ψ V W := ⟨Heisenberg₂ ψ V W (e w₀) Φ.1,
      mem_ThS.2 (GlobalTheory.Mem.ThetaClosed.isThetaFun_heis hψ (mem_ThS.1 Φ.2) _)⟩
    rw [hheis, hom', hheis, hact, ← hw.Heisenberg₂ g h (e w₀) Φ Φ' rfl]
    exact hom' _ Φ'
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    simp only [map_zero]
    exact hw.aut γ hγ γ' hγ' Φ
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    simp only [hom']
    exact hw.cont Φ (e w)
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨j1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D V W
    have : BorelSpace (WA V W) := ⟨rfl⟩
    have : BorelSpace (WO V W) := ⟨rfl⟩
    obtain ⟨ν, hν, hF, hint⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WO V W) e.symm hcs
      (by simpa using hc) (ratL V W) (ratL W V) (fun x => by rw [← hrat, e.apply_symm_apply]) μ 𝓕 hμ h𝓕
    refine lintegral_eq_of_integral_eq (ratL W V) hK hcov (hTh _).cont (hTh _).cont (norm_periodic hψ (hTh _))
      (norm_periodic hψ (hTh _)) hμ h𝓕 ?_
    rw [← hint, ← hint]
    simp only [e.apply_symm_apply]
    exact hw.unit ν _ hν hF p Φ
  · obtain ⟨r, hr0, hℓ⟩ := hw.split ε hε g h hg hh x y hx hy
    refine ⟨r, hr0, fun ℓ hinv f hf => ?_⟩
    obtain ⟨Φ, rfl⟩ := hsurj f hf
    have := hℓ (ℓ ∘ₗ E.toLinearMap ∘ₗ (ThS ψ V W).subtype) (fun u hu Ψ Ψ' hΨ => ?_) Φ
    · rw [hom']
      unfold splitFac at this
      rw [if_pos hr] at this
      exact this
    · have hu' : cA D ε • e.symm u = e.symm u := by
        apply e.injective
        rw [hsm, e.apply_symm_apply]
        exact Matrix.ext hu
      have := hinv (e.symm u) (fun i j => congrFun (congrFun hu' i) j) _ (hTh Ψ)
      rw [hheis, e.apply_symm_apply, ← hΨ] at this
      exact this
  · simp only [← he]
    exact hom' p Φ

end GlobalTheory.Mem.WeilOriented
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.TupChar

theorem chrEq_mul {D : D7} {c c' : IdC D} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => (congrArg₂ (· * ·) (h.1.2 x) (h'.1.2 x)).trans (mul_one _)⟩,
    fun P e he k x hx => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
  rfl

theorem unramEverywhere {D : D7} {c : IdC D} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hu : ∀ P, χ.UnrAt P) :
    UnramEverywhere D c := fun x hx h4 h5 => by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  apply Circle.ext
  rw [GlobalTheory.Mem.EtaTilde.val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu x hx, Circle.coe_one,
    Units.val_eq_one]
  refine finprod_eq_one_of_forall_eq_one fun P => ?_
  have e := GlobalTheory.Mem.EtaTilde.val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := e
  have e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    refine le_antisymm ((h2 _).1 h4 P) ?_
    rw [← e']
    exact mul_le_of_le_one_right' ((h2 _).1 h5 P)
  rw [e1, WithZero.log_one, neg_zero, zpow_zero]

end GlobalTheory.Mem.TupChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFormsNonisomorphicTypePartsInfEqBot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.TypesDisj

theorem prtW_inf_eq_bot : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (i : Fin D.R.m) (π π' : Φ), π ≠ π' → y.prtW F.lv2 i (rep π) ⊓ y.prtW F.lv2 i (rep π') = ⊥ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hI hP _ y Φ rep hR i π π' hne
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  have h0 := hB.models.νW i
  have hO := (GlobalTheory.FinTypesRows.isotL_span_orth D (Wc D i) _ R.θ (R.MW i (sg0 D A3.A)) (y.PW i) y.hF (R.βW i)
    (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))) (R.eWf i (sg0 D A3.A)) _ (R.fdW i) hI (D.sp.W_sig _)
    hB.models.inf (y.stdPsi.2 i) h0.1.1 h0.2 (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)).2
  have hHP := GlobalTheory.HilbertLevels.herm_lev hI hB.models.inf (D.sp.W_sig _) (R.MW i (sg0 D A3.A)) (R.βW i)
    (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))) h0.1.1 h0.2
  have hni : ¬ (rep π).Iso (rep π') := fun h => hne (hR.inj π π' h)
  rw [eq_bot_iff]
  rintro w ⟨hw, hw'⟩
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨b, hb, hab⟩ := Submodule.mem_map.1 hw'
  have hba : b = a := LinearEquiv.injective _ hab
  subst hba
  have hz := hO _ _ hni b ha b hb
  have hm : b ∈ Mult R.θ (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A)))) :=
    Mult.goodPart_le _ _ _ _ _ ha.1
  have hmT := Submodule.mem_map_of_mem (f := (PiTensorProduct.lift : MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap) hm
  by_contra hne0
  have hpos := hHP.pos ⟨_, hmT⟩ (fun h => hne0 ((Submodule.mem_bot ℂ).2 (congrArg Subtype.val h)))
  simp only at hpos
  unfold ipMT at hpos
  have hs : ∀ z, PiTensorProduct.lift.symm (((PiTensorProduct.lift : MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap) z) = z :=
    fun z => LinearEquiv.symm_apply_apply _ z
  rw [hs, hz] at hpos
  simp at hpos

end GlobalTheory.Mem.R3.Rw.TypesDisj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfDecoratedLatticeSplicedAtPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.Splice

theorem isPtOf_splice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q Q0 Q1 : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 F)) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (p0 : DecoF E n ST SG Q0) (p1 : DecoF E n ST SG Q1) (q : DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g0 p0 → GlobalTheory.Mem.Col2.IsPtOf hc h p1 → (∀ P ∈ Q, ¬ IsOver v P) → (∀ w ∈ SG, ¬ IsOver v w) → Deco.SameOff ST SG v q.deco.1 p1.deco.1 → (∀ P : HeightOneSpectrum (𝓞 E), IsOver v P → localization₂ P.asIdeal q.deco.1.N = localization₂ P.asIdeal p0.deco.1.N) → (∀ P : ST, IsOver v P.1 → q.deco.1.f P = p0.deco.1.f P) → (∀ P : Q, ∃ P' : Q1, P'.1 = P.1 ∧ p1.fr P' = q.fr P) → GlobalTheory.Mem.Col2.IsPtOf hc (h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0))) q := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q Q0 Q1 v g0 h p0 p1 q h0 h1 hQ hSG hoff hN hf hfr
  obtain ⟨⟨hg0, hd0⟩, -⟩ := (ChTwRead.isPtOf_iff hc g0 p0).1 h0
  obtain ⟨⟨hh, hd1⟩, hfr1⟩ := (ChTwRead.isPtOf_iff hc h p1).1 h1
  set m := h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0)) with hm
  have hv : bc (prV (E := E) v) m = bc (prV (E := E) v) g0 := by
    rw [hm, map_mul, rll_put_self, ← map_mul, mul_inv_cancel_left]
  have hne : ∀ P : HeightOneSpectrum (𝓞 E), ¬ IsOver v P → P.under (𝓞 F) ≠ v := by
    rintro P hP rfl
    exact hP rfl
  have hw : ∀ P : HeightOneSpectrum (𝓞 E), ¬ IsOver v P →
      bc (prV (E := E) (P.under (𝓞 F))) m = bc (prV (E := E) (P.under (𝓞 F))) h := by
    intro P hP
    rw [hm, map_mul, rll_put_ne n v _ (hne P hP), mul_one]
  have hmU : m ∈ UAd hc n :=
    mul_mem hh (rll_put_mem_UAd hc n v (afsplit_bc_mem hc.sig 1 v _ (mul_mem (inv_mem hh) hg0)))
  refine (ChTwRead.isPtOf_iff hc m q).2 ⟨⟨hmU, ?_⟩, fun P i j => ?_⟩
  · ext1
    · refine Formalism.L2.DIV.eq_of_forall_localized_eq fun P => ?_
      by_cases hP : IsOver v P
      · rw [hN P hP, hd0]
        exact (updn_mem_loc hP hv).symm
      · rw [hoff.N P hP, hd1]
        exact (updn_mem_loc (v := P.under (𝓞 F)) rfl (hw P hP)).symm
    · funext P
      by_cases hP : IsOver v P.1
      · rw [hf P hP, hd0]
        exact (updn_f_loc ST SG P hP hv).symm
      · rw [hoff.f P hP, hd1]
        exact (updn_f_loc ST SG (v := P.1.under (𝓞 F)) P rfl (hw P.1 hP)).symm
    · funext w
      have hP := hSG w.1 w.2
      rw [hoff.be w hP, hd1]
      exact (updn_be_loc ST SG (v := w.1.under (𝓞 F)) w rfl (hw w.1 hP)).symm
  · obtain ⟨⟨P1, hP1⟩, hP', e⟩ := hfr P
    have hPv := hQ P.1 P.2
    simp only at hP'
    subst hP'
    rw [← e, ← hfr1 ⟨_, hP1⟩ i j]
    refine ChTwRead.adAt_congr_prV P.1 ?_
    have := congrArg (fun g : GL (Fin n) (E ⊗[F] (P.1.under (𝓞 F)).adicCompletion F) =>
      g.val i j) (hw P.1 hPv)
    exact this

end GlobalTheory.Mem.Col2.Splice
end

