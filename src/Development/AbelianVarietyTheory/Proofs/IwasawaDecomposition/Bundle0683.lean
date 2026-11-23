module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevJCosetsOfFurther
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwist
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.Mv

namespace GlobalTheory.HeightCounting.Up.MvTw

section Gen

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C)
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
variable {A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m}

section Comp
variable (R : RealDat3 a.D A3 Ks)

def once : @RealDat3 c.D G _ _ Pl0 I0 T₀ (famInThreeCoefficientChange c A3) Ks _ _ (alg c iK) := real3 c R

def thru : @RealDat3 c.D G _ _ Pl0 I0 T₀ (famInThreeCoefficientChange c A3) Ks _ _ (alg c iK) :=
  (by with_unfolding_all exact ((real3 (a := b) c (iK := alg b iK) (real3 b R)) :))

def thruY : letI := alg c iK; type_of% (once c R).ioY := letI := alg c iK; (by with_unfolding_all exact ((thru b c R).ioY :))

def thruX : letI := alg c iK; type_of% (once c R).ioX := letI := alg c iK; (by with_unfolding_all exact ((thru b c R).ioX :))

theorem thruY_eq : letI := alg c iK; (once c R).ioY = thruY b c R :=
  letI := alg c iK
  eq_of_heq (HEq.trans ((by with_unfolding_all exact ((real_ioY c R.toRealDat).symm :)) : HEq (once c R).ioY R.ioY)
    ((by with_unfolding_all exact ((HEq.trans (real_ioY b R.toRealDat) ((by with_unfolding_all exact ((real_ioY (a := b) c (iK := alg b iK) (real b R.toRealDat)) :))) :
    HEq _ (thruY b c R)) :))))

theorem thruX_eq : letI := alg c iK; (once c R).ioX = thruX b c R :=
  letI := alg c iK
  eq_of_heq (HEq.trans ((by with_unfolding_all exact ((real_ioX c R.toRealDat).symm :)) : HEq (once c R).ioX R.ioX)
    ((by with_unfolding_all exact ((HEq.trans (real_ioX b R.toRealDat) ((by with_unfolding_all exact ((real_ioX (a := b) c (iK := alg b iK) (real b R.toRealDat)) :))) :
    HEq _ (thruX b c R)) :))))

theorem thru_eq : once c R = thru b c R :=
  letI := alg c iK
  (by with_unfolding_all exact ((congrArg₂ (DatCopy.setIo (once c R)) (thruY_eq b c R) (thruX_eq b c R)) :))

end Comp

variable {R : RealDat3 a.D A3 Ks} (F : Face3 a.D A3) (y : Hd R.toRealDat) (y' : HdB b R.toRealDat)


set_option maxHeartbeats 1000000 in
theorem pkT_move (hs : Same b y y') {mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G} {p : PkD a.D G} (t : PkT F y mA p) :
    letI := alg b iK
    ∃ t' : PkT (R := real3 b R) (face3 b F) (hd3 b y y') (mCp b mA) (pCp b p),
      HEq t'.tA t.tA ∧ HEq t'.rep t.rep ∧ (∀ c, HEq (t'.ch c).jE (t.ch c).jE) ∧ (∀ c, HEq (t'.ch c).jM (t.ch c).jM) ∧
        (∀ c, HEq (t'.ch c).jX (t.ch c).jX) ∧ HEq t'.lf.eW t.lf.eW ∧ HEq t'.lf.jMt t.lf.jMt := by
  letI := alg b iK
  have hs' := fixTup_same b hs
  have h1 := (GlobalTheory.Mem.R3.Tr.reps_parts_tr B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs').1 p.Φ t.rep t.reps
  have h2 := fun c => GlobalTheory.Mem.R3.Rw.chT_tr B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' c p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ => (p.sA c μ).A) :))) ((by with_unfolding_all exact ((p.ch c) :))) ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :))) ((by with_unfolding_all exact ((t.ch c) :)))
    ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x)) :)))
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.Mem.R3.Rw.lfT_of_same B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ j => (p.sL μ j).A) :))) ((by with_unfolding_all exact (p.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :))) ((by with_unfolding_all exact (t.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x)) :)))
  have h4 := (GlobalTheory.Mem.R3.Rw.rr_eta_tr B C a b G Pl0 I0 T₀ Ks A3 R F).2 y (hd3 b y y') true (p.ch true).EE (t.ch true).jE
    ((by with_unfolding_all exact ((h2 true).choose.jE :))) p.nR p.cR p.Xo ((by with_unfolding_all exact ((h2 true).choose_spec.1 :))) t.rr
  refine ⟨{ rep := (by with_unfolding_all exact (t.rep :))
            reps := (by with_unfolding_all exact (h1 :))
            tA := (by with_unfolding_all exact (t.tA :))
            lawsA := (by with_unfolding_all exact (t.lawsA :))
            lawsL := (by with_unfolding_all exact (t.lawsL :))
            hA := (by with_unfolding_all exact (t.hA :))
            hL := (by with_unfolding_all exact (t.hL :))
            ch := fun c => (by with_unfolding_all exact ((h2 c).choose :))
            lf := (by with_unfolding_all exact (l :))
            dall := (by with_unfolding_all exact ((dall_tr b F t.dall) :))
            rr := (by with_unfolding_all exact (h4 :)) }, ?_, ?_, fun c => ?_, fun c => ?_, fun c => ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl t.tA) :))
  · exact (by with_unfolding_all exact ((HEq.refl t.rep) :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.2 :))
  · exact (by with_unfolding_all exact (hl1 :))
  · exact (by with_unfolding_all exact (hl2 :))

end Gen

section Dat

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}


set_option maxHeartbeats 1000000 in
theorem transportModuliCoreWithConstants_comp (z₀ : Dat a.st I hX T Wt) (Xg : Finset (Gc b.st.B px → b.st.B.LL)) (tr : TrI b.st.B px)
    (co : Formalism.L2.Pj.CoreJ b.st.toD7) (al : Algebra co.Q.c.F b.st.toD7.what₂.LL)
    (ale : ∀ y : co.Q.c.F, b.st.B.embLL (algebraMap co.Q.c.F b.st.toD7.what₂.LL y) = y)
    (R : RealDat3 b.st.toD7 (famR b.st I hX (usedOf I T Wt) Xg tr) co.Q.c.F)
    (hXg : Xg = z₀.Xg) (htr : tr = z₀.tr)
    (hc : HEq co (coreJ (a := a) b z₀.core)) (hR : HEq R (real3 (a := a) b (iK := z₀.alg) z₀.R)) :
    HEq (coreJ (a := b) c co) (coreJ (a := a) c z₀.core) ∧
      HEq (real3 (a := b) c (iK := al) R) (real3 (a := a) c (iK := z₀.alg) z₀.R) := by
  have hc' := eq_of_heq hc
  subst hXg htr hc'
  have e : al = ((by with_unfolding_all exact ((alg (a := a) b z₀.alg) :))) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    refine Eq.trans (ale y) ?_
    exact (by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :))
  subst e
  have hR' : R = ((by with_unfolding_all exact ((real3 (a := a) b (iK := z₀.alg) z₀.R) :))) := eq_of_heq ((by with_unfolding_all exact (hR :)))
  subst hR'
  refine ⟨?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl (coreJ (a := a) c z₀.core)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (thru_eq (a := a) b c (iK := z₀.alg) z₀.R).symm) :))


set_option maxHeartbeats 1000000 in
theorem copy_comp (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (hXg : z.Xg = z₀.Xg) (htr : z.tr = z₀.tr)
    (hc : HEq z.core (coreJ (a := a) b z₀.core)) (hR : HEq z.R (real3 (a := a) b (iK := z₀.alg) z₀.R)) :
    HEq (coreJ (a := b) c z.core) (coreJ (a := a) c z₀.core) ∧
      HEq (real3 (a := b) c (iK := z.alg) z.R) (real3 (a := a) c (iK := z₀.alg) z₀.R) :=
  (by with_unfolding_all exact ((transportModuliCoreWithConstants_comp b c z₀ z.Xg z.tr z.core z.alg z.alg_eq z.R hXg htr hc hR) :))

end Dat

section Main

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}


set_option maxHeartbeats 2000000 in
theorem moved_again (o o' : q.Over) (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) (m : Moved o) (hc : m.Copy) (hh : m.Coh) :
    ∃ m' : Moved o', m'.z = DatCopy.copy (a := o.Z) o'.Z s m.z ∧ m'.Copy ∧ m'.Coh := by
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ m.z.alg _ m.z.R.toRealDat m.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := pkT_move (a := o.Z) o'.Z (iK := m.z.alg) m.z.F m.y y' hy m.t
  have he := (@GlobalTheory.Mem.R3.Rw.rr_eta_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ _ m.z.alg _ m.z.R m.z.F).1
  letI : Algebra m.z.core.Q.c.F (Late.D o'.Z).what₂.LL := alg (a := o.Z) o'.Z m.z.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% m.t.tA) = m.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have hk := copy_comp (a := Z₀) o.Z o'.Z z₀ m.z m.Xg m.tr ((by with_unfolding_all exact (hc.core :))) ((by with_unfolding_all exact (hc.R :)))
  have hW := forcedContentPlaces_eq_transport_sameFiniteGroup (a := o.Z) o'.Z s m.z
  refine ⟨{ z := DatCopy.copy (a := o.Z) o'.Z s m.z
            intersectionNumber_baseChange := (by with_unfolding_all exact ((cp_holds (a := o.Z) o'.Z s m.z m.intersectionNumber_baseChange) :))
            exAt := DatCopy.copy_exAt (a := o.Z) o'.Z s m.exAt
            inGeo := (by with_unfolding_all exact ((cp_inGeo (a := o.Z) o'.Z s m.z m.inGeo) :))
            Xg := (by with_unfolding_all exact (m.Xg :))
            tr := (by with_unfolding_all exact (m.tr :))
            core := fun h => ⟨(by with_unfolding_all exact ((lawsCore_tr (a := o.Z) o'.Z (m.core h).1) :)), (by with_unfolding_all exact ((m.core h).2.1 :)), (by with_unfolding_all exact ((m.core h).2.2.1 :)),
              (by with_unfolding_all exact ((m.core h).2.2.2 :))⟩
            eta := fun j v => Eq.trans ((by with_unfolding_all exact ((he j ((by with_unfolding_all exact (v :)))) :)) : _ = etaOf m.z.R m.z.F j v) (m.eta j v)
            W1 := fun F0 => Eq.trans ((by with_unfolding_all exact ((hW ((by with_unfolding_all exact (F0 :)))) :)) : _ = m.z.W1 ((by with_unfolding_all exact (F0 :)))) ((by with_unfolding_all exact ((m.W1 ((by with_unfolding_all exact (F0 :)))) :)))
            y := (by with_unfolding_all exact ((hd3 (a := o.Z) o'.Z (iK := m.z.alg) m.y y') :))
            tup := (by with_unfolding_all exact (m.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := fun c u => (by with_unfolding_all exact ((HEq.trans (heq_of_eq (congrArg (fun r : type_of% m.t.tA => (r c ((by with_unfolding_all exact (u :)))).j) hA))
              (m.tA c ((by with_unfolding_all exact (u :))))) :)) }, rfl, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (hk.1 :))
  · exact (by with_unfolding_all exact (hk.2 :))
  · exact (by with_unfolding_all exact (hh.tupT :))
  · exact (by with_unfolding_all exact ((HEq.trans ((by with_unfolding_all exact (hy.PY :)) : HEq (fixTup (a := o.Z) o'.Z (iK := m.z.alg) m.y y').PY.ψ m.y.PY.ψ) hh.PY) :))
  · exact (by with_unfolding_all exact ((HEq.trans ((by with_unfolding_all exact (hy.PW :)) : HEq (fun i => ((fixTup (a := o.Z) o'.Z (iK := m.z.alg) m.y y').PW i).ψ) (fun i => (m.y.PW i).ψ)) hh.PW) :))
  · exact (by with_unfolding_all exact ((a2.trans hh.rep) :))
  · exact (by with_unfolding_all exact ((fun c => (a3 c).trans (hh.jE c)) :))
  · exact (by with_unfolding_all exact ((fun c => (a4 c).trans (hh.jM c)) :))
  · exact (by with_unfolding_all exact ((fun c => (a5 c).trans (hh.jX c)) :))
  · exact (by with_unfolding_all exact ((a6.trans hh.eW) :))
  · exact (by with_unfolding_all exact ((a7.trans hh.jMt) :))

end Main

theorem moved_tw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (N : TwNew (Dof x)) : ∃ m : Moved (oTw x N), m.z = datTw x N ∧ m.Copy ∧ m.Coh :=
  moved_again x.o (oTw x N) (sgTw x N) x.m x.copy x.coh

end GlobalTheory.HeightCounting.Up.MvTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAddCharZmodEqOfNeOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory

theorem exists_nontrivial_addChar_eq_of_ne (p : ℕ) [Fact p.Prime] (Pr : Prop) (φ : AddChar (ZMod p) ℂ) (h : Pr → φ ≠ 1) :
    ∃ ψ' : AddChar (ZMod p) ℂ, ψ' ≠ 1 ∧ (Pr → ψ' = φ) := by
  by_cases hP : Pr
  · exact ⟨φ, h hP, fun _ => rfl⟩
  · refine ⟨ZMod.stdAddChar, ?_, fun h' => absurd h' hP⟩
    intro h1
    have hprim := ZMod.isPrimitive_stdAddChar p
    apply hprim (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, h1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up

theorem cenTw_read {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : ∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩ : P.q.Over))).nd)).coeff ((sgTw x N).iso g)) → (sideTw x N).cen μ c = x.s.cen μ c0 := by
  intro μ c c0 h
  have e : (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)) = (((by with_unfolding_all exact (c :)) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))) : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)) :=
    MonoidAlgebra.coeff_injective (Finsupp.ext fun g => (by with_unfolding_all exact ((h g) :)))
  have e2 : c0 = ((by with_unfolding_all exact (c :)) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))) := Subtype.ext e
  exact (by with_unfolding_all exact ((congrArg (x.s.cen μ) e2).symm :))

theorem readTw_ex {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) :
    ∃ r : ReadPk m (sideTw x N), r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y) := (by with_unfolding_all exact (
  (GlobalTheory.T.adelicRowsReading_transport_laterHeckeGaloisStage x (nTw x N) x.fits.grp (fitsTw x N).grpAt (fitsTw x N).cen m hc hh (sgTw x N) (sideTw x N) rfl HEq.rfl
    (cenTw_read x N)) :))

theorem jMtTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin) :
    ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1 := by
  cases m with
  | mk z intersectionNumber_baseChange exAt inGeo Xg tr core eta W1 y tup t tA =>
    obtain rfl : z = datTw x N := hm
    have e : HEq t.lf.jMt x.m.t.lf.jMt := (by with_unfolding_all exact ((hh.jMt.trans x.coh.jMt.symm) :))
    have e2 : t.lf.jMt = ((by with_unfolding_all exact (x.m.t.lf.jMt :)) : type_of% t.lf.jMt) := eq_of_heq ((by with_unfolding_all exact (e :)))
    intro μ h i y
    exact (by with_unfolding_all exact (((hp.jMt μ h i y).trans ((heq_of_eq (congrArg (fun φ : type_of% t.lf.jMt => φ μ i y) e2)).trans (x.pin.jMt μ h i y).symm)) :))

theorem eWTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin) :
    ∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y) := by
  cases m with
  | mk z intersectionNumber_baseChange exAt inGeo Xg tr core eta W1 y tup t tA =>
    obtain rfl : z = datTw x N := hm
    have e : HEq t.lf.eW x.m.t.lf.eW := (by with_unfolding_all exact ((hh.eW.trans x.coh.eW.symm) :))
    have e2 : t.lf.eW = ((by with_unfolding_all exact (x.m.t.lf.eW :)) : type_of% t.lf.eW) := eq_of_heq ((by with_unfolding_all exact (e :)))
    intro i y
    exact (by with_unfolding_all exact (((hp.eW i y).trans ((heq_of_eq (congrArg (fun φ : type_of% t.lf.eW => φ i y) e2)).trans (x.pin.eW i y).symm)) :))

theorem readTw : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)), m.z = datTw x N → m.Copy → m.Coh → ∃ r : ReadPk m (sideTw x N), r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y) ∧ (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) ∧ (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) := by
  intro K B f T w P x N m hm hc hh
  have H := readTw_ex x N m hc hh
  refine H.elim fun r h => ?_
  exact Exists.intro r (And.intro h.1 (And.intro h.2 (And.intro (jMtTw x N m hm hh r h.1) (eWTw x N m hm hh r h.1))))

end GlobalTheory.HeightCounting.Up
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPenultimateLevelCouplingCosets
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mem.Col2.TwistLevel


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_levJ_cosets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → Nonempty (TwLevJ I l Z F Q u a chOf K) := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hFin hUl hchi
  exact exists_levJ_cosets_of_further I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hUl hchi
    (GlobalTheory.T.furtherPlaces_group_contains_chart_levels I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hFin hUl hchi)

end GlobalTheory.Mem.Col2.TwistLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassGroupDescentOfCoeffFieldTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TwistDescent

variable {D : D7} {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl}

abbrev rd (ρ : Reading i k b v) : D.ntw.Ok i k →+* FractionRing ρ.Oe :=
  (algebraMap ρ.Oe (FractionRing ρ.Oe)).comp (algebraMap (D.ntw.Ok i k) ρ.Oe)

theorem rd_injective (ρ : Reading i k b v) : Function.Injective (rd ρ) :=
  (IsFractionRing.injective ρ.Oe (FractionRing ρ.Oe)).comp ρ.inj

theorem eq_iff_of_reads {ρ : Reading i k b v} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (g g' : G D.host.E D.nd.Om) : χ g = χ g' ↔ ψ₀ g = ψ₀ g' := by
  constructor
  · intro he
    apply Units.ext
    apply ρ.emb.injective
    rw [h g, h g', he]
  · intro he
    apply Units.ext
    apply rd_injective ρ
    rw [← h g, ← h g', he]

theorem one_iff_of_reads {ρ : Reading i k b v} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (g : G D.host.E D.nd.Om) : χ g = 1 ↔ ψ₀ g = 1 := by
  simpa using eq_iff_of_reads h g 1

theorem twOK_of_reads {ρ : Reading i k b v} {Q : Finset (PlE D.host)} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (hs : ∀ u ∈ Q, IsSplitPl D.host u) (hd : Disjoint Q (D.ntw.S0 i))
    (ho : IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om))) (ha : AntiHom D.ntw.cc ψ₀)
    (hp : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) (hr : RamExactly ψ₀ (↑Q : Set (PlE D.host)))
    (ht : BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i)) : IntegralHeckeForms.TwOK i k Q χ := by
  have hker : (χ.ker : Set (G D.host.E D.nd.Om)) = ψ₀.ker := Set.ext fun g => by
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact one_iff_of_reads h g
  refine ⟨hs, hd, hker ▸ ho, fun g g' hg => ?_, fun g => ?_, fun w A hA => ?_, fun w hw A hA σ hσ => ?_⟩
  · rw [← map_inv, eq_iff_of_reads h, map_inv]
    exact ha g g' hg
  · have h1 : χ g ^ (D.ntw.l i ^ k) = 1 := by
      rw [← map_pow, one_iff_of_reads h, map_pow]
      exact hp g
    have h2 : ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) ^ (D.ntw.l i ^ k) = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨a, -, h3⟩ := (D.ntw.zk_prim i k).eq_pow_of_pow_eq_one h2
    refine Subgroup.mem_zpowers_iff.2 ⟨(a : ℤ), ?_⟩
    rw [zpow_natCast]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h3)
  · rw [← hr w A hA]
    simp only [ne_eq, one_iff_of_reads h]
  · exact (one_iff_of_reads h σ).2 (ht w hw A hA σ hσ)

theorem exists_reads {ρ : Reading i k b v} (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)
    (hp : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) :
    ∃ χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ, (∀ g, χ g ∈ Subgroup.zpowers (D.ntw.zk i k)) ∧
      ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) := by
  have hz : IsPrimitiveRoot (rd ρ (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) :=
    (D.ntw.zk_prim i k).map_of_injective (rd_injective ρ)
  have hx : ∀ g, ∃ a : ℕ, rd ρ (((D.ntw.zk i k) ^ a : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) =
      ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) := fun g => by
    have h1 : (ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL)) ^ (D.ntw.l i ^ k) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hp g, Units.val_one, map_one]
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one h1
    exact ⟨a, by rw [Units.val_pow_eq_pow_val, map_pow]; exact ha⟩
  choose a ha using hx
  let χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ := MonoidHom.mk' (fun g => D.ntw.zk i k ^ a g) fun g g' => by
    apply Units.ext
    apply rd_injective ρ
    rw [ha (g * g'), map_mul ψ₀, Units.val_mul, map_mul ρ.emb, Units.val_mul, map_mul (rd ρ), ha, ha]
  refine ⟨χ, fun g => ⟨(a g : ℤ), by simp [χ]⟩, fun g => (ha g).symm⟩

theorem exists_pulls_twOK : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v) (Q : Finset (PlE D.host)) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∀ u ∈ Q, IsSplitPl D.host u) → Disjoint Q (D.ntw.S0 i) → IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc ψ₀ → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → RamExactly ψ₀ (↑Q : Set (PlE D.host)) → BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i) → (∃ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀) ∧ ∀ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀ → IntegralHeckeForms.TwOK i k Q (ψ.comp (D.ntw.art i Q)) := by
  intro D i k b v ρ Q ψ₀ hs hd ho ha hp hr ht
  refine ⟨?_, fun ψ hψ => twOK_of_reads (ρ := ρ) (fun g => hψ g) hs hd ho ha hp hr ht⟩
  obtain ⟨χ, hv, hχ⟩ := exists_reads (ρ := ρ) ψ₀ hp
  have hfin : IsOfFinOrder (D.ntw.zk i k) := isOfFinOrder_iff_pow_eq_one.2
    ⟨_, pow_pos (D.ntw.lPrime i).out.pos k, (IsPrimitiveRoot.coe_units_iff.mp (D.ntw.zk_prim i k)).pow_eq_one⟩
  haveI : Finite (Subgroup.zpowers (D.ntw.zk i k)) := finite_zpowers.2 hfin
  have hker : (χ.ker : Set (G D.host.E D.nd.Om)) = ψ₀.ker := Set.ext fun g => by
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact one_iff_of_reads hχ g
  obtain ⟨f, hf⟩ := D.ntw.art_univ i Q
    (fun u hu hl => Finset.disjoint_left.1 hd hu (D.ntw.twistExcludedPlaces_contains_residueChar i hl)) (Subgroup.zpowers (D.ntw.zk i k))
    (by
      rintro ⟨x, n, rfl⟩
      refine ⟨k, Subtype.ext ?_⟩
      change (D.ntw.zk i k ^ n) ^ (D.ntw.l i ^ k) = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        (IsPrimitiveRoot.coe_units_iff.mp (D.ntw.zk_prim i k)).pow_eq_one, one_zpow])
    (χ.codRestrict _ hv) (by rw [MonoidHom.ker_codRestrict, hker]; exact ho)
    (fun g g' h => Subtype.ext (by
      change χ g' = (χ g)⁻¹
      rw [← map_inv, eq_iff_of_reads hχ, map_inv]
      exact ha g g' h))
    (fun u hu A hA σ hσ => Subtype.ext (by
      change χ σ = 1
      rw [one_iff_of_reads hχ]
      by_contra hne
      exact hu ((hr u A hA).1 ⟨σ, hσ, hne⟩)))
  refine ⟨(Subgroup.zpowers (D.ntw.zk i k)).subtype.comp f, fun g => ?_⟩
  have h1 : f (D.ntw.art i Q g) = χ.codRestrict _ hv g := by rw [← hf]; rfl
  change ρ.emb _ = rd ρ (((f (D.ntw.art i Q g) : Subgroup.zpowers (D.ntw.zk i k)) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k)
  rw [h1]
  exact hχ g

end GlobalTheory.TwistDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralLevelObjectsReplacedStages
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 4000000 in
theorem exists_sRest_top : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (F0 : ∀ u, Forms0 D u) (P : SPack D F0) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), GapHyp D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c ∧ SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ R eE P.X P.inst P.G t j ∧ ∀ (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F0 F'), ∃ (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)) (S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF)), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro hDS hHC hCusp hDSU hRF D G' _ _ Pl0 T A Ks _ _ _ R F F0 P eE hGap hph hL hR hDs hLev hGrp hPin hE0 hM hRange hNorm hDall
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.Mem.SRe.seeAt_exists D G' Pl0 T A Ks R F P.X P.inst P.pin hLev hGrp hPin hE0
  obtain ⟨v₀, hv, c, hc, hev⟩ :=
    _root_.GlobalTheory.Mem.SRe.evalOn_all hDS hCusp hDSU hRF D G' Pl0 T A Ks R F P.X P.inst t P.pin hGap hLev hM.inf hM.ν0 ht
  have hg := GlobalTheory.T.evaluation_goodRows_to_conjugate_goodRows D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c hLev hM.inf hv ht hev
  have hle := (_root_.GlobalTheory.Mem.SRe.levCols_le_triv_and_finite hHC hCusp D G' Pl0 T A Ks R F hLev hM.inf hM.ν0).1
  obtain ⟨hfr, j, hj⟩ :=
    _root_.GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c eE hc hv hM.HE hRange hNorm hle hev hg.1
  refine ⟨hfr hDall, j, t, c, hc, ht, hg.2, hj, ?_⟩
  intro N hh F' hs
  have hF := _root_.GlobalTheory.Mem.SRe.finX_reY D ⟨P.toNew (hfr hDall) j, N, hh⟩ P.X P.Y P.fin
  obtain ⟨S, hS⟩ := exists_sRest_re D F0 P (hfr hDall) j N hh F' hs hF hph hL hR hDs
  exact ⟨hF, S, hS⟩

end GlobalTheory.Mem.SRe
end

