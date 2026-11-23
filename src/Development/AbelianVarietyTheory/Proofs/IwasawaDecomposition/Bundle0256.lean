module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalR
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G GlobalTheory.Points
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def constHom (M : RatModel o Ω) (U : M.Z.Opens) : o →+* Γ(M.Z, U) :=
  (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom

theorem finiteType_constHom (M : RatModel o Ω) {U : M.Z.Opens} (hU : IsAffineOpen U) :
    (M.constHom U).FiniteType := by
  have := M.lft
  have h1 : (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
    M.s.finiteType_appLE (isAffineOpen_top _) hU _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

variable {Ω' : Type} [Field Ω'] [Algebra o Ω']

theorem exists_nbhd_of_map_O (M : RatModel o Ω) (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω') {z' : M'.Z} {z : M.Z}
    (hz : ∀ a ∈ M.O z, φ a ∈ M'.O z') :
    ∃ (V : M'.Z.Opens) (U : M.Z.Opens), z' ∈ V ∧ IsAffineOpen U ∧ (U : Set M.Z).Nonempty ∧
      ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M.Z.Opens)) (x := z) trivial
  have hUne : (U : Set M.Z).Nonempty := ⟨z, hzU⟩
  letI := (M.constHom U).toAlgebra
  obtain ⟨s, hs⟩ := (M.finiteType_constHom hU).out
  let V : M'.Z.Opens := ⟨⋂ f ∈ s, {w | φ (valF M.pt U f) ∈ M'.O w},
    isOpen_biInter_finset fun f _ => M'.isOpen_setOf_mem_O _⟩
  have hzV : z' ∈ V := Set.mem_iInter₂.2 fun f _ => hz _ (valF_mem_O hzU f)
  have hsV : ∀ f ∈ s, φ (valF M.pt U f) ∈ M'.ringOn V := fun f hf =>
    mem_ringOn.2 fun w hw => Set.mem_iInter₂.1 hw f hf
  have key : ∀ f : Γ(M.Z, U), φ (valF M.pt U f) ∈ M'.ringOn V := by
    intro f
    have hf : f ∈ Algebra.adjoin o (s : Set Γ(M.Z, U)) := hs ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact hsV x hx
    | algebraMap r =>
      have e : valF M.pt U (algebraMap o Γ(M.Z, U) r) = algebraMap o Ω r := M.valF_constFn hUne r
      rw [e, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_add (f := _), map_add (f := _), res_apply, res_apply]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_mul, map_mul, res_apply, res_apply]
      exact mul_mem hx hy
  refine ⟨V, U, hzV, hU, hUne, fun x hx => ?_⟩
  obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
  exact key f

theorem exists_isHom_of_map_O :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω']
      (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') →
        ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  intro o Ω _ _ _ M Ω' _ _ M' φ h
  refine exists_isHom_of_local fun z' => ?_
  obtain ⟨z, hz⟩ := h z'
  exact exists_nbhd_of_map_O M M' φ hz

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherFaceStatementsIndependentOfError
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def reFaceErr (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : type_of% R.err0 :=
  fun w _ => errOf ((R.toCx3 F).data (reFace F Dc Sp Zsc).cr false) ((reFace F Dc Sp Zsc).fc (R.toCx3 F).zs).Z.F0 w


set_option maxHeartbeats 4000000 in
theorem reFace_errEq (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ErrEq (R.withErr (reFaceErr R F Dc Sp Zsc)) (reFace F Dc Sp Zsc) := fun _ _ => rfl


set_option maxHeartbeats 4000000 in
theorem reFace_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : Keep (A3 := A3) R.toRealDat F.lv2 cG) :
    Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩


set_option maxHeartbeats 4000000 in
theorem reFace_keep_back (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (h : Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG) : Keep (A3 := A3) R.toRealDat F.lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩


set_option maxHeartbeats 4000000 in
theorem reFace_scal (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hs : R.IsScal F) : R.IsScal (reFace F Dc Sp Zsc) := by
  refine ⟨hs.lam0, hs.kap, hs.off, fun i t p hp => ?_, fun i p v hv hp => ?_, hs.tup⟩
  · refine (hs.abs0 i t p hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd hp (h.1 p)
  · refine (hs.abs i p v hv hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd (h.2 p v hv) hp


set_option maxHeartbeats 4000000 in
theorem reFace_pins (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hP : Pins R F cG) : Pins (R.withErr e) (reFace F Dc Sp Zsc) cG := by
  have h := RealDat3.weak_characterisation_with_error hP.char e
  have hl6' : ∀ i, (Zsc ((R.withErr e).toCx3 F).zs).l6m i = (F.Zsc ((R.withErr e).toCx3 F).zs).l6m i ∨
      ((∀ p, (R.withErr e).Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → (R.withErr e).PartAt F i p v) := fun i => by
    rw [RealDat3.zs_withErr]
    exact (hl6 i).imp id fun h => ⟨h.1, fun p v hv => (RealDat3.partAt_withErr e i p v).2 (h.2 p v hv)⟩
  exact ⟨⟨h.base, h.inert, h.fullY, h.fullX, h.fullP, reFace_scal (R.withErr e) F Dc Sp Zsc hl6' h.scal, h.tup, h.phase, h.allPl⟩,
    reFace_keep R F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩


set_option maxHeartbeats 4000000 in
theorem further_face_statements_independent_of_error (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.withErr e) (reFace F Dc Sp Zsc) :=
  ⟨⟨h.ex.ItY, h.ex.ItX, h.ex.ioY, h.ex.ioX, h.ex.Th, h.ex.ioP, h.ex.thF, h.ex.thG⟩, h.conj, h.levelW, h.integral⟩


set_option maxHeartbeats 4000000 in
def reFaceRead (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) : Read (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X0 :=
  { Y with
    mj := ⟨Y.mj.eW, Y.mj.eW_range, Y.mj.eW_norm, Y.mj.eW_lat⟩
    cen0 := fun cG hK => Y.cen0 cG (reFace_keep_back R F cG Dc Sp Zsc e hK)
    cen1 := fun cG hK => Y.cen1 cG (reFace_keep_back R F cG Dc Sp Zsc e hK) }


set_option maxHeartbeats 4000000 in
def reFaceReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ReadL (R.withErr e) (reFace F Dc Sp Zsc) X0 (reFaceRead R F Dc Sp Zsc e X0 Y) :=
  { Z with }

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.RealGeo.Upd

section
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section
variable (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (kap lam err)

abbrev upE : RealDat D A C.Q.c.F := { R.upd6 kap lam with err0 := err }


set_option maxHeartbeats 1600000 in
def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat C.toCore R i Tp tup) :
    OMDat C.toCore (upE C R kap lam err) i Tp tup := { O with }


set_option maxHeartbeats 1600000 in
def updFWT {κ v₀} (t : FWTie C R κ v₀) : FWTie C (upE C R kap lam err) κ v₀ :=
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

variable {C R}
variable {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (O : ∀ i, OMDat C.toCore R i Unit (fun _ => A.μ0))


set_option maxHeartbeats 1600000 in
theorem omPins_upE (i : Fin D.R.m) (h : OMPins C R κ v₀ O i) :
    OMPins C (upE C R kap lam err) κ v₀ (fun i => updO C R kap lam err (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

end

end

end GlobalTheory.RealGeo.Upd

namespace GlobalTheory.RealGeo


set_option maxHeartbeats 1600000 in
theorem geoHalf_upd : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (ph : Fin D.R.m → ℂ) kap lam err (g : GlobalTheory.RealGeo.GeoHalf C R ph), ∃ g' : GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph, g'.κ = g.κ ∧ HEq g'.v₀ g.v₀ ∧ (GlobalTheory.RealGeo.InGeo g → GlobalTheory.RealGeo.InGeo g') := by
  intro D G _ _ Pl0 T A C _ R ph kap lam err g
  refine ⟨⟨g.κ, g.v₀, Upd.updFWT C R kap lam err g.fw, g.bar, fun i => Upd.updO C R kap lam err (g.O i),
    fun i => Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩, rfl, HEq.rfl, ?_⟩
  intro h
  exact ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

end GlobalTheory.RealGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodOperatorSpectrum
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SJ.PairMain

theorem op_ramCrd_eq {D : D7} (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (hK : St.LevelSubgroupCharacter) (w u : D.what₂.Word) (hw : w = u)
    (p : PerW St hK w) (q : PerW St hK u) (hpq : HEq p q) {n : ℕ} (b : Fin n → (D.mem w).A.Mram) (c : Fin n → ℂ)
    (φ : (D.mem u).A.Mram) (hc : HEq (∑ i, c i • b i) φ) (T : Cu St u hK)
    (hT : colDictL St q.Tr hK T = ((φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    (((p.op (ramCrd b c) : HHX St)) : L2X St) = PuFun St u hK q.Dt T := by
  subst hw
  obtain rfl := eq_of_heq hpq
  obtain rfl := eq_of_heq hc
  have h1 : ramCrd b c = Submodule.inclusion inf_le_left (∑ i, c i • b i) := by
    show Submodule.inclusion inf_le_left (Fintype.linearCombination ℂ b c) = _
    rw [Fintype.linearCombination_apply]
    rfl
  have h2 : (colDict St p.Tr hK p.hI p.hB).symm (Submodule.inclusion inf_le_left (∑ i, c i • b i)) = T := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [colDict_apply, hT]
    rfl
  rw [h1]
  simp only [PerW.op, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h2]
  rfl

theorem pair_step : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (fc X.zs).Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin ((fc X.zs).Dc.a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (R.wU u) = u) → (fc X.zs).Sp = spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (R.wU u) i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) → ∀ (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (sEEc : X.EE →ₗ⋆[ℂ] Tw s (HHX St)), HEq sEE sEEc → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (κ₀ : ℂ), κ₀ ≠ 0 → (∀ F, Tw.out (sEEc (M.eR F)) = κ₀ • conjHH St G (j F)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu St u hK), colDictL St (pw u).Tr hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR F), (fc X.zs).Sp.Pu (R.wU u) (cjv s (M.cφ u φ))⟫_ℂ = cj s (κ * ⟪((conjHH St G (j F) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T⟫_ℂ) := by
  intro D Bs A X fc s R cr M St G hK pw wdD bR hw hSp hb
  generalize (fc X.zs).Sp = SP at hSp ⊢
  subst hSp
  intro sEE sEEc hE j κ₀ hκ₀ hout u
  obtain rfl := eq_of_heq hE
  refine ⟨starRingEnd ℂ κ₀, (map_ne_zero _).2 hκ₀, ?_⟩
  intro F φ T hT
  refine (Pair.inner_tw_of_smul (E := HHX St) s (sEE (M.eR F) : Tw s (HHX St))
    ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ)) : Tw s (HHX St)) κ₀
    ((conjHH St G (j F) : HHX St)) (hout F)).trans ?_
  congr 2
  have hcc : cjVec s _ (cjv s (M.cφ u φ)) = M.cφ u φ := funext fun i => cj_cj s _
  have hP : Tw.out (s := s) ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ))) =
      (pw (wdD (R.wU u))).op (ramCrd (bR (R.wU u)) (M.cφ u φ)) :=
    (spOf_Pu s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR (R.wU u) (cjv s (M.cφ u φ))).trans (by rw [hcc])
  have key := op_ramCrd_eq St hK _ u (hw u) _ _ (congr_arg_heq pw (hw u)) (bR (R.wU u)) (M.cφ u φ) _
    (Pair.sum_coord_heq M u _ (hw u) (bR (R.wU u)) (hb u) φ) T hT
  rw [Submodule.coe_inner]
  exact congrArg _ ((congrArg Subtype.val hP).trans key)

end GlobalTheory.Mem.SJ.PairMain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

namespace GlobalTheory.ChernScale

section General

variable {α : Type*} [MeasurableSpace α] {κ : Sort*}

theorem restrict_iSup_eq (μ : κ → Measure α) {S : Set α} (hS : MeasurableSet S) :
    (⨆ i, μ i).restrict S = ⨆ i, (μ i).restrict S := by
  refine le_antisymm ?_ (iSup_le fun i => Measure.restrict_mono subset_rfl (le_iSup μ i))
  have h : (⨆ i, μ i) ≤ (⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [← Measure.restrict_add_restrict_compl (μ := μ i) hS, Measure.add_apply, Measure.add_apply]
    exact add_le_add (Measure.le_iff'.1 (le_iSup (fun i => (μ i).restrict S) i) B)
      (Measure.le_iff'.1 (Measure.restrict_mono subset_rfl (le_iSup μ i)) B)
  calc (⨆ i, μ i).restrict S ≤ ((⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ).restrict S :=
        Measure.restrict_mono subset_rfl h
    _ = (⨆ i, (μ i).restrict S).restrict S := by
        rw [Measure.restrict_add, Measure.restrict_restrict hS, Set.inter_compl_self,
          Measure.restrict_empty, add_zero]
    _ ≤ _ := Measure.restrict_le_self

theorem smul_iSup_eq (ν : κ → Measure α) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    c • (⨆ i, ν i) = ⨆ i, c • ν i := by
  have mono : ∀ (d : ℝ≥0∞) {μ μ' : Measure α}, μ ≤ μ' → d • μ ≤ d • μ' := fun d μ μ' h =>
    Measure.le_iff.2 fun s _ => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl <| Measure.le_iff'.1 h s
  rcases eq_or_ne c 0 with rfl | h0
  · simp only [zero_smul]
    exact (le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)).symm
  refine le_antisymm ?_ (iSup_le fun i => mono c (le_iSup ν i))
  have key : (⨆ i, ν i) ≤ c⁻¹ • ⨆ i, c • ν i := iSup_le fun i => by
    calc ν i = c⁻¹ • c • ν i := by rw [smul_smul, ENNReal.inv_mul_cancel h0 hc, one_smul]
      _ ≤ _ := mono _ (le_iSup (fun i => c • ν i) i)
  calc c • (⨆ i, ν i) ≤ c • c⁻¹ • ⨆ i, c • ν i := mono c key
    _ = _ := by rw [smul_smul, ENNReal.mul_inv_cancel h0 hc, one_smul]

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {n : ℕ}

theorem chartMeas_restrict_eq (e : OpenPartialHomeomorph X (V n)) {ρ ρ' : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S) (h : ∀ y ∈ e.source, y ∈ S → ρ y = c * ρ' y) :
    (chartMeas e ρ).restrict S = c • (chartMeas e ρ').restrict S := by
  ext B hB
  rw [Measure.smul_apply, Measure.restrict_apply hB, Measure.restrict_apply hB, smul_eq_mul,
    chartMeas_apply e ρ (hB.inter hS), chartMeas_apply e ρ' (hB.inter hS), ← lintegral_const_mul' c _ hc]
  refine setLIntegral_congr_fun (measurableSet_image e (e.open_source.measurableSet.inter (hB.inter hS))
    Set.inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  show ρ (e.symm (e y)) = c * ρ' (e.symm (e y))
  rw [e.left_inv hy.1]
  exact h y hy.1 hy.2.2

theorem glueMeas_restrict_eq {ι : Type*} (e : ι → OpenPartialHomeomorph X (V n)) {ρ ρ' : ι → X → ℝ≥0∞}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S)
    (h : ∀ i, ∀ y ∈ (e i).source, y ∈ S → ρ i y = c * ρ' i y) :
    (glueMeas e ρ).restrict S = c • (glueMeas e ρ').restrict S := by
  rw [glueMeas, glueMeas, restrict_iSup_eq _ hS, restrict_iSup_eq _ hS, smul_iSup_eq _ hc]
  exact iSup_congr fun i => chartMeas_restrict_eq (e i) hc hS (h i)

end General

end GlobalTheory.ChernScale

namespace GlobalTheory.GoodMetric

open GlobalTheory.ChernScale

theorem hasChernIntegral_of_eq_mul : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R R₀ : MvPolynomial (ι × ℕ) ℝ) (t v : ℝ),
    (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      chernTop R (fun w => H A (c.e.symm w)) (c.e y) = t * chernTop R₀ (fun w => H A (c.e.symm w)) (c.e y)) →
    HasChernIntegral E O H R₀ v → HasChernIntegral E O H R (t * v) := by
  intro F _ σ X ι m E O H R R₀ t v hRt hv
  have hP : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  have key : ∀ (ε ε' : ℤˣ) (c : ℝ), 0 ≤ c → (∀ x : ℝ, ((ε : ℤ) : ℝ) * (t * x) = c * (((ε' : ℤ) : ℝ) * x)) →
      chernTopPart E H R ε (ptsIn X.str σ O) =
        ENNReal.ofReal c * chernTopPart E H R₀ ε' (ptsIn X.str σ O) := by
    intro ε ε' c hc hx
    have hm : (chernTopPart E H R ε).restrict (ptsIn X.str σ O) =
        ENNReal.ofReal c • (chernTopPart E H R₀ ε').restrict (ptsIn X.str σ O) :=
      glueMeas_restrict_eq _ ENNReal.ofReal_ne_top hP fun a y hy hyS => ?_
    · have := congrArg (fun μ : Measure (CxPts X.str σ) => μ (ptsIn X.str σ O)) hm
      simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self] using this
    · have e1 := hRt y hyS a hy _ (E.nonempty (under y)).choose_spec
      beta_reduce
      rw [e1, hx, ENNReal.ofReal_mul hc]
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε ε t ht (fun x => by ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 ε)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 1 t ht (fun x => by ring), key (-1) (-1) t ht (fun x => by ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
      ring
  · have ht' : 0 ≤ -t := by linarith
    refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε (-ε) (-t) ht' (fun x => by rw [Units.val_neg, Int.cast_neg]; ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 _)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 (-1) (-t) ht' (fun x => by push_cast; ring), key (-1) 1 (-t) ht' (fun x => by push_cast; ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht']
      ring

end GlobalTheory.GoodMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasEigEigOfType
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows

noncomputable section

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def eigOfType (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ :=
  principalLevelFrame.cOfT (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π))

def HasEig (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  principalLevelFrame.IsEigOf (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π)) c

theorem hasEig_eigOfType {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} {π : D.what₂.FT} (h : ∃ c, HasEig R F Y π c) :
    HasEig R F Y π (eigOfType R F Y π) := by
  unfold eigOfType principalLevelFrame.cOfT
  unfold HasEig at h ⊢
  rw [dite_eq_left h]
  exact h.choose_spec

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineSpaceCoveredMorphismStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineSpaceCoveredMorphism : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → AffCover M M' φ f (Fintype.card J - 1) := by
  first | exact @GlobalTheory.FlagBundle.ProjBundle.affCover | exact GlobalTheory.FlagBundle.ProjBundle.affCover | (intros; apply GlobalTheory.FlagBundle.ProjBundle.affCover <;> assumption)
end

