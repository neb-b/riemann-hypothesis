module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0703
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0411
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.SiteGoodPrimeTorsion
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulPrIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEquiv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0683
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerIntAtOfSeriesRat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsTwTied
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

theorem WPt.colsTwTied : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), q.O.ex.tw = q.w.tw q.Z ∧ ∃ tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes q.x.n.tp q.x.col.C (q.w.tw q.Z), TC.StdTw q.w.I q.w.l q.Z q.w.l0 tw ∧ Formalism.L2.Rows.EMtTied (q.w.D q.Z) q.x.col.C tw := by
  intro 𝒮 K q
  refine ⟨?_, ?_⟩
  · exact congrArg (fun s : Σ (Gt : GatTies (q.w.D q.Z)) (cmp : LatCmp (q.w.D q.Z)) (tw : TwForms (q.w.D q.Z)),
      KerFam (q.w.D q.Z) Gt cmp tw (ofObj q.O).Gy => s.2.2.1) q.x.ker_eq
  · obtain ⟨tw, htw⟩ := _root_.GlobalTheory.Mem.Col2.TC.colsTwPTiedS_std q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C q.x.n.xi q.x.col.std q.x.col.stdLv
    exact ⟨tw, htw, GlobalTheory.Mem.Col2.EMt.eMtTied q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C tw q.x.what₂.emt0 q.x.what₂.emt⟩

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComparisonDataStepsNonReferenceTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

namespace GlobalTheory.Mem.Top.KerTwLv

theorem fill_of : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      Formalism.MainNotions.G.CmpJ.FillTie t.Gt u v hg (Fl u v hg) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  intro x s b hb
  have h1 := hw u v hg x s (b + 1) (by simp [SizeData₂.lifts]; omega)
  apply (Rat.cast_injective (α := ℝ))
  rw [Formalism.BasicNotions.D7.hcW_e]
  have e : (((((Fl u v hg).w x (b + 1) s : ℤ) : ℚ)) : ℝ) = (((Fl u v hg).w x (b + 1) s : ℤ) : ℝ) := by push_cast; rfl
  rw [e, h1]
  unfold wj G.kaJ wG
  rw [dite_eq_left (by omega)]
  push_cast
  ring

theorem fin_of : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Finite (Formalism.L2.G.compG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram
          (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Uloc ((w.D Z).what₂.places.resChar v)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt _ j hj β
  exact finite_compG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram _ _ _
    (fun x hx => ((tt.ch.lev u _ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).U_eq x).1 hx)
    (tt.ch.finite_cls u _ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β)


set_option maxHeartbeats 4000000 in
theorem cmpJ_data_ne : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  intro hμ
  obtain ⟨tt, htt⟩ := _root_.GlobalTheory.Mem.Col2.TC.colsTwPTiedS_std w.I w.ok w.pins w.l Z w.l0 nch n.tp t.C n.xi t.std t.stdLv
  have hpl := GlobalTheory.T.served_place_no_chain_place_or_type_prime_over w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  obtain ⟨dt, hdt⟩ := GlobalTheory.T.twisted_chart_levels_determinant_maps_values w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hB := GlobalTheory.T.exists_orthonormal_step_basis_base_lattice_charts w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hψ := GlobalTheory.T.exists_chainChart_localUnitCharacter_compatible_level w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hfin := fin_of w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt
  have hfill := fill_of w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  let Cd : GlobalTheory.Mem.Top.KerTwLv.ChData tt.ch t.g.herm u ((w.D Z).what₂.muAt v) v hg :=
    { B := fun j hj => (hB j hj).choose
      fr_lat := fun j hj β => (hB j hj).choose_spec.2 β
      ψ := fun j hj β => (hψ j hj β).choose
      fin := hfin }
  have hhyp := GlobalTheory.T.twisted_chain_charts_hyperspecial_stabilise_lattice w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ tt htt hpl Cd
  let Zt := Formalism.MainNotions.G.KAat.atInTw (X0 := t.g.herm) tt.forms u ((w.D Z).what₂.muAt v) hμ dt (Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1)
  have A : Formalism.MainNotions.G.ChF.HypTies Zt t.Gt t.cmp :=
    { fl_t := (hfl u v hg).1
      fill := hfill
      step := fun j hj =>
        { frRat := fun β => Cd.frRat t.Gt (Fl u v hg) (hfl u v hg).1 j hj β
          sameU := fun β => Cd.sameU tt.forms hμ t.Gt (Fl u v hg) (hfl u v hg).1 dt j hj β
          hypT := fun β => (hhyp j hj β).1
          bad_p := hpl.2.1
          std := (hB j hj).choose_spec.1
          psi := fun β => (hψ j hj β).choose_spec
          chRat := hdt j hj
          hypC := fun β => (hhyp j hj β).2
          ok := hpl.1
          siteGood_prime_torsion := hpl.2.2
          Lb_eq := fun β => Cd.Lb_eq tt.forms hμ t.Gt (Fl u v hg) (hfl u v hg).1 dt j hj β } }
  exact ⟨Cd.Lv t.Gt (Fl u v hg) (hfl u v hg).1, Zt.I t.Gt, A.hyp t.g.cmp, fun j hj => rfl,
    fun j hj => (A.atHyp t.g.cmp).chX j hj, fun j hj => Cd.empty t.Gt (Fl u v hg) (hfl u v hg).1 j hj⟩

end GlobalTheory.Mem.Top.KerTwLv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentificationsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionCompatible_at_readIdentifications : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → (Fintype.card G = D.what₂.restRowsFiniteGroupCard → Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) → GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)) → DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C) ∧ (MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C)) := by
  first | exact @GlobalTheory.divTied3_read | exact GlobalTheory.divTied3_read | (intros; apply GlobalTheory.divTied3_read <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorEmbeddingKappaEqRowsKappaAtInfinitePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorEmbedding_kappa_eq_rowsKappa_at_infinitePlace : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → (∀ σ, Xd.kapR σ = kapSharp D) → ∀ e : D.what₂.LL →+* ℂ, Xd.kapR e = (s1Of R F).κ (InfinitePlace.mk e) := by
  first | exact @GlobalTheory.KapRow.kapR_eq_rows_kappa | exact GlobalTheory.KapRow.kapR_eq_rows_kappa | (intros; apply GlobalTheory.KapRow.kapR_eq_rows_kappa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.BrgRead

set_option maxHeartbeats 1000000

theorem embLL_labLL_eq {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem gram_V (X : Stages) (h : DiagSpaces X.toD7.sp) (i : Fin X.toD7.R.m) : (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.toD7.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem isDualPair_smul {D : D7} {θ : InfFam D} {MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)} {cX : CoefA D.sp.X'}
    {prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ} (h : IsDualPair θ MX cX prX) {c : ℂ} (hc : c ≠ 0) :
    IsDualPair θ MX cX (c • prX) := by
  refine ⟨smul_ne_zero hc h.1, fun τ g hg w v u hu => ?_⟩
  simp only [LinearMap.smul_apply]
  rw [h.2 τ g hg w v u hu]

theorem exists_coefData : ∀ (D : D7), Seed.VPos D → ∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
  ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ)
    (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] cX.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) →ₛₗ[D.what₂.embLL] (cV i).W),
    cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧
    (gramR = D.sp.X'.gram ∨ gramR = -D.sp.X'.gram) ∧
    Bridge.CoefMapTie D.sp.X' cX.coef c0R (rhoV (labLL D) _) ∧
    (∀ i, Bridge.CoefMapTie (Vc D i) (cV i).coef (c0L i) (rhoVr (labLL D) _)) ∧
    (∀ x y, inner ℂ (c0R x) (c0R y) = D.what₂.embLL (pairV (labLL D) _ gramR x y)) ∧
    ∀ i x y, inner ℂ (c0L i x) (c0L i y) = D.what₂.embLL (pairVr (labLL D) _
      (if D.sp.Vneg ((i : ℕ) + 1) then -(Vc D i).gram else (Vc D i).gram) x y) := by
  intro D hV θ hθ MX
  obtain ⟨cX, prX, c0R, gramR, hcX, hdual, hg, hmap, hin⟩ := GlobalTheory.CoefSpace.exists_coef_dualPair D θ MX hθ
  have hL := fun i => GlobalTheory.CoefModel.exists_coef_lift D i (hV i)
  choose cV c0L hcV hmapL hinL using hL
  obtain ⟨c, hc, hiso⟩ := GlobalTheory.PrIsoScale.exists_smul_prIso D θ MX cX prX hθ hcX hdual
  exact ⟨cX, cV, c • prX, gramR, c0R, c0L, hcX, hcV, isDualPair_smul hdual hc, hiso, hg, hmap, hmapL, hin, hinL⟩
theorem hecke_degrees : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px),
    (∀ t P, (famR X I hX U Xg tr).A.heckeR t (P, 0) = 1 ∧
      ∀ k, X.toD7.sp.X'.rank < k → (famR X I hX U Xg tr).A.heckeR t (P, k) = 0) ∧
    (∀ i t P, (famR X I hX U Xg tr).A.heckeL i t (P, 0) = 1 ∧
      ∀ k, (Vc X.toD7 i).rank < k → (famR X I hX U Xg tr).A.heckeL i t (P, k) = 0) := by
  intro X px I hX U Xg tr
  have hk3 := X.B.R.m_add_three_le_k
  refine ⟨fun t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩, fun i t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩⟩
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.X'_rank
    change X.toD7.sp.X'.rank < k at hk
    rw [e] at hk
    change _ < k
    unfold Ranks.rankX' at hk
    unfold Ranks.N
    simp only [Ranks.r] at hk ⊢
    change X.B.R.k + X.B.R.m - 1 + X.B.R.m * X.B.R.t < k at hk
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.V_rank _ (by omega) i.2
    change (X.toD7.sp.V ((i : ℕ) + 1)).rank < k at hk
    rw [e] at hk
    exact hk

theorem exists_brgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∃ (cX : CoefA X.toD7.sp.X') (cV : ∀ i, CoefA (Vc X.toD7 i)) (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ ∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ := by
  intro X px I hX U Xg tr L eG hI hV hL hG hβX hβV hsX hsV θ hθ MX
  have hVP : Seed.VPos X.toD7 := fun i => X.B.V_posDef _ (by omega) i.2
  obtain ⟨cX, cV, prX, gramR, c0R, c0L, hcX, hcV, hdual, hiso, hgram, hmapR, hmapL, hinR, hinL⟩ :=
    exists_coefData X.toD7 hVP θ hθ MX
  have hR := GlobalTheory.T.exists_rowForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hmapR hinR hβX hsX
  have hLf := fun i => GlobalTheory.T.exists_liftForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cV i (c0L i) (hcV i) (hmapL i) (hinL i) (hβV i)
    (gram_V X hI.spaces i) (hsV i)
  obtain ⟨sR, hsR, hstR⟩ := hR
  choose sL hsL hstL using hLf
  obtain ⟨hok, hon, hit, hion⟩ := GlobalTheory.Mem.R3.famR_places X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hmu, heta, hroots⟩ := GlobalTheory.Mem.R3.Brg.values X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hdR, hdL⟩ := hecke_degrees X px I hX U Xg tr
  have hrk : X.toD7.sp.X'.rank = (famR X I hX U Xg tr).A.r + X.toD7.R.m * (famR X I hX U Xg tr).A.t := X.toD7.sp.X'_rank
  have hrkL : ∀ i : Fin X.toD7.R.m, (Vc X.toD7 i).rank = (famR X I hX U Xg tr).A.r + (famR X I hX U Xg tr).A.t :=
    fun i => X.toD7.sp.V_rank _ (by omega) i.2
  let B : Seed.BType (famR X I hX U Xg tr) L cX cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) :=
    { R := sR, L := fun i t => sL i t, rankR := hrk, rankL := hrkL }
  classical
  refine ⟨cX, cV, fun P => P.1, L.Pg, B, fun Q => Q.1, L.Pg.image (fun PP => PP.under (𝓞 X.toD7.host.F)), prX,
    hcX, hcV, hdual, hiso, ?_, hstR, hstL⟩
  exact
    { red_R := fun t q => (hsR t).1 q
      red_L := fun i t q => (hsL i t).1 q
      tie := ⟨gramR, c0R, c0L,
        { ranks := ⟨rfl, rfl, rfl⟩
          v0 := rfl
          tauL_ok := fun τ => RingHom.ext fun x => embLL_labLL_eq τ x
          pl_inj := fun a b h => Subtype.ext h
          q := fun P => rfl
          S_fin := Set.toFinite _
          ok := hok
          gramR_eq := hgram
          mapR := hmapR
          mapL := hmapL
          coefR := fun t => (hsR t).2.1
          coefL := fun i t => (hsL i t).2.1 }⟩
      sb := rfl
      roots := hroots
      pl_onto := hon
      degR := hdR
      degL := hdL
      muVal := hmu
      etaVal := heta
      in_tie := hit
      in_onto := hion
      in_R := fun t => (hsR t).2.2
      in_L := fun i t => (hsL i t).2.2
      in_SF := fun v => by
        simp only [Finset.mem_image]
        refine exists_congr fun PP => and_congr_right fun _ => ?_
        rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal, Ideal.under_def] }

end GlobalTheory.Mem.R3.BrgRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBoundOfPrimitive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SeriesStep
open GlobalTheory.Mem.R3.Tr
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem listPin_oTw (x : St P) (N : TwNew (Dof x))
    (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
    (c b : ℝ) {I : Type}
    (Lc : Formalism.IndefR.Links.LevCh (Dof x) I) (h : ListPin (Dof x) Lc c b) :
    ListPin (w.st (oTw x N).Z).toD7 (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z Lc) c b := by
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G) :)), ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact ((hN _ h2) :))⟩

theorem listSt_oTw (cDep : ℝ) (x : St P) (N : TwNew (Dof x))
    (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
    (x' : St P) (ho : x'.o = oTw x N)
    (hR : HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh))
    (h : ListSt cDep x) : ListSt cDep x' := by
  unfold ListSt
  generalize x'.m.z.R.toRealDat.toLevCh = Lc' at hR ⊢
  revert Lc'
  unfold Dof
  rw [ho]
  intro Lc' hR
  rw [eq_of_heq hR]
  exact listPin_oTw x N hN _ _ _ h

end GlobalTheory.HeightCounting.Up.SeriesStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesIntegralUniformPrimePower
section
namespace GlobalTheory

theorem serInt_outright : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP
  exact ⟨fun u hu c0 hc0 => GlobalTheory.LevelSeries.serIntAt_record D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP u hu c0 hc0, _root_.GlobalTheory.DescIntRoad.descIntAt_of_laws D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP⟩

end GlobalTheory
end

