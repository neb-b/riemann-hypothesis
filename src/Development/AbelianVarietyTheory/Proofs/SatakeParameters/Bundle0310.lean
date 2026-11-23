module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0309
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownLiftUpLiftPositiveScalarUsedTuplesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downLift_upLift_positiveScalar_usedTuples : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → GlobalTheory.NRows.LamUsed D := by
  first | exact @GlobalTheory.NRows.LamUsedProof.main | exact GlobalTheory.NRows.LamUsedProof.main | (intros; apply GlobalTheory.NRows.LamUsedProof.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundConstantOneOfChainAgreement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

namespace GlobalTheory.AtG

theorem jetTableBound_constantOne_of_chainAgreement : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D),
    (∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D EX Dx μ) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i) →
    Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant D L EX 1 := by
  intro hJ D L EX Dx hT hS i w hw u hu μ hμ
  exact _root_.GlobalTheory.ColPeriodTies.boundAt_of_ties hJ D L EX Dx μ (hT μ hμ) i (hS i) w hw u hu

end GlobalTheory.AtG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoiceStepZeroChartsGood
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwU.AtTrue.charts_zero_good : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ Kc : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1) ∧ (∀ β, (Kc β).lev.Lb = F.to0.cls0.lev.Lb ∧ (Kc β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (Kc β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (Kc β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (Kc β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((Kc ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hStd
  obtain ⟨K0, hR, hEq, hy⟩ := GlobalTheory.T.columnTuple_stepZero_read_by_memberLevel I hI hP l Z u F a Q hQ hStd
  obtain ⟨N, hN, hNc⟩ := GlobalTheory.unipotent_type_character_finite_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F.to0.glev0 ℂ (RingHom.id ℂ)
    (fun i => (I.rec7 l Z).host.g_prime i) (fun i => ⟨_, Complex.isPrimitiveRoot_exp _ ((I.rec7 l Z).host.g_prime i).ne_zero⟩)
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  haveI : NeZero (B.R.N 0) := ⟨(B.R.N_pos 0).ne'⟩
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hgr, -, -⟩ := hc 0 (Nat.zero_le _)
  have hB := basePi_of_ok hX hPr u
  have hLb : ∀ β, (K0 β).lev.Lb = baseLb B.fields.E (B.R.N 0) ((B.primes X).vT u) := fun β => by
    obtain ⟨k, hk⟩ := hR.readsK
    ext x
    exact (hk.lb β x).trans (GlobalTheory.Mem.Col2.Reside.mem_baseLb hPr u _ x).symm
  have hlaws := fun β => GlobalTheory.Mem.Col2.Reside.swapLaws B.sp.cm hB (hPr.T_prime u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => by simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hPr.vT_norm u P hP) hgr (K0 β).lev (hLb β)
  choose hl hk using hlaws
  refine ⟨fun β => { K0 β with lev := GlobalTheory.Mem.Col2.Reside.swap (K0 β).lev _ (hl β) }, ⟨hR, fun β => ⟨hk β, N, hN, fun κ => ?_⟩⟩, fun β => hEq β, hy⟩
  have hm : κ.1 ∈ F.to0.cls0.lev.U := (hEq β).2.2.1 ▸ κ.2
  have e := (hEq β).2.2.2 κ ⟨κ.1, hm⟩ rfl
  show (K0 β).lev.chi κ ^ N = 1
  rw [e]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact (hNc _).1)
end

