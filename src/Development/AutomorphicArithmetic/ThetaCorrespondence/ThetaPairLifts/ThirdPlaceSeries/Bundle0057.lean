module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0053
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Development.AutomorphicArithmetic.ResidueCharacters.RowDef
public import Development.AutomorphicArithmetic.ResidueCharacters.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRootSubOneLengthLeTameValue
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0884
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0306
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0557
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Divisibility.Bundle0008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MjReadRealizationEqual
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.Reads
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
set_option maxHeartbeats 2000000 in
theorem mjRead_of_indefinite_down_join (x : TwIn ex) {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) :
    Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y))) := by
  intro i v
  have h1 := x.Y.mjRead i (x.Z.jW i v)
  have h2 := x.Z.jW_read i v
  have h3 : x.Y.mj.eW i (x.Z.jW i v) ∈ LinearMap.range (x.Y.mj.eW i) := ⟨_, rfl⟩
  rw [x.Y.mj.eW_range i] at h3
  have h4 := h3.2
  have h5 : Mult.postOn _ (x.R.toRealDat.eWf i (sg0 D x.A3.A)) ((x.R.HW i (sg0 D x.A3.A)).e (x.Y.mj.eW i (x.Z.jW i v))) =
      (x.R.HW i (sg0 D x.A3.A)).e (x.Y.mj.eW i (x.Z.jW i v)) := sub_eq_zero.1 h4
  refine h1.trans (congrArg _ ?_)
  rw [← h5, h2]
  rfl
set_option maxHeartbeats 4000000 in
theorem mt_mj_read_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), Holds x.R x.F → Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie) ∧ Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y))) := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y _
  exact ⟨liftGroupForms_eq_extended_rationalForms_companion x, _root_.GlobalTheory.Mem.R3.Reads.mjRead_of_indefinite_down_join x y⟩
end GlobalTheory.Mem.R3.Reads
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowGlue
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
variable {D : D7}
end UpperTheory.N
theorem UpperTheory.N.starSF_of_rowC_alt (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) : _root_.UpperTheory.N.RowCAlt A B → _root_.UpperTheory.N.StarSelfDualCondition := by
  intro h eps Fm
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := _root_.GlobalTheory.NLink.admissible_parameters_design_family Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1),
    fun x hxx hx i HW F Cm X C₂ hS k hTw hs h2 π hπ => ?_⟩
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hs h2 π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hc : UpperTheory.N.costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    UpperTheory.N.Num.cost_le (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hs le_rfl
  unfold Bd at hb ⊢
  linarith
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffBad
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SummandEig
theorem offBad_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := _root_.GlobalTheory.T.place_below_good_not_mem_badPl
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj Q Pp hG hS d hd
  obtain ⟨s, α, hov, hα, hR1, hR2⟩ := frameReps D (Formalism.IndefR.Links.Vc D j) D.R.nV hAg.hF (hAg.PV j) (hAg.stdV j) Pp hS d hd
  obtain ⟨c, hc1⟩ := irrScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s α hα _ _ _ hR1 hR2
  have hc := isoScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s.v _ _ _ c hc1
  have hsB : s.v ∉ Formalism.L2.badPl D i := _root_.GlobalTheory.SummandEig.offBad_alt hL D P X i hμ Pp hG s.v hov
  refine ⟨c, fun f' hf' g => ?_⟩
  have hFI : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have h := hf'
    rw [P.H.av.typeV i Q] at h
    exact h
  have hFT : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]
    exact ⟨_, rfl⟩
  have hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      Formalism.L2.NG.rt D.host.E D.R.nV κ ((P.M.loc i).real (hj ▸ f')) = (P.M.loc i).real (hj ▸ f') := by
    intro κ hκ ht
    have ht' : TrivOutside (Formalism.L2.badPl D i)ᶜ κ := fun v hv => ht v fun h => hv (by
      rw [Set.mem_singleton_iff.1 h]
      exact hsB)
    obtain ⟨h1, h2⟩ := P.H.hecke.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := hFT.2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  have hkey := cast_sum P.M (D.nd.mu i) hj _ _ (by omega) (by omega) f' _ _ c (hc _ hFI hfix)
  have hreal : ∀ w, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w)) =
      (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w) := by
    intro w
    rw [hAg.real (D.nd.mu i) hμ j f' (hAg.a j * w), inv_mul_cancel_left]
  have hfin : ∀ w, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' ((hAg.PV j).ψ w * γ) =
      c • X.fn hμ j f' ((hAg.PV j).ψ w) := by
    intro w
    apply (hAg.eW (D.nd.mu i) hμ j).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul, hreal]
    have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w * γ)) =
        Formalism.L2.NG.rt D.host.E D.R.nV (Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
          ((P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f') (hAg.a j * w) := by
      intro γ hγ
      have e2 : (hAg.PV j).ψ w * γ = (hAg.PV j).ψ (w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ) := by
        rw [map_mul, Formalism.IndefR.principalLevelFrame.pre_spec (hAg.PV j) (rep_mem _ Pp d hγ)]
      rw [e2, hreal]
      show _ = (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
      rw [mul_assoc]
    rw [Finset.sum_congr rfl e1, ← Finset.sum_apply, hkey]
    rfl
  obtain ⟨a₀, ha₀, k, hk, rfl⟩ := (_root_.GlobalTheory.AdelicSplitParts.split_parts D (Formalism.IndefR.Links.Vc D j)).1 g
  obtain ⟨w, rfl⟩ := (hAg.PV j).onto k hk
  obtain ⟨y, hy, -⟩ := X.existsUnique_vec hμ j f'
  have hw := hfin w
  rw [← hy] at hw ⊢
  have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
      X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ) =
        (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := fun γ hγ =>
    (congrArg (X.R.extV j (X.tupT (D.nd.mu i)) y) (mul_assoc _ _ _)).trans
      (extV_inf X j _ y ha₀ (mul_mem ((hAg.PV j).into w) (rep_mem _ Pp d hγ)))
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := Finset.sum_congr rfl e1
    _ = (X.R.cV j).ρ a₀⁻¹ (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := (map_sum _ _ _).symm
    _ = (X.R.cV j).ρ a₀⁻¹ (c • X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := congrArg _ hw
    _ = c • (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := map_smul _ _ _
    _ = c • X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w) :=
      congrArg _ (extV_inf X j _ y ha₀ ((hAg.PV j).into w)).symm
end GlobalTheory.SummandEig
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackOfTup
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.Inhab
open GlobalTheory.SymBridge
section Frames
variable {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
end Frames
section True
open GlobalTheory.Mem
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
end True
section Built
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
def realPackageOfInput {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.GlobalTheory.MiS.RealPackAlt ex where
  R := Rc
  S := S
  P := divisionPairOfAdelicFormsFaceColumnsData x
  Dcf := x.F.Dc
  Spf := x.F.Sp
  Zscf := x.F.Zsc
  Ks := x.core.Q.c.F
  Q := _root_.GlobalTheory.Mem.R3.realisationOfInput y
def tupleAtIndex {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (s : W.P.T) : D.what₂.Tup := W.P.I.tup s
theorem used0_tupP_packOf_and_tupT_eq {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) (s : x.T) :
    Formalism.IndefR.RecTie.Used0 D (_root_.GlobalTheory.Fam.Inhab.tupleAtIndex (_root_.GlobalTheory.Fam.Inhab.realPackageOfInput y) s) ∧ x.Y.tupT (_root_.GlobalTheory.Fam.Inhab.tupleAtIndex (_root_.GlobalTheory.Fam.Inhab.realPackageOfInput y) s) = s :=
  ⟨_root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) s, x.Y.tupT_tup s⟩
end Built
end GlobalTheory.Fam.Inhab
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacementOfRealisationStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_nonvanishing_alt : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q → (∀ x : S.X.B.I.E, HEq (S.X.ιE x) x) → _root_.Formalism.IndefR.IndefiniteRealisationExtends Q := by
  first | exact @_root_.GlobalTheory.RowPlacementReal.placement_of_realisation_alt | exact _root_.GlobalTheory.RowPlacementReal.placement_of_realisation_alt | (intros; apply _root_.GlobalTheory.RowPlacementReal.placement_of_realisation_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPins3RealTOf
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.Mem.R3
set_option maxHeartbeats 4000000 in
theorem realPins3_realTOf_alt : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt a.x Rc S), HEq (a.Zsc (zsOf t.r.z.R t.r.z.F)).F0 (F0K K.s (w.D Z)) → _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a Rc S y h
  rw [_root_.Formalism.IndefR.Pins3.realPins3_iff_twPl_iff_W1]
  have hr := t.r.z.twisted_places_eq_complex_side_of_eq_nonzero_index (F0K K.s (w.D Z)) t.exact.symm t.r.z.R.kap a.lam a.err a.Dc a.Sp a.Zsc 0 0 (eq_of_heq h)
  show ∀ v, v ∈ a.x.R.twPl ↔ (a.x.R.toCx3 a.x.F).W1 a.x.F.cr (a.x.R.num a.x.F 0 0) v
  clear y h
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  dsimp only at hr ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hr
end GlobalTheory.Mem.R3
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPinsRealTOf
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3
set_option maxHeartbeats 4000000 in
theorem realPins_realTOf_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), x.R.C = Rc.T.n.cf → (∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i)) → (open Classical in x.R.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE)) → y.tS ∈ Formalism.L2.Theta.GfC (Yc D 0) → Formalism.IndefR.AutomorphicEvaluation.ConjLevel y.tS⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (y.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (y.ιS k)) → Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt x.R.toRealDat x.F.lv2 S.X y.instEq y.tS → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y hC hD hPg hfin hLev hRow
  exact
    { cfEq := hC
      qGuard := x.pins.keep.guard
      hF := x.Y.hF
      phsOne := x.pins.phs
      prXunit := x.pins.keep.prX
      grpRecPin := x.pins.keep.grp
      fdiag := hD
      pgEq := hPg
      tSfin := hfin
      tSpin := fun _ => ⟨hLev, hRow⟩
      eGtie := rfl
      betaStd := x.pins.keep.beta
      bR_read := fun _ _ => rfl }
end GlobalTheory.Mem.R3
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
namespace GlobalTheory.BigTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl Kc Y cX}
namespace PtAt
variable {Csz : ℝ}
set_option maxHeartbeats 1000000 in
def ofReal_alt (P : IndefiniteRowSideFullHecke ex) (Del h0 : ℕ) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs))
    (gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
      ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam)
    {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (B : _root_.Formalism.IndefR.RealTBAlt Rc P.toRowSideFamily Dcf Spf (P.zsc Del h0 Csz) S)
    (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) : PtAt ex Csz :=
  { P := P, Del := Del, h0 := h0, hDel := hDel, hh0 := hh0, Dcf := Dcf, Spf := Spf, gamDvd := gamDvd
    T := B.T, alg := B.alg, R := B.Q.Rl
    charW := B.Q.charW, zs := B.Q.zs, s0 := B.Q.s0, s1 := B.Q.s1, dc := B.Q.dc, stdChar := B.Q.stdChar, signs := B.Q.signs
    cG := B.Q.cG, Sx := B.Q.Sx, nexp := B.Q.nexp, stdV := B.Q.stdV, stdX := B.Q.stdX, host := B.Q.host, err_eq := B.Q.err_eq
    vpos := B.Q.vpos
    κ := B.κ, v₀ := B.v₀, fw := B.fw, bar := B.bar, O := B.O, pins := B.pins, rhoGeo := B.rhoGeo, equivAll := B.equivAll
    cTie := B.cTie, phase := B.phase
    qGuard := Qp.qGuard, hF := Qp.hF, phsOne := Qp.phsOne, prXunit := Qp.prXunit, grpRecPin := Qp.grpRecPin, fdiag := Qp.fdiag
    eGtie := Qp.eGtie, betaStd := Qp.betaStd
    tupT := Qr.tupT, hm := Qr.hm, Tp := Qr.Tp, tupXi := Qr.recR.tupXi, tupAt := Qr.recR.tupAt, tupTie := Qr.tupTie
    tupT_tup := Qr.tupT_tup, muEq := Qr.muEq }
variable (p : PtAt ex Csz)
def RealisedCondition : Prop :=
  ∃ (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc)
    (B : _root_.Formalism.IndefR.RealTBAlt Rc p.P.toRowSideFamily p.Dcf p.Spf (p.P.zsc p.Del p.h0 Csz) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q),
    _root_.Formalism.IndefR.IndefiniteRealisationCompatible Qp Qr ∧ _root_.GlobalTheory.BigTop.PtAt.ofReal_alt p.P p.Del p.h0 p.hDel p.hh0 p.Dcf p.Spf p.gamDvd B Qp Qr = p
structure CompatibilityConditions : Prop where
  real : p.RealisedCondition
  core : GlobalTheory.BigOn.CoreTies L ex.errX p.T p.R.toRealDat
  pb : p.T.pb = p.R.C.P.pb
  types : GlobalTheory.DimPartsCompare.TameTie D p.R.C.W.om
  series : Nonempty (GlobalTheory.SeriesTie.ExportTie p.nexp p.v₀)
  level : p.LevelTie
  data : p.DataTie
  psiVal : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (p.Tp.psi w).ValuesIn 0 D.what₂.embLL
  ray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (Formalism.L2.Host.embLL0 D).fieldRange
  roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange
  rayQ : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel p.R.toRealDat t)
  twist : GlobalTheory.EX.DQ.TwAllAt D ex.nch ex.xd
structure PointConditions' : Prop where
  exAt : p.R.toRealDat.ExAt
  jEvBar : JEvBar p.T p.R.toRealDat p.κ
  geoAct : GeoAct p.T p.R.toRealDat p.κ p.v₀
  evInj : EvInj p.T p.R.toRealDat p.v₀
  ioExt : IoExt p.R.toRealDat
  oneMap : ∀ i, OneMapRowR p.T p.R.toRealDat p.κ p.v₀ p.O (phEff p.R) i
  prim : PrimRows3 p.R p.F
  sep : p.P.A3.fam3.TypesSep3
  ok : p.P.A3.fam3.Ok3 1
  framesOK : Formalism.IndefR.Mi.FramesOKg2 p.R
  divRows : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I
  psi : PsiPPTie D p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.I.eG
  d0 : D.what₂.D0 = (p.P.A3.A.fam.R p.P.A3.A.fam.μ0).dZ (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) (p.P.Zs.Z p.P.A3.A.fam.μ0)
  export_ : p.ExportRow
  goodFT : Formalism.BasicNotions.GoodFTAll D
  w1 : ∀ w, (p.R.toCx3 p.F).W1 p.F.cr (p.N 0 0) w → w ∈ p.R.twPl
  ties : p.CompatibilityConditions
section OfReal
variable {P : IndefiniteRowSideFullHecke ex} {Del h0 : ℕ} {hDel : D.s.Del = (Del : ℚ)} {hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
  {gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
    ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {B : _root_.Formalism.IndefR.RealTBAlt Rc P.toRowSideFamily Dcf Spf (P.zsc Del h0 Csz) S}
  {Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q} {Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q}
end OfReal
namespace Realised
variable {p} (h : p.RealisedCondition)
include h
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.induction {Q : PtAt ex Csz → Prop}
    (hQ : ∀ (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc)
      (B : _root_.Formalism.IndefR.RealTBAlt Rc p.P.toRowSideFamily p.Dcf p.Spf (p.P.zsc p.Del p.h0 Csz) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q),
      _root_.Formalism.IndefR.IndefiniteRealisationCompatible Qp Qr → Q (_root_.GlobalTheory.BigTop.PtAt.ofReal_alt p.P p.Del p.h0 p.hDel p.hh0 p.Dcf p.Spf p.gamDvd B Qp Qr)) : Q p :=
  let ⟨Rc, S, B, Qp, Qr, a, e⟩ := h
  Eq.subst (motive := Q) e (hQ Rc S B Qp Qr a)
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.exists_frame : ∃ Rc : _root_.Formalism.L2.RecTAlt ex, p.R.C = Rc.T.n.cf ∧ HEq p.Tp Rc.T.n.tp ∧ p.R.ψ = Rc.T.theta.W.ψ :=
  h.induction (Q := fun p => ∃ Rc : _root_.Formalism.L2.RecTAlt ex, p.R.C = Rc.T.n.cf ∧ HEq p.Tp Rc.T.n.tp ∧ p.R.ψ = Rc.T.theta.W.ψ)
    fun Rc _ B Qp Qr _ => ⟨Rc, Qp.cfEq, Qr.tpEq, B.Q.psiPin⟩
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.valLL0 : Formalism.L2.Host.ValLL0 D p.R.C := by
  obtain ⟨Rc, e, -⟩ := h.exists_frame
  exact e ▸ Rc.T.chrVal
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.psiChoice : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp := by
  obtain ⟨Rc, e, e', -⟩ := h.exists_frame
  have := Rc.T.chrPsi
  revert e'
  generalize p.Tp = t
  generalize p.R.C = c at e t ⊢
  subst e
  intro e'
  exact eq_of_heq e' ▸ this
end Realised
theorem CompatibilityConditions.eSer {p : PtAt ex Csz} (h : p.CompatibilityConditions) : GlobalTheory.GLq.ESerTie D := h.types.eSerTie
end PtAt
def EventuallyAtPoints {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → Q x hx i p
theorem EventuallyAtPoints.of_forall {eps : ℝ} {Fm : FamP eps} {Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : ∀ x hx i p, p.PointConditions' → Q x hx i p) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q := ⟨0, fun x hx _ => h x hx⟩
theorem EventuallyAtPoints.and {eps : ℝ} {Fm : FamP eps} {Q Q' : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q) (h' : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q') : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => Q x hx i p ∧ Q' x hx i p :=
  let ⟨a, h⟩ := h
  let ⟨b, h'⟩ := h'
  ⟨max a b, fun x hx hle i p hp => ⟨h x hx ((le_max_left _ _).trans hle) i p hp, h' x hx ((le_max_right _ _).trans hle) i p hp⟩⟩
def LambdaLowerBound₂ : Prop := Closed FamHyp fun Fm CH => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ C, (p.S true).L6 (p.N C CH)
end GlobalTheory.BigTop
end
end
end

