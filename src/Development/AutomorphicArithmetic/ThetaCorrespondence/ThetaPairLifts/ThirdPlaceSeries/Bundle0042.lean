module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWExportSmallStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_export_all_data_small_has : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Nonempty (GlobalTheory.SeriesTie.ExportTie (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).YS (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).v₀) ∧ LevelIs (p.w.D p.Z).nexp ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).R.eG.trans (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cG) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).P0 (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).ψ0⁻¹ ∧ AllData (p.w.D p.Z).nexp p.O.ex.xd.xd0 ∧ SmallHas (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf := by
  first | exact @_root_.GlobalTheory.sideW_export_small_alt | exact _root_.GlobalTheory.sideW_export_small_alt | (intros; apply _root_.GlobalTheory.sideW_export_small_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamAtInertStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eigen_compatibility_fourth_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ s : GlobalTheory.DownLift.Sys D, GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
  intro _ _ D P X _ _ _ _ i _ j _ _ _ _ _ y _ hy h hops s hs w hw _
  obtain ⟨B, hB⟩ :=
    GlobalTheory.DownLift.Params.paramsV X.R X.given.core j (X.tupT (D.nd.mu i)) h hops s y hs hy
  exact ⟨B w, hB _ hw w rfl⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamSplitStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eigen_compatibility_third_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ s : GlobalTheory.DownLift.Sys D, GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
  first | exact @_root_.GlobalTheory.EigStr.sysParam_split_alt | exact _root_.GlobalTheory.EigStr.sysParam_split_alt | (intros; apply _root_.GlobalTheory.EigStr.sysParam_split_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeNZRecOfJoin
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.TypeNZJoin
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
theorem typeNZRec_of_join_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), (∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) →
    ∀ i, GlobalTheory.NJoin.EigString X i → GlobalTheory.NJoin.EigGood X i → GlobalTheory.RowCopy.TypeNZRec D.nd D.naut i := by
  intro hL D P X _ hT i hS hG x hx
  have hμ : Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  obtain ⟨hjPos, hjLe⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.val + 1 = D.nd.j i := Nat.sub_add_cancel hjPos
  exact of_cast (D := D) (μ := D.nd.mu i) hj _
    (fun f hf h0 => inj_at X hT i hS hG hμ j hj x hx f hf h0)
end GlobalTheory.TypeNZJoin
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValInert
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ValInert
theorem val_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∀ c : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} → c = (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) := by
  intro _ hL D P X _ _ _ _ i hμ j hj w hG hI c hc
  have hcw := conjSelf D w hI
  have hLv : X.R.toLevCh.Is X.A.μ0 := X.recR.base.lev
  obtain ⟨hg, -, -⟩ := (GlobalTheory.GoodPrimes.good_primes X.R X.F hLv).2.1 _ w hG
  have hm0 : (X.R.C.mu0 j).UnrAt w := (X.R.C.isMu0 j).unr w fun k hk => hg (by
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk'
    · exact Ideal.mul_mem_left _ _ hk')
  have hxu : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra h
    rcases (hLv.Q_ram _ w).1 h with h | ⟨PP, h, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr h)).2 hc
  have hxi : X.R.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ, xi_eq X.cfEq X.Tp P.tp X.tpEq]
  have hmu : (P.chr.e1 (D.naut.muC i)).1 = X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) := by
    rw [P.chr.muC i j hj, hxi, X.cfEq]
    rfl
  have hu : D.naut.unr (D.naut.locG (D.naut.muC i) w) := (P.chr.unr_iff _ w).2 (by rw [hmu]; exact hm0.mul hxu)
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card _ hu).trans (D.naut.locG_dim _ w))
  have haa : a = a⁻¹ := by
    have e := (D.naut.csd_unr (D.naut.muC i) w w (D.naut.muC_csd i) hcw hu).2
    rw [ha, Multiset.map_singleton] at e
    exact Multiset.singleton_inj.1 e
  have hns := notSplit D w hcw
  have heu := (D.naut.etaTinv_def w).1
  have hee : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(-1 : ℂ)⁻¹} := by
    rw [(D.naut.etaTinv_def w).2, D.naut.etaT_inert w hns, Multiset.map_singleton]
  have hc1 : c = a * (-1 : ℂ)⁻¹ := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu heu (D.naut.locG_dim _ w) hee, ha, Multiset.map_singleton] at hc
    exact (Multiset.singleton_inj.1 hc).symm
  have hcc : c = c⁻¹ := by
    have h1 : (-1 : ℂ)⁻¹ = -1 := by norm_num
    rw [hc1, mul_inv, inv_inv, ← haa, h1]
  have hte : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 =
      X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) * X.R.C.eta⁻¹ := by
    rw [P.chr.tw, hmu, P.chr.etaTinv, X.cfEq]
  have hut : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1.UnrAt w :=
    (P.chr.unr_iff _ w).1 (by rw [D.naut.locG_tw]; exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu heu)
  have hc2 := P.chr.frob _ w hut
  rw [hc] at hc2
  have hc3 : c = (((X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ : ℂˣ) : ℂ)⁻¹ := by
    rw [Multiset.singleton_inj.1 hc2, hte]
    simp
  have hv : GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w =
      (X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ := by
    rw [← GlobalTheory.LFun.val_eq_of_chrEq (hLv.mu0 j) w, ← GlobalTheory.LFun.val_eq_of_chrEq (hLv.xi _) w,
      ← GlobalTheory.LFun.val_eq_of_chrEq hLv.eta w]
    first
      | rfl
      | (simp only [GlobalTheory.DownLift.valV, GlobalTheory.DownLift.chiV, Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, GlobalTheory.LFun.val, GlobalTheory.LFun.locChar]; ext; simp)
      | (unfold GlobalTheory.DownLift.valV GlobalTheory.DownLift.chiV Formalism.IndefR.Lift.chrTh Formalism.IndefR.Links.LevCh.mu Formalism.IndefR.Lift.tup GlobalTheory.LFun.val GlobalTheory.LFun.locChar; simp)
  rw [hv, hcc, hc3, inv_inv]
end GlobalTheory.ValInert
end
end

