module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0422
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatIntegrandLocalFactorSplitsTwistPlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0377
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingOfSg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.MainNotions.S Formalism.IndefR.Mult in
theorem GlobalTheory.SeeSaw.exists_isJ_of_par {D : D7} {u : D.what₂.Word}
    (hsg : ∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i)
    {par} (M : DSModel D.sp.X' par) (hpar : par = parB (Ptw D) D.R.m) :
    ∃ j, GlobalTheory.Core.Rk.Top.IsJ u M j := by
  subst hpar
  obtain ⟨j, hj⟩ := GlobalTheory.Core.Rk.Top.exists_isJ D u M
  exact ⟨j, hj hsg⟩

theorem GlobalTheory.SeeSaw.sg_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (τ) :
    ((((I.rec7 l Z).fm u).sg τ).w i : ℚ) =
      sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  have h2 := (TC.tup_sgHC_eq (B.hcW u τ) i).trans
    (congrArg (fun P => Formalism.L2.Col.RowPar.sgHC P i) (TC.tup_rowPar_eq B u τ))
  exact (Formalism.L2.Col.RowPar.sg_eq (B.hc τ) i).trans (congrArg (· - _) h2.symm)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatIntegrandLocalFactorSplitsTwistPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatIntegrand_localFactor_splits_twistPlace : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ a, IsMajOf c s a → ∀ (u₁ u₂ : s.CC c) φ, IsQ w k u₁ → ∀ v₁ ∈ s.KF, ∀ v₂ ∈ s.KF, ∀ z : ℝ, (D.R.t : ℝ) / 2 - 1 < z → ∀ PP ∈ w.Q, ∃ (J : Subgroup (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) (μ : Measure (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) (ζ : GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → ℂ), IsOpen (J : Set (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧ Integrable ζ μ ∧ (∀ y ∈ J, ζ y = 1) ∧ (∀ g, gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG s.V s.β s.L ↔ GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g ∈ J) ∧ (z = (D.R.t : ℝ) / 2 → ∫ y, ζ y ∂μ = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) ∧ ∀ x ∈ intOff c s, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x = 1 → ∀ y, flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) y) = ζ y * flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z x := by
  first | exact @GlobalTheory.ChainTw.OnePlace.local_factor | exact GlobalTheory.ChainTw.OnePlace.local_factor | (intros; apply GlobalTheory.ChainTw.OnePlace.local_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTypePlacesOfLevCh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ComCols

variable {D : D7}

theorem isTypePlaces_of_levCh {L : LevCh D Unit} (hL : L.Is ()) : GlobalTheory.Core.Mi.IsTypePlaces L.Pg := by
  classical
  refine ⟨fun PP hPP => ?_, fun v hv => ?_⟩
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h1
    · exact Ideal.mul_mem_left _ _ h1
  · have := v.isMaximal
    obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    let W : Formalism.L2.DIV.Pl D.host.E := ⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
    have hW : W.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQ'.over.symm
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal := by
      rw [← hW] at hv
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ W.asIdeal := hv
      rw [map_natCast, Nat.cast_mul] at h2
      exact (W.isPrime.mem_or_mem h2).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    have hS := GlobalTheory.ChainOnto.Model.mem_S hL (GlobalTheory.Member.exists_isInfFam_family D).choose 1 L.triv k W hk
    unfold GlobalTheory.ChainOnto.Com.S at hS
    obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hS
    refine ⟨P, ⟨hP, e.trans hW⟩, ?_⟩
    rintro P' ⟨hP', e'⟩
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (e'.trans (e.trans hW).symm) with h | h
    · exact h
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h) (GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hP) (Or.inl hP'))

theorem com_is_of_levCh {L : LevCh D Unit} (hL : L.Is ()) (c : GlobalTheory.ChainOnto.Com D) (hθ : IsInfFam c.θ) (hψ : IsStdChar D c.ψ (-1))
    (hP : c.Pg = L.Pg) (hμ : ∀ j : Fin D.R.m, ChrEq (c.μ ((j : ℕ) + 1)) (L.C.mu0 j)) (hη : ChrEq c.η L.C.eta)
    (hχ : ∀ j : Fin D.R.m, ∀ PP ∈ c.Pg, IsRes (L.C.mu0 j) PP (c.chi ((j : ℕ) + 1) PP)⁻¹) : c.Is := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D c.η L.C.eta hη L.C.isEta
  have hS : ∀ (k : Fin 2) (Q : Formalism.L2.DIV.Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      Q.under (𝓞 D.host.F) ∈ c.S := fun k Q hk => by
    have := GlobalTheory.ChainOnto.Model.mem_S hL c.θ c.ψ L.triv k Q hk
    unfold GlobalTheory.ChainOnto.Com.S at this ⊢
    rw [hP]
    exact this
  refine ⟨hθ, hψ, ⟨hη.1, GlobalTheory.Mem.TupChar.unramEverywhere hη L.C.isEta.unr, ⟨⟨_, hres⟩, fun η h a => ?_⟩, fun τ => ?_,
    fun j hj => ?_⟩, fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hχ j⟩, ?_⟩
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : i < D.R.m := by omega
    refine ⟨(hμ ⟨i, hi⟩).1, ⟨_, hres⟩, fun η _ a => ?_⟩
    show c.μ (i + 1) (idF D a) = _
    rw [pow_zero]
    exact GlobalTheory.GridWeil.triv_base (hμ ⟨i, hi⟩) (L.C.isMu0 ⟨i, hi⟩).triv a
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (L.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((L.C.isMu0 j).unr w fun k hk => hw (hS k w hk))
  · rw [hP]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun Q hQ Q' hQ' => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hQ) (Or.inl hQ')

end GlobalTheory.SeeSaw.ComCols
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumExistsAtLevelPrimePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.LastSeeSawDatum

section Helpers

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem comb_apply' {S T : HSp D} (c : WO S T →₀ ℂ) (g : WO S T → ℂ) (u : WO S T) :
    comb ψ S T c g u = ∑ x ∈ c.support, c x * (ψ (symplOH S T u x) * g (u + x)) := by
  simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]

theorem isThetaFunO_add' {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := {
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    funext w
    have h1 := congrFun (hU u hu.1 hi) w
    have h2 := congrFun (hU' u hu.2 hi) w
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem heisO_smul' {S T : HSp D} (u : WO S T) (r : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (r • f) = r • heisO ψ S T u f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem heisO_add' {S T : HSp D} (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext w; simp only [heisO, Pi.add_apply]; ring

theorem heisO_zero' {S T : HSp D} (u : WO S T) : heisO ψ S T u (0 : WO S T → ℂ) = 0 := by
  funext w; simp only [heisO, Pi.zero_apply, mul_zero]

theorem isThetaFunO_zero' (S T : HSp D) : IsThetaFunO ψ S T (0 : WO S T → ℂ) := {
  quasi γ w := by simp only [Pi.zero_apply, mul_zero]
  level := ⟨⊤, isOpen_univ, fun u _ _ => heisO_zero' u⟩
  cont := continuous_const
  smooth k L hL hfin w := by simp only [Pi.zero_apply]; exact contDiff_const }

theorem isThetaFunO_smul' {S T : HSp D} (r : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (r • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul', hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := by
    simp only [Pi.smul_apply, smul_eq_mul]; exact contDiff_const.mul (hf.smooth k L hL hfin w) }

variable {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}

theorem vac_zero : Vac ψ S T LS LT P 0 :=
  ⟨isThetaFunO_zero' S T, fun u _ => heisO_zero' _, fun e _ u _ _ => heisO_zero' _⟩

theorem vac_add {f g : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) (hg : Vac ψ S T LS LT P g) :
    Vac ψ S T LS LT P (f + g) :=
  ⟨isThetaFunO_add' hf.1 hg.1, fun u hu => by rw [heisO_add', hf.2.1 u hu, hg.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_add', hf.2.2 e he u hu hu', hg.2.2 e he u hu hu']⟩

theorem vac_smul (r : ℂ) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT P (r • f) :=
  ⟨isThetaFunO_smul' r hf.1, fun u hu => by rw [heisO_smul', hf.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_smul', hf.2.2 e he u hu hu']⟩

theorem vac_sum {ι : Type} (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, Vac ψ S T LS LT P (f i)) : Vac ψ S T LS LT P (∑ i ∈ s, r i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (vac_zero : Vac ψ S T LS LT P 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact vac_add (vac_smul _ (h a (Finset.mem_insert_self a s))) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem comb_smul_fun (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext u
  simp only [comb_apply', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem comb_sum_fun {ι : Type} (c : WO S T →₀ ℂ) (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ) :
    comb ψ S T c (∑ i ∈ s, r i • f i) = ∑ i ∈ s, r i • comb ψ S T c (f i) := by
  funext u
  simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem comb_swap {A S X : HSp D} (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ) (G : WO A S → WO S X → ℂ)
    (u : WO A S) (x : WO S X) :
    comb ψ S X c' (fun x' => comb ψ A S c (fun u' => G u' x') u) x =
      comb ψ A S c (fun u' => comb ψ S X c' (G u') x) u := by
  simp only [comb_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Helpers

theorem lastDatum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (Ψ : Matrix n n' k → ℂ) (LA : Lat A) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ), CombAt (· = p.v) c → CombAt (· = p.v) c' → (∀ f₀, Vac ψ A S LA LS (· = p.v) f₀ → Over ψ α β LA LS f₀ Ψ (comb ψ A S c f₀)) → (∀ f₀, Vac ψ S X LS LX (· = p.v) f₀ → Over ψ β γ₀ LS LX f₀ (phiOne (ε • Q) (lastPair q Λ)) (comb ψ S X c' f₀)) → ∃ (e : WO A S →₀ ℂ) (e' : WO S X →₀ ℂ), CombAt (· = p.v) e ∧ CombAt (· = p.v) e' ∧ ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → BiVacAt ψ LA LS LX (· = p.v) (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) ∧ lastBi o o'' τ Ξ Φ₂ = biComb ψ A S X c c' (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hIC n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := GlobalTheory.T.lastSeesaw_datum_eq_lattice_pair_over_vacuum D k p q ψ hψ hU χ hχ hIC n n' n'' V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LA LS LT LX hLA hLS hLT hLX hβQ hγΛ c c' hc hc' hcv hcv'
  obtain ⟨e, he, heP⟩ := _root_.GlobalTheory.FinPl.DatumBack.datumBack D k p n n' ψ hψ hU A S α β LA LS hLA hLS Ψ c hc hcv
  obtain ⟨e', he', heP'⟩ := _root_.GlobalTheory.FinPl.DatumBack.datumBack D k p (n'' ⊕ Fin 1) n ψ hψ hU S X β γ₀ LS LX hLS hLX _ c' hc' hcv'
  refine ⟨e, e', he, he', ?_⟩
  intro L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂
  have ha : charInd (resChar χ hχ q) Q ≠ 0 := by
    intro h
    have hev : Q.ev 0 = 0 := by
      unfold Pair.ev
      rw [dite_eq_left Q.lat.zero_mem]
      exact map_zero Q.fn
    have h0 := congrFun h 0
    simp only [charInd, vecInd, hev, neg_zero, AddChar.map_zero_eq_one, Q.lat.zero_mem, if_true, mul_one,
      Pi.zero_apply] at h0
    exact one_ne_zero h0
  have hA : ∀ y : WO L S, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) ∧
      comb ψ A S c (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) = fun u => Ξ ((o.resS S).symm (u, y)) := by
    intro y
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.LastSrcSlice.main D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ _ ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
    exact heP g _ hg
  have hcol : ∀ x, (fun u => lastBi o o'' τ Ξ Φ₂ u x) =
      Φ₂ (o''.resT S x).1 • fun u => Ξ ((o.resS S).symm (u, kap τ S (o''.resT S x).2)) := by
    intro x; funext u; rfl
  have hAc : ∀ x, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) ∧
      comb ψ A S c (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) = fun u => lastBi o o'' τ Ξ Φ₂ u x := by
    intro x
    rw [hcol x, comb_smul_fun, comb_smul_fun]
    exact ⟨vac_smul _ (hA _).1, by rw [(hA _).2]⟩
  have hX : ∀ u, Vac ψ S X LS LX (· = p.v) (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) ∧
      comb ψ S X c' (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) = lastBi o o'' τ Ξ Φ₂ u := by
    intro u
    obtain ⟨g, hg⟩ := hε α α₀ β γ γ₀ hα hγ Q Λ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
    exact heP' g _ hg
  generalize lastBi o o'' τ Ξ Φ₂ = C at hAc hX ⊢
  refine ⟨⟨fun x => ?_, fun u => ?_⟩, ?_⟩
  · have e1 : (fun u' => comb ψ S X e' (C u') x) =
        ∑ j ∈ e'.support, (e' j * ψ (symplOH S X x j)) • fun u' => C u' (x + j) := by
      funext u'
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u' => comb ψ S X e' (C u') x))
    rw [e1, comb_sum_fun]
    exact vac_sum _ _ _ fun j _ => (hAc (x + j)).1
  · have e2 : (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u) =
        ∑ i ∈ e.support, (e i * ψ (symplOH A S u i)) • comb ψ S X e' (C (u + i)) := by
      funext x
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ S X LS LX (· = p.v) (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u)
    rw [e2]
    exact vac_sum _ _ _ fun i _ => (hX (u + i)).1
  · funext u x
    have hsw : ∀ u', comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x =
        comb ψ A S e (fun u'' => C u'' x) u' := by
      intro u'
      have h1 := comb_swap (ψ := ψ) e c' (fun u'' x' => comb ψ S X e' (C u'') x') u' x
      beta_reduce at h1
      rw [h1]
      congr 1
      funext u''
      exact congrFun (hX u'').2 x
    show C u x = comb ψ A S c (fun u' => comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x) u
    simp only [hsw]
    exact (congrFun (hAc x).2 u).symm

end GlobalTheory.LastSeeSawDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveMain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RLatMove

theorem card_eq_of_frame {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) : Fintype.card Y = n := by
  apply le_antisymm
  · calc Fintype.card Y = (1 : Matrix Y Y k).rank := Matrix.rank_one.symm
      _ = (F.γ * F.β).rank := by rw [F.γβ]
      _ ≤ F.γ.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_width _
      _ = n := Fintype.card_fin n
  · calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
      _ = (1 : Matrix (Fin n) (Fin n) k).rank := Matrix.rank_one.symm
      _ = (F.β * F.γ).rank := by rw [F.βγ]
      _ ≤ F.β.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card Y := Matrix.rank_le_card_width _

def frameGL {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) (B : GL Y k) (σ : Fin n ≃ Y) : GL (Fin n) k where
  val := (F.β * B.val).submatrix id σ
  inv := ((B⁻¹).val * F.γ).submatrix σ id
  val_inv := by
    rw [Matrix.submatrix_mul_equiv (F.β * B.val) ((B⁻¹).val * F.γ) id σ id]
    have : F.β * B.val * ((B⁻¹).val * F.γ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc B.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul, F.βγ]
    rw [this, Matrix.submatrix_id_id]
  inv_val := by
    have h := Matrix.submatrix_mul_equiv ((B⁻¹).val * F.γ) (F.β * B.val) σ (Equiv.refl (Fin n)) σ
    simp only [Equiv.coe_refl] at h
    rw [h]
    have : (B⁻¹).val * F.γ * (F.β * B.val) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    rw [this, Matrix.submatrix_one_equiv]

theorem frameGL_val {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) (B : GL Y k) (σ : Fin n ≃ Y) :
    (frameGL F B σ).val = (F.β * B.val).submatrix id σ := rfl

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

theorem finJ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : PkHyp W) : Finite {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := by
  haveI := hW.fin
  have : {PP | PP ∈ (pk W).Pg ∨ QAll W PP} = ((pk W).Pg : Set _) ∪ ⋃ t, ((pk W).Q t : Set _) := by
    ext PP; simp [QAll]
  have hf : Set.Finite {PP | PP ∈ (pk W).Pg ∨ QAll W PP} := by
    rw [this]; exact (Finset.finite_toSet _).union (Set.finite_iUnion fun t => Finset.finite_toSet _)
  exact hf.to_subtype

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

theorem move_main : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j)) → ∃ b : ∀ j, GA D (Yc D j), (∀ j, b j ∈ GfC (Yc D j)) ∧ (∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (N j) P) ∧ ∀ PP h j c (hc : j + c = (l PP h).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (l PP h).q) (Yc D j) (b j) ((pk W).βY j) (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hz hτ hNT hζ hLT hgP htP hdisj hPre hOrth hbas FY N hN hInt
  classical
  haveI : Finite {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := finJ W hW
  letI : Fintype {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP} => (l i.1 i.2).q.v) := by
    intro i i' hii
    apply _root_.GlobalTheory.Fam.PlaceInj.under_injective W hW
    simp only at hii
    rwa [(l i.1 i.2).under, (l i'.1 i'.2).under] at hii
  have key : ∀ j, j < D.R.m → ∃ t ∈ GfC (Yc D j),
      (∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
        GlobalTheory.FinPl.Moves (Yc D j) t ((pk W).ΛY j) (N j) P) ∧
      ∀ PP h c (hc : j + c = (l PP h).s + 1),
        ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
          GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧
          MovedTo (ofSplit (l PP h).q) (Yc D j) t ((pk W).βY j)
            (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id
              fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
    intro j hj
    have hsj : ∀ PP h, j + ((l PP h).s + 1 - j) = (l PP h).s + 1 := fun PP h => by
      have := (l PP h).hs; omega
    have hE : ∀ PP h, ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
        GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e := by
      intro PP h
      obtain ⟨eqv, heqv⟩ := GlobalTheory.SymBridge.PhiAgreeProof.zPos_equiv D.R.k ((l PP h).s + 1) D.R.t j
      have hcard := card_eq_of_frame (FY PP h j _ (hsj PP h))
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod] at hcard
      have hr : D.R.k + ((l PP h).s + 1) + j * D.R.t = (Yc D j).rank := by
        rw [← hcard]; have := hsj PP h; omega
      exact ⟨eqv.trans (finCongr hr), fun x => by simp [heqv]⟩
    choose E hEo using hE
    let σ : ∀ PP h, Fin (Yc D j).rank ≃ (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((l PP h).s + 1 - j)) :=
      fun PP h => (E PP h).symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) j _ (hsj PP h))
    let M : ∀ i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP}, GL (Fin (Yc D j).rank) (l i.1 i.2).k :=
      fun i => frameGL (FY i.1 i.2 j _ (hsj i.1 i.2)) (bas i.1 i.2 j _ (hsj i.1 i.2)) (σ i.1 i.2)
    have hsd := _root_.GlobalTheory.Fam.sdY_frames W hW j hj
    obtain ⟨t, ht, Lt, hLt, hMv, hAgree, hMT⟩ := _root_.GlobalTheory.FinPl.BasePoint.exists_move D (Yc D j) ((pk W).ΛY j) (N j) ((pk W).βY j)
      hsd.1 (hN j hj) {PP // PP ∈ (pk W).Pg ∨ QAll W PP} (fun i => (l i.1 i.2).k)
      (fun i => (l i.1 i.2).q) hinj M
    refine ⟨t, ht, ?_, ?_⟩
    · intro P hP
      have hloc : ∀ w, P w → GlobalTheory.FinPl.latV (Yc D j) Lt (· = w) = GlobalTheory.FinPl.latV (Yc D j) (N j) (· = w) := by
        intro w hw
        by_cases hex : ∃ i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP}, (l i.1 i.2).q.v = w
        · obtain ⟨⟨PP, h⟩, rfl⟩ := hex
          have hPg : PP ∉ (pk W).Pg := fun hPg => hP _ hw ((hgP _).2 ⟨PP, hPg, (l PP h).under⟩)
          have hb := hbas PP h hPg j _ (hsj PP h)
          have hm := hMT ⟨PP, h⟩
          have hval : (M ⟨PP, h⟩).val = (FY PP h j _ (hsj PP h)).β.submatrix id (σ PP h) := by
            simp only [M, frameGL_val, hb, Units.val_one, Matrix.mul_one]
          rw [hval] at hm
          exact _root_.GlobalTheory.SplitFrameLat.latV_eq (Yc D j) t ((pk W).ΛY j) Lt (N j) ((pk W).βY j) _ (l PP h).q _
            (FY PP h j _ (hsj PP h)) (σ PP h) ht hsd.1 hsd.2 hLt (hN j hj) (hMv _) hm
            (hInt PP h j _ (hsj PP h))
        · push_neg at hex
          exact hAgree w (fun i => (hex i).symm)
      have hEq := GlobalTheory.T.latticeCompletion_eq_of_local_agreement (Yc D j) Lt (N j) P hLt.1 (hN j hj).1 hloc
      have := hMv P
      unfold GlobalTheory.FinPl.Moves at this ⊢
      rwa [← hEq]
    · intro PP h c hc
      obtain rfl : c = (l PP h).s + 1 - j := by omega
      exact ⟨E PP h, hEo PP h, hMT ⟨PP, h⟩⟩
  choose T hT hMovesT hFrT using key
  refine ⟨fun j => if h : j < D.R.m then T j h else 1, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j < D.R.m
    · simp only [dif_pos h]; exact hT j h
    · simp only [dif_neg h]; exact one_mem _
  · intro j hj P hP
    simp only [dif_pos hj]
    exact hMovesT j hj P hP
  · intro PP h j c hc
    have hj : j < D.R.m := by have := (l PP h).hs; omega
    simp only [dif_pos hj]
    exact hFrT j hj PP h c hc

end GlobalTheory.RLatMove
end

