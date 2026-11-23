module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueBilinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep.Lin

open GlobalTheory.Core.Mi.SepPer

variable {D : D7}

theorem per_int {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) {f : GA D B.V → ℂ} (hf : f ∈ contLeft B.V) :
    (∀ h, IntegrableOn (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν) ∧
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
  obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := _root_.GlobalTheory.BesselQuot.besGrp_quotient D ρ B
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut B.cpt hφ
  have hμ : B.vA.μ B.vA.𝓕 < ⊤ := GlobalTheory.Unf.vol_fund_lt_top B.cpt B.vA
  have hν1 : B.vN.ν B.vN.𝓝 = 1 := B.vN.unit.2.2
  have hν : B.vN.ν B.vN.𝓝 < ⊤ := by rw [hν1]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  have hemb := GlobalTheory.Unf.BesSemi.continuous_embA B.d B.o
  have hpsi := GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 (vecB B.o B.ζ)
  obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hf.1.continuousOn
  have hsup : ∀ (h : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h)‖ ≤ K := by
    intro h n
    have hs : n.1 * embA B.d B.o h ∈ besGrp B.d B.o :=
      mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)
    obtain ⟨γ, hγ, hγs⟩ := hΩ _ hs
    rw [← hf.2 γ (Subgroup.mem_inf.1 hγ).1]
    exact hK _ hγs
  have hbd : ∀ h n, ‖GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n‖ ≤ Cφ * K := by
    intro h n
    simp only [GlobalTheory.MixPer.besFun, norm_mul, norm_star, norm_psiBes hψ, mul_one]
    exact mul_le_mul (hCφ h) (hsup h n) (norm_nonneg _) ((norm_nonneg _).trans (hCφ h))
  have hcont : ∀ h, Continuous (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) := by
    intro h
    change Continuous fun n : flagN B.d => φ h * f (n.1 * embA B.d B.o h) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)
    exact (continuous_const.mul (hf.1.comp (continuous_subtype_val.mul continuous_const))).mul
      (continuous_star.comp (hpsi.comp continuous_subtype_val))
  have hcontH : ∀ n : flagN B.d, Continuous fun h => GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n := by
    intro n
    simp only [GlobalTheory.MixPer.besFun]
    exact (hφ.2.mul (hf.1.comp (continuous_const.mul hemb))).mul continuous_const
  have houtC : Continuous fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
    haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA B.A
    exact continuous_of_dominated (bound := fun _ => Cφ * K)
      (fun h => (hcont h).aestronglyMeasurable)
      (fun h => Filter.Eventually.of_forall fun n => hbd h n) (integrable_const _)
      (Filter.Eventually.of_forall fun n => hcontH n)
  refine ⟨fun h => Measure.integrableOn_of_bounded hν.ne (hcont h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun n => hbd h n), ?_⟩
  refine Measure.integrableOn_of_bounded (M := Cφ * K * B.vN.ν.real B.vN.𝓝) hμ.ne houtC.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  exact norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd h n

theorem per_add_left {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ₁ φ₂ : GA D B.A → ℂ} (h₁ : IsContAut B.A φ₁) (h₂ : IsContAut B.A φ₂) {f : GA D B.V → ℂ} (hf : f ∈ contLeft B.V) :
    B.per ψ (φ₁ + φ₂) f = B.per ψ φ₁ f + B.per ψ φ₂ f := by
  obtain ⟨i₁, o₁⟩ := per_int B hψ h₁ hf
  obtain ⟨i₂, o₂⟩ := per_int B hψ h₂ hf
  have e : ∀ h n, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ (φ₁ + φ₂) f h n =
      GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ₁ f h n + GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ₂ f h n := by
    intro h n; simp only [GlobalTheory.MixPer.besFun, Pi.add_apply]; ring
  simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
  simp_rw [e]
  rw [← integral_add o₁ o₂]
  exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_add (i₁ h) (i₂ h))

theorem biComb_add (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (K K' : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (K + K') = biComb ψ A S A' c c' K + biComb ψ A S A' c c' K' := by
  funext u v
  simp only [biComb, GlobalTheory.FrComb.comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (a : ℂ) (K : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (a • K) = a • biComb ψ A S A' c c' K := by
  funext u v
  simp only [biComb, GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

end GlobalTheory.TriStep.Lin


open GlobalTheory.TriStep.Lin GlobalTheory.Core.Mi.SepPer in
theorem GlobalTheory.TriStep.valK_bilin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → (∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (Λ Ξ)) → ∃ T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ, ∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1 := by
  intro D ψ hψ σ S Q c₁ c₂ _ _ φ hφ Λ _ hΛ
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hC : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) :=
    fun Ξ => _root_.GlobalTheory.FrCombAny.biTheta_biComb D ψ hψ S.B.A S.J.W₀ S.B'.A (Λ Ξ) (hΛ Ξ) c₁ c₂
  have hA : ∀ Ξ, IsContAut S.B'.A (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ))) :=
    fun Ξ => GlobalTheory.SeeSawLastValue.contAut_biLift hB S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ (hC Ξ)
  have hL : ∀ Ξ Ξ', biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (Ξ + Ξ'))) =
      biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) +
        biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ')) := by
    intro Ξ Ξ'
    funext h₂
    have e := GlobalTheory.SeeSmallPf.biLift_sum hB S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ
      ![biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ), biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ')]
      (fun i => by fin_cases i <;> simp [hC]) h₂
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rw [map_add (f := _), biComb_add, e, Pi.add_apply]
  have hf : ∀ f : GlobalTheory.TriStep.space Q, f.1 ∈ contLeft S.B'.V := by
    intro f
    have := f.2.1 1
    rw [map_one, GlobalTheory.TriStep.rTrans_one] at this
    exact ⟨this.2, this.1⟩
  refine ⟨LinearMap.mk₂ ℂ (fun Ξ f => GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) ?_ ?_ ?_ ?_, fun Ξ f => rfl⟩
  · intro Ξ Ξ' f
    simp only [GlobalTheory.TriStep.valK]
    rw [hL, per_add_left S.B' hψ (hA Ξ) (hA Ξ') (hf f)]
  · intro a Ξ f
    simp only [GlobalTheory.TriStep.valK]
    rw [map_smul, biComb_smul, GlobalTheory.SeeSawRhs.biLift_smul, GlobalTheory.SeeSawStep.per_smul_left, smul_eq_mul]
  · intro Ξ f g
    simp only [GlobalTheory.TriStep.valK]
    obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := _root_.GlobalTheory.BesselQuot.besGrp_quotient D σ S.B'
    obtain ⟨Cp, hadd, -⟩ := per_add_bound S.B' hψ (hA Ξ) Ω hΩc hΩ
    exact hadd _ _ (hf f) (hf g)
  · intro a Ξ f
    simp only [GlobalTheory.TriStep.valK]
    exact GlobalTheory.SeeSawStep.per_smul_right S.B' ψ _ a f.1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueInvariantMiddleGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep.GlMid

variable {D : D7}

theorem comb_right_comm (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (L : Module.End ℂ (WO A S → ℂ))
    (K : WO A S → WO S A' → ℂ) (c : WO S A' →₀ ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' c (fun v' => L (fun u' => K u' v') u) v = L (fun u' => comb ψ S A' c (K u') v) u := by
  have e : (fun u' => comb ψ S A' c (K u') v) =
      ∑ t ∈ c.support, (c t * ψ (symplOH S A' v t)) • (fun u' => K u' (v + t)) := by
    funext u'
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem comb_left_comm (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (L : Module.End ℂ (WO S A' → ℂ))
    (K : WO A S → WO S A' → ℂ) (c : WO A S →₀ ℂ) (u : WO A S) (v : WO S A') :
    comb ψ A S c (fun u' => L (K u') v) u = L (fun v' => comb ψ A S c (fun u' => K u' v') u) v := by
  have e : (fun v' => comb ψ A S c (fun u' => K u' v') u) =
      ∑ t ∈ c.support, (c t * ψ (symplOH A S u t)) • (fun v' => K (u + t) v') := by
    funext v'
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem comb_om_comm {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : Om S T}
    (h : IsWeilDatumO ψ S T χS χT ω) (g : GA D S) (g' : GA D T) (c : WO S T →₀ ℂ)
    (hc : ∀ t ∈ c.support, actO S T g g' t = t) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    comb ψ S T c (ω (g, g') f) = ω (g, g') (comb ψ S T c f) := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [map_smul, h.om_heis g g' t f hf, hc t ht]

theorem idem_mul {e : AE D} (he : IsSplitIdem D e) : (e + cA D e) * (1 - (e + cA D e)) = 0 := by
  have h1 := he.1
  have h2 := he.2.1
  have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  linear_combination -h1 - 2 * h2 - h3

theorem actO_fix_left {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {a : GA D T} (ha : SuppAt e T a) {t : WO S T}
    (ht : IsHalf (1 - (e + cA D e)) t) : actO S T 1 a t = t := by
  unfold actO
  rw [inv_one, show mt S (1 : GA D S) = 1 from rfl, Matrix.mul_one]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k, mt T a i k * t k j = (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k * t k j := fun k => by
    have ha' := ha i k
    rw [Matrix.sub_apply] at ha'
    have ht' := ht k j
    linear_combination (-(t k j)) * ha' +
      (-((e + cA D e) * (mt T a i k - (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k))) * ht' +
      ((mt T a i k - (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k) * t k j) * idem_mul he
  rw [Finset.sum_congr rfl fun k _ => key k, ← Matrix.mul_apply, Matrix.one_mul]

theorem actO_fix_right {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {a : GA D S} (ha : SuppAt e S a⁻¹) {t : WO S T}
    (ht : IsHalf (1 - (e + cA D e)) t) : actO S T a 1 t = t := by
  unfold actO
  rw [show mt T (1 : GA D T) = 1 from rfl, Matrix.one_mul]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k, t i k * mt S a⁻¹ k j = t i k * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := fun k => by
    have ha' := ha k j
    rw [Matrix.sub_apply] at ha'
    have ht' := ht i k
    linear_combination (-(t i k)) * ha' +
      (-((e + cA D e) * (mt S a⁻¹ k j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j))) * ht' +
      ((mt S a⁻¹ k j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j) * t i k) * idem_mul he
  rw [Finset.sum_congr rfl fun k _ => key k, ← Matrix.mul_apply, Matrix.mul_one]

end GlobalTheory.TriStep.GlMid

namespace GlobalTheory.TriStep
open GlobalTheory.TriStep.GlMid

theorem valK_glMid : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₁ Q.k) (Ξ₁ Ξ₁' : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₁'.1 = om Q.μ₁ 1 g Ξ₁.1 → Ξ₂'.1 = om Q.μ₂ g 1 Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂') f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ξ₁ Ξ₁' Ξ₂ Ξ₂' h₁ h₂ hC f _
  obtain ⟨a₁, ha₁⟩ := Witness.exists_isLoc (ofSplit Q.q) Q.F.F₁ g
  have hsplit : IsSplitIdem D (ofSplit Q.q).e := (ofSplit Q.q).split
  have comp₁ : (ofSplit Q.q).IsComp S.χ₁ Q.μ₁⁻¹ := fun x a hxa => by
    have e := Q.comp₁ x a hxa
    rw [MonoidHom.inv_apply, Circle.coe_inv] at e
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e, inv_inv]
  have comp₂ : (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := fun x a hxa => by
    have e := Q.comp₂ x a hxa
    rw [MonoidHom.inv_apply, Circle.coe_inv] at e
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e, inv_inv]
  have hL : ∀ (X₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) (v : WO S.J.W₀ S.B'.A),
      IsThetaFunO ψ S.B.A S.J.W₀ (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ X₂) u v) ∧
      (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' X₂) u v) = S.oma (1, a₁) (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ X₂) u v) := by
    intro X₂ v
    obtain ⟨T₁, hT₁, hT⟩ := hΛ.1 X₂ v
    have e : ∀ X₁ : SB (Matrix Q.n₁ Q.n₀ Q.k), (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ X₂) u v) = T₁ X₁ :=
      fun X₁ => funext (hT X₁ _ (fun _ => rfl))
    rw [e, e]
    refine ⟨hT₁.theta Ξ₁, ?_⟩
    symm
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.B.A S.J.W₀ S.χ₁ S.χ₁ S.oma S.weila Q.μ₁⁻¹ Q.μ₁⁻¹ comp₁ comp₁ Q.n₁ Q.n₀
      Q.F.F₀ Q.F.F₁ T₁ hT₁ 1 1 a₁ g (GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.B.A Q.n₀ Q.F.F₀).1 ha₁ Ξ₁ Ξ₁' ?_
    rw [h₁]
    simp
  have hR : ∀ (X₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (u : WO S.B.A S.J.W₀),
      IsThetaFunO ψ S.J.W₀ S.B'.A (Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂) u) ∧
      Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂') u = S.omb (a₁, 1) (Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂) u) := by
    intro X₁ u
    obtain ⟨T₂, hT₂, hT⟩ := hΛ.2 X₁ u
    have e : ∀ X₂ : SB (Matrix Q.n₂ Q.n₁ Q.k), Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ X₂) u = T₂ X₂ :=
      fun X₂ => funext (hT X₂ _ (fun _ => rfl))
    rw [e, e]
    refine ⟨hT₂.theta Ξ₂, ?_⟩
    symm
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W₀ S.B'.A S.χ₂ S.χ₂ S.omb S.weilb Q.μ₂⁻¹ Q.μ₂⁻¹ comp₂ comp₂ Q.n₂ Q.n₁
      Q.F.F₁ Q.F.F₂ T₂ hT₂ a₁ g 1 1 ha₁ (GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.B'.A Q.n₂ Q.F.F₂).1 Ξ₂ Ξ₂' ?_
    rw [h₂]
    simp
  have hA : ∀ t ∈ c₁.support, actO S.B.A S.J.W₀ 1 a₁ t = t := fun t ht =>
    actO_fix_left hsplit ha₁.1 (hc₁ t ht)
  have hB : ∀ t ∈ c₂.support, actO S.J.W₀ S.B'.A a₁ 1 t = t := fun t ht =>
    actO_fix_right hsplit ((GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.J.W₀ Q.n₁ Q.F.F₁).2.2 a₁ g ha₁).1 (hc₂ t ht)

  have hY : ∀ v', IsThetaFunO ψ S.B.A S.J.W₀ (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') := by
    intro v'
    have e : (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') =
        ∑ t ∈ c₂.support, (c₂ t * ψ (symplOH S.J.W₀ S.B'.A v' t)) •
          (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u (v' + t)) := by
      funext u
      simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [e]
    exact GlobalTheory.Core.Rk.Collect.theta_sum _ _ _ fun t => (hL Ξ₂ (v' + t)).1
  have hC' : ∀ u v, biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v =
      S.omb (a₁, 1) (fun v' => S.oma (1, a₁)
        (fun u' => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u' v') u) v := by
    intro u v
    have s1 : ∀ u'', comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂') u'') =
        S.omb (a₁, 1) (comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'')) := fun u'' => by
      rw [(hR Ξ₁' u'').2]
      exact comb_om_comm S.weilb a₁ 1 c₂ hB (hR Ξ₁' u'').1
    have s2 : ∀ v' u'', comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'') v' =
        S.oma (1, a₁) (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') u'' := fun v' u'' => by
      have e : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'' =
          fun w => S.oma (1, a₁) (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u w) u'' :=
        funext fun w => congrFun (hL Ξ₂ w).2 u''
      rw [e]
      exact comb_right_comm ψ (S.oma (1, a₁)) (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) c₂ u'' v'
    unfold biComb
    simp only [s1]
    rw [comb_left_comm ψ (S.omb (a₁, 1)) (fun u'' v' => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'') v') c₁ u v]
    refine congrArg (fun F => S.omb (a₁, 1) F v) (funext fun v' => ?_)
    simp only [s2 v']
    rw [comb_om_comm S.weila 1 a₁ c₁ hA (hY v')]

  obtain ⟨b1, -, -, -⟩ := GlobalTheory.SeeSaw.biAct_all D ψ S.B.A S.J.W₀ S.B'.A S.χ₁ S.χ₁ S.χ₂ S.χ₂ S.oma S.omb S.weila S.weilb _ hC
  have hD := b1 (1, a₁)
  obtain ⟨-, -, d3, -⟩ := GlobalTheory.SeeSaw.biAct_all D ψ S.B.A S.J.W₀ S.B'.A S.χ₁ S.χ₁ S.χ₂ S.χ₂ S.oma S.omb S.weila S.weilb _ hD
  have integ : ∀ (h₂ : GA D S.B'.A) (h₁ : GA D S.J.W₀) (h₀ : GA D S.B.A),
      φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v) 0) 0 =
      φ h₀ * S.omb (h₁ * a₁, h₂) (fun v => S.oma (h₀, h₁ * a₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 := by
    intro h₂ h₁ h₀
    have e1 : (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v) 0) =
        S.omb (a₁, 1) (fun v => S.oma (h₀, h₁ * a₁)
          (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) := by
      funext v
      simp only [hC']
      rw [← d3 (h₀, h₁) (a₁, 1) 0 v]
      refine congrArg (fun F => S.omb (a₁, 1) F v) (funext fun v' => ?_)
      change S.oma (h₀, h₁) (S.oma (1, a₁)
        (fun u' => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u' v')) 0 = _
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hinv : ∀ h₂ : GA D S.B'.A, ∀ γ ∈ GQ S.J.W₀, ∀ h₁ : GA D S.J.W₀,
      (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) (γ * h₁) =
      (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) h₁ := by
    intro h₂ γ hγ h₁
    refine congrArg (fun F : GA D S.B.A → ℂ => ∫ h₀ in S.B.vA.𝓕, F h₀ ∂S.B.vA.μ) (funext fun h₀ => ?_)
    have e1 : ∀ v, S.oma (h₀, γ * h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0 =
        S.oma (h₀, h₁) (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0 := fun v => by
      have := GlobalTheory.SeeSawLastValue.om_aut_mul S.weila (one_mem _) hγ h₀ h₁ (GlobalTheory.FrComb.slice_left hC v)
      rwa [one_mul] at this
    simp only [e1]
    have := GlobalTheory.SeeSawLastValue.om_aut_mul S.weilb hγ (one_mem _) h₁ h₂ (GlobalTheory.FrComb.slice_right (b1 (h₀, h₁)) 0)
    rw [one_mul] at this
    exact congrArg (φ h₀ * ·) this
  unfold valK
  congr 1
  funext h₂
  unfold biLift
  simp only [integ h₂]
  exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S.J.W₀ S.J.v0.μ S.J.v0.𝓕 S.J.v0.haar S.J.v0.fund
    (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) (hinv h₂) a₁

end GlobalTheory.TriStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqLatFrameOfIsSDFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd
open GlobalTheory.AdForm.LiveModel GlobalTheory.AdForm.PinInhab GlobalTheory.MixModel

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

abbrev lineZ (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem gram_X' {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (hI : I.Ok) : (I.rec7 l Z).sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  have key : ∀ S : HSp (I.rec7 l Z), ∀ n, S = Examples₂.posSpace hs n → S.gram = 1 := by
    rintro _ n rfl; exact gram_pos hs n
  exact key _ _ h2

def oTop {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) :
    ∀ n, n = (I.rec7 l Z).R.m → OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)) :=
  fun n h => Eq.rec (motive := fun n _ => OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)))
    (topDec (gram_X hI _) (gram_X' hI)) h.symm

def piE (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : (I.rec7 l Z).host.E :=
  ((X.piT u : 𝓞 B.host.E) : B.host.E)

def zeta (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : Fin (lineZ (I.rec7 l Z)).rank → (I.rec7 l Z).host.E :=
  fun _ => piE I l Z u

def xgeo {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok)
    (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (u : B.Word)
    (Λ : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : XGeo (I.rec7 l Z) :=
  ⟨fun _ => stdSp _, vac, lineZ _, oTop l Z hI, zeta I l Z u, 1, Λ⟩

theorem norm_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    star (zeta I l Z u) ⬝ᵥ (lineZ (I.rec7 l Z)).gram *ᵥ zeta I l Z u = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) := by
  have h := congrArg (fun z : 𝓞 B.host.E => (z : B.host.E)) (l.pr.piT_norm u)
  rw [gram_pos, Matrix.one_mulVec]
  simp only [dotProduct, zeta, piE, Pi.star_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [map_mul, map_natCast] at h
  rw [show (lineZ (I.rec7 l Z)).rank = 1 from rfl, one_smul]
  exact (mul_comm _ _).trans h

theorem isLineVec_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    IsLineVec (lineZ (I.rec7 l Z)) (zeta I l Z u) := by
  refine ⟨rfl, ?_⟩
  rw [norm_zeta]
  have := (l.pr.T_prime u).ne_zero
  exact_mod_cast this

theorem eq_latFrame_of_isSDFrame {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSDFrame V β Λ 1) : Λ = GlobalTheory.PlaceModel.latFrame V := by
  obtain ⟨c, -, -, -, h4, h5⟩ := h
  ext x
  constructor
  · intro hx
    have := h5 x hx
    rw [one_pow, Nat.cast_one, one_smul] at this
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame]
    exact this
  · intro hx
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame] at hx
    have := h4 x hx
    rwa [one_pow, Nat.cast_one, one_smul] at this

end GlobalTheory.XGeoStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfAddCharTrivialOnHomLatticeLineStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_addChar_trivial_on_homLattice_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i : Fin ρ) (c : AE D), c - 1 ∈ idAt D (· = v) → (∀ b ∈ idAt D (· = v), dV.extY W (dW.jY ⬝ Matrix.single i i b) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) → ψ (symplO V W (dV.extX W (dW.jX ⬝ Matrix.single i i c)) (dV.extY W (dW.jY ⬝ Matrix.single i i b))) = 1) → c - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.InvLat.int_of_psi_line | exact GlobalTheory.FinPl.InvLat.int_of_psi_line | (intros; apply GlobalTheory.FinPl.InvLat.int_of_psi_line <;> assumption)
end
end

