module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormTwelveCubedEqOneOfFiveLePrime
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0008
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KappaIntegralOfCalculation
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)

theorem kappa_integral_of_calculation (hC : CalcC) : uniformGaussModelConditionReformulated := by
  intro l _ hl g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN n _ _ Θ γ hγ hK
  obtain ⟨hFr, hF1, hall, hbin⟩ := hC l hl g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN
  have hσ : ∀ a : MaximalUnramifiedExtension l, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (frobSq (MaximalUnramifiedExtension l) l σ hU).2
  let _ : StarRing (BrC.Osub σ) := BrC.starO hσ
  have hun : (Matrix.of fun a b => (⟨γ a b, BrC.mem_Osub.2 (hγ.1 a b)⟩ : BrC.Osub σ)).conjTranspose *
      (Matrix.of fun a b => (⟨γ a b, BrC.mem_Osub.2 (hγ.1 a b)⟩ : BrC.Osub σ)) = 1 := by
    ext a b
    rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum, Matrix.one_apply]
    have h := hγ.2 a b
    have e : ((if a = b then (1 : BrC.Osub σ) else 0 : BrC.Osub σ) : MaximalUnramifiedExtension l) =
        if a = b then 1 else 0 := by split_ifs <;> rfl
    rw [e, ← h]
    rfl
  exact Formalism.L2.Th1.E.generalIntOf ℂ_[l] (unitBall ℂ_[l]) (fun _ => Iff.rfl)
    (lgF ℂ_[l] l) (expF ℂ_[l] l) (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) hFr
    (BrC.Osub σ) ((MaximalUnramifiedExtension l).subtype.comp (BrC.Osub σ).subtype)
    (fun α => (hall α.1 α.2.1 α.2.2).1)
    (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz))
    hF1
    (fun α => (hall α.1 α.2.1 α.2.2).2.1)
    (fun α => (hall α.1 α.2.1 α.2.2).2.2)
    n Θ (Matrix.of fun a b => (⟨γ a b, BrC.mem_Osub.2 (hγ.1 a b)⟩ : BrC.Osub σ)) hun hK

theorem HypShape_of (hC : CalcC) : HypShape := by
  intro l _ hl g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN N0 N1 ιr _ _ n _ f f' hff Θ hΘ
  have hl2 : 2 ≤ l := by omega
  obtain ⟨hFr, hF1, hall, hbin⟩ := hC l hl g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN
  obtain ⟨hf, hf', hG1, hG2, hG3⟩ := hff
  have hσ : ∀ a : MaximalUnramifiedExtension l, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (frobSq (MaximalUnramifiedExtension l) l σ hU).2
  let _ : StarRing (BrC.Osub σ) := BrC.starO hσ
  have gram : ∀ (a b : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l)
      (ha : ∀ e i, ‖a e i‖ ≤ 1 ∧ σ (σ (a e i)) = a e i) (hb : ∀ e i, ‖b e i‖ ≤ 1 ∧ σ (σ (b e i)) = b e i)
      (e e' : ιr × Fin N0 × Fin N1) (c : BrC.Osub σ), ∑ i, σ (a e i) * b e' i = c.1 →
      ∑ i, star (⟨a e i, BrC.mem_Osub.2 (ha e i)⟩ : BrC.Osub σ) *
        (⟨b e' i, BrC.mem_Osub.2 (hb e' i)⟩ : BrC.Osub σ) = c := by
    intro a b ha hb e e' c h
    apply Subtype.ext
    rw [← h, AddSubmonoidClass.coe_finsetSum]
    rfl
  have hph : PowerSeries.constantCoeff (phL l g2 g3 s2 ε) = 0 := hFr.2.2
  have hPh0 : MvPowerSeries.constantCoeff
      (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph
  have hpt : ∀ i, Formalism.L2.Th1.C.IsPt (unitBall ℂ_[l])
      (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[l] l) (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype f f' i) := fun i =>
    Formalism.L2.Th1.C.Pts.isPt_flin hFr.1 hFr.2.1
      (by
        rintro (e | e)
        · exact (hall _ (hf e i).1 (hf e i).2).1
        · exact (hall _ (hf' e i).1 (hf' e i).2).1)
      (by rintro (e | e) <;> exact Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X _)
  obtain ⟨h3, h4, h5⟩ := Formalism.L2.Th1.E.substExpInt ℂ_[l] n (Bool × ιr × Fin N0 × Fin N1)
    (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[l] l) (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype f f') (fun i => (hpt i).1)
    (fun i => (hpt i).2) (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε)) _ hPh0 hΘ
  have hΘe : Θ = Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) * Θ) := by
    rw [← mul_assoc]
    have := Formalism.L2.Th1.C.mvExp_neg hPh0
    rw [← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq] at this
    rw [this, one_mul]
  refine ⟨_, _, h4, h5, ?_, ?_⟩
  · have hF0 : MvPowerSeries.constantCoeff (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF.1, map_zero]
    have hcob : cob (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F) (lgF ℂ_[l] l) = 0 := by
      rw [← Formalism.L2.Th1.E.Joints.map_lgF' (MaximalUnramifiedExtension l).subtype l, ← Formalism.L2.Th1.E.mapCob _ _ _ _ _ hF.1,
        hF.2.2, map_zero]
    rw [Formalism.L2.Th1.E.mapCob _ _ _ _ _ hF.1,
      Formalism.L2.Th1.E.sumEBridge ℂ_[l] (lgF ℂ_[l] l) (expF ℂ_[l] l) (BrC.logPair hl2) _ hF0 hcob]
    refine (Formalism.L2.Th1.E.congIffSimeq ℂ_[l] (unitBall ℂ_[l]) (fun _ => Iff.rfl) _ _ _).1 ?_
    rw [Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ fun i => (hpt i).1]
    exact Formalism.L2.Th1.C.hyperbolicSum ℂ_[l] (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) hFr
      (BrC.Osub σ) ((MaximalUnramifiedExtension l).subtype.comp (BrC.Osub σ).subtype)
      (fun α => (hall α.1 α.2.1 α.2.2).1)
      (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz))
      hF1
      (fun α => (hall α.1 α.2.1 α.2.2).2.1)
      (fun α => (hall α.1 α.2.1 α.2.2).2.2)
      n (ιr × Fin N0 × Fin N1)
      (fun e i => ⟨f e i, BrC.mem_Osub.2 (hf e i)⟩) (fun e i => ⟨f' e i, BrC.mem_Osub.2 (hf' e i)⟩)
      (fun e e' => gram f f hf hf e e' 0 (hG1 e e'))
      (fun e e' => gram f' f' hf' hf' e e' 0 (hG2 e e'))
      (fun e e' => gram f f' hf hf' e e' _ (by
        rw [hG3 e e']
        split_ifs <;> rfl))
      (Bool × ιr × Fin N0 × Fin N1)
      (fun e => MvPowerSeries.X (false, e)) (fun e => MvPowerSeries.X (true, e))
      (fun e => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X _) (fun e => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X _)
  · unfold inHyp
    rw [← h3, ← hΘe]

end Formalism.L2.Th1.Top
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)

theorem PhMap_proof : PhMap := fun _ _ _ _ _ _ φ _ hl g2 g3 s2 ε =>
  Formalism.L2.Th1.E.Joints.map_phFF φ hl g2 g3 s2 ε

namespace PAdicPowerSeriesCoefficients

section Maps

variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (φ : K →+* K')

theorem cc_map {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.constantCoeff (PowerSeries.map φ f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_zero]

theorem map_expF {l : ℕ} (hl : 2 ≤ l) : PowerSeries.map φ (expF K l) = expF K' l := by
  refine (expSpec K' l hl).2.2.2 _ (cc_map φ (expSpec K l hl).1) ?_
  rw [← Formalism.L2.Th1.E.Joints.map_lgF' φ l, ← Formalism.L2.Th1.B.Map.map_psubst' φ (expSpec K l hl).1,
    (expSpec K l hl).2.1, PowerSeries.map_X]

theorem map_mulBy {l : ℕ} (hl : 2 ≤ l) (a : K) :
    PowerSeries.map φ (Formalism.L2.Th1.C.mulBy (lgF K l) (expF K l) a) =
      Formalism.L2.Th1.C.mulBy (lgF K' l) (expF K' l) (φ a) := by
  unfold Formalism.L2.Th1.C.mulBy
  rw [Formalism.L2.Th1.B.Map.map_psubst' φ (FAux.cc_arg hl a), map_mul, PowerSeries.map_C,
    Formalism.L2.Th1.E.Joints.map_lgF', map_expF φ hl]

theorem cc_mulBy {l : ℕ} (hl : 2 ≤ l) (a : K) :
    PowerSeries.constantCoeff (Formalism.L2.Th1.C.mulBy (lgF K l) (expF K l) a) = 0 :=
  Pair.cc_ps (τ := Unit) (FAux.cc_arg hl a) (expSpec K l hl).1

end Maps

section Field

variable {l : ℕ} [Fact l.Prime]

theorem lg_map {τ : Type} {f : MvPowerSeries τ (MaximalUnramifiedExtension l)}
    (h : Formalism.L2.Th1.C.LG (unitBall (MaximalUnramifiedExtension l)) f) :
    Formalism.L2.Th1.C.LG (unitBall ℂ_[l]) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype f) := by
  refine ⟨?_, fun n => ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.1, map_zero]
  · unfold Formalism.L2.Th1.C.mvExp
    rw [← PowerSeries.map_exp (MaximalUnramifiedExtension l).subtype, ← Formalism.L2.Th1.B.Map.map_psubst (MaximalUnramifiedExtension l).subtype h.1,
      MvPowerSeries.coeff_map]
    exact h.2 n

theorem of_closed_int {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hU : UnrOK (MaximalUnramifiedExtension l) l σ) {P : ℂ_[l] → Prop}
    (hc : IsClosed {z : ℂ_[l] | P z}) (hi : ∀ n : ℤ, P (n : ℂ_[l])) {x : MaximalUnramifiedExtension l} (hx : ‖x‖ ≤ 1)
    (hs : σ x = x) : P (x : ℂ_[l]) :=
  BrC.of_closed_int hU (P := fun z : MaximalUnramifiedExtension l => P (z : ℂ_[l])) (hc.preimage continuous_subtype_val)
    (fun n => by simpa using hi n) hx hs

theorem endInt {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hU : UnrOK (MaximalUnramifiedExtension l) l σ) {α : MaximalUnramifiedExtension l} (hα : ‖α‖ ≤ 1)
    (hs : σ (σ α) = α) :
    Formalism.L2.Th1.C.EndInt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l) (α : ℂ_[l]) := by
  intro n
  have h := map_mulBy (MaximalUnramifiedExtension l).subtype hU.1.two_le α
  rw [show (α : ℂ_[l]) = (MaximalUnramifiedExtension l).subtype α from rfl, ← h, PowerSeries.coeff_map]
  exact BrC.endInt hU hα hs n

theorem phNorm {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hl : 2 ≤ l) {ph : PowerSeries (MaximalUnramifiedExtension l)} {α : MaximalUnramifiedExtension l}
    (h : NormRel l σ ph α) :
    Formalism.L2.Th1.C.PhNormAt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype ph) (α : ℂ_[l]) ((σ α : MaximalUnramifiedExtension l) : ℂ_[l]) := by
  have h1 := lg_map ((BrC.phNorm_iff ph α).2 h)
  unfold Formalism.L2.Th1.C.PhNormAt Formalism.L2.Th1.C.Cong
  have e : MvPowerSeries.map (MaximalUnramifiedExtension l).subtype
      (PowerSeries.subst (Formalism.L2.Th1.C.mulBy (lgF (MaximalUnramifiedExtension l) l) (expF (MaximalUnramifiedExtension l) l) α) ph -
        (α * σ α) • ph) =
      PowerSeries.subst (Formalism.L2.Th1.C.mulBy (lgF ℂ_[l] l) (expF ℂ_[l] l) (α : ℂ_[l]))
        (PowerSeries.map (MaximalUnramifiedExtension l).subtype ph) -
        ((α : ℂ_[l]) * ((σ α : MaximalUnramifiedExtension l) : ℂ_[l])) • PowerSeries.map (MaximalUnramifiedExtension l).subtype ph := by
    rw [map_sub, Formalism.L2.Th1.B.Map.map_psubst (MaximalUnramifiedExtension l).subtype (cc_mulBy hl α),
      MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C]
    have h2 : MvPowerSeries.map (MaximalUnramifiedExtension l).subtype
        (Formalism.L2.Th1.C.mulBy (lgF (MaximalUnramifiedExtension l) l) (expF (MaximalUnramifiedExtension l) l) α) =
        Formalism.L2.Th1.C.mulBy (lgF ℂ_[l] l) (expF ℂ_[l] l) (α : ℂ_[l]) :=
      map_mulBy (MaximalUnramifiedExtension l).subtype hl α
    rw [h2, map_mul]
    rfl
  rw [← e]
  exact h1

end Field

end PAdicPowerSeriesCoefficients

open PAdicPowerSeriesCoefficients in
theorem CalcC_proof : CalcC := by
  intro l _ h5 g2 g3 ε s2 hg2 hg3 hε hth σ hU F _ hN
  have hl : 2 ≤ l := hU.1.two_le
  have hnl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h : ‖(((l : ℕ) : MaximalUnramifiedExtension l) : ℂ_[l])‖ = (l : ℝ)⁻¹ := hU.2.2.1
    simpa using h
  have hP := BrC.logPair (K := ℂ_[l]) hl
  obtain ⟨F', hF'⟩ := (Formalism.InvariantFactorPaths.G7.Top.lawExists ℂ_[l] l hU.1 hnl).1
  have hph : PowerSeries.constantCoeff (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) = 0 :=
    cc_map _ (FAux.cc_phFF hl g2 g3 s2 ε)
  have hth' : ∀ n, ‖PowerSeries.coeff n (thetaS l (g2 : ℂ_[l]) (g3 : ℂ_[l]) (ε : ℂ_[l]))‖ ≤ 1 := by
    intro n
    have hm := FAux.thetaS_map (MaximalUnramifiedExtension l).subtype hl g2 g3 ε
    have e : thetaS l (g2 : ℂ_[l]) (g3 : ℂ_[l]) (ε : ℂ_[l]) =
        PowerSeries.map (MaximalUnramifiedExtension l).subtype (thetaS l g2 g3 ε) := hm.symm
    rw [e, PowerSeries.coeff_map]
    exact hth n
  have hF1 : F1 F' (cob F' (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε))) := by
    rw [PhMap_proof _ _ (MaximalUnramifiedExtension l).subtype l hl]
    exact first_level_on_curve ℂ_[l] l hU.1 hU.2.1 hnl F' hF' _ _ _ _ hg2 hg3 hε hth'
  obtain ⟨-, hFG, hC1⟩ := Formalism.L2.Th1.C.first_level_from_universal_holds ℂ_[l] F' _ _ _ hP (BrC.lawLog hl hF')
    hph hF1.2.1
  have hFr : Formalism.L2.Th1.C.Frame (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) := ⟨hP, hFG, hph⟩
  have hσ : ∀ a : MaximalUnramifiedExtension l, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (frobSq (MaximalUnramifiedExtension l) l σ hU).2
  have hcl := Formalism.L2.Th1.C.unit_ball_closed ℂ_[l]
  have hbin : ∀ z : MaximalUnramifiedExtension l, ‖z‖ ≤ 1 → σ z = z →
      Formalism.L2.Th1.C.IsBinomScalar (unitBall ℂ_[l]) (z : ℂ_[l]) := fun z hz hs =>
    of_closed_int hU (Formalism.L2.Th1.C.binomClosed ℂ_[l] _ hcl) (Formalism.L2.Th1.C.intBinomScalar ℂ_[l] _)
      hz hs
  let _ : StarRing (BrC.Osub σ) := BrC.starO hσ
  have key := Formalism.L2.Th1.C.normAdjAll ℂ_[l] (unitBall ℂ_[l]) _ _ _ hFr (BrC.Osub σ)
    ((MaximalUnramifiedExtension l).subtype.comp (BrC.Osub σ).subtype)
    (fun α => endInt hU α.2.1 α.2.2)
    (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz))
    (fun z hz => of_closed_int hU
      (Formalism.L2.Th1.C.zLinClosed ℂ_[l] _ hcl _ _ _ hP.1 hP.2.2.1 hph)
      (Formalism.L2.Th1.C.zLinInt ℂ_[l] _ _ _ _ hFr hC1) z.2.1 (congrArg Subtype.val hz))
    hC1
    (by
      show ‖(2 : ℂ_[l])⁻¹‖ ≤ 1
      have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := BrC.norm_two hU
      have h3 : ‖(2 : ℂ_[l])‖ = 1 := by rw [← h2, ← FAux.norm_coe, map_ofNat]
      rw [norm_inv, h3, inv_one])
    (by
      have : (2 : BrC.Osub σ) =
          (BrC.unitO (BrC.norm_two hU) (by rw [map_ofNat, map_ofNat]) : (BrC.Osub σ)ˣ) :=
        Subtype.ext rfl
      rw [this]
      exact Units.isUnit _)
    (BrC.two_units hU)
    (fun u => phNorm hl (hN _ (BrC.norm_unitO u) (u : BrC.Osub σ).2.2))
  refine ⟨hFr, hC1, fun α hα hs => ⟨endInt hU hα hs, ?_⟩, hbin⟩
  exact key ⟨α, BrC.mem_Osub.2 ⟨hα, hs⟩⟩

end Formalism.L2.Th1.Top
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OrthogonalShapeOneLetter
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)

namespace ConjugatePartitionShape

theorem factors (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 ε s2 : MaximalUnramifiedExtension l) (h2 : (g2 : ℂ_[l]) = ι L.g₂) (h3 : (g3 : ℂ_[l]) = ι L.g₃)
    (hs2 : (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 L)) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1)
    (hD : ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1) (hε : ‖ε‖ = 1)
    (hθ : ∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1)
    (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice) (hω2 : ω₀ / 2 ∉ L.lattice)
    (N : ℕ) (hN : 0 < N) (hlN : ¬ l ∣ N) (s : ℂ) (hs : (N : ℂ) * s ∈ L.lattice) :
    ∃ V : PowerSeries ℂ_[l], Formalism.L2.Th1.E.IntS V ∧
      (Formalism.DworkPowerSeriesWeights.mvExp (-(PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε))) : PowerSeries ℂ_[l]) * V =
        thetaOne l L ι (ε : ℂ_[l]) ω₀ s := by
  have hW : Formalism.L2.Th1.E.IntCurve (Formalism.L2.Th1.E.curveL l L ι) := by
    unfold Formalism.L2.Th1.E.curveL
    rw [← h2, ← h3]
    exact Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short l hl _ _ hg2 hg3 hD
  exact Formalism.L2.Th1.E.joint_integrality l L ι (by omega) hW g2 g3 s2 ε h2 h3 hs2 hε hθ ω₀ hω hω2 s N hN hlN hs

theorem cc_ph (l : ℕ) [Fact l.Prime] (hl : 2 ≤ l) (g2 g3 s2 ε : MaximalUnramifiedExtension l) :
    PowerSeries.constantCoeff (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF hl, map_zero]

end ConjugatePartitionShape

open ConjugatePartitionShape

end Formalism.L2.Th1.Top
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaAdditiveHomogeneousHomothety
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy jInv)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.InvariantFactorPaths.G7 (at1)

namespace ThetaHomothety

open Formalism.L2.Th1.F (scalePair opU herm th0 area taylor0 sgStar)


theorem herm_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z x : ℂ) :
    herm (scalePair L c hc) (c * z) (c * x) = herm L z x := by
  exact Formalism.L2.Th1.F.Homog.herm_scale (L := L) (c := c) (hc := hc) z x

theorem opU_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ s z : ℂ) :
    opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2)) (c * z) =
      opU L s (th0 L (ω₀ / 2)) z := by
  unfold opU
  rw [herm_scale L c hc z s, herm_scale L c hc s s]
  have h1 : c * ω₀ / 2 = c * (ω₀ / 2) := by ring
  have h2 : c * z + c * s = c * (z + s) := by ring
  rw [h1, h2, Formalism.L2.Th1.F.Homog.normalizedTheta_scale (L := L) (c := c) (hc := hc)]

theorem differentiable_opU (L : PeriodPair) (s : ℂ) {θ : ℂ → ℂ} (h : Differentiable ℂ θ) :
    Differentiable ℂ (opU L s θ) := by
  show Differentiable ℂ fun z =>
    θ (z + s) * Complex.exp (-(Real.pi : ℂ) * herm L z s - (Real.pi : ℂ) * herm L s s / 2)
  simp only [herm]
  fun_prop

theorem differentiable_evenTheta (L : PeriodPair) (t : ℂ) : Differentiable ℂ (th0 L t) := by
  have hs : Differentiable ℂ (sgStar L) := (Formalism.L2.Th1.F.sgStarBasic L).1
  show Differentiable ℂ fun z => opU L t (sgStar L) z / opU L t (sgStar L) 0
  exact (differentiable_opU L t hs).div_const _

theorem taylor0_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ s : ℂ) :
    PowerSeries.rescale c
        (taylor0 (opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2)))) =
      taylor0 (opU L s (th0 L (ω₀ / 2))) := by
  have hd : Differentiable ℂ
      (opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2))) :=
    differentiable_opU _ _ (differentiable_evenTheta _ _)
  have hF : (fun z => opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2)) (c * z)) =
      opU L s (th0 L (ω₀ / 2)) := funext (opU_scale L c hc ω₀ s)
  ext n
  simp only [taylor0, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
  rw [← hF, iteratedDeriv_comp_const_mul hd.contDiff c]
  simp only [mul_zero]
  ring

end ThetaHomothety

end Formalism.L2.Th1.Top
end
end

