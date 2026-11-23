module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepScalarsOfRealisation
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTwAn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Core.Mi.SepPer

variable {D : D7}

def contLeft (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | Continuous F ∧ ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨hF.add hG, fun γ hγ g => by simp [hF' γ hγ g, hG' γ hγ g]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c F ⟨hF, hF'⟩
    exact ⟨continuous_const.mul hF, fun γ hγ g => by simp [hF' γ hγ g]⟩

theorem rTrans_mem {V : HSp D} (t : GA D V) {F : GA D V → ℂ} (hF : F ∈ contLeft V) : rTrans t F ∈ contLeft V :=
  ⟨hF.1.comp (continuous_id.mul continuous_const), fun γ hγ g => by
    simp only [rTrans, mul_assoc]; exact hF.2 γ hγ (g * t)⟩

theorem norm_psiBes {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (n : GA D S) : ‖psiBes ψ d θ z n‖ = 1 := by
  exact hψ.1.2.1 _

theorem per_add_bound {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) (Ω : Set (GA D B.V)) (hΩc : IsCompact Ω)
    (hΩ : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) :
    ∃ C : ℝ, (∀ f g, f ∈ contLeft B.V → g ∈ contLeft B.V → B.per ψ φ (f + g) = B.per ψ φ f + B.per ψ φ g) ∧
      ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) → ‖B.per ψ φ f‖ ≤ C * K := by
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut B.cpt hφ
  have hμ : B.vA.μ B.vA.𝓕 < ⊤ := GlobalTheory.Unf.vol_fund_lt_top B.cpt B.vA
  have hν1 : B.vN.ν B.vN.𝓝 = 1 := B.vN.unit.2.2
  have hν : B.vN.ν B.vN.𝓝 < ⊤ := by rw [hν1]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  have hψc : Continuous ψ := hψ.1.1
  have hemb := GlobalTheory.Unf.BesSemi.continuous_embA B.d B.o
  have hpsi := GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψc 1 (vecB B.o B.ζ)

  have hsup : ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) →
      ∀ (h : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h)‖ ≤ K := by
    intro f hf K hK h n
    have hs : n.1 * embA B.d B.o h ∈ besGrp B.d B.o :=
      mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)
    obtain ⟨γ, hγ, hγs⟩ := hΩ _ hs
    rw [← hf.2 γ (Subgroup.mem_inf.1 hγ).1]
    exact hK _ hγs
  have hbd : ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) →
      ∀ h n, ‖GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n‖ ≤ Cφ * K := by
    intro f hf K hK h n
    simp only [GlobalTheory.MixPer.besFun, norm_mul, norm_star, norm_psiBes hψ, mul_one]
    exact mul_le_mul (hCφ h) (hsup f hf K hK h n) (norm_nonneg _) ((norm_nonneg _).trans (hCφ h))
  have hcont : ∀ f, f ∈ contLeft B.V → ∀ h, Continuous (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) := by
    intro f hf h
    change Continuous fun n : flagN B.d => φ h * f (n.1 * embA B.d B.o h) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)
    exact (continuous_const.mul (hf.1.comp (continuous_subtype_val.mul continuous_const))).mul
      (continuous_star.comp (hpsi.comp continuous_subtype_val))
  have hcontH : ∀ f, f ∈ contLeft B.V → ∀ n : flagN B.d,
      Continuous fun h => GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n := by
    intro f hf n
    simp only [GlobalTheory.MixPer.besFun]
    exact (hφ.2.mul (hf.1.comp (continuous_const.mul hemb))).mul continuous_const
  have hK : ∀ f, f ∈ contLeft B.V → ∃ K : ℝ, ∀ x ∈ Ω, ‖f x‖ ≤ K := by
    intro f hf
    obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hf.1.continuousOn
    exact ⟨K, hK⟩
  have hin : ∀ f, f ∈ contLeft B.V → ∀ h,
      IntegrableOn (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν := by
    intro f hf h
    obtain ⟨K, hK⟩ := hK f hf
    exact Measure.integrableOn_of_bounded hν.ne (hcont f hf h).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n => hbd f hf K hK h n)
  have houtC : ∀ f, f ∈ contLeft B.V →
      Continuous fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
    intro f hf
    obtain ⟨K, hK⟩ := hK f hf
    haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA B.A
    exact continuous_of_dominated (bound := fun _ => Cφ * K)
      (fun h => (hcont f hf h).aestronglyMeasurable)
      (fun h => Filter.Eventually.of_forall fun n => hbd f hf K hK h n) (integrable_const _)
      (Filter.Eventually.of_forall fun n => hcontH f hf n)
  have hout : ∀ f, f ∈ contLeft B.V →
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
    intro f hf
    obtain ⟨K, hK⟩ := hK f hf
    refine Measure.integrableOn_of_bounded (M := Cφ * K * B.vN.ν.real B.vN.𝓝) hμ.ne (houtC f hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun h => ?_)
    exact norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd f hf K hK h n
  refine ⟨Cφ * B.vA.μ.real B.vA.𝓕, fun f g hf hg => ?_, fun f hf K hK' => ?_⟩
  · have e : ∀ h n, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ (f + g) h n =
        GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n + GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ g h n := by
      intro h n; simp only [GlobalTheory.MixPer.besFun, Pi.add_apply]; ring
    simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
    simp_rw [e]
    rw [← integral_add (hout f hf) (hout g hg)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_add (hin f hf h) (hin g hg h))
  · have hνr : B.vN.ν.real B.vN.𝓝 = 1 := by simp [Measure.real, hν1]
    have h1 : ∀ h ∈ B.vA.𝓕, ‖∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν‖ ≤ Cφ * K := by
      intro h _
      have := norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd f hf K hK' h n
      rwa [hνr, mul_one] at this
    have h2 := norm_setIntegral_le_of_norm_le_const hμ h1
    simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
    calc _ ≤ Cφ * K * B.vA.μ.real B.vA.𝓕 := h2
      _ = _ := by ring

end GlobalTheory.Core.Mi.SepPer

namespace GlobalTheory.Core.Mi.SepPer

variable {D : D7}

theorem mult_mem_contLeft (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (u : M.Vec) : T u ∈ contLeft V := by
  let Q : Submodule ℂ (MMap M) :=
    { carrier := {T | ∀ u, T u ∈ contLeft V}
      add_mem' := fun ha hb u => by simpa using (contLeft V).add_mem (ha u) (hb u)
      zero_mem' := fun u => by simpa using (contLeft V).zero_mem
      smul_mem' := fun c T hT u => by simpa using (contLeft V).smul_mem c (hT u) }
  have : Mult θ M J χ ≤ Q := Submodule.span_le.2 fun T hT u => ⟨(hT.aut u).cont, (hT.aut u).left⟩
  exact this hT u

theorem mult_bound (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (Ω : Set (GA D V)) (hΩ : IsCompact Ω)
    (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g ∈ Ω, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact _root_.GlobalTheory.Core.Mi.sobolev_unif_bound D θ V S M J χ hθ T hT Ω hΩ τ v
  | zero => exact ⟨[], 0, by simp, fun w g _ => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    obtain ⟨L₁, C₁, hL₁, hb₁⟩ := h₁
    obtain ⟨L₂, C₂, hL₂, hb₂⟩ := h₂
    refine ⟨L₁ ++ L₂, max C₁ 0 + max C₂ 0, fun l hl => ?_, fun w g hg => ?_⟩
    · rcases List.mem_append.1 hl with h | h
      exacts [hL₁ l h, hL₂ l h]
    · set s₁ := (L₁.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      set s₂ := (L₂.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      have hs₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      have hs₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [List.map_append, List.sum_append, MultilinearMap.add_apply, Pi.add_apply]
      calc _ ≤ ‖T₁ (Function.update v τ w) g‖ + ‖T₂ (Function.update v τ w) g‖ := norm_add_le _ _
        _ ≤ C₁ * s₁ + C₂ * s₂ := add_le_add (hb₁ w g hg) (hb₂ w g hg)
        _ ≤ max C₁ 0 * s₁ + max C₂ 0 * s₂ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₁)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₂)
        _ ≤ (max C₁ 0 + max C₂ 0) * (s₁ + s₂) := by
          have := le_max_right C₁ 0; have := le_max_right C₂ 0; nlinarith
  | smul c T _ h =>
    obtain ⟨L, C, hL, hb⟩ := h
    refine ⟨L, ‖c‖ * C, hL, fun w g hg => ?_⟩
    rw [MultilinearMap.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb w g hg) (norm_nonneg _)

end GlobalTheory.Core.Mi.SepPer

namespace GlobalTheory.Core.Mi


open SepPer in
theorem sepCont_per_rTrans : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S) (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (φ : GA D B.A → ℂ), IsInfFam θ → IsStdChar D ψ (-1) → IsContAut B.A φ → ∀ T ∈ MultT θ M J χ, ∃ Λ : SmT M →ₗ[ℂ] ℂ, SepCont M Λ ∧ ∀ x, Λ x = B.per ψ φ (rTrans t (T x)) := by
  intro D θ ψ ρ B S M J χ t φ hθ hψ hφ T hT
  obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := _root_.GlobalTheory.BesselQuot.besGrp_quotient D ρ B
  obtain ⟨Cp, hadd, hbd⟩ := per_add_bound B hψ hφ Ω hΩc hΩ
  set T' : MMap M := PiTensorProduct.lift.symm T with hT'
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  have hTt : ∀ u : M.Vec, T (PiTensorProduct.tprod ℂ u) = T' u := by
    intro u
    have : T = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply T).symm
    rw [this, PiTensorProduct.lift.tprod]
  have hmem : ∀ x : SmT M, T x ∈ contLeft B.V := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [map_smul, hTt]
      exact (contLeft B.V).smul_mem r (mult_mem_contLeft θ M J χ hT'm u)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact (contLeft B.V).add_mem hx hy
  let Λ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun x => B.per ψ φ (rTrans t (T x))
      map_add' := fun x y => by
        have e : rTrans t (T (x + y)) = rTrans t (T x) + rTrans t (T y) := by
          funext g; simp [rTrans]
        rw [e]
        exact hadd _ _ (rTrans_mem t (hmem x)) (rTrans_mem t (hmem y))
      map_smul' := fun c x => by
        have e : rTrans t (T (c • x)) = c • rTrans t (T x) := by
          funext g; simp [rTrans]
        have := GlobalTheory.HandHom.per_smul B ψ 1 c φ (rTrans t (T x))
        rw [one_smul, one_mul] at this
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [e, this] }
  refine ⟨Λ, fun τ v => ?_, fun x => rfl⟩
  have hΩt : IsCompact ((fun g => g * t) '' Ω) := hΩc.image (continuous_id.mul continuous_const)
  obtain ⟨L, Cu, hL, hb⟩ := mult_bound θ hθ M J χ hT'm _ hΩt τ v
  let ℓ₀ : M.sm τ →ₗ[ℂ] ℂ := (Λ.compMultilinearMap (PiTensorProduct.tprod ℂ)).toLinearMap v τ
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓw : ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w)) := by
    intro w
    have := congrArg (fun m => m w) hℓ
    simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
  refine ⟨ℓ, ⟨L, Cp * Cu, hL, fun w hw => ?_⟩, hℓw⟩
  have hw' : w ∈ M.sm τ := Submodule.subset_span hw
  have e := hℓw ⟨w, hw'⟩
  simp only at e
  rw [e]
  change ‖B.per ψ φ (rTrans t (T (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩))))‖ ≤ _
  have hK : ∀ x ∈ Ω, ‖rTrans t (T (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩))) x‖ ≤
      Cu * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum := by
    intro x hx
    rw [rTrans, hTt]
    exact hb ⟨w, hw'⟩ (x * t) ⟨x, hx, rfl⟩
  calc _ ≤ Cp * (Cu * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum) := hbd _ (rTrans_mem t (hmem _)) _ hK
    _ = _ := by ring

end GlobalTheory.Core.Mi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentreComm

open GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : InfFam D} {V : HSp D}


variable (θ V) in
def CommOnSm (A B : (GA D V → ℂ) → (GA D V → ℂ)) : Prop := ∀ f ∈ SmFun θ V, A (B f) = B (A f)

theorem lin_sum {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {α : Type} (s : Finset α)
    (g : α → GA D V → ℂ) (hg : ∀ a ∈ s, g a ∈ SmFun θ V) : T (∑ a ∈ s, g a) = ∑ a ∈ s, T (g a) := by
  induction s using Finset.induction_on with
  | empty => simpa using hT.smul 0 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hT.add _ (hg a (by simp)) _
      (Submodule.sum_mem _ fun b hb => hg b (by simp [hb])), ih fun b hb => hg b (by simp [hb])]

theorem comm_foldr {T : (GA D V → ℂ) → (GA D V → ℂ)} {α : Type} (A : α → (GA D V → ℂ) → (GA D V → ℂ))
    (l : List α) (hl : ∀ a ∈ l, LinOnSm θ V (A a)) (hc : ∀ a ∈ l, CommOnSm θ V T (A a)) :
    CommOnSm θ V T fun f => l.foldr (fun a g => A a g) f := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro f hf
    have h2 := linOnSm_foldr A l fun b hb => hl b (by simp [hb])
    simp only [List.foldr_cons]
    rw [hc a (by simp) _ (h2.mem f hf), ih (fun b hb => hl b (by simp [hb])) (fun b hb => hc b (by simp [hb])) f hf]

theorem comm_gelf {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {τ : D.what₂.Tau}
    (hc : ∀ Z, CommOnSm θ V T (RderC θ V τ Z)) (k : ℕ) : CommOnSm θ V T (gelf θ V τ k) := by
  have hl : ∀ idx : Fin (k + 1) → Fin V.rank, ∀ S ∈ (List.ofFn fun a : Fin (k + 1) =>
      RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)), LinOnSm θ V S ∧ CommOnSm θ V T S := fun idx S hS => by
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hS
    exact ⟨linOnSm_RderC τ _, hc _⟩
  intro f hf
  simp only [gelf]
  rw [lin_sum hT _ _ fun idx _ => (linOnSm_foldr (fun S => S) _ fun S hS => (hl idx S hS).1).mem f hf]
  exact Finset.sum_congr rfl fun idx _ =>
    comm_foldr (fun S => S) _ (fun S hS => (hl idx S hS).1) (fun S hS => (hl idx S hS).2) f hf

theorem gelf_RderC (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (k : ℕ) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    CommOnSm θ V (gelf θ V τ k) (RderC θ V τ' Z) := by
  intro f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
  simp only [RderC]
  rw [(linOnSm_gelf τ k).add _ (Rder_mem hf h1) _ (Submodule.smul_mem _ _ (Rder_mem hf h2)), (linOnSm_gelf τ k).smul,
    GlobalTheory.CuspLie.gelf_Rder hθ h1 hf, GlobalTheory.CuspLie.gelf_Rder hθ h2 hf]

end GlobalTheory.CentreComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFirstStageLValuesPositive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem isPar_flat_of_le {D : D7} {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} (hr : D.R.r ≤ s.V.rank)
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB : IsPar u B) :
    IsPar (⟨u.1, hle u.2⟩ : (flat c w j s hr).CC c) B := by
  refine ⟨fun h => ?_, fun v hv => ?_⟩
  · have h2 : ((⟨u.1, hle u.2⟩ : (flat c w j s hr).CC c) : SmT (flat c w j s hr).M →ₗ[ℂ] (GA D (flat c w j s hr).V → ℂ)) = 0 :=
      (Submodule.coe_eq_zero).2 h
    exact hB.1 ((Submodule.coe_eq_zero).1 h2)
  · have h3 := hB.2 v hv
    unfold ParFun at h3 ⊢
    exact h3

theorem bounded_first_member (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {c : Com D} (hc : c.Is) (hj : 0 ≤ D.R.m) {s' : PiLocalization₂ D}
    (hflat : s'.Is c 0) (u' : s'.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB' : IsPar u' B) :
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r (((D.R.r : ℝ) - 1) / 2) := by
  have hrank : s'.V.rank = D.R.r := by
    rw [hflat.rank]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hbd0 := _root_.GlobalTheory.ChainOnto.parBound_of_rapidDecay hCRD D (_root_.GlobalTheory.ChainOnto.LevelFacts.levFacts D) c hc 0 hj s' hflat u' B hB'
  rw [hrank] at hbd0
  exact hbd0

theorem conjStable_first_member (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {c : Com D} (hc : c.Is) (hj : 0 ≤ D.R.m) {s' : PiLocalization₂ D}
    (hflat : s'.Is c 0) (u' : s'.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB' : IsPar u' B) :
    ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' → B w' = (B w).map star) ∧
      (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w) := by
  have hex : ∃ v, PiLocalization₂.val u' v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hB'.1
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s'.V → ℂ := fun g => conj (PiLocalization₂.val u' v g) with hfdef
  have hPF : ParFun c s' (PiLocalization₂.val u' v) B := hB'.2 v hv
  have h3 : GlobalTheory.LFun.IsParamFunV s'.V c.S f B := ((_root_.GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D c hc 0 hj s' hflat).2 f B).1 hPF
  obtain ⟨h4a, _, _⟩ := _root_.GlobalTheory.ConjVal.conj_values_hecke hCRD D c hc 0 hj s' hflat
  obtain ⟨hcont, ⟨C, hC⟩, hinv, _⟩ := h4a u' v
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s'.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  exact GlobalTheory.T.boundedAutomorphic_parameters_star_stable D s'.V c.S f hfmem B h3

end GlobalTheory.ChainTw

namespace GlobalTheory.ChainTw

theorem lPos_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LPos D := by
  intro hCRD D c w hw j hj s hs hj0 u B hB
  subst hj0
  have hc := hw.com
  obtain ⟨hr, hL, hflat⟩ := hs
  have hle := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw 0 hj s ⟨hr, hL, hflat⟩ hr
  have hB' := isPar_flat_of_le hr hle u B hB
  have hbd : GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) :=
    GlobalTheory.LiftPole.Bounded.mono (bounded_first_member hCRD hc hj hflat _ B hB') (by linarith)
  refine ⟨hbd, fun k hk => ?_⟩
  have hst := conjStable_first_member hCRD hc hj hflat _ B hB'
  have hch := hc.chars.2.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hrt : ((D.R.r : ℝ) / 2) + 1 < (1 + (D.R.t : ℝ)) / 2 := by
    have h5 : D.R.r + 5 ≤ D.R.t := by simpa [Formalism.BasicNotions.Ranks.r] using D.R.rank_add_five_le
    have h5' : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast h5
    linarith
  obtain ⟨l, hl, he⟩ := GlobalTheory.T.euler_product_conjugation_stable_parameters_pos D c.S B (c.μ (k + 1)) D.R.r ((D.R.r : ℝ) / 2) ((1 + (D.R.t : ℝ)) / 2) hch.1 hch.2
    (hc.unr ⟨k, hk⟩) hbd hrt hst
  refine ⟨l, hl, ?_⟩
  rw [← he]
  congr 1
  push_cast
  ring

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepScalarsOfRealisationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainStep_scalars_of_realisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → SoftQ D → QOfVal D → LPos D → LFull D → StepLam D → ∀ h : RangeX R, RChain R h → NormX R h → RUnif R h → RowPar R → IPDict R → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  first | exact @GlobalTheory.ChainTw.scalars_of_realisation | exact GlobalTheory.ChainTw.scalars_of_realisation | (intros; apply GlobalTheory.ChainTw.scalars_of_realisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionMatrixBoundedRationalAutIntegralStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completionMatrix_boundedRationalAut_integral : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs →
    GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ → ∀ (j c : ℕ) (a : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k),
    IsGL ι a g →
    (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, a⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • a x ∈ lamYat (Pr := Pr) (R := R) j P) →
    IntM (g⁻¹ : GL _ k).val ∧ IntM ((ϖ : k) ^ j • g.val) := by
  first | exact @GlobalTheory.TwBridge.isGL_int_of_bdd | exact GlobalTheory.TwBridge.isGL_int_of_bdd | (intros; apply GlobalTheory.TwBridge.isGL_int_of_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalAdelicPointOfUnitaryBaseSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalAdelicPoint_of_unitary_baseSpace : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ γ : GL (Fin (D.R.N 0)) D.host.E, γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ a : GA D (D.sp.X 0), a ∈ GQ (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧ ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ := by
  first | exact @GlobalTheory.Core.Mi.exists_GQ_of_unitary0 | exact GlobalTheory.Core.Mi.exists_GQ_of_unitary0 | (intros; apply GlobalTheory.Core.Mi.exists_GQ_of_unitary0 <;> assumption)
end

