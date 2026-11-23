module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0025
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PairingK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0022
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceThetaFunctionVacuumConjugatePlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0018
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SD_k.Indep (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X
def AdDecomp_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ε w, d.IsW ε w → ∀ (e : AF F), e * e = e → ∀ x : d.G,
  e • inFrame d.b x = e • (1 : Matrix _ _ (AE F E)) →
  ∃ (x₁ x₂ x₃ x₄ : d.G) (t c b : Mx F E d.n d.n) (a a' : GL (Fin d.n) (AE F E)), x = x₁ * (w * x₂ * w⁻¹) * x₃ * x₄ ∧
    inFrame d.b x₁ = Matrix.fromBlocks 1 t 0 1 ∧ inFrame d.b x₂ = Matrix.fromBlocks 1 c 0 1 ∧
    inFrame d.b x₃ = Matrix.fromBlocks a.1 0 0 a'.1 ∧ inFrame d.b x₄ = Matrix.fromBlocks 1 b 0 1 ∧
    e • t = 0 ∧ e • c = 0 ∧ e • b = 0 ∧ e • a.1 = e • (1 : Mx F E d.n d.n) ∧ e • a'.1 = e • (1 : Mx F E d.n d.n)
def AwayAct_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w (x : d.G), d.cw w (inFrame d.b x) = 1 →
  ∃ A : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ, ∀ Ψ, d.Indep w Ψ → d.Indep w (A Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w f (A Ψ)
def FinAct_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ x : d.G, (∀ w, d.cw w (inFrame d.b x) = 1) →
  ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F),
    ∀ f : Mx F E d.m d.n → ℂ, (∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X) → ∀ Φ ∈ d.sch,
      d.T Φ = (fun X => f X * g fun k => (d.crd X k).2) → d.T (d.om x Φ) = fun X => f X * g' fun k => (d.crd X k).2
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianInvariant
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_chart_gaussian_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  first | exact @_root_.GlobalTheory.ThetaOfSmF.theta_of_smF_k | exact _root_.GlobalTheory.ThetaOfSmF.theta_of_smF_k | (intros; apply _root_.GlobalTheory.ThetaOfSmF.theta_of_smF_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CoefK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.LagrangianIntegralFactorisation GlobalTheory.ThetaTransform
theorem coef_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∃ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (κ : ℝ), μW.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < κ ∧
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        Continuous (nrm σ JS JT ξ₀ B.ψ ν 𝓕 f) ∧ Integrable (nrm σ JS JT ξ₀ B.ψ ν 𝓕 f) ν ∧
        ∀ y : WOF F E nS nT,
          ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) f w * starRingEnd ℂ (f w) ∂μW =
            (κ : ℂ) * ∫ v, phase σ JS JT ξ₀ B.ψ y v * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f v ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  have hstd := _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB
  obtain ⟨N, α, β, e, hCe, he, hrat, hrat', hec, hes, hαc, hαs, hβc, hβs, hr1, hr2⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.coords_k hB hS hT hξ hσ
  obtain ⟨μN, μW, 𝓕W, c₁, hμN, hμW, h𝓕W, hc₁, hpar⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.parseval_pol_k hB N e hec hes hrat hrat'
  obtain ⟨c₀, hc₀, hlam⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.lam_formula_k hB JS JT ξ₀ ν 𝓕 hν h𝓕 N α β e hCe he hβc hβs hr1 hr2
  obtain ⟨c₂, hc₂, hmap, hint⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.map_haar α hαc hαs ν hν μN hμN
  have hn0 : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  refine ⟨μW, 𝓕W, c₁ / (c₂ * ‖c₀‖ ^ 2), hμW, h𝓕W, by positivity, fun f hf => ?_⟩
  obtain ⟨Φ, hΦ, rfl⟩ := _root_.GlobalTheory.ThetaOntoF.exists_thV_eqF_k F E σ B hB nS (nT + nT) JS _ hS hT' ξ₀ hξ hσ hstd N e he hrat f hf
  obtain ⟨hΦc, hΦi, hΦm⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.schA_facts_k hB N μN hμN Φ hΦ
  have hnrm : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (thV B.ψ Φ ∘ e) =
      fun v => ((‖c₀‖ ^ 2 : ℝ) : ℂ) * (Φ (α v) * starRingEnd ℂ (Φ (α v))) := by
    funext v
    unfold nrm
    rw [hlam Φ hΦ v, map_mul, Complex.ofReal_pow, ← Complex.mul_conj' c₀]
    ring
  have hph : ∀ y v, phase σ JS JT ξ₀ B.ψ y v = B.ψ (α v ⬝ᵥ β y) := by
    intro y v
    unfold phase
    rw [he]
    have h1 : e (dCd F JT * v) = (α v, 0) := by
      have := hCe 0 v
      rwa [Matrix.mul_zero, zero_add, map_zero] at this
    have h2 : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
      have := hCe y 0
      rwa [Matrix.mul_zero, add_zero, map_zero] at this
    rw [h1, h2]
    simp [symV]
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [hnrm]
    exact continuous_const.mul ((hΦc.comp hαc).mul (Complex.continuous_conj.comp (hΦc.comp hαc)))
  · rw [hnrm]
    exact ((hint _).2 hΦi).const_mul _
  · rw [_root_.PositivityTheory.ThKW.AdelicSchwartzProperties.heis_C_k hB JS JT ξ₀ N α β e hCe he Φ y]
    have hl : ∫ w in 𝓕W, (thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e) w * starRingEnd ℂ ((thV B.ψ Φ ∘ e) w) ∂μW =
        (c₁ : ℂ) * ∫ x, B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x) ∂μN :=
      hpar _ (hΦm (β y)) Φ hΦ
    rw [hl, hnrm]
    simp_rw [hph]
    have hr : ∫ v, B.ψ (α v ⬝ᵥ β y) * (((‖c₀‖ ^ 2 : ℝ) : ℂ) * (Φ (α v) * starRingEnd ℂ (Φ (α v)))) ∂ν =
        ((‖c₀‖ ^ 2 : ℝ) : ℂ) * ((c₂ : ℂ) * ∫ x, B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x) ∂μN) := by
      rw [← hmap (fun x => B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x)), ← integral_const_mul]
      congr 1
      funext v
      ring
    rw [hr]
    have hc2 : (c₂ : ℂ) ≠ 0 := by exact_mod_cast hc₂.ne'
    have hc0 : ((‖c₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hn0 2).ne'
    have hn' : ((‖c₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    push_cast
    field_simp
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContDiffHeisIotaK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
noncomputable section
namespace GlobalTheory.ThetaSmoothF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem contDiff_heis_iota_k (σ : E →ₐ[F] E) (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) (x : WOF F E nS nT) :
    ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (_root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB)
  let φ : (IxF F nS nT → ℂ) →+ ℂ :=
    { toFun := fun v => lam (symplOHF σ JS JT ξ₀ x (iotaVF ι v))
      map_zero' := by rw [iotaVF_zero, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun u v => by rw [iotaVF_add, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _)] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ x (continuous_iotaVF hι))
  let eqv := (Module.finBasis ℝ (IxF F nS nT → ℂ)).equivFunL
  let L' : (Fin (Module.finrank ℝ (IxF F nS nT → ℂ)) → ℝ) →+ WOF F E nS nT :=
    (iotaHom ι).comp eqv.symm.toLinearEquiv.toAddMonoidHom
  have hL' : Continuous L' := (continuous_iotaVF hι).comp eqv.symm.continuous
  have hsm := hf.smooth _ L' hL' (fun t => real_iotaVF hι _) x
  have hg : ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => f (x + iotaVF ι v) := by
    have h1 := hsm.comp eqv.contDiff
    convert h1 using 1
    funext v
    simp [L', iotaHom]
  have e : (fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x) =
      fun v => Complex.exp (φ.toRealLinearMap hφ v) * f (x + iotaVF ι v) := by
    funext v
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ x _ (real_iotaVF hι v))]
    rfl
  rw [e]
  exact ((φ.toRealLinearMap hφ).contDiff.cexp).mul hg
end GlobalTheory.ThetaSmoothF
open GlobalTheory.ThetaSmoothF in
theorem GlobalTheory.ThetaSmoothF.sm_of_thetaF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 →
        Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι hψ f hf
  have hstd := _root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB
  let H := HMF (nS := nS) (nT := nT) JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)
  let B₀ : (IxF F nS nT → ℂ) →ₗ[ℝ] (IxF F nS nT → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
      (fun x x' y => by simp [Matrix.mulVec_add, dotProduct_add])
      (fun c x y => by simp [Matrix.mulVec_smul, dotProduct_smul])
      (fun x y y' => by simp [add_dotProduct])
      (fun c x y => by simp [star_smul, smul_dotProduct])
  let om : (IxF F nS nT → ℂ) →L[ℝ] (IxF F nS nT → ℂ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap ∘ₗ B₀)
  have e : (fun x y => om x y) = fun x y => (star y ⬝ᵥ H *ᵥ x).im := rfl
  have hH : IsHeis (fun x y : IxF F nS nT → ℂ => (star y ⬝ᵥ H *ᵥ x).im) (rhoVF σ JS JT ξ₀ B.ψ hψ ι) := by
    refine ⟨fun g => ?_, fun u v g => ?_, fun u g => norm_rhoBF hψ _ g, fun g => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι 0) g = g
      rw [iotaVF_zero]
      exact rhoBF_zero hψ g
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι v) g) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (u + v)) g
      rw [rhoBF_rhoBF, iotaVF_add, _root_.GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι u v]
    · exact (_root_.GlobalTheory.RealWeilF.continuous_rhoBF F E σ nS nT JS JT ξ₀ B.ψ hψ g).comp (continuous_iotaVF hι)
  refine _root_.GlobalTheory.RealWeil.sm_of_weak_deriv_closed (IxF F nS nT → ℂ) (BBF σ JS JT ξ₀ B.ψ) om (rhoVF σ JS JT ξ₀ B.ψ hψ ι) (e ▸ hH)
    (WOF F E nS nT) (ev _ _) norm_ev_le (fun b C => norm_QB_le b)
    (fun x v => ⟨B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)), x + iotaVF ι v, fun b => rfl⟩)
    {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g.1} ?_ ?_ f hf
  · intro g hg x
    exact (_root_.GlobalTheory.ThetaSmoothF.contDiff_heis_iota_k σ B hB JS JT ξ₀ hι hg x).differentiable (by simp)
  · intro g hg z
    let L : ℝ →+ WOF F E nS nT :=
      { toFun := fun t => iotaVF ι (t • z)
        map_zero' := by rw [zero_smul, iotaVF_zero]
        map_add' := fun s t => by rw [add_smul, iotaVF_add] }
    have hL : Continuous L := (continuous_iotaVF hι).comp (continuous_id.smul continuous_const)
    have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => real_iotaVF hι _
    let d : WOF F E nS nT → ℂ := fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g.1 w) 0
    have hlev : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u d = d := by
      obtain ⟨U, hU, hUf⟩ := hg.level
      exact ⟨U, hU, fun u hu hu0 =>
        _root_.GlobalTheory.T.theta_function_rapid_decay F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 L hL hL0 u hu0 (hUf u hu hu0)⟩
    have hsm : ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L' →
        (∀ t, (L' t).map (finPartF F E) = 0) → ∀ w, ContDiff ℝ ∞ fun t => d (w + L' t) :=
      fun k L' hL' hL'0 w => _root_.GlobalTheory.T.theta_function_integrable F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 k L' hL' hL'0 w
    have hd : IsThetaFunOF σ JS JT ξ₀ B.ψ d :=
      ⟨fun γ w => _root_.GlobalTheory.T.theta_function_moderate_growth F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 γ w, hlev,
        _root_.GlobalTheory.T.theta_integral_unfolding F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd d hlev hsm, hsm⟩
    have hb := _root_.GlobalTheory.TowerFD.thetaFunOF_bounded F E σ nS nT JS JT ξ₀ B.ψ hψ d hd
    refine ⟨toBF d hd.cont hb hd.quasi, hd, fun x => ?_⟩
    exact (_root_.GlobalTheory.T.theta_function_smooth_vectors F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 x).hasDerivAt
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftNonvanishing
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_theta_lift_nonvanishing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (w + L t) := by
  first | exact @_root_.GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM_k | exact _root_.GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM_k | (intros; apply _root_.GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsEigenvectorSplitIdempotent
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
theorem _root_.GlobalTheory.T.exists_eigenvector_split_idempotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  exact @_root_.PositivityTheory.ThKW.SplitVacuumEigenvectors.exists_vac_split_k
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFiniteDimensionalWeilArchimedeanOrbit
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
namespace UpperTheory.PolynomialDataFiniteKType₂
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
private theorem mat_inv_mul_pk {X : Spc F E n} (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  have : mat (g⁻¹ * g) = mat g⁻¹ * mat g := rfl
  rw [← this, inv_mul_cancel]; rfl
private theorem gInf_le_pk {W : Spc F E d} {k : UA σ W.J} (hk : k ∈ gInf σ W) : k ∈ UAt σ W (evI F) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    intro u _
    have : mat (1 : UA σ W.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  | mul g h _ _ hg hh =>
    intro u hu
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      have : mat (g * h) = mat g * mat h := rfl
      rw [this, sub_mul, one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]
  | inv g _ hg =>
    intro u hu
    have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, mat_inv_mul_pk, mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]
private noncomputable def pureL_pk {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
end UpperTheory.PolynomialDataFiniteKType₂
open UpperTheory.PolynomialDataFiniteKType₂ in
theorem UpperTheory.exists_finiteDimensional_weil_archimedean_orbit :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ Φ ∈ PolData B M, ∃ V : Submodule ℂ (Fn F n d), FiniteDimensional ℂ V ∧ V ≤ schA F (Fin n × Fin d) ∧ ∀ k ∈ gInf σ W, om (1, k) Φ ∈ V := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hK : ∀ k ∈ gInf σ W, k ∈ KInf σ W B.emb := fun k hk =>
    ⟨gInf_le_pk hk, fun w => by
      rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hP.skew.sig w) (hP.skew.cartan w)]
      exact Commute.one_right _⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := h2
    have hD : GlobalTheory.ThK.Dbl.Prs.Dat B M hfin.toFinset f φ :=
      ⟨hf, h1, fun v hv => by simpa using hv⟩
    obtain ⟨g, hg, e⟩ := hD.pureA hP.good
    obtain ⟨U, hU, hU'⟩ := _root_.GlobalTheory.ThK.Dbl.polFin_k hP f hf
    refine ⟨U.map (pureL_pk φ), inferInstance, ?_, fun k hk => ?_⟩
    · rintro _ ⟨f', -, rfl⟩
      exact Submodule.subset_span ⟨f', g, hg, e f'⟩
    · obtain ⟨A, hA⟩ := _root_.GlobalTheory.ThK.Dbl.Prs.inf_op_k _root_.PositivityTheory.ThKF.A.archOp_k hP (hK k hk)
      have hact := (hA f hf).2
      exact ⟨A f, hU' k (hK k hk) _ hact, (hact _ (hD.rest hP.good)).symm⟩
  | zero => exact ⟨⊥, inferInstance, bot_le, fun k _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    obtain ⟨V', h1', h2', h3'⟩ := hy
    exact ⟨V ⊔ V', inferInstance, sup_le h2 h2', fun k hk => by
      rw [map_add (f := _)]; exact Submodule.add_mem_sup (h3 k hk) (h3' k hk)⟩
  | smul c x _ hx =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    exact ⟨V, h1, h2, fun k hk => by rw [map_smul]; exact V.smul_mem c (h3 k hk)⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsNonzeroThetaFunction
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.exists_nonzero_theta_function : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∃ f₀ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 := by
  first | exact @_root_.GlobalTheory.ThetaNonzeroF.exists_isThetaFunOF_ne_zero_k | exact _root_.GlobalTheory.ThetaNonzeroF.exists_isThetaFunOF_ne_zero_k | (intros; apply _root_.GlobalTheory.ThetaNonzeroF.exists_isThetaFunOF_ne_zero_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeightFunctionContinuousPos
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_function_continuous_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x := by
  first | exact @_root_.GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos_k | exact _root_.GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos_k | (intros; apply _root_.GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LevelK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem level_k : _root_.PositivityTheory.ThKEst.Level_k := _root_.PositivityTheory.ThKEst.level_of_k _root_.PositivityTheory.ThKEst.coefEq_of_k fourierInj_of (_root_.PositivityTheory.ThKEst.coefBd_of_k coefReal_of)
end PositivityTheory.ThKEst
end
end
end

