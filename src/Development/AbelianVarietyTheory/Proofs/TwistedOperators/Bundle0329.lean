module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedThetaSeriesRapidDecay
section
namespace I195MixedCoordinates_3aa6f9d92ad8d1052bda2e20

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_3aa6f9d92ad8d1052bda2e20

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.MixWeight

theorem trace_mul_single {m r : ℕ} (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin m) (j : Fin r) (c : ℂ) :
    (M * Matrix.single i j c).trace = M j i * c := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single j (fun b _ hb => Finset.sum_eq_zero fun c' _ => by
    rw [if_neg fun h => hb h.2.symm, mul_zero]) (by simp)]
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg fun h => hb h.1.symm, mul_zero]) (by simp)]
  simp

theorem norm_le_forms {m r : ℕ} (B : Matrix (Fin r) (Fin m) ℂ) (ξ : ℂ) (hξ : ξ ≠ 0) (i : Fin m) (j : Fin r) :
    ‖B j i‖ ≤ ‖ξ‖⁻¹ * ∑ b : Bool, |2 * (ξ * (B * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false, trace_mul_single, mul_one]
  rw [le_inv_mul_iff₀ hξn, ← norm_mul]
  have h1 := Complex.norm_le_abs_re_add_abs_im (ξ * B j i)
  have e1 : |2 * (ξ * (B j i * Complex.I)).re| = 2 * |(ξ * B j i).im| := by
    rw [← mul_assoc, Complex.mul_I_re, abs_mul, abs_neg, abs_two]
  have e2 : |2 * (ξ * B j i).re| = 2 * |(ξ * B j i).re| := by rw [abs_mul, abs_two]
  rw [e1, e2]
  linarith [abs_nonneg (ξ * B j i).re, abs_nonneg (ξ * B j i).im]

theorem sum_norm_le {m r : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (hG : IsUnit G.det) (ξ : ℂ) (hξ : ξ ≠ 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : Matrix (Fin m) (Fin r) ℂ,
      ∑ k, ∑ j, ‖x k j‖ ≤ A * ∑ i : Fin m, ∑ j : Fin r, ∑ b : Bool,
        |2 * (ξ * (xᴴ * G * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
  have hg0 : 0 ≤ ∑ i, ∑ k, ‖G⁻¹ i k‖ := by positivity
  refine ⟨m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ‖ξ‖⁻¹, by positivity, fun x => ?_⟩
  have hx : x = (xᴴ * G * G⁻¹)ᴴ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one, Matrix.conjTranspose_conjTranspose]
  have hxkj : ∀ k j, ‖x k j‖ ≤ (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ‖(xᴴ * G) j i‖ := by
    intro k j
    rw [hx, Matrix.conjTranspose_apply, norm_star, Matrix.mul_apply, ← hx]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact (Finset.single_le_sum (f := fun k' => ‖G⁻¹ i k'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i' => ∑ k', ‖G⁻¹ i' k'‖) (fun _ _ => by positivity) (Finset.mem_univ i))
  have key : ∑ k, ∑ j, ‖x k j‖ ≤ m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ‖ξ‖⁻¹ * ∑ i : Fin m, ∑ j : Fin r, ∑ b : Bool,
      |2 * (ξ * (xᴴ * G * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
    calc ∑ k, ∑ j, ‖x k j‖ ≤ ∑ _k : Fin m, ∑ j, (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ‖(xᴴ * G) j i‖ :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => hxkj k j
      _ = m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ j, ∑ i, ‖(xᴴ * G) j i‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, mul_assoc]
      _ = m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ∑ j, ‖(xᴴ * G) j i‖ := by congr 1; exact Finset.sum_comm
      _ ≤ m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ∑ j, ‖ξ‖⁻¹ * ∑ b : Bool,
            |2 * (ξ * (xᴴ * G * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
          gcongr with i _ j _
          exact norm_le_forms _ ξ hξ i j
      _ = _ := by
          rw [mul_assoc ((m : ℝ) * ∑ i, ∑ k, ‖G⁻¹ i k‖) ‖ξ‖⁻¹, Finset.mul_sum (a := ‖ξ‖⁻¹)]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          rfl
  exact key

end GlobalTheory.MixWeight

namespace GlobalTheory.MixWeight

open GlobalTheory.MixModel

variable {D : D7}

theorem enorm_mixS_le' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W : HSp D} {ρ : ℕ}
    (d : HypDec V V₀ ρ) (v : GlobalTheory.Unf.VolM D W.rank ρ) (φ : WO V W → ℂ) (x : Mx D W.rank ρ) (w : WO V₀ W) :
    ‖d.mixS W ψ v.μ v.𝓕 φ x w‖ₑ ≤ GlobalTheory.HeisTaylor.supN φ := by
  simp only [HypDec.mixS, HypDec.integrandS_eq]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ a in v.𝓕, ‖ψ (symplOH V W (d.extY W a) (d.extX W x)) * φ (d.extY W a + d.extX W x + d.ext0 W w)‖ₑ ∂v.μ
      ≤ ∫⁻ _ in v.𝓕, GlobalTheory.HeisTaylor.supN φ ∂v.μ := by
        refine lintegral_mono fun a => ?_
        rw [enorm_mul, ← ofReal_norm (ψ _), hψ.1.2.1, ENNReal.ofReal_one, one_mul]
        exact GlobalTheory.HeisTaylor.enorm_le_supN φ _
    _ = _ := by rw [setLIntegral_const, v.covol.2.2, mul_one]

theorem one_add_pow_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) : (1 + L) ^ N ≤ 2 ^ N * (1 + L ^ N) := by
  first
  | exact @_root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le
  | exact _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le
  | (apply _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le ..)

theorem mixS_weight_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ N : ℕ,
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ → ∀ x : Mx D X.rank r,
      ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N) ≤
        ENNReal.ofReal C * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) GlobalTheory.HeisTaylor.supN k Ψ := by
  intro D ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ N
  let v : GlobalTheory.Unf.VolM D X.rank r := ⟨μ', 𝓕', hμ⟩
  let zA : D.what₂.Tau × Fin X.rank × Fin r × Bool → Matrix (Fin X.rank) (Fin r) ℂ :=
    fun a => Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)
  let ℓ : D.what₂.Tau × Fin X.rank × Fin r × Bool → Mx D X.rank r → ℝ := fun a x =>
    |2 * (tauE D a.1 D.host.xi0 * ((compAt θ a.1 x)ᴴ * gramAt D X a.1 * zA a).trace).re|
  choose Z hZ using fun a : D.what₂.Tau × Fin X.rank × Fin r × Bool =>
    GlobalTheory.Unf.norm_mixS_dRho_ge D ψ hψ θ hθ V S₀ X r d v a.1 (zA a)
  have laws := GlobalTheory.Unf.SupFin.supSob_laws D ψ hψ θ hθ V X
  choose C hC using fun a : D.what₂.Tau × Fin X.rank × Fin r × Bool => (laws.2.1 a.1 (Z a)).2
  let K : NNReal := ∑ a, C a
  have hL0 : ∀ x, 0 ≤ ∑ a, ℓ a x := fun x => Finset.sum_nonneg fun a _ => abs_nonneg _

  have hpow : ∀ n : ℕ, ∀ f : WO V X → ℂ, IsThetaFunO ψ V X f → ∀ x,
      ENNReal.ofReal ((∑ a, ℓ a x) ^ n) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ ≤
        ((K ^ n : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ n f := by
    intro n
    induction n with
    | zero =>
      intro f hf x
      rw [pow_zero, ENNReal.ofReal_one, one_mul, pow_zero, ENNReal.coe_one, one_mul]
      exact (enorm_mixS_le' hψ d v f x 0).trans (GlobalTheory.Size.wordSum_zero _ _ _).ge
    | succ n ih =>
      intro f hf x
      have step : ∀ a, ENNReal.ofReal ((∑ a, ℓ a x) ^ n) * (ENNReal.ofReal (ℓ a x) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ) ≤
          ((K ^ n : NNReal) : ENNReal) * ((C a : ENNReal) * GlobalTheory.Unf.supSob ψ θ (n + 1) f) := by
        intro a
        have hg := GlobalTheory.OrientedHeis.theta_dRho hθ hψ a.1 (Z a) hf
        have h1 : ENNReal.ofReal (ℓ a x) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ ≤
            ‖d.mixS X ψ μ' 𝓕' (dRho (heisO ψ V X) θ a.1 (Z a) f) x 0‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hZ a f hf x 0)
        calc _ ≤ ENNReal.ofReal ((∑ a, ℓ a x) ^ n) *
              ‖d.mixS X ψ μ' 𝓕' (dRho (heisO ψ V X) θ a.1 (Z a) f) x 0‖ₑ := by gcongr
          _ ≤ ((K ^ n : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ n (dRho (heisO ψ V X) θ a.1 (Z a) f) := ih _ hg x
          _ ≤ _ := by gcongr; exact hC a n f hf
      calc ENNReal.ofReal ((∑ a, ℓ a x) ^ (n + 1)) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ
          = ∑ a, ENNReal.ofReal ((∑ a, ℓ a x) ^ n) * (ENNReal.ofReal (ℓ a x) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ) := by
            rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg (hL0 x) n),
              ENNReal.ofReal_sum_of_nonneg (fun a _ => abs_nonneg _), Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
        _ ≤ ∑ a, ((K ^ n : NNReal) : ENNReal) * ((C a : ENNReal) * GlobalTheory.Unf.supSob ψ θ (n + 1) f) :=
            Finset.sum_le_sum fun a _ => step a
        _ = ((K ^ (n + 1) : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ (n + 1) f := by
            rw [← Finset.mul_sum, ← Finset.sum_mul, pow_succ]
            simp only [K, ENNReal.coe_mul, ENNReal.ofNNReal_finsetSum]
            ring

  have hG : ∀ τ : D.what₂.Tau, IsUnit (gramAt D X τ).det := fun τ => by
    have e : (gramAt D X τ).det = tauE D τ (HSpace.gram X).det := by rw [RingHom.map_det]; rfl
    rw [isUnit_iff_ne_zero, e]
    exact (map_ne_zero_iff _ (tauE D τ).injective).2 (gram_det_ne X)
  have hξ : ∀ τ : D.what₂.Tau, tauE D τ D.host.xi0 ≠ 0 := fun τ =>
    (map_ne_zero_iff _ (tauE D τ).injective).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  choose A hA0 hA using fun τ : D.what₂.Tau => sum_norm_le (r := r) (gramAt D X τ) (hG τ) _ (hξ τ)
  have hAt : 0 ≤ ∑ τ, A τ := Finset.sum_nonneg fun τ _ => hA0 τ
  have hrs : ∀ x : Mx D X.rank r, ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ (∑ τ, A τ) * ∑ a, ℓ a x := by
    intro x
    have e : ∑ a, ℓ a x = ∑ τ, ∑ i : Fin X.rank, ∑ j : Fin r, ∑ b : Bool, ℓ (τ, i, j, b) x := by
      simp only [Fintype.sum_prod_type]
    rw [e, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => (hA τ (compAt θ τ x)).trans ?_
    refine mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := A) (fun τ _ => hA0 τ) (Finset.mem_univ τ)) ?_
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨N, (1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + ((K ^ N : NNReal) : ℝ)), by positivity, fun Ψ hΨ x => ?_⟩
  show _ ≤ _ * GlobalTheory.Unf.supSob ψ θ N Ψ
  have hLn := hL0 x
  have hb : (1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N ≤
      (1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + (∑ a, ℓ a x) ^ N) := by
    have h1 : 1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ (1 + ∑ τ, A τ) * (1 + ∑ a, ℓ a x) := by
      nlinarith [hrs x]
    calc (1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N ≤ ((1 + ∑ τ, A τ) * (1 + ∑ a, ℓ a x)) ^ N :=
          pow_le_pow_left₀ (by positivity) h1 N
      _ = (1 + ∑ τ, A τ) ^ N * (1 + ∑ a, ℓ a x) ^ N := mul_pow _ _ _
      _ ≤ (1 + ∑ τ, A τ) ^ N * (2 ^ N * (1 + (∑ a, ℓ a x) ^ N)) := by gcongr; exact one_add_pow_le hLn N
      _ = _ := by ring
  have h0 := hpow 0 Ψ hΨ x
  have hN := hpow N Ψ hΨ x
  rw [pow_zero, ENNReal.ofReal_one, one_mul, pow_zero, ENNReal.coe_one, one_mul] at h0
  have hmono : GlobalTheory.Unf.supSob ψ θ 0 Ψ ≤ GlobalTheory.Unf.supSob ψ θ N Ψ := GlobalTheory.Size.wordSum_mono (Nat.zero_le N) Ψ
  calc ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N)
      ≤ ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + (∑ a, ℓ a x) ^ N)) := by
        gcongr
    _ = ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N) * (‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ +
          ENNReal.ofReal ((∑ a, ℓ a x) ^ N) * ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ) := by
        rw [ENNReal.ofReal_mul (p := (1 + ∑ τ, A τ) ^ N * 2 ^ N) (by positivity),
          ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
        ring
    _ ≤ ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N) * (GlobalTheory.Unf.supSob ψ θ N Ψ +
          ((K ^ N : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ N Ψ) :=
        mul_le_mul_of_nonneg_left (add_le_add (h0.trans hmono) hN) zero_le
    _ = ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + ((K ^ N : NNReal) : ℝ))) * GlobalTheory.Unf.supSob ψ θ N Ψ := by
        rw [ENNReal.ofReal_mul (p := (1 + ∑ τ, A τ) ^ N * 2 ^ N) (by positivity),
          ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
        ring

end GlobalTheory.MixWeight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusInfConjLeSpanTypePrimesProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModulConj

open Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

theorem le_of_le_primes {R : Type} [CommRing R] [IsDedekindDomain R] {I J : Ideal R} (hJ : Squarefree J)
    (h : ∀ P : Ideal R, P.IsPrime → J ≤ P → I ≤ P) : I ≤ J := by
  have hrad : I ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun P hP => h P hP.2 hP.1
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)
  exact Ideal.le_of_dvd (hJ.isRadical n I (Ideal.dvd_iff_le.2 hn))

theorem squarefree_span_g (D : D7) (k : Fin 2) :
    Squarefree (Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)}) := by
  have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime k).ne_zero
  exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (g_splits D k).2

end GlobalTheory.ModulConj

namespace GlobalTheory.ModulConj

open Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

theorem inf_le_place {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (k : Fin 2)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    G.modul ⊓ D.host.conj • G.modul ≤ P.asIdeal := by
  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal
    rwa [map_natCast]
  have hS : P.under (𝓞 D.host.F) ∈ G.pl.S0 := by
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  set v := P.under (𝓞 D.host.F) with hvdef
  have hw : (G.pl.w v).under (𝓞 D.host.F) = v := G.pl.under_w hS
  have hmod : G.modul ≤ (G.pl.w v).asIdeal := by
    have hd : (G.pl.w v).asIdeal ^ G.pl.depth sc v ∣ G.modul := Finset.dvd_prod_of_mem _ hS
    exact (Ideal.le_of_dvd hd).trans (Ideal.pow_le_self (G.pl.depth_pos sc v).ne')
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (P := G.pl.w v) (Q := P) (by rw [hw]) with h | h
  · rw [h]
    exact inf_le_left.trans hmod
  · rw [h]
    intro x hx
    have hx2 := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 (Ideal.mem_inf.1 hx).2
    have hy : D.host.conj⁻¹ • x ∈ (G.pl.w v).asIdeal := hmod hx2
    have e : Formalism.DivisionValues.cO D.host.E (D.host.conj⁻¹ • x) = x := by
      apply RingOfIntegers.ext
      show star ((D.host.conj⁻¹ • x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E)
      rw [GlobalTheory.TypePlaces.star_eq_conj]
      exact D.host.conj.apply_symm_apply (x : D.host.E)
    show x ∈ (G.pl.w v).asIdeal.map (Formalism.DivisionValues.cO D.host.E)
    rw [← e]
    exact Ideal.mem_map_of_mem _ hy

theorem modul_inf_conj_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc),
    G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} := by
  intro D T L sc G
  have hk : ∀ k : Fin 2, G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} := by
    intro k
    refine le_of_le_primes (squarefree_span_g D k) fun Q hQ hle => ?_
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q := hle (Ideal.subset_span rfl)
    have hne : Q ≠ ⊥ := by
      rintro rfl
      exact (D.host.g_prime k).ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hg))
    exact inf_le_place G k ⟨Q, hQ, hne⟩ hg
  have hco : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  intro x hx
  rw [Ideal.mem_span_singleton, Nat.cast_mul]
  exact hco.mul_dvd (Ideal.mem_span_singleton.1 (hk 0 hx)) (Ideal.mem_span_singleton.1 (hk 1 hx))

end GlobalTheory.ModulConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeNormRationalTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.MajDom

theorem re_form_le {n : ℕ} (G fr : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool)
    (h : frᴴ * Formalism.REAL.Jm ε * fr = G) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (G *ᵥ v)).re ≤ ∑ i, ‖(fr *ᵥ v) i‖ ^ 2 := by
  subst h
  have e : star v ⬝ᵥ ((frᴴ * Formalism.REAL.Jm ε * fr) *ᵥ v) =
      star (fr *ᵥ v) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (fr *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have hd : ∀ w : Fin n → ℂ, Formalism.REAL.Jm ε *ᵥ w = fun i => (if ε i = true then (1 : ℂ) else -1) * w i := by
    intro w; funext i; exact Matrix.mulVec_diagonal _ _ _
  rw [e, hd, dotProduct, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hw : star (fr *ᵥ v) i * ((if ε i = true then (1 : ℂ) else -1) * (fr *ᵥ v) i) =
      (if ε i = true then (1 : ℂ) else -1) * ((‖(fr *ᵥ v) i‖ : ℂ) ^ 2) := by
    rw [← Complex.conj_mul', Pi.star_apply, Complex.star_def]
    ring
  rw [hw]
  split_ifs
  · simp only [one_mul]
    norm_cast
  · have : (-((‖(fr *ᵥ v) i‖ : ℂ) ^ 2)).re = -(‖(fr *ᵥ v) i‖ ^ 2) := by norm_cast
    rw [neg_one_mul, this]
    nlinarith [sq_nonneg ‖(fr *ᵥ v) i‖]

theorem form_isom {n : ℕ} (G P : Matrix (Fin n) (Fin n) ℂ) (hP : Pᴴ * G * P = G) (u : Fin n → ℂ) :
    star (P *ᵥ u) ⬝ᵥ (G *ᵥ (P *ᵥ u)) = star u ⬝ᵥ (G *ᵥ u) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP]

end GlobalTheory.SepPer.MajDom

namespace GlobalTheory.SepPer.MajDom

variable {D : D7}

theorem tauE_sig (τ : D.what₂.Tau) (a : D.host.E) :
    tauE D τ (D.sp.cm.sig a) = starRingEnd ℂ (tauE D τ a) :=
  D.sp.cm.cmUnram.2.1 _ a

theorem cmp_mulVec (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (γ : GA D V) (z₀ z : Fin V.rank → D.host.E)
    (h : mt V γ *ᵥ ratV z₀ = ratV z) (τ : D.what₂.Tau) :
    cmp θ τ γ *ᵥ (fun i => tauE D τ (z₀ i)) = fun i => tauE D τ (z i) := by
  let φ : AE D →+* ℂ := (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hφ : ∀ e : D.host.E, φ (incA D e) = tauE D τ e := by
    intro e
    show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ e)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    exact (hθ τ).1 e
  have hc : cmp θ τ γ = (mt V γ).map φ := rfl
  have e1 : (⇑φ ∘ ratV z₀) = fun j => tauE D τ (z₀ j) := funext fun j => hφ (z₀ j)
  funext i
  have := congrArg (fun w => φ (w i)) h
  simp only [RingHom.map_mulVec] at this
  rw [e1] at this
  rw [hc, this]
  exact hφ (z i)

theorem form_zv {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) :
    star (fun i => tauE D τ (zv d i)) ⬝ᵥ (gramAt D V τ *ᵥ fun i => tauE D τ (zv d i)) = 1 := by
  have hg := congrArg (fun M => tauE D τ (M 0 0)) d.gram
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [antiDiagonalSignGramMatrix, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    tauE_sig] at hg
  simp only [dotProduct, Matrix.mulVec, gramAt, Matrix.map_apply, Pi.star_apply, Complex.star_def, Finset.mul_sum, zv]
  refine Eq.trans ?_ (hg.trans (by simp))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc]
  congr 1
  exact (tauE_sig τ _).symm

end GlobalTheory.SepPer.MajDom

namespace GlobalTheory.SepPer.MajDom

theorem one_le_nrm : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (B : Fr V) (x : GA D Y)
    (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z →
    ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  intro D θ hθ Y V d B x γ z _ hmt τ
  set G := gramAt D V τ
  set u₀ : Fin V.rank → ℂ := fun i => tauE D τ (zv d i) with hu₀
  set P := cmp θ τ (stabilizerEmbedding d x)⁻¹ * cmp θ τ γ with hP
  have hv : cmp θ τ (stabilizerEmbedding d x)⁻¹ *ᵥ (fun i => tauE D τ (z i)) = P *ᵥ u₀ := by
    rw [← cmp_mulVec θ hθ γ (zv d) z hmt τ, Matrix.mulVec_mulVec]
  have hPG : Pᴴ * G * P = G := by
    have h1 := GlobalTheory.Doubling.infMat_isometry hθ τ (stabilizerEmbedding d x)⁻¹
    have h2 := GlobalTheory.Doubling.infMat_isometry hθ τ γ
    calc Pᴴ * G * P = (cmp θ τ γ)ᴴ * ((cmp θ τ (stabilizerEmbedding d x)⁻¹)ᴴ * G * cmp θ τ (stabilizerEmbedding d x)⁻¹) * cmp θ τ γ := by
          rw [hP, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]
  have hform : star (P *ᵥ u₀) ⬝ᵥ (G *ᵥ (P *ᵥ u₀)) = 1 := by
    rw [form_isom G P hPG u₀]
    exact form_zv d τ
  have key := re_form_le G (B.fr τ) (B.ε τ) (B.fr_gram τ) (P *ᵥ u₀)
  rw [hform, Complex.one_re] at key
  unfold nrm eu
  rw [hv]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt key

end GlobalTheory.SepPer.MajDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientCharPartialLEntireNonvanishingIntegersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_char_partial_L_entire_nonvanishing_integers : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, i < j → j < c.m → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) z) ∧ ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
  first | exact @GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero | exact GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero | (intros; apply GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero <;> assumption)
end

