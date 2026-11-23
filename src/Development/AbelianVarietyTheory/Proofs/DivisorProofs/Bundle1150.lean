module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGram
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma continuousAt_cutoff_mul_chern_form_coeff {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hG : _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G v) (hdet : IsUnit (G v).det) (hρ : ContinuousAt ρ v) :
    ContinuousAt (fun x => (ρ x : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G x)
      v := by
  refine ContinuousAt.mul (Complex.continuous_ofReal.continuousAt.comp (f := ρ) hρ) ?_
  refine _root_.GlobalTheory.GoodTop.continuousAt_mixTop (K := fun x _ => _root_.GlobalTheory.GoodTop.curvAt G x)
    fun i a b p q => ?_
  have h := hG.curv (j := 0) hdet
    (by rw [zero_add]; first | exact le_top | exact_mod_cast (le_top : ((2 : ℕ∞) ≤ ⊤)) | exact WithTop.coe_le_coe.2 le_top)
    (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q
  exact h.continuousAt


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
      IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → ContDiffOn ℝ ∞ ρ U →
      (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) U := by
  intro n r _ _ U K G₀ ρ hU hK hKU hG₀ hρ hρK
  have hcont : ContinuousOn
      (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) K :=
    fun v hv => (continuousAt_cutoff_mul_chern_form_coeff (hG₀ v (hKU hv)).1 (hG₀ v (hKU hv)).2
      (hρ.contDiffAt (hU.mem_nhds (hKU hv))).continuousAt).continuousWithinAt
  refine (hcont.integrableOn_compact hK).of_forall_diff_eq_zero hU.measurableSet
    fun v hv => ?_
  rw [hρK v hv.1 hv.2, Complex.ofReal_zero, zero_mul]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqRankOneFactorSL2OfGeometricOnShells
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace ShellSum

open Function

def shell {X : Type} (H : ℕ → Set X) : ℕ → Set X
  | 0 => H 0
  | j + 1 => H (j + 1) \ H j

def shellVal (q : ℕ) (b : ℂ) : ℕ → ℂ
  | 0 => 1
  | j + 1 => (b / q) ^ (j + 1)

def shellMass (q : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => (q : ℝ) ^ (j + 1) - (q : ℝ) ^ j

theorem shellMass_nonneg (q : ℕ) (hq : 2 ≤ q) (j : ℕ) : 0 ≤ shellMass q j := by
  cases j with
  | zero => simp [shellMass]
  | succ j =>
    simp only [shellMass, sub_nonneg]
    exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q)) (Nat.le_succ j)

theorem hasSum_shell (q : ℕ) (hq : 2 ≤ q) (b : ℂ) (hb : ‖b‖ < 1) :
    HasSum (fun j => shellVal q b j * (shellMass q j : ℂ)) (cSL q b) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : HasSum (fun j : ℕ => b ^ j * (b * (1 - (q : ℂ)⁻¹))) ((1 - b)⁻¹ * (b * (1 - (q : ℂ)⁻¹))) :=
    (hasSum_geometric_of_norm_lt_one hb).mul_right _
  have hb1 : (1 - b) ≠ 0 := by
    intro h
    have : b = 1 := by linear_combination -h
    rw [this] at hb; simp at hb
  have e1 : (fun n : ℕ => shellVal q b (n + 1) * (shellMass q (n + 1) : ℂ)) =
      fun j => b ^ j * (b * (1 - (q : ℂ)⁻¹)) := by
    funext j; simp only [shellVal, shellMass, div_pow]; push_cast; field_simp; ring
  have e2 : cSL q b - ∑ i ∈ Finset.range 1, shellVal q b i * (shellMass q i : ℂ) =
      (1 - b)⁻¹ * (b * (1 - (q : ℂ)⁻¹)) := by
    simp only [Finset.range_one, Finset.sum_singleton, shellVal, shellMass, cSL, Complex.ofReal_one]
    field_simp; ring
  refine (hasSum_nat_add_iff' 1).1 ?_
  show HasSum (fun n : ℕ => shellVal q b (n + 1) * (shellMass q (n + 1) : ℂ))
    (cSL q b - ∑ i ∈ Finset.range 1, shellVal q b i * (shellMass q i : ℂ))
  rw [e1, e2]; exact h1

theorem mem_shell_iff {X : Type} {H : ℕ → Set X} (hmono : Monotone H) (j : ℕ) (x : X) :
    x ∈ shell H j ↔ x ∈ H j ∧ ∀ i < j, x ∉ H i := by
  cases j with
  | zero => simp [shell]
  | succ j =>
    simp only [shell, Set.mem_diff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i hi hx => h2 (hmono (Nat.lt_succ_iff.1 hi) hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 j (Nat.lt_succ_self j)⟩

theorem shell_disjoint {X : Type} {H : ℕ → Set X} (hmono : Monotone H) :
    Pairwise (Disjoint on shell H) := by
  have key : ∀ i j, i < j → Disjoint (shell H i) (shell H j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    exact ((mem_shell_iff hmono j x).1 hj).2 i hij ((mem_shell_iff hmono i x).1 hi).1
  intro i j hij
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem iUnion_shell {X : Type} {H : ℕ → Set X} (hmono : Monotone H) (hU : ⋃ j, H j = Set.univ) :
    ⋃ j, shell H j = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hex : ∃ n, x ∈ H n := Set.mem_iUnion.1 (hU ▸ Set.mem_univ x)
  exact Set.mem_iUnion.2 ⟨Nat.find hex, (mem_shell_iff hmono _ x).2
    ⟨Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩⟩

theorem integral_geom_on_shells {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℕ) (hq : 2 ≤ q) (a : ℂ)
    (ha : ‖a‖ < 1) (H : ℕ → Set X) (hH : ∀ j, MeasurableSet (H j)) (hmono : Monotone H)
    (hU : ⋃ j, H j = Set.univ) (hμ : ∀ j, μ (H j) = (q : ENNReal) ^ j) (F : X → ℂ)
    (hF0 : ∀ x ∈ H 0, F x = 1) (hF : ∀ j x, x ∈ H (j + 1) → x ∉ H j → F x = (a / q) ^ (j + 1)) :
    Integrable F μ ∧ ∫ x, F x ∂μ = cSL q a ∧ ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ := by
  set S := shell H with hSdef
  have hSm : ∀ j, MeasurableSet (S j) := by
    intro j; cases j with
    | zero => exact hH 0
    | succ j => exact (hH _).diff (hH _)
  have hSd : Pairwise (Disjoint on S) := shell_disjoint hmono
  have hSU : ⋃ j, S j = Set.univ := iUnion_shell hmono hU
  have hSF : ∀ j, ∀ x ∈ S j, F x = shellVal q a j := by
    intro j x hx; cases j with
    | zero => exact hF0 x hx
    | succ j => exact hF j x hx.1 hx.2
  have hSμ : ∀ j, μ (S j) = ENNReal.ofReal (shellMass q j) := by
    intro j; cases j with
    | zero => simp [hSdef, shell, shellMass, hμ]
    | succ j =>
      show μ (H (j + 1) \ H j) = _
      rw [measure_diff (hmono (Nat.le_succ j)) (hH j).nullMeasurableSet
          (by rw [hμ]; exact ENNReal.pow_ne_top (by simp)),
        hμ, hμ, shellMass, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  have hSr : ∀ j, μ.real (S j) = shellMass q j := by
    intro j; rw [Measure.real, hSμ, ENNReal.toReal_ofReal (shellMass_nonneg q hq j)]
  have hmeas : AEStronglyMeasurable F μ := by
    rw [← Measure.restrict_univ (μ := μ), ← hSU, aestronglyMeasurable_iUnion_iff]
    intro j
    refine (aestronglyMeasurable_const (b := shellVal q a j)).congr ?_
    filter_upwards [ae_restrict_mem (hSm j)] with x hx
    exact (hSF j x hx).symm
  set s : ℝ := (1 - (q : ℝ)⁻¹ * ‖a‖) / (1 - ‖a‖) with hsdef
  have hq1 : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ q))
  have hs0 : 0 ≤ s := by
    apply div_nonneg
    · have : (q : ℝ)⁻¹ * ‖a‖ ≤ 1 := mul_le_one₀ hq1 (norm_nonneg a) ha.le
      linarith
    · linarith
  have hsC : ((s : ℝ) : ℂ) = cSL q ((‖a‖ : ℝ) : ℂ) := by
    rw [hsdef]; unfold cSL; push_cast; ring
  have hreal : HasSum (fun j => ‖shellVal q a j‖ * shellMass q j) s := by
    have e : (fun j => ((‖shellVal q a j‖ * shellMass q j : ℝ) : ℂ)) =
        fun j => shellVal q ((‖a‖ : ℝ) : ℂ) j * (shellMass q j : ℂ) := by
      funext j
      cases j with
      | zero => simp [shellVal]
      | succ j => simp [shellVal, norm_pow, norm_div]
    refine Complex.hasSum_ofReal.1 ?_
    show HasSum (fun j => ((‖shellVal q a j‖ * shellMass q j : ℝ) : ℂ)) ((s : ℝ) : ℂ)
    rw [e, hsC]
    exact hasSum_shell q hq ((‖a‖ : ℝ) : ℂ) (by simpa using ha)
  have hL : ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ := by
    rw [← setLIntegral_univ, ← hSU, lintegral_iUnion hSm hSd]
    have hterm : ∀ j, ∫⁻ x in S j, ‖F x‖ₑ ∂μ = ENNReal.ofReal (‖shellVal q a j‖ * shellMass q j) := by
      intro j
      rw [setLIntegral_congr_fun (hSm j) (fun x hx => by rw [hSF j x hx]), setLIntegral_const, hSμ,
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (norm_nonneg _) (shellMass_nonneg q hq j))
      hreal.summable, hreal.tsum_eq, ← hsC, ← ofReal_norm_eq_enorm, Complex.norm_real,
      Real.norm_of_nonneg hs0]
  have hint : Integrable F μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hL]
    exact enorm_lt_top
  refine ⟨hint, ?_, hL⟩
  have h1 := hasSum_integral_iUnion hSm hSd hint.integrableOn
  rw [hSU, Measure.restrict_univ] at h1
  refine h1.unique ?_
  have e3 : (fun n => ∫ x in S n, F x ∂μ) = fun j => shellVal q a j * (shellMass q j : ℂ) := by
    funext j
    rw [setIntegral_congr_fun (hSm j) (fun x hx => hSF j x hx), setIntegral_const, hSr, Complex.real_smul,
      mul_comm]
  rw [e3]
  exact hasSum_shell q hq a ha

end ShellSum

theorem integral_geometric_shells : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℕ), 2 ≤ q →
    ∀ (a : ℂ), ‖a‖ < 1 →
    ∀ (H : ℕ → Set X), (∀ j, MeasurableSet (H j)) → Monotone H → ⋃ j, H j = Set.univ →
    (∀ j, μ (H j) = (q : ENNReal) ^ j) → ∀ (F : X → ℂ), (∀ x ∈ H 0, F x = 1) →
    (∀ j x, x ∈ H (j + 1) → x ∉ H j → F x = (a / q) ^ (j + 1)) →
    Integrable F μ ∧ ∫ x, F x ∂μ = cSL q a ∧ ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ :=
  fun μ q hq a ha H hH hmono hU hμ F hF0 hF =>
    ShellSum.integral_geom_on_shells μ q hq a ha H hH hmono hU hμ F hF0 hF

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulRight
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RightMulJac

theorem integral_mul_right : ∀ (D : D7) (t n : ℕ) (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)),
    IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
    ∀ (a : GL (Fin n) (AE D)) (f : Mx D t n → ℂ),
      ∫ x, f (x ⬝ a.1) ∂μ₁ = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(t : ℂ)) * ∫ x, f x ∂μ₁ := by
  intro D t n μ₁ 𝓕₁ hμ a f
  haveI : μ₁.IsAddHaarMeasure := hμ.1
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  have hkey := GlobalTheory.ModuLR.modu_lrMul D t n μ₁ hμ.1 1 a
  simp only [map_one, one_pow, one_mul, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul, ENNReal.coe_one] at hkey
  set c : ℝ≥0 := absA D (Matrix.GeneralLinearGroup.det a) with hc
  have hc0 : c ≠ 0 := by
    exact ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  have hcont : Continuous fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n) := continuous_id.matrix_mul continuous_const
  have hcont' : Continuous fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) (a⁻¹).val : Mx D t n) := continuous_id.matrix_mul continuous_const
  let e : Mx D t n ≃ₜ Mx D t n :=
    { toFun := fun u => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)
      invFun := fun u => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) (a⁻¹).val : Mx D t n)
      left_inv := fun u => by simp [Matrix.mul_assoc]
      right_inv := fun u => by simp [Matrix.mul_assoc]
      continuous_toFun := hcont
      continuous_invFun := hcont' }
  have hemb : MeasurableEmbedding (fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) := e.measurableEmbedding
  have hmap : μ₁.map (fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) = ((c : ENNReal) ^ t)⁻¹ • μ₁ := by
    conv_rhs => rw [hkey]
    rw [smul_smul, ENNReal.inv_mul_cancel (by simp [hc0]) (by simp), one_smul]
  rw [show (∫ x, f (x ⬝ a.1) ∂μ₁) = ∫ x, f ((fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) x) ∂μ₁ from rfl,
    ← hemb.integral_map, hmap, integral_smul_measure]
  rw [Complex.real_smul, npow]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.coe_toReal,
    show (-(t : ℂ)) = ((-(t : ℝ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (NNReal.coe_nonneg c), Real.rpow_neg (NNReal.coe_nonneg c), Real.rpow_natCast]

end GlobalTheory.RightMulJac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrbitCentralizerAlmostAll
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.KottAlmost

section Generic

variable {K A : Type} [CommRing K] [Ring A] [Algebra K A]

def shU (σ : A →+* Aᵐᵒᵖ) (u : Aˣ) : Aˣ where
  val := (σ u).unop
  inv := (σ ((u⁻¹ : Aˣ) : A)).unop
  val_inv := by rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  inv_val := by rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem shU_inv_val (σ : A →+* Aᵐᵒᵖ) (u : Aˣ) : (((shU σ u)⁻¹ : Aˣ) : A) = (σ ((u⁻¹ : Aˣ) : A)).unop := rfl

theorem sh_mul (σ : A →+* Aᵐᵒᵖ) (a b : A) : (σ (a * b)).unop = (σ b).unop * (σ a).unop := by
  rw [map_mul, MulOpposite.unop_mul]

theorem comm_sh (σ : A →+* Aᵐᵒᵖ) (a : A) (y : Aˣ) (cy : Kˣ)
    (hy : (y : A) * (σ y).unop = algebraMap K A cy) (ha : a * y = y * a) :
    (σ a).unop * y = y * (σ a).unop := by
  have hsy : (σ y).unop = ((y⁻¹ : Aˣ) : A) * algebraMap K A cy := by
    rw [← hy, ← mul_assoc, Units.inv_mul, one_mul]
  have h := congrArg (fun z => (σ z).unop) ha
  simp only [sh_mul] at h
  rw [hsy] at h
  have h' : (((y⁻¹ : Aˣ) : A) * (σ a).unop) * algebraMap K A cy =
      ((σ a).unop * ((y⁻¹ : Aˣ) : A)) * algebraMap K A cy := by
    rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, h]; simp only [mul_assoc]
  have hk : IsUnit (algebraMap K A cy) := cy.isUnit.map (algebraMap K A)
  have h'' := hk.mul_right_cancel h'
  calc (σ a).unop * y = y * (((y⁻¹ : Aˣ) : A) * (σ a).unop) * y := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = y * ((σ a).unop * ((y⁻¹ : Aˣ) : A)) * y := by rw [h'']
    _ = y * (σ a).unop := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

end Generic

end GlobalTheory.OrbFinAf.KottAlmost

namespace GlobalTheory.OrbFinAf.KottAlmost

section Step

variable {K A : Type} [CommRing K] [Ring A] [Algebra K A]

theorem step (σ : A →+* Aᵐᵒᵖ) (hinv : ∀ a, (σ (σ a).unop).unop = a)
    (I : A → Prop) (J : K → Prop) (hJ1 : J 1)
    (h1 : ∀ a b, I a → I b → I (a * b)) (h2 : ∀ a, I a → I (σ a).unop)
    (γ : uGroup (A := K) σ)
    (h3 : ∀ g : Aˣ, I ((g⁻¹ * (γ : Aˣ × Kˣ).1 * g : Aˣ) : A) → I ((g⁻¹ * (γ : Aˣ × Kˣ).1⁻¹ * g : Aˣ) : A) →
      ∃ e : Aˣ, e * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * e ∧ I ((e⁻¹ * g : Aˣ) : A) ∧ I ((g⁻¹ * e : Aˣ) : A))
    (h4 : ∀ s : Aˣ, s * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * s → I (s : A) → I ((s⁻¹ : Aˣ) : A) →
      (σ s).unop = s → ∃ t : Aˣ, t * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * t ∧ I (t : A) ∧ I ((t⁻¹ : Aˣ) : A) ∧
        (t : A) * (σ t).unop = s)
    (g : uGroup (A := K) σ)
    (hg : I (((g⁻¹ * γ * g : uGroup (A := K) σ) : Aˣ × Kˣ).1 : A) ∧
      I (((((g⁻¹ * γ * g : uGroup (A := K) σ) : Aˣ × Kˣ).1)⁻¹ : Aˣ) : A)) :
    ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id _) γ, ∃ d : uGroup (A := K) σ,
      (I ((d : Aˣ × Kˣ).1 : A) ∧ I ((((d : Aˣ × Kˣ).1)⁻¹ : Aˣ) : A) ∧ J ((d : Aˣ × Kˣ).2 : K) ∧
        J ((((d : Aˣ × Kˣ).2)⁻¹ : Kˣ) : K)) ∧ g = c * d := by
  obtain ⟨⟨g1, cg⟩, hgm⟩ := g
  obtain ⟨⟨y, cy⟩, hym⟩ := γ
  have hgm' : (g1 : A) * (σ g1).unop = algebraMap K A cg := hgm
  have hym' : (y : A) * (σ y).unop = algebraMap K A cy := hym
  have hg1 : I ((g1⁻¹ * y * g1 : Aˣ) : A) := hg.1
  have hg2 : I ((g1⁻¹ * y⁻¹ * g1 : Aˣ) : A) := by
    have e : (g1⁻¹ * y * g1 : Aˣ)⁻¹ = g1⁻¹ * y⁻¹ * g1 := by group
    rw [← e]; exact hg.2
  obtain ⟨e, he, hu1, hu2⟩ := h3 g1 hg1 hg2
  obtain ⟨u, hu⟩ : ∃ u : Aˣ, u = e⁻¹ * g1 := ⟨_, rfl⟩
  rw [← hu] at hu1
  have hu2' : I ((u⁻¹ : Aˣ) : A) := by
    have : u⁻¹ = g1⁻¹ * e := by rw [hu]; group
    rw [this]; exact hu2
  obtain ⟨s, hs⟩ : ∃ s : Aˣ, s = u * shU σ u := ⟨_, rfl⟩
  have hsv : (s : A) = (u : A) * (σ u).unop := by rw [hs]; rfl
  have hsI : I (s : A) := by rw [hsv]; exact h1 _ _ hu1 (h2 _ hu1)
  have hsI' : I ((s⁻¹ : Aˣ) : A) := by
    rw [hs, _root_.mul_inv_rev, Units.val_mul, shU_inv_val]
    exact h1 _ _ (h2 _ hu2') hu2'
  have hss : (σ s).unop = s := by
    rw [hsv, sh_mul, hinv]
  have hsval : (s : A) = ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop := by
    rw [hsv, hu, Units.val_mul, sh_mul, ← hgm']
    simp only [mul_assoc]
  have hey : ((e⁻¹ : Aˣ) : A) * y = y * ((e⁻¹ : Aˣ) : A) := by
    have : e⁻¹ * y = y * e⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, he, mul_inv_cancel_right]
    exact congrArg Units.val this
  have hby := comm_sh σ ((e⁻¹ : Aˣ) : A) y cy hym' hey
  have hsy : s * y = y * s := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hsval]
    calc ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop * y
        = ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (y * (σ ((e⁻¹ : Aˣ) : A)).unop) := by rw [mul_assoc, hby]
      _ = ((e⁻¹ : Aˣ) : A) * (y * algebraMap K A cg) * (σ ((e⁻¹ : Aˣ) : A)).unop := by
          rw [mul_assoc ((e⁻¹ : Aˣ) : A), ← mul_assoc (algebraMap K A cg), Algebra.commutes]; simp only [mul_assoc]
      _ = (y : A) * (((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop) := by
          rw [← mul_assoc ((e⁻¹ : Aˣ) : A) (y : A), hey]; simp only [mul_assoc]
  obtain ⟨t, ht, htI, htI', hts⟩ := h4 s hsy hsI hsI' hss
  have hcm : ((e * t : Aˣ) : A) * (σ ((e * t : Aˣ) : A)).unop = algebraMap K A cg := by
    rw [Units.val_mul, sh_mul]
    calc (e : A) * t * ((σ t).unop * (σ e).unop) = e * (t * (σ t).unop) * (σ e).unop := by
          simp only [mul_assoc]
      _ = e * (((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop) * (σ e).unop := by
          rw [hts, hsval]
      _ = algebraMap K A cg * ((σ ((e⁻¹ : Aˣ) : A)).unop * (σ e).unop) := by
          simp only [← mul_assoc, Units.mul_inv, one_mul]
      _ = _ := by rw [← sh_mul, Units.mul_inv, map_one, MulOpposite.unop_one, mul_one]
  have hdm : ((t⁻¹ * u : Aˣ) : A) * (σ ((t⁻¹ * u : Aˣ) : A)).unop = algebraMap K A ((1 : Kˣ) : K) := by
    rw [Units.val_mul, sh_mul, Units.val_one, map_one]
    calc ((t⁻¹ : Aˣ) : A) * u * ((σ u).unop * (σ ((t⁻¹ : Aˣ) : A)).unop)
        = ((t⁻¹ : Aˣ) : A) * ((u : A) * (σ u).unop) * (σ ((t⁻¹ : Aˣ) : A)).unop := by simp only [mul_assoc]
      _ = ((t⁻¹ : Aˣ) : A) * ((t : A) * (σ t).unop) * (σ ((t⁻¹ : Aˣ) : A)).unop := by
          rw [hts, hsv]
      _ = 1 := by
          rw [← mul_assoc, Units.inv_mul, one_mul, ← sh_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  refine ⟨⟨(e * t, cg), hcm⟩, ?_, ⟨(t⁻¹ * u, 1), hdm⟩, ⟨h1 _ _ htI' hu1, ?_, hJ1, by rw [inv_one]; exact hJ1⟩, ?_⟩
  · apply Subtype.ext; apply Prod.ext
    · show e * t * y = y * (e * t)
      rw [mul_assoc, ht, ← mul_assoc, he, mul_assoc]
    · show cg * cy = cy * cg
      exact mul_comm _ _
  · show I (((t⁻¹ * u)⁻¹ : Aˣ) : A)
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
    exact h1 _ _ hu2' htI
  · apply Subtype.ext; apply Prod.ext
    · show g1 = e * t * (t⁻¹ * u)
      rw [hu]; group
    · show cg = cg * 1
      rw [mul_one]

end Step

end GlobalTheory.OrbFinAf.KottAlmost

namespace GlobalTheory.OrbFinAf.KottAlmost

theorem starT_starT {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    (starT G.star R (starT G.star R a).unop).unop = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => rw [starT_tmul, starT_tmul, G.star_star]
  | add a b ha hb => rw [map_add (f := _), MulOpposite.unop_add, map_add (f := _), MulOpposite.unop_add, ha, hb]

end GlobalTheory.OrbFinAf.KottAlmost
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfDimLeZero
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_isNef_of_dim_le_zero : ∀ (k : Type) [Field k] [Infinite k], (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (0 : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) := by
  intro k _ _ Y _ hp hd A N hA hN
  have : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hp
  have hAN : (tens A N).IsLB := (IsNef.tens_of_isProjOver (IsAmpleLB.isNef (k := k) hA) hN hp).isLB
  have hlt : topologicalKrullDim Y < ((1 : ℕ) : WithBot ℕ∞) :=
    lt_of_le_of_lt hd (by exact_mod_cast Nat.zero_lt_one)
  refine isAmpleLB_of_subsingleton_coh_one Y (tens A N) hAN fun F _ => ⟨1, le_rfl, ?_⟩
  have : IsFiniteQC (twist F (lbPow (tens A N) 1)) := isFiniteQC_twist (isLB_lbPow hAN 1)
  exact hA.subsingleton_coh_of_dim_lt _ hlt

end GlobalTheory
end

