module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryPolynomialSpectralGap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

theorem toMK_injective_of_gap {n : ℕ} (ε : Fin n → Bool) : Function.Injective (fun k : KG ε => toMK k) := by
  intro a b h
  exact Subtype.ext (Subtype.ext (Units.ext h))

theorem integrable_real_of_continuousK {n : ℕ} {ε : Fin n → Bool} {f : KG ε → ℝ} (hf : Continuous f) :
    Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem sq_dist_right_translate_le {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n) (hX : ∀ j, inK ε (X j))
    (C : ℝ) (hC : 0 ≤ C)
    (hcoef : ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y)
    {d : ℕ} {p : KG ε → ℂ} (hp : p ∈ polyV ε d) (k : KG ε) :
    ∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε) ≤
      3 * C * Formalism.REAL.hs (toMK k - 1) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) := by
  obtain ⟨Y, hY, hexp, hhs⟩ := compact_exponential_surjective n ε (toMK k) k.2
  have hk : expK ε Y 1 = k := by
    apply toMK_injective_of_gap ε
    show toMK (expK ε Y 1) = toMK k
    rw [toMK_expK hY, Complex.ofReal_one, one_smul, hexp]
  obtain ⟨c, rfl, hc⟩ := hcoef Y hY
  have h1 := _root_.GlobalTheory.KFourier.norm_sub_expK_sq_le ε d p hp _ hY
  rw [hk, GlobalTheory.T.compactUnitaryRightDeriv_real_linear_direction ε d p hp X c hX] at h1
  have hcont : ∀ j, Continuous (rder ε [X j] p) := fun j =>
    continuous_of_mem (rder_mem_and_hasDerivAt ε d p hp (X j) (hX j)).1
  have hpt : ∀ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ≤
      (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := by
    intro x
    rw [Finset.sum_apply]
    calc ‖∑ j, ((c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ≤ (∑ j, |c j| * ‖rder ε [X j] p x‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          simp [Complex.norm_real]
      _ ≤ (∑ j, |c j| ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := by simp [sq_abs]
  have hint : ∀ j, Integrable (fun x => ‖rder ε [X j] p x‖ ^ 2) (muK ε) := fun j =>
    integrable_real_of_continuousK ((hcont j).norm.pow 2)
  have h2 : ∫ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ∂(muK ε) ≤
      (∑ j, c j ^ 2) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) := by
    rw [← integral_finsetSum _ fun j _ => hint j, ← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      ((integrable_finsetSum _ fun j _ => hint j).const_mul _) (Filter.Eventually.of_forall hpt)
  have hE : 0 ≤ ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ C * Formalism.REAL.hs (∑ j, (c j : ℂ) • X j) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) :=
        mul_le_mul_of_nonneg_right hc hE
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hhs hC
        nlinarith

theorem spectral_gap_rder : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) →
    (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
    ∀ i : ℕ, 1 ≤ i → ∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) →
    c * (i : ℝ) ^ α * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) := by
  intro n ε r X hX hspan
  obtain ⟨C3, hC3, hcoef⟩ := _root_.GlobalTheory.KGap.spanning_coef_bound ε X hspan
  obtain ⟨C4, hC4, hker⟩ := _root_.GlobalTheory.KFourier.kernel_near_one ε
  set A : ℝ := 3 * C3 * C4 ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 / (A + 1), 1 / 2, by positivity, by norm_num, ?_⟩
  intro i hi p hp horth
  set E := ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) with hEdef
  have hE : 0 ≤ E := Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  obtain ⟨κ, hκc, hκ0, hκ1, hκmem, hκb⟩ := hker m
  have hpc : Continuous p := continuous_of_mem hp
  have horth' := GlobalTheory.T.orthogonal_lowerDegree_kernel_translates ε (m + 1) p (fun k => (κ k : ℂ)) hκmem horth
  have h1 := GlobalTheory.T.sqrt_integral_norm_sq_le_integral_kernel_mul_translate ε p κ hpc hκc hκ0 hκ1 horth'
  set P := ∫ x, ‖p x‖ ^ 2 ∂(muK ε) with hPdef
  have hP : 0 ≤ P := integral_nonneg fun x => by positivity
  have hint : Integrable (fun k => κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1))) (muK ε) := by
    refine integrable_real_of_continuousK ?_
    refine (hκc.mul continuous_const).mul (Real.continuous_sqrt.comp ?_)
    unfold Formalism.REAL.hs
    fun_prop
  have h2 : ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) ≤
      ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun k => mul_nonneg (hκ0 k) (Real.sqrt_nonneg _))
      hint (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hκ0 k)
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have := sq_dist_right_translate_le ε X hX C3 hC3 hcoef hp k
    nlinarith [show 0 ≤ Formalism.REAL.hs (toMK k - 1) from by unfold Formalism.REAL.hs; positivity]
  have h3 : ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) =
      Real.sqrt (3 * C3 * E) * ∫ k, κ k * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) := by
    rw [← integral_const_mul]; congr 1; funext k; ring
  have hmi : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hmi] at hκb
  set I : ℝ := ((m + 1 : ℕ) : ℝ) with hIdef
  have hI : 1 ≤ I := by rw [hIdef]; exact_mod_cast Nat.succ_pos m
  have hsq : Real.sqrt P ≤ Real.sqrt (3 * C3 * E) * (C4 * I ^ (-(1 / 4 : ℝ))) := by
    calc Real.sqrt P ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left hκb (Real.sqrt_nonneg _)
  have hq : 0 ≤ I ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hPle : P ≤ 3 * C3 * E * C4 ^ 2 * (I ^ (-(1 / 4 : ℝ))) ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg P) hsq 2
    rw [Real.sq_sqrt hP, mul_pow, Real.sq_sqrt (by positivity), mul_pow] at h
    linarith
  have hpow : (I ^ (-(1 / 4 : ℝ))) ^ 2 * I ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
    norm_num
  have hIp : 0 ≤ I ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have key : I ^ (1 / 2 : ℝ) * P ≤ A * E := by
    calc I ^ (1 / 2 : ℝ) * P ≤ I ^ (1 / 2 : ℝ) * (3 * C3 * E * C4 ^ 2 * (I ^ (-(1 / 4 : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hPle hIp
      _ = A * E * ((I ^ (-(1 / 4 : ℝ))) ^ 2 * I ^ (1 / 2 : ℝ)) := by rw [hA]; ring
      _ = A * E := by rw [hpow, mul_one]
  have hA1 : 0 < A + 1 := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ hA1]
  nlinarith

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFormFamilyHypothesesChangedSecondNormStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formFamilyHypotheses_changedSecondNorm : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (n : SecNorm B) (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd c : ℝ), FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S Tn G Gc PH Prw Pet Pd → PtIn S Tn G c Gc PH Prw Pet nus → ∃ G' : GlobalFamilyData (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka wL wF, FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' Gc PH Prw Pet Pd ∧ PtIn (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' c Gc PH Prw Pet nus := by
  first | exact @GlobalTheory.NormMove.exists_famIn_ptIn | exact GlobalTheory.NormMove.exists_famIn_ptIn | (intros; apply GlobalTheory.NormMove.exists_famIn_ptIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSmallIffOpo
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

namespace GlobalTheory.FinalJoin2

theorem FO_eq_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D = Q.c.F := by
  apply le_antisymm
  · rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    have e := h (Q.eO.symm y)
    rw [RingEquiv.apply_symm_apply] at e
    have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
    rw [e']
    exact SetLike.coe_mem _
  · intro z hz
    haveI := Q.c.fin
    haveI : NumberField Q.c.F := NumberField.mk
    have hint : ∀ x : 𝓞 Q.c.F, ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) ∈ FO D := fun x => by
      have e : D.what₂.phiO (Q.eO x) = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) := h x
      rw [← e]
      exact phiO_mem_FO D _
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨z, hz⟩ : Q.c.F)
    have : z = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) / ((algebraMap (𝓞 Q.c.F) Q.c.F y : Q.c.F) : ℂ) := by
      have := congrArg (fun t : Q.c.F => (t : ℂ)) hxy
      simpa using this.symm
    rw [this]
    exact div_mem (hint x) (hint y)

theorem fieldSmall_iff_opo : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D),
    FieldSmall D large₂ ↔ OPO large₂ (recB h.toLawsCore) := by
  intro D T h large₂
  have hF : FO D = T.Q.c.F := FO_eq_coeff T.Q h.toLawsCore.pins.2.2.1
  letI : NumberField (FO D) := NumberField.mk
  let e : FO D ≃+* (recB h.toLawsCore).KO := (IntermediateField.equivOfEq hF).toRingEquiv
  have h1 : Module.finrank ℚ (FO D) = Module.finrank ℚ (recB h.toLawsCore).KO :=
    (LinearEquiv.ofBijective e.toRingHom.toRatAlgHom.toLinearMap e.bijective).finrank_eq
  have h2 : NumberField.discr (FO D) = NumberField.discr (recB h.toLawsCore).KO :=
    NumberField.discr_eq_discr_of_ringEquiv _ e
  unfold FieldSmall OPO
  rw [← h1, ← h2]

end GlobalTheory.FinalJoin2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSumCompactUnitaryFourierValueOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KFourier
open MeasureTheory
variable {n : ℕ}

theorem orth_decomp_L (ε : Fin n → Bool) (d : ℕ) (p : KG ε → ℂ) (hp : Continuous p) :
    ∃ p' ∈ polyV ε d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * (p k - p' k) ∂(muK ε) = 0 :=
  GlobalTheory.T.exists_orthogonal_projection_polynomial_compact_unitary ε d p hp

theorem conv_swap_L (ε : Fin n → Bool) (e q g : KG ε → ℂ) (he : Continuous e) (hq : Continuous q)
    (hg : Continuous g) :
    ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) =
      ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) :=
  GlobalTheory.T.integral_star_mul_convolution_eq_integral_swap ε e q g he hq hg

theorem eq_zero_of_orth_L (ε : Fin n → Bool) (h : KG ε → ℂ) (hh : Continuous h)
    (ho : ∀ d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) : h = 0 :=
  _root_.GlobalTheory.KFourier.eq_zero_of_orth_poly ε h hh ho

theorem integrable_of_cont (ε : Fin n → Bool) {f : KG ε → ℂ} (hf : Continuous f) : Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem firstCountable_KG (ε : Fin n → Bool) : FirstCountableTopology (KG ε) :=
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  ((isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).isInducing.firstCountableTopology

theorem continuous_param (ε : Fin n → Bool) {F : KG ε → KG ε → ℂ} (hF : Continuous (Function.uncurry F)) :
    Continuous fun a => ∫ k, F a k ∂(muK ε) := by
  haveI := firstCountable_KG ε
  have := continuous_parametric_integral_of_continuous (μ := muK ε) hF (s := Set.univ) isCompact_univ
  simpa [Measure.restrict_univ] using this

theorem sum_ker_poly (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i)) :
    ∀ d, ∀ p ∈ polyV ε d, ∑ i ∈ Finset.range (d + 1), ∫ k, e i k * p k ∂(muK ε) = p 1 := by
  intro d
  induction d with
  | zero =>
    intro p hp
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    exact (he 0).2.2 p hp (fun q hq => by simp [lowV] at hq; simp [hq])
  | succ d ih =>
    intro p hp
    obtain ⟨p', hp', horth⟩ := orth_decomp_L ε d p (continuous_of_mem hp)
    have hp'' : (fun k => p k - p' k) ∈ polyV ε (d + 1) :=
      sub_mem hp (polyV_mono ε (Nat.le_succ d) hp')
    have hcp : Continuous p := continuous_of_mem hp
    have hcp' : Continuous p' := continuous_of_mem hp'
    have hce : ∀ i, Continuous (e i) := fun i => continuous_of_mem (he i).1
    have hsplit : ∀ i, ∫ k, e i k * p k ∂(muK ε) =
        ∫ k, e i k * p' k ∂(muK ε) + ∫ k, e i k * (p k - p' k) ∂(muK ε) := by
      intro i
      rw [← integral_add (integrable_of_cont ε (f := fun k => e i k * p' k) ((hce i).mul hcp'))
        (integrable_of_cont ε (f := fun k => e i k * (p k - p' k)) ((hce i).mul (hcp.sub hcp')))]
      congr 1; funext k; ring
    rw [Finset.sum_range_succ, hsplit (d + 1), Finset.sum_congr rfl (fun i _ => hsplit i),
      Finset.sum_add_distrib, ih p' hp']
    have h0 : ∫ k, e (d + 1) k * p' k ∂(muK ε) = 0 := (he (d + 1)).2.1 p' hp'
    have h1 : ∫ k, e (d + 1) k * (p k - p' k) ∂(muK ε) = p 1 - p' 1 :=
      (he (d + 1)).2.2 _ hp'' (fun q hq => horth q hq)
    have h2 : ∀ i ∈ Finset.range (d + 1), ∫ k, e i k * (p k - p' k) ∂(muK ε) = 0 := by
      intro i hi
      have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hs : (fun k => star (e i k)) ∈ polyV ε d := polyV_mono ε hi' (star_mem (he i).1)
      have := horth _ hs
      simpa using this
    rw [Finset.sum_eq_zero h2, h0, h1]
    ring

theorem ker_vanish (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i)) {d i : ℕ} (hi : d < i)
    {p : KG ε → ℂ} (hp : p ∈ polyV ε d) : ∫ k, e i k * p k ∂(muK ε) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact (he (j + 1)).2.1 p (polyV_mono ε (by omega) hp)

theorem hasSum_kFourier (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i))
    (g : KG ε → ℂ) (hg : Continuous g) (b : ℕ → ℝ) (hb : Summable b)
    (hbd : ∀ i (k' : KG ε), ‖∫ k, e i k * g (k' * k) ∂(muK ε)‖ ≤ b i) :
    HasSum (fun i => ∫ k, e i k * g k ∂(muK ε)) (g 1) := by
  have hce : ∀ i, Continuous (e i) := fun i => continuous_of_mem (he i).1
  set P : ℕ → KG ε → ℂ := fun i k' => ∫ k, e i k * g (k' * k) ∂(muK ε) with hPdef
  have hPc : ∀ i, Continuous (P i) := fun i =>
    continuous_param ε (F := fun k' k => e i k * g (k' * k))
      (((hce i).comp continuous_snd).mul (hg.comp (continuous_fst.mul continuous_snd)))
  have hsum : ∀ k', Summable (fun i => P i k') := fun k' => Summable.of_norm_bounded hb (fun i => hbd i k')
  set u : KG ε → ℂ := fun k' => ∑' i, P i k' with hudef
  have hu : Continuous u := continuous_tsum hPc hb hbd
  have key : ∀ d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * (u k - g k) ∂(muK ε) = 0 := by
    intro d q hq
    have hcq : Continuous q := continuous_of_mem hq
    obtain ⟨M, hM⟩ : ∃ M, ∀ k, ‖star (q k)‖ ≤ M := by
      obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_star.comp hcq)).isBounded.exists_norm_le
      exact ⟨M, fun k => hM _ ⟨k, Set.mem_univ _, rfl⟩⟩
    have hint : ∀ i, Integrable (fun k => star (q k) * P i k) (muK ε) := fun i =>
      integrable_of_cont ε ((continuous_star.comp hcq).mul (hPc i))
    have hnorm : ∀ i, ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) ≤ M * b i := by
      intro i
      calc ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) ≤ ∫ _k, M * b i ∂(muK ε) := by
            refine integral_mono (hint i).norm (integrable_const _) (fun k => ?_)
            rw [norm_mul]
            exact mul_le_mul (hM k) (hbd i k) (norm_nonneg _) ((norm_nonneg _).trans (hM k))
        _ = M * b i := by simp
    have hsn : Summable fun i => ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) :=
      Summable.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg _) hnorm (hb.mul_left M)
    have e1 : ∫ k, star (q k) * u k ∂(muK ε) = ∑' i, ∫ k, star (q k) * P i k ∂(muK ε) := by
      rw [integral_tsum_of_summable_integral_norm hint hsn]
      congr 1; funext k
      rw [hudef]; simp only
      exact (tsum_mul_left).symm
    set r : ℕ → KG ε → ℂ := fun i y => ∫ x, e i x * star (q (y * x⁻¹)) ∂(muK ε) with hrdef
    have hpy : ∀ y, (fun x => star (q (y * x⁻¹))) ∈ polyV ε d := fun y =>
      star_mem (inv_mem (φ := fun k => q (y * k)) (mul_left_mem y hq))
    have hrc : ∀ i, Continuous (r i) := fun i =>
      continuous_param ε (F := fun y x => e i x * star (q (y * x⁻¹)))
        (((hce i).comp continuous_snd).mul (continuous_star.comp (hcq.comp (continuous_fst.mul continuous_snd.inv))))
    have e2 : ∀ i, ∫ k, star (q k) * P i k ∂(muK ε) = ∫ y, g y * r i y ∂(muK ε) := fun i =>
      conv_swap_L ε (e i) q g (hce i) hcq hg
    have hr0 : ∀ i ∉ Finset.range (d + 1), ∫ y, g y * r i y ∂(muK ε) = 0 := by
      intro i hi
      have hi' : d < i := by simpa using hi
      have : ∀ y, r i y = 0 := fun y => ker_vanish ε e he hi' (hpy y)
      simp [this]
    have hrs : ∀ y, ∑ i ∈ Finset.range (d + 1), r i y = star (q y) := by
      intro y
      have := sum_ker_poly ε e he d _ (hpy y)
      simp only [hrdef]
      simpa using this
    have e3 : ∫ k, star (q k) * u k ∂(muK ε) = ∫ k, star (q k) * g k ∂(muK ε) := by
      rw [e1, tsum_congr e2, tsum_eq_sum hr0, ← integral_finsetSum]
      · congr 1; funext y
        rw [← Finset.mul_sum, hrs y, mul_comm]
      · intro i _
        exact integrable_of_cont ε (hg.mul (hrc i))
    have hsub : (fun k => star (q k) * (u k - g k)) = fun k => star (q k) * u k - star (q k) * g k := by
      funext k; ring
    rw [hsub, integral_sub (integrable_of_cont ε (f := fun k => star (q k) * u k) ((continuous_star.comp hcq).mul hu))
      (integrable_of_cont ε (f := fun k => star (q k) * g k) ((continuous_star.comp hcq).mul hg)), e3, sub_self]
  have hzero := eq_zero_of_orth_L ε (fun k => u k - g k) (hu.sub hg) key
  have h1 : u 1 = g 1 := sub_eq_zero.1 (congrFun hzero 1)
  have h2 : u 1 = ∑' i, ∫ k, e i k * g k ∂(muK ε) := by simp [hudef, hPdef]
  rw [← h1, h2]
  have := (hsum 1).hasSum
  simpa [hPdef] using this

end GlobalTheory.KFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.Hilbert90FiniteIdelesCongruence
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleNinety

theorem fixed_baseChange {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (c : E →ₐ[F] E) (hcc : ∀ x, c (c x) = x)
    (hfix : ∀ x, c x = x → ∃ t : F, x = algebraMap F E t) (y : R ⊗[F] E)
    (hy : Algebra.TensorProduct.map (AlgHom.id F R) c y = y) : ∃ a : R, y = a ⊗ₜ 1 := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + Algebra.TensorProduct.map (AlgHom.id F R) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := hfix (x + c x) (by rw [map_add (f := _), hcc, add_comm])
      refine ⟨t • a, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← TensorProduct.tmul_add, ht,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add (f := _), TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT y
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [← TensorProduct.smul_tmul', ← ht, hy, ← two_smul F y, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem conj_ne_one (D : D7) : cF D ≠ 1 := by
  intro h
  obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  obtain ⟨t, s, hs, hts⟩ := D.sp.cm.cmUnram.2.2 P hM
  have hs' : (s : D.host.E) = cF D (t : D.host.E) := hs
  rw [h] at hs'
  have : s = t := Subtype.ext hs'
  rw [this, sub_self] at hts
  exact hts P.zero_mem

theorem fixed_conj (D : D7) (x : D.host.E) (hx : cF D x = x) : ∃ t : D.host.F, x = algebraMap D.host.F D.host.E t := by
  have : Algebra.IsQuadraticExtension D.host.F D.host.E := { finrank_eq_two' := D.sp.cm.deg2 }
  have hcard : Nat.card (D.host.E ≃ₐ[D.host.F] D.host.E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, D.sp.cm.deg2]
  obtain ⟨g, -, hg⟩ := (Nat.card_eq_two_iff' (1 : D.host.E ≃ₐ[D.host.F] D.host.E)).1 hcard
  obtain ⟨t, ht⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := D.host.F) x).2 fun f => by
    by_cases hf : f = 1
    · rw [hf]; rfl
    · rw [hg f hf, ← hg _ (conj_ne_one D), hx]
  exact ⟨t, ht.symm⟩

theorem coe_cjFin (D : D7) (y : (AfE D)ˣ) : ((cjFin D y : (AfE D)ˣ) : AfE D) = barF D (y : AfE D) := by
  have h : D.conjF = (cF D : D.host.E →ₐ[D.host.F] D.host.E) :=
    AlgHom.ext fun x => (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  unfold cjFin barF
  rw [h]
  rfl

theorem finiteIdeles_normOne_eq_div_conj_with_congruence : ∀ (D : D7), (∀ x : (AfE D)ˣ, NormOne x → ∃ y, x = y / cjFin D y) ∧ (∀ y : (AfE D)ˣ, cjFin D y = y → ∃ a : Af D.host.F, (y : AfE D) = a ⊗ₜ 1) ∧ ∀ (p N : ℕ) (x : (AfE D)ˣ), p.Prime → p ≠ 2 → p ∣ N → 0 < N → NormOne x → CongOne N x → ∃ y, IntUnit y ∧ CongOne p y ∧ x = y / cjFin D y := by
  intro D
  have hcc : ∀ x, cF D (cF D x) = x := fun x => star_star x
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun p N x hp h2 hpN _ hx hc => ?_⟩
  · obtain ⟨y, hy⟩ := GlobalTheory.UCls.NormOne.finiteAdele_quadratic_exists_unit_eq_mul_sg (cF D) hcc (fixed_conj D) (conj_ne_one D) (x : AfE D) hx
    refine ⟨y, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hy.symm)
  · exact fixed_baseChange (Af D.host.F) (cF D : D.host.E →ₐ[D.host.F] D.host.E) hcc (fixed_conj D) _
      ((coe_cjFin D y).symm.trans (congrArg Units.val hy))
  · obtain ⟨w, hw, hwe⟩ := hc
    obtain ⟨k, rfl⟩ := hpN
    obtain ⟨y, y', hy, hy', hyy, hroot, hq⟩ := GlobalTheory.OddRoot.exists_root_odd D p (hp.odd_of_ne_two h2) (x : AfE D)
      (k • w) (nsmul_mem hw k) (by rw [hwe, mul_smul]) hx
    refine ⟨Units.mkOfMulEqOne y y' hyy, ⟨hy, hy'⟩, hq, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hroot.symm)

end GlobalTheory.IdeleNinety
end

