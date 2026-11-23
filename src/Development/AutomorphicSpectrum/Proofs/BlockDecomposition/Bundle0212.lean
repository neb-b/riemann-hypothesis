module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatQCech
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLattice
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.GenericFibre

theorem isMultiHomogIdeal_map_rat {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℚ))) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · exact Ideal.map_span _ _

theorem finiteDimensional_chartLatQ :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℤ),
      IsArithVar (mCoordIdeal y) (D + 1) → FiniteDimensional ℚ (chartLatQ y b 1) := by
  intro K _ ι _ Ω _ _ y D b hV
  classical
  letI : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  letI : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain ⟨e⟩ := ChartLatQCech.proof K ι Ω y (D + 1) b hV
  have hQ := isMultiHomogIdeal_map_rat hV.2.1.2.1
  have hG := QuotPartGraded.proof ℚ K ι _ hQ
  have hS := PositivityTheory.HtPt.Ktw.a11 ℚ K ι _
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.quotPart ℚ (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) (mCoordIdeal y)))
    inferInstance inferInstance hG
  haveI := hS.1 b 0
  exact Module.Finite.equiv e.symm

end GlobalTheory.CompanionTheory.GenericFibre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCharacterArtinCompatStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_character_artin_compat : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω) (χ : HChar E) (n : (E →+* ℂ) → ℤ)
    (μ : G E Ω →* (Qbar l)ˣ), IsLAdicOf art ι χ n μ → ∀ (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (σ : G E Ω), art (localIdele E w x) = toAb E Ω σ →
    ((μ σ : (Qbar l)ˣ) : Qbar l) = ι.symm (((χ.1 (localIdele E w x) : ℂˣ) : ℂ)) * locPow ι n w (x : w.adicCompletion E) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele | exact GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele | (intros; apply GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisOpenSubgroupLocalUnitsStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_open_subgroup_local_units : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (U : Subgroup (w.adicCompletion E)ˣ), IsOpen (U : Set (w.adicCompletion E)ˣ) → (∀ x ∈ U, IsUnitAt w x) →
    ∃ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) ∧
      ∀ σ ∈ V, σ ∈ Ine (F := E) A → ∃ x ∈ U, art (localIdele E w x) = toAb E Ω σ := by
  first | exact @GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units | exact GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units | (intros; apply GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionFormula
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inner_cls_eq {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {a b : Mat n → V} (ha : MemLp (fun y : G n => a y.val) 2 μ)
    (hb : MemLp (fun y : G n => b y.val) 2 μ) :
    ⟪cls μ a, cls μ b⟫_ℂ = ∫ y : G n, ⟪a y.val, b y.val⟫_ℂ ∂μ := by
  have e1 : cls μ a = ha.toLp _ := dif_pos ha
  have e2 : cls μ b = hb.toLp _ := dif_pos hb
  rw [e1, e2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {a b : G n → V} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun y => ⟪a y, b y⟫_ℂ) μ := by
  have h := L2.integrable_inner (𝕜 := ℂ) (ha.toLp _) (hb.toLp _)
  refine h.congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem integrable_adjoint_apply {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    {A : G n → (V →L[ℂ] V)} {φ : G n → V} (hA : ∀ v, MemLp (fun y => A y v) 2 μ) (hφ : MemLp φ 2 μ) :
    Integrable (fun y => ContinuousLinearMap.adjoint (A y) (φ y)) μ := by
  classical
  let b := stdOrthonormalBasis ℂ V
  have key : (fun y => ContinuousLinearMap.adjoint (A y) (φ y)) =
      fun y => ∑ i, ⟪A y (b i), φ y⟫_ℂ • b i := by
    funext y
    rw [← b.sum_repr' (ContinuousLinearMap.adjoint (A y) (φ y))]
    simp only [ContinuousLinearMap.adjoint_inner_right]
  rw [key]
  exact integrable_finsetSum _ fun i _ => (integrable_inner_of_memLp μ (hA (b i)) hφ).smul_const _

theorem actFormula (hLt : LtSob) (hComm : LtComm) : ActFormula := by
  intro n _ _ μ _ E _ Ω T F c hStd h A hRow f hf hCpt f' hSob' hSec' hcls x hx
  have hStd0 := hStd
  obtain ⟨hLg, hUni, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, -⟩ := hStd0
  obtain ⟨-, -, -, -, -, -, hCptSob, -⟩ := hCS
  have hdet : x.det ≠ 0 := hx
  let x₀ : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet
  have hx₀ : x₀.val = x := rfl
  have hfS : Sob μ f := (hCptSob n μ E.V hLg hRC f hf.1 hCpt).1
  have hmul : ∀ g ∈ GLs n, x * g ∈ GLs n := fun g hg => by
    have hg' : g.det ≠ 0 := hg
    show (x * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdet hg'
  have hφS : Sob μ (lTr x₀ f) := (hLt n μ E.V hLg hUni hRC x₀ f hfS).1
  have hψS : Sob μ (lTr x₀ f') := (hLt n μ E.V hLg hUni hRC x₀ f' hSob').1
  have hφE : IsSec E (lTr x₀ f) := fun g hg k => by
    show f (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f (x₀.val * g))
    rw [hx₀, ← mul_assoc]
    exact hf.2 _ (hmul g hg) k
  have hψE : IsSec E (lTr x₀ f') := fun g hg k => by
    show f' (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f' (x₀.val * g))
    rw [hx₀, ← mul_assoc]
    exact hSec' _ (hmul g hg) k
  have hclsT : cls μ (lTr x₀ f') = F.Φ h (cls μ (lTr x₀ f)) :=
    hComm n μ E Ω T F c hStd h x₀ f f' hfS hSob' hcls
  have hφL : MemLp (fun y : G n => lTr x₀ f y.val) 2 μ := hφS.2 []
  have hAL : ∀ v, MemLp (fun y : G n => A y.val v) 2 μ := fun v => (hRow v).1.2 []
  have hint : Integrable
      (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (lTr x₀ f y.val)) μ :=
    integrable_adjoint_apply μ (A := fun y : G n => A y.val) hAL hφL
  refine ext_inner_left ℂ fun v => ?_
  have hrow := (hRow v).2.2 (lTr x₀ f) (lTr x₀ f') hφS hφE hψS hψE hclsT
  rw [inner_cls_eq μ (hAL v) hφL] at hrow
  have hval : lTr x₀ f' 1 = f' x := by
    show f' (x₀.val * 1) = f' x
    rw [hx₀, mul_one]
  rw [hval] at hrow
  rw [← hrow]
  show ⟪v, ∫ y : G n, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val)) ∂μ⟫_ℂ = _
  have hint' : Integrable (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))) μ := hint
  rw [← integral_inner hint' v]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show ⟪v, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))⟫_ℂ = ⟪A y.val v, f (x₀.val * y.val)⟫_ℂ
  rw [hx₀, ContinuousLinearMap.adjoint_inner_right]

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointSmooth
section
noncomputable section

open scoped ContDiff InnerProductSpace

namespace GlobalTheory.CompanionTheory.KerFc

def innerSmulRightR {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e : V) :
    V →L[ℝ] (V →L[ℂ] V) :=
  LinearMap.mkContinuous
    { toFun := fun x => (innerSL ℂ x).smulRight e
      map_add' := fun x y => by
        ext w
        simp [inner_add_left, add_smul]
      map_smul' := fun r x => by
        ext w
        change ⟪r • x, w⟫_ℂ • e = r • (⟪x, w⟫_ℂ • e)
        rw [← Complex.coe_smul r x, inner_smul_left, Complex.conj_ofReal, mul_smul, Complex.coe_smul] }
    ‖e‖
    (fun x => by
      refine (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_)
      have h1 : ‖⟪x, w⟫_ℂ‖ ≤ ‖x‖ * ‖w‖ := norm_inner_le_norm x w
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul]
      calc ‖⟪x, w⟫_ℂ‖ * ‖e‖ ≤ (‖x‖ * ‖w‖) * ‖e‖ := by gcongr
        _ = ‖e‖ * ‖x‖ * ‖w‖ := by ring)

theorem innerSmulRightR_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e x : V) :
    innerSmulRightR e x = (innerSL ℂ x).smulRight e := rfl

theorem adjoint_eq_sum {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (B : V →L[ℂ] V) :
    ContinuousLinearMap.adjoint B =
      ∑ i, innerSmulRightR (stdOrthonormalBasis ℂ V i) (B (stdOrthonormalBasis ℂ V i)) := by
  ext w
  rw [ContinuousLinearMap.sum_apply]
  simp only [innerSmulRightR_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [← (stdOrthonormalBasis ℂ V).sum_repr' (ContinuousLinearMap.adjoint B w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem adjSmooth : AdjSmooth := by
  intro W V _ _ _ _ _ _ A s hA
  have hEq : (fun y => ContinuousLinearMap.adjoint (A y)) = fun y =>
      ∑ i, innerSmulRightR (stdOrthonormalBasis ℂ V i) (A y (stdOrthonormalBasis ℂ V i)) := by
    funext y
    exact adjoint_eq_sum (A y)
  rw [hEq]
  refine ContDiffOn.sum fun i _ => ?_
  exact (innerSmulRightR (stdOrthonormalBasis ℂ V i)).contDiff.comp_contDiffOn (hA _)

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelLocalization
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff ZeroAtInfty InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveLoc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  have hx' : x.det ≠ 0 := hx
  have hy' : y.det ≠ 0 := hy
  show (x * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx' hy'

theorem inv_mem {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n :=
  (Matrix.isUnit_nonsing_inv_det x (isUnit_iff_ne_zero.mpr hx)).ne_zero

theorem val_mem (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero

def step (r s : ℝ) : ℝ := Real.smoothTransition (r + 1 - s)

theorem step_contDiff (r : ℝ) : ContDiff ℝ ∞ (step r) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem step_eq_one {r s : ℝ} (h : s ≤ r) : step r s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem step_eq_zero {r s : ℝ} (h : r + 1 ≤ s) : step r s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

def cutAt (r : ℝ) (x y : Mat n) : ℝ := step r (lg (x⁻¹ * y))

theorem cutAt_smooth (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (cutAt r x) (GLs n) := by
  have hm : ContDiff ℝ ∞ (fun y : Mat n => x⁻¹ * y) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x⁻¹)).contDiff
  have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) :=
    (hL n).2.2.2.1.comp hm.contDiffOn fun _ hy => mul_mem (inv_mem hx) hy
  exact (step_contDiff r).comp_contDiffOn h1

theorem cutAt_mul_unitary (hL : LgFacts) (r : ℝ) {x g : Mat n} (hx : x ∈ GLs n) (hg : g ∈ GLs n)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : cutAt r x (g * k.1) = cutAt r x g := by
  have h := (hL n).2.2.1 (x⁻¹ * g) (mul_mem (inv_mem hx) hg) 1 k
  have e : ((1 : Matrix.unitaryGroup (Fin n) ℂ)).1 * (x⁻¹ * g) * k.1 = x⁻¹ * (g * k.1) := by
    rw [show ((1 : Matrix.unitaryGroup (Fin n) ℂ)).1 = 1 from rfl, one_mul, mul_assoc]
  rw [e] at h
  simp only [cutAt, h]

def cutSec {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (r : ℝ) (x : Mat n) (f : Mat n → V) : Mat n → V :=
  fun y => ((cutAt r x y : ℝ) : ℂ) • f y

theorem cutSec_mem (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) {E : KMod n} {f : Mat n → E.V}
    (hf : f ∈ CE E) : cutSec r x f ∈ CE E := by
  refine ⟨?_, fun g hg k => ?_⟩
  · have hc : ContDiffOn ℝ ∞ (fun y => ((cutAt r x y : ℝ) : ℂ)) (GLs n) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (cutAt_smooth hL r hx)
    exact hc.smul hf.1
  · simp only [cutSec, cutAt_mul_unitary hL r hx hg k, hf.2 g hg k, map_smul]

theorem cutSec_cpt (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (f : Mat n → V) : Cpt (cutSec r x f) := by
  refine ⟨lg x + (r + 1), fun y hy h => ?_⟩
  have e : x * (x⁻¹ * y) = y := Matrix.mul_nonsing_inv_cancel_left x y (isUnit_iff_ne_zero.mpr hx)
  have hs := (hL n).1 x hx (x⁻¹ * y) (mul_mem (inv_mem hx) hy)
  rw [e] at hs
  have h0 : cutAt r x y = 0 := step_eq_zero (by linarith)
  simp [cutSec, h0]

theorem cutSec_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ} {x y : Mat n} (hx : x ∈ GLs n)
    (f : Mat n → V) (h : lg y ≤ r) : cutSec r x f (x * y) = f (x * y) := by
  have e : x⁻¹ * (x * y) = y := Matrix.nonsing_inv_mul_cancel_left x y (isUnit_iff_ne_zero.mpr hx)
  have h1 : cutAt r x (x * y) = 1 := by
    rw [cutAt, e]
    exact step_eq_one h
  simp [cutSec, h1]

theorem wave_sub {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E fun t y => u t y - v t y := by
  have h := GlobalTheory.CompanionTheory.WaveK.Lin.wave_add hu (GlobalTheory.CompanionTheory.WaveK.Lin.wave_smul (-1 : ℂ) hv)
  simpa [sub_eq_add_neg] using h

theorem kerLoc : KerLoc := by
  intro n _ _ μ _ E g T k hg hL _ _ hS hW hk hsupp heq hker
  refine ⟨hk, hsupp, heq, fun u hu x hx => ?_⟩
  obtain ⟨R, hR⟩ := hsupp
  obtain ⟨c, hc⟩ := hS n
  obtain ⟨r, hRr, hcr⟩ : ∃ r : ℝ, R ≤ r ∧ |c| * (1 + |T|) ≤ r :=
    ⟨max R (|c| * (1 + |T|)), le_max_left _ _, le_max_right _ _⟩
  have hf := cutSec_mem hL r hx (hu.2.1 0)
  have hcpt := cutSec_cpt hL r hx (u 0)
  obtain ⟨v, hv, hv0⟩ := hW n E _ hf hcpt
  have huv : ∀ t, |t| ≤ T → u t x = v t x := by
    intro t ht
    refine sub_eq_zero.mp (hc E _ (wave_sub hu hv) t x hx fun y hy hly => ?_)
    have hb : c * (1 + |t|) ≤ |c| * (1 + |T|) := by
      have h1 : |t| ≤ |T| := ht.trans (le_abs_self T)
      have h2 : (0 : ℝ) ≤ 1 + |t| := by positivity
      calc c * (1 + |t|) ≤ |c| * (1 + |t|) := mul_le_mul_of_nonneg_right (le_abs_self c) h2
        _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
    show u 0 (x * y) - v 0 (x * y) = 0
    rw [hv0 _ (mul_mem hx hy), cutSec_eq hx _ (hly.trans (hb.trans hcr)), sub_self]
  have h1 : act μ E k (u 0) x = act μ E k (cutSec r x (u 0)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show k y.val (u 0 (x * y.val)) = k y.val (cutSec r x (u 0) (x * y.val))
    by_cases h : R < lg y.val
    · simp [hR _ (val_mem y) h]
    · rw [cutSec_eq hx _ ((not_lt.mp h).trans hRr)]
  rw [h1, hker _ hf hcpt v hv hv0 x hx]
  show _ = ∫ t, (g t : ℂ) • u t x
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (g t : ℂ) • v t x = (g t : ℂ) • u t x
  by_cases h : T < |t|
  · simp [hg.2.2 t h]
  · rw [huv t (not_lt.mp h)]

end GlobalTheory.CompanionTheory.WaveLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExists
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rowExists_of_factor (hFac : FactorRapid) (hEv : EvAdj) : RowExists := by
  intro n _ _ μ _ E _ Ω T F c hS h hh v
  have hS' := hS
  obtain ⟨hLg, hUn, hRC, hSG, hAE, -, -, hCS, hSO, -, -, -, -, -, hOm, -⟩ := hS'
  obtain ⟨h₁, h₂, r₁, r₂, r₂s, rfl⟩ := hFac h hh
  obtain ⟨κ, hκ, hrow⟩ := hEv n μ E Ω T F c hS h₁ r₁ v
  obtain ⟨C₁, hC₁⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (star h₂) r₂s
  obtain ⟨C₂, hC₂⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm h₂ r₂
  obtain ⟨f, hfS, hfE, hfc, -⟩ := hC₁ κ hκ
  refine ⟨f, hfS, hfE, ?_⟩
  intro φ f' hφS hφE hf'S hf'E hf'
  obtain ⟨φ₂, hφ₂S, hφ₂E, hφ₂c, -⟩ := hC₂ (cls μ φ) (subset_closure ⟨φ, hφS, hφE, rfl⟩)
  have hmul : cls μ f' = F.Φ h₁ (cls μ φ₂) := by
    rw [hf', F.map_mul, hφ₂c]
    rfl
  rw [hfc, F.map_star, ContinuousLinearMap.adjoint_inner_left, ← hφ₂c]
  exact hrow φ₂ f' hφ₂S hφ₂E hf'S hf'E hmul

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2LimitEqPointwiseLimitHolds
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem l2_limit_eq_pointwise_limit : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (a : ℕ → Mat n → V) (b : Mat n → V) (x : Lp V 2 μ), (∀ k, MemLp (fun y : G n => a k y.val) 2 μ) → Tendsto (fun k => cls μ (a k)) atTop (𝓝 x) → (∀ z ∈ GLs n, Tendsto (fun k => a k z) atTop (𝓝 (b z))) → MemLp (fun y : G n => b y.val) 2 μ ∧ cls μ b = x := by
  intro n _ _ μ _ V _ _ _ a b x hm hc hp
  have hin : TendstoInMeasure μ (fun k => (cls μ (a k) : G n → V)) atTop (x : G n → V) :=
    tendstoInMeasure_of_tendsto_Lp hc
  obtain ⟨ns, hns, hae⟩ := hin.exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂μ, ∀ k, (cls μ (a k) : G n → V) y = a k y.val :=
    ae_all_iff.2 fun k => coe_cls μ (hm k)
  have hbx : (fun y : G n => b y.val) =ᵐ[μ] x := by
    filter_upwards [hae, hall] with y h1 h2
    have hy : y.val ∈ GLs n := by
      have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
      exact hu.ne_zero
    have h3 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (b y.val)) :=
      (hp y.val hy).comp hns.tendsto_atTop
    have h4 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (x y)) := by
      simpa only [h2] using h1
    exact tendsto_nhds_unique h3 h4
  exact cls_of_ae μ hbx

end GlobalTheory.CompanionTheory.PresSobA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationRightTranslate
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem Mol_rR_eq (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (hU : Unimod) (φ : Mat n → ℝ) (h : G n) (x : Lp V 2 μ) (z : Mat n) :
    Mol μ φ (⇑(rR μ V h x)) z = Mol μ φ (⇑x) (z * h.val) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have he : MeasurableEmbedding (fun y : G n => y * h) := (Homeomorph.mulRight h).measurableEmbedding
  have h1 : Mol μ φ (⇑(rR μ V h x)) z = ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x (u * h) ∂μ := by
    unfold Mol
    refine integral_congr_ae ?_
    filter_upwards [rR_coe μ hU h x] with u hu
    rw [hu]
  rw [h1]
  unfold Mol
  rw [← hm.integral_comp he (fun u : G n => φ (z * h.val * (u⁻¹ : G n).val) • x u)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have : z * h.val * ((u * h)⁻¹ : G n).val = z * (u⁻¹ : G n).val := by
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp only [this]

end GlobalTheory.CompanionTheory.PresSobA
end
end

