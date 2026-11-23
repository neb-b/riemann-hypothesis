module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Topology
open scoped ContDiff

namespace GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
def invM (y : Lie E a) : Lie E a := toL (Matrix.of y)⁻¹


omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiffOn_invM : ContDiffOn ℝ ∞ (invM (E := E) (a := a)) (invSet E a) := by
  have h1 : ContDiffOn ℝ ∞ (fun y : Lie E a => Ring.inverse (Matrix.of y).det) (invSet E a) := fun y hy => by
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hy
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact (this.comp y contDiff_det.contDiffAt).contDiffWithinAt
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  have h2 : ContDiff ℝ ∞ fun y : Lie E a => (Matrix.of y).adjugate i j := by
    simp only [Matrix.adjugate_apply]
    have h3 : ContDiff ℝ ∞ fun y : Lie E a => (Function.update y j (Pi.single i 1) : Lie E a) := by
      refine contDiff_pi.2 fun k => ?_
      by_cases h : k = j
      · subst h; simpa using contDiff_const
      · simpa [Function.update_of_ne h] using contDiff_apply ℝ _ k
    exact contDiff_det.comp h3
  exact h1.mul h2.contDiffOn

theorem continuous_infGL : Continuous (infGL E a) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem continuousOn_chart {φ : GA E a → ℂ} (hφ : Continuous φ) :
    ContinuousOn (fun p : GA E a × Lie E a => chart φ p.1 p.2) (Set.univ ×ˢ invSet E a) := by
  rw [continuousOn_iff_continuous_restrict]
  have hu : Continuous fun p : (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a)) =>
      (IsUnit.unit (p.2.2 : IsUnit (Matrix.of p.1.2)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_snd.comp continuous_subtype_val, ?_⟩
    have := contDiffOn_invM.continuousOn.comp_continuous
      (f := fun p : (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a)) => p.1.2)
      (continuous_snd.comp continuous_subtype_val) fun p => p.2.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  refine (hφ.comp ((continuous_fst.comp continuous_subtype_val).mul (continuous_infGL.comp hu))).congr fun p => ?_
  exact (chart_val φ p.1.1 (IsUnit.unit (p.2.2 : IsUnit (Matrix.of p.1.2)))).symm


omit [_root_.NumberField.IsTotallyComplex E] in
def coef (i : Fin (Module.finrank ℝ (Lie E a))) (y : Lie E a) : Lie E a →L[ℝ] ℂ :=
  Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord i) ∘L lmul (invM y)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiffOn_coef (i : Fin (Module.finrank ℝ (Lie E a))) : ContDiffOn ℝ ∞ (coef i) (invSet E a) := by
  refine contDiffOn_clm_apply.2 fun Y => ?_
  exact (Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord i) ∘L
    rmul Y).contDiff.comp_contDiffOn contDiffOn_invM

theorem fderiv_chart (φ : Sm E a) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    fderiv ℝ (chart φ.1 g) y = ∑ i, chart (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 g y • coef i y := by
  ext Y
  have e : Y = rmul (lmul (invM y) Y) y := by
    change Matrix.of Y = Matrix.of y * ((Matrix.of y)⁻¹ * Matrix.of Y)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hy)]
  have e2 : ∀ X, rmul X y = lmul y X := fun _ => rfl
  conv_lhs => rw [e, e2, ← (Module.finBasis ℝ (Lie E a)).sum_repr (lmul (invM y) Y)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, ← e2, ← chart_lieD φ.2 _ g hy, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm,
    Complex.real_smul]
  rfl

def Good (φ : Sm E a) : Prop := (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}

theorem Good.lie {φ : Sm E a} (h : Good φ) (X : Lie E a) : Good (lie E a X φ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · have e : chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
      funext x; simp only [chart, mul_assoc, h.1]
    simp only [lie_apply, lieD, e]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun k hk => ?_)
    have e := LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : rt E a (finGL E a k) φ = φ := hk
    simp only [Module.End.mul_apply, hk'] at e
    exact e.symm


omit [_root_.NumberField.IsTotallyComplex E] in
theorem exists_bound {r : ℕ} {V : Type} [NormedAddCommGroup V] {Ψ : GA E a → Lie E a → V} {S : Set (Lie E a)}
    (hS : IsCompact S) (hc : ContinuousOn (fun p : GA E a × Lie E a => Ψ p.1 p.2) (Set.univ ×ˢ S))
    (hl : ∀ γ g, Ψ (ratGL E a γ * g) = Ψ g) (g : GA E a) :
    ∃ C, ∀ (x : BlockIx a r → Ad E), ∀ y ∈ S, ‖Ψ (unip x * g) y‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn
    (f := fun p : (BlockIx a r → Ad E) × Lie E a => Ψ (unip p.1 * g) p.2)
    (hc.comp (((CuspidalL2GL.continuous_unip.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
      fun p hp => ⟨trivial, hp.2⟩)
  refine ⟨C, fun x y hy => ?_⟩
  obtain ⟨_, ⟨z, rfl⟩, hk⟩ := hcov x
  have := hC (_, y) ⟨hk, hy⟩
  simp only [unip_add, mul_assoc] at this
  exact (congrArg (fun f => ‖f y‖) ((congrArg (fun u => Ψ (u * _)) (unip_algebraMap z)).trans (hl _ _))).symm.trans_le
    this

theorem Good.chart_left {φ : Sm E a} (h : Good φ) (γ : GL (Fin a) E) (g : GA E a) :
    chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
  funext x; simp only [chart, mul_assoc, h.1]

theorem Good.continuousOn_chart {φ : Sm E a} (h : Good φ) :
    ContinuousOn (fun p : GA E a × Lie E a => chart φ.1 p.1 p.2) (Set.univ ×ˢ invSet E a) :=
  ConstTermSmooth.continuousOn_chart (ContAut.continuous_of_isOpen_stab E a φ h.2)

theorem Good.continuousOn_fderiv {φ : Sm E a} (h : Good φ) :
    ContinuousOn (fun p : GA E a × Lie E a => fderiv ℝ (chart φ.1 p.1) p.2) (Set.univ ×ˢ invSet E a) := by
  refine ContinuousOn.congr ?_ fun p hp => fderiv_chart φ p.1 hp.2
  exact continuousOn_finsetSum _ fun i _ => (h.lie _).continuousOn_chart.smul
    ((contDiffOn_coef i).continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2)

section Integral

variable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
  (ν : Measure (BlockIx a r → Ad E)) [IsFiniteMeasure ν]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem integrable_unip {V : Type} [NormedAddCommGroup V] {Ψ : GA E a → Lie E a → V}
    (hc : ContinuousOn (fun p : GA E a × Lie E a => Ψ p.1 p.2) (Set.univ ×ˢ invSet E a))
    (hl : ∀ γ g, Ψ (ratGL E a γ * g) = Ψ g) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    Integrable (fun x => Ψ (unip x * g) y) ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  obtain ⟨C, hC⟩ := exists_bound (r := r) (isCompact_singleton (x := y))
    (hc.mono (Set.prod_mono_right (Set.singleton_subset_iff.2 hy))) hl g
  have hf : Continuous fun x : BlockIx a r → Ad E => Ψ (unip x * g) y :=
    hc.comp_continuous ((CuspidalL2GL.continuous_unip.mul continuous_const).prodMk continuous_const) fun _ => ⟨trivial, hy⟩
  exact Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun x => hC x y rfl)


omit [BorelSpace (BlockIx a r → Ad E)] [IsFiniteMeasure ν] in
theorem chart_integral (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun g => ∫ x, φ (unip x * g) ∂ν) g = fun y => ∫ x, chart φ (unip x * g) y ∂ν := by
  funext y
  by_cases h : IsUnit (Matrix.of y)
  · simp only [chart, dif_pos h, mul_assoc]
  · simp only [chart, dif_neg h, integral_zero]

theorem Good.hasFDerivAt {φ : Sm E a} (h : Good φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    HasFDerivAt (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) (∫ x, fderiv ℝ (chart φ.1 (unip x * g)) y ∂ν) y := by
  rw [chart_integral]
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hy)
  have hl : ∀ γ g, (fun y => fderiv ℝ (chart φ.1 (ratGL E a γ * g)) y) = fun y => fderiv ℝ (chart φ.1 g) y :=
    fun γ g => by rw [h.chart_left]
  obtain ⟨C, hC⟩ := exists_bound (r := r) (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) hS
    (h.continuousOn_fderiv.mono (Set.prod_mono_right hSU)) hl g
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) fun z hz =>
      (integrable_unip ν h.continuousOn_chart h.chart_left g hz).1)
    (integrable_unip ν h.continuousOn_chart h.chart_left g hy)
    (integrable_unip ν (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) h.continuousOn_fderiv hl g hy).1
    (.of_forall hC) (integrable_const C) (.of_forall fun x z hz => ?_)
  exact ((contDiffAt_chart φ.2 _ (hSU hz)).differentiableAt (by simp)).hasFDerivAt

theorem Good.fderiv_integral {φ : Sm E a} (h : Good φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    fderiv ℝ (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) y = ∑ i,
      chart (fun g => ∫ x, (CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 (unip x * g) ∂ν) g y • coef i y := by
  rw [(h.hasFDerivAt ν g hy).fderiv]
  simp only [fderiv_chart φ _ hy, chart_integral]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_unip ν (h.lie _).continuousOn_chart (h.lie _).chart_left g hy).smul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_smul_const _ _

theorem contDiffOn_integral (g : GA E a) (n : ℕ) : ∀ φ : Sm E a, Good φ →
    ContDiffOn ℝ n (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) (invSet E a) := by
  induction n with
  | zero =>
    intro φ h
    exact contDiffOn_zero.2 fun y hy => (h.hasFDerivAt ν g hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro φ h
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
    refine ⟨fun y hy => (h.hasFDerivAt ν g hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr ?_ fun y hy => h.fderiv_integral ν g hy
    exact ContDiffOn.sum fun i _ => (ih _ (h.lie _)).smul ((contDiffOn_coef i).of_le (by exact_mod_cast le_top))

end Integral

theorem constTerm_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a),
      lieD X (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 _ _ h1 φ hl ho
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simp [h1]⟩
  have h : Good φ := ⟨hl, ho⟩
  refine ⟨fun g => contDiffOn_infty.2 fun n => contDiffOn_integral _ g n φ h, fun X g => ?_⟩
  rw [lieD, (h.hasFDerivAt (μ.restrict 𝓕) g (y := oneL E a) isUnit_one).fderiv, ContinuousLinearMap.integral_apply
    (integrable_unip _ (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) h.continuousOn_fderiv
      (fun γ g => by rw [h.chart_left]) g (y := oneL E a) isUnit_one)]
  rfl

end GlobalTheory.ConstTermSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CplxOfFrame
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameCplx

theorem gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ (-Gᵀ) x = -(xᴴ * G.map τ * x)ᵀ := by
  ext a b
  simp only [FD.gram, hermC, FD.col, of_apply, Matrix.neg_apply, transpose_apply, Matrix.mul_apply, map_neg, map_apply,
    conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  simp_rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hermC_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r) (v : Fin r → ℂ) :
    hermC τ (-Gᵀ) (FD.col x a) v = -((star v ᵥ* (G.map τ * x)) a) := by
  simp only [hermC, FD.col, Matrix.neg_apply, transpose_apply, Matrix.mul_apply, map_neg, map_apply, vecMul, dotProduct,
    Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  simp_rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section lin
variable {r : ℕ} {G x S s : Matrix (Fin r) (Fin r) ℂ}

theorem isUnit_det (hS : S * S = 1) (hG : xᴴ * G * x = -S) : IsUnit x.det := by
  have h : (-(S * (xᴴ * G))) * x = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hG, Matrix.mul_neg, neg_neg, hS]
  exact Matrix.isUnit_det_of_left_inverse h

theorem inv_mul_inv (hS : S * S = 1) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) : x⁻¹ * s = -(S * x⁻¹) := by
  have hx := isUnit_det hS hG
  have : s = -(x * S) * x⁻¹ := by rw [← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  rw [this, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hx]

open scoped ComplexOrder in
theorem cartan (hS : S * S = 1) (hH : Sᴴ = S) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) : IsCartanInv G s := by
  have hx := isUnit_det hS hG
  have hxH : IsUnit xᴴ.det := by rw [Matrix.det_conjTranspose]; exact hx.star
  have hs' : s = -(x * S * x⁻¹) := by rw [← Matrix.neg_mul, ← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  have hG' : G = -((x⁻¹)ᴴ * S * x⁻¹) := by
    rw [← Matrix.neg_mul, ← Matrix.mul_neg, ← hG, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc xᴴ,
      Matrix.nonsing_inv_mul_cancel_left _ _ hxH, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  have c1 : ∀ M : Matrix (Fin r) (Fin r) ℂ, x⁻¹ * (x * M) = M := fun M => Matrix.nonsing_inv_mul_cancel_left _ _ hx
  have c2 : ∀ M : Matrix (Fin r) (Fin r) ℂ, S * (S * M) = M := fun M => by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  have c3 : ∀ M : Matrix (Fin r) (Fin r) ℂ, xᴴ * ((x⁻¹)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hx, conjTranspose_one, Matrix.one_mul]
  have hGs : G * s = (x⁻¹)ᴴ * x⁻¹ := by
    rw [hG', hs']; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs']; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]
    exact Matrix.mul_nonsing_inv _ hx
  · rw [Matrix.mul_assoc, hGs, hG', hs']
    simp only [conjTranspose_neg, conjTranspose_mul, hH, Matrix.neg_mul, Matrix.mul_assoc, c3]
  · rw [hGs]
    have hu : IsUnit x⁻¹ := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hx)
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit hu)

theorem adj_inv (hS : S * S = 1) (hH : Sᴴ = S) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) :
    sᴴ * (G * x) = -(G * x * S) := by
  obtain ⟨h1, h2, -⟩ := cartan hS hH hG hs
  have : x = -(s * (x * S)) := by
    rw [← Matrix.mul_assoc, hs, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, hS, Matrix.mul_one]
  calc sᴴ * (G * x) = -((sᴴ * G * s) * (x * S)) := by
        conv_lhs => rw [this]
        simp only [Matrix.mul_neg, Matrix.mul_assoc]
    _ = _ := by rw [h2, Matrix.mul_assoc]
end lin

theorem sgnM_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : sgnM X * sgnM X = 1 := by
  rw [sgnM, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; unfold FD.sgn; split_ifs <;> simp

theorem sgnM_herm {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : (sgnM X)ᴴ = sgnM X := by
  rw [sgnM, diagonal_conjTranspose]
  congr 1; funext a; simp

theorem per_cplx {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x s : Matrix (Fin r) (Fin r) ℂ) (hG : xᴴ * G.map τ * x = -sgnM X)
    (hs : s * x = -(x * sgnM X)) (v : Fin r → ℂ) (a : Fin r) :
    (if (a : ℕ) < X.p0 then hermC τ (-Gᵀ) (FD.col x a) (I • (s *ᵥ v)) else (x⁻¹ *ᵥ (I • (s *ᵥ v))) a) =
      I * (if (a : ℕ) < X.p0 then hermC τ (-Gᵀ) (FD.col x a) v else (x⁻¹ *ᵥ v) a) := by
  split_ifs with h
  · rw [hermC_eq, hermC_eq, star_smul, star_mulVec, smul_vecMul, vecMul_vecMul,
      adj_inv (sgnM_sq X) (sgnM_herm X) hG hs, vecMul_neg, ← vecMul_vecMul, sgnM]
    simp only [Pi.smul_apply, Pi.neg_apply, vecMul_diagonal]
    simp [FD.sgn, h]
  · rw [mulVec_smul, mulVec_mulVec, inv_mul_inv (sgnM_sq X) hG hs, neg_mulVec, ← mulVec_mulVec, sgnM]
    simp only [Pi.smul_apply, Pi.neg_apply, mulVec_diagonal]
    simp [FD.sgn, h]


open scoped ComplexOrder in
theorem cplx_of_frame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) ∧ (∀ τ, IsCartanInv (gramAt D V τ) 1) ∧ ∀ (τ : D.what₂.Tau) (u : Matrix (Fin W.rank) (Fin V.rank) ℂ), zOf θ V W hr X idx x (lineAt θ τ (cplxO 1 (s τ) u) 1) = I • zOf θ V W hr X idx x (lineAt θ τ u 1) := by
  intro D ψ θ V W r g hr X bas idx _ hθ hV _ hM _ x s hx hs
  subst hr
  have hGm : X.Gm = -(HSpace.gram W)ᵀ := hM.model.1
  have hG : ∀ τ : X.Ψ, (mat x τ)ᴴ * (HSpace.gram W).map τ.1 * mat x τ = -sgnM X := fun τ => by
    have h := hx τ
    rw [hGm, gram_eq] at h
    have h2 : (sgnM X)ᵀ = sgnM X := by rw [sgnM, diagonal_transpose]
    rw [← h2, ← h, transpose_neg, transpose_transpose, neg_neg]
  have hs' : ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → s ρ * mat x τ = -(mat x τ * sgnM X) := hs
  refine ⟨fun ρ => ?_, fun ρ => ?_, fun ρ u => ?_⟩
  · have h := hG ⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩
    exact cartan (sgnM_sq X) (sgnM_herm X) h (hs' ρ _ rfl)
  · have : gramAt D V ρ = 1 := by
      rw [gramAt, hV]; exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this]
    refine ⟨by simp, by simp, ?_⟩
    rw [Matrix.mul_one]; exact Matrix.PosDef.one
  · have hL : ∀ z : Matrix (Fin W.rank) (Fin V.rank) ℂ, IsLineAt θ ρ z (lineAt θ ρ z) := fun z =>
      Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ ρ z)
    funext b j
    simp only [zOf, Pi.smul_apply, smul_eq_mul, perC]
    obtain ⟨τ, a⟩ := idx j
    have hτ : ∃ ρ', τ.1 = tauE D ρ' := (hM.psi _).1 τ.2
    simp only [realM, dif_pos hτ, (hL _).2.2, hGm]
    by_cases e : hτ.choose = ρ
    · simp only [if_pos e]
      have := per_cplx X τ.1 (HSpace.gram W) (mat x τ) (s ρ) (hG τ) (hs' ρ τ (e ▸ hτ.choose_spec)) (fun k => u k b) a
      convert this using 3 <;> (try funext k) <;> simp [cplxO, Matrix.mul_apply, mulVec, dotProduct]
    · simp only [if_neg e]
      simp [hermC, mulVec, dotProduct]

end GlobalTheory.FrameCplx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLinearCombination
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspFormLin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {d : ℕ}

theorem growth_smul_add (c : ℂ) {f f' : GL (Fin d) (Cinf E) → ℂ}
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N)
    (h' : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f' y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖c * f y + f' y‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, h⟩ := h
  obtain ⟨C', N', h'⟩ := h'
  refine ⟨‖c‖ * |C| + |C'|, N + N', fun y => ?_⟩
  have h1 := one_le_height y
  have e : ‖f y‖ ≤ |C| * height y ^ (N + N') :=
    (h y).trans (mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right N N'))
      (by positivity) (abs_nonneg C))
  have e' : ‖f' y‖ ≤ |C'| * height y ^ (N + N') :=
    (h' y).trans (mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left N' N))
      (by positivity) (abs_nonneg C'))
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, add_mul, mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left e (norm_nonneg c)) e'

theorem isAutForm_smul_add (c : ℂ) {φ ψ : Sm E d} (h : IsAutForm φ) (h' : IsAutForm ψ) :
    IsAutForm (c • φ + ψ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change c * φ.1 _ + ψ.1 _ = c * φ.1 _ + ψ.1 _
    rw [h.left, h'.left]
  · refine isOpen_stab_of_mem_nhds (finRep E d) (c • φ + ψ) (Filter.mem_of_superset
      ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) ?_)
    intro k hk
    have h1 : finRep E d k φ = φ := hk.1
    have h2 : finRep E d k ψ = ψ := hk.2
    change finRep E d k (c • φ + ψ) = c • φ + ψ
    rw [map_add (f := _), map_smul, h1, h2]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E d k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E d k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change cptRep E d k (c • φ + ψ) ∈ _
    rw [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
      (Submodule.subset_span ⟨k, rfl⟩)
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z φ) '' Zalg E d) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z ψ) '' Zalg E d)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    change z (c • φ + ψ) ∈ _
    rw [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
      (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    exact growth_smul_add c (h.growth g) (h'.growth g)

theorem isCuspForm_smul_add (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (d : ℕ) (c : ℂ)
    (φ ψ : Sm E d) (h : IsCuspForm φ) (h' : IsCuspForm ψ) : IsCuspForm (c • φ + ψ) := by
  refine ⟨isAutForm_smul_add c h.1 h'.1, fun r h0 h1 _ _ ν 𝓕 hν h𝓕 g => ?_⟩
  have i := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d φ h.1.level) h.1.left ν h𝓕 g
  have i' := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d ψ h'.1.level) h'.1.left ν h𝓕 g
  change ∫ x in 𝓕, (c * φ.1 (unip x * g) + ψ.1 (unip x * g)) ∂ν = 0
  rw [integral_add (i.const_mul c) i', integral_const_mul, h.2 r h0 h1 ν 𝓕 hν h𝓕 g, h'.2 r h0 h1 ν 𝓕 hν h𝓕 g,
    mul_zero, add_zero]

end GlobalTheory.CuspFormLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetCharIffExp
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetCharArch

theorem map_conj {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

end GlobalTheory.DetCharArch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartIndependentClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFactorDepthInChart_independent_closedField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X X' : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch X' f k := by
  first | exact @GlobalTheory.DepthField.nuFacC_field | exact GlobalTheory.DepthField.nuFacC_field | (intros; apply GlobalTheory.DepthField.nuFacC_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso : ∀ (X : Scheme.{0}) (W : X.Opens) (L M : LB X), LBIso (L.pull W.ι) (M.pull W.ι) → ∃ w : Cmp W L M, IsoOn W L M w := by
  first | exact @GlobalTheory.PicGlue.isoOn_of_lbIso | exact GlobalTheory.PicGlue.isoOn_of_lbIso | (intros; apply GlobalTheory.PicGlue.isoOn_of_lbIso <;> assumption)
end

