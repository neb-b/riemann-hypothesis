module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.JumpAndLengthOfAdmitted
public import Formalism.AdmissibleDesigns.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealLieChartKernelOperatorAtOne
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW Topology

namespace GlobalTheory.JSW.KerDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
def rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := rmul
      map_add' := fun y z => ContinuousLinearMap.ext fun x => Matrix.mul_add (Matrix.of x) (Matrix.of y) (Matrix.of z)
      map_smul' := fun c y => ContinuousLinearMap.ext fun x => Matrix.mul_smul (Matrix.of x) c (Matrix.of y) }

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_rmul_le (y : Lie E a) : ‖rmul y‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ :=
  (rmulL (E := E) (a := a)).le_opNorm y

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_mul_le (x y : Lie E a) :
    ‖toL (Matrix.of x * Matrix.of y)‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ * ‖x‖ :=
  (rmulL (E := E) (a := a)).le_opNorm₂ y x


omit [_root_.NumberField.IsTotallyComplex E] in
theorem eventually_inv_bdd :
    ∀ᶠ Y in 𝓝 (oneL E a), Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < ‖oneL E a‖ + 1 := by
  have hc : ContinuousAt (fun Y : Lie E a => toL (Matrix.of Y)⁻¹) (oneL E a) := by
    have h := continuousAt_matrix_inv (1 : Matrix (Fin a) (Fin a) (Cinf E)) (by
      rw [Matrix.det_one]
      exact NormedRing.inverse_continuousAt (1 : (Cinf E)ˣ))
    exact h
  have h1 : toL (Matrix.of (oneL E a))⁻¹ = oneL E a := by simp
  have h0 : ‖toL (Matrix.of (oneL E a))⁻¹‖ < ‖oneL E a‖ + 1 := by rw [h1]; exact lt_add_one _
  have h2 := hc.norm.eventually (gt_mem_nhds h0)
  exact Filter.Eventually.and (isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)) h2

theorem norm_chart_le (φ : GA E a → ℂ) (g : GA E a) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (Y : Lie E a) :
    ‖chart φ g Y‖ ≤ max C 0 := by
  unfold chart
  split_ifs
  · exact le_max_of_le_left (hC _)
  · simp

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have h := ContinuousOn.measurable_piecewise (hφ g).continuousOn (continuousOn_const (c := (0 : ℂ)))
    isOpen_invSet.measurableSet
  convert h using 1
  funext Y
  by_cases hY : Y ∈ invSet E a
  · rw [Set.piecewise_eq_of_mem _ _ _ hY]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hY]
    have hY' : ¬ IsUnit (Matrix.of Y) := hY
    simp [chart, hY']

theorem hasFDerivAt_chart_kerOp_of_bound {X : Type} [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) (φ : Sm E a) (hφ : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C)
    (hD : ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖)
    (g : GA E a) :
    HasFDerivAt (chart (kerOp ν k γ φ.1) g)
      (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) := by
  obtain ⟨hkm, hγm, hint⟩ := hk
  obtain ⟨Cφ, hCφ⟩ := hφ
  obtain ⟨CD, hCD⟩ := hD
  set M := ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ with hM
  set B := ‖oneL E a‖ + 1 with hB
  have hM0 : 0 ≤ M := norm_nonneg _
  have hB0 : 0 ≤ B := by positivity
  set s : Set (Lie E a) := {Y | Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < B} with hs_def
  have hs : s ∈ 𝓝 (oneL E a) := eventually_inv_bdd
  set F : Lie E a → X → ℂ := fun Y x => k x * chart φ.1 g (rmul (toL (γ x).val) Y) with hF
  set F' : Lie E a → X → (Lie E a →L[ℝ] ℂ) := fun Y x =>
    k x • (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)).comp (rmul (toL (γ x).val)) with hF'
  have hγL : Measurable fun x => toL (γ x).val := hγm
  have heq : chart (kerOp ν k γ φ.1) g =ᶠ[𝓝 (oneL E a)] fun Y => ∫ x, F Y x ∂ν := by
    filter_upwards [isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)] with Y hY
    obtain ⟨u, hu⟩ := hY
    have hY' : Y = toL u.val := hu.symm
    subst hY'
    rw [chart_val]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change k x * φ.1 (g * infGL E a u * infGL E a (γ x)) = k x * chart φ.1 g (rmul (toL (γ x).val) (toL u.val))
    rw [mul_assoc, ← map_mul, ← chart_val φ.1 g (u * γ x)]
    rfl
  have e1 : ∀ x, rmul (toL (γ x).val) (oneL E a) = toL (γ x).val := fun x => one_mul (γ x).val
  have hF'1 : F' (oneL E a) =
      fun x => k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) := by
    funext x; simp only [hF', e1]
  refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
  rw [← hF'1]

  have hmeasF : ∀ Y, AEStronglyMeasurable (F Y) ν := fun Y => by
    refine (hkm.aestronglyMeasurable).mul ?_
    refine ((measurable_chart φ.2 g).comp ?_).aestronglyMeasurable
    exact ((rmulL (E := E) (a := a)).flip Y).continuous.measurable.comp hγL
  have hmeasF' : AEStronglyMeasurable (F' (oneL E a)) ν := by
    rw [hF'1]
    refine hkm.aestronglyMeasurable.smul ?_
    exact (ContinuousLinearMap.compL ℝ (Lie E a) (Lie E a) ℂ).aestronglyMeasurable_comp₂
      ((measurable_fderiv ℝ (chart φ.1 g)).comp hγL).aestronglyMeasurable
      ((rmulL (E := E) (a := a)).continuous.measurable.comp hγL).aestronglyMeasurable

  have hint0 : Integrable (F (oneL E a)) ν := by
    refine Integrable.mono' ((hint 0).mul_const (max Cφ 0)) (hmeasF _) (ae_of_all _ fun x => ?_)
    simp only [hF, norm_mul, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_chart_le φ.1 g hCφ _) (norm_nonneg _)

  set K := max CD 0 * M * B * M with hK
  have hbound : ∀ᵐ x ∂ν, ∀ Y ∈ s, ‖F' Y x‖ ≤ ‖k x‖ * height (γ x) ^ 2 * K := by
    refine ae_of_all _ fun x Y hY => ?_
    have hu : IsUnit (Matrix.of Y) := hY.1
    set y := hu.unit * γ x with hy
    have hyv : rmul (toL (γ x).val) Y = toL y.val := by
      rw [hy, Units.val_mul, IsUnit.unit_spec]; rfl
    have hyi : toL (y⁻¹).val = toL (Matrix.of (toL (γ x)⁻¹.val) * Matrix.of (toL (hu.unit⁻¹).val)) := by
      rw [hy, _root_.mul_inv_rev, Units.val_mul]; rfl
    have hui : ‖toL (hu.unit⁻¹).val‖ ≤ B := by
      rw [Matrix.coe_units_inv, IsUnit.unit_spec]; exact hY.2.le
    have hg1 : ‖toL (γ x).val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x)⁻¹.val)]
    have hg2 : ‖toL (γ x)⁻¹.val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x).val)]
    have hL : ‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ ≤ max CD 0 * (M * B * height (γ x)) := by
      rw [hyv]
      refine (hCD g y).trans ?_
      have h1 : ‖toL (y⁻¹).val‖ ≤ M * B * height (γ x) := by
        rw [hyi]
        refine (norm_mul_le _ _).trans ?_
        gcongr
      calc CD * ‖toL (y⁻¹).val‖ ≤ max CD 0 * ‖toL (y⁻¹).val‖ := by gcongr; exact le_max_left _ _
        _ ≤ _ := by gcongr
    have hR : ‖rmul (toL (γ x).val)‖ ≤ M * height (γ x) := (norm_rmul_le _).trans (mul_le_mul_of_nonneg_left hg1 hM0)
    calc ‖F' Y x‖ ≤ ‖k x‖ * (‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ * ‖rmul (toL (γ x).val)‖) := by
          simp only [hF', norm_smul]
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖k x‖ * ((max CD 0 * (M * B * height (γ x))) * (M * height (γ x))) := by
          have hh0 : 0 ≤ height (γ x) := (norm_nonneg _).trans hg1
          gcongr
      _ = ‖k x‖ * height (γ x) ^ 2 * K := by rw [hK]; ring
  have hdiff : ∀ᵐ x ∂ν, ∀ Y ∈ s, HasFDerivAt (F · x) (F' Y x) Y := by
    refine ae_of_all _ fun x Y hY => ?_
    have hmem : rmul (toL (γ x).val) Y ∈ invSet E a := IsUnit.mul hY.1 (γ x).isUnit
    have h1 : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y))
        (rmul (toL (γ x).val) Y) :=
      ((contDiffAt_chart φ.2 g hmem).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp Y (rmul (toL (γ x).val)).hasFDerivAt).const_mul (k x)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs (Filter.Eventually.of_forall hmeasF) hint0 hmeasF'
    hbound ((hint 2).mul_const K) hdiff

end GlobalTheory.JSW.KerDeriv

namespace GlobalTheory.JSW

theorem hasFDerivAt_chart_kerOp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type)
    [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      HasFDerivAt (chart (kerOp ν k γ φ.1) g)
        (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) :=
  fun E _ _ _ a _ _ ν k γ hk φ hφ hL g =>
    KerDeriv.hasFDerivAt_chart_kerOp_of_bound ν k γ hk φ hφ (_root_.GlobalTheory.JSW.norm_fderiv_chart_le E a φ hL) g

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertFrameConjExtendsAndFrameMapSurjective
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.InertFrameConj

open Matrix

theorem cT_diagonal_mul {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (d : Fin n → K) :
    Formalism.UG.cT σ (diagonal d) * diagonal d = diagonal fun j => σ (d j) * d j := by
  unfold Formalism.UG.cT
  rw [diagonal_map (map_zero σ), diagonal_transpose, diagonal_mul_diagonal]

def dg {K : Type} [Field K] {n : ℕ} (i : Fin n) (t : Kˣ) : GL (Fin n) K where
  val := diagonal (Function.update 1 i (t : K))
  inv := diagonal (Function.update 1 i ((t⁻¹ : Kˣ) : K))
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]

theorem cT_dg {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (i : Fin n) (t : Kˣ) :
    Formalism.UG.cT σ (dg i t).val * (dg i t).val = diagonal (Function.update 1 i (σ t * t)) := by
  change Formalism.UG.cT σ (diagonal _) * diagonal _ = _
  rw [cT_diagonal_mul]
  congr 1
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem eq_of_cT_dg {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (i : Fin n) (t : Kˣ)
    (h : Formalism.UG.cT σ (dg i t).val * (dg i t).val = 1) : σ t * t = 1 := by
  have := congrFun (congrFun h i) i
  rw [cT_dg] at this
  simpa using this

theorem dg_mem {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (i : Fin n) (t : Kˣ) (h : σ t * t = 1) :
    dg i t ∈ Formalism.UG.UJ σ (1 : Matrix (Fin n) (Fin n) K) := by
  show Formalism.UG.cT σ (dg i t).val * 1 * (dg i t).val = 1
  rw [Matrix.mul_one, cT_dg, h, ← diagonal_one]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem cT_mul_self_of_frame {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (b g : GL (Fin n) K) (J : Matrix (Fin n) (Fin n) K)
    (hb : Formalism.UG.cT σ b.val * b.val = J)
    (h : Formalism.UG.cT σ (b⁻¹ * g * b).val * J * (b⁻¹ * g * b).val = J) : Formalism.UG.cT σ g.val * g.val = 1 := by
  have e1 : Formalism.UG.cT σ (b⁻¹).val * Formalism.UG.cT σ b.val = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  have e2 : b.val * (b⁻¹).val = 1 := Units.mul_inv b
  subst hb
  simp only [Units.val_mul, Formalism.UG.cT_mul] at h
  have h' : Formalism.UG.cT σ b.val * (Formalism.UG.cT σ g.val * g.val) * b.val = Formalism.UG.cT σ b.val * b.val := by
    rw [← h]
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc (Formalism.UG.cT σ (b⁻¹).val), e1, Matrix.one_mul, ← Matrix.mul_assoc b.val, e2, Matrix.one_mul]
  have h'' := congrArg (fun M => Formalism.UG.cT σ (b⁻¹).val * M * (b⁻¹).val) h'
  simp only [Matrix.mul_assoc] at h''
  rwa [e2, Matrix.mul_one, ← Matrix.mul_assoc (Formalism.UG.cT σ (b⁻¹).val), e1, Matrix.one_mul, ← Matrix.mul_assoc,
    e1, Matrix.one_mul] at h''

theorem eq_of_norms {K : Type} [Field K] (σ : K →+* K) (Y Y' : K) (hne : Y ≠ Y') (h1 : σ Y * Y = σ Y' * Y')
    (h2 : σ (Y + 1) * (Y + 1) = σ (Y' + 1) * (Y' + 1)) : σ Y = Y' := by
  rw [map_add (f := _), map_add (f := _), map_one] at h2
  have h3 : σ Y + Y = σ Y' + Y' := by linear_combination h2 - h1
  have h4 : σ Y * (Y - Y') = Y' * (Y - Y') := by linear_combination h1 - Y' * h3
  exact mul_right_cancel₀ (sub_ne_zero.2 hne) h4

end GlobalTheory.InertFrameConj


open GlobalTheory.InertFrameConj GlobalTheory.SplitPts in
theorem GlobalTheory.InertFrameConj.conj_and_surjective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), 0 < n → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) ∧ Function.Surjective p := by
  intro L _ _ _ n hn v w _ Dv b _ hb p hp
  have i0 : Fin n := ⟨0, hn⟩

  have hu : ∀ x : locU n w, Formalism.UG.cT Dv.σw (cLoc w x.1).val * (cLoc w x.1).val = 1 := by
    intro x
    refine cT_mul_self_of_frame Dv.σw b (cLoc w x.1) _ hb ?_
    have h : Formalism.UG.cT Dv.σw (p x).val.val * Formalism.UG.antiJ (w.adicCompletion L) n * (p x).val.val =
        Formalism.UG.antiJ (w.adicCompletion L) n := (p x).2
    rw [hp x] at h
    exact h
  have hdg : ∀ (t : (w.adicCompletion L)ˣ) (x : locU n w), cLoc w x.1 = dg i0 t → Dv.σw t * t = 1 := by
    intro t x hx
    have := hu x
    rw [hx] at this
    exact eq_of_cT_dg Dv.σw i0 t this

  have hinj := (algebraMap L (w.adicCompletion L)).injective
  by_cases hsp : IsSplitAt w
  ·
    exfalso
    have h2 : (2 : w.adicCompletion L) ≠ 0 := by
      rw [show (2 : w.adicCompletion L) = algebraMap L _ 2 from (map_ofNat _ 2).symm]
      exact (map_ne_zero _).2 two_ne_zero
    have h := hdg (Units.mk0 2 h2) (locPt hsp (dg i0 (Units.mk0 2 h2))) (cLoc_locPt hsp _)
    rw [Units.val_mk0, map_ofNat] at h
    have h4 : algebraMap L (w.adicCompletion L) 4 = algebraMap L _ 1 := by
      rw [map_one, ← h, map_ofNat]; norm_num
    have := hinj h4
    norm_num at this

  have hcs : conjSrc (conjE L) w = w := by
    by_contra hne
    exact hsp ⟨_, hne, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w _).2
      (Or.inr (conjPl_self_conjSrc w))⟩
  obtain ⟨s, hs, hsv⟩ : ∃ s : w.adicCompletion L →+* w.adicCompletion L,
      (∀ k : L, s (algebraMap L _ k) = algebraMap L _ (IsCMField.complexConj L k)) ∧
        ∀ x, Valued.v (s x) = Valued.v x := by
    have key : ∀ (u : HeightOneSpectrum (𝓞 L)) (_ : u = w) (f : u.adicCompletion L →+* w.adicCompletion L),
        (∀ k : L, f (algebraMap L _ k) = algebraMap L _ (conjE L k)) → (∀ x, Valued.v (f x) = Valued.v x) →
        ∃ s : w.adicCompletion L →+* w.adicCompletion L,
          (∀ k : L, s (algebraMap L _ k) = algebraMap L _ (IsCMField.complexConj L k)) ∧
            ∀ x, Valued.v (s x) = Valued.v x := by
      rintro u rfl f h1 h2
      exact ⟨f, h1, h2⟩
    exact key _ hcs _ (conjLoc_spec (conjE L) w).2.1 (conjLoc_spec (conjE L) w).2.2
  obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv L n w s hs hsv

  have hpair : ∀ y : L, y ≠ IsCMField.complexConj L y →
      Dv.σw (algebraMap L _ y) * algebraMap L _ y =
        Dv.σw (algebraMap L _ (IsCMField.complexConj L y)) * algebraMap L _ (IsCMField.complexConj L y) := by
    intro y hy
    have hy0 : y ≠ 0 := fun h => hy (by rw [h, map_zero])
    have hc0 : IsCMField.complexConj L y ≠ 0 := fun h => hy0 (by
      simpa using congrArg (IsCMField.complexConj L) h)
    have hY : algebraMap L (w.adicCompletion L) y ≠ 0 := (map_ne_zero _).2 hy0
    have hY' : algebraMap L (w.adicCompletion L) (IsCMField.complexConj L y) ≠ 0 := (map_ne_zero _).2 hc0
    set z : (w.adicCompletion L)ˣ := Units.mk0 (algebraMap L _ y / algebraMap L _ (IsCMField.complexConj L y))
      (div_ne_zero hY hY') with hz
    have hsz : s z * z = 1 := by
      rw [hz, Units.val_mk0, map_div₀, hs, hs, IsCMField.complexConj_apply_apply]
      field_simp
    have hmem := dg_mem s i0 z hsz
    have h := hdg z (e.symm ⟨dg i0 z, hmem⟩) (by rw [← he, e.apply_symm_apply])
    rw [hz, Units.val_mk0, map_div₀] at h
    have hσ0 : Dv.σw (algebraMap L _ (IsCMField.complexConj L y)) ≠ 0 := (map_ne_zero _).2 hY'
    field_simp at h
    linear_combination h
  have hext : ∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x) := by
    have hone : ∀ y : L, y ≠ IsCMField.complexConj L y →
        Dv.σw (algebraMap L _ y) = algebraMap L _ (IsCMField.complexConj L y) := by
      intro y hy
      refine eq_of_norms Dv.σw _ _ (fun h => hy (hinj h)) (hpair y hy) ?_
      have hy1 : y + 1 ≠ IsCMField.complexConj L (y + 1) := by
        rw [map_add (f := _), map_one]; exact fun h => hy (add_right_cancel h)
      have := hpair (y + 1) hy1
      simpa only [map_add (f := _), map_one] using this
    obtain ⟨t, ht⟩ : ∃ t : L, t ≠ IsCMField.complexConj L t := by
      by_contra hc
      push_neg at hc
      exact IsCMField.complexConj_ne_one L (AlgEquiv.ext fun t => (hc t).symm)
    intro x
    by_cases hx : x = IsCMField.complexConj L x
    · have hxt : x + t ≠ IsCMField.complexConj L (x + t) := by
        rw [map_add (f := _), ← hx]; exact fun h => ht (add_left_cancel h)
      have h1 := hone _ hxt
      rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hone t ht, ← hx] at h1
      rw [← hx]
      exact add_right_cancel h1
    · exact hone x hx
  refine ⟨hext, ?_⟩
  obtain ⟨e', he'⟩ := GlobalTheory.DefU.Inert.locU_equiv L n w Dv.σw hext Dv.unram.2.1
  have hb1 : Formalism.UG.cT Dv.σw b.1 * 1 * b.1 = Formalism.UG.antiJ _ n := by rwa [Matrix.mul_one]
  intro g
  let P := e'.trans (GlobalTheory.InertSatake.conjEquiv Dv.σw b hb1)
  have hP : ((P (P.symm g) : Formalism.UG.GU Dv.σw n) : GL (Fin n) (w.adicCompletion L)) =
      b⁻¹ * cLoc w (P.symm g).1 * b := by
    change b⁻¹ * (e' _ : GL (Fin n) _) * b = _
    rw [he']
  refine ⟨P.symm g, Subtype.ext ?_⟩
  rw [hp, ← hP, P.apply_symm_apply]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralHermitianAdjointCovolOnePeriodicEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SWChangeVar

theorem integral_adjO_eq : ∀ (D : D7) (V W : HSp D) (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL V W) ν 𝓖' → IsCovolOne (ratL W V) μ 𝓕 → ∀ (Φ : WO V W → ℂ), (∀ (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : WO V W), Φ (ratW W V γ + u) = Φ u) → ∫ y in 𝓖', Φ (GlobalTheory.PairLift.adjO V W y) ∂ν = ∫ u in 𝓕, Φ u ∂μ := by
  intro D V W ν 𝓖' μ 𝓕 hν hμ Φ hΦ
  haveI : BorelSpace (Mx D V.rank W.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D W.rank V.rank) := ⟨rfl⟩
  let A : Mx D V.rank W.rank ≃+ Mx D W.rank V.rank :=
    { toFun := GlobalTheory.PairLift.adjO V W
      invFun := GlobalTheory.PairLift.adjO W V
      left_inv := GlobalTheory.AdjLawPf.adj_invol W V
      right_inv := GlobalTheory.AdjLawPf.adj_invol V W
      map_add' := GlobalTheory.AdjLawPf.adj_add V W }
  let L : Mx D V.rank W.rank ≃ₜ+ Mx D W.rank V.rank :=
    { A with
      continuous_toFun := GlobalTheory.AdjLawPf.adj_cont V W
      continuous_invFun := GlobalTheory.AdjLawPf.adj_cont W V }
  let e : Mx D V.rank W.rank ≃ᵐ Mx D W.rank V.rank := L.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = GlobalTheory.PairLift.adjO V W y := fun _ => rfl
  haveI := hν.1
  have hH : (ν.map e).IsAddHaarMeasure := L.isAddHaarMeasure_map ν
  have hmp : MeasurePreserving e ν (ν.map e) := e.measurable.measurePreserving ν
  let r : ratL W V ≃ ratL V W :=
    { toFun := fun g => ⟨GlobalTheory.PairLift.adjO W V g, GlobalTheory.AdjLawPf.adj_rat_of W V g g.2⟩
      invFun := fun g => ⟨GlobalTheory.PairLift.adjO V W g, GlobalTheory.AdjLawPf.adj_rat_of V W g g.2⟩
      left_inv := fun g => Subtype.ext (GlobalTheory.AdjLawPf.adj_invol V W g)
      right_inv := fun g => Subtype.ext (GlobalTheory.AdjLawPf.adj_invol W V g) }
  have hcov : IsCovolOne (ratL W V) (ν.map e) (e '' 𝓖') := by
    refine ⟨hH, ?_, ?_⟩
    · refine hν.2.1.image_of_equiv e.toEquiv (hmp.symm e).quasiMeasurePreserving r fun g a => ?_
      show GlobalTheory.PairLift.adjO V W (GlobalTheory.PairLift.adjO W V (g : Mx D W.rank V.rank) + a) =
        (g : Mx D W.rank V.rank) + GlobalTheory.PairLift.adjO V W a
      rw [GlobalTheory.AdjLawPf.adj_add, GlobalTheory.AdjLawPf.adj_invol]
    · rw [e.map_apply, e.preimage_image]; exact hν.2.2
  have hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank V.rank, ∀ a, Φ (γ + a) = Φ a := by
    rintro _ ⟨γ, rfl⟩ a
    exact hΦ γ a
  have h := GlobalTheory.MixModel.covolOne_integral_eq (μ := μ) (μ' := ν.map e) (𝓕 := 𝓕) (𝓕' := e '' 𝓖') hμ hcov Φ hφ
  rw [setIntegral_map_equiv, e.preimage_image] at h
  exact h

end GlobalTheory.SWChangeVar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementMemAdelicGLSupportedAtFinitePlaceStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurComplement_mem_adelicGLSupportedAtFinitePlaces : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
  first | (exact @GlobalTheory.SchurExt.mkGL_Scof_mem_supS) | (exact GlobalTheory.SchurExt.mkGL_Scof_mem_supS) | (intros; apply GlobalTheory.SchurExt.mkGL_Scof_mem_supS  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItems
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem splitCase_bound_at_point_of_admitted_items : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB →
    (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) →
    EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB := by
  intro hAR hTD hEC D i r ρ π dc ep e' c0 cB hA hG2 hL hD hπ
  obtain ⟨hJ, hRow⟩ := EmbeddingTypes.jump_and_length_of_admitted i r ρ π dc e' c0 cB hA hL hD hπ
  obtain ⟨g1, -, g3, g4, g578, g5x, g6, -, a51, -, -, hBK, hLc, -, -, hTB, unr, ct, -, dcm, -, tie, -,
    font, -, fin, -⟩ := hA
  have g5 : TruncatedSeriesCountingIdentities.admG5 i r := Formalism.MainNotions.N.K.SplitLatticeDiagonal.admG5_of_adm51_admG5 i r ρ π hπ a51 g578
  have g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π := hG2 hL.2.2.2.1 hL.2.2.2.2 hπ
  refine ⟨hJ, hRow, fun hs hsha _ => ?_⟩
  have hthm := _root_.GlobalTheory.SelmerBoundAtPoint.main hAR hTD hEC D i r ρ π dc (EmbeddingTypes.lenRowSplit i dc e' c0) (fun _ => e') cB
    g1 g2 g3 g4 g5 g5x g6 hBK.1 hBK.2 ct dcm font fin tie a51 unr
    (EmbeddingTypes.admissible_length_of_local i r ρ π dc hD.2 e' c0 hRow) hLc hTB
  exact EmbeddingTypes.length_bound_of_theorem i ρ π dc hD.2 e' c0 cB hJ hthm hL.2.2.2.1 hL.2.2.2.2 hπ hs hsha

end GlobalTheory
end

