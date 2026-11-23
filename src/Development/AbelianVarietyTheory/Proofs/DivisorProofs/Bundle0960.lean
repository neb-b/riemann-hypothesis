module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterMaximalCompactDetPow
section
open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory.KChar

open Matrix

theorem norm_eq_one_of_compact {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] (f : G → ℂ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hc : Continuous f) (h1 : f 1 ≠ 0) : ∀ a, ‖f a‖ = 1 := by
  have hf1 : f 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    have h2 : f 1 * (f 1 - 1) = 0 := by rw [mul_sub, ← this]; ring
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h h1
    · exact sub_eq_zero.mp h
  obtain ⟨M, hM⟩ := (isCompact_range hc.norm).bddAbove
  have hb : ∀ a, ‖f a‖ ≤ M := fun a => hM ⟨a, rfl⟩
  have hpow : ∀ a (n : ℕ), f (a ^ n) = f a ^ n := by
    intro a n
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hle : ∀ a, ‖f a‖ ≤ 1 := by
    intro a
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
    have := hb (a ^ n)
    rw [hpow, norm_pow] at this
    linarith
  intro a
  have hinv : ‖f a‖ * ‖f a⁻¹‖ = 1 := by
    rw [← norm_mul, ← hmul, mul_inv_cancel, hf1, norm_one]
  have h2 := hle a⁻¹
  have h3 := hle a
  have h4 : 0 ≤ ‖f a‖ := norm_nonneg _
  have h5 : 0 ≤ ‖f a⁻¹‖ := norm_nonneg _
  nlinarith

theorem fromBlocks_mem (R S : ℕ) (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ)
    (ha : aᴴ * a = 1) (hd : dᴴ * d = 1) :
    (Matrix.fromBlocks a 0 0 d)ᴴ * Jm R S * Matrix.fromBlocks a 0 0 d = Jm R S := by
  change (Matrix.fromBlocks a 0 0 d)ᴴ * Matrix.fromBlocks 1 0 0 (-1) * Matrix.fromBlocks a 0 0 d =
    Matrix.fromBlocks 1 0 0 (-1)
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [ha, hd]

theorem unitary_ch {n : ℕ} (a : Matrix.unitaryGroup (Fin n) ℂ) : (a : Matrix (Fin n) (Fin n) ℂ)ᴴ * a = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp a.2
  simpa [Matrix.star_eq_conjTranspose] using this

theorem kchar : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∃ x y : ℤ, ∀ (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ), aᴴ * a = 1 → dᴴ * d = 1 →
      χ (Matrix.fromBlocks a 0 0 d) = a.det ^ x * d.det ^ y := by
  intro R S χ hmul hc hnz
  haveI := GlobalTheory.compactSpace_unitaryGroup (Fin R) ℂ
  haveI := GlobalTheory.compactSpace_unitaryGroup (Fin S) ℂ
  have h1R : (1 : Matrix (Fin R) (Fin R) ℂ)ᴴ * 1 = 1 := by simp
  have h1S : (1 : Matrix (Fin S) (Fin S) ℂ)ᴴ * 1 = 1 := by simp

  let fA : Matrix.unitaryGroup (Fin R) ℂ → ℂ := fun a => χ (Matrix.fromBlocks (a : Matrix (Fin R) (Fin R) ℂ) 0 0 1)
  have hmA : ∀ a b, fA (a * b) = fA a * fA b := by
    intro a b
    have e : Matrix.fromBlocks ((a * b : Matrix.unitaryGroup (Fin R) ℂ) : Matrix (Fin R) (Fin R) ℂ) 0 0
        (1 : Matrix (Fin S) (Fin S) ℂ) =
        Matrix.fromBlocks (a : Matrix (Fin R) (Fin R) ℂ) 0 0 1 * Matrix.fromBlocks (b : Matrix (Fin R) (Fin R) ℂ) 0 0 1 := by
      rw [Matrix.fromBlocks_multiply]; simp
    simp only [fA]
    rw [e]
    exact hmul _ _ (fromBlocks_mem R S _ _ (unitary_ch a) h1S) (fromBlocks_mem R S _ _ (unitary_ch b) h1S)
  have hcA : Continuous fA := by
    refine hc.comp_continuous ?_ (fun a => fromBlocks_mem R S _ _ (unitary_ch a) h1S)
    exact Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const continuous_const
  have hnA : ∀ a, ‖fA a‖ = 1 :=
    norm_eq_one_of_compact fA hmA hcA (hnz _ (fromBlocks_mem R S _ _ (unitary_ch 1) h1S))
  obtain ⟨x, hx⟩ := GlobalTheory.UpqChar.char_unitary fA hmA hnA hcA

  let fD : Matrix.unitaryGroup (Fin S) ℂ → ℂ := fun d => χ (Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) ℂ) 0 0 (d : Matrix (Fin S) (Fin S) ℂ))
  have hmD : ∀ a b, fD (a * b) = fD a * fD b := by
    intro a b
    have e : Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) ℂ) 0 0
        ((a * b : Matrix.unitaryGroup (Fin S) ℂ) : Matrix (Fin S) (Fin S) ℂ) =
        Matrix.fromBlocks 1 0 0 (a : Matrix (Fin S) (Fin S) ℂ) * Matrix.fromBlocks 1 0 0 (b : Matrix (Fin S) (Fin S) ℂ) := by
      rw [Matrix.fromBlocks_multiply]; simp
    simp only [fD]
    rw [e]
    exact hmul _ _ (fromBlocks_mem R S _ _ h1R (unitary_ch a)) (fromBlocks_mem R S _ _ h1R (unitary_ch b))
  have hcD : Continuous fD := by
    refine hc.comp_continuous ?_ (fun a => fromBlocks_mem R S _ _ h1R (unitary_ch a))
    exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const continuous_subtype_val
  have hnD : ∀ a, ‖fD a‖ = 1 :=
    norm_eq_one_of_compact fD hmD hcD (hnz _ (fromBlocks_mem R S _ _ h1R (unitary_ch 1)))
  obtain ⟨y, hy⟩ := GlobalTheory.UpqChar.char_unitary fD hmD hnD hcD
  refine ⟨x, y, fun a d ha hd => ?_⟩
  have maU : a ∈ Matrix.unitaryGroup (Fin R) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact ha
  have mdU : d ∈ Matrix.unitaryGroup (Fin S) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact hd
  have e : Matrix.fromBlocks a 0 0 d = Matrix.fromBlocks a 0 0 (1 : Matrix (Fin S) (Fin S) ℂ) *
      Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) ℂ) 0 0 d := by
    rw [Matrix.fromBlocks_multiply]; simp
  rw [e, hmul _ _ (fromBlocks_mem R S _ _ ha h1S) (fromBlocks_mem R S _ _ h1R hd)]
  have hA := hx ⟨a, maU⟩
  have hD := hy ⟨d, mdU⟩
  simp only [fA, fD] at hA hD
  rw [hA, hD]

end GlobalTheory.KChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryHaarBallLowerBound
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.MatUnitIso

variable {k K B : Type} [Field k] [CommRing K] [Ring B] [Algebra k K] [Algebra k B]

def phiL {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B) :
    Matrix (Fin n) (Fin n) K →ₗ[k] B where
  toFun M := ∑ a, ∑ b, ι (M a b) * E a b
  map_add' M N := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.smul_sum, smul_mul_assoc]

theorem phiL_apply {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B) (M) :
    phiL ι E M = ∑ a, ∑ b, ι (M a b) * E a b := rfl

theorem core {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (M : Matrix (Fin n) (Fin n) K) (c a d e : Fin n) :
    E c a * phiL ι E M * E d e = ι (M a d) * E c e := by
  have h : ∀ a' b', E c a * (ι (M a' b') * E a' b') * E d e
      = if a = a' then (if b' = d then ι (M a d) * E c e else 0) else 0 := by
    intro a' b'
    rw [← mul_assoc, ← (hc (M a' b') (E c a)).eq]
    simp only [mul_assoc, hE, mul_ite, mul_zero]
    split_ifs with h1 h2
    · subst h1 h2; rw [mul_assoc, hE, if_pos rfl]
    · rw [mul_assoc, hE, if_neg h2, mul_zero]
    · rw [zero_mul]
  simp only [phiL_apply, Finset.mul_sum, Finset.sum_mul, h]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem extract {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (h1 : ∑ a, E a a = 1) (M : Matrix (Fin n) (Fin n) K) (a b : Fin n) :
    ∑ c, E c a * phiL ι E M * E b c = ι (M a b) := by
  simp only [core ι E hc hE, ← Finset.mul_sum, h1, mul_one]

theorem phiL_injective {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hi : Function.Injective ι) (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (h1 : ∑ a, E a a = 1) : Function.Injective (phiL ι E) := by
  intro M N h
  ext a b
  apply hi
  rw [← extract ι E hc hE h1 M a b, ← extract ι E hc hE h1 N a b, h]

theorem phiL_one {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (h1 : ∑ a, E a a = 1) : phiL ι E 1 = 1 := by
  simp [phiL_apply, Matrix.one_apply, h1]

theorem phiL_mul {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (M N : Matrix (Fin n) (Fin n) K) :
    phiL ι E (M * N) = phiL ι E M * phiL ι E N := by
  have h : ∀ a b c d, ι (M a b) * E a b * (ι (N c d) * E c d)
      = if b = c then ι (M a b * N b d) * E a d else 0 := by
    intro a b c d
    rw [mul_assoc, ← mul_assoc (E a b), ← (hc (N c d) (E a b)).eq, mul_assoc, hE,
      ← mul_assoc, ← map_mul]
    split_ifs with hbc
    · subst hbc; rfl
    · rw [mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [phiL_apply, Finset.sum_mul, Finset.mul_sum, h, Matrix.mul_apply, map_sum]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]

theorem matrixRingEquiv_of_matrixUnits : ∀ (k K B : Type) [Field k] [CommRing K] [Ring B] [Algebra k K] [Algebra k B] [FiniteDimensional k B] (n : ℕ) (ι : K →ₐ[k] B), Function.Injective ι → (∀ z x, Commute (ι z) x) → Module.finrank k B = n ^ 2 * Module.finrank k K → ∀ E : Fin n → Fin n → B, (∀ a b c d, E a b * E c d = if b = c then E a d else 0) → ∑ a, E a a = 1 → ∃ Φ : Matrix (Fin n) (Fin n) K ≃+* B, (∀ M, Φ M = ∑ a, ∑ b, ι (M a b) * E a b) ∧ ∀ x a b, ι (Φ.symm x a b) = ∑ c, E c a * x * E b c := by
  intro k K B _ _ _ _ _ _ n ι hi hc hdim E hE h1
  haveI : FiniteDimensional k K := FiniteDimensional.of_injective (ι : K →ₐ[k] B).toLinearMap hi
  have hinj := phiL_injective ι E hi hc hE h1
  have hrank : Module.finrank k (Matrix (Fin n) (Fin n) K) = Module.finrank k B := by
    rw [Module.finrank_matrix, hdim]; simp [Fintype.card_fin, sq]
  have hsurj : Function.Surjective (phiL ι E) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  let f : Matrix (Fin n) (Fin n) K →+* B :=
    { toFun := phiL ι E
      map_one' := phiL_one ι E h1
      map_mul' := phiL_mul ι E hc hE
      map_zero' := map_zero _
      map_add' := map_add _ }
  let Φ : Matrix (Fin n) (Fin n) K ≃+* B := RingEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨Φ, fun M => rfl, fun x a b => ?_⟩
  obtain ⟨M, rfl⟩ := hsurj x
  have hx : Φ.symm (phiL ι E M) = M := Φ.symm_apply_apply M
  rw [hx]
  exact (extract ι E hc hE h1 M a b).symm

end GlobalTheory.MatUnitIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb bas)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.FinChart
open scoped ContDiff ENNReal

namespace GlobalTheory

namespace FinChart

variable {D : ℕ}

theorem cHess_eq_hessC {f : V D → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f (toV D z)) :
    cHess D (fun v => (f v : ℂ)) (toV D z) = hessC (f ∘ toV D) z := by
  set x := toV D z with hx
  set H := fderiv ℝ (fderiv ℝ f) x with hH
  have hD : HasFDerivAt (fderiv ℝ f) H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have h₁ : fderiv ℝ (f ∘ toV D) =
      fun w => (fderiv ℝ f (toV D w)).comp (toV D).toContinuousLinearMap :=
    funext fun _ => (toV D).comp_right_fderiv
  have h₂ (u w : Fin D → ℂ) : fderiv ℝ (fderiv ℝ (f ∘ toV D)) z u w = H (toV D u) (toV D w) := by
    have := ((hD.comp z (toV D).hasFDerivAt).clm_comp
      (hasFDerivAt_const (toV D).toContinuousLinearMap z)).fderiv
    rw [h₁]
    erw [this]
    simp
  have hdiff := ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf
  set G : Fin D → V D → ℂ := fun l y => (2 : ℂ)⁻¹ *
    ((fderiv ℝ f y (bas D l) : ℂ) + Complex.I * (fderiv ℝ f y (Complex.I • bas D l) : ℂ))
  have hwdb (l) : wdb D l (fun y => (f y : ℂ)) =ᶠ[𝓝 x] G l := by
    filter_upwards [hdiff] with y hy
    simp only [wdb, G, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy]
    ring
  have hGd (l e) : fderiv ℝ (G l) x e =
      ((H e (bas D l) : ℂ) + Complex.I * (H e (Complex.I • bas D l) : ℂ)) / 2 := by
    have ha (b : V D) : HasFDerivAt (fun y => ((fderiv ℝ f y b : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((fderiv ℝ f x).comp (0 : V D →L[ℝ] V D) + H.flip b)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (hD.clm_apply (hasFDerivAt_const b x))
    have hG : HasFDerivAt (G l) _ x :=
      ((ha (bas D l)).add ((ha (Complex.I • bas D l)).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    rw [hG.fderiv]
    simp
    ring
  ext j l
  have b₁ (a : Fin D) : toV D (Pi.single a 1) = bas D a := rfl
  have b₂ (a : Fin D) : toV D (Complex.I • Pi.single a 1) = Complex.I • bas D a := rfl
  simp only [cHess, Matrix.of_apply, wd, (hwdb l).fderiv_eq, hGd, hessC, h₂, b₁, b₂]
  push_cast
  linear_combination (-(H (Complex.I • bas D j) (Complex.I • bas D l) : ℂ) / 4) * Complex.I_mul_I

theorem measurePreserving_toV : MeasurePreserving (toV D) :=
  MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
    (volume_preserving_ofLp_complex (Fin D))

end FinChart

section Abstract

variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem integrableOn_source_iff_of_density (c : OpenPartialHomeomorph X (Fin e → ℂ))
    {μ : Measure X} {w : (Fin e → ℂ) → ℝ} (hw : ContinuousOn w c.target)
    (hw0 : ∀ y ∈ c.target, 0 ≤ w y) (hμ : ∀ S, MeasurableSet S → S ⊆ c.source →
      μ S = ∫⁻ y in c.target ∩ c.symm ⁻¹' S, ENNReal.ofReal (w y))
    {g : X → ℝ} (hg : Measurable g) :
    (IntegrableOn g c.source μ ↔ IntegrableOn (fun y => g (c.symm y) * w y) c.target) ∧
      ∫ x in c.source, g x ∂μ = ∫ y in c.target, g (c.symm y) * w y := by
  have hT := c.open_target.measurableSet
  have key : μ.restrict c.source =
      ((volume.restrict c.target).withDensity fun y => ENNReal.ofReal (w y)).map c.symm := by
    ext S hS
    rw [Measure.restrict_apply hS, hμ _ (hS.inter c.open_source.measurableSet) inter_subset_right,
      Measure.map_apply_of_aemeasurable ((c.continuousOn_symm.aemeasurable hT).mono_ac
        (withDensity_absolutelyContinuous _ _)) hS, withDensity_apply',
      Measure.restrict_restrict' hT]
    congr 2
    ext y
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, c.map_target h.2⟩⟩
  rw [IntegrableOn, key]
  exact map_withDensity_integrable_integral c.open_target c.continuousOn_symm hw hw0 hg

theorem integrable_of_pieces (A : FinHolAtlas e X) (P : ChartPartition A) {μ : Measure X}
    {w : Fin A.n → (Fin e → ℂ) → ℝ} (hw : ∀ j, ContinuousOn (w j) (A.chart j).target)
    (hw0 : ∀ j, ∀ y ∈ (A.chart j).target, 0 ≤ w j y)
    (hμ : ∀ j S, MeasurableSet S → S ⊆ (A.chart j).source →
      μ S = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S, ENNReal.ofReal (w j y))
    {g : X → ℝ} (hg : Measurable g) (hi : ∀ j, IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w j y) (A.chart j).target) :
    Integrable g μ ∧ ∫ x, g x ∂μ = ∑ j, ∫ y in (A.chart j).target,
      P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w j y := by
  have hc (j) : Continuous (P.χ j) := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨l, hl⟩ := A.cover x
    have h₁ := ((P.smooth j l).continuousOn.mono fun y hy => ⟨hy, mem_univ _⟩).continuousAt
      ((A.chart l).open_target.mem_nhds ((A.chart l).map_source hl))
    refine (h₁.comp ((A.chart l).continuousAt hl)).congr ?_
    exact eventually_of_mem ((A.chart l).open_source.mem_nhds hl) fun z hz =>
      congrArg (P.χ j) ((A.chart l).left_inv hz)
  have key (j) := integrableOn_source_iff_of_density (A.chart j) (hw j) (hw0 j) (hμ j)
    ((hc j).measurable.mul hg)
  have h0 (j) (x) (hx : x ∉ (A.chart j).source) : P.χ j x * g x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (P.tsupport_subset j h), zero_mul]
  have h₁ (j) : Integrable (fun x => P.χ j x * g x) μ :=
    ((key j).1.2 (hi j)).integrable_of_forall_notMem_eq_zero (h0 j)
  have e : g = fun x => ∑ j, P.χ j x * g x := funext fun x => by
    rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
  refine ⟨e ▸ integrable_finsetSum _ fun j _ => h₁ j, ?_⟩
  conv_lhs => rw [e]
  rw [integral_finsetSum _ fun j _ => h₁ j]
  exact Finset.sum_congr rfl fun j _ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 j)).symm.trans (key j).2

end Abstract

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}
  {φ : Weight p σ B}

namespace Weight

theorem IsCInf.maDens_eq (h : φ.IsCInf) (c : AlgChart p σ D) {z : Fin D → ℂ}
    (hz : z ∈ c.finChart.target) :
    maDens (fun _ y => φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      c.chernDens φ (c.finChart.symm z) := by
  have hr : c.e (c.finChart.symm z) = toV D z := c.e.right_inv hz
  have hd := h.contDiffAt c (c.finChart.map_target hz) (mem_pick φ.isLB (c.finChart.symm z))
  rw [hr] at hd
  have e : (fun y => φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) = fun y => 2⁻¹ *
      ((fun v => φ.φ (pick φ.isLB (c.finChart.symm z)) (c.e.symm v)) ∘ toV D) y :=
    funext fun _ => div_eq_inv_mul _ _
  rw [maDens, ReciprocityTheory.AnForm.A.mdisc_const, e, hessC_const_mul', AlgChart.chernDens, AlgChart.hess,
    hr, cHess_eq_hessC hd, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Fintype.card_fin, ← mul_assoc, mul_assoc (D.factorial : ℝ), ← mul_pow, div_eq_mul_inv _ (_ ^ D),
    ← inv_pow]
  congr 3
  ring

variable {A : FinHolAtlas D (CxPts p σ)}

theorem IsCInf.locDens_eq (h : φ.IsCInf) (hA : IsAlgAtlas A) (j : Fin A.n) {z : Fin D → ℂ}
    (hz : z ∈ (A.chart j).target) : locDens A (fun _ => φ.locPot) j z =
      (hA.anRead.chart j).chernDens φ ((A.chart j).symm z) := by
  unfold locDens
  rw [hA.chart_eq j] at hz ⊢
  exact h.maDens_eq _ hz

theorem IsCInf.chernPart_eq [SecondCountableTopology (CxPts p σ)] (h : φ.IsCInf)
    (hA : IsAlgAtlas A) (ε : ℤˣ) (j : Fin A.n) (S : Set (CxPts p σ)) (hS : MeasurableSet S)
    (hs : S ⊆ (A.chart j).source) : φ.chernPart D ε S =
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S,
        ENNReal.ofReal (max ((ε : ℤ) * locDens A (fun _ => φ.locPot) j y) 0) := by
  have hl (y) := h.locDens_eq hA j (z := y)
  generalize locDens A (fun _ => φ.locPot) j = d at hl ⊢
  rw [hA.chart_eq j] at hs hl ⊢
  set c := hA.anRead.chart j
  have hm := measurableSet_image c.e hS hs
  rw [chernPart_apply h ε c hS hs, ← measurePreserving_toV.setLIntegral_comp_preimage_emb
    (toV D).toHomeomorph.measurableEmbedding]
  have e : c.e '' S = c.e.target ∩ c.e.symm ⁻¹' S := by
    rw [← c.e.image_source_inter_eq', inter_eq_right.2 (show S ⊆ c.e.source from hs)]
  rw [e] at hm ⊢
  refine setLIntegral_congr_fun (hm.preimage (toV D).continuous.measurable) fun y hy => ?_
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_le, max_eq_left, hl y hy.1]
  rfl

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)]

theorem IsCInf.chernInt_eq_mInt_of_isAlgAtlas (h : φ.IsCInf) (hA : IsAlgAtlas A)
    {g : CxPts p σ → ℝ} (hg : Measurable g) :
    (φ.ChernIntegrableOn D univ g ↔ MIntegrable A (fun _ => φ.locPot) g) ∧
      (φ.ChernIntegrableOn D univ g → φ.chernInt D univ g = mInt A (fun _ => φ.locPot) g) := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set P := hne.some
  set d := locDens A fun _ => φ.locPot with hd
  have hdc (j) : ContinuousOn (d j) (A.chart j).target := locDensCont A _
    (fun _ => ((isCInf_iff_isSmooth hA.anRead).1 h).isPotential hA) j
  let w (ε : ℤˣ) (j) (y) : ℝ := max ((ε : ℤ) * d j y) 0
  have hw (ε j) : ContinuousOn (w ε j) (A.chart j).target :=
    (continuous_id.max continuous_const).comp_continuousOn (continuousOn_const.mul (hdc j))
  have hw0 (ε j) : ∀ y ∈ (A.chart j).target, 0 ≤ w ε j y := fun _ _ => le_max_right _ _
  have hsub (j y) : w 1 j y - w (-1) j y = d j y := by
    simpa [w] using max_zero_sub_max_neg_zero_eq_self (d j y)
  have habs (ε j y) : |w ε j y| ≤ |d j y| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ((le_abs_self _).trans_eq ?_) (abs_nonneg _)
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have back (hm : MIntegrable A (fun _ => φ.locPot) g) (ε j) : IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w ε j y)
      (A.chart j).target := by
    obtain ⟨hKc, hKs⟩ := image_closed_compact (A.chart j) (isClosed_tsupport (P.χ j))
      (P.tsupport_subset j)
    refine integrableOn_target_of_closed (A.chart j) (Z := tsupport (P.χ j))
      (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
    have hcc := (chi_comp_continuousOn P j).mono hKs
    refine Integrable.mono ((hm j _ hKs hKc).continuousOn_mul hcc hKc) ?_ (.of_forall fun y => ?_)
    · exact (((hcc.aemeasurable hKc.measurableSet).mul (hg.comp_aemeasurable
        (((A.chart j).continuousOn_symm.mono hKs).aemeasurable hKc.measurableSet))).mul
        (((hw ε j).mono hKs).aemeasurable hKc.measurableSet)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (habs ε j y) (by positivity)
  have pieces (hm : MIntegrable A (fun _ => φ.locPot) g) (ε) :=
    integrable_of_pieces A P (hw ε) (hw0 ε) (h.chernPart_eq hA ε) hg (back hm ε)
  have fwd (hi : φ.ChernIntegrableOn D univ g) : MIntegrable A (fun _ => φ.locPot) g :=
    fun j K hK _ => by
    have key (ε) := (integrableOn_source_iff_of_density (A.chart j) (hw ε j) (hw0 ε j)
      (h.chernPart_eq hA ε j) hg).1.1
    refine IntegrableOn.mono_set ?_ hK
    refine (Integrable.sub (key 1 (hi.1.mono_set (subset_univ _)))
      (key (-1) (hi.2.mono_set (subset_univ _)))).congr (.of_forall fun y => ?_)
    simp only [Pi.sub_apply, ← mul_sub, hsub, hd]
  refine ⟨⟨fwd, fun hm => ⟨(pieces hm 1).1.integrableOn, (pieces hm (-1)).1.integrableOn⟩⟩,
    fun hi => ?_⟩
  have hm := fwd hi
  rw [chernInt, Measure.restrict_univ, Measure.restrict_univ, (pieces hm 1).2, (pieces hm (-1)).2,
    mInt, dif_pos hne, integralWith, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (back hm 1 j) (back hm (-1) j)]
  simp only [← mul_sub, hsub, hd, P]

theorem chernInt_eq_mInt (R : AnRead p σ D) (h : φ.IsCInf) {g : CxPts p σ → ℝ}
    (hg : Measurable g) :
    (φ.ChernIntegrableOn D univ g ↔ MIntegrable R.finAtlas (fun _ => φ.locPot) g) ∧
      (φ.ChernIntegrableOn D univ g →
        φ.chernInt D univ g = mInt R.finAtlas (fun _ => φ.locPot) g) :=
  h.chernInt_eq_mInt_of_isAlgAtlas R.isAlgAtlas_finAtlas hg

end Weight

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdicCompletionGLDiagonalPoweStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_adicCompletionGL_diagonalPowers : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ g : GL (Fin a) (w.adicCompletion E), ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w (n := a), g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k := by
  first | exact @GlobalTheory.IwasawaGL.iwasawa_diagPow | exact GlobalTheory.IwasawaGL.iwasawa_diagPow | (intros; apply GlobalTheory.IwasawaGL.iwasawa_diagPow <;> assumption)
end

