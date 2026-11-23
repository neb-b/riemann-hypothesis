module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0218
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0220
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0104
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0215
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0216
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChainPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0161
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointInChart
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section wirt1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def dz (f : ℂ → E) (τ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f τ 1 - Complex.I • fderiv ℝ f τ Complex.I)

def dzb (f : ℂ → E) (τ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + Complex.I • fderiv ℝ f τ Complex.I)

theorem hasFDerivAt_norm1 {τ : ℂ} (hτ : τ ≠ 0) :
    HasFDerivAt (fun σ : ℂ => ‖σ‖) ((1 / (2 * Real.sqrt (‖τ‖ ^ 2))) • (2 • innerSL ℝ τ)) τ := by
  have h2 : HasFDerivAt (fun σ : ℂ => ‖σ‖ ^ 2) (2 • innerSL ℝ τ) τ := (hasStrictFDerivAt_norm_sq τ).hasFDerivAt
  have h1 := h2.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.2 hτ))
  have e : (fun σ : ℂ => Real.sqrt (‖σ‖ ^ 2)) = fun σ => ‖σ‖ := funext fun σ => Real.sqrt_sq (norm_nonneg σ)
  rw [e] at h1
  exact h1

theorem fderiv_norm_apply {τ : ℂ} (hτ : τ ≠ 0) (v : ℂ) :
    fderiv ℝ (fun σ : ℂ => ‖σ‖) τ v = ‖τ‖⁻¹ * (τ.re * v.re + τ.im * v.im) := by
  rw [(hasFDerivAt_norm1 hτ).fderiv]
  have hs : Real.sqrt (‖τ‖ ^ 2) = ‖τ‖ := Real.sqrt_sq (norm_nonneg τ)
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, hs, smul_eq_mul, Complex.inner, nsmul_eq_mul]
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  simp only [Complex.conj_re, Complex.conj_im, Complex.mul_re]
  field_simp
  ring

theorem normPow_deriv_apply {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) (v : ℂ) :
    fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ v =
      (n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * (τ.re * v.re + τ.im * v.im)) := by
  rw [((hasFDerivAt_norm1 hτ).pow n).fderiv]
  rw [← (hasFDerivAt_norm1 hτ).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, fderiv_norm_apply hτ]

theorem gauge_scalar {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) :
    τ * (1 / 2) * ((((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ) -
        Complex.I * (((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
      ((‖τ‖ ^ n : ℝ) : ℂ) * ((n : ℂ) / 2) := by
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  have hconj : τ * ((τ.re : ℂ) - Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
    have := Complex.mul_conj τ
    rw [Complex.normSq_eq_norm_sq] at this
    rw [← this]
    congr 1
    apply Complex.ext <;> simp
  rcases n with _ | m
  · simp
  · have e : τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) -
        Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
        (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (τ * ((τ.re : ℂ) - Complex.I * τ.im)) := by
      push_cast
      ring
    rw [e, hconj]
    push_cast
    field_simp
    ring

theorem dz_gauge {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) {f : ℂ → E} (hf : DifferentiableAt ℝ f τ) :
    τ • dz (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) τ =
      ((‖τ‖ ^ n : ℝ) : ℂ) • (τ • dz f τ + ((n : ℂ) / 2) • f τ) := by
  have hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ :=
    Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt
  have hP := hN.smul hf.hasFDerivAt
  have hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f := rfl
  unfold dz
  rw [hfun, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]
  have key := gauge_scalar hτ n
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *
  linear_combination (norm := module) key • f τ

theorem gauge_scalar_bar {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) :
    conj τ * (1 / 2) * ((((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ) +
        Complex.I * (((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
      ((‖τ‖ ^ n : ℝ) : ℂ) * ((n : ℂ) / 2) := by
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  have hconj : conj τ * ((τ.re : ℂ) + Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
    have := Complex.mul_conj τ
    rw [Complex.normSq_eq_norm_sq, mul_comm] at this
    rw [← this]
    congr 1
    apply Complex.ext <;> simp
  rcases n with _ | m
  · simp
  · have e : conj τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) +
        Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
        (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (conj τ * ((τ.re : ℂ) + Complex.I * τ.im)) := by
      push_cast
      ring
    rw [e, hconj]
    push_cast
    field_simp
    ring

theorem dzb_gauge {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) {f : ℂ → E} (hf : DifferentiableAt ℝ f τ) :
    conj τ • dzb (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) τ =
      ((‖τ‖ ^ n : ℝ) : ℂ) • (conj τ • dzb f τ + ((n : ℂ) / 2) • f τ) := by
  have hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ :=
    Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt
  have hP := hN.smul hf.hasFDerivAt
  have hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f := rfl
  unfold dzb
  rw [hfun, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]
  have key := gauge_scalar_bar hτ n
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *
  linear_combination (norm := module) key • f τ

end wirt1

section read0

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def pt0 {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) : Fin n → ℂ := fun l => PBH.consC τ c (Fin.cast hn.symm l)

def Lz {n : ℕ} : ℂ →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun l : Fin n => if l.val = 0 then ContinuousLinearMap.id ℝ ℂ else 0

theorem Lz_apply {n : ℕ} (h0 : 0 < n) (v : ℂ) : (Lz (n := n)) v = Pi.single ⟨0, h0⟩ v := by
  funext l
  by_cases hl : l.val = 0
  · have : l = ⟨0, h0⟩ := Fin.ext hl
    subst this
    simp [Lz]
  · have : l ≠ ⟨0, h0⟩ := fun h => hl (by rw [h])
    simp [Lz, hl, this]

theorem hasFDerivAt_base_point {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) :
    HasFDerivAt (pt0 hn c) (Lz (n := n)) τ := by
  have e : pt0 hn c = fun σ => Lz (n := n) σ + pt0 hn c 0 := by
    funext σ l
    show PBH.consC σ c (Fin.cast hn.symm l) = (Lz (n := n)) σ l + PBH.consC 0 c (Fin.cast hn.symm l)
    by_cases hl : l.val = 0
    · simp [PBH.consC, Lz, hl]
    · simp [PBH.consC, Lz, hl]
  rw [e]
  exact (Lz (n := n)).hasFDerivAt.add_const _

theorem base_point_zero_coord {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) :
    pt0 hn c τ ⟨0, by omega⟩ = τ := by
  simp [pt0, PBH.consC]

theorem pointWithZeroSecondCoord_mem_chart_of_restricted {n ρ : ℕ} (hn : 1 + ρ = n) {c : Fin ρ → ℂ} (hc : c ∈ OmX ρ) {τ : ℂ} (hτ : τ ≠ 0) :
    pt0 hn c τ ∈ OmX n := by
  subst hn
  have e : pt0 rfl c τ = PBH.consC τ c := funext fun l => by simp [pt0]
  rw [e]
  exact (PBH.omX_consC hτ c).2 hc

theorem operators_at_base_point {n ρ : ℕ} (hn : 1 + ρ = n) {c : Fin ρ → ℂ} (hc : c ∈ OmX ρ) {τ : ℂ} (hτ : τ ≠ 0)
    (f : (Fin n → ℂ) → E) (hf : DifferentiableAt ℝ f (pt0 hn c τ)) :
    opL (⟨0, by omega⟩ : Fin n) 0 f (pt0 hn c τ) = τ • dz (fun σ => f (pt0 hn c σ)) τ ∧
    opL (⟨0, by omega⟩ : Fin n) 1 f (pt0 hn c τ) = τ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 2 f (pt0 hn c τ) = τ⁻¹ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 3 f (pt0 hn c τ) = conj τ • dzb (fun σ => f (pt0 hn c σ)) τ ∧
    opL (⟨0, by omega⟩ : Fin n) 4 f (pt0 hn c τ) = conj τ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 5 f (pt0 hn c τ) = (conj τ)⁻¹ • f (pt0 hn c τ) := by
  have hmem := pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ
  have h0 := base_point_zero_coord hn c τ
  have hd : ∀ v, fderiv ℝ (fun σ => f (pt0 hn c σ)) τ v = fderiv ℝ f (pt0 hn c τ) (Pi.single ⟨0, by omega⟩ v) := by
    intro v
    have h := (hf.hasFDerivAt.comp τ (hasFDerivAt_base_point hn c τ)).fderiv
    change fderiv ℝ (f ∘ pt0 hn c) τ v = _
    rw [h, ContinuousLinearMap.comp_apply, Lz_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show pOp _ f _ = _
    unfold pOp
    rw [if_pos hmem, h0]
    unfold wirt dz
    rw [hd, hd]
  · show cOp _ f _ = _
    simp only [cOp, h0]
  · show ciOp _ f _ = _
    simp only [ciOp, h0]
  · show pbOp _ f _ = _
    unfold pbOp
    rw [if_pos hmem, h0]
    unfold wirtBar dzb
    rw [hd, hd]
    rfl
  · show cbOp _ f _ = _
    simp only [cbOp, h0]
    rfl
  · show cbiOp _ f _ = _
    simp only [cbiOp, h0]
    rfl

end read0

end Formalism.FourierDecayAlt.P.PBP
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFP
section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutFP

def GoodFnLeaf : Prop :=
  ∀ (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (π : Q.Mx k ρ → (Wp →L[ℂ] Wp)) (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)),
    0 ≤ Tz k ρ z * Tz k ρ z' → ∀ (X : Q.ActualOps k ρ z z' π π') (j : Fin 6), ParameterFamilyAlgebra.Good z z' π π' (X.fn j)

def GoodTLeaf : Prop :=
  ∀ (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (π : Q.Mx k ρ → (Wp →L[ℂ] Wp)) (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)),
    (∀ c : Fin ρ → ℂ, c ∈ OmX ρ) → (∀ c c' : Fin ρ → ℂ, c = c') →
    ∀ (X : Q.ActualOps k ρ z z' π π') (Y : ℂ) (a b : Fin 2), ParameterFamilyAlgebra.Good z z' π π' (X.t Y a b)

section Asm

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gens_good (hfn : GoodFnLeaf) (ht : GoodTLeaf) (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (hD : IsData P z z' π π' X μ L st l0)
    (hOm : ∀ c : Fin P.r → ℂ, c ∈ OmX P.r) (hS : ∀ c c' : Fin P.r → ℂ, c = c') :
    HerA.Gens (ParameterFamilyAlgebra.goodAlg z z' π π') L st := by
  obtain ⟨κ, hx, hxi, -⟩ :=
    xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hT : 0 ≤ Tz P.k P.r z * Tz P.k P.r z' := Formalism.FourierDecayAlt.P.Qx5.place_alt_alt hD.1
  obtain ⟨-, -, hAL, hQQ, -, -, -, hst⟩ := hD
  have hF : ∀ i j, Q.mkP (X.fn i) (X.fn j) ∈ ParameterFamilyAlgebra.goodAlg z z' π π' := fun i j =>
    ParameterFamilyAlgebra.good_mkP (hfn P.k P.r z z' Wp Wq π π' hT X i) (hfn P.k P.r z z' Wp Wq π π' hT X j)
  have hz : ∀ g ∈ zfns L, g ∈ ParameterFamilyAlgebra.goodAlg z z' π π' := by
    obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4, h5, h6, -⟩ := hAL
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h1]; exact hF _ _
    · rw [h2]; exact hF _ _
    · rw [h3]; exact hF _ _
    · rw [h4]; exact hF _ _
    · rw [h5]; exact hF _ _
    · rw [h6]; exact hF _ _
  have hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ ParameterFamilyAlgebra.goodAlg z z' π π' := by
    intro Y _ i j
    rw [hQQ Y, Matrix.smul_apply]
    refine (ParameterFamilyAlgebra.goodAlg z z' π π').smul_mem ?_ _
    exact ParameterFamilyAlgebra.good_mkP (ht P.k P.r z z' Wp Wq π π' hOm hS X Y i j) (ht P.k P.r z z' Wp Wq π π' hOm hS X _ j i)
  exact HerA.gens_of _ L st hst κ _ hx hxi hz hQ

theorem frameParam_of (hfn : GoodFnLeaf) (ht : GoodTLeaf) : PBI.FrameParam := by
  intro Wp Wq _ _ _ _ _ _ P p X μ L st hD w hA Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  have hr0 : ∀ l : Fin (JC.parLev P P.r).r, False := fun l => by
    have := l.isLt
    simp only [JC.parLev, Nat.sub_self] at this
    omega
  have hOm : ∀ c : Fin (JC.parLev P P.r).r → ℂ, c ∈ OmX (JC.parLev P P.r).r := fun c l => (hr0 l).elim
  have hS : ∀ c c' : Fin (JC.parLev P P.r).r → ℂ, c = c' := fun c c' => funext fun l => (hr0 l).elim
  have hg := gens_good hfn ht (JC.parLev P P.r) _ _ _ _ X μ L st p.l0 hD hOm hS
  have hent : ∀ e e', ParameterFamilyAlgebra.Good _ _ _ _ ((Fr.ofWord L st (D.positionted w)).F e e').1 := fun e e' =>
    ((HerA.frameAlg L st hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2 hg (D.positionted w) hA e e').1).1
  have key := fun e b => hent e b Par U₀ hU₀ hUpos (fun Z => Ψ Z b) (fun Z y => Ψf Z b y)
    (fun Z c y hy => hR Z b c y hy) (hF b)
  choose Φ hΦR hΦF hΦS hΦW using key
  refine ⟨fun Z e y => ∑ b, Φ e b Z y, ?_, ?_, ?_, ?_⟩
  · intro Z e c y hy
    simp only [P5.act, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => hΦR e b Z c y hy
  · intro e
    exact ParameterFamilyAlgebra.parFam_sum _ fun b _ => hΦF e b
  · intro K hK e q hq hG hqK
    exact Finset.sum_eq_zero fun b _ => hΦS e b K (fun q' hG' hq' => hK b q' hG' hq') q hq hG hqK
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi e c
    simp only [P5.act, Submodule.coe_sum, Finset.sum_apply]
    rw [integral_finsetSum _ (fun b _ => ParameterFamilyAlgebra.parFam_integrable (hΦF e b) hKp hν hyG
      (fun Z hZ => hKV ⟨hZ, hyV⟩))]
    exact Finset.sum_congr rfl fun b _ => hΦW e b ν Kp hKp hν (Ψi b) y V hV hyV hyG hKV
      (fun c' y' hy' hG' => hi b c' y' hy' hG') c

end Asm

end Formalism.FourierDecayAlt.P.CutFP
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapFinal
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem datum_bound_holds : DatumBd := datumBd_of_chain SSn.ChainPf.chain_bound_holds

theorem jABddKapQQ_of_leaves (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_typeProj datum_bound_holds hG hP

theorem jABddKapQQ_of_cut (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) (hNW : NrmWFacts) : JABddKapQQ :=
  jABddKapQQ_of_leaves hG (typeProj_of hPE hGL hDU hNW)

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem kap_Dw_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    PI.UnitaryGroupMassFormula.GsFr.Dw k r * B2.embWb k r μ = B2.embWb k r μ * PI.UnitaryGroupMassFormula.GsFr.Dw k r := by
  ext i j
  simp only [PI.UnitaryGroupMassFormula.GsFr.Dw, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : TwoByOneBlock.mid k r i <;> by_cases hj : TwoByOneBlock.mid k r j
  · have hi' : (r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : (r ≤ j.val ∧ j.val ≤ r + k) := hj
    simp [hi', hj']
  · have hi' : (r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : ¬(r ≤ j.val ∧ j.val ≤ r + k) := hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [TwoByOneBlock.emb_out_col μ i j hj]
    simp [hi', hj', hij]
  · have hi' : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : (r ≤ j.val ∧ j.val ≤ r + k) := hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [TwoByOneBlock.emb_out_row μ i j hi]
    simp [hi', hj', hij]
  · have hi' : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : ¬(r ≤ j.val ∧ j.val ≤ r + k) := hj
    simp [hi', hj']

theorem wbP_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.wbP k r (h *ᵥ v) = h *ᵥ SSn.wbP k r v := by
  obtain ⟨η, -, -, rfl⟩ := (TwoByOneBlock.UWset_iff hz h).1 hh
  have e : ∀ w, SSn.wbP k r w = PI.UnitaryGroupMassFormula.GsFr.Dw k r *ᵥ w := fun w => by
    rw [PI.UnitaryGroupMassFormula.GsFr.Dw_mulVec]; rfl
  rw [e, e, Matrix.mulVec_mulVec, kap_Dw_emb, ← Matrix.mulVec_mulVec]

theorem kap_prWv_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (h *ᵥ v) = h *ᵥ SSn.prWv k r z v := by
  have hz' : h *ᵥ z = z := hh.2.2
  have hherm : herm (Hpk k r) (h *ᵥ SSn.wbP k r v) z = herm (Hpk k r) (SSn.wbP k r v) z := by
    conv_lhs => rw [← hz']
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1 _ _
  unfold SSn.prWv
  rw [wbP_mulVec hz hh, Matrix.mulVec_add, Matrix.mulVec_smul, hz', hherm]

theorem kap_nrmW_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (a : Fin (2 * r + k + 1) → ℂ) :
    PRho.nrmW k r z (h *ᵥ a) = PRho.nrmW k r z a := by
  unfold PRho.nrmW
  rw [kap_prWv_mulVec hz hh, Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1]

theorem kap_mulVec_contDiff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Fin n → ℂ => M *ᵥ a) := by
  have h := ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).contDiff
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).restrict_scalars ℝ
  convert h using 1
  funext a
  rfl

theorem kap_herm_contDiff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Fin n → ℂ => herm H u u) := by
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (starRingEnd ℂ) := Complex.conjCLE.contDiff
  have e : (fun u : Fin n → ℂ => herm H u u) = fun u => ∑ i, starRingEnd ℂ (u i) * (H *ᵥ u) i := by
    funext u; simp [herm, dotProduct, Complex.star_def]
  rw [e]
  refine ContDiff.sum fun i _ => ?_
  exact (hconj.comp (contDiff_apply ℝ (fun _ => ℂ) i)).mul ((contDiff_apply ℝ (fun _ => ℂ) i).comp (kap_mulVec_contDiff H))

theorem kap_nrmW_contDiff (z : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => PRho.nrmW k r z a) := by
  have e : (fun a => PRho.nrmW k r z a) =
      fun a => (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.Pm k r z *ᵥ a) (PI.UnitaryGroupMassFormula.GsFr.Pm k r z *ᵥ a)).re := by
    funext a; unfold PRho.nrmW; rw [PI.UnitaryGroupMassFormula.GsFr.Pm_mulVec]; rfl
  rw [e]
  exact Complex.reCLM.contDiff.comp ((kap_herm_contDiff (Hpk k r)).comp (kap_mulVec_contDiff _))

theorem weighted_norm_facts_hold : NrmWFacts := fun k r z hz _ =>
  ⟨kap_nrmW_contDiff z, fun _ hh a => kap_nrmW_mulVec hz hh a⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnFinal
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

theorem sSnRealiser_of (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : SSnRealiser :=
  sSnAssemble_of (JA.datumCompose_of (JA.datumBd_of_chain hCh)) hG hR

theorem jABddSSnQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnQQ :=
  jABddSSnQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

theorem jABddSSnStarQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnStarQQ :=
  jABddSSnStarQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjInt
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

theorem adjoint_integral_identity_holds : AdjInt := adjInt_of_parts hermitian_curvature_adjoint_integral unitary_rho_holds form_adjoint_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

