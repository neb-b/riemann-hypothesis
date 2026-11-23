module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarScaling
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HaarScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem haar_smul {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (c : ℝ≥0) (hc : 0 < c) :
    IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.conc, smul_zero]
  · intro a ha
    have hcont : Continuous (lmulM a : Mt k r → Mt k r) := by
      unfold lmulM
      exact (continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h.left a ha]
  · intro a ha
    have hcont : Continuous (rmulF a) := by
      unfold rmulF
      exact (continuous_id (X := Mat k r)).matrix_mul continuous_const
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h.right a ha]
  · intro K hK
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  · intro h0
    apply h.ne_zero
    have h1 : (c • μ) Set.univ = 0 := by rw [h0]; rfl
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (by exact_mod_cast h2 : c = 0) hc.ne'
    · exact Measure.measure_univ_eq_zero.mp h2

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def scaleG (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) : RealPlaceData k r Wp Wq :=
  { D with μG := c • D.μG, haarG := haar_smul D.haarG c hc }

theorem iteratedDeriv_two_const_mul (c : ℂ) (f : ℝ → ℂ) :
    iteratedDeriv 2 (fun x => c * f x) = fun x => c * iteratedDeriv 2 f x := by
  have h2 : ∀ g : ℝ → ℂ, iteratedDeriv 2 g = deriv (deriv g) := by
    intro g
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h2, deriv_const_mul_field', deriv_const_mul_field']

theorem oneMinusDD_const_mul (c : ℂ) (h : ℝ → ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * h a b) t₁ t₂ = c * oneMinusDD h t₁ t₂ := by
  simp only [oneMinusDD, iteratedDeriv_two_const_mul, ← mul_sub]

variable [FiniteDimensional ℂ Wq]

theorem ph_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) :
    Ph (scaleG D c hc) F F' p = ((c : ℝ) : ℂ) * Ph D F F' p := by
  have hμ : (scaleG D c hc).μG = c • D.μG := rfl
  unfold Ph
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rfl

theorem betaInf_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    betaInf (scaleG D c hc) F F' = ((c : ℝ) : ℂ) * betaInf D F F' := by
  have hreg : ∀ p, regBracket (scaleG D c hc) F F' p =
      fun a b => ((c : ℝ) : ℂ) * regBracket D F F' p a b := by
    intro p
    funext a b
    have hχ : (scaleG D c hc).χ = D.χ := rfl
    simp only [regBracket]
    rw [ph_scale, hχ]
    ring
  have hz : (scaleG D c hc).z = D.z := rfl
  have hz' : (scaleG D c hc).z' = D.z' := rfl
  have hS : (scaleG D c hc).μSS = D.μSS := rfl
  unfold betaInf betaInfTau
  simp only [hreg, hz, hz', hS, oneMinusDD_const_mul, mul_assoc, integral_const_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

theorem beta_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    beta (scaleG D c hc) F F' = beta D F F' := rfl

end

end Formalism.FourierDecayAlt.P.HaarScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.HaarScaling

theorem lemma_b_normalised_of_parts : Formalism.FourierDecayAlt.B2.LemmaBNormFromParts := by
  intro hC hJ hD hI k r Wp Wq _ _ _ _ _ _ D A hA hF
  exact hC k r Wp Wq D A hA hF (hJ k r Wp Wq D) (hD k r Wp Wq D) (hI k r Wp Wq D A hA)

theorem lemma_b_any_measure_from_normalised : Formalism.FourierDecayAlt.B2.LemmaBAnyFromNorm := by
  intro hN hB k r Wp Wq _ _ _ _ _ _ D A hA
  obtain ⟨c, ⟨hc, hF⟩, -⟩ := hB k r Wp Wq D
  have hF' : IntFormula (scaleG D c hc) := hF
  obtain ⟨h1, h2, h3, h4⟩ := hN k r Wp Wq (scaleG D c hc) A hA hF'
  refine ⟨c, hc, hF, h1, ?_, ?_, h4⟩
  · intro F F' hF1 hF2
    rw [← beta_scale D c hc F F', h2 F F' hF1 hF2, betaInf_scale]
  · intro UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4 hIC
    exact h3 UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4
      (fun p hp T hT i j hij hj => (hIC p hp T hT i j hij hj).smul_measure_nnreal)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.HaarScaling

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end Formalism.FourierDecayAlt.P.HaarScaling
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HsInnerAddSmulRight
section
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_add_smul_left (A A' C : Wq →L[ℂ] Wp) (a : ℂ) :
    B.hsInner (A + a • A') C = B.hsInner A C + a * B.hsInner A' C := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, inner_add_right, inner_smul_right, Finset.sum_add_distrib, Finset.mul_sum]

theorem hsInner_add_smul_right (A C C' : Wq →L[ℂ] Wp) (a : ℂ) :
    B.hsInner A (C + a • C') = B.hsInner A C + conj a * B.hsInner A C' := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, inner_add_left, inner_smul_left, Finset.sum_add_distrib, Finset.mul_sum]

end HS

section Forms

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_add_smul (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x x' : Ix S → RadSp k r z z' π π') (a : ℂ) :
    act M (x + a • x') = act M x + a • act M x' := by
  funext e
  simp only [act, Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul, Finset.sum_add_distrib, Finset.smul_sum]

theorem pairAt_add_smul_left (μ : Measure (Mt k r)) (Φ Φ' Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ)
    (h1 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ)
    (h2 : Integrable (fun g : Mt k r => B.hsInner ((Φ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ) :
    pairAt μ (Φ + a • Φ') Ψ c = pairAt μ Φ Ψ c + a * pairAt μ Φ' Ψ c := by
  unfold pairAt
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hsInner_add_smul_left]
  rw [integral_add h1 (h2.const_mul a), integral_const_mul]

theorem pairAt_add_smul_right (μ : Measure (Mt k r)) (Φ Ψ Ψ' : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ)
    (h1 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ)
    (h2 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ) :
    pairAt μ Φ (Ψ + a • Ψ') c = pairAt μ Φ Ψ c + conj a * pairAt μ Φ Ψ' c := by
  unfold pairAt
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hsInner_add_smul_right]
  rw [integral_add h1 (h2.const_mul (conj a)), integral_const_mul]

theorem form_add_smul_left (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u u' y : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ)
    (hin : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hin' : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u' b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hout : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y b) (glue i c c')))
    (hout' : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u' b) (y b) (glue i c c'))) :
    form μ i (u + a • u') y c = form μ i u y c + a * form μ i u' y c := by
  unfold form
  have hpt : (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ ((u + a • u') b) (y b) (glue i c c')) =
      fun c' => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y b) (glue i c c') +
        a * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u' b) (y b) (glue i c c')) := by
    funext c'
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_congr rfl fun b _ => pairAt_add_smul_left μ (u b) (u' b) (y b) _ a (hin c' b) (hin' c' b),
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hpt, integral_add hout (hout'.const_mul a), integral_const_mul]

theorem form_add_smul_right (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u y y' : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ)
    (hin : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hin' : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y' b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hout : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y b) (glue i c c')))
    (hout' : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y' b) (glue i c c'))) :
    form μ i u (y + a • y') c = form μ i u y c + conj a * form μ i u y' c := by
  unfold form
  have hpt : (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) ((y + a • y') b) (glue i c c')) =
      fun c' => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y b) (glue i c c') +
        conj a * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y' b) (glue i c c')) := by
    funext c'
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_congr rfl fun b _ => pairAt_add_smul_right μ (u b) (y b) (y' b) _ a (hin c' b) (hin' c' b),
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hpt, integral_add hout (hout'.const_mul (conj a)), integral_const_mul]

end Forms

theorem formSesqOfInt : FormSesqOfInt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st l0 K hI w hw i c hc x hx x' hx' y hy a
  have hK : ∀ v : Ix S → RadSp P.k P.r z z' π π', v ∈ Submodule.pi Set.univ (fun _ : Ix S => K i) → InK (K i) v :=
    fun v hv b => (Submodule.mem_pi.mp hv) b (Set.mem_univ b)
  have h1 := hI w hw i c hc x y (hK x hx) (hK y hy)
  have h2 := hI w hw i c hc x' y (hK x' hx') (hK y hy)
  have h3 := hI w hw i c hc y x (hK y hy) (hK x hx)
  have h4 := hI w hw i c hc y x' (hK y hy) (hK x' hx')
  constructor
  · show form μ i (act (RRi L st i w) (x + a • x')) y c =
      form μ i (act (RRi L st i w) x) y c + a * form μ i (act (RRi L st i w) x') y c
    rw [act_add_smul]
    exact form_add_smul_left μ i _ _ y c a h1.1 h2.1 h1.2 h2.2
  · show form μ i (act (RRi L st i w) y) (x + a • x') c =
      form μ i (act (RRi L st i w) y) x c + conj a * form μ i (act (RRi L st i w) y) x' c
    exact form_add_smul_right μ i _ x x' c a h3.1 h4.1 h3.2 h4.2

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x6

open C2x5

variable {k r : ℕ}

lemma herm_ff {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) = C2.Adiag k r z a b := by
  rw [ggBlockA k r z hz a b, hzz_real]
  simp only [C2.Adiag, ggLastU, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
  · subst ha hb; simp
  · simp [ha, hb, Ne.symm hb, show a ≠ b from fun h => hb (h ▸ ha)]
  · simp [ha, hb, show a ≠ b from fun h => ha (h ▸ hb)]
  · by_cases hab : a = b
    · subst hab; simp [ha]
    · simp [ha, hab]

lemma E_cast {n : ℕ} (x : Fin n → ℂ) : star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

lemma E_unit {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) (v : Fin n → ℂ) :
    ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  apply Complex.ofReal_injective
  rw [← E_cast (H *ᵥ v), ← E_cast v, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec]

lemma euclid_cs {n : ℕ} (a b : Fin n → ℂ) :
    Complex.normSq (star b ⬝ᵥ a) ≤ (∑ i, Complex.normSq (a i)) * (∑ i, Complex.normSq (b i)) := by
  have h1 : ‖star b ⬝ᵥ a‖ ≤ ∑ i, ‖b i‖ * ‖a i‖ := by
    rw [dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Pi.star_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖b i‖) (fun i => ‖a i‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖star b ⬝ᵥ a‖ ^ 2 ≤ (∑ i, ‖b i‖ * ‖a i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖a i‖ ^ 2) := h2
    _ = (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := mul_comm _ _

lemma Hpk_mul_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * M) i j = GBasic.sgn k r i * M (GBasic.sig k r i) j := by
  rw [Matrix.mul_apply]
  simp [GBasic.Hpk_eq]

lemma mul_Hpk_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (M * Hpk k r) i j = M i (GBasic.sig k r j) * GBasic.sgn k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (GBasic.sig k r j)]
  · rw [GBasic.Hpk_eq, if_pos (GBasic.sig_sig k r j).symm, GBasic.sgn_sig]
  · intro l _ hl
    rw [GBasic.Hpk_eq, if_neg, mul_zero]
    intro h
    exact hl (by rw [h, GBasic.sig_sig])
  · simp

lemma normSq_sgn (i : Fin (2 * r + k + 1)) : Complex.normSq (GBasic.sgn k r i) = 1 := by
  unfold GBasic.sgn
  split_ifs <;> simp

end C2x6

open C2x5 C2x6

theorem gram_block_form : C2.GramBlocks := by
  intro k r z z' hz hz' g hg
  have hH := GBasic.Hpk_herm k r

  have hpres : ∀ v w, herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
    intro v w
    simp only [herm]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, show gᴴ * Hpk k r * g = Hpk k r from hg]
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₁]
    exact herm_ff hz.1 a b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [ggHerm_swap _ hH]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₂]
    rw [hpres]
    exact herm_ff hz'.1 a b

theorem majorant_estimate : C2.Majorant := by
  intro k r
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  refine ⟨?_, hsq, fun v => ⟨?_, ?_⟩⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hH, hsq, Matrix.one_mul]
  · simp only [herm]
    rw [E_cast, E_unit _ hH hsq]
  · have hcs := euclid_cs (Hpk k r *ᵥ v) v
    rw [E_unit _ hH hsq] at hcs
    set S := ∑ i, Complex.normSq (v i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have h1 : ‖herm (Hpk k r) v v‖ ^ 2 ≤ S ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, sq]
      exact hcs
    have h2 : ‖herm (Hpk k r) v v‖ ≤ S := (pow_le_pow_iff_left₀ (norm_nonneg _) hS two_ne_zero).mp h1
    exact (Complex.re_le_norm _).trans h2

theorem norm_of_inverse : C2.NormInv := by
  intro k r g hg
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg

  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hsq]
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hleft
  have hright : g * g⁻¹ = 1 := by
    rw [hinv]
    first
    | exact Matrix.mul_eq_one_comm.mp hleft
    | exact mul_eq_one_comm.mp hleft
  have hsum : ∑ i, ∑ j, Complex.normSq (g⁻¹ i j) = ∑ i, ∑ j, Complex.normSq (g i j) := by
    have he : ∀ i j, Complex.normSq (g⁻¹ i j) =
        Complex.normSq (g (GBasic.sig k r j) (GBasic.sig k r i)) := by
      intro i j
      rw [hinv, mul_Hpk_apply, Hpk_mul_apply, Matrix.conjTranspose_apply, Complex.normSq_mul,
        Complex.normSq_mul, normSq_sgn, normSq_sgn, Complex.star_def, Complex.normSq_conj]
      ring
    simp only [he]
    let σ : Equiv.Perm (Fin (2 * r + k + 1)) :=
      Function.Involutive.toPerm _ (GBasic.sig_sig k r)
    rw [Finset.sum_comm]
    refine Fintype.sum_equiv σ _ _ fun j => ?_
    exact Fintype.sum_equiv σ _ _ fun i => rfl
  refine ⟨by simp only [B.gN, hsum], ?_⟩

  set i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have hcs := euclid_cs (fun l => g⁻¹ l i0) (fun l => star (g i0 l))
  have h1 : star (fun l => star (g i0 l)) ⬝ᵥ (fun l => g⁻¹ l i0) = 1 := by
    have := congrFun (congrFun hright i0) i0
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simpa [dotProduct] using this
  rw [h1, Complex.normSq_one] at hcs
  have hgN : ∀ h : B.Mat k r, B.gN h ^ 2 = ∑ i, ∑ j, Complex.normSq (h i j) := fun h =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hA : ∑ l, Complex.normSq (g⁻¹ l i0) ≤ B.gN g⁻¹ ^ 2 := by
    rw [hgN, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun j => ∑ l, Complex.normSq (g⁻¹ l j))
      (fun j _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hB : ∑ l, Complex.normSq (star (g i0 l)) ≤ B.gN g ^ 2 := by
    rw [hgN]
    simp only [Complex.star_def, Complex.normSq_conj]
    exact Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (g i l))
      (fun i _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hN0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have hEq : B.gN g⁻¹ = B.gN g := by simp only [B.gN, hsum]
  rw [hEq] at hA
  have h4 : 1 ≤ B.gN g ^ 2 * B.gN g ^ 2 :=
    hcs.trans (mul_le_mul hA hB (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _)
      (sq_nonneg _))
  by_contra hlt
  push_neg at hlt
  have : B.gN g ^ 2 * B.gN g ^ 2 < 1 := by
    have h5 : B.gN g ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (B.gN g)]
  linarith

end Formalism.FourierDecayAlt.P
end

