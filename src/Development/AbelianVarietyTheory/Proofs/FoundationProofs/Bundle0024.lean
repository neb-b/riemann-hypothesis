module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariables
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerChange

lemma exists_ball (z : ℂ) (hz : 0 < z.im) :
    ∃ (c : ℂ) (r : ℝ), Metric.ball c r ⊆ {u : ℂ | 0 < u.im} ∧ Complex.I ∈ Metric.ball c r ∧
      z ∈ Metric.ball c r := by
  have key : ∀ (u : ℂ) (R : ℝ), 0 < u.im → 0 < R → u.re ^ 2 + u.im ^ 2 < 2 * R * u.im →
      u ∈ Metric.ball ((R : ℂ) * Complex.I) R := by
    intro u R hu hR h
    rw [Metric.mem_ball, Complex.dist_eq, ← sq_lt_sq₀ (norm_nonneg _) hR.le, Complex.sq_norm,
      Complex.normSq_apply]
    simp
    nlinarith
  set a := (z.re ^ 2 + z.im ^ 2) / z.im with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a * z.im = z.re ^ 2 + z.im ^ 2 := by rw [ha]; field_simp
  refine ⟨((a + 1 : ℝ) : ℂ) * Complex.I, a + 1, ?_, key _ _ (by simp) (by linarith) ?_,
    key _ _ hz (by linarith) ?_⟩
  · intro u hu
    rw [Metric.mem_ball, Complex.dist_eq] at hu
    have := (Complex.abs_im_le_norm _).trans_lt hu
    simp at this
    have := (abs_lt.1 this).1
    show 0 < u.im
    linarith
  · simp; linarith
  · nlinarith [mul_nonneg ha0 hz.le]

lemma hasDerivAt_segInt (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (fun τ : ℂ => ∫ t in (0 : ℝ)..1,
      g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I)) (g z) z := by
  obtain ⟨c, r, hB, hI, hzB⟩ := exists_ball z hz
  obtain ⟨G, hG⟩ := (hg.mono hB).isExactOn_ball
  refine ((hG z hzB).sub_const (G Complex.I)).congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hzB] with τ hτ
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, Complex.I + t * (τ - Complex.I) ∈ Metric.ball c r := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    simpa using (convex_ball c r).add_smul_sub_mem hI hτ ht
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => G (Complex.I + s * (τ - Complex.I)))
        (g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℂ => Complex.I + u * (τ - Complex.I)) (τ - Complex.I) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (τ - Complex.I)).const_add Complex.I
    exact (HasDerivAt.comp (t : ℂ) (h₂ := G) (hG _ (hmem t ht)) h1).comp_ofReal
  have hc : ContinuousOn (fun t : ℝ => g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I))
      (Set.uIcc 0 1) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (hg.continuousOn.mono hB).comp (f := fun t : ℝ => Complex.I + t * (τ - Complex.I))
      (by fun_prop) hmem
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

def ecoef (w : ℕ) (h : ℍ → ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (h ∘ ofComplex) (Complex.I + t * (v - Complex.I)) *
    (-(Complex.I + t * (v - Complex.I))) ^ (w - n) * (v - Complex.I)

lemma coeff_eichler (w : ℕ) (h : ℍ → ℂ) (τ : ℍ) (n : ℕ) :
    (eichler w h τ).coeff n = (w.choose n : ℂ) * ecoef w h n τ := by
  unfold eichler ecoef
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using hn)]; simp

lemma hasDerivAt_ecoef (w : ℕ) (h : ℍ → ℂ) (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (n : ℕ) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (ecoef w h n) ((h ∘ ofComplex) z * (-z) ^ (w - n)) z :=
  hasDerivAt_segInt (fun u => (h ∘ ofComplex) u * (-u) ^ (w - n))
    ((UpperHalfPlane.mdifferentiable_iff.1 hh).mul (by fun_prop)) z hz

lemma polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  unfold slP
  rw [LinearMap.sum_apply]
  rfl

lemma polySlash_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (s z u : ℂ)
    (h1 : (g 0 0 : ℂ) - s * g 1 0 = u) (h2 : (g 0 1 : ℂ) - s * g 1 1 = -z * u) :
    slP w g ((X + C (-s)) ^ w) = C (u ^ w) * (X + C (-z)) ^ w := by
  have e : C u * (X + C (-z)) = (C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) +
      C (-s) * (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) := by
    have e1 := congrArg C h1
    have e2 := congrArg C h2
    simp only [map_sub, map_mul, map_neg] at e1 e2 ⊢
    linear_combination (-X) * e1 - e2
  rw [C_pow, ← mul_pow, e, polySlash_apply]
  conv_rhs => rw [add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_X_add_C_pow, smul_eq_C_mul, mul_pow, C_mul, C_pow, map_natCast]
  ring

lemma coe_smul_eq (σ : SL(2, ℤ)) (τ : ℍ) :
    ((σ • τ : ℍ) : ℂ) = ((mat σ 0 0 : ℂ) * τ + mat σ 0 1) / ((mat σ 1 0 : ℂ) * τ + mat σ 1 1) := by
  rw [coe_specialLinearGroup_apply]
  simp

theorem polySlash_eichler_smul (k : ℕ) (hk : 2 ≤ k) (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (σ : SL(2, ℤ)) : ∃ C : ℂ[X], ∀ τ : ℍ,
      slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C := by
  obtain ⟨w, rfl⟩ : ∃ w, k = w + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set h : ℍ → ℂ := f ∣[((w + 2 : ℕ) : ℤ)] σ with hdef
  have hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hdef, ModularForm.SL_slash]
    exact hf.slash _ _
  set a : ℂ := ((mat σ 0 0 : ℤ) : ℂ) with ha
  set b : ℂ := ((mat σ 0 1 : ℤ) : ℂ) with hb
  set c : ℂ := ((mat σ 1 0 : ℤ) : ℂ) with hc
  set d : ℂ := ((mat σ 1 1 : ℤ) : ℂ) with hd
  have hdet : a * d - b * c = 1 := by
    have := σ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc, hd]
    exact_mod_cast this
  refine ⟨slP w (mat σ) (eichler w f (σ • I)) - eichler w h I, fun τ => ?_⟩
  ext n
  set q : ℕ → ℂ := fun i => ((C a * X + C b) ^ i * (C c * X + C d) ^ (w - i)).coeff n with hq
  have hslP : ∀ p : ℂ[X], (slP w (mat σ) p).coeff n = ∑ i ∈ Finset.range (w + 1), p.coeff i * q i := by
    intro p
    rw [polySlash_apply, finsetSum_coeff]
    simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rfl
  set Φ : ℂ → ℂ := fun v => ∑ i ∈ Finset.range (w + 1),
      (w.choose i : ℂ) * ecoef w f i ((a * v + b) / (c * v + d)) * q i -
    (w.choose n : ℂ) * ecoef w h n v with hΦ
  have hΦ1 : ∀ τ : ℍ, Φ τ = (slP w (mat σ) (eichler w f (σ • τ))).coeff n - (eichler w h τ).coeff n := by
    intro τ
    simp only [hΦ, hslP, coeff_eichler, coe_smul_eq]
    rfl
  have hder : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt Φ 0 z := by
    intro z hz
    obtain ⟨τ, rfl⟩ : ∃ τ : ℍ, (τ : ℂ) = z := ⟨⟨z, hz⟩, rfl⟩
    have hj : c * τ + d ≠ 0 := by
      rw [hc, hd, ← ModularGroup.denom_apply]
      exact denom_ne_zero _ _
    have hs : ((σ • τ : ℍ) : ℂ) = (a * τ + b) / (c * τ + d) := coe_smul_eq σ τ
    have hm : HasDerivAt (fun v : ℂ => (a * v + b) / (c * v + d)) ((c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      have h1 : HasDerivAt (fun v : ℂ => a * v + b) a (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
      have h2 : HasDerivAt (fun v : ℂ => c * v + d) c (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
      refine (h1.fun_div h2 hj).congr_deriv ?_
      rw [inv_pow, div_eq_mul_inv]
      linear_combination ((c * τ + d) ^ 2)⁻¹ * hdet
    have hA : ∀ i, HasDerivAt (fun v : ℂ => ecoef w f i ((a * v + b) / (c * v + d)))
        (f (σ • τ) * (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      intro i
      have := hasDerivAt_ecoef w f hf i _ (σ • τ).im_pos
      simp only [Function.comp_apply, ofComplex_apply] at this
      exact HasDerivAt.comp (τ : ℂ) (h₂ := ecoef w f i) (by rw [← hs]; exact this) hm
    have hB := hasDerivAt_ecoef w h hh n _ τ.im_pos
    simp only [Function.comp_apply, ofComplex_apply] at hB
    have hP := congrArg (fun p : ℂ[X] => p.coeff n)
      (polySlash_pow w (mat σ) ((σ • τ : ℍ) : ℂ) τ (c * τ + d)⁻¹
        (by rw [hs, ← ha, ← hc]; rw [div_eq_mul_inv]
            linear_combination (-a) * mul_inv_cancel₀ hj + (c * τ + d)⁻¹ * hdet)
        (by rw [hs, ← hb, ← hd]; rw [div_eq_mul_inv]
            linear_combination (-b) * mul_inv_cancel₀ hj - (c * τ + d)⁻¹ * τ * hdet))
    simp only [hslP, coeff_C_mul, coeff_X_add_C_pow] at hP
    have hv : h τ = f (σ • τ) * (c * τ + d)⁻¹ ^ (w + 2) := by
      rw [hdef, ModularForm.SL_slash_apply, ModularGroup.denom_apply, zpow_neg, zpow_natCast, inv_pow]
    refine ((HasDerivAt.fun_sum (u := Finset.range (w + 1)) fun i _ =>
      ((hA i).const_mul (w.choose i : ℂ)).mul_const (q i)).fun_sub
        (hB.const_mul (w.choose n : ℂ))).congr_deriv ?_
    have : ∑ i ∈ Finset.range (w + 1), (w.choose i : ℂ) *
        (f (σ • τ) * (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (c * τ + d)⁻¹ ^ 2) * q i =
        f (σ • τ) * (c * τ + d)⁻¹ ^ 2 * ∑ i ∈ Finset.range (w + 1),
          (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (w.choose i : ℂ) * q i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hP, hv]
    ring
  have hconst : Φ τ = Φ (I : ℍ) :=
    isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hder z hz).deriv) τ.im_pos (I : ℍ).im_pos
  rw [hΦ1, hΦ1] at hconst
  rw [coeff_add, coeff_sub]
  linear_combination hconst

end GlobalTheory.EichlerChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmul
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem polySlash_map_conj (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, lcoeff_apply, Polynomial.map_sum, Polynomial.map_smul,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    map_intCast, coeff_map, Polynomial.map_intCast, Polynomial.map_natCast]

theorem eichler_smul (w : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    eichler w (c • f) τ = c • eichler w f τ := by
  simp only [eichler, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_C_mul, ← mul_assoc, ← C_mul]
  congr 2
  have : ∀ t : ℝ, ((c • f) ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I) =
      c * ((f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) := by
    intro t; simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [this, intervalIntegral.integral_const_mul]
  ring

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

theorem polynomialMapCoeffConj_mem_eichlerShimuraCocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : Γ → ℂ[X]) (hz : z ∈ Z1 Γ w) : cj z ∈ Z1 Γ w := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · have := h1 γ
    rw [mem_degreeLT] at this ⊢
    exact lt_of_le_of_lt (degree_map_le) this
  · simp only [cj, h2, Polynomial.map_add (f := _), polySlash_map_conj]

theorem polynomialMapCoeffConj_mem_eichlerShimuraCoboundaries (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : Γ → ℂ[X]) (hz : z ∈ B1 Γ w) : cj z ∈ B1 Γ w := by
  obtain ⟨⟨p, hp⟩, rfl⟩ := hz
  have hp' : p.map (starRingEnd ℂ) ∈ degreeLT ℂ (w + 1) := by
    rw [mem_degreeLT] at hp ⊢
    exact lt_of_le_of_lt (degree_map_le) hp
  refine ⟨⟨p.map (starRingEnd ℂ), hp'⟩, ?_⟩
  funext γ
  simp only [cj, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply,
    LinearMap.sub_apply, LinearMap.id_apply, Polynomial.map_sub, polySlash_map_conj]

theorem per_smul (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (f : ℍ → ℂ) (c : ℂ) :
    per Γ w (c • f) = c • per Γ w f := by
  funext γ
  simp only [per, Pi.smul_apply, eichler_smul, map_smul]

theorem cj_mem_Z1_cj_mem_B1_per_smul : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ), (∀ z ∈ Z1 Γ w, cj z ∈ Z1 Γ w) ∧
    (∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w) ∧ ∀ (f : ℍ → ℂ) (c : ℂ), per Γ w (c • f) = c • per Γ w f :=
  fun Γ w => ⟨polynomialMapCoeffConj_mem_eichlerShimuraCocycles Γ w, polynomialMapCoeffConj_mem_eichlerShimuraCoboundaries Γ w, per_smul Γ w⟩

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalPolyDegreeSlashAction
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem eval_polySlash : ∀ (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (z : ℂ), p ∈ degreeLT ℂ (w + 1) → ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ≠ 0 → (slP w g p).eval z = ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ w * p.eval (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) := by
  intro w g p z hp hz
  have hn : p.natDegree < w + 1 := by
    rcases eq_or_ne p 0 with rfl | h
    · simp
    · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)
  have hs : slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
    simp [slP, LinearMap.sum_apply, LinearMap.toSpanSingleton_apply]
  rw [hs, eval_finsetSum, eval_eq_sum_range' hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [eval_smul, eval_mul, eval_pow, eval_add, eval_C, eval_X, smul_eq_mul]
  rw [div_pow, ← Nat.sub_add_cancel hi', pow_add]
  rw [Nat.sub_add_cancel hi']
  have hD : ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ i ≠ 0 := pow_ne_zero _ hz
  have e := mul_inv_cancel₀ hD
  linear_combination (-(p.coeff i * ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) ^ i *
    ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ (w - i))) * e

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExceptionalPrimesFiniteCardLe
section
open Finset

namespace GlobalTheory

theorem exceptional_primes_finite_card_le (n m : ℕ) (hn : n ≠ 0) (hm : n < m) :
    Set.Finite {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ∧
      Set.ncard {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ≤ 3 := by
  classical
  set F : Finset ℕ := n.primeFactors.filter (fun ℓ => m < ℓ ^ (4 * padicValNat ℓ n)) with hF
  have hS : {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} = (F : Set ℕ) := by
    ext ℓ
    simp only [hF, Set.mem_ofPred_eq, coe_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨⟨hp, ?_, hn⟩, h⟩
      by_contra hd
      rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hd] at h
      simp at h
      omega
    · rintro ⟨⟨hp, -, -⟩, h⟩
      exact ⟨hp, h⟩
  rw [hS]
  refine ⟨F.finite_toSet, ?_⟩
  rw [Set.ncard_coe_finset]
  by_contra hc
  have hc4 : 4 ≤ F.card := by omega
  have h1 : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ≤ n := by
    have e : ∏ ℓ ∈ n.primeFactors, ℓ ^ padicValNat ℓ n = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.padicValNat_def, Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
    have hd : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ∣ n := by
      conv_rhs => rw [← e]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h2 : m ^ F.card ≤ ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) :=
    Finset.pow_card_le_prod F _ m fun ℓ hℓ => ((Finset.mem_filter.1 hℓ).2).le
  have h3 : ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) = (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm]
  have h4 : m ^ 4 ≤ m ^ F.card := Nat.pow_le_pow_right (by omega) hc4
  have h5 : (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left h1 4
  have h6 : n ^ 4 < m ^ 4 := Nat.pow_lt_pow_left hm (by norm_num)
  omega

theorem exceptional_set_count : Formalism.CyclotomicNorms.BBCount := by
  intro g hg
  have key : ∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ∧
      Set.ncard {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ≤ 3 := by
    intro d hd
    have h1 : 1 < g ^ d := Nat.one_lt_pow (by omega) (by omega)
    exact exceptional_primes_finite_card_le (g ^ d - 1) (g ^ d) (by omega) (by omega)
  refine ⟨key, fun N => ?_⟩
  induction N with
  | zero =>
    have : Formalism.CyclotomicNorms.BB 0 g = {g} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, -⟩)
        · exact h
        · omega
      · exact Or.inl
    rw [this]
    simp
  | succ N ih =>
    have : Formalism.CyclotomicNorms.BB (N + 1) g = Formalism.CyclotomicNorms.BB N g ∪ {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, h3⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_ge N d with h | h
          · obtain rfl : d = N + 1 := by omega
            exact Or.inr h3
          · exact Or.inl (Or.inr ⟨d, h1, h, h3⟩)
      · rintro ((h | ⟨d, h1, h2, h3⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨d, h1, by omega, h3⟩
        · exact Or.inr ⟨N + 1, by omega, le_rfl, h⟩
    rw [this]
    obtain ⟨hf, hc⟩ := key (N + 1) (by omega)
    refine ⟨ih.1.union hf, ?_⟩
    have := Set.ncard_union_le (Formalism.CyclotomicNorms.BB N g) {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ}
    have := ih.2
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZero
section
open Polynomial

namespace GlobalTheory

theorem exists_deg_lt_two_correction_simple :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A),
      P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧
        w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  intro k A _ _ _ _ _ _ _ _ _ _ n b P₀ w hP
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨φ, hφ⟩ := ((_root_.GlobalTheory.DedekindCodim.dedekind_finiteType_codim k A).2.1 P₀ hP).2
  set α : k := φ (algebraMap k[X] A X) with hα
  have hC : algebraMap k[X] A (C α) = algebraMap k A α := by
    rw [IsScalarTower.algebraMap_apply k k[X] A]; rfl
  have hlin : algebraMap k[X] A (X - C α) ∈ P₀ := by
    rw [hφ, map_sub, map_sub, hC, φ.commutes, ← hα]
    simp
  have hne : algebraMap k[X] A (X - C α) ≠ 0 := by
    intro h0
    have h1 : (X - C α) • (1 : A) = 0 := by rw [Algebra.smul_def, h0, zero_mul]
    have h3 : b.repr (1 : A) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp h3
    have h4 := congrArg (fun a => b.repr a i) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h4
    exact mul_ne_zero (X_sub_C_ne_zero α) hi h4
  have hbot : P₀ ≠ ⊥ := fun h => hne (by rw [h] at hlin; simpa using hlin)
  have hlt := Ideal.pow_lt_self P₀ hbot hP.ne_top 2 le_rfl
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  set q : k[X] := (X - C α) ^ 2 with hq
  have hmon : q.Monic := (monic_X_sub_C α).pow 2
  have hqdeg : q.degree = (2 : ℕ) := by
    rw [hq, degree_pow, degree_X_sub_C]; rfl
  have hqmem : algebraMap k[X] A q ∈ P₀ ^ 2 := by
    rw [hq, map_pow]; exact Ideal.pow_mem_pow hlin 2
  let c : Fin n → k[X] := fun i => b.repr (π - w) i
  let p : Fin n → k[X] := fun i => c i %ₘ q
  let d : Fin n → k[X] := fun i => c i /ₘ q
  have hs : ∑ i, c i • b i = π - w := b.sum_repr (π - w)
  have h2 : ∑ i, c i • b i = ∑ i, p i • b i + algebraMap k[X] A q * ∑ i, d i • b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, smul_smul, ← add_smul]
    exact congrArg (· • b i) (modByMonic_add_div (c i) q).symm
  have key : w + ∑ i, p i • b i = π - algebraMap k[X] A q * ∑ i, d i • b i := by
    linear_combination hs - h2
  have hM : algebraMap k[X] A q * ∑ i, d i • b i ∈ P₀ ^ 2 := Ideal.mul_mem_right _ _ hqmem
  refine ⟨p, fun i => ?_, ?_, ?_⟩
  · rw [← hqdeg]; exact degree_modByMonic_lt _ hmon
  · rw [key]; exact P₀.sub_mem hπP (Ideal.pow_le_self two_ne_zero hM)
  · intro h
    apply hπ2
    have : π = (w + ∑ i, p i • b i) + algebraMap k[X] A q * ∑ i, d i • b i := by
      rw [key]; ring
    rw [this]; exact (P₀ ^ 2).add_mem h hM

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitEqSumSlash
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem uOp_eq_sum_slash (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q) : GlobalTheory.Hk.uOp q f = ∑ j ∈ Finset.range q, f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  funext z
  rw [Finset.sum_apply, uOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set g := Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne')) with hg
  have hval : g.1 = !![(1 : ℝ), (j : ℝ); 0, (q : ℝ)] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hg]
  have hdet : g.det.val = (q : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hval]; simp
  have hpos : 0 < g.det.val := by rw [hdet]; exact_mod_cast hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [slash_apply, σ, ite_eq_left hpos, abs_of_pos hpos, hdet, ← ofComplex_apply (g • z),
    coe_smul_of_det_pos hpos]
  simp [num, denom, hval]
  rw [mul_assoc, ← zpow_neg (q : ℂ) k, ← zpow_add₀ hq0,
    show k - 1 + -k = -1 by omega, zpow_neg_one, mul_comm]

end GlobalTheory.Hk
end

