module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.MaximalCompactGL2FiniteAdeleCharacterization
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.KMem

variable {F : Type} [Field F] [NumberField F]

theorem mem_Ohat_iff {x : Af F} : x ∈ Ohat F ↔ ∀ w, Valued.v (pLoc F w x) ≤ 1 := by
  simp only [Ohat, Subring.mem_iInf, Subring.mem_comap, ValuationSubring.mem_toSubring,
    HeightOneSpectrum.mem_adicCompletionIntegers]

theorem eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = a * b := h.symm
    _ ≤ a * 1 := by gcongr
    _ = a := mul_one a

theorem det_le {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (A : Matrix (Fin 2) (Fin 2) K) (h : ∀ i j, v (A i j) ≤ 1) : v A.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (v.map_sub _ _).trans (max_le ?_ ?_) <;> rw [v.map_mul]
  · exact mul_le_one' (h 0 0) (h 1 1)
  · exact mul_le_one' (h 0 1) (h 1 0)

theorem det_mul_det_inv (g : GL (Fin 2) (Af F)) :
    (g : Matrix (Fin 2) (Fin 2) (Af F)).det * ((g⁻¹ : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)).det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem v_det (g : GL (Fin 2) (Af F)) (w : HeightOneSpectrum (𝓞 F)) (h : ∀ i j, Valued.v (pLoc F w (g.val i j)) ≤ 1) :
    Valued.v (pLoc F w g.val.det) ≤ 1 := by
  rw [RingHom.map_det]
  exact det_le _ _ h

theorem mem_KLev_iff (u : GL (Fin 2) (Af F)) :
    u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1 := by
  rw [mem_KLev]
  constructor
  · rintro ⟨ha, hb, -⟩
    have ha' : ∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1 := fun w i j => mem_Ohat_iff.1 (ha i j) w
    have hb' : ∀ w i j, Valued.v (pLoc F w ((u⁻¹ : GL (Fin 2) (Af F)).val i j)) ≤ 1 :=
      fun w i j => mem_Ohat_iff.1 (hb i j) w
    refine ⟨ha', fun w => eq_one_of_mul (v_det u w (ha' w)) (v_det _ w (hb' w)) ?_⟩
    rw [← Valuation.map_mul, ← map_mul, det_mul_det_inv, map_one, Valuation.map_one]
  · rintro ⟨ha, hd⟩
    have hinv : ∀ w, Valued.v (pLoc F w (((Matrix.GeneralLinearGroup.det u)⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
      intro w
      have h1 : Valued.v (pLoc F w ((Matrix.GeneralLinearGroup.det u : (Af F)ˣ) : Af F)) *
          Valued.v (pLoc F w (((Matrix.GeneralLinearGroup.det u)⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, Units.mul_inv, map_one, Valuation.map_one]
      rw [Matrix.GeneralLinearGroup.val_det_apply, hd w, one_mul] at h1
      exact h1
    have hO : ∀ a b, u a b ∈ Ohat F := fun a b => mem_Ohat_iff.2 fun w => ha w a b
    refine ⟨hO, fun a b => mem_Ohat_iff.2 fun w => ?_, fun a b => ⟨u a b - (1 : Matrix (Fin 2) (Fin 2) (Af F)) a b, ?_, by simp⟩⟩
    · rw [Matrix.coe_units_inv, Matrix.inv_def, ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit,
        Matrix.smul_apply, smul_eq_mul, map_mul, Valuation.map_mul, hinv w, one_mul, Matrix.adjugate_fin_two]
      fin_cases a <;> fin_cases b <;> simp [ha w]
    · refine sub_mem (hO a b) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _

end GlobalTheory.HilbertThetaSeries.KMem


open GlobalTheory.HilbertThetaSeries.KMem in
theorem GlobalTheory.HilbertThetaSeries.kMem : ∀ (F : Type) [Field F] [NumberField F], (∀ u : GL (Fin 2) (Af F), u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1) ∧ (∀ (u : (Af F)ˣ) (x : Af F), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → (∀ w, Valued.v (pLoc F w x) ≤ 1) → aff u x ∈ KLev F 2 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ KLev F 2 1) ∧ (∀ w, ∀ g ∈ K1 w 0, locGL F 2 w g ∈ KLev F 2 1) ∧ (∀ (x : F) w, Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x) ∧ ∀ x : F, (∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1) ↔ IsIntegral ℤ x := by
  intro F _ _
  refine ⟨mem_KLev_iff, fun u x hu hx => ⟨?_, ?_⟩, fun w g hg => ?_, fun x w => ?_, fun x => ?_⟩
  · refine (mem_KLev_iff _).2 ⟨fun w i j => ?_, fun w => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [aff, (hu w).le, hx w]
    · simp [aff, Matrix.det_fin_two, hu w]
  · refine (mem_KLev_iff _).2 ⟨fun w i j => ?_, fun w => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, (hu w).le]
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two, hu w]
  · obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hg
    have hk : ∀ i j, Valued.v ((k.val i j : w.adicCompletionIntegers F) : w.adicCompletion F) ≤ 1 :=
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (k.val i j).2
    refine (mem_KLev_iff _).2 ⟨fun v i j => ?_, fun v => ?_⟩
    · change Valued.v ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w _)).val i j) ≤ 1
      by_cases hv : v = w
      · subst hv; rw [pLoc_locGL]; exact hk i j
      · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    · rw [RingHom.map_det]
      change Valued.v ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w _)).val.det) = 1
      by_cases hv : v = w
      · subst hv
        rw [pLoc_locGL]
        have e : ((Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers F).subtype k).val).det =
            (((Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) := by
          rw [Matrix.GeneralLinearGroup.val_det_apply]
          exact ((v.adicCompletionIntegers F).subtype.map_det k.val).symm
        rw [e]
        refine eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers F)ˣ).val.2)
          ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletionIntegers F)ˣ).val.2) ?_
        rw [← Valuation.map_mul]
        have h := congrArg (fun y : v.adicCompletionIntegers F => (y : v.adicCompletion F)) (Matrix.GeneralLinearGroup.det k).mul_inv
        exact (congrArg Valued.v h).trans (Valuation.map_one _)
      · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.det_one, Valuation.map_one]
  · exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  · constructor
    · intro h
      obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x h
      exact NumberField.RingOfIntegers.isIntegral_coe r
    · intro h w
      have e : x = algebraMap (𝓞 F) F ⟨x, h⟩ := rfl
      rw [e]
      exact HeightOneSpectrum.valuation_le_one w _

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization : ∀ (F : Type) [Field F] [NumberField F], (∀ u : GL (Fin 2) (Af F), u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1) ∧ (∀ (u : (Af F)ˣ) (x : Af F), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → (∀ w, Valued.v (pLoc F w x) ≤ 1) → aff u x ∈ KLev F 2 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ KLev F 2 1) ∧ (∀ w, ∀ g ∈ K1 w 0, locGL F 2 w g ∈ KLev F 2 1) ∧ (∀ (x : F) w, Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x) ∧ ∀ x : F, (∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1) ↔ IsIntegral ℤ x := by
  first | exact @GlobalTheory.HilbertThetaSeries.kMem | exact GlobalTheory.HilbertThetaSeries.kMem | (intros; apply GlobalTheory.HilbertThetaSeries.kMem <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.NormSumFreeOrbitsLeInvPrime
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem freeOrbit_prime_dvd_card {p : ℕ} [Fact p.Prime] {α : Type} (σ : α → α) (F : Finset α)
    (hF : ∀ x ∈ F, σ x ∈ F) (hp : ∀ x ∈ F, σ^[p] x = x) (hfree : ∀ x ∈ F, σ x ≠ x) :
    p ∣ F.card := by
  classical
  let f : Function.End F := fun y => ⟨σ y, hF y y.2⟩
  have hf : ∀ (n : ℕ) (y : F), (((f ^ n) y : F) : α) = σ^[n] y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', Function.iterate_succ_apply', ← ih y]
      rfl
  have h1 : f ^ p ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    rw [pow_one, hf]
    exact hp y y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) h1
  have h3 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨y, hy⟩
    exact hfree y y.2 (congrArg Subtype.val hy)
  rw [h3, Fintype.card_coe] at h2
  exact Nat.modEq_zero_iff_dvd.mp h2

theorem norm_prime_Qbar_eq (p : ℕ) [Fact p.Prime] : ‖(p : Qbar p)‖ = (p : ℝ)⁻¹ := by
  have h := PadicAlgCl.valuation_p p
  rw [← PadicAlgCl.valuation_coe, h]
  simp

theorem norm_sum_free_orbits_le : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  intro p _ ι α σ s Φ hs hp hfree hinv hle
  classical
  have hna := PadicAlgCl.isNonarchimedean p
  have key : ∀ c ∈ s.image Φ,
      ‖ι.symm ((s.filter (fun x => Φ x = c)).card • c)‖ ≤ (p : ℝ)⁻¹ := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    have hd : p ∣ (s.filter (fun x => Φ x = Φ y)).card := by
      apply freeOrbit_prime_dvd_card σ
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hs x hx.1, (hinv x hx.1).trans hx.2⟩
      · intro x hx
        exact hp x (Finset.mem_filter.1 hx).1
      · intro x hx
        exact hfree x (Finset.mem_filter.1 hx).1
    obtain ⟨k, hk⟩ := hd
    rw [map_nsmul, nsmul_eq_mul, norm_mul, hk, Nat.cast_mul, norm_mul, norm_prime_Qbar_eq]
    have h1 : ‖((k : ℕ) : Qbar p)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
    have h2 := hle y hy
    calc (p : ℝ)⁻¹ * ‖((k : ℕ) : Qbar p)‖ * ‖ι.symm (Φ y)‖ ≤ (p : ℝ)⁻¹ * 1 * 1 := by gcongr
      _ = (p : ℝ)⁻¹ := by ring
  have hsum : ∑ x ∈ s, Φ x = ∑ c ∈ s.image Φ, (s.filter (fun x => Φ x = c)).card • c :=
    Finset.sum_comp (fun c => c) Φ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  generalize s.image Φ = T at key
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (hna _ _).trans (max_le (key a (Finset.mem_insert_self a T))
      (ih fun c hc => key c (Finset.mem_insert_of_mem hc)))

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_free_orbits_le_inv_prime : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | exact GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | (intros; apply GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.PoissonSummationGaussianConstantOnEvenBlocks
section
open Matrix Complex
open scoped Real

namespace GlobalTheory.HilbertThetaSeries

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dotProduct_transpose_mul_diagonal_mul_mulVec (P : Matrix ι ι ℝ) (t : ι → ℂ) (x : ι → ℝ) :
    (fun i => (x i : ℂ)) ⬝ᵥ ((P.map ofReal)ᵀ * diagonal t * P.map ofReal) *ᵥ (fun i => (x i : ℂ)) =
      ∑ j, t j * (((P *ᵥ x) j : ℝ) : ℂ) ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    ← ofReal_mulVec_eq P x]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem siegelGaussIntegral_transpose_mul_diagonal_mul {P : Matrix ι ι ℝ} (hP : P.det ≠ 0)
    {t : ι → ℂ} (ht : ∀ i, 0 < (t i).im) :
    siegelGaussIntegral ((P.map ofReal)ᵀ * diagonal t * P.map ofReal) =
      (|P.det⁻¹| : ℝ) * ∏ i, (π / (-(π * I * t i))) ^ (1 / 2 : ℂ) := by
  have hb (i : ι) : 0 < (-(π * I * t i)).re := by simpa using mul_pos Real.pi_pos (ht i)
  have key := GaussianFourier.integral_cexp_neg_sum_mul_add hb fun _ => 0
  have hc := integral_comp_mulVec_of_det_ne_zero hP (f := fun y : ι → ℝ =>
    cexp (-∑ i, -(π * I * t i) * (y i : ℂ) ^ 2 + ∑ i, (0 : ℂ) * y i)) (by fun_prop)
  rw [key] at hc
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Complex.exp_zero,
    mul_one] at hc
  rw [← hc, siegelGaussIntegral]
  congr 2 with x
  rw [dotProduct_transpose_mul_diagonal_mul_mulVec]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, zero_mul, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem tsum_cexp_diagonal_gaussian {B : Matrix ι ι ℝ} (hB : B.det ≠ 0) (u : ι → ℝ) {z : ι → ℂ}
    (hz : ∀ i, 0 < (z i).im) :
    ∑' m : ι → ℤ, cexp (π * I * ∑ j, (-(z j)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) =
      ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ j, (-I * z j) ^ (1 / 2 : ℂ)) *
        ∑' m : ι → ℤ, cexp (π * I * ∑ j, z j * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) *
          cexp (2 * π * I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  have hz0 (i : ι) : z i ≠ 0 := fun h0 => by simpa [h0] using hz i
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht (i : ι) : 0 < (-(z i)⁻¹).im := by
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos (hz i) (normSq_pos.2 (hz0 i))
  have ht0 (i : ι) : -(z i)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero (hz0 i))
  have h := (isSiegel_diagonal_iff.2 ht).transpose_mul_mul hB
  have key := h.riemannTheta_eq_neg_inv (B⁻¹ *ᵥ u) 0
  rw [siegelGaussIntegral_transpose_mul_diagonal_mul hB ht, riemannTheta, riemannTheta] at key
  simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one,
    riemannThetaTerm_def] at key
  have hinv : ((B.map ofReal)ᵀ * diagonal (fun i => -(z i)⁻¹) * B.map ofReal)⁻¹ =
      ((B⁻¹ᵀ).map ofReal)ᵀ * diagonal (fun i => -z i) * (B⁻¹ᵀ).map ofReal := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_diagonal_of_ne_zero ht0,
      ← transpose_nonsing_inv, inv_map_ofReal hB, transpose_map, transpose_transpose,
      Matrix.mul_assoc]
    simp
  rw [hinv] at key
  have hc : ((|B.det⁻¹| : ℝ) : ℂ) * ∏ i, (π / -(π * I * -(z i)⁻¹)) ^ (1 / 2 : ℂ) =
      ((|B.det| : ℝ) : ℂ)⁻¹ * ∏ j, (-I * z j) ^ (1 / 2 : ℂ) := by
    rw [abs_inv, ofReal_inv]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    field_simp [hz0 i]
    simp
  rw [hc] at key
  refine (tsum_congr fun m => ?_).trans (key.trans (congrArg _ (tsum_congr fun m => ?_)))
  · have e := dotProduct_transpose_mul_diagonal_mul_mulVec B (fun i => -(z i)⁻¹)
      ((fun i => (m i : ℝ)) + B⁻¹ *ᵥ u)
    rw [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hB.isUnit, one_mulVec] at e
    simp only [Pi.add_apply, ofReal_add, ofReal_intCast] at e
    rw [e]
    simp only [Pi.zero_apply, ofReal_zero, add_zero, dotProduct, mul_zero, Finset.sum_const_zero,
      ofReal_add]
    congr 1
    ring
  · have e := dotProduct_transpose_mul_diagonal_mul_mulVec B⁻¹ᵀ (fun i => -z i)
      (fun i => (m i : ℝ))
    have e2 : (B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ⬝ᵥ u = (fun i => (m i : ℝ)) ⬝ᵥ B⁻¹ *ᵥ u := by
      rw [mulVec_transpose, dotProduct_mulVec]
    simp only [ofReal_intCast] at e
    simp only [Pi.zero_apply, ofReal_zero, add_zero, zero_add]
    rw [neg_mulVec, dotProduct_neg, e, ← Complex.exp_add, ← ofReal_sum]
    change _ = cexp (_ + 2 * π * I * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ⬝ᵥ u : ℝ) : ℂ))
    rw [e2]
    simp only [dotProduct, neg_mul, Finset.sum_neg_distrib, ofReal_sum, ofReal_mul, ofReal_intCast]
    congr 1
    ring

end General

theorem tsum_cexp_block_gaussian : ∀ (V κ : Type) [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ] (k : ℕ), Fintype.card κ = 2 * k → ∀ (B : Matrix (V × κ) (V × κ) ℝ), B.det ≠ 0 → ∀ (u : V × κ → ℝ) (z : V → ℂ), (∀ v, 0 < (z v).im) → ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-(z j.1)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) = ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ v, (-Complex.I * z v)) ^ k * ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, z j.1 * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  intro V κ _ _ _ _ k hk B hB u z hz
  rw [tsum_cexp_diagonal_gaussian hB u (z := fun j => z j.1) fun j => hz j.1]
  congr 2
  rw [Fintype.prod_prod_type, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Finset.prod_const, Finset.card_univ, hk]
  rw [pow_mul, one_div, cpow_ofNat_inv_pow]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_gaussian_constant_on_even_blocks : ∀ (V κ : Type) [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ] (k : ℕ), Fintype.card κ = 2 * k → ∀ (B : Matrix (V × κ) (V × κ) ℝ), B.det ≠ 0 → ∀ (u : V × κ → ℝ) (z : V → ℂ), (∀ v, 0 < (z v).im) → ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-(z j.1)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) = ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ v, (-Complex.I * z v)) ^ k * ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, z j.1 * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian | exact GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian | (intros; apply GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionLinearCombination
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem hasQ_lin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ) (c : ℂ), HasQ f a → HasQ g b → HasQ (f + g) (a + b) ∧ HasQ (c • f) (c • a) ∧ HasQ (f - g) (a - b) ∧ HasQ (fun _ : Hn F => c) (fun ξ => open Classical in if ξ = 0 then c else 0) := by
  intro F _ _ _ f g a b c hf hg
  obtain ⟨⟨D, hD, hfa⟩, hfs⟩ := hf
  obtain ⟨⟨E, hE, hgb⟩, hgs⟩ := hg
  have hez : ∀ z : Hn F, ez (0 : F) z = 1 := by
    intro z
    simp [ez, reAt]
  have scale : ∀ (ξ : F) (m k : ℕ), IsIntegral ℤ ((m : F) * ξ) →
      IsIntegral ℤ (((m * k : ℕ) : F) * ξ) ∧ IsIntegral ℤ (((k * m : ℕ) : F) * ξ) := by
    intro ξ m k h
    have e1 : ((m * k : ℕ) : F) * ξ = ((k : ℤ) : F) * ((m : F) * ξ) := by push_cast; ring
    have e2 : ((k * m : ℕ) : F) * ξ = ((k : ℤ) : F) * ((m : F) * ξ) := by push_cast; ring
    have hk : IsIntegral ℤ ((k : ℤ) : F) := isIntegral_algebraMap
    exact ⟨e1 ▸ hk.mul h, e2 ▸ hk.mul h⟩
  have both : ∀ ξ : F, a ξ ≠ 0 ∨ b ξ ≠ 0 →
      (ξ = 0 ∨ TP ξ) ∧ IsIntegral ℤ (((D * E : ℕ) : F) * ξ) := by
    intro ξ h
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := hfa ξ h
      exact ⟨h1, (scale ξ D E h2).1⟩
    · obtain ⟨h1, h2⟩ := hgb ξ h
      exact ⟨h1, (scale ξ E D h2).2⟩
  have hDE : 0 < D * E := Nat.mul_pos hD hE
  refine ⟨⟨⟨D * E, hDE, ?_⟩, ?_⟩, ⟨⟨D, hD, ?_⟩, ?_⟩, ⟨⟨D * E, hDE, ?_⟩, ?_⟩, ⟨⟨1, one_pos, ?_⟩, ?_⟩⟩
  · intro ξ h
    apply both
    by_contra hc
    push_neg at hc
    apply h
    simp [hc.1, hc.2]
  · intro z
    simpa [Pi.add_apply, add_mul] using (hfs z).add (hgs z)
  · intro ξ h
    apply hfa
    intro h0
    apply h
    simp [h0]
  · intro z
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using (hfs z).mul_left c
  · intro ξ h
    apply both
    by_contra hc
    push_neg at hc
    apply h
    simp [hc.1, hc.2]
  · intro z
    simpa [Pi.sub_apply, sub_mul] using (hfs z).sub (hgs z)
  · intro ξ h
    have h0 : ξ = 0 := by
      by_contra hne
      apply h
      simp [hne]
    subst h0
    refine ⟨Or.inl rfl, ?_⟩
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : F))
  · intro z
    have := hasSum_single (f := fun ξ : F => (open Classical in if ξ = 0 then c else 0) * ez ξ z) (0 : F) (by
      intro ξ hξ
      simp [hξ])
    convert this using 1
    simp [hez z]
end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_linear_combination : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ) (c : ℂ), HasQ f a → HasQ g b → HasQ (f + g) (a + b) ∧ HasQ (c • f) (c • a) ∧ HasQ (f - g) (a - b) ∧ HasQ (fun _ : Hn F => c) (fun ξ => open Classical in if ξ = 0 then c else 0) := by
  first | exact @GlobalTheory.HilbertThetaSeries.hasQ_lin | exact GlobalTheory.HilbertThetaSeries.hasQ_lin | (intros; apply GlobalTheory.HilbertThetaSeries.hasQ_lin <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.RatPts

theorem pInf_algebraMap (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) = rhom x := by
  funext v
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
    ((algebraMap F (Ad F) x).1 v) = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x
  rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  simpa using InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe
    (IsTotallyReal.isReal v) (WithAbs.toAbs _ x)

theorem pInf_ratGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) = toInf γ := by
  ext i j v
  exact congrFun (pInf_algebraMap F (γ i j)) v

theorem ratGL_real_fin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F),
    ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧
      ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  intro F _ _ _ γ
  refine ⟨?_, fun h => ?_⟩
  · rw [← pInf_ratGL]
    exact (TR.infGL_mul_finGL (ratGL F 2 γ)).symm
  · obtain ⟨τ, hτ⟩ := GlobalTheory.WeakApproxGL.exists_rat_det_pos F 2 h
    refine ⟨τ, fun v => ?_⟩
    have e := hτ v
    rwa [MonoidHom.comp_apply, pInf_ratGL] at e

end GlobalTheory.HilbertThetaSeries.RatPts

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_GL2_infinite_finite_factor : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F), ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | exact GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | (intros; apply GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin <;> assumption)
end

