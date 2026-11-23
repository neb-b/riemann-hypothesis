module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCompHomogeneousIsHomogeneous
section
open IsLocalRing

namespace GlobalTheory

open MvPolynomial

theorem norm_comp_homogeneous_isHomogeneous :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n d : ℕ)
      (f : MvPolynomial (Fin n) L), f.IsHomogeneous d →
      ∃ F : MvPolynomial (Fin n × Fin (Module.finrank K L)) K,
        F.IsHomogeneous (d * Module.finrank K L) ∧
        ∀ y : Fin n × Fin (Module.finrank K L) → K, MvPolynomial.eval y F =
          Algebra.norm K (MvPolynomial.eval
            (fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j) f) := by
  intro K L _ _ _ _ n d f hf
  classical
  set m := Module.finrank K L
  set b := Module.finBasis K L
  let g : Fin n → MvPolynomial (Fin n × Fin m) L := fun i => ∑ j, X (i, j) * C (b j)
  have hg : ∀ i, (g i).IsHomogeneous 1 := by
    intro i
    refine IsHomogeneous.sum _ _ _ (fun j _ => ?_)
    simpa using (isHomogeneous_X L (i, j)).mul (isHomogeneous_C _ (b j))
  let G : MvPolynomial (Fin n × Fin m) L := bind₁ g f
  have hG : G.IsHomogeneous d := by simpa [G, aeval_eq_bind₁] using hf.aeval g hg
  have hGev : ∀ y : Fin n × Fin m → K, eval (fun p => algebraMap K L (y p)) G =
      eval (fun i => ∑ j, algebraMap K L (y (i, j)) * b j) f := by
    intro y
    have key : ∀ (φ : MvPolynomial (Fin n) L) (x : Fin n × Fin m → L),
        eval x (bind₁ g φ) = eval (fun i => eval x (g i)) φ := by
      intro φ x
      induction φ using MvPolynomial.induction_on <;> simp_all
    rw [show G = bind₁ g f from rfl, key]
    congr 2
    funext i
    simp [g]
    rfl
  let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin m) K) :=
    fun i j => ∑ s ∈ G.support, monomial s (Algebra.leftMulMatrix b (AddMonoidAlgebra.coeff G s) i j)
  have hM : ∀ i j, (M i j).IsHomogeneous d := by
    intro i j
    refine IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ ?_)
    have := hG (mem_support_iff.mp hs)
    rwa [Finsupp.degree_eq_weight_one]
  refine ⟨M.det, ?_, ?_⟩
  · rw [Matrix.det_apply']
    refine IsHomogeneous.sum _ _ _ (fun σ _ => ?_)
    have hp : (∏ i, M (σ i) i).IsHomogeneous (d * m) := by
      have := IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => d) (fun i _ => hM _ _)
      simpa [mul_comm] using this
    have hε : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n × Fin m) K).IsHomogeneous 0 := by
      rw [← map_intCast (C : K →+* MvPolynomial (Fin n × Fin m) K)]
      exact isHomogeneous_C _ _
    simpa using hε.mul hp
  · intro y
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det b, ← hGev]
    congr 1
    ext i j
    show eval y (M i j) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [M, map_sum, eval_monomial]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eval_eq' _ G, map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have : AddMonoidAlgebra.coeff G s * ∏ k, (algebraMap K L (y k)) ^ (s k) = (∏ k, y k ^ s k) • AddMonoidAlgebra.coeff G s := by
      rw [Algebra.smul_def, mul_comm]
      simp [map_prod, map_pow]
    rw [this, map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm, Finsupp.prod_fintype]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEigenvalueLeOneOfIntegralMatrixUltrametric
section
namespace GlobalTheory

theorem norm_eigenvalue_le_one_of_integral_matrix (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] (emb : O →+* K) (hemb : ∀ c, ‖emb c‖ ≤ 1) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K) (hc : c ≠ 0)
    (hM : (M.map emb).mulVec c = μ • c) : ‖μ‖ ≤ 1 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => ‖c j‖) ⟨j₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖c k‖ :=
    lt_of_lt_of_le (norm_pos_iff.2 hj₀) (hk j₀ (Finset.mem_univ _))
  have hrow : (M.map emb).mulVec c k = μ * c k := by
    rw [hM]; simp
  have hsum : ‖(M.map emb).mulVec c k‖ ≤ ‖c k‖ := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
    rw [norm_mul]
    calc ‖emb (M k j)‖ * ‖c j‖ ≤ 1 * ‖c k‖ :=
          mul_le_mul (hemb _) (hk j (Finset.mem_univ _)) (norm_nonneg _) zero_le_one
      _ = ‖c k‖ := one_mul _
  rw [hrow, norm_mul] at hsum
  have : ‖μ‖ * ‖c k‖ ≤ 1 * ‖c k‖ := by rwa [one_mul]
  exact le_of_mul_le_mul_right this hpos

theorem eigenvalue_integral_matrix_norm_le_one :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] (emb : O →+* K),
      (∀ c, ‖emb c‖ ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K),
      c ≠ 0 → (M.map emb).mulVec c = μ • c → ‖μ‖ ≤ 1 :=
  fun O K _ _ _ emb hemb n M μ c hc hM =>
    norm_eigenvalue_le_one_of_integral_matrix O K emb hemb n M μ c hc hM

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.NormSheaf

def normForm (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ} (x : Fin m → L) :
    MvPolynomial (Fin m) K :=
  (∑ i, (X i : MvPolynomial (Fin m) K) •
    (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* MvPolynomial (Fin m) K)).det

def normIdeal (A K L B : Type) [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L] [FiniteDimensional K L]
    [CommRing B] [Algebra B L] (J : Ideal B) : Ideal A :=
  Ideal.span {a | ∃ (m : ℕ) (g : Fin m → B), (∀ i, g i ∈ J) ∧
    ∃ s, algebraMap A K a = (normForm K L (fun i => algebraMap B L (g i))).coeff s}

end GlobalTheory.NormSheaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormInvLePowCardOfNormProdEqOne
section
namespace GlobalTheory

theorem norm_inv_le_pow_card_of_norm_prod_eq_one :
    ∀ (B : Multiset ℂˣ) (M : ℝ), 1 ≤ M → (∀ b ∈ B, ‖(b : ℂ)‖ ≤ M) →
      ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 → ∀ b ∈ B, ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ M ^ B.card := by
  intro B M hM hB hprod b hb
  have aux : ∀ C : Multiset ℂˣ, (∀ c ∈ C, ‖(c : ℂ)‖ ≤ M) →
      ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ ≤ M ^ C.card := by
    intro C
    induction C using Multiset.induction_on with
    | empty => intro _; simp
    | cons a C ih =>
      intro hC
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, norm_mul,
        mul_comm (M ^ _)]
      exact mul_le_mul (hC a (Multiset.mem_cons_self a C))
        (ih fun c hc => hC c (Multiset.mem_cons_of_mem hc)) (norm_nonneg _) (by linarith)
  obtain ⟨C, rfl⟩ := Multiset.exists_cons_of_mem hb
  have hC : ∀ c ∈ C, ‖(c : ℂ)‖ ≤ M := fun c hc => hB c (Multiset.mem_cons_of_mem hc)
  rw [Multiset.map_cons, Multiset.prod_cons, norm_mul] at hprod
  have hinv : ‖((b⁻¹ : ℂˣ) : ℂ)‖ = ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact (eq_inv_of_mul_eq_one_right hprod).symm
  rw [hinv, Multiset.card_cons]
  exact (aux C hC).trans (pow_le_pow_right₀ hM (Nat.le_succ _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivCexpPhaseLe
section
open scoped ContDiff
open scoped Nat

noncomputable section

namespace GlobalTheory

theorem norm_iteratedFDeriv_real_cexp (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

theorem norm_iteratedFDeriv_succ_clm_add_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (h : E → ℂ) (hh : ContDiff ℝ ∞ h) (i : ℕ) (t : E) :
    ‖iteratedFDeriv ℝ (i + 1) (fun t => L t + h t) t‖ ≤ ‖L‖ + ‖iteratedFDeriv ℝ (i + 1) h t‖ := by
  have hd : ∀ s, DifferentiableAt ℝ h s := fun s =>
    (hh.differentiable (by simp)).differentiableAt
  have hf : fderiv ℝ (fun t => L t + h t) = fun s => L + fderiv ℝ h s := by
    funext s
    exact (L.hasFDerivAt.add (hd s).hasFDerivAt).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hf, ← norm_iteratedFDeriv_fderiv]
  have hfh : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (by simp)
  change ‖iteratedFDeriv ℝ i ((fun _ => L) + fderiv ℝ h) t‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_const (c := L)).contDiffAt (hfh.of_le (by exact_mod_cast le_top)).contDiffAt]
  refine (norm_add_le _ _).trans ?_
  gcongr ?_ + _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [iteratedFDeriv_const_of_ne hi.ne']
    simp

theorem norm_iteratedFDeriv_cexp_phase_le :
    ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by
  intro V E _ _ _ _ _ _ B h hh hre n R
  set F : E → ℝ := fun t => ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j h t‖ with hF
  have hFc : Continuous F := by
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact (hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hFc.continuousOn
  refine ⟨(n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n, fun y t ht => ?_⟩
  have htb : t ∈ Metric.closedBall (0 : E) R := by simpa using ht
  have hKj : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j h t‖ ≤ |K| := by
    intro j hj
    have h1 : ‖iteratedFDeriv ℝ j h t‖ ≤ F t :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j h t‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h2 : F t ≤ K := (le_abs_self _).trans ((Real.norm_eq_abs (F t)) ▸ hK t htb)
    exact (h1.trans h2).trans (le_abs_self K)
  set D : ℝ := (1 + ‖B‖ + |K|) * (1 + ‖y‖) with hD
  have hy0 := norm_nonneg y
  have hB0 := norm_nonneg B
  have hK0 := abs_nonneg K
  have hD1 : 1 ≤ D := by
    rw [hD]; nlinarith
  have hDge : ‖B‖ * ‖y‖ + |K| ≤ D := by
    rw [hD]; nlinarith
  have hphi : ContDiff ℝ ∞ (fun t => B y t + h t) := (B y).contDiff.add hh
  have hcomp : (fun t => Complex.exp (B y t + h t)) = Complex.exp ∘ (fun t => B y t + h t) := rfl
  rw [hcomp]
  have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Complex.exp) (f := fun t => B y t + h t)
    (n := n) (N := ∞) Complex.contDiff_exp hphi (by exact_mod_cast le_top) t (C := 1) (D := D)
    (fun i _ => by rw [norm_iteratedFDeriv_real_cexp, hre y t, Real.exp_zero])
    (fun i hi1 hin => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      calc ‖iteratedFDeriv ℝ (j + 1) (fun t => B y t + h t) t‖
          ≤ ‖B y‖ + ‖iteratedFDeriv ℝ (j + 1) h t‖ :=
            norm_iteratedFDeriv_succ_clm_add_le (B y) h hh j t
        _ ≤ ‖B‖ * ‖y‖ + |K| := add_le_add (B.le_opNorm y) (hKj _ hin)
        _ ≤ D := hDge
        _ ≤ D ^ (j + 1) := le_self_pow₀ hD1 (by omega))
  calc _ ≤ (n ! : ℝ) * 1 * D ^ n := key
    _ = (n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n * (1 + ‖y‖) ^ n := by rw [hD, mul_pow]; ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivIteratedFDeriv
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem norm_iteratedFDeriv_iteratedFDeriv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by
  induction n generalizing j with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.zero_add]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      norm_iteratedFDeriv_fderiv, ih (j + 1)]
    rw [show n + (j + 1) = n + 1 + j by omega]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeLintegralTaylorTailIteratedDeriv
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem taylorTail_step_one {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (a : ℝ) (hg : Differentiable ℝ g) (hd : Continuous (deriv g))
    (hlim : Tendsto g atTop (𝓝 0)) :
    ENNReal.ofReal ‖g a‖ ≤ ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := by
  by_cases hI : IntegrableOn (deriv g) (Ioi a)
  · have hint : ∫ x in Ioi a, deriv g x = 0 - g a :=
      integral_Ioi_of_hasDerivAt_of_tendsto hg.continuous.continuousWithinAt
        (fun x _ => (hg x).hasDerivAt) hI hlim
    rw [zero_sub] at hint
    have h1 : ‖g a‖ ≤ ∫ x in Ioi a, ‖deriv g x‖ := by
      calc ‖g a‖ = ‖∫ x in Ioi a, deriv g x‖ := by rw [hint, norm_neg]
        _ ≤ ∫ x in Ioi a, ‖deriv g x‖ := norm_integral_le_integral_norm _
    calc ENNReal.ofReal ‖g a‖ ≤ ENNReal.ofReal (∫ x in Ioi a, ‖deriv g x‖) := ENNReal.ofReal_le_ofReal h1
      _ = ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := ofReal_integral_norm_eq_lintegral_enorm hI
  · have : ∫⁻ t in Ioi a, ‖deriv g t‖ₑ = ∞ := by
      by_contra hne
      exact hI ⟨hd.aestronglyMeasurable, lt_top_iff_ne_top.mpr hne⟩
    rw [this]; exact le_top

theorem taylorTail_inner (j : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫⁻ t in Ioo (0:ℝ) s, ENNReal.ofReal (t ^ j / (j.factorial : ℝ))
      = ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) := by
  have hcont : Continuous (fun t : ℝ => t ^ j / (j.factorial : ℝ)) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le,
      intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
    push_cast
    rw [zero_pow (Nat.succ_ne_zero j), sub_zero, div_div, mul_comm]
  · exact (hcont.integrableOn_Icc (a := 0) (b := s)).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact div_nonneg (pow_nonneg ht.1.le _) (by positivity)

theorem taylorTail_tonelli (f : ℝ → ℝ≥0∞) (hf : Measurable f) (j : ℕ) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ∫⁻ s in Ioi t, f s
      = ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) * f s := by
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) with hw
  have hwm : Measurable w := by fun_prop
  let G : ℝ → ℝ → ℝ≥0∞ := fun t s => w t * (Ioi t).indicator f s
  have hG : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have : Function.uncurry G = fun p : ℝ × ℝ => w p.1 * ({p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.2) p) := by
      ext ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, G, Set.indicator, mem_Ioi, mem_setOf_eq]
    rw [this]
    exact (hwm.comp measurable_fst).mul ((hf.comp measurable_snd).indicator hS)
  have step1 : ∫⁻ t in Ioi (0:ℝ), w t * ∫⁻ s in Ioi t, f s
      = ∫⁻ t in Ioi (0:ℝ), ∫⁻ s in Ioi (0:ℝ), G t s := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [G]
    rw [lintegral_const_mul _ (hf.indicator measurableSet_Ioi), lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr (le_of_lt (mem_Ioi.mp ht))]
  rw [step1, lintegral_lintegral_swap hG.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have : ∀ t, G t s = (Iio s).indicator w t * f s := by
    intro t
    by_cases h : t < s <;> simp [G, Set.indicator, h]
  simp_rw [this]
  rw [lintegral_mul_const _ (hwm.indicator measurableSet_Iio), lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, taylorTail_inner j s hs]

theorem taylorTail_bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (h : ℝ → F) (m : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hlim : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0)) :
    ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ m / (m.factorial : ℝ)) * ‖iteratedDeriv (m + 1) h t‖ₑ := by
  have hdiff : ∀ n : ℕ, Differentiable ℝ (iteratedDeriv n h) := fun n =>
    hh.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)
  have hcont : ∀ n : ℕ, Continuous (iteratedDeriv n h) := fun n => (hdiff n).continuous
  have key : ∀ j ≤ m, ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ := by
    intro j
    induction j with
    | zero =>
      intro _
      have := taylorTail_step_one h 0 (hdiff 0) (by rw [← iteratedDeriv_one]; exact hcont 1)
        (by simpa using hlim 0 (Nat.zero_le _))
      simpa [iteratedDeriv_one] using this
    | succ j ih =>
      intro hj
      refine (ih (Nat.le_of_succ_le hj)).trans ?_
      calc ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ
          ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) *
              ∫⁻ s in Ioi t, ‖iteratedDeriv (j + 1 + 1) h s‖ₑ := by
            refine lintegral_mono (fun t => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (zero_le')
            have := taylorTail_step_one (iteratedDeriv (j+1) h) t (hdiff _)
              (by rw [← iteratedDeriv_succ]; exact hcont _) (hlim (j+1) hj)
            simpa [iteratedDeriv_succ] using this
        _ = _ := taylorTail_tonelli _ ((hcont _).enorm.measurable) j
  exact key m le_rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMapRingOfIntegersLeOne
section
namespace GlobalTheory.RingOfIntegersNormBound

theorem norm_le_one_of_isIntegral {F : Type*} [NormedField F] [IsUltrametricDist F]
    {x : F} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨q, hq, hqx⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hqx
  have hlead : q.coeff q.natDegree = 1 := hq
  rw [hlead, map_one, one_mul] at hqx
  have hpow : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ F (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hqx
  have hpos : 0 < ‖x‖ := lt_trans one_pos hlt
  have key : ∀ n : ℕ,
      ‖∑ i ∈ Finset.range n, algebraMap ℤ F (q.coeff i) * x ^ i‖ < ‖x‖ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ‖x‖ ^ n < ‖x‖ ^ (n + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self n)
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ih.trans h1) ?_)
      rw [norm_mul, norm_pow]
      have h2 : ‖algebraMap ℤ F (q.coeff n)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one F (q.coeff n)
      calc ‖algebraMap ℤ F (q.coeff n)‖ * ‖x‖ ^ n ≤ 1 * ‖x‖ ^ n :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ‖x‖ ^ n := one_mul _
        _ < _ := h1
  have := key q.natDegree
  rw [← norm_neg, ← hpow, norm_pow] at this
  exact lt_irrefl _ this

theorem norm_map_ringOfIntegers_le_one {K : Type} [Field K] [NumberField K] {p : ℕ}
    [Fact (Nat.Prime p)] (f : K →+* ℂ_[p]) (c : NumberField.RingOfIntegers K) :
    ‖(f : K → ℂ_[p]) (↑c : K)‖ ≤ (1 : ℝ) :=
  norm_le_one_of_isIntegral (map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe c))

end GlobalTheory.RingOfIntegersNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPowTwoPowSubOneGe
section
namespace GlobalTheory.PowerTwoNormLowerBound

theorem norm_pow_two_pow_sub_one_ge {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < (1 / 2 : ℝ)) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    set w := z ^ (2 ^ k) with hw
    have hw1 : ‖w - 1‖ < 1 / 2 := h _
    have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
      have e : (2 : ℂ) = (w + 1) - (w - 1) := by ring
      have := norm_sub_le (w + 1) (w - 1)
      rw [← e] at this
      have n2 : ‖(2 : ℂ)‖ = 2 := by simp
      linarith
    have eq : z ^ (2 ^ (k + 1)) - 1 = (w - 1) * (w + 1) := by
      rw [hw, pow_succ, pow_mul]; ring
    rw [eq, norm_mul, pow_succ]
    have h0 : 0 ≤ ‖z - 1‖ := norm_nonneg _
    have h0' : 0 ≤ (3 / 2 : ℝ) ^ k := by positivity
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖w - 1‖ * ‖w + 1‖ := mul_le_mul ih h2 (by norm_num) (norm_nonneg _)

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : (1 / 2 : ℝ) < (3 / 2 : ℝ) ^ k * ‖z - 1‖ := (div_lt_iff₀ hpos).mp hk
  have h2 := norm_pow_two_pow_sub_one_ge h k
  have h3 := h (2 ^ k)
  linarith

end GlobalTheory.PowerTwoNormLowerBound
end

