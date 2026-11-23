module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingHermSelf
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace TraceDualMin

theorem herm_one_eq {n : ℕ} (x y : Fin n → E) : herm 1 x y = ∑ k, x k * cc (y k) := by
  simp [herm, Matrix.one_apply]

theorem herm_smul_left {n : ℕ} (a : E) (x y : Fin n → E) :
    herm 1 (a • x) y = a * herm 1 x y := by
  simp [herm_one_eq, Finset.mul_sum, mul_assoc]

theorem herm_smul_right {n : ℕ} (a : E) (x y : Fin n → E) :
    herm 1 x (a • y) = cc a * herm 1 x y := by
  simp [herm_one_eq, Finset.mul_sum, cc, mul_left_comm]

theorem cc_cc (a : E) : cc (cc a) = a := by
  simp [cc]

theorem cc_herm_self {n : ℕ} (x : Fin n → E) : cc (herm 1 x x) = herm 1 x x := by
  simp [herm_one_eq, cc, mul_comm]

theorem trace_cc (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem isIntegral_cc {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (cc a) :=
  ha.map ((IsCMField.complexConj E).restrictScalars ℤ).toAlgHom

theorem embedding_herm_self {n : ℕ} (σ : E →+* ℂ) (x : Fin n → E) :
    σ (herm 1 x x) = ((∑ k, ‖σ (x k)‖ ^ 2 : ℝ) : ℂ) := by
  simp [herm_one_eq, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj']


omit [IsCMField E] in
theorem mem_inv_different {x : E} (hx : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (x * a) = k) :
    x ∈ (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one,
    Submodule.mem_traceDual]
  intro a ha
  obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
  obtain ⟨k, hk⟩ := hx b
  exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩

end TraceDualMin


open TraceDualMin in
theorem trace_dual_min {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ)
    (u : Fin n → E) (hu : u ≠ 0) (htr : ∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (herm 1 u y) = k) :
    2 * (fdeg E : ℝ) / rdE E ^ 2 ≤ ∑ σ : E →+* ℂ, ∑ k, ‖σ (u k)‖ ^ 2 := by
  set D : FractionalIdeal (𝓞 E)⁰ E := (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot

  have h1 : ∀ y ∈ Λ, herm 1 u y ∈ D⁻¹ := by
    intro y hy
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem (⟨cc (a : E), _root_.GlobalTheory.TraceDualMin.isIntegral_cc a.isIntegral_coe⟩ : 𝓞 E) hy)
    refine ⟨k, ?_⟩
    rw [← hk]
    change _ = Algebra.trace ℚ E (herm 1 u (cc (a : E) • y))
    rw [herm_smul_right, _root_.GlobalTheory.TraceDualMin.cc_cc, mul_comm]
  have h2 : ∀ δ ∈ D, δ • u ∈ Λ := by
    intro δ hδ
    refine hdual _ fun y hy => ?_
    rw [herm_smul_left]
    have := FractionalIdeal.mul_mem_mul hδ (h1 y hy)
    rw [mul_inv_cancel₀ hD0] at this
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp this
    rw [← hb]
    exact b.isIntegral_coe
  have h3 : ∀ δ ∈ D, herm 1 u u * δ ∈ D⁻¹ := by
    intro δ hδ
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem a (h2 δ hδ))
    refine ⟨k, ?_⟩
    rw [← hk, ← trace_cc]
    change _ = Algebra.trace ℚ E (herm 1 u ((a : E) • δ • u))
    rw [herm_smul_right, herm_smul_right]
    congr 1
    conv_rhs => rw [← cc_herm_self u]
    simp only [cc, map_mul]
    ring
  have h4 : herm 1 u u ∈ D⁻¹ * D⁻¹ := by
    rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hD0]
    exact h3
  have hnorm : ∀ σ : E →+* ℂ, ‖σ (herm 1 u u)‖ = ∑ k, ‖σ (u k)‖ ^ 2 := by
    intro σ
    rw [embedding_herm_self, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h0 : herm 1 u u ≠ 0 := by
    intro h
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hnorm σ
    rw [h, map_zero, norm_zero, eq_comm,
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at this
    apply hu
    funext k
    simpa using this k (Finset.mem_univ k)
  have h5 := absNorm_le_abs_norm_of_mem h4 h0
  rw [map_mul, hD, absNorm_inv_differentIdeal] at h5
  have h6 : (dE E)⁻¹ * (dE E)⁻¹ ≤ |((Algebra.norm ℚ (herm 1 u u) : ℚ) : ℝ)| := by
    have h := (Rat.cast_le (K := ℝ)).mpr h5
    simpa [dE] using h
  have h7 := finrank_mul_abs_norm_rpow_le_sum (herm 1 u u)
  simp only [hnorm] at h7
  refine le_trans ?_ h7
  have hd : 0 ≤ dE E := abs_nonneg _
  have hf : 2 * (fdeg E : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Nat.mul_div_le (Module.finrank ℚ E) 2
  have h8 : (rdE E ^ 2)⁻¹ = ((dE E)⁻¹ * (dE E)⁻¹) ^ ((Module.finrank ℚ E : ℝ)⁻¹) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hd) (inv_nonneg.mpr hd), Real.inv_rpow hd, rdE, one_div, sq,
      mul_inv]
  rw [div_eq_mul_inv, h8]
  gcongr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoordsNoHomogeneousRelationGenericHyperpla
section
namespace GlobalTheory


open MvPolynomial in
theorem aeval_mul_of_isHomogeneous_cone {K L ι : Type} [CommRing K] [CommRing L] [Algebra K L]
    {Q : MvPolynomial ι K} {d : ℕ} (hQ : Q.IsHomogeneous d) (c : L) (x : ι → L) :
    aeval (fun a => c * x a) Q = c ^ d * aeval x Q := by
  classical
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hQ.degree_eq_sum_deg_support hs
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hd]
  ring


open MvPolynomial in
theorem aeval_eq_pow_mul_aeval_dehomogenise {K L : Type} [CommRing K] [Field L] [Algebra K L]
    {m : ℕ} {Q : MvPolynomial (Fin (m + 1)) K} {d : ℕ} (hQ : Q.IsHomogeneous d)
    (x : Fin (m + 1) → L) (hx : x 0 ≠ 0) :
    aeval x Q = x 0 ^ d * aeval (fun a : Fin m => x a.succ / x 0)
      (aeval (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) Q) := by
  set y : Fin m → L := fun a => x a.succ / x 0 with hy
  have hx' : x = fun a => x 0 * (Fin.cons 1 y : Fin (m + 1) → L) a := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · simp
    · simp only [Fin.cons_succ, hy]
      field_simp
  have key : (fun i => aeval y ((Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) i)) =
      (Fin.cons 1 y : Fin (m + 1) → L) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  conv_lhs => rw [hx']
  rw [aeval_mul_of_isHomogeneous_cone hQ,
    aeval_eq_bind₁ (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K), aeval_bind₁, key]


open MvPolynomial in
theorem dehomogenise_ne_zero_of_isHomogeneous {K : Type} [Field K]
    {m : ℕ} {Q : MvPolynomial (Fin (m + 1)) K} {d : ℕ} (hQ : Q.IsHomogeneous d) (h0 : Q ≠ 0) :
    aeval (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) Q ≠ 0 := by
  intro h
  have hinj := IsFractionRing.injective (MvPolynomial (Fin (m + 1)) K)
    (FractionRing (MvPolynomial (Fin (m + 1)) K))
  have hx0 : (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘
      X) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    exact (map_ne_zero_iff _ hinj).mpr (X_ne_zero 0)
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := FractionRing (MvPolynomial (Fin (m + 1)) K)) hQ
    (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘ X) hx0
  rw [h, map_zero, mul_zero, aeval_algebraMap_apply, aeval_X_left_apply] at e
  exact h0 (hinj (by rw [e, map_zero]))

theorem exists_coordinates_no_homogeneous_relation_of_generic_zero :
    ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ),
    (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 →
    (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N,
      ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d →
        MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  intro K _ σ m N t ζ ht hζ hrel
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain _ | N := N
  · exact absurd (funext fun j => j.elim0) hζ
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hζ
  have hj0' : ζ j0 ≠ 0 := hj0
  have hind : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra hne
    exact ht p hne hp
  obtain ⟨J, hJ⟩ := exists_algebraicIndependent_ratios_of_generic_zero K ℂ m N t ζ j0 hind hj0' hrel
  refine ⟨Fin.cons j0 J, fun Q d hQ0 hQ => ?_⟩
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := ℂ) hQ
    (fun a => ζ ((Fin.cons j0 J : Fin (m + 1) → Fin (N + 1)) a)) (by simpa using hj0')
  change MvPolynomial.aeval _ Q ≠ 0
  rw [e]
  simp only [Fin.cons_zero, Fin.cons_succ]
  refine mul_ne_zero (pow_ne_zero _ hj0') ?_
  intro h
  exact dehomogenise_ne_zero_of_isHomogeneous hQ hQ0 ((algebraicIndependent_iff.mp hJ) _ h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNeZeroPair
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.BasePointFree

theorem exists_ne_zero_pair (g : ℂ → ℂ) (hg : Differentiable ℂ g) (h1 : g 1 ≠ 0) (m : ℂ)
    (hm : m ≠ 0) : ∃ t : ℂ, g t ≠ 0 ∧ g (-(m * t)) ≠ 0 := by
  by_contra hne
  push Not at hne
  have hg' : Differentiable ℂ (fun t : ℂ => g (-(m * t))) := hg.comp (by fun_prop)
  have A : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have B : AnalyticOnNhd ℂ (fun t : ℂ => g (-(m * t))) Set.univ := fun z _ => hg'.analyticAt z
  have := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero A B (fun z _ => by
    by_cases h : g z = 0
    · simp [h]
    · simp [hne z h]) isPreconnected_univ
  rcases this with h | h
  · exact h1 (h 1 (Set.mem_univ _))
  · have := h (-m⁻¹) (Set.mem_univ _)
    apply h1
    simpa [hm] using this

theorem HC_add_smul_left {ι : Type} [Fintype ι] {n : ℕ} (w c γ : Fin n → EuclideanSpace ℂ ι)
    (a : ℂ) : HC (w + a • c) γ = HC w γ + a * HC c γ := by
  simp only [HC, Hf, Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem prod_translate_mem {E : Type} [Field E] [NumberField E] (X : PT E) {n : ℕ}
    (s : (Fin n → Vsp X.dim) → ℂ) (hs : s ∈ X.Sec 1 n) (m : ℕ) (c : Fin n → Vsp X.dim) :
    (fun w => s (w + (1 : ℂ) • c) ^ m * s (w + (-(m : ℂ)) • c)) ∈ X.Sec (m + 1) n := by
  obtain ⟨hd, hs⟩ := hs
  refine ⟨?_, fun γ hγ v => ?_⟩
  · exact ((hd.comp (by fun_prop)).pow m).mul (hd.comp (by fun_prop))
  · simp only
    rw [add_right_comm v γ, add_right_comm v γ, hs γ hγ, hs γ hγ, HC_add_smul_left,
      HC_add_smul_left, mul_pow, mul_pow, ← Complex.exp_nat_mul]
    have : ((m + 1 : ℕ) : ℂ) * Real.pi * HC v γ + ((m + 1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2 =
        (m : ℂ) * (((1 : ℕ) : ℂ) * Real.pi * (HC v γ + 1 * HC c γ) +
          ((1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2) +
        (((1 : ℕ) : ℂ) * Real.pi * (HC v γ + -(m : ℂ) * HC c γ) +
          ((1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2) := by
      push_cast; ring
    rw [this, Complex.exp_add ((m : ℂ) * _)]
    ring

theorem exists_sec_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ), s ∈ X.Sec 1 1 → s ≠ 0 → ∀ q : ℕ, 2 ≤ q → ∀ v : Fin 1 → Vsp X.dim, ∃ F ∈ X.Sec q 1, F v ≠ 0 := by
  intro E _ _ _ X s hs hs0 q hq v
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hs0
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  obtain ⟨t, h1, h2⟩ := exists_ne_zero_pair (fun t : ℂ => s (v + t • (p - v)))
    (hs.1.comp (by fun_prop)) (by simpa using hp) m hm
  refine ⟨_, prod_translate_mem X s hs m (t • (p - v)), ?_⟩
  refine mul_ne_zero (pow_ne_zero _ (by simpa using h1)) ?_
  rwa [smul_smul, neg_mul]

end GlobalTheory.BasePointFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaRunParametersUniformTorus
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaRunParameters

theorem exists_large_nat (B c₁ c₂ d C : ℝ) (hB : 0 < B) (hd : 0 ≤ d) :
    ∃ q : ℕ, 1 ≤ q ∧ c₁ < q ∧ c₂ ≤ (q : ℝ) / 2 ∧ 1 ≤ (q : ℝ) / B ∧
      4 * (7 + Real.log q) + d + 1 ≤ q * ((q : ℝ) / B) ∧ C ≤ q * ((q : ℝ) / B) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 + |c₁| + 2 * |c₂| + B * (33 + d + |C|))
  have h1 := abs_nonneg c₁
  have h2 := abs_nonneg c₂
  have h3 := abs_nonneg C
  have h1' := le_abs_self c₁
  have h2' := le_abs_self c₂
  have h3' := le_abs_self C
  have h4 : 0 ≤ B * (33 + d + |C|) := by positivity
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hK : 33 + d + |C| ≤ (q : ℝ) / B := by
    rw [le_div_iff₀ hB]; linarith
  have hlog : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hm : (q : ℝ) * (33 + d + |C|) ≤ q * ((q : ℝ) / B) :=
    mul_le_mul_of_nonneg_left hK (by linarith)
  have hqd : d ≤ q * d := le_mul_of_one_le_left hd hq1
  have hqC : |C| ≤ q * |C| := le_mul_of_one_le_left h3 hq1
  refine ⟨q, by exact_mod_cast hq1, by linarith, by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem exists_par : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ),
    2 ≤ PT.f E * r → 1 ≤ m → m ^ 4 ≤ PT.f E → (PT.f E : ℝ) ≤ PT.rd E →
    (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E →
    ∃ (q : ℕ) (R0 : ℝ), 0 < th (E := E) q R0 ∧ ∀ X : PT E, X.r = r → (∃ τ, X.dim τ ≤ m) →
      ∃ P : Par X 1, P.q = q ∧ P.R0 = R0 ∧ P.m = m := by
  intro E _ _ _ r m hfr hm1 hmf hfrd hf2 hrd
  have hf : 0 < PT.f E := by
    rcases Nat.eq_zero_or_pos (PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hfR : (0 : ℝ) < PT.f E := by exact_mod_cast hf
  have hrd0 : 0 < PT.rd E := by linarith
  have hRR : 0 < RR (E := E) := by unfold RR; positivity
  set S : ℝ := 270 + 90 * (((PT.f E * r : ℕ) : ℝ) + 1) with hS
  have hS0 : 0 < S := by positivity
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  have hB : 0 < Real.sqrt S ^ 2 * RR (E := E) ^ 4 := by rw [hsq]; positivity
  have hA : 0 < PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3 := by rw [hsq]; positivity
  obtain ⟨q, hq1, hc1, hc2, hb, h5, h6⟩ := exists_large_nat (Real.sqrt S ^ 2 * RR (E := E) ^ 4)
    ((dstar (E := E) m : ℝ) ^ 2 * omStar (E := E) * (PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3))
    (M1 (E := E) m) (dstar (E := E) m)
    (((PT.f E * r : ℕ) : ℝ) * Real.log 2 + 2 * dstar (E := E) m + 3 +
      (1 + 1) * (r * Real.log r + 3 * r + 3)) hB (Nat.cast_nonneg _)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  refine ⟨q, Real.sqrt S, Real.sqrt_pos.mpr (div_pos hA hq0), ?_⟩
  intro X hX hdim
  subst hX
  refine ⟨⟨q, Real.sqrt S, m, hq1, le_rfl, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, hb, hc2,
    hq1, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hsq, hS]
    unfold PT.gA
    have : (0 : ℝ) ≤ ((PT.f E * X.r : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor
    · linarith
    · rw [Nat.cast_one]; linarith
  · unfold th
    rw [Real.sq_sqrt (div_pos hA hq0).le, ← mul_div_assoc, div_lt_one hq0]
    exact hc1
  · unfold t0 b0
    rw [Nat.cast_one, mul_one, mul_one]
    exact h5
  · unfold t0 b0 PT.gA
    rw [Nat.cast_one]
    exact h6

end GlobalTheory.ThetaRunParameters
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupLeL2PrincipalTorus
section
namespace GlobalTheory

theorem _root_.GlobalTheory.packingCount : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount
  intro n P δ R hδ hR hP hsep
  have h1 := _root_.GlobalTheory.finset_card_le_of_separated P hδ (hδ.le.trans hR) 0
    (by simpa [dist_zero_right] using hP) (fun x hx y hy hxy => hsep x hx y hy hxy)
  rw [finrank_euclideanSpace_fin] at h1
  exact h1.trans (_root_.GlobalTheory.one_add_two_mul_div_pow_le hδ hR n)

theorem _root_.GlobalTheory.sup_le_l2_principal_torus : _root_.ReciprocityTheory.ChartRestriction.G.I2.GSupStatement := _root_.ReciprocityTheory.ChartRestriction.G.I2.gSup _root_.GlobalTheory.packingCount

end GlobalTheory
end

