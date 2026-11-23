module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
section
noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

def twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  C (∏ τ, (emb τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
    bind₁ (fun k : ι × Fin n × Fin n => ∑ j : Fin n,
      C (emb k.1 ((M : Matrix (Fin n) (Fin n) E) k.2.1 j)) * X (k.1, j, k.2.2)) P

def polFun {K ι : Type} [CommRing K] {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) K) :
    (ι → Matrix (Fin n) (Fin n) K) → K :=
  fun y => eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P

theorem polFun_apply {K ι : Type} [CommRing K] {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) K)
    (y : ι → Matrix (Fin n) (Fin n) K) : polFun P y = eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P := rfl

open MvPolynomial in
private lemma eval_bind_eq_eval_comp {K σ τ : Type} [CommRing K] (f : σ → MvPolynomial τ K)
    (x : τ → K) (P : MvPolynomial σ K) :
    eval x (bind₁ f P) = eval (fun i => eval x (f i)) P := by
  rw [← aeval_eq_eval, ← aeval_eq_eval, aeval_bind₁]

open MvPolynomial in
theorem _root_.GlobalTheory.IntegralityCompare.eval_twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (x : ι → Matrix (Fin n) (Fin n) ℂ) :
    eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2)
        (_root_.GlobalTheory.IntegralityCompare.twSub emb M s P) =
      (∏ τ, (emb τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
        eval (fun k : ι × Fin n × Fin n =>
          (((M : Matrix (Fin n) (Fin n) E).map (emb k.1)) * x k.1) k.2.1 k.2.2) P := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSub, map_mul, eval_C, eval_bind_eq_eval_comp]
  congr 3
  funext k
  simp [Matrix.mul_apply, eval_sum]

end GlobalTheory.IntegralityCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximal
section
open IsLocalRing

namespace GlobalTheory

theorem exists_eval₂_approx_maximalIdeal_pow_succ {A R : Type} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (hm : (maximalIdeal A).map φ = maximalIdeal R) (θ : R)
    (h1 : ∀ r : R, ∃ P : Polynomial A, r - Polynomial.eval₂ φ θ P ∈ maximalIdeal R)
    (n : ℕ) (x : R) (hx : x ∈ maximalIdeal R ^ n) :
    ∃ P : Polynomial A, Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ n ∧
      x - Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ (n + 1) := by
  have hpow : maximalIdeal R ^ n = (maximalIdeal A ^ n).map φ := by
    rw [Ideal.map_pow, hm]
  rw [hpow] at hx
  unfold Ideal.map at hx
  refine Submodule.span_induction (p := fun x _ => ∃ P : Polynomial A,
      Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ n ∧
      x - Polynomial.eval₂ φ θ P ∈ maximalIdeal R ^ (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨Polynomial.C a, ?_, ?_⟩
    · rw [Polynomial.eval₂_C, hpow]; exact Ideal.mem_map_of_mem φ ha
    · simp
  · exact ⟨0, by simp, by simp⟩
  · rintro x y _ _ ⟨P, hP, hxP⟩ ⟨Q, hQ, hyQ⟩
    refine ⟨P + Q, ?_, ?_⟩
    · rw [Polynomial.eval₂_add]; exact add_mem hP hQ
    · have : x + y - Polynomial.eval₂ φ θ (P + Q) =
          (x - Polynomial.eval₂ φ θ P) + (y - Polynomial.eval₂ φ θ Q) := by
        rw [Polynomial.eval₂_add]; ring
      rw [this]; exact add_mem hxP hyQ
  · rintro r x _ ⟨P, hP, hxP⟩
    obtain ⟨Q, hQ⟩ := h1 r
    refine ⟨Q * P, ?_, ?_⟩
    · rw [Polynomial.eval₂_mul]; exact Ideal.mul_mem_left _ _ hP
    · have : r • x - Polynomial.eval₂ φ θ (Q * P) =
          r * (x - Polynomial.eval₂ φ θ P) +
            (r - Polynomial.eval₂ φ θ Q) * Polynomial.eval₂ φ θ P := by
        rw [Polynomial.eval₂_mul, smul_eq_mul]; ring
      rw [this]
      refine add_mem (Ideal.mul_mem_left _ _ hxP) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hQ hP

theorem exists_poly_sub_mem_maximalIdeal_pow : ∀ {A R : Type} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (φ : A →+* R), (maximalIdeal A).map φ = maximalIdeal R →
    ∀ θ : R, (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) →
    ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n := by
  intro A R _ _ _ _ φ hm θ h1 n r
  simp only [Polynomial.eval_map] at h1 ⊢
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨Q, -, hQ⟩ := exists_eval₂_approx_maximalIdeal_pow_succ φ hm θ h1 n _ hP
    refine ⟨P + Q, ?_⟩
    have : r - Polynomial.eval₂ φ θ (P + Q) =
        r - Polynomial.eval₂ φ θ P - Polynomial.eval₂ φ θ Q := by
      rw [Polynomial.eval₂_add]; ring
    rw [this]; exact hQ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniqueness
section
open IsLocalRing TensorProduct

namespace GlobalTheory

open IsLocalRing TensorProduct in
private lemma mem_ideal_of_sum_mul_mem_of_independent_mod_max {A : Type} [CommRing A] [IsLocalRing A] {κ : Type} [Fintype κ] :
    ∀ (d : ℕ) (C : Fin d → κ → A),
      (∀ c : Fin d → A, (∀ l, ∑ i, c i * C i l ∈ maximalIdeal A) → ∀ i, c i ∈ maximalIdeal A) →
      ∀ (I : Ideal A) (b : Fin d → A), (∀ l, ∑ i, b i * C i l ∈ I) → ∀ i, b i ∈ I := by
  intro d
  induction d with
  | zero => intro C _ I b _ i; exact i.elim0
  | succ d ih =>
    intro C hC I b hb
    have h0 : ∃ l0, C 0 l0 ∉ maximalIdeal A := by
      by_contra h
      push_neg at h
      have := hC (Pi.single 0 1) (fun l => by
        simpa [Fin.sum_univ_succ, Pi.single_apply] using h l) 0
      simp at this
    obtain ⟨l0, hl0⟩ := h0
    set u := C 0 l0 with hu
    have hunit : IsUnit u := (IsLocalRing.mem_maximalIdeal _).not.mp hl0 |> not_not.mp
    let C' : Fin d → κ → A := fun i l => u * C i.succ l - C i.succ l0 * C 0 l
    have hC' : ∀ c : Fin d → A, (∀ l, ∑ i, c i * C' i l ∈ maximalIdeal A) → ∀ i, c i ∈ maximalIdeal A := by
      intro c hc i
      have key := hC (Fin.cons (-(∑ j, c j * C j.succ l0)) (fun j => u * c j)) (fun l => by
        convert hc l using 1
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, C']
        rw [show ∑ i, c i * (u * C i.succ l - C i.succ l0 * C 0 l)
            = ∑ i, u * c i * C i.succ l - (∑ i, c i * C i.succ l0) * C 0 l by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)]
        ring) i.succ
      simp only [Fin.cons_succ] at key
      exact ((Ideal.IsPrime.mem_or_mem inferInstance key).resolve_left hl0)
    have hb' := ih C' hC' I (fun i => b i.succ) (fun l => by
      have e : ∑ i, b i.succ * C' i l = u * (∑ i, b i * C i l) - (∑ i, b i * C i l0) * C 0 l := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp only [C']
        rw [show ∑ i : Fin d, b i.succ * (u * C i.succ l - C i.succ l0 * C 0 l)
            = u * ∑ i : Fin d, b i.succ * C i.succ l - (∑ i : Fin d, b i.succ * C i.succ l0) * C 0 l by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)]
        ring
      rw [e]
      exact I.sub_mem (I.mul_mem_left _ (hb l)) (I.mul_mem_right _ (hb l0)))
    intro i
    refine Fin.cases ?_ (fun j => hb' j) i
    have h1 : b 0 * u ∈ I := by
      have := hb l0
      rw [Fin.sum_univ_succ] at this
      have h2 : ∑ i : Fin d, b i.succ * C i.succ l0 ∈ I :=
        I.sum_mem (fun j _ => I.mul_mem_right _ (hb' j))
      simpa [hu] using I.sub_mem this h2
    obtain ⟨v, hv⟩ := hunit
    have := I.mul_mem_right (↑v⁻¹ : A) h1
    rwa [← hv, mul_assoc, Units.mul_inv, mul_one] at this


open IsLocalRing TensorProduct in
theorem _root_.GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), φ.Flat → (maximalIdeal A).map φ = maximalIdeal R → ∀ (θ : R) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) → (∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A) → ∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n := by
  intro A R _ _ _ _ φ hflat hmax θ q _ _ _ hind n P hdeg hP i
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hflat
  have hsm : ∀ (a : A) (r : R), a • r = φ a * r := fun a r => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hφm : ∀ a ∈ maximalIdeal A, φ a ∈ maximalIdeal R := fun a ha => hmax ▸ Ideal.mem_map_of_mem φ ha
  by_cases hi : i < q.natDegree
  swap
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (not_lt.mp hi))]
    exact Ideal.zero_mem _
  set d := q.natDegree with hd
  rw [← hmax, ← Ideal.map_pow] at hP
  obtain ⟨K, y, g, hg⟩ := Submodule.mem_span_set'.mp hP
  have hb : ∀ k, ∃ b ∈ maximalIdeal A ^ n, φ b = g k := fun k => (g k).2
  choose b hbI hbg using hb
  have hev : (P.map φ).eval θ = ∑ j : Fin d, φ (P.coeff j) * θ ^ (j : ℕ) := by
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (Polynomial.natDegree_map_le) hdeg),
      Finset.sum_range]
    simp [Polynomial.coeff_map]
  have hsum : ∑ k, φ (b k) * y k = (P.map φ).eval θ := by
    rw [← hg]
    exact Finset.sum_congr rfl (fun k _ => by rw [hbg, smul_eq_mul, mul_comm])
  let v : Fin d ⊕ Fin K → R := Sum.elim (fun j => θ ^ (j : ℕ)) y
  let f : Fin d ⊕ Fin K → A := Sum.elim (fun j => P.coeff j) (fun k => - b k)
  have hx : Fintype.linearCombination A v f = 0 := by
    rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
    simp only [v, f, Sum.elim_inl, Sum.elim_inr, hsm, map_neg, neg_mul, Finset.sum_neg_distrib]
    rw [hsum, hev]
    ring
  obtain ⟨k, a, z, hxz, haf⟩ := Module.Flat.exists_factorization_of_apply_eq_zero_of_free hx
  let e : Fin d ⊕ Fin K → Fin d ⊕ Fin K → A := fun x x' => if x = x' then 1 else 0
  let C : Fin d → Fin k → A := fun j l => a (e (Sum.inl j)) l
  let w : Fin k → R := fun l => z (Finsupp.single l 1)
  have hz : ∀ x : Fin k →₀ A, z x = ∑ l, φ (x l) * w l := by
    intro x
    conv_lhs => rw [← Finsupp.univ_sum_single x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => by rw [← Finsupp.smul_single_one, map_smul, hsm])
  have hθ : ∀ j : Fin d, θ ^ (j : ℕ) = ∑ l, φ (C j l) * w l := by
    intro j
    have h1 : θ ^ (j : ℕ) = Fintype.linearCombination A v (e (Sum.inl j)) := by
      rw [Fintype.linearCombination_apply]
      simp [e, v]
    rw [h1, hxz, LinearMap.comp_apply, hz]
  have haf' : ∀ l, ∑ j : Fin d, P.coeff (j : ℕ) * C j l = ∑ k', b k' * a (e (Sum.inr k')) l := by
    intro l
    have h2 := DFunLike.congr_fun haf l
    rw [LinearMap.pi_apply_eq_sum_univ a f, Finsupp.finsetSum_apply, Fintype.sum_sum_type] at h2
    simp only [f, e, C, Sum.elim_inl, Sum.elim_inr, Finsupp.smul_apply, smul_eq_mul, neg_mul,
      Finset.sum_neg_distrib, Finsupp.coe_zero, Pi.zero_apply] at h2
    linear_combination h2
  have hCm : ∀ c : Fin d → A, (∀ l, ∑ j, c j * C j l ∈ maximalIdeal A) → ∀ j, c j ∈ maximalIdeal A := by
    intro c hc j
    let Q : Polynomial A := ∑ j' : Fin d, Polynomial.C (c j') * Polynomial.X ^ (j' : ℕ)
    have hQdeg : Q.natDegree < d := by
      by_cases hQ : Q = 0
      · rw [hQ, Polynomial.natDegree_zero]; exact lt_of_le_of_lt (Nat.zero_le _) j.2
      · exact (Polynomial.natDegree_lt_iff_degree_lt hQ).mpr (Polynomial.degree_sum_fin_lt c)
    have hQc : Q.coeff j = c j := by
      simp [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj]
    have hQe : (Q.map φ).eval θ = ∑ l, φ (∑ j', c j' * C j' l) * w l := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Q, Polynomial.map_sum, Polynomial.eval_finsetSum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, hθ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j' _ => by rw [map_mul]; ring)
    rw [← hQc]
    refine hind Q hQdeg ?_ j
    rw [hQe]
    exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_right _ _ (hφm _ (hc l)))
  exact mem_ideal_of_sum_mul_mem_of_independent_mod_max d C hCm (maximalIdeal A ^ n) (fun j => P.coeff j)
    (fun l => by
      rw [haf' l]
      exact Ideal.sum_mem _ (fun k' _ => Ideal.mul_mem_right _ _ (hbI k'))) ⟨i, hi⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMargin
section
namespace GlobalTheory

private lemma quad_smul {ι : Type} [Fintype ι] (M : ι → ι → ℝ) (a : ℝ) (c : ι → ℝ) :
    ∑ i, ∑ j, (a • c) i * (a • c) j * M i j = a ^ 2 * ∑ i, ∑ j, c i * c j * M i j := by
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

private lemma quad_err {ι : Type} [Fintype ι] (E : ι → ι → ℝ) (η : ℝ) (_hη : 0 ≤ η)
    (hE : ∀ i j, |E i j| ≤ η) (c : ι → ℝ) :
    |∑ i, ∑ j, c i * c j * E i j| ≤ (Fintype.card ι : ℝ) ^ 2 * (‖c‖ ^ 2 * η) := by
  have hc : ∀ i, |c i| ≤ ‖c‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm c i
  calc |∑ i, ∑ j, c i * c j * E i j|
      ≤ ∑ i, ∑ j, |c i * c j * E i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, ‖c‖ ^ 2 * η := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul, sq]
        have h1 := hc i; have h2 := hc j; have h3 := hE i j
        have := abs_nonneg (c i); have := abs_nonneg (c j); have := abs_nonneg (E i j)
        have := norm_nonneg c
        calc |c i| * |c j| * |E i j| ≤ ‖c‖ * ‖c‖ * |E i j| := by gcongr
          _ ≤ ‖c‖ * ‖c‖ * η := by gcongr
    _ = (Fintype.card ι : ℝ) ^ 2 * (‖c‖ ^ 2 * η) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem posDef_quad_margin {ι : Type} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) :
    ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) →
      ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun E _ c hc => absurd (Subsingleton.elim c 0) hc⟩
  set q : (ι → ℝ) → ℝ := fun c => ∑ i, ∑ j, c i * c j * M i j with hq
  have hcont : Continuous q := by
    simp only [hq]; fun_prop
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    (NormedSpace.sphere_nonempty).mpr zero_le_one
  obtain ⟨c₀, hc₀, hmin⟩ :=
    (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl; simp at hc₀
  set μ := q c₀ with hμ
  have hμpos : 0 < μ := hM c₀ hc₀ne
  have hlow : ∀ c : ι → ℝ, c ≠ 0 → μ * ‖c‖ ^ 2 ≤ q c := by
    intro c hc
    have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hmem : ‖c‖⁻¹ • c ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
    have h1 : μ ≤ q (‖c‖⁻¹ • c) := hmin hmem
    have h2 : q (‖c‖⁻¹ • c) = (‖c‖⁻¹) ^ 2 * q c := quad_smul M _ c
    rw [h2] at h1
    have h3 : (‖c‖⁻¹) ^ 2 * ‖c‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]
    calc μ * ‖c‖ ^ 2 ≤ ((‖c‖⁻¹) ^ 2 * q c) * ‖c‖ ^ 2 := by gcongr
      _ = q c := by rw [mul_comm ((‖c‖⁻¹) ^ 2), mul_assoc, h3, mul_one]
  set K : ℝ := (Fintype.card ι : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  refine ⟨μ / (2 * K + 1), div_pos hμpos (by linarith), ?_⟩
  intro E hE c hc
  have hη0 : 0 ≤ μ / (2 * K + 1) := (div_pos hμpos (by linarith)).le
  have herr := quad_err E _ hη0 hE c
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hsplit : ∑ i, ∑ j, c i * c j * (M i j + E i j)
      = q c + ∑ i, ∑ j, c i * c j * E i j := by
    simp only [hq, mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  have hKη : K * (μ / (2 * K + 1)) < μ := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  have hs2 : 0 < ‖c‖ ^ 2 := by positivity
  have := hlow c hc
  have hlow' := (abs_le.mp herr).1
  rw [← hK] at hlow'
  nlinarith [mul_lt_mul_of_pos_right hKη hs2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosSemidefRealOfIntQuadFormNonneg
section
namespace GlobalTheory

open Matrix

theorem intSymm_posSemidef_real :
    ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm →
      (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) →
      (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  intro g B hB hQ
  set M : Matrix (Fin g) (Fin g) ℝ := B.map (Int.cast : ℤ → ℝ) with hM

  set f : (Fin g → ℝ) → ℝ := fun x => dotProduct x (M.mulVec x) with hf
  have hcont : Continuous f := by
    simp only [hf, dotProduct, mulVec]
    fun_prop
  have hscale : ∀ (c : ℝ) (x : Fin g → ℝ), f (c • x) = c ^ 2 * f x := by
    intro c x
    simp only [hf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hint : ∀ v : Fin g → ℤ, f (fun i => (v i : ℝ)) = ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by
    intro v
    simp only [hf, hM, dotProduct, mulVec, Matrix.map_apply]
    push_cast
    rfl
  have hrat : ∀ q : Fin g → ℚ, 0 ≤ f (fun i => (q i : ℝ)) := by
    intro q
    set N : ℕ := ∏ i, (q i).den with hN
    have hNpos : 0 < N := Finset.prod_pos (fun i _ => (q i).den_pos)
    have hdvd : ∀ i, (q i).den ∣ N := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    let v : Fin g → ℤ := fun i => (q i).num * ((N / (q i).den : ℕ) : ℤ)
    have hv : (N : ℝ) • (fun i => (q i : ℝ)) = fun i => (v i : ℝ) := by
      funext i
      have hd : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
      simp only [Pi.smul_apply, smul_eq_mul, v, Int.cast_mul, Int.cast_natCast]
      rw [Nat.cast_div (hdvd i) hd, Rat.cast_def]
      field_simp
    have h1 := hscale (N : ℝ) (fun i => (q i : ℝ))
    rw [hv, hint] at h1
    have h2 : (0 : ℝ) ≤ ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by exact_mod_cast hQ v
    have h3 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    nlinarith
  have hdense : DenseRange (fun q : Fin g → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hall : ∀ x : Fin g → ℝ, 0 ≤ f x := by
    intro x
    have hclosed : IsClosed {x : Fin g → ℝ | 0 ≤ f x} := isClosed_le continuous_const hcont
    have hsub : Set.range (fun q : Fin g → ℚ => fun i => (q i : ℝ)) ⊆ {x | 0 ≤ f x} := by
      rintro _ ⟨q, rfl⟩
      exact hrat q
    have := hdense.closure_range ▸ (closure_minimal hsub hclosed)
    exact this (Set.mem_univ x)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp [hM, conjTranspose_apply, hB.apply i j]
  · simpa [hf] using hall x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatAlternatingOrthogonalOrthogonalLeAlt
section
open Matrix

namespace GlobalTheory

theorem rat_alternating_orthogonal_orthogonal_le :
    ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq →
      Mq.det ≠ 0 → ∀ x : Fin r → ℚ,
      (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by
  intro r Mq V hT hdet x hx
  have hB : ∀ u v : Fin r → ℚ, Matrix.toBilin' Mq u v = u ⬝ᵥ Mq *ᵥ v :=
    fun u v => Matrix.toBilin'_apply' Mq u v
  have hanti : ∀ u v : Fin r → ℚ, u ⬝ᵥ Mq *ᵥ v = -(v ⬝ᵥ Mq *ᵥ u) := by
    intro u v
    have h1 : v ⬝ᵥ Mqᵀ *ᵥ u = u ⬝ᵥ Mq *ᵥ v := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    rw [← h1, hT, Matrix.neg_mulVec, dotProduct_neg]
  have hrefl : (Matrix.toBilin' Mq).IsRefl := by
    intro u v h
    rw [hB] at h ⊢
    rw [hanti, h, neg_zero]
  have hnd : (Matrix.toBilin' Mq).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl V,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy
  show Matrix.toBilin' Mq y x = 0
  rw [hB, hanti, hx y ?_, neg_zero]
  intro w hw
  have h := hy w hw
  change Matrix.toBilin' Mq w y = 0 at h
  rw [hB, hanti] at h
  exact neg_eq_zero.mp h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem residueField_map_finite_of_quasiFinite {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (h : f.QuasiFinite) :
    (IsLocalRing.ResidueField.map f).Finite := by
  algebraize [f]
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Algebra.QuasiFinite R (IsLocalRing.ResidueField S) :=
    Algebra.QuasiFinite.of_surjective_algHom (IsScalarTower.toAlgHom R S _)
      IsLocalRing.residue_surjective
  have : Algebra.QuasiFinite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    .of_restrictScalars R _ _
  have hfin : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.QuasiFinite.iff_of_isArtinianRing.mp this
  have heq : IsLocalRing.ResidueField.map f =
      algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  rw [heq]
  exact RingHom.finite_algebraMap.mpr hfin

theorem residueFieldMap_finite_of_locallyQuasiFinite {Y Z : Scheme.{0}} (g : Y ⟶ Z)
    [LocallyQuasiFinite g] (y : Y) : (g.residueFieldMap y).hom.Finite := by
  have hq : (g.stalkMap y).hom.QuasiFinite := g.quasiFiniteAt y
  exact residueField_map_finite_of_quasiFinite _ hq

end GlobalTheory
end

