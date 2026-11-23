module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivative
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.UnramSimpleGen

theorem not_mem_sq_of_derivative : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (p : HeightOneSpectrum (𝓞 E)) (P : HeightOneSpectrum (𝓞 E')) (β : 𝓞 E') (f : Polynomial ℤ),
    f.Monic → Polynomial.aeval β f = 0 → Algebra.adjoin E {(β : E')} = ⊤ →
    (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 E') x ∈ P.asIdeal ↔ x ∈ p.asIdeal) →
    Polynomial.aeval β (Polynomial.derivative f) ∉ P.asIdeal →
    ∀ c : 𝓞 E, c ∉ p.asIdeal ^ 2 → algebraMap (𝓞 E) (𝓞 E') c ∉ P.asIdeal ^ 2 := by
  intro E E' _ _ _ _ _ p P β f _ hβ hadj hPp hder c hc

  have hmem := aeval_derivative_mem_differentIdeal (𝓞 E) E E' β hadj
  have hint : IsIntegral (𝓞 E) β := Algebra.IsIntegral.isIntegral β
  have hdvd : minpoly (𝓞 E) β ∣ f.map (algebraMap ℤ (𝓞 E)) :=
    minpoly.isIntegrallyClosed_dvd hint (by rw [aeval_map_algebraMap]; exact hβ)
  obtain ⟨k, hk⟩ := hdvd
  have hfd : aeval β (derivative f) = aeval β (derivative (minpoly (𝓞 E) β)) * aeval β k := by
    have h := congrArg (fun q => aeval β (derivative q)) hk
    simp only [derivative_mul, map_add (f := _), map_mul, minpoly.aeval, zero_mul, add_zero] at h
    rw [← h, derivative_map, aeval_map_algebraMap]
  have hnd : ¬ P.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 E') := by
    intro h
    apply hder
    rw [hfd]
    exact Ideal.mul_mem_right _ _ ((Ideal.dvd_iff_le.1 h) hmem)

  haveI := p.isMaximal
  have hnle : ¬ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) ≤ P.asIdeal ^ 2 := by
    intro hle
    have h := pow_sub_one_dvd_differentIdeal (𝓞 E) (p := p.asIdeal) P.asIdeal 2 p.ne_bot
      (Ideal.dvd_iff_le.2 hle)
    exact hnd (by simpa using h)

  by_cases hcp : c ∈ p.asIdeal
  swap
  · intro h
    exact hcp ((hPp c).1 (Ideal.pow_le_self two_ne_zero h))

  obtain ⟨J, hJ⟩ : p.asIdeal ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hcp)
  have hJp : ¬ J ≤ p.asIdeal := by
    intro h
    apply hc
    have h1 : Ideal.span {c} ≤ p.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h1 (Ideal.mem_span_singleton_self c)
  obtain ⟨s, hsJ, hsp⟩ := Set.not_subset.1 hJp
  have hps : p.asIdeal * Ideal.span {s} ≤ Ideal.span {c} := by
    rw [hJ]; exact Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 hsJ)
  intro hcP
  apply hnle
  have hs' : algebraMap (𝓞 E) (𝓞 E') s ∉ P.asIdeal := fun h => hsp ((hPp s).1 h)
  have hcop : IsCoprime P.asIdeal (Ideal.span {algebraMap (𝓞 E) (𝓞 E') s}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    refine P.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hs' ?_)
    rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hdiv : P.asIdeal ^ 2 ∣ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) *
      Ideal.span {algebraMap (𝓞 E) (𝓞 E') s} := by
    rw [Ideal.dvd_iff_le]
    calc p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) * Ideal.span {algebraMap (𝓞 E) (𝓞 E') s}
        = (p.asIdeal * Ideal.span {s}).map (algebraMap (𝓞 E) (𝓞 E')) := by
          rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
      _ ≤ (Ideal.span {c}).map (algebraMap (𝓞 E) (𝓞 E')) := Ideal.map_mono hps
      _ = Ideal.span {algebraMap (𝓞 E) (𝓞 E') c} := by rw [Ideal.map_span, Set.image_singleton]
      _ ≤ P.asIdeal ^ 2 := (Ideal.span_singleton_le_iff_mem _).2 hcP
  exact Ideal.dvd_iff_le.1 ((hcop.pow_left).dvd_of_dvd_mul_right hdiv)

end GlobalTheory.UnramSimpleGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotSqMulUnit
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise

namespace GlobalTheory.UnramSquare

theorem not_sq_mul_unit (K : Type) [Field K] [NumberField K] (Q : Ideal (𝓞 K)) [Q.IsMaximal] :
    Algebra.IsUnramifiedAt ℤ Q → ∀ p : ℕ, p.Prime → (p : 𝓞 K) ∈ Q → ∀ y u : 𝓞 K, u ∉ Q →
      y ^ 2 = (p : 𝓞 K) * u → False := by
  intro h p hp hpQ y u hu hyu
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hPr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hPr.isMaximal (by simpa using hpZ.ne_zero)
  haveI hQp : Q.IsPrime := inferInstance
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hpQ
  letI := Localization.AtPrime.algebraOfLiesOver (Ideal.span {(p : ℤ)}) Q
  have h2 := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (Ideal.span {(p : ℤ)}) Q).1 h).2
  have hyQ : y ∈ Q := hQp.mem_of_pow_mem 2 (by rw [hyu]; exact Q.mul_mem_right _ hpQ)
  have h3 : algebraMap (𝓞 K) (Localization.AtPrime Q) y ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q y).2 hyQ
  rw [← h2, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at h3
  obtain ⟨w, hw⟩ := h3
  obtain ⟨⟨z, t⟩, hzt⟩ := IsLocalization.surj Q.primeCompl w
  have htz : (t : 𝓞 K) * y = p * z := by
    apply IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
    simp only at hzt
    rw [map_mul, map_mul, ← hw, ← hzt]
    simp only [map_natCast, eq_intCast, Int.cast_natCast]
    ring
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4 : (t : 𝓞 K) ^ 2 * u = p * z ^ 2 := by
    apply mul_left_cancel₀ hp0
    calc (p : 𝓞 K) * ((t : 𝓞 K) ^ 2 * u) = (t : 𝓞 K) ^ 2 * y ^ 2 := by rw [hyu]; ring
      _ = ((t : 𝓞 K) * y) ^ 2 := by ring
      _ = p * (p * z ^ 2) := by rw [htz]; ring
  have h5 : (t : 𝓞 K) ^ 2 * u ∈ Q := by rw [h4]; exact Q.mul_mem_right _ hpQ
  rcases hQp.mem_or_mem h5 with h6 | h6
  · exact t.2 (hQp.mem_of_pow_mem 2 h6)
  · exact hu h6

end GlobalTheory.UnramSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotXPowSuccDvdDetOfFirstOrderKernelEqZero
section
open Polynomial

namespace GlobalTheory

theorem exists_det_one_mul_mul_eq_diagonal {K : Type} [Field K] {a : ℕ}
    (A : Matrix (Fin a) (Fin a) K) :
    ∃ (P Q : Matrix (Fin a) (Fin a) K) (D : Fin a → K),
      P.det = 1 ∧ Q.det = 1 ∧ P * A * Q = Matrix.diagonal D := by
  obtain ⟨L, L', D, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal A
  exact ⟨_, _, D, Matrix.TransvectionStruct.det_toMatrix_prod L,
    Matrix.TransvectionStruct.det_toMatrix_prod L', h⟩

theorem not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero :
    ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (0 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m → ¬ (Polynomial.X : Polynomial K) ^ (m + 1) ∣ Ψ.det := by
  classical
  intro K _ a m Ψ hker hm hdvd
  set A := Ψ.map fun p => p.coeff 0 with hA
  set B := Ψ.map fun p => p.coeff 1 with hB
  have hker' : ∀ x0 x1 : Fin a → K, A.mulVec x0 = 0 → B.mulVec x0 + A.mulVec x1 = 0 → x0 = 0 := by
    intro x0 x1 h0 h1
    by_contra hne
    refine hker (fun _ => x0) (fun _ => x1) (fun _ => ⟨h0, h1⟩) ?_
    exact (linearIndependent_unique_iff (v := fun _ : Fin 1 => x0)).2 hne
  obtain ⟨P, Q, D, hP, hQ, hD⟩ := exists_det_one_mul_mul_eq_diagonal A
  have hPu : IsUnit P.det := hP ▸ isUnit_one
  have hQu : IsUnit Q.det := hQ ▸ isUnit_one
  have hPinj : ∀ v : Fin a → K, P.mulVec v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero hPu.ne_zero hv
  have hQinj : ∀ v : Fin a → K, Q.mulVec v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero hQu.ne_zero hv

  have hcard : (Finset.univ.filter fun i => D i = 0).card ≤ m := by
    have h1 : A.rank = Fintype.card {i // D i ≠ 0} := by
      rw [← Matrix.rank_diagonal, ← hD, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu,
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu]
    have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h3 : Fintype.card {i // D i ≠ 0} = a - Fintype.card {i // D i = 0} := by
      rw [Fintype.card_subtype_compl]; simp
    have h4 : Fintype.card {i // D i = 0} = (Finset.univ.filter fun i => D i = 0).card :=
      Fintype.card_subtype _
    have h5 : Fintype.card {i // D i = 0} ≤ a := by
      simpa using Fintype.card_subtype_le (fun i => D i = 0)
    rw [Matrix.rank] at h1
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    omega
  have hAQ : ∀ v : Fin a → K, P.mulVec (A.mulVec (Q.mulVec v)) = fun i => D i * v i := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]
    ext i
    rw [Matrix.mulVec_diagonal]
  have hcol : ∀ i j, D j = 0 → (A * Q) i j = 0 := by
    intro i j hj
    have h1 : A.mulVec (Q.mulVec (Pi.single j 1)) = 0 := by
      apply hPinj
      rw [hAQ]
      ext k
      by_cases hk : k = j
      · subst hk; simp [hj]
      · simp [hk]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h1
    exact congrFun h1 i
  set Θ : Matrix (Fin a) (Fin a) K[X] := Ψ * Q.map C with hΘ
  have hΘ0 : ∀ i j, (Θ i j).coeff 0 = (A * Q) i j := by
    intro i j
    simp [hΘ, hA, Matrix.mul_apply, Polynomial.finsetSum_coeff]
  have hΘ1 : ∀ i j, (Θ i j).coeff 1 = (B * Q) i j := by
    intro i j
    simp [hΘ, hB, Matrix.mul_apply, Polynomial.finsetSum_coeff]
  set Θ' : Matrix (Fin a) (Fin a) K[X] :=
    Matrix.of fun i j => if D j = 0 then (Θ i j).divX else Θ i j with hΘ'
  have hfac : Θ = Θ' * Matrix.diagonal fun j => if D j = 0 then (X : K[X]) else 1 := by
    ext1 i j
    rw [Matrix.mul_diagonal]
    by_cases hj : D j = 0
    · have := Polynomial.divX_mul_X_add (Θ i j)
      rw [hΘ0, hcol i j hj] at this
      simpa [hΘ', hj] using this.symm
    · simp [hΘ', hj]
  have hdetΘ : Θ.det = Ψ.det := by
    have : (Q.map C).det = (1 : K[X]) := by
      have := RingHom.map_det (C : K →+* K[X]) Q
      rw [hQ, map_one] at this
      exact this.symm
    rw [hΘ, Matrix.det_mul, this, mul_one]
  have hdet : Ψ.det = Θ'.det * X ^ (Finset.univ.filter fun i => D i = 0).card := by
    rw [← hdetΘ]
    conv_lhs => rw [hfac]
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite]
    simp
  set T : Matrix (Fin a) (Fin a) K := Θ'.map fun p => p.coeff 0 with hT
  have hTinj : ∀ y : Fin a → K, T.mulVec y = 0 → y = 0 := by
    intro y hy
    set y0 : Fin a → K := fun j => if D j = 0 then y j else 0 with hy0
    set y1 : Fin a → K := fun j => if D j = 0 then 0 else y j with hy1
    have e0 : A.mulVec (Q.mulVec y0) = 0 := by
      apply hPinj
      rw [hAQ]
      ext k
      by_cases hk : D k = 0 <;> simp [hy0, hk]
    have e1 : B.mulVec (Q.mulVec y0) + A.mulVec (Q.mulVec y1) = 0 := by
      rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      ext i
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : D j = 0
      · simp [hT, hΘ', hy0, hy1, hj, Polynomial.coeff_divX, hΘ1]
      · simp [hT, hΘ', hy0, hy1, hj, hΘ0]
    have z0 : y0 = 0 := hQinj _ (hker' _ _ e0 e1)
    rw [z0, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add] at e1
    have z1 := hAQ y1
    rw [e1, Matrix.mulVec_zero] at z1
    ext k
    by_cases hk : D k = 0
    · simpa [hy0, hk] using congrFun z0 k
    · simpa [hy1, hk] using (congrFun z1 k).symm
  have hTdet : T.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    exact hv (hTinj v hv0)
  apply hTdet
  have hc : T.det = Θ'.det.coeff 0 := by
    have := RingHom.map_det (Polynomial.constantCoeff : K[X] →+* K) Θ'
    exact this.symm
  rw [hc, ← Polynomial.X_dvd_iff]
  set ν := (Finset.univ.filter fun i => D i = 0).card
  have h1 : (X : K[X]) * X ^ ν ∣ Θ'.det * X ^ ν := by
    rw [← hdet, ← pow_succ']
    exact (pow_dvd_pow _ (by omega)).trans hdvd
  exact (mul_dvd_mul_iff_right (pow_ne_zero _ Polynomial.X_ne_zero)).1 h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrime
section
open scoped PowerSeries Pointwise

namespace GlobalTheory

theorem numerical_bounds_of_forty_mul_lt : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 →
    40 * (H * N ^ 2 + N ^ 3) < l →
    2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧
      8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  intro l H N η r hN hη hηH hr hl
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hH : 2 ≤ H := by omega
  have hHN : 4 * H ≤ H * N ^ 2 := by nlinarith
  have hN3 : 8 ≤ N ^ 3 := by
    have : N ^ 3 = N * N ^ 2 := by ring
    nlinarith
  have hNr : 4 * (N * r) ≤ N ^ 3 := by
    have : N ^ 3 = N * N ^ 2 := by ring
    rw [this]; nlinarith
  have hsub : (N - 1) * r ≤ N * r := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hηr : 4 * (η * r) ≤ H * N ^ 2 := by
    have : η * r ≤ H * r := Nat.mul_le_mul_right _ hηH.le
    nlinarith
  have hNη : (N + 2) * η ≤ H * N ^ 2 := by
    have h1 : (N + 2) * η ≤ (N + 2) * H := Nat.mul_le_mul_left _ hηH.le
    have h2 : N + 2 ≤ N ^ 2 := by nlinarith
    have h3 : (N + 2) * H ≤ N ^ 2 * H := Nat.mul_le_mul_right _ h2
    nlinarith
  have hrη : r * η ≤ H * N ^ 2 := by
    have : r * η ≤ r * H := Nat.mul_le_mul_left _ hηH.le
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 2 * (N - 1) * r = 2 * ((N - 1) * r) := by ring
    rw [this]; nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · have : 4 * η * r = 4 * (η * r) := by ring
    rw [this]; nlinarith
  · have : (r + 2) * η = r * η + 2 * η := by ring
    rw [this]; nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXPowPrimePowSubOneMemSpan
section
namespace GlobalTheory

theorem sq_dvd_choose_prime_pow (l : ℕ) (hl : l.Prime) (b k : ℕ) (hb : 1 ≤ b) (hk0 : k ≠ 0)
    (hk : k < l ^ (b - 1)) : l ^ 2 ∣ (l ^ b).choose k := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨m, hm⟩ : ∃ m, l ^ b = m + 1 := Nat.exists_eq_succ_of_ne_zero (pow_pos hl.pos b).ne'
  have hkb : j + 1 ≤ l ^ b := le_trans hk.le (Nat.pow_le_pow_right hl.pos (Nat.sub_le b 1))
  have hC : (l ^ b).choose (j + 1) ≠ 0 := (Nat.choose_pos hkb).ne'

  have hid : l ^ b * m.choose j = (l ^ b).choose (j + 1) * (j + 1) := by
    rw [hm]; exact Nat.add_one_mul_choose_eq m j

  have hv : padicValNat l (j + 1) < b - 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : l ^ padicValNat l (j + 1) ≤ j + 1 :=
      Nat.le_of_dvd (Nat.succ_pos j) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have h2 : l ^ (b - 1) ≤ l ^ padicValNat l (j + 1) := Nat.pow_le_pow_right hl.pos hcon
    omega
  have hdiv : l ^ b ∣ (l ^ b).choose (j + 1) * (j + 1) := by
    rw [← hid]; exact dvd_mul_right _ _
  have hne : (l ^ b).choose (j + 1) * (j + 1) ≠ 0 := mul_ne_zero hC (Nat.succ_ne_zero j)
  rw [(by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hne, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hC (by omega : j + 1 ≠ 0)] at hdiv
  exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hC).mpr (by omega)

theorem one_add_X_pow_prime_pow_sub_one_mem_span (l : ℕ) [Fact l.Prime] (b : ℕ) (hb : 1 ≤ b) :
    ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) ∈
      Ideal.span {((l : Polynomial ℤ)) ^ 2, Polynomial.X ^ (l ^ (b - 1))} := by

  have key : ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) =
      ∑ i ∈ Finset.range (l ^ b),
        Polynomial.X ^ (i + 1) * (((l ^ b).choose (i + 1) : ℕ) : Polynomial ℤ) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  by_cases hi : i + 1 < l ^ (b - 1)
  ·
    obtain ⟨c, hc⟩ := sq_dvd_choose_prime_pow l (Fact.out) b (i + 1) hb (Nat.succ_ne_zero i) hi
    rw [hc, Nat.cast_mul, Nat.cast_pow, mul_left_comm]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  ·
    push_neg at hi
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    rw [hd, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneSubSumLeProdOneSubRange
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem one_sub_sum_le_prod_one_sub_range (x : ℕ → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (r : ℕ) : 1 - ∑ i ∈ Finset.range r, x i ≤ ∏ i ∈ Finset.range r, (1 - x i) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hS : 0 ≤ ∑ i ∈ Finset.range n, x i := Finset.sum_nonneg (fun i _ => h0 i)
    have hx1 : 0 ≤ 1 - x n := by linarith [h1 n]
    have := mul_le_mul_of_nonneg_right ih hx1
    nlinarith [h0 n]

theorem sum_rpow_sub_le (q : ℝ) (r : ℕ) (σ : ℝ) (hq : 2 ≤ q) (hσ : (r : ℝ) + 5 / 2 ≤ σ) :
    ∑ i ∈ Finset.range r, q ^ ((i : ℝ) - σ) ≤ 2 / q ^ 3 := by
  have hq0 : 0 < q := by linarith
  have hterm : ∀ i : ℕ, q ^ ((i : ℝ) - σ) = q ^ i / q ^ σ := by
    intro i; rw [Real.rpow_sub hq0, Real.rpow_natCast]
  simp_rw [hterm]
  rw [← Finset.sum_div, geom_sum_eq (by linarith : q ≠ 1)]
  have hqs : 0 < q ^ σ := Real.rpow_pos_of_pos hq0 σ
  have hrs : q ^ r / q ^ σ ≤ 1 / q ^ 2 := by
    have h1 : q ^ r / q ^ σ = q ^ ((r : ℝ) - σ) := by rw [Real.rpow_sub hq0, Real.rpow_natCast]
    have h2 : q ^ ((r : ℝ) - σ) ≤ q ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : q ^ (-2 : ℝ) = 1 / q ^ 2 := by
      rw [Real.rpow_neg hq0.le]; norm_num
    rw [h1]; linarith
  have hq1 : 0 < q - 1 := by linarith
  have hpr : 0 < q ^ r := pow_pos hq0 r
  calc (q ^ r - 1) / (q - 1) / q ^ σ ≤ q ^ r / (q - 1) / q ^ σ := by
        gcongr; linarith
    _ = (q ^ r / q ^ σ) / (q - 1) := by ring
    _ ≤ (1 / q ^ 2) / (q - 1) := by gcongr
    _ ≤ 2 / q ^ 3 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hq0 2, pow_pos hq0 3]

theorem lattice_zeta_sq_bound : ∀ (q : ℝ) (r : ℕ) (σ : ℝ), 2 ≤ q → (r : ℝ) + 5 / 2 ≤ σ →
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 < 1 ∧
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 ≤ 16 * q ^ (-(3 : ℝ)) := by
  intro q r σ hq hσ
  have hq0 : 0 < q := by linarith
  set x : ℕ → ℝ := fun i => q ^ ((i : ℝ) - σ) with hx
  have hS := sum_rpow_sub_le q r σ hq hσ
  have hq3 : 8 ≤ q ^ 3 := by nlinarith [sq_nonneg q, mul_le_mul hq hq (by norm_num) hq0.le]
  set w : ℝ := 1 / q ^ 3 with hw
  have hw0 : 0 < w := by positivity
  have hw8 : w ≤ 1 / 8 := by
    rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hq3
  have h0 : ∀ i, 0 ≤ x i := fun i => (Real.rpow_pos_of_pos hq0 _).le

  have hD := one_sub_sum_le_prod_one_sub_range (fun i => min (x i) 1)
    (fun i => le_min (h0 i) zero_le_one) (fun i => min_le_right _ _) r
  have hmin : ∀ i ∈ Finset.range r, min (x i) 1 = x i := by
    intro i hi
    apply min_eq_left
    have : x i ≤ ∑ j ∈ Finset.range r, x j :=
      Finset.single_le_sum (fun j _ => h0 j) hi
    have : 2 / q ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  rw [Finset.sum_congr rfl hmin, Finset.prod_congr rfl (fun i hi => by rw [hmin i hi])] at hD
  set D := ∏ i ∈ Finset.range r, (1 - x i) with hDdef
  have h2w : 2 / q ^ 3 = 2 * w := by rw [hw]; ring
  have hDlow : 1 - 2 * w ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hP : ∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹ = D⁻¹ := by
    rw [Finset.prod_inv_distrib]
  have hrhs : 16 * q ^ (-(3 : ℝ)) = 16 * w := by
    rw [Real.rpow_neg hq0.le, hw]; norm_num
  rw [hP, hrhs]
  have ha : 0 < 1 - 2 * w := by linarith
  have hPle : D⁻¹ ≤ (1 - 2 * w)⁻¹ := inv_anti₀ ha hDlow
  have hP0 : 0 ≤ D⁻¹ := inv_nonneg.mpr hDpos.le
  have hsq : D⁻¹ ^ 2 ≤ ((1 - 2 * w)⁻¹) ^ 2 := pow_le_pow_left₀ hP0 hPle 2
  have hkey : ((1 - 2 * w)⁻¹) ^ 2 ≤ 1 + 16 * w := by
    rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  have hkey2 : ((1 - 2 * w)⁻¹) ^ 2 < 2 := by
    rw [inv_pow, inv_lt_iff_one_lt_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  constructor <;> linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfPerfectOfDvdSubAdicSeparated
section
open scoped NNReal

namespace GlobalTheory

theorem ringHom_eq_of_perfect_of_dvd_sub :
    ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  intro l _ R O _ _ _ _ _ x e he hH ψ ψ' h
  ext y
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  obtain ⟨z, rfl⟩ : ∃ z : R, z ^ l ^ n = y :=
    ⟨(iterateFrobeniusEquiv R l n).symm y, by
      have hs := (iterateFrobeniusEquiv R l n).apply_symm_apply y
      rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at hs⟩
  rw [map_pow, map_pow, ← sub_pow_char_pow]
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hn : n ≤ e * l ^ n :=
    (Nat.lt_pow_self (by omega)).le.trans (Nat.le_mul_of_pos_left _ he)
  exact (pow_dvd_pow x hn).trans (by rw [pow_mul]; exact pow_dvd_pow_of_dvd (h z) _)

end GlobalTheory
end

