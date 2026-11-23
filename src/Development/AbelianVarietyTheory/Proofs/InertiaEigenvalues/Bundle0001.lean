module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddLeOfStrictAnti
section
namespace GlobalTheory.StrictAntiAddLe

theorem add_le_of_strictAnti : ∀ {m : ℕ} {s : Fin m → ℕ}, StrictAnti s →
    ∀ (k : ℕ) (i j : Fin m), (↑j : ℕ) = (↑i : ℕ) + k → s j + k ≤ s i := by
  intro m s hs k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hlt : (i : ℕ) + k < m := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hlt⟩ rfl
    have h2 : s j < s ⟨(i : ℕ) + k, hlt⟩ := by
      apply hs
      rw [Fin.lt_def]
      show (i : ℕ) + k < (j : ℕ)
      omega
    omega

end GlobalTheory.StrictAntiAddLe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddMulInvMem
section
universe u_1

namespace GlobalTheory.AddMulInvMembership

theorem add_mul_inv_mem :
    (let d1 : {K : Type u_1} → [inst : Field K] → Subring K → K → K → Prop :=
      @(fun {K : Type u_1} [Field K] (S : Subring K) (π a : K) ↦ a * π⁻¹ ∈ S);
    ∀ {K : Type u_1} [inst : Field K] [StarRing K] {S : Subring K} {π a b : K},
      d1 S π a → d1 S π b → d1 S π (a + b)) := by
  intro d1 K _ _ S π a b ha hb
  show (a + b) * π⁻¹ ∈ S
  rw [add_mul]
  exact S.add_mem ha hb

end GlobalTheory.AddMulInvMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValuationNonnegRingOfIntegersNumberField
section
open NumberField

namespace GlobalTheory

theorem addValuation_nonneg_of_ringOfIntegers :
    ∀ (L : Type) [Field L] [NumberField L] (v : AddValuation L (WithTop ℤ)) (a : 𝓞 L),
      0 ≤ v (a : L) := by
  intro L _ _ v a
  have hZ : ∀ m : ℤ, 0 ≤ v (m : L) := by
    intro m
    induction m using Int.induction_on with
    | zero => simp [AddValuation.map_zero]
    | succ k ih =>
      rw [Int.cast_add, Int.cast_one]
      exact AddValuation.map_le_add v ih (by rw [AddValuation.map_one])
    | pred k ih =>
      rw [Int.cast_sub, Int.cast_one]
      exact AddValuation.map_le_sub v ih (by rw [AddValuation.map_one])
  by_contra hneg
  push_neg at hneg
  obtain ⟨f, hm, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe a
  set x : L := (a : L) with hx
  have hxtop : v x ≠ ⊤ := ne_top_of_lt hneg
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hxtop
  have hk0 : k < 0 := by
    rw [← hk] at hneg
    exact_mod_cast hneg
  by_cases hn : f.natDegree = 0
  · rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    have hc : c = 1 := by
      have h1 := hm.leadingCoeff
      rwa [Polynomial.leadingCoeff_C] at h1
    subst hc
    simp at hf
  simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
    one_mul, add_eq_zero_iff_eq_neg] at hf
  apply_fun v at hf
  rw [AddValuation.map_neg, AddValuation.map_pow, ← hk] at hf
  have hlt : ((f.natDegree • k : ℤ) : WithTop ℤ) <
      v (∑ i ∈ Finset.range f.natDegree, (algebraMap ℤ L) (f.coeff i) * x ^ i) := by
    apply AddValuation.map_lt_sum v (WithTop.coe_ne_top)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [AddValuation.map_mul, AddValuation.map_pow, ← hk, eq_intCast]
    calc ((f.natDegree • k : ℤ) : WithTop ℤ) < ((i • k : ℤ) : WithTop ℤ) := by
          rw [WithTop.coe_lt_coe, nsmul_eq_mul, nsmul_eq_mul]
          have : (i : ℤ) < f.natDegree := by exact_mod_cast hi
          nlinarith
      _ = i • (k : WithTop ℤ) := by rw [WithTop.coe_nsmul]
      _ ≤ v ((f.coeff i : ℤ) : L) + i • (k : WithTop ℤ) := le_add_of_nonneg_left (hZ _)
  rw [WithTop.coe_nsmul, hf] at hlt
  exact lt_irrefl _ hlt

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditivePolyTaylorCoeffSubNormLe
section
open Polynomial

namespace GlobalTheory

theorem additive_poly_taylor_coeff_sub_norm_le :
    ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 →
      ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  intro l hl E a W ha hW j hj
  have hp : l.Prime := hl.out
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_
  have hak : ‖a k‖ ≤ 1 := ha k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [Polynomial.taylor_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_pow]
  rcases lt_trichotomy j (l ^ k) with h | h | h
  · have hne : j ≠ l ^ k := h.ne
    simp only [hne, if_false, mul_zero, sub_zero]
    obtain ⟨m, hm⟩ : l ∣ (l ^ k).choose j := hp.dvd_choose_pow (by omega) h.ne
    rw [hm, Nat.cast_mul, norm_mul, norm_mul, norm_mul]
    have h1 : ‖W ^ (l ^ k - j)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hW
    have h2 : ‖(m : ℂ_[l])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m
    calc ‖a k‖ * (‖W ^ (l ^ k - j)‖ * (‖(l : ℂ_[l])‖ * ‖(m : ℂ_[l])‖))
        ≤ 1 * (1 * (‖(l : ℂ_[l])‖ * 1)) := by gcongr
      _ = ‖(l : ℂ_[l])‖ := by ring
  · subst h
    simp
  · have hne : j ≠ l ^ k := h.ne'
    simp only [hne, if_false, mul_zero, sub_zero, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfect
section
namespace GlobalTheory.PerfectCompletion

section General

variable {V : Type} [CommRing V] (x : V)

theorem eval_eq_zero_iff (n : ℕ) (y : AdicCompletion (Ideal.span {x}) V) :
    AdicCompletion.eval (Ideal.span {x}) V n y = 0 ↔
      (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ n ∣ y := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton x),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem complete :
    IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x})
      (AdicCompletion (Ideal.span {x}) V) := by
  have h := AdicCompletion.isAdicComplete (M := V) (Submodule.fg_span_singleton x)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {x}) V),
    Ideal.map_span, Set.image_singleton] at h
  exact h

theorem dense (y : AdicCompletion (Ideal.span {x}) V) (r : ℕ) :
    ∃ (s : V) (z : AdicCompletion (Ideal.span {x}) V),
      y = algebraMap V _ s + (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r * z := by
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {x}) V r y)
  have : AdicCompletion.eval (Ideal.span {x}) V r (y - algebraMap V _ s) = 0 := by
    rw [map_sub, ← hs, sub_eq_zero]
    rfl
  obtain ⟨z, hz⟩ := (eval_eq_zero_iff x r _).1 this
  exact ⟨s, z, by rw [← hz]; ring⟩

theorem dvd_iff (s : V) (r : ℕ) :
    (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r ∣ algebraMap V _ s ↔ x ^ r ∣ s := by
  rw [← eval_eq_zero_iff]
  have : AdicCompletion.eval (Ideal.span {x}) V r (algebraMap V _ s) =
      Submodule.Quotient.mk s := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem sModEq_iff {C : Type} [CommRing C] (c : C) (n : ℕ) (u v : C) :
    u ≡ v [SMOD (Ideal.span {c} ^ n • ⊤ : Submodule C C)] ↔ c ^ n ∣ u - v := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

end General

section Perfect

variable (l : ℕ) [Fact l.Prime] {V : Type} [CommRing V] [CharP V l] [PerfectRing V l]

theorem pow_root (c : V) : ((frobeniusEquiv V l).symm c) ^ l = c := by
  have := (frobeniusEquiv V l).apply_symm_apply c
  rwa [frobeniusEquiv_apply, frobenius_def] at this

theorem dvd_of_pow_dvd_pow (x s : V) (n : ℕ) (h : x ^ (l * n) ∣ s ^ l) : x ^ n ∣ s := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(frobeniusEquiv V l).symm c, (frobeniusEquiv V l).injective ?_⟩
  rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, hc, mul_pow,
    pow_root, ← pow_mul, mul_comm n l]

end Perfect

theorem perfect : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l]
    [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧
      Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  intro l hl V _ _ _ x
  set C := AdicCompletion (Ideal.span {x}) V
  set X := algebraMap V C x with hX
  have h0 : ((l : ℕ) : C) = 0 := by
    rw [← map_natCast (algebraMap V C), CharP.cast_eq_zero, map_zero]
  refine ⟨h0, ?_⟩
  rcases subsingleton_or_nontrivial C with hC | hC
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨y, Subsingleton.elim _ _⟩⟩
  haveI : CharP C l := (CharP.charP_iff_prime_eq_zero hl.out).mpr h0
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hle : ∀ n : ℕ, n ≤ l * n := fun n => Nat.le_mul_of_pos_left n hl.out.pos
  refine ⟨fun y z hyz => ?_, fun y => ?_⟩
  ·
    have hw : (y - z) ^ l = 0 := by
      simp only at hyz
      rw [sub_pow_char, hyz, sub_self]
    rw [← sub_eq_zero]
    set w := y - z
    refine AdicCompletion.ext fun n => ?_
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, map_zero, eval_eq_zero_iff]
    obtain ⟨s, t, hst⟩ := dense x w (l * n)
    have h1 : X ^ (l * n) ∣ algebraMap V C (s ^ l) := by
      have e : algebraMap V C (s ^ l) = -((X ^ (l * n)) ^ l * t ^ l) := by
        rw [map_pow, eq_neg_iff_add_eq_zero, ← mul_pow, ← add_pow_char, ← hst, hw]
      rw [e, dvd_neg]
      exact dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _
    rw [dvd_iff] at h1
    have h2 := dvd_of_pow_dvd_pow l x s n h1
    rw [hst]
    refine dvd_add ?_ (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)
    rw [dvd_iff]
    exact h2
  ·
    choose s t hst using fun n => dense x y (l * n)
    set b : ℕ → V := fun n => (frobeniusEquiv V l).symm (s n) with hb
    have hbs : ∀ n, b n ^ l = s n := fun n => pow_root l (s n)
    have hcau : ∀ {m n : ℕ}, m ≤ n →
        algebraMap V C (b m) ≡ algebraMap V C (b n) [SMOD (Ideal.span {X} ^ m • ⊤ : Submodule C C)] := by
      intro m n hmn
      rw [sModEq_iff, ← map_sub, dvd_iff]
      refine dvd_of_pow_dvd_pow l x _ m ?_
      rw [sub_pow_char, hbs, hbs, ← dvd_iff, map_sub]
      have e : algebraMap V C (s m) - algebraMap V C (s n) = X ^ (l * n) * t n - X ^ (l * m) * t m := by
        have := hst m; have := hst n; linear_combination hst n - hst m
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow X (Nat.mul_le_mul_left l hmn)) _)
        (dvd_mul_right _ _)
    obtain ⟨L, hL⟩ := (complete x).toIsPrecomplete.prec hcau
    refine ⟨L, ?_⟩
    simp only
    rw [← sub_eq_zero]
    refine (complete x).toIsHausdorff.haus _ fun n => ?_
    rw [sModEq_iff, sub_zero]
    obtain ⟨u, hu⟩ := (sModEq_iff _ _ _ _).1 (hL n)
    have e : L ^ l - y = -((X ^ n) ^ l * u ^ l) - X ^ (l * n) * t n := by
      have hL' : L = algebraMap V C (b n) - X ^ n * u := by rw [← hu]; ring
      rw [hL', sub_pow_char, ← map_pow, hbs, mul_pow]
      linear_combination -(hst n)
    rw [e]
    exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _))
      (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)

end GlobalTheory.PerfectCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDoma
section
open scoped NNReal

namespace GlobalTheory.ValCompletion

section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

theorem evalₐ_eq_zero_iff (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : (I ^ n).map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a ^ n} := by
    have : I ^ n = Ideal.span {a ^ n} := by rw [h, Ideal.span_singleton_pow]
    rw [this, Ideal.map_span, Set.image_singleton, map_pow]
  rw [← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective

theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by
  induction y using AdicCompletion.induction_on with
  | _ x =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl

theorem isUnit_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n y) := by
  have key : IsUnit (AdicCompletion.evalₐ I (n + 1) y) := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
    rw [← factorPow_evalₐ (show 1 ≤ n + 1 by omega), ← ha] at hy
    obtain ⟨b, hb⟩ := hy.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : a * b - 1 ∈ I ^ 1 := by
      rw [← Ideal.Quotient.eq]
      exact hb
    rw [pow_one] at h1
    have hn : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) (a * b - 1)) :=
      ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h1 _⟩
    have hu := hn.isUnit_add_one
    rw [map_sub, map_one, sub_add_cancel, map_mul] at hu
    rw [← ha]
    exact isUnit_of_mul_isUnit_left hu
  rw [← factorPow_evalₐ (Nat.le_succ n)]
  exact key.map _

theorem isUnit_of_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by
  let f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n := fun n =>
    IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ y hy n)
  have hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x := fun n x =>
    IsLocalization.Away.lift_eq y _ x
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, hf0, factorPow_evalₐ]
  have e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y :=
    AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]
  rw [← e]
  exact (IsLocalization.Away.algebraMap_isUnit y).map _

end General

section Val
variable {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {x : V}

theorem not_pow_succ_dvd_pow (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : ¬ x ^ (m + 1) ∣ x ^ m := by
  rintro ⟨c, hc⟩
  apply hxu
  have h : x ^ m * 1 = x ^ m * (x * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
  exact IsUnit.of_mul_eq_one c (mul_left_cancel₀ (pow_ne_zero m hx0) h).symm

theorem algebraMap_pow_ne_zero (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ m ≠ 0 := by
  intro h
  have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) (m + 1)) h
  rw [← map_pow, evalₐ_algebraMap, map_zero, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  exact not_pow_succ_dvd_pow hx0 hxu m h2

theorem exists_eq_mul_unit (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (y : AdicCompletion (Ideal.span {x}) V) (hy : y ≠ 0) :
    ∃ (a : V) (n : ℕ), a ∣ x ^ n ∧ ∃ u : (AdicCompletion (Ideal.span {x}) V)ˣ, y = algebraMap V (AdicCompletion (Ideal.span {x}) V) a * u := by
  obtain ⟨n, hn⟩ : ∃ n, AdicCompletion.evalₐ (Ideal.span {x}) n y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (AdicCompletion.ext_evalₐ fun n => by rw [hc n, map_zero])
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {x}) (n + 1) y)
  have hna : ¬ x ^ n ∣ a := by
    intro hd
    apply hn
    rw [← factorPow_evalₐ (Nat.le_succ n), ← ha, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hd
  obtain ⟨b, hb⟩ : a ∣ x ^ n := by
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a (x ^ n)
    · exact ⟨c, hc.symm⟩
    · exact absurd ⟨c, hc.symm⟩ hna
  obtain ⟨z, hz⟩ : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) ∣ y - algebraMap V (AdicCompletion (Ideal.span {x}) V) a := by
    rw [← evalₐ_eq_zero_iff rfl, map_sub, evalₐ_algebraMap, ← ha, sub_self]
  have hunit : IsUnit (1 + algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) x * z) := by
    apply isUnit_of_evalₐ
    have hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self x
    rw [map_add (f := _), map_one, map_mul, map_mul, evalₐ_algebraMap, evalₐ_algebraMap, hx1,
      mul_zero, zero_mul, add_zero]
    exact isUnit_one
  refine ⟨a, n, ⟨b, hb⟩, hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, mul_add, mul_one]
  have : y = algebraMap V (AdicCompletion (Ideal.span {x}) V) a + algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) * z := by rw [← hz]; ring
  rw [this, pow_succ, ← map_pow, hb, map_mul]
  ring

end Val

end GlobalTheory.ValCompletion


open GlobalTheory.ValCompletion in
theorem GlobalTheory.adicCompletion_valuationRing_props : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  intro V _ _ _ x hx0 hxu
  have hne : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 := by
    simpa using algebraMap_pow_ne_zero hx0 hxu 1
  have hnt : Nontrivial (AdicCompletion (Ideal.span {x}) V) := ⟨⟨_, _, hne⟩⟩
  have hdom : IsDomain (AdicCompletion (Ideal.span {x}) V) := by
    refine @NoZeroDivisors.to_isDomain _ _ hnt ⟨fun {y z} hyz => ?_⟩
    by_contra hc
    push_neg at hc
    obtain ⟨a, n, ⟨c, hc1⟩, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hc.1
    obtain ⟨b, m, ⟨d, hd1⟩, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hc.2
    apply algebraMap_pow_ne_zero hx0 hxu (n + m)
    have h1 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b = 0 := by
      have h2 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b * ((u : AdicCompletion (Ideal.span {x}) V) * w) = 0 := by
        rw [← hyz]; ring
      exact (Units.mul_left_eq_zero (u * w)).1 (by rw [Units.val_mul]; exact h2)
    rw [pow_add, ← map_pow, ← map_pow, hc1, hd1]
    simp only [map_mul]
    calc _ = (algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b) * (algebraMap V (AdicCompletion (Ideal.span {x}) V) c * algebraMap V (AdicCompletion (Ideal.span {x}) V) d) := by ring
      _ = 0 := by rw [h1, zero_mul]
  refine ⟨hdom, ⟨fun y z => ?_⟩, hne, ?_, ?_⟩
  · by_cases hy : y = 0
    · exact ⟨0, Or.inr (by rw [hy, mul_zero])⟩
    by_cases hz : z = 0
    · exact ⟨0, Or.inl (by rw [hz, mul_zero])⟩
    obtain ⟨a, n, -, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hy
    obtain ⟨b, m, -, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hz
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a b
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * w, Or.inl ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * w * ((u : AdicCompletion (Ideal.span {x}) V) * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * u, Or.inr ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * u * ((w : AdicCompletion (Ideal.span {x}) V) * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
  · rintro ⟨v, hv⟩
    apply hxu
    obtain ⟨e, he⟩ := isUnit_iff_exists_inv.1 (⟨v, hv⟩ : IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x))
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) 1) he
    have hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self x
    rw [map_mul, evalₐ_algebraMap, hx1, zero_mul, map_one, eq_comm, ← map_one (Ideal.Quotient.mk _),
      Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton] at h2
    exact isUnit_of_dvd_one h2
  · have e : (Ideal.span {x}).map (algebraMap V (AdicCompletion (Ideal.span {x}) V)) = Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← e, IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton x)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalIntertwine
section
namespace GlobalTheory.AevalIntertwine

theorem aeval_intertwine : ∀ {K M N : Type} [inst : Field K] [inst_1 : AddCommGroup M] [inst_2 : Module K M] [inst_3 : AddCommGroup N] [inst_4 : Module K N] (f : M →ₗ[K] N) (A : Module.End K M) (B : Module.End K N), (∀ (x : M), (f : M → N) ((A : M → M) x) = (B : N → N) ((f : M → N) x)) → ∀ (p : Polynomial K) (x : M), (f : M → N) (((Polynomial.aeval A : Polynomial K → Module.End K M) p : M → M) x) = ((Polynomial.aeval B : Polynomial K → Module.End K N) p : N → N) ((f : M → N) x) := by
  intro K M N _ _ _ _ _ f A B h p
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a x
    simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  · intro p q hp hq x
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  · intro n a ih x
    have e : ∀ {V : Type} [AddCommGroup V] [Module K V] (E : Module.End K V) (y : V),
        Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ (n + 1)) y
          = Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n) (E y) := by
      intro V _ _ E y
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [e, e, ih, h]

end GlobalTheory.AevalIntertwine
end

