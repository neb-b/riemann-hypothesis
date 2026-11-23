module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NilpotentDerivationRank
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ggeo.DerivFree

variable {k : Type} [Field k] {R : Type} [CommRing R] [Algebra k R]

theorem deriv_mul_pow (D : Derivation k R R) {z : R} (hz : D z = 1) {c : R} (hc : D c = 0) (m : ℕ) :
    D (c * z ^ m) = (m : R) * c * z ^ (m - 1) := by
  rw [D.leibniz, D.leibniz_pow, hz, hc]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  ring

theorem iter_mul_pow (D : Derivation k R R) {z : R} (hz : D z = 1) {c : R} (hc : D c = 0)
    (n i : ℕ) :
    (⇑D)^[n] (c * z ^ i) = (i.descFactorial n : R) * c * z ^ (i - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hdc : D ((i.descFactorial n : R) * c) = 0 := by
      rw [D.leibniz, hc, Derivation.map_natCast]
      simp
    rw [deriv_mul_pow D hz hdc, Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

theorem iter_sum (D : Derivation k R R) (n : ℕ) {ι : Type} (s : Finset ι) (f : ι → R) :
    (⇑D)^[n] (∑ i ∈ s, f i) = ∑ i ∈ s, (⇑D)^[n] (f i) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ih, map_sum]

theorem iter_sub (D : Derivation k R R) (n : ℕ) (a b : R) :
    (⇑D)^[n] (a - b) = (⇑D)^[n] a - (⇑D)^[n] b := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, map_sub]

theorem iter_smul (D : Derivation k R R) (n : ℕ) (r : k) (a : R) :
    (⇑D)^[n] (r • a) = r • (⇑D)^[n] a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, D.map_smul]

theorem factorial_ne_zero_of_lt (p : ℕ) [Fact p.Prime] [CharP k p] {j : ℕ} (hj : j < p) :
    ((j.factorial : ℕ) : k) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff k p] at h
  have := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).1 h
  omega

theorem coeff_zero (p : ℕ) [Fact p.Prime] [CharP k p] (D : Derivation k R R) {z : R}
    (hz : D z = 1) (m : ℕ) (hm : m ≤ p) (c : ℕ → R) (hc : ∀ i, D (c i) = 0)
    (h : ∑ i ∈ Finset.range m, c i * z ^ i = 0) : ∀ i < m, c i = 0 := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    have hlast : c m = 0 := by
      have h1 := congrArg (⇑D)^[m] h
      have h0 : (⇑D)^[m] (0 : R) = 0 := by
        have := iter_smul D m (0 : k) (0 : R)
        simpa using this
      rw [iter_sum, h0, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add,
        iter_mul_pow D hz (hc m), Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one] at h1
      · have hf : ((m.factorial : ℕ) : k) ≠ 0 := factorial_ne_zero_of_lt p (by omega)
        have h2 : ((m.factorial : ℕ) : k) • c m = 0 := by
          rw [Algebra.smul_def, map_natCast]; exact h1
        exact (smul_eq_zero.1 h2).resolve_left hf
      · intro i hi
        have hi' : i < m := Finset.mem_range.1 hi
        rw [iter_mul_pow D hz (hc i), Nat.descFactorial_eq_zero_iff_lt.2 hi']
        simp
    rw [Finset.sum_range_succ, hlast, zero_mul, add_zero] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih (by omega) h i hi
    · exact hlast

theorem exists_coeff (p : ℕ) [Fact p.Prime] [CharP k p] (D : Derivation k R R) {z : R}
    (hz : D z = 1) (j : ℕ) (hj : j ≤ p) (a : R) (ha : (⇑D)^[j] a = 0) :
    ∃ c : ℕ → R, (∀ i, D (c i) = 0) ∧ a = ∑ i ∈ Finset.range j, c i * z ^ i := by
  induction j generalizing a with
  | zero => exact ⟨fun _ => 0, by simp, by simpa using ha⟩
  | succ j ih =>
    set b := (⇑D)^[j] a with hb
    have hDb : D b = 0 := by
      rw [hb, ← Function.iterate_succ_apply' (⇑D)]; exact ha
    have hf : ((j.factorial : ℕ) : k) ≠ 0 := factorial_ne_zero_of_lt p (by omega)
    set e := (((j.factorial : ℕ) : k))⁻¹ • b with he
    have hDe : D e = 0 := by rw [he, D.map_smul, hDb, smul_zero]
    have hker : (⇑D)^[j] (a - e * z ^ j) = 0 := by
      rw [iter_sub, iter_mul_pow D hz hDe, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one,
        ← hb, he, mul_smul_comm]
      have hnb : ((j.factorial : ℕ) : R) * b = ((j.factorial : ℕ) : k) • b := by
        rw [Algebra.smul_def, map_natCast]
      rw [hnb, smul_smul, inv_mul_cancel₀ hf, one_smul, sub_self]
    obtain ⟨c, hc, hac⟩ := ih (by omega) _ hker
    refine ⟨fun i => if i = j then e else c i, ?_, ?_⟩
    · intro i; by_cases hi : i = j <;> simp [hi, hDe, hc]
    · rw [Finset.sum_range_succ]
      have : ∑ i ∈ Finset.range j, (if i = j then e else c i) * z ^ i
          = ∑ i ∈ Finset.range j, c i * z ^ i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [if_neg (Finset.mem_range.1 hi).ne]
      rw [this, ← hac]
      simp

theorem exists_deriv_eq_one (p : ℕ) [Fact p.Prime] (D : Derivation k R R)
    (hnil : ∀ a : R, (⇑D)^[p] a = 0) (t : R) (ht : IsUnit ((⇑D)^[p - 1] t)) :
    ∃ z : R, D z = 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨w, hw⟩ := ht
  have hp1 : p - 1 = (p - 2) + 1 := by omega
  have hs : D ((⇑D)^[p - 2] t) = (w : R) := by
    rw [hw, hp1, Function.iterate_succ_apply']
  have hDw : D (w : R) = 0 := by
    have h := hnil t
    have hp2 : p = (p - 1) + 1 := by omega
    rw [hp2, Function.iterate_succ_apply'] at h
    rw [hw]
    simpa using h
  have hDinv : D ((w⁻¹ : Rˣ) : R) = 0 := by
    have h1 : D ((w : R) * ((w⁻¹ : Rˣ) : R)) = 0 := by
      rw [Units.mul_inv, D.map_one_eq_zero]
    rw [D.leibniz, hDw, smul_zero, add_zero, smul_eq_mul] at h1
    exact (Units.mul_right_eq_zero w).1 h1
  refine ⟨((w⁻¹ : Rˣ) : R) * (⇑D)^[p - 2] t, ?_⟩
  rw [D.leibniz, hs, hDinv, smul_zero, add_zero, smul_eq_mul, Units.inv_mul]

noncomputable def coeffMap (p : ℕ) (D : Derivation k R R) (z : R) :
    (Fin p → LinearMap.ker (D : R →ₗ[k] R)) →ₗ[k] R where
  toFun a := ∑ i, (a i : R) * z ^ (i : ℕ)
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.smul_sum, smul_mul_assoc]

theorem coeffMap_bijective (p : ℕ) [Fact p.Prime] [CharP k p] (D : Derivation k R R) {z : R}
    (hz : D z = 1) (hnil : ∀ a : R, (⇑D)^[p] a = 0) :
    Function.Bijective (coeffMap p D z) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    let c : ℕ → R := fun i => if h : i < p then (a ⟨i, h⟩ : R) else 0
    have hc : ∀ i, D (c i) = 0 := by
      intro i
      by_cases h : i < p
      · have h3 : D (a ⟨i, h⟩ : R) = 0 := LinearMap.mem_ker.1 (a ⟨i, h⟩).2
        simpa [c, h] using h3
      · simp [c, h]
    have hsum : ∑ i ∈ Finset.range p, c i * z ^ i = 0 := by
      rw [Finset.sum_range]
      have h2 : (∑ i : Fin p, (a i : R) * z ^ (i : ℕ)) = 0 := ha
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c]
    have h0 := coeff_zero p D hz p le_rfl c hc hsum
    funext i
    apply Subtype.ext
    have := h0 i i.2
    simpa [c] using this
  · intro a
    obtain ⟨c, hc, hac⟩ := exists_coeff p D hz p le_rfl a (hnil a)
    refine ⟨fun i => ⟨c i, hc i⟩, ?_⟩
    rw [hac, Finset.sum_range]
    rfl

theorem finrank_and_vanishing : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = 0) → ∀ t : R, IsUnit ((⇑D)^[p - 1] t) →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  intro k _ p _ _ R _ _ _ D ε hnil t ht
  obtain ⟨z, hz⟩ := exists_deriv_eq_one p D hnil t ht
  have hbij := coeffMap_bijective p D hz hnil
  refine ⟨?_, z, ?_, ?_⟩
  · have e := (LinearEquiv.ofBijective (coeffMap p D z) hbij).finrank_eq
    rw [← e, Module.finrank_pi_fintype]
    simp
  · rw [hz, map_one]
    exact one_ne_zero
  · intro u hmul hker huz
    have hpow : ∀ i : ℕ, u (z ^ i) = 0 := by
      intro i
      induction i with
      | zero => rw [pow_zero]; exact hker 1 D.map_one_eq_zero
      | succ i ih => rw [pow_succ, hmul, ih, huz]; simp
    apply LinearMap.ext
    intro a
    obtain ⟨b, rfl⟩ := hbij.2 a
    have h2 : coeffMap p D z b = ∑ i, (b i : R) * z ^ (i : ℕ) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum]
    simp only [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hmul, hpow, hker _ (b i).2]
    simp

end GlobalTheory.CompanionTheory.Ggeo.DerivFree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonarchValuationOfPrime
section
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Ggeo

def ltOneIdeal {R : Type} [CommRing R] [IsDomain R] (μ : R →*₀ ℝ)
    (h0 : ∀ x, 0 ≤ μ x) (h1 : ∀ x, μ x ≤ 1)
    (hadd : ∀ x y, μ (x + y) ≤ max (μ x) (μ y)) : Ideal R where
  carrier := {x | μ x < 1}
  add_mem' := by
    intro x y hx hy
    exact lt_of_le_of_lt (hadd x y) (max_lt hx hy)
  zero_mem' := by
    show μ 0 < 1
    simp
  smul_mem' := by
    intro c x hx
    show μ (c * x) < 1
    rw [map_mul]
    have hx' : μ x < 1 := hx
    nlinarith [h0 c, h0 x, h1 c]

private theorem eq_pow_count_normalizedFactors_of_uniformizer {R : Type} [CommRing R] [IsDedekindDomain R]
    (μ : R →*₀ ℝ) (P : Ideal R) [P.IsPrime] (hone : ∀ x, x ∉ P → μ x = 1)
    (π : R) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) (x : R) (hx : x ≠ 0) :
    μ x = μ π ^ (normalizedFactors (Ideal.span {x})).count P := by
  have hspan : ∀ y : R, y ≠ 0 → Ideal.span {y} ≠ 0 := fun y hy => by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hy
  have hadd : ∀ y z : R, y ≠ 0 → z ≠ 0 → (normalizedFactors (Ideal.span {y * z})).count P =
      (normalizedFactors (Ideal.span {y})).count P + (normalizedFactors (Ideal.span {z})).count P := by
    intro y z hy hz
    rw [← Ideal.span_singleton_mul_span_singleton, normalizedFactors_mul (hspan y hy) (hspan z hz),
      Multiset.count_add]
  have hzero : ∀ y : R, y ∉ P → (normalizedFactors (Ideal.span {y})).count P = 0 := by
    intro y hy
    apply Ideal.count_normalizedFactors_eq
    · rw [pow_zero, Ideal.one_eq_top]
      exact le_top
    · rw [zero_add, pow_one, Ideal.span_singleton_le_iff_mem]
      exact hy
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (zero_mem _)
  have hπ1 : (normalizedFactors (Ideal.span {π})).count P = 1 := by
    apply Ideal.count_normalizedFactors_eq
    · rw [pow_one, Ideal.span_singleton_le_iff_mem]
      exact hπ
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hπ2
  obtain ⟨A, hA⟩ : P ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem P).2 hπ)
  have hAP : ¬A ≤ P := by
    intro hle
    apply hπ2
    rw [← Ideal.span_singleton_le_iff_mem, hA, pow_two]
    exact Ideal.mul_mono_right hle
  obtain ⟨s, hsA, hsP⟩ := SetLike.not_le_iff_exists.1 hAP
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hsP (zero_mem _)
  have hstep : ∀ y : R, y ∈ P → ∃ z, s * y = π * z := by
    intro y hy
    have : s * y ∈ Ideal.span {π} := by
      rw [hA, mul_comm s y]
      exact Ideal.mul_mem_mul hy hsA
    exact Ideal.mem_span_singleton.1 this
  have hdiv : ∀ y : R, y ≠ 0 → y ∈ P → ∃ z, z ≠ 0 ∧
      (normalizedFactors (Ideal.span {y})).count P =
        (normalizedFactors (Ideal.span {z})).count P + 1 ∧ μ y = μ π * μ z := by
    intro y hy hyP
    obtain ⟨z, hz⟩ := hstep y hyP
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hz
      exact mul_ne_zero hs0 hy hz
    have hc := hadd s y hs0 hy
    rw [hz, hadd π z hπ0 hz0, hπ1, hzero s hsP] at hc
    refine ⟨z, hz0, by omega, ?_⟩
    have hμ : μ s * μ y = μ π * μ z := by rw [← map_mul, ← map_mul, hz]
    rwa [hone s hsP, one_mul] at hμ
  suffices H : ∀ n : ℕ, ∀ y : R, y ≠ 0 → (normalizedFactors (Ideal.span {y})).count P = n →
      μ y = μ π ^ n from H _ x hx rfl
  intro n
  induction n with
  | zero =>
    intro y hy hn
    by_cases hyP : y ∈ P
    · obtain ⟨z, _, hc, _⟩ := hdiv y hy hyP
      omega
    · rw [hone y hyP, pow_zero]
  | succ n ih =>
    intro y hy hn
    by_cases hyP : y ∈ P
    · obtain ⟨z, hz0, hc, hμ⟩ := hdiv y hy hyP
      rw [hμ, ih z hz0 (by omega), pow_succ, mul_comm]
    · rw [hzero y hyP] at hn
      omega

theorem map_eq_pow_count_of_ultrametric :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (μ : R →*₀ ℝ) (a : R), a ≠ 0 →
      (∀ x, 0 ≤ μ x) → (∀ x, μ x ≤ 1) → (∀ x y, μ (x + y) ≤ max (μ x) (μ y)) →
      μ a < 1 → μ a ≠ 0 →
      ∃ (P : Ideal R) (c : ℝ), P.IsPrime ∧ P ≠ ⊥ ∧ a ∈ P ∧ 0 < c ∧
        ∀ x : R, x ≠ 0 → μ x = c ^ (normalizedFactors (Ideal.span {x})).count P := by
  intro R _ _ μ a ha h0 h1 hadd hlt hne
  set P := GlobalTheory.CompanionTheory.Ggeo.ltOneIdeal μ h0 h1 hadd with hPdef
  have hmem : ∀ x, x ∈ P ↔ μ x < 1 := fun x => Iff.rfl
  have hPtop : P ≠ ⊤ := by
    intro htop
    have h1P := (Ideal.eq_top_iff_one P).1 htop
    rw [hmem, map_one] at h1P
    exact lt_irrefl _ h1P
  have hPprime : P.IsPrime := by
    refine ⟨hPtop, ?_⟩
    intro x y hxy
    have hxy' : μ x * μ y < 1 := by
      rw [← map_mul]
      exact (hmem _).1 hxy
    by_contra hc
    rw [not_or] at hc
    have hx1 : ¬μ x < 1 := fun h => hc.1 ((hmem x).2 h)
    have hy1 : ¬μ y < 1 := fun h => hc.2 ((hmem y).2 h)
    rw [not_lt] at hx1 hy1
    nlinarith [h0 x, h0 y]
  haveI := hPprime
  have haP : a ∈ P := (hmem a).2 hlt
  have hbot : P ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at haP
    exact ha haP
  obtain ⟨π, hπ, hπ2⟩ : ∃ π ∈ P ^ 1, π ∉ P ^ 2 := SetLike.exists_of_lt
    (Ideal.pow_right_strictAnti P hbot hPtop (by norm_num : 1 < 2))
  rw [pow_one] at hπ
  have hone : ∀ x, x ∉ P → μ x = 1 := fun x hx =>
    le_antisymm (h1 x) (not_lt.1 fun h => hx ((hmem x).2 h))
  have hkey := eq_pow_count_normalizedFactors_of_uniformizer μ P hone π hπ hπ2
  have hπne : μ π ≠ 0 := by
    intro h
    have ha' := hkey a ha
    rw [h] at ha'
    rcases Nat.eq_zero_or_pos ((normalizedFactors (Ideal.span {a})).count P) with hk | hk
    · rw [hk, pow_zero] at ha'
      rw [ha'] at hlt
      exact lt_irrefl _ hlt
    · rw [zero_pow hk.ne'] at ha'
      exact hne ha'
  exact ⟨P, μ π, hPprime, hbot, haP, lt_of_le_of_ne (h0 π) (Ne.symm hπne), hkey⟩

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModulesGlueCover
section
namespace GlobalTheory.CompanionTheory.Ggeo

theorem finite_projective_of_isLocalizedModule_cover :
    ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : J → Type) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module (Localization.Away (f i)) (F i)]
    [∀ i, IsScalarTower R (Localization.Away (f i)) (F i)] [∀ i, Module.Finite (Localization.Away (f i)) (F i)]
    [∀ i, Module.Projective (Localization.Away (f i)) (F i)] (φ : ∀ i, E →ₗ[R] F i),
    (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (φ i)) → Module.Finite R E ∧ Module.Projective R E := by
  intro R E _ _ _ J _ f hf F _ _ _ _ _ _ φ hφ
  have hex : ∀ g : Set.range f, ∃ i, f i = g.1 := fun g => g.2
  choose idx hidx using hex
  have hA : ∀ g : Set.range f, IsLocalization.Away g.1 (Localization.Away (f (idx g))) := by
    intro g
    rw [← hidx g]
    infer_instance
  have hL : ∀ g : Set.range f, IsLocalizedModule (Submonoid.powers g.1) (φ (idx g)) := by
    intro g
    rw [← hidx g]
    exact hφ _
  have hfp : Module.FinitePresentation R E :=
    Module.FinitePresentation.of_localizationSpan' (Set.range f) hf
      (Mₚ := fun g => F (idx g)) (Rₚ := fun g => Localization.Away (f (idx g)))
      (fun g => φ (idx g)) (fun g => Module.finitePresentation_of_projective _ _)
  have hflat : Module.Flat R E := by
    refine Module.flat_of_isLocalized_span (R := R) R E (Set.range f) hf (fun g => F (idx g))
      (fun g => φ (idx g)) (fun g => ?_)
    have : Module.Flat R (Localization.Away (f (idx g))) :=
      IsLocalization.flat _ (Submonoid.powers (f (idx g)))
    exact Module.Flat.trans R (Localization.Away (f (idx g))) (F (idx g))
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubspaceContainsUnit
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FiniteAlgebraUnit

theorem exists_isUnit_mem_of_forall_point :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R]
    (U : Submodule k R), (∀ x : R →ₐ[k] k, ∃ t ∈ U, x t ≠ 0) → ∃ w ∈ U, IsUnit w := by
  intro k _ _ R _ _ _ U hU
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : Infinite k := IsAlgClosed.instInfinite

  have hpt : ∀ m : Ideal R, m.IsMaximal → ∃ x : R →ₐ[k] k, ∀ r ∈ m, x r = 0 := by
    intro m hm
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    haveI : Module.Finite k (R ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap
        (Ideal.Quotient.mkₐ_surjective k m)
    let e : k ≃ₐ[k] (R ⧸ m) :=
      AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨(e.symm : (R ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩
    have h0 : Ideal.Quotient.mkₐ k m r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    change e.symm (Ideal.Quotient.mkₐ k m r) = 0
    rw [h0, map_zero]

  let f : Ideal R → Submodule k U := fun m => (m.restrictScalars k).comap U.subtype
  have hfin : (f '' {m : Ideal R | m.IsMaximal}).Finite :=
    (IsArtinianRing.setOfPred_isMaximal_finite R).image f
  let s : Finset (Submodule k U) := hfin.toFinset
  have htop : (⊤ : Submodule k U) ∉ s := by
    intro h
    obtain ⟨m, hm, hfm⟩ := (Set.Finite.mem_toFinset hfin).mp h
    obtain ⟨x, hx⟩ := hpt m hm
    obtain ⟨t, htU, ht⟩ := hU x
    have : (⟨t, htU⟩ : U) ∈ f m := by rw [hfm]; trivial
    exact ht (hx t this)
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (s := s) htop
  obtain ⟨w, hw⟩ : ∃ w : U, w ∉ ⋃ p ∈ s, (p : Set U) := by
    by_contra hcon
    push_neg at hcon
    exact hne (Set.eq_univ_of_forall hcon)
  refine ⟨w, w.2, ?_⟩
  by_contra hnu
  obtain ⟨m, hm, hwm⟩ := exists_max_ideal_of_mem_nonunits (show (w : R) ∈ nonunits R from hnu)
  apply hw
  simp only [Set.mem_iUnion]
  exact ⟨f m, (Set.Finite.mem_toFinset hfin).mpr ⟨m, hm, rfl⟩, hwm⟩

end GlobalTheory.CompanionTheory.FiniteAlgebraUnit
end

