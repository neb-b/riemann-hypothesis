module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDVROfClosedSubringPrincipal
section
open IsLocalRing

namespace GlobalTheory

private theorem eq_zero_of_forall_mem_pow_of_isAdicComplete {S : Type} [CommRing S] (I : Ideal S)
    (hc : IsAdicComplete I S) (s : S) (h : ∀ n : ℕ, s ∈ I ^ n) : s = 0 := by
  refine hc.toIsHausdorff.haus' s fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact h n

private theorem exists_limit_of_isAdicComplete {S : Type} [CommRing S] (I : Ideal S)
    (hc : IsAdicComplete I S) (f : ℕ → S) (h : ∀ {a b : ℕ}, a ≤ b → f a - f b ∈ I ^ a) :
    ∃ L : S, ∀ n, f n - L ∈ I ^ n := by
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec' f fun {a b} hab => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact h hab
  refine ⟨L, fun n => ?_⟩
  have := hL n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this

private theorem isUnit_of_not_mem_maximalIdeal_of_closed {S : Type} [CommRing S] [IsLocalRing S]
    (Λ : Subring S) (π : Λ) (hπm : (π : S) ∈ maximalIdeal S)
    (hres : ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S)
    (hdiv : ∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a)
    (hcl : ∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ)
    (a : Λ) (ha : (a : S) ∉ maximalIdeal S) : IsUnit a := by
  have hu : IsUnit (a : S) := by
    by_contra h
    exact ha ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨t, ht⟩ : ∃ t : S, (a : S) * t = 1 := ⟨((hu.unit⁻¹ : Sˣ) : S), hu.mul_val_inv⟩
  obtain ⟨b, hbΛ, hb⟩ := hres t
  have h1 : ((1 - a * ⟨b, hbΛ⟩ : Λ) : S) ∈ maximalIdeal S := by
    have e : ((1 - a * ⟨b, hbΛ⟩ : Λ) : S) = (a : S) * (t - b) := by
      push_cast
      rw [mul_sub, ht]
    rw [e]
    exact Ideal.mul_mem_left _ _ hb
  obtain ⟨c, hcd⟩ := hdiv _ h1
  have hab : (a : S) * b = 1 - (π : S) * c := by
    have e := congrArg Subtype.val hcd
    push_cast at e
    linear_combination -e
  have htΛ : t ∈ Λ := by
    apply hcl
    intro n
    refine ⟨(b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i,
      Λ.mul_mem hbΛ (Λ.sum_mem fun i _ => Λ.pow_mem (Λ.mul_mem π.2 c.2) i), ?_⟩
    have g := mul_neg_geom_sum ((π : S) * c) n
    have e : t - (b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i = t * ((π : S) * c) ^ n := by
      linear_combination ((b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i) * ht
        - t * (∑ i ∈ Finset.range n, ((π : S) * c) ^ i) * hab - t * g
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mul_mem_right _ _ hπm) n)
  exact isUnit_iff_exists_inv.2 ⟨⟨t, htΛ⟩, Subtype.ext ht⟩

private theorem exists_pow_dvd_of_mem_maximalIdeal_pow {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S]
    (Λ : Subring S) (π : Λ) (hπ0 : (π : S) ≠ 0) (hπm : (π : S) ∈ maximalIdeal S)
    (hc : IsAdicComplete (maximalIdeal S) S)
    (hres : ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S)
    (hdiv : ∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a)
    (hcl : ∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ)
    (k : ℕ) : ∃ N : ℕ, ∀ a : Λ, (a : S) ∈ maximalIdeal S ^ N → π ^ k ∣ a := by
  induction k with
  | zero => exact ⟨0, fun a _ => by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    have hne : ((π ^ k : Λ) : S) ≠ 0 := by
      push_cast
      exact pow_ne_zero _ hπ0
    obtain ⟨M, hM⟩ : ∃ M, ((π ^ k : Λ) : S) ∉ maximalIdeal S ^ M := by
      by_contra h
      push_neg at h
      exact hne (eq_zero_of_forall_mem_pow_of_isAdicComplete _ hc _ h)
    refine ⟨max N M, fun a ha => ?_⟩
    obtain ⟨u, rfl⟩ := hN a (Ideal.pow_le_pow_right (le_max_left _ _) ha)
    rw [pow_succ]
    refine mul_dvd_mul_left _ ?_
    by_contra hu
    have hunit : IsUnit u := isUnit_of_not_mem_maximalIdeal_of_closed Λ π hπm hres hdiv hcl u fun h => hu (hdiv u h)
    apply hM
    have e : π ^ k = (π ^ k * u) * ↑hunit.unit⁻¹ := by
      rw [mul_assoc, hunit.mul_val_inv, mul_one]
    rw [e, Subring.coe_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (le_max_right _ _) ha)

theorem isDVR_of_closed_subring_principal :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (Λ : Subring S) (π : Λ), (π : S) ≠ 0 → (π : S) ∈ maximalIdeal S → IsAdicComplete (maximalIdeal S) S → (∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) → (∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a) → (∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ) → ∃ _ : IsDiscreteValuationRing Λ, maximalIdeal Λ = Ideal.span {π} ∧ IsAdicComplete (maximalIdeal Λ) Λ := by
  intro S _ _ _ Λ π hπ0 hπm hc hres hdiv hcl
  have hunit : ∀ a : Λ, IsUnit a ↔ (a : S) ∉ maximalIdeal S := fun a =>
    ⟨fun h hm => (IsLocalRing.mem_maximalIdeal _).1 hm (h.map Λ.subtype),
      isUnit_of_not_mem_maximalIdeal_of_closed Λ π hπm hres hdiv hcl a⟩
  have hsep : ∀ x : Λ, (∀ n : ℕ, π ^ n ∣ x) → x = 0 := by
    intro x hx
    have : (x : S) = 0 := by
      refine eq_zero_of_forall_mem_pow_of_isAdicComplete _ hc _ fun n => ?_
      obtain ⟨c, hc'⟩ := hx n
      rw [hc', Subring.coe_mul, Subring.coe_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm n)
    exact_mod_cast this
  have hirr : Irreducible π := by
    refine ⟨fun h => (hunit π).1 h hπm, fun ⦃a b⦄ hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨ha, hb⟩ := hne
    rw [hunit, not_not] at ha hb
    obtain ⟨x, rfl⟩ := hdiv a ha
    obtain ⟨y, rfl⟩ := hdiv b hb
    have h0 : π * (1 - π * (x * y)) = 0 := by linear_combination hab
    rcases mul_eq_zero.1 h0 with h | h
    · exact hπ0 (by rw [h]; rfl)
    · exact (hunit π).1 (isUnit_iff_exists_inv.2 ⟨x * y, by linear_combination -h⟩) hπm
  have hfac : ∀ {x : Λ}, x ≠ 0 → ∃ n : ℕ, Associated (π ^ n) x := by
    intro x hx
    have hex : ∃ n, ¬ π ^ n ∣ x := by
      by_contra h
      push_neg at h
      exact hx (hsep x h)
    classical
    obtain ⟨k, hk, hk1⟩ : ∃ k, π ^ k ∣ x ∧ ¬ π ^ (k + 1) ∣ x := by
      have h0 : Nat.find hex ≠ 0 := by
        intro h
        have := Nat.find_spec hex
        rw [h, pow_zero] at this
        exact this (one_dvd x)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
      refine ⟨k, not_not.1 (Nat.find_min hex (by omega)), ?_⟩
      rw [← Nat.succ_eq_add_one, ← hk]
      exact Nat.find_spec hex
    obtain ⟨u, rfl⟩ := hk
    have hu : IsUnit u := (hunit u).2 fun hm => hk1 (by
      rw [pow_succ]
      exact mul_dvd_mul_left _ (hdiv u hm))
    exact ⟨k, hu.unit, by rw [hu.unit_spec]⟩
  have hdvr : IsDiscreteValuationRing Λ :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, hfac⟩
  have hmax : maximalIdeal Λ = Ideal.span {π} := by
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, not_not, Ideal.mem_span_singleton]
    refine ⟨hdiv x, fun ⟨c, hc'⟩ => ?_⟩
    rw [hc', Subring.coe_mul]
    exact Ideal.mul_mem_right _ _ hπm
  refine ⟨hdvr, hmax, ?_⟩
  rw [hmax]
  have hmem : ∀ (n : ℕ) (y : Λ), y ∈ (Ideal.span {π}) ^ n • (⊤ : Submodule Λ Λ) ↔ π ^ n ∣ y := by
    intro n y
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    refine hsep x fun n => ?_
    have := hx n
    rwa [SModEq.sub_mem, sub_zero, hmem] at this
  · intro f hf
    have hfS : ∀ {a b : ℕ}, a ≤ b → (f a : S) - f b ∈ maximalIdeal S ^ a := by
      intro a b hab
      have := hf hab
      rw [SModEq.sub_mem, hmem] at this
      obtain ⟨c, hc'⟩ := this
      have e := congrArg Subtype.val hc'
      push_cast at e
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm a)
    obtain ⟨L, hL⟩ := exists_limit_of_isAdicComplete _ hc (fun n => (f n : S)) hfS
    have hLΛ : L ∈ Λ := hcl L fun n => ⟨f n, (f n).2, by
      rw [← neg_sub]
      exact neg_mem (hL n)⟩
    refine ⟨⟨L, hLΛ⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, hmem]
    obtain ⟨N, hN⟩ := exists_pow_dvd_of_mem_maximalIdeal_pow Λ π hπ0 hπm hc hres hdiv hcl n
    have h1 : π ^ n ∣ f n - f (max n N) := by
      have := hf (le_max_left n N)
      rwa [SModEq.sub_mem, hmem] at this
    have h2 : π ^ n ∣ f (max n N) - ⟨L, hLΛ⟩ := hN _ (by
      push_cast
      exact Ideal.pow_le_pow_right (le_max_right n N) (hL _))
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
section
open IsLocalRing

namespace GlobalTheory.PowerSeriesNormal

open PowerSeries

variable {R : Type} [CommRing R] [IsDomain R]

theorem dvd_of_pow_dvd [IsNoetherianRing R] [IsIntegrallyClosed R] {f g h : R} (hg : g ≠ 0)
    (hh : h ≠ 0) (H : ∀ n : ℕ, g ^ n ∣ h * f ^ n) : g ∣ f := by
  classical
  let K := FractionRing R
  have hinj := IsFractionRing.injective R K
  have hgK : algebraMap R K g ≠ 0 := (map_ne_zero_iff _ hinj).2 hg
  have hhK : algebraMap R K h ≠ 0 := (map_ne_zero_iff _ hinj).2 hh
  set x : K := algebraMap R K f / algebraMap R K g with hx
  let M : Submodule R K := Submodule.span R {(algebraMap R K h)⁻¹}
  have hpow : ∀ n : ℕ, x ^ n ∈ M := by
    intro n
    obtain ⟨c, hc⟩ := H n
    have : x ^ n = c • (algebraMap R K h)⁻¹ := by
      rw [Algebra.smul_def, hx, div_pow, eq_mul_inv_iff_mul_eq₀ hhK, div_mul_eq_mul_div,
        div_eq_iff (pow_ne_zero _ hgK)]
      have := congrArg (algebraMap R K) hc
      simp only [map_mul, map_pow] at this
      linear_combination this
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin R {x}) ≤ M := by
    intro y hy
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    change Polynomial.aeval x p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpow i)
  have : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M (Submodule.fg_span_singleton _)
  have := isNoetherian_of_le hle
  have hint : IsIntegral R x :=
    isIntegral_of_submodule_noetherian _ this x (Algebra.subset_adjoin rfl)
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).1 inferInstance hint
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, hx, mul_comm]
  exact (div_mul_cancel₀ _ hgK).symm

theorem dvd_of_dvd_X_pow_mul {u a : R⟦X⟧} (hu : ¬ (X : R⟦X⟧) ∣ u) {c : ℕ}
    (h : u ∣ X ^ c * a) : u ∣ a := by
  induction c generalizing a with
  | zero => simpa using h
  | succ c ih =>
    apply ih
    obtain ⟨v, hv⟩ := h
    have hXv : (X : R⟦X⟧) ∣ u * v := ⟨X ^ c * a, by rw [← hv]; ring⟩
    rcases X_prime.dvd_or_dvd hXv with hu' | ⟨w, hw⟩
    · exact absurd hu' hu
    · refine ⟨w, mul_left_cancel₀ (X_ne_zero (R := R)) ?_⟩
      calc X * (X ^ c * a) = X ^ (c + 1) * a := by ring
        _ = u * v := hv
        _ = X * (u * w) := by rw [hw]; ring

theorem exists_eq_X_pow_mul {f : R⟦X⟧} (hf : f ≠ 0) :
    ∃ (a : ℕ) (f₁ : R⟦X⟧), ¬ (X : R⟦X⟧) ∣ f₁ ∧ f = X ^ a * f₁ := by
  obtain ⟨f₁, hf₁⟩ := X_pow_order_dvd (φ := f)
  refine ⟨f.order.toNat, f₁, ?_, hf₁⟩
  rintro ⟨e, he⟩
  have hd : (X : R⟦X⟧) ^ (f.order.toNat + 1) ∣ f := ⟨e, by rw [pow_succ, mul_assoc, ← he, ← hf₁]⟩
  rw [X_pow_dvd_iff] at hd
  exact coeff_order hf (hd _ (Nat.lt_succ_self _))

def almostMultiples (g : R⟦X⟧) : Ideal R⟦X⟧ where
  carrier := {f | ∃ h, h ≠ 0 ∧ ∀ n : ℕ, g ^ n ∣ h * f ^ n}
  zero_mem' := ⟨1, one_ne_zero, fun n => by
    rw [one_mul]; exact pow_dvd_pow_of_dvd (dvd_zero g) n⟩
  add_mem' := by
    rintro a b ⟨h, hh, H⟩ ⟨k, hk, K⟩
    refine ⟨h * k, mul_ne_zero hh hk, fun n => ?_⟩
    rw [add_pow, Finset.mul_sum]
    refine Finset.dvd_sum fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have e : g ^ n = g ^ i * g ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
    have e2 : h * k * (a ^ i * b ^ (n - i) * (n.choose i : R⟦X⟧))
        = (h * a ^ i) * (k * b ^ (n - i)) * (n.choose i : R⟦X⟧) := by ring
    rw [e, e2]
    exact (mul_dvd_mul (H i) (K _)).mul_right _
  smul_mem' := by
    rintro c a ⟨h, hh, H⟩
    refine ⟨h, hh, fun n => ?_⟩
    rw [smul_eq_mul, mul_pow, mul_left_comm]
    exact (H n).mul_left _

private theorem mem_almostMultiples_iff {g f : R⟦X⟧} :
    f ∈ almostMultiples g ↔ ∃ h, h ≠ 0 ∧ ∀ n : ℕ, g ^ n ∣ h * f ^ n := Iff.rfl

private theorem constantCoeff_dvd_of_mem_almostMultiples [IsNoetherianRing R] [IsIntegrallyClosed R] {g e : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) (he : e ∈ almostMultiples g) :
    constantCoeff g ∣ constantCoeff e := by
  obtain ⟨h, hh, H⟩ := mem_almostMultiples_iff.1 he
  obtain ⟨b, h₁, hh₁, rfl⟩ := exists_eq_X_pow_mul hh
  have H' : ∀ n : ℕ, g ^ n ∣ h₁ * e ^ n := fun n =>
    dvd_of_dvd_X_pow_mul (fun hX => hg (X_prime.dvd_of_dvd_pow hX))
      (c := b) (by simpa [mul_assoc] using H n)
  have hg0 : constantCoeff g ≠ 0 := fun h0 => hg (X_dvd_iff.2 h0)
  have hh0 : constantCoeff h₁ ≠ 0 := fun h0 => hh₁ (X_dvd_iff.2 h0)
  exact dvd_of_pow_dvd hg0 hh0 fun n => by
    simpa [map_mul, map_pow] using map_dvd constantCoeff (H' n)

private theorem mem_almostMultiples_of_X_pow_mul_mem {g e : R⟦X⟧} (hg : ¬ (X : R⟦X⟧) ∣ g) {k : ℕ}
    (he : X ^ k * e ∈ almostMultiples g) : e ∈ almostMultiples g := by
  obtain ⟨h, hh, H⟩ := mem_almostMultiples_iff.1 he
  refine mem_almostMultiples_iff.2 ⟨h, hh, fun n => ?_⟩
  have : h * (X ^ k * e) ^ n = X ^ (k * n) * (h * e ^ n) := by ring
  exact dvd_of_dvd_X_pow_mul (fun hX => hg (X_prime.dvd_of_dvd_pow hX)) (this ▸ H n)

private theorem exists_X_pow_dvd_sub_mul_of_mem_almostMultiples [IsNoetherianRing R] [IsIntegrallyClosed R] {g f : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) (hf : f ∈ almostMultiples g) :
    ∀ k : ℕ, ∃ r : R⟦X⟧, X ^ k ∣ f - g * r := by
  have hgI : g ∈ almostMultiples g :=
    mem_almostMultiples_iff.2 ⟨1, one_ne_zero, fun n => by rw [one_mul]⟩
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨r, e, he⟩ := ih
    have hmem : X ^ k * e ∈ almostMultiples g := by
      rw [← he]; exact Ideal.sub_mem _ hf (Ideal.mul_mem_right _ _ hgI)
    obtain ⟨c, hc⟩ := constantCoeff_dvd_of_mem_almostMultiples hg (mem_almostMultiples_of_X_pow_mul_mem hg hmem)
    refine ⟨r + C c * X ^ k, ?_⟩
    have hX : (X : R⟦X⟧) ∣ e - g * C c := by
      rw [X_dvd_iff]; simp [hc]
    obtain ⟨w, hw⟩ := hX
    refine ⟨w, ?_⟩
    have : f - g * (r + C c * X ^ k) = X ^ k * (e - g * C c) := by
      linear_combination he
    rw [this, hw]; ring

theorem almostMultiples_le [IsNoetherianRing R] [IsIntegrallyClosed R] {g : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) : almostMultiples g ≤ Ideal.span {g} := by
  intro f hf
  rw [Ideal.mem_span_singleton]
  choose r hr using exists_X_pow_dvd_sub_mul_of_mem_almostMultiples hg hf
  have hstable : ∀ j m : ℕ, j ≤ m → coeff j (r (m + 1)) = coeff j (r (j + 1)) := by
    intro j m hjm
    have h1 : X ^ (j + 1) ∣ g * (r (j + 1) - r (m + 1)) := by
      have e1 : g * (r (j + 1) - r (m + 1)) = (f - g * r (m + 1)) - (f - g * r (j + 1)) := by ring
      rw [e1]
      exact dvd_sub ((pow_dvd_pow X (by omega)).trans (hr (m + 1))) (hr (j + 1))
    have h2 := X_prime.pow_dvd_of_dvd_mul_left (j + 1) hg h1
    rw [X_pow_dvd_iff] at h2
    have := h2 j (Nat.lt_succ_self j)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  refine ⟨mk fun k => coeff k (r (k + 1)), ?_⟩
  rw [← sub_eq_zero]
  ext m
  rw [map_zero]
  have hq : X ^ (m + 1) ∣ r (m + 1) - mk fun k => coeff k (r (k + 1)) := by
    rw [X_pow_dvd_iff]
    intro j hj
    rw [map_sub, coeff_mk, hstable j m (by omega), sub_self]
  have hsum : X ^ (m + 1) ∣ f - g * mk fun k => coeff k (r (k + 1)) := by
    have e1 : f - g * (mk fun k => coeff k (r (k + 1))) =
        (f - g * r (m + 1)) + g * (r (m + 1) - mk fun k => coeff k (r (k + 1))) := by ring
    rw [e1]
    exact dvd_add (hr (m + 1)) (dvd_mul_of_dvd_right hq g)
  rw [X_pow_dvd_iff] at hsum
  exact hsum m (Nat.lt_succ_self m)

theorem dvd_of_pow_dvd_powerSeries [IsNoetherianRing R] [IsIntegrallyClosed R] {f g h : R⟦X⟧}
    (hg : g ≠ 0) (hh : h ≠ 0) (H : ∀ n : ℕ, g ^ n ∣ h * f ^ n) : g ∣ f := by
  obtain ⟨a, g₁, hg₁, rfl⟩ := exists_eq_X_pow_mul hg
  have hg₁0 : g₁ ≠ 0 := by rintro rfl; exact hg₁ (dvd_zero _)
  have hmem : f ∈ almostMultiples g₁ := ⟨h, hh, fun n =>
    (pow_dvd_pow_of_dvd (dvd_mul_left g₁ (X ^ a)) n).trans (H n)⟩
  obtain ⟨f', rfl⟩ := Ideal.mem_span_singleton.1 (almostMultiples_le hg₁ hmem)
  rcases eq_or_ne f' 0 with rfl | hf'
  · simp
  obtain ⟨e, f₁, hf₁, rfl⟩ := exists_eq_X_pow_mul hf'
  obtain ⟨b, h₁, hh₁, rfl⟩ := exists_eq_X_pow_mul hh
  have h1 : g₁ ^ (b + 1) * X ^ (a * (b + 1)) ∣
      g₁ ^ (b + 1) * (X ^ (b + e * (b + 1)) * (h₁ * f₁ ^ (b + 1))) := by
    have e1 : (X ^ a * g₁) ^ (b + 1) = g₁ ^ (b + 1) * X ^ (a * (b + 1)) := by ring
    have e2 : X ^ b * h₁ * (g₁ * (X ^ e * f₁)) ^ (b + 1) =
        g₁ ^ (b + 1) * (X ^ (b + e * (b + 1)) * (h₁ * f₁ ^ (b + 1))) := by ring
    rw [← e1, ← e2]; exact H (b + 1)
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero (b + 1) hg₁0)).1 h1
  have hw : ¬ (X : R⟦X⟧) ∣ h₁ * f₁ ^ (b + 1) := fun hX =>
    (X_prime.dvd_or_dvd hX).elim hh₁ fun h' => hf₁ (X_prime.dvd_of_dvd_pow h')
  have hae : a ≤ e := by
    by_contra hlt
    push Not at hlt
    have h3 : (X : R⟦X⟧) ^ (b + e * (b + 1) + 1) ∣ X ^ (b + e * (b + 1)) * (h₁ * f₁ ^ (b + 1)) :=
      (pow_dvd_pow X (by nlinarith)).trans h2
    rw [pow_succ] at h3
    exact hw ((mul_dvd_mul_iff_left (pow_ne_zero _ (X_ne_zero (R := R)))).1 h3)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hae
  exact ⟨X ^ d * f₁, by ring⟩

theorem isIntegrallyClosed_powerSeries : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R], IsIntegrallyClosed (PowerSeries R) := by
  intro R _ _ _ _
  let K := FractionRing R⟦X⟧
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨⟨f, ⟨g, hg⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R⟦X⟧) x
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  set x := IsLocalization.mk' K f (⟨g, hg⟩ : nonZeroDivisors R⟦X⟧) with hxdef
  have hgx : algebraMap R⟦X⟧ K g * x = algebraMap R⟦X⟧ K f := by
    rw [mul_comm, hxdef]; exact IsLocalization.mk'_spec K f ⟨g, hg⟩
  obtain ⟨p, hp, hpx⟩ := hx
  have hpx' : Polynomial.aeval x p = 0 := by rw [Polynomial.aeval_def]; exact hpx
  have key : ∀ n : ℕ, g ^ n ∣ g ^ p.natDegree * f ^ n := by
    intro n
    set q := (Polynomial.X ^ n : Polynomial R⟦X⟧) %ₘ p
    have hq : Polynomial.aeval x q = x ^ n := by
      rw [Polynomial.aeval_modByMonic_eq_self_of_root hpx']; simp
    have hqd : q.natDegree ≤ p.natDegree := Polynomial.natDegree_modByMonic_le _ hp
    have hterm : ∀ i ≤ p.natDegree, algebraMap R⟦X⟧ K g ^ p.natDegree * x ^ i =
        algebraMap R⟦X⟧ K (g ^ (p.natDegree - i) * f ^ i) := by
      intro i hi
      calc algebraMap R⟦X⟧ K g ^ p.natDegree * x ^ i
          = algebraMap R⟦X⟧ K g ^ (p.natDegree - i) * (algebraMap R⟦X⟧ K g * x) ^ i := by
            rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
        _ = algebraMap R⟦X⟧ K (g ^ (p.natDegree - i) * f ^ i) := by
            rw [hgx, map_mul, map_pow, map_pow]
    have hz : algebraMap R⟦X⟧ K g ^ p.natDegree * x ^ n = algebraMap R⟦X⟧ K
        (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (g ^ (p.natDegree - i) * f ^ i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hq, Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ p.natDegree := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hqd
      rw [Algebra.smul_def, mul_left_comm, hterm i hi']
      simp only [map_mul]
    refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (g ^ (p.natDegree - i) * f ^ i),
      IsFractionRing.injective R⟦X⟧ K ?_⟩
    rw [map_mul, map_mul, ← hz, map_pow, map_pow, ← hgx, map_pow]
    ring
  obtain ⟨y, hy⟩ := dvd_of_pow_dvd_powerSeries hg0 (pow_ne_zero _ hg0) key
  refine ⟨y, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, hy, map_mul, mul_comm]

end GlobalTheory.PowerSeriesNormal
end

