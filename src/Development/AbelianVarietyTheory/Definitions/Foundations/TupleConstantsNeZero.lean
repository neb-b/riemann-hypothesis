module

public import Mathlib
public import Formalism.PairingDivisors.StatementH
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

@[expose] public section

open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

noncomputable section

namespace GlobalTheory.Square

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def IsAwayUnit (m : ℕ) (x : K) : Prop :=
  ∃ (a : 𝓞 K) (k k' : ℕ), a ∣ (m : 𝓞 K) ^ k' ∧ x * (m : K) ^ k = (a : K)

structure An (y : ℕ) where

  c : ℂ

  c0 : ℂ

  u : Fin y → ℂ

  Lv : ℤ → ℂ

structure Co (K κ : Type) where

  X : Type
  [finX : Fintype X]

  gam : X → ℕ

  z : X → κ → K

  z' : X → κ → K

attribute [instance] Co.finX

def normAlg {κ X : Type} [Fintype κ] [Fintype X] (G : κ → κ → K) (gam : X → ℕ) (z : X → κ → K) : K :=
  ∑ x, (gam x : K)⁻¹ * ∑ k, ∑ l, z x k * star (z x l) * G k l

structure Sq (K : Type) where

  κ : Type
  [finκ : Fintype κ]

  G : κ → κ → K

  Om : ℂ

  Om' : ℂ

  A : ℂ

  e : ℕ

  p : ℕ

  q : ℕ

  e0 : ℕ

  h0 : ℕ

  base : An (p + q)

attribute [instance] Sq.finκ

def StepRatio {T : Type} (σ₀ : K →+* ℂ) (Qn : ℕ) (S0 : Finset T) (cc qq : T → ℕ) (u1 u0 : ℂ) : Prop :=
  ∃ (b : K) (g g' : T → 𝓞 K), IsAwayUnit Qn b ∧
    (∀ v ∈ S0, g v ∣ (qq v : 𝓞 K) ^ cc v ∧ g' v ∣ (qq v : 𝓞 K) ^ cc v) ∧
    u1 = σ₀ (b * ∏ v ∈ S0, (g v : K) / (g' v : K)) * u0


omit [NumberField K] [StarRing K] in
theorem IsAwayUnit.of_dvd {m k : ℕ} {a : 𝓞 K} (h : a ∣ (m : 𝓞 K) ^ k) : IsAwayUnit m (a : K) :=
  ⟨a, 0, k, h, by simp⟩


omit [NumberField K] [StarRing K] in
theorem IsAwayUnit.one (m : ℕ) : IsAwayUnit m (1 : K) :=
  ⟨1, 0, 0, by simp, by simp⟩


omit [NumberField K] [StarRing K] in
theorem IsAwayUnit.mul {m : ℕ} {x x' : K} (h : IsAwayUnit m x) (h' : IsAwayUnit m x') : IsAwayUnit m (x * x') := by
  obtain ⟨a, k, j, ha, hx⟩ := h
  obtain ⟨a', k', j', ha', hx'⟩ := h'
  refine ⟨a * a', k + k', j + j', by rw [pow_add]; exact mul_dvd_mul ha ha', ?_⟩
  have : ((a * a' : 𝓞 K) : K) = (a : K) * (a' : K) := by simp
  rw [this, ← hx, ← hx']
  ring


omit [StarRing K] in
theorem vw_eq_zero_of_notMem (w : Pl K) {a : 𝓞 K} (ha : a ∉ w.asIdeal) : vw w (a : K) = 0 := by
  classical
  have ha0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rintro rfl
    exact ha w.asIdeal.zero_mem
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ ha0]
  by_contra h
  have h' : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
    intro h0
    exact h (by rw [h0]; rfl)
  exact ha (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd ha0 w.irreducible).1 h'))

theorem IsAwayUnit.ne_zero_and_vw {m : ℕ} {x : K} (h : IsAwayUnit m x) (w : Pl K) (hm : (m : 𝓞 K) ∉ w.asIdeal) :
    x ≠ 0 ∧ vw w x = 0 := by
  obtain ⟨a, k, k', ⟨b, hb⟩, hx⟩ := h
  have hpow : ∀ j : ℕ, (m : 𝓞 K) ^ j ∉ w.asIdeal := fun j hj => hm (w.isPrime.mem_of_pow_mem j hj)
  have ha : a ∉ w.asIdeal := fun h => hpow k' (hb ▸ w.asIdeal.mul_mem_right b h)
  have ha0 : (a : K) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    exact ha (this ▸ w.asIdeal.zero_mem)
  have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at hx; exact ha0 hx.symm
  have hk0 : (m : K) ^ k ≠ 0 := by intro h; rw [h, mul_zero] at hx; exact ha0 hx.symm
  refine ⟨hx0, ?_⟩
  have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w x _ hx0 hk0
  have h2 := vw_eq_zero_of_notMem w ha
  have h3 := vw_eq_zero_of_notMem w (hpow k)
  have h4 : ((((m : 𝓞 K) ^ k : 𝓞 K)) : K) = (m : K) ^ k := by simp
  rw [h4] at h3
  rw [hx, h2, h3] at h1
  omega


namespace TwoStep

theorem vw_natCast_nonneg (w : Pl K) (n : ℕ) : (0 : ℝ) ≤ (vw w (n : K) : ℝ) := by
  have : 0 ≤ vw w (n : K) := by simpa using Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (n : 𝓞 K)
  exact_mod_cast this



end TwoStep

end GlobalTheory.Square
