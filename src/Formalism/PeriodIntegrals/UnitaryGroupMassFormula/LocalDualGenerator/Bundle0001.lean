module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDualCase
section
noncomputable section
open Module

namespace PI.LocDualGen.EpC

variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]

private theorem nontrivial_of_finrank_eq_two (hr : finrank K L = 2) : Nontrivial L := by
  rcases subsingleton_or_nontrivial L with h | h
  · rw [Module.finrank_zero_of_subsingleton] at hr
    exact absurd hr (by norm_num)
  · exact h

private theorem exists_not_mem_range_algebraMap_of_finrank_eq_two (hr : finrank K L = 2) :
    ∃ x : L, x ∉ Set.range (algebraMap K L) := by
  by_contra h
  push Not at h
  have hsurj : LinearMap.range (Algebra.linearMap K L) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨a, ha⟩ := h y
    exact ⟨a, ha⟩
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap K L)
  rw [hsurj, finrank_top, Module.finrank_self, hr] at h1
  omega

private theorem exists_eq_add_mul_of_finrank_eq_two' (hr : finrank K L = 2) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (y : L) :
    ∃ a c : K, algebraMap K L a + algebraMap K L c * x = y := by
  have := nontrivial_of_finrank_eq_two hr
  have hli : LinearIndependent K ![(1 : L), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      refine ⟨?_, rfl⟩
      have h0 : algebraMap K L s = 0 := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact hst
      exact (algebraMap K L).injective (by rw [h0, map_zero])
    · exfalso
      apply hx
      refine ⟨-(s / t), ?_⟩
      have h2 : t • x = -(s • (1 : L)) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact hst
      have h3 : x = t⁻¹ • (t • x) := by
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [Algebra.algebraMap_eq_smul_one, h3, h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hcard : Fintype.card (Fin 2) = finrank K L := by
    rw [hr, Fintype.card_fin]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  have hy := b.sum_repr y
  rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one] at hy
  exact ⟨b.repr y 0, b.repr y 1, hy⟩

theorem dichotomy (hr : finrank K L = 2) (hred : IsReduced L) :
    IsField L ∨ ∃ e : L, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  have := nontrivial_of_finrank_eq_two hr
  obtain ⟨x, hx⟩ := exists_not_mem_range_algebraMap_of_finrank_eq_two hr
  have hrep := exists_eq_add_mul_of_finrank_eq_two' hr hx
  obtain ⟨p, q, hpq0⟩ := hrep (x ^ 2)
  have hpq : x ^ 2 = algebraMap K L p + algebraMap K L q * x := hpq0.symm
  by_cases hroot : ∃ r : K, r ^ 2 = p + q * r
  · obtain ⟨r, hr2⟩ := hroot
    have hfac : (x - algebraMap K L r) * (x - algebraMap K L (q - r)) = 0 := by
      have h' : algebraMap K L (r ^ 2) = algebraMap K L (p + q * r) := by rw [hr2]
      simp only [map_add (f := _), map_mul, map_pow, map_sub] at h' ⊢
      linear_combination hpq - h'
    by_cases hrs : r = q - r
    · exfalso
      have hsq : (x - algebraMap K L r) ^ 2 = 0 := by
        have h' := hfac
        rw [← hrs] at h'
        rw [sq]
        exact h'
      have hz : x - algebraMap K L r = 0 := hred.eq_zero _ ⟨2, hsq⟩
      exact hx ⟨r, (sub_eq_zero.mp hz).symm⟩
    · right
      have hd : q - r - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
      have hsq : (x - algebraMap K L r) * (x - algebraMap K L r) =
          algebraMap K L (q - r - r) * (x - algebraMap K L r) := by
        have h' := hfac
        simp only [map_sub] at h' ⊢
        linear_combination h'
      have hu : algebraMap K L (q - r - r)⁻¹ * algebraMap K L (q - r - r) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hd, map_one]
      have hback : x - algebraMap K L r = algebraMap K L (q - r - r) *
          (algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r)) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd, map_one, one_mul]
      refine ⟨algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r), ?_, ?_, ?_⟩
      · show _ * _ = _
        linear_combination (algebraMap K L (q - r - r)⁻¹) ^ 2 * hsq +
          algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r) * hu
      · intro he
        rw [he, mul_zero, sub_eq_zero] at hback
        exact hx ⟨r, hback.symm⟩
      · intro he
        rw [he, mul_one] at hback
        apply hx
        refine ⟨q - r, ?_⟩
        simp only [map_sub] at hback ⊢
        linear_combination -hback
  · push Not at hroot
    left
    refine ⟨⟨0, 1, zero_ne_one⟩, fun a b => mul_comm a b, ?_⟩
    intro y hy
    obtain ⟨a, c, rfl⟩ := hrep y
    have hN : a * a + a * c * q - c ^ 2 * p ≠ 0 := by
      intro h0
      by_cases hc : c = 0
      · subst hc
        apply hy
        have ha : a = 0 := by simpa using h0
        simp [ha]
      · apply hroot (-a / c)
        have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
        linear_combination (c⁻¹) ^ 2 * h0 + (p * (1 + c * c⁻¹) - q * a * c⁻¹) * hci
    have hprod : (algebraMap K L a + algebraMap K L c * x) *
        (algebraMap K L (a + c * q) - algebraMap K L c * x) =
        algebraMap K L (a * a + a * c * q - c ^ 2 * p) := by
      simp only [map_add (f := _), map_mul, map_sub, map_pow]
      linear_combination (-(algebraMap K L c) ^ 2) * hpq
    refine ⟨algebraMap K L (a * a + a * c * q - c ^ 2 * p)⁻¹ *
      (algebraMap K L (a + c * q) - algebraMap K L c * x), ?_⟩
    rw [mul_left_comm, hprod, ← map_mul, inv_mul_cancel₀ hN, map_one]

end PI.LocDualGen.EpC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDualSplit
section
noncomputable section
open ValuativeRel Module

namespace PI.LocDualGen.EpS

variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]

theorem li (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    LinearIndependent K ![e, 1 - e] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h0' : (1 - e) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs : s • e = 0 := by
    have := congrArg (· * e) hst
    simp only [add_mul, smul_mul_assoc, he.eq, zero_mul] at this
    rwa [mul_comm (1 - e) e, hef, smul_zero, add_zero] at this
  have ht : t • (1 - e) = 0 := by
    have := congrArg (· * (1 - e)) hst
    simp only [add_mul, smul_mul_assoc, hf.eq, zero_mul, hef, smul_zero, zero_add] at this
    exact this
  exact ⟨(smul_eq_zero.mp hs).resolve_right h0, (smul_eq_zero.mp ht).resolve_right h0'⟩

section V
variable [ValuativeRel K]

theorem isIntegral_idem (e : L) (he : IsIdempotentElem e) : IsIntegral 𝒪[K] e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub (by simp)
  · simp [pow_two, he.eq]

theorem mem_of_isIntegral {c : K} (h : IsIntegral 𝒪[K] c) : c ∈ 𝒪[K] := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝒪[K]) (K := K)).mp h
  rw [← hy]; exact y.2
end V

variable (hr : finrank K L = 2) (e : L) (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1)

def bas : Basis (Fin 2) K L :=
  basisOfLinearIndependentOfCardEqFinrank (li e he h0 h1) (by simp [hr])

theorem bas0 : bas hr e he h0 h1 0 = e := by simp [bas]
theorem bas1 : bas hr e he h0 h1 1 = 1 - e := by simp [bas]

theorem decomp (z : L) :
    z = (bas hr e he h0 h1).repr z 0 • e + (bas hr e he h0 h1).repr z 1 • (1 - e) := by
  conv_lhs => rw [← (bas hr e he h0 h1).sum_repr z]
  rw [Fin.sum_univ_two, bas0, bas1]

theorem repr_pair (s t : K) :
    (bas hr e he h0 h1).repr (s • e + t • (1 - e)) 0 = s ∧
    (bas hr e he h0 h1).repr (s • e + t • (1 - e)) 1 = t := by
  have : s • e + t • (1 - e) = s • bas hr e he h0 h1 0 + t • bas hr e he h0 h1 1 := by
    rw [bas0, bas1]
  rw [this]
  simp

theorem mul_decomp (z w : L) :
    z * w = ((bas hr e he h0 h1).repr z 0 * (bas hr e he h0 h1).repr w 0) • e +
      ((bas hr e he h0 h1).repr z 1 * (bas hr e he h0 h1).repr w 1) • (1 - e) := by
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have hfe : (1 - e) * e = 0 := by rw [mul_comm, hef]
  conv_lhs => rw [decomp hr e he h0 h1 z, decomp hr e he h0 h1 w]
  simp only [add_mul, mul_add, smul_mul_smul_comm, he.eq, hf.eq, hef, hfe, smul_zero, add_zero,
    zero_add]

def pr (i : Fin 2) : L →ₐ[K] K :=
  AlgHom.ofLinearMap ((bas hr e he h0 h1).coord i)
    (by
      have : (1 : L) = (1 : K) • e + (1 : K) • (1 - e) := by simp
      rw [Basis.coord_apply, this]
      fin_cases i
      · exact (repr_pair hr e he h0 h1 1 1).1
      · exact (repr_pair hr e he h0 h1 1 1).2)
    (by
      intro z w
      simp only [Basis.coord_apply]
      rw [mul_decomp hr e he h0 h1 z w]
      fin_cases i
      · exact (repr_pair hr e he h0 h1 _ _).1
      · exact (repr_pair hr e he h0 h1 _ _).2)

theorem pr_apply (i : Fin 2) (z : L) : pr hr e he h0 h1 i z = (bas hr e he h0 h1).repr z i := rfl

theorem pr_e : pr hr e he h0 h1 0 e = 1 ∧ pr hr e he h0 h1 1 e = 0 := by
  have : e = (1 : K) • e + (0 : K) • (1 - e) := by simp
  have key := repr_pair hr e he h0 h1 1 0
  rw [← this] at key
  rw [pr_apply, pr_apply]; exact key

theorem pr_f : pr hr e he h0 h1 0 (1 - e) = 0 ∧ pr hr e he h0 h1 1 (1 - e) = 1 := by
  rw [map_sub, map_sub, map_one, map_one, (pr_e hr e he h0 h1).1, (pr_e hr e he h0 h1).2]
  simp

theorem trace_eq (z : L) : Algebra.trace K L z = pr hr e he h0 h1 0 z + pr hr e he h0 h1 1 z := by
  rw [Algebra.trace_eq_matrix_trace (bas hr e he h0 h1) z, Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, bas0, bas1]
  have a := congrArg (fun w => (bas hr e he h0 h1).repr w 0) (mul_decomp hr e he h0 h1 z e)
  have b := congrArg (fun w => (bas hr e he h0 h1).repr w 1) (mul_decomp hr e he h0 h1 z (1 - e))
  rw [a, b, (repr_pair hr e he h0 h1 _ _).1, (repr_pair hr e he h0 h1 _ _).2]
  have pe := pr_e hr e he h0 h1
  have pf := pr_f hr e he h0 h1
  simp only [pr_apply] at pe pf
  rw [pe.1, pf.2, mul_one, mul_one, pr_apply, pr_apply]

variable [ValuativeRel K]

theorem int_iff (z : L) :
    IsIntegral 𝒪[K] z ↔ pr hr e he h0 h1 0 z ∈ 𝒪[K] ∧ pr hr e he h0 h1 1 z ∈ 𝒪[K] := by
  constructor
  · intro h
    exact ⟨mem_of_isIntegral (h.map ((pr hr e he h0 h1 0).restrictScalars 𝒪[K])),
      mem_of_isIntegral (h.map ((pr hr e he h0 h1 1).restrictScalars 𝒪[K]))⟩
  · rintro ⟨ha, hb⟩
    rw [decomp hr e he h0 h1 z, Algebra.smul_def, Algebra.smul_def]
    have hie := isIntegral_idem (K := K) e he
    have hif : IsIntegral 𝒪[K] (1 - e) := isIntegral_one.sub hie
    have ia : IsIntegral 𝒪[K] (algebraMap K L ((bas hr e he h0 h1).repr z 0)) :=
      isIntegral_algebraMap (R := 𝒪[K]) (x := (⟨_, ha⟩ : 𝒪[K]))
    have ib : IsIntegral 𝒪[K] (algebraMap K L ((bas hr e he h0 h1).repr z 1)) :=
      isIntegral_algebraMap (R := 𝒪[K]) (x := (⟨_, hb⟩ : 𝒪[K]))
    exact (ia.mul hie).add (ib.mul hif)


include hr e he h0 h1 in
include hr he h0 h1 in
theorem selfDual_split (x : L) :
    (∀ y : L, IsIntegral 𝒪[K] y → Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ IsIntegral 𝒪[K] x := by
  have pe := pr_e hr e he h0 h1
  have pf := pr_f hr e he h0 h1
  constructor
  · intro h
    have ha := h e (isIntegral_idem e he)
    have hb := h (1 - e) (isIntegral_one.sub (isIntegral_idem e he))
    rw [trace_eq hr e he h0 h1, map_mul, map_mul, pe.1, pe.2] at ha
    rw [trace_eq hr e he h0 h1, map_mul, map_mul, pf.1, pf.2] at hb
    simp only [mul_one, mul_zero, add_zero, zero_add] at ha hb
    exact (int_iff hr e he h0 h1 x).mpr ⟨ha, hb⟩
  · intro hx y hy
    have := (int_iff hr e he h0 h1 (x * y)).mp (hx.mul hy)
    rw [trace_eq hr e he h0 h1]
    exact add_mem this.1 this.2

end PI.LocDualGen.EpS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram
section
noncomputable section

open ValuativeRel

namespace PI.LocDualGen.W

def PsiKer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (t : ℚ_[l]) (a : ℚ), (∃ n : ℕ, a.den = l ^ n) → ‖t - (a : ℚ_[l])‖ ≤ 1 →
    (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ ‖t‖ ≤ 1)

def FpDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K]

def FpDualUnram : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    Irreducible ((l : ℕ) : 𝒪[K]) →
    ∀ a : K, (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K))‖ ≤ 1) ↔ a ∈ 𝒪[K]

def EpSelfDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (L : Type) [CommRing L]
    [Algebra K L], IsNonarchimedeanLocalField K → CharZero K →
    Module.Free K L → Module.finrank K L = 2 → IsReduced L →
    ∀ O : Subring L, (∀ x : L, x ∈ O ↔ IsIntegral 𝒪[K] x) →
    (∀ ϖ : 𝒪[K], Irreducible ϖ → ∀ x ∈ O,
      x * x ∈ Submodule.span O {algebraMap K L (ϖ : K)} →
        x ∈ Submodule.span O {algebraMap K L (ϖ : K)}) →
    ∀ x : L, (∀ y ∈ O, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ O

end PI.LocDualGen.W
end
end

