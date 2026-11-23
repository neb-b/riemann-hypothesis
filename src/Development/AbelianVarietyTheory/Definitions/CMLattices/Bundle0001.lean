module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.CMLattices.CmHostBarHalfIntegerGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.Test

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_rt (H : Host E) : H.bar H.rt = -H.rt := by
  have hsq : (H.bar H.rt - H.rt) * (H.bar H.rt + H.rt) = 0 := by
    have e : H.bar (H.rt ^ 2) = H.bar (-(H.d : 𝓞 E)) := by rw [H.rt_sq]
    rw [map_pow, map_neg, map_natCast, ← H.rt_sq] at e
    linear_combination e
  rcases mul_eq_zero.mp hsq with h | h
  · exfalso
    have hfix : H.bar H.rt = H.rt := sub_eq_zero.mp h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hc := H.bar_eq H.rt
    rw [hfix] at hc
    have hconj : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← NumberField.IsCMField.complexEmbedding_complexConj, ← hc]
    have hsqC : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow]
      have e : ((H.rt ^ 2 : 𝓞 E) : E) = ((-(H.d : 𝓞 E) : 𝓞 E) : E) := by rw [H.rt_sq]
      push_cast at e
      rw [e]
      simp
    have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.mp hconj
    have hre := congrArg Complex.re hsqC
    simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
    have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  · linear_combination h

variable {D : Datum H} {ε : ℤˣ} {h : D.La → D.La → OK H}

variable {K : Type} [Field K] [NumberField K]

theorem hasType_neg {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {G : Over (Sp (𝓞 K))} [GrpObj G] {act : OAct (𝓞 E) G}
    {p q : ℕ} (h : HasType H act ρ p q) : HasType H act (-ρ) q p := by
  intro k _ _ β hβ τ
  obtain ⟨h1, h2⟩ := h k β hβ τ
  have e1 : τ H.rt ^ 2 = -(H.d : k) := by rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have e2 : β ρ ^ 2 = -(H.d : k) := by rw [← map_pow, hρ, map_neg, map_natCast]
  have hτ : (τ H.rt - β ρ) * (τ H.rt + β ρ) = 0 := by linear_combination e1 - e2
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    have hd0 : ((H.d : ℕ) : 𝓞 K) = 0 := by
      have e := hρ
      rw [zero_pow two_ne_zero] at e
      exact neg_eq_zero.mp e.symm
    exact H.d_prime.ne_zero (by exact_mod_cast hd0)
  have h2k : (2 : k) ≠ 0 := by
    intro h0
    have e : β 2 = β 0 := by rw [map_ofNat, h0, map_zero]
    have := hβ e
    norm_num at this
  have hβρ : β ρ ≠ 0 := by
    intro h0
    exact hρ0 (hβ (h0.trans (map_zero β).symm))
  have hne : β ρ ≠ -β ρ := by
    intro h0
    have e : (2 : k) * β ρ = 0 := by linear_combination h0
    rcases mul_eq_zero.mp e with e' | e'
    · exact h2k e'
    · exact hβρ e'
  constructor
  · intro hneg
    rw [map_neg] at hneg
    apply h2
    intro heq
    rw [heq] at hneg
    exact hne hneg
  · intro hne'
    apply h1
    rcases mul_eq_zero.mp hτ with h0 | h0
    · exact sub_eq_zero.mp h0
    · exfalso
      apply hne'
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_left h0

end GlobalTheory.CM.Test
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial
open scoped TensorProduct Pointwise

namespace GlobalTheory.CM

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem baseChange_neg_form (D : Datum H) (x y : ℝ ⊗[ℤ] D.La) :
    (-D.EF).baseChange ℝ x y = -D.EF.baseChange ℝ x y := by
  induction x with
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
  | tmul r a =>
    induction y with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]; ring
    | tmul s b => simp

def oppDatum (D : Datum H) : Datum H where
  La := D.La
  fin := D.fin
  proj := D.proj
  EF := -D.EF
  alt x := by simp [D.alt]
  unimod := by
    have : (⇑(-D.EF) : D.La → _) = (fun f => -f) ∘ D.EF := rfl
    rw [this]
    exact neg_involutive.bijective.comp D.unimod
  adj a x y := by simp [D.adj]
  p := D.q
  q := D.p
  rank := by rw [D.rank, add_comm]
  dom := by
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    refine ⟨-J, fun x => by simp [h1], fun x y => ?_, fun x hx => ?_, fun a A t hA ht => ?_⟩
    · simp [baseChange_neg_form, h2]
    · simpa [baseChange_neg_form] using h3 x hx
    · obtain ⟨e1, e2, e3⟩ := h4 a A (starRingEnd ℂ t) hA (by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [ht, map_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp [add_comm])
      refine ⟨by rw [LinearMap.neg_comp, LinearMap.comp_neg, e1], by simpa using e2, ?_⟩
      rw [LinearMap.neg_comp, map_neg, e3]
      simp

end General

namespace CyclotomicTwentyEight

end CyclotomicTwentyEight

end GlobalTheory.CM
end
end

