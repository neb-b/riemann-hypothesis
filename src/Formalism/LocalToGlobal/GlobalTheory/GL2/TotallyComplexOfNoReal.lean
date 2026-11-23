module

public import Formalism.LocalToGlobal.GlobalTheory.GL2.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.UnipotentAdelicQuotients.Bundle0001

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ShortIntervalPrimes NumberField

section Ray

variable {K0 : Type} [Field K0] [NumberField K0]

lemma exists_mem_sub_one_mem (qq I : Ideal (𝓞 K0)) (hI : CoprimeTo K0 qq I) :
    ∃ b ∈ I, b ≠ 0 ∧ b - 1 ∈ qq := by
  obtain ⟨i, hi, t, ht, hit⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 K0) ∈ I ⊔ qq by rw [hI.2]; trivial)
  by_cases h0 : i = 0
  · subst h0
    have ht1 : t = 1 := by simpa using hit
    have hq : qq = ⊤ := (Ideal.eq_top_iff_one qq).2 (ht1 ▸ ht)
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.1
    exact ⟨b, hb, hb0, by rw [hq]; trivial⟩
  · refine ⟨i, hi, h0, ?_⟩
    have : i - 1 = -t := by rw [← hit]; ring
    rw [this]
    exact qq.neg_mem ht

lemma exists_rel_of_class (qq I J : Ideal (𝓞 K0)) (hI : CoprimeTo K0 qq I) (hJ : CoprimeTo K0 qq J)
    (x y : 𝓞 K0) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ b - 1 ∈ qq ∧ Ideal.span {a} ⊔ qq = ⊤ ∧
      Ideal.span {a} * I = Ideal.span {b} * J := by
  obtain ⟨b, hbI, hb0, hb1⟩ := exists_mem_sub_one_mem qq I hI
  have hxb : x * b ∈ Ideal.span {y} := by
    have : x * b ∈ Ideal.span {x} * I := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hbI
    rw [hxy] at this
    exact Ideal.mul_le_left this
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hxb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact mul_ne_zero hx hb0 ha.symm
  have hy' : Ideal.span {y} ≠ (0 : Ideal (𝓞 K0)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hy
  have key : Ideal.span {a} * I = Ideal.span {b} * J := by
    apply mul_left_cancel₀ hy'
    calc Ideal.span {y} * (Ideal.span {a} * I) = Ideal.span {a * y} * I := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, mul_comm y a]
      _ = Ideal.span {b} * (Ideal.span {x} * I) := by
          rw [ha, ← mul_assoc, Ideal.span_singleton_mul_span_singleton, mul_comm b x]
      _ = Ideal.span {y} * (Ideal.span {b} * J) := by
          rw [hxy, mul_left_comm]
  have hbq : Ideal.span {b} ⊔ qq = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 K0) = b - (b - 1) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self b)) (Ideal.mem_sup_right hb1)
  have hcop : Ideal.span {b} * J ⊔ qq = ⊤ := by
    have h1 : IsCoprime (Ideal.span {b}) qq := Ideal.isCoprime_iff_sup_eq.2 hbq
    have h2 : IsCoprime J qq := Ideal.isCoprime_iff_sup_eq.2 hJ.2
    exact Ideal.isCoprime_iff_sup_eq.1 (h1.mul_left h2)
  have haq : Ideal.span {a} ⊔ qq = ⊤ := by
    rw [← key] at hcop
    refine top_unique ?_
    calc (⊤ : Ideal (𝓞 K0)) = Ideal.span {a} * I ⊔ qq := hcop.symm
      _ ≤ Ideal.span {a} ⊔ qq := sup_le_sup_right Ideal.mul_le_left qq
  exact ⟨a, b, ha0, hb0, hb1, haq, key⟩

variable (hCN : HeckeCharacterZeroLocus.ClassNumberQuad.ClassNumberLe.{0})
include hCN

end Ray

end Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

end
