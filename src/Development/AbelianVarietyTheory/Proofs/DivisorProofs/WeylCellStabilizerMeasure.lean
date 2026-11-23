module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158

@[expose] public section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory.ShellU

section Balls

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def ball (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (j : ℤ) : AddSubgroup L where
  carrier := {b | Valued.v b ≤ WithZero.exp j}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show Valued.v (a + b) ≤ _
    exact (Valuation.map_add _ a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by
    show Valued.v (-a) ≤ _
    rwa [Valuation.map_neg]

def antiBall (σ : L →+* L) (j : ℤ) : AddSubgroup L where
  carrier := {b | σ b = -b ∧ Valued.v b ≤ WithZero.exp j}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_add (f := _), ha, hb, neg_add], (Valuation.map_add _ a b).trans (max_le ha' hb')⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [map_neg, ha], by rwa [Valuation.map_neg]⟩

def fixBall (σ : L →+* L) (j : ℤ) : AddSubgroup L where
  carrier := {f | σ f = f ∧ Valued.v f ≤ WithZero.exp j}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_add (f := _), ha, hb], (Valuation.map_add _ a b).trans (max_le ha' hb')⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [map_neg, ha], by rwa [Valuation.map_neg]⟩

theorem mem_ball {j : ℤ} {b : L} : b ∈ ball L j ↔ Valued.v b ≤ WithZero.exp j := Iff.rfl

theorem mem_antiBall {σ : L →+* L} {j : ℤ} {b : L} :
    b ∈ antiBall σ j ↔ σ b = -b ∧ Valued.v b ≤ WithZero.exp j := Iff.rfl

theorem mem_fixBall {σ : L →+* L} {j : ℤ} {f : L} :
    f ∈ fixBall σ j ↔ σ f = f ∧ Valued.v f ≤ WithZero.exp j := Iff.rfl


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem relIndex_eq_of_mul {c : L} (hc : c ≠ 0) {A B A' B' : AddSubgroup L}
    (hA : ∀ x, x ∈ A ↔ c * x ∈ A') (hB : ∀ x, x ∈ B ↔ c * x ∈ B') : A.relIndex B = A'.relIndex B' := by
  have e1 : A = A'.comap (AddMonoidHom.mulLeft c) := AddSubgroup.ext hA
  have e2 : B = B'.comap (AddMonoidHom.mulLeft c) := AddSubgroup.ext hB
  rw [e1, AddSubgroup.relIndex_comap, e2, AddSubgroup.map_comap_eq_self_of_surjective]
  intro y
  exact ⟨c⁻¹ * y, mul_inv_cancel_left₀ hc y⟩

theorem le_exp_neg_one_of_lt_one {y : WithZero (Multiplicative ℤ)} (h : y < 1) : y ≤ WithZero.exp (-1 : ℤ) := by
  induction y using WithZero.recZeroCoe with
  | zero => exact zero_le'
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    show (a : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

theorem relIndex_ball {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) :
    (ball L (-1)).relIndex (ball L 0) = q ^ 2 := by
  obtain ⟨-, -, -, -, -, -, hcard⟩ := hU
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hv
  let f : v.valuationSubring →+ L := v.valuationSubring.subtype.toAddMonoidHom
  have e1 : (IsLocalRing.maximalIdeal v.valuationSubring).toAddSubgroup = (ball L (-1)).comap f := by
    ext x
    show x ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ v (x : L) ≤ WithZero.exp (-1 : ℤ)
    rw [Valuation.mem_maximalIdeal_iff]
    refine ⟨le_exp_neg_one_of_lt_one, fun h => h.trans_lt ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have e2 : (⊤ : AddSubgroup v.valuationSubring).map f = ball L 0 := by
    ext x
    rw [mem_ball, WithZero.exp_zero]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (Valuation.mem_valuationSubring_iff _ _).1 y.2
    · intro h
      exact ⟨⟨x, (Valuation.mem_valuationSubring_iff _ _).2 h⟩, trivial, rfl⟩
  rw [← e2, ← AddSubgroup.relIndex_comap, ← e1, AddSubgroup.relIndex_top_right, AddSubgroup.index_eq_card]
  exact hcard

theorem relIndex_anti_eq_fix {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (j : ℤ) :
    (antiBall σ j).relIndex (antiBall σ (j + 1)) = (fixBall σ (-1)).relIndex (fixBall σ 0) := by
  obtain ⟨hσ, -, hϖ, hv, ⟨x, -, hx⟩, -, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  set δ := σ x - x with hδ
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hδ0 : δ ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hv'; exact WithZero.exp_ne_zero hv'.symm
  have hc : δ * ϖ ^ (j + 1) ≠ 0 := mul_ne_zero hδ0 (zpow_ne_zero _ hϖ0)
  have key : ∀ (i : ℤ) (z : L), z ∈ antiBall σ (i + (j + 1)) ↔ δ * ϖ ^ (j + 1) * z ∈ fixBall σ i := by
    intro i z
    rw [mem_antiBall, mem_fixBall]
    refine and_congr ?_ ?_
    · rw [map_mul, map_mul, map_zpow₀, hϖ, hσδ]
      constructor
      · intro h; rw [h]; ring
      · intro h
        apply mul_left_cancel₀ hc
        linear_combination -h
    · rw [map_mul, map_mul, map_zpow₀, hx, hv', one_mul, ← WithZero.exp_zsmul, WithZero.exp_add,
        smul_eq_mul, mul_neg, mul_one, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_comm]
  refine relIndex_eq_of_mul hc (fun z => ?_) (fun z => ?_)
  · rw [← key]; congr! 2; ring
  · rw [← key]; congr! 2; ring

theorem relIndex_antiBall {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (j : ℤ) :
    (antiBall σ j).relIndex (antiBall σ (j + 1)) = q := by
  have h0 := relIndex_ball hU
  have h1 := relIndex_anti_eq_fix hU (-1)
  rw [relIndex_anti_eq_fix hU j]
  obtain ⟨hσ, hvσ, -, -, ⟨x, hxO, hx⟩, -, -⟩ := hU
  set δ := σ x - x with hδ
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hδ0 : δ ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  set e := -x / δ with he
  have he1 : e + σ e = 1 := by
    rw [he, map_div₀, map_neg, hσδ]; field_simp; rw [hδ]; ring
  have hve : Valued.v e ≤ 1 := by
    rw [he, map_div₀, hx, div_one, Valuation.map_neg]
    exact (Valuation.mem_integer_iff _ _).1 hxO
  let t : L →+ L := AddMonoidHom.id L - σ.toAddMonoidHom
  have ht : ∀ z, t z = z - σ z := fun z => rfl
  have hte : ∀ b, σ b = -b → t (e * b) = b := fun b hb => by
    rw [ht, map_mul, hb]; linear_combination b * he1
  have hσt : ∀ z, σ (t z) = -t z := fun z => by rw [ht, map_sub, hσ]; ring
  have hvt : ∀ z i, Valued.v z ≤ WithZero.exp i → Valued.v (t z) ≤ WithZero.exp (i : ℤ) := fun z i h =>
    (Valuation.map_sub _ _ _).trans (max_le h ((hvσ z).le.trans h))
  have hve' : ∀ z i, Valued.v z ≤ WithZero.exp i → Valued.v (e * z) ≤ WithZero.exp (i : ℤ) := fun z i h => by
    rw [map_mul]; exact (mul_le_mul' hve h).trans (one_mul _).le
  have hle : WithZero.exp (-1 : ℤ) ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.2 (by norm_num)
  have a1 : (ball L 0).map t = antiBall σ 0 := by
    ext b
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hσt z, hvt z 0 hz⟩
    · rintro ⟨hb, hb'⟩
      exact ⟨e * b, hve' b 0 hb', hte b hb⟩
  have a2 : (antiBall σ (-1)).comap t ⊓ ball L 0 = fixBall σ 0 ⊔ ball L (-1) := by
    apply le_antisymm
    · rintro z ⟨⟨-, hz⟩, hz'⟩
      refine AddSubgroup.mem_sup.2 ⟨z - e * t z, ⟨?_, ?_⟩, e * t z, hve' _ _ hz, by ring⟩
      · have : t (z - e * t z) = 0 := by rw [map_sub, hte _ (hσt z), sub_self]
        rw [ht] at this
        exact (sub_eq_zero.1 this).symm
      · exact (Valuation.map_sub _ _ _).trans (max_le hz' ((hve' _ _ hz).trans hle))
    · refine sup_le (fun z hz => ⟨⟨hσt z, ?_⟩, hz.2⟩) (fun z hz => ⟨⟨hσt z, hvt z _ hz⟩, le_trans hz hle⟩)
      rw [ht, hz.1, sub_self, map_zero]; exact zero_le'
  have a3 : ball L (-1) ⊓ fixBall σ 0 = fixBall σ (-1) :=
    le_antisymm (fun z hz => ⟨hz.2.1, hz.1⟩) (fun z hz => ⟨hz.2, hz.1, hz.2.trans hle⟩)
  have b1 : (fixBall σ 0 ⊔ ball L (-1)).relIndex (ball L 0) = (fixBall σ (-1)).relIndex (fixBall σ 0) := by
    rw [← a2, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, a1, ← h1]; norm_num
  have b2 : (ball L (-1)).relIndex (fixBall σ 0 ⊔ ball L (-1)) = (fixBall σ (-1)).relIndex (fixBall σ 0) := by
    rw [AddSubgroup.relIndex_sup_right, ← a3, AddSubgroup.inf_relIndex_right]
  have b3 := AddSubgroup.relIndex_mul_relIndex (ball L (-1)) (fixBall σ 0 ⊔ ball L (-1)) (ball L 0) le_sup_right
    (by rw [← a2]; exact inf_le_right)
  rw [b1, b2, h0, ← sq] at b3
  exact Nat.pow_left_injective two_ne_zero b3

end Balls

theorem measure_eq_relIndex_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (H K : Subgroup G) (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (hle : H ≤ K)
    (hi : H.relIndex K ≠ 0) : μ K = (H.relIndex K : ENNReal) * μ H := by
  have hemb : MeasurableEmbedding (K.subtype : K → G) := MeasurableEmbedding.subtype_coe hK
  haveI : (μ.comap (K.subtype : K → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hi⟩
  have key := (H.subgroupOf K).index_mul_measure (hemb.measurable hH) (μ.comap (K.subtype : K → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (K.subtype : K → G) '' Set.univ = (K : Set G) := by
    ext x; simp
  have e2 : (K.subtype : K → G) '' ((H.subgroupOf K : Subgroup K) : Set K) = (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  exact key.symm

theorem measure_chain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H : ℤ → Subgroup G) {q : ℕ} (hq : q ≠ 0)
    (hm : ∀ j, MeasurableSet (H j : Set G)) (hle : ∀ j, H j ≤ H (j + 1))
    (hi : ∀ j, (H j).relIndex (H (j + 1)) = q) (h0 : μ (H 0) = 1) (j : ℤ) : μ (H j) = (q : ENNReal) ^ j := by
  have hq0 : (q : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have step : ∀ j, μ (H (j + 1)) = q * μ (H j) := fun j => by
    rw [measure_eq_relIndex_mul μ (H j) (H (j + 1)) (hm _) (hm _) (hle j) (by rw [hi]; exact hq), hi]
  induction j using Int.induction_on with
  | zero => rw [h0, zpow_zero]
  | succ i ih => rw [step, ih, ENNReal.zpow_add hq0 hqt, zpow_one, mul_comm]
  | pred i ih =>
    have h := step (-(i : ℤ) - 1)
    rw [sub_add_cancel, ih] at h
    apply (ENNReal.mul_right_inj hq0 hqt).1
    rw [← h]
    conv_lhs => rw [show -(i : ℤ) = 1 + (-(i : ℤ) - 1) by ring, ENNReal.zpow_add hq0 hqt, zpow_one]

theorem isOpen_ball {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L}
    (hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (j : ℤ) : IsOpen {x : L | Valued.v x ≤ WithZero.exp j} := by
  have e : {x : L | Valued.v x ≤ WithZero.exp j} = (fun x => ϖ ^ j * x) ⁻¹' (intL L : Set L) := by
    ext x
    show _ ↔ Valued.v (ϖ ^ j * x) ≤ 1
    rw [map_mul, map_zpow₀, hv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, WithZero.exp_neg,
      inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
    rfl
  rw [e]
  exact (Valued.isOpen_integer L).preimage (continuous_const.mul continuous_id)

end GlobalTheory.ShellU

end
