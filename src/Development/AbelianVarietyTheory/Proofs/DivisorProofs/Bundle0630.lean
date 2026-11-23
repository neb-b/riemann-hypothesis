module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryDegreePartCocycleModIdeal
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobRel
theorem coeff_subst_sub_mem :
    ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ]
      (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) →
      (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) →
      ∀ (m : ℕ) (c : MvPowerSeries σ Q),
        (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) →
        ∀ (w : τ →₀ ℕ), w.degree = m → ∃ r ∈ N,
          coeff w (MvPowerSeries.subst (QLog.up (Q := Q) u) c) -
            coeff w (MvPowerSeries.subst (QLog.up (Q := Q) ℓ) c) = algebraMap B Q r := by
  intro B Q σ τ _ _ _ _ N u ℓ hu hlin m c hc w hw
  have hℓ : ∀ s, constantCoeff (ℓ s) = 0 := fun s => by
    simpa only [coeff_zero_eq_constantCoeff_apply, hu s] using (hlin s 0 (by simp)).symm
  have horder : ∀ s, (2 : ℕ∞) ≤ (u s - ℓ s).order := fun s =>
    nat_le_order (n := 2) fun β hβ => by
      rw [map_sub, hlin s β (by omega), sub_self]
  have huSubst : HasSubst (QLog.up (Q := Q) u) :=
    hasSubst_of_constantCoeff_zero fun s => by simp [QLog.up, hu s]
  have hℓSubst : HasSubst (QLog.up (Q := Q) ℓ) :=
    hasSubst_of_constantCoeff_zero fun s => by simp [QLog.up, hℓ s]
  rw [coeff_subst huSubst, coeff_subst hℓSubst,
    ← finsum_sub_distrib (coeff_subst_finite huSubst c w) (coeff_subst_finite hℓSubst c w)]
  refine finsum_induction (fun x : Q => ∃ r ∈ N, x = algebraMap B Q r)
    ⟨0, N.zero_mem, by simp⟩
    (fun x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩ => ⟨r + t, N.add_mem hr ht, by rw [hx, hy, map_add]⟩)
    fun α => ?_
  have hprod (v : σ → MvPowerSeries τ B) :
      (α.prod fun s e => QLog.up (Q := Q) v s ^ e) =
        MvPowerSeries.map (algebraMap B Q) (α.prod fun s e => v s ^ e) := by
    simp only [QLog.up, Finsupp.prod, map_prod, map_pow]
  rw [hprod u, hprod ℓ, coeff_map, coeff_map, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub,
    ← map_sub]
  by_cases h : α.degree < m
  · obtain ⟨b, hb, hcb⟩ := hc α h
    exact ⟨b * _, N.mul_mem_right _ hb, by rw [hcb, map_mul]⟩
  · have hmono := GlobalTheory.SubstMod.order_monoProd_sub u ℓ hu hℓ horder α
    have hdegree : w.degree < α.degree + 1 := by omega
    have hzero : coeff w ((α.prod fun s e => u s ^ e) - α.prod fun s e => ℓ s ^ e) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hdegree) hmono)
    exact ⟨0, N.zero_mem, by rw [hzero, map_zero, mul_zero]⟩

theorem coeff_op_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type} (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (op μ u v i) = coeff β (u i + v i) := _root_.GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one

theorem coeff_prod_addLeft : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups

theorem coeff_prod_addRight : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) = if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := _root_.GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups

theorem coeff_evalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero

theorem coeff_evalTwoGroups_first_second_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem degree_sumElim3 {d : ℕ} (a b e : Fin d →₀ ℕ) :
    (Finsupp.sumElim a (Finsupp.sumElim b e)).degree = a.degree + b.degree + e.degree := by
  simp [Finsupp.degree_eq_sum, Fintype.sum_sum_type, add_assoc]

theorem x_hasSubst {R : Type} [CommRing R] {d : ℕ} (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)
    (hu : ∀ j, constantCoeff (u j) = 0) (hv : ∀ j, constantCoeff (v j) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem cocycle_rel_mod : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (m : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → In N (cob2 (QLog.up (Q := Q) μ) c) → ∀ n : Fin d →₀ ℕ, n.degree = m → ∀ a b : Fin d →₀ ℕ, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → ∃ r ∈ N, (∏ i, Nat.choose ((a + b) i) (a i) : Q) * coeff (Finsupp.sumElim (a + b) (n - (a + b))) c - (∏ i, Nat.choose ((n - a) i) (b i) : Q) * coeff (Finsupp.sumElim a (n - a)) c = algebraMap B Q r := by
  intro B O Q _ _ _ _ θ d μ hμ N m c hc hcob n hn a b ha _ hab hab'
  set e := n - (a + b) with he_def
  have he : e ≠ 0 := fun h => hab' (le_antisymm hab (tsub_eq_zero_iff_le.1 h))
  have hbe : b + e = n - a := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  have hn' : a + b + e = n := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  set w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ := Finsupp.sumElim a (Finsupp.sumElim b e) with hw_def
  have hw : w.degree = m := by
    rw [← hn, ← hn', hw_def, degree_sumElim3, map_add (f := _), map_add (f := _)]
  have hX : ∀ (R : Type) [CommRing R] (j : Fin d),
      constantCoeff (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := fun R _ j => by
    simp [x1, x2, x3]
  have hop : ∀ (R : Type) [CommRing R] (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
      (∀ i, constantCoeff (ν i) = 0) → ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      constantCoeff (op ν u v i) = 0 := fun R _ ν hν u v hu hv i =>
    constantCoeff_subst_eq_zero (x_hasSubst u v hu hv) (fun s => by cases s <;> simp [hu, hv]) (hν i)
  have hmapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      map (algebraMap B Q) (op μ u v i) = op (QLog.up (Q := Q) μ) (fun j => map (algebraMap B Q) (u j))
        (fun j => map (algebraMap B Q) (v j)) i := fun u v hu hv i => by
    simp only [op, at2, QLog.up]
    rw [map_subst (x_hasSubst u v hu hv)]
    congr 1
    funext s
    cases s <;> rfl
  have hmX : ∀ j, (map (algebraMap B Q) (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x1 j) ∧
      (map (algebraMap B Q) (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x2 j) ∧
      (map (algebraMap B Q) (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x3 j) := fun j => by
    simp [x1, x2, x3, map_X]

  have hc2 : ∀ s, constantCoeff (Sum.elim (op μ x1 x2) x3 s) = 0 := by
    intro s
    cases s with
    | inl i => exact hop B μ hμ.const _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i
    | inr i => exact (hX B i).2.2
  have hd2 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim (op μ x1 x2) x3 s) = coeff β (Sum.elim (fun i => x1 i + x2 i) x3 s) := by
    intro s β hβ
    cases s with
    | inl i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i β hβ
    | inr i => rfl
  obtain ⟨r2, hr2, h2⟩ := coeff_subst_sub_mem N _ _ hc2 hd2 m c hc w hw
  have hu2 : QLog.up (Q := Q) (Sum.elim (op μ x1 x2) x3) = Sum.elim (op (QLog.up (Q := Q) μ) x1 x2) x3 := by
    funext s
    cases s with
    | inl i =>
      simp only [QLog.up, Sum.elim_inl]
      rw [hmapop _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1)]
      simp only [(hmX _).1, (hmX _).2.1]
    | inr i => simp only [QLog.up, Sum.elim_inr]; exact (hmX i).2.2
  have hl2 : QLog.up (Q := Q) (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) x3) =
      Sum.elim (fun i => x1 i + x2 i) x3 := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl, map_add (f := _), (hmX i).1, (hmX i).2.1]
    | inr i => simp only [QLog.up, Sum.elim_inr]; exact (hmX i).2.2
  rw [hu2, hl2] at h2
  have hv2 : coeff w (MvPowerSeries.subst (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q)) x3) c) =
      (∏ i, ((a + b) i).choose (a i) : Q) * coeff (Finsupp.sumElim (a + b) e) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => by simp [(hX Q j).1, (hX Q j).2.1]) (fun j => (hX Q j).2.2)),
      finsum_eq_single _ (Finsupp.sumElim (a + b) e)]
    · rw [hw_def, coeff_prod_addLeft, ite_eq_left rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addLeft, ite_eq_right hα, smul_zero]

  have hc3 : ∀ s, constantCoeff (Sum.elim x1 (op μ x2 x3) s) = 0 := by
    intro s
    cases s with
    | inl i => exact (hX B i).1
    | inr i => exact hop B μ hμ.const _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i
  have hd3 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim x1 (op μ x2 x3) s) = coeff β (Sum.elim x1 (fun i => x2 i + x3 i) s) := by
    intro s β hβ
    cases s with
    | inl i => rfl
    | inr i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i β hβ
  obtain ⟨r3, hr3, h3⟩ := coeff_subst_sub_mem N _ _ hc3 hd3 m c hc w hw
  have hu3 : QLog.up (Q := Q) (Sum.elim x1 (op μ x2 x3)) = Sum.elim x1 (op (QLog.up (Q := Q) μ) x2 x3) := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl]; exact (hmX i).1
    | inr i =>
      simp only [QLog.up, Sum.elim_inr]
      rw [hmapop _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2)]
      simp only [(hmX _).2.1, (hmX _).2.2]
  have hl3 : QLog.up (Q := Q) (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) =
      Sum.elim x1 (fun i => x2 i + x3 i) := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl]; exact (hmX i).1
    | inr i => simp only [QLog.up, Sum.elim_inr, map_add (f := _), (hmX i).2.1, (hmX i).2.2]
  rw [hu3, hl3] at h3
  have hv3 : coeff w (MvPowerSeries.subst (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q))) c) =
      (∏ i, ((b + e) i).choose (b i) : Q) * coeff (Finsupp.sumElim a (b + e)) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => (hX Q j).1) (fun j => by simp [(hX Q j).2.1, (hX Q j).2.2])),
      finsum_eq_single _ (Finsupp.sumElim a (b + e))]
    · rw [hw_def, coeff_prod_addRight, ite_eq_left rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addRight, ite_eq_right hα, smul_zero]

  obtain ⟨k, hk, hk'⟩ := hcob w
  have hsplit : coeff w (cob2 (QLog.up (Q := Q) μ) c) = coeff w (at2 c x2 x3) -
      coeff w (MvPowerSeries.subst (Sum.elim (op (QLog.up (Q := Q) μ) x1 x2) x3) c) +
      coeff w (MvPowerSeries.subst (Sum.elim x1 (op (QLog.up (Q := Q) μ) x2 x3)) c) - coeff w (at2 c x1 x2) := by
    simp only [cob2, map_sub, map_add (f := _)]; rfl
  rw [hsplit, hw_def, coeff_evalTwoGroups_second_third_eq_zero c a b e ha, coeff_evalTwoGroups_first_second_eq_zero c a b e he, ← hw_def] at hk'
  rw [hbe] at hv3
  refine ⟨-k - r2 + r3, N.add_mem (N.sub_mem (N.neg_mem hk) hr2) hr3, ?_⟩
  rw [map_add (f := _), map_sub, map_neg, ← hk', ← h2, ← h3, hv2, hv3]
  ring

end GlobalTheory.CobRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneTeichmullerLiftIsCocycleModP
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem cob2_cob1_lift_mem_intBy_and_swap_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ →
    ∀ f ∈ quasiInt p k (Fin d),
      cob2 (fun i => Katz.lift p (μ i)) (cob1 (fun i => Katz.lift p (μ i)) f) ∈ intBy p k _ p ∧
      swap (cob1 (fun i => Katz.lift p (μ i)) f) - cob1 (fun i => Katz.lift p (μ i)) f ∈
        intBy p k _ p := by
  intro p _ k _ _ _ d μ hμ f hf
  have hL : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  obtain ⟨hcc1, hcc2, -⟩ := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (fun i => Katz.lift p (μ i)) hL f
  have hred := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ hμ.const
  have hr := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)

  have hX3 : ∀ (j : Fin d ⊕ (Fin d ⊕ Fin d)),
      constantCoeff (X j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)) = 0 :=
    fun j => constantCoeff_X j
  have hx1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      ∀ i, constantCoeff (op (fun i => Katz.lift p (μ i)) a b i) = 0 := by
    intro a b ha hb i
    exact ((_root_.GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt (Fr p k) d _ Empty a b ha hb).2.2.2.1 _).trans (hL i)
  refine ⟨?_, ?_⟩
  · rw [hcc1]
    have hA := hop x1 _ hx1 (hop x2 x3 hx2 hx3)
    have hB := hop _ x3 (hop x1 x2 hx1 hx2) hx3
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) _ _ (op μ x1 (op μ x2 x3)) f
      hA hB (fun i => (hred.2.2.1 i).1) (fun i => ?_) hf
    rw [← hμ.assoc]
    exact (hred.2.2.1 i).2
  · rw [hcc2]
    have hXs : ∀ (j : Fin d ⊕ Fin d),
        constantCoeff (X j : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
      fun j => constantCoeff_X j
    have hS : ∀ i, constantCoeff (swap (Katz.lift p (μ i))) = 0 := by
      intro i
      exact ((_root_.GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt (Fr p k) d _ Empty _ _ (fun j => hXs _) (fun j => hXs _)).2.2.2.1 _).trans
        (hL i)
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ Fin d) _ _ μ f hS hL (fun i => ?_)
      (fun i => (hr.2.2.1 (μ i))) hf
    have := (hred.1 _ _ (hr.2.2.1 (μ i))).2
    rwa [hμ.comm i] at this

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomialStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_cob1_homog_lift_binomial :
    ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q]
    (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ →
    ∀ (m : ℕ) (h : MvPowerSeries (Fin d) Q), m ≠ 0 →
    (∀ α : Fin d →₀ ℕ, α.degree ≠ m → coeff α h = 0) →
    ∀ a e : Fin d →₀ ℕ, (a + e).degree ≤ m →
    coeff (Finsupp.sumElim a e) (cob1 (GlobalTheory.QLog.up Q μ) h) =
      if a ≠ 0 ∧ e ≠ 0 then (∏ i, Nat.choose ((a + e) i) (a i) : Q) * coeff (a + e) h else 0 := by
  intro B O Q _ _ _ _ θ d μ hμ m h hm hh a e hdeg
  classical
  have hlin : ∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 →
      coeff α (GlobalTheory.QLog.up Q μ i) = coeff α (addLaw Q d i) := by
    intro i α hα
    rw [GlobalTheory.QLog.up, coeff_map, GlobalTheory.CobHom.coeff_lift_low hμ i α hα,
      GlobalTheory.Katz.LowLaw.coeff_addLaw]
    split_ifs <;> simp
  have hlow : ∀ α : Fin d →₀ ℕ, α.degree < m → coeff α h = 0 := fun α hα => hh α hα.ne
  have hγ : (Finsupp.sumElim a e).degree = (a + e).degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    simp
  have h0 : coeff 0 h = 0 := hh 0 (by simpa using Ne.symm hm)
  have hlead := (GlobalTheory.CobLead.cob_eq_additive_lead Q d (GlobalTheory.QLog.up Q μ)
    m hlin).1 h hlow (Finsupp.sumElim a e)
  rw [hlead.2 (hγ ▸ hdeg), GlobalTheory.CobHom.coeff_cob1_additive_law_binomial]
  by_cases ha : a = 0
  · subst a
    by_cases he : e = 0
    · subst e
      simp [h0]
    · simp [he]
  · by_cases he : e = 0
    · subst e
      simp [ha]
    · simp [ha, he]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwist
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

set_option backward.isDefEq.respectTransparency false

theorem delta_two_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem delta_zero_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem face_two {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_two_eq]

theorem face_zero {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_zero_eq]

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

open GlobalTheory.EtC.PicSpec

theorem corrFam_nat (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) {E : Spc} (hE : Inv Q E) (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (corrFam Q q L p s h U x) = corrFam Q q L p s h V (x.res g) := by
  match p with
  | 0 =>
    rw [corrFam_zero, corrFam_zero]
    exact map_zero (((res _ (tw q 1)).X s).obj.map g.op).hom
  | 1 =>
    obtain rfl : s = 0 := by omega
    rw [corrFam_one, corrFam_one, lineUnit_res,
      GlobalTheory.T.kummerReductionChernDefectSection_res Q q hqQ U _ (hE U ⟨x.face 0⟩) V g]
  | p + 2 =>
    rw [corrFam_add_two, corrFam_add_two]
    exact map_zero (((res _ (tw q 1)).X s).obj.map g.op).hom

theorem coefficientReduction_firstChernClass_tateTwist : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1),
    red Q q E 2 1 (c1 Q L) = c1 q L := by
  intro Q q _ hqQ E hE L
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hUnit : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive Q).1 L hE
  obtain ⟨γ', hγ', hγ0', hγ1', hγ2'⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hUnit
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).1 E 2 γ
  have hred : red Q q E 2 1 (c1 Q L) = CohomologyClass.mk β := by
    rw [← hγ]
    exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).2 E 2 γ β hβ
  rw [hred, ← hγ']
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (corrFam Q q L) (corrFam_nat Q q hqQ hE L)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨α, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1, hβ]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).1 x, hα, corrFam_zero, sec_map_zero, hγ0, hγ0', map_zero, sub_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_zero, smul_zero, Finset.sum_const_zero, add_zero, corrFam_one]
    refine (GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential Q q hqQ U (lineUnit L x) (hE U ⟨x.face 0⟩) _ _ (fun V g v hv => ?_) (fun V g w hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 1 1 _ V U g x]
      exact hγ1 V (x.res g) v (by simpa only [lineUnit_res] using hv)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 1 1 _ V U g x]
      exact hγ1' V (x.res g) w (by simpa only [lineUnit_res] using hw)
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_one]
    rw [show corrFam Q q L (1 + 1) (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three,
      lineUnit_face, face_zero, face_two]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, mul_comm (lineUnit L _) (lineUnit L _), ← sub_eq_add_neg]
    norm_num
    refine (GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects Q q hqQ U _ _ (hE U ⟨(x.face 0).face 0⟩) _ _ (fun V g v w hv hw => ?_) (fun V g v w hv hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 2 0 _ V U g x]
      exact hγ2 V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 2 0 _ V U g x]
      exact hγ2' V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
  | p + 3 =>
    have hZ := res_isZero (tw q 1) t (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.RedChern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComulChartSubSubstMemPSmulStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comul_chart_sub_subst_mem_p_smul : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n, Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  first | exact @GlobalTheory.comul_ev_sub_ev₂_subst_mem | exact GlobalTheory.comul_ev_sub_ev₂_subst_mem | (intros; apply GlobalTheory.comul_ev_sub_ev₂_subst_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffEqZeroOfEvalEqComulStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_eq_zero_of_eval_eq_comul' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : O)}) O] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, constantCoeff (μ i) = 0 := by
  first | exact @GlobalTheory.constantCoeff_eq_zero_of_eval_eq_comul | exact GlobalTheory.constantCoeff_eq_zero_of_eval_eq_comul | (intros; apply GlobalTheory.constantCoeff_eq_zero_of_eval_eq_comul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMemStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_iterate_invariantDerivation_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → ∀ (N : Ideal B) (l : MvPowerSeries (Fin d) Q) (j : Fin d), In N (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ (u : Fin d → B) (n : ℕ), 2 ≤ n → ∃ b ∈ N, constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[n] l) = algebraMap B Q b := by
  first | exact @GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem | exact GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem | (intros; apply GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem <;> assumption)
end

