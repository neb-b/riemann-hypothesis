module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrSpanG
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrBase

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrSpan
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G.Joints.PlaneGramSpan

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem coe_initSet_zero (N : ℕ) : ((initSet N 0 : Finset (Fin N)) : Set (Fin N)) = ∅ := by
  ext j; simp [initSet]

theorem coe_initSet_succ (N : ℕ) (i : Fin N) :
    ((initSet N (i.succ : Fin (N + 1)).val : Finset (Fin N)) : Set (Fin N)) = {j | j ≤ i} := by
  ext j
  simp only [initSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Fin.val_succ]
  rw [Fin.le_iff_val_le_val]
  omega

theorem brSPAN [CharZero (G.KK O)] (S : G.UniformizedDVR p O) (h3 : Formalism.MainNotions.PlaneGramData.PolynomialSpanAtRing O) :
    SPAN (G.KK O) (vQ p S) p := by
  classical
  intro _ N r _ sg d
  obtain ⟨h3a, h3b, h3c⟩ := h3
  let LL : G.Letters (Fin N) := ⟨sg⟩
  haveI : Finite (Idx N r LL d) := idx_finite h3a N r LL d
  letI : Fintype (Idx N r LL d) := Fintype.ofFinite _
  have hint : ∀ F : MvPolynomial (Fin N × Fin r) (G.KK O), Integral (vQ p S) F →
      ∀ m, ∃ o : O, AddMonoidAlgebra.coeff F m = algebraMap O (G.KK O) o :=
    fun F hF m => (vQ_nonneg_iff S _).1 (hF m)
  let cI : (b : Idx N r LL d) → Fin #(G.colRange b.1.1.mu) → ℤ :=
    fun b k => ((G.colRange b.1.1.mu).equivFin.symm k : ℤ)
  refine ⟨Idx N r LL d, inferInstance, fun b => G.Psi (G.KK O) b.1.1.mu b.1.2, fun b => b.1.1.mu,
    fun b => #(G.colRange b.1.1.mu), fun b k => G.Kcol (G.KK O) b.1.1.mu (cI b k) N (b.1.2 (cI b k)),
    cI, fun b k i => b.1.1.h i (cI b k),
    fun b k => Finset.univ.filter (fun i => G.IsUsed b.1.1.mu (cI b k) i),
    ?_, li_K h3a N r LL d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    refine ⟨?_, ?_⟩
    · rw [PolK_eq]
      exact (psiK_mem h3a b).1
    · intro m
      obtain ⟨o, ho⟩ := (psiK_mem h3a b).2 m
      rw [ho]
      exact (vQ_nonneg_iff S _).2 ⟨o, rfl⟩
  · intro F hF
    obtain ⟨hFK, hFI⟩ := hF
    rw [PolK_eq] at hFK
    obtain ⟨l, hl⟩ := span_all (LL := LL) h3a F hFK (hint F hFI)
    exact ⟨fun b => algebraMap O _ (l b), fun b => (vQ_nonneg_iff S _).2 ⟨_, rfl⟩, hl⟩
  · rintro th F ⟨⟨hFK, hFI⟩, hA⟩
    rw [PolK_eq] at hFK
    have hth : ∀ i : Fin N, ((th i.succ : ℤ) : WithTop ℤ) ≤ G.valS LL {j | j ≤ i} F := by
      intro i
      have h1 := hA i.succ
      change ((th i.succ : ℤ) : WithTop ℤ) ≤ valS sg (initSet N (i.succ : Fin (N + 1)).val) F at h1
      rw [valS_eq, coe_initSet_succ] at h1
      exact h1
    obtain ⟨l, hl1, hl2⟩ := span_mem h3b F hFK (hint F hFI) (fun i => th i.succ) hth
    refine ⟨fun b => algebraMap O _ (l b), fun b => (vQ_nonneg_iff S _).2 ⟨_, rfl⟩, ?_, hl2⟩
    intro b hb i
    have hlb : l b ≠ 0 := by
      intro h0
      apply hb
      simp [h0]
    dsimp only
    rw [lastIdx_eq]
    cases i using Fin.cases with
    | zero =>
      rw [b.1.1.zero]
      have hF0 : F ≠ 0 := by
        intro hF0
        rw [hF0] at hl2
        have hz := Fintype.linearIndependent_iff.1 (li_K h3a N r LL d) _ hl2.symm b
        exact hlb (IsFractionRing.injective O (G.KK O) (by rw [hz, map_zero]))
      have h0 := hA 0
      change ((th 0 : ℤ) : WithTop ℤ) ≤ valS sg (initSet N (0 : Fin (N + 1)).val) F at h0
      rw [valS_eq, Fin.val_zero, coe_initSet_zero] at h0
      exact valS_empty_le LL F hF0 _ h0
    | succ j => exact hl1 b hlb j
  · intro b
    exact (prod_fin_equiv (G.colRange b.1.1.mu) (fun c => G.Kcol (G.KK O) b.1.1.mu c N (b.1.2 c))).symm
  · intro b k
    dsimp only
    rw [PolK, mem_restrictSupport_iff]
    intro m hm
    rw [← Formalism.MainNotions.G.Joints.StandardMonomialSpace.lift_Kcol_map (algebraMap O (G.KK O))] at hm
    have hm' := MvPolynomial.support_map_subset _ _ hm
    intro i
    have h1 := (h3c N r LL d b.1.1).1 (cI b k) (b.1.2 (cI b k)) i m hm'
    simpa [G.multideg] using h1
  · intro b i
    rw [← (h3c N r LL d b.1.1).2.1 i]
    refine Finset.card_bij (fun k _ => (((G.colRange b.1.1.mu).equivFin.symm k : ℤ))) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨Subtype.prop _, hk⟩
    · intro k1 _ k2 _ h
      exact (G.colRange b.1.1.mu).equivFin.symm.injective (Subtype.ext h)
    · intro c hc
      simp only [Finset.mem_filter] at hc
      refine ⟨(G.colRange b.1.1.mu).equivFin ⟨c, hc.1⟩, ?_, ?_⟩
      · simp [cI, hc.2]
      · simp
  · intro b k i hc
    refine ((h3c N r LL d b.1.1).2.2.2.1 (cI b k) hc i).trans (le_of_eq ?_)
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LL]
    tauto
  · intro b k i
    dsimp only
    rw [valS_eq]
    cases i using Fin.cases with
    | zero =>
      rw [Fin.val_zero, coe_initSet_zero]
      have hv0 : colVal (cI b k) (b.1.1.h 0 (cI b k)) r = 0 := by
        show colVal (cI b k) (G.colH (b.1.1.mu 0) (cI b k)) r = 0
        rw [b.1.1.zero, colH_zero]
        have hr := NeZero.ne r
        simp only [colVal]
        split_ifs <;> omega
      rw [hv0]
      exact valS_empty_nonneg LL _
    | succ j =>
      rw [coe_initSet_succ]
      exact col_est h3b b.1.1 (cI b k) (b.1.2 (cI b k)) (b.2.2.1 (cI b k)) j
  · intro b i
    dsimp only
    rw [lastIdx_eq, stage_identity b.1.1 i]
    exact (sum_fin_equiv _ (fun c => colVal c (b.1.1.h i c) r)).symm

end Formalism.MainNotions.PlaneGram
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.UnitLevelOne
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section Dig

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]

theorem vQ_rat_ge (hp : p.Prime) (S : G.UniformizedDVR p O) (x : ℚ) (c : ℕ) (h : CovariantDegrees.PadicGe p x c) :
    ((c : ℕ) : WithTop ℚ) ≤ vQ p S ((x : ℚ) : G.KK O) := by
  obtain ⟨z, hz⟩ := G.Joints.rat_padicGe_cast hp S x c h
  rw [hz, ← geQ_nat_iff S]
  exact G.Joints.geQ_vK_pow_mul S c z

theorem vQ_rat_nonneg (hp : p.Prime) (S : G.UniformizedDVR p O) (x : ℚ) (h : CovariantDegrees.PadicGe p x 0) :
    0 ≤ vQ p S ((x : ℚ) : G.KK O) := by
  have := vQ_rat_ge hp S x 0 (by simpa using h)
  simpa using this

theorem vQ_rat_unit [CharZero (G.KK O)] (hp : p.Prime) (S : G.UniformizedDVR p O) (x : ℚ) (hx : x ≠ 0)
    (h : padicValRat p x = 0) : vQ p S ((x : ℚ) : G.KK O) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 := vQ_rat_nonneg hp S x (Or.inr (by simp [h]))
  have h2 := vQ_rat_nonneg hp S x⁻¹ (Or.inr (by rw [padicValRat.inv, h]; simp))
  have h3 : vQ p S ((x : ℚ) : G.KK O) + vQ p S ((x⁻¹ : ℚ) : G.KK O) = 0 := by
    rw [← AddValuation.map_mul, ← Rat.cast_mul, mul_inv_cancel₀ hx, Rat.cast_one, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg h1 h2).mp h3).1

theorem unit_level_one (n : ℕ) : G.cUnit 1 n * G.dUnit 1 n 0 = 1 := by
  unfold G.cUnit G.dUnit
  have : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  simp [this]

theorem unit_at_zero (P : ℕ) : G.cUnit P 0 * G.dUnit P 0 0 = 1 := by
  unfold G.cUnit G.dUnit
  simp

theorem brDIG [CharZero (G.KK O)] (D : Formalism.BasicNotions.D7) (S : G.UniformizedDVR p O) {n' : ℕ} (hG : G.AdmissibleDVR p n' O)
    (h5 : PlaneGramData.FactorialDigitSplitAtRing p O) : DIG (G.KK O) (vQ p S) p := by
  classical
  intro _ τ _ r g
  have hp := hG.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hA, hB⟩ := (G.GLWeightTheory.lemma_five_two_first_holds D) p hp hG.five_le
  refine ⟨fun t ρ n => (((∏ a, ((ρ a).factorial : ℚ)) * ((p ^ g t).factorial : ℚ) ^ n : ℚ) : G.KK O),
    fun t ρ β => ((PlaneGramData.gamDig (p ^ g t) ρ β : ℚ) : G.KK O), ?_, ?_⟩
  · intro t ρ hρ
    obtain ⟨h1, h2, -⟩ := h5 (g t) r ρ hρ
    refine ⟨fun n => ?_, fun β => ⟨vQ_rat_unit hp S _ (h2 β).1 (h2 β).2, ?_⟩⟩
    · rw [Rat.cast_ne_zero]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast Nat.factorial_ne_zero _)
        (pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero _))
    · have := congrArg (fun x : ℚ => (x : G.KK O)) (h1 β)
      push_cast at this ⊢
      rw [this]
  · intro ρ hρ c _ ε hε
    set tt : τ × Fin r → ℕ := fun k => g k.1 - 1 with htt
    set rh : τ × Fin r → ℕ := fun k => ρ k.1 k.2 with hrh'
    have hlev : ∀ k : τ × Fin r, g k.1 ≠ 0 → tt k + 1 = g k.1 := by
      intro k h0; simp only [htt]; omega
    have hrh : ∀ k, rh k < p ^ (tt k + 1) := by
      intro k
      have h := hρ k.1 k.2
      by_cases h0 : g k.1 = 0
      · rw [h0, pow_zero] at h
        exact lt_of_lt_of_le h (Nat.one_le_pow _ _ hp.pos)
      · rw [hlev k h0]; exact h
    obtain ⟨-, -, hQ⟩ := hB (τ × Fin r) tt rh hrh
    obtain ⟨T, q, hT, hq⟩ := hQ (decide (ε = -1)) c
    set ze : (τ × Fin r → ℕ) → (τ × Fin r → ℕ) := fun β k => if g k.1 = 0 then 0 else β k with hze
    have hquot : ∀ e' : τ × Fin r → ℕ,
        ((∏ k, (((rh k + p ^ (tt k + 1) * e' k).factorial : ℕ) : ℚ)) /
          (∏ k, ((rh k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (tt k + 1)).factorial : ℚ) ^ (e' k))) =
        ∏ k, G.cUnit (p ^ (tt k + 1)) (e' k) * G.dUnit (p ^ (tt k + 1)) (e' k) (rh k) := by
      intro e'
      have hlet : ∀ k, (((rh k + p ^ (tt k + 1) * e' k).factorial : ℕ) : ℚ) =
          (((rh k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (tt k + 1)).factorial : ℚ) ^ (e' k)) *
            (G.cUnit (p ^ (tt k + 1)) (e' k) * G.dUnit (p ^ (tt k + 1)) (e' k) (rh k)) := by
        intro k
        rw [hA (tt k) (rh k) (e' k) (hrh k)]; ring
      rw [Finset.prod_congr rfl (fun k _ => hlet k), Finset.prod_mul_distrib]
      have hne : (∏ k, ((rh k).factorial : ℚ) * ((e' k).factorial : ℚ) *
          ((p ^ (tt k + 1)).factorial : ℚ) ^ (e' k)) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
        have h1 : ((rh k).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
        have h2 : ((e' k).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
        have h3 : ((p ^ (tt k + 1)).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
        exact mul_ne_zero (mul_ne_zero h1 h2) (pow_ne_zero _ h3)
      rw [mul_div_cancel_left₀ _ hne]
    have hk : ∀ (β : τ × Fin r → ℕ) (k : τ × Fin r),
        G.cUnit (p ^ (tt k + 1)) (ze β k) * G.dUnit (p ^ (tt k + 1)) (ze β k) (rh k) =
          G.cUnit (p ^ g k.1) (β k) * G.dUnit (p ^ g k.1) (β k) (ρ k.1 k.2) := by
      intro β k
      by_cases h0 : g k.1 = 0
      · have hr0 : ρ k.1 k.2 = 0 := by
          have h := hρ k.1 k.2
          rw [h0, pow_zero] at h
          omega
        have e1 : ze β k = 0 := by simp only [hze, if_pos h0]
        have e2 : rh k = 0 := hr0
        rw [e1, e2, unit_at_zero, h0, pow_zero, hr0, unit_level_one]
      · have e1 : ze β k = β k := by simp only [hze, if_neg h0]
        rw [e1, hlev k h0]
    have hprod : ∀ β : τ × Fin r → ℕ,
        (∏ k, G.cUnit (p ^ (tt k + 1)) (ze β k) * G.dUnit (p ^ (tt k + 1)) (ze β k) (rh k)) =
          ∏ t, PlaneGramData.gamDig (p ^ g t) (ρ t) (fun a => β (t, a)) := by
      intro β
      rw [Finset.prod_congr rfl (fun k _ => hk β k), Fintype.prod_prod_type]
      rfl
    have hsum : ∀ β : τ × Fin r → ℕ,
        (∑ j ∈ T, q j * ∏ k, ((ze β k).choose (j k) : ℚ)) =
          ∑ j ∈ T.filter (fun m => ∀ k : τ × Fin r, g k.1 = 0 → m k = 0), q j * ∏ k, ((β k).choose (j k) : ℚ) := by
      intro β
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hjz
      · congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases h0 : g k.1 = 0
        · simp only [hze, if_pos h0, hjz k h0, Nat.choose_zero_right]
        · simp only [hze, if_neg h0]
      · push Not at hjz
        obtain ⟨k, h0, hne⟩ := hjz
        rw [Finset.prod_eq_zero (Finset.mem_univ k), mul_zero]
        simp only [hze, if_pos h0]
        rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hne), Nat.cast_zero]
    refine ⟨T.filter (fun m => ∀ k : τ × Fin r, g k.1 = 0 → m k = 0), fun m => ((q m : ℚ) : G.KK O), ?_, ?_⟩
    · intro m hm
      have := hT m (Finset.mem_filter.mp hm).1
      exact ⟨vQ_rat_nonneg hp S _ this.2, by omega⟩
    · intro β
      have hb := hq (ze β)
      simp only [hquot, hprod, hsum] at hb
      have hv := vQ_rat_ge hp S _ c hb
      have e : ((∏ t, ((PlaneGramData.gamDig (p ^ g t) (ρ t) (fun a => β (t, a)) : ℚ) : G.KK O)) ^ ε -
          binomComb (T.filter (fun m => ∀ k : τ × Fin r, g k.1 = 0 → m k = 0))
            (fun m => ((q m : ℚ) : G.KK O)) β) =
          (((if decide (ε = -1) = true then (∏ t, PlaneGramData.gamDig (p ^ g t) (ρ t) (fun a => β (t, a)))⁻¹
            else ∏ t, PlaneGramData.gamDig (p ^ g t) (ρ t) (fun a => β (t, a))) -
            ∑ j ∈ T.filter (fun m => ∀ k : τ × Fin r, g k.1 = 0 → m k = 0),
              q j * ∏ k, ((β k).choose (j k) : ℚ) : ℚ) : G.KK O) := by
        unfold binomComb
        rcases hε with rfl | rfl
        · simp
        · simp
      rw [e]
      exact hv

end Dig

end Formalism.MainNotions.PlaneGram
end
end

