module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionIntegralBasisChange
section
namespace GlobalTheory


open Matrix in
theorem phaseCondition_basisChange : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ)
    (P : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) →
    (∀ i j, P i j ∈ Formalism.UG.intL L) → (∀ i j, Q' i j ∈ Formalism.UG.intL L) → Q * Q' = 1 →
    ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (P * x * Q)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))) + σ (δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))))) / 2) = 1) := by
  intro L _ _ σ δ n n' A ψ P Q Q' hσσ hσv hP hQ' hQQ' x hx C' hskew hv hint
  have hmap1 : (1 : Matrix (Fin n) (Fin n) L).map σ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)
  have hyQ' : (P * x * Q) * Q' = P * x := by rw [Matrix.mul_assoc, hQQ', Matrix.mul_one]
  have e1 : ∀ Z : Matrix (Fin n) (Fin n') L, Q * (Q' * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hQQ', Matrix.one_mul]
  have e2 : ∀ Z : Matrix (Fin n) (Fin n') L, (Q'.map σ)ᵀ * ((Q.map σ)ᵀ * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.map_mul, hQQ', hmap1, Matrix.transpose_one,
      Matrix.one_mul]
  have intMul : ∀ {a b c : ℕ} (M : Matrix (Fin a) (Fin b) L) (N : Matrix (Fin b) (Fin c) L),
      (∀ i j, M i j ∈ Formalism.UG.intL L) → (∀ i j, N i j ∈ Formalism.UG.intL L) → ∀ i j, (M * N) i j ∈ Formalism.UG.intL L := by
    intro a b c M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)
  have hPσ : ∀ i j, (P.map σ)ᵀ i j ∈ Formalism.UG.intL L := by
    intro i j
    show Valued.v (σ (P j i)) ≤ 1
    rw [hσv]; exact hP j i
  have htr : Matrix.trace ((P.map σ)ᵀ * C' * P * (x * A * (x.map σ)ᵀ)) =
      Matrix.trace (C' * ((P * x * Q) * (Q' * A * (Q'.map σ)ᵀ) * ((P * x * Q).map σ)ᵀ)) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc, e1, e2]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hCx : (P.map σ)ᵀ * (C' * (P * x * Q)) * Q' = (P.map σ)ᵀ * C' * P * x := by
    calc (P.map σ)ᵀ * (C' * (P * x * Q)) * Q' = (P.map σ)ᵀ * (C' * ((P * x * Q) * Q')) := by
          simp only [Matrix.mul_assoc]
      _ = (P.map σ)ᵀ * (C' * (P * x)) := by rw [hyQ']
      _ = _ := by simp only [Matrix.mul_assoc]
  have := hx ((P.map σ)ᵀ * C' * P) ?_ ?_ ?_
  · rw [htr] at this; exact this
  · intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσσ, hskew,
      Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · intro i j
    have hlt : ∀ (a b : L), Valued.v a ≤ 1 → Valued.v b < 1 → Valued.v (a * b) < 1 := by
      intro a b ha hb
      rw [map_mul]
      calc Valued.v a * Valued.v b ≤ 1 * Valued.v b := mul_le_mul' ha le_rfl
        _ = Valued.v b := one_mul _
        _ < 1 := hb
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    rw [mul_comm]
    refine hlt _ _ (hP k j) ?_
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
    exact hlt _ _ (hPσ i l) (hv l k)
  · intro i j
    rw [← hCx]
    exact intMul _ _ (intMul _ _ hPσ hint) hQ' i j

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionSubIntegralMatrix
section
noncomputable section

namespace GlobalTheory.Hk3.ShiftPhase

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mul_int {a b c : ℕ} (P : Matrix (Fin a) (Fin b) L) (Q : Matrix (Fin b) (Fin c) L)
    (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) (hQ : ∀ i j, Q i j ∈ Formalism.UG.intL L) :
    ∀ i j, (P * Q) i j ∈ Formalism.UG.intL L := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hQ k j)

theorem trace_int {a : ℕ} (P : Matrix (Fin a) (Fin a) L) (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) :
    P.trace ∈ Formalism.UG.intL L :=
  Subring.sum_mem _ fun i _ => hP i i

theorem conjT_int {a b : ℕ} (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (P : Matrix (Fin a) (Fin b) L) (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) :
    ∀ i j, (Matrix.transpose (P.map σ)) i j ∈ Formalism.UG.intL L := by
  intro i j
  show Valued.v (σ (P j i)) ≤ 1
  rw [hσ]; exact hP j i

theorem phase_shift (σ : L →+* L) (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (h2 : Valued.v (2 : L) = 1) (ψ : AddChar L ℂ) (hψ : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1)
    (u u' : L) (hd : u - u' ∈ Formalism.UG.intL L) (h : ψ ((u + σ u) / 2) = 1) :
    ψ ((u' + σ u') / 2) = 1 := by
  have he : ((u - u') + σ (u - u')) / 2 ∈ Formalism.UG.intL L := by
    show Valued.v (((u - u') + σ (u - u')) / 2) ≤ 1
    rw [map_div₀, h2, div_one]
    refine (Formalism.UG.intL L).add_mem hd ?_
    show Valued.v (σ (u - u')) ≤ 1
    rw [hσ]; exact hd
  have hs : σ (((u - u') + σ (u - u')) / 2) = ((u - u') + σ (u - u')) / 2 := by
    rw [map_div₀, map_add (f := _), hσσ, map_ofNat]; ring
  have heq : (u' + σ u') / 2 = (u + σ u) / 2 - ((u - u') + σ (u - u')) / 2 := by
    rw [map_sub]; ring
  rw [heq, AddChar.map_sub_eq_div, h, hψ _ he hs, div_one]

end GlobalTheory.Hk3.ShiftPhase

namespace GlobalTheory.Hk3.ShiftPhase

open Matrix

theorem conjT_mul_int {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {a b : ℕ} (σ : L →+* L)
    (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (C : Matrix (Fin a) (Fin a) L) (hC : ∀ i j, σ (C i j) = - C j i)
    (x : Matrix (Fin a) (Fin b) L) (hCx : ∀ i j, (C * x) i j ∈ Formalism.UG.intL L) :
    ∀ i j, (Matrix.transpose (x.map σ) * C) i j ∈ Formalism.UG.intL L := by
  intro j k
  have h : (Matrix.transpose (x.map σ) * C) j k = - σ ((C * x) k j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hC,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  refine (Formalism.UG.intL L).neg_mem ?_
  show Valued.v (σ _) ≤ 1
  rw [hσ]; exact hCx k j

theorem shift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) →
    Valued.v δ = 1 → σ δ = -δ → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    ∀ x l : Matrix (Fin n') (Fin n) L, (∀ i j, l i j ∈ Formalism.UG.intL L) →
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (x - l)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))) + σ (δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))))) / 2) = 1) := by
  intro L _ _ ϖ σ q δ n n' A ψ hU hq hA hδ _ hψ x l hl hx C hC hCv hCxl
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, -⟩ := hU
  have hCi : ∀ i j, C i j ∈ Formalism.UG.intL L := fun i j => (hCv i j).le
  have hCl : ∀ i j, (C * l) i j ∈ Formalism.UG.intL L := mul_int C l hCi hl
  have hCx : ∀ i j, (C * x) i j ∈ Formalism.UG.intL L := by
    have e : C * x = C * (x - l) + C * l := by rw [Matrix.mul_sub]; abel
    intro i j
    rw [e, Matrix.add_apply]
    exact (Formalism.UG.intL L).add_mem (hCxl i j) (hCl i j)
  have hsub : Matrix.transpose ((x - l).map σ) = Matrix.transpose (x.map σ) - Matrix.transpose (l.map σ) := by
    ext i j; simp [map_sub]
  set X := Matrix.transpose (x.map σ) with hX
  set Y := Matrix.transpose (l.map σ) with hY
  have hYi : ∀ i j, Y i j ∈ Formalism.UG.intL L := conjT_int σ hσv l hl
  have hXC : ∀ i j, (X * C) i j ∈ Formalism.UG.intL L := conjT_mul_int σ hσσ hσv C hC x hCx
  have hd : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y)))
      = Matrix.trace (C * x * A * Y) + Matrix.trace (X * C * l * A) - Matrix.trace (C * l * A * Y) := by
    have h3 : Matrix.trace (C * (l * A * X)) = Matrix.trace (X * C * l * A) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    rw [h3]
    simp only [Matrix.mul_assoc]
    abel
  have hdi : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y))) ∈ Formalism.UG.intL L := by
    rw [hd]
    refine (Formalism.UG.intL L).sub_mem ((Formalism.UG.intL L).add_mem ?_ ?_) ?_
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hCx hA) hYi)
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hXC hl) hA)
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hCl hA) hYi)
  rw [hsub]
  refine phase_shift σ hσσ hσv h2 ψ hψ (δ * Matrix.trace (C * (x * A * X))) _ ?_ (hx C hC hCv hCx)
  rw [← mul_sub]
  refine (Formalism.UG.intL L).mul_mem ?_ hdi
  show Valued.v δ ≤ 1
  rw [hδ]

end GlobalTheory.Hk3.ShiftPhase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

private theorem sorted_list_sign_split (d : List ℤ) (h : d.Pairwise (fun a b => b ≤ a)) :
    d = d.filter (fun x => decide (0 < x)) ++ d.filter (fun x => decide (x = 0)) ++ d.filter (fun x => decide (x < 0)) := by
  induction d with
  | nil => rfl
  | cons x t ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hx, ht⟩ := h
    have ih := ih ht
    rcases lt_trichotomy 0 x with hpos | hzero | hneg
    · have h1 : ¬ x = 0 := by omega
      have h2 : ¬ x < 0 := by omega
      rw [List.filter_cons_of_pos (by simp [hpos]), List.filter_cons_of_neg (by simp [h1]),
        List.filter_cons_of_neg (by simp [h2]), List.cons_append, List.cons_append, ← ih]
    · subst hzero
      have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; simpa using hx y hy
      rw [e1, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simp),
        List.filter_cons_of_neg (by simp), e1, List.nil_append, List.cons_append, ← ih]
    · have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have e2 : t.filter (fun x => decide (x = 0)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have h1 : ¬ 0 < x := by omega
      have h2 : ¬ x = 0 := by omega
      rw [e1, e2, List.nil_append, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp [h1]), List.filter_cons_of_neg (by simp [h2]),
        List.filter_cons_of_pos (by simp [hneg]), e1, e2, List.nil_append, List.nil_append, ← ih]

private theorem flatMap_singleton_natCast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = l.map (fun a : ℕ => (a : ℤ)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

private theorem label_list_eq_signed (n : ℕ) (s : List ℕ) : labIn n s =
    s.map (fun a : ℕ => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++ (s.reverse.map fun a : ℕ => -(a : ℤ)) := by
  unfold labIn
  show List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s) ++ _ ++
      List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s.reverse) = _
  rw [flatMap_singleton_natCast, flatMap_singleton_natCast]
  simp [List.map_map, Function.comp_def]

theorem labIn_selfDual_iff : ∀ (n : ℕ) (d : List ℤ), (d.length = n ∧ d.Pairwise (fun a b => b ≤ a) ∧ dualLab d = d) ↔
    ∃ s : List ℕ, 2 * s.length ≤ n ∧ s.Pairwise (fun a b => b ≤ a) ∧ (∀ a ∈ s, 0 < a) ∧ d = labIn n s := by
  intro n d
  constructor
  · rintro ⟨hlen, hsort, hdual⟩
    have hsplit := sorted_list_sign_split d hsort
    set P := d.filter (fun x => decide (0 < x)) with hPdef
    set Z := d.filter (fun x => decide (x = 0)) with hZdef
    set N := d.filter (fun x => decide (x < 0)) with hNdef
    have hPN : P = (N.map Neg.neg).reverse := by
      have e : P = (dualLab d).filter (fun x => decide (0 < x)) := by rw [hdual]
      rw [e, dualLab, List.filter_reverse, List.filter_map, hNdef]
      congr 2
      apply List.filter_congr
      intro x _
      simp
    have hN : N = P.reverse.map Neg.neg := by
      rw [hPN, List.reverse_reverse, List.map_map]
      simp
    have hZ : Z = List.replicate Z.length 0 := by
      rw [List.eq_replicate_iff]
      refine ⟨rfl, ?_⟩
      intro b hb
      rw [hZdef] at hb
      simpa using (List.mem_filter.mp hb).2
    have hlenPN : N.length = P.length := by rw [hN, List.length_map, List.length_reverse]
    have hdlen : d.length = P.length + Z.length + N.length := by
      have := congrArg List.length hsplit
      simpa only [List.length_append] using this
    have hposP : ∀ x ∈ P, 0 < x := by
      intro x hx
      rw [hPdef] at hx
      simpa using (List.mem_filter.mp hx).2
    have hcast : (P.map Int.toNat).map (fun a : ℕ => (a : ℤ)) = P := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id P]
      apply List.map_congr_left
      intro x hx
      have := hposP x hx
      simp only [Function.comp_apply, id]
      omega
    refine ⟨P.map Int.toNat, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map]; omega
    · have hPs : P.Pairwise (fun a b => b ≤ a) := hsort.filter _
      rw [List.pairwise_map]
      exact hPs.imp (fun h => Int.toNat_le_toNat h)
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have := hposP x hx
      omega
    · have hneg : ((P.map Int.toNat).reverse.map fun a : ℕ => -(a : ℤ)) = N := by
        rw [hN]
        conv_rhs => rw [← hcast]
        simp [List.map_reverse, List.map_map, Function.comp_def]
      have hZ' : Z = List.replicate (n - 2 * P.length) 0 := by
        rw [hZ]
        congr 1
        omega
      rw [label_list_eq_signed, hcast, List.length_map, hneg, ← hZ']
      exact hsplit
  · rintro ⟨s, hs, hsort, hpos, rfl⟩
    rw [label_list_eq_signed]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_replicate, List.length_reverse]
      omega
    · rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hsort.imp (fun h => by exact_mod_cast h)
      · rw [List.pairwise_replicate]
        right; exact le_refl _
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [List.eq_of_mem_replicate hb]
        exact_mod_cast Nat.zero_le x
      · rw [List.pairwise_map, List.pairwise_reverse]
        refine hsort.imp (fun h => ?_)
        simp only [neg_le_neg_iff]
        exact_mod_cast h
      · intro a ha b hb
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
        have hb0 : -(y : ℤ) ≤ 0 := by simp
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
          have : (0 : ℤ) ≤ x := by exact_mod_cast Nat.zero_le x
          omega
        · rw [List.eq_of_mem_replicate ha]
          exact hb0
    · simp [dualLab, List.map_append, List.reverse_append, List.map_reverse, List.map_map,
        Function.comp_def, List.map_replicate, List.reverse_replicate]

end GlobalTheory.Hk3
end

