module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionLowerEntryMultiplicationLaw
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.PartRed.LowLaw

section Alg
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


omit [Fintype n'] [DecidableEq n'] in
theorem rowAdd_mul_apply (r l : Fin c) (a : k) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (p : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)) :
    ((fromBlocks 1 0 0 (transvection r l a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) p q =
      t p q + if p = Sum.inr r then a * t (Sum.inr l) q else 0 := by
  rw [Matrix.mul_apply]
  rcases p with p | p
  · simp [Fintype.sum_sum_type, Matrix.one_apply]
  · simp [Fintype.sum_sum_type, transvection, add_mul, Finset.sum_add_distrib, Matrix.one_apply, single_apply,
      ite_and, eq_comm]

theorem mem_trans {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ transSet ρ ↔ Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val := by simp [transSet]

theorem mem_fix {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ fixSet ρ ↔ (∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨
      (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s) := by simp [fixSet]

theorem mem_low {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ lowSet ρ ↔ ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val := by simp [lowSet]

theorem fill_row_zero (ρ : ℕ) (l r : Fin c) (i : Fin (c + 1)) (hi : ρ < i.val) (hil : i.val ≤ l.val)
    (hr : r.val + 1 = i.val) (E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (hfix : fixSet ρ ⊆ E)
    (hlow : (lowSet ρ).filter (fun e => colIx e < i.val) ⊆ E)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : (transSet (n := n) (n' := n') (c := c) ρ) → k)
    (q : n' ⊕ Fin (c + 1)) (hq : (Sum.inr r, q) ∉ transSet (n := n) (n' := n') (c := c) ρ) :
    fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) q = 0 := by
  simp only [fillAt, of_apply]
  rcases q with s | j
  · have h1 : (Sum.inr l, Sum.inl s) ∉ transSet (n := n) (n' := n') (c := c) ρ := by
      rw [mem_trans]; simp [Free]; omega
    have h2 : (Sum.inr l, Sum.inl s) ∈ E := hfix (by rw [mem_fix]; right; exact ⟨l, s, rfl, by omega, rfl⟩)
    rw [dif_neg h1, if_pos h2]
    simp [basePt]
  · rw [mem_trans] at hq
    simp [Free] at hq
    have hj : j.val ≤ r.val := by omega
    have h1 : (Sum.inr l, Sum.inr j) ∉ transSet (n := n) (n' := n') (c := c) ρ := by
      rw [mem_trans]; simp [Free]; omega
    have h2 : (Sum.inr l, Sum.inr j) ∈ E := by
      by_cases hjρ : j.val ≤ ρ
      · exact hfix (by rw [mem_fix]; left; exact ⟨j, rfl, hjρ, by simp [Free]; omega⟩)
      · exact hlow (by
          rw [Finset.mem_filter, mem_low]
          exact ⟨⟨l, j, rfl, by omega, by omega⟩, by simp [colIx]; omega⟩)
    have hlj : l.val ≠ j.val := by omega
    rw [dif_neg h1, if_pos h2]
    simp [basePt, hlj]

theorem rowAdd_fill (ρ : ℕ) (l r : Fin c) (i : Fin (c + 1)) (hi : ρ < i.val) (hil : i.val ≤ l.val)
    (hr : r.val + 1 = i.val) (E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (hfix : fixSet ρ ⊆ E)
    (hlow : (lowSet ρ).filter (fun e => colIx e < i.val) ⊆ E) (b : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : (transSet (n := n) (n' := n') (c := c) ρ) → k) :
    (fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *
        fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y =
      fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x (y + fun j => if j.1.1 = Sum.inr r then
        b * fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) j.1.2 else 0) := by
  ext p q
  rw [rowAdd_mul_apply]
  by_cases hpq : (p, q) ∈ transSet (n := n) (n' := n') (c := c) ρ
  · conv_rhs => rw [fillAt, of_apply, dif_pos hpq]
    conv_lhs => rw [fillAt, of_apply, dif_pos hpq]
    rfl
  · have h0 : (if p = Sum.inr r then
        b * fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) q else 0) = 0 := by
      split_ifs with hp
      · subst hp
        rw [fill_row_zero ρ l r i hi hil hr E hfix hlow x y q hpq, mul_zero]
      · rfl
    rw [h0, add_zero]
    simp only [fillAt, of_apply, dif_neg hpq]

omit [Fintype n'] [DecidableEq n'] in
theorem ch_rowAdd (l r : Fin c) (i : Fin (c + 1)) (hr : r.val + 1 = i.val) (b : k)
    (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) =
      ch t + b * t (Sum.inr l) (Sum.inr i) := by
  have hsi : r.succ = i := Fin.ext (by simp [hr])
  simp [ch, rowAdd_mul_apply, Finset.sum_add_distrib, hsi]

def elem (r l : Fin c) (h : r ≠ l) (a : k) : GL (Fin c) k :=
  ⟨transvection r l a, transvection r l (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem embA_elem_val (r l : Fin c) (h : r ≠ l) (a : k) :
    (embA n (elem r l h a)).val = fromBlocks 1 0 0 (transvection r l a) := rfl

theorem embA_elem_inv_val (r l : Fin c) (h : r ≠ l) (a : k) :
    ((embA n (elem r l h a))⁻¹).val = fromBlocks 1 0 0 (transvection r l (-a)) := rfl

theorem embA_elem_mem (r l : Fin c) (h : r ≠ l) (hrl : r.val < l.val) (a : k) (p : ℕ) :
    embA n (elem r l h a) ∈ N k n c p := by
  apply Subgroup.subset_closure
  show InN p _
  intro r' s hrs
  rw [embA_elem_val]
  rcases r' with r' | r' <;> rcases s with s | s
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]
  · simp only [lev, Sum.elim_inr] at hrs
    simp only [fromBlocks_apply₂₂, transvection, Matrix.add_apply, single_apply, Matrix.one_apply, Sum.inr.injEq]
    have : ¬ (r = r' ∧ l = s) := by
      rintro ⟨rfl, rfl⟩
      omega
    rw [if_neg this, add_zero]

theorem simpleSum_elem (r l : Fin c) (h : r ≠ l) (a : k) :
    simpleSum (embA n (elem r l h a)) = if l.val = r.val + 1 then a else 0 := by
  rw [simpleSum, embA_elem_val]
  have key : ∀ i j : Fin c, (if j.val = i.val + 1 then
      (fromBlocks 1 0 0 (transvection r l a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr j) else 0) =
      if j = l then (if i = r then (if l.val = r.val + 1 then a else 0) else 0) else 0 := by
    intro i j
    simp only [fromBlocks_apply₂₂, transvection, Matrix.add_apply, single_apply]
    by_cases hij : j.val = i.val + 1
    · have hne : i ≠ j := fun h => by rw [h] at hij; omega
      rw [if_pos hij, one_apply_ne hne, zero_add]
      by_cases hi : i = r
      · subst hi
        by_cases hj : j = l
        · subst hj; simp [hij]
        · simp [hj, Ne.symm hj]
      · simp [hi, Ne.symm hi]
    · rw [if_neg hij]
      by_cases hi : i = r
      · subst hi
        by_cases hj : j = l
        · subst hj; simp [hij]
        · simp [hj]
      · simp [hi]
  simp only [key]
  simp

end Alg

theorem evalLaw_low : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), ρ < i.val → i.val ≤ l.val → ∀ E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.fixSet ρ ⊆ E → (GlobalTheory.PartRed.lowSet ρ).filter (fun e => GlobalTheory.PartRed.colIx e < i.val) ⊆ E → E ⊆ GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ → (Sum.inr l, Sum.inr i) ∉ E → GlobalTheory.PartRed.EvalLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) E (GlobalTheory.PartRed.transSet ρ) (Sum.inr l, Sum.inr i) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c ρ M _ _ L hc hL l i hi hil E hfix hlow hEsub hlE
  unfold GlobalTheory.PartRed.EvalLaw
  intro b Φ
  have hlc := l.isLt
  let r : Fin c := ⟨i.val - 1, by omega⟩
  have hr : r.val + 1 = i.val := by show i.val - 1 + 1 = i.val; omega
  have hrl' : r.val < l.val := by show i.val - 1 < l.val; omega
  have hrl : r ≠ l := fun h => by rw [h] at hrl'; exact lt_irrefl _ hrl'
  set β := basePt c (0 : Matrix n n' k) with hβ
  set T := GlobalTheory.PartRed.transSet (n := n) (n' := n') (c := c) ρ with hT
  set u := elem (k := k) r l hrl (-b) with hu
  have hgN : embA n u ∈ N k n c (ρ + 1) := embA_elem_mem r l hrl hrl' (-b) (ρ + 1)
  have hmem := _root_.GlobalTheory.AffineSB.mem_SB_comp_affine k (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) (embA n u)⁻¹ 0 Φ.1 Φ.2
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨_, hmem⟩
  have hΦ₁ : ∀ t, Φ₁.1 t = Φ.1 (((embA n u)⁻¹).val * t) := fun t => by simp [Φ₁]
  have hL1 := hL u hgN Φ Φ₁ hΦ₁
  have hinv : ((embA n u)⁻¹).val = fromBlocks 1 0 0 (transvection r l b) := by
    rw [hu, embA_elem_inv_val, neg_neg]
  have hβli : β (Sum.inr l) (Sum.inr i) = if l.val = i.val then 1 else 0 := by
    simp [hβ, basePt]
  have hss : simpleSum (embA n u) = -(b * β (Sum.inr l) (Sum.inr i)) := by
    rw [hu, simpleSum_elem, hβli]
    by_cases h : l.val = i.val
    · rw [if_pos (by omega), if_pos h]; ring
    · rw [if_neg (by omega), if_neg h]; ring
  have hxli : ∀ x y, GlobalTheory.PartRed.fillAt β E T x y (Sum.inr l) (Sum.inr i) = x (Sum.inr l) (Sum.inr i) := by
    intro x y
    have h1 : (Sum.inr l, Sum.inr i) ∉ T := by rw [hT, mem_trans]; simp [Free]; omega
    simp only [GlobalTheory.PartRed.fillAt, of_apply, dif_neg h1, if_neg hlE]
  refine ⟨(ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) • Φ₁, ?_, ?_⟩
  · rw [map_smul, hL1, smul_smul, hss, neg_neg, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
  · intro x
    dsimp only
    let s : (T → k) → (T → k) := fun y j =>
      if j.1.1 = Sum.inr r then b * GlobalTheory.PartRed.fillAt β E T x y (Sum.inr l) j.1.2 else 0
    have hfill : ∀ y, (fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *
        GlobalTheory.PartRed.fillAt β E T x y = GlobalTheory.PartRed.fillAt β E T x (y + s y) :=
      fun y => rowAdd_fill ρ l r i hi hil hr E hfix hlow b x y
    have hch : ∀ y, ch (GlobalTheory.PartRed.fillAt β E T x (y + s y)) =
        ch (GlobalTheory.PartRed.fillAt β E T x y) + b * x (Sum.inr l) (Sum.inr i) := fun y => by
      rw [← hfill, ch_rowAdd l r i hr b, hxli]
    have hone : (ψ (b * x (Sum.inr l) (Sum.inr i)) : ℂ) * ψ (-(b * x (Sum.inr l) (Sum.inr i))) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
    let G : (T → k) → ℂ := fun y => Φ.1 (GlobalTheory.PartRed.fillAt β E T x y) *
      (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ)
    have key : ∀ y, Φ₁.1 (GlobalTheory.PartRed.fillAt β E T x y) * (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ) =
        (ψ (b * x (Sum.inr l) (Sum.inr i)) : ℂ) * G (y + s y) := by
      intro y
      simp only [G]
      rw [hΦ₁, hinv, hfill, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      linear_combination (-(Φ.1 (GlobalTheory.PartRed.fillAt β E T x (y + s y)) *
        (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ))) * hone
    let S : Finset T := Finset.univ.filter fun j => j.1.1 = Sum.inr r
    have hs_cont : Continuous s := by
      refine continuous_pi fun j => ?_
      simp only [s]
      split_ifs
      · refine continuous_const.mul ?_
        simp only [GlobalTheory.PartRed.fillAt, of_apply]
        split_ifs <;> first | exact continuous_apply _ | exact continuous_const
      · exact continuous_const
    have hs_dep : ∀ y y' : T → k, (∀ j, j ∉ S → y j = y' j) → s y = s y' := by
      intro y y' h
      funext j
      simp only [s]
      split_ifs
      · congr 1
        simp only [GlobalTheory.PartRed.fillAt, of_apply]
        split_ifs <;> first | rfl | exact h _ (by simp [S]; exact Ne.symm hrl)
      · rfl
    have hs_supp : ∀ (y : T → k) j, j ∉ S → s y j = 0 := by
      intro y j hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [s, if_neg hj]
    have hchg := _root_.GlobalTheory.CoordShear.integral_shear k ν hν T S s hs_cont hs_dep hs_supp G
    simp only [GlobalTheory.PartRed.red, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, GlobalTheory.PartRed.chL_apply]
    calc ∫ y : T → k, (ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * Φ₁.1 (GlobalTheory.PartRed.fillAt β E T x y) *
          (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ) ∂(Measure.pi fun _ => ν)
        = ∫ y : T → k, ((ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * ψ (b * x (Sum.inr l) (Sum.inr i))) *
          G (y + s y) ∂(Measure.pi fun _ => ν) := by
          congr 1; funext y; rw [mul_assoc, key, mul_assoc]
      _ = ((ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * ψ (b * x (Sum.inr l) (Sum.inr i))) *
          ∫ y : T → k, G y ∂(Measure.pi fun _ => ν) := by rw [integral_const_mul, hchg]
      _ = _ := by
          rw [show b * (x (Sum.inr l) (Sum.inr i) - β (Sum.inr l) (Sum.inr i)) =
            -(b * β (Sum.inr l) (Sum.inr i)) + b * x (Sum.inr l) (Sum.inr i) by ring,
            AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.PartRed.LowLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionUpperFreeEntryTranslationLaw
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.PartRed.UpperLaw
open GlobalTheory.PartRed

section Alg
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def elem (l m : Fin c) (h : l ≠ m) (a : k) : GL (Fin c) k :=
  ⟨transvection l m a, transvection l m (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem embA_elem_apply (l m : Fin c) (h : l ≠ m) (a : k) (r s : n ⊕ Fin c) :
    (embA n (elem l m h a)).val r s
      = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s + if r = Sum.inr l ∧ s = Sum.inr m then a else 0 := by
  have : (embA n (elem l m h a)).val = fromBlocks 1 0 0 (transvection l m a) := rfl
  rw [this]
  rcases r with r | r <;> rcases s with s | s <;>
    simp [transvection, Matrix.one_apply, Matrix.single_apply, eq_comm]

theorem elem_inv (l m : Fin c) (h : l ≠ m) (a : k) : (elem l m h (-a))⁻¹ = elem l m h a := by
  ext1
  show transvection l m (- -a) = transvection l m a
  rw [neg_neg]

theorem embA_elem_mul {Q : Type} (l m : Fin c) (h : l ≠ m) (a : k) (t : Matrix (n ⊕ Fin c) Q k) (r : n ⊕ Fin c) (q : Q) :
    ((embA n (elem l m h a)).val * t) r q = t r q + if r = Sum.inr l then a * t (Sum.inr m) q else 0 := by
  simp only [Matrix.mul_apply, embA_elem_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [Matrix.one_apply]
  · by_cases hr : r = Sum.inr l
    · simp [hr]
    · simp [hr]

theorem simpleSum_elem (l m : Fin c) (h : l ≠ m) (a : k) :
    simpleSum (embA n (elem l m h a)) = if m.val = l.val + 1 then a else 0 := by
  unfold simpleSum
  have : ∀ i j : Fin c, (if j.val = i.val + 1 then (embA n (elem l m h a)).val (Sum.inr i) (Sum.inr j) else 0)
      = if i = l then (if j = m then (if m.val = l.val + 1 then a else 0) else 0) else 0 := by
    intro i j
    rw [embA_elem_apply]
    by_cases h1 : j.val = i.val + 1
    · have : i ≠ j := by intro e; subst e; omega
      by_cases h2 : i = l <;> by_cases h3 : j = m <;> simp_all [Matrix.one_apply]
    · by_cases h2 : i = l <;> by_cases h3 : j = m <;> simp_all
  simp [this]

theorem elem_mem_N (ρ : ℕ) (l m : Fin c) (h : l ≠ m) (hlm : l.val < m.val) (hm : m.val ≤ ρ) (a : k) :
    embA n (elem l m h a) ∈ N k n c (ρ + 1) := by
  apply Subgroup.subset_closure
  intro r s hrs
  rw [embA_elem_apply, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  simp only [lev, Sum.elim_inr] at hrs
  omega

variable {ρ : ℕ} {I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))}

theorem free_of_mem (hI : I ⊆ transSet ρ ∪ upSet ρ) {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} (he : e ∈ I) :
    Free (ρ + 1) e := by
  rcases Finset.mem_union.1 (hI he) with h | h
  · simp only [transSet, Finset.mem_filter] at h
    exact h.2.1
  · simp only [upSet, Finset.mem_filter] at h
    obtain ⟨-, l, i, rfl, h1, -⟩ := h
    exact h1

theorem fill_low (hI : I ⊆ transSet ρ ∪ upSet ρ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k)
    (m : Fin c) (j : Fin (c + 1)) (hj : j.val ≤ m.val) (hm : j.val ≤ ρ) :
    fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y (Sum.inr m) (Sum.inr j)
      = if m.val = j.val then 1 else 0 := by
  have hf : ¬ Free (ρ + 1) ((Sum.inr m, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) := by
    show ¬ (m.val < j.val)
    omega
  have h1 : (Sum.inr m, Sum.inr j) ∉ I := fun h => hf (free_of_mem hI h)
  have h2 : ((Sum.inr m, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) ∈ fixSet ρ ∪ lowSet ρ := by
    apply Finset.mem_union_left
    simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨j, rfl, hm, hf⟩
  simp only [fillAt, Matrix.of_apply, dif_neg h1, if_pos h2]
  simp [basePt]

def shear (ρ : ℕ) (I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (l m : Fin c) (a : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k) : I → k :=
  fun e => if e.1.1 = Sum.inr l then
    a * fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y (Sum.inr m) e.1.2 else 0

theorem elem_mul_fill (l m : Fin c) (i : Fin (c + 1)) (h : l ≠ m) (hmi : m.val = i.val) (hl : l.val < i.val)
    (hi : i.val ≤ ρ) (h1 : transSet ρ ⊆ I) (h2 : (upSet ρ).filter (fun e => i.val < colIx e) ⊆ I)
    (hI : I ⊆ transSet ρ ∪ upSet ρ) (hli : (Sum.inr l, Sum.inr i) ∉ I) (a : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k) :
    (embA n (elem l m h a)).val * fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y
      = fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I (x + Matrix.single (Sum.inr l) (Sum.inr i) a)
          (y + shear ρ I l m a x y) := by
  ext r q
  rw [embA_elem_mul]
  by_cases hr : (r, q) ∈ I
  · conv_rhs => rw [fillAt, Matrix.of_apply, dif_pos hr]
    conv_lhs => enter [1]; rw [fillAt, Matrix.of_apply, dif_pos hr]
    rfl
  · conv_rhs => rw [fillAt, Matrix.of_apply, dif_neg hr]
    conv_lhs => enter [1]; rw [fillAt, Matrix.of_apply, dif_neg hr]
    by_cases hrl : r = Sum.inr l
    · subst hrl
      rw [if_pos rfl]
      have hT : ∀ q : n' ⊕ Fin (c + 1), Free (ρ + 1) ((Sum.inr l, q) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) →
          (∀ j, q = Sum.inr j → ρ < j.val) → (Sum.inr l, q) ∈ I := by
        intro q hq hq'
        apply h1
        simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hq, hq'⟩
      rcases q with s | j
      · exact absurd (hT (Sum.inl s) (show l.val + 1 < ρ + 1 by omega) (by simp)) hr
      · have hj : j.val ≤ i.val := by
          by_contra hj
          apply hr
          by_cases hρ : ρ < j.val
          · refine hT _ (show l.val < j.val by omega) ?_
            intro j' e
            cases e
            exact hρ
          · apply h2
            simp only [upSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨l, j, rfl, by omega, by omega⟩, by simp only [colIx, Sum.elim_inr]; omega⟩
        rw [fill_low hI x y m j (by omega) (by omega)]
        by_cases hE : ((Sum.inr l, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) ∈ fixSet ρ ∪ lowSet ρ
        · rw [if_pos hE, if_pos hE]
          have : j.val ≤ l.val := by
            rcases Finset.mem_union.1 hE with h | h
            · simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
              rcases h with ⟨j', e, -, hf⟩ | ⟨_, _, -, -, e⟩
              · have : ¬ (l.val < j.val) := hf
                omega
              · cases e
            · simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
              obtain ⟨l', j', e, -, hf⟩ := h
              cases e
              exact hf
          rw [if_neg (by omega)]
          simp
        · rw [if_neg hE, if_neg hE, Matrix.add_apply]
          congr 1
          by_cases hij : i = j
          · subst hij
            simp [hmi]
          · have : ¬ m.val = j.val := fun e => hij (Fin.ext (by omega))
            simp [this, hij]
    · rw [if_neg hrl, add_zero, Matrix.add_apply, Matrix.single_apply_of_ne _ _ _ _ _ (fun e => hrl e.1.symm), add_zero]

theorem ch_elem_mul (l m : Fin c) (h : l ≠ m) (a : k) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((embA n (elem l m h a)).val * t) = ch t + a * t (Sum.inr m) (Sum.inr l.succ) := by
  simp [ch, embA_elem_mul, Finset.sum_add_distrib]

end Alg

theorem intLaw_up : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), l.val < i.val → i.val ≤ ρ → ∀ I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.transSet ρ ⊆ I → (GlobalTheory.PartRed.upSet ρ).filter (fun e => i.val < GlobalTheory.PartRed.colIx e) ⊆ I → I ⊆ GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ → (Sum.inr l, Sum.inr i) ∉ I → GlobalTheory.PartRed.IntLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) I (Sum.inr l, Sum.inr i) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c ρ M _ _ L hc hL l i hl hi I h1 h2 hI hli a Φ
  let m : Fin c := ⟨i.val, by omega⟩
  have hmi : m.val = i.val := rfl
  have h : l ≠ m := by intro e; rw [e] at hl; omega
  let d : k := if m.val = l.val + 1 then a else 0
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun x => Φ.1 ((embA n (elem l m h a)).val * x + 0), _root_.GlobalTheory.AffineSB.mem_SB_comp_affine k _ _ _ 0 Φ.1 Φ.2⟩
  have hΦ₁ : ∀ x, Φ₁.1 x = Φ.1 ((embA n (elem l m h a)).val * x) := fun x => by simp only [Φ₁, add_zero]
  have hL₁ : L Φ₁ = (ψ d : ℂ) • L Φ := by
    have := hL (elem l m h (-a)) (elem_mem_N ρ l m h (by omega) (by omega) _) Φ Φ₁ (fun t => by
      rw [hΦ₁, ← map_inv, elem_inv])
    rw [this, simpleSum_elem]
    congr 3
    simp only [d]
    split_ifs <;> simp
  refine ⟨(ψ (-d) : ℂ) • Φ₁, ?_, fun x => ?_⟩
  · rw [map_smul, hL₁, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    simp
  · unfold red
    rw [← _root_.GlobalTheory.CoordShear.integral_shear k ν hν I (Finset.univ.filter fun e : I => e.1.1 = Sum.inr l) (shear ρ I l m a x) ?_ ?_ ?_
      (fun y => Φ.1 (fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I
        (x + Matrix.single (Sum.inr l) (Sum.inr i) a) y) *
        (ψ (-chL (fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I
          (x + Matrix.single (Sum.inr l) (Sum.inr i) a) y)) : ℂ))]
    · congr 1
      funext y
      rw [← elem_mul_fill l m i h hmi hl hi h1 h2 hI hli a x y, chL_apply, chL_apply, ch_elem_mul,
        fill_low hI x y m l.succ (by rw [Fin.val_succ]; omega) (by rw [Fin.val_succ]; omega)]
      have hd : (a * if m.val = l.succ.val then 1 else 0) = d := by
        simp only [d, Fin.val_succ]
        split_ifs <;> simp
      rw [hd, Submodule.coe_smul, Pi.smul_apply, hΦ₁, smul_eq_mul, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    · refine continuous_pi fun e => ?_
      unfold shear
      split_ifs
      · refine continuous_const.mul ?_
        simp only [fillAt, Matrix.of_apply]
        split_ifs
        · exact continuous_apply _
        · exact continuous_const
        · exact continuous_const
      · exact continuous_const
    · intro y y' hy
      funext e
      unfold shear
      split_ifs
      · congr 1
        simp only [fillAt, Matrix.of_apply]
        split_ifs with he
        · apply hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro e
          exact h (Sum.inr_injective e).symm
        · rfl
        · rfl
      · rfl
    · intro y j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [shear, if_neg hj]

end GlobalTheory.PartRed.UpperLaw
end
end

