module

public import Mathlib
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import ReciprocityTheory.DualLattices.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0006
public import Formalism.DropLevelBounds.Statement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DeterminantPairingQuotientValuationLowerBound
section
open ReciprocityTheory.PGsh

namespace GlobalTheory.DetPairingBound

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps

theorem cayDet_isHomogeneous (n : ℕ) (C : Type) [CommRing C] :
    (cayDet n C).IsHomogeneous n := by
  show (Matrix.mvPolynomialX (Fin n) (Fin n) C).det.IsHomogeneous n
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [← map_intCast (MvPolynomial.C : C →+* MvPolynomial (Fin n × Fin n) C)]
  refine IsHomogeneous.C_mul ?_ _
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => Matrix.mvPolynomialX (Fin n) (Fin n) C (σ i) i) (fun _ => 1)
    (fun i _ => by simpa [Matrix.mvPolynomialX_apply] using isHomogeneous_X (R := C) ((σ i, i) : Fin n × Fin n))
  simpa using h

theorem coeff_cayDet_pow_nonneg (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (n x : ℕ) (A : Fin n × Fin n →₀ ℕ) : 0 ≤ v (AddMonoidAlgebra.coeff (cayDet n C ^ x) A) := by
  rw [← cayDet_map (R := C), ← map_pow, coeff_map, eq_intCast]
  exact intCast_nonneg v _

theorem sum_eq_of_mem_support (C : Type) [CommRing C] (n x : ℕ) (A : Fin n × Fin n →₀ ℕ)
    (hA : A ∈ (cayDet n C ^ x).support) : ∑ j, A j = n * x := by
  have h := (cayDet_isHomogeneous n C).pow x
  rw [← Finsupp.degree_eq_sum]
  by_contra hne
  exact (mem_support_iff.mp hA) (h.coeff_eq_zero hne)

theorem le_val_div {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {N D : C} {a d r : ℝ}
    (hN : (a : WithTop ℝ) ≤ v N) (hD : v D = d) (h : r ≤ a - d) : (r : WithTop ℝ) ≤ v (N / D) := by
  have hD0 : D ≠ 0 := by
    rintro rfl
    simp at hD
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  · obtain ⟨b, hb⟩ := exists_real v hN0
    rw [div_eq_coe v hD0 hb hD]
    rw [hb, WithTop.coe_le_coe] at hN
    exact WithTop.coe_le_coe.mpr (by linarith)

theorem main : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (i n₀ s : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), 1 ≤ s → 1 ≤ n₀ →
    (∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (AddMonoidAlgebra.coeff Q A)) →
    (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (3 * Real.logb l n₀ + 2 * Real.logb l s + i + 3) : ℝ) : WithTop ℝ) ≤
      v ((∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) / (∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A))) := by
  intro C _ _ v l hl hvl i n₀ s Q hs hn₀ hQ
  have hvnat : ∀ m : ℕ, m ≠ 0 → v (m : C) = ((padicValNat l m : ℝ) : WithTop ℝ) := by
    intro m hm
    rw [natCast_eq_factorization v hl hvl hm, Nat.factorization_def m hl, ← Nat.padicValNat_def]
  obtain ⟨-, hL2, hL3⟩ := GlobalTheory.LegendreBounds.legendre_bounds l hl
  have hk0 : l ^ i * s ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hl.ne_zero) (by omega)

  have hP := GlobalTheory.DetPowPairing.main C n₀ (l ^ i * s)
  rw [← Nat.cast_prod, ← Nat.cast_prod] at hP
  have hF0 : (∏ c ∈ Finset.range n₀, c.factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero c
  have hF1 : (∏ c ∈ Finset.range n₀, (l ^ i * s + c).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero _
  have hF0' : ((∏ c ∈ Finset.range n₀, c.factorial : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr hF0
  have hDen := (eq_div_iff hF0').mpr ((mul_comm _ _).trans hP)
  have hvD := div_eq_coe v hF0' (hvnat _ hF1) (hvnat _ hF0)
  rw [← hDen] at hvD

  obtain ⟨wb, hwb⟩ : ∃ wb : ℝ, wb = (n₀ : ℝ) * ((l : ℝ) ^ i * s) / ((l : ℝ) - 1) -
      (n₀ : ℝ) ^ 2 * (Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) + 1) := ⟨_, rfl⟩
  obtain ⟨qb, hqb⟩ : ∃ qb : ℝ, qb = (s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) :=
    ⟨_, rfl⟩
  have hnum : ∀ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, ((wb + qb : ℝ) : WithTop ℝ) ≤
      v (AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) *
        AddMonoidAlgebra.coeff Q A) := by
    intro A hA
    have hsum := sum_eq_of_mem_support C n₀ (l ^ i * s) A hA
    have hW := hL2 (Fin n₀ × Fin n₀) A
      (by rw [hsum]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hk0))
    rw [hsum] at hW
    simp only [Fintype.card_prod, Fintype.card_fin] at hW
    push_cast at hW
    have hwt : (A.prod fun _ e => (e.factorial : C)) = ((∏ j, (A j).factorial : ℕ) : C) := by
      rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Nat.cast_prod]
    have hne : (∏ j, (A j).factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _
    have h2 : (wb : WithTop ℝ) ≤ ((padicValNat l (∏ j, (A j).factorial) : ℝ) : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr (by rw [hwb, sq]; linarith)
    have h3 : (qb : WithTop ℝ) ≤ v (AddMonoidAlgebra.coeff Q A) := by
      rw [hqb]; exact hQ A
    rw [AddValuation.map_mul, AddValuation.map_mul, hwt, hvnat _ hne]
    calc ((wb + qb : ℝ) : WithTop ℝ) = 0 + (wb : WithTop ℝ) + (qb : WithTop ℝ) := by
          rw [zero_add, WithTop.coe_add]
      _ ≤ _ := add_le_add (add_le_add (coeff_cayDet_pow_nonneg C v n₀ _ A) h2) h3
  refine le_val_div v (a := wb + qb) (AddValuation.map_le_sum v hnum) hvD ?_

  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hn1 : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hn0 : (n₀ : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n₀).ne'
  have hs0 : (s : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < s).ne'
  have hli : (l : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by linarith : (0 : ℝ) < l).ne'
  have hLn := Real.logb_nonneg hl1 hn1
  have hLs := Real.logb_nonneg hl1 hs1
  have hlK : Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) =
      Real.logb l n₀ + i + Real.logb l s := by
    rw [Real.logb_mul hn0 (mul_ne_zero hli hs0), Real.logb_mul hli hs0, Real.logb_pow,
      Real.logb_self_eq_one hl1]
    ring
  have hlQ : Real.logb l ((n₀ : ℝ) * s) = Real.logb l n₀ + Real.logb l s :=
    Real.logb_mul hn0 hs0
  have h3 := hL3 n₀ (l ^ i * s)
  push_cast at h3
  have hsq : (n₀ : ℝ) * (Real.logb l n₀ + 1) ≤ (n₀ : ℝ) ^ 2 * (Real.logb l n₀ + 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  rw [hwb, hqb, hlK, hlQ]
  linarith

end GlobalTheory.DetPairingBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic
section
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.BasicFlow

lemma pivot {ι κ : Type} [DecidableEq ι] [Fintype κ] (s : Finset ι)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (φ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ v : ι → ℝ, (∀ i, i ∉ s → v i = 0) → (∀ i, 0 ≤ v i) → T v = 0 → v = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, i ∉ s → x i = 0)
    (hc : Fintype.card κ < (s.filter fun i => x i ≠ 0).card) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ T y = T x ∧ φ x ≤ φ y ∧ (∀ i, x i = 0 → y i = 0) ∧
      (s.filter fun i => y i ≠ 0).card < (s.filter fun i => x i ≠ 0).card := by
  set t := s.filter fun i => x i ≠ 0 with ht
  let E : (t → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun v i => if h : i ∈ t then v ⟨i, h⟩ else 0
      map_add' := fun v w => by ext i; by_cases h : i ∈ t <;> simp [h]
      map_smul' := fun c v => by ext i; by_cases h : i ∈ t <;> simp [h] }
  have hker : LinearMap.ker (T ∘ₗ E) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa using hc
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hw' : T (E w) = 0 := hw
  have hE0 : E w ≠ 0 := by
    intro h
    apply hw0
    ext ⟨i, hi⟩
    have := congrFun h i
    simpa [E, hi] using this
  have hEt : ∀ i, i ∉ t → E w i = 0 := fun i hi => by simp [E, hi]
  obtain ⟨v, hv0, hvt, hvT, hvφ⟩ :
      ∃ v : ι → ℝ, v ≠ 0 ∧ (∀ i, i ∉ t → v i = 0) ∧ T v = 0 ∧ 0 ≤ φ v := by
    rcases le_total 0 (φ (E w)) with h | h
    · exact ⟨E w, hE0, hEt, hw', h⟩
    · refine ⟨-E w, neg_ne_zero.2 hE0, fun i hi => by simp [hEt i hi], by simp [hw'], ?_⟩
      simpa using h
  have hneg : (t.filter fun i => v i < 0).Nonempty := by
    by_contra hn
    apply hv0
    refine hT v (fun i hi => hvt i fun h => hi (Finset.mem_filter.1 h).1) (fun i => ?_) hvT
    by_cases hi : i ∈ t
    · by_contra hlt
      exact hn ⟨i, Finset.mem_filter.2 ⟨hi, not_le.1 hlt⟩⟩
    · exact (hvt i hi).ge
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image _ (fun i => x i / (-v i)) hneg
  obtain ⟨hjt, hjv⟩ := Finset.mem_filter.1 hj
  have hc0 : 0 ≤ x j / (-v j) := div_nonneg (hx j) (by linarith)
  have hzero : ∀ i, x i = 0 → (x + (x j / (-v j)) • v) i = 0 := by
    intro i hi
    have : v i = 0 := hvt i fun h => (Finset.mem_filter.1 h).2 hi
    simp [hi, this]
  refine ⟨x + (x j / (-v j)) • v, fun i => ?_, by simp [hvT], ?_, hzero, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : v i < 0
    · have hit : i ∈ t := by
        by_contra h
        exact hi.ne (hvt i h)
      have := hmin i (Finset.mem_filter.2 ⟨hit, hi⟩)
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · have := mul_nonneg hc0 (not_lt.1 hi)
      linarith [hx i]
  · rw [map_add (f := _), map_smul, smul_eq_mul]
    have := mul_nonneg hc0 hvφ
    linarith
  · apply Finset.card_lt_card
    refine ⟨fun i hi => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨h1, fun h => h2 (hzero i h)⟩
    · apply (Finset.mem_filter.1 (h hjt)).2
      have : v j ≠ 0 := hjv.ne
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring

lemma basic {ι κ : Type} [DecidableEq ι] [Fintype κ] (s : Finset ι)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (φ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ v : ι → ℝ, (∀ i, i ∉ s → v i = 0) → (∀ i, 0 ≤ v i) → T v = 0 → v = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, i ∉ s → x i = 0) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ T y = T x ∧ φ x ≤ φ y ∧ (∀ i, x i = 0 → y i = 0) ∧
      (s.filter fun i => y i ≠ 0).card ≤ Fintype.card κ := by
  induction' h : (s.filter fun i => x i ≠ 0).card using Nat.strong_induction_on
    with n ih generalizing x
  by_cases hc : (s.filter fun i => x i ≠ 0).card ≤ Fintype.card κ
  · exact ⟨x, hx, rfl, le_rfl, fun _ h => h, hc⟩
  · obtain ⟨y, h1, h2, h3, h4, h5⟩ := pivot s T φ hT x hx hs (not_le.1 hc)
    obtain ⟨z, g1, g2, g3, g4, g5⟩ :=
      ih _ (h ▸ h5) y h1 (fun i hi => h4 i (hs i hi)) rfl
    exact ⟨z, g1, g2.trans h2, h3.trans g3, fun i hi => g4 i (h4 i hi), g5⟩

lemma entry_le (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d W x) (a : ZMod d) (i : ℕ) (hi : i ∈ oddLevels d) : x a i ≤ W a := by
  obtain ⟨h0, h2⟩ := hx
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have e1 : (l : ℝ) ^ i * x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i :=
    Finset.single_le_sum (f := fun i => (l : ℝ) ^ i * x a i)
      (fun j _ => mul_nonneg (by positivity) (h0 a j)) hi
  have e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
  have e3 : x a i ≤ (l : ℝ) ^ i * x a i := le_mul_of_one_le_left (h0 a i) (one_le_pow₀ hl1)
  have := h2 a
  linarith

lemma low_optimum (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (hW : 0 ≤ W) (i0 : ℕ) :
    ∃ x : ZMod d → ℕ → ℝ, (IsFlow l d W x ∧ ∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x a i = 0) ∧
      ∀ x' : ZMod d → ℕ → ℝ, IsFlow l d W x' →
        (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x' a i = 0) → flowVal d x' ≤ flowVal d x := by
  let S : Set (ZMod d → ℕ → ℝ) :=
    {x | IsFlow l d W x ∧ ∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x a i = 0}
  have hclosed : IsClosed S := by
    simp only [S, IsFlow, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun a => isClosed_iInter fun i =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun a => isClosed_le (by fun_prop) continuous_const
    · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_eq (by fun_prop) continuous_const
  have hK : IsCompact (Set.pi Set.univ fun a : ZMod d =>
      Set.pi Set.univ fun _ : ℕ => Set.Icc (0 : ℝ) (W a)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_Icc
  have hS : IsCompact S := by
    refine hK.of_isClosed_subset hclosed ?_
    rintro x ⟨h0, h1⟩ a - i -
    refine ⟨h0.1 a i, ?_⟩
    by_cases h : i ∈ oddLevels d
    · exact entry_le l d hl W x h0 a i h
    · rw [h1 a i (Or.inr h)]; exact hW a
  have hne : S.Nonempty := ⟨fun _ _ => 0, ⟨fun _ _ => le_rfl, fun a => by simpa using hW a⟩,
    fun _ _ _ => rfl⟩
  obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne
    (f := fun x => flowVal d x) (Continuous.continuousOn (by unfold flowVal; fun_prop))
  exact ⟨x, hx, fun x' h1 h2 => hmax (a := x') ⟨h1, h2⟩⟩

lemma truncate (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (i0 : ℕ)
    (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d W x) :
    ∃ x' : ZMod d → ℕ → ℝ, IsFlow l d W x' ∧
      (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x' a i = 0) ∧
      flowVal d x ≤ flowVal d x' + (∑ a, W a) / (l : ℝ) ^ i0 := by
  obtain ⟨h0, h2⟩ := hx
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  let y : ZMod d → ℕ → ℝ := fun a i => if i0 ≤ i ∨ i ∉ oddLevels d then 0 else x a i
  have hy : ∀ a i, y a i ≤ x a i := fun a i => by
    simp only [y]; split_ifs
    · exact h0 a i
    · exact le_rfl
  refine ⟨y, ⟨fun a i => ?_, fun a => le_trans (add_le_add ?_ ?_) (h2 a)⟩,
    fun a i h => if_pos h, ?_⟩
  · simp only [y]; split_ifs
    · exact le_rfl
    · exact h0 a i
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy a i) (by positivity)
  · exact Finset.sum_le_sum fun i _ => hy _ i
  · have hp : (0 : ℝ) < (l : ℝ) ^ i0 := by positivity
    rw [← sub_le_iff_le_add', le_div_iff₀ hp]
    unfold flowVal
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    have e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
    have e3 : (∑ i ∈ oddLevels d, x a i - ∑ i ∈ oddLevels d, y a i) * (l : ℝ) ^ i0
        ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases h : i0 ≤ i
      · have : y a i = 0 := if_pos (Or.inl h)
        rw [this, sub_zero, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 h) (h0 a i)
      · have : y a i = x a i := if_neg (by simp [h, hi])
        rw [this, sub_self, zero_mul]
        exact mul_nonneg (by positivity) (h0 a i)
    have := h2 a
    linarith

theorem dropLevelsBasic : DropLevelsBasic := by
  intro l d _ hl W hW i0
  obtain ⟨x, ⟨hx, hx0⟩, hmax⟩ := low_optimum l d hl W hW i0
  have hm : maxFlow l d W ≤ flowVal d x + (∑ a, W a) / (l : ℝ) ^ i0 := by
    refine csSup_le ⟨_, x, hx, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2, h3⟩ := truncate l d hl W i0 z hz
    linarith [hmax z' h1 h2]
  let T : (ZMod d × ℕ → ℝ) →ₗ[ℝ] (ZMod d → ℝ) :=
    { toFun := fun v s => (∑ i ∈ oddLevels d, (l : ℝ) ^ i * v (s, i)) +
        (∑ i ∈ oddLevels d, v (s - (i : ZMod d), i))
      map_add' := fun v w => by
        ext s; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c v => by
        ext s
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum,
          mul_left_comm c] }
  let φ : (ZMod d × ℕ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ s : ZMod d, ∑ i ∈ oddLevels d, v (s, i)
      map_add' := fun v w => by simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }
  obtain ⟨y, h1, h2, h3, h4, h5⟩ := basic ((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d) T φ
    (fun v hv hv0 hT => by
      ext ⟨a, i⟩
      by_cases hi : i ∈ oddLevels d
      · refine le_antisymm ?_ (hv0 _)
        exact entry_le l d hl 0 (fun a i => v (a, i))
          ⟨fun a i => hv0 _, fun s => (congrFun hT s).le⟩ a i hi
      · exact hv _ (by simp [hi]))
    (fun p => x p.1 p.2) (fun p => hx.1 _ _)
    (fun p hp => hx0 _ _ (Or.inr (by simpa using hp)))
  refine ⟨fun a i => y (a, i), ⟨fun a i => h1 _, fun s => ?_⟩,
    fun a i h => h4 (a, i) (hx0 a i h), ?_, ?_⟩
  · exact (congrFun h2 s).le.trans (hx.2 s)
  · simpa [ZMod.card] using h5
  · have : flowVal d x ≤ flowVal d (fun a i => y (a, i)) := h3
    linarith

end GlobalTheory.BasicFlow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfForallPairPointsValuationIntegers
section
namespace GlobalTheory.ChF

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section

variable {O : Type} [CommRing O] {d : ℕ}

private theorem exists_algHom_ev (j : Fin 2) : ∃ E : PS O 1 d →ₐ[O] PS O 2 d,
    (∀ u, E u = ev (n := 2) ![pt O d j] u) ∧ ∀ q, E (X q) = X (j, q.2) := by
  have h : HasSubst (fun q : Fin 1 × Fin d => (![pt O d j] : Fin 1 → Pt O 2 d) q.1 q.2) :=
    hasSubst_of_constantCoeff_zero fun q => by simp [pt, Matrix.cons_val_fin_one]
  refine ⟨substAlgHom h, fun u => by rw [coe_substAlgHom]; rfl, fun q => ?_⟩
  rw [coe_substAlgHom, subst_X h]
  simp [pt, Matrix.cons_val_fin_one]

private theorem exists_ringHom_eval {A B σ : Type} [CommRing A] [CommRing B] [Finite σ]
    (J : Ideal B) (hJ : IsAdicComplete J B) (E : A →+* B) (b : σ → B)
    (hb : ∀ q, ∃ M : ℕ, b q ^ M ∈ J) :
    ∃ T : MvPowerSeries σ A →+* B, (∀ u, T (C u) = E u) ∧ ∀ q, T (X q) = b q := by
  letI : Algebra A B := E.toAlgebra
  obtain ⟨T, hT⟩ := (mvPowerSeries_eval_of_pow_mem B J σ b hb).1 hJ A
  exact ⟨T.toRingHom, fun u => T.commutes u, hT⟩

private theorem exists_curry :
    ∃ S : PS O 2 d →ₐ[O] MvPowerSeries (Fin 1 × Fin d) (PS O 1 d), Function.Injective S ∧
      (∀ u, S (ev (n := 2) ![pt O d 0] u) = MvPowerSeries.map (C : O →+* PS O 1 d) u) ∧
      ∀ u, S (ev (n := 2) ![pt O d 1] u) = C u := by
  obtain ⟨E₀, hE₀, hX₀⟩ := exists_algHom_ev (O := O) (d := d) 0
  obtain ⟨E₁, hE₁, hX₁⟩ := exists_algHom_ev (O := O) (d := d) 1
  have hA := (mem_sup_span_X_pow_iff_and_isAdicComplete O ⊥ (Fin 1 × Fin d)).2 inferInstance
  have hP := (mem_sup_span_X_pow_iff_and_isAdicComplete O ⊥ (Fin 2 × Fin d)).2 inferInstance
  have hB := (mem_sup_span_X_pow_iff_and_isAdicComplete (PS O 1 d) _ (Fin 1 × Fin d)).2 hA
  set I : Ideal (PS O 1 d) := (⊥ : Ideal O).map (C : O →+* PS O 1 d) ⊔
    Ideal.span (Set.range (X : Fin 1 × Fin d → PS O 1 d)) with hI
  set J : Ideal (PS O 2 d) := (⊥ : Ideal O).map (C : O →+* PS O 2 d) ⊔
    Ideal.span (Set.range (X : Fin 2 × Fin d → PS O 2 d)) with hJ
  set K : Ideal (MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) := I.map C ⊔
    Ideal.span (Set.range X) with hK
  have hXK : ∀ q : Fin 1 × Fin d, ∃ M : ℕ,
      (X q : MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) ^ M ∈ K := fun q =>
    ⟨1, by rw [pow_one]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)⟩
  have hCK : ∀ q : Fin 1 × Fin d, ∃ M : ℕ,
      (C (X q) : MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) ^ M ∈ K := fun q =>
    ⟨1, by
      rw [pow_one]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _
        (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)))⟩
  have hXJ : ∀ q : Fin 2 × Fin d, ∃ M : ℕ, (X q : PS O 2 d) ^ M ∈ J := fun q =>
    ⟨1, by rw [pow_one]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)⟩
  obtain ⟨S, hS⟩ := (mvPowerSeries_eval_of_pow_mem _ K (Fin 2 × Fin d)
    (fun q => if q.1 = 0 then X (0, q.2) else C (X (0, q.2))) fun q => by
      split_ifs
      exacts [hXK _, hCK _]).1 hB O
  have hq : ∀ q : Fin 1 × Fin d, ((0 : Fin 1), q.2) = q := fun q =>
    Prod.ext (Subsingleton.elim _ _) rfl
  have hc : ∀ t : O, algebraMap O (MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) t = C (C t) :=
    fun t => MvPowerSeries.algebraMap_apply
  have h0 : S.toRingHom.comp E₀.toRingHom = MvPowerSeries.map (C : O →+* PS O 1 d) := by
    refine (mvPowerSeries_eval_of_pow_mem _ K (Fin 1 × Fin d) X hXK).2 inferInstance O _ _
      (fun t => ?_) (fun q => ?_) (fun q => map_X _ q)
    · rw [map_C]
      exact ((S.comp E₀).commutes t).trans (hc t)
    · change S (E₀ (X q)) = _
      rw [hX₀, hS, if_pos rfl, hq]
  have h1 : S.toRingHom.comp E₁.toRingHom = C := by
    refine (mvPowerSeries_eval_of_pow_mem _ K (Fin 1 × Fin d) (fun q => C (X q)) hCK).2
      inferInstance O _ _ (fun t => ?_) (fun q => ?_) (fun q => rfl)
    · exact ((S.comp E₁).commutes t).trans (hc t)
    · change S (E₁ (X q)) = _
      rw [hX₁, hS, if_neg (by simp), hq]
  refine ⟨S, ?_, fun u => ?_, fun u => ?_⟩
  · obtain ⟨T, hTC, hTX⟩ : ∃ T : MvPowerSeries (Fin 1 × Fin d) (PS O 1 d) →+* PS O 2 d,
        (∀ u, T (C u) = E₁ u) ∧ ∀ q, T (X q) = X (0, q.2) :=
      exists_ringHom_eval J hP E₁.toRingHom _ fun q => hXJ _
    have hTS : T.comp S.toRingHom = RingHom.id _ := by
      refine (mvPowerSeries_eval_of_pow_mem _ J (Fin 2 × Fin d) X hXJ).2 inferInstance O _ _
        (fun t => ?_) (fun q => ?_) (fun q => rfl)
      · change T (S (algebraMap O _ t)) = _
        rw [S.commutes, hc]
        exact (hTC (C t)).trans (E₁.commutes t)
      · change T (S (X q)) = _
        obtain ⟨j, i⟩ := q
        rw [hS]
        fin_cases j
        · simp [hTX]
        · simp [hTC, hX₁]
    exact Function.LeftInverse.injective (g := T) fun f => DFunLike.congr_fun hTS f
  · rw [← hE₀]
    exact DFunLike.congr_fun h0 u
  · rw [← hE₁]
    exact DFunLike.congr_fun h1 u

theorem eq_zero_of_forall_pair_points (W : (PS O 1 d →ₐ[O] O) → Prop)
    (hW : ∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) (f : PS O 2 d)
    (hf : ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O),
      (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) →
        W φ → W φ' → Φ f = 0) : f = 0 := by
  obtain ⟨S, hS, h0, h1⟩ := exists_curry (O := O) (d := d)
  refine hS ?_
  rw [map_zero]
  ext1 e
  rw [map_zero]
  refine hW _ fun φ' hφ' => ?_
  have hC : φ'.toRingHom.comp (C : O →+* PS O 1 d) = RingHom.id O :=
    RingHom.ext fun t => φ'.commutes t
  have key : MvPowerSeries.map φ'.toRingHom (S f) = 0 := by
    refine hW _ fun φ hφ => ?_
    refine hf (φ.comp ((MvPowerSeries.mapAlgHom φ').comp S)) φ φ' (fun u => ?_) (fun u => ?_)
      hφ hφ'
    · change φ (MvPowerSeries.map φ'.toRingHom (S _)) = _
      rw [h0, ← RingHom.comp_apply, ← MvPowerSeries.map_comp, hC, MvPowerSeries.map_id]
      rfl
    · change φ (MvPowerSeries.map φ'.toRingHom (S _)) = _
      rw [h1, map_C]
      exact φ.commutes _
  have := congrArg (coeff e) key
  rwa [coeff_map, map_zero] at this

end

theorem eq_zero_of_forall_pair_points_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (W : (PS O 1 d →ₐ[O] O) → Prop), (∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) → ∀ f : PS O 2 d, (∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → W φ → W φ' → Φ f = 0) → f = 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ W hW f hf => eq_zero_of_forall_pair_points W hW f hf

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FactorialWeightedPairingDetPowProportionalStatement
section
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorialWeightedPairing_detPow_proportional : (∀ (C : Type) [Field C] [CharZero C] (n₀ M Y : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), M ≤ Y → Q.IsHomogeneous (n₀ * M) →
    (∑ A ∈ (cayDet n₀ C ^ Y).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ Y) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ (Y - M) * Q) A) * (∑ A ∈ (cayDet n₀ C ^ M).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ M) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ M) A) = (∑ A ∈ (cayDet n₀ C ^ M).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ M) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) * (∑ A ∈ (cayDet n₀ C ^ Y).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ Y) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ Y) A)) := by
  first | exact @GlobalTheory.DetPowPairing.pairing_pow_proportional | exact GlobalTheory.DetPowPairing.pairing_pow_proportional | (intros; apply GlobalTheory.DetPowPairing.pairing_pow_proportional <;> assumption)
end

