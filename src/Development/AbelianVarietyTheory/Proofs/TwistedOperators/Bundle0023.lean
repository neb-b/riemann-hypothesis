module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd
section
open Module GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula

namespace GlobalTheory.GaussCount

open Module in
private lemma cast_prod_pow_sub_pow_eq_prod_pow_mul_prod (q m a : ℕ) (hq : 0 < q) (h : a ≤ m) :
    ((∏ i ∈ Finset.range a, (q ^ m - q ^ i) : ℕ) : ℤ) =
      (∏ i ∈ Finset.range a, (q : ℤ) ^ i) * ∏ i ∈ Finset.range a, ((q : ℤ) ^ (m - i) - 1) := by
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq hi')]
  have e : (q : ℤ) ^ m = (q : ℤ) ^ i * (q : ℤ) ^ (m - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  push_cast
  rw [e]
  ring

open Module in
private lemma gaussBinom_self (q n : ℕ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n n = 1 := by
  induction n with
  | zero => exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right q 0
  | succ n ih =>
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero q n (n + 1) (by omega),
      Nat.sub_self, pow_zero, ih]
    rfl

open Module in
private lemma gaussBinom_mul_prod_pow_succ_sub_one (q n a : ℕ) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a : ℤ) * ∏ i ∈ Finset.range a, ((q : ℤ) ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range a, ((q : ℤ) ^ (n - i) - 1) := by
  induction n generalizing a with
  | zero =>
    rcases a with _ | a
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right]
    · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_succ, Finset.prod_range_succ']
      simp
  | succ n ih =>
    rcases a with _ | a
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right]
    · have h1 := ih (a + 1)
      have h2 := ih a
      rw [Finset.prod_range_succ, Finset.prod_range_succ] at h1
      have hB : (∏ i ∈ Finset.range a, ((q : ℤ) ^ (n - i) - 1)) *
          ((q : ℤ) ^ (n - a) * (q : ℤ) ^ (a + 1) - (q : ℤ) ^ (n + 1)) = 0 := by
        by_cases han : a ≤ n
        · rw [← pow_add, show n - a + (a + 1) = n + 1 by omega]
          ring
        · rw [Finset.prod_eq_zero (i := n) (Finset.mem_range.mpr (by omega)) (by simp)]
          ring
      rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, Finset.prod_range_succ, Finset.prod_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      push_cast
      linear_combination h1 + (q : ℤ) ^ (n - a) * ((q : ℤ) ^ (a + 1) - 1) * h2 + hB

open Module in
private lemma prod_pow_succ_sub_one_eq_prod_pow_sub (q n : ℕ) :
    ∏ i ∈ Finset.range n, ((q : ℤ) ^ (i + 1) - 1) = ∏ i ∈ Finset.range n, ((q : ℤ) ^ (n - i) - 1) := by
  simpa [gaussBinom_self] using gaussBinom_mul_prod_pow_succ_sub_one q n n

open Module in
private lemma prod_pow_succ_sub_one_ne_zero {q : ℕ} (hq : 1 < q) (n : ℕ) :
    ∏ i ∈ Finset.range n, ((q : ℤ) ^ (i + 1) - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have : (1 : ℤ) < (q : ℤ) ^ (i + 1) := one_lt_pow₀ (by exact_mod_cast hq) (by omega)
  linarith

open Module in
private lemma card_submodule_finrank_eq_gaussBinom (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (j : ℕ) :
    Nat.card {L : Submodule k V // finrank k L = j} =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Nat.card k) (finrank k V) j := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  by_cases hj : j ≤ finrank k V
  · have h := _root_.GlobalTheory.SubspaceNumber.card_subspaces_mul k V j hj
    have hZ := congrArg (fun x : ℕ => (x : ℤ)) h
    simp only [Nat.cast_mul] at hZ
    rw [cast_prod_pow_sub_pow_eq_prod_pow_mul_prod (Nat.card k) j j (by omega) le_rfl,
      cast_prod_pow_sub_pow_eq_prod_pow_mul_prod (Nat.card k) _ j (by omega) hj,
      ← prod_pow_succ_sub_one_eq_prod_pow_sub (Nat.card k) j,
      ← gaussBinom_mul_prod_pow_succ_sub_one (Nat.card k) (finrank k V) j] at hZ
    have hQ : ∏ i ∈ Finset.range j, ((Nat.card k : ℕ) : ℤ) ^ i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ =>
        pow_ne_zero _ (by exact_mod_cast (show Nat.card k ≠ 0 by omega))
    have hF := prod_pow_succ_sub_one_ne_zero hq j
    have key : (Nat.card {L : Submodule k V // finrank k L = j} : ℤ) =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Nat.card k) (finrank k V) j := by
      apply mul_right_cancel₀ (mul_ne_zero hQ hF)
      linear_combination hZ
    exact_mod_cast key
  · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero _ _ _ (by omega)]
    haveI : IsEmpty {L : Submodule k V // finrank k L = j} :=
      ⟨fun ⟨L, hL⟩ => by have := Submodule.finrank_le L; omega⟩
    exact Nat.card_of_isEmpty


open Module in
theorem _root_.GlobalTheory.GaussCount.subspaceCount : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.SubspaceCount := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.SubspaceCount
  intro k _ _ V _ _ _ j
  exact card_submodule_finrank_eq_gaussBinom k V j

open Module in
private lemma gaussBinom_mul_prod_mul_prod_sub_eq_prod (q n a : ℕ) (h : a ≤ n) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a : ℤ) * (∏ i ∈ Finset.range a, ((q : ℤ) ^ (i + 1) - 1)) *
        (∏ i ∈ Finset.range (n - a), ((q : ℤ) ^ (i + 1) - 1)) =
      ∏ i ∈ Finset.range n, ((q : ℤ) ^ (i + 1) - 1) := by
  rw [mul_assoc, ← mul_assoc (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a : ℤ), gaussBinom_mul_prod_pow_succ_sub_one, prod_pow_succ_sub_one_eq_prod_pow_sub q (n - a), prod_pow_succ_sub_one_eq_prod_pow_sub q n]
  have hsplit := Finset.prod_range_add (fun i => (q : ℤ) ^ (n - i) - 1) a (n - a)
  rw [Nat.add_sub_cancel' h] at hsplit
  rw [hsplit]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.sub_sub]

open Module in
private lemma gaussBinom_sub_eq_gaussBinom {q : ℕ} (hq : 1 < q) (n a : ℕ) (h : a ≤ n) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n (n - a) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a := by
  have h1 := gaussBinom_mul_prod_mul_prod_sub_eq_prod q n a h
  have h2 := gaussBinom_mul_prod_mul_prod_sub_eq_prod q n (n - a) (Nat.sub_le n a)
  rw [Nat.sub_sub_self h] at h2
  have hne := mul_ne_zero (prod_pow_succ_sub_one_ne_zero hq a) (prod_pow_succ_sub_one_ne_zero hq (n - a))
  have : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n (n - a) : ℤ) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a := by
    apply mul_right_cancel₀ hne
    linear_combination h2 - h1
  exact_mod_cast this


open Module in
theorem _root_.GlobalTheory.GaussCount.card_codim (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (j : ℕ) :
    Nat.card {L : Submodule k V // finrank k (V ⧸ L) = j} =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Nat.card k) (finrank k V) j := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  by_cases hj : j ≤ finrank k V
  · have e : {L : Submodule k V // finrank k (V ⧸ L) = j} ≃
        {L : Submodule k V // finrank k L = finrank k V - j} :=
      Equiv.subtypeEquivRight fun L => by
        have := L.finrank_quotient_add_finrank
        omega
    rw [Nat.card_congr e, card_submodule_finrank_eq_gaussBinom k V, gaussBinom_sub_eq_gaussBinom hq _ _ hj]
  · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero _ _ _ (by omega)]
    haveI : IsEmpty {L : Submodule k V // finrank k (V ⧸ L) = j} :=
      ⟨fun ⟨L, hL⟩ => by have := L.finrank_quotient_add_finrank; omega⟩
    exact Nat.card_of_isEmpty


open Module in
theorem _root_.GlobalTheory.GaussCount.gauss_formula (q : ℕ) (R : Type) [CommRing R] (Y : R) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j =
      ∏ i ∈ Finset.range m, (1 - (q : R) ^ i * Y) := by
  induction m with
  | zero => simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right]
  | succ m ih =>
    have h0 : ∑ j ∈ Finset.range (m + 1 + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j =
        ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j := by
      rw [Finset.sum_range_succ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero q m (m + 1) (by omega)]
      simp
    have h2 := Finset.sum_range_succ' (fun j => (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j) (m + 1)
    have h1 : ∑ j ∈ Finset.range (m + 1), (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
        ((q ^ (m - j) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : ℕ) : R) * Y ^ (j + 1) =
        -((q : R) ^ m * Y) * ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
      have e : (q : R) ^ m = (q : R) ^ j * (q : R) ^ (m - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hjm]
      rw [Nat.triangle_succ, e]
      push_cast
      ring
    have hterm : ∀ j, (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
        (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q (m + 1) (j + 1) : R) * Y ^ (j + 1) =
        (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m (j + 1) : R) * Y ^ (j + 1) +
        (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
          ((q ^ (m - j) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : ℕ) : R) * Y ^ (j + 1) := by
      intro j
      rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ]
      push_cast
      ring
    rw [Finset.prod_range_succ, ← ih, Finset.sum_range_succ',
      Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, h1]
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right] at h2 ⊢
    linear_combination h0 - h2

end GlobalTheory.GaussCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx

theorem integral_mul_mem_SB {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [R1Space X]
    [MeasurableSpace E] (μ : Measure E) (G : X × E → ℂ) (hG : G ∈ SB (X × E)) (χ : E → ℂ) :
    (fun x => ∫ e, G (x, e) * χ e ∂μ) ∈ SB X := by
  obtain ⟨h1, h2⟩ := hG
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x₀
    have hK : IsCompact (Prod.snd '' tsupport G) := h2.isCompact.image continuous_snd
    have h := hK.eventually_forall_of_forall_eventually (x₀ := x₀)
      (P := fun x y => G (x, y) = G (x₀, y)) (by
        intro y _
        have ha := h1.eventually_eq (x₀, y)
        have hc : Continuous fun z : X × E => ((x₀, z.2) : X × E) := by fun_prop
        have hb := (h1.comp_continuous hc).eventually_eq (x₀, y)
        filter_upwards [ha, hb] with z hz hz'
        exact hz.trans hz'.symm)
    filter_upwards [h] with x hx
    congr 1
    funext e
    by_cases he : e ∈ Prod.snd '' tsupport G
    · rw [hx e he]
    · have : ∀ x', G (x', e) = 0 := fun x' =>
        image_eq_zero_of_notMem_tsupport fun h' => he ⟨_, h', rfl⟩
      rw [this, this]
  · refine HasCompactSupport.intro (h2.isCompact.image continuous_fst) fun x hx => ?_
    have : ∀ e, G (x, e) = 0 := fun e =>
      image_eq_zero_of_notMem_tsupport fun h' => hx ⟨_, h', rfl⟩
    simp [this]

section
variable {k : Type*} [Field k] {n n' : Type*} {c : ℕ}

theorem affPt_of_free (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    affPt p x₀ e rs.1.1 rs.1.2 = basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2 + e rs := by
  obtain ⟨⟨r, s⟩, h⟩ := rs
  simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_pos h]
  congr 1
  rcases r with r | r <;> rcases s with s | s
  · exact h.elim
  all_goals rfl

theorem affPt_inl_inl (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r : n) (s : n') :
    affPt p x₀ e (Sum.inl r) (Sum.inl s) = x₀ r s := by
  simp [affPt, basePt, Free]

variable [TopologicalSpace k] [IsTopologicalRing k]

theorem continuous_affPt_uncurry (p : ℕ) :
    Continuous fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt p z.1 z.2 := by
  refine continuous_matrix fun r s => ?_
  by_cases h : Free p (r, s)
  · have := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt_of_free p z.1 z.2 ⟨(r, s), h⟩
    simp only at this
    simp only [this]
    fun_prop
  · simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]
    rcases r with r | r <;> rcases s with s | s
    · exact continuous_fst.matrix_elem r s
    all_goals exact continuous_const

theorem isClosedEmbedding_affPt_uncurry [T2Space k] (p : ℕ) :
    IsClosedEmbedding
      fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        affPt p z.1 z.2 := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
      ((Matrix.of fun r s => M (Sum.inl r) (Sum.inl s) : Matrix n n' k),
        fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} =>
          M rs.1.1 rs.1.2 - basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2)) ?_ ?_
    (continuous_affPt_uncurry p)
  · rintro ⟨x, e⟩
    refine Prod.ext ?_ ?_
    · ext r s
      simp [affPt_inl_inl]
    · funext rs
      simp [affPt_of_free]
  · refine Continuous.prodMk (continuous_matrix fun r s => continuous_id.matrix_elem _ _) ?_
    exact continuous_pi fun rs => (continuous_id.matrix_elem _ _).sub continuous_const

theorem comp_affPt_mem_SB [T2Space k] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    (fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) ∈ SB _ :=
  ⟨hΦ.1.comp_continuous (continuous_affPt_uncurry p),
    hΦ.2.comp_isClosedEmbedding (isClosedEmbedding_affPt_uncurry p)⟩

end

section
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c : ℕ}


open scoped Classical in
open Classical in
theorem integrable_opE_integrand (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x₀ : Matrix n n' k) :
    Integrable (fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)) (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc : Continuous fun e => affPt (c := c) p x₀ e :=
    (continuous_affPt_uncurry p).comp (Continuous.prodMk_right x₀)
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · refine (hΦ.1.continuous.comp hc).mul (continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_)))
    exact continuous_finsetSum _ fun i _ => hc.matrix_elem _ _
  · refine HasCompactSupport.mul_right ?_
    have h2 := (comp_affPt_mem_SB p hΦ).2
    refine HasCompactSupport.intro (h2.isCompact.image continuous_snd) fun e he => ?_
    exact image_eq_zero_of_notMem_tsupport
      (f := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) (x := (x₀, e)) fun h' => he ⟨_, h', rfl⟩


omit [BorelSpace k] [DecidableEq n] [DecidableEq n'] in
theorem opE_mem_SB (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) : opE ψ ν p Φ ∈ SB (Matrix n n' k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  exact integral_mul_mem_SB _ _ (comp_affPt_mem_SB p hΦ)
    (fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))

theorem opE_smul_add (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] (z : ℂ) {Φ Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ := by
  funext x₀
  have h1 := (integrable_opE_integrand p hψ ν hΦ x₀).const_mul z
  have h2 := integrable_opE_integrand p hψ ν hΨ x₀
  simp only [opE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add h1 h2]
  congr 1
  funext e
  ring

end

theorem opE_SB_and_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure], (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p Φ ∈ SB (Matrix n n' k)) ∧ ∀ (z : ℂ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ p ψ hψ ν _ =>
    ⟨fun _ hΦ => opE_mem_SB p ψ ν hΦ, fun z _ hΦ _ hΨ => opE_smul_add p hψ ν z hΦ hΨ⟩

end GlobalTheory.RootEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleOuterTprod
section
open scoped TensorProduct

namespace GlobalTheory.OuterTensor

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem isIrreducible_outer_tprod :
    ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W), ρ.IsIrreducible → σ.IsIrreducible → (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IsIrreducible := by
  intro G H V W _ _ _ _ _ _ _ _ ρ σ hρ hσ
  have hV := nontrivial_of_isIrreducible ρ hρ
  have hW := nontrivial_of_isIrreducible σ hσ
  have sρ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible G V ρ hρ
  have sσ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hσ
  have hVW : Nontrivial (V ⊗[ℂ] W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h : (⊥ : Submodule ℂ (V ⊗[ℂ] W)) = ⊤)
  have h1 : ∀ (g : G) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map (ρ g) B x ∈ S.toSubmodule := by
    intro g B
    have hB : B ∈ Submodule.span ℂ (Set.range σ) := sσ ▸ Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨h, rfl⟩ := hB
      intro x hx
      exact S.apply_mem_toSubmodule (g, h) hx
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [TensorProduct.map_add_right, LinearMap.add_apply]
      exact add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [TensorProduct.map_smul_right, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hB x hx)
  have h2 : ∀ (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map A B x ∈ S.toSubmodule := by
    intro A B
    have hA : A ∈ Submodule.span ℂ (Set.range ρ) := sρ ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨g, rfl⟩ := hA
      exact h1 g B
    | zero => intro x _; simp
    | add A C _ _ hA hC =>
      intro x hx
      rw [TensorProduct.map_add_left, LinearMap.add_apply]
      exact add_mem (hA x hx) (hC x hx)
    | smul c A _ hA =>
      intro x hx
      rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hA x hx)
  have h3 : ∀ (F : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W), ∀ x ∈ S.toSubmodule, F x ∈ S.toSubmodule := by
    intro F
    obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ V W V W).surjective F
    induction t using TensorProduct.induction_on with
    | zero => intro x _; simp
    | tmul A B =>
      intro x hx
      rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
      exact h2 A B x hx
    | add s t hs ht =>
      intro x hx
      rw [map_add (f := _), LinearMap.add_apply]
      exact add_mem (hs x hx) (ht x hx)
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx0
    have := h3 (f.smulRight y) x hx
    simpa [hf] using this

end GlobalTheory.OuterTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeKerOfLocalFiniteLengthToSimpleStatement
section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_ker_of_local_finite_length_to_simple : ∀ {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab Op K → Rel ≤ LinearMap.ker φ →
    (∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ) →
    (∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g) →
    (∀ U : Submodule ℂ W, GlobalTheory.TensHead.Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) →
    K ≤ LinearMap.ker φ := by
  first | exact @GlobalTheory.TensHead.le_ker_of_simple_commuting | exact GlobalTheory.TensHead.le_ker_of_simple_commuting | (intros; apply GlobalTheory.TensHead.le_ker_of_simple_commuting <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapSwapShearedProductMeasureUnimodularStatement
section
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_swap_sheared_product_measure_unimodular : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H), IsClosed (N : Set H) → ∀ (κ : Measure N), κ.IsHaarMeasure → κ.map (fun n => n⁻¹) = κ → ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by
  first | exact @GlobalTheory.UnfoldNormal.map_swap_map_shear | exact GlobalTheory.UnfoldNormal.map_swap_map_shear | (intros; apply GlobalTheory.UnfoldNormal.map_swap_map_shear <;> assumption)
end

