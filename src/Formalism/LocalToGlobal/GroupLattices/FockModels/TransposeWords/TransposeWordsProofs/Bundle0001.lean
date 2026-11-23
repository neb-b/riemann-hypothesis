module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0001
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0014

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingDividedAdjoint
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

lemma adj_fockR_of_subset {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ))
    (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  apply Finset.sum_subset h
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]
  ring

lemma adj_fockR_add_left {σ R : Type*} [CommRing R] (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [adj_fockR_of_subset _ _ (f.support ∪ f'.support) MvPolynomial.support_add,
    adj_fockR_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    adj_fockR_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.coeff_add]
  ring

lemma adj_fockR_smul_left {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR (a • f) g = a * fockR f g := by
  rw [adj_fockR_of_subset _ _ f.support MvPolynomial.support_smul, fockR, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

lemma adj_fockR_symm {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) :
    fockR f g = fockR g f := by
  classical
  rw [adj_fockR_of_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    adj_fockR_of_subset g f (f.support ∪ g.support) Finset.subset_union_right]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma adj_fockR_add_right {σ R : Type*} [CommRing R] (f g g' : MvPolynomial σ R) :
    fockR f (g + g') = fockR f g + fockR f g' := by
  rw [adj_fockR_symm, adj_fockR_add_left, adj_fockR_symm g, adj_fockR_symm g']

lemma adj_fockR_smul_right {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR f (a • g) = a * fockR f g := by
  rw [adj_fockR_symm, adj_fockR_smul_left, adj_fockR_symm]

lemma adj_fockR_map {σ R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : MvPolynomial σ R) :
    fockR (map φ f) (map φ g) = φ (fockR f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [adj_fockR_of_subset _ _ f.support (MvPolynomial.support_map_subset _ _), fockR, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp [MvPolynomial.coeff_map]

lemma adj_fockR_rat {σ : Type*} (f g : MvPolynomial σ ℚ) : fockR f g = fockQ f g := rfl

lemma adj_rowDiv_int {r n : ℕ} (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) ℤ) :
    fockR (rowDiv ℤ a b k f) g = fockR f (rowDiv ℤ b a k g) := by
  apply Int.cast_injective (α := ℚ)
  have e1 := adj_fockR_map (Int.castRingHom ℚ) (rowDiv ℤ a b k f) g
  have e2 := adj_fockR_map (Int.castRingHom ℚ) f (rowDiv ℤ b a k g)
  simp only [eq_intCast] at e1 e2
  rw [← e1, ← e2, ← lclosedeq_rowDiv_map, ← lclosedeq_rowDiv_map, adj_fockR_rat, adj_fockR_rat]
  exact fockQRowDivAdj r n a b k _ _

lemma adj_monomial_eq {σ R : Type*} [CommRing R] (m : σ →₀ ℕ) (c : R) :
    (monomial m c : MvPolynomial σ R) = c • map (Int.castRingHom R) (monomial m (1 : ℤ)) := by
  rw [MvPolynomial.map_monomial, map_one, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem fock_pairing_divided_adjoint : FockRRowDivAdj := by
  intro R _ r n a b k f g
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    induction g using MvPolynomial.induction_on' with
    | monomial m' c' =>
      rw [adj_monomial_eq m c, adj_monomial_eq m' c', rowDiv_smul, rowDiv_smul,
        lclosedeq_rowDiv_map, lclosedeq_rowDiv_map]
      rw [adj_fockR_smul_left, adj_fockR_smul_right, adj_fockR_smul_left, adj_fockR_smul_right,
        adj_fockR_map, adj_fockR_map, adj_rowDiv_int]
    | add g1 g2 h1 h2 =>
      rw [rowDiv_add, adj_fockR_add_right, adj_fockR_add_right, h1, h2]
  | add f1 f2 h1 h2 =>
    rw [rowDiv_add, adj_fockR_add_left, adj_fockR_add_left, h1, h2]

lemma adj_applyWord_cons {R : Type*} [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ)
    (w : List (Fin r × Fin r × ℕ)) (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) F = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w F) := by
  rfl

lemma adj_applyWord_append {R : Type*} [CommRing R] {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (l1 ++ l2) F = applyWord R l1 (applyWord R l2 F) := by
  unfold applyWord
  rw [List.foldr_append]

lemma adj_transposeWord_cons {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by
  simp [transposeWord]

theorem fock_pairing_word_adjoint : FockRWordAdj := by
  intro R _ r n w
  induction w with
  | nil =>
    intro F G
    rfl
  | cons x w ih =>
    intro F G
    rw [adj_applyWord_cons, fock_pairing_divided_adjoint R r n x.1 x.2.1 x.2.2, ih, adj_transposeWord_cons,
      adj_applyWord_append]
    rfl

end Formalism.L2.G.Model.TS
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingHighestWeightProof
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

theorem hw_dom {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r)
    (f : MvPolynomial (Fin r × Fin n) B) (hf : f ∈ dualWeyl B r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by
  classical
  rw [standardMonomialSpanDomain B r n ν] at hf
  have key : ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t := by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
      intro m hm k
      have h := (bidetDominance B r n K sz hsz I m hm).1 k
      rw [hshape] at h
      exact h
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm
      rcases Finset.mem_union.mp (support_add hm) with h | h
      · exact hx m h
      · exact hy m h
    | smul c x _ hx =>
      intro m hm
      exact hx m (support_smul hm)
  intro m hm k
  rw [rowNu_partial_sum ν hnr k]
  exact key m hm k

theorem hw_kill {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) B) (hG : G ∈ dualWeyl B r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv B a b k G = 0 := by
  classical
  have hGp : IsWeightedHomogeneous (lehwP a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro m hm
    rw [lehw_weight_P]
    have hm' := hGh hm
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hm']
  have hsh := lehw_rowDiv_shift B (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp
  have hmem := rowDivStable B r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have h1 := hsh hm
  rw [lehw_weight_P] at h1
  have h2 := hw_dom ν hn _ hmem m (mem_support_iff.mpr hm) (a.val + 1)
  have h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [h1] at h3
  linarith

theorem eval_idFrame_hw (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow]
  have h := eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega)
  change eval (idPoint R r n) _ ^ _ = 1
  rw [h, one_pow]

theorem fock_pairing_highest_weight_proof : FockPairingHighestWeight := by
  intro K _ _ r n hn ν hν F hF
  classical
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F with hGdef
  have hG : G ∈ dualWeyl K r n ν := dualWeylRowGraded K r n ν _ F hF
  have hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν) :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨c, hc⟩ := hwLine K r n hn ν hν G hG
    (fun a b hab k hk => hw_kill hn ν G hG hGh a b hab k hk)
  have hHW := hwRowWeight K r n hn ν hν
  have h1 : fockR (hw K hn ν) F = fockR (hw K hn ν) G := by
    unfold fockR
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hm))]
  have h2 : fockR (hw K hn ν) G = c * fockR (hw K hn ν) (hw K hn ν) := by
    rw [hc]
    unfold fockR
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_smul, smul_eq_mul]
    ring
  have hcolF : IsWeightedHomogeneous (colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
  have hcolH : IsWeightedHomogeneous (colW r n) (hw K hn ν) ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp (hwMem K r n hn ν hν)).1
  have hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idFrame K r n (a, j) = 0 := by
    intro a j h
    simp [idFrame, h]
  have eF := lhwline_diag hn ν F hcolF (idFrame K r n) hD
  have eH := lhwline_diag hn ν (hw K hn ν) hcolH (idFrame K r n) hD
  have hev1 := eval_idFrame_hw K hn ν
  have hDmem : lhwline_mnu hn ν ∈ (hw K hn ν).support := by
    rw [mem_support_iff]
    intro h0
    rw [h0, zero_mul, hev1] at eH
    exact one_ne_zero eH
  have hcoef : AddMonoidAlgebra.coeff F (lhwline_mnu hn ν) = c * AddMonoidAlgebra.coeff (hw K hn ν) (lhwline_mnu hn ν) := by
    have e : AddMonoidAlgebra.coeff F (lhwline_mnu hn ν) = AddMonoidAlgebra.coeff G (lhwline_mnu hn ν) := by
      rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hDmem))]
    rw [e, hc, coeff_smul, smul_eq_mul]
  have hevF : eval (idFrame K r n) F = c := by
    rw [eF, hcoef, mul_assoc, ← eH, hev1, mul_one]
  rw [h1, h2, hevF]

end Formalism.L2.G.Model.TS
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

section general

variable {σ R : Type*} [CommRing R]

lemma tsact_eq_sum (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  refine Finset.sum_subset h fun m _ hm => ?_
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]

lemma tsact_symm (f g : MvPolynomial σ R) : fockR f g = fockR g f := by
  classical
  rw [tsact_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    tsact_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma tsact_add_left (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [tsact_eq_sum (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    tsact_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    tsact_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

lemma tsact_smul_left (c : R) (f g : MvPolynomial σ R) :
    fockR (c • f) g = c * fockR f g := by
  rw [tsact_eq_sum (c • f) g f.support MvPolynomial.support_smul]
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring

lemma tsact_zero_left (g : MvPolynomial σ R) : fockR (0 : MvPolynomial σ R) g = 0 := by
  unfold fockR
  simp

lemma tsact_sum_left {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ s, F i) g = ∑ i ∈ s, fockR (F i) g := by
  classical
  refine Finset.induction_on s (by simp [tsact_zero_left]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, tsact_add_left, ih]

lemma tsact_sum_right {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR g (∑ i ∈ s, F i) = ∑ i ∈ s, fockR g (F i) := by
  rw [tsact_symm, tsact_sum_left]
  exact Finset.sum_congr rfl fun i _ => tsact_symm _ _

lemma tsact_smul_right (c : R) (f g : MvPolynomial σ R) :
    fockR f (c • g) = c * fockR f g := by
  rw [tsact_symm, tsact_smul_left, tsact_symm]

lemma tsact_monomial_left (m : σ →₀ ℕ) (a : R) (h : MvPolynomial σ R) :
    fockR (monomial m a) h = a * h.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  classical
  by_cases ha : a = 0
  · subst ha; simp [tsact_zero_left]
  · unfold fockR
    rw [MvPolynomial.support_monomial, if_neg ha, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

lemma tsact_fact_eq (m : σ →₀ ℕ) (s : Finset σ) (h : m.support ⊆ s) :
    ∏ k ∈ m.support, (m k).factorial = ∏ k ∈ s, (m k).factorial := by
  refine Finset.prod_subset h fun k _ hk => ?_
  have h0 : m k = 0 := by simpa using hk
  rw [h0, Nat.factorial_zero]

lemma tsact_fact_succ (m : σ →₀ ℕ) (v : σ) :
    ∏ k ∈ (m + Finsupp.single v 1).support, ((m + Finsupp.single v 1 : σ →₀ ℕ) k).factorial
      = (m v + 1) * ∏ k ∈ m.support, (m k).factorial := by
  classical
  have h1 : (m + Finsupp.single v 1).support ⊆ insert v m.support := by
    intro k hk
    rw [Finset.mem_insert]
    by_cases hkv : k = v
    · exact Or.inl hkv
    · right
      simpa [Finsupp.mem_support_iff, Finsupp.single_apply, Ne.symm hkv] using hk
  rw [tsact_fact_eq _ _ h1, tsact_fact_eq m (insert v m.support) (Finset.subset_insert _ _),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v m.support),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v m.support)]
  have h2 : ∏ k ∈ (insert v m.support).erase v, ((m + Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ (insert v m.support).erase v, (m k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Finset.mem_erase] at hk
    simp [Finsupp.single_apply, Ne.symm hk.1]
  rw [h2]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

lemma tsact_X_mul (v : σ) (f h : MvPolynomial σ R) :
    fockR (f * X v) h = fockR f (pderiv v h) := by
  classical
  rw [tsact_eq_sum (f * X v) h _ (MvPolynomial.support_mul_X v f).le, Finset.sum_map]
  unfold fockR
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, MvPolynomial.coeff_pderiv, tsact_fact_succ]
  push_cast
  ring

end general

section what₂

variable {R : Type*} [CommRing R] {r n : ℕ}

lemma tsact_rowAct_X (G : Matrix (Fin r) (Fin r) R) (v : Fin r × Fin n) :
    rowAct R G (X v) = ∑ b : Fin r, C (G v.1 b) * X (b, v.2) := by
  simp [rowAct]

lemma tsact_coeff_zero (G : Matrix (Fin r) (Fin r) R) (h : MvPolynomial (Fin r × Fin n) R) :
    AddMonoidAlgebra.coeff (rowAct R G h) 0 = AddMonoidAlgebra.coeff h 0 := by
  show MvPolynomial.constantCoeff (rowAct R G h) = MvPolynomial.constantCoeff h
  induction h using MvPolynomial.induction_on
  next a => simp [rowAct]
  next p q hp hq => simp only [map_add (f := _), hp, hq]
  next p v hp => simp [hp, rowAct]

lemma tsact_chain (G : Matrix (Fin r) (Fin r) R) (b : Fin r) (s : Fin n) (h : MvPolynomial (Fin r × Fin n) R) :
    pderiv (b, s) (rowAct R G h) = ∑ a : Fin r, G a b • rowAct R G (pderiv (a, s) h) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    obtain ⟨c, t⟩ := v
    have hL : pderiv (b, s) (∑ d : Fin r, C (G c d) * X (d, t) : MvPolynomial (Fin r × Fin n) R)
        = if t = s then C (G c b) else 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [pderiv_C_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [eq_comm]
      · simp [hts]
    have hR : ∑ a : Fin r, G a b • (rowAct R G p * rowAct R G (pderiv (a, s) (X (c, t))))
        = rowAct R G p * (if t = s then C (G c b) else 0) := by
      simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [apply_ite, Finset.sum_ite_eq, smul_eq_C_mul, mul_comm]
      · simp [hts]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), tsact_rowAct_X, hL, hp]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [hR]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm]

end what₂

theorem fock_pairing_row_action : FockRRowAct := by
  intro R _ r n g P
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro Q
    have h1 : rowAct R g (C a : MvPolynomial (Fin r × Fin n) R) = C a := by simp [rowAct]
    rw [h1, C_apply, tsact_monomial_left, tsact_monomial_left, tsact_coeff_zero]
  | add p q hp hq =>
    intro Q
    rw [map_add (f := _), tsact_add_left, tsact_add_left, hp, hq]
  | mul_X p v hp =>
    intro Q
    rw [map_mul, tsact_rowAct_X, Finset.mul_sum, tsact_sum_left, tsact_X_mul, tsact_chain, tsact_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : rowAct R g p * (C (g v.1 b) * X (b, v.2)) = g v.1 b • (rowAct R g p * X (b, v.2)) := by
      rw [smul_eq_C_mul]; ring
    rw [e, tsact_smul_left, tsact_X_mul, hp, tsact_smul_right, Matrix.transpose_apply]

end Formalism.L2.G.Model.TS
end
end

