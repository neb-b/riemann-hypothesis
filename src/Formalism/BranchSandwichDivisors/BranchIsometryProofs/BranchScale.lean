module

public import Formalism.BranchSandwichDivisors.StatementW
public import Formalism.GradedWeylDivisibility.FinalD

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL

noncomputable section

namespace Formalism.BranchingDeterminantCap

lemma bs_fock_smul_left {σ : Type*} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (c • f) g = c * fockF f g := by
  rw [smul_eq_C_mul, LFocks_C_mul_left]

lemma bs_fock_smul_right {σ : Type*} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  rw [smul_eq_C_mul, LFocks_C_mul_right]

lemma bs_map_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (hf : f ∈ weyl ℚ r n hn ν) : map (algebraMap ℚ ℂ) f ∈ weyl ℂ r n hn ν := by
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

lemma bs_dual_le_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    dualWeyl ℂ r n ν ≤ weyl ℂ r n hn ν := by
  rw [standardMonomialSpanDomain ℂ r n ν, Submodule.span_le]
  rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
  rw [← ldlat_map_bidet (algebraMap ℚ ℂ)]
  apply bs_map_weyl
  rw [weylEqNablaQ r n hn ν hν, ← hsh]
  exact bidetMem ℚ r n K sz hsz I

lemma bs_dom {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hf : f ∈ dualWeyl ℂ r n ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t) ∧
      ∑ a : Fin r, rowDeg m a = ∑ t : Fin n, ν t := by
  classical
  rw [standardMonomialSpanDomain ℂ r n ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance ℂ r n K sz hsz I m hm
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

lemma bs_abel (n : ℕ) (x : Fin n → ℤ) :
    ∑ a, (a.val : ℤ) * x a =
      ∑ k ∈ Finset.range n, ((∑ a, x a) - ∑ a : Fin n with a.val < k + 1, x a) := by
  have h1 : ∀ a : Fin n, (a.val : ℤ) = ∑ k ∈ Finset.range n, if k < a.val then (1 : ℤ) else 0 := by
    intro a
    rw [Finset.sum_boole]
    have : (Finset.range n).filter (fun k => k < a.val) = Finset.range a.val := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      have := a.isLt
      omega
    rw [this, Finset.card_range]
  calc ∑ a, (a.val : ℤ) * x a
      = ∑ a : Fin n, ∑ k ∈ Finset.range n, (if k < a.val then x a else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        conv_lhs => rw [h1 a]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
    _ = ∑ k ∈ Finset.range n, ∑ a : Fin n, (if k < a.val then x a else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h : k < a.val
        · rw [if_pos h, if_neg (by omega)]; ring
        · rw [if_neg h, if_pos (by omega)]; ring

lemma bs_height_le (n : ℕ) (x y : Fin n → ℕ)
    (h1 : ∀ k : ℕ, (∑ a : Fin n with a.val < k, x a) ≤ ∑ a : Fin n with a.val < k, y a)
    (h2 : ∑ a, x a = ∑ a, y a) :
    ∑ a : Fin n, (a.val : ℤ) * (y a : ℤ) ≤ ∑ a : Fin n, (a.val : ℤ) * (x a : ℤ) := by
  rw [bs_abel, bs_abel]
  refine Finset.sum_le_sum fun k _ => ?_
  have e1 := h1 (k + 1)
  have e1' : (∑ a : Fin n with a.val < k + 1, (x a : ℤ)) ≤ ∑ a : Fin n with a.val < k + 1, (y a : ℤ) := by
    exact_mod_cast e1
  have e2' : (∑ a, (x a : ℤ)) = ∑ a, (y a : ℤ) := by exact_mod_cast h2
  linarith

lemma bs_hwspace {n : ℕ} (sg : Fin n → ℕ) (hsg : Antitone sg) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (hq : q ∈ dualWeyl ℂ n n sg) (hqw : IsWeightedHomogeneous (rowW n n) q sg) :
    ∃ c : ℂ, q = c • hw ℂ le_rfl sg := by
  apply hwLine ℂ n n le_rfl sg hsg q hq
  intro a b hab k hk
  by_contra hne
  have hmem := rowDivStable ℂ n n sg a b k q hq
  have hht : IsWeightedHomogeneous (lhwinHt n n) q (∑ a : Fin n, (a.val : ℤ) * (sg a : ℤ)) := by
    intro d hd
    rw [lhwin_weight_ht, hqw hd]
  have hsh := lhwin_rowDiv_shift ℂ _ a b k q hht
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
  have e := hsh hd
  rw [lhwin_weight_ht] at e
  simp only [ldrow_weight_rowW] at e
  have dom := bs_dom sg _ hmem d (mem_support_iff.mpr hd)
  have hle := bs_height_le n (rowDeg d) sg dom.1 dom.2
  have hab' : (a.val : ℤ) - b.val ≤ -1 := by
    have : a.val < b.val := hab
    omega
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith

structure BsForm {n : ℕ} (sg : Fin n → ℕ)
    (D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ) : Prop where
  addl : ∀ p p' q, D (p + p') q = D p q + D p' q
  smull : ∀ (c : ℂ) p q, D (c • p) q = c * D p q
  addr : ∀ p q q', D p (q + q') = D p q + D p q'
  smulr : ∀ (c : ℂ) p q, D p (c • q) = star c * D p q
  adj : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ dualWeyl ℂ n n sg, ∀ q ∈ dualWeyl ℂ n n sg,
    D (rowAct ℂ g p) q = D p (rowAct ℂ g.conjTranspose q)

namespace BsForm

variable {n : ℕ} {sg : Fin n → ℕ}
  {D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ}

lemma zerol (H : BsForm sg D) (q) : D 0 q = 0 := by
  have := H.smull 0 0 q
  simpa using this

lemma zeror (H : BsForm sg D) (p) : D p 0 = 0 := by
  have := H.smulr 0 p 0
  simpa using this

lemma suml (H : BsForm sg D) {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin n × Fin n) ℂ) (q) :
    D (∑ i ∈ s, g i) q = ∑ i ∈ s, D (g i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.zerol]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.addl, ih]

lemma sumr (H : BsForm sg D) {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin n × Fin n) ℂ) (p) :
    D p (∑ i ∈ s, g i) = ∑ i ∈ s, D p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.zeror]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.addr, ih]

lemma hw_weight (H : BsForm sg D) (hsg : Antitone sg) (μ : Fin n → ℕ) (hμ : μ ≠ sg)
    (q : MvPolynomial (Fin n × Fin n) ℂ) (hq : q ∈ dualWeyl ℂ n n sg)
    (hqw : IsWeightedHomogeneous (rowW n n) q μ) : D (hw ℂ le_rfl sg) q = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hμ
  let t : Fin n → ℂ := fun b => if b = a then 2 else 1
  have hprod : ∀ e : Fin n → ℕ, ∏ b, t b ^ e b = 2 ^ e a := by
    intro e
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb; simp [t, hb]
    · simp
  have hnu : rowNu (r := n) sg = sg := by
    funext b
    simp [rowNu]
  have hhw : IsWeightedHomogeneous (rowW n n) (hw ℂ le_rfl sg) sg := by
    have := hwRowWeight ℂ n n le_rfl sg hsg
    rwa [hnu] at this
  have hconj : (Matrix.diagonal t).conjTranspose = Matrix.diagonal t := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext b
    by_cases hb : b = a <;> simp [t, hb]
  have e := H.adj (Matrix.diagonal t) _ (hwMem ℂ n n le_rfl sg hsg) q hq
  rw [hconj, rowActDiagWeight ℂ n n t sg _ hhw, rowActDiagWeight ℂ n n t μ _ hqw, hprod, hprod,
    H.smull, H.smulr] at e
  have hstar : star ((2 : ℂ) ^ μ a) = 2 ^ μ a := by simp
  rw [hstar] at e
  have hne : (2 : ℂ) ^ sg a - 2 ^ μ a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h' : (2 : ℕ) ^ sg a = 2 ^ μ a := by exact_mod_cast h
    exact ha (Nat.pow_right_injective le_rfl h').symm
  have : ((2 : ℂ) ^ sg a - 2 ^ μ a) * D (hw ℂ le_rfl sg) q = 0 := by rw [sub_mul, e, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

lemma hw_rad (H : BsForm sg D) (hsg : Antitone sg) (h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0)
    (q : MvPolynomial (Fin n × Fin n) ℂ) (hq : q ∈ dualWeyl ℂ n n sg) : D (hw ℂ le_rfl sg) q = 0 := by
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW n n) q
  have hsum := sum_weightedHomogeneousComponent (rowW n n) q
  rw [finsum_eq_sum _ hfin] at hsum
  rw [← hsum, H.sumr]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have hmem := dualWeylRowGraded ℂ n n sg μ q hq
  have hw' := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW n n) μ q
  by_cases hμ : μ = sg
  · subst hμ
    obtain ⟨c, hc⟩ := bs_hwspace μ hsg _ hmem hw'
    rw [hc, H.smulr, h0, mul_zero]
  · exact H.hw_weight hsg μ hμ _ hmem hw'

lemma rad_rowDiv (H : BsForm sg D) (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ dualWeyl ℂ n n sg)
    (h0 : ∀ q ∈ dualWeyl ℂ n n sg, D p q = 0) (a b : Fin n) (k : ℕ) :
    ∀ q ∈ dualWeyl ℂ n n sg, D (rowDiv ℂ a b k p) q = 0 := by
  intro q hq
  set N := (rowGen ℂ a b p).natDegree + k + 1 with hN
  have h1 : (rowGen ℂ a b p).natDegree < N := by omega
  have hk : k ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  set P : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.monomial i (D (rowDiv ℂ a b i p) q) with hP
  have hP0 : P = 0 := by
    apply Polynomial.funext
    intro c
    simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    have e := H.adj (lfockq_mat a b c) p hp q hq
    rw [h0 _ (dualWeylRowStable ℂ n n sg _ q hq), ← lfockq_eval_rowGen, lfockq_eval_C _ N h1,
      H.suml] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_C_mul, H.smull, mul_comm]
    rfl
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Finset.sum_ite_eq',
    if_pos hk, Polynomial.coeff_zero] at this
  exact this

theorem eq_zero (H : BsForm sg D) (hsg : Antitone sg)
    (h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0) :
    ∀ p ∈ dualWeyl ℂ n n sg, ∀ q ∈ dualWeyl ℂ n n sg, D p q = 0 := by
  have W : ∀ w : List (Fin n × Fin n × ℕ), applyWord ℂ w (hw ℂ le_rfl sg) ∈ dualWeyl ℂ n n sg ∧
      ∀ q ∈ dualWeyl ℂ n n sg, D (applyWord ℂ w (hw ℂ le_rfl sg)) q = 0 := by
    intro w
    induction w with
    | nil => exact ⟨hwMem ℂ n n le_rfl sg hsg, H.hw_rad hsg h0⟩
    | cons x w ih =>
      rw [applyWord_cons]
      exact ⟨rowDivStable ℂ n n sg _ _ _ _ ih.1, H.rad_rowDiv _ ih.1 ih.2 _ _ _⟩
  intro p hp q hq
  have key : ∀ p ∈ weyl ℂ n n le_rfl sg, D p q = 0 := by
    intro p hp'
    unfold weyl at hp'
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact (W w).2 q hq
    | zero => exact H.zerol q
    | add x y _ _ hx hy => rw [H.addl, hx, hy, add_zero]
    | smul c x _ hx => rw [H.smull, hx, mul_zero]
  exact key p (bs_dual_le_weyl le_rfl sg hsg hp)

end BsForm

end Formalism.BranchingDeterminantCap
