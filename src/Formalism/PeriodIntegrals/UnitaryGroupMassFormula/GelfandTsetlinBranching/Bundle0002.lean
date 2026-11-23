module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FockFEqSumOfSubsetB

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FockFRowActRight
section
noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def iotaC (R : Type) [CommRing R] (n k : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + k)) (Fin (n + k)) R :=
  Matrix.reindexAlgEquiv R R finSumFinEquiv (Matrix.fromBlocks Y 0 0 1)

theorem iotaC_mul (R : Type) [CommRing R] (n k : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    iotaC R n k (A * B) = iotaC R n k A * iotaC R n k B := by
  rw [iotaC, iotaC, iotaC, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem iotaC_one (R : Type) [CommRing R] (n k : ℕ) : iotaC R n k 1 = 1 := by
  rw [iotaC, Matrix.fromBlocks_one, map_one]

theorem iotaC_map (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (n k : ℕ)
    (Y : Matrix (Fin n) (Fin n) R) : (iotaC R n k Y).map φ = iotaC S n k (Y.map φ) := by
  ext i j
  simp only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem iotaC_conj (n k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    iotaC ℂ n k Y.conjTranspose = (iotaC ℂ n k Y).conjTranspose := by
  ext i j
  simp only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, Matrix.conjTranspose_apply, apply_ite, eq_comm]

theorem iotaC_det (n k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : (iotaC ℂ n k Y).det = Y.det := by
  rw [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

theorem iotaC_zero (R : Type) [CommRing R] (n : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    iotaC R n 0 Y = Y := by
  have hi : ∀ i : Fin (n + 0), finSumFinEquiv.symm i = Sum.inl i := fun i => by
    rw [Equiv.symm_apply_eq]; rfl
  ext i j
  simp [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, hi]

open Formalism.REAL (fockF)

def fct {σ : Type} (m : σ →₀ ℕ) : ℂ := ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)

theorem fockF_eq_sum {σ : Type} (p q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ))
    (hs : ∀ m, p.coeff m ≠ 0 → q.coeff m ≠ 0 → m ∈ s) :
    fockF p q = ∑ m ∈ s, p.coeff m * star (q.coeff m) * fct m := by
  classical
  trans ∑ m ∈ p.support ∩ s, p.coeff m * star (q.coeff m) * fct m
  · unfold fockF fct
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro m hm hms
    by_cases hq : q.coeff m = 0
    · simp [hq]
    · exact absurd (Finset.mem_inter.mpr ⟨hm, hs m (MvPolynomial.mem_support_iff.mp hm) hq⟩) hms
  · apply Finset.sum_subset Finset.inter_subset_right
    intro m hm hms
    by_cases hp : p.coeff m = 0
    · simp [hp]
    · exact absurd (Finset.mem_inter.mpr ⟨MvPolynomial.mem_support_iff.mpr hp, hm⟩) hms

theorem fockF_add_left {σ : Type} (p p' q : MvPolynomial σ ℂ) :
    fockF (p + p') q = fockF p q + fockF p' q := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ, r.support ⊆ p.support ∪ p'.support →
      fockF r q = ∑ m ∈ p.support ∪ p'.support, r.coeff m * star (q.coeff m) * fct m :=
    fun r hr => fockF_eq_sum r q _ (fun m h1 _ => hr (MvPolynomial.mem_support_iff.mpr h1))
  rw [hs (p + p') MvPolynomial.support_add, hs p Finset.subset_union_left,
    hs p' Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fockF_smul_left {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fockF (c • p) q = c * fockF p q := by
  classical
  rw [fockF_eq_sum (c • p) q p.support (fun m h _ => by
        rw [MvPolynomial.coeff_smul, smul_eq_mul] at h
        exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul h)),
    fockF_eq_sum p q p.support (fun m h _ => MvPolynomial.mem_support_iff.mpr h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockF_zero_left {σ : Type} (q : MvPolynomial σ ℂ) : fockF 0 q = 0 := by
  simp [fockF]

theorem fockF_add_right {σ : Type} (p q q' : MvPolynomial σ ℂ) :
    fockF p (q + q') = fockF p q + fockF p q' := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ,
      fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m :=
    fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)
  rw [hs, hs, hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

theorem fockF_smul_right {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fockF p (c • q) = star c * fockF p q := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ,
      fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m :=
    fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)
  rw [hs, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fockF_sum_left {σ ι : Type} (s : Finset ι) (x : ι → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, x i) q = ∑ i ∈ s, fockF (x i) q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fockF]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_left, ih]

theorem fockF_sum_right {σ ι : Type} (s : Finset ι) (x : ι → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ) :
    fockF p (∑ i ∈ s, x i) = ∑ i ∈ s, fockF p (x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fockF]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_right, ih]

theorem fockF_lc {σ ι : Type} (s : Finset ι) (a : ι → ℂ) (x : ι → MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, a i • x i) (∑ j ∈ s, a j • x j) =
      ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * fockF (x i) (x j) := by
  rw [fockF_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fockF_smul_left, fockF_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fockF_smul_right]
  ring

private theorem eq_zero_of_fockF_self_eq_zero {σ : Type} (p : MvPolynomial σ ℂ) (h : fockF p p = 0) : p = 0 := by
  classical
  by_contra hp
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hp)
  have hre : (fockF p p).re =
      ∑ m ∈ p.support, Complex.normSq (p.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) := by
    unfold fockF
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    show (p.coeff m * (starRingEnd ℂ) (p.coeff m) * _).re = _
    rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpos : 0 < ∑ m ∈ p.support, Complex.normSq (p.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) :=
    Finset.sum_pos (fun m hm => mul_pos (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm))
      (Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _))) ⟨m, hm⟩
  rw [← hre, h, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

theorem lc_zero_of_gram {σ τ ι : Type} (s : Finset ι) (a : ι → ℂ) (xe : ι → MvPolynomial σ ℂ)
    (xf : ι → MvPolynomial τ ℂ) (K : ℂ)
    (hK : ∀ i j, fockF (xf i) (xf j) = K * fockF (xe i) (xe j))
    (h0 : ∑ i ∈ s, a i • xe i = 0) : ∑ i ∈ s, a i • xf i = 0 := by
  have hyy : fockF (∑ i ∈ s, a i • xf i) (∑ i ∈ s, a i • xf i) = 0 := by
    have he := fockF_lc s a xe
    rw [h0, fockF_zero_left] at he
    rw [fockF_lc]
    simp_rw [hK]
    calc _ = K * ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * fockF (xe i) (xe j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [← he, mul_zero]
  exact eq_zero_of_fockF_self_eq_zero _ hyy

theorem fockF_rowAct_right (r n : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) (p q : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF p (rowAct ℂ M q) = fockF (rowAct ℂ M.conjTranspose p) q := by
  rw [fockRowAdj r n M.conjTranspose p q, Matrix.conjTranspose_conjTranspose]

end PI.WGB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.RowActDiagMonomial
section
noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

def wnB (n N : ℕ) : Fin N × Fin N → (Fin n → ℕ) :=
  fun v => if hv : v.1.1 < n then Pi.single (⟨v.1.1, hv⟩ : Fin n) 1 else 0

def prowB (n N : ℕ) (a : Fin N) : ℕ := if a.1 < n then n - a.1 else 0

def psiB (n N : ℕ) : Fin N × Fin N → ℕ := fun v => prowB n N v.1

def PsiB (n : ℕ) : (Fin n → ℕ) →+ ℕ where
  toFun m := ∑ j, (n - j.1) * m j
  map_zero' := by simp
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]

theorem PsiB_apply (n : ℕ) (m : Fin n → ℕ) : PsiB n m = ∑ j, (n - j.1) * m j := rfl

theorem PsiB_wnB (n N : ℕ) (v : Fin N × Fin N) : PsiB n (wnB n N v) = psiB n N v := by
  unfold wnB psiB prowB
  split_ifs with hv
  · rw [PsiB_apply]
    simp [Pi.single_apply]
  · simp

theorem weight_psiB (n N : ℕ) (e : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (psiB n N) e = PsiB n (Finsupp.weight (wnB n N) e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_nsmul, PsiB_wnB]

def chiB {n : ℕ} (t : Fin n → ℂ) (m : Fin n → ℕ) : ℂ := ∏ j, t j ^ m j

theorem chiB_add {n : ℕ} (t : Fin n → ℂ) (a b : Fin n → ℕ) : chiB t (a + b) = chiB t a * chiB t b := by
  simp [chiB, pow_add, Finset.prod_mul_distrib]

theorem chiB_smul {n : ℕ} (t : Fin n → ℂ) (k : ℕ) (a : Fin n → ℕ) : chiB t (k • a) = chiB t a ^ k := by
  simp only [chiB, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm]

theorem chiB_zero {n : ℕ} (t : Fin n → ℂ) : chiB t 0 = 1 := by simp [chiB]

theorem chiB_weight {n : ℕ} {σ : Type*} (t : Fin n → ℂ) (w : σ → (Fin n → ℕ)) (e : σ →₀ ℕ) :
    chiB t (Finsupp.weight w e) = ∏ v ∈ e.support, chiB t (w v) ^ e v := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  induction e.support using Finset.cons_induction with
  | empty => simp [chiB_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, chiB_add, chiB_smul, ih]

def dB (n N : ℕ) (t : Fin n → ℂ) : Fin N → ℂ := fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1

theorem chiB_wnB {n N : ℕ} (t : Fin n → ℂ) (v : Fin N × Fin N) : chiB t (wnB n N v) = dB n N t v.1 := by
  unfold wnB dB
  split_ifs with hv
  · unfold chiB
    rw [Finset.prod_eq_single (⟨v.1.1, hv⟩ : Fin n)]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  · simp [chiB]

theorem rowAct_diag_X {N : ℕ} (d : Fin N → ℂ) (v : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal d) (X v) = C (d v.1) * X v := by
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem rowAct_diag_monomial {n N : ℕ} (t : Fin n → ℂ) (e : Fin N × Fin N →₀ ℕ) (c : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) (monomial e c) =
      chiB t (Finsupp.weight (wnB n N) e) • monomial e c := by
  have hC : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) (C c) = C c := by
    simp [Formalism.GradedWeylDivisibility.rowAct]
  rw [chiB_weight, monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow, rowAct_diag_X, mul_pow, Finset.prod_mul_distrib, chiB_wnB]
  rw [smul_eq_C_mul, map_prod]
  simp only [C_pow]
  ring

theorem rowAct_diag_homog {n N : ℕ} (t : Fin n → ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ)
    (hg : IsWeightedHomogeneous (wnB n N) g m) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) g = chiB t m • g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [rowAct_diag_monomial, hg (mem_support_iff.mp he)]

theorem comp_sum_B {σ M : Type*} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (f : MvPolynomial σ ℂ)
    (F : Finset M) (hF : ∀ e ∈ f.support, Finsupp.weight w e ∈ F) :
    ∑ m ∈ F, weightedHomogeneousComponent w m f = f := by
  ext e
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hF e (mem_support_iff.mpr (Ne.symm hne)))

theorem comp_zero_B {σ M : Type*} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (f : MvPolynomial σ ℂ) (m : M)
    (hm : ∀ e ∈ f.support, Finsupp.weight w e ≠ m) : weightedHomogeneousComponent w m f = 0 := by
  ext e
  rw [coeff_weightedHomogeneousComponent]
  change (if Finsupp.weight w e = m then f.coeff e else 0) = 0
  split_ifs with h
  · by_contra hne
    exact hm e (mem_support_iff.mpr hne) h
  · rfl

theorem sep_mem_B {ι T V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : T → Module.End ℂ V) (p : ι → T → ℂ) (P : Submodule ℂ V) (hP : ∀ t, ∀ x ∈ P, C t x ∈ P)
    (hsep : ∀ i j, i ≠ j → ∃ t, p i t ≠ p j t) :
    ∀ (F : Finset ι) (y : ι → V), (∀ i ∈ F, ∀ t, C t (y i) = p i t • y i) → ∑ i ∈ F, y i ∈ P →
      ∀ i ∈ F, y i ∈ P := by
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
    intro y hy hs i0 hi0
    by_cases hall : ∀ i ∈ F, i = i0
    · have hF : F = {i0} := by
        ext i
        simp only [Finset.mem_singleton]
        exact ⟨hall i, fun e => e ▸ hi0⟩
      rw [hF, Finset.sum_singleton] at hs
      exact hs
    push_neg at hall
    obtain ⟨i1, hi1, hne⟩ := hall
    obtain ⟨t, ht⟩ := hsep i1 i0 hne
    let y' : ι → V := fun i => (p i t - p i1 t) • y i
    have hy'1 : y' i1 = 0 := by simp [y']
    have hsum : ∑ i ∈ F.erase i1, y' i = C t (∑ i ∈ F, y i) - p i1 t • ∑ i ∈ F, y i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_erase _ hy'1, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [y']
      rw [hy i hi t, sub_smul]
    have hmem : ∑ i ∈ F.erase i1, y' i ∈ P := by
      rw [hsum]
      exact P.sub_mem (hP t _ hs) (P.smul_mem _ hs)
    have key := ih (F.erase i1) (Finset.erase_ssubset hi1) y'
      (fun i hi u => by
        simp only [y']
        rw [map_smul, hy i (Finset.mem_of_mem_erase hi) u, smul_comm]) hmem
      i0 (Finset.mem_erase.mpr ⟨fun e => hne e.symm, hi0⟩)
    have hd : p i0 t - p i1 t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    have e0 : y i0 = (p i0 t - p i1 t)⁻¹ • y' i0 := by
      simp only [y']
      rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [e0]
    exact P.smul_mem _ key

theorem embGL_apply_B {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) (a b : Fin N) :
    ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a b =
      if ha : a.1 < n then (if hb : b.1 < n then (g : Matrix (Fin n) (Fin n) ℂ) ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0)
      else (if b.1 < n then 0 else 1) := by
  subst h
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embGL_diag_B {n N : ℕ} (h : n + 1 = N) (t : Fin n → ℂˣ) :
    ((embGL ℂ n N h (diagGL ℂ n t) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal (dB n N (fun j => (t j : ℂ))) := by
  ext a b
  have ha2 := a.2
  have hb2 := b.2
  rw [embGL_apply_B, Matrix.diagonal_apply]
  by_cases ha : a.1 < n <;> by_cases hb : b.1 < n
  · rw [dite_eq_left ha, dite_eq_left hb]
    show (Matrix.diagonal fun a => (t a : ℂ)) ⟨a.1, ha⟩ ⟨b.1, hb⟩ = _
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp [dB, ha]
    · have hne : (⟨a.1, ha⟩ : Fin n) ≠ ⟨b.1, hb⟩ := fun e => hab (Fin.ext (Fin.mk.inj_iff.mp e))
      simp [hab, hne]
  · have hab : a ≠ b := fun e => hb (e ▸ ha)
    rw [dite_eq_left ha, dite_eq_right hb, if_neg hab]
  · have hab : a ≠ b := fun e => ha (e ▸ hb)
    rw [dite_eq_right ha, if_pos hb, if_neg hab]
  · have hab : a = b := Fin.ext (by omega)
    subst hab
    rw [dite_eq_right ha, if_neg hb, if_pos rfl]
    simp [dB, ha]

theorem torus_mem_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (t : Fin n → ℂˣ) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ W) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N fun j => (t j : ℂ))) f ∈ W := by
  have h1 := hW (diagGL ℂ n t) f hf
  unfold sqAct at h1
  rw [embGL_diag_B, Matrix.diagonal_transpose] at h1
  have hu : detPow ℂ N (embGL ℂ n N h (diagGL ℂ n t)) lam.detShift ≠ 0 := Units.ne_zero _
  have := W.smul_mem (detPow ℂ N (embGL ℂ n N h (diagGL ℂ n t)) lam.detShift)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this

theorem graded_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ W) (m : Fin n → ℕ) :
    weightedHomogeneousComponent (wnB n N) m f ∈ W := by
  classical
  let F := f.support.image (Finsupp.weight (wnB n N))
  by_cases hm : m ∈ F
  · refine sep_mem_B (T := Fin n → ℂˣ)
      (fun t => (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N fun j => (t j : ℂ)))).toLinearMap)
      (fun m t => chiB (fun j => (t j : ℂ)) m) W (fun t x hx => torus_mem_B h lam W hW t x hx) ?_ F
      (fun m => weightedHomogeneousComponent (wnB n N) m f) ?_ ?_ m hm
    · intro i j hij
      obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := Function.ne_iff.mp hij
      let τ : Fin n → ℂˣ := fun l => if l = k then Units.mk0 (2 : ℂ) two_ne_zero else 1
      have key : ∀ a : Fin n → ℕ, chiB (fun l => ((τ l : ℂˣ) : ℂ)) a = (2 : ℂ) ^ a k := by
        intro a
        unfold chiB
        rw [Finset.prod_eq_single k]
        · simp [τ]
        · intro l _ hl
          simp [τ, hl]
        · simp
      refine ⟨τ, ?_⟩
      show chiB (fun l => ((τ l : ℂˣ) : ℂ)) i ≠ chiB (fun l => ((τ l : ℂˣ) : ℂ)) j
      rw [key, key]
      intro he
      apply hk
      have h2 : ((2 ^ i k : ℕ) : ℂ) = ((2 ^ j k : ℕ) : ℂ) := by push_cast; exact he
      exact Nat.pow_right_injective le_rfl (Nat.cast_injective h2)
    · intro i _ t
      exact rowAct_diag_homog _ _ _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · rw [comp_sum_B]
      · exact hf
      · intro e he
        exact Finset.mem_image_of_mem _ he
  · rw [comp_zero_B]
    · exact W.zero_mem
    · intro e he hw
      exact hm (hw ▸ Finset.mem_image_of_mem _ he)

end PI.WGB
end
end

