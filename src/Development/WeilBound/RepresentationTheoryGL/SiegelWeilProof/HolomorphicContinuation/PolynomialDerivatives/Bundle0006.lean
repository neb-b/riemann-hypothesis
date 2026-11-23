module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.IntegrableRpowGauss
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SymbolFirstFamilyOfMem

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMomOfBasic
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem fockMono_zero (c : ℝ) : fockMono c (0 : Fin m × Fin n × Bool →₀ ℕ) = (1 : PX m n) := by
  simp [fockMono]

theorem fock_C (c : ℝ) (r : ℂ) : fock c (C r : PX m n) = C r := by
  classical
  by_cases hr : r = 0
  · subst hr; simp [fock]
  · rw [fock, ← monomial_zero', support_monomial, if_neg hr, Finset.sum_singleton, coeff_monomial, if_pos rfl,
      fockMono_zero, smul_eq_C_mul, mul_one, monomial_zero']

theorem deg_lt (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) (hk : s k ≠ 0)
    (t : Fin m × Fin n × Bool →₀ ℕ) (ht : ∀ x, t x ≤ (s - Finsupp.single k 1 : Fin m × Fin n × Bool →₀ ℕ) x) : ∑ x, t x < ∑ x, s x := by
  refine lt_of_le_of_lt (Finset.sum_le_sum fun x _ => ht x) ?_
  refine Finset.sum_lt_sum (fun x _ => by simp) ⟨k, Finset.mem_univ _, ?_⟩
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
  omega

variable (hB : FockBasic)

include hB in
theorem pderiv_fock (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv k (fock c p) = (2 * c : ℂ) • fock c (pderiv (flip k) p) := by
  classical
  obtain ⟨hL, -, hX⟩ := hB m n c hc
  induction p using MvPolynomial.induction_on with
  | C r => rw [fock_C, pderiv_C, pderiv_C, hL.map_zero, smul_zero]
  | add p q hp hq => rw [hL.map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), hL.map_add (f := _), smul_add]
  | mul_X p j hp =>
    rw [mul_comm, hX, pderiv_cr, hp, map_smul, pderiv_mul, pderiv_X, hL.map_add (f := _), hX, Pi.single_apply]
    by_cases h : k = flip j
    · have h' : j = flip k := by rw [h, flip_flip]
      rw [if_pos h, if_pos h', one_mul, smul_add, add_comm]
    · have h' : ¬ j = flip k := fun e => h (by rw [e, flip_flip])
      rw [if_neg h, if_neg h', zero_mul, hL.map_zero, zero_smul, add_zero, zero_add]

variable (hM : OneMom)

include hB hM in
theorem mom_fock_X (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    mom c (fock c (X k * p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
  obtain ⟨hL, -, hX⟩ := hB m n c hc
  have e1 := mom_pderiv hM c hc k (fock c p)
  have e2 : mom c (pderiv k (fock c p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
    rw [pderiv_fock hB c hc, mom_smul]
  rw [hX, cr_apply, mom_add hM c hc, ← neg_one_smul ℂ (pderiv k (fock c p)), mom_smul, mom_smul, ← e2, e1]
  ring

include hB hM in
theorem fockMom_of : FockMom := by
  intro m n c hc
  obtain ⟨hL, -, -⟩ := hB m n c hc
  have h1 : mom c (1 : PX m n) ≠ 0 := by
    rw [← C_1, ← monomial_zero', mom_monomial hM c hc, one_mul, phi]
    refine Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    simp only [Finsupp.coe_zero, Pi.zero_apply, g1, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add,
      pow_one, if_true]
    exact_mod_cast (div_pos Real.pi_pos hc).ne'
  refine ⟨h1, ?_⟩
  let D : PX m n → ℂ := fun p => mom c (fock c p) - mom c (1 : PX m n) * contr c p
  have hDadd : ∀ p q, D (p + q) = D p + D q := by
    intro p q; simp only [D]; rw [hL.map_add (f := _), mom_add hM c hc, contr_add]; ring
  have hDC : ∀ r, D (C r) = 0 := by
    intro r; simp only [D]
    rw [fock_C, contr_C, C_eq_smul_one, mom_smul]; ring
  have hDX : ∀ k p, D (X k * p) = (2 * c : ℂ) * D (pderiv (flip k) p) := by
    intro k p; simp only [D]; rw [mom_fock_X hB hM c hc, contr_X_mul]; ring
  have hmono : ∀ N, ∀ s : Fin m × Fin n × Bool →₀ ℕ, ∑ x, s x = N → ∀ r, D (monomial s r) = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro s hs r
      by_cases h0 : s = 0
      · subst h0; rw [monomial_zero']; exact hDC r
      · obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
        have hk' : s k ≠ 0 := by simpa using hk
        have hs' : Finsupp.single k 1 + (s - Finsupp.single k 1) = s := by
          ext x
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
          split_ifs with hx
          · subst hx; omega
          · simp
        have hXm : monomial s r = (X k : PX m n) * monomial (s - Finsupp.single k 1) r := by
          rw [X, monomial_mul, one_mul, hs']
        rw [hXm, hDX, pderiv_monomial]
        have hlt : ∑ x, ((s - Finsupp.single k 1 - Finsupp.single (flip k) 1 : Fin m × Fin n × Bool →₀ ℕ) x) < N :=
          hs ▸ deg_lt s k hk' _ (fun x => by simp only [Finsupp.coe_tsub, Pi.sub_apply]; exact tsub_le_self)
        rw [ih _ hlt _ rfl, mul_zero]
  intro p
  have hD0 : D p = 0 := by
    induction p using MvPolynomial.induction_on' with
    | monomial s r => exact hmono _ s rfl r
    | add p q hp hq => rw [hDadd, hp, hq, add_zero]
  exact sub_eq_zero.1 hD0

theorem fockMom_of_basic (hB : FockBasic) : FockMom := fockMom_of hB oneMom

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SymKEqZeroOfOm
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

namespace CoreD

variable {m n : ℕ} {ε : Fin m → Bool}

def psi (p q : Sym m n) : ℂ :=
  ∑ u ∈ p.support ∪ q.support, star (p.coeff u) * q.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ)

theorem psi_eq (p q : Sym m n) (T : Finset _) (h : p.support ∪ q.support ⊆ T) :
    psi p q = ∑ u ∈ T, star (p.coeff u) * q.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ) := by
  unfold psi
  refine Finset.sum_subset h fun u _ hu => ?_
  rw [Finset.mem_union, not_or, mem_support_iff, mem_support_iff, not_not, not_not] at hu
  simp [hu.1, hu.2]

theorem psi_add_right (p q₁ q₂ : Sym m n) : psi p (q₁ + q₂) = psi p q₁ + psi p q₂ := by
  classical
  have h0 : (q₁ + q₂).support ⊆ q₁.support ∪ q₂.support := support_add
  rw [psi_eq p (q₁ + q₂) (p.support ∪ q₁.support ∪ q₂.support) (by
      intro u hu; rcases Finset.mem_union.1 hu with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · rcases Finset.mem_union.1 (h0 h) with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
        · exact Finset.mem_union_right _ h'),
    psi_eq p q₁ (p.support ∪ q₁.support ∪ q₂.support) (Finset.union_subset_left le_rfl),
    psi_eq p q₂ (p.support ∪ q₁.support ∪ q₂.support)
      (Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem psi_herm (p q : Sym m n) : psi q p = star (psi p q) := by
  unfold psi
  rw [Finset.union_comm, star_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [star_mul', star_star, star_prod, star_natCast]
  ring

theorem psi_pos (p : Sym m n) (hp : p ≠ 0) : 0 < (psi p p).re := by
  unfold psi
  rw [Finset.union_self, Complex.re_sum]
  have hterm : ∀ u, (star (p.coeff u) * p.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ)).re =
      Complex.normSq (p.coeff u) * ∏ k ∈ u.support, ((u k).factorial : ℝ) := by
    intro u
    have : star (p.coeff u) * p.coeff u = (Complex.normSq (p.coeff u) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [this, show (∏ k ∈ u.support, ((u k).factorial : ℂ)) = ((∏ k ∈ u.support, ((u k).factorial : ℝ) : ℝ) : ℂ) by
      push_cast; rfl, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hterm]
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 (mt support_eq_empty.1 hp)
  refine Finset.sum_pos' (fun v _ => mul_nonneg (Complex.normSq_nonneg _)
    (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)) ⟨u, hu, mul_pos ?_ (Finset.prod_pos fun _ _ => by
      exact_mod_cast Nat.factorial_pos _)⟩
  exact Complex.normSq_pos.2 (mem_support_iff.1 hu)

theorem psi_sum_right {ι : Type*} (p : Sym m n) (F : Finset ι) (f : ι → Sym m n) :
    psi p (∑ x ∈ F, f x) = ∑ x ∈ F, psi p (f x) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [psi]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, psi_add_right, ih]

theorem psi_sum_left {ι : Type*} (p : Sym m n) (F : Finset ι) (f : ι → Sym m n) :
    psi (∑ x ∈ F, f x) p = ∑ x ∈ F, psi (f x) p := by
  rw [psi_herm, psi_sum_right, star_sum]
  exact Finset.sum_congr rfl fun x _ => (psi_herm _ _).symm


variable (ε) in
def Om : Module.End ℂ (Sym m n) :=
  ∑ ij : Fin n × Fin n, (symK ε ij.1 ij.2).toLinearMap * (symK ε ij.2 ij.1).toLinearMap

theorem Om_apply (s : Sym m n) : Om ε s = ∑ ij : Fin n × Fin n, symK ε ij.1 ij.2 (symK ε ij.2 ij.1 s) := by
  simp [Om, LinearMap.sum_apply]

theorem Om_mem {N : ℕ} {s : Sym m n} (hs : s ∈ S ε N) : Om ε s ∈ S ε N := by
  rw [Om_apply]
  exact Submodule.sum_mem _ fun ij _ => symK_mem _ _ (symK_mem _ _ hs)


variable (ε) in
def OmS (N : ℕ) : Module.End ℂ (S (n := n) ε N) := (Om ε).restrict fun _ hs => Om_mem hs

section adj

variable (hadj : ∀ (i j : Fin n) (s t : Sym m n), psi (symK ε i j s) t = psi s (symK ε j i t))
include hadj

theorem psi_Om (a b : Sym m n) : psi (Om ε a) b = psi a (Om ε b) := by
  rw [Om_apply, Om_apply, psi_sum_left, psi_sum_right]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [hadj, ← hadj ij.2 ij.1]

theorem psi_Om_diag (a : Sym m n) : psi a (Om ε a) = ∑ ij : Fin n × Fin n, psi (symK ε ij.2 ij.1 a) (symK ε ij.2 ij.1 a) := by
  rw [Om_apply, psi_sum_right]
  exact Finset.sum_congr rfl fun ij _ => (hadj ij.2 ij.1 a _).symm

theorem symK_eq_zero_of_Om (a : Sym m n) (h : Om ε a = 0) (i j : Fin n) : symK ε i j a = 0 := by
  have h0 := psi_Om_diag hadj a
  rw [h, show psi a 0 = 0 by simp [psi]] at h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hnn : ∀ ij ∈ (Finset.univ : Finset (Fin n × Fin n)),
      0 ≤ (psi (symK ε ij.2 ij.1 a) (symK ε ij.2 ij.1 a)).re := fun ij _ => by
    by_cases hz : symK ε ij.2 ij.1 a = 0
    · rw [hz]; simp [psi]
    · exact (psi_pos _ hz).le
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre.symm (j, i) (Finset.mem_univ _)
  by_contra hz
  exact (psi_pos _ hz).ne' this

theorem ker_inf_range {N : ℕ} (v : S (n := n) ε N) (h0 : OmS ε N v = 0) (h1 : ∃ u, OmS ε N u = v) : v = 0 := by
  obtain ⟨u, rfl⟩ := h1
  have h0' : Om ε (OmS ε N u).1 = 0 := congrArg Subtype.val h0
  have : psi (OmS ε N u).1 (OmS ε N u).1 = 0 := by
    change psi (Om ε u.1) (Om ε u.1) = 0
    rw [psi_Om hadj]
    change psi u.1 (Om ε (OmS ε N u).1) = 0
    rw [h0']; simp [psi]
  by_contra hne
  have hne' : (OmS ε N u).1 ≠ 0 := fun h => hne (Subtype.ext h)
  exact (psi_pos _ hne').ne' (by rw [this]; simp)

theorem pow_kill {N : ℕ} (k : ℕ) (v : S (n := n) ε N) (h : (OmS ε N ^ (k + 1)) v = 0) : OmS ε N v = 0 := by
  induction k generalizing v with
  | zero => simpa using h
  | succ k ih =>
    have h' : (OmS ε N ^ (k + 1)) (OmS ε N v) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ]; exact h
    exact ker_inf_range hadj _ (ih _ h') ⟨v, rfl⟩

theorem exists_q (N : ℕ) : ∃ q : Polynomial ℂ, q.eval 0 = 1 ∧ ∀ v, OmS ε N (Polynomial.aeval (OmS (n := n) ε N) q v) = 0 := by
  set T := OmS (n := n) ε N
  have hp : T.charpoly ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  obtain ⟨g, hpg, hg⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd _ hp 0
  rw [map_zero, sub_zero] at hpg hg
  have hg0 : g.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]; exact fun h => hg (Polynomial.X_dvd_iff.2 h)
  refine ⟨Polynomial.C (g.eval 0)⁻¹ * g, by simp [hg0], fun v => ?_⟩
  have hz : (Polynomial.aeval T T.charpoly) v = 0 := by rw [LinearMap.aeval_self_charpoly]; rfl
  rw [hpg, map_mul, map_pow, Polynomial.aeval_X, Module.End.mul_apply] at hz
  rw [map_mul, Module.End.mul_apply, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, map_smul]
  rcases Nat.eq_zero_or_pos (Polynomial.rootMultiplicity 0 T.charpoly) with hk | hk
  · rw [hk, pow_zero, Module.End.one_apply] at hz
    rw [hz, map_zero, smul_zero]
  · obtain ⟨k, hk'⟩ := Nat.exists_eq_add_of_lt hk
    rw [hk', zero_add] at hz
    rw [pow_kill hadj k _ hz, smul_zero]

end adj

end CoreD

end PositivityTheory.Rg.Sw.LC
end
end

