module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.BfSmulRight
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoeffSmulX
section
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem fform_eq_gf (c : ℝ) (p q : PX m n) : fform c p q = gf (fun s => (wt c s : ℂ)) p q := rfl

theorem wt_univ (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    wt c s = ∏ k, ((s k).factorial : ℝ) * (2 * c) ^ (s k) := by
  unfold wt
  refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
  have : s k = 0 := by simpa [Finsupp.mem_support_iff] using hk
  simp [this]

theorem wt_pos {c : ℝ} (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) : 0 < wt c s := by
  rw [wt_univ]
  exact Finset.prod_pos fun k _ => mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (by linarith) _)

theorem wt_step (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (wt c (Finsupp.single k 1 + s) : ℂ) = ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (wt c s : ℂ) := by
  have h : wt c (Finsupp.single k 1 + s) = (2 * c) * ((s k : ℝ) + 1) * wt c s := by
    rw [wt_univ, wt_univ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun j => ((s j).factorial : ℝ) * (2 * c) ^ (s j)) (Finset.mem_univ k)]
    have hrest : ∏ j ∈ Finset.univ.erase k, (((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j).factorial : ℝ) *
          (2 * c) ^ ((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j) =
        ∏ j ∈ Finset.univ.erase k, ((s j).factorial : ℝ) * (2 * c) ^ (s j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjk : j ≠ k := Finset.ne_of_mem_erase hj
      simp [Finsupp.single_apply, Ne.symm hjk]
    rw [hrest]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [add_comm 1 (s k), Nat.factorial_succ, pow_succ]
    push_cast; ring
  rw [h]; push_cast; ring

theorem KopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), X (a, i, false) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), X (a, j, true) * pderiv (a, i, true) p := by
  simp [KopL, LinearMap.sub_apply, LinearMap.sum_apply]

theorem rdeg_add (ε : Fin m → Bool) (s t : Fin m × Fin n × Bool →₀ ℕ) : rdeg ε (s + t) = rdeg ε s + rdeg ε t := by
  funext a; simp [rdeg, Finset.sum_add_distrib]

theorem rdeg_single (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) (hk : inF1 ε k) :
    rdeg ε (Finsupp.single k 1) = fun a => if a = k.1 then 1 else 0 := by
  funext a
  unfold rdeg
  obtain ⟨a0, i0, b0⟩ := k
  simp only [inF1] at hk
  subst hk
  by_cases ha : a = a0
  · subst ha
    rw [if_pos rfl, Finset.sum_eq_single i0]
    · simp
    · intro i _ hi; simp [Finsupp.single_apply, Ne.symm hi]
    · simp
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h; exact ha (congrArg Prod.fst h).symm

theorem term_mem_box (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) (k l : Fin m × Fin n × Bool)
    (hk : inF1 ε k) (hl : inF1 ε l) (hkl : k.1 = l.1) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) :
    X k * pderiv l (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [pderiv_monomial, X, monomial_mul, one_mul, one_mul]
  by_cases h0 : s l = 0
  · simp [h0]
  · rw [show (monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) ((s l : ℕ) : ℂ) : PX m n) =
        ((s l : ℕ) : ℂ) • monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) (1 : ℂ) by
        rw [smul_monomial, smul_eq_mul, mul_one]]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun k' hk' => ?_, ?_, rfl⟩)
    · rcases Finset.mem_union.mp (Finsupp.support_add hk') with h | h
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h; rw [h]; exact hk
      · exact hs k' (Finsupp.support_tsub h)
    · have hle : Finsupp.single l 1 ≤ s := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      have e1 : rdeg ε (Finsupp.single k 1) = rdeg ε (Finsupp.single l 1) := by
        rw [rdeg_single ε k hk, rdeg_single ε l hl, hkl]
      rw [rdeg_add, e1, ← rdeg_add, add_tsub_cancel_of_le hle]
      exact hR

theorem gen_stable (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) : KopL ε i j (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [KopL_apply]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun a ha => ?_) (Submodule.sum_mem _ fun a ha => ?_)
  · have ha' : ε a = true := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, i, false) (a, j, false) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR
  · have ha' : ε a = false := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, j, true) (a, i, true) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR

theorem box_stable (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) :
    ∀ f ∈ box (n := n) ε R, KopL ε i j f ∈ box ε R := by
  intro f hf
  refine Submodule.span_induction (p := fun x _ => KopL ε i j x ∈ box ε R) ?_ ?_ ?_ ?_ hf
  · rintro x ⟨s, hs, hR, rfl⟩
    exact gen_stable ε i j R s hs hR
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ r hx

def symW (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) : ℂ := ∏ k ∈ u.support, ((u k).factorial : ℂ)

theorem symW_step (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (k) :
    symW (Finsupp.single k 1 + u) = 1 * ((u k : ℂ) + 1) * symW u := by
  have hu : ∀ v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ,
      symW v = ∏ k, ((v k).factorial : ℂ) := fun v => by
    unfold symW
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
    have : v k = 0 := by simpa [Finsupp.mem_support_iff] using hk
    simp [this]
  rw [hu, hu, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun j => ((u j).factorial : ℂ)) (Finset.mem_univ k)]
  have hrest : ∏ j ∈ Finset.univ.erase k,
      (((Finsupp.single k 1 + u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) j).factorial : ℂ) =
      ∏ j ∈ Finset.univ.erase k, ((u j).factorial : ℂ) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    simp [Finsupp.single_apply, Ne.symm hjk]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm 1 (u k), Nat.factorial_succ]
  push_cast; ring

theorem coeff_smul_X {τ : Type} [DecidableEq τ] (c : ℂ) (w0 u : τ) :
    (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) = if w0 = u then c else 0 := by
  rw [coeff_smul, coeff_X']
  by_cases h : w0 = u
  · subst h; simp
  · rw [if_neg (fun e => h ((Finsupp.single_left_inj one_ne_zero).mp e)), if_neg h]; simp

theorem expand_lin {τ : Type} [Fintype τ] [DecidableEq τ] (c : ℂ) (w0 : τ) :
    (c • X w0 : MvPolynomial τ ℂ) = ∑ u, (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) • X u := by
  simp_rw [coeff_smul_X, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]; simp

theorem symK_lin (ε : Fin m → Bool) (i j : Fin n) (v) :
    ∃ (c : ℂ) (w0 : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)), symK ε i j (X v : Sym m n) = c • X w0 := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;>
    first
    | exact ⟨1, _, (one_smul _ _).symm⟩
    | exact ⟨-1, _, by rw [neg_smul, one_smul]⟩
    | exact ⟨0, Sum.inl (a, i', b), (zero_smul _ _).symm⟩

theorem symK_hlin (ε : Fin m → Bool) (i j : Fin n) (v) :
    symK ε i j (X v : Sym m n) = ∑ u, (symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1) • X u := by
  obtain ⟨c, w0, h⟩ := symK_lin ε i j v
  rw [h]; exact expand_lin c w0

theorem symK_tr (ε : Fin m → Bool) (i j : Fin n) (v u) :
    (symK ε j i (X u : Sym m n)).coeff (Finsupp.single v 1) = star ((symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1)) := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> rcases u with ⟨a', i'', b'⟩ | ⟨a', i'', b'⟩ <;>
    simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;> simp_all [coeff_X', Finsupp.single_left_inj, coeff_neg] <;> aesop

end CoreC

open CoreC CoreC.G in
theorem formFacts : FormFacts := by
  intro m n ε c hc
  have hw : ∀ (s : Fin m × Fin n × Bool →₀ ℕ) k, (fun s => (wt c s : ℂ)) (Finsupp.single k 1 + s) =
      ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (fun s => (wt c s : ℂ)) s := fun s k => wt_step c s k
  have hst : ∀ s : Fin m × Fin n × Bool →₀ ℕ, star ((fun s => (wt c s : ℂ)) s) = (fun s => (wt c s : ℂ)) s :=
    fun s => Complex.conj_ofReal _
  have hpos : ∀ s : Fin m × Fin n × Bool →₀ ℕ, 0 < ((fun s => (wt c s : ℂ)) s).re := fun s => by
    simpa using wt_pos hc s
  refine ⟨fun p q => gf_herm _ hst p q, fun p hp => gf_pos _ hst hpos p hp, fun i j p q => ?_,
    fun i j R f hf => box_stable ε i j R f hf, fun i j s t => ⟨by simp [fform], ?_⟩⟩
  · rw [fform_eq_gf, fform_eq_gf, KopL_apply, KopL_apply, gf_sub_left, gf_sub_right, gf_sum_left, gf_sum_left,
      gf_sum_right, gf_sum_right]
    congr 1 <;> exact Finset.sum_congr rfl fun a _ => gf_adj _ hw _ _ _ _
  · exact der_adj (w := symW) 1 symW_step (symK ε i j) (symK ε j i) (symK_hlin ε i j) (symK_hlin ε j i)
      (symK_tr ε i j) s t

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ComapDomainInlAdd
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev Ix (m n : ℕ) := Fin m × Fin n × Bool

abbrev Dk (k : Ix m n) : Module.End ℂ (PX m n) := (pderiv (R := ℂ) k).toLinearMap

theorem pderiv_comm (i j : Ix m n) (p : PX m n) : pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    have hc : ∀ a b : Ix m n, pderiv a (pderiv b (X k : PX m n)) = 0 := by
      intro a b; rw [pderiv_X]; by_cases h : b = k
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [pderiv_mul, map_add (f := _), hp, hc, mul_zero, add_zero]
    ring

theorem dk_comm (i j : Ix m n) : Commute (Dk i) (Dk j) :=
  LinearMap.ext fun p => pderiv_comm i j p

def dvE (e : Ix m n → ℕ) : Module.End ℂ (PX m n) :=
  ((Finset.univ : Finset (Ix m n)).toList.map fun k => Dk k ^ e k).prod

theorem list_dv_mul (l : List (Ix m n)) (a b : Ix m n → ℕ) :
    (l.map fun k => Dk k ^ a k).prod * (l.map fun k => Dk k ^ b k).prod = (l.map fun k => Dk k ^ (a k + b k)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    have hc : Commute (l.map fun k => Dk k ^ a k).prod (Dk x ^ b x) := by
      apply Commute.symm
      apply Commute.list_prod_right
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨z, -, rfl⟩ := hy
      exact ((dk_comm x z).pow_pow _ _)
    calc Dk x ^ a x * (l.map fun k => Dk k ^ a k).prod * (Dk x ^ b x * (l.map fun k => Dk k ^ b k).prod)
        = Dk x ^ a x * ((l.map fun k => Dk k ^ a k).prod * Dk x ^ b x) * (l.map fun k => Dk k ^ b k).prod := by
          simp only [mul_assoc]
      _ = Dk x ^ a x * (Dk x ^ b x * (l.map fun k => Dk k ^ a k).prod) * (l.map fun k => Dk k ^ b k).prod := by
          rw [hc.eq]
      _ = Dk x ^ (a x + b x) * ((l.map fun k => Dk k ^ a k).prod * (l.map fun k => Dk k ^ b k).prod) := by
          simp only [pow_add, mul_assoc]
      _ = _ := by rw [ih]

theorem dvE_mul (a b : Ix m n → ℕ) : dvE a * dvE b = dvE (a + b) := by
  unfold dvE; rw [list_dv_mul]; rfl

theorem dvE_single (k : Ix m n) : dvE (Pi.single k 1) = Dk k := by
  unfold dvE
  rw [List.prod_map_eq_pow_single k]
  · simp only [Pi.single_eq_same, pow_one]
    convert pow_one (Dk k)
    exact @List.count_eq_one_of_mem _ instBEqOfDecidableEq inferInstance _ _ (Finset.nodup_toList _)
      (Finset.mem_toList.2 (Finset.mem_univ k))
  · intro a' ha' _
    simp [Pi.single_apply, ha']

theorem opMono_eq (t : Ix m n ⊕ Ix m n →₀ ℕ) (f : PX m n) :
    opMono t f = monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn) 1 * dvE (fun k => t (Sum.inr k)) f := rfl

theorem opMono_add (t : Ix m n ⊕ Ix m n →₀ ℕ) (f g : PX m n) : opMono t (f + g) = opMono t f + opMono t g := by
  simp only [opMono_eq, map_add (f := _), mul_add]

theorem opMono_smul (t : Ix m n ⊕ Ix m n →₀ ℕ) (a : ℂ) (f : PX m n) : opMono t (a • f) = a • opMono t f := by
  simp only [opMono_eq, map_smul, mul_smul_comm]

theorem op_eq_of_subset (s : Sym m n) (S : Finset (Ix m n ⊕ Ix m n →₀ ℕ)) (h : s.support ⊆ S) (f : PX m n) :
    op s f = ∑ t ∈ S, s.coeff t • opMono t f := by
  unfold op
  apply Finset.sum_subset h
  intro t _ ht
  rw [MvPolynomial.notMem_support_iff.1 ht, zero_smul]

theorem op_add (u v : Sym m n) (f : PX m n) : op (u + v) f = op u f + op v f := by
  classical
  rw [op_eq_of_subset (u + v) (u.support ∪ v.support) MvPolynomial.support_add,
    op_eq_of_subset u (u.support ∪ v.support) Finset.subset_union_left,
    op_eq_of_subset v (u.support ∪ v.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [MvPolynomial.coeff_add, add_smul]

theorem op_smul (a : ℂ) (u : Sym m n) (f : PX m n) : op (a • u) f = a • op u f := by
  classical
  rw [op_eq_of_subset (a • u) u.support MvPolynomial.support_smul, op, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [coeff_smul, smul_eq_mul, mul_smul]

theorem op_zero (f : PX m n) : op (0 : Sym m n) f = 0 := by simp [op]

theorem op_sum {ι : Type*} (S : Finset ι) (u : ι → Sym m n) (f : PX m n) : op (∑ i ∈ S, u i) f = ∑ i ∈ S, op (u i) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [op_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add, ih]

theorem op_monomial (t : Ix m n ⊕ Ix m n →₀ ℕ) (a : ℂ) (f : PX m n) : op (monomial t a) f = a • opMono t f := by
  classical
  rw [op_eq_of_subset _ {t} (MvPolynomial.support_monomial_subset), Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem op_add_f (u : Sym m n) (f g : PX m n) : op u (f + g) = op u f + op u g := by
  simp only [op, opMono_add, smul_add, Finset.sum_add_distrib]

theorem op_smul_f (u : Sym m n) (a : ℂ) (f : PX m n) : op u (a • f) = a • op u f := by
  simp only [op, opMono_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_comm]

theorem op_zero_f (u : Sym m n) : op u 0 = 0 := by simp [op, opMono_eq]

theorem dvE_zero : dvE (0 : Ix m n → ℕ) = 1 := by
  unfold dvE; simp

theorem op_C (a : ℂ) (f : PX m n) : op (C a : Sym m n) f = a • f := by
  rw [← monomial_zero', op_monomial, opMono_eq]
  have h0 : (fun k : Ix m n => (0 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) = 0 := by ext; simp
  rw [h0, dvE_zero, Finsupp.comapDomain_zero]
  simp

theorem comapDomain_inl_add (t s : Ix m n ⊕ Ix m n →₀ ℕ) :
    (t + s).comapDomain Sum.inl Sum.inl_injective.injOn =
      t.comapDomain Sum.inl Sum.inl_injective.injOn + s.comapDomain Sum.inl Sum.inl_injective.injOn := by
  ext k; simp [Finsupp.comapDomain_apply]

theorem opMono_add_inl (t : Ix m n ⊕ Ix m n →₀ ℕ) (k : Ix m n) (f : PX m n) :
    opMono (t + Finsupp.single (Sum.inl k) 1) f = X k * opMono t f := by
  rw [opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (Finsupp.single (Sum.inl k) 1 : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn =
      Finsupp.single k 1 := by
    ext j; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
  have h2 : (fun j : Ix m n => (t + Finsupp.single (Sum.inl k) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr j)) = fun j => t (Sum.inr j) := by
    ext j; simp [Finsupp.single_apply]
  rw [h1, h2, monomial_add_single, pow_one]
  ring

theorem opMono_add_inr (t : Ix m n ⊕ Ix m n →₀ ℕ) (k : Ix m n) (f : PX m n) :
    opMono (t + Finsupp.single (Sum.inr k) 1) f = opMono t (pderiv k f) := by
  rw [opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (Finsupp.single (Sum.inr k) 1 : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn = 0 := by
    ext j; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
  have h2 : (fun j : Ix m n => (t + Finsupp.single (Sum.inr k) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr j)) =
      (fun j => t (Sum.inr j)) + Pi.single k 1 := by
    ext j; simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [h1, add_zero, h2, ← dvE_mul, dvE_single]
  rfl

theorem op_mul_inl (u : Sym m n) (k : Ix m n) (f : PX m n) : op (u * X (Sum.inl k)) f = X k * op u f := by
  classical
  conv_lhs => rw [u.as_sum, Finset.sum_mul]
  rw [op_sum]
  conv_rhs => rw [op, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [X, monomial_mul, mul_one, op_monomial, opMono_add_inl, mul_smul_comm]

theorem op_mul_inr (u : Sym m n) (k : Ix m n) (f : PX m n) : op (u * X (Sum.inr k)) f = op u (pderiv k f) := by
  classical
  conv_lhs => rw [u.as_sum, Finset.sum_mul]
  rw [op_sum]
  conv_rhs => rw [op]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [X, monomial_mul, mul_one, op_monomial, opMono_add_inr]

theorem op_X_mul (u : Sym m n) : ∀ (k : Ix m n) (g : PX m n),
    op u (X k * g) = X k * op u g + op (pderiv (Sum.inr k) u) g := by
  induction u using MvPolynomial.induction_on with
  | C a => intro k g; simp [op_C, op_zero, mul_smul_comm]
  | add p q hp hq => intro k g; rw [op_add, op_add, hp, hq, map_add (f := _), op_add]; ring
  | mul_X p j hp =>
    intro k g
    rcases j with j | j
    · rw [op_mul_inl, op_mul_inl, hp, pderiv_mul, pderiv_X, op_add, op_mul_inl]
      simp only [Pi.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, mul_zero, op_zero, add_zero]
      ring
    · rw [op_mul_inr, op_mul_inr, pderiv_mul, pderiv_mul, pderiv_X, pderiv_X, op_add_f, op_add, hp, op_mul_inr]
      by_cases h : j = k
      · subst h
        simp only [Pi.single_apply, if_true, mul_one, one_mul]
        ring
      · have h' : (Sum.inr k : Ix m n ⊕ Ix m n) ≠ Sum.inr j := fun e => h (Sum.inr_injective e).symm
        have e1 : ¬ (k = j) := fun e => h e.symm
        have e2 : ¬ ((Sum.inr j : Ix m n ⊕ Ix m n) = Sum.inr k) := fun e => h (Sum.inr_injective e)
        simp only [Pi.single_apply, e1, e2, if_false, zero_mul, mul_zero, op_zero, add_zero, op_zero_f, zero_add]

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FformSmulRight
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def cw (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ :=
  if ∀ a i, s (a, i, false) = s (a, i, true) then
    ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0

theorem contr_eq_sum (c : ℝ) (p : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, p.coeff s * cw c s := by
  unfold contr cw
  rw [← Finset.sum_subset hS]
  · refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  · intro s _ hs
    rw [MvPolynomial.notMem_support_iff.mp hs]
    simp

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eq_sum c (p + q) (p.support ∪ q.support) support_add,
    contr_eq_sum c p (p.support ∪ q.support) Finset.subset_union_left,
    contr_eq_sum c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem contr_smul (c : ℝ) (r : ℂ) (p : PX m n) : contr c (r • p) = r * contr c p := by
  classical
  rw [contr_eq_sum c (r • p) p.support (support_smul), contr_eq_sum c p p.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_smul, smul_eq_mul, mul_assoc]

def contrL (c : ℝ) : PX m n →ₗ[ℂ] ℂ where
  toFun := contr c
  map_add' := contr_add c
  map_smul' := contr_smul c

theorem fform_eq_sum (c : ℝ) (p q : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ∪ q.support ⊆ S) :
    fform c p q = ∑ s ∈ S, star (p.coeff s) * q.coeff s * (wt c s : ℂ) := by
  unfold fform
  rw [← Finset.sum_subset hS]
  intro s _ hs
  have h1 : p.coeff s = 0 := MvPolynomial.notMem_support_iff.mp fun h => hs (Finset.mem_union_left _ h)
  simp [h1]

theorem fform_add_right (c : ℝ) (p q₁ q₂ : PX m n) : fform c p (q₁ + q₂) = fform c p q₁ + fform c p q₂ := by
  classical
  set S := p.support ∪ q₁.support ∪ q₂.support
  rw [fform_eq_sum c p (q₁ + q₂) S (Finset.union_subset (by intro x hx; simp [S, hx]) (fun x hx => by
      have := support_add hx; simp only [S, Finset.mem_union] at this ⊢; tauto)),
    fform_eq_sum c p q₁ S (Finset.union_subset (by intro x hx; simp [S, hx]) (by intro x hx; simp [S, hx])),
    fform_eq_sum c p q₂ S (Finset.union_subset (by intro x hx; simp [S, hx]) (by intro x hx; simp [S, hx])),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fform_smul_right (c : ℝ) (p q : PX m n) (r : ℂ) : fform c p (r • q) = r * fform c p q := by
  classical
  rw [fform_eq_sum c p (r • q) (p.support ∪ q.support) (Finset.union_subset Finset.subset_union_left
      (support_smul.trans Finset.subset_union_right)),
    fform_eq_sum c p q (p.support ∪ q.support) le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring

end PositivityTheory.Rg.Sw.LC.Core
end
end

