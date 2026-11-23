module

public import ReciprocityTheory.DualLattices.IsUnitOfNotMem
public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.EigPowEqOne
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem smul_cancel (hv : v.Integers R) {n : Type} {e : Matrix n n R} (he : e ≠ 0) {x y : R}
    (h : x • e = y • e) : x = y := by
  obtain ⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact he (Matrix.ext hc)
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  have h2 := congrArg (algebraMap R C) h1
  rw [map_mul, map_mul] at h2
  have hne : algebraMap R C (e i j) ≠ 0 := by
    intro h0
    rw [← map_zero (algebraMap R C)] at h0
    exact hij (hv.hom_inj h0)
  exact hv.hom_inj (mul_right_cancel₀ hne h2)

theorem eig_pow_eq_one (hv : v.Integers R) {p : ℕ} [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n]
    [Algebra ℤ_[p] R] (N : Matrix n n ℤ_[p]) (e : Matrix n n R) (he : e ≠ 0) (x : R)
    (h : N.map (algebraMap ℤ_[p] R) * e = x • e) {m : ℕ} (hN : N ^ m = 1) : x ^ m = 1 := by
  have hpow : ∀ k : ℕ, (N.map (algebraMap ℤ_[p] R)) ^ k * e = x ^ k • e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, h, Matrix.mul_smul, ih, smul_smul, ← pow_succ']
  have hN' : (N.map (algebraMap ℤ_[p] R)) ^ m = 1 := by
    have := congrArg (algebraMap ℤ_[p] R).mapMatrix hN
    rwa [map_pow, map_one, RingHom.mapMatrix_apply] at this
  have h1 := hpow m
  rw [hN', one_mul] at h1
  exact (smul_cancel hv he (by rw [one_smul]; exact h1)).symm

theorem fermat (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] (z : ℤ_[p]) :
    res hv (algebraMap ℤ_[p] R z) ^ p = res hv (algebraMap ℤ_[p] R z) := by
  have hz : z ^ p - z ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
      ZMod.pow_card, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hz
  have hp0 : res hv (p : R) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hpv
  have h0 : res hv (algebraMap ℤ_[p] R (z ^ p - z)) = 0 := by
    rw [← hw, map_mul, map_mul, map_natCast (algebraMap ℤ_[p] R), hp0, mul_zero]
  rw [map_sub, map_sub, map_pow, map_pow, sub_eq_zero] at h0
  exact h0

theorem proj (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [CommGroup G] [Fintype G] (hG : IsUnit (Fintype.card G : R))
    (A : G → Matrix n n ℤ_[p]) (hA : ∀ γ γ', A (γ * γ') = A γ * A γ') (hA1 : A 1 = 1)
    (εT : ι → Matrix n n R) (horth : ∀ i j, εT i * εT j = if i = j then εT i else 0)
    (hsum : ∑ i, εT i = 1) (ψ : ι → G → R)
    (heig : ∀ j γ, (A γ).map (algebraMap ℤ_[p] R) * εT j = ψ j γ • εT j)
    (hsep : ∀ j k, εT j ≠ 0 → εT k ≠ 0 → j ≠ k → ∃ γ, ψ j γ ≠ ψ k γ)
    (i : ι) (hi : εT i ≠ 0) : ∃ j, εT j ≠ 0 ∧ ∀ γ, ψ j γ = ψ i γ ^ p := by
  classical
  have hApow : ∀ γ (k : ℕ), A (γ ^ k) = A γ ^ k := by
    intro γ k
    induction k with
    | zero => simp [hA1]
    | succ k ih => rw [pow_succ, hA, ih, pow_succ]
  have hmul : ∀ j, εT j ≠ 0 → ∀ γ γ', ψ j (γ * γ') = ψ j γ * ψ j γ' := by
    intro j hj γ γ'
    apply smul_cancel hv hj
    have e1 := heig j (γ * γ')
    rw [hA, Matrix.map_mul, Matrix.mul_assoc, heig j γ', Matrix.mul_smul, heig j γ, smul_smul] at e1
    rw [← e1, mul_comm (ψ j γ')]
  have hn1 : 1 ≤ Fintype.card G := Fintype.card_pos
  have hpowG : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ Fintype.card G = 1 := fun j hj γ =>
    eig_pow_eq_one hv (A γ) (εT j) hj (ψ j γ) (heig j γ) (by rw [← hApow, pow_card_eq_one, hA1])
  have hiv : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ (Fintype.card G - 1) * ψ j γ = 1 := by
    intro j hj γ
    rw [← pow_succ, Nat.sub_add_cancel hn1, hpowG j hj γ]
  have hsum0 : ∀ χ : G → R, (∀ γ γ', χ (γ * γ') = χ γ * χ γ') → ∀ γ0, χ γ0 ≠ 1 →
      ∑ γ, χ γ = 0 := by
    intro χ hχ γ0 h0
    have e : ∑ γ, χ γ = χ γ0 * ∑ γ, χ γ := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_bijective (γ0 * ·) (Group.mulLeft_bijective γ0) (fun γ => χ γ0 * χ γ) χ
        (fun γ => (hχ γ0 γ).symm)).symm
    have e2 : (1 - χ γ0) * ∑ γ, χ γ = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    have e3 := congrArg (algebraMap R C) e2
    rw [map_mul, map_zero] at e3
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd (sub_eq_zero.mp (hv.hom_inj (h.trans (map_zero _).symm))).symm h0
    · exact hv.hom_inj (h.trans (map_zero _).symm)
  have hPe : ∀ (c : G → R) j, (∑ γ, c γ • (A γ).map (algebraMap ℤ_[p] R)) * εT j =
      (∑ γ, c γ * ψ j γ) • εT j := by
    intro c j
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Matrix.smul_mul, heig, smul_smul]
  have hdecomp : ∀ M : Matrix n n R, M = ∑ j, M * εT j := fun M => by
    rw [← Finset.mul_sum, hsum, Matrix.mul_one]
  by_contra hcon
  push_neg at hcon
  have hP'0 : (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R)) = 0 := by
    rw [hdecomp (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R))]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : εT j = 0
    · rw [hj, Matrix.mul_zero]
    · rw [hPe (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p) j]
      obtain ⟨γ0, hγ0⟩ := hcon j hj
      have hz := hsum0 (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p * ψ j γ)
        (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by
          intro h1
          apply hγ0
          try simp only at h1
          calc ψ j γ0 = (ψ i γ0 ^ (Fintype.card G - 1) * ψ i γ0) ^ p * ψ j γ0 := by
                rw [hiv i hi, one_pow, one_mul]
            _ = ((ψ i γ0 ^ (Fintype.card G - 1)) ^ p * ψ j γ0) * ψ i γ0 ^ p := by ring
            _ = ψ i γ0 ^ p := by rw [h1, one_mul])
      try simp only at hz
      rw [hz, zero_smul]
  have hPi : (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) =
      (Fintype.card G : R) • εT i := by
    rw [hdecomp (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)),
      Finset.sum_eq_single i]
    · rw [hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) i]
      simp only [hiv i hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · intro j _ hji
      by_cases hj : εT j = 0
      · rw [hj, Matrix.mul_zero]
      · rw [hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) j]
        obtain ⟨γ0, hγ0⟩ := hsep j i hj hi hji
        have hz := hsum0 (fun γ => ψ i γ ^ (Fintype.card G - 1) * ψ j γ)
          (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by
            intro h1
            apply hγ0
            try simp only at h1
            calc ψ j γ0 = (ψ i γ0 ^ (Fintype.card G - 1) * ψ i γ0) * ψ j γ0 := by
                  rw [hiv i hi, one_mul]
              _ = (ψ i γ0 ^ (Fintype.card G - 1) * ψ j γ0) * ψ i γ0 := by ring
              _ = ψ i γ0 := by rw [h1, one_mul])
        try simp only at hz
        rw [hz, zero_smul]
    · simp
  obtain ⟨a, b, hab⟩ : ∃ a b, εT i a b ∉ mI hv := by
    by_contra hc
    push_neg at hc
    exact hi (idem_eq_zero hv (εT i) (by rw [horth, if_pos rfl]) hc)
  haveI := charP p hv hpv
  have hfrob : res hv ((∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p •
      (A γ).map (algebraMap ℤ_[p] R)) a b) =
      res hv ((∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) a b) ^ p := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum, map_mul,
      map_pow]
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [mul_pow, fermat p hv hpv]
  have hres_n : res hv (Fintype.card G : R) ≠ 0 := by
    intro h0
    have h1 : IsUnit (res hv (Fintype.card G : R)) := hG.map (res hv)
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hres_e : res hv (εT i a b) ≠ 0 := by
    intro h0
    exact hab (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  rw [hP'0, hPi] at hfrob
  simp only [Matrix.zero_apply, map_zero, Matrix.smul_apply, smul_eq_mul, map_mul] at hfrob
  exact pow_ne_zero p (mul_ne_zero hres_n hres_e) hfrob.symm

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
section
noncomputable section

open Ideal

namespace ReciprocityTheory.PGsh

variable {p : ℕ} [hp : Fact p.Prime]

section Untilt

variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

private lemma pow_p_pow_eq (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) (n : ℕ) :
    f n ^ p ^ n = f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, hf, ih]

lemma untilt_eq_of_coeff (x : PreTilt O p) (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n)
    (hx : ∀ n, Perfection.coeff (ModP O p) p n x = Ideal.Quotient.mk (span {(p : O)}) (f n)) :
    x.untilt = f 0 := by
  show Perfection.teichmuller p (span {(p : O)}) x = f 0
  exact Perfection.teichmuller_spec fun n => ⟨f n, (hx n).symm, by rw [pow_p_pow_eq f hf n]⟩

def ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) : PreTilt O p :=
  ⟨fun n => Ideal.Quotient.mk (span {(p : O)}) (f n), fun n => by
    show (Ideal.Quotient.mk (span {(p : O)}) (f (n + 1))) ^ p = _
    rw [← map_pow, hf]⟩

lemma coeff_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) (n : ℕ) :
    Perfection.coeff (ModP O p) p n (ofRoots f hf) = Ideal.Quotient.mk (span {(p : O)}) (f n) :=
  rfl

lemma untilt_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) :
    (ofRoots f hf).untilt = f 0 :=
  untilt_eq_of_coeff _ f hf (coeff_ofRoots f hf)

lemma untilt_symm_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) :
    ((_root_.frobeniusEquiv (PreTilt O p) p).symm (ofRoots f hf)).untilt = f 1 := by
  apply untilt_eq_of_coeff _ (fun n => f (n + 1)) (fun n => hf (n + 1))
  intro n
  rw [← PreTilt.coeff_def, PreTilt.coeff_frobeniusEquiv_symm, PreTilt.coeff_def]
  rfl

end Untilt

section Roots

variable (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C]

private lemma le_one_of_pow (hv : v.Integers O) {z : C} {w : O} (h : z ^ p = algebraMap O C w) :
    v z ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have h1 : 1 < v z ^ p := one_lt_pow₀ hlt hp.out.ne_zero
  rw [← map_pow, h] at h1
  exact absurd (hv.map_le_one w) (not_le.2 h1)

lemma exists_root (hv : v.Integers O) (x : O) : ∃ y : O, y ^ p = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos
  obtain ⟨y, rfl⟩ := hv.exists_of_le_one (le_one_of_pow C v O hv hz)
  exact ⟨y, hv.hom_inj (by rw [map_pow, hz])⟩

lemma exists_primitiveRoot [CharZero C] (hv : v.Integers O) :
    ∃ ζ : O, IsPrimitiveRoot ζ p := by
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p C)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p C hp.out.pos))
  have hzp : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.1 hz
  have hz1 : z ^ p = algebraMap O C 1 := by rw [hzp.pow_eq_one, map_one]
  obtain ⟨y, rfl⟩ := hv.exists_of_le_one (le_one_of_pow C v O hv hz1)
  exact ⟨y, (IsPrimitiveRoot.map_iff_of_injective hv.hom_inj).1 hzp⟩

private def rootSeq (r : O → O) (c : O) : ℕ → O
  | 0 => c
  | n + 1 => r (rootSeq r c n)

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem exists_pflat (hv : v.Integers O) : ∃ pflat : PreTilt O p, pflat.untilt = (p : O) := by
  choose r hr using exists_root (p := p) C v O hv
  exact ⟨ofRoots (rootSeq O r p) (fun n => hr _), untilt_ofRoots _ _⟩

theorem exists_eps [CharZero C] (hv : v.Integers O) :
    ∃ ε : PreTilt O p,
      IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p := by
  choose r hr using exists_root (p := p) C v O hv
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot (p := p) C v O hv
  let f : ℕ → O := fun n => Nat.casesOn n 1 (fun m => rootSeq O r ζ m)
  have hf : ∀ n, f (n + 1) ^ p = f n := by
    intro n
    cases n with
    | zero => exact hζ.pow_eq_one
    | succ m => exact hr _
  refine ⟨ofRoots f hf, ?_⟩
  rw [untilt_symm_ofRoots]
  exact hζ

end Roots

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.FischerSmulRight
section
noncomputable section

open MvPolynomial Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

def fw (A : Fin ν × ι →₀ ℕ) : ℂ := ((A.prod fun _ e => e.factorial : ℕ) : ℂ)

private theorem finsupp_prod_factorial_add_single_one (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = B.prod (fun _ e => e.factorial) * (B v + 1) := by
  have hv : v ∈ insert v B.support := Finset.mem_insert_self v B.support
  have h1 : (B + Finsupp.single v 1).support ⊆ insert v B.support := by
    intro x hx
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hx
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hxv : x = v
    · exact Or.inl hxv
    · right
      rwa [if_neg (Ne.symm hxv), add_zero] at hx
  have h2 : B.support ⊆ insert v B.support := Finset.subset_insert v B.support
  have hrest : ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial
      = ∏ x ∈ (insert v B.support).erase v, (B x).factorial := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hx).symm, add_zero]
  calc (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = ∏ x ∈ insert v B.support, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        Finsupp.prod_of_support_subset _ h1 _ (fun _ _ => Nat.factorial_zero)
    _ = ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) v).factorial
          * ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        (Finset.mul_prod_erase _ (fun x => ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial) hv).symm
    _ = (B v).factorial * (∏ x ∈ (insert v B.support).erase v, (B x).factorial) * (B v + 1) := by
        rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]; ring
    _ = (∏ x ∈ insert v B.support, (B x).factorial) * (B v + 1) := by
        rw [← Finset.mul_prod_erase _ _ hv]
    _ = B.prod (fun _ e => e.factorial) * (B v + 1) := by
        rw [Finsupp.prod_of_support_subset _ h2 _ (fun _ _ => Nat.factorial_zero)]

theorem fw_add_single (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    fw (B + Finsupp.single v 1) = fw B * ((B v : ℂ) + 1) := by
  unfold fw
  rw [finsupp_prod_factorial_add_single_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

theorem fischer_eq_sum (P Q : MvPolynomial (Fin ν × ι) ℂ) (S : Finset (Fin ν × ι →₀ ℕ))
    (hS : P.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), P.support ⊆ T →
      ∑ A ∈ T, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A
        = ∑ A ∈ P.support, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : AddMonoidAlgebra.coeff P A = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ P.support, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_left _ hx)
    _ = ∑ A ∈ S, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A := (key S hS).symm

theorem fischer_add_left (P P' Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (P + P') Q = fischer P Q + fischer P' Q := by
  have hsub : (P + P').support ⊆ P.support ∪ P'.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at hA
    rw [Finset.mem_union, MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    rw [h.1, h.2, add_zero] at hA
    exact hA rfl
  rw [fischer_eq_sum (P + P') Q (P.support ∪ P'.support) hsub,
    fischer_eq_sum P Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_left _ hx),
    fischer_eq_sum P' Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_right _ hx),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fischer_smul_left (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (c • P) Q = c * fischer P Q := by
  have hsub : (c • P).support ⊆ P.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul] at hA
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hA
    rw [h, smul_zero]
  rw [fischer_eq_sum (c • P) Q P.support hsub,
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fischer_add_right (P Q Q' : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (Q + Q') = fischer P Q + fischer P Q' := by
  rw [fischer_eq_sum P (Q + Q') P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q' P.support (Finset.Subset.refl _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _)]
  ring

theorem fischer_smul_right (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (c • Q) = starRingEnd ℂ c * fischer P Q := by
  rw [fischer_eq_sum P (c • Q) P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul]
  ring

theorem fischer_sum_right {α : Type*} (s : Finset α) (P : MvPolynomial (Fin ν × ι) ℂ)
    (f : α → MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (∑ i ∈ s, f i) = ∑ i ∈ s, fischer P (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum P 0 P.support (Finset.Subset.refl _)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]

theorem fischer_sum_left {α : Type*} (s : Finset α) (f : α → MvPolynomial (Fin ν × ι) ℂ)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (∑ i ∈ s, f i) Q = ∑ i ∈ s, fischer (f i) Q := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum 0 Q ∅ (by simp)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

theorem fischer_C_left (c : ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (C c) Q = c * starRingEnd ℂ (AddMonoidAlgebra.coeff Q 0) := by
  have hsub : (C c : MvPolynomial (Fin ν × ι) ℂ).support ⊆ {0} := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hA
    rw [Finset.mem_singleton]
    by_contra h
    exact hA (if_neg (fun e => h e.symm))
  rw [fischer_eq_sum (C c) Q {0} hsub, Finset.sum_singleton, MvPolynomial.coeff_C, if_pos rfl]
  simp [fw]

private theorem fischer_eq_sum_of_support_subset (P Q : MvPolynomial (Fin ν × ι) ℂ)
    (S : Finset (Fin ν × ι →₀ ℕ)) (hS : Q.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), Q.support ⊆ T →
      ∑ A ∈ T, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A
        = ∑ A ∈ Q.support, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : AddMonoidAlgebra.coeff Q A = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ Q.support, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_right _ hx)
    _ = ∑ A ∈ S, AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * fw A := (key S hS).symm

private theorem fischer_monomial_right (P : MvPolynomial (Fin ν × ι) ℂ)
    (m : Fin ν × ι →₀ ℕ) (b : ℂ) :
    fischer P (monomial m b) = AddMonoidAlgebra.coeff P m * starRingEnd ℂ b * fw m := by
  rw [fischer_eq_sum_of_support_subset P (monomial m b) {m} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem fischer_mul_X (P Q : MvPolynomial (Fin ν × ι) ℂ) (v : Fin ν × ι) :
    fischer (P * X v) Q = fischer P (pderiv v Q) := by
  induction Q using MvPolynomial.induction_on'
  next m b =>
    rw [MvPolynomial.pderiv_monomial, fischer_monomial_right, fischer_monomial_right,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have hv : m v ≠ 0 := Finsupp.mem_support_iff.1 h
      have hm : m - Finsupp.single v 1 + Finsupp.single v 1 = m := by
        ext x
        rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with hx
        · subst hx
          omega
        · omega
      have hw : fw m = fw (m - Finsupp.single v 1) * (m v : ℂ) := by
        have h1 := fw_add_single (m - Finsupp.single v 1) v
        rw [hm, Finsupp.tsub_apply, Finsupp.single_eq_same,
          Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hv), Nat.cast_one, sub_add_cancel] at h1
        exact h1
      rw [hw, map_mul, map_natCast]
      ring
    · have hv : m v = 0 := by simpa [Finsupp.mem_support_iff] using h
      rw [hv]
      simp
  next Q₁ Q₂ h₁ h₂ =>
    rw [fischer_add_right, map_add (f := _), fischer_add_right, h₁, h₂]

end ReciprocityTheory.PGsh
end
end

