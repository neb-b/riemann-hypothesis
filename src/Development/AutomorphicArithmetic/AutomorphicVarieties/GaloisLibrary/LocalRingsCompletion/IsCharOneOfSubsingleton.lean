module

public import Mathlib

@[expose] public section

noncomputable section

open PowerSeries IsLocalRing

namespace UpperTheory.V.abelian₂

section Lift

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]

theorem aeval_sub_mem {I : Ideal R} {x : R} (hx : x ∈ I) {p q : Polynomial O} {n : ℕ}
    (h : ∀ i < n, p.coeff i = q.coeff i) : Polynomial.aeval x p - Polynomial.aeval x q ∈ I ^ n := by
  obtain ⟨r, hr⟩ : Polynomial.X ^ n ∣ p - q :=
    Polynomial.X_pow_dvd_iff.2 fun i hi => by simp [h i hi]
  rw [← map_sub, hr, map_mul, map_pow, Polynomial.aeval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hx n)

theorem eq_of_sub_mem_pow (I : Ideal R) [IsHausdorff I R] {a b : R} (h : ∀ n, a - b ∈ I ^ n) : a = b := by
  apply sub_eq_zero.mp
  apply IsHausdorff.haus ‹IsHausdorff I R› (a - b)
  intro n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact h n

theorem exists_lim (I : Ideal R) [IsAdicComplete I R] (x : I) (f : O⟦X⟧) :
    ∃ y : R, ∀ n, y - Polynomial.aeval (x : R) (trunc n f) ∈ I ^ n := by
  obtain ⟨y, hy⟩ := IsPrecomplete.prec' (I := I) (fun n => Polynomial.aeval (x : R) (trunc n f))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact aeval_sub_mem x.2 fun i hi => by simp [coeff_trunc, hi, hi.trans_le hmn])
  refine ⟨y, fun n => ?_⟩
  have := (hy n).symm
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this

def lift (I : Ideal R) [IsAdicComplete I R] (x : I) : O⟦X⟧ →ₐ[O] R where
  toFun f := (exists_lim I x f).choose
  map_one' := eq_of_sub_mem_pow I fun n => by
    have h := (I ^ n).add_mem ((exists_lim I x (1 : O⟦X⟧)).choose_spec n)
      (aeval_sub_mem (p := trunc n 1) (q := (1 : Polynomial O)) x.2 fun i hi => by
        simp [coeff_trunc, hi, coeff_one, Polynomial.coeff_one])
    simpa using h
  map_mul' f g := eq_of_sub_mem_pow I fun n => by
    have h1 := (exists_lim I x (f * g)).choose_spec n
    have h2 := (exists_lim I x f).choose_spec n
    have h3 := (exists_lim I x g).choose_spec n
    have h4 := aeval_sub_mem (p := trunc n (f * g)) (q := trunc n f * trunc n g) (n := n) x.2 fun i hi => by
      rw [coeff_trunc, if_pos hi, ← Polynomial.coeff_coe, Polynomial.coe_mul,
        coeff_mul_eq_coeff_trunc_mul_trunc _ _ hi]
    have := (I ^ n).sub_mem ((I ^ n).sub_mem ((I ^ n).add_mem h1 h4)
      (Ideal.mul_mem_right (exists_lim I x g).choose _ h2))
      (Ideal.mul_mem_left _ (Polynomial.aeval (x : R) (trunc n f)) h3)
    rw [map_mul (Polynomial.aeval (x : R))] at this
    convert this using 1
    ring
  map_zero' := eq_of_sub_mem_pow I fun n => by
    simpa using (exists_lim I x (0 : O⟦X⟧)).choose_spec n
  map_add' f g := eq_of_sub_mem_pow I fun n => by
    have h1 := (exists_lim I x (f + g)).choose_spec n
    have := (I ^ n).sub_mem ((I ^ n).sub_mem h1 ((exists_lim I x f).choose_spec n))
      ((exists_lim I x g).choose_spec n)
    rw [map_add (f := _), map_add (f := _)] at this
    convert this using 1
    ring
  commutes' r := eq_of_sub_mem_pow I fun n => by
    have h := (I ^ n).add_mem ((exists_lim I x (algebraMap O O⟦X⟧ r)).choose_spec n)
      (aeval_sub_mem (p := trunc n (algebraMap O O⟦X⟧ r)) (q := Polynomial.C r) x.2 fun i hi => by
        simp [coeff_trunc, hi, PowerSeries.algebraMap_apply, coeff_C, Polynomial.coeff_C])
    simpa using h

end Lift

section Local

variable {O : Type*} [CommRing O] [IsLocalRing O]


variable (O) in
def oneUnits : Subgroup Oˣ where
  carrier := {u | (u : O) - 1 ∈ maximalIdeal O}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have := (maximalIdeal O).add_mem (Ideal.mul_mem_right (b : O) _ ha) hb
    simpa [sub_mul] using this
  inv_mem' {a} ha := by
    have := (maximalIdeal O).neg_mem (Ideal.mul_mem_right ((a⁻¹ : Oˣ) : O) _ ha)
    simpa [sub_mul] using this

def pt (u : oneUnits O) : maximalIdeal O := ⟨((u : Oˣ) : O) - 1, u.2⟩

@[simp] theorem coe_pt (u : oneUnits O) : (pt u : O) = ((u : Oˣ) : O) - 1 := rfl

def ev [IsAdicComplete (maximalIdeal O) O] (a : maximalIdeal O) : O⟦X⟧ →ₐ[O] O :=
  lift (maximalIdeal O) a

end Local

section MuLam

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def mu (f : O⟦X⟧) : ℕ∞ := ⨅ n, IsDiscreteValuationRing.addVal O (coeff n f)

def lam (f : O⟦X⟧) : ℕ := sInf {n | IsDiscreteValuationRing.addVal O (coeff n f) = mu f}

theorem mu_le (f : O⟦X⟧) (n : ℕ) : mu f ≤ IsDiscreteValuationRing.addVal O (coeff n f) := iInf_le _ n

theorem addVal_coeff_lam (f : O⟦X⟧) : IsDiscreteValuationRing.addVal O (coeff (lam f) f) = mu f := by
  have hne : {n | IsDiscreteValuationRing.addVal O (coeff n f) = mu f}.Nonempty := by
    obtain ⟨n, hn⟩ := csInf_mem (Set.range_nonempty fun n => IsDiscreteValuationRing.addVal O (coeff n f))
    exact ⟨n, hn⟩
  exact Nat.sInf_mem hne

theorem mu_eq_top_iff {f : O⟦X⟧} : mu f = ⊤ ↔ f = 0 := by
  unfold mu
  rw [iInf_eq_top, PowerSeries.ext_iff]
  simp [IsDiscreteValuationRing.addVal_eq_top_iff]

end MuLam

def omega (R : Type*) [CommRing R] (l n : ℕ) : Polynomial R := (1 + Polynomial.X) ^ (l ^ n) - 1

section Char

variable {R : Type*} [CommRing R]

def locLen (P : Ideal R) [P.IsPrime] (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

def coinvLen (g : R) (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (QuotSMulTop g M)

def invLen (g : R) (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (Submodule.torsionBy R M g)

end Char

end UpperTheory.V.abelian₂

end
